open Colors
open Prelude
open PbftReplica
open Connect
open ParseConf
open Core
open Async


let replica : (pBFTstate mStateMachine) ref = ref pBFTdummySM;;


(* TO CHECK: Do messages go through if too small? *)
let buffer_size : int = (4 (*8*) (*16*) (*128*) * 1024)


(* ==========================================================
   Worker to connect and send messages to the other replicas.
 *)
module Worker = struct
  module T = struct
    type 'worker functions = { send : ('worker, string, unit) Rpc_parallel.Function.t }

    module Worker_state = struct
      type init_arg = node_nfo * node_nfo [@@deriving bin_io]
      type t = node_nfo * node_nfo * (Writer.t Deferred.t)
    end

    module Connection_state = struct
      type init_arg = unit [@@deriving bin_io]
      type t = unit
    end

    module Functions
        (C : Rpc_parallel.Creator
         with type worker_state := Worker_state.t
          and type connection_state := Connection_state.t) = struct
      let send = C.create_rpc
                   ~f:(fun ~worker_state ~conn_state:() (smsg : string) ->
                     let (mynfo,nfo,dw) = worker_state in
                     dw >>= fun w ->

                     (***TODO***)
                     (* How to close the writer if the replica on the other side is dead? *)

                     (*Writer.set_raise_when_consumer_leaves w true;*)
                     (*print_endline (kYEL ^ "[open(" ^ node_nfo2string nfo ^ ")? " ^ string_of_bool (Writer.is_open w) ^ "]" ^ kNRM);*)
                     (*Sexp.output stdout (Io_stats.sexp_of_t Writer.io_stats);*)
                     (* The connection has to be made when we want to send the message *)
                     (***PRINTING***)
                     (*print_endline (kYEL ^ "[sending message to " ^ node_nfo2string nfo ^ " (still " ^ string_of_int (Writer.bytes_to_write w) ^ " bytes to write): " ^ Batteries.String.of_list (msg2string m) ^ "]" ^ kNRM);*)
                     let _ = Writer.write w smsg in
                     (***PRINTING***)
                     (*print_endline (kYEL ^ "[message is sent]" ^ kNRM);*)
                     Deferred.return ()
                   )
                   ~bin_input:String.bin_t
                   ~bin_output:Unit.bin_t
                   ()

      let functions = {send}

      let rec init_worker_state (mynfo,nfo) =
        (
          print_endline ("[initializing connection with " ^ node_nfo2string nfo ^ "]");
          let dw = connect_to nfo in
          Deferred.return (mynfo, nfo, dw)
        )

      let init_connection_state ~connection:_ ~worker_state:_ = return
    end
  end
  include Rpc_parallel.Make(T)
end

type conn_nfo = { nfo : node_nfo; conn : Worker.Connection.t };;

(* ======================================== *)



(* ========================================
   Runs the state machine on an input
 *)
let print_outputs out =
  print_endline ("[outputs: " ^ Batteries.String.of_list (directedMsgs2string out) ^ "]")

let print_output_new_view o =
  match Obj.magic o.dmMsg with
  | PBFTnew_view _ -> print_endline ("[outputs: " ^ Batteries.String.of_list (directedMsg2string o) ^ "]")
  | _ -> ()

let print_outputs_new_view out =
  match out with
  | [o] -> print_output_new_view o
  | _ -> ()

           
let run_replica_on_input mynfo (m : msg) : directedMsgs =
  (***PRINTING***)
  (*print_endline (kGRN ^ "[input message: " ^ Batteries.String.of_list (msg2string m) ^ "]" ^ kNRM);*)
  let (sm,out) = lrun_sm (!replica) (Obj.magic m) in
  replica := sm;

  (***PRINTING***)
  (*print_outputs out;*)
  (*print_outputs_new_view out;*)
  out;;

(* ======================================== *)


  
(* ========================================
     Various to_string functions
 *)
let conn_nfo2string (nfo : conn_nfo) : string =
  "{nfo=" ^ node_nfo2string (nfo.nfo) ^ ";conn=_}";;

let rec conn_nfos2string_aux (nfos : conn_nfo list) : string =
  match nfos with
  | [] -> ""
  | [nfo] -> conn_nfo2string nfo
  | nfo :: nfos -> conn_nfo2string nfo ^ ";" ^ conn_nfos2string_aux nfos;;

let conn_nfos2string (nfos : conn_nfo list) : string =
  "{" ^ conn_nfos2string_aux nfos ^ "}";;

let destination2string (n : name) : string =
  match Obj.magic n with
  | PBFTreplica r -> "R(" ^ string_of_int (Obj.magic r) ^ ")"
  | PBFTclient  c -> "C(" ^ string_of_int (Obj.magic c) ^ ")" ;;

let rec destinations2string_aux (l : name list) : string =
  match l with
  | [] -> ""
  | [d] -> destination2string d
  | d :: l -> destination2string d ^ ";" ^ destinations2string_aux l;;

let destinations2string (l : name list) : string =
  "{" ^ destinations2string_aux l ^ "}";;

(* ======================================== *)



(* ========================================
     Functions to send outputs
 *)
let name2ie_node (n : name) : ie_node =
  match Obj.magic n with
  | PBFTreplica i -> I_node (Obj.magic i)
  | PBFTclient  i -> E_node (Obj.magic i)

let rec find_conn_nfo (dst : name) (nfos : conn_nfo list) : conn_nfo option =
  match nfos with
  | [] -> None
  | nfo :: nfos ->
     if name2ie_node dst = nfo.nfo.id then Some nfo
     else find_conn_nfo dst nfos;;

let send_output_dst mynfo (msg : msg) (dst : name) (delay : int) (nfos : conn_nfo list) : unit Deferred.t =
  match find_conn_nfo dst nfos with
  | None ->
     (print_endline ("[couldn't send output because didn't find destination " ^ destination2string dst ^ " among " ^ conn_nfos2string nfos ^ "]");
      Deferred.return ())
  | Some nfo ->
     (***PRINTING***)
     (*print_endline ("[destination: " ^ destination2string dst ^ "]");*)
     let smsg = Marshal.to_string msg [] in
     if 0 < delay then
       within'
         ~monitor:(Monitor.create ())
         (fun () -> Clock.after (Time.Span.of_sec (float_of_int delay /. 1000.))
                    >>= fun () -> Worker.Connection.run_exn nfo.conn ~f:Worker.functions.send ~arg:(smsg(*im*)))
     else
       Worker.Connection.run_exn nfo.conn ~f:Worker.functions.send ~arg:(smsg(*im*))

let rec send_output mynfo (msg : msg) (l : name list) (delay : int) (nfos : conn_nfo list) : unit Deferred.t =
  match l with
  | [] -> Deferred.return ()
  | dst :: dsts ->
     let _ = send_output_dst mynfo msg dst delay nfos in
     send_output mynfo msg dsts delay nfos;;

let rec send_outputs mynfo (out : directedMsgs) (nfos : conn_nfo list) : unit Deferred.t =
  match out with
  | [] -> Deferred.return ()
  | dmsg :: dmsgs ->
     let msg   = Obj.magic (dmsg.dmMsg) in
     let dst   = dmsg.dmDst in
     let delay = dmsg.dmDelay in
     (*print_endline ("[destinations: " ^ Batteries.String.of_list (names2string dst) ^ "]");*)
     (*print_endline ("[destinations: " ^ destinations2string dst ^ "]");*)
     let _ = send_output mynfo msg dst delay nfos in
     send_outputs mynfo dmsgs nfos;;

(* ======================================== *)



(* ========================================
 *)
(* b=true means that we found our id in the list.
   The returned list is the list l minus our id.
 *)
let rec get_my_output (nfo : node_nfo) (l : name list) : bool * name list =
  match l with
  | [] -> (false,[])
  | dst :: dsts ->
     let (b,l) = get_my_output nfo dsts in
     if name2ie_node dst = nfo.id then
       (true,l)
     else (b,dst :: l);;

let mk_message_if_some_dest (names : name list) (msg : msg) (delay : int) : directedMsgs =
  match names with
  | [] -> []
  | _ -> [{ dmMsg = Obj.magic msg ; dmDst = names; dmDelay = delay }];;

let rec get_my_outputs (nfo : node_nfo) (out : directedMsgs) : (msg * int) list * directedMsgs =
  match out with
  | [] -> ([],[])
  | dmsg :: dmsgs ->
     let msg : msg = Obj.magic dmsg.dmMsg in
     let dst = dmsg.dmDst in
     let delay = dmsg.dmDelay in
     let (b,names) = get_my_output nfo dst in
     let dmsgs1 = mk_message_if_some_dest names msg delay in
     let (mymsgs,dmsgs2) = get_my_outputs nfo dmsgs in
     if b then ((msg,delay) :: mymsgs, dmsgs1 @ dmsgs2)
     else (mymsgs, dmsgs1 @ dmsgs2) ;;

(* ======================================== *)



(* ========================================
 *)

let rec run_replica_on_inputs mynfo nfos (msgs : (msg * int) list) : unit Deferred.t =
  match msgs with
  | [] -> Deferred.return ()
  | (msg,delay) :: msgs ->
       within'
         ~monitor:(Monitor.create ())
         (fun () -> Clock.after (Time.Span.of_sec (float_of_int delay /. 1000.))
                    >>= fun () ->
                    (*print_endline ("[running proccess on input]");*)
                    (*let time1 = Prelude.Time.get_time () in*)
                    let dmsgs : directedMsgs = run_replica_on_input mynfo msg in
                    (*print_endline (kYEL ^ "[elapsed: " ^ Batteries.String.of_list (Prelude.Time.time2string (Prelude.Time.sub_time (Prelude.Time.get_time ()) time1)) ^ " --- " ^ "msg: " ^ Batteries.String.of_list (msg2string (Obj.magic msg)) ^ "]" ^ kNRM);*)

                    (*print_endline ("[extracting my own messages]");*)
                    let (mymsgs,dmsgs') = get_my_outputs mynfo dmsgs in

                    (***PRINTING***)
                    (*print_endline ("[sending outputs]");*)
                    (*print_outputs out;*)
                    print_outputs_new_view dmsgs';
                    let _ = send_outputs mynfo dmsgs' nfos in

                    run_replica_on_inputs mynfo nfos mymsgs
         );

(*       (*print_endline ("[running proccess on input]");*)
       let dmsgs : directedMsgs = run_replica_on_input mynfo msg in

       (*print_endline ("[extracting my own messages]");*)
       let (mymsgs,dmsgs') = get_my_outputs mynfo dmsgs in

       (*print_endline ("[sending outputs]");*)
       let _ = send_outputs mynfo dmsgs' nfos in*)

       run_replica_on_inputs mynfo nfos (msgs(* @ mymsgs*))



let rec read_messages mynfo buffer size ofs : (msg list * string) =
  let header = Marshal.header_size in
  if header <= size then
    let total = Marshal.total_size buffer ofs in
    if total <= size then
      (*let str = String.sub buffer ofs total in*)
      (*print_endline ("[size: " ^ string_of_int size ^ "; total: " ^ string_of_int (Marshal.total_size buffer ofs) ^ "; bytes: " ^ str ^ "]");*)
      let msg : msg = Marshal.from_string (Bytes.to_string buffer) ofs in
      if total < size then
        let (msgs, rest) = read_messages mynfo buffer (size - total) (ofs + total) in
        (msg :: msgs, rest)
      else ([msg], "")
    else ([], String.sub (Bytes.to_string buffer) ofs size)
  else ([], String.sub (Bytes.to_string buffer) ofs size)


let rec read_inputs mynfo init buffer r (nfos : conn_nfo list) : unit Deferred.t =
  (*print_endline ("[reading]");*)
  Reader.read r buffer ~len:(buffer_size)
  >>= function
  | `Eof -> (print_endline (kRED ^ "[EOF]" ^ kNRM); Deferred.return ())
  | `Ok bytes_read ->
     (*print_endline ("[bytes read (bufer size: " ^ string_of_int bytes_read ^ ") (total size " ^ string_of_int (Marshal.total_size buffer 0) ^ "): " ^ String.sub buffer 0 bytes_read ^ "]");*)
     (*print_endline ("[(bufer size: " ^ string_of_int buffer_size ^ ") (bytes read: " ^ string_of_int bytes_read ^ ") (total size " ^ string_of_int (Marshal.total_size buffer 0) ^ ")]");*)
     let buffer' = init ^ Bytes.to_string buffer in
     let (msgs, rest) = read_messages mynfo (Bytes.of_string buffer') (String.length init + bytes_read) 0 in
     (***PRINTING***)
     (*print_endline (kCYN ^ "[read: " ^ Batteries.String.of_list (str_concat (map msg2string msgs)) ^ "]" ^ kNRM);*)

     run_replica_on_inputs mynfo nfos (List.map msgs (fun m -> (m,0)));

     read_inputs mynfo rest buffer r nfos;;


let rec connect_to_all mynfo (nfos : node_nfo list) : (conn_nfo list) Deferred.t =
  match nfos with
  | [] -> Deferred.return []
  | nfo :: nfos ->
     Worker.serve (mynfo,nfo)
     >>= fun worker ->
     Worker.Connection.client_exn worker ()
     >>= fun conn ->
     connect_to_all mynfo nfos
     >>= fun conn_nfos -> Deferred.return ({nfo = nfo; conn = conn} :: conn_nfos)


let setup_connections (myid : int) (conf : string) (numfaults : int) (numclients : int) =
  let numreplicas = (3 * numfaults) + 1 in
  print_endline ("[number of faults: "   ^ string_of_int numfaults   ^ "]");
  print_endline ("[number of replicas: " ^ string_of_int numreplicas ^ "]");
  print_endline ("[number of clients: "  ^ string_of_int numclients  ^ "]");

  print_endline ("[initializing generator]");
  let () = Nocrypto_entropy_unix.initialize () in

  print_endline ("[reading configuration file]");
  Reader.open_file conf
  >>= fun c ->
  (* false means myid is a replica *)
  let line_number = 1 in
  parse_conf conf true myid line_number c
  >>= fun (ownopt,replicas0,clients0) ->
  let own = make_own myid ownopt in
  let replicas = Batteries.List.take numreplicas replicas0 in
  let clients  = Batteries.List.take numclients  clients0  in
  print_endline ("[***replicas***]");
  print_nfos replicas;
  print_endline ("[***clients***]");
  print_nfos clients;

  print_endline ("[setting up connections]");
  let nodes = replicas @ clients in
  connect_to_all own nodes
  >>= fun conns ->

  print_endline ("[starting server socket]");
  let host_and_port =
    Tcp.Server.create
      ~on_handler_error:(*`Raise*)(`Call(fun addr exn -> print_endline ("[connection from " ^ Socket.Address.to_string addr ^ " died]")))
      (*~backlog:(100)*)
      (Tcp.Where_to_listen.of_port own.port)
      (fun addr r _w ->
        print_endline (kBYEL ^ "[handling connection from " ^ Socket.Address.to_string addr ^ "]" ^ kNRM);
        let init = "" in
        let buffer = String.create buffer_size in
        read_inputs own init buffer r conns)
  in

  ignore (host_and_port : (Socket.Address.Inet.t, int) Tcp.Server.t Deferred.t);
  Deferred.never () ;;

                 
let command =
  Command.async_spec
    ~summary:"Start a replica"
    Command.Spec.(
      empty
      +> flag "-id" (optional_with_default 0 int)
        ~doc:" Replica identifier"

      +> flag "-conf" (optional_with_default "config" string)
        ~doc:" Configuration file"

      +> flag "-num-faults" (optional_with_default 1 int)
        ~doc:" Number of faults"

      +> flag "-num-clients" (optional_with_default 1 int)
        ~doc:" Number of clients"
    )
    (fun id conf numfaults numclients () ->
      print_endline ("[setting replica]");
      replica := local_replica (*numreplicas numclients*) (Obj.magic id);
      setup_connections id conf numfaults numclients);;


let () = Rpc_parallel.start_app command;;
