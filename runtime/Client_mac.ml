open Colors
open Prelude
open PbftReplica
open Connect
open ParseConf
open MacKeyFun
open Core
open Async



(* ================================================================
   =--                 GLOBAL VARIABLES
 *)
(* turn this to false if you don't want to sign messages *)
let signing : bool ref = ref true

let plot_ts_file  : string = "pbft_ts"
let plot_avg_file : string = "pbft_avg"

(* default response time is 5ms when no signatures and 15ms when signatures *)
let max_time = if !signing then 0.030(*15*) else 0.005

let nfaults : int ref = ref 1

let initial_timestamp = 1

let printing_period : int ref = ref 10
let plotting_period : int ref = ref 10

let buffer_size : int = (128 (*16*) * 1024)
(* =--
   ================================================================ 
 *)


type reply_nfo = { timestamp : int; view : int; replica : int; result : int } [@@deriving bin_io]
(*type request_nfo = { timestamp : int; request : int } [@@deriving bin_io]*)


type writer_nfo = { nfo : node_nfo; w : Writer.t Deferred.t };;


exception Couldnt_find_primary


let is_primary_nfo (view : int) (nreps : int) (nfo : node_nfo) : bool =
  match nfo.id with
  | I_node n -> n = view mod nreps
  | E_node _ -> false


let rec find_primary_writer_nfo (view : int) (nreps : int) (nfos : writer_nfo list) : writer_nfo =
  match nfos with
  | [] -> raise Couldnt_find_primary
  | nfo :: nfos ->
     if is_primary_nfo view nreps nfo.nfo then nfo
     else find_primary_writer_nfo view nreps nfos


let sign_request breq syms : Cstruct.t list =
  let o = Obj.magic (PBFTmsg_bare_request breq) in
  let css = sign_list o syms in
(*  (if verify_one o pub cs
   then print_endline ("[managed to verify my own message]")
   else print_endline ("[couldn't verify my own message]"));*)
  css

    
let send_request prim view timestamp request id syms wnfo =
  let opr       = Obj.magic (Opr_add request) in
  let timestamp = timestamp in
  let client    = Obj.magic id in
  let breq      = Bare_req (opr,timestamp,client) in
  let tokens    = (if !signing then Obj.magic (sign_request breq syms) else Obj.magic([()])) in
  let req       = PBFTrequest (Req(breq,tokens)) in
  (*print_endline ("[sending request]");*)
  wnfo.w >>= fun w -> Deferred.return (Writer.write w (Marshal.to_string req []))

(*  try_with (fun () -> wnfo.w)
  >>| function
  | Ok w -> Writer.write w (Marshal.to_string req [])
  | Error exn -> print_endline (kBRED ^ "[writing error]" ^ kNRM)*)


let send_request_to_primary view timestamp request id syms wnfos =
  let pwnfo = find_primary_writer_nfo view (List.length wnfos) wnfos in
  send_request true view timestamp request id syms pwnfo


let rec send_request_to_all view timestamp request id syms nreps wnfos =
  match wnfos with
  | [] -> Deferred.return ()
  | wnfo :: wnfos ->
     (*if is_primary_nfo view nreps wnfo.nfo then
       print_endline ("[not contacting primary]")
     else*)
     print_endline ("[contacting " ^ ie_node2string wnfo.nfo.id ^ "]");
     let _ = send_request false view timestamp request id syms wnfo in
     send_request_to_all view timestamp request id syms nreps wnfos


let rec connect_to_all (nfos : node_nfo list) : writer_nfo list =
  match nfos with
  | [] -> []
  | nfo :: nfos ->
     let dw = connect_to nfo in
     let l = connect_to_all nfos in
     { nfo = nfo; w = dw } :: l


type worker_state_type =
  {
    last_timestamp  : int;
    last_request    : int;
    current_view    : int;
    rep_replied     : (int (* replica id *) * int (* view *)) list;
    time_sent       : Prelude.Time.t;
    time_average    : Prelude.Time.t;
    outliers        : int;
    client_id       : int;
    syms            : Cstruct.t list;
    max_timestamp   : int;
    writer_nfos     : writer_nfo list;
    writer_plot_ts  : Writer.t;
    writer_plot_avg : Writer.t;
  }

let update_new_timestamp_worker_state ws new_ts new_request new_view replicas new_time new_avg new_outliers =
  {
    last_timestamp  = new_ts;
    last_request    = new_request;
    current_view    = new_view;
    rep_replied     = replicas;
    time_sent       = new_time;
    time_average    = new_avg;
    outliers        = new_outliers;
    client_id       = ws.client_id;
    syms            = ws.syms;
    max_timestamp   = ws.max_timestamp;
    writer_nfos     = ws.writer_nfos;
    writer_plot_ts  = ws.writer_plot_ts;
    writer_plot_avg = ws.writer_plot_avg;
  }

let update_replicas_worker_state ws replicas =
  {
    last_timestamp  = ws.last_timestamp;
    last_request    = ws.last_request;
    current_view    = ws.current_view;
    rep_replied     = replicas;
    time_sent       = ws.time_sent;
    time_average    = ws.time_average;
    outliers        = ws.outliers;
    client_id       = ws.client_id;
    syms            = ws.syms;
    max_timestamp   = ws.max_timestamp;
    writer_nfos     = ws.writer_nfos;
    writer_plot_ts  = ws.writer_plot_ts;
    writer_plot_avg = ws.writer_plot_avg;
  }

let rec get_highest_view v l =
  match l with
  | [] -> v
  | (r,w) :: l -> if v < w then get_highest_view w l else get_highest_view v l


(* ==========================================================
   Worker to gather replies
 *)
module Worker = struct
  module T = struct
    type 'worker functions =
      {
        add_reply : ('worker, reply_nfo, unit) Rpc_parallel.Function.t
      }

    module Worker_state = struct
      type init_arg = int (* id *)
                      * int (* number of replicas *)
                      * int (* number of clients *)
                      * int (* max timestamp *)
                      * node_nfo list (* replica infos *) [@@deriving bin_io]
      type t = worker_state_type ref
    end

    module Connection_state = struct
      type init_arg = unit [@@deriving bin_io]
      type t = unit
    end

    module Functions
        (C : Rpc_parallel.Creator
         with type worker_state := Worker_state.t
          and type connection_state := Connection_state.t) = struct

      let rec start_timer (worker_state : worker_state_type ref) (view : int) (timestamp : int) : unit Deferred.t =
        Clock.after (Time.Span.of_sec 2.) >>= fun () ->
        let ws : worker_state_type = !worker_state in
        if (timestamp = ws.last_timestamp) && (List.length ws.rep_replied < !nfaults + 1) then
          (
            (* no progress has been made *)
            print_endline (kBMAG ^ "[no progress (" ^ string_of_int timestamp ^ "), contacting all replicas]" ^ kNRM);
            let _ = send_request_to_all ws.current_view ws.last_timestamp ws.last_request ws.client_id ws.syms (List.length ws.writer_nfos) ws.writer_nfos in
            print_endline (kBMAG ^ "[contacted all replicas]" ^ kNRM);
            start_timer worker_state view timestamp
          )
        else
          (
            (*print_endline (kBGRN ^ "[progressed (" ^ string_of_int timestamp ^ "-" ^ string_of_int (ws.last_timestamp) ^ ")]" ^ kNRM);*)
            Deferred.return ()
          )

      let add_reply = C.create_rpc
                        ~f:(fun ~worker_state ~conn_state:() (nfo : reply_nfo) ->
                          let ws = !worker_state in
                          let replicas' = (if ws.current_view <= nfo.view then
                                             if ws.last_timestamp = nfo.timestamp then
                                               if List.exists ws.rep_replied (fun (i,v) -> nfo.replica = i) then ws.rep_replied
                                               else
                                                 (nfo.replica,nfo.view) :: ws.rep_replied
                                             else ws.rep_replied
                                           else (print_endline (kBRED ^ "[old view, got " ^ string_of_int nfo.view ^ ", expected " ^ string_of_int ws.current_view ^ "]" ^ kNRM);
                                                 ws.rep_replied)) in
                          let _ = if List.length replicas' = !nfaults + 1 && ws.last_timestamp < ws.max_timestamp then
                                    (
                                      let t = Prelude.Time.sub_time (Prelude.Time.get_time ()) ws.time_sent in
                                      let (new_outliers, new_avg) =
                                        if Prelude.Time.lt_time (Prelude.Time.mk_time max_time) t
                                        then (ws.outliers + 1, ws.time_average)
                                        else (ws.outliers, Prelude.Time.div_time (Prelude.Time.add_time (Prelude.Time.mul_time ws.time_average  (ws.last_timestamp - 1)) t) ws.last_timestamp) in
                                      let new_time = Prelude.Time.get_time () in
                                      let new_ts = ws.last_timestamp + 1 in
                                      let new_request = 17 in
                                      let new_view = get_highest_view ws.current_view replicas' in
                                      let _ =
                                        if (ws.last_timestamp mod !plotting_period) = 0 then
                                          (
                                            Writer.write ws.writer_plot_ts  (string_of_int ws.last_timestamp ^ " " ^ Batteries.String.of_list (Prelude.Time.time2string t) ^ "\n");
                                            Writer.write ws.writer_plot_avg (string_of_int ws.last_timestamp ^ " " ^ Batteries.String.of_list (Prelude.Time.time2string new_avg) ^ "\n")
                                          )
                                        else () in
                                      let _ =
                                        if (ws.last_timestamp mod !printing_period) = 0 then
                                          print_endline (kMAG
                                                         ^ "["
                                                         ^ "timestamp: " ^ string_of_int ws.last_timestamp
                                                         ^ "; result: " ^ string_of_int nfo.result
                                                         ^ "; time since request was sent: " ^ Batteries.String.of_list (Prelude.Time.time2string t)
                                                         ^ "; outliers: " ^ string_of_int new_outliers
                                                         ^ "; old average: " ^ Batteries.String.of_list (Prelude.Time.time2string ws.time_average)
                                                         ^ "; new average: " ^ Batteries.String.of_list (Prelude.Time.time2string new_avg)
                                                         ^ "]"
                                                         ^ kNRM)
                                        else () in
                                      let _ =
                                        if ws.current_view < new_view then
                                          print_endline (kCYN ^ "[changed view: " ^ string_of_int ws.current_view ^ " -> " ^ string_of_int new_view ^ "]" ^ kNRM)
                                        else () in
                                      worker_state := update_new_timestamp_worker_state ws new_ts new_request new_view [] new_time new_avg new_outliers;
                                      (*print_endline (kYEL ^ "[sending new request with timestamp " ^ string_of_int new_ts ^ "]" ^ kNRM);*)
                                      let _ = send_request_to_primary ws.current_view new_ts new_request ws.client_id ws.syms ws.writer_nfos in
                                      let _ = start_timer worker_state ws.current_view new_ts in
                                      ()
                                    )
                                  else worker_state := update_replicas_worker_state ws replicas' in
                          Deferred.return ()
                        )
                        ~bin_input:bin_reply_nfo
                        ~bin_output:Unit.bin_t
                        ()

      let functions = {add_reply}

      let rec init_worker_state (id, numfaults, numclients, max, nfos) =
        let syms = List.map nfos (fun nfo -> lookup_client_key (Obj.magic (ie_node2int nfo.id)) (Obj.magic id)) in

        Writer.open_file ~append:(false) (plot_ts_file ^ "_" ^ string_of_int id ^ "_" ^ string_of_int numfaults ^ "_" ^ string_of_int numclients ^ "_" ^ string_of_int max ^ ".dat")
        >>= fun plot_ts ->
        let _ = Writer.write plot_ts "#instance/time to receive enough replies\n" in

        Writer.open_file ~append:(false) (plot_avg_file ^ "_" ^ string_of_int id ^ "_" ^ string_of_int numfaults ^ "_" ^ string_of_int numclients ^ "_" ^ string_of_int max ^ ".dat")
        >>= fun plot_avg ->
        let _ = Writer.write plot_avg "#instance/average time to receive enough replies\n" in

        let current_view = 0 in
        let wnfos        = connect_to_all nfos in
        let t            = Prelude.Time.get_time () in
        let avg          = Prelude.Time.mk_time 0. in
        let outliers     = 0 in
        let request      = 17 in

        let ws = ref {last_timestamp  = initial_timestamp;
                      last_request    = request;
                      current_view    = current_view;
                      rep_replied     = [];
                      time_sent       = t;
                      time_average    = avg;
                      outliers        = outliers;
                      client_id       = id;
                      syms            = syms;
                      max_timestamp   = max;
                      writer_nfos     = wnfos;
                      writer_plot_ts  = plot_ts;
                      writer_plot_avg = plot_avg} in

        let _ = send_request_to_primary current_view initial_timestamp request id syms wnfos in
        let _ = start_timer ws current_view initial_timestamp in
        Deferred.return ws
                                                                        
      let init_connection_state ~connection:_ ~worker_state:_ = return
    end
  end
  include Rpc_parallel.Make(T)
end


let extract_reply_info (msg : pBFTmsg) : (int * int * int * int * int) option =
  match msg with
  | PBFTreply (Reply (Bare_reply (v,ts,c,i,res), a)) -> Some (v,ts,Obj.magic c,Obj.magic i,Obj.magic res)
  | _ -> None


let handle_message id conn msg =
  match extract_reply_info msg with
  | Some (view,timestamp,client,replica,result) ->
     if client = id then
       (* we should also do something with the result *)
       (*let _ = print_endline ("[message matches expected reply]") in*)
       let nfo = { timestamp = timestamp; view = view; replica = replica; result = Obj.magic result } in
       let _ = Worker.Connection.run_exn conn ~f:Worker.functions.add_reply ~arg:(nfo) in
       ()
     else ()
  | None -> print_endline ("[message doesn't match expected reply]")


let rec read_messages id conn buffer size ofs : string =
  let header = Marshal.header_size in
  if header <= size then
    let total = Marshal.total_size buffer ofs in
    if total <= size then
      (*print_endline ("[size: " ^ string_of_int size ^ "; total: " ^ string_of_int (Marshal.total_size buffer ofs) ^ "; bytes: " ^ str ^ "]");*)
      let msg : pBFTmsg = Marshal.from_string (Bytes.to_string buffer) ofs in
      (*print_endline (kCYN ^ "[read: " ^ Batteries.String.of_list (msg2string msg) ^ "]" ^ kNRM);*)
      let _ = handle_message id conn msg in
      if total < size then
        read_messages id conn buffer (size - total) (ofs + total)
      else ""
    else String.sub (Bytes.to_string buffer) ofs size
  else String.sub (Bytes.to_string buffer) ofs size


let rec read_inputs addr id init buffer r conn =
  (*print_endline ("[reading from " ^ Socket.Address.to_string addr ^ "]");*)
  Reader.read r buffer ~len:(buffer_size)
  >>= function
  | `Eof -> return ()
  | `Ok bytes_read ->
     (*print_endline ("[bytes read (bufer size: " ^ string_of_int bytes_read ^ ") (total size " ^ string_of_int (Marshal.total_size buffer 0) ^ "): " ^ String.sub buffer 0 bytes_read ^ "]");*)
     let buffer' = init ^ Bytes.to_string buffer in
     let rest = read_messages id conn (Bytes.of_string buffer') (String.length init + bytes_read) 0 in
     read_inputs addr id rest buffer r conn;;


let initialize (id : int) (conf : string) (max : int) (nf : int) (numclients : int) (printingp : int) (plottingp : int) =
  print_endline ("[initializing generator]");
  let () = Nocrypto_entropy_unix.initialize () in

  print_endline ("[number of faults: " ^ string_of_int nf ^ "]");
  nfaults := nf;

  print_endline ("[printing period: " ^ string_of_int printingp ^ "]");
  printing_period := printingp;

  print_endline ("[plotting period: " ^ string_of_int plottingp ^ "]");
  plotting_period := plottingp;

  print_endline ("[reading configuration file]");
  Reader.open_file conf
  >>= fun c ->
  (* false means not a replica *)
  parse_conf conf false id 1 c
  >>= fun (ownopt,replicas0,_clients) ->
  let own = make_own id ownopt in
  let numreplicas = (3 * nf) + 1 in
  let replicas = Batteries.List.take numreplicas replicas0 in
  print_endline ("[***replicas***]");
  print_nfos replicas;

  print_endline ("[setting up connections]");
  Worker.serve (id,nf,numclients,max,replicas)
  >>= fun worker ->
  Worker.Connection.client_exn worker ()
  >>= fun conn ->

  print_endline ("[starting server socket]");
  let host_and_port =
    Tcp.Server.create
      ~on_handler_error:(*`Raise*)`Ignore(*(`Call(fun addr exn -> print_endline ("[connection died]")))*)
      (Tcp.Where_to_listen.of_port own.port)
      (fun addr r __ ->
        print_endline (kBYEL ^ "[handling connection from " ^ Socket.Address.to_string addr ^ "]" ^ kNRM);
        let init = "" in
        let buffer = String.create buffer_size in
        read_inputs addr id init buffer r conn) in
  ignore (host_and_port : (Socket.Address.Inet.t, int) Tcp.Server.t Deferred.t);
  Deferred.never ();;

let command =
  Command.async_spec
    ~summary:"Start a client"
    Command.Spec.(
      empty
      +> flag "-id" (optional_with_default 0 int)
        ~doc:" client identifier"

      +> flag "-conf" (optional_with_default "config" string)
        ~doc:" Configuration file"

      +> flag "-max" (optional_with_default 10 int)
        ~doc:" Number of messages to send (default 10)"

      +> flag "-num-faults" (optional_with_default 1 int)
        ~doc:" Number of faults"

      +> flag "-num-clients" (optional_with_default 1 int)
        ~doc:" Number of faults"

      +> flag "-printing-period" (optional_with_default 10 int)
        ~doc:" Printing period"

      +> flag "-plotting-period" (optional_with_default 10 int)
        ~doc:" Plotting period"
    )
    (fun id conf max nfaults numclients printingp plottingp () ->
      initialize id conf max nfaults numclients printingp plottingp);;

let () = Rpc_parallel.start_app command;;
