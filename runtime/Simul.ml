open Colors
open Prelude
open PbftReplica
open RsaKeyFun
open Core

(* turn this to false if you don't want to sign messages *)
let signing : bool ref = ref true

type idrep = { id : name ; replica : pBFTstate mStateMachine }

let replicas : idrep list ref = ref []

let set_replicas () =
  replicas := [{ id = Obj.magic (PBFTreplica (Obj.magic 0)); replica = local_replica (Obj.magic 0) };
               { id = Obj.magic (PBFTreplica (Obj.magic 1)); replica = local_replica (Obj.magic 1) };
               { id = Obj.magic (PBFTreplica (Obj.magic 2)); replica = local_replica (Obj.magic 2) };
               { id = Obj.magic (PBFTreplica (Obj.magic 3)); replica = local_replica (Obj.magic 3) }]

let sign_request breq priv =
  let o  = Obj.magic (PBFTmsg_bare_request breq) in
  sign_one o priv

let mk_request (priv : Nocrypto.Rsa.priv) (timestamp : int) (request : int) (id : name) =
  let opr       = Obj.magic (Opr_add request) in
  let client    = id in
  let breq      = Bare_req (opr,timestamp,client) in
  let tokens    = [ (if !signing then Obj.magic (sign_request breq priv) else Obj.magic()) ] in
  PBFTrequest (Req(breq,tokens))

let rec find_replica (id : name) (replicas : idrep list) : (pBFTstate mStateMachine) option =
  match replicas with
  | [] -> None
  | idrep :: idreps ->
     if id = idrep.id then
       Some idrep.replica
     else find_replica id idreps

let rec replace_replica (id : name) (rep : pBFTstate mStateMachine) (replicas : idrep list) =
  match replicas with
  | [] -> []
  | idrep :: idreps ->
     if id = idrep.id then
       { id = id; replica = rep } :: idreps
     else idrep :: replace_replica id rep idreps

let destination2string (n : name) : string =
  match Obj.magic n with
  | PBFTreplica r -> "R(" ^ string_of_int (Obj.magic r) ^ ")"
  | PBFTclient  c -> "C(" ^ string_of_int (Obj.magic c) ^ ")" ;;

let rec run_replicas_on_inputs (inflight : directedMsgs) : directedMsgs =
  match inflight with
  | [] -> []
  | dm :: dms ->
     (*print_endline (kCYN ^ "[processsing: " ^ Batteries.String.of_list (directedMsg2string dm) ^ "]" ^ kNRM);*)
     match dm.dmDst with
     | [] -> run_replicas_on_inputs dms
     | id :: ids ->
        let dm' = { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay } in
        match find_replica id (!replicas) with
        | None ->
           (*print_endline (kBRED ^ "[couldn't find id " ^ destination2string id ^ "]" ^ kNRM);*)
           let failed_to_deliver = { dmMsg = dm.dmMsg; dmDst = [id]; dmDelay = dm.dmDelay } in
           failed_to_deliver :: run_replicas_on_inputs (dm' :: dms)
        | Some rep ->
           (*print_endline (kGRN ^ "[input message: " ^ Batteries.String.of_list (msg2string (Obj.magic dm.dmMsg)) ^ "]" ^ kNRM);*)
           let (rep',dmsgs) = lrun_sm rep (Obj.magic dm.dmMsg) in
           (*print_endline ("[done]");*)
           replicas := replace_replica id rep' (!replicas);
           run_replicas_on_inputs (dm' :: dms @ dmsgs)

let rec run_client (id : client) (priv : Nocrypto.Rsa.priv) (timestamp : int) (max : int) (avg : Prelude.Time.t) (primary : name) (printing_period : int) =
  let req = mk_request priv timestamp 17 id in
  let inflight = [{ dmMsg = Obj.magic req; dmDst = [primary]; dmDelay = 0 }] in
  let t = Prelude.Time.get_time () in
  let failed_to_deliver = run_replicas_on_inputs inflight in
  let d = Prelude.Time.sub_time (Prelude.Time.get_time ()) t in
  let new_avg = Prelude.Time.div_time (Prelude.Time.add_time (Prelude.Time.mul_time avg  (timestamp - 1)) d) timestamp in
  (*let s = Batteries.String.of_list (directedMsgs2string failed_to_deliver) in*)
  (if timestamp mod printing_period = 0 then
     print_endline (kMAG
                    ^ "[timestamp: " ^ string_of_int timestamp
                    ^ "; elapsed time: " ^ Batteries.String.of_list (Prelude.Time.time2string d)
                    ^ "; average: " ^ Batteries.String.of_list (Prelude.Time.time2string new_avg)
                    (*^ "; non delievered messages: " ^ s*)
                    ^ "]"
                    ^ kNRM)
   else ());
  if timestamp < max then
    run_client id priv (timestamp + 1) max new_avg primary printing_period
  else ()

let command =
  Command.basic_spec
    ~summary:"Start a client"
    Command.Spec.(
      empty
      +> flag "-max" (optional_with_default 10 int)
        ~doc:" Number of messages to send (default 10)"

      +> flag "-printing-period" (optional_with_default 10 int)
        ~doc:" Number of messages to send (default 10)"
    )
    (fun max printing_period () ->
      print_endline ("[initializing generator]");
      let () = Nocrypto_entropy_unix.initialize () in

      print_endline ("[setting replicas]");
      set_replicas ();

      print_endline ("[running client]");
      let client_id         = Obj.magic 0 in
      let initial_timestamp = 1 in
      let initial_avg       = Prelude.Time.mk_time 0. in
      let primary           = Obj.magic (PBFTreplica (Obj.magic 0)) in
      let priv              = lookup_client_sending_key (Obj.magic client_id) in
      run_client client_id priv initial_timestamp max initial_avg primary printing_period)

let _ = Command.run ~version:"1.0" ~build_info:"PBFT" command
