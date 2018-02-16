open Colors
open Core
open Async


(* either internal or external *)
type ie_node =
| I_node of int
| E_node of int [@@deriving bin_io]

type node_nfo = { id : ie_node; host : string; port : int; key : string } [@@deriving bin_io]


let ie_node2string (n : ie_node) : string =
  match n with
  | I_node i -> "I(" ^ string_of_int i ^ ")"
  | E_node i -> "E(" ^ string_of_int i ^ ")"

let ie_node2int (n : ie_node) : int =
  match n with
  | I_node i -> i
  | E_node i -> i


let node_nfo2string (nfo : node_nfo) : string =
  "{id=" ^ ie_node2string nfo.id ^ ";host=" ^ nfo.host ^ ";port=" ^ string_of_int nfo.port ^ ";key=" ^ nfo.key ^ "}"


let print_nfo (nfo : node_nfo) : unit =
  print_endline ("[id:" ^ ie_node2string nfo.id ^ ";host:" ^ nfo.host ^ ";port:" ^ string_of_int nfo.port ^ ";key:" ^ nfo.key ^ "}")


let rec print_nfos (nfos : node_nfo list) : unit =
  match nfos with
  | [] -> ()
  | nfo :: nfos -> print_nfo nfo; print_nfos nfos


(*let rec connect_to_loop (nfo : node_nfo) (wait : float) : Writer.t Deferred.t =
  try_with
    (fun () ->
      print_endline ("[connecting to " ^ node_nfo2string nfo ^ "]");
      (* WARNING: Setting the timeout doesn't seem to be doing anything.
          Is there a connect function that keeps on trying for a while?
       *)
      Async.Tcp.with_connection
        ~timeout:(Time.Span.of_int_sec 60)
        ~reader_buffer_size:(40) (* What's the default value *)
        (Async.Tcp.to_inet_address (Socket.Address.Inet.create (Async.Unix.Inet_addr.of_string nfo.host) nfo.port))
        (fun sock _r w ->
          print_endline (kBBLU ^ "[connected to " ^ node_nfo2string nfo ^ " using " ^ Socket.Address.to_string (Socket.getsockname sock) ^ "]" ^ kNRM);
          Deferred.return w))
  >>= function
  | Ok (w) -> Deferred.return w
  | Error _ ->
     (
       print_endline ("[failure to connect---sleeping for 1s]");
       Clock.after (Time.Span.of_sec wait) >>= fun () ->
       connect_to_loop nfo ((*2. *.*) wait)
     )
 *)


let rec connect_to_loop (nfo : node_nfo) (wait : float) : Writer.t Deferred.t =
  try_with
    (fun () ->
      (*print_endline ("[connecting to " ^ node_nfo2string nfo ^ "]");*)
      (* WARNING: Setting the timeout doesn't seem to be doing anything.
          Is there a connect function that keeps on trying for a while?
       *)
      Async.Tcp.connect
        ~timeout:(Time.Span.of_int_sec 60)
        ~reader_buffer_size:((*20*)40) (* What's the default value *)
        (*~interrupt:(Deferred.return (print_endline("[connection to " ^ node_nfo2string nfo ^ " died]")))*)
        ~buffer_age_limit:(`At_most(Time.Span.of_int_sec 10))
        (Async.Tcp.Where_to_connect.of_inet_address (Socket.Address.Inet.create (Async.Unix.Inet_addr.of_string nfo.host) nfo.port)))
  >>= function
  | Ok (sock,_r,w) ->
     (
       print_endline (kBBLU ^ "[connected to " ^ node_nfo2string nfo ^ " using " ^ Socket.Address.to_string (Socket.getsockname sock) ^ "]" ^ kNRM);
       Deferred.return w
     )
  | Error _ ->
     (
       (*print_endline ("[failure to connect---sleeping for 1s]");*)
       Clock.after (Time.Span.of_sec wait) >>= fun () ->
       connect_to_loop nfo ((*2. *.*) wait)
     )


let connect_to (nfo : node_nfo) : Writer.t Deferred.t =
  connect_to_loop nfo 1.
