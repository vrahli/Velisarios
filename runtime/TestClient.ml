open Colors
open Core
open Async

let rec connect_to_loop (wait : float) : Writer.t Deferred.t =
  try_with
    (fun () ->
      (* WARNING: Setting the timeout doesn't seem to be doing anything.
          Is there a connect function that keeps on trying for a while?
       *)
      Async.Tcp.connect
        ~timeout:(Time.Span.of_int_sec 60)
        ~reader_buffer_size:((*20*)40) (* What's the default value *)
        (*~interrupt:(Deferred.return (print_endline("[connection to " ^ node_nfo2string nfo ^ " died]")))*)
        (Async.Tcp.to_inet_address (Socket.Address.Inet.create (Async.Unix.Inet_addr.of_string "127.0.0.1") 5000)))
  >>= function
  | Ok (sock,r,w) ->
     (
       print_endline (kBBLU ^ "[connected to server using " ^ Socket.Address.to_string (Socket.getsockname sock) ^ "]" ^ kNRM);
       Deferred.return w
     )
  | Error _ ->
     (
       (*print_endline ("[failure to connect---sleeping for 1s]");*)
       Clock.after (Time.Span.of_sec wait) >>= fun () ->
       connect_to_loop ((*2. *.*) wait)
     )


let connect_to () : Writer.t Deferred.t =
  connect_to_loop 1.

let rec mk_input n =
  if n = 0 then ""
  else "x" ^ mk_input (n - 1)

let rec send_inputs w n m =
  if n = m then Deferred.return ()
  else
    let i = mk_input 1000 in
    print_endline (kBBLU ^ "[sending input(" ^ string_of_int m ^ ") " ^ i ^ "]" ^ kNRM);
    let s = Marshal.to_string i [] in
    let _ = Writer.write w s in
    send_inputs w n (m + 1)

let start () =
  let dw = connect_to () in
  dw >>= fun w ->
  send_inputs w 10000 0;

  Deferred.never () ;;

let command =
  Command.async
    ~summary:"Start a server"
    Command.Spec.(
      empty
    )
    (fun () ->
      print_endline ("[starting client]");
      start ());;


let () = Rpc_parallel.start_app command;;
