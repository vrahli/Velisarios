open Colors
open Core
open Async

let buffer_size : int = (1 * 128)

let rec read_messages n buffer size ofs : (int * string list * string) =
  (*print_endline (kMAG ^ "[extracting input from (len:" ^ string_of_int (String.length buffer) ^ "; size:" ^ string_of_int size ^ "; ofs:" ^ string_of_int ofs ^ ") " ^ buffer ^ "]" ^ kNRM);*)
  (*print_endline (kMAG ^ "[i.e. (len " ^ string_of_int (String.length (String.sub buffer ofs size)) ^ ") " ^ String.sub buffer ofs size ^ "]" ^ kNRM);*)
  (*print_endline (kBYEL ^ "[string size:" ^ string_of_int size ^ "; offset:" ^ string_of_int ofs ^ "]" ^ kNRM);*)
  let header = Marshal.header_size in
  (*print_endline (kBYEL ^ "[header size:" ^ string_of_int header ^ "]" ^ kNRM);*)
  if header <= size then
    let data = Marshal.data_size buffer ofs in
    (*print_endline (kBYEL ^ "[data size:" ^ string_of_int data ^ "]" ^ kNRM);*)
    let total = Marshal.total_size buffer ofs in
    (*print_endline (kBYEL ^ "[total size:" ^ string_of_int total ^ "]" ^ kNRM);*)
    if total <= size then
      let i : string = Marshal.from_string buffer ofs in
      print_endline (kBYEL ^ "[read input (" ^ string_of_int n ^ ") " ^ i ^ "]" ^ kNRM);
      (*print_endline (kBYEL ^ "[marshaled was " ^ String.sub buffer ofs total ^ "]" ^ kNRM);*)
      if total < size then
        let (m, inputs, rest) = read_messages (n + 1) buffer (size - total) (ofs + total) in
        (m, i :: inputs, rest)
      else (n + 1, [i], "")
    else (n, [], String.sub buffer ofs size)
  else (n, [], String.sub buffer ofs size)

let rec read_inputs n init buffer r : unit Deferred.t =
  (*print_endline (kBYEL ^ "[reading]" ^ kNRM);*)
  Reader.read r buffer ~len:(buffer_size)
  >>= function
  | `Eof -> (print_endline (kRED ^ "[EOF]" ^ kNRM); Deferred.return ())
  | `Ok bytes_read ->
     let buffer' = init ^ buffer in
     (*print_endline (kBYEL ^ "[extracting inputs]" ^ kNRM);*)
     let (m, input, rest) = read_messages n buffer' (bytes_read + String.length init) 0 in
     (*print_endline (kBYEL ^ "[rest " ^ rest ^ "]" ^ kNRM);*)

     read_inputs m rest buffer r;;

let start () =
  let host_and_port =
    Tcp.Server.create
      ~on_handler_error:`Raise
      (*~backlog:(100)*)
      (Tcp.on_port 5000)
      (fun addr r _w ->
        print_endline (kBYEL ^ "[handling connection from " ^ Socket.Address.to_string addr ^ "]" ^ kNRM);
        let init = "" in
        let buffer = String.create buffer_size in
        read_inputs 0 init buffer r)
  in

  ignore (host_and_port : (Socket.Address.Inet.t, int) Tcp.Server.t Deferred.t);
  Deferred.never () ;;

                 
let command =
  Command.async
    ~summary:"Start a server"
    Command.Spec.(
      empty
    )
    (fun () ->
      print_endline ("[setting server]");
      start ());;


let () = Rpc_parallel.start_app command;;
