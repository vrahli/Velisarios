open Colors
open Core
open Async


type key =
  | PrivK of Nocrypto.Rsa.priv
  | PubK of Nocrypto.Rsa.pub


let export_key printb privatekeyfile publickeyfile : unit Deferred.t =
  let () = Nocrypto_entropy_unix.initialize () in
  (*let cs = Nocrypto.Rng.generate 13 in
  let g = Nocrypto.Rng.(create ~seed:cs (module Nocrypto.Rng.Generators.Fortuna)) in*)
  let priv : Nocrypto.Rsa.priv = Nocrypto.Rsa.generate ~g:(!Nocrypto.Rng.generator) 2048 in
  let pub : Nocrypto.Rsa.pub = Nocrypto.Rsa.pub_of_priv priv in
  let priv_key = Sexplib.Sexp.to_string (Nocrypto.Rsa.sexp_of_priv priv) in
  let pub_key = Sexplib.Sexp.to_string (Nocrypto.Rsa.sexp_of_pub pub) in

  Writer.open_file ~append:(false) privatekeyfile
  >>= fun privw ->
  let _ = Writer.write privw (priv_key ^ "\n") in
  let _ =
    if printb
    then print_endline ("[private key exported to " ^ privatekeyfile ^ ": " ^ priv_key ^ "]")
    else print_endline ("[private key exported to " ^ privatekeyfile ^ "]") in

  Writer.open_file ~append:(false) publickeyfile
  >>= fun pubw ->
  let _ = Writer.write pubw (pub_key ^ "\n") in
  let _ =
    if printb
    then print_endline ("[public key exported to " ^ publickeyfile ^ ": " ^ pub_key ^ "]")
    else print_endline ("[public key exported to " ^ publickeyfile ^ "]") in

  Deferred.return ()


let read_private_key (privatekey : string) : Nocrypto.Rsa.priv =
  print_endline ("[reading private key from " ^ privatekey ^ "]");
  Nocrypto.Rsa.priv_of_sexp (Sexplib.Sexp.load_sexp privatekey)

let read_public_key  (publickey  : string) : Nocrypto.Rsa.pub  =
  print_endline ("[reading public key from " ^ publickey ^ "]");
  Nocrypto.Rsa.pub_of_sexp (Sexplib.Sexp.load_sexp publickey)


let read_key privatekey publickey : unit Deferred.t =
  let priv : Nocrypto.Rsa.priv = read_private_key privatekey in
  let pub  : Nocrypto.Rsa.pub  = read_public_key publickey in
  let priv_key = Sexplib.Sexp.to_string (Nocrypto.Rsa.sexp_of_priv priv) in
  let pub_key = Sexplib.Sexp.to_string (Nocrypto.Rsa.sexp_of_pub pub) in
  print_endline ("[private key read from " ^ privatekey ^ ": " ^ priv_key ^ "]");
  print_endline ("[public key read from " ^ publickey ^ ": " ^ pub_key ^ "]");
  Deferred.return ()


let lookup_replica_sending_key (i : Obj.t(*rep*)) : Nocrypto.Rsa.priv =
  try
    read_private_key ("private_key" ^ string_of_int (Obj.magic i))
  with
  | _ -> read_private_key ("somekeys/private_key" ^ string_of_int (Obj.magic i))

let lookup_client_sending_key (c : Obj.t(*client*)) : Nocrypto.Rsa.priv =
  try
    read_private_key ("private_key_client" ^ string_of_int (Obj.magic c))
  with
  | _ -> read_private_key ("somekeys/private_key_client" ^ string_of_int (Obj.magic c))

let lookup_replica_receiving_key (i : Obj.t(*rep*)) : Nocrypto.Rsa.pub =
  try
    read_public_key ("public_key" ^ string_of_int (Obj.magic i))
  with
  | _ -> read_public_key ("somekeys/public_key" ^ string_of_int (Obj.magic i))

let lookup_client_receiving_key (c : Obj.t(*client*)) : Nocrypto.Rsa.pub =
  try
    read_public_key ("public_key_client" ^ string_of_int (Obj.magic c))
  with
  | _ -> read_public_key ("somekeys/public_key_client" ^ string_of_int (Obj.magic c))


let rec compare_strings (s1 : string) (s2 : string) : string =
  if (0 < String.length s1) && (0 < String.length s2) then
    let a = String.sub s1 0 1 in
    let b = String.sub s2 0 1 in
    "(" ^ a ^ "|" ^ b ^ ")"
    ^ (if a = b then "+" else "-")
    ^ compare_strings (String.sub s1 1 (String.length s1 - 1)) (String.sub s2 1 (String.length s2 - 1))
  else "{" ^ s1 ^ "|" ^ s2 ^ "}"


let rec remove_left_padding (s : string) : string =
  if 0 < String.length s then
    if String.sub s 0 1 = "\x00"
    then remove_left_padding (String.sub s 1 (String.length s - 1))
    else s
  else s


let sign (privatekey : string) (publickey : string) (i : string) : unit =
  let () = Nocrypto_entropy_unix.initialize () in

  let priv = read_private_key privatekey in
  let pub  = read_public_key publickey in

  let msg  = Cstruct.of_string i in
  let hash = Nocrypto.Hash.SHA256.digest msg in
  let dec  = Nocrypto.Rsa.decrypt priv hash in
  let enc  = Nocrypto.Rsa.encrypt pub dec in

  print_endline ("[verified-with-padding? " ^ string_of_bool (hash = enc) ^ "]");
  print_endline ("[verified-without-padding? " ^ string_of_bool (remove_left_padding (Cstruct.to_string hash) = remove_left_padding (Cstruct.to_string enc)) ^ "]");
  print_endline (kBLU ^ "[msg-:" ^ Cstruct.to_string msg  ^ "]" ^ kNRM);
  print_endline (kRED ^ "[hash:" ^ Cstruct.to_string hash ^ "]" ^ kNRM);
  print_endline (kGRN ^ "[dec-:" ^ Cstruct.to_string dec  ^ "]" ^ kNRM);
  print_endline (kRED ^ "[enc-:" ^ Cstruct.to_string enc  ^ "]" ^ kNRM);
  ()



let verify_one (o : Obj.t) (n : Obj.t) (pub : Nocrypto.Rsa.pub) (dec : Cstruct.t) : bool =
  print_endline (kCYN ^ "[verifying signature]" ^ kNRM);
(*  let pub_key = Sexplib.Sexp.to_string (Nocrypto.Rsa.sexp_of_pub pub) in
  print_endline ("[using public key:" ^ pub_key ^ "]");*)

  let smsg : string = Marshal.to_string o [] in
  (*print_endline ("[message: " ^ smsg ^ "]");*)
  let msg  = Cstruct.of_string smsg in
  let hash = Nocrypto.Hash.SHA256.digest msg in
  (*print_endline ("[hash:" ^ Cstruct.to_string hash ^ "]");*)
  let enc  = Nocrypto.Rsa.encrypt pub dec in
  (*let b : bool = hash = enc in*)
  let b : bool = remove_left_padding (Cstruct.to_string hash) = remove_left_padding (Cstruct.to_string enc) in
  (
    if b then ()
    else
      (
        print_endline (kBRED ^ "could not verify signature" ^ kNRM)(*;

        print_endline ("[redoing the computation]");
        print_endline ("[getting private key of sender]");
        let priv = lookup_replica_sending_key (Obj.magic 1) in
        print_endline ("[signing as if it were the sender]");
        let new_dec = Nocrypto.Rsa.decrypt priv hash in
        print_endline ("[verifying new signature]");
        let new_enc = Nocrypto.Rsa.encrypt pub new_dec in
        let b : bool = remove_left_padding (Cstruct.to_string hash) = remove_left_padding (Cstruct.to_string new_enc) in
        if b then print_endline ("[managed to redo the computation]")
        else print_endline ("[could not redo the computation]")*)
      )
  );

  (*  print_endline (kMAG ^ "[verified signature: " ^ string_of_bool b ^ "]" ^ kNRM);
  print_endline (kBLU ^ "[1: " ^ Cstruct.to_string enc  ^ "]" ^ kNRM);
  print_endline (kYEL ^ "[2: " ^ Cstruct.to_string hash ^ "]" ^ kNRM);*)
  b


let sign_one (o : Obj.t) (priv : Nocrypto.Rsa.priv) : Cstruct.t =
  (*print_endline (kCYN ^ "[signing message]" ^ kNRM);*)
  let smsg = Marshal.to_string o [] in
  (*print_endline ("[message: " ^ smsg ^ "]");*)
  let msg  = Cstruct.of_string smsg in
  let hash = Nocrypto.Hash.SHA256.digest msg in
  (*print_endline ("[hash:" ^ Cstruct.to_string hash ^ "]");*)
  let dec  = Nocrypto.Rsa.decrypt priv hash in
  (*print_endline (kMAG ^ "[signed message]" ^ kNRM);*)
  dec


let sign_list (o : Obj.t) (privs : Nocrypto.Rsa.priv list) : Cstruct.t list =
  Nocrypto_entropy_unix.initialize ();
  List.map privs (sign_one o)
