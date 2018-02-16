open Colors
open Core
open Async


type key =
  | SymmK of Cstruct.t


let mk_secret n m =
  if n <= m then
    string_of_int n ^ "-" ^ string_of_int m
  else
    string_of_int m ^ "-" ^ string_of_int n

let export_key (printb : bool) (symkeyfile : string) (n : int) (m : int) : unit Deferred.t =
  let () = Nocrypto_entropy_unix.initialize () in

  let secret = mk_secret n m in
  let key : Cstruct.t = Cstruct.of_string secret in
  let sym_key = Sexplib.Sexp.to_string (Cstruct.sexp_of_t key) in

  Writer.open_file ~append:(false) symkeyfile
  >>= fun symw ->
  let _ = Writer.write symw (sym_key ^ "\n") in
  let _ =
    if printb
    then print_endline ("[symmetric key exported to " ^ symkeyfile ^ ": " ^ sym_key ^ "]")
    else print_endline ("[symmetric key exported to " ^ symkeyfile ^ "]") in

  Deferred.return ()


let read_symmetric_key (symkeyfile : string) : Cstruct.t =
  print_endline ("[reading symmetric key from " ^ symkeyfile ^ "]");
  Cstruct.t_of_sexp (Sexplib.Sexp.load_sexp symkeyfile)


let read_key symkeyfile : unit Deferred.t =
  let sym : Cstruct.t = read_symmetric_key symkeyfile in
  let sym_key = Sexplib.Sexp.to_string (Cstruct.sexp_of_t sym) in
  print_endline ("[symmetric key read from " ^ symkeyfile ^ ": " ^ sym_key ^ "]");
  Deferred.return ()


let lookup_replica_key (slf : Obj.t(*rep*)) (i : Obj.t(*rep*)) : Cstruct.t =
  try
    read_symmetric_key ("symmetric_key" ^ string_of_int (Obj.magic slf) ^ "-" ^ string_of_int (Obj.magic i))
  with
  | _ -> read_symmetric_key ("somekeys/symmetric_key" ^ string_of_int (Obj.magic slf) ^ "-" ^ string_of_int (Obj.magic i))

let lookup_client_key (slf : Obj.t(*rep*)) (c : Obj.t(*client*)) : Cstruct.t =
  try
    read_symmetric_key ("symmetric_key_client" ^ string_of_int (Obj.magic slf) ^ "-" ^ string_of_int (Obj.magic c))
  with
  | _ -> read_symmetric_key ("somekeys/symmetric_key_client" ^ string_of_int (Obj.magic slf) ^ "-" ^ string_of_int (Obj.magic c))


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


(*let sign (symkeyfile : string) (i : string) : unit =
  let () = Nocrypto_entropy_unix.initialize () in

  let sym  = read_symmetric_key symkeyfile in
  let msg  = Cstruct.of_string i in
  let hmac = Nocrypto.Hash.SHA256.hmac sym msg in

  let hash = Nocrypto.Hash.SHA256.digest msg in

  print_endline ("[verified-with-padding? " ^ string_of_bool (hash = enc) ^ "]");
  print_endline ("[verified-without-padding? " ^ string_of_bool (remove_left_padding (Cstruct.to_string hash) = remove_left_padding (Cstruct.to_string enc)) ^ "]");
  print_endline (kBLU ^ "[msg-:" ^ Cstruct.to_string msg  ^ "]" ^ kNRM);
  print_endline (kRED ^ "[hash:" ^ Cstruct.to_string hash ^ "]" ^ kNRM);
  print_endline (kGRN ^ "[dec-:" ^ Cstruct.to_string dec  ^ "]" ^ kNRM);
  print_endline (kRED ^ "[enc-:" ^ Cstruct.to_string enc  ^ "]" ^ kNRM);
  ()*)



let verify_one (o : Obj.t) (n : Obj.t) (sym : Cstruct.t) (mac : Cstruct.t) : bool =
  (*print_endline (kCYN ^ "[verifying signature]" ^ kNRM);*)
  (*let pub_key = Sexplib.Sexp.to_string (Nocrypto.Rsa.sexp_of_pub pub) in
  print_endline ("[using public key:" ^ pub_key ^ "]");*)

  let smsg : string = Marshal.to_string o [] in
  (*print_endline ("[message: " ^ smsg ^ "]");*)
  let msg  = Cstruct.of_string smsg in
  let hmac = Nocrypto.Hash.SHA256.hmac sym msg in

  (*print_endline (kCYN ^ "[comparing 2 macs]" ^ kNRM);*)
  let b : bool = remove_left_padding (Cstruct.to_string hmac) = remove_left_padding (Cstruct.to_string mac) in
  (
    if b then ()
    else
      (
        ()
      (*print_endline (kBRED ^ "could not verify signature" ^ kNRM)*)

      (*;

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


let sign_one (o : Obj.t) (sym : Cstruct.t) : Cstruct.t =
  let smsg = Marshal.to_string o [] in
  let msg  = Cstruct.of_string smsg in
  let hmac = Nocrypto.Hash.SHA256.hmac sym msg in
  hmac


let sign_list (o : Obj.t) (syms : Cstruct.t list) : Cstruct.t list =
  Nocrypto_entropy_unix.initialize ();
  List.map syms (sign_one o)
