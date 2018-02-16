let rec combine_objects (l : Obj.t list) : string =
  match l with
  | [] -> ""
  | o :: os ->
     let s1 = Marshal.to_string o [] in
     let s2 = combine_objects os in
     s1 ^ s2


let create_hash_objects (l : Obj.t list) : Cstruct.t =
  let s = combine_objects l in
  let c = Cstruct.of_string s in
  Nocrypto.Hash.SHA256.digest c

let verify_hash_objects (l : Obj.t list) (c : Cstruct.t) : bool =
  let c' = create_hash_objects l in
  c = c'

let create_hash_pair (o1 : Obj.t) (o2 : Obj.t) : Cstruct.t =
  create_hash_objects [o1;o2]

let verify_hash_pair (o1 : Obj.t) (o2 : Obj.t) (c : Cstruct.t) : bool =
  verify_hash_objects [o1;o2] c
