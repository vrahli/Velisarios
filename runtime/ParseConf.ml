open Colors;;
open Prelude;;
open Connect;;
open Core;;
open Async;;


exception Bad_config_file of string ;;


(* returns: own info + info other replicas + info clients *)
let parse_line brep myid n s : node_nfo option * node_nfo list * node_nfo list =
  match Str.split (Str.regexp " +\\|:") s with
  | ["id";sid;"host";host;"port";sport;"private-key";privKey;"public-key";pubKey] ->
     let id   = int_of_string sid in
     let port = int_of_string sport in
     if brep && id = myid then
       let nfo = {id = I_node id; host = host; port = port; key = privKey} in
       (Some nfo, [], [])
     else
       let nfo = {id = I_node id; host = host; port = port; key = pubKey} in
       (None, [nfo], [])

  | ["client";sid;"host";host;"port";sport;"private-key";privKey;"public-key";pubKey] ->
     let id   = int_of_string sid in
     let port = int_of_string sport in
     if (not brep) && id = myid then
       let nfo = {id = E_node id; host = host; port = port; key = privKey} in
       (Some nfo, [], [])
     else
       let nfo = {id = E_node id; host = host; port = port; key = pubKey} in
       (None, [], [nfo])

  | [] -> (None, [], [])

  | l -> raise (Bad_config_file ("wrong number of components (" ^ string_of_int (List.length l) ^ "), line " ^ string_of_int n))


let first_option opt1 opt2 =
  match opt1, opt2 with
  | Some x, _ -> Some x
  | None, _ -> opt2


(* true to parse the file as a replica/false to parse it as a client *)
let rec parse_conf file brep myid n c =
  Reader.read_line c
  >>= function
  | `Eof -> (print_endline (kRED ^ "[EOF(" ^ file ^ ")]" ^ kNRM); Deferred.return (None, [], []))
  | `Ok s ->
     let  (own1,reps1,clients1) = parse_line brep myid n s in
     parse_conf file brep myid (n + 1) c
     >>= fun (own2,reps2,clients2) ->
     Deferred.return (first_option own1 own2, reps1 @ reps2, clients1 @ clients2)

let make_own myid opt =
  match opt with
  | Some nfo -> nfo
  | None -> raise (Bad_config_file "I couldn't get my own data")
