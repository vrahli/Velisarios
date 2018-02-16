(*

  Copyright 2016 Luxembourg University
  Copyright 2017 Luxembourg University

  This file is part of Velisarios.

  Velisarios is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Velisarios is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with Velisarios.  If not, see <http://www.gnu.org/licenses/>.


  Authors: Vincent Rahli
           Ivana Vukotic

*)


Require Export Crypto.


Section AuthMsg.

  Context { pd  : @Data }.
  Context { pk  : @Key }.
  Context { pn  : @Node }.
  Context { pat : AuthTok }.
  Context { paf : @AuthFun pn pk pat pd }.

  (* from the data we should be able to extract some info like who send it *)
  Class DataAuth :=
    MkDataAuth
      {
        data_auth : name (* self *) -> data -> option name
      }.
  Context { pda : DataAuth }.

  (*
  Record AuthData :=
    MkAuthData
      {
        adData : Data;
        adToken : Token
      }.
   *)

  (* --- Replaced by a function on Data in EventOrdering
  (* function that given a message [m], returns a list of authenticated
     messages of the form {msg, mac}, such that {msg, macs}
     is contained in [m] and [mac] is in the Token vector [macs] *)
  Class GetContainedAuthMsgs :=
    { get_contained_auth_msgs : @msg m -> list auth_msg }.
   *)

  (*
  Definition verify_op (d : Data) (mac : Token) (kop : option key) : bool :=
    match kop with
    | Some k => verify d k mac
    | None => false
    end.

  Definition verify_auth_data (d : auth_data) (k : key) : bool :=
    verify (adData d) k (adToken d).

  Definition verify_auth_data_op (d : auth_data) (kop : option key) : bool :=
    match kop with
    | Some k => verify_auth_data d k
    | None => false
    end.
   *)

  Definition verify_authenticated_data_key (n : name) (m : AuthenticatedData) (k : receiving_key) : bool :=
    existsb (fun token => verify (am_data m) n k token) (am_auth m).

  Definition verify_authenticated_data_keys (n : name) (m : AuthenticatedData) (ks : receiving_keys) : bool :=
    existsb (verify_authenticated_data_key n m) ks.

  (*
  Definition verify_auth_msg_op (d : AuthMsg) (kop : option key) : bool :=
    match kop with
    | Some k => verify_auth_msg_key d k
    | None => false
    end.
   *)

  (*
  (* Extract the sender of some authenticated data.
   We return None can't say who sent the authenticated data (see data_auth).
   slf is the location at which we're doing that.
   We also return None if slf is not an internal name. *)
  Definition am_sender (slf : name) (m : AuthenticatedData) : option name :=
    data_auth slf (am_data m).
  (*  match slf with
  | IName n => data_auth n (am_data m)
  | EName _ => None
  end.*)
*)

  Definition verify_authenticated_data
             (slf  : name)
             (m    : AuthenticatedData)
             (keys : local_key_map) : bool :=
    match data_auth slf (am_data m) with
    | Some name => verify_authenticated_data_keys name m (lookup_receiving_keys keys name)
    | None => false
    end.

  Definition verify_one_auth_data
             (slf : name)
             (km  : local_key_map)
             (a   : AuthenticatedData) : bool :=
     verify_authenticated_data slf a km.

  Fixpoint verify_list_auth_data
           (slf : name)
           (km  : local_key_map)
           (l   : list AuthenticatedData) : bool :=
    match l with
    | [] => true
    | entry :: entries =>
      verify_one_auth_data slf km entry
      &&
      verify_list_auth_data slf km entries
    end.

(*
  Definition verify_keys_b (d : auth_data) (keys : local_key_map) : bool :=
    existsb (fun dk => verify_auth_data d (dk_key dk)) keys.

  Definition verify_keys (d : auth_data) (keys : local_key_map) : Prop :=
    verify_keys_b d keys = true.

  Definition verify_mac_b (d : Data) (mac : Token) (keys : local_key_map) : bool :=
    verify_keys_b (MkAuthData d mac) keys.

  Definition verify_macs_b (d : Data) (macs : Tokens) (keys : local_key_map) : bool :=
    existsb (fun mac => verify_mac_b d mac keys) macs.

  Definition verify_macs (d : Data) (macs : Tokens) (keys : local_key_map) : Prop :=
    verify_macs_b d macs keys = true.

  Definition verify_macs_with_name_b
             (d    : Data)
             (macs : Tokens)
             (keys : local_key_map)
             (n    : name) : bool :=
    match lookup_key keys n with
    | Some key =>
      existsb
        (fun mac => verify_auth_data (MkAuthData d mac) key)
        macs
    | None => false
    end.
 *)

End AuthMsg.
