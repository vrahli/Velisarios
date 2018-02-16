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


Require Export Node.


Section Crypto.

  Context { n  : @Node }.

  Class Key :=
    MkKey
      {
        sending_key   : Set;
        receiving_key : Set;
      }.
  Context { pk : Key }.

  Definition sending_keys   := list sending_key.
  Definition receiving_keys := list receiving_key.

  (* "directed sending key" *)
  Record DSKey :=
    MkDSKey
      {
        dsk_dst : list name;  (* destinations *)
        dsk_key : sending_key (* key *)
      }.

  (* "directed receiving key" *)
  Record DRKey :=
    MkDRKey
      {
        drk_dst : list name;    (* sources *)
        drk_key : receiving_key (* key *)
      }.

  Record local_key_map : Set :=
    MkLocalKeyMap
    {
      lkm_sending_keys   : list DSKey;
      lkm_receiving_keys : list DRKey;
    }.

  Definition key_map := name (* Src *) -> local_key_map.

(*  Definition lookup_dskey (km : local_key_map) (h : name) : option DSKey :=
    find
      (fun dk => if in_dec name_dec h (dsk_dst dk) then true else false)
      (lkm_sending_keys km).*)

  Definition lookup_dskeys (km : local_key_map) (h : name) : list DSKey :=
    filter
      (fun dk => if in_dec name_dec h (dsk_dst dk) then true else false)
      (lkm_sending_keys km).

(*  Definition lookup_sending_key (km : local_key_map) (h : name) : option sending_key :=
    option_map
      (fun dk => dsk_key dk)
      (lookup_dskey km h).*)

  Definition lookup_drkeys (km : local_key_map) (h : name) : list DRKey :=
    filter
      (fun dk => if in_dec name_dec h (drk_dst dk) then true else false)
      (lkm_receiving_keys km).

(*  Definition lookup_drkey (km : local_key_map) (h : name) : option DRKey :=
    find
      (fun dk => if in_dec name_dec h (drk_dst dk) then true else false)
      (lkm_receiving_keys km).*)

(*  Definition lookup_receiving_key (km : local_key_map) (h : name) : option receiving_key :=
    option_map
      (fun dk => drk_key dk)
      (lookup_drkey km h).*)

  Definition lookup_receiving_keys (km : local_key_map) (h : name) : list receiving_key :=
    map drk_key (lookup_drkeys km h).

  (*Definition has_sending_key (km : local_key_map) (h : name) : Prop :=
    lookup_dskeys km h <> [].*)

  (* This is used to state that we can at least try to verify messages from nodes *)
  Definition has_receiving_key (km : local_key_map) (h : name) : Prop :=
    lookup_drkeys km h <> [].

  (* This says that if the source has a key for sending messages to [n] then the
     destination also has that key.
     We use this in sent_byz to talk about leaked keys.
     ---The sending keys are the ones that are supposed to be private *)
  Definition got_key_for (n : name) (kmsrc kmdst : local_key_map) : Prop :=
    exists k,
      In k (map dsk_key (lookup_dskeys kmsrc n))
      /\ In k (map dsk_key (lookup_dskeys kmdst n)).

  Class AuthTok :=
    MkAuthTok
      {
        Token     :> Set;
        Token_dec : Deq Token;
      }.
  Context { authtok : AuthTok }.

  Definition Tokens := list Token.

  Lemma Tokens_dec : Deq Tokens.
  Proof.
    introv.
    apply list_eq_dec; auto.
    apply Token_dec.
  Qed.

  (* QUESTION: Shouldn't Data just be Msg? *)
  (* @Ivnote: message = data + MAC (i.e. crypto data ) *)
  Class Data := MkData { data : Set }.
  Context { pd : Data }.

  Class AuthFun :=
    MkAuthFun
      {
        create : data -> sending_keys -> Tokens;
        verify : data -> name -> receiving_key -> Token -> bool;
      }.
  Context { authfun : AuthFun }.

  (* we might want a more fine grain function that only uses the keys meant for the
     intended recipient *)
  Definition authenticate
             (d   : data)
(*             (dst : name)*)
             (km  : local_key_map) : Tokens :=
    create d (map dsk_key (lkm_sending_keys km)).

  Record AuthenticatedData :=
    MkAuthData
      {
        am_data   :> data;
        am_auth   : Tokens
      }.

End Crypto.
