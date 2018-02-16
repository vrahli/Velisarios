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


Require Export Bvector.
Require Import List.
Require Import Arith.
Require Export PBFT.
Require Import hmacfcf.cAU.
Require Import fcf.Comp.
Require Import fcf.DistSem.
Require Import hmacfcf.hF.
Require Import fcf.FCF.  (* Definition Adv_wcr *)


Section PBFTcollision_resistant_wcr.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  (* Taken from VST/hmacfcf/HMAC_spec *)
  Variable a c p : nat.
  Definition b : nat := c + p.

  Definition Message := PBFTmsg.
  Variable splitAndPad : PBFTmsg -> list (Bvector b).

  (* The compression function *)
  Variable h : Bvector a -> Bvector b -> Bvector a.
  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Bvector a.
  Variable fpad : Bvector p.


  (********************
  Definition first_part (m : Message) := cons (splitAndPad m).
(*   Definition first_part_iv (m : PBFTmsg) := h iv (first_part m). *)
  Definition last_part  (m : PBFTmsg) := last (splitAndPad m).
  Definition app_fpad (x : Bvector ) : Bvector b :=
    (Vector.append x (fpad x)).

  Definition last_part_padded  (m : PBFTmsg) := h (Vector.append (last_part m) fpad).
*)

  (* The iteration of the compression function. *)
  Definition h_star (m : Message) :=
    fold_left h (splitAndPad m).

  Definition app_fpad (x : Bvector c) : Bvector b :=
    (Vector.append x (fpad x)).

  Definition h_star_pad k x :=
    app_fpad (h_star k x).


(*  Definition GHMAC k m :=
    let (k_Out, k_In) := splitVector c c k in
    h k_Out (app_fpad (h_star k_In m)).  *)

  (* why this is not compiling? *)
  Variable A : Comp (Message * Message).

  Require Import sha.HMAC_spec_abstract.
  Check (HMAC_Abstract.Message). (* this returns set *)
  Definition h_star_WCR
             (A : Comp (Message * Message))
             epsilon := true.


  XXXXXXXXXXXXXXXXXXXXXXXX

    Class PBFTmsgVector :=
    {
      msg2vector : PBFTmsg -> forall k, Bvector k;
    }.


  Require Import HMAC_spec_abstract.
  Print HMAC_Abstract.Message.

  Require Import sha.HMAC_spec_list.
  Require Import hmacfcf.HMAC_PRF.

  Check h_star.

  Check cAU.Adv_WCR.

  Definition h_star_WCR
             (A : OracleComp
                    (HMAC_Abstract.Message PARS.P)
                    (Bvector EQ.c)
                    bool)
             epsilon :=
    cAU.Adv_WCR
      (list_EqDec (Bvector_EqDec (HMAC_spec.b EQ.c EQ.p)))
      (Bvector_EqDec EQ.c)
      (h_star EQ.p M.h_v)
      ({ 0 , 1 }^ EQ.c)
      (Y EQ.fpad_v
         (au_F_A
            (A_GHMAC
               EQ.p
               Message_eqdec
               (HMAC_Abstract.wrappedSAP EQ.c EQ.p EQ.splitAndPad_v)
               A))) <= epsilon.


  Class PBFThash_axioms :=
    {
      create_hash_messages_collision_resistant :
        exists epsilon,
          cAU.Adv_WCR _ _  create_hash_messages (Rnd c) au_F_A
          <= epsilon;

      (*
      create_hash_messages_collision_resistant :
        exists epsilon,
          cAU.Adv_WCR _ _  (h_star_pad h fpad) ({ 0 , 1 }^c) (au_F_A A)) 
    <= epsilon;

*)
(*        forall msgs1 msgs2,
          create_hash_messages msgs1 = create_hash_messages msgs2
          -> msgs1 = msgs2;
*)

      create_hash_state_last_reply_collision_resistant :
        forall sm1 sm2 last1 last2,
          create_hash_state_last_reply sm1 last1 = create_hash_state_last_reply sm2 last2
          -> sm1 = sm2 /\ last1 = last2
    }.

  Context { pbft_hash_axioms : PBFThash_axioms }.

End PBFTcollision_resistant_wcr.
