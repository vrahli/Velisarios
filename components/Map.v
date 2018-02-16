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


Require Import QArith_base.
Require Import tactics2.
Require Import list_util.
Require Import Eqdep_dec.


Require Import Node.
Require Import Msg.
Require Import Crypto.
Require Import EventOrdering.
Require Import Process.
Require Import PairState.


Section Map.

Context { pn     : @Node }.
Context { pm     : @Msg }.
Context { pk     : @Key }.

Definition mapSM_upd {SX I T U : Type}
           (f : T -> U)
           (X : Update SX I T) : Update SX I U :=
  fun state i =>
    match X state i with
    | (Some s, t) => (Some s, f t)
    | (None, t) => (None, f t)
    end.

Definition mapSM {SX I T U : Type}
           (f : T -> U)
           (X : StateMachine SX I T)
  : StateMachine SX I U :=
  mkSM (mapSM_upd f (sm_update X)) (sm_state X).

Definition nmapSM {SX I T U : Type}
           (f : name -> T -> U)
           (X : NStateMachine SX I T)
  : NStateMachine SX I U := fun n => mapSM (f n) (X n).

Lemma mapSM_state_iff :
  forall {SX T U}
         (f  : T -> U)
         (X  : StateMachine SX msg T)
         (eo : EventOrdering)
         (e  : Event),
    state_sm_on_event (mapSM f X) e
    = state_sm_on_event X e.
Proof.
  intros SX T U f X eo.
  induction e as [e ind] using predHappenedBeforeInd; introv; simpl.
  rewrite (state_sm_on_event_unroll (mapSM _ _)).
  rewrite (state_sm_on_event_unroll X).
  destruct (dec_isFirst e) as [d|d]; simpl in *.

  - unfold mapSM_upd; simpl.
    dest_cases w; symmetry in Heqw; destruct w0; simpl in *; auto.

  - rewrite ind;[|apply local_pred_is_direct_pred;auto].
    unfold mapSM_upd; simpl.
    destruct (state_sm_on_event X (local_pred e)); simpl; auto.
    dest_cases w; symmetry in Heqw; destruct w0; simpl; auto.
Qed.

Lemma mapSM_output_iff :
  forall {SX T U}
         (f  : T -> U)
         (X  : StateMachine SX msg T)
         (eo : EventOrdering)
         (e  : Event),
    output_sm_on_event (mapSM f X) e
    = option_map f (output_sm_on_event X e).
Proof.
  introv.
  rewrite (output_sm_on_event_unroll (mapSM _ _)).
  rewrite (output_sm_on_event_unroll X).
  destruct (dec_isFirst e) as [d|d]; simpl in *.

  - unfold mapSM_upd; simpl.
    dest_cases w; symmetry in Heqw; destruct w0; simpl in *; auto.

  - rewrite mapSM_state_iff.
    destruct (state_sm_on_event X (local_pred e)); simpl; auto.
    unfold mapSM_upd; simpl.
    dest_cases w; symmetry in Heqw; destruct w0; simpl; auto.
Qed.

(* same as mapSM_output_iff in the case where the state machine returns a list *)
Lemma mapSM_list_output_iff :
  forall {SX T U}
         (f  : T -> list U)
         (X  : StateMachine SX msg T)
         (eo : EventOrdering)
         (e  : Event)
         (u  : U),
    In u (loutput_sm_on_event (mapSM f X) e)
    <->
    In u (olist2list (option_map f (output_sm_on_event X e))).
Proof.
  introv.
  unfold loutput_sm_on_event.
  rewrite mapSM_output_iff; tcsp.
Qed.

End Map.
