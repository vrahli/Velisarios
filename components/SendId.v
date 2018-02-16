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


Section SendId.

Context { pn     : @Node }.
Context { pm     : @Msg }.
Context { pk     : @Key }.

(* why None ??? *)
(* To send a message that contains our id.
     This state machine outputs some information and halts right away. *)
Definition SendId {I O : Type} (F : name -> O) : NStateMachine _ I O :=
  fun slf => mkSM (fun _ _ => (None, F slf)) tt.


Lemma state_sm_on_event_SendId_none :
  forall {O} (F : name -> list O) (n : name) (eo : EventOrdering) (e : Event),
    state_sm_on_event (SendId F n) e = None.
Proof.
  intros O F nm eo.
  induction e as [e ind] using predHappenedBeforeInd; introv; simpl.
  rewrite state_sm_on_event_unroll.
  destruct (dec_isFirst e) as [d|d]; simpl; auto.
  rewrite ind; auto.
  apply local_pred_is_direct_pred; auto.
Qed.

(* QUESTION: Do we need a similar lemma when F doesn't output lists? *)
Lemma SendId_list_output_iff :
  forall {O} (F : name -> list O) (o : O) (n : name) (eo : EventOrdering) (e : Event),
    In o (loutput_sm_on_event (SendId F n) e)
    <-> (In o (F n) /\ isFirst e).
Proof.
  introv; split; intro h.

  - rewrite loutput_sm_on_event_unroll in h.
    destruct (dec_isFirst e) as [d|d]; simpl in *; auto.

    apply in_olist2list in h; exrepnd.
    remember (state_sm_on_event (SendId F n) (local_pred e)) as sop.
    symmetry in Heqsop; destruct sop; simpl in *; ginv.
    rewrite state_sm_on_event_SendId_none in Heqsop; ginv.

  - repnd.
    rewrite loutput_sm_on_event_unroll.
    destruct (dec_isFirst e) as [d|d]; simpl; tcsp.
Qed.

End SendId.
