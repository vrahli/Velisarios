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


Section Parallel.

Context { pn     : @Node }.
Context { pm     : @Msg }.
Context { pk     : @Key }.

(* transition form SX to sx *)
Definition parallel_upd {SX SY I O : Type}
           (X : Update SX I (list O))
           (Y : Update SY I (list O)) : Update (pstate SX SY) I (list O) :=
  fun state i =>
    match state with
    | pstate_two sx sy =>
      let (sx', outx) := X sx i in
      let (sy', outy) := Y sy i in
      (opt_states2pstate sx' sy', outx ++ outy)
    | pstate_left sx =>
      let (sx', outx) := X sx i in
      (option_map (fun x => pstate_left x) sx', outx)
    | pstate_right sy =>
      let (sy', outy) := Y sy i in
      (option_map (fun x => pstate_right x) sy', outy)
    end.

Definition parallel {SX SY I O : Type}
           (X : StateMachine SX I (list O))
           (Y : StateMachine SY I (list O))
  : StateMachine (pstate SX SY) I (list O) :=
  mkSM (parallel_upd (sm_update X) (sm_update Y))
       (pstate_two (sm_state X) (sm_state Y)).

Definition nparallel {SX SY I O : Type}
           (X : NStateMachine SX I (list O))
           (Y : NStateMachine SY I (list O))
  : NStateMachine (pstate SX SY) I (list O) :=
  fun slf => parallel (X slf) (Y slf).

Notation "a [||] b" := (nparallel a b) (at level 100).

Lemma state_sm_on_event_parallel_some_pstate_two_implies :
  forall {SX SY O}
         (X  : StateMachine SX msg (list O))
         (Y  : StateMachine SY msg (list O))
         (eo : EventOrdering)
         (e  : Event)
         (l  : SX)
         (r  : SY),
    state_sm_on_event (parallel X Y) e = Some (pstate_two l r)
    -> state_sm_on_event X e = Some l
       /\ state_sm_on_event Y e = Some r.
Proof.
  intros SX SY O X Y eo.
  induction e as [e ind] using predHappenedBeforeInd; introv h.
  rewrite state_sm_on_event_unroll in h.
  destruct (dec_isFirst e) as [d1|d1]; simpl in *.

  - dest_cases w; symmetry in Heqw; simpl in *.
    dest_cases y; symmetry in Heqy; simpl in *.
    destruct w0; simpl in *; ginv.

    + destruct y0; simpl in *; ginv.

      rewrite (state_sm_on_event_unroll X).
      rewrite (state_sm_on_event_unroll Y).
      destruct (dec_isFirst e); tcsp; GC.
      allrw; simpl; tcsp.

    + destruct y0; simpl in *; ginv.

  - remember (state_sm_on_event (parallel X Y) (local_pred e)) as sop; symmetry in Heqsop.
    destruct sop; simpl in *; ginv.
    destruct p; simpl in *; ginv.

    + dest_cases w; symmetry in Heqw; simpl in *; ginv.
      dest_cases y; symmetry in Heqy; simpl in *; ginv.
      destruct w0; simpl in *; ginv.

      * destruct y0; simpl in *; ginv.
        rewrite (state_sm_on_event_unroll X).
        rewrite (state_sm_on_event_unroll Y).
        destruct (dec_isFirst e); tcsp; GC.
        apply ind in Heqsop; auto;[|apply local_pred_is_direct_pred; auto].
        repnd; repeat (allrw; simpl; tcsp).

      * destruct y0; simpl in *; ginv.

    + dest_cases w; symmetry in Heqw; simpl in *; ginv.
      destruct w0; simpl in *; ginv.

    + dest_cases w; symmetry in Heqw; simpl in *; ginv.
      destruct w0; simpl in *; ginv.
Qed.

Lemma state_sm_on_event_parallel_some_pstate_left_implies :
  forall {SX SY O}
         (X  : StateMachine SX msg (list O))
         (Y  : StateMachine SY msg (list O))
         (eo : EventOrdering)
         (e  : Event)
         (l  : SX),
    state_sm_on_event (parallel X Y) e = Some (pstate_left l)
    -> state_sm_on_event X e = Some l
       /\ state_sm_on_event Y e = None.
Proof.
  intros SX SY O X Y eo.
  induction e as [e ind] using predHappenedBeforeInd; introv h.
  rewrite state_sm_on_event_unroll in h.
  destruct (dec_isFirst e) as [d1|d1]; simpl in *.

  - dest_cases w; symmetry in Heqw; simpl in *.
    dest_cases y; symmetry in Heqy; simpl in *.
    destruct w0; simpl in *; ginv.

    + destruct y0; simpl in *; ginv.

      rewrite (state_sm_on_event_unroll X).
      rewrite (state_sm_on_event_unroll Y).
      destruct (dec_isFirst e); tcsp; GC.
      allrw; simpl; tcsp.

    + destruct y0; simpl in *; ginv.

  - remember (state_sm_on_event (parallel X Y) (local_pred e)) as sop; symmetry in Heqsop.
    destruct sop; simpl in *; ginv.
    destruct p; simpl in *; ginv.

    + apply state_sm_on_event_parallel_some_pstate_two_implies in Heqsop.
      exrepnd.
      dest_cases w; symmetry in Heqw; simpl in *; ginv.
      dest_cases y; symmetry in Heqy; simpl in *; ginv.
      destruct w0; simpl in *; ginv.

      * destruct y0; simpl in *; ginv.
        rewrite (state_sm_on_event_unroll X).
        rewrite (state_sm_on_event_unroll Y).
        destruct (dec_isFirst e); tcsp; GC.
        repnd; repeat (allrw; simpl; tcsp).

      * destruct y0; simpl in *; ginv.

    + dest_cases w; symmetry in Heqw; simpl in *; ginv.
      destruct w0; simpl in *; ginv.

      * apply ind in Heqsop; auto;[|apply local_pred_is_direct_pred; auto].
        repnd.
        rewrite (state_sm_on_event_unroll X).
        rewrite (state_sm_on_event_unroll Y).
        destruct (dec_isFirst e); tcsp.
        repeat(allrw; simpl in *; tcsp).

    + dest_cases w; symmetry in Heqw; simpl in *; ginv.
      destruct w0; simpl in *; ginv.
Qed.

Lemma state_sm_on_event_parallel_some_pstate_right_implies :
  forall {SX SY O}
         (X  : StateMachine SX msg (list O))
         (Y  : StateMachine SY msg (list O))
         (eo : EventOrdering)
         (e  : Event)
         (r  : SY),
    state_sm_on_event (parallel X Y) e = Some (pstate_right r)
    -> state_sm_on_event X e = None
       /\ state_sm_on_event Y e = Some r.
Proof.
  intros SX SY O X Y eo.
  induction e as [e ind] using predHappenedBeforeInd; introv h.
  rewrite state_sm_on_event_unroll in h.
  destruct (dec_isFirst e) as [d1|d1]; simpl in *.

  - dest_cases w; symmetry in Heqw; simpl in *.
    dest_cases y; symmetry in Heqy; simpl in *.
    destruct y0; simpl in *; ginv.

    + destruct w0; simpl in *; ginv.
      rewrite (state_sm_on_event_unroll X).
      rewrite (state_sm_on_event_unroll Y).
      destruct (dec_isFirst e); tcsp; GC.
      allrw; simpl; tcsp.

    + destruct w0; simpl in *; ginv.

  - remember (state_sm_on_event (parallel X Y) (local_pred e)) as sop; symmetry in Heqsop.
    destruct sop; simpl in *; ginv.
    destruct p; simpl in *; ginv.

    + apply state_sm_on_event_parallel_some_pstate_two_implies in Heqsop.
      exrepnd.
      dest_cases w; symmetry in Heqw; simpl in *; ginv.
      dest_cases y; symmetry in Heqy; simpl in *; ginv.
      destruct y0; simpl in *; ginv.

      * destruct w0; simpl in *; ginv.
        rewrite (state_sm_on_event_unroll X).
        rewrite (state_sm_on_event_unroll Y).
        destruct (dec_isFirst e); tcsp; GC.
        repnd; repeat (allrw; simpl; tcsp).

      * destruct w0; simpl in *; ginv.

    + dest_cases w; symmetry in Heqw; simpl in *; ginv.
      destruct w0; simpl in *; ginv.

    + dest_cases w; symmetry in Heqw; simpl in *; ginv.
      destruct w0; simpl in *; ginv.

      * apply ind in Heqsop ; auto;[|apply local_pred_is_direct_pred; auto]; repnd.
        rewrite (state_sm_on_event_unroll X).
        rewrite (state_sm_on_event_unroll Y).
        destruct (dec_isFirst e); tcsp.
        repeat(allrw; simpl in *; tcsp).
Qed.

Lemma state_sm_on_event_parallel_none_implies :
  forall {SX SY O}
         (X  : StateMachine SX msg (list O))
         (Y  : StateMachine SY msg (list O))
         (eo : EventOrdering)
         (e  : Event),
    state_sm_on_event (parallel X Y) e = None
    -> state_sm_on_event X e = None
       /\ state_sm_on_event Y e = None.
Proof.
  intros SX SY O X Y eo.
  induction e as [e ind] using predHappenedBeforeInd; introv h.
  rewrite state_sm_on_event_unroll in h.
  destruct (dec_isFirst e) as [d1|d1]; simpl in *.

  - dest_cases w; symmetry in Heqw; simpl in *.
    dest_cases y; symmetry in Heqy; simpl in *.
    destruct y0; simpl in *; ginv.

    + destruct w0; simpl in *; ginv.

    + destruct w0; simpl in *; ginv.
      rewrite (state_sm_on_event_unroll X).
      rewrite (state_sm_on_event_unroll Y).
      destruct (dec_isFirst e); tcsp; GC.
      allrw; simpl; tcsp.

  - remember (state_sm_on_event (parallel X Y) (local_pred e)) as sop; symmetry in Heqsop.
    destruct sop; simpl in *; ginv.

    {
      destruct p; simpl in *; ginv.

      - apply state_sm_on_event_parallel_some_pstate_two_implies in Heqsop; repnd.

        dest_cases w; symmetry in Heqw; simpl in *; ginv.
        dest_cases y; symmetry in Heqy; simpl in *; ginv.
        destruct y0; simpl in *; ginv.

        + destruct w0; simpl in *; ginv.

        + destruct w0; simpl in *; ginv.
          rewrite (state_sm_on_event_unroll X).
          rewrite (state_sm_on_event_unroll Y).
          destruct (dec_isFirst e); tcsp; GC.
          repnd; repeat (allrw; simpl; tcsp).

      - dest_cases w; symmetry in Heqw; simpl in *; ginv.
        destruct w0; simpl in *; ginv.
        apply state_sm_on_event_parallel_some_pstate_left_implies in Heqsop; repnd.
        rewrite (state_sm_on_event_unroll X).
        rewrite (state_sm_on_event_unroll Y).
        destruct (dec_isFirst e); tcsp; GC.
        repeat (allrw; simpl; dands; auto).

      - dest_cases w; symmetry in Heqw; simpl in *; ginv.
        destruct w0; simpl in *; ginv.
        apply state_sm_on_event_parallel_some_pstate_right_implies in Heqsop; repnd.
        rewrite (state_sm_on_event_unroll X).
        rewrite (state_sm_on_event_unroll Y).
        destruct (dec_isFirst e); tcsp; GC.
        repeat (allrw; simpl; dands; auto).
    }

    {
      apply ind in Heqsop;[|apply local_pred_is_direct_pred; auto]; repnd.
      rewrite (state_sm_on_event_unroll X).
      rewrite (state_sm_on_event_unroll Y).
      destruct (dec_isFirst e); tcsp.
      repeat(allrw; simpl in *; tcsp).
    }
Qed.

Lemma parallel_output_iff :
  forall {SX SY O}
         (X  : StateMachine SX msg (list O))
         (Y  : StateMachine SY msg (list O))
         (eo : EventOrdering)
         (e  : Event)
         (x  : O),
    In x (loutput_sm_on_event (parallel X Y) e)
    <->
    (
      In x (loutput_sm_on_event X e)
      \/
      In x (loutput_sm_on_event Y e)
    ).
Proof.
  introv; split; intro h.

  {
    rewrite loutput_sm_on_event_unroll in h.
    destruct (dec_isFirst e) as [d|d]; simpl in *.

    {
      dest_cases w; symmetry in Heqw; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *.
      rewrite in_app_iff in h.
      repndors;[left|right].

      - rewrite loutput_sm_on_event_unroll.
        destruct (dec_isFirst e); tcsp; GC.
        allrw; simpl; auto.

      - rewrite loutput_sm_on_event_unroll.
        destruct (dec_isFirst e); tcsp; GC.
        allrw; simpl; auto.
    }

    {
      remember (state_sm_on_event (parallel X Y) (local_pred e)) as sop; symmetry in Heqsop.
      destruct sop; simpl in *; ginv; tcsp.

      destruct p; simpl in *; tcsp.

      + dest_cases w; symmetry in Heqw; simpl in *.
        dest_cases y; symmetry in Heqy; simpl in *.
        apply in_app_iff in h; repndors;[left|right].

        * rewrite loutput_sm_on_event_unroll.
          destruct (dec_isFirst e); tcsp; GC.
          apply state_sm_on_event_parallel_some_pstate_two_implies in Heqsop; repnd.
          repeat (allrw; simpl; tcsp).

        * rewrite loutput_sm_on_event_unroll.
          destruct (dec_isFirst e); tcsp; GC.
          apply state_sm_on_event_parallel_some_pstate_two_implies in Heqsop; repnd.
          repeat (allrw; simpl; tcsp).

      + dest_cases w; symmetry in Heqw; simpl in *.
        apply state_sm_on_event_parallel_some_pstate_left_implies in Heqsop; repnd.
        left.
        rewrite loutput_sm_on_event_unroll.
        destruct (dec_isFirst e); tcsp; GC.
        repeat (allrw; simpl; tcsp).

      + dest_cases w; symmetry in Heqw; simpl in *.
        apply state_sm_on_event_parallel_some_pstate_right_implies in Heqsop; repnd.
        right.
        rewrite loutput_sm_on_event_unroll.
        destruct (dec_isFirst e); tcsp; GC.
        repeat (allrw; simpl; tcsp).
    }
  }

  {
    rewrite loutput_sm_on_event_unroll.
    destruct (dec_isFirst e) as [d|d]; simpl in *.

    - dest_cases w; symmetry in Heqw; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *.
      apply in_app_iff.
      repndors.

      + rewrite loutput_sm_on_event_unroll in h.
        destruct (dec_isFirst e); simpl in *; tcsp; GC.
        rewrite Heqw in h; simpl in h; tcsp.

      + rewrite loutput_sm_on_event_unroll in h.
        destruct (dec_isFirst e); simpl in *; tcsp; GC.
        rewrite Heqy in h; simpl in h; tcsp.

    - remember (state_sm_on_event (parallel X Y) (local_pred e)) as sop.
      symmetry in Heqsop; destruct sop; simpl in *; tcsp.

      + destruct p; simpl in *.

        * dest_cases w; symmetry in Heqw; simpl in *.
          dest_cases y; symmetry in Heqy; simpl in *.
          apply state_sm_on_event_parallel_some_pstate_two_implies in Heqsop; repnd.
          apply in_app_iff.
          repndors.

          { rewrite loutput_sm_on_event_unroll in h.
            destruct (dec_isFirst e); simpl in *; tcsp; GC.
            rewrite Heqsop0 in h; simpl in h.
            rewrite Heqw in h; simpl in h; tcsp. }

          { rewrite loutput_sm_on_event_unroll in h.
            destruct (dec_isFirst e); simpl in *; tcsp; GC.
            rewrite Heqsop in h; simpl in h; tcsp.
            rewrite Heqy in h; simpl in h; tcsp. }

        * dest_cases w; symmetry in Heqw; simpl in *.
          apply state_sm_on_event_parallel_some_pstate_left_implies in Heqsop; repnd.
          repndors.

          { rewrite loutput_sm_on_event_unroll in h.
            destruct (dec_isFirst e); simpl in *; tcsp; GC.
            rewrite Heqsop0 in h; simpl in h.
            rewrite Heqw in h; simpl in h; tcsp. }

          { rewrite loutput_sm_on_event_unroll in h.
            destruct (dec_isFirst e); simpl in *; tcsp; GC.
            rewrite Heqsop in h; simpl in h; tcsp. }

        * dest_cases w; symmetry in Heqw; simpl in *.
          apply state_sm_on_event_parallel_some_pstate_right_implies in Heqsop; repnd.
          repndors.

          { rewrite loutput_sm_on_event_unroll in h.
            destruct (dec_isFirst e); simpl in *; tcsp; GC.
            rewrite Heqsop0 in h; simpl in h; tcsp. }

          { rewrite loutput_sm_on_event_unroll in h.
            destruct (dec_isFirst e); simpl in *; tcsp; GC.
            rewrite Heqsop in h; simpl in h; tcsp.
            rewrite Heqw in h; simpl in *; auto. }

      + apply state_sm_on_event_parallel_none_implies in Heqsop; repnd.
        rewrite (loutput_sm_on_event_unroll X) in h.
        rewrite (loutput_sm_on_event_unroll Y) in h.
        destruct (dec_isFirst e); tcsp; GC.
        rewrite Heqsop, Heqsop0 in h; simpl in h; tcsp.
  }
Qed.

End Parallel.


Open Scope proc.
Notation "a [||] b" := (nparallel a b) (at level 100) : proc.
Close Scope proc.
