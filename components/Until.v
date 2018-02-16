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
Require Import EventOrderingLemmas.
Require Import Process.
Require Import PairState.


Section Until.

Context { pn     : @Node }.
Context { pm     : @Msg }.
Context { pk     : @Key }.

Open Scope eo.

Definition Until_upd {SX SY I OX OY : Type}
           (X : Update SX I (list OX))
           (Y : Update SY I (list OY)) : Update (pstate SX SY) I (list OX) :=
  fun state i =>
    match state with
    | pstate_two sx sy =>
      let (sx', outx) := X sx i in
      let (sy', outy) := Y sy i in
      if nullb outy (* if outy is not null, we halt X *)
      then
        match opt_states2pstate sx' sy' with
        (* both X and Y are still running *)
        | Some (pstate_two x y) as st => (st, outx)
        (* X is still running *)
        | Some (pstate_left x) as st => (st, outx)
        (* X is not running anymore *)
        | _ => (None, outx)
        end
      else (None, outx)
    | pstate_left sx =>
      let (sx', outx) := X sx i in
      match sx' with
      | Some x => (Some (pstate_left x), outx)
      | None => (None, outx)
      end
    | _ => (None, [])
    end.

Definition Until {SX SY I OX OY : Type}
           (X : StateMachine SX I (list OX))
           (Y : StateMachine SY I (list OY))
  : StateMachine (pstate SX SY) I (list OX) :=
  mkSM (Until_upd (sm_update X) (sm_update Y))
       (pstate_two (sm_state X) (sm_state Y)).

Definition nUntil {SX SY I OX OY : Type}
           (X : NStateMachine SX I (list OX))
           (Y : NStateMachine SY I (list OY))
  : NStateMachine (pstate SX SY) I (list OX) :=
  fun slf => Until (X slf) (Y slf).

Definition UntilSend_upd {SX SY I O : Type}
           (X : Update SX I (list O))
           (Y : Update SY I (list O)) : Update (pstate SX SY) I (list O) :=
  fun state i =>
    match state with
    | pstate_two sx sy =>
      let (sx', outx) := X sx i in
      let (sy', outy) := Y sy i in
      (* This is similar to Until.
           If outy is not null, we halt X.
           Here, we also send the outputs of Y. while with Until we don't. *)
      if nullb outy
      then
        match opt_states2pstate sx' sy' with
        (* both X and Y are still running *)
        | Some (pstate_two x y) as st => (st, outx)
        (* X is still running *)
        | Some (pstate_left x) as st => (st, outx)
        (* X is not running anymore *)
        | _ => (None, outx)
        end
      else (None, outx ++ outy) (* Here's the difference with Until.  Here we send Y's outputs. *)
    | pstate_left sx =>
      let (sx', outx) := X sx i in
      match sx' with
      | Some x => (Some (pstate_left x), outx)
      | None => (None, outx)
      end
    | _ => (None, [])
    end.

Definition UntilSend {SX SY I O : Type}
           (X : StateMachine SX I (list O))
           (Y : StateMachine SY I (list O))
  : StateMachine (pstate SX SY) I (list O) :=
  mkSM (UntilSend_upd (sm_update X) (sm_update Y))
       (pstate_two (sm_state X) (sm_state Y)).

Definition nUntilSend {SX SY I O : Type}
           (X : NStateMachine SX I (list O))
           (Y : NStateMachine SY I (list O))
  : NStateMachine (pstate SX SY) I (list O) :=
  fun slf => UntilSend (X slf) (Y slf).



Lemma state_sm_on_event_UntilSend_some_pstate_two_implies :
  forall {SX SY O : Type}
         (X  : StateMachine SX msg (list O))
         (Y  : StateMachine SY msg (list O))
         (eo : EventOrdering)
         (e  : Event)
         (l  : SX)
         (r  : SY),
    state_sm_on_event (UntilSend X Y) e = Some (pstate_two l r)
    -> state_sm_on_event X e = Some l
       /\ state_sm_on_event Y e = Some r
       /\ (forall e' x, e' ⊑ e -> ~ In x (loutput_sm_on_event Y e')).
Proof.
  intros SX SY O X Y eo.
  induction e as [e ind] using predHappenedBeforeInd; introv h; simpl.
  rewrite state_sm_on_event_unroll in h.
  rewrite (state_sm_on_event_unroll X).
  rewrite (state_sm_on_event_unroll Y).
  destruct (dec_isFirst e) as [d|d]; simpl in *.

  - dest_cases w; symmetry in Heqw; simpl in *.
    dest_cases y; symmetry in Heqy; simpl in *.
    dest_cases z; symmetry in Heqz; simpl in *.
    apply nullb_true_iff in Heqz; subst; simpl in *.
    destruct w0, y0; simpl in *; ginv.
    dands; auto.
    introv lte.
    apply localHappenedBeforeLe_implies_or2 in lte; repndors;
      [|apply no_local_predecessor_if_first in lte; tcsp].
    subst.

    rewrite loutput_sm_on_event_unroll.
    destruct (dec_isFirst e); tcsp; GC.
    allrw; simpl; tcsp.

  - remember (state_sm_on_event (UntilSend X Y) (local_pred e)) as sop.
    symmetry in Heqsop; destruct sop; simpl in *; ginv;[].
    destruct p; simpl in *; ginv.

    + apply ind in Heqsop;[|apply local_pred_is_direct_pred; auto].
      repnd; allrw; simpl.
      dest_cases w; symmetry in Heqw; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *.
      dest_cases z; symmetry in Heqz; simpl in *.
      apply nullb_true_iff in Heqz; subst; simpl in *.
      destruct w0, y0; simpl in *; ginv.
      dands; auto.
      introv lte.

      apply localHappenedBeforeLe_implies_or in lte; repndors.

      { subst; rewrite loutput_sm_on_event_unroll.
        destruct (dec_isFirst e); tcsp; GC.
        repeat (allrw; simpl; tcsp). }

      eapply Heqsop; auto.

    + dest_cases w; symmetry in Heqw; simpl in *; ginv.
      destruct w0; ginv.
Qed.

Lemma state_sm_on_event_UntilSend_some_pstate_left_implies :
  forall {SX SY O : Type}
         (X  : StateMachine SX msg (list O))
         (Y  : StateMachine SY msg (list O))
         (eo : EventOrdering)
         (e  : Event)
         (l  : SX),
    state_sm_on_event (UntilSend X Y) e = Some (pstate_left l)
    -> state_sm_on_event X e = Some l
       /\ state_sm_on_event Y e = None
       /\ (forall e' x, e' ⊑ e -> ~ In x (loutput_sm_on_event Y e')).
Proof.
  intros SX SY O X Y eo.
  induction e as [e ind] using predHappenedBeforeInd; introv h; simpl.
  rewrite state_sm_on_event_unroll in h.
  rewrite (state_sm_on_event_unroll X).
  rewrite (state_sm_on_event_unroll Y).
  destruct (dec_isFirst e) as [d|d]; simpl in *.

  - dest_cases w; symmetry in Heqw; simpl in *.
    dest_cases y; symmetry in Heqy; simpl in *.
    dest_cases z; symmetry in Heqz; simpl in *.
    apply nullb_true_iff in Heqz; subst; simpl in *.
    destruct w0, y0; simpl in *; ginv.
    dands; auto.
    introv lte.
    apply localHappenedBeforeLe_implies_or2 in lte; repndors;
      [|apply no_local_predecessor_if_first in lte; tcsp].
    subst.

    rewrite loutput_sm_on_event_unroll.
    destruct (dec_isFirst e); tcsp; GC.
    allrw; simpl; tcsp.

  - remember (state_sm_on_event (UntilSend X Y) (local_pred e)) as sop.
    symmetry in Heqsop; destruct sop; simpl in *; ginv;[].
    destruct p; simpl in *; ginv.

    + apply state_sm_on_event_UntilSend_some_pstate_two_implies in Heqsop.
      repnd; allrw; simpl in *.
      dest_cases w; symmetry in Heqw; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *.
      dest_cases z; symmetry in Heqz; simpl in *.
      apply nullb_true_iff in Heqz; subst; simpl in *.
      destruct w0, y0; simpl in *; ginv.
      dands; auto.

      introv lte.

      apply localHappenedBeforeLe_implies_or in lte; repndors.

      { subst; rewrite loutput_sm_on_event_unroll.
        destruct (dec_isFirst e); tcsp; GC.
        repeat (allrw; simpl; tcsp). }

      eapply Heqsop; auto.

    + dest_cases w; symmetry in Heqw; simpl in *; ginv.
      destruct w0; ginv.
      apply ind in Heqsop;[|apply local_pred_is_direct_pred; auto].
      repnd; allrw; simpl.
      allrw; simpl.
      dands; auto.

      introv lte.

      apply localHappenedBeforeLe_implies_or in lte; repndors.

      { subst; rewrite loutput_sm_on_event_unroll.
        destruct (dec_isFirst e); tcsp; GC.
        repeat (allrw; simpl; tcsp). }

      eapply Heqsop; auto.
Qed.

Lemma state_sm_on_event_UntilSend_some_pstate_right_implies :
  forall {SX SY O : Type}
         (X  : StateMachine SX msg (list O))
         (Y  : StateMachine SY msg (list O))
         (eo : EventOrdering)
         (e  : Event)
         (r  : SY),
    state_sm_on_event (UntilSend X Y) e = Some (pstate_right r)
    -> False.
Proof.
  introv h; simpl.
  rewrite state_sm_on_event_unroll in h.
  destruct (dec_isFirst e) as [d|d]; simpl in *.

  - dest_cases w; symmetry in Heqw; simpl in *.
    dest_cases y; symmetry in Heqy; simpl in *.
    dest_cases z; symmetry in Heqz; simpl in *.
    apply nullb_true_iff in Heqz; subst; simpl in *.
    destruct w0, y0; simpl in *; ginv.

  - remember (state_sm_on_event (UntilSend X Y) (local_pred e)) as sop.
    symmetry in Heqsop; destruct sop; simpl in *; ginv;[].
    destruct p; simpl in *; ginv.

    + dest_cases w; symmetry in Heqw; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *.
      dest_cases z; symmetry in Heqz; simpl in *.
      destruct w0, y0; simpl in *; ginv.

    + dest_cases w; symmetry in Heqw; simpl in *; ginv.
      destruct w0; ginv.
Qed.

Lemma state_sm_on_event_UntilSend_none_implies :
  forall {SX SY O : Type}
         (X  : StateMachine SX msg (list O))
         (Y  : StateMachine SY msg (list O))
         (eo : EventOrdering)
         (e  : Event),
    state_sm_on_event (UntilSend X Y) e = None
    ->
    exists e',
      e' ⊑ e
      /\
      (
        state_sm_on_event X e' = None
        \/
        exists x, In x (loutput_sm_on_event Y e')
      ).
Proof.
  intros SX SY O X Y eo.
  induction e as [e ind] using predHappenedBeforeInd; introv h; simpl.
  rewrite state_sm_on_event_unroll in h.
  destruct (dec_isFirst e) as [d|d]; simpl in *.

  - dest_cases w; symmetry in Heqw; simpl in *.
    dest_cases y; symmetry in Heqy; simpl in *.
    dest_cases z; symmetry in Heqz; simpl in *.
    apply nullb_true_iff in Heqz; subst; simpl in *.
    destruct w0, y0; simpl in *; ginv.

    + exists e; dands; auto;[apply localHappenedBeforeLe_implies_or2; tcsp|].
      left.
      rewrite state_sm_on_event_unroll.
      destruct (dec_isFirst e); tcsp; GC.
      allrw; simpl; tcsp.

    + exists e; dands; auto;[apply localHappenedBeforeLe_implies_or2; tcsp|].
      left.
      rewrite state_sm_on_event_unroll.
      destruct (dec_isFirst e); tcsp; GC.
      allrw; simpl; tcsp.

    + exists e; dands; auto;[apply localHappenedBeforeLe_implies_or2; tcsp|].
      right.
      destruct y1; simpl in *; ginv.
      exists o.
      rewrite loutput_sm_on_event_unroll.
      destruct (dec_isFirst e); tcsp; GC.
      allrw; simpl; tcsp.

  - remember (state_sm_on_event (UntilSend X Y) (local_pred e)) as sop.
    symmetry in Heqsop; destruct sop; simpl in *; ginv;[|].

    + destruct p; simpl in *; ginv.

      * apply state_sm_on_event_UntilSend_some_pstate_two_implies in Heqsop; repnd.
        dest_cases w; symmetry in Heqw; simpl in *.
        dest_cases y; symmetry in Heqy; simpl in *.
        dest_cases z; symmetry in Heqz; simpl in *.

        { apply nullb_true_iff in Heqz; subst; simpl in *.
          destruct w0, y0; simpl in *; ginv.

          - exists e; dands; auto;[apply localHappenedBeforeLe_implies_or2; tcsp|].
            left.
            rewrite state_sm_on_event_unroll.
            destruct (dec_isFirst e); tcsp; GC.
            repeat (allrw; simpl; auto).

          - exists e; dands; auto;[apply localHappenedBeforeLe_implies_or2; tcsp|].
            left.
            rewrite state_sm_on_event_unroll.
            destruct (dec_isFirst e); tcsp; GC.
            repeat (allrw; simpl; auto). }

        { exists e; dands; auto;[apply localHappenedBeforeLe_implies_or2; tcsp|].
          right; GC.
          destruct y1; simpl in *; ginv.
          exists o.
          rewrite loutput_sm_on_event_unroll.
          destruct (dec_isFirst e); tcsp; GC.
          repeat (allrw; simpl; auto). }

      * apply state_sm_on_event_UntilSend_some_pstate_left_implies in Heqsop; repnd.
        dest_cases w; symmetry in Heqw; simpl in *.
        destruct w0; simpl in *; ginv.

        exists e; dands; auto;[apply localHappenedBeforeLe_implies_or2; tcsp|].
        left.
        rewrite state_sm_on_event_unroll.
        destruct (dec_isFirst e); tcsp; GC.
        repeat (allrw; simpl; auto).

      * apply state_sm_on_event_UntilSend_some_pstate_right_implies in Heqsop; repnd; tcsp.

    + apply ind in Heqsop;[|apply local_pred_is_direct_pred; auto].
      exrepnd.
      exists e'; dands; auto.
      eapply localLe_trans;[exact Heqsop1|].
      apply local_pred_le.
Qed.

Lemma UntilSend_output_iff0 :
  forall {SX SY O : Type}
         (X  : StateMachine SX msg (list O))
         (Y  : StateMachine SY msg (list O))
         (eo : EventOrdering)
         (e  : Event)
         (o  : O),
    In o (loutput_sm_on_event (UntilSend X Y) e)
    <->
    (
      (forall e' x, e' ⊏ e -> ~ In x (loutput_sm_on_event Y e'))
      /\
      (
        In o (loutput_sm_on_event X e)
        \/
        (
          In o (loutput_sm_on_event Y e)
          /\
          exists s, state_sm_before_event X e = Some s
        )
      )
    ).
Proof.
  introv; split; intro h.

  - rewrite loutput_sm_on_event_unroll in h.
    rewrite (loutput_sm_on_event_unroll X).
    rewrite (loutput_sm_on_event_unroll Y).
    destruct (dec_isFirst e) as [d|d]; simpl in *.

    + dands.

      { introv lte.
        apply no_local_predecessor_if_first in lte; tcsp. }

      dest_cases w; symmetry in Heqw; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *.
      dest_cases z; symmetry in Heqz; simpl in *.

      * apply nullb_true_iff in Heqz; subst; simpl in *; left.
        destruct w0, y0; simpl in *; auto.

      * allrw in_app_iff; repndors; tcsp.
        right; dands; auto.
        exists (sm_state X).
        rewrite state_sm_before_event_unroll.
        destruct (dec_isFirst e); tcsp; GC.

    + apply in_olist2list in h; exrepnd.
      remember (state_sm_on_event (UntilSend X Y) (local_pred e)) as sop.
      destruct sop; symmetry in Heqsop; simpl in *; ginv;[].
      destruct p; simpl in *; tcsp.

      * apply state_sm_on_event_UntilSend_some_pstate_two_implies in Heqsop.
        repnd; allrw; simpl in *.
        dest_cases w; symmetry in Heqw; simpl in *.
        dest_cases y; symmetry in Heqy; simpl in *.
        dest_cases z; symmetry in Heqz; simpl in *.

        {
          apply nullb_true_iff in Heqz; subst; simpl in *.
          destruct w0, y0; simpl in *; ginv; dands; tcsp;
            try (complete (introv lte;
                           apply localHappenedBefore_implies_le_local_pred in lte;
                           apply Heqsop; auto)).
        }

        {
          apply in_app_iff in h0; dands; auto.

          - introv lte.
            apply localHappenedBefore_implies_le_local_pred in lte.
            apply Heqsop; auto.

          - repndors; tcsp.
            right; dands; auto.
            exists l.
            rewrite state_sm_before_event_as_state_sm_on_event_pred; auto.
        }

      * dest_cases w; symmetry in Heqw.
        apply state_sm_on_event_UntilSend_some_pstate_left_implies in Heqsop.
        repeat (repnd; allrw; simpl in * ).
        destruct w0; simpl in *; ginv; dands; tcsp;
          try (complete (introv lte;
                         apply localHappenedBefore_implies_le_local_pred in lte;
                         apply Heqsop; auto)).

  - rewrite (loutput_sm_on_event_unroll X) in h.
    rewrite (loutput_sm_on_event_unroll Y) in h.
    rewrite loutput_sm_on_event_unroll.
    destruct (dec_isFirst e) as [d|d]; simpl in *; repnd.

    + dest_cases w; symmetry in Heqw; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *.
      dest_cases z; symmetry in Heqz; simpl in *.

      * apply nullb_true_iff in Heqz; subst; simpl in *; repndors; tcsp.
        destruct w0, y0; simpl in *; tcsp.

      * allrw in_app_iff; tcsp.

    + allrw @in_olist2list.
      remember (state_sm_on_event (UntilSend X Y) (local_pred e)) as sop.
      symmetry in Heqsop; destruct sop; simpl in *.

      * destruct p; simpl in *.

        { apply state_sm_on_event_UntilSend_some_pstate_two_implies in Heqsop; repnd.
          rewrite Heqsop0, Heqsop1 in h; simpl in h.
          dest_cases w; symmetry in Heqw; simpl in *.
          dest_cases y; symmetry in Heqy; simpl in *.
          dest_cases z; symmetry in Heqz; simpl in *.

          - apply nullb_true_iff in Heqz; subst; simpl in *.
            repndors; exrepnd; ginv; simpl in *; tcsp.
            destruct w0, y0; simpl in *; try (complete (eexists; dands; eauto)).

          - exists (w1 ++ y1); rewrite in_app_iff.
            repndors; exrepnd; ginv. }

        { apply state_sm_on_event_UntilSend_some_pstate_left_implies in Heqsop; repnd.
          rewrite Heqsop0, Heqsop1 in h; simpl in h.
          repndors; exrepnd; ginv.
          dest_cases w; symmetry in Heqw; simpl in *.
          destruct w0; simpl in *; simpl in *; ginv;
            try (complete (eexists; dands; eauto)). }

        { apply state_sm_on_event_UntilSend_some_pstate_right_implies in Heqsop; tcsp. }

      * assert False; tcsp.
        apply state_sm_on_event_UntilSend_none_implies in Heqsop; exrepnd.
        repndors; exrepnd.

        { remember (state_sm_on_event X (local_pred e)) as sxop.
          symmetry in Heqsxop; destruct sxop; simpl in *; ginv;[].
          eapply state_sm_on_event_none_monotonic in Heqsop0;[|exact Heqsop1].
          rewrite Heqsop0 in Heqsxop; ginv. }

        { remember (state_sm_on_event Y (local_pred e)) as syop.
          symmetry in Heqsyop; destruct syop; simpl in *; ginv;[].
          eapply state_sm_on_event_none_monotonic in Heqsop0;[|exact Heqsop1].
          rewrite state_sm_before_event_as_state_sm_on_event_pred in h2; auto.
          rewrite Heqsop0 in h2; ginv. }

        { apply h0 in Heqsop2; tcsp.
          eapply local_trans_le_l;[|apply local_pred_is_localCausal;auto]; auto. }

        { apply h0 in Heqsop2; tcsp.
          eapply local_trans_le_l;[|apply local_pred_is_localCausal;auto]; auto. }
Qed.

Lemma UntilSend_output_iff :
  forall {SX SY O : Type}
         (X  : StateMachine SX msg (list O))
         (Y  : StateMachine SY msg (list O))
         (eo : EventOrdering)
         (e  : Event)
         (o  : O),
    In o (loutput_sm_on_event (UntilSend X Y) e)
    <->
    (
      no_loutput_sm_on_event_prior_to Y e
      /\
      (
        In o (loutput_sm_on_event X e)
        \/
        (
          In o (loutput_sm_on_event Y e)
          /\
          state_sm_before_event_exists X e
        )
      )
    ).
Proof.
  introv.
  rewrite UntilSend_output_iff0; tcsp.
Qed.

End Until.


Open Scope proc.
Notation "a [until] b" := (nUntil a b) (at level 100) : proc.
Notation "a [until-send] b" := (nUntilSend a b) (at level 100) : proc.
Close Scope proc.
