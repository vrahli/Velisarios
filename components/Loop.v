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


Section Loop.

Context { pn     : @Node }.
Context { pm     : @Msg }.
Context { pk     : @Key }.

Definition simple_state_machine_upd {SX S I T U : Type}
           (upd : SUpdate S T U)
           (X   : Update SX I T) : Update (S * SX) I U :=
  fun state i =>
    let (s,sx) := state in
    let (sxop, t) := X sx i in
    let (s', o) := upd s t in
    (option_map (fun sx' => (s', sx')) sxop, o).

Definition simple_state_machineSM {SX S I T U : Type}
           (upd  : SUpdate S T U)
           (init : S)
           (X    : StateMachine SX I T)
  : StateMachine (S * SX) I U :=
  mkSM (simple_state_machine_upd upd (sm_update X))
       (init, sm_state X).

Definition n_simple_state_machineSM {SX S I T U : Type}
           (upd  : SUpdate S T U)
           (init : S)
           (X    : NStateMachine SX I T)
  : NStateMachine (S * SX) I U :=
  fun n => simple_state_machineSM upd init (X n).

Definition state_machine_upd {SX S I T U : Type}
           (upd : Update S T U)
           (X   : Update SX I T) : Update (S * SX) I U :=
  fun state i =>
    let (s,sx) := state in
    let (sxop, t) := X sx i in
    let (sop, o) := upd s t in
    match sop, sxop with
    | Some s', Some sx' => (Some (s', sx'), o)
    | _, _ => (None, o)
    end.

Definition state_machineSM {SX S I T U : Type}
           (upd  : Update S T U)
           (init : S)
           (X    : StateMachine SX I T)
  : StateMachine (S * SX) I U :=
  mkSM (state_machine_upd upd (sm_update X))
       (init, sm_state X).

Definition n_state_machineSM {SX S I T U : Type}
           (upd  : Update S T U)
           (init : S)
           (X    : NStateMachine SX I T)
  : NStateMachine (S * SX) I U :=
  fun n => state_machineSM upd init (X n).

Lemma simple_state_machineSM_state_iff :
  forall {S SX T U}
         (upd  : SUpdate S T U)
         (init : S)
         (X    : StateMachine SX msg T)
         (eo   : EventOrdering)
         (e    : Event)
         (s    : S)
         (sx   : SX),
    state_sm_on_event (simple_state_machineSM upd init X) e = Some (s, sx)
    <->
    exists t s' sx',
      state_sm_on_event X e = Some sx
      /\ output_sm_on_event X e = Some t
      /\ state_sm_before_event (simple_state_machineSM upd init X) e = Some (s', sx')
      /\ state_sm_before_event X e = Some sx'
      /\ op_update X sx' (trigger e) = Some (Some sx, t)
      /\ s = fst (upd s' t).
Proof.
  intros S SX T U upd init X eo.
  induction e as [e ind] using predHappenedBeforeInd; introv; simpl.
  rewrite (state_sm_on_event_unroll (simple_state_machineSM _ _ _)).
  rewrite (state_sm_on_event_unroll X).
  destruct (dec_isFirst e) as [d|d]; simpl in *.

  - split; intro h.

    + apply op_state_some_iff in h; exrepnd.
      allrw; simpl.
      unfold op_state; simpl.
      unfold simple_state_machine_upd in h0; simpl in h0.
      repeat (dest_cases w); simpl in *.
      destruct w0; simpl in *; ginv.
      exists w1 init (sm_state X); dands; auto; try congruence.

      {
        rewrite output_sm_on_event_unroll.
        destruct (dec_isFirst e); tcsp; simpl.
        allrw; simpl; auto.
        unfold op_output; simpl.
        allrw <- ; simpl; auto.
      }

      {
        rewrite state_sm_before_event_unroll.
        destruct (dec_isFirst e); tcsp; simpl.
      }

      {
        rewrite state_sm_before_event_unroll.
        destruct (dec_isFirst e); tcsp; simpl.
      }

      {
        allrw <- ; simpl; auto.
      }

    + exrepnd; ginv; subst.
      apply op_state_some_iff in h1; exrepnd.
      apply op_update_some_iff in h5; exrepnd; ginv.
      rewrite h1 in *; ginv.
      unfold op_state; simpl.
      repeat (dest_cases w); simpl in *; subst.
      unfold option_map.
      rewrite state_sm_before_event_unroll in h3.
      rewrite state_sm_before_event_unroll in h4.
      destruct (dec_isFirst e); tcsp; simpl; ginv.
      rewrite <- Heqw in *; ginv.

  - remember (state_sm_on_event (simple_state_machineSM upd init X) (local_pred e)) as sop.
    symmetry in Heqsop; destruct sop; simpl in *.

    + destruct p.
      apply ind in Heqsop;[|apply local_pred_is_direct_pred;auto].
      exrepnd; subst; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *.
      dest_cases z; symmetry in Heqz; simpl in *.
      destruct y0; simpl in *; split; intro h; tcsp; ginv;
        repeat (allrw; simpl in * ).

      * exists y1 (fst (upd s' t)) s1; dands; auto; allrw; simpl; auto.

        {
          rewrite output_sm_on_event_unroll; destruct (dec_isFirst e); tcsp.
          repeat (allrw; simpl; tcsp).
        }

        {
          rewrite state_sm_before_event_unroll.
          destruct (dec_isFirst e); tcsp; GC.
          repeat (allrw; simpl).
          dest_cases w; symmetry in Heqw; simpl in *; auto.
        }

        {
          rewrite state_sm_before_event_as_state_sm_on_event_pred; auto.
        }

      * exrepnd; subst; simpl in *; ginv.
        rewrite Heqsop1 in h1; simpl in *.
        rewrite Heqy in h1; simpl in *; ginv.
        rewrite state_sm_before_event_as_state_sm_on_event_pred in h4; auto.
        rewrite Heqsop1 in h4; ginv.
        rewrite h5 in Heqy; ginv.
        apply implies_eq_fst in Heqz; simpl in Heqz; subst.

        f_equal; f_equal.
        rewrite state_sm_before_event_unroll in h3.
        destruct (dec_isFirst e); tcsp; GC.
        rewrite Heqsop3 in h3; simpl in *.
        rewrite Heqsop5 in h3; simpl in *.
        dest_cases w; symmetry in Heqw; simpl in *; ginv.

      * assert False; tcsp.
        exrepnd; subst; simpl in *; ginv.
        rewrite Heqsop1 in h1; simpl in h1.
        rewrite Heqy in h1; simpl in *; ginv.

    + split; intro h; ginv.
      exrepnd; subst; simpl in *.
      assert False; tcsp.

      rewrite state_sm_before_event_as_state_sm_on_event_pred in h3; auto.
      rewrite Heqsop in h3; ginv.
Qed.

Lemma simple_state_machineSM_output_iff0 :
  forall {S SX T U}
         (upd  : SUpdate S T U)
         (init : S)
         (X    : StateMachine SX msg T)
         (eo   : EventOrdering)
         (e    : Event)
         (u    : U),
    output_sm_on_event (simple_state_machineSM upd init X) e = Some u
    <->
    exists t s sx,
      output_sm_on_event X e = Some t
      /\ state_sm_before_event (simple_state_machineSM upd init X) e = Some (s,sx)
      /\ u = snd (upd s t).
Proof.
  introv.
  rewrite (output_sm_on_event_unroll (simple_state_machineSM _ _ _)).
  rewrite (output_sm_on_event_unroll X).
  destruct (dec_isFirst e) as [d|d]; simpl in *.

  - split; intro h; ginv.

    + dest_cases w; symmetry in Heqw; simpl in *; auto; ginv.
      dest_cases y; symmetry in Heqy; simpl in *.
      apply implies_eq_snd in Heqy; simpl in Heqy; subst.
      exists w1 init (sm_state X); dands; auto.
      rewrite state_sm_before_event_unroll.
      destruct (dec_isFirst e); tcsp; ginv; simpl.

    + exrepnd; subst; ginv; simpl in *.
      dest_cases w; symmetry in Heqw; simpl in *; auto.
      dest_cases y; symmetry in Heqy; simpl in *; auto.
      apply implies_eq_snd in Heqy; simpl in Heqy; subst.
      rewrite state_sm_before_event_unroll in h2.
      destruct (dec_isFirst e); tcsp; simpl in *; ginv.

  - split; intro h.

    + remember (state_sm_on_event (simple_state_machineSM upd init X) (local_pred e)) as sop.
      symmetry in Heqsop; destruct sop; simpl in *; ginv;[].
      destruct p; simpl in *.

      apply simple_state_machineSM_state_iff in Heqsop.
      exrepnd; subst; simpl in *.
      repeat (allrw; simpl in * ).
      dest_cases w; symmetry in Heqw; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *.
      apply implies_eq_snd in Heqy; simpl in Heqy; subst.

      exists w1 (fst (upd s' t)) s0.
      dands; auto.

      rewrite state_sm_before_event_unroll.
      destruct (dec_isFirst e); tcsp; GC.
      repeat (allrw; simpl).
      dest_cases y; symmetry in Heqy; simpl in *; auto.

    + exrepnd; subst; simpl in *.
      rewrite state_sm_before_event_as_state_sm_on_event_pred in h2; auto.
      allrw; simpl.

      apply simple_state_machineSM_state_iff in h2.
      exrepnd; subst.
      rewrite h2 in h1; simpl in h1; ginv.
      dest_cases w; symmetry in Heqw; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *; auto.
Qed.


Lemma simple_state_machineSM_output_iff :
  forall {S SX T U}
         (upd  : SUpdate S T U)
         (init : S)
         (X    : StateMachine SX msg T)
         (eo   : EventOrdering)
         (e    : Event)
         (u    : U),
    output_sm_on_event (simple_state_machineSM upd init X) e = Some u
    <->
    exists t s,
      output_sm_on_event X e = Some t
      /\ SM_state_before_event (simple_state_machineSM upd init X) e s
      /\ u = snd (upd s t).
Proof.
  introv.
  rewrite simple_state_machineSM_output_iff0.
  split; intro h; exrepnd; subst; unfold SM_state_before_event in *; allrw.

  - exists t s; dands; auto.

  - remember (state_sm_before_event (simple_state_machineSM upd init X) e) as sop;
      destruct sop; tcsp; destruct p; subst.
    exists t s s1; dands; auto.
Qed.

Lemma simple_state_machineSM_list_output_iff :
  forall {S SX T U}
         (upd  : SUpdate S T (list U))
         (init : S)
         (X    : StateMachine SX msg T)
         (eo   : EventOrdering)
         (e    : Event)
         (u    : U),
    In u (loutput_sm_on_event (simple_state_machineSM upd init X) e)
    <->
    exists t s,
      output_sm_on_event X e = Some t
      /\ SM_state_before_event (simple_state_machineSM upd init X) e s
      /\ In u (snd (upd s t)).
Proof.
  introv.
  unfold loutput_sm_on_event.
  remember (output_sm_on_event (simple_state_machineSM upd init X) e) as sop.
  symmetry in Heqsop; destruct sop; simpl in *.
  - apply simple_state_machineSM_output_iff in Heqsop; exrepnd; subst; simpl in *.
    split; intro h.
    + exists t s; dands; auto.
    + exrepnd.
      rewrite Heqsop0 in h0; ginv.
      unfold SM_state_before_event in *.
      remember (state_sm_before_event (simple_state_machineSM upd init X) e) as p.
      symmetry in Heqp; destruct p; tcsp.
      destruct p; simpl in *; repeat subst; auto.
  - split; intro h; tcsp.
    exrepnd.
    unfold SM_state_before_event in *.
    remember (state_sm_before_event (simple_state_machineSM upd init X) e) as p.
    symmetry in Heqp; destruct p; tcsp.
    destruct p; simpl in *; repeat subst; auto.
    apply output_sm_on_event_none_implies_state_sm_before_event_none in Heqsop.
    rewrite Heqsop in Heqp; ginv.
Qed.

Lemma state_machineSM_state_iff :
  forall {S SX T U}
         (upd  : Update S T U)
         (init : S)
         (X    : StateMachine SX msg T)
         (eo   : EventOrdering)
         (e    : Event)
         (s    : S)
         (sx   : SX),
    state_sm_on_event (state_machineSM upd init X) e = Some (s, sx)
    <->
    exists t s' sx',
      state_sm_on_event X e = Some sx
      /\ output_sm_on_event X e = Some t
      /\ state_sm_before_event (state_machineSM upd init X) e = Some (s', sx')
      /\ state_sm_before_event X e = Some sx'
      /\ sm_update X sx' (trigger e) = (Some sx, t)
      /\ Some s = fst (upd s' t).
Proof.
  intros S SX T U upd init X eo.
  induction e as [e ind] using predHappenedBeforeInd; introv; simpl.
  rewrite (state_sm_on_event_unroll (state_machineSM _ _ _)).
  rewrite (state_sm_on_event_unroll X).
  destruct (dec_isFirst e) as [d|d]; simpl in *.

  - dest_cases w; symmetry in Heqw; simpl.
    dest_cases y; symmetry in Heqy; simpl.
    destruct y0, w0; simpl; auto.

    + split; intro h; ginv.

      * exists w1 init (sm_state X).
        dands; auto; allrw; simpl; auto.

        {
          rewrite output_sm_on_event_unroll.
          destruct (dec_isFirst e); tcsp; simpl.
          allrw; simpl; auto.
        }

        {
          rewrite state_sm_before_event_unroll.
          destruct (dec_isFirst e); tcsp; simpl.
        }

        {
          rewrite state_sm_before_event_unroll.
          destruct (dec_isFirst e); tcsp; simpl.
        }

      * exrepnd; ginv; simpl in *.
        rewrite state_sm_before_event_unroll in h3.
        destruct (dec_isFirst e); tcsp; ginv.
        rewrite Heqw in h5; ginv.
        rewrite Heqy in h0; simpl in *; ginv.

    + split; intro h; exrepnd; ginv.

    + split; intro h; exrepnd; ginv.
      assert False; tcsp.

      rewrite output_sm_on_event_unroll in h2.
      destruct (dec_isFirst e); tcsp; GC.
      rewrite Heqw in h2; simpl in *; ginv.

      rewrite state_sm_before_event_unroll in h4.
      destruct (dec_isFirst e); tcsp; GC; ginv.

      rewrite state_sm_before_event_unroll in h3.
      destruct (dec_isFirst e); tcsp; GC; ginv.

      rewrite Heqy in h0; simpl in *; ginv.

    + split; intro h; exrepnd; ginv.

  - remember (state_sm_on_event (state_machineSM upd init X) (local_pred e)) as sop.
    symmetry in Heqsop; destruct sop; simpl in *.

    + destruct p.
      apply ind in Heqsop;[|apply local_pred_is_direct_pred;auto].
      exrepnd; subst; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *.
      dest_cases z; symmetry in Heqz; simpl in *.
      destruct z0, y0; simpl in *; split; intro h; tcsp; ginv;
        repeat (allrw; simpl in * ).

      * exists y1 s0 s1; dands; auto; allrw; simpl; auto.

        {
          rewrite output_sm_on_event_unroll; destruct (dec_isFirst e); tcsp.
          repeat (allrw; simpl; tcsp).
        }

        {
          rewrite state_sm_before_event_unroll.
          destruct (dec_isFirst e); tcsp; GC.
          repeat (allrw; simpl).
          dest_cases w; symmetry in Heqw; simpl in *; auto.
          destruct w0; simpl in *; ginv.
        }

        {
          rewrite state_sm_before_event_as_state_sm_on_event_pred; auto.
        }

      * exrepnd; subst; simpl in *; ginv.
        rewrite Heqsop1 in h1; simpl in *.
        rewrite Heqy in h1; simpl in *; ginv.
        rewrite state_sm_before_event_as_state_sm_on_event_pred in h4; auto.
        rewrite Heqsop1 in h4; ginv.
        rewrite h5 in Heqy; ginv.
        apply implies_eq_fst in Heqz; simpl in Heqz; subst.

        f_equal; f_equal.
        rewrite state_sm_before_event_unroll in h3.
        destruct (dec_isFirst e); tcsp; GC.
        rewrite Heqsop3 in h3; simpl in *.
        rewrite Heqsop5 in h3; simpl in *.
        dest_cases w; symmetry in Heqw; simpl in *; ginv.
        destruct w0; simpl in *; ginv.
        rewrite Heqz in h0; ginv.

      * assert False; tcsp.
        exrepnd; subst; simpl in *; ginv.
        rewrite Heqsop1 in h1; simpl in h1.
        rewrite Heqy in h1; simpl in *; ginv.

      * assert False; tcsp.
        exrepnd; subst; simpl in *; ginv.
        rewrite Heqsop1 in h1; simpl in h1.
        rewrite Heqy in h1; simpl in *; ginv.

        rewrite state_sm_before_event_as_state_sm_on_event_pred in h4; auto.
        rewrite Heqsop1 in h4; ginv.
        rewrite h5 in Heqy; ginv.

        rewrite state_sm_before_event_unroll in h3.
        destruct (dec_isFirst e); tcsp; GC.
        rewrite Heqsop3 in h3; simpl in *.
        rewrite Heqsop5 in h3; simpl in *.
        dest_cases w; symmetry in Heqw; simpl in *; ginv.
        destruct w0; simpl in *; ginv.
        rewrite Heqz in h0; ginv.

      * assert False; tcsp.
        exrepnd; subst; simpl in *; ginv.
        rewrite Heqsop1 in h1; simpl in h1.
        rewrite Heqy in h1; simpl in *; ginv.

    + split; intro h; ginv.
      exrepnd; subst; simpl in *.
      assert False; tcsp.

      rewrite state_sm_before_event_as_state_sm_on_event_pred in h3; auto.
      rewrite Heqsop in h3; ginv.
Qed.

Lemma state_machineSM_output_iff0 :
  forall {S SX T U}
         (upd  : Update S T U)
         (init : S)
         (X    : StateMachine SX msg T)
         (eo   : EventOrdering)
         (e    : Event)
         (u    : U),
    output_sm_on_event (state_machineSM upd init X) e = Some u
    <->
    exists t s sx,
      output_sm_on_event X e = Some t
      /\ state_sm_before_event (state_machineSM upd init X) e = Some (s,sx)
      /\ u = snd (upd s t).
Proof.
  introv.
  rewrite (output_sm_on_event_unroll (state_machineSM _ _ _)).
  rewrite (output_sm_on_event_unroll X).
  destruct (dec_isFirst e) as [d|d]; simpl in *.

  - split; intro h; ginv.

    + dest_cases w; symmetry in Heqw; simpl in *; auto; ginv.
      dest_cases y; symmetry in Heqy; simpl in *.

      exists w1 init (sm_state X); dands; auto.

      { rewrite state_sm_before_event_unroll.
        destruct (dec_isFirst e); tcsp; ginv; simpl. }

      { destruct y0, w0; simpl; allrw; simpl; auto. }

    + exrepnd; subst; ginv; simpl in *.
      dest_cases w; symmetry in Heqw; simpl in *; auto.
      dest_cases y; symmetry in Heqy; simpl in *; auto.
      rewrite state_sm_before_event_unroll in h2.
      destruct (dec_isFirst e); tcsp; simpl in *; ginv.

      destruct y0, w0; simpl; allrw; auto.

  - split; intro h.

    + remember (state_sm_on_event (state_machineSM upd init X) (local_pred e)) as sop.
      symmetry in Heqsop; destruct sop; simpl in *; ginv;[].
      destruct p; simpl in *.

      apply state_machineSM_state_iff in Heqsop.
      exrepnd; subst; simpl in *.
      repeat (allrw; simpl in * ).
      dest_cases w; symmetry in Heqw; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *.

      exists w1 s s0.
      dands; auto.

      { rewrite state_sm_before_event_unroll.
        destruct (dec_isFirst e); tcsp; GC.
        repeat (allrw; simpl).
        dest_cases y; symmetry in Heqy; simpl in *; auto.
        destruct y2; simpl in *; ginv. }

      { destruct y0, w0; simpl in *; allrw; simpl; auto. }

    + exrepnd; subst; simpl in *.
      rewrite state_sm_before_event_as_state_sm_on_event_pred in h2; auto.
      allrw; simpl.

      apply state_machineSM_state_iff in h2.
      exrepnd; subst.
      rewrite h2 in h1; simpl in h1; ginv.
      dest_cases w; symmetry in Heqw; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *; auto.
      destruct y0, w0; simpl; auto.
Qed.

Lemma state_machineSM_output_iff :
  forall {S SX T U}
         (upd  : Update S T U)
         (init : S)
         (X    : StateMachine SX msg T)
         (eo   : EventOrdering)
         (e    : Event)
         (u    : U),
    output_sm_on_event (state_machineSM upd init X) e = Some u
    <->
    exists t s,
      output_sm_on_event X e = Some t
      /\ SM_state_before_event (state_machineSM upd init X) e s
      /\ u = snd (upd s t).
Proof.
  introv.
  rewrite state_machineSM_output_iff0.
  split; intro h; exrepnd; subst; unfold SM_state_before_event in *; allrw.

  - exists t s; dands; auto.

  - remember (state_sm_before_event (state_machineSM upd init X) e) as sop;
      destruct sop; tcsp; destruct p; subst.
    exists t s s1; dands; auto.
Qed.

Lemma state_machineSM_list_output_iff :
  forall {S SX T U}
         (upd  : Update S T (list U))
         (init : S)
         (X    : StateMachine SX msg T)
         (eo   : EventOrdering)
         (e    : Event)
         (u    : U),
    In u (loutput_sm_on_event (state_machineSM upd init X) e)
    <->
    exists t s,
      output_sm_on_event X e = Some t
      /\ SM_state_before_event (state_machineSM upd init X) e s
      /\ In u (snd (upd s t)).
Proof.
  introv.
  unfold loutput_sm_on_event.
  remember (output_sm_on_event (state_machineSM upd init X) e) as sop.
  symmetry in Heqsop; destruct sop; simpl in *.
  - apply state_machineSM_output_iff in Heqsop; exrepnd; subst; simpl in *.
    split; intro h.
    + exists t s; dands; auto.
    + exrepnd.
      rewrite Heqsop0 in h0; ginv.
      unfold SM_state_before_event in *.
      remember (state_sm_before_event (state_machineSM upd init X) e) as p.
      symmetry in Heqp; destruct p; tcsp.
      destruct p; simpl in *; repeat subst; auto.
  - split; intro h; tcsp.
    exrepnd.
    unfold SM_state_before_event in *.
    remember (state_sm_before_event (state_machineSM upd init X) e) as p.
    symmetry in Heqp; destruct p; tcsp.
    destruct p; simpl in *; repeat subst; auto.
    apply output_sm_on_event_none_implies_state_sm_before_event_none in Heqsop.
    rewrite Heqsop in Heqp; ginv.
Qed.

End Loop.
