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


Section Bind.

Context { pn     : @Node }.
Context { pm     : @Msg }.
Context { pk     : @Key }.

Open Scope eo.

Inductive bindState (SX T SY : Type) :=
| bind_state (sx : option SX) (sys : list (T * SY)).
Arguments bind_state [SX] [T] [SY] _ _.

Definition updStateOp {S I O}
           (sm  : StateMachine S I O)
           (sop : option S) : StateMachine S I O :=
  match sop with
  | Some s => updState sm s
  | None => MkSM true (sm_update sm) (sm_state sm)
  end.

Definition run_main_process {SX I T}
           (X : StateMachine SX I (list T))
           (sxop : option SX)
           (i : I) : option SX * list T :=
  match sxop with
  | Some sx => sm_update X sx i
  | None => (None, [])
  end.

Definition run_sub_process {SY I T U}
           (gY : T -> StateMachine SY I (list U))
           (p : T * SY)
           (i : I) : option (T * SY) * list U :=
  let (t,sy) := p in
  match sm_update (gY t) sy i with
  | (Some sy', outs) => (Some (t, sy'), outs)
  | (None, outs) => (None, outs)
  end.

(* why X and gY have different types??? *)
(* why is this function on states??? *)
(* all the functions use, flatmap ??? *)
Definition bind_upd {SX SY I T U}
           (X : StateMachine SX I (list T))
           (gY : T -> StateMachine SY I (list U))
  : Update (bindState SX T SY) I (list U) :=
  fun state (i : I) =>
    match state with
    | bind_state sxop sys => (* The state is a pair of X and a bunch of Ys *)
      (* we run X on the input i and get some outputs outs *)
      let (sx',ts) := run_main_process X sxop i in
      (* we run the process generator gY on these outputs *)
      let sys' := map (fun t => (t, sm_state (gY t))) ts in (* NOTE: what if the state machine is supposed to be halted right from the beginning? *)
      (* now we run these Ys++Ys' on the input as well,
           and here outs is a list of pairs (option (t,state), outputs) *)
      let pairs := map (fun p => run_sub_process gY p i) (sys ++ sys') in
      (* We get the state machines and clear the ones that have halted *)
      let new_sys := mapOption fst pairs in
      (* new state *)
      let new_state :=
          if is_none sx' && nullb new_sys
          then None
          else Some (bind_state sx' new_sys) in
      (new_state, flat_map snd pairs)
    end.

Definition bind_init {I SX T SY}
           (X : StateMachine SX I (list T)) : bindState SX T SY :=
  bind_state (Some (sm_state X)) [].

Definition bind {SX SY I T U : Type}
           (X : StateMachine SX I (list T))
           (gY : T -> StateMachine SY I (list U))
  : StateMachine (bindState SX T SY) I (list U) :=
  mkSM (bind_upd X gY) (bind_init X).

(* ??? I do undrestand that we have here named state machines, but functions??? *)
Definition nbind {SX SY I T U : Type}
           (X : NStateMachine SX I (list T))
           (gY : T -> NStateMachine SY I (list U))
  : NStateMachine (bindState SX T SY) I (list U) :=
  fun slf => bind (X slf) (fun t => gY t slf).

Notation "a [>>=] f" := (nbind a f) (at level 100).


Lemma state_sm_on_event_bind_some_state_X :
  forall {SX SY T U}
         (X    : StateMachine SX msg (list T))
         (gY   : T -> StateMachine SY msg (list U))
         (eo   : EventOrdering)
         (e    : Event)
         (sop  : option SX)
         (sys  : list (T * SY)),
    state_sm_on_event (mkSM (bind_upd X gY) (bind_init X)) e
    = Some (bind_state sop sys)
    -> state_sm_on_event X e = sop.
Proof.
  intros SX SY T U X gY eo.
  induction e as [e ind] using predHappenedBeforeInd; introv eqs.
  rewrite state_sm_on_event_unroll in eqs.
  rewrite state_sm_on_event_unroll.
  destruct (dec_isFirst e) as [d|d].

  {
    unfold bind_upd, mkSM in eqs; simpl in *.
    apply op_state_some_iff in eqs; exrepnd; simpl in *; allrw.
    unfold op_state; simpl.
    dest_cases w; symmetry in Heqw.
    dest_cases y; symmetry in Heqy; simpl in *; ginv.
  }

  {
    remember (state_sm_on_event (mkSM (bind_upd X gY) (bind_init X)) (local_pred e)) as L.
    symmetry in HeqL.
    destruct L; simpl in *; ginv;[].
    destruct b.
    pose proof (ind (local_pred e) (local_pred_is_direct_pred e d) sx sys0) as h.
    autodimp h hyp.
    rewrite h.

    unfold bind_upd in eqs; simpl in eqs.
    apply op_state_some_iff in eqs; exrepnd; simpl in *; allrw.
    unfold run_main_process in eqs0; simpl in eqs0.
    destruct sx; simpl in *; auto; repeat (dest_cases w; simpl in * ).
    ginv; unfold op_state; simpl; allrw <- ; simpl; auto.
  }
Qed.

Lemma state_sm_on_event_bind_none_state_X :
  forall {SX SY T U}
         (X    : StateMachine SX msg (list T))
         (gY   : T -> StateMachine SY msg (list U))
         (eo   : EventOrdering)
         (e    : Event),
    state_sm_on_event (mkSM (bind_upd X gY) (bind_init X)) e = None
    -> state_sm_on_event X e = None.
Proof.
  intros SX SY T U X gY eo.
  induction e as [e ind] using predHappenedBeforeInd; introv eqs.
  rewrite state_sm_on_event_unroll in eqs.
  rewrite state_sm_on_event_unroll.
  destruct (dec_isFirst e) as [d|d].

  {
    unfold bind_upd, mkSM in eqs; simpl in *.
    dest_cases w; symmetry in Heqw.
    dest_cases y; symmetry in Heqy; simpl in *; ginv.
    apply andb_true_iff in Heqy; repnd.
    destruct w0; simpl in *; tcsp.
  }

  {
    remember (state_sm_on_event (mkSM (bind_upd X gY) (bind_init X)) (local_pred e)) as L.
    symmetry in HeqL.
    destruct L; simpl in *; ginv;[|].

    {
      destruct b.
      apply state_sm_on_event_bind_some_state_X in HeqL; rewrite HeqL.
      simpl in *.
      unfold run_main_process in eqs.
      destruct sx; simpl in *; tcsp.
      dest_cases w; symmetry in Heqw; simpl in *.
      dest_cases y; symmetry in Heqy; tcsp; GC.
      apply andb_true_iff in Heqy; repnd.
      destruct w0; simpl in *; tcsp.
    }

    pose proof (ind (local_pred e) (local_pred_is_direct_pred e d)) as h.
    autodimp h hyp.
    rewrite h; simpl; auto.
  }
Qed.

Lemma bind_state_implies :
  forall {SX SY T U}
         (X    : StateMachine SX msg (list T))
         (gY   : T -> StateMachine SY msg (list U))
         (eo   : EventOrdering)
         (e    : Event)
         (sxop : option SX)
         (sys  : list (T * SY))
         (t    : T)
         (sy   : SY),
    state_sm_on_event (mkSM (bind_upd X gY) (bind_init X)) e
    = Some (bind_state sxop sys)
    -> In (t,sy) sys
    ->
    exists (e'    : Event)
           (outxs : list T)
           (p     : e' ⊑ e),
      output_sm_on_event X e' = Some outxs
      /\ In t outxs
      /\ @state_sm_on_event _ _ _ _ _ (gY t) (subEventOrdering e') (mkSubOrderingLe p) = Some sy.
Proof.
  intros SX SY T U X gY eo.
  induction e as [e ind] using predHappenedBeforeInd.
  introv eqs i.
  rewrite state_sm_on_event_unroll in eqs.
  destruct (dec_isFirst e) as [d|d].

  {
    unfold bind_upd, mkSM in eqs; simpl in eqs.
    dest_cases w; symmetry in Heqw; simpl in *.
    dest_cases z; symmetry in Heqz; simpl in *; ginv.
    clear Heqz.
    rewrite map_map in *.
    allrw @mapOption_map; unfold compose in *; simpl in *.
    apply in_mapOption in i; exrepnd.
    dest_cases y; symmetry in Heqy; destruct y0; simpl in *; ginv.

    exists e w1 (localHappenedBeforeLe_refl e).
    dands; auto.

    + rewrite output_sm_on_event_unroll.
      destruct (dec_isFirst e); tcsp; GC.
      rewrite Heqw; simpl; auto.

    + rewrite state_sm_on_event_unroll.
      pose proof (isFirst_mkSubOrderingLe_eq (localHappenedBeforeLe_refl e)) as isFrefl.
      destruct (@dec_isFirst _ _ _ (subEventOrdering e) (mkSubOrderingLe (localHappenedBeforeLe_refl e)));
        [|assert False; tcsp].

      rewrite trigger_mkSubOrderingLe.
      rewrite Heqy; simpl; auto.
  }

  remember (state_sm_on_event (mkSM (bind_upd X gY) (bind_init X)) (local_pred e)) as Lop; symmetry in HeqLop.
  destruct Lop; simpl in *; ginv.

  unfold bind_upd in eqs.
  destruct b; simpl in *.
  unfold run_main_process in eqs; simpl in *.
  destruct sx; simpl in *; ginv.

  {
    dest_cases w; symmetry in Heqw; simpl in *.
    dest_cases z; symmetry in Heqz; simpl in *; ginv.
    apply andb_false_iff in Heqz; repnd.
    rewrite mapOption_map in i; unfold compose in i.
    apply in_mapOption in i; exrepnd.

    unfold run_sub_process in i0.
    dest_cases y; symmetry in Heqy; destruct y0; simpl in *; ginv.

    apply in_app_iff in i1; destruct i1 as [i1|i1].

    - pose proof (ind (local_pred e)
                      (local_pred_is_direct_pred e d)
                      (Some s)
                      sys0 t a) as h.
      repeat (autodimp h hyp).
      exrepnd.

      assert (e' ⊑ e) as q.
      { eapply localLe_trans;[exact p|].
        apply local_pred_le. }
      exists e' outxs q; dands; auto.
      rewrite state_sm_on_event_unroll.
      pose proof (not_first_sub_event_ordering eo e e' q) as nF; repeat (autodimp nF hyp).
      destruct (@dec_isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe q)) as [d1|d1]; tcsp; GC.
      rewrite (local_mkSubOrderingLe _ p).
      rewrite h0; simpl.
      rewrite Heqy; simpl; auto.

    - apply in_map_iff in i1; exrepnd; ginv.
      exists e w1 (localHappenedBeforeLe_refl e).
      dands; auto.

      { apply state_sm_on_event_bind_some_state_X in HeqLop; auto.
        rewrite output_sm_on_event_unroll; destruct (dec_isFirst e); tcsp; GC.
        rewrite HeqLop; simpl.
        rewrite Heqw; simpl; auto. }

      { rewrite state_sm_on_event_unroll.
        pose proof (isFirst_mkSubOrderingLe_eq (localHappenedBeforeLe_refl e)) as isFrefl.
        destruct (@dec_isFirst _ _ _ (subEventOrdering e) (mkSubOrderingLe (localHappenedBeforeLe_refl e)));
          [|assert False; tcsp].

        rewrite trigger_mkSubOrderingLe.
        rewrite Heqy; simpl; auto. }
  }

  {
    dest_cases w; symmetry in Heqw; simpl in *; ginv.
    autorewrite with core in *.
    rewrite mapOption_map in i; unfold compose in i.
    apply in_mapOption in i; exrepnd.
    unfold run_sub_process in i0.
    dest_cases y; symmetry in Heqy.
    destruct y0; simpl in *; ginv.

    pose proof (ind (local_pred e)
                    (local_pred_is_direct_pred e d)
                    None
                    sys0
                    t
                    a) as h.
    repeat (autodimp h hyp).
    exrepnd.

    assert (e' ⊑ e) as q.
    { eapply localLe_trans;[exact p|].
      apply local_pred_le. }

    exists e' outxs q; dands; auto.
    rewrite state_sm_on_event_unroll.
    pose proof (not_first_sub_event_ordering eo e e' q) as nF; repeat (autodimp nF hyp).
    destruct (@dec_isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe q)) as [d1|d1]; tcsp; GC.
    rewrite (local_mkSubOrderingLe _ p).
    rewrite h0; simpl.
    rewrite Heqy; simpl; auto.
  }
Qed.

Lemma implies_in_sub_component :
  forall {SX SY T U}
         (X  : StateMachine SX msg (list T))
         (gY : T -> StateMachine SY msg (list U))
         (eo : EventOrdering)
         (e' e : Event)
         (p : e' ⊑ e)
         t sy sop sys,
    In t (loutput_sm_on_event X e')
    -> @state_sm_on_event _ _ _ _ _ (gY t) (subEventOrdering e') (mkSubOrderingLe p) = Some sy
    -> state_sm_on_event (bind X gY) e = Some (bind_state sop sys)
    -> In (t,sy) sys.
Proof.
  intros SX SY T U X gY eo e'.
  induction e as [e ind] using predHappenedBeforeInd.
  introv iX eqsy eqsb.
  rewrite state_sm_on_event_unroll in eqsy.
  rewrite state_sm_on_event_unroll in eqsb.
  destruct (@dec_isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe p)) as [d1|d1].

  - apply isFirst_mkSubOrderingLe in d1; subst.
    rewrite trigger_mkSubOrderingLe in eqsy.
    destruct (dec_isFirst e) as [d2|d2].

    + rewrite loutput_sm_on_event_unroll in iX.
      destruct (dec_isFirst e); tcsp; GC.
      simpl in *.
      dest_cases w; symmetry in Heqw; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *; ginv.

      apply andb_false_iff in Heqy; repnd.
      allrw map_map.
      allrw @mapOption_map; unfold compose in *.
      apply in_mapOption; simpl.
      eexists; dands;[eauto|].
      dest_cases w; simpl in *; subst; simpl in *; auto.

    + remember (state_sm_on_event (bind X gY) (local_pred e)) as sbop.
      symmetry in Heqsbop; destruct sbop; simpl in *; ginv.
      destruct b; simpl in *.
      unfold run_main_process in *; simpl in *.
      destruct sx; simpl in *; ginv; tcsp.

      * dest_cases w; symmetry in Heqw.
        dest_cases y; symmetry in Heqy; simpl in *; ginv.
        clear Heqy.
        allrw @mapOption_map; unfold compose in *.
        allrw @mapOption_app.
        allrw in_app_iff.
        allrw @in_mapOption.
        rewrite loutput_sm_on_event_unroll in iX.
        destruct (dec_isFirst e); tcsp; GC.

        applydup @state_sm_on_event_bind_some_state_X in Heqsbop.
        rewrite Heqsbop0 in iX; simpl in iX.
        rewrite Heqw in iX; simpl in iX.

        right; exists (t, sm_state (gY t)).
        dands;[apply in_map_iff; eexists; dands; eauto|].
        simpl.
        dest_cases w; destruct w0; simpl in *; ginv.

      * dest_cases w; symmetry in Heqw; simpl in *; autorewrite with core in *; ginv.
        assert False; tcsp.
        rewrite loutput_sm_on_event_unroll in iX.
        destruct (dec_isFirst e); tcsp; GC.

        applydup @state_sm_on_event_bind_some_state_X in Heqsbop.
        rewrite Heqsbop0 in iX; simpl in iX; tcsp.

  - destruct (dec_isFirst e) as [d2|d2]; simpl in *; tcsp.

    + dup p as xx.
      apply isFirst_localHappenedBeforeLe_implies_eq in xx; auto; subst.
      destruct d1; apply isFirst_mkSubOrderingLe_eq.

    + apply not_isFirst_implies_le_local_pred in d1.
      rewrite (local_mkSubOrderingLe _ d1) in eqsy.

      remember (@state_sm_on_event _ _ _ _ _ (gY t) (subEventOrdering e') (mkSubOrderingLe d1)) as syop.
      symmetry in Heqsyop.
      destruct syop; simpl in *; ginv.

      remember (state_sm_on_event (bind X gY) (local_pred e)) as sbop.
      symmetry in Heqsbop.
      destruct sbop; simpl in *; ginv.
      destruct b.

      pose proof (ind (local_pred e) (local_pred_is_direct_pred e d2) d1 t s sx sys0) as q.
      repeat (autodimp q hyp).

      simpl in *.
      unfold run_main_process in *; simpl in *.
      destruct sx; simpl in *; tcsp.

      * dest_cases w; symmetry in Heqw; simpl in *.
        dest_cases y; symmetry in Heqy; simpl in *; ginv.
        allrw @mapOption_map; unfold compose.
        allrw @mapOption_app.
        apply in_app_iff; left.
        apply in_mapOption.
        eexists; dands;[eauto|].
        simpl.
        dest_cases w; simpl in *; subst; simpl in *; auto.

      * dest_cases y; symmetry in Heqy; simpl in *; ginv.
        autorewrite with core in *.
        allrw @mapOption_map; unfold compose in *.
        apply in_mapOption.
        eexists; dands;[eauto|].
        simpl.
        dest_cases w; simpl in *; subst; simpl in *; auto.
Qed.

Lemma implies_in_sub_component2 :
  forall {SX SY T U}
         (X  : StateMachine SX msg (list T))
         (gY : T -> StateMachine SY msg (list U))
         (eo : EventOrdering)
         (e' e : Event)
         (p : e' ⊑ e)
         t sy,
    In t (loutput_sm_on_event X e')
    -> @state_sm_on_event _ _ _ _ _ (gY t) (subEventOrdering e') (mkSubOrderingLe p) = Some sy
    -> state_sm_on_event (bind X gY) e = None
    -> False.
Proof.
  intros SX SY T U X gY eo e'.
  induction e as [e ind] using predHappenedBeforeInd.
  introv iX eqsy eqsb.
  rewrite state_sm_on_event_unroll in eqsy.
  rewrite state_sm_on_event_unroll in eqsb.
  destruct (@dec_isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe p)) as [d1|d1].

  - apply isFirst_mkSubOrderingLe in d1; subst.
    rewrite trigger_mkSubOrderingLe in eqsy.
    destruct (dec_isFirst e) as [d2|d2].

    + rewrite loutput_sm_on_event_unroll in iX.
      destruct (dec_isFirst e); tcsp; GC.
      simpl in *.
      dest_cases w; symmetry in Heqw; simpl in *.
      dest_cases y; symmetry in Heqy; simpl in *; ginv.

      apply andb_true_iff in Heqy; repnd.
      allrw map_map.
      allrw @mapOption_map; unfold compose in *.
      apply is_none_true_iff in Heqy0; subst; simpl in *.
      rewrite nullb_true_iff in Heqy.
      rewrite mapOption_nil in Heqy.
      apply Heqy in iX; simpl in *.
      dest_cases w; simpl in *; subst; simpl in *; ginv.

    + remember (state_sm_on_event (bind X gY) (local_pred e)) as sbop.
      symmetry in Heqsbop; destruct sbop; simpl in *; ginv.

      { destruct b; simpl in *.
        unfold run_main_process in *; simpl in *.
        destruct sx; simpl in *; ginv; tcsp.

        * dest_cases w; symmetry in Heqw.
          dest_cases y; symmetry in Heqy; simpl in *; ginv.

          apply andb_true_iff in Heqy; repnd.
          apply is_none_true_iff in Heqy0; subst; simpl in *.

          allrw @mapOption_map; unfold compose in *.
          allrw @mapOption_app.
          allrw @mapOption_map; unfold compose in *.
          rewrite nullb_true_iff in Heqy.
          apply app_eq_nil in Heqy; repnd.
          allrw @mapOption_nil.

          rewrite loutput_sm_on_event_unroll in iX.
          destruct (dec_isFirst e); tcsp; GC.

          applydup @state_sm_on_event_bind_some_state_X in Heqsbop.
          rewrite Heqsbop0 in iX; simpl in iX.
          rewrite Heqw in iX; simpl in iX.

          apply Heqy in iX; simpl in *.
          dest_cases z; symmetry in Heqz.
          destruct z0; simpl in *; ginv.

        * dest_cases w; symmetry in Heqw; simpl in *; autorewrite with core in *; ginv.
          assert False; tcsp.
          rewrite loutput_sm_on_event_unroll in iX.
          destruct (dec_isFirst e); tcsp; GC.

          applydup @state_sm_on_event_bind_some_state_X in Heqsbop.
          rewrite Heqsbop0 in iX; simpl in iX; tcsp. }

      { rewrite loutput_sm_on_event_unroll in iX.
        destruct (dec_isFirst e); tcsp; GC.

        applydup @state_sm_on_event_bind_none_state_X in Heqsbop.
        rewrite Heqsbop0 in iX; simpl in iX; tcsp. }

  - destruct (dec_isFirst e) as [d2|d2]; simpl in *; tcsp.

    + dup p as xx.
      apply isFirst_localHappenedBeforeLe_implies_eq in xx; auto; subst.
      destruct d1; apply isFirst_mkSubOrderingLe_eq.

    + apply not_isFirst_implies_le_local_pred in d1.
      rewrite (local_mkSubOrderingLe _ d1) in eqsy.

      remember (@state_sm_on_event _ _ _ _ _ (gY t) (subEventOrdering e') (mkSubOrderingLe d1)) as syop.
      symmetry in Heqsyop.
      destruct syop; simpl in *; ginv.

      remember (state_sm_on_event (bind X gY) (local_pred e)) as sbop.
      symmetry in Heqsbop.
      destruct sbop; simpl in *; ginv.

      { destruct b.

        pose proof (ind (local_pred e) (local_pred_is_direct_pred e d2) d1 t s) as q.
        repeat (autodimp q hyp).

        simpl in *.
        unfold run_main_process in *; simpl in *.
        destruct sx; simpl in *; tcsp.

        * dest_cases w; symmetry in Heqw; simpl in *.
          dest_cases y; symmetry in Heqy; simpl in *; ginv.
          allrw @mapOption_map; unfold compose in *.
          allrw @mapOption_app.
          allrw @mapOption_map; unfold compose in *.
          allrw andb_true_iff; repnd.
          allrw @is_none_true_iff; subst; simpl in *; ginv.
          allrw @nullb_true_iff.
          apply app_eq_nil in Heqy; repnd.
          allrw @mapOption_nil.

          eapply implies_in_sub_component in Heqsbop;
            [|exact iX|exact Heqsyop].
          apply Heqy0 in Heqsbop.
          simpl in *.
          dest_cases w; simpl in *; subst; simpl in *; auto; ginv.

        * dest_cases y; symmetry in Heqy; simpl in *; ginv.
          autorewrite with core in *.
          allrw @mapOption_map; unfold compose in *.
          allrw @nullb_true_iff.
          allrw @mapOption_nil.

          eapply implies_in_sub_component in Heqsbop;
            [|exact iX|exact Heqsyop].
          apply Heqy in Heqsbop.
          simpl in *.
          dest_cases w; simpl in *; subst; simpl in *; auto; ginv. }

      { apply ind in Heqsyop; auto.
        apply local_pred_is_direct_pred; auto. }
Qed.

Lemma output_bind_iff :
  forall {SX SY T U}
         (X  : StateMachine SX msg (list T))
         (gY : T -> StateMachine SY msg (list U))
         (eo : EventOrdering)
         (e  : Event)
         (u  : U),
    In u (loutput_sm_on_event (bind X gY) e)
    <->
    exists (e' : Event)
           (p  : e' ⊑ e)
           (t  : T),
      In t (loutput_sm_on_event X e')
      /\ In u (@loutput_sm_on_event _ _ _ _ _ (gY t) (subEventOrdering e') (mkSubOrderingLe p)).
Proof.
  introv; split; intro h; exrepnd.

  - rewrite loutput_sm_on_event_unroll in h.
    destruct (dec_isFirst e) as [d|d]; ginv; simpl in *.

    + exists e (localHappenedBeforeLe_refl e).
      rewrite loutput_sm_on_event_unroll.
      destruct (dec_isFirst e); tcsp; GC.

      dest_cases w; symmetry in Heqw; simpl in *.
      allrw flat_map_map; unfold compose in *.
      apply in_flat_map in h; exrepnd.

      exists x.
      dands; auto.

      rewrite loutput_sm_on_event_unroll.
      pose proof (isFirst_mkSubOrderingLe_eq (localHappenedBeforeLe_refl e)) as isFrefl.
      destruct (@dec_isFirst _ _ _ (subEventOrdering e) (mkSubOrderingLe (localHappenedBeforeLe_refl e)));
        [|assert False; tcsp].

      rewrite trigger_mkSubOrderingLe.
      unfold run_sub_process in h0; dest_cases w; destruct w2; simpl in *; ginv.

    + remember (state_sm_on_event (bind X gY) (local_pred e)) as sop; symmetry in Heqsop.
      destruct sop; simpl in *; ginv; tcsp;[].
      destruct b.

      unfold bind_upd in h.
      unfold run_main_process in h; simpl in *.
      destruct sx; simpl in *; ginv.

      * dest_cases w; symmetry in Heqw; simpl in *.

        allrw flat_map_map.
        unfold compose in *.

        apply in_flat_map in h; exrepnd.
        apply in_app_iff in h1; repndors.

        { eapply bind_state_implies in Heqsop;[|eauto].
          exrepnd.

          assert (e' ⊑ e) as q.
          { eapply localLe_trans;[exact p|].
            apply local_pred_le. }

          exists e' q x0; dands; auto.

          { unfold loutput_sm_on_event; rewrite Heqsop1; simpl; auto. }

          rewrite loutput_sm_on_event_unroll.
          pose proof (not_first_sub_event_ordering eo e e' q) as nF; repeat (autodimp nF hyp).
          destruct (@dec_isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe q)) as [d1|d1]; tcsp; GC.
          rewrite (local_mkSubOrderingLe _ p).
          rewrite Heqsop0; simpl.
          unfold run_sub_process in h0.
          dest_cases w; simpl in *.
          destruct w2; simpl in *; auto. }

        { apply in_map_iff in h1; exrepnd; ginv.
          exists e (localHappenedBeforeLe_refl e) x0.
          dands; auto.

          - apply state_sm_on_event_bind_some_state_X in Heqsop.
            rewrite loutput_sm_on_event_unroll.
            destruct (dec_isFirst e); tcsp; GC.
            rewrite Heqsop; simpl.
            rewrite Heqw; simpl; auto.

          - rewrite loutput_sm_on_event_unroll.
            pose proof (isFirst_mkSubOrderingLe_eq (localHappenedBeforeLe_refl e)) as isFrefl.
            destruct (@dec_isFirst _ _ _ (subEventOrdering e) (mkSubOrderingLe (localHappenedBeforeLe_refl e)));
              [|assert False; tcsp].

            rewrite trigger_mkSubOrderingLe.
            unfold run_sub_process in h0; dest_cases w; destruct w2; ginv. }

      * allrw flat_map_map; autorewrite with core in *; unfold compose in *.
        rewrite in_flat_map in h; exrepnd.

        eapply bind_state_implies in Heqsop;[|eauto].
        exrepnd.

        assert (e' ⊑ e) as q.
        { eapply localLe_trans;[exact p|].
          apply local_pred_le. }

        exists e' q x0.
        dands; auto.

        { unfold loutput_sm_on_event; rewrite Heqsop1; simpl; auto. }

        rewrite loutput_sm_on_event_unroll.

        destruct (@dec_isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe q)) as [d1|d1];
          simpl in *; ginv;[|].

        {
          applydup isFirst_mkSubOrderingLe in d1; subst.
          dup p as lpd.
          apply event_le_local_pred in lpd.
          rewrite state_sm_on_event_unroll in Heqsop0.
          dest_cases w.
        }

        {
          rewrite (local_mkSubOrderingLe _ p).
          rewrite Heqsop0; simpl.
          dest_cases w; symmetry in Heqw.
          destruct w0; simpl in *; auto.
        }

  - rewrite loutput_sm_on_event_unroll.
    destruct (dec_isFirst e) as [d|d]; simpl.

    + assert (e' = e) as xx.
      { destruct p as [p1 p2].
        apply (isFirst_loc_implies_causal e e') in d; auto.
        destruct p1 as [p1|p1]; auto.
        destruct d as [d|d]; auto.
        eapply causal_trans in d;[|exact p1].
        apply causal_anti_reflexive in d; tcsp. }
      subst.

      dest_cases w; symmetry in Heqw; simpl in *.
      allrw flat_map_map; unfold compose; simpl.
      apply in_flat_map.
      rewrite loutput_sm_on_event_unroll in h1.
      destruct (dec_isFirst e) as [d1|d1]; tcsp; GC.
      rewrite Heqw in h1; simpl in h1.

      exists t; dands; auto.
      rewrite loutput_sm_on_event_unroll in h0.

      pose proof (isFirst_mkSubOrderingLe_eq p) as isFrefl.
      destruct (@dec_isFirst _ _ _ (subEventOrdering e) (mkSubOrderingLe p));
        [|assert False; tcsp]; GC.

      rewrite trigger_mkSubOrderingLe in h0.
      dest_cases y; symmetry in Heqy; destruct y0; simpl in *; tcsp.

    + remember (state_sm_on_event (bind X gY) (local_pred e)) as sop.
      destruct sop; simpl; symmetry in Heqsop.

      * destruct b.
        unfold bind_upd, run_main_process; simpl.
        destruct sx; simpl.

        {
          dest_cases w; symmetry in Heqw; simpl in *.
          allrw flat_map_map; unfold compose; simpl.
          rewrite flat_map_app.
          rewrite flat_map_map; unfold compose.
          rewrite in_app_iff.

          rewrite loutput_sm_on_event_unroll in h0.
          destruct (@dec_isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe p)) as [d1|d1].

          {
            applydup isFirst_mkSubOrderingLe in d1; subst.
            rewrite loutput_sm_on_event_unroll in h1.
            destruct (dec_isFirst e) as [d2|d2]; tcsp; GC; simpl in *.
            applydup @state_sm_on_event_bind_some_state_X in Heqsop.
            rewrite Heqsop0 in h1; simpl in h1.
            rewrite Heqw in h1; simpl in h1.
            right; apply in_flat_map.
            exists t; dands; auto.
            dest_cases w; simpl in *; destruct w2; simpl in *; auto.
          }

          {
            pose proof (localHappenedBeforeLe_implies_or p) as q.
            repndors; subst;
              [destruct d1; apply isFirst_mkSubOrderingLe_eq|].

            rewrite (local_mkSubOrderingLe _ q) in h0.
            rewrite trigger_mkSubOrderingLe in h0.

            remember (@state_sm_on_event _ _ _ _ _ (gY t) (subEventOrdering e') (mkSubOrderingLe q)) as syop.
            destruct syop; simpl in *; ginv; tcsp;[].
            symmetry in Heqsyop.

            left.
            apply in_flat_map.
            exists (t,s0); dands; auto;
              [|unfold run_sub_process; dest_cases w; simpl in *;
                destruct w2; simpl in *; auto].

            eapply implies_in_sub_component in Heqsop;
              [|exact h1|exact Heqsyop]; auto.
          }
        }

        {
          allrw flat_map_map; unfold compose; autorewrite with core.
          apply in_flat_map; simpl.

          rewrite loutput_sm_on_event_unroll in h0.
          destruct (@dec_isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe p)) as [d1|d1].

          {
            applydup isFirst_mkSubOrderingLe in d1; subst.
            rewrite loutput_sm_on_event_unroll in h1.
            destruct (dec_isFirst e) as [d2|d2]; tcsp; GC; simpl in *.
            applydup @state_sm_on_event_bind_some_state_X in Heqsop.
            rewrite Heqsop0 in h1; simpl in h1; tcsp.
          }

          {
            pose proof (localHappenedBeforeLe_implies_or p) as q.
            repndors; subst;
              [destruct d1; apply isFirst_mkSubOrderingLe_eq|].

            rewrite (local_mkSubOrderingLe _ q) in h0.
            rewrite trigger_mkSubOrderingLe in h0.

            remember (@state_sm_on_event _ _ _ _ _ (gY t) (subEventOrdering e') (mkSubOrderingLe q)) as syop.
            destruct syop; simpl in *; ginv; tcsp;[].
            symmetry in Heqsyop.

            exists (t,s); dands; auto;
              [|unfold run_sub_process; dest_cases w; simpl in *; destruct w0; simpl in *; tcsp].

            eapply implies_in_sub_component in Heqsop;
              [|exact h1|exact Heqsyop]; auto.
          }
        }

      * rewrite loutput_sm_on_event_unroll in h0.
        destruct (@dec_isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe p)) as [d1|d1].

        {
          applydup isFirst_mkSubOrderingLe in d1; subst.
          rewrite loutput_sm_on_event_unroll in h1.
          destruct (dec_isFirst e) as [d2|d2]; tcsp; GC; simpl in *.
          remember (state_sm_on_event X (local_pred e)) as sx; symmetry in Heqsx.
          destruct sx; simpl in *; ginv.
          apply state_sm_on_event_bind_none_state_X in Heqsop.
          rewrite Heqsop in Heqsx; ginv.
        }

        {
          pose proof (localHappenedBeforeLe_implies_or p) as q.
          repndors; subst;
            [destruct d1; apply isFirst_mkSubOrderingLe_eq|].

          rewrite (local_mkSubOrderingLe _ q) in h0.
          rewrite trigger_mkSubOrderingLe in h0.

          remember (@state_sm_on_event _ _ _ _ _ (gY t) (subEventOrdering e') (mkSubOrderingLe q)) as syop.
          destruct syop; simpl in *; ginv; tcsp;[].
          symmetry in Heqsyop.

          eapply implies_in_sub_component2 in Heqsop;
            [|exact h1|exact Heqsyop]; auto.
        }
Qed.

End Bind.


Open Scope proc.
Notation "a [>>=] f" := (nbind a f) (at level 100) : proc.
Close Scope proc.
