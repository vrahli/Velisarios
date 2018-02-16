(*

  Copyright 2016 Luxembourg University
  Copyright 2017 Luxembourg University
  Copyright 2018 Luxembourg University

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


Require Export PBFTwell_formed_log.
Require Export PBFTordering.
Require Export PBFTprops3.
Require Export PBFTnew_view_in_log.
Require Export PBFTwf_view_change_state.
Require Export PBFT_A_1_2_5.
Require Export PBFT_A_1_2_2.


Section PBFT_A_1_2_4.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition is_current_view (st : PBFTstate) v : Prop :=
    current_view st = v.

  Lemma is_current_view_initial_state_eq :
    forall st v,
      is_current_view (initial_state st) v <-> v = initial_view.
  Proof.
    introv; unfold is_current_view; simpl; split; tcsp.
  Qed.
  Hint Rewrite is_current_view_initial_state_eq : pbft.

  Lemma is_current_view_log_new_pre_prepare :
    forall st p d v,
      is_current_view (log_new_pre_prepare st p d) v <-> is_current_view st v.
  Proof.
    introv; unfold is_current_view; simpl; sp.
  Qed.
  Hint Rewrite is_current_view_log_new_pre_prepare : pbft.

  Lemma is_current_view_increment_sequence_number :
    forall st v,
      is_current_view (increment_sequence_number st) v
      <-> is_current_view st v.
  Proof.
    introv; unfold is_current_view; simpl; sp.
  Qed.
  Hint Rewrite is_current_view_increment_sequence_number : pbft.

  Lemma is_current_view_update_primary_state :
    forall st ps v,
      is_current_view (update_primary_state st ps) v
      <-> is_current_view st v.
  Proof.
    introv; unfold is_current_view; simpl; sp.
  Qed.
  Hint Rewrite is_current_view_update_primary_state : pbft.

  Lemma is_current_view_gt :
    forall st v,
      is_current_view st v
      -> 0 < v
      -> 0 < current_view st.
  Proof.
    introv iscv ltv.
    unfold is_current_view in iscv; subst; auto.
  Qed.
  Hint Resolve is_current_view_gt : pbft.

  Lemma is_current_view_same :
    forall st v1 v2,
      is_current_view st v1
      -> is_current_view st v2
      -> v1 = v2.
  Proof.
    introv isc1 isc2; unfold is_current_view in *; subst; auto.
  Qed.

  Lemma check_send_replies_preserves_is_current_view :
    forall slf view keys entryop state sn msgs state' v,
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> is_current_view state' v
      -> is_current_view state v.
  Proof.
    introv chk iscv.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_is_current_view : pbft.

  Lemma is_current_view_update_log :
    forall st L v,
      is_current_view (update_log st L) v <-> is_current_view st v.
  Proof.
    introv; unfold is_current_view; simpl; sp.
  Qed.
  Hint Rewrite is_current_view_update_log : pbft.

  Lemma check_stable_preserves_is_current_view :
    forall i st1 cs st2 v,
      check_stable i st1 cs = Some st2
      -> is_current_view st2 v
      -> is_current_view st1 v.
  Proof.
    introv check isc.
    apply check_stable_preserves_current_view in check.
    unfold is_current_view in *; subst; auto.
  Qed.

  Lemma is_current_view_update_checkpoint_state :
    forall st cs v,
      is_current_view (update_checkpoint_state st cs) v <-> is_current_view st v.
  Proof.
    introv; unfold is_current_view; simpl; tcsp.
  Qed.
  Hint Rewrite is_current_view_update_checkpoint_state : pbft.

  Lemma current_view_decrement_requests_in_progress_if_primary :
    forall i v st,
      current_view (decrement_requests_in_progress_if_primary i v st)
      = current_view st.
  Proof.
    introv.
    unfold decrement_requests_in_progress_if_primary; simpl; smash_pbft.
  Qed.
  Hint Rewrite current_view_decrement_requests_in_progress_if_primary : pbft.

  Lemma is_current_view_decrement_requests_in_progress_if_primary :
    forall i v st x,
      is_current_view (decrement_requests_in_progress_if_primary i v st) x
      <-> is_current_view st x.
  Proof.
    introv.
    unfold is_current_view.
    unfold decrement_requests_in_progress_if_primary; simpl; smash_pbft; tcsp.
  Qed.
  Hint Rewrite is_current_view_decrement_requests_in_progress_if_primary : pbft.

  Lemma find_and_execute_requests_preserves_is_current_view :
    forall i v keys st msgs st' x,
      find_and_execute_requests i v keys st = (msgs, st')
      -> is_current_view st' x
      -> is_current_view st x.
  Proof.
    introv h.
    apply find_and_execute_requests_preserves_current_view in h.
    unfold is_current_view; allrw; auto.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_is_current_view : pbft.

  Lemma eq_views :
    forall (v1 v2 : View),
      v1 = v2 <-> view2nat v1 = view2nat v2.
  Proof.
    introv; destruct v1, v2; simpl in *; split; intro h; subst; tcsp; ginv; auto.
  Qed.

  Lemma is_current_view_update_view :
    forall st v x,
      is_current_view (update_view st v) x
      <-> if lt_dec (current_view st) v then x = v
          else is_current_view st x.
  Proof.
    introv; unfold is_current_view; destruct st; simpl.
    unfold max_view; smash_pbft; split; intro h; subst; simpl in *;
      tcsp; try omega;
        simpl in *;
        try (complete (apply eq_views; simpl; omega));
        try (complete (allrw ViewLe_false; simpl in *; omega)).
  Qed.

  Lemma implies_max_view_right :
    forall (a b : View), a <= b -> max_view a b = b.
  Proof.
    introv h; destruct a, b; simpl in *.
    apply eq_views; simpl; unfold max_view; smash_pbft.
    allrw ViewLe_false; simpl in *; omega.
  Qed.

  Lemma implies_max_view_left :
    forall (a b : View), b <= a -> max_view a b = a.
  Proof.
    introv h; destruct a, b; simpl in *.
    apply eq_views; simpl; unfold max_view; smash_pbft.
    simpl in *; omega.
  Qed.

  Ltac is_current_view_simplifier :=
    match goal with
    | [ H1 : is_current_view ?s ?v1, H2 : is_current_view ?s ?v2 |- _ ] =>
      let h := fresh "h" in
      pose proof (is_current_view_same s v1 v2 H1 H2) as h; subst; GC

    | [ H : is_current_view ?s initial_view |- _ ] =>
      unfold is_current_view in H; rewrite H in *; simpl in *; omega
    end.

  Ltac fold_is_current_view :=
    let cv := fresh "cv" in
    match goal with
    | [ H : context[current_view ?x] |- _ ] => remember (current_view x) as cv
    end;
    match goal with
    | [ H : cv = current_view ?x |- _ ] =>
      symmetry in H; fold (is_current_view x cv) in H
    end.

  Ltac rewrite_is_current_view :=
    match goal with
    | [ H : is_current_view ?s _, H' : context[current_view ?s] |- _ ] => rewrite H in *
    | [ H : is_current_view ?s _ |- context[current_view ?s] ] => rewrite H in *
    end.

  Ltac smash_pbft_ind2 ind :=
    let d   := fresh "d" in
    let hyp := fresh "hyp" in
    match goal with
    | [ H : state_sm_before_event ?sm ?e = Some ?s |- _ ] =>
      let K := fresh H in
      rewrite <- ite_first_state_sm_on_event_as_before in H;
      unfold ite_first in H;
      destruct (dec_isFirst e) as [d|d]; ginv;
      try (complete (clear_current_view; simpl in *; simplifier; smash_pbft));
      try (complete (fold_is_current_view; ginv; autorewrite with pbft in *; subst;
                     simpl in *; try omega; repeat is_current_view_simplifier));
      first[fail
           |idtac;[];
            repeat (autodimp ind hyp);
            first[fail
                 |idtac;[];
                  dup H as K;
                  eapply ind in K; eauto; clear ind;
                  repeat rewrite_is_current_view;
                  eauto 2 with pbft;
                  exrepnd;
                  repeat (eexists;[]);
                  dands; eauto; eauto 3 with eo pbft;
                  complete (repndors; tcsp; try cpltLR)
                 ]
           ]
    end.

  Fixpoint find_new_view_entry
           (S : PBFTviewChangeState)
           (v : View) : option PBFTviewChangeEntry :=
    match S with
    | [] => None
    | entry :: entries =>
      if ViewDeq v (vce_view entry) then Some entry
      else find_new_view_entry entries v
    end.

  Lemma find_implies_new_view_in_log :
    forall S v entry nv,
      find_new_view_entry S v = Some entry
      -> vce_new_view entry = Some nv
      -> v = new_view2view nv (* follows from wf_view_change_state S *)
      -> new_view_in_log nv S.
  Proof.
    induction S; introv f e eqv; simpl in *; tcsp.
    smash_pbft.
  Qed.

  Lemma find_new_view_entry_implies_in :
    forall S v entry,
      find_new_view_entry S v = Some entry
      -> In entry S /\ vce_view entry = v.
  Proof.
    induction S; introv f; simpl in *; tcsp; smash_pbft.
    apply IHS in f; tcsp.
  Qed.

  Lemma find_in_wf_view_change_state_implies_same_view :
    forall S v entry nv,
      wf_view_change_state S
      -> find_new_view_entry S v = Some entry
      -> vce_new_view entry = Some nv
      -> v = new_view2view nv.
  Proof.
    introv wf find eqnv.
    apply find_new_view_entry_implies_in in find; repnd.
    applydup wf_view_change_state_implies_all_entries in find0; auto.
    subst.
    inversion find1 as [wfvc wfvcs wfnv]; clear find1.
    destruct entry; simpl in *; subst.
    symmetry; apply wfnv; auto.
  Qed.
  Hint Resolve find_in_wf_view_change_state_implies_same_view : pbft.

  Lemma add_new_view_to_entry_cancel_if_find :
    forall entry nv nv',
      vce_new_view entry = Some nv'
      -> add_new_view_to_entry entry nv = entry.
  Proof.
    introv e; destruct entry; simpl in *.
    subst; simpl in *; auto.
  Qed.

  Lemma log_new_view_cancel_if_find :
      forall S v nv entry nv',
        find_new_view_entry S v = Some entry
        -> vce_new_view entry = Some nv'
        -> v = new_view2view nv
        -> log_new_view S nv = S.
  Proof.
    induction S; introv find eqnv eqv; simpl in *; tcsp.
    smash_pbft; tcsp.

    - erewrite add_new_view_to_entry_cancel_if_find; eauto.

    - f_equal.
      eapply IHS; eauto.
  Qed.

  Lemma new_view_in_log_implies_exists_entry_in :
    forall nv S,
      new_view_in_log nv S
      ->
      exists e,
        In e S
        /\ vce_new_view e = Some nv.
  Proof.
    induction S; introv i; simpl in *; tcsp; smash_pbft.

    - exists a; tcsp.

    - apply IHS in i; exrepnd.
      exists e; dands; tcsp.
  Qed.

  Lemma in_view_change_state_implies_new_view_in_log :
    forall e nv S,
      In e S
      -> vce_new_view e = Some nv
      -> wf_view_change_state S
      -> new_view_in_log nv S.
  Proof.
    induction S; introv i eqnv wf; simpl in *; tcsp.
    inversion wf as [|? ? imp wfa wfs]; clear wf; subst; simpl in *.
    repndors; subst; smash_pbft.

    - apply wfa in eqnv; tcsp.

    - repeat (autodimp IHS hyp).
      apply new_view_in_log_implies_exists_entry_in in IHS; exrepnd.
      applydup imp in IHS1; tcsp.
      destruct IHS2.
      apply wf_view_change_entry_new_view in IHS0; eauto 2 with pbft;[].
      allrw; auto.
  Qed.
  Hint Resolve in_view_change_state_implies_new_view_in_log : pbft.

  Lemma has_new_view_implies_exists_correct_new_view_in_log :
    forall (v : View) st,
      0 < v
      -> wf_view_change_state st
      -> has_new_view st v = true
      -> exists V OP NP a0,
          new_view_in_log (mk_new_view v V OP NP a0) st
          (*/\ correct_new_view (mk_new_view v V OP NP a0) = true*).
  Proof.
    introv ltv wf hnv.
    unfold has_new_view in hnv; smash_pbft; simpl in *; try omega.
    unfold has_new_view1 in hnv.
    rewrite existsb_exists in hnv; exrepnd.
    smash_pbft.
    destruct n0, v; simpl in *.

    assert (wf_view_change_entry x) as wfx by eauto with pbft.

    match goal with
    | [ H : vce_new_view _ = _ |- _ ] =>
      applydup wf_view_change_entry_new_view in H; auto
    end.
    simpl in *; subst.

    exists V OP NP a; dands; auto; eauto 2 with pbft.
  Qed.

  (* see Invariant A.1.2 (4) in PBFT PhD p.145 *)
  Lemma pre_prepare_from_primary_implies_exists_new_view :
    forall (eo : EventOrdering)
           (e       : Event)
           (slf     : Rep)
           (n       : SeqNum)
           (v       : View)
           (a       : Tokens)
           (d       : PBFTdigest)
           (rs      : list Request)
           (state   : PBFTstate),
      0 < v
      -> state_sm_on_event (PBFTreplicaSM slf) e = Some state
      -> pre_prepare_in_log (mk_pre_prepare v n rs a) d (log state) = true
      ->
      exists V OP NP a,
        new_view_in_log (mk_new_view v V OP NP a) (view_change_state state)
        /\ correct_new_view (mk_new_view v V OP NP a) = true.
  Proof.
    introv lt0v eqst prep.
    dup eqst as hnv.
    eapply pre_prepare_in_log_implies_has_new_view in hnv;[|eauto]; auto.
    simpl in *.

    eapply has_new_view_implies_exists_correct_new_view_in_log in hnv; auto; eauto 2 with pbft.
    exrepnd.
    exists V OP NP a0; dands; auto.
    eapply PBFT_A_1_2_5; eauto.
  Qed.

End PBFT_A_1_2_4.
