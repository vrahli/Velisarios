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


Require Export PBFTprops4.
Require Export PBFTwf_view_change_state.
Require Export PBFTtactics3.


Section PBFThas_new_view.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma check_send_replies_preserves_view_change_state :
    forall i v keys gi st n msgs st',
      check_send_replies i v keys gi st n = (msgs, st')
      -> view_change_state st' = view_change_state st.
  Proof.
    introv check.
    unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_view_change_state : pbft.

  Definition has_nv s v := has_new_view s v = true.

  Lemma check_send_replies_preserves_has_new_view :
    forall i v keys gi st n msgs st' w,
      check_send_replies i v keys gi st n = (msgs, st')
      -> has_nv (view_change_state st) w
      -> has_nv (view_change_state st') w.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve check_send_replies_preserves_has_new_view : pbft.

  Lemma check_send_replies_update_log_preserves_has_new_view :
    forall i v keys gi st L n msgs st' w,
      check_send_replies i v keys gi (update_log st L) n = (msgs, st')
      -> has_nv (view_change_state st) w
      -> has_nv (view_change_state st') w.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_has_new_view : pbft.

  Lemma check_stable_preserves_view_change_state :
    forall slf cp_entry st st',
      check_stable slf st cp_entry = Some st'
      -> view_change_state st' = view_change_state st.
  Proof.
    introv check.
    unfold check_stable in check; smash_pbft.
  Qed.
  Hint Resolve check_stable_preserves_view_change_state : pbft.

  Lemma check_stable_preserves_has_new_view :
    forall slf cp_entry st st' v,
      check_stable slf st cp_entry = Some st'
      -> has_nv (view_change_state st) v
      -> has_nv (view_change_state st') v.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve check_stable_preserves_has_new_view : pbft.

  Lemma check_stable_update_checkpoint_state_preserves_has_new_view :
    forall i st C entry st' v,
      check_stable i (update_checkpoint_state st C) entry = Some st'
      -> has_nv (view_change_state st) v
      -> has_nv (view_change_state st') v.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve check_stable_update_checkpoint_state_preserves_has_new_view : pbft.

  Lemma view_change_state_decrement_requests_in_progress :
    forall i v s,
      view_change_state (decrement_requests_in_progress_if_primary i v s)
      = view_change_state s.
  Proof.
    introv; destruct s; unfold decrement_requests_in_progress_if_primary; smash_pbft.
  Qed.
  Hint Rewrite view_change_state_decrement_requests_in_progress : pbft.

  Lemma find_and_execute_preserves_view_change_state :
    forall v keys slf msg st st',
      find_and_execute_requests slf v keys st = (msg, st')
      -> view_change_state st' = view_change_state st.
  Proof.
    introv find.
    unfold find_and_execute_requests in find; smash_pbft.
    unfold execute_requests in *.
    remember (ready st) as xx.
    destruct xx;  symmetry in Heqxx; inversion Heqx; tcsp;
      unfold check_broadcast_checkpoint in *; smash_pbft.
  Qed.
  Hint Resolve find_and_execute_preserves_view_change_state : pbft.

  Lemma find_and_execute_preserves_has_new_view :
    forall v keys slf msg st st' w,
      find_and_execute_requests slf v keys st = (msg, st')
      -> has_nv (view_change_state st) w
      -> has_nv (view_change_state st') w.
  Proof.
    introv find.
    apply find_and_execute_preserves_view_change_state in find.
    unfold has_new_view; allrw; tcsp.
  Qed.
  Hint Resolve find_and_execute_preserves_has_new_view : pbft.

  Lemma implies_or_in_log_new_view :
    forall e nv s,
      In e s
      ->
      (
        In e (log_new_view s nv)
        \/
        In (add_new_view_to_entry e nv) (log_new_view s nv)
      ).
  Proof.
    induction s; introv i; simpl in *; tcsp.
    repndors; subst; tcsp; smash_pbft.
    apply IHs in i; tcsp.
  Qed.

  Lemma vce_view_add_new_view_to_entry :
    forall e nv,
      vce_view (add_new_view_to_entry e nv) = vce_view e.
  Proof.
    destruct e; introv; destruct vce_new_view; simpl; auto.
  Qed.
  Hint Rewrite vce_view_add_new_view_to_entry : pbft.

  Lemma vce_new_view_add_new_view_to_entry_some_implies :
    forall e nv nv',
      vce_new_view (add_new_view_to_entry e nv) = Some nv'
      ->
      (
        vce_new_view e = Some nv'
        \/
        nv = nv'
      ).
  Proof.
    introv h.
    destruct e; simpl in *.
    destruct vce_new_view; simpl in *; ginv; tcsp.
  Qed.

  Lemma vce_new_view_add_new_view_to_entry_none_implies :
    forall e nv,
      vce_new_view (add_new_view_to_entry e nv) = None
      -> vce_new_view e = None.
  Proof.
    introv h; destruct e; simpl in *.
    destruct vce_new_view; simpl in *; tcsp.
  Qed.

  Lemma log_new_view_state_preserves_has_new_view :
    forall st nv v,
      correct_new_view nv = true
      -> has_nv (view_change_state st) v
      -> has_nv (log_new_view (view_change_state st) nv) v.
  Proof.
    introv cor h.
    unfold has_nv, has_new_view in *; smash_pbft.
    unfold has_new_view1 in *.
    allrw existsb_exists; exrepnd; smash_pbft.
    apply (implies_or_in_log_new_view x nv) in h1.
    repndors.

    - eexists; smash_pbft; dands; auto.

    - eexists; dands; eauto; autorewrite with pbft; smash_pbft;[].

      match goal with
      | [ H : vce_new_view (add_new_view_to_entry _ _) = _ |- _ ] =>
        apply vce_new_view_add_new_view_to_entry_none_implies in H
      end.

      match goal with
      | [ H1 : ?x = Some _, H2 : ?x = None |- _ ] => rewrite H1 in H2; ginv; auto
      end.
  Qed.
  Hint Resolve log_new_view_state_preserves_has_new_view : pbft.

  Lemma vce_view_add_own_view_change2entry :
    forall vc e,
      vce_view (add_own_view_change2entry vc e) = vce_view e.
  Proof.
    introv; destruct e; simpl; destruct vce_view_change; simpl; auto.
  Qed.
  Hint Rewrite vce_view_add_own_view_change2entry : pbft.

  Lemma vce_new_view_add_own_view_change2entry :
    forall vc e,
      vce_new_view (add_own_view_change2entry vc e) = vce_new_view e.
  Proof.
    introv; destruct e; simpl; destruct vce_view_change; simpl; auto.
  Qed.
  Hint Rewrite vce_new_view_add_own_view_change2entry : pbft.

  Lemma add_own_view_change_to_state_preserves_has_new_view :
    forall vc s1 s2 v e n,
      add_own_view_change_to_state vc s1 = (e, n, s2)
      -> has_nv s1 v
      -> has_nv s2 v.
  Proof.
    induction s1; introv add h; simpl in *; smash_pbft.

    - unfold has_nv, has_new_view in *; simpl in *; smash_pbft.

    - clear IHs1.
      unfold has_nv, has_new_view in *; simpl in *; smash_pbft; repndors; tcsp.

    - pose proof (IHs1 x1 v e x3) as q; autodimp q hyp; clear IHs1.
      unfold has_nv, has_new_view in *; smash_pbft.
  Qed.
  Hint Resolve add_own_view_change_to_state_preserves_has_new_view : pbft.

  Lemma start_view_change_preserves_has_new_view :
    forall vc s1 s2 v e n,
      start_view_change vc s1 = (e, n, s2)
      -> has_nv s1 v
      -> has_nv s2 v.
  Proof.
    introv start h.
    unfold start_view_change in start; eauto 2 with pbft.
  Qed.
  Hint Resolve start_view_change_preserves_has_new_view : pbft.

  Lemma add_other_view_change_preserves_has_new_view :
    forall s1 v vc e n s2,
      has_nv s1 v
      -> add_other_view_change vc s1 = Some (e, n, s2)
      -> has_nv s2 v.
  Proof.
    induction s1; introv h add; simpl in *; smash_pbft.

    - unfold has_nv, has_new_view in *; smash_pbft.

    - clear IHs1.
      unfold has_nv, has_new_view in *; simpl in *; smash_pbft; repndors; tcsp;
        destruct a; simpl in *; smash_pbft.

    - unfold has_nv, has_new_view in *; smash_pbft; repndors; tcsp;[|].

      + pose proof (IHs1 (vce_view a) vc e n x2) as q; smash_pbft.

      + pose proof (IHs1 (vce_view a) vc e n x2) as q; smash_pbft;
          pose proof (IHs1 v vc e n x2) as w; smash_pbft.
  Qed.
  Hint Resolve add_other_view_change_preserves_has_new_view : pbft.

  Lemma view_change_state_update_checkpoint_from_new_view :
    forall s c n,
      view_change_state (update_checkpoint_from_new_view s c n) = view_change_state s.
  Proof.
    introv; unfold update_checkpoint_from_new_view; smash_pbft.
  Qed.
  Hint Rewrite view_change_state_update_checkpoint_from_new_view : pbft.

  Lemma view_change_state_trim_checkpoint :
    forall s cop,
      view_change_state (trim_checkpoint s cop) = view_change_state s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite view_change_state_trim_checkpoint : pbft.

  Lemma log_checkpoint_cert_from_new_view_preserves_has_new_view :
    forall i s1 v n C S s2 msgs w,
      log_checkpoint_cert_from_new_view i s1 v n C S = (s2, msgs)
      -> has_nv (view_change_state s1) w
      -> has_nv (view_change_state s2) w.
  Proof.
    introv lc h; unfold log_checkpoint_cert_from_new_view in lc; smash_pbft.
  Qed.
  Hint Resolve log_checkpoint_cert_from_new_view_preserves_has_new_view : pbft.

  Lemma update_state_new_view_preserves_has_new_view :
    forall i s1 nv v s2 msgs,
      update_state_new_view i s1 nv = (s2, msgs)
      -> has_nv (view_change_state s1) v
      -> has_nv (view_change_state s2) v.
  Proof.
    introv upd h.
    unfold update_state_new_view in upd; smash_pbft.
    simpl in *; smash_pbft.
  Qed.
  Hint Resolve update_state_new_view_preserves_has_new_view : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_has_new_view :
    forall i P s1 s2 M v,
      add_prepare_to_log_from_new_view_pre_prepare i s1 P = (s2, M)
      -> has_nv (view_change_state s1) v
      -> has_nv (view_change_state s2) v.
  Proof.
    destruct P; introv add h; simpl in *; smash_pbft.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_has_new_view : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_has_new_view :
    forall i P s1 s2 M v,
      add_prepares_to_log_from_new_view_pre_prepares i s1 P = (s2, M)
      -> has_nv (view_change_state s1) v
      -> has_nv (view_change_state s2) v.
  Proof.
    induction P; introv add h; simpl in *; smash_pbft.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_has_new_view : pbft.

  Lemma implies_or_in_log_new_view_and_entry :
    forall x e nv s,
      In e s
      ->
      (
        In e (log_new_view_and_entry s nv x)
        \/
        (
          In (add_new_view_to_entry x nv) (log_new_view_and_entry s nv x)
          /\ vce_view e = new_view2view nv
        )
      ).
  Proof.
    induction s; introv i; simpl in *; tcsp.
    repndors; subst; tcsp; smash_pbft.
    apply IHs in i; tcsp.
  Qed.

  Lemma wf_view_change_state_implies_two_equal :
    forall e1 e2 s,
      wf_view_change_state s
      -> In e1 s
      -> In e2 s
      -> vce_view e1 = vce_view e2
      -> e1 = e2.
  Proof.
    induction s; introv wf i1 i2 eqvs; simpl in *; tcsp.
    inversion wf as [|? ? imp wf1 wf2]; clear wf; subst.
    repndors; subst; tcsp.

    - apply imp in i1; tcsp.

    - apply imp in i2; tcsp.
  Qed.

  Lemma check_broadcast_new_view_preserves_new_view_of_entry :
    forall i s e nv e' O N x,
      wf_view_change_state (view_change_state s)
      -> check_broadcast_new_view i s e = Some (nv, e', O, N)
      -> In e (view_change_state s)
      -> In x (view_change_state s)
      -> vce_view x = vce_view e'
      -> vce_new_view x = vce_new_view e'.
  Proof.
    introv wf check j k eqvs.
    unfold check_broadcast_new_view in *; smash_pbft.
    unfold view_changed_entry in *; smash_pbft.
    eapply wf_view_change_state_implies_two_equal in j; try (exact k); auto.
    subst; auto.
  Qed.

  Lemma has_new_view_update_view :
    forall s w v,
      has_nv (view_change_state s) v
      -> has_nv (view_change_state (update_view s w)) v.
  Proof.
    auto.
  Qed.
  Hint Resolve has_new_view_update_view : pbft.

  Lemma has_new_view_change_sequence_number :
    forall s n v,
      has_nv (view_change_state s) v
      -> has_nv (view_change_state (change_sequence_number s n)) v.
  Proof.
    auto.
  Qed.
  Hint Resolve has_new_view_change_sequence_number : pbft.

  Lemma has_new_view_log_pre_prepares_of_new_view :
    forall s P v,
      has_nv (view_change_state s) v
      -> has_nv (view_change_state (log_pre_prepares_of_new_view s P)) v.
  Proof.
    auto.
  Qed.
  Hint Resolve has_new_view_log_pre_prepares_of_new_view : pbft.

  Lemma check_broadcast_new_view_implies_equal_views2 :
    forall i s e nv e' O N,
      wf_view_change_entry e
      -> check_broadcast_new_view i s e = Some (nv, e', O, N)
      -> vce_view e' = new_view2view nv.
  Proof.
    introv h q; symmetry; eauto 3 with pbft.
  Qed.
  Hint Resolve check_broadcast_new_view_implies_equal_views2 : pbft.

  Definition unique_new_view S e :=
    forall e',
      In e' S
      -> vce_view e' = vce_view e
      -> vce_new_view e' = vce_new_view e.

  Lemma check_broadcast_new_view_preserves_new_view_of_entry2 :
    forall i s e nv e' O N,
      wf_view_change_state (view_change_state s)
      -> check_broadcast_new_view i s e = Some (nv, e', O, N)
      -> In e (view_change_state s)
      -> unique_new_view (view_change_state s) e'.
  Proof.
    introv wf check j k eqv.
    eapply check_broadcast_new_view_preserves_new_view_of_entry; eauto.
  Qed.
  Hint Resolve check_broadcast_new_view_preserves_new_view_of_entry2 : pbft.

  Lemma log_new_view_and_entry_preserves_has_new_view :
    forall S nv v e,
      unique_new_view S e
      -> vce_view e = new_view2view nv
      -> correct_new_view nv = true
      -> has_nv S v
      -> has_nv (log_new_view_and_entry S nv e) v.
  Proof.
    introv imp eqv cor h.
    unfold has_nv, has_new_view in *; smash_pbft.
    unfold has_new_view1 in *.
    allrw existsb_exists; exrepnd; smash_pbft.

    applydup (implies_or_in_log_new_view_and_entry e x nv) in h1.
    repndors; repnd.

    - eexists; smash_pbft; dands; auto.

    - eexists; dands; eauto; autorewrite with pbft; smash_pbft;[].

      match goal with
      | [ H : vce_new_view (add_new_view_to_entry _ _) = _ |- _ ] =>
        apply vce_new_view_add_new_view_to_entry_none_implies in H
      end.
      apply imp in h1; tcsp.
      rewrite h1 in *; pbft_simplifier.
  Qed.
  Hint Resolve log_new_view_and_entry_preserves_has_new_view : pbft.

  Lemma has_new_view_log_new_view_and_entry_state :
    forall s nv e v,
      has_nv (log_new_view_and_entry (view_change_state s) nv e) v
      -> has_nv (view_change_state (log_new_view_and_entry_state s nv e)) v.
  Proof.
    auto.
  Qed.
  Hint Resolve has_new_view_log_new_view_and_entry_state : pbft.

  Lemma has_new_view_log_new_view_state :
    forall s nv v,
      has_nv (log_new_view (view_change_state s) nv) v
      -> has_nv (view_change_state (log_new_view_state s nv)) v.
  Proof.
    auto.
  Qed.
  Hint Resolve has_new_view_log_new_view_state : pbft.

  Lemma has_nv_preserved :
    forall (eo : EventOrdering) (e : Event) slf st1 st2 v,
      state_sm_before_event (PBFTreplicaSM slf) e = Some st1
      -> state_sm_on_event (PBFTreplicaSM slf) e = Some st2
      -> has_nv (view_change_state st1) v
      -> has_nv (view_change_state st2) v.
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers6 smash_pbft_ind3.

    {
      eapply update_state_new_view_preserves_has_new_view;[eauto|].
      apply has_new_view_update_view.
      apply has_new_view_change_sequence_number.
      apply has_new_view_log_pre_prepares_of_new_view.
      apply has_new_view_log_new_view_and_entry_state.
      apply log_new_view_and_entry_preserves_has_new_view; eauto 4 with pbft.
    }
  Qed.

  Lemma PBFThas_new_view_is_preserved :
    forall (eo : EventOrdering) (e1 e2 : Event) slf st1 st2 v,
      e1 ⊑ e2
      -> state_sm_before_event (PBFTreplicaSM slf) e1 = Some st1
      -> state_sm_before_event (PBFTreplicaSM slf) e2 = Some st2
      -> has_new_view (view_change_state st1) v = true
      -> has_new_view (view_change_state st2) v = true.
  Proof.
    introv.
    revert st2.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv h1 h2 h3 h4.

    apply localHappenedBeforeLe_implies_or2 in h1; repndors; subst; tcsp;[|].

    {
      match goal with
      | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; ginv
      end.
    }

    apply local_implies_pred_or_local in h1; repndors; exrepnd.

    {
      eapply state_sm_on_event_if_before_event_direct_pred in h1;[|eauto].
      eapply has_nv_preserved;[| |eauto];[|eauto]; auto.
    }

    pose proof (ind e) as q; autodimp q hyp; clear ind.

    pose proof (state_sm_before_event_some_between e e2 (PBFTreplicaSM slf) st2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    pose proof (q s') as h; clear q; repeat (autodimp h hyp); eauto 2 with eo.

    eapply state_sm_on_event_if_before_event_direct_pred in h1;[|eauto].
    eapply has_nv_preserved;[| |eauto];[|eauto]; auto.
  Qed.

  Lemma PBFThas_new_view_is_preserved2 :
    forall (eo : EventOrdering) (e1 e2 : Event) slf st1 st2 v,
      e1 ⊑ e2
      -> state_sm_before_event (PBFTreplicaSM slf) e1 = Some st1
      -> state_sm_on_event (PBFTreplicaSM slf) e2 = Some st2
      -> has_new_view (view_change_state st1) v = true
      -> has_new_view (view_change_state st2) v = true.
  Proof.
    introv lee hst1 hst2 hnv.

    dup hst2 as eqst.
    rewrite state_sm_on_event_unroll2 in eqst.
    remember (state_sm_before_event (PBFTreplicaSM slf) e2) as eqst'.
    symmetry in Heqeqst'.
    destruct eqst'; simpl in *; ginv.

    applydup localLe_implies_loc in lee.

    eapply has_nv_preserved; try (exact Heqeqst'); auto.
    eapply PBFThas_new_view_is_preserved; eauto.
  Qed.

  Lemma PBFThas_new_view_is_preserved3 :
    forall (eo : EventOrdering) (e1 e2 : Event) slf st1 st2 v,
      e1 ⊑ e2
      -> state_sm_on_event (PBFTreplicaSM slf) e1 = Some st1
      -> state_sm_on_event (PBFTreplicaSM slf) e2 = Some st2
      -> has_new_view (view_change_state st1) v = true
      -> has_new_view (view_change_state st2) v = true.
  Proof.
    introv lee hst1 hst2 hnv.

    apply localHappenedBeforeLe_implies_or2 in lee; repndors; subst.

    { rewrite hst2 in hst1; ginv. }

    apply local_implies_local_or_pred in lee; repndors; exrepnd.

    {
      pose proof (state_sm_before_event_as_state_sm_on_event_pred
                    (PBFTreplicaSM slf) e2) as q.
      autodimp q hyp; eauto 2 with eo.
      applydup pred_implies_local_pred in lee.
      rewrite <- lee0 in q.
      rewrite <- q in hst1.
      eapply has_nv_preserved; try (exact hst1); try (exact hst2); auto.
    }

    {
      pose proof (state_sm_before_event_as_state_sm_on_event_pred
                    (PBFTreplicaSM slf) e) as q.
      autodimp q hyp; eauto 2 with eo.
      applydup pred_implies_local_pred in lee1.
      rewrite <- lee2 in q.
      rewrite <- q in hst1.
      eapply PBFThas_new_view_is_preserved2; try (exact hst2); try(exact hst1); eauto 2 with eo.
    }
  Qed.

End PBFThas_new_view.


Hint Resolve check_send_replies_preserves_view_change_state : pbft.
Hint Resolve check_send_replies_preserves_has_new_view : pbft.
Hint Resolve check_send_replies_update_log_preserves_has_new_view : pbft.
Hint Resolve check_stable_preserves_view_change_state : pbft.
Hint Resolve check_stable_preserves_has_new_view : pbft.
Hint Resolve check_stable_update_checkpoint_state_preserves_has_new_view : pbft.
Hint Resolve find_and_execute_preserves_view_change_state : pbft.
Hint Resolve find_and_execute_preserves_has_new_view : pbft.
Hint Resolve log_new_view_state_preserves_has_new_view : pbft.
Hint Resolve add_own_view_change_to_state_preserves_has_new_view : pbft.
Hint Resolve start_view_change_preserves_has_new_view : pbft.
Hint Resolve add_other_view_change_preserves_has_new_view : pbft.
Hint Resolve log_checkpoint_cert_from_new_view_preserves_has_new_view : pbft.
Hint Resolve update_state_new_view_preserves_has_new_view : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_has_new_view : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_has_new_view : pbft.


Hint Rewrite @vce_view_add_new_view_to_entry : pbft.
Hint Rewrite @vce_view_add_own_view_change2entry : pbft.
Hint Rewrite @vce_new_view_add_own_view_change2entry : pbft.
Hint Rewrite @view_change_state_update_checkpoint_from_new_view : pbft.
Hint Rewrite @view_change_state_trim_checkpoint : pbft.
Hint Rewrite @view_change_state_decrement_requests_in_progress : pbft.
