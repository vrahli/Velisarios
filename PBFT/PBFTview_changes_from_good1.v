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


Require Export PBFTreceived_prepare_like.
(*Require Export PBFT_A_1_2_2.
Require Export PBFT_A_1_2_1.*)
Require Export PBFT_A_1_2_8.
Require Export PBFTnew_view_are_received3.
Require Export PBFTsent_commits_are_in_log.

(*Require Export PBFT_A_1_9_part1.*)


Section PBFTview_changes_from_good1.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma verify_new_view_implies_verify_view_change_in_cert :
    forall i keys nv vc,
      verify_new_view i keys nv = true
      -> In vc (new_view2cert nv)
      -> verify_view_change i keys vc = true.
  Proof.
    introv verify j.
    destruct nv, v; simpl in *.
    unfold verify_new_view in verify; simpl in *; smash_pbft.
    clear verify.
    repeat (rewrite verify_list_auth_data_app in verify0); smash_pbft.
    clear verify1 verify2.

    induction V; simpl in *; tcsp.
    repeat (rewrite verify_list_auth_data_app in verify0); smash_pbft.
    repndors; subst; tcsp.
  Qed.
  Hint Resolve verify_new_view_implies_verify_view_change_in_cert : pbft.

  Definition view_change2main_auth_data (v : ViewChange) : AuthenticatedData :=
    match v with
    | view_change (bare_view_change v n s C P i) a =>
      MkAuthData (PBFTmsg_bare_view_change (bare_view_change v n s C P i)) a
    end.

  Lemma view_change2main_data_auth_in_view_change2auth_data :
    forall vc, In (view_change2main_auth_data vc) (view_change2auth_data vc).
  Proof.
    introv; destruct vc, v; simpl; tcsp.
  Qed.
  Hint Resolve view_change2main_data_auth_in_view_change2auth_data : pbft.

  Lemma in_implies_view_change2main_auth_data_in_new_view2auth_data :
    forall vc nv,
      In vc (new_view2cert nv)
      -> In (view_change2main_auth_data vc) (new_view2auth_data nv).
  Proof.
    introv i; destruct nv, v; simpl in *.
    right.
    allrw in_app_iff.
    left.
    induction V; simpl in *; repndors; subst; allrw in_app_iff; smash_pbft.
  Qed.
  Hint Resolve in_implies_view_change2main_auth_data_in_new_view2auth_data : pbft.

  Lemma verify_view_change_implies_verify_main :
    forall i keys vc,
      verify_view_change i keys vc = true
      -> verify_authenticated_data (PBFTreplica i) (view_change2main_auth_data vc) keys = true.
  Proof.
    introv verify; destruct vc, v; simpl in *.
    unfold verify_view_change in verify; simpl in *; smash_pbft.
  Qed.
  Hint Resolve verify_view_change_implies_verify_main : pbft.

  Lemma PBFTdata_auth_view_change2main_auth_data_some_implies :
    forall i vc k,
      PBFTdata_auth (PBFTreplica i) (view_change2main_auth_data vc) = Some k
      -> k = PBFTreplica (view_change2sender vc).
  Proof.
    introv h.
    destruct vc, v; simpl in *; ginv; auto.
  Qed.

  Lemma same_digests_same :
    forall d, same_digests d d = true.
  Proof.
    introv.
    unfold same_digests; smash_pbft.
  Qed.
  Hint Rewrite same_digests_same : pbft.
  Hint Resolve same_digests_same : pbft.

  Lemma check_between_water_marks_implies_lt :
    forall m n,
      check_between_water_marks m n = true
      -> m < n.
  Proof.
    introv check; unfold check_between_water_marks in *; smash_pbft.
  Qed.
  Hint Resolve check_between_water_marks_implies_lt : pbft.

  Lemma prepare_of_pre_in_log_implies_prepare_in_log :
    forall v n r a d i L,
      prepare_of_pre_in_log (mk_pre_prepare v n r a) d i L = true
      -> exists a', prepare_in_log (mk_prepare v n d i a') L = true.
  Proof.
    induction L; introv prep; simpl in *; tcsp; smash_pbft.

    - destruct a0; simpl in *.
      unfold eq_request_data in *; smash_pbft.
      unfold is_prepare_for_entry; simpl; smash_pbft.
      unfold in_list_rep_toks in *.
      allrw existsb_exists; exrepnd; smash_pbft.
      destruct x as [i a']; simpl in *.
      exists a'; simpl.
      rewrite existsb_exists; eexists; dands; eauto; smash_pbft.

    - autodimp IHL hyp.
      exrepnd.
      destruct a0; simpl in *.
      unfold eq_request_data in *; smash_pbft.
      unfold is_prepare_for_entry, eq_request_data; simpl; smash_pbft.
  Qed.

  Lemma equal_nats_implies_equal_views :
    forall (v1 v2 : View),
      view2nat v1 = view2nat v2
      -> v1 = v2.
  Proof.
    introv h; destruct v1, v2; simpl in *; auto.
  Qed.

  Lemma in_view_change2auth_data_implies2 :
    forall m v,
      In m (view_change2auth_data v)
      -> (exists w a, m = MkAuthData (PBFTmsg_bare_view_change w) a /\ v = view_change w a)
         \/ (exists c a, m = MkAuthData (PBFTmsg_bare_checkpoint c) a)
         \/ (exists p a, m = MkAuthData (PBFTmsg_bare_pre_prepare p) a)
         \/ (exists p a, m = MkAuthData (PBFTmsg_bare_prepare p) a)
         \/ (exists r a, m = MkAuthData (PBFTmsg_bare_request r) a).
  Proof.
    introv i.
    destruct v, v; simpl in *; repndors; subst; ginv; auto.

    { left; eexists; eexists; eauto. }

    allrw in_app_iff; repndors.

    - apply in_checkpoints2auth_data_implies in i; tcsp.
      right; left; auto.

    - apply in_prepared_info2auth_data_implies in i; repndors; tcsp;
        try (complete (right; right; left; auto));
        try (complete (right; right; right; auto)).
  Qed.

  Lemma in_view_changes2auth_data_implies2 :
    forall m V,
      In m (view_changes2auth_data V)
      -> (exists v a, m = MkAuthData (PBFTmsg_bare_view_change v) a /\ In (view_change v a) V)
         \/ (exists c a, m = MkAuthData (PBFTmsg_bare_checkpoint c) a)
         \/ (exists p a, m = MkAuthData (PBFTmsg_bare_pre_prepare p) a)
         \/ (exists p a, m = MkAuthData (PBFTmsg_bare_prepare p) a)
         \/ (exists r a, m = MkAuthData (PBFTmsg_bare_request r) a).
  Proof.
    induction V; introv i; simpl in i; tcsp.
    allrw in_app_iff; repndors; tcsp.

    - apply in_view_change2auth_data_implies2 in i; auto.
      repndors; tcsp;
        try (complete (right; left; tcsp));
        try (complete (right; right; left; tcsp));
        try (complete (right; right; right; tcsp));
        try (complete (right; right; right; left; tcsp));
        try (complete (right; right; right; right; tcsp));[].
      left.
      simpl.
      exrepnd; subst.
      eexists; eexists; dands; eauto.

    - autodimp IHV hyp.
      repndors; tcsp;
        try (complete (right; left; tcsp));
        try (complete (right; right; left; tcsp));
        try (complete (right; right; right; tcsp));
        try (complete (right; right; right; left; tcsp));
        try (complete (right; right; right; right; tcsp));[].
      left.
      simpl.
      exrepnd; subst.
      eexists; eexists; dands; eauto.
  Qed.

  Lemma in_pre_prepares2auth_data_implies :
    forall m P,
      In m (pre_prepares2auth_data P)
      -> (exists p a, m = MkAuthData (PBFTmsg_bare_pre_prepare p) a /\ In (pre_prepare p a) P)
         \/ (exists r a, m = MkAuthData (PBFTmsg_bare_request r) a).
  Proof.
    induction P; introv i; simpl in i; tcsp.
    destruct a; simpl in *.
    repndors; subst; simpl in *; tcsp;[|].
    - left; eexists; eexists; dands; eauto.
    - allrw in_app_iff.
      repndors;[|].
      + unfold pre_prepare2auth_data_req in i; simpl in i.
        allrw in_map_iff; exrepnd; subst; simpl in *.
        right; destruct x, b; simpl; eexists; eexists; eauto.
      + autodimp IHP hyp; exrepnd; subst; tcsp.
        repndors; exrepd; subst; tcsp.
        * left; eexists; eexists; dands; eauto.
        * right; eexists; eexists; dands; eauto.
  Qed.

  Lemma view_change2main_auth_data_in_get_contained_auth_data_implies :
    forall vc m,
      In (view_change2main_auth_data vc) (PBFTget_contained_auth_data m)
      -> m = PBFTview_change vc
         \/ (exists nv, m = PBFTnew_view nv /\ In vc (new_view2cert nv)).
  Proof.
    introv i.
    destruct m, vc, v; simpl in *; repndors; tcsp;
      try (complete (destruct r; simpl in *; ginv));
      try (complete (destruct p; simpl in *; ginv));
      try (complete (destruct c; simpl in *; ginv)).

    - unfold pre_prepare2auth_data_req in i; simpl in *.
      allrw in_map_iff; exrepnd; subst.
      destruct x, b; simpl in *; ginv.

    - destruct v0, v; simpl in *; repndors; ginv; tcsp;[].
      apply in_app_iff in i; repndors.

      + apply in_checkpoints2auth_data_implies in i; exrepnd; ginv.

      + apply in_prepared_info2auth_data_implies in i; repndors; exrepnd; ginv.

    - destruct v0, v; simpl in *; repndors; ginv; tcsp;[].
      allrw in_app_iff; repndors;
        try (complete (eapply in_pre_prepares2auth_data_implies in i; repndors; exrepnd; ginv));[].

      applydup in_view_changes2auth_data_implies2 in i.
      repndors; exrepnd; ginv.
      right.
      eexists; dands; eauto.
  Qed.

  Hint Resolve in_implies_view_change2main_auth_data_in_new_view2auth_data : pbft.
  Hint Resolve verify_view_change_implies_verify_main : pbft.

  Lemma update_state_new_view_preserves_new_view_in_log_backward :
    forall slf nv' nv msg state state',
      update_state_new_view slf state nv = (state', msg)
      -> new_view_in_log nv' (view_change_state state)
      -> new_view_in_log nv' (view_change_state state').
  Proof.
    introv upd nvinlog.
    unfold update_state_new_view in upd; smash_pbft.
    simpl in *.
    erewrite log_checkpoint_cert_from_new_view_preserves_view_change_state;[|eauto]; auto.
  Qed.
  Hint Resolve update_state_new_view_preserves_new_view_in_log_backward : pbft.

  Lemma implies_new_view_in_log_log_new_view_and_entry :
    forall nv s e e',
      In e s
      -> vce_new_view e' = None
      -> vce_view e = vce_view e'
      -> wf_view_change_state s
      -> new_view2view nv = vce_view e
      -> new_view_in_log nv (log_new_view_and_entry s nv e').
  Proof.
    induction s; introv i h eqv wf w; simpl in *; tcsp.
    inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
    repndors; subst; smash_pbft;
      destruct e'; simpl in *; subst; simpl; auto.
  Qed.
  Hint Resolve implies_new_view_in_log_log_new_view_and_entry : pbft.

  Fixpoint own_view_change_in_log
           (vc : ViewChange)
           (S  : PBFTviewChangeState) : Prop :=
    match S with
    | [] => False
    | entry :: entries =>
      vce_view_change entry = Some vc
      \/ own_view_change_in_log vc entries
    end.

  Lemma mk_current_view_change_increment_view :
    forall i v s,
      mk_current_view_change i v (increment_view s)
      = mk_current_view_change i v s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite mk_current_view_change_increment_view : pbft.

  Lemma mk_current_view_change_change_view_change_state :
    forall i v s x,
      mk_current_view_change i v (change_view_change_state s x)
      = mk_current_view_change i v s.
  Proof.
    sp.
  Qed.
  Hint Rewrite mk_current_view_change_change_view_change_state : pbft.

  Lemma check_send_replies_preserves_own_view_change_in_log :
    forall i v keys giop s1 n msgs s2 vc,
      check_send_replies i v keys giop s1 n = (msgs, s2)
      -> own_view_change_in_log vc (view_change_state s2)
      -> own_view_change_in_log vc (view_change_state s1).
  Proof.
    introv check own.
    unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_own_view_change_in_log : pbft.

  Lemma check_stable_preserves_own_view_change_in_log :
    forall i s1 cop s2 vc,
      check_stable i s1 cop = Some s2
      -> own_view_change_in_log vc (view_change_state s2)
      -> own_view_change_in_log vc (view_change_state s1).
  Proof.
    introv check own.
    unfold check_stable in check; smash_pbft.
  Qed.
  Hint Resolve check_stable_preserves_own_view_change_in_log : pbft.

  Lemma own_view_change_log_new_view_and_entry_implies :
    forall vc s nv e,
      own_view_change_in_log vc (log_new_view_and_entry s nv e)
      -> own_view_change_in_log vc s
         \/ vce_view_change e = Some vc.
  Proof.
    induction s; introv own; simpl in *; repndors; tcsp.

    - destruct e, vce_new_view; simpl in *; tcsp.

    - smash_pbft; repndors; tcsp.
      apply IHs in own; repndors; tcsp.
  Qed.

  Lemma start_view_change_preserves_own_view_change_in_log :
    forall vc s1 e n s2 vc',
      start_view_change vc s1 = (e, n, s2)
      -> own_view_change_in_log vc' s2
      -> own_view_change_in_log vc' s1 \/ vc = vc'.
  Proof.
    introv start own.
    unfold start_view_change in start.
    revert e n s2 start own.
    induction s1; introv start own; repeat (simpl in *; smash_pbft); repndors; tcsp.

    - destruct a, vce_view_change; simpl in *; ginv; tcsp.

    - eapply IHs1 in own;[|reflexivity].
      repndors; tcsp.
  Qed.

  Lemma add_other_view_change_preserves_own_view_change_in_log :
    forall vc s1 e n s2 vc',
      add_other_view_change vc s1 = Some (e, n, s2)
      -> own_view_change_in_log vc' s2
      -> own_view_change_in_log vc' s1.
  Proof.
    induction s1; introv add own; repeat (simpl in *; tcsp; smash_pbft); repndors; tcsp.

    - destruct a; simpl in *; tcsp; smash_pbft.

    - eapply IHs1 in own; eauto.
  Qed.
  Hint Resolve add_other_view_change_preserves_own_view_change_in_log : pbft.

  Lemma own_view_change_log_new_view_implies :
    forall vc s nv,
      own_view_change_in_log vc (log_new_view s nv)
      -> own_view_change_in_log vc s.
  Proof.
    induction s; introv own; simpl in *; repndors; tcsp; smash_pbft; repndors; tcsp.
    apply IHs in own; tcsp.
  Qed.
  Hint Resolve own_view_change_log_new_view_implies : pbft.

  Lemma view_change2sender_refresh_view_change :
    forall vc s,
      view_change2sender (refresh_view_change vc s)
      = view_change2sender vc.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite view_change2sender_refresh_view_change : pbft.

  Lemma in_implies_own_view_change_in_log :
    forall vc e s,
      In e s
      -> wf_view_change_state s
      -> vce_view_change e = Some vc
      -> own_view_change_in_log vc s.
  Proof.
    induction s; introv i wf vce; simpl in *; tcsp;[].
    inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
    repndors; subst; tcsp.
  Qed.
  Hint Resolve in_implies_own_view_change_in_log : pbft.

  Lemma start_view_change_implies_own_view_change_in_log :
    forall vc s1 e n s2,
      wf_view_change_state s1
      -> (forall vc', own_view_change_in_log vc' s1 -> view_change2view vc' < view_change2view vc)
      -> start_view_change vc s1 = (e, n, s2)
      -> own_view_change_in_log vc s2.
  Proof.
    introv wf imp start.
    unfold start_view_change in start.
    revert e n s2 imp start.
    induction s1; introv imp start; repeat (simpl in *; tcsp; smash_pbft).

    - inversion wf as [|? ? w wf1 wf2]; subst; clear wf.
      destruct a, vce_view_change; simpl in *; tcsp.
      subst.
      eapply wf_view_change_entry_view_change in wf1; simpl;eauto.
      simpl in *.
      pose proof (imp v) as q; autodimp q hyp.
      rewrite wf1 in *; simpl in *; try omega.

    - inversion wf as [|? ? w wf1 wf2]; subst; clear wf.
      autodimp IHs1 hyp.
      pose proof (IHs1 e x3 x1) as q; repeat (autodimp q hyp).
  Qed.
  Hint Resolve start_view_change_implies_own_view_change_in_log : pbft.

  Lemma implies_own_view_change_log_new_view_and_entry_entry :
    forall vc s nv e,
      vce_view_change e = Some vc
      -> own_view_change_in_log vc (log_new_view_and_entry s nv e).
  Proof.
    induction s; introv eqvc; simpl in *; smash_pbft.
  Qed.
  Hint Resolve implies_own_view_change_log_new_view_and_entry_entry : pbft.

  Lemma lt_next_view :
    forall (v : View), v < next_view v.
  Proof.
    introv; destruct v; simpl; omega.
  Qed.
  Hint Resolve lt_next_view : pbft.

  Lemma le_next_view :
    forall (v : View), v <= next_view v.
  Proof.
    introv; destruct v; simpl; omega.
  Qed.
  Hint Resolve le_next_view : pbft.

  Lemma start_view_change_preserves_view_change_somewhere_in_log2 :
    forall vc s1 e n s2 x,
      start_view_change vc s1 = (e, n, s2)
      -> view_change_somewhere_in_log x s2
      -> view_change_somewhere_in_log x s1
         \/ (x = vc /\ own_view_change_in_log vc s2).
  Proof.
    introv start vcinlog.
    unfold start_view_change in start.
    revert e n s2 start vcinlog.

    induction s1; introv add vcinlog; repeat (simpl in *; repndors; smash_pbft); tcsp.

    - destruct a, vce_view_change; simpl in *; repndors; subst; tcsp.

    - pose proof (IHs1 e x4 x2) as q; clear IHs1; repeat (autodimp q hyp); tcsp.
  Qed.

  Lemma send_new_view_in_check_broadcast_prepare_false :
    forall nv dst i rd g,
      In (send_new_view nv dst) (check_broadcast_prepare i rd g)
      <-> False.
  Proof.
    introv; split; intro h; tcsp.
    apply in_check_broadcast_prepare_implies in h;exrepnd;subst;ginv.
  Qed.
  Hint Rewrite send_new_view_in_check_broadcast_prepare_false : pbft.

  Lemma send_new_view_in_check_broadcast_commit_false :
    forall nv dst i rd g,
      In (send_new_view nv dst) (check_broadcast_commit i rd g)
      <-> False.
  Proof.
    introv; split; intro h; tcsp.
    apply in_check_broadcast_commit_implies in h;exrepnd;subst;ginv.
  Qed.
  Hint Rewrite send_new_view_in_check_broadcast_commit_false : pbft.

  Hint Rewrite in_app_iff : pbft.

  Lemma false_or_left : forall p, False \/ p <-> p.
  Proof.
    introv; split; tcsp.
  Qed.
  Hint Rewrite false_or_left : pbft.

  Lemma false_or_right : forall p, p \/ False <-> p.
  Proof.
    introv; split; tcsp.
  Qed.
  Hint Rewrite false_or_right : pbft.

  Lemma send_new_view_in_check_send_replies_false_new_view_in_log :
    forall nv dst msgs i v k g s1 n s2 l,
      In (send_new_view nv dst) msgs
      -> check_send_replies i v k g s1 n = (msgs, s2)
      -> new_view_in_log nv l.
  Proof.
    introv j check.
    eapply message_in_check_send_replies_implies in check;eauto; ginv.
  Qed.
  Hint Resolve send_new_view_in_check_send_replies_false_new_view_in_log : pbft.

  Lemma send_new_view_in_find_and_execute_requests_false_new_view_in_log :
    forall i v k s1 msgs s2 nv dst l,
      find_and_execute_requests i v k s1 = (msgs, s2)
      -> In (send_new_view nv dst) msgs
      -> new_view_in_log nv (view_change_state l).
  Proof.
    introv f j.
    eapply message_in_find_and_execute_requests_implies in f;eauto.
    repndors; exrepnd; ginv.
  Qed.
  Hint Resolve send_new_view_in_find_and_execute_requests_false_new_view_in_log : pbft.

  Lemma send_check_bcast_send_new_view_false :
    forall nv1 d1 nv2 d2,
      send_check_bcast_new_view nv1 d1 = send_new_view nv2 d2
      <-> False.
  Proof.
    introv; split; introv h; ginv; tcsp.
  Qed.
  Hint Rewrite send_check_bcast_send_new_view_false : pbft.

  Lemma own_view_change_in_update_log_implies :
    forall vc s L,
      own_view_change_in_log vc (view_change_state (update_log s L))
      -> own_view_change_in_log vc (view_change_state s).
  Proof.
    tcsp.
  Qed.
  Hint Resolve own_view_change_in_update_log_implies : pbft.

  Lemma find_and_execute_requests_init :
    forall i v ks,
      find_and_execute_requests i v ks (initial_state i) = ([], initial_state i).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite find_and_execute_requests_init : pbft.

  Lemma find_and_execute_requests_preserves_own_view_change_in_log :
    forall i v ks s1 msgs s2 vc,
      find_and_execute_requests i v ks s1 = (msgs, s2)
      -> own_view_change_in_log vc (view_change_state s2)
      -> own_view_change_in_log vc (view_change_state s1).
  Proof.
    introv f o; apply find_and_execute_preserves_view_change_state in f; allrw <-; auto.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_own_view_change_in_log : pbft.

End PBFTview_changes_from_good1.


Hint Resolve verify_new_view_implies_verify_view_change_in_cert : pbft.
Hint Resolve view_change2main_data_auth_in_view_change2auth_data : pbft.
Hint Resolve in_implies_view_change2main_auth_data_in_new_view2auth_data : pbft.
Hint Resolve verify_view_change_implies_verify_main : pbft.
Hint Resolve same_digests_same : pbft.
Hint Resolve check_between_water_marks_implies_lt : pbft.
Hint Resolve in_implies_view_change2main_auth_data_in_new_view2auth_data : pbft.
Hint Resolve verify_view_change_implies_verify_main : pbft.
Hint Resolve update_state_new_view_preserves_new_view_in_log_backward : pbft.
Hint Resolve implies_new_view_in_log_log_new_view_and_entry : pbft.
Hint Resolve check_send_replies_preserves_own_view_change_in_log : pbft.
Hint Resolve check_stable_preserves_own_view_change_in_log : pbft.
Hint Resolve add_other_view_change_preserves_own_view_change_in_log : pbft.
Hint Resolve own_view_change_log_new_view_implies : pbft.
Hint Resolve in_implies_own_view_change_in_log : pbft.
Hint Resolve start_view_change_implies_own_view_change_in_log : pbft.
Hint Resolve implies_own_view_change_log_new_view_and_entry_entry : pbft.
Hint Resolve lt_next_view : pbft.
Hint Resolve le_next_view : pbft.
Hint Resolve PBFTcurrent_view_increases_local_pred : pbft.
Hint Resolve view_change2main_data_auth_in_view_change2auth_data : pbft.
Hint Resolve send_new_view_in_check_send_replies_false_new_view_in_log : pbft.
Hint Resolve send_new_view_in_find_and_execute_requests_false_new_view_in_log : pbft.
Hint Resolve own_view_change_in_update_log_implies : pbft.
Hint Resolve find_and_execute_requests_preserves_own_view_change_in_log : pbft.


Hint Rewrite @same_digests_same : pbft.
Hint Rewrite @mk_current_view_change_increment_view : pbft.
Hint Rewrite @mk_current_view_change_change_view_change_state : pbft.
Hint Rewrite @view_change2sender_refresh_view_change : pbft.
Hint Rewrite @send_new_view_in_check_broadcast_prepare_false : pbft.
Hint Rewrite @send_new_view_in_check_broadcast_commit_false : pbft.
Hint Rewrite @in_app_iff : pbft.
Hint Rewrite @false_or_left : pbft.
Hint Rewrite @false_or_right : pbft.
Hint Rewrite @send_check_bcast_send_new_view_false : pbft.
Hint Rewrite @find_and_execute_requests_init : pbft.
