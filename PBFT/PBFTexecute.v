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


Require Export PBFTnew_view_in_log.
Require Export PBFTgarbage_collect.
Require Export PBFTreceived_prepare_like.


Section PBFTexecute.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


(*  (* The difference with smash_pbft_ind is that we have an additional [try omega] here  *)
  Ltac custom_smash_pbft_ind ind :=
    let d   := fresh "d" in
    let hyp := fresh "hyp" in
    match goal with
    | [ H : state_sm_before_event ?sm ?eo ?e = Some ?s |- _ ] =>
      let K := fresh H in
      rewrite <- ite_first_state_sm_on_event_as_before in H;
      unfold ite_first in H;
      destruct (dec_isFirst e) as [d|d]; gen_inv;
      try (complete (try clear_current_view; simpl in *; subst; simpl in *; pbft_simplifier; smash_pbft; try omega));
      first[fail
           |idtac;[];
            repeat (autodimp ind hyp);
            first[fail
                 |idtac;[];
                  dup H as K;
                  eapply ind in K; eauto; clear ind;
                  eauto 2 with pbft;
                  exrepnd;
                  repeat (eexists;[]);
                  dands; eauto; eauto 3 with eo pbft;
                  complete (repndors; tcsp; try cpltLR; try congruence; try omega)
                 ]
           ]
    end.*)

  Lemma check_send_replies_preserves_next_to_execute :
    forall i v keys giop s1 n msgs s2,
      check_send_replies i v keys giop s1 n = (msgs, s2)
      -> next_to_execute s2 = next_to_execute s1.
  Proof.
    introv check; unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.

  Lemma check_send_replies_preserves_sm_state :
    forall i v keys giop s1 n msgs s2,
      check_send_replies i v keys giop s1 n = (msgs, s2)
      -> sm_state s2 = sm_state s1.
  Proof.
    introv check; unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.

  Lemma check_send_replies_preserves_last_reply_state :
    forall i v keys giop s1 n msgs s2,
      check_send_replies i v keys giop s1 n = (msgs, s2)
      -> last_reply_state s2 = last_reply_state s1.
  Proof.
    introv check; unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.

  Lemma check_stable_preserves_next_to_execute :
    forall i s1 cop s2,
      check_stable i s1 cop = Some s2
      -> next_to_execute s2 = next_to_execute s1.
  Proof.
    introv check; unfold check_stable in check; smash_pbft.
  Qed.

  Lemma next_to_execute_decrement_requests_in_progress_if_primary :
    forall i v s,
      next_to_execute (decrement_requests_in_progress_if_primary i v s)
      = next_to_execute s.
  Proof.
    introv; unfold decrement_requests_in_progress_if_primary; smash_pbft.
  Qed.
  Hint Rewrite @next_to_execute_decrement_requests_in_progress_if_primary : pbft.

  Lemma check_broadcast_checkpoint_preserves_next_to_execute :
    forall i n v keys s1 s2 msgs,
      check_broadcast_checkpoint i n v keys s1 = (s2, msgs)
      -> next_to_execute s2 = next_to_execute s1.
  Proof.
    introv check; unfold check_broadcast_checkpoint in check; smash_pbft.
  Qed.

  Lemma find_and_execute_requests_preserves_next_to_execute :
    forall i v keys s1 msgs s2,
      find_and_execute_requests i v keys s1 = (msgs, s2)
      ->
      (
        next_to_execute s2 = next_to_execute s1
        \/
        exists entry,
          find_entry (log s1) (next_to_execute s1) = Some entry
          /\ is_committed_entry entry = true
          /\ next_to_execute s2 = next_seq (next_to_execute s1)
      ).
  Proof.
    introv fexec.
    unfold find_and_execute_requests in fexec; smash_pbft.
    unfold execute_requests in *.
    destruct (ready s1); smash_pbft.
    right; exists x; dands; auto.

    rename_hyp_with check_broadcast_checkpoint check.
    apply check_broadcast_checkpoint_preserves_next_to_execute in check; simpl in *; auto.
  Qed.

  Lemma check_stable_preserves_sm_state :
    forall i s1 cop s2,
      check_stable i s1 cop = Some s2
      -> sm_state s2 = sm_state s1.
  Proof.
    introv check; unfold check_stable in check; smash_pbft.
  Qed.

  Lemma check_stable_preserves_last_reply_state :
    forall i s1 cop s2,
      check_stable i s1 cop = Some s2
      -> last_reply_state s2 = last_reply_state s1.
  Proof.
    introv check; unfold check_stable in check; smash_pbft.
  Qed.

  Lemma check_broadcast_checkpoint_preserves_sm_state :
    forall i n v keys s1 s2 msgs,
      check_broadcast_checkpoint i n v keys s1 = (s2, msgs)
      -> sm_state s2 = sm_state s1.
  Proof.
    introv check; unfold check_broadcast_checkpoint in check; smash_pbft.
  Qed.

  Lemma check_broadcast_checkpoint_preserves_last_reply_state :
    forall i n v keys s1 s2 msgs,
      check_broadcast_checkpoint i n v keys s1 = (s2, msgs)
      -> last_reply_state s2 = last_reply_state s1.
  Proof.
    introv check; unfold check_broadcast_checkpoint in check; smash_pbft.
  Qed.

  Lemma find_and_execute_requests_preserves_next_to_execute2 :
    forall i v keys s1 msgs s2,
      find_and_execute_requests i v keys s1 = (msgs, s2)
      ->
      (
        (
          next_to_execute s2 = next_to_execute s1
          /\ sm_state s2 = sm_state s1
          /\ last_reply_state s2 = last_reply_state s1
        )
        \/
        exists entry reps,
          find_entry (log s1) (next_to_execute s1) = Some entry
          /\ is_committed_entry entry = true
          /\ next_to_execute s2 = next_seq (next_to_execute s1)
          /\ reply2requests i v keys (log_entry2requests entry) (sm_state s1) (last_reply_state s1)
             = (reps, sm_state s2, last_reply_state s2)
      ).
  Proof.
    introv fexec.
    unfold find_and_execute_requests in fexec; smash_pbft.
    unfold execute_requests in *.
    destruct (ready s1); smash_pbft; tcsp;[].

    rename_hyp_with check_broadcast_checkpoint check.
    applydup check_broadcast_checkpoint_preserves_next_to_execute in check as eqnext; simpl in *; auto.
    applydup check_broadcast_checkpoint_preserves_sm_state in check as eqsm; simpl in *; auto.
    applydup check_broadcast_checkpoint_preserves_last_reply_state in check as eqlast; simpl in *; auto.

    right; exists x x5; dands; auto; try congruence.
  Qed.

  Lemma sm_state_decrement_requests_in_progress :
    forall i v s,
      sm_state (decrement_requests_in_progress_if_primary i v s)
      = sm_state s.
  Proof.
    introv; unfold decrement_requests_in_progress_if_primary; smash_pbft.
  Qed.
  Hint Rewrite sm_state_decrement_requests_in_progress : pbft.

  Lemma last_reply_state_decrement_requests_in_progress :
    forall i v s,
      last_reply_state (decrement_requests_in_progress_if_primary i v s)
      = last_reply_state s.
  Proof.
    introv; unfold decrement_requests_in_progress_if_primary; smash_pbft.
  Qed.
  Hint Rewrite last_reply_state_decrement_requests_in_progress : pbft.

  Lemma low_water_mark_change_next_to_execute :
    forall s n,
      low_water_mark (change_next_to_execute s n)
      = low_water_mark s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite low_water_mark_change_next_to_execute : pbft.

  Lemma low_water_mark_change_sm_state :
    forall s sm,
      low_water_mark (change_sm_state s sm)
      = low_water_mark s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite low_water_mark_change_sm_state : pbft.

  Lemma low_water_mark_change_last_reply_state :
    forall s r,
      low_water_mark (change_last_reply_state s r)
      = low_water_mark s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite low_water_mark_change_last_reply_state : pbft.

  Lemma log_checkpoint_cert_from_new_view_preserves_next_to_execute :
    forall i s1 v n C S s2 cop,
      log_checkpoint_cert_from_new_view i s1 v n C S = (s2, cop)
      -> next_to_execute s2 = next_to_execute s1.
  Proof.
    introv cert.
    unfold log_checkpoint_cert_from_new_view in cert; smash_pbft.
  Qed.

  Lemma log_checkpoint_cert_from_new_view_preserves_sm_state :
    forall i s1 v n C S s2 cop,
      log_checkpoint_cert_from_new_view i s1 v n C S = (s2, cop)
      -> sm_state s2 = sm_state s1.
  Proof.
    introv cert.
    unfold log_checkpoint_cert_from_new_view in cert; smash_pbft.
  Qed.

  Lemma log_checkpoint_cert_from_new_view_preserves_last_reply_state :
    forall i s1 v n C S s2 cop,
      log_checkpoint_cert_from_new_view i s1 v n C S = (s2, cop)
      -> last_reply_state s2 = last_reply_state s1.
  Proof.
    introv cert.
    unfold log_checkpoint_cert_from_new_view in cert; smash_pbft.
  Qed.

  Lemma update_state_new_view_preserves_next_to_execute :
    forall i s1 nv s2 msgs,
      correct_new_view nv = true
      -> well_formed_log (log s1)
      -> update_state_new_view i s1 nv = (s2, msgs)
      ->
      exists maxV vc,
        view_change_cert2max_seq_vc (new_view2cert nv) = Some (maxV, vc)
        /\
        (
          (
            low_water_mark s1 < maxV
            /\ next_to_execute s1 <= maxV
            /\ low_water_mark s2 = maxV
            /\ next_to_execute s2 = next_seq maxV
            /\ sm_state s2 = si_state (view_change2stable vc)
            /\ last_reply_state s2 = si_lastr (view_change2stable vc)
          )
          \/
          (
            low_water_mark s1 < maxV
            /\ maxV < next_to_execute s1
            /\ low_water_mark s2 = maxV
            /\ next_to_execute s2 = next_to_execute s1
            /\ sm_state s2 = sm_state s1
            /\ last_reply_state s2 = last_reply_state s1
          )
          \/
          (
            maxV <= low_water_mark s1
            /\ low_water_mark s2 = low_water_mark s1
            /\ next_to_execute s2 = next_to_execute s1
            /\ sm_state s2 = sm_state s1
            /\ last_reply_state s2 = last_reply_state s1
          )
        ).
  Proof.
    introv cor wf upd.
    unfold update_state_new_view, update_checkpoint_from_new_view in upd;
      smash_pbft;[| | |];
        try rename_hyp_with log_checkpoint_cert_from_new_view cert;
        try rename_hyp_with view_change_cert2max_seq_vc mseq;
        try applydup log_checkpoint_cert_from_new_view_preserves_next_to_execute in cert;
        try applydup log_checkpoint_cert_from_new_view_preserves_sm_state in cert;
        try applydup log_checkpoint_cert_from_new_view_preserves_last_reply_state in cert;
        try applydup sn_of_view_change_cert2max_seq_vc in mseq;
        try applydup view_change_cert2_max_seq_vc_some_in in mseq.

    - eexists; eexists; dands; eauto;[].
      left; dands; auto; try congruence;[].
      apply correct_new_view_implies_correct_view_change in mseq1; auto.
      subst.
      eapply log_checkpoint_cert_from_new_view_preserves_low_water_mark2 in cert; eauto.

    - eexists; eexists; dands; eauto;[].
      right; left.
      dands; auto; try congruence; try omega.
      apply correct_new_view_implies_correct_view_change in mseq1; auto.
      subst.
      eapply log_checkpoint_cert_from_new_view_preserves_low_water_mark2 in cert; eauto.

    - eexists; eexists; dands; eauto;[].
      right; right.
      dands; auto; try congruence; try omega.

    - rewrite view_change_cert2max_seq_vc_none_implies_correct_new_view_false in cor; auto; ginv.
  Qed.

  Lemma correct_new_view_implies_has_new_view_log_new_view_and_entry :
    forall s nv e,
      correct_new_view nv = true
      -> 0 < vce_view e
      -> vce_new_view e = None
      -> has_new_view (log_new_view_and_entry s nv e) (vce_view e) = true.
  Proof.
    introv cor nvnone lee.
    unfold has_new_view; smash_pbft.
    unfold has_new_view1.

    induction s; simpl; smash_pbft;
      try (complete (unfold add_new_view_to_entry in *; destruct e; simpl in *;
                     subst; simpl in *; ginv)).
  Qed.

  Lemma new_view_in_log_log_new_view_and_entry :
    forall nv s e,
      vce_new_view e = None
      -> vce_view e = new_view2view nv
      -> new_view_in_log nv (log_new_view_and_entry s nv e).
  Proof.
    induction s; introv vcnone eqvs; simpl; smash_pbft;
      try (complete (destruct e; simpl in *; subst; simpl in *; tcsp)).
  Qed.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_next_to_execute :
    forall i ppd s1 s2 msgs,
      add_prepare_to_log_from_new_view_pre_prepare i s1 ppd = (s2, msgs)
      -> next_to_execute s2 = next_to_execute s1.
  Proof.
    introv add; unfold add_prepare_to_log_from_new_view_pre_prepare in add; smash_pbft.
    rename_hyp_with check_send_replies check.
    apply check_send_replies_preserves_next_to_execute in check; simpl in *; auto.
  Qed.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_sm_state :
    forall i ppd s1 s2 msgs,
      add_prepare_to_log_from_new_view_pre_prepare i s1 ppd = (s2, msgs)
      -> sm_state s2 = sm_state s1.
  Proof.
    introv add; unfold add_prepare_to_log_from_new_view_pre_prepare in add; smash_pbft.
    rename_hyp_with check_send_replies check.
    apply check_send_replies_preserves_sm_state in check; simpl in *; auto.
  Qed.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_last_reply_state :
    forall i ppd s1 s2 msgs,
      add_prepare_to_log_from_new_view_pre_prepare i s1 ppd = (s2, msgs)
      -> last_reply_state s2 = last_reply_state s1.
  Proof.
    introv add; unfold add_prepare_to_log_from_new_view_pre_prepare in add; smash_pbft.
    rename_hyp_with check_send_replies check.
    apply check_send_replies_preserves_last_reply_state in check; simpl in *; auto.
  Qed.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_next_to_execute :
    forall i P s1 s2 msgs,
      add_prepares_to_log_from_new_view_pre_prepares i s1 P = (s2, msgs)
      -> next_to_execute s2 = next_to_execute s1.
  Proof.
    induction P; introv add; simpl in *; tcsp; smash_pbft.
    rename_hyp_with add_prepare_to_log_from_new_view_pre_prepare add.
    rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares adds.
    apply IHP in adds.
    apply add_prepare_to_log_from_new_view_pre_prepare_preserves_next_to_execute in add; try congruence.
  Qed.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_sm_state :
    forall i P s1 s2 msgs,
      add_prepares_to_log_from_new_view_pre_prepares i s1 P = (s2, msgs)
      -> sm_state s2 = sm_state s1.
  Proof.
    induction P; introv add; simpl in *; tcsp; smash_pbft.
    rename_hyp_with add_prepare_to_log_from_new_view_pre_prepare add.
    rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares adds.
    apply IHP in adds.
    apply add_prepare_to_log_from_new_view_pre_prepare_preserves_sm_state in add; try congruence.
  Qed.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_last_reply_state :
    forall i P s1 s2 msgs,
      add_prepares_to_log_from_new_view_pre_prepares i s1 P = (s2, msgs)
      -> last_reply_state s2 = last_reply_state s1.
  Proof.
    induction P; introv add; simpl in *; tcsp; smash_pbft.
    rename_hyp_with add_prepare_to_log_from_new_view_pre_prepare add.
    rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares adds.
    apply IHP in adds.
    apply add_prepare_to_log_from_new_view_pre_prepare_preserves_last_reply_state in add; try congruence.
  Qed.

  Lemma correct_new_view_implies_has_new_view_log_new_view :
    forall s nv,
      0 < new_view2view nv
      -> correct_new_view nv = true
      -> (forall entry x, In entry s -> vce_new_view entry = Some x -> correct_new_view x = true)
      -> has_new_view s (new_view2view nv) = false
      -> has_new_view (log_new_view s nv) (new_view2view nv) = true.
  Proof.
    introv gt0 cor allcor hnv.
    unfold has_new_view in *; smash_pbft.
    unfold has_new_view1 in *.

    induction s; simpl; smash_pbft;
      repeat (autodimp IHs hyp); try (complete (introv i j; eapply allcor; eauto));
        try (complete (destruct a; simpl in *; subst; simpl in *; ginv)).
  Qed.

  Lemma implies_new_view_in_log_log_new_view :
    forall s nv,
      (forall entry x, In entry s -> vce_new_view entry = Some x -> correct_new_view x = true)
      -> has_new_view s (new_view2view nv) = false
      -> new_view_in_log nv (log_new_view s nv).
  Proof.
    introv allcor hnv.
    unfold has_new_view in *; smash_pbft.
    unfold has_new_view1 in hnv.

    induction s; introv; simpl in *; smash_pbft;
      repeat (autodimp IHs hyp); try (complete (introv i j; eapply allcor; eauto));
        try (complete (destruct a; simpl in *; subst; simpl in *; ginv)).
  Qed.

  Lemma next_to_execute_check_one_stable :
    forall i s l,
      next_to_execute (check_one_stable i s l) = next_to_execute s.
  Proof.
    induction l; introv; smash_pbft.
    eapply check_stable_preserves_next_to_execute; eauto.
  Qed.
  Hint Rewrite next_to_execute_check_one_stable : pbft.

  Lemma sm_state_check_one_stable :
    forall i s l,
      sm_state (check_one_stable i s l) = sm_state s.
  Proof.
    induction l; introv; smash_pbft.
    eapply check_stable_preserves_sm_state; eauto.
  Qed.
  Hint Rewrite sm_state_check_one_stable : pbft.

  Lemma last_reply_state_check_one_stable :
    forall i s l,
      last_reply_state (check_one_stable i s l) = last_reply_state s.
  Proof.
    induction l; introv; smash_pbft.
    eapply check_stable_preserves_last_reply_state; eauto.
  Qed.
  Hint Rewrite last_reply_state_check_one_stable : pbft.

  Lemma next_to_execute_from :
    forall i (eo : EventOrdering) (e : Event) st,
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> 1 < next_to_execute st (* initial one is 1 *)
      -> exists e' st1 st2,
          e' ⊑ e
          /\ state_sm_before_event (PBFTreplicaSM i) e' = Some st1
          /\ state_sm_on_event (PBFTreplicaSM i) e' = Some st2
          /\ next_to_execute st2 = next_to_execute st
          /\ sm_state st2 = sm_state st
          /\ last_reply_state st2 = last_reply_state st
          /\
          (
            (* either we update the state because we just committed a request *)
            (
              exists entry reps,
                next_to_execute st2 = next_seq (next_to_execute st1)
                /\ find_entry (log st1) (next_to_execute st1) = Some entry
                /\ is_committed_entry entry = true
                /\ reply2requests i (current_view st1) (local_keys st1) (log_entry2requests entry) (sm_state st1) (last_reply_state st1)
                   = (reps, sm_state st2, last_reply_state st2)
            )
            \/
            (* or we update the state because of some new-view *)
            (
              exists nv maxV vc,
                initial_view < new_view2view nv
                /\ current_view st1 <= new_view2view nv
                /\ has_new_view (view_change_state st1) (new_view2view nv) = false
                /\ has_new_view (view_change_state st2) (new_view2view nv) = true
                /\ view_change_cert2max_seq_vc (new_view2cert nv) = Some (maxV,vc)
                /\ new_view_in_log nv (view_change_state st2)
                /\ next_to_execute st2 = next_seq maxV
                /\ next_to_execute st1 <= maxV
                /\ sm_state st2 = si_state (view_change2stable vc)
                /\ last_reply_state st2 = si_lastr (view_change2stable vc)
            )
          ).
  Proof.
    intros i eo e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv eqst next.

    dup eqst as eqst_At_e.
    rewrite state_sm_on_event_unroll2 in eqst.

    match goal with
    | [ H : context[map_option _ ?s] |- _ ] =>
      remember s as sop; symmetry in Heqsop; destruct sop; simpl in *;[|ginv];op_st_some m eqtrig
    end.

    unfold PBFTreplica_update in eqst.

    destruct m;
      simpl in *; ginv; subst; tcsp;
        try smash_handlers; try (smash_pbft_ind ind).

    {
      (* pre-prepare *)

      rename_hyp_with check_send_replies check.
      applydup check_send_replies_preserves_next_to_execute in check as eqnext; simpl in *.
      applydup check_send_replies_preserves_sm_state in check as eqsm; simpl in *.
      applydup check_send_replies_preserves_last_reply_state in check as eqlast; simpl in *.
      rewrite eqnext in next; rewrite eqnext; rewrite eqsm; rewrite eqlast.
      try (smash_pbft_ind ind).
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.
      applydup check_send_replies_preserves_next_to_execute in check as eqnext; simpl in *.
      applydup check_send_replies_preserves_sm_state in check as eqsm; simpl in *.
      applydup check_send_replies_preserves_last_reply_state in check as eqlast; simpl in *.
      rewrite eqnext in next; rewrite eqnext; rewrite eqsm; rewrite eqlast.
      try (smash_pbft_ind ind).
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      applydup check_send_replies_preserves_next_to_execute in check as eqnext; simpl in *.
      applydup check_send_replies_preserves_sm_state in check as eqsm; simpl in *.
      applydup check_send_replies_preserves_last_reply_state in check as eqlast; simpl in *.
      rewrite eqnext in next; rewrite eqnext; rewrite eqsm; rewrite eqlast.
      try (smash_pbft_ind ind).
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.
      autorewrite with pbft in *.
      applydup find_and_execute_requests_preserves_next_to_execute2 in fexec.
      repndors; repnd;[try rewrite fexec1 in next; try (smash_pbft_ind ind)|].

      exrepnd.
      exists e; eexists; eexists; dands; eauto; eauto 2 with eo;
        autorewrite with pbft; auto.
      left.
      exists entry reps; dands; auto.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with update_state_new_view upd.

      apply CheckBCastNewView2entry_some_implies in cb.
      applydup update_state_new_view_preserves_wf in upd; simpl;[|eauto 4 with pbft];[].
      applydup wf_view_change_state_implies_all_entries in cb;[|eauto 3 with pbft];[].

      applydup check_broadcast_new_view_implies_eq_views in check;[|eauto 4 with pbft].
      applydup check_broadcast_new_view_implies in check.

      applydup update_state_new_view_preserves_next_to_execute in upd;
        simpl;[|eauto 2 with pbft|eauto 4 with pbft];[].
      simpl in *; autorewrite with pbft in *.

      exrepnd; repndors; repnd;
        [|allrw; try (smash_pbft_ind ind)
         |allrw; try (smash_pbft_ind ind)];[].

      exists e; eexists; eexists; dands; eauto; eauto 2 with eo;[].
      right.

      match goal with
      | [ H1 : view_change_cert2max_seq_vc ?a = _,
               H2 : view_change_cert2max_seq ?b = _,
                    H3 : ?a = ?b |- _] =>
        unfold view_change_cert2max_seq in H2; rewrite <- H3 in H2;
          rewrite H1 in H2; inversion H2 as [xx]; symmetry in xx; subst maxV0
      end.

      exists x2 maxV vc; dands; auto; try congruence;[| |].

      - match goal with
          | [ H : new_view2view _ = _ |- _ ] => rewrite H
          end.
          apply implies_has_new_view_false; auto; eauto 2 with pbft.

      - applydup update_state_new_view_preserves_view_change_state in upd as eqv.
        rewrite eqv; simpl.
        match goal with
        | [ H : new_view2view _ = _ |- _ ] => rewrite H
        end.
        match goal with
        | [ H : _ = vce_view _ |- _ ] => rewrite <- H
        end.
        apply correct_new_view_implies_has_new_view_log_new_view_and_entry; auto; eauto 2 with pbft; try congruence;[].
        subst; autorewrite with pbft; auto.

      - applydup update_state_new_view_preserves_view_change_state in upd as eqv.
        rewrite eqv; simpl.
        apply new_view_in_log_log_new_view_and_entry; auto; try congruence;[].
        subst; autorewrite with pbft; auto.
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with correct_new_view cor.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_next_to_execute in add.
      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_sm_state in add.
      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_last_reply_state in add.
      applydup PBFTnew_view_in_log.add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state in add as eqvcs.
      simpl in *.

      applydup update_state_new_view_preserves_next_to_execute in upd;
        simpl;[|eauto 2 with pbft|eauto 4 with pbft];[].
      simpl in *; autorewrite with pbft in *.

      exrepnd; repndors; repnd;
        try (assert (1 < next_to_execute p) as xx by congruence);
        [|allrw; try (smash_pbft_ind ind)
         |allrw; try (smash_pbft_ind ind)];[].

      exists e; eexists; eexists; dands; eauto; eauto 2 with eo;[].
      right.

      exists v maxV vc; dands; auto; try congruence;[|].

      - applydup update_state_new_view_preserves_view_change_state in upd as eqv.
        rewrite eqv; simpl.
        apply correct_new_view_implies_has_new_view_log_new_view; auto; eauto 2 with pbft; try congruence;[].

        introv k eqnv.
        rewrite eqvcs in k.
        eapply PBFT_A_1_2_5_before; try (exact Heqsop); auto.
        eauto 3 with pbft.

      - applydup update_state_new_view_preserves_view_change_state in upd as eqv.
        rewrite eqv; simpl.
        rewrite eqvcs.
        apply implies_new_view_in_log_log_new_view; auto; eauto 2 with pbft;[].

        introv k eqnv.
        eapply PBFT_A_1_2_5_before; try (exact Heqsop); auto.
        eauto 3 with pbft.
    }
  Qed.

End PBFTexecute.


Hint Rewrite @next_to_execute_decrement_requests_in_progress_if_primary : pbft.
Hint Rewrite @sm_state_decrement_requests_in_progress : pbft.
Hint Rewrite @last_reply_state_decrement_requests_in_progress : pbft.
Hint Rewrite @low_water_mark_change_next_to_execute : pbft.
Hint Rewrite @low_water_mark_change_sm_state : pbft.
Hint Rewrite @low_water_mark_change_last_reply_state : pbft.
Hint Rewrite @next_to_execute_check_one_stable : pbft.
Hint Rewrite @sm_state_check_one_stable : pbft.
Hint Rewrite @last_reply_state_check_one_stable : pbft.
