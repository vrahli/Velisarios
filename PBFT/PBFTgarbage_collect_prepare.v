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


Require Export PBFTgarbage_collect_misc1.


Section PBFTgarbage_collect_prepare.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.

  Lemma find_and_execute_requests_prepare_in_log_check_between_water_marks :
    forall i state msgs state' p,
      find_and_execute_requests i (current_view state) (local_keys state) state = (msgs, state')
      -> prepare_in_log p (log state') = true
      -> check_between_water_marks (low_water_mark state') (prepare2seq p) = true
      -> check_between_water_marks (low_water_mark state) (prepare2seq p) = true.
  Proof.
    introv fexec h check.
    applydup find_and_execute_requests_preserves_low_water_mark in fexec.
    rewrite <- fexec0 in check.
    eapply find_and_execute_requests_preserves_prepare_in_log in fexec; [|eauto]. auto.
  Qed.
  Hint Resolve find_and_execute_requests_prepare_in_log_check_between_water_marks : pbft.

  Lemma find_and_execute_requests_prepare_in_log_check_between_water_marks2 :
    forall i state msgs state' p,
      find_and_execute_requests i (current_view state) (local_keys state) state = (msgs, state')
      -> prepare_in_log p (log state') = true
      -> check_between_water_marks (low_water_mark state) (prepare2seq p) = true
      -> check_between_water_marks (low_water_mark state') (prepare2seq p) = true.
  Proof.
    introv fexec h check.
    applydup find_and_execute_requests_preserves_low_water_mark in fexec.
    rewrite fexec0 in check.
    eapply find_and_execute_requests_preserves_prepare_in_log in fexec; [|eauto]. auto.
  Qed.
  Hint Resolve find_and_execute_requests_prepare_in_log_check_between_water_marks2 : pbft.

  Lemma  find_and_execute_requests_check_between_water_marks :
    forall i view keys st1 msgs st2 p,
      find_and_execute_requests i view keys st1 = (msgs, st2)
      -> check_between_water_marks (low_water_mark st2) (prepare2seq p) = true
      -> check_between_water_marks (low_water_mark st1) (prepare2seq p) = true.
  Proof.
    introv find. eapply find_and_execute_requests_preserves_low_water_mark in find; allrw <-. auto.
  Qed.
  Hint Resolve  find_and_execute_requests_check_between_water_marks : pbft.

  Lemma prepares_are_between_water_marks_if_in_log :
    forall p i (eo : EventOrdering) (e : Event) st,
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> prepare_in_log p (log st) = true
      -> check_between_water_marks (low_water_mark st) (prepare2seq p) = true.
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers3 smash_pbft_ind3.

    {
      (* pre-prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_pre_prepare_and_prepare2log add.

      applydup PBFTordering.check_send_replies_preserves_low_water_mark in check.

      eapply check_send_replies_preserves_prepare_in_log in check;[|eauto].
      simpl in check.

      eapply add_new_pre_prepare_and_prepare2log_preserves_prepare_in_log in add;
        [| |eauto]; autorewrite with pbft; auto;[].

      rewrite <- check0; autorewrite with pbft.
      repndors; try (smash_pbft_ind ind).
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_prepare2log add.

      applydup PBFTordering.check_send_replies_preserves_low_water_mark in check.

      eapply check_send_replies_preserves_prepare_in_log in check;[|eauto].
      simpl in check.

      eapply add_new_prepare2log_preserves_prepare_in_log in add;[|eauto].

      rewrite <- check0; autorewrite with pbft.
      repndors; repnd; subst; try (smash_pbft_ind ind).
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_commit2log add.

      applydup PBFTordering.check_send_replies_preserves_low_water_mark in check.

      eapply check_send_replies_preserves_prepare_in_log in check;[|eauto].
      simpl in check.

      eapply add_new_commit2log_preserves_prepare_in_log in add.
      rewrite add in check; clear add.

      rewrite <- check0; autorewrite with pbft.
      repndors; try (smash_pbft_ind ind).
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.

      applydup find_and_execute_requests_preserves_low_water_mark in fexec.
      rewrite <- fexec0.
      eapply find_and_execute_requests_preserves_prepare_in_log in fexec;[|eauto].
      try (smash_pbft_ind ind).
    }

    {
      (* check-stable *)

      rename_hyp_with prepare_in_log prep.

      assert (check_between_water_marks (low_water_mark p0) (prepare2seq p) = true) as b by (smash_pbft_ind ind).
      clear ind.
      match goal with
      | [ |- context[check_one_stable ?i ?s ?l] ] =>
        pose proof (low_water_mark_check_one_stable i s l) as w
      end.
      unfold check_between_water_marks in *; smash_pbft.
      dands; auto; simpl in *; try omega;[].
      apply check_one_stable_preserves_prepare_in_log2 in prep; eauto 3 with pbft; tcsp.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with prepare_in_log prep.

      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 4 with pbft;[].

      dup prep as prep'.
      eapply update_state_new_view_preserves_prepare_in_log in prep';[| |eauto];
        simpl in *; autorewrite with pbft in *; eauto 4 with pbft;[].

      assert (check_between_water_marks (low_water_mark p0) (prepare2seq p) = true)
        as bwm by (smash_pbft_ind ind).

      unfold update_state_new_view in *; smash_pbft.

      rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup sn_of_view_change_cert2max_seq_vc in mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      subst.

      rename_hyp_with log_checkpoint_cert_from_new_view check.
      applydup log_checkpoint_cert_from_new_view_preserves_well_formed_log in check;
        simpl in *;[|eauto 4 with pbft];[].

      assert (correct_view_change (new_view2view x2) x8 = true) as corvc by eauto 3 with pbft.

      applydup clear_log_checkpoint_preserves_prepare_in_log2 in prep; auto;[].
      repnd.

      unfold log_checkpoint_cert_from_new_view in *; smash_pbft; simpl in *;[|].

      + rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
        eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft.
        subst.

        unfold check_between_water_marks in *; smash_pbft.
        dands; auto; simpl in *; try omega.

      + rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
        eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft.
        subst.

        unfold check_between_water_marks in *; smash_pbft.
        allrw SeqNumLe_true; simpl in *.
        dands; auto; simpl in *; try omega.
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with prepare_in_log prep.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_low_water_mark in add.
      autorewrite with pbft in *.

      eapply update_state_new_view_preserves_prepare_in_log2 in prep;[| | |eauto];
        simpl in *; auto;[].
      repnd.
      autorewrite with pbft in *.
      exrepnd.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log in prep2;[|eauto];[].

      simpl in *.
      autorewrite with pbft in *.
      destruct prep2 as [prep2|prep2].

      - assert (check_between_water_marks (low_water_mark p0) (prepare2seq p) = true)
          as bwm by (smash_pbft_ind ind).
        rewrite add1 in bwm.

        repndors;[|exrepnd; allrw <- ; auto];[].

        repnd.
        subst.
        unfold check_between_water_marks in *; smash_pbft.
        simpl in *; try omega.

      - exrepnd; subst; simpl in *; autorewrite with pbft in *.
        rewrite add1 in prep5.

        hide_hyp add.
        hide_hyp ind.
        hide_hyp prep2.

        applydup seq_of_pre_prepare_in_new_view in prep3;auto;[].
        exrepnd.
        rewrite prep1 in prep4; ginv.

        unfold check_between_water_marks; smash_pbft; allrw SeqNumLe_true; simpl in *.
        dands;[repndors; repnd; simpl in *; try omega; try congruence|];[].

        applydup pre_prepare_in_new_view_exists in prep3; auto.
        exrepnd.
        apply in_view_change_cert2prep_implies in prep4; exrepnd.

        assert (correct_view_change (new_view2view v) vc = true) as cvc by (eauto 3 with pbft).

        unfold correct_view_change in cvc; smash_pbft.
        unfold correct_view_change_preps in *.
        allrw forallb_forall.
        discover.
        clear cvc cvc1 cvc0.
        smash_pbft.
        unfold check_between_water_marks in *; smash_pbft.
        allrw SeqNumLe_true.

        dup prep1 as w.
        eapply view_change_cert2max_seq_implies_le in prep1;[|eauto].
        simpl in *.

        repndors; repnd; subst; try omega;[].
        rewrite prep0 in *; omega.
    }
  Qed.

  Lemma check_send_replies_update_log_preserves_prepare_somewhere_in_log_false :
    forall slf view keys eop state n msgs state' p L,
      check_send_replies slf view keys eop (update_log state L) n = (msgs, state')
      -> prepare_somewhere_in_log p (log state') = false
      -> prepare_somewhere_in_log p L = false.
  Proof.
    introv check h. eapply check_send_replies_preserves_prepare_somewhere_in_log_false in h;[|eauto]. simpl in *. auto.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_prepare_somewhere_in_log_false : pbft.

  Lemma prepares_get_garbage_collected_direct_pred0_v2 :
    forall i (eo : EventOrdering) (e : Event) s1 s2 p,
      state_sm_before_event (PBFTreplicaSM i) e = Some s1
      -> state_sm_on_event (PBFTreplicaSM i) e = Some s2
      -> prepare_somewhere_in_log p (log s1) = true
      -> prepare_somewhere_in_log p (log s2) = false
      -> prepare2seq p <= low_water_mark s2.
  Proof.
    introv eqst1 eqst2 prep1 prep2.
    rewrite state_sm_on_event_unroll2 in eqst2.

    match goal with
    | [ H : context[state_sm_before_event ?sm ?e] |- _ ] =>
      remember (state_sm_before_event sm e) as st; symmetry in Heqst;
        destruct st; simpl in *; ginv;[]; op_st_some m eqtrig
    end.

    unfold PBFTreplica_update in eqst2.

    destruct m;
      simpl in *; ginv; subst; tcsp;
        try smash_handlers; try (smash_pbft_ind ind).

    (* 6 subgoals *)

    {
      (* pre-prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_pre_prepare_and_prepare2log add.

      eapply check_send_replies_update_log_preserves_prepare_somewhere_in_log_false in prep2; eauto.

      eapply add_new_pre_prepare_and_prepare2log_preserves_prepare_somewhere_in_log_false in prep2;[|eauto].

      pbft_simplifier.
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_prepare2log add.

      eapply check_send_replies_update_log_preserves_prepare_somewhere_in_log_false in prep2;[|eauto].

      eapply add_new_prepare2log_preserves_prepare_somewhere_in_log_false in prep2;[|eauto].
      pbft_simplifier.
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_commit2log add.

      eapply check_send_replies_update_log_preserves_prepare_somewhere_in_log_false in prep2;[|eauto].

      eapply add_new_commit2log_preserves_prepare_somewhere_in_log_false in prep2;[|eauto].
      pbft_simplifier.
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.
      applydup find_and_execute_requests_preserves_low_water_mark in fexec.
      rewrite <- fexec0.

      dup fexec as fexec'.
      eapply find_and_execute_requests_preserves_prepare_somewhere_in_log_forward in fexec';
        eauto; eauto 3 with pbft; pbft_simplifier.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with CheckBCastNewView2entry cb.

      apply CheckBCastNewView2entry_some_implies in cb.
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 4 with pbft;[].
      applydup check_broadcast_new_view_generates in check as cor.

      unfold update_state_new_view in upd; smash_pbft;[].

      rename_hyp_with view_change_cert2max_seq_vc mseq.
      rename_hyp_with log_checkpoint_cert_from_new_view cert.
      applydup sn_of_view_change_cert2max_seq_vc in mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      subst.

      apply clear_log_checkpoint_preserves_prepare_somewhere_in_log_false in prep2.
      repndors.

      {
        eapply log_checkpoint_cert_from_new_view_preserves_prepare_somewhere_in_log_false_backward in cert; eauto.
        simpl in *; autorewrite with pbft in *; pbft_simplifier.
      }

      unfold log_checkpoint_cert_from_new_view in *;
        simpl in *; smash_pbft; simpl in *; autorewrite with pbft in *;
          [| | |].

      - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
        eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext;
          eauto 3 with pbft;[].
        subst; simpl in *.

        unfold check_between_water_marks; smash_pbft.

      - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
        apply extract_seq_and_digest_from_checkpoint_certificate_none_implies in ext.
        rewrite ext in *.
        simpl in *; ginv.

      - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
        eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext;
          eauto 3 with pbft;[].
        subst; simpl in *.

        unfold check_between_water_marks; smash_pbft.

      - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
        apply extract_seq_and_digest_from_checkpoint_certificate_none_implies in ext.

        rename_hyp_with view_change_cert2max_seq_vc maxs.
        applydup view_change_cert2_max_seq_vc_some_in in maxs.
        applydup sn_of_view_change_cert2max_seq_vc in maxs.
        subst.

        assert (correct_view_change (new_view2view x2) x8 = true) as cvc by eauto 3 with pbft;[].
        unfold correct_view_change, correct_view_change_cert in cvc; smash_pbft.
        rewrite ext in *.
        simpl in *; ginv; try omega.
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_low_water_mark in add.
      autorewrite with pbft in *.

      destruct (le_dec (prepare2seq p) (low_water_mark s2)) as [d|d]; auto.
      assert False; tcsp.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_somewhere_in_log_true_forward in add;
        simpl;[| | |eauto];auto; eauto 3 with pbft;[].

      eapply update_state_new_view_preserves_prepare_somewhere_in_log_true_forward in upd;
        simpl;[| | |eauto];auto; try omega.
      pbft_simplifier.
    }
  Qed.

  Lemma prepares_get_garbage_collected_direct_pred0 :
    forall i (eo : EventOrdering) (e : Event) s1 s2 p,
      state_sm_before_event (PBFTreplicaSM i) e = Some s1
      -> state_sm_on_event (PBFTreplicaSM i) e = Some s2
      -> prepare_somewhere_in_log p (log s1) = true
      -> prepare_somewhere_in_log p (log s2) = false
      -> check_between_water_marks (low_water_mark s2) (prepare2seq p) = false.
  Proof.
    introv eqst1 eqst2 prep1 prep2.

    pose proof (prepares_get_garbage_collected_direct_pred0_v2 i eo e s1 s2 p) as q.
    repeat (autodimp q hyp).
    unfold check_between_water_marks; smash_pbft.
  Qed.

  Lemma prepares_get_garbage_collected_direct_pred :
    forall i (eo : EventOrdering) (e1 e2 : Event) state1 state2 p,
      e1 ⊂ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> prepare_somewhere_in_log p (log state1) = true
      -> prepare_somewhere_in_log p (log state2) = false
      -> check_between_water_marks (low_water_mark state2) (prepare2seq p) = false.
  Proof.
    introv lees eqst1 eqst2 prep1 prep2.
    eapply state_sm_before_event_if_on_event_direct_pred in eqst1;[|eauto].
    clear dependent e1.
    eapply prepares_get_garbage_collected_direct_pred0; eauto.
  Qed.

  Lemma prepares_get_garbage_collected_direct_pred_v2 :
    forall i (eo : EventOrdering) (e1 e2 : Event) state1 state2 p,
      e1 ⊂ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> prepare_somewhere_in_log p (log state1) = true
      -> prepare_somewhere_in_log p (log state2) = false
      -> prepare2seq p <= low_water_mark state2.
  Proof.
    introv lees eqst1 eqst2 prep1 prep2.
    eapply state_sm_before_event_if_on_event_direct_pred in eqst1;[|eauto].
    clear dependent e1.
    eapply prepares_get_garbage_collected_direct_pred0_v2; eauto.
  Qed.

  Lemma prepares_get_garbage_collected_v2 :
    forall i (eo : EventOrdering) (e1 e2 : Event) state1 state2 p,
      e1 ⊏ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> prepare_somewhere_in_log p (log state1) = true
      -> prepare_somewhere_in_log p (log state2) = false
      -> prepare2seq p <= low_water_mark state2.
  Proof.
    intros i eo e1 e2.
    induction e2 as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv ltes eqst1 eqst2 prep1 prep2.

    pose proof (local_implies_pred_or_local e1 e2) as q; autodimp q hyp.
    repndors.

    - eapply prepares_get_garbage_collected_direct_pred_v2; eauto.

    - exrepnd.

      pose proof (state_sm_on_event_some_between e e2 (PBFTreplicaSM i) state2) as h.
      repeat (autodimp h hyp); eauto 3 with eo;[].
      exrepnd.

      remember (prepare_somewhere_in_log p (log s')) as b.
      symmetry in Heqb; destruct b.

      + eapply (prepares_get_garbage_collected_direct_pred_v2 i _ e e2) in q1; eauto.

      + pose proof (PBFTlow_water_mark_increases_on_event _ e1 e i state1 s') as lelwm1.
        repeat (autodimp lelwm1 hyp); eauto 2 with eo.

        pose proof (PBFTlow_water_mark_increases_on_event _ e e2 i s' state2) as lelwm2.
        repeat (autodimp lelwm2 hyp); eauto 3 with eo.

        apply pred_implies_local_pred in q1; subst.
        autodimp ind hyp; eauto 2 with eo.
        pose proof (ind state1 s' p) as q; repeat (autodimp q hyp).
        clear ind.
        omega.
  Qed.

  Lemma prepares_get_garbage_collected :
    forall i (eo : EventOrdering) (e1 e2 : Event) state1 state2 p,
      e1 ⊏ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> prepare_somewhere_in_log p (log state1) = true
      -> prepare_somewhere_in_log p (log state2) = false
      -> check_between_water_marks (low_water_mark state2) (prepare2seq p) = false.
  Proof.
    introv ltes eqst1 eqst2 prep1 prep2.
    eapply prepares_get_garbage_collected_v2 in ltes; eauto.
    unfold check_between_water_marks; smash_pbft.
  Qed.

  Lemma non_garbage_collected_prepares_direct_pred :
    forall i (eo : EventOrdering) (e1 e2 : Event) state1 state2 p1 p2,
      e1 ⊂ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> prepare_somewhere_in_log p1 (log state1) = true
      -> prepare_somewhere_in_log p2 (log state2) = true
      -> prepare2seq p1 = prepare2seq p2
      -> prepare_somewhere_in_log p1 (log state2) = true.
  Proof.
    introv lees eqst1 eqst2 prep1 prep2 eqseqs.

    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.

    assert False; tcsp.

    pose proof (prepares_get_garbage_collected_direct_pred
                  i eo e1 e2 state1 state2 p1) as q.
    repeat (autodimp q hyp).
    rewrite eqseqs in q.

    apply prepare_somewhere_in_log_iff_prepare_in_log in prep2;[|eauto 2 with pbft].
    eapply prepares_are_between_water_marks_if_in_log in prep2;[|eauto].
    pbft_simplifier.
  Qed.

  Lemma non_garbage_collected_prepares :
    forall i (eo : EventOrdering) (e1 e2 : Event) state1 state2 p1 p2,
      e1 ⊏ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> prepare_somewhere_in_log p1 (log state1) = true
      -> prepare_somewhere_in_log p2 (log state2) = true
      -> prepare2seq p1 = prepare2seq p2
      -> prepare_somewhere_in_log p1 (log state2) = true.
  Proof.
    introv lees eqst1 eqst2 prep1 prep2 eqseqs.

    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.

    assert False; tcsp.

    pose proof (prepares_get_garbage_collected i eo e1 e2 state1 state2 p1) as q.
    repeat (autodimp q hyp).
    rewrite eqseqs in q.

    apply prepare_somewhere_in_log_iff_prepare_in_log in prep2;[|eauto 2 with pbft].
    eapply prepares_are_between_water_marks_if_in_log in prep2;[|eauto].
    pbft_simplifier.
  Qed.

End PBFTgarbage_collect_prepare.

Hint Resolve  find_and_execute_requests_check_between_water_marks : pbft.
