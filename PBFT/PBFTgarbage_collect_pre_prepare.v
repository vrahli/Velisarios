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


Section PBFTgarbage_collect_pre_prepare.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma pre_prepares_are_between_water_marks_if_in_log :
    forall p d i (eo : EventOrdering) (e : Event) st,
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> pre_prepare_in_log p d (log st) = true
      -> check_between_water_marks (low_water_mark st) (pre_prepare2seq p) = true.
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers3 smash_pbft_ind3.

    {
      (* request *)

      autorewrite with pbft.

      apply pre_prepare_in_log_add_new_prepare2log in h.
      repndors; try (smash_pbft_ind ind);[].

      repnd; subst; simpl in *.
      unfold check_new_request in *; smash_pbft.
    }

    {
      (* pre-prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_pre_prepare_and_prepare2log add.

      applydup PBFTordering.check_send_replies_preserves_low_water_mark in check.

      eapply check_send_replies_preserves_pre_prepare_in_log in check;[|eauto].
      simpl in check.

      eapply add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log in add;
        [|eauto]; autorewrite with pbft; auto;[].

      rewrite <- check0; autorewrite with pbft.
      repndors; try (smash_pbft_ind ind).
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_prepare2log add.

      applydup PBFTordering.check_send_replies_preserves_low_water_mark in check.

      eapply check_send_replies_preserves_pre_prepare_in_log in check;[|eauto].
      simpl in check.

      eapply add_new_prepare2log_preserves_pre_prepare_in_log in add;[|eauto].

      rewrite <- check0; autorewrite with pbft.
      repndors; repnd; subst; try (smash_pbft_ind ind).
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_commit2log add.

      applydup PBFTordering.check_send_replies_preserves_low_water_mark in check.

      eapply check_send_replies_preserves_pre_prepare_in_log in check;[|eauto].
      simpl in check.

      eapply add_new_commit2log_preserves_pre_prepare_in_log in add.
      rewrite add in check; clear add.

      rewrite <- check0; autorewrite with pbft.
      repndors; try (smash_pbft_ind ind).
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.

      applydup find_and_execute_requests_preserves_low_water_mark in fexec.
      rewrite <- fexec0.
      eapply find_and_execute_requests_preserves_pre_prepare_in_log in fexec;[|eauto].
      try (smash_pbft_ind ind).
    }

    {
      (* check-stable *)

      rename_hyp_with pre_prepare_in_log prep.

      assert (check_between_water_marks (low_water_mark p0) (pre_prepare2seq p) = true) as b by (smash_pbft_ind ind).
      clear ind.
      match goal with
      | [ |- context[check_one_stable ?i ?s ?l] ] =>
        pose proof (low_water_mark_check_one_stable i s l) as w
      end.
      unfold check_between_water_marks in *; smash_pbft.
      dands; auto; simpl in *; try omega;[].
      apply pre_prepare_in_log_check_one_stable2 in prep; eauto 3 with pbft; tcsp.
    }

    {
      (* check-bcast-new-view *)

      autorewrite with pbft in *.

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with pre_prepare_in_log prep.

      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 4 with pbft;[].

      rename_hyp_with CheckBCastNewView2entry ce.
      apply CheckBCastNewView2entry_some_implies in ce.

      unfold update_state_new_view in *; smash_pbft.

      - rename_hyp_with view_change_cert2max_seq_vc mseq.
        applydup sn_of_view_change_cert2max_seq_vc in mseq.
        applydup view_change_cert2_max_seq_vc_some_in in mseq.
        subst.

        rename_hyp_with log_checkpoint_cert_from_new_view check.
        applydup log_checkpoint_cert_from_new_view_preserves_well_formed_log in check;
          simpl in *;[|eauto 4 with pbft];[].

        apply clear_log_checkpoint_preserves_pre_prepare_in_log2 in prep; auto;[].
        repnd.

        assert (correct_view_change (new_view2view x2) x8 = true) as corvc by eauto 3 with pbft.

        unfold log_checkpoint_cert_from_new_view in *; smash_pbft; simpl in *;[| | |].

        + rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
          eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft.
          subst.

          apply pre_prepare_in_log_log_pre_prepares_implies in prep0; repndors; repnd.

          * assert (check_between_water_marks (low_water_mark p0) (pre_prepare2seq p) = true) as bwm by (smash_pbft_ind ind).

            unfold check_between_water_marks in *; smash_pbft.
            allrw SeqNumLe_true; simpl in *.
            dands; auto; simpl in *; try omega.

          * unfold check_between_water_marks in *; smash_pbft.
            allrw SeqNumLe_true; simpl in *.
            dands; auto; simpl in *; try omega.

            rename_hyp_with check_broadcast_new_view bcast.
            eapply in_check_broadcast_new_view_implies_between_water_marks in bcast;
              [|eauto|eauto].
            unfold check_between_water_marks in *; smash_pbft.

        + rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
          apply extract_seq_and_digest_from_checkpoint_certificate_none_implies in ext.
          rewrite ext in *; simpl in *; ginv.

        + rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
          eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft.
          subst.

          apply pre_prepare_in_log_log_pre_prepares_implies in prep0; repndors; repnd.

          * assert (check_between_water_marks (low_water_mark p0) (pre_prepare2seq p) = true) as bwm by (smash_pbft_ind ind).

            unfold check_between_water_marks in *; smash_pbft.
            allrw SeqNumLe_true; simpl in *.
            dands; auto; simpl in *; try omega.

          * unfold check_between_water_marks in *; smash_pbft.
            allrw SeqNumLe_true; simpl in *.
            dands; auto; simpl in *; try omega.

            rename_hyp_with check_broadcast_new_view bcast.
            eapply in_check_broadcast_new_view_implies_between_water_marks in bcast;
              [|eauto|eauto].
            unfold check_between_water_marks in *; smash_pbft.

        + rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
          apply extract_seq_and_digest_from_checkpoint_certificate_none_implies in ext.
          rewrite ext in *; simpl in *; ginv.

          assert (correct_view_change (new_view2view x2) x8 = true) as cvc by eauto 3 with pbft;[].
          unfold correct_view_change, correct_view_change_cert in cvc; smash_pbft.
          rewrite ext in *.
          simpl in *; ginv; try omega.

      - apply pre_prepare_in_log_log_pre_prepares_implies in prep; repndors; repnd;
          [smash_pbft_ind ind|];[].

        rename_hyp_with check_broadcast_new_view bcast.
        eapply in_check_broadcast_new_view_implies_between_water_marks in bcast;
          [|eauto|eauto].
        unfold check_between_water_marks in *; smash_pbft.
        dands; simpl in *; try omega.

      - apply pre_prepare_in_log_log_pre_prepares_implies in prep; repndors; repnd;
          [smash_pbft_ind ind|];[].

        rename_hyp_with check_broadcast_new_view bcast.
        applydup check_broadcast_new_view_generates in bcast as cor.
        apply correct_new_view_implies_view_change_cert2max_seq_vc_some in cor.
        exrepnd.
        rewrite cor0 in *; ginv.
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with pre_prepare_in_log prep.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_low_water_mark in add.
      simpl in *; autorewrite with pbft in *.

      eapply update_state_new_view_preserves_pre_prepare_in_log2 in prep;[| | |eauto];
        simpl in *; auto;[].
      repnd.
      autorewrite with pbft in *.
      exrepnd.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log in prep2;[|eauto];[].

      simpl in *.
      autorewrite with pbft in *.
      destruct prep2 as [prep2|prep2].

      - assert (check_between_water_marks (low_water_mark p0) (pre_prepare2seq p) = true)
          as bwm by (smash_pbft_ind ind).
        rewrite add1 in bwm.

        repndors;[|exrepnd; allrw <- ; auto];[].

        repnd.
        subst.
        unfold check_between_water_marks in *; smash_pbft.
        simpl in *; try omega.

      - exrepnd; subst; simpl in *; autorewrite with pbft in *.
        rewrite add1 in prep6.

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

  Lemma pre_prepares_get_garbage_collected_direct_pred0_v2 :
    forall i (eo : EventOrdering) (e : Event) s1 s2 p d,
      state_sm_before_event (PBFTreplicaSM i) e = Some s1
      -> state_sm_on_event (PBFTreplicaSM i) e = Some s2
      -> pre_prepare_in_log p d (log s1) = true
      -> pre_prepare_in_log p d (log s2) = false
      -> pre_prepare2seq p <= low_water_mark s2.
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

    (* 8 subgoals *)

    {
      (* request *)

      apply pre_prepare_in_log_add_new_pre_prepare2log_false_implies in prep2.
      smash_pbft_ind ind.
    }

    {
      (* pre-prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_pre_prepare_and_prepare2log add.

      eapply check_send_replies_preserves_pre_prepare_in_log_false in prep2;[|eauto].
      simpl in *.

      eapply add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log_false in prep2;[|eauto].
      pbft_simplifier.
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_prepare2log add.

      eapply check_send_replies_preserves_pre_prepare_in_log_false in prep2;[|eauto].
      simpl in *.

      eapply add_new_prepare2log_preserves_pre_prepare_in_log_false in prep2;[|eauto].
      pbft_simplifier.
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_commit2log add.

      eapply check_send_replies_preserves_pre_prepare_in_log_false in prep2;[|eauto].
      simpl in *.

      eapply add_new_commit2log_preserves_pre_prepare_in_log_false in prep2;[|eauto].
      pbft_simplifier.
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.
      applydup find_and_execute_requests_preserves_low_water_mark in fexec.
      rewrite <- fexec0.

      dup fexec as fexec'.
      eapply find_and_execute_requests_preserves_pre_prepare_in_log_forward in fexec';
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

      unfold update_state_new_view in upd; smash_pbft;[| |];
        try (complete (apply pre_prepare_in_log_log_pre_prepares_false in prep2; pbft_simplifier));[].

      rename_hyp_with view_change_cert2max_seq_vc mseq.
      rename_hyp_with log_checkpoint_cert_from_new_view cert.
      applydup sn_of_view_change_cert2max_seq_vc in mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      subst.

      apply clear_log_checkpoint_preserves_pre_prepare_in_log_false in prep2.
      repndors;[|].

      {
        eapply log_checkpoint_cert_from_new_view_preserves_pre_prepare_in_log_false_backward in cert; eauto.
        simpl in *; autorewrite with pbft in *; pbft_simplifier.
        apply pre_prepare_in_log_log_pre_prepares_false in cert.
        pbft_simplifier.
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

      destruct (le_dec (pre_prepare2seq p) (low_water_mark s2)) as [d1|d1]; auto;[].
      assert False; tcsp.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_forward in add;
        simpl;[|eauto].

      eapply update_state_new_view_preserves_pre_prepare_in_log_true_forward in upd;
        simpl;[| | |eauto]; auto; try omega.
      pbft_simplifier.
    }
  Qed.

  Lemma pre_prepares_get_garbage_collected_direct_pred_v2 :
    forall i (eo : EventOrdering) (e1 e2 : Event) state1 state2 pp d,
      e1 ⊂ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> pre_prepare_in_log pp d (log state1) = true
      -> pre_prepare_in_log pp d (log state2) = false
      -> pre_prepare2seq pp <= low_water_mark state2.
  Proof.
    introv lees eqst1 eqst2 prep1 prep2.
    eapply state_sm_before_event_if_on_event_direct_pred in eqst1;[|eauto].
    clear dependent e1.
    eapply pre_prepares_get_garbage_collected_direct_pred0_v2; eauto.
  Qed.

  Lemma pre_prepares_get_garbage_collected_v2 :
    forall i (eo : EventOrdering) (e1 e2 : Event) state1 state2 pp d,
      e1 ⊏ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> pre_prepare_in_log pp d (log state1) = true
      -> pre_prepare_in_log pp d (log state2) = false
      -> pre_prepare2seq pp <= low_water_mark state2.
  Proof.
    intros i eo e1 e2.
    induction e2 as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv ltes eqst1 eqst2 prep1 prep2.

    pose proof (local_implies_pred_or_local e1 e2) as q; autodimp q hyp.
    repndors.

    - eapply pre_prepares_get_garbage_collected_direct_pred_v2; eauto.

    - exrepnd.

      pose proof (state_sm_on_event_some_between e e2 (PBFTreplicaSM i) state2) as h.
      repeat (autodimp h hyp); eauto 3 with eo;[].
      exrepnd.

      remember (pre_prepare_in_log pp d (log s')) as b.
      symmetry in Heqb; destruct b.

      + eapply (pre_prepares_get_garbage_collected_direct_pred_v2 i _ e e2) in q1; eauto.

      + pose proof (PBFTlow_water_mark_increases_on_event _ e1 e i state1 s') as lelwm1.
        repeat (autodimp lelwm1 hyp); eauto 2 with eo.

        pose proof (PBFTlow_water_mark_increases_on_event _ e e2 i s' state2) as lelwm2.
        repeat (autodimp lelwm2 hyp); eauto 3 with eo.

        apply pred_implies_local_pred in q1; subst.
        autodimp ind hyp; eauto 2 with eo.
        pose proof (ind state1 s' pp d) as q; repeat (autodimp q hyp).
        clear ind.
        omega.
  Qed.

  Lemma non_garbage_collected_pre_prepares_direct_pred :
    forall i (eo : EventOrdering) (e1 e2 : Event) state1 state2 p1 p2 d1 d2,
      e1 ⊂ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> pre_prepare_in_log p1 d1 (log state1) = true
      -> pre_prepare_in_log p2 d2 (log state2) = true
      -> pre_prepare2seq p1 = pre_prepare2seq p2
      -> pre_prepare_in_log p1 d1 (log state2) = true.
  Proof.
    introv lees eqst1 eqst2 prep1 prep2 eqseqs.

    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.

    assert False; tcsp.

    pose proof (pre_prepares_get_garbage_collected_direct_pred_v2
                  i eo e1 e2 state1 state2 p1 d1) as q.
    repeat (autodimp q hyp).
    rewrite eqseqs in q.

    eapply pre_prepares_are_between_water_marks_if_in_log in prep2;[|eauto].
    unfold check_between_water_marks in *; smash_pbft; try omega.
  Qed.

  Lemma non_garbage_collected_pre_prepares :
    forall i (eo : EventOrdering) (e1 e2 : Event) state1 state2 p1 p2 d1 d2,
      e1 ⊏ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> pre_prepare_in_log p1 d1 (log state1) = true
      -> pre_prepare_in_log p2 d2 (log state2) = true
      -> pre_prepare2seq p1 = pre_prepare2seq p2
      -> pre_prepare_in_log p1 d1 (log state2) = true.
  Proof.
    introv lees eqst1 eqst2 prep1 prep2 eqseqs.

    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.

    assert False; tcsp.

    pose proof (pre_prepares_get_garbage_collected_v2 i eo e1 e2 state1 state2 p1 d1) as q.
    repeat (autodimp q hyp).
    rewrite eqseqs in q.

    eapply pre_prepares_are_between_water_marks_if_in_log in prep2;[|eauto].
    unfold check_between_water_marks in *; smash_pbft; try omega.
  Qed.

End PBFTgarbage_collect_pre_prepare.
