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


Require Export PBFTwell_formed_log.
Require Export PBFTordering.
Require Export PBFTprops3.
Require Export PBFTwf.
Require Export PBFTgarbage_collect.
Require Export PBFTpreserves_has_new_view.
Require Export PBFT_A_1_2_7.



Section PBFT_A_1_2_1.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma own_prepare_is_already_logged_with_different_digest_clear_log_checkpoint_false_implies :
    forall (n s : SeqNum) i v d L,
      n < s
      -> own_prepare_is_already_logged_with_different_digest i s v d (clear_log_checkpoint L n) = None
      -> own_prepare_is_already_logged_with_different_digest i s v d L = None.
  Proof.
    induction L; introv h own; simpl in *; smash_pbft.
    repeat (autodimp IHL hyp).
    allrw SeqNumLe_true.
    dands; auto.
    unfold own_prepare_is_already_in_entry_with_different_digest in *; smash_pbft.
    destruct a, log_entry_request_data; simpl in *; ginv; omega.
  Qed.
  Hint Resolve own_prepare_is_already_logged_with_different_digest_clear_log_checkpoint_false_implies : pbft.

  Lemma update_state_new_view_preserves_own_prepare_is_already_logged_with_different_digest_false_forward :
    forall i (s : SeqNum) v d s1 nv s2 msgs,
      correct_new_view nv = true
      -> update_state_new_view i s1 nv = (s2, msgs)
      -> low_water_mark s2 < s
      -> own_prepare_is_already_logged_with_different_digest i s v d (log s2) = None
      -> own_prepare_is_already_logged_with_different_digest i s v d (log s1) = None.
  Proof.
    introv cor upd h prep.

    unfold update_state_new_view in upd; smash_pbft.
    unfold log_checkpoint_cert_from_new_view in *; smash_pbft.

    - unfold update_log_checkpoint_stable, low_water_mark in *; simpl in *.
      apply own_prepare_is_already_logged_with_different_digest_clear_log_checkpoint_false_implies in prep; eauto 3 with pbft;[].

      rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      apply sn_of_view_change_cert2max_seq_vc in mseq; subst.

      rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft;[].
      subst; auto.

    - rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      apply sn_of_view_change_cert2max_seq_vc in mseq; subst.

      rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      apply extract_seq_and_digest_from_checkpoint_certificate_none_implies in ext.
      rewrite ext in *.
      simpl in *; ginv.

    - unfold update_log_checkpoint_stable, low_water_mark in *; simpl in *.
      apply own_prepare_is_already_logged_with_different_digest_clear_log_checkpoint_false_implies in prep; eauto 3 with pbft;[].

      rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      apply sn_of_view_change_cert2max_seq_vc in mseq; subst.

      rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft;[].
      subst; auto.

    - rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      apply sn_of_view_change_cert2max_seq_vc in mseq; subst.

      rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      apply extract_seq_and_digest_from_checkpoint_certificate_none_implies in ext.
      rewrite ext in *.
      simpl in *; ginv.

      apply correct_new_view_implies_correct_view_change in mseq0; auto.
      unfold correct_view_change, correct_view_change_cert in *; smash_pbft.
      rewrite ext in *; simpl in *; omega.
  Qed.
  Hint Resolve update_state_new_view_preserves_own_prepare_is_already_logged_with_different_digest_false_forward : pbft.


  (* Invariant A.1.2 (1) in PBFT PhD p.145 *)
  Lemma PBFT_A_1_2_1 :
    forall (eo      : EventOrdering)
           (e       : Event)
           (i       : Rep)
           (n       : SeqNum)
           (v       : View)
           (a1 a2   : Tokens)
           (d1 d2   : PBFTdigest)
           (state   : PBFTstate),
      state_sm_on_event (PBFTreplicaSM i) e = Some state
      -> prepare_in_log (mk_prepare v n d1 i a1) (log state) = true
      -> prepare_in_log (mk_prepare v n d2 i a2) (log state) = true
      -> d1 = d2.
  Proof.
    intros eo e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv eqst prep1 prep2.

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

    { (* pre-prepare *)

      match goal with
      | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
        dup H as check1; dup H as check2
      end.

      eapply check_send_replies_preserves_prepare_in_log in check1;[|exact prep1].
      eapply check_send_replies_preserves_prepare_in_log in check2;[|exact prep2].
      simpl in *.

      match goal with
      | [ H : add_new_pre_prepare_and_prepare2log _ _ _ _ _ _ = _ |- _ ] =>
        dup H as add1; dup H as add2
      end.

      eapply add_new_pre_prepare_and_prepare2log_preserves_prepare_in_log in add1;[| |exact check1];
        autorewrite with pbft in *; auto;[].
      eapply add_new_pre_prepare_and_prepare2log_preserves_prepare_in_log in add2;[| |exact check2];
        autorewrite with pbft in *; auto;[].

      repndors; repnd; try (smash_pbft_ind ind).

      - match goal with
        | [ H : own_prepare_is_already_logged_with_different_digest _ _ _ _ _ = _ |- _ ] =>
          eapply own_prepare_is_already_logged_with_different_digest_false_and_prepare_in_log_implies_same_digest in H;
            [|destruct p0, b; simpl in *;
              unfold pre_prepare2prepare, mk_prepare in *; ginv]
        end.

        match goal with
        | [ H : mk_prepare _ _ _ _ _ = _ |- _ ] =>
          applydup mk_prepare_eq_pre_prepare2prepare_implies_eq in H
        end.
        repnd; subst; auto.

      - match goal with
        | [ H : own_prepare_is_already_logged_with_different_digest _ _ _ _ _ = _ |- _ ] =>
          eapply own_prepare_is_already_logged_with_different_digest_false_and_prepare_in_log_implies_same_digest in H;
            [|destruct p0, b; simpl in *;
              unfold pre_prepare2prepare, mk_prepare in *; ginv]
        end.

        match goal with
        | [ H : mk_prepare _ _ _ _ _ = _ |- _ ] =>
          applydup mk_prepare_eq_pre_prepare2prepare_implies_eq in H
        end.
        repnd; subst; auto.

      - repeat
          match goal with
          | [ H : mk_prepare _ _ _ _ _ = _ |- _ ] =>
            apply mk_prepare_eq_pre_prepare2prepare_implies_eq in H
          end.
        repnd; subst; auto.
    }

    { (* prepare *)

      match goal with
      | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
        dup H as check1; dup H as check2
      end.

      eapply check_send_replies_preserves_prepare_in_log in check1;[|exact prep1].
      eapply check_send_replies_preserves_prepare_in_log in check2;[|exact prep2].
      simpl in *.

      match goal with
      | [ H : add_new_prepare2log _ _ _ _ = _ |- _ ] =>
        dup H as add1; dup H as add2
      end.

      eapply add_new_prepare2log_preserves_prepare_in_log in add1;[|exact check1];
        autorewrite with pbft in *; auto;[].
      eapply add_new_prepare2log_preserves_prepare_in_log in add2;[|exact check2];
        autorewrite with pbft in *; auto;[].

      repndors; repnd;
        try (complete (subst; simpl in *; tcsp));
        try (smash_pbft_ind ind).
    }

    { (* commit *)

      match goal with
      | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
        dup H as check1; dup H as check2
      end.

      eapply check_send_replies_preserves_prepare_in_log in check1;[|exact prep1].
      eapply check_send_replies_preserves_prepare_in_log in check2;[|exact prep2].
      simpl in *.

      match goal with
      | [ H : add_new_commit2log _ _ = _ |- _ ] =>
        dup H as add1; dup H as add2
      end.

      eapply add_new_commit2log_preserves_prepare_in_log in add1.
      rewrite check1 in add1; symmetry in add1.
      eapply add_new_commit2log_preserves_prepare_in_log in add2.
      rewrite check2 in add2; symmetry in add2.

      try (smash_pbft_ind ind).
    }

    {
      (* check-bcast-new-view*)

      rename_hyp_with update_state_new_view upd.

      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 4 with pbft;[].

      eapply update_state_new_view_preserves_prepare_in_log in prep1;[| |eauto];simpl in *;eauto 4 with pbft;[].
      eapply update_state_new_view_preserves_prepare_in_log in prep2;[| |eauto];simpl in *;eauto 4 with pbft;[].
      rewrite log_pre_prepares_preserves_prepare_in_log in prep1.
      rewrite log_pre_prepares_preserves_prepare_in_log in prep2.
      try (smash_pbft_ind ind).
    }

    { (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      eapply update_state_new_view_preserves_prepare_in_log2 in prep1;
        [| | |eauto];simpl;auto.
      eapply update_state_new_view_preserves_prepare_in_log2 in prep2;
        [| | |eauto];simpl;auto.
      simpl in *.
      autorewrite with pbft in *.
      exrepnd.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log in prep5;[|eauto];[].
      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log in prep3;[|eauto];[].

      hide_hyp prep4.
      hide_hyp prep0.
      simpl in *.
      autorewrite with pbft in *.

      repndors; exrepnd; autorewrite with pbft in *; try (smash_pbft_ind ind);[| |].

      - eapply PBFT_A_1_2_7_before in prep3;[|eauto];auto.
        exrepnd.
        eapply pre_prepare_in_log_implies_has_new_view_before in prep3;[|eauto];auto.
        simpl in *.
        apply pre_prepare_in_map_correct_new_view_implies2 in prep6;auto;[].
        simpl in *.
        rewrite prep6 in *.
        destruct pp, b; simpl in *.
        unfold mk_prepare, pre_prepare2prepare in *; ginv; simpl in *; pbft_simplifier.

      - eapply PBFT_A_1_2_7_before in prep5;[|eauto];auto.
        exrepnd.
        eapply pre_prepare_in_log_implies_has_new_view_before in prep5;[|eauto];auto.
        simpl in *.
        apply pre_prepare_in_map_correct_new_view_implies2 in prep6;auto;[].
        simpl in *.
        rewrite prep6 in *.
        destruct pp, b; simpl in *.
        unfold mk_prepare, pre_prepare2prepare in *; ginv; simpl in *; pbft_simplifier.

      - rename_hyp_with correct_new_view cor.
        applydup correct_new_view_implies_norepeatsb in cor as norep.

        match goal with
        | [ H1 : mk_prepare _ _ _ _ _ = _, H2 : mk_prepare _ _ _ _ _ = _ |- _ ] =>
          applydup mk_prepare_eq_pre_prepare2prepare_implies_eq_seq in H1 as eqsn1;
            applydup mk_prepare_eq_pre_prepare2prepare_implies_eq_seq in H2 as eqsn2;
            rewrite <- eqsn1 in eqsn2; clear eqsn1
        end.

        eapply norepeatsb_and_in_map_digest_same_seq_implies_eq in norep;
          [|exact prep6|exact prep9|]; auto;[].
        repnd; subst.

        repeat
          match goal with
          | [ H : mk_prepare _ _ _ _ _ = _ |- _ ] =>
            apply mk_prepare_eq_pre_prepare2prepare_implies_eq in H
          end.
        repnd; subst; auto.
    }
  Qed.
  Hint Resolve PBFT_A_1_2_1 : pbft.

  (* Uses if_prepare_in_log_digest_unique *)
  Lemma PBFT_A_1_2_1_direct_pred :
    forall (eo : EventOrdering)
           (e1 e2   : Event)
           (i       : Rep)
           (n       : SeqNum)
           (v       : View)
           (a1 a2   : Tokens)  (* these two should be different!!! *)
           (d1 d2   : PBFTdigest)
           (state1 state2 : PBFTstate),
      e1 ⊂ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> prepare_in_log (mk_prepare v n d1 i a1) (log state1) = true
      -> prepare_in_log (mk_prepare v n d2 i a2) (log state2) = true
      -> d1 = d2.
  Proof.
    introv ltev eqst1 eqst2 pl1 pl2.

    dup eqst2 as eqst2_At_e.
    hide_hyp eqst2_At_e.

    rewrite state_sm_on_event_unroll2 in eqst2.

    match goal with
    | [ H : context[map_option _ ?s] |- _ ] =>
      remember s as sop; symmetry in Heqsop; destruct sop; simpl in *;[|ginv];op_st_some m eqtrig
    end.

    rewrite state_sm_before_event_as_state_sm_on_event_pred in Heqsop; eauto 2 with eo.
    apply pred_implies_local_pred in ltev.
    subst.
    rewrite eqst1 in Heqsop; ginv.

    unfold PBFTreplica_update in eqst2.

    destruct m;
      simpl in *; ginv; subst; tcsp;
        try (smash_handlers); try (smash_pbft_ind ind); eauto 2 with pbft.

    (* 6 goals left *)

    { (* pre-prepare *)

      match goal with
      | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
        dup H as check;
          eapply check_send_replies_preserves_prepare_in_log in check;[|eauto];
            simpl in *
      end.

      match goal with
      | [ H : add_new_pre_prepare_and_prepare2log _ _ _ _ _ _ = _ |- _ ] =>
        dup H as add;
          eapply add_new_pre_prepare_and_prepare2log_preserves_prepare_in_log in add;
          [| |eauto]; autorewrite with pbft in *; auto
      end.

      repndors; repnd; auto; eauto 3 with pbft;[].

      match goal with
      | [ H : own_prepare_is_already_logged_with_different_digest _ _ _ _ _ = _ |- _ ] =>
        rename H into own;
          eapply own_prepare_is_already_logged_with_different_digest_false_and_prepare_in_log_implies_same_digest in own;
          [|destruct p0, b; simpl in *; unfold pre_prepare2prepare, mk_prepare in *; ginv]
      end.

      match goal with
      | [ H : mk_prepare _ _ _ _ _ = _ |- _ ] =>
        applydup mk_prepare_eq_pre_prepare2prepare_implies_eq in H
      end.
      repnd; subst; auto.
    }

    { (* prepare *)

      match goal with
      | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
        dup H as check;
          eapply check_send_replies_preserves_prepare_in_log in check;[|eauto];
            simpl in *
      end.

      match goal with
      | [ H : add_new_prepare2log _ _ _ _ = _ |- _ ] =>
        dup H as add;
          eapply add_new_prepare2log_preserves_prepare_in_log in add;[|exact check];
            autorewrite with pbft in *; auto;[]
      end.

      repndors; repnd; auto; subst; simpl in *; tcsp; eauto 3 with pbft.
    }

    { (* commit *)

      match goal with
      | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
        dup H as check;
          eapply check_send_replies_preserves_prepare_in_log in check;[|eauto];
            simpl in *
      end.

      match goal with
      | [ H : add_new_commit2log _ _ = _ |- _ ] =>
        dup H as add;
          eapply add_new_commit2log_preserves_prepare_in_log in add;
          rewrite check in add; symmetry in add
      end.

      eauto 3 with pbft.
    }

    {
      (* check-ready *)

      apply check_one_stable_preserves_prepare_in_log in pl2; smash_pbft.
    }

    {
      (* check-bcast-new-view*)

      rename_hyp_with update_state_new_view upd.

      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 4 with pbft;[].

      eapply update_state_new_view_preserves_prepare_in_log in pl2;[| |eauto];simpl in *;eauto 4 with pbft;[].
      rewrite log_pre_prepares_preserves_prepare_in_log in pl2.
      eauto 3 with pbft.
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      eapply update_state_new_view_preserves_prepare_in_log2 in pl2;
        [| | |eauto];simpl in *; auto;[].
      exrepnd.
      hide_hyp pl0.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log2
        in pl3;[|eauto];[].
      simpl in *; autorewrite with pbft in *.

      repndors; exrepnd; eauto 3 with pbft; try (smash_pbft_ind ind);[].

      eapply PBFT_A_1_2_7 in pl1;[|eauto];auto; autorewrite with eo; auto;[].
      exrepnd.
      eapply pre_prepare_in_log_implies_has_new_view in pl1;[|eauto];auto; autorewrite with eo; auto;[].
      simpl in *.
      apply pre_prepare_in_map_correct_new_view_implies2 in pl4;auto;[].
      simpl in *.
      rewrite pl4 in *.
      destruct pp, b; simpl in *.
      unfold mk_prepare, pre_prepare2prepare in *; ginv; simpl in *; pbft_simplifier.
    }
  Qed.
  Hint Resolve PBFT_A_1_2_1_direct_pred : pbft.

End PBFT_A_1_2_1.


Hint Resolve update_state_new_view_preserves_wf : pbft.
Hint Resolve own_prepare_is_already_logged_with_different_digest_clear_log_checkpoint_false_implies : pbft.
Hint Resolve update_state_new_view_preserves_own_prepare_is_already_logged_with_different_digest_false_forward : pbft.
Hint Resolve PBFT_A_1_2_1 : pbft.
Hint Resolve PBFT_A_1_2_1_direct_pred : pbft.
