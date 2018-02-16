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


Require Export PBFTprops4.
Require Export PBFTnew_view_in_log.
Require Export PBFTreceived_prepare_like.
(*Require Export PBFTnew_view_are_received2.*)


Section PBFT_new_views_are_received3.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Hint Rewrite low_water_mark_log_new_view_and_entry_state : pbft.
  Hint Rewrite low_water_mark_log_new_pre_prepare : pbft.
  Hint Rewrite low_water_mark_increment_sequence_number : pbft.
  Hint Rewrite low_water_mark_update_primary_state : pbft.


  Lemma add_new_pre_prepare2log_preserves_pre_prepare_in_log_true :
    forall pp d pp' d' L,
      pre_prepare_in_log pp d L = true
      -> pre_prepare_in_log pp d (add_new_pre_prepare2log pp' d' L) = true.
  Proof.
    introv prep.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    apply pre_prepare_in_log_add_new_pre_prepare2log_false_implies in Heqb; pbft_simplifier.
  Qed.
  Hint Resolve add_new_pre_prepare2log_preserves_pre_prepare_in_log_true : pbft.

  Lemma add_new_prepare2log_preserves_pre_prepare_in_log_forward :
    forall i L P Fc gi K pp d,
      add_new_prepare2log i L P Fc = (gi, K)
      -> pre_prepare_in_log pp d L = true
      -> pre_prepare_in_log pp d K = true.
  Proof.
    introv add prep.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    eapply add_new_prepare2log_preserves_pre_prepare_in_log_false in add;[|eauto].
    pbft_simplifier.
  Qed.
  Hint Resolve add_new_prepare2log_preserves_pre_prepare_in_log_forward : pbft.

  Lemma add_new_commit2log_preserves_pre_prepare_in_log_forward :
    forall L c gi K pp d,
      add_new_commit2log L c = (gi, K)
      -> pre_prepare_in_log pp d L = true
      -> pre_prepare_in_log pp d K = true.
  Proof.
    introv add prep.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    eapply add_new_commit2log_preserves_pre_prepare_in_log_false in add;[|eauto].
    pbft_simplifier.
  Qed.
  Hint Resolve add_new_commit2log_preserves_pre_prepare_in_log_forward : pbft.

  Hint Resolve clear_log_checkpoint_preserves_pre_prepare_in_log_true : pbft.

  Lemma check_stable_preserves_pre_prepare_in_log_forward :
    forall i st eop st' pp d,
      low_water_mark st' < pre_prepare2seq pp
      -> check_stable i st eop = Some st'
      -> pre_prepare_in_log pp d (log st) = true
      -> pre_prepare_in_log pp d (log st') = true.
  Proof.
    introv hseq check prep.
    unfold check_stable in *; smash_pbft.
    rename_hyp_with checkpoint_entry2stable stable.
    applydup checkpoint_entry2stable_implies_same_sn in stable.
    allrw; smash_pbft.
  Qed.
  Hint Resolve check_stable_preserves_pre_prepare_in_log_forward : pbft.

  Lemma check_stable_preserves_new_view_in_log_forward :
    forall i st eop st' nv,
      check_stable i st eop = Some st'
      -> new_view_in_log nv (view_change_state st)
      -> new_view_in_log nv (view_change_state st').
  Proof.
    introv check nvinlog.
    unfold check_stable in check; smash_pbft.
  Qed.
  Hint Resolve check_stable_preserves_new_view_in_log_forward : pbft.

  Lemma check_stable_preserves_low_water_mark :
    forall i st st' cpst1 cpst2 smst R c e,
      check_between_water_marks (low_water_mark st) (checkpoint2seq c) = true
      -> add_new_checkpoint2cp_state cpst1 smst R c = (Some e, cpst2)
      -> check_stable i (update_checkpoint_state st cpst2) e = Some st'
      -> low_water_mark st <= low_water_mark st'.
  Proof.
    introv bwm add check.
    unfold check_stable in check; smash_pbft.
    rename_hyp_with add_new_checkpoint2cp_state add.
    apply cp_sn_of_add_new_checkpoint2cp_state in add.
    rename_hyp_with checkpoint_entry2stable stable.
    applydup checkpoint_entry2stable_implies_same_sn in stable.
    rewrite <- stable0; clear stable0.
    allrw.
    allrw check_between_water_marks_true; omega.
  Qed.
  Hint Resolve check_stable_preserves_low_water_mark : pbft.

  Lemma update_state_new_view_preserves_pre_prepare_in_log_true_forward :
    forall i s1 v s2 msgs pp d,
      correct_new_view v = true
      -> update_state_new_view i s1 v = (s2, msgs)
      -> low_water_mark s2 < pre_prepare2seq pp
      -> pre_prepare_in_log pp d (log s1) = true
      -> pre_prepare_in_log pp d (log s2) = true.
  Proof.
    introv cor upd lseq prep.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; tcsp
    end.
    eapply update_state_new_view_preserves_pre_prepare_in_log_false_forward in upd; eauto.
  Qed.
  Hint Resolve update_state_new_view_preserves_pre_prepare_in_log_true_forward : pbft.

  Lemma update_state_new_view_preserves_low_water_mark :
    forall i st1 nv st2 msgs,
      correct_new_view nv = true
      -> update_state_new_view i st1 nv = (st2, msgs)
      -> low_water_mark st1 <= low_water_mark st2.
  Proof.
    introv cornv upd; unfold update_state_new_view in upd; smash_pbft.

    rename_hyp_with view_change_cert2max_seq_vc vc.
    applydup sn_of_view_change_cert2max_seq_vc in vc.
    applydup view_change_cert2_max_seq_vc_some_in in vc.
    subst.

    unfold log_checkpoint_cert_from_new_view in *; smash_pbft; simpl.

    - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate exct.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in exct;
        auto; eauto 3 with pbft;[].
      subst; simpl in *; try omega.

    - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate exct.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in exct;
        auto; eauto 3 with pbft;[].
      subst; simpl in *; try omega.
  Qed.

  Lemma check_broadcast_new_view_some_implies_has_new_view_false :
    forall i st e nv e' O N,
      wf_view_change_state (view_change_state st)
      -> In e (view_change_state st)
      -> check_broadcast_new_view i st e = Some (nv, e', O, N)
      -> has_new_view (view_change_state st) (vce_view e) = false.
  Proof.
    introv wf j check.
    unfold check_broadcast_new_view in check; smash_pbft.
    eapply view_changed_entry_some_implies_has_new_view_false; eauto.
  Qed.

  Lemma implies_pre_prepare_in_log_pre_prepares :
    forall pp d (m : SeqNum) P l,
      (forall pp' d',
          pre_prepare_in_log pp' d' l = true
          -> pre_prepare2seq pp' = pre_prepare2seq pp
          -> pre_prepare2view pp' <> pre_prepare2view pp)
      -> m < pre_prepare2seq pp
      -> In (pp, d) P
      -> no_repeats (map (fun p => pre_prepare2seq (fst p)) P)
      -> pre_prepare_in_log pp d (log_pre_prepares l m P) = true.
  Proof.
    induction P; introv imp lem i nrep; simpl in *; tcsp.
    repnd.
    inversion nrep as [|? ? ni norep]; subst; clear nrep.
    repndors; ginv; tcsp; smash_pbft; try omega;[|].

    - apply log_pre_prepares_preserves_pre_prepare_in_log_true.
      apply implies_same_pre_prepare_in_add_new_pre_prepare2log.
      introv prep xx.
      apply imp in prep; destruct pp, p', b, b0; simpl in *; ginv; auto.

    - eapply IHP; auto.
      introv prep eqseqs.

      apply pre_prepare_in_log_add_new_prepare2log in prep;
        repndors; repnd; subst.

      + apply imp in prep; tcsp.

      + destruct ni.
        apply in_map_iff.
        eexists; dands; eauto.
        simpl; auto.
  Qed.

  Lemma digest_for_pre_prepare_implies_equal_pre_prepare2digest :
    forall d pp,
      digest_for_pre_prepare d pp = true
      -> d = pre_prepare2digest pp.
  Proof.
    introv h.
    unfold digest_for_pre_prepare, same_digests in h; smash_pbft.
  Qed.

  Lemma correct_new_view_implies_no_repeats_no_repeats_seqs :
    forall nv,
      correct_new_view nv = true
      -> no_repeats (map pre_prepare2seq (new_view2oprep nv ++ new_view2nprep nv)).
  Proof.
    introv cor.
    unfold correct_new_view in *; smash_pbft.
    eapply norepeatsb_as_no_repeats; eauto.
  Qed.

  Lemma implies_pre_prepare_in_log_add_new_pre_prepare_and_prepare2log :
    forall i L Fp Fc giop K pp d,
      well_formed_log L
      -> (forall (pp' : Pre_prepare) (d' : PBFTdigest),
             pre_prepare_in_log pp' d' L = true
             -> pre_prepare2seq pp' = pre_prepare2seq pp
             -> pre_prepare2view pp' <> pre_prepare2view pp)
      -> add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> pre_prepare_in_log pp d K = true.
  Proof.
    induction L; introv wf imp add; repeat (simpl in *; tcsp; smash_pbft).

    - destruct pp, b; simpl in *; smash_pbft; allrw map_map; simpl in *;
        allrw map_id; autorewrite with pbft in *; tcsp.

    - destruct a, x, log_entry_pre_prepare_info; simpl in *; ginv; smash_pbft.
      destruct pp, b; simpl in *; smash_pbft; allrw map_map; simpl in *;
        allrw map_id; autorewrite with pbft in *; tcsp.

    - destruct a, x, log_entry_pre_prepare_info; simpl in *; ginv; smash_pbft.

    - destruct a, log_entry_pre_prepare_info; simpl in *; ginv;[|smash_pbft].
      destruct log_entry_request_data.
      pose proof (imp (mk_pre_prepare v s (map fst reqs) auth) d0) as q; clear imp.
      simpl in q.
      smash_pbft; autodimp q hyp; destruct pp, b; simpl in *;
        unfold eq_request_data in *; smash_pbft; ginv;
          autodimp q hyp; tcsp.

    - rename_hyp_with add_new_pre_prepare_and_prepare2log add.
      inversion wf as [|? ? diff wf1 wf2]; subst; clear wf.
      eapply IHL;[| |eauto]; auto;[].
      clear IHL add.
      introv w z x.

      applydup PBFTpre_prepare_in_log_preserves.entry_of_pre_prepare_in_log in w.
      exrepnd.
      applydup diff in w0; clear diff w0 wf1.

      destruct pp, b, pp', b; simpl in *; subst.

      destruct a, entry; simpl in *.
      subst; simpl in *.
      unfold entries_have_different_request_data in w2; simpl in *.
      unfold eq_request_data in *; smash_pbft.

      pose proof (imp (pre_prepare (bare_pre_prepare v s d1) a1) d') as q; clear imp.
      simpl in *; smash_pbft.
      repeat (autodimp q hyp).
  Qed.
  Hint Resolve implies_pre_prepare_in_log_add_new_pre_prepare_and_prepare2log : pbft.

  Lemma digest_for_pre_prepare_pre_prepare2digest :
    forall p, digest_for_pre_prepare (pre_prepare2digest p) p = true.
  Proof.
    introv; destruct p, b; simpl.
    unfold digest_for_pre_prepare; simpl.
    unfold same_digests; simpl; smash_pbft.
  Qed.
  Hint Rewrite digest_for_pre_prepare_pre_prepare2digest : pbft.
  Hint Resolve digest_for_pre_prepare_pre_prepare2digest : pbft.

  Lemma implies_pre_prepare_in_log_add_prepares_to_log_from_new_view_pre_prepares :
    forall pp i P s1 s2 msgs,
      well_formed_log (log s1)
      -> (forall (pp' : Pre_prepare) (d' : PBFTdigest),
             pre_prepare_in_log pp' d' (log s1) = true
             -> pre_prepare2seq pp' = pre_prepare2seq pp
             -> pre_prepare2view pp' <> pre_prepare2view pp)
      -> (forall pp d, In (pp,d) P -> i <> PBFTprimary (pre_prepare2view pp) /\ d = pre_prepare2digest pp)
      -> In (pp, pre_prepare2digest pp) P
      -> low_water_mark s1 < pre_prepare2seq pp
      -> no_repeats (map (fun p => pre_prepare2seq (fst p)) P)
      -> add_prepares_to_log_from_new_view_pre_prepares i s1 P = (s2,msgs)
      -> pre_prepare_in_log pp (pre_prepare2digest pp) (log s2) = true.
  Proof.
    induction P; introv wf imp nprim j lwm norep add; simpl in *; tcsp.
    repnd; simpl in *.

    inversion norep as [|? ? ni nrep]; subst; clear norep.

    pose proof (nprim a0 a) as w.
    autodimp w hyp; repnd; subst.
    assert (forall pp d,
               In (pp, d) P
               -> i <> PBFTprimary (pre_prepare2view pp)
                  /\ d = pre_prepare2digest pp)
      as nprim' by (introv xx; apply nprim; tcsp).
    clear nprim.

    repndors; ginv; smash_pbft; try omega;[|].

    - eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_forward;[eauto|].
      eapply check_send_replies_preserves_pre_prepare_in_log_forward;[eauto|]; simpl.

      eapply implies_pre_prepare_in_log_add_new_pre_prepare_and_prepare2log;
        [| |eauto]; auto.

    - rename_hyp_with check_send_replies check.
      applydup check_send_replies_update_log_preserves_low_water_mark in check.
      eapply IHP;[| | | | | |eauto]; auto; try congruence;[|].

      { eapply check_send_replies_preserves_wf;[eauto|];simpl.
        eapply add_new_pre_prepare_and_prepare2log_preserve_wf;
          [| | | |eauto|]; simpl; autorewrite with pbft; auto. }

      introv w z.
      eapply check_send_replies_preserves_pre_prepare_in_log in w;[|eauto];simpl in w.

      eapply add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log in w;[|eauto].
      repndors;[|].

      { eapply imp; eauto. }

      repnd; subst.
      intro x.
      rewrite z in *.
      destruct ni.
      apply in_map_iff.
      eexists; dands;[|eauto]; simpl; auto.
  Qed.


  Lemma new_views_are_received3 :
    forall (eo : EventOrdering)
           (e  : Event)
           (nv : NewView)
           (i  : Rep)
           (st : PBFTstate)
           (pp : Pre_prepare),
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> new_view_in_log nv (view_change_state st)
      -> low_water_mark st < pre_prepare2seq pp
      -> In pp (new_view2oprep nv)
      -> pre_prepare_in_log pp (pre_prepare2digest pp) (log st) = true.
  Proof.
    intros eo e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv eqst nvin wm ppinnv.

    dup eqst as eqst_At_e; hide_hyp eqst_At_e.
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

      eapply check_send_replies_preserves_pre_prepare_in_log_forward;[eauto|]; simpl.
      eapply PBFTgarbage_collect_misc1.add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log_forward;[eauto|].
      eapply check_send_replies_preserves_new_view_in_log in nvin;[|eauto]; simpl in *.
      erewrite <- check_send_replies_update_log_preserves_low_water_mark in wm;[|eauto].
      try (smash_pbft_ind ind).
    }

    {
      (* prepare *)

      eapply check_send_replies_preserves_pre_prepare_in_log_forward;[eauto|]; simpl.
      eapply add_new_prepare2log_preserves_pre_prepare_in_log_forward;[eauto|].
      eapply check_send_replies_preserves_new_view_in_log in nvin;[|eauto]; simpl in *.
      erewrite <- check_send_replies_update_log_preserves_low_water_mark in wm;[|eauto].
      try (smash_pbft_ind ind).
    }

    {
      (* commit *)

      eapply check_send_replies_preserves_pre_prepare_in_log_forward;[eauto|]; simpl.
      eapply add_new_commit2log_preserves_pre_prepare_in_log_forward;[eauto|].
      eapply check_send_replies_preserves_new_view_in_log in nvin;[|eauto]; simpl in *.
      erewrite <- check_send_replies_update_log_preserves_low_water_mark in wm;[|eauto].
      try (smash_pbft_ind ind).
    }

    {
      (* checkpoint *)

      rename_hyp_with add_new_checkpoint2cp_state add.
      applydup add_new_checkpoint2cp_state_preserves_sn_stable in add.
      assert (low_water_mark p < pre_prepare2seq pp) as lwm.
      { eapply Nat.le_lt_trans;[|eauto]; rewrite add0; auto. }
      try (smash_pbft_ind ind).
    }

    {
      (* check-ready *)

      eapply find_and_execute_requests_preserves_pre_prepare_in_log_forward;[eauto|].
      eapply find_and_execute_requests_preserves_new_view_in_log in nvin;[|eauto].
      erewrite <- find_and_execute_requests_preserves_low_water_mark in wm;[|eauto].
      try (smash_pbft_ind ind).
    }

    {
      (* check-stable *)

      assert (low_water_mark p < pre_prepare2seq pp) as lwm.
      { eapply Nat.le_lt_trans;[|eauto]; eauto 2 with pbft. }

      assert (pre_prepare_in_log pp (pre_prepare2digest pp) (log p) = true) as prep by try (smash_pbft_ind ind).
      eauto 3 with pbft.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with update_state_new_view upd.
      rename_hyp_with check_broadcast_new_view check.

      applydup CheckBCastNewView2entry_some_implies in cb.
      eapply update_state_new_view_preserves_new_view_in_log in nvin;[|eauto].
      simpl in *.

      eapply update_state_new_view_preserves_pre_prepare_in_log_true_forward;
        [|eauto| |]; simpl; auto;[eauto 3 with pbft|];[].

      applydup check_broadcast_new_view_implies_eq_views in check;[|eauto 3 with pbft];[].
      applydup update_state_new_view_preserves_low_water_mark in upd;[|eauto 3 with pbft];[].
      autorewrite with pbft in *.

      assert (low_water_mark p < pre_prepare2seq pp) as lppp by omega.

      eapply log_new_view_and_entry_preserves_new_view_in_log in nvin;
        [|apply check_broadcast_new_view_implies in check; exrepnd; congruence].
      repndors.

      - apply log_pre_prepares_preserves_pre_prepare_in_log_true.
        try (smash_pbft_ind ind).

      - subst x2.
        hide_hyp upd.
        applydup check_broadcast_new_view_some_implies_has_new_view_false in check as hnv;
          auto;[|eauto 3 with pbft];[].
        rewrite <- check0 in hnv.

        assert (forall pp d,
                   pre_prepare_in_log pp d (log p) = true
                   -> pre_prepare2view pp <> new_view2view nv) as imp1.
        {
          introv prep xx.
          dup prep as prep'.
          eapply pre_prepare_in_log_implies_has_new_view_before in prep;[|eauto];auto;[].
          rewrite  xx in prep; pbft_simplifier.
        }

        assert (forall pp d,
                   In (pp, d) (x4 ++ x3)
                   -> new_view2view nv = pre_prepare2view pp) as imp2.
        {
          introv; eapply check_broadcast_new_view_preserves_view; eauto.
        }

        applydup check_broadcast_new_view_implies_no_repeats_seqs in check.

        applydup check_broadcast_new_view_implies_equal_new_view2oprep in check as xx.
        rewrite xx in ppinnv; clear xx.
        apply in_map_iff in ppinnv; exrepnd; simpl in *; subst.
        assert (In (pp,x0) (x4 ++ x3)) as j by (apply in_app_iff; tcsp).

        eapply check_broadcast_new_view_implies_digest_and_auth in check;[|eauto]; repnd.
        apply digest_for_pre_prepare_implies_equal_pre_prepare2digest in check2; subst.
        apply implies_pre_prepare_in_log_pre_prepares; auto.
        introv prep eqseqs.
        applydup imp1 in prep.
        erewrite imp2 in prep0;[|apply in_app_iff;left; eauto]; auto.

      - apply check_broadcast_new_view_implies in check; exrepnd.
        subst; simpl in *; autorewrite with pbft in *; pbft_simplifier.
    }

    {
      (* new-view *)

      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with update_state_new_view upd.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state in add.
      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_low_water_mark in add.
      simpl in *; autorewrite with pbft in *.

      eapply update_state_new_view_preserves_new_view_in_log in nvin;[|eauto].
      simpl in *.
      applydup update_state_new_view_preserves_low_water_mark in upd;auto;[].
      autorewrite with pbft in *.

      eapply update_state_new_view_preserves_pre_prepare_in_log_true_forward;
        [|eauto| |]; simpl; auto.

      rewrite <- add1 in *.
      rewrite add0 in *.

      assert (low_water_mark p < pre_prepare2seq pp) as lppp by omega.

      apply log_new_view_preserves_new_view_in_log in nvin;repndors;[|].

      {
        eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_forward;[eauto|];[].
        simpl.
        try (smash_pbft_ind ind).
      }

      subst v.

      assert (forall pp d,
                 pre_prepare_in_log pp d (log p) = true
                 -> pre_prepare2view pp <> new_view2view nv) as imp1.
      {
        introv prep xx.
        dup prep as prep'.
        eapply pre_prepare_in_log_implies_has_new_view_before in prep;[|eauto];auto;[].
        rewrite  xx in prep; pbft_simplifier.
      }

      assert (forall pp,
                 In pp (new_view2oprep nv ++ new_view2nprep nv)
                 -> new_view2view nv = pre_prepare2view pp) as imp2.
      {
        introv xx; symmetry.
        eapply correct_new_view_implies_pre_prepare2view_eq_new_view2view; eauto.
      }

      rename_hyp_with correct_new_view cor.

      applydup correct_new_view_implies_no_repeats_no_repeats_seqs in cor.

      assert (In pp (new_view2oprep nv ++ new_view2nprep nv)) as j by (apply in_app_iff; tcsp).
      assert (In (pp,pre_prepare2digest pp) (map add_digest (new_view2oprep nv ++ new_view2nprep nv))) as k.
      { apply in_map_iff; eexists; dands; eauto; tcsp. }

      eapply implies_pre_prepare_in_log_add_prepares_to_log_from_new_view_pre_prepares;
        [| | | | | |eauto]; simpl; auto; allrw map_map; auto; eauto 2 with pbft;[|].

      { introv prep xx; applydup imp1 in prep.
        erewrite imp2 in prep0;[|apply in_app_iff;left; eauto]; auto. }

      { introv xx.
        apply in_map_iff in xx; exrepnd.
        unfold add_digest in xx1; ginv; dands; auto;[].
        apply imp2 in xx0; rewrite <- xx0.
        introv zz; subst.
        pose proof (correct_new_view_implies_from_primary nv) as q; autodimp q hyp. }
    }
Qed.

End PBFT_new_views_are_received3.


Hint Rewrite @low_water_mark_log_new_view_and_entry_state : pbft.
Hint Rewrite @low_water_mark_log_new_pre_prepare : pbft.
Hint Rewrite @low_water_mark_increment_sequence_number : pbft.
Hint Rewrite @low_water_mark_update_primary_state : pbft.
Hint Rewrite @digest_for_pre_prepare_pre_prepare2digest : pbft.


Hint Resolve add_new_pre_prepare2log_preserves_pre_prepare_in_log_true : pbft.
Hint Resolve add_new_prepare2log_preserves_pre_prepare_in_log_forward : pbft.
Hint Resolve add_new_commit2log_preserves_pre_prepare_in_log_forward : pbft.
Hint Resolve clear_log_checkpoint_preserves_pre_prepare_in_log_true : pbft.
Hint Resolve check_stable_preserves_pre_prepare_in_log_forward : pbft.
Hint Resolve check_stable_preserves_new_view_in_log_forward : pbft.
Hint Resolve check_stable_preserves_low_water_mark : pbft.
Hint Resolve update_state_new_view_preserves_pre_prepare_in_log_true_forward : pbft.
Hint Resolve implies_pre_prepare_in_log_add_new_pre_prepare_and_prepare2log : pbft.
Hint Resolve digest_for_pre_prepare_pre_prepare2digest : pbft.
