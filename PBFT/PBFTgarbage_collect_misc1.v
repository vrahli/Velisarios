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
Require Export PBFTprops5.
Require Export PBFTsomewhere_in_log.
Require Export PBFTwf.
Require Export PBFTin_log.
Require Export PBFTpre_prepare_in_log_preserves.


Section PBFTgarbage_collect_misc1.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Hint Rewrite andb_false_r : bool.

  Lemma prepare_in_entry_pre_prepare2entry :
    forall prep pp d,
      prepare_in_entry prep (pre_prepare2entry pp d) = false.
  Proof.
    introv; unfold prepare_in_entry; simpl.
    unfold is_prepare_for_entry; simpl.
    autorewrite with bool; auto.
  Qed.
  Hint Rewrite prepare_in_entry_pre_prepare2entry : pbft.

  Lemma prepare_in_entry_change_pre_prepare_info_of_entry :
    forall prep pp a,
      prepare_in_entry prep (change_pre_prepare_info_of_entry pp a)
      = prepare_in_entry prep a.
  Proof.
    introv; destruct a; simpl; tcsp.
  Qed.
  Hint Rewrite prepare_in_entry_change_pre_prepare_info_of_entry : pbft.

  Lemma prepare_somewhere_in_log_add_new_pre_prepare2log :
    forall prep pp d L,
      prepare_somewhere_in_log prep (add_new_pre_prepare2log pp d L)
      = prepare_somewhere_in_log prep L.
  Proof.
    induction L; simpl in *; smash_pbft.
  Qed.
  Hint Rewrite prepare_somewhere_in_log_add_new_pre_prepare2log : pbft.

  Lemma check_send_replies_preserves_prepare_somewhere_in_log :
    forall prep slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> prepare_somewhere_in_log prep (log state') = true
      -> prepare_somewhere_in_log prep (log state) = true.
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_prepare_somewhere_in_log : pbft.

  Lemma fill_out_pp_info_with_prepare_preserves_prepare_in_entry :
    forall i a pp Fp Fc x prep,
      fill_out_pp_info_with_prepare i a pp Fp Fc = Some x
      -> prepare_in_entry prep a = true
      -> prepare_in_entry prep (gi_entry x) = true.
  Proof.
    introv fill j.
    unfold prepare_in_entry in *; smash_pbft.
    allrw is_prepare_for_entry_true_iff.
    applydup fill_out_pp_info_with_prepare_preserves_request_data in fill.
    allrw.
    dands; eauto 2 with pbft.
  Qed.
  Hint Resolve fill_out_pp_info_with_prepare_preserves_prepare_in_entry : pbft.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_prepare_somewhere_in_log_forward :
    forall i L pp d Fp Fc giop K prep,
      add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> prepare_somewhere_in_log prep L = true
      -> prepare_somewhere_in_log prep K = true.
  Proof.
    induction L; introv h q; simpl in *; smash_pbft; repndors; tcsp.

    - left; eauto 2 with pbft.

    - right; eapply IHL; eauto.
  Qed.
  Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_prepare_somewhere_in_log_forward : pbft.

  Lemma prepare_in_entry_MkNewLogEntryWithPrepare :
    forall prep pp d rt,
      prepare_in_entry prep (MkNewLogEntryWithPrepare pp d rt)
      = (eq_request_data (pre_prepare2request_data pp d) (prepare2request_data prep))
          && same_rep_tok (prepare2rep_toks prep) rt.
  Proof.
    introv.
    unfold prepare_in_entry, is_prepare_for_entry, MkNewLogEntryWithPrepare; simpl.
    autorewrite with bool; auto.
  Qed.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_prepare_somewhere_in_log :
    forall i L pp d Fp Fc giop K prep,
      i = rt_rep (Fp tt)
      -> add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> prepare_somewhere_in_log prep K = true
      -> prepare_somewhere_in_log prep L = true
         \/
         (
           prep = request_data_and_rep_toks2prepare (pre_prepare2request_data pp d) (Fp tt)
           /\ prepare_somewhere_in_log prep L = false
         ).
  Proof.
    induction L; introv eqi h q; simpl in *; smash_pbft; repndors; tcsp.

    - simpl in *; smash_pbft; repndors; tcsp.
      allrw prepare_in_entry_MkNewLogEntryWithPrepare; smash_pbft.
      unfold eq_request_data in *; smash_pbft.
      allrw same_rep_tok_true_iff.
      rewrite e; rewrite <- q0.
      autorewrite with pbft; auto.

    - allrw similar_entry_and_pre_prepare_true_iff.
      unfold fill_out_pp_info_with_prepare in *.
      destruct a; simpl in *.
      destruct log_entry_pre_prepare_info; smash_pbft.
      unfold prepare_in_entry, is_prepare_for_entry in *; simpl in *; smash_pbft.
      unfold eq_request_data in *; smash_pbft.

      unfold add_prepare_if_not_enough in *; smash_pbft.
      repndors; tcsp;[].

      allrw same_rep_tok_true_iff.

      remember (prepare_somewhere_in_log prep L) as z; symmetry in Heqz; destruct z; tcsp.

      right; dands; tcsp.

      { rewrite e; rewrite <- q0; autorewrite with pbft; dands; auto. }

      {
        rewrite <- q0 in *; simpl in *.
        right.
        apply in_list_rep_toks_false_implies_existsb_same_rep_toks_false; auto.
      }

    - remember (prepare_in_entry prep a) as z; symmetry in Heqz; destruct z; tcsp.
      match goal with
      | [ H : context[add_new_pre_prepare_and_prepare2log] |- _ ] => rename H into add
      end.
      eapply IHL in add;[| |eauto]; auto.
      repndors; tcsp.
  Qed.

  Lemma own_prepare_is_already_logged_with_different_digest_false_and_prepare_somewhere_in_log_implies_same_digest :
    forall L i s v d d' a,
      own_prepare_is_already_logged_with_different_digest i s v d L = None
      -> prepare_somewhere_in_log (mk_prepare v s d' i a) L = true
      -> d = d'.
  Proof.
    induction L; introv h w; simpl in *; pbft_simplifier.
    smash_pbft.

    repndors; tcsp;[|eapply IHL; eauto];[].
    unfold prepare_in_entry in w; smash_pbft.

    allrw is_prepare_for_entry_true_iff; simpl in *.
    allrw existsb_exists; exrepnd.
    allrw same_rep_tok_true_iff; subst.

    rename_hyp_with own_prepare_is_already_in_entry_with_different_digest own.
    eapply own_prepare_is_already_in_entry_with_different_digest_false_and_same_request_data_implies_same_digest in own; eauto.
  Qed.

  Lemma add_new_prepare2log_preserves_prepare_somewhere_in_log :
    forall slf gi Fc prep new_prep L new_log,
      add_new_prepare2log slf L new_prep Fc = (gi, new_log)
      -> prepare_somewhere_in_log prep new_log = true
      -> prepare_somewhere_in_log prep L = true
         \/
         new_prep = prep.
  Proof.
    induction L; introv IH1 IH2; simpl in *; pbft_simplifier;
      simpl in *; smash_pbft; repndors; tcsp;
        unfold prepare_in_entry in *; smash_pbft;
          allrw is_prepare_for_entry_true_iff;
          allrw same_rep_tok_true_iff; simpl in *;
            repndors; tcsp.

    {
      pose proof (decomp_propose prep) as q1; rewrite <- q1; clear q1.
      pose proof (decomp_propose new_prep) as q2; rewrite <- q2; clear q2.
      allrw; simpl; tcsp.
    }

    {
      match goal with
      | [ H : add_prepare2entry _ _ _ _ = _ |- _ ] => rename H into add
      end.
      applydup gi_entry_of_add_prepare2entry_some in add.
      apply add_prepare2entry_some_implies_log_entry_prepares_gi_entry_or in add.
      smash_pbft; GC.

      - match goal with
        | [ H1 : ?x = _, H2 : existsb _ ?x = _ |- _ ] =>
          rewrite H1 in H2; simpl in H2; pbft_simplifier; repndors; auto;[]
        end.
        left; left; dands; tcsp.

      - match goal with
        | [ H1 : ?x = _, H2 : existsb _ ?x = _ |- _ ] =>
          rewrite H1 in H2; simpl in H2; pbft_simplifier; repndors; auto
        end.

        + allrw same_rep_tok_true_iff.
          right.
          pose proof (decomp_propose prep) as q1; rewrite <- q1; clear q1.
          pose proof (decomp_propose new_prep) as q2; rewrite <- q2; clear q2.
          f_equal; congruence.

        + left; left; dands; tcsp.

(*      - match goal with
        | [ H1 : ?x = _, H2 : existsb _ ?x = _ |- _ ] =>
          rewrite H1 in H2; simpl in H2; pbft_simplifier; repndors; auto;[]
        end.
        left; left; dands; tcsp.*)
    }

    {
      pose proof (IHL x1) as q; repeat (autodimp q hyp); tcsp.
    }
  Qed.

  Lemma add_new_commit2log_preserves_prepare_somewhere_in_log :
    forall p c L1 L2 i,
      add_new_commit2log L1 c = (i, L2)
      -> prepare_somewhere_in_log p L2 = prepare_somewhere_in_log p L1.
  Proof.
    induction L1; introv h; simpl in *; tcsp; smash_pbft; simpl; smash_pbft.

    - unfold prepare_in_entry; simpl; smash_pbft.

    - f_equal.
      match goal with
      | [ H : context[add_commit2entry] |- _ ] => rename H into add
      end.
      applydup add_commit2entry_preserves_log_entry_prepares in add.
      applydup gi_entry_of_add_commit2entry_some in add.
      unfold prepare_in_entry; allrw; f_equal.
      unfold is_prepare_for_entry.
      unfold eq_request_data; smash_pbft.

    - f_equal.
      eapply IHL1; eauto.
  Qed.

  Lemma check_between_water_marks_turns_false_stays_false :
    forall (lwm1 lwm2 lwm3 n : SeqNum),
      lwm1 <= lwm2
      -> lwm2 <= lwm3
      -> check_between_water_marks lwm1 n = true
      -> check_between_water_marks lwm2 n = false
      -> check_between_water_marks lwm3 n = false.
  Proof.
    introv h1 h2 check1 check2.
    unfold check_between_water_marks in *; smash_pbft.
    repndors; tcsp; allrw SeqNumLe_true; allrw SeqNumLe_false; simpl in *; try omega.
  Qed.

  Lemma low_water_mark_update_log :
    forall a b, low_water_mark (update_log a b) = low_water_mark a.
  Proof.
    introv; tcsp.
  Qed.
  Hint Rewrite low_water_mark_update_log : pbft.

  Lemma prepare2seq_pre_prepare2seq :
    forall i keys p d,
      prepare2seq (pre_prepare2prepare i keys p d)
      = pre_prepare2seq p.
  Proof.
    introv.
    destruct p, b; simpl; auto.
  Qed.
  Hint Rewrite prepare2seq_pre_prepare2seq : pbft.

  Lemma is_prepare_for_entry_implies_same_seq :
    forall e p,
      is_prepare_for_entry e p = true -> entry2seq e = prepare2seq p.
  Proof.
    introv h.
    allrw is_prepare_for_entry_true_iff.
    destruct e, p, b; simpl in *; subst; simpl in *; auto.
  Qed.

  Lemma clear_log_checkpoint_preserves_prepare_in_log2 :
    forall p L sn,
      well_formed_log L
      -> prepare_in_log p (clear_log_checkpoint L sn) = true
      -> prepare_in_log p L = true
         /\ sn < prepare2seq p.
  Proof.
    induction L; simpl in *; introv wf h; tcsp; smash_pbft.

    - assert False; tcsp.

      inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto; repnd.

      match goal with
      | [ H : is_prepare_for_entry _ _ = true |- _ ] =>
        apply is_prepare_for_entry_true_implies in H
      end.

      match goal with
      | [ H : prepare_in_log _ _ = _ |- _ ] => apply entry_of_prepare_in_log in H
      end.
      exrepnd.
      pose proof (imp entry) as q; autodimp q hyp; apply q; auto.
      allrw; auto.

    - inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.

    - inversion wf as [|? ? imp wfL]; subst; clear wf.
      dands; auto.
      rename_hyp_with is_prepare_for_entry isprep.
      apply is_prepare_for_entry_implies_same_seq in isprep.
      rewrite <- isprep.
      allrw SeqNumLe_false; auto.

    - inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.
  Qed.

  Hint Resolve clear_log_checkpoint_preserves_prepare_in_log : pbft.

  Lemma update_state_new_view_preserves_prepare_in_log_backward :
    forall i st nv st' msgs p,
      well_formed_log (log st)
      -> update_state_new_view i st nv = (st', msgs)
      -> prepare_in_log p (log st') = true
      -> prepare_in_log p (log st) = true.
  Proof.
    introv wf upd prep.
    unfold update_state_new_view in upd; smash_pbft.
    unfold log_checkpoint_cert_from_new_view in *; smash_pbft.
  Qed.

  Lemma check_stable_implies_low_water_mark :
    forall i s1 e s2,
      check_stable i s1 e = Some s2
      -> low_water_mark s2 = cp_sn e.
  Proof.
    introv check; unfold check_stable in check; smash_pbft.
  Qed.

  Lemma check_stable_preserves_prepare_in_log2 :
    forall slf state entry state' p,
      well_formed_log (log state)
      -> check_stable slf state entry = Some state'
      -> prepare_in_log p (log state') = true
      -> prepare_in_log p (log state) = true
         /\ cp_sn entry < prepare2seq p.
  Proof.
    introv wf h q.
    unfold check_stable in h; smash_pbft.
    apply clear_log_checkpoint_preserves_prepare_in_log2 in q; repnd; auto.
  Qed.

  Lemma correct_new_view_implies_correct_view_change :
    forall nv vc,
      correct_new_view nv = true
      -> In vc (new_view2cert nv)
      -> correct_view_change (new_view2view nv) vc = true.
  Proof.
    introv cor i.
    apply correct_new_view_implies_correct_cert in cor.
    allrw forallb_forall; tcsp.
  Qed.
  Hint Resolve correct_new_view_implies_correct_view_change : pbft.

  Lemma opre_prepare_in_new_view_exists :
    forall pp d nv,
      correct_new_view nv = true
      -> In (pp,d) (map add_digest (new_view2oprep nv))
      ->
      exists p,
        In p (view_change_cert2prep (new_view2cert nv))
        /\ pre_prepare2seq pp = prepared_info2seq p.
  Proof.
    introv cor i.
    allrw in_map_iff.
    unfold add_digest in *.
    exrepnd; ginv.

    destruct nv, v; simpl in *.
    unfold correct_new_view in *; simpl in *; smash_pbft.
    rename_hyp_with correct_new_view_npre_prepare_op nall.
    rename_hyp_with correct_new_view_opre_prepare_op oall.
    allrw forallb_forall.
    discover.
    clear oall nall.

    unfold correct_new_view_opre_prepare_op in *; smash_pbft.
    unfold correct_new_view_opre_prepare in *; smash_pbft.
    allrw SeqNumLt_true.
    unfold oexists_last_prepared in *.
    rewrite existsb_exists in *; exrepnd; smash_pbft.
  Qed.

  Lemma npre_prepare_in_new_view_exists :
    forall pp d nv,
      correct_new_view nv = true
      -> In (pp,d) (map add_digest (new_view2nprep nv))
      -> pre_prepare2seq pp < pre_prepares2max_seq (new_view2oprep nv).
  Proof.
    introv cor i.
    allrw in_map_iff.
    unfold add_digest in *.
    exrepnd; ginv.

    destruct nv, v; simpl in *.
    unfold correct_new_view in *; simpl in *; smash_pbft.
    rename_hyp_with correct_new_view_npre_prepare_op nall.
    rename_hyp_with correct_new_view_opre_prepare_op oall.
    allrw forallb_forall.
    discover.
    clear oall nall.

    unfold correct_new_view_npre_prepare_op in *; smash_pbft.
    unfold correct_new_view_npre_prepare in *; smash_pbft.
  Qed.

  Lemma pos_pre_prepares2max_seq_implies :
    forall OP,
      0 < pre_prepares2max_seq OP
      ->
      exists p,
        In p OP
        /\ pre_prepares2max_seq OP = pre_prepare2seq p.
  Proof.
    induction OP; introv h; simpl in *; try omega.
    unfold max_seq_num in *; smash_pbft.
    - autodimp IHOP hyp; exrepnd.
      eexists; dands; eauto.
    - exists a; dands; auto.
  Qed.

  Lemma pre_prepare_in_new_view_exists :
    forall pp d nv,
      correct_new_view nv = true
      -> In (pp,d) (map add_digest (new_view2oprep nv ++ new_view2nprep nv))
      ->
      exists p,
        In p (view_change_cert2prep (new_view2cert nv))
        /\ pre_prepare2seq pp <= prepared_info2seq p.
  Proof.
    introv cor i.
    allrw map_app.
    allrw in_app_iff.
    repndors.

    - apply opre_prepare_in_new_view_exists in i; auto.
      exrepnd; eexists; dands; eauto; allrw; omega.

    - apply npre_prepare_in_new_view_exists in i; auto.
      destruct nv, v; simpl in *.
      unfold correct_new_view in cor; simpl in *; smash_pbft.

      pose proof (pos_pre_prepares2max_seq_implies OP) as q; autodimp q hyp; try omega.
      exrepnd.
      rewrite q0 in *; clear q0.

      rename_hyp_with correct_new_view_npre_prepare_op nall.
      rename_hyp_with correct_new_view_opre_prepare_op oall.
      allrw forallb_forall.
      discover.
      clear oall nall.

      unfold correct_new_view_opre_prepare_op in *; smash_pbft.
      unfold correct_new_view_opre_prepare in *; smash_pbft.
      allrw SeqNumLt_true.
      unfold oexists_last_prepared in *.
      rewrite existsb_exists in *; exrepnd; smash_pbft.

      exists x0; dands; allrw <- ; auto; try omega.
  Qed.

  Lemma view_change_cert2max_seq_implies_le :
    forall C vc (n : SeqNum),
      view_change_cert2max_seq C = Some n
      -> In vc C
      -> view_change2seq vc <= n.
  Proof.
    introv h i; simpl in *.
    unfold view_change_cert2max_seq in *; smash_pbft.
    revert dependent n.
    revert dependent x2.
    induction C; introv h; simpl in *; smash_pbft.

    - repndors; subst; tcsp; try omega.
      autodimp IHC hyp.
      pose proof (IHC x2 n) as q; autodimp q hyp.

    - repndors; subst; tcsp.
      autodimp IHC hyp.
      pose proof (IHC x3 x1) as q; autodimp q hyp; try omega.

    - repndors; subst; tcsp.
      clear IHC.
      destruct C; simpl in *; smash_pbft.
  Qed.

  Lemma low_water_mark_log_new_view_and_entry_state :
    forall s nv e,
      low_water_mark (log_new_view_and_entry_state s nv e) = low_water_mark s.
  Proof.
    introv; destruct s; simpl; tcsp.
  Qed.
  Hint Rewrite low_water_mark_log_new_view_and_entry_state : pbft.

  Lemma log_checkpoint_cert_from_new_view_preserves_low_water_mark :
    forall i s1 v n view vc S s2 cop,
      low_water_mark s1 < view_change2seq vc
      -> correct_view_change view vc = true
      -> log_checkpoint_cert_from_new_view i s1 v n (view_change2cert vc) S = (s2, cop)
      -> low_water_mark s1 <= low_water_mark s2.
  Proof.
    introv h cor chk.
    unfold log_checkpoint_cert_from_new_view in chk; smash_pbft; simpl in *.

    - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext;[|eauto].
      rewrite ext in *; try omega.

    - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext;[|eauto].
      rewrite ext in *; try omega.
  Qed.

  Lemma extract_seq_and_digest_from_checkpoint_certificate_none_implies_correct_view_change_false :
    forall vc view,
      extract_seq_and_digest_from_checkpoint_certificate (view_change2cert vc) = None
      -> correct_view_change view vc = false.
  Proof.
    introv ext; unfold extract_seq_and_digest_from_checkpoint_certificate in ext.
    destruct vc, v; simpl in *.
    destruct C; simpl in *; ginv.
    unfold correct_view_change, correct_view_change_cert; simpl; smash_pbft.
    right; omega.
  Qed.

  Lemma log_checkpoint_cert_from_new_view_preserves_low_water_mark2 :
    forall i s1 v n view vc S s2 cop,
      low_water_mark s1 < view_change2seq vc
      -> correct_view_change view vc = true
      -> log_checkpoint_cert_from_new_view i s1 v n (view_change2cert vc) S = (s2, cop)
      -> low_water_mark s2 = view_change2seq vc.
  Proof.
    introv h cor chk.
    unfold log_checkpoint_cert_from_new_view in chk; smash_pbft; simpl in *; auto; try omega.

    - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext;[|eauto].
      rewrite ext in *; simpl in *; try omega; auto.

    - rewrite extract_seq_and_digest_from_checkpoint_certificate_none_implies_correct_view_change_false in cor; auto; ginv.

    - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext;[|eauto].
      rewrite ext in *; try omega; auto.

    - rewrite extract_seq_and_digest_from_checkpoint_certificate_none_implies_correct_view_change_false in cor; auto; ginv.
  Qed.

  Lemma view_change_cert2max_seq_vc_none_implies_correct_new_view_false :
    forall nv,
      view_change_cert2max_seq_vc (new_view2cert nv) = None
      -> correct_new_view nv = false.
  Proof.
    introv mseq.
    destruct nv, v; simpl in *.
    destruct V; simpl in *; ginv;[|smash_pbft];[].
    unfold correct_new_view; simpl; smash_pbft; try omega.
  Qed.
  Hint Resolve view_change_cert2max_seq_vc_none_implies_correct_new_view_false : pbft.

  Lemma update_state_new_view_preserves_prepare_in_log2 :
    forall p i s1 nv s2 msgs,
      correct_new_view nv = true
      -> well_formed_log (log s1)
      -> update_state_new_view i s1 nv = (s2, msgs)
      -> prepare_in_log p (log s2) = true
      -> exists n,
          view_change_cert2max_seq (new_view2cert nv) = Some n
          /\ prepare_in_log p (log s1) = true
          /\
          (
            (
              low_water_mark s1 < n
              /\ low_water_mark s2 < prepare2seq p
              /\ low_water_mark s2 = n
            )
            \/
            (
              n <= low_water_mark s1
              /\ low_water_mark s1 = low_water_mark s2
            )
          ).
  Proof.
    introv cor wf upd prep.
    unfold update_state_new_view in upd; smash_pbft.

    - rename_hyp_with log_checkpoint_cert_from_new_view chk.
      rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup sn_of_view_change_cert2max_seq_vc in mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      applydup correct_new_view_implies_correct_view_change in mseq1;auto.

      applydup log_checkpoint_cert_from_new_view_preserves_log in chk.
      subst; rewrite chk0.
      eapply clear_log_checkpoint_preserves_prepare_in_log2 in prep; eauto;
        try (complete (allrw <- ; auto)); repnd.

      unfold view_change_cert2max_seq; allrw.
      eexists; dands; eauto.

      dup chk as chk'.
      eapply log_checkpoint_cert_from_new_view_preserves_low_water_mark in chk';
        [| |eauto]; auto;[].
      dup chk as chk''.
      eapply log_checkpoint_cert_from_new_view_preserves_low_water_mark2 in chk'';
        [| |eauto]; auto;[].
      rewrite chk''.
      left; dands; try omega; auto.

    - unfold view_change_cert2max_seq; allrw.
      eexists; dands; eauto.

    - rewrite view_change_cert2max_seq_vc_none_implies_correct_new_view_false in cor; auto; ginv.
  Qed.

  Lemma low_water_mark_log_new_pre_prepare :
    forall s p d,
      low_water_mark (log_new_pre_prepare s p d) = low_water_mark s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite low_water_mark_log_new_pre_prepare : pbft.

  Lemma low_water_mark_increment_sequence_number :
    forall s, low_water_mark (increment_sequence_number s) = low_water_mark s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite low_water_mark_increment_sequence_number : pbft.

  Lemma low_water_mark_update_primary_state :
    forall s p,
      low_water_mark (update_primary_state s p) = low_water_mark s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite low_water_mark_update_primary_state : pbft.

  Lemma clear_log_checkpoint_preserves_pre_prepare_in_log2 :
    forall d p L sn,
      well_formed_log L
      -> pre_prepare_in_log p d (clear_log_checkpoint L sn) = true
      -> pre_prepare_in_log p d L = true /\ sn < pre_prepare2seq p.
  Proof.
    induction L; simpl in *; introv wf h; tcsp; smash_pbft.

    - assert False; tcsp.

      inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto; repnd.

      allrw similar_entry_and_pre_prepare_true_iff.

      match goal with
      | [ H : pre_prepare_in_log _ _ _ = _ |- _ ] => apply entry_of_pre_prepare_in_log in H
      end.
      exrepnd.
      pose proof (imp entry) as q; autodimp q hyp; apply q; auto.
      allrw; auto.

    - inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.

    - inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
      dands; auto.
      allrw similar_entry_and_pre_prepare_true_iff.
      destruct a, p, b; simpl in *; subst; auto.

    - inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.
  Qed.

  Lemma check_stable_preserves_pre_prepare_in_log2 :
    forall d slf state entry state' p,
      well_formed_log (log state)
      -> check_stable slf state entry = Some state'
      -> pre_prepare_in_log p d (log state') = true
      -> pre_prepare_in_log p d (log state) = true
         /\ cp_sn entry < pre_prepare2seq p.
  Proof.
    introv wf h q.
    unfold check_stable in h; smash_pbft;[].
    apply clear_log_checkpoint_preserves_pre_prepare_in_log2 in q; repnd; auto.
  Qed.

  Lemma in_from_min_to_max_of_view_changes_implies_between_water_marks :
    forall entry min n view,
      (forall vc, In vc (view_change_entry2view_changes entry) -> correct_view_change view vc = true)
      -> view_change_cert2max_seq (view_change_entry2view_changes entry) = Some min
      -> In n (from_min_to_max_of_view_changes entry)
      -> check_between_water_marks min n = true.
  Proof.
    introv cor h i.
    apply in_from_min_to_max_op_implies in i; exrepnd.
    rewrite h in *; ginv.

    unfold check_between_water_marks; smash_pbft; split; auto.

    unfold view_change_cert2max_seq_preps in *; smash_pbft.

    rename_hyp_with view_change_cert2max_seq_preps_vc mseq.
    apply view_change_cert2max_seq_preps_some_implies in mseq; exrepnd.
    subst.

    discover.
    clear cor.
    unfold correct_view_change in *; smash_pbft.
    unfold correct_view_change_preps in *.
    allrw forallb_forall.
    discover; smash_pbft.

    eapply view_change_cert2max_seq_implies_le in h;[|eauto].
    unfold check_between_water_marks in *; smash_pbft.
    simpl in *; try omega.
  Qed.
  Hint Resolve in_from_min_to_max_of_view_changes_implies_between_water_marks : pbft.

  Lemma in_check_broadcast_new_view_implies_between_water_marks :
    forall i state e nv e' opreps npreps pp d m vc,
      check_broadcast_new_view i state e = Some (nv, e', opreps, npreps)
      -> In (pp,d) (opreps ++ npreps)
      -> view_change_cert2max_seq_vc (new_view2cert nv) = Some (m, vc)
      -> check_between_water_marks m (pre_prepare2seq pp) = true.
  Proof.
    introv check j mseq.
    applydup check_broadcast_new_view_generates in check as cor.

    unfold check_broadcast_new_view in check; smash_pbft.
    unfold correct_new_view in cor; simpl in *; smash_pbft.

    allrw forallb_forall.

    eapply in_from_min_to_max_of_view_changes_implies_between_water_marks;
      [|unfold view_change_cert2max_seq;rewrite mseq;auto|]; auto.

    rename_hyp_with create_new_prepare_messages cr.
    allrw in_app_iff; repndors.

    - eapply o_pre_prepare_in_create_new_prepare_messages_implies in cr;[|eauto].
      exrepnd.
      apply create_new_prepare_message_implies_same_sequence_number in cr0; subst; auto.

    - eapply n_pre_prepare_in_create_new_prepare_messages_implies in cr;[|eauto].
      exrepnd.
      apply create_new_prepare_message_implies_same_sequence_number in cr0; subst; auto.
  Qed.

  Lemma correct_new_view_implies_view_change_cert2max_seq_vc_some :
    forall nv,
      correct_new_view nv = true
      -> exists x, view_change_cert2max_seq_vc (new_view2cert nv) = Some x.
  Proof.
    introv cor.
    unfold correct_new_view in cor; smash_pbft.

    destruct nv, v; simpl in *.
    destruct V; simpl in *; try omega.

    destruct (view_change_cert2max_seq_vc V); repnd; smash_pbft.
  Qed.

  Lemma correct_new_view_implies_between_water_marks :
    forall nv pp d m vc,
      correct_new_view nv = true
      -> In (pp,d) (map add_digest (new_view2oprep nv ++ new_view2nprep nv))
      -> view_change_cert2max_seq_vc (new_view2cert nv) = Some (m, vc)
      -> check_between_water_marks m (pre_prepare2seq pp) = true.
  Proof.
    introv cor i mseq.

    unfold correct_new_view in cor; simpl in *; smash_pbft.
    allrw forallb_forall.

    allrw map_app.
    allrw in_app_iff.
    allrw in_map_iff.
    unfold add_digest in i.

    repndors; exrepnd; ginv; discover.

    - unfold correct_new_view_opre_prepare_op in *.
      unfold view_change_cert2max_seq in *.
      rewrite mseq in *.

      rename_hyp_with correct_new_view_opre_prepare ocor.
      unfold correct_new_view_opre_prepare in ocor; smash_pbft.

      unfold check_between_water_marks; smash_pbft.
      split; simpl in *; try omega.

      unfold oexists_last_prepared in *.
      allrw existsb_exists; exrepnd.
      smash_pbft.
      allrw.

      apply in_view_change_cert2prep_implies in ocor1; exrepnd.
      discover.

      assert (correct_view_change (new_view2view nv) vc0 = true) as corvc by (eauto 3 with pbft).

      unfold correct_view_change in corvc; smash_pbft.
      unfold correct_view_change_preps in *.
      allrw forallb_forall.
      discover; smash_pbft.
      unfold check_between_water_marks in *; smash_pbft.

      eapply view_change_cert2max_seq_implies_le in ocor1;
        [|unfold view_change_cert2max_seq;allrw;reflexivity].
      simpl in *; try omega.

    - unfold correct_new_view_npre_prepare_op in *.
      unfold view_change_cert2max_seq in *.
      rewrite mseq in *.

      rename_hyp_with correct_new_view_npre_prepare ncor.
      unfold correct_new_view_npre_prepare in ncor; smash_pbft.

      unfold check_between_water_marks; smash_pbft.
      split; simpl in *; try omega.

      apply Nat.lt_le_incl.
      eapply Nat.lt_le_trans;[eauto|].

      unfold nexists_last_prepared in *.
      allrw @existsb_false.

      pose proof (pos_pre_prepares2max_seq_implies (new_view2oprep nv)) as pos.
      autodimp pos hyp; try omega;[].
      exrepnd.
      rewrite pos0 in *.
      clear pos0.

      discover.

      rename_hyp_with correct_new_view_npre_prepare ncor'.
      rename_hyp_with correct_new_view_opre_prepare ocor'.
      clear ncor'.
      unfold correct_new_view_opre_prepare in ocor'; smash_pbft.

      unfold oexists_last_prepared in *.
      allrw existsb_exists; exrepnd.
      smash_pbft.
      allrw.

      apply in_view_change_cert2prep_implies in ocor'1; exrepnd.
      discover.

      assert (correct_view_change (new_view2view nv) vc0 = true) as corvc by (eauto 3 with pbft).

      unfold correct_view_change in corvc; smash_pbft.
      unfold correct_view_change_preps in *.
      allrw forallb_forall.
      discover; smash_pbft.
      unfold check_between_water_marks in *; smash_pbft.

      eapply view_change_cert2max_seq_implies_le in ocor'1;
        [|unfold view_change_cert2max_seq;allrw;reflexivity].
      simpl in *; try omega.
  Qed.

  Lemma update_state_new_view_preserves_pre_prepare_in_log2 :
    forall pp d i s1 nv s2 msgs,
      correct_new_view nv = true
      -> well_formed_log (log s1)
      -> update_state_new_view i s1 nv = (s2, msgs)
      -> pre_prepare_in_log pp d (log s2) = true
      -> exists n,
          view_change_cert2max_seq (new_view2cert nv) = Some n
          /\ pre_prepare_in_log pp d (log s1) = true
          /\
          (
            (
              low_water_mark s1 < n
              /\ low_water_mark s2 < pre_prepare2seq pp
              /\ low_water_mark s2 = n
            )
            \/
            (
              n <= low_water_mark s1
              /\ low_water_mark s1 = low_water_mark s2
            )
          ).
  Proof.
    introv cor wf upd prep.
    unfold update_state_new_view in upd; smash_pbft.

    - rename_hyp_with log_checkpoint_cert_from_new_view chk.
      rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup sn_of_view_change_cert2max_seq_vc in mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      applydup correct_new_view_implies_correct_view_change in mseq1;auto.

      applydup log_checkpoint_cert_from_new_view_preserves_log in chk.
      subst; rewrite chk0.

      eapply clear_log_checkpoint_preserves_pre_prepare_in_log2 in prep; eauto;
        try (complete (allrw <- ; auto)); repnd.

      unfold view_change_cert2max_seq; allrw.
      eexists; dands; eauto.

      dup chk as chk'.
      eapply log_checkpoint_cert_from_new_view_preserves_low_water_mark in chk';
        [| |eauto]; auto;[].
      dup chk as chk''.
      eapply log_checkpoint_cert_from_new_view_preserves_low_water_mark2 in chk'';
        [| |eauto]; auto;[].
      rewrite chk''.
      left; dands; try omega; auto.

    - unfold view_change_cert2max_seq; allrw.
      eexists; dands; eauto.

    - rewrite view_change_cert2max_seq_vc_none_implies_correct_new_view_false in cor; auto; ginv.
  Qed.

  Lemma check_send_replies_preserves_prepare_somewhere_in_log_false :
    forall i v keys eop s1 n msgs s2 p,
      check_send_replies i v keys eop s1 n = (msgs, s2)
      -> prepare_somewhere_in_log p (log s2) = false
      -> prepare_somewhere_in_log p (log s1) = false.
  Proof.
    introv check prep.
    unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_prepare_somewhere_in_log_false :
    forall i L pp d Fp Fc giop K prep,
      add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> prepare_somewhere_in_log prep K = false
      -> prepare_somewhere_in_log prep L = false.
  Proof.
    introv add h.
    match goal with
    | [ |- ?x = _ ] => remember x as b; destruct b; auto; symmetry in Heqb
    end.
    eapply add_new_pre_prepare_and_prepare2log_preserves_prepare_somewhere_in_log_forward in add; eauto.
  Qed.

  Lemma add_prepare2entry_preserves_prepare_in_entry_false :
    forall i a P Fc x p,
      add_prepare2entry i a P Fc = Some x
      -> prepare_in_entry p (gi_entry x) = false
      -> prepare_in_entry p a = false.
  Proof.
    introv add prep.
    unfold add_prepare2entry in add; destruct a; smash_pbft.
    unfold prepare_in_entry, is_prepare_for_entry, eq_request_data in *; simpl in *.
    smash_pbft.
    match goal with
    | [ |- ?x = _ ] => remember x as b; destruct b; symmetry in Heqb; auto
    end.
    allrw existsb_exists.
    allrw @existsb_false.
    exrepnd.
    unfold add_prepare_if_not_enough in *; smash_pbft; ginv.
  Qed.
  Hint Resolve add_prepare2entry_preserves_prepare_in_entry_false : pbft.

  Lemma add_new_prepare2log_preserves_prepare_somewhere_in_log_false :
    forall i L P Fc gi K p,
      add_new_prepare2log i L P Fc = (gi, K)
      -> prepare_somewhere_in_log p K = false
      -> prepare_somewhere_in_log p L = false.
  Proof.
    induction L; introv add prep; simpl in *; smash_pbft.
  Qed.
  Hint Resolve add_new_prepare2log_preserves_prepare_somewhere_in_log_false : pbft.

  Lemma add_commit2entry_preserves_prepare_in_entry_false :
    forall a c x p,
      add_commit2entry a c = Some x
      -> prepare_in_entry p x = false
      -> prepare_in_entry p a = false.
  Proof.
    introv add prep.
    unfold add_commit2entry in add; destruct a; smash_pbft.
  Qed.
  Hint Resolve add_commit2entry_preserves_prepare_in_entry_false : pbft.

  Lemma add_new_commit2log_preserves_prepare_somewhere_in_log_false :
    forall L c gi K p,
      add_new_commit2log L c = (gi, K)
      -> prepare_somewhere_in_log p K = false
      -> prepare_somewhere_in_log p L = false.
  Proof.
    induction L; introv add prep; simpl in *; smash_pbft.
  Qed.
  Hint Resolve add_new_commit2log_preserves_prepare_somewhere_in_log_false : pbft.

  Lemma clear_log_checkpoint_preserves_prepare_somewhere_in_log_false :
    forall p L (n : SeqNum),
      prepare_somewhere_in_log p (clear_log_checkpoint L n) = false
      ->
      (
        prepare_somewhere_in_log p L = false
        \/
        prepare2seq p <= n
      ).
  Proof.
    induction L; introv prep; simpl in *; smash_pbft.

    - allrw SeqNumLe_true.
      apply IHL in prep; repndors; tcsp.
      remember (prepare_in_entry p a) as b; symmetry in Heqb; destruct b; tcsp.
      unfold prepare_in_entry in *; smash_pbft.
      unfold is_prepare_for_entry, eq_request_data in *; smash_pbft.
      destruct a, p, b; simpl in *; autorewrite with pbft in *; subst; simpl in *; tcsp.

    - allrw SeqNumLe_false.
      apply IHL in prep0; repndors; tcsp.
  Qed.

  Lemma prepare_in_log_implies_prepare_somewhere_in_log :
    forall p L,
      prepare_in_log p L = true
      -> prepare_somewhere_in_log p L = true.
  Proof.
    induction L; introv h; simpl in *; smash_pbft.
    left.
    unfold prepare_in_entry; smash_pbft.
  Qed.
  Hint Resolve prepare_in_log_implies_prepare_somewhere_in_log : pbft.

  Lemma prepare_somewhere_in_log_iff_prepare_in_log :
    forall p L,
      well_formed_log L
      -> prepare_somewhere_in_log p L = true
         <-> prepare_in_log p L = true.
  Proof.
    introv wf; split; introv h; smash_pbft.

    induction L; simpl in *; tcsp; smash_pbft; repndors;
      try (inversion wf as [|? ? imp wfe wfl]; subst; clear wf);
      try (complete (unfold prepare_in_entry in *; smash_pbft)).

    repeat (autodimp IHL hyp).
    applydup entry_of_prepare_in_log in IHL; exrepnd.
    applydup imp in IHL0.
    unfold entries_have_different_request_data in *.
    unfold is_prepare_for_entry in *.
    unfold eq_request_data in *; smash_pbft.
  Qed.

  Lemma prepare_somewhere_in_log_implies_prepare_in_log :
    forall p L,
      well_formed_log L
      -> prepare_somewhere_in_log p L = true
      -> prepare_in_log p L = true.
  Proof.
    introv wf prep; apply prepare_somewhere_in_log_iff_prepare_in_log in prep; auto.
  Qed.
  Hint Resolve prepare_somewhere_in_log_implies_prepare_in_log : pbft.

  Lemma implies_prepare_in_log_change_entry_add_replies2entry :
    forall p L n e reps,
      prepare_in_log p L = true
      -> find_entry L n = Some e
      -> prepare_in_log p (change_entry L (add_replies2entry e reps)) = true.
  Proof.
    induction L; introv prep find; simpl in *; smash_pbft.

    - unfold similar_entry, eq_request_data in *; smash_pbft.
      apply entry2seq_if_find_entry in find; subst.
      destruct a, e; simpl in *; subst; tcsp.

    - unfold similar_entry, eq_request_data in *; smash_pbft.
      unfold is_prepare_for_entry, eq_request_data in *; smash_pbft.

    - unfold similar_entry, eq_request_data in *; smash_pbft.
      unfold is_prepare_for_entry, eq_request_data in *; smash_pbft.
  Qed.
  Hint Resolve implies_prepare_in_log_change_entry_add_replies2entry : pbft.

  Lemma find_and_execute_requests_preserves_prepare_somewhere_in_log_forward :
    forall msg i prep s1 s2 v keys,
      well_formed_log (log s1)
      -> find_and_execute_requests i v keys s1 = (msg, s2)
      -> prepare_somewhere_in_log prep (log s1) = true
      -> prepare_somewhere_in_log prep (log s2) = true.
  Proof.
    introv wf find h.
    apply prepare_somewhere_in_log_iff_prepare_in_log in h; auto.
    apply prepare_somewhere_in_log_iff_prepare_in_log; eauto 3 with pbft;[].

    clear wf.

    unfold find_and_execute_requests in *; smash_pbft.

    unfold execute_requests in *.
    destruct (ready s1); simpl in *; smash_pbft.

    rename_hyp_with check_broadcast_checkpoint check.
    apply check_broadcast_checkpoint_preserves_log in check.
    simpl in *.
    rewrite <- check; eauto 3 with pbft.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_prepare_somewhere_in_log_forward : pbft.

  Lemma prepare_somewhere_in_log_log_pre_prepares :
    forall p P L lwm,
      prepare_somewhere_in_log p (log_pre_prepares L lwm P)
      = prepare_somewhere_in_log p L.
  Proof.
    induction P; introv; simpl in *; smash_pbft.
    rewrite IHP.
    autorewrite with pbft; auto.
  Qed.
  Hint Rewrite prepare_somewhere_in_log_log_pre_prepares : pbft.

  Lemma prepare_somewhere_in_log_false_iff_prepare_in_log_false :
    forall p L,
      well_formed_log L
      -> prepare_somewhere_in_log p L = false
         <-> prepare_in_log p L = false.
  Proof.
    introv wf; split; introv h; smash_pbft.

    {
      remember (prepare_in_log p L) as b; symmetry in Heqb; destruct b; auto.
      apply prepare_somewhere_in_log_iff_prepare_in_log in Heqb; auto.
      pbft_simplifier.
    }

    {
      remember (prepare_somewhere_in_log p L) as b; symmetry in Heqb; destruct b; auto.
      apply prepare_somewhere_in_log_iff_prepare_in_log in Heqb; auto.
      pbft_simplifier.
    }
  Qed.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_somewhere_in_log_false_backward :
    forall p i s1 pps s2 msgs,
      well_formed_log (log s1)
      -> well_formed_log (log s2)
      -> add_prepares_to_log_from_new_view_pre_prepares i s1 pps = (s2, msgs)
      -> prepare_somewhere_in_log p (log s2) = false
      -> prepare_somewhere_in_log p (log s1) = false.
  Proof.
    introv wf1 wf2 add prep.
    apply prepare_somewhere_in_log_false_iff_prepare_in_log_false in prep; auto.
    apply prepare_somewhere_in_log_false_iff_prepare_in_log_false; auto.
    eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log_backward in add;[|eauto]; auto.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_somewhere_in_log_false_backward : pbft.

  Lemma log_checkpoint_cert_from_new_view_preserves_prepare_somewhere_in_log_false_backward :
    forall i s1 v m C S s2 chkop p,
      log_checkpoint_cert_from_new_view i s1 v m C S = (s2, chkop)
      -> prepare_somewhere_in_log p (log s2) = false
      -> prepare_somewhere_in_log p (log s1) = false.
  Proof.
    introv chk prep.
    apply log_checkpoint_cert_from_new_view_preserves_log in chk.
    allrw; auto.
  Qed.

  Lemma update_state_new_view_preserves_prepare_somewhere_in_log2 :
    forall p i s1 nv s2 msgs,
      correct_new_view nv = true
      -> well_formed_log (log s1)
      -> update_state_new_view i s1 nv = (s2, msgs)
      -> prepare_somewhere_in_log p (log s2) = true
      -> exists n,
          view_change_cert2max_seq (new_view2cert nv) = Some n
          /\ prepare_somewhere_in_log p (log s1) = true
          /\
          (
            (
              low_water_mark s1 < n
              /\ low_water_mark s2 < prepare2seq p
              /\ low_water_mark s2 = n
            )
            \/
            (
              n <= low_water_mark s1
              /\ low_water_mark s1 = low_water_mark s2
            )
          ).
  Proof.
    introv cor wf upd prep.
    rewrite prepare_somewhere_in_log_iff_prepare_in_log in prep; eauto 2 with pbft.
    eapply update_state_new_view_preserves_prepare_in_log2 in prep;[| | |eauto];auto.
    exrepnd; exists n; dands; auto.
    rewrite prepare_somewhere_in_log_iff_prepare_in_log; auto.
  Qed.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_somewhere_in_log_true_forward :
    forall p i s1 pps s2 msgs,
      well_formed_log (log s1)
      -> well_formed_log (log s2)
      -> add_prepares_to_log_from_new_view_pre_prepares i s1 pps = (s2, msgs)
      -> prepare_somewhere_in_log p (log s1) = true
      -> prepare_somewhere_in_log p (log s2) = true.
  Proof.
    introv wf1 wf2 add prep.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_somewhere_in_log_false_backward in add;[| | |eauto]; auto.
    pbft_simplifier.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_somewhere_in_log_true_forward : pbft.

  Lemma implies_prepare_somewhere_in_log_clear_log_checkpoint :
    forall p L (n : SeqNum),
      n < prepare2seq p
      -> prepare_somewhere_in_log p L = true
      -> prepare_somewhere_in_log p (clear_log_checkpoint L n) = true.
  Proof.
    introv h prep.

    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    apply clear_log_checkpoint_preserves_prepare_somewhere_in_log_false in Heqb.
    repndors; tcsp; pbft_simplifier; try omega.
  Qed.
  Hint Resolve implies_prepare_somewhere_in_log_clear_log_checkpoint : pbft.

  Lemma update_state_new_view_preserves_prepare_somewhere_in_log_true_forward :
    forall i s1 nv s2 msgs p,
      correct_new_view nv = true
      -> update_state_new_view i s1 nv = (s2, msgs)
      -> low_water_mark s2 < prepare2seq p
      -> prepare_somewhere_in_log p (log s1) = true
      -> prepare_somewhere_in_log p (log s2) = true.
  Proof.
    introv cor upd h prep.
    unfold update_state_new_view in *; smash_pbft;[].

    rename_hyp_with view_change_cert2max_seq_vc mseq.
    rename_hyp_with log_checkpoint_cert_from_new_view check.

    applydup sn_of_view_change_cert2max_seq_vc in mseq.
    applydup view_change_cert2_max_seq_vc_some_in in mseq.
    subst.

    applydup PBFTprops2.correct_new_view_implies_correct_view_change in mseq1;auto;[].

    unfold log_checkpoint_cert_from_new_view in *; smash_pbft; simpl in *.

    - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext;[|eauto];subst.
      apply implies_prepare_somewhere_in_log_clear_log_checkpoint; auto.

    - rewrite extract_seq_and_digest_from_checkpoint_certificate_none_implies_correct_view_change_false in mseq0;auto.

    - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext;[|eauto];subst.
      apply implies_prepare_somewhere_in_log_clear_log_checkpoint; auto.

    - rewrite extract_seq_and_digest_from_checkpoint_certificate_none_implies_correct_view_change_false in mseq0;auto.
  Qed.
  Hint Resolve update_state_new_view_preserves_prepare_somewhere_in_log_true_forward : pbft.

  Lemma check_send_replies_preserves_pre_prepare_in_log_false :
    forall i v keys eop s1 n msgs s2 pp d,
      check_send_replies i v keys eop s1 n = (msgs, s2)
      -> pre_prepare_in_log pp d (log s2) = false
      -> pre_prepare_in_log pp d (log s1) = false.
  Proof.
    introv check prep.
    unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_pre_prepare_in_log_false : pbft.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log_forward :
    forall i L pp d Fp Fc giop K pp' d',
      add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> pre_prepare_in_log pp' d' L = true
      -> pre_prepare_in_log pp' d' K = true.
  Proof.
    induction L; introv h q; simpl in *; smash_pbft; repndors; tcsp;
      try (complete (destruct a, log_entry_pre_prepare_info; ginv));[].

    destruct a, log_entry_pre_prepare_info; ginv.
    unfold fill_out_pp_info_with_prepare in *; smash_pbft.
  Qed.
  Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log_forward : pbft.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log_false :
    forall i L pp d Fp Fc giop K pp' d',
      add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> pre_prepare_in_log pp' d' K = false
      -> pre_prepare_in_log pp' d' L = false.
  Proof.
    introv add h.
    match goal with
    | [ |- ?x = _ ] => remember x as b; destruct b; auto; symmetry in Heqb
    end.
    eapply add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log_forward in add; eauto.
  Qed.

  Lemma add_new_prepare2log_preserves_pre_prepare_in_log_false :
    forall i L P Fc gi K pp d,
      add_new_prepare2log i L P Fc = (gi, K)
      -> pre_prepare_in_log pp d K = false
      -> pre_prepare_in_log pp d L = false.
  Proof.
    induction L; introv add prep; simpl in *; smash_pbft; repndors; tcsp;
      try (complete (destruct a; simpl in *; smash_pbft)).
  Qed.
  Hint Resolve add_new_prepare2log_preserves_pre_prepare_in_log_false : pbft.

  Lemma add_new_commit2log_preserves_pre_prepare_in_log_false :
    forall L c gi K pp d,
      add_new_commit2log L c = (gi, K)
      -> pre_prepare_in_log pp d K = false
      -> pre_prepare_in_log pp d L = false.
  Proof.
    induction L; introv add prep; simpl in *; smash_pbft; repndors; tcsp;
      try (complete (destruct a; simpl in *; smash_pbft)).
  Qed.
  Hint Resolve add_new_commit2log_preserves_pre_prepare_in_log_false : pbft.

  Lemma request_data2seq_pre_prepare2request_data :
    forall pp d,
      request_data2seq (pre_prepare2request_data pp d) = pre_prepare2seq pp.
  Proof.
    introv; destruct pp, b; simpl; auto.
  Qed.
  Hint Rewrite request_data2seq_pre_prepare2request_data : pbft.

  Lemma clear_log_checkpoint_preserves_pre_prepare_in_log_false :
    forall pp d L (n : SeqNum),
      pre_prepare_in_log pp d (clear_log_checkpoint L n) = false
      ->
      (
        pre_prepare_in_log pp d L = false
        \/
        pre_prepare2seq pp <= n
      ).
  Proof.
    induction L; introv prep; simpl in *; smash_pbft;[].

    apply IHL in prep; repndors; tcsp.
    unfold similar_entry_and_pre_prepare, eq_request_data in *.
    destruct a; simpl in *; smash_pbft.
  Qed.

  Lemma implies_pre_prepare_in_log_change_entry_add_replies2entry :
    forall pp d L n e reps,
      pre_prepare_in_log pp d L = true
      -> find_entry L n = Some e
      -> pre_prepare_in_log pp d (change_entry L (add_replies2entry e reps)) = true.
  Proof.
    induction L; introv prep find; simpl in *; smash_pbft;
      try (complete (destruct e; simpl in *; unfold eq_request_data in *; smash_pbft));
      try (complete (unfold similar_entry, eq_request_data in *; smash_pbft;
                     apply entry2seq_if_find_entry in find; subst;
                     destruct a, e; simpl in *; subst; tcsp)).
  Qed.
  Hint Resolve implies_pre_prepare_in_log_change_entry_add_replies2entry : pbft.

  Lemma find_and_execute_requests_preserves_pre_prepare_in_log_forward :
    forall msg i pp d s1 s2 v keys,
      find_and_execute_requests i v keys s1 = (msg, s2)
      -> pre_prepare_in_log pp d (log s1) = true
      -> pre_prepare_in_log pp d (log s2) = true.
  Proof.
    introv find h.

    unfold find_and_execute_requests in *; smash_pbft;[].

    unfold execute_requests in *.
    destruct (ready s1); simpl in *; smash_pbft;[].

    rename_hyp_with check_broadcast_checkpoint check.
    apply check_broadcast_checkpoint_preserves_log in check.
    simpl in *.
    rewrite <- check; eauto 3 with pbft.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_pre_prepare_in_log_forward : pbft.

  Lemma log_checkpoint_cert_from_new_view_preserves_pre_prepare_in_log_false_backward :
    forall i s1 v m C S s2 chkop pp d,
      log_checkpoint_cert_from_new_view i s1 v m C S = (s2, chkop)
      -> pre_prepare_in_log pp d (log s2) = false
      -> pre_prepare_in_log pp d (log s1) = false.
  Proof.
    introv chk prep.
    apply log_checkpoint_cert_from_new_view_preserves_log in chk.
    allrw; auto.
  Qed.

  Lemma pre_prepare_in_log_log_pre_prepares_false :
    forall pp d P L lwm,
      pre_prepare_in_log pp d (log_pre_prepares L lwm P) = false
      -> pre_prepare_in_log pp d L = false.
  Proof.
    induction P; introv prep; simpl in *; tcsp.
    repnd; smash_pbft.
  Qed.

  Lemma check_send_replies_preserves_pre_prepare_in_log_forward :
    forall i v keys giop s1 n msgs s2 pp d,
      check_send_replies i v keys giop s1 n = (msgs, s2)
      -> pre_prepare_in_log pp d (log s1) = true
      -> pre_prepare_in_log pp d (log s2) = true.
  Proof.
    introv check prep.
    unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_pre_prepare_in_log_forward : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_in_log_forward :
    forall slf state pp d ppd state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state ppd = (state', msgs)
      -> pre_prepare_in_log pp d (log state) = true
      -> pre_prepare_in_log pp d (log state') = true.
  Proof.
    introv h q.
    unfold add_prepare_to_log_from_new_view_pre_prepare in h.
    smash_pbft.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_in_log_forward : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_in_log_backward :
    forall slf state ppd pp d state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state ppd = (state', msgs)
      -> pre_prepare_in_log pp d (log state') = false
      -> pre_prepare_in_log pp d (log state) = false.
  Proof.
    introv h q.
    match goal with
    | [ |- ?a = ?b ] => remember a as pb; symmetry in Heqpb; destruct pb; auto
    end.
    eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_in_log_forward in h;[|eauto].
    rewrite h in q; ginv.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_in_log_backward : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_forward :
    forall slf pp d pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> pre_prepare_in_log pp d (log state) = true
      -> pre_prepare_in_log pp d (log state') = true.
  Proof.
    induction pps; introv h q; simpl in *; smash_pbft; repnd.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_forward : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_backward :
    forall slf pp d pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> pre_prepare_in_log pp d (log state') = false
      -> pre_prepare_in_log pp d (log state) = false.
  Proof.
    introv h q.
    match goal with
    | [ |- ?a = ?b ] => remember a as pb; symmetry in Heqpb; destruct pb; auto
    end.
    eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_forward in h;[|eauto].
    rewrite h in q; ginv.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_backward : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_false_backward :
    forall pp d i s1 pps s2 msgs,
      well_formed_log (log s1)
      -> well_formed_log (log s2)
      -> add_prepares_to_log_from_new_view_pre_prepares i s1 pps = (s2, msgs)
      -> pre_prepare_in_log pp d (log s2) = false
      -> pre_prepare_in_log pp d (log s1) = false.
  Proof.
    introv wf1 wf2 add prep.
    eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_backward in add;[|eauto]; auto.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_false_backward : pbft.

  Lemma update_state_new_view_preserves_pre_prepare_in_log_true_forward :
    forall pp d i s1 v s2 msgs,
      correct_new_view v = true
      -> update_state_new_view i s1 v = (s2, msgs)
      -> low_water_mark s2 < pre_prepare2seq pp
      -> pre_prepare_in_log pp d (log s1) = true
      -> pre_prepare_in_log pp d (log s2) = true.
  Proof.
    introv cor upd h prep.
    match goal with
    | [ |- ?x = _ ] => remember x as b; destruct b; auto; symmetry in Heqb
    end.
    eapply update_state_new_view_preserves_pre_prepare_in_log_false_forward in upd; eauto.
  Qed.
  Hint Resolve update_state_new_view_preserves_pre_prepare_in_log_true_forward : pbft.

  Lemma pre_prepare_in_log_check_one_stable2 :
    forall pp d i s l,
      well_formed_log (log s)
      -> low_water_mark s < pre_prepare2seq pp
      -> pre_prepare_in_log pp d (log (check_one_stable i s l)) = true
      -> pre_prepare_in_log pp d (log s) = true
         /\ low_water_mark (check_one_stable i s l) < pre_prepare2seq pp.
  Proof.
    induction l; introv wf lwm prep; simpl in *; smash_pbft;[].
    rename_hyp_with check_stable check.
    dup check as check'.
    eapply check_stable_preserves_pre_prepare_in_log2 in check;[| |eauto]; auto.
    repnd; dands; auto.
    apply low_water_mark_of_check_stable in check'; rewrite check'; simpl in *; omega.
  Qed.

  Lemma check_one_stable_preserves_prepare_in_log :
    forall i s l p,
      well_formed_log (log s)
      -> prepare_in_log p (log (check_one_stable i s l)) = true
      -> prepare_in_log p (log s) = true.
  Proof.
    induction l; introv wf prep; simpl in *; smash_pbft;[].
    rename_hyp_with check_stable check.
    eapply check_stable_preserves_prepare_in_log in check;[| |eauto]; auto.
  Qed.
  Hint Resolve check_one_stable_preserves_prepare_in_log : pbft.

  Lemma check_one_stable_preserves_prepare_in_log2 :
    forall i s l p,
      well_formed_log (log s)
      -> low_water_mark s < prepare2seq p
      -> prepare_in_log p (log (check_one_stable i s l)) = true
      -> prepare_in_log p (log s) = true /\
         low_water_mark (check_one_stable i s l) < prepare2seq p.
  Proof.
    induction l; introv wf lwm prep; simpl in *; smash_pbft;[].
    rename_hyp_with check_stable check.
    dup check as check'.
    eapply check_stable_preserves_prepare_in_log2 in check;[| |eauto]; auto.
    repnd; dands; auto.
    apply low_water_mark_of_check_stable in check'; rewrite check'; simpl in *; omega.
  Qed.

  Lemma prepare_somewhere_in_log_check_one_stable_false_implies :
    forall p i s l,
      prepare_somewhere_in_log p (log (check_one_stable i s l)) = false
      -> prepare_somewhere_in_log p (log s) = true
      -> prepare2seq p <= low_water_mark (check_one_stable i s l).
  Proof.
    induction l; introv prep1 prep2; simpl in *; smash_pbft;[].
    clear IHl.
    unfold check_stable in *; smash_pbft.
    applydup clear_log_checkpoint_preserves_prepare_somewhere_in_log_false in prep1.
    repndors; pbft_simplifier.
    rename_hyp_with checkpoint_entry2stable stable.
    applydup checkpoint_entry2stable_implies_same_sn in stable; rewrite <- stable0.
    simpl in *; try omega.
  Qed.
  Hint Resolve prepare_somewhere_in_log_check_one_stable_false_implies : pbft.

  Lemma pre_prepare_in_log_check_one_stable_false_implies :
    forall p d i s l,
      pre_prepare_in_log p d (log (check_one_stable i s l)) = false
      -> pre_prepare_in_log p d (log s) = true
      -> pre_prepare2seq p <= low_water_mark (check_one_stable i s l).
  Proof.
    induction l; introv prep1 prep2; simpl in *; smash_pbft;[].
    clear IHl.
    unfold check_stable in *; smash_pbft.
    applydup clear_log_checkpoint_preserves_pre_prepare_in_log_false in prep1.
    repndors; pbft_simplifier.
    rename_hyp_with checkpoint_entry2stable stable.
    applydup checkpoint_entry2stable_implies_same_sn in stable; rewrite <- stable0.
    simpl in *; try omega.
  Qed.
  Hint Resolve pre_prepare_in_log_check_one_stable_false_implies : pbft.

  Lemma add_new_checkpoint2cp_state_preserves_check_between_water_marks :
    forall s1 sm lastr c eop s2 n,
      add_new_checkpoint2cp_state s1 sm lastr c = (eop, s2)
      -> check_between_water_marks (scp_sn (chk_state_stable s1)) n = true
      -> check_between_water_marks (scp_sn (chk_state_stable s2)) n = true.
  Proof.
    introv add check.
    apply add_new_checkpoint2cp_state_preserves_sn_stable in add; allrw; auto.
  Qed.
  Hint Resolve add_new_checkpoint2cp_state_preserves_check_between_water_marks : pbft.

End PBFTgarbage_collect_misc1.


Hint Rewrite andb_false_r : bool.


Hint Rewrite @prepare_in_entry_pre_prepare2entry : pbft.
Hint Rewrite @prepare_in_entry_change_pre_prepare_info_of_entry : pbft.
Hint Rewrite @prepare_somewhere_in_log_add_new_pre_prepare2log : pbft.
Hint Rewrite @low_water_mark_update_log : pbft.
Hint Rewrite @prepare2seq_pre_prepare2seq : pbft.
Hint Rewrite @low_water_mark_log_new_view_and_entry_state : pbft.
Hint Rewrite @low_water_mark_log_new_pre_prepare : pbft.
Hint Rewrite @low_water_mark_increment_sequence_number : pbft.
Hint Rewrite @low_water_mark_update_primary_state : pbft.
Hint Rewrite @prepare_somewhere_in_log_log_pre_prepares : pbft.
Hint Rewrite @request_data2seq_pre_prepare2request_data : pbft.


Hint Resolve check_send_replies_preserves_prepare_somewhere_in_log : pbft.
Hint Resolve fill_out_pp_info_with_prepare_preserves_prepare_in_entry : pbft.
Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_prepare_somewhere_in_log_forward : pbft.
Hint Resolve clear_log_checkpoint_preserves_prepare_in_log : pbft.
Hint Resolve correct_new_view_implies_correct_view_change : pbft.
Hint Resolve view_change_cert2max_seq_vc_none_implies_correct_new_view_false : pbft.
Hint Resolve in_from_min_to_max_of_view_changes_implies_between_water_marks : pbft.
Hint Resolve add_prepare2entry_preserves_prepare_in_entry_false : pbft.
Hint Resolve add_new_prepare2log_preserves_prepare_somewhere_in_log_false : pbft.
Hint Resolve add_commit2entry_preserves_prepare_in_entry_false : pbft.
Hint Resolve add_new_commit2log_preserves_prepare_somewhere_in_log_false : pbft.
Hint Resolve prepare_in_log_implies_prepare_somewhere_in_log : pbft.
Hint Resolve prepare_somewhere_in_log_implies_prepare_in_log : pbft.
Hint Resolve implies_prepare_in_log_change_entry_add_replies2entry : pbft.
Hint Resolve find_and_execute_requests_preserves_prepare_somewhere_in_log_forward : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_somewhere_in_log_false_backward : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_somewhere_in_log_true_forward : pbft.
Hint Resolve implies_prepare_somewhere_in_log_clear_log_checkpoint : pbft.
Hint Resolve update_state_new_view_preserves_prepare_somewhere_in_log_true_forward : pbft.
Hint Resolve check_send_replies_preserves_pre_prepare_in_log_false : pbft.
Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log_forward : pbft.
Hint Resolve add_new_prepare2log_preserves_pre_prepare_in_log_false : pbft.
Hint Resolve add_new_commit2log_preserves_pre_prepare_in_log_false : pbft.
Hint Resolve implies_pre_prepare_in_log_change_entry_add_replies2entry : pbft.
Hint Resolve find_and_execute_requests_preserves_pre_prepare_in_log_forward : pbft.
Hint Resolve check_send_replies_preserves_pre_prepare_in_log_forward : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_in_log_forward : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_in_log_backward : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_forward : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_backward : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_false_backward : pbft.
Hint Resolve update_state_new_view_preserves_pre_prepare_in_log_true_forward : pbft.
Hint Resolve check_one_stable_preserves_prepare_in_log : pbft.
Hint Resolve prepare_somewhere_in_log_check_one_stable_false_implies : pbft.
Hint Resolve pre_prepare_in_log_check_one_stable_false_implies : pbft.
Hint Resolve add_new_checkpoint2cp_state_preserves_check_between_water_marks : pbft.
