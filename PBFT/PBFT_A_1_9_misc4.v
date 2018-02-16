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


Require Export PBFT_A_1_9_part1.
Require Export PBFT_A_1_2_5.
Require Export PBFT_A_1_9_misc1.
Require Export PBFT_A_1_9_misc2.
Require Export PBFT_A_1_9_misc3.


Section PBFT_A_1_9_misc4.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma in_view_change_cert2max_seq_vc_implies_view_change2seq_le :
    forall vc C max x,
      In vc C
      -> view_change_cert2max_seq_vc C = Some (max, x)
      -> view_change2seq vc <= max.
  Proof.
    induction C; introv i m; simpl in *; tcsp; repndors; subst; smash_pbft; try omega;[].
    destruct C; simpl in *; smash_pbft.
  Qed.

  Lemma entry2prepared_info_preserves_request_data :
    forall a x rd,
      is_request_data_for_entry a rd = true
      -> entry2prepared_info a = Some x
      -> prepared_info2request_data x = rd.
  Proof.
    introv isreq eqx.
    destruct a; simpl in *.
    destruct log_entry_pre_prepare_info; smash_pbft;[].
    unfold is_request_data_for_entry, eq_request_data in *; simpl in *; smash_pbft.
    unfold prepared_info2request_data; simpl.
    destruct rd; simpl; auto.
  Qed.
  Hint Resolve entry2prepared_info_preserves_request_data : pbft.

  Lemma entry2prepared_info_none_implies_is_prepared_entry_false :
    forall a,
      entry2prepared_info a = None
      -> is_prepared_entry a = false.
  Proof.
    introv h; destruct a; simpl in *.
    destruct log_entry_pre_prepare_info; simpl in *; smash_pbft.
  Qed.

  Lemma is_prepared_entry_implies_info_is_prepared :
    forall a x,
      is_prepared_entry a = true
      -> entry2prepared_info a = Some x
      -> well_formed_log_entry a
      -> info_is_prepared x = true.
  Proof.
    introv isprep h wf.
    unfold info_is_prepared.
    destruct x, a, log_entry_pre_prepare_info, log_entry_request_data; simpl in *;
      unfold prepared_info2senders, prepared_info2pp_sender, prepared_info2view in *;
      simpl in *; smash_pbft.
    allrw map_map; simpl in *; autorewrite with list; dands; auto.

    - unfold prepared_info_has_correct_digest, prepared_info2requests; simpl; smash_pbft.
      apply well_formed_log_entry_correct_digest in wf.
      simpl in *.
      unfold same_digests in wf; smash_pbft.

    - apply well_formed_log_entry_prepares in wf; simpl in *.
      apply norepeatsb_as_no_repeats.
      rename_hyp_with length len; clear len.
      induction log_entry_prepares; simpl in *; tcsp.
      inversion wf as [|? ? ni norep]; subst; clear wf.
      autodimp IHlog_entry_prepares hyp.
      constructor; auto;[].
      destruct a; simpl in *.
      intro xx; apply in_map_iff in xx; exrepnd.
      destruct x; simpl in *; subst.
      destruct ni; apply in_map_iff; eexists; dands; eauto.
      simpl; auto.

    - apply well_formed_log_entry_no_prepare_from_leader in wf; simpl in *.
      rewrite forallb_forall; introv xx.
      apply in_map_iff in xx; exrepnd.
      destruct x0; simpl in *; subst; smash_pbft.
      destruct wf; apply in_map_iff.
      eexists; dands; eauto.
      simpl; auto.

    - apply forallb_forall; introv xx; simpl in *.
      apply in_map_iff in xx; exrepnd; subst; simpl in *.
      destruct x0; simpl in *; smash_pbft.
  Qed.
  Hint Resolve is_prepared_entry_implies_info_is_prepared : pbft.

  Lemma prepared_implies :
    forall rd L sn,
      well_formed_log L
      -> prepared_log rd L = true
      -> sn < request_data2seq rd
      ->
      exists pi,
        In pi (gather_prepared_messages L sn)
        /\ info_is_prepared pi = true
        /\ prepared_info2request_data pi = rd.
  Proof.
    induction L; introv wf prep gtsn; simpl in *; tcsp; smash_pbft;
      try (inversion wf as [|? ? imp wf1 wf2]; subst; clear wf); auto.

    - exists x; dands; tcsp; eauto 3 with pbft.

    - rewrite entry2prepared_info_none_implies_is_prepared_entry_false in prep; ginv.

    - unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
      destruct a, log_entry_request_data; simpl in *; try omega.

    - eapply IHL in prep;[| |eauto];auto; exrepnd.
      exists pi; dands; auto.
  Qed.

  Lemma pre_prepare2view_prepared_info_pre_prepare :
    forall pi,
      pre_prepare2view (prepared_info_pre_prepare pi)
      = prepared_info2view pi.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite pre_prepare2view_prepared_info_pre_prepare : pbft.

  Lemma requests2digest_pre_prepare2requests_prepared_info_pre_prepare :
    forall pi,
      info_is_prepared pi = true
      -> requests2digest (pre_prepare2requests (prepared_info_pre_prepare pi))
         = prepared_info2digest pi.
  Proof.
    introv prep.
    apply info_is_prepared_implies_prepared_info_has_correct_digest in prep.
    destruct pi, prepared_info_pre_prepare, b; simpl.
    unfold prepared_info_has_correct_digest in prep; simpl in *.
    unfold prepared_info2requests in *; simpl in *; smash_pbft.
  Qed.

  Lemma prepared_info2request_data_eq_request_data_implies_prepared_info2view :
    forall pi v n d,
      prepared_info2request_data pi = request_data v n d
      -> prepared_info2view pi = v.
  Proof.
    introv prep; destruct pi, prepared_info_pre_prepare, b; simpl in *.
    unfold prepared_info2request_data in *; simpl in *; ginv; tcsp.
  Qed.

  Lemma prepared_info2request_data_eq_request_data_implies_prepared_info2digest :
    forall pi v n d,
      prepared_info2request_data pi = request_data v n d
      -> prepared_info2digest pi = d.
  Proof.
    introv prep; destruct pi, prepared_info_pre_prepare, b; simpl in *.
    unfold prepared_info2request_data in *; simpl in *; ginv; tcsp.
  Qed.

  Lemma PBFT_A_1_4_same_loc :
    forall (eo : EventOrdering)
           (e  : Event)
           (i  : Rep)
           (n  : SeqNum)
           (v  : View)
           (d1 : PBFTdigest)
           (d2 : PBFTdigest)
           (st : PBFTstate),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> prepared (request_data v n d1) st = true
      -> prepared (request_data v n d2) st = true
      -> d1 = d2.
  Proof.
    introv sentbyz ckeys atMost eqloc eqst prep1 prep2.
    eapply A_1_4; eauto; eauto 3 with pbft eo.
  Qed.

  Lemma PBFT_A_1_4_same_loc_before :
    forall (eo : EventOrdering)
           (e  : Event)
           (i  : Rep)
           (n  : SeqNum)
           (v  : View)
           (d1 : PBFTdigest)
           (d2 : PBFTdigest)
           (st : PBFTstate),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> loc e = PBFTreplica i
      -> state_sm_before_event (PBFTreplicaSM i) e = Some st
      -> prepared (request_data v n d1) st = true
      -> prepared (request_data v n d2) st = true
      -> d1 = d2.
  Proof.
    introv sentbyz ckeys atMost eqloc eqst prep1 prep2.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d|d]; ginv; subst; simpl in *;[].
    eapply PBFT_A_1_4_same_loc; try (exact eqst); eauto;
      autorewrite with pbft eo in *; eauto 3 with pbft eo.
  Qed.

  Lemma prepared_info2request_data_eq_request_data_implies_prepared_info2seq :
    forall pi v n d,
      prepared_info2request_data pi = request_data v n d
      -> prepared_info2seq pi = n.
  Proof.
    introv prep; destruct pi, prepared_info_pre_prepare, b; simpl in *.
    unfold prepared_info2request_data in *; simpl in *; ginv; tcsp.
  Qed.

  Lemma entry2prepared_info_some_implies_is_prepared_entry :
    forall a nfo,
      entry2prepared_info a = Some nfo
      -> is_prepared_entry a = true.
  Proof.
    introv h.
    destruct a, log_entry_pre_prepare_info; simpl in *; smash_pbft.
  Qed.
  Hint Resolve entry2prepared_info_some_implies_is_prepared_entry : pbft.

  Lemma in_gather_prepared_messages_implies :
    forall nfo L n,
      In nfo (gather_prepared_messages L n)
      ->
      exists entry,
        In entry L
        /\ n < entry2seq entry
        /\ entry2prepared_info entry = Some nfo.
  Proof.
    induction L; introv i; simpl in *; tcsp; smash_pbft;
      repndors; subst; tcsp;
        try (complete (apply IHL in i; exrepnd; exists entry; tcsp)).
    exists a; dands; tcsp.
  Qed.

  Lemma in_gather_prepared_messages_implies_prepared :
    forall nfo L n,
      well_formed_log L
      -> In nfo (gather_prepared_messages L n)
      -> prepared_log
           (request_data
              (prepared_info2view nfo)
              (prepared_info2seq nfo)
              (prepared_info2digest nfo)) L = true.
  Proof.
    introv wf i.
    apply in_gather_prepared_messages_implies in i; exrepnd.
    induction L; simpl in *; tcsp; repndors; subst; tcsp; smash_pbft;
      try (inversion wf as [|? ? imp wf1 wf2]; subst; clear wf); tcsp;[|].

    - unfold is_request_data_for_entry, eq_request_data in *.
      smash_pbft.
      destruct entry, log_entry_pre_prepare_info, log_entry_request_data;
        simpl in *; smash_pbft.

    - repeat (autodimp IHL hyp).
      apply prepared_log_implies in IHL; exrepnd.
      unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
      rewrite IHL2 in *; clear IHL2.
      apply imp in IHL1.
      unfold entries_have_different_request_data in *; tcsp.
  Qed.
  Hint Resolve in_gather_prepared_messages_implies_prepared : pbft.

  Lemma entry2prepared_info_some_implies_entry2pre_prepare_some :
    forall entry nfo,
      entry2prepared_info entry = Some nfo
      -> exists pp, entry2pre_prepare entry = Some pp.
  Proof.
    introv h; destruct entry, log_entry_pre_prepare_info, log_entry_request_data;
      simpl in *; smash_pbft.
  Qed.

  Lemma in_entry_implies_pre_prepare_in_log :
    forall pp entry L,
      well_formed_log L
      -> In entry L
      -> entry2pre_prepare entry = Some pp
      -> pre_prepare_in_log pp (pre_prepare2digest pp) L = true.
  Proof.
    induction L; introv wf i h; simpl in *; tcsp.
    inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
    repndors; subst; tcsp; smash_pbft.

    - clear imp IHL wf2.
      destruct entry, log_entry_request_data, log_entry_pre_prepare_info; simpl in *; ginv; simpl in *.
      unfold eq_request_data in *; smash_pbft.

    - clear imp IHL wf2.
      destruct entry, log_entry_request_data, log_entry_pre_prepare_info; simpl in *; ginv; simpl in *.
      unfold eq_request_data in *; smash_pbft.
      unfold pre_prepare2digest in *; simpl in *.
      apply well_formed_log_entry_correct_digest in wf1; simpl in wf1.
      unfold same_digests in *; smash_pbft.
      rewrite requests2digest_map_fst_as_requests_and_replies2digest in n; tcsp.

    - repeat (autodimp IHL hyp).
      apply entry_of_pre_prepare_in_log2 in IHL; exrepnd.
      applydup imp in IHL0.

      unfold entries_have_different_request_data in *.
      unfold similar_entry_and_pre_prepare in *.
      destruct a; simpl in *.
      unfold eq_request_data in *; smash_pbft.
  Qed.

  Lemma pre_prepare_in_log_before_implies_in_on :
    forall (eo : EventOrdering) (e : Event) i st pp d,
      pre_prepare_in_log pp d (log st) = true
      -> state_sm_before_event (PBFTreplicaSM i) e = Some st
      ->
      exists e',
        direct_pred e = Some e'
        /\ state_sm_on_event (PBFTreplicaSM i) e' = Some st.
  Proof.
    introv prep eqst.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d1|d1]; ginv;[].
    exists (local_pred e); dands; auto; eauto 3 with eo.
  Qed.

  Lemma entry2prepared_info_some_implies_equal_views :
    forall entry nfo,
      entry2prepared_info entry = Some nfo
      -> entry2view entry = prepared_info2view nfo.
  Proof.
    introv j.
    destruct entry, log_entry_pre_prepare_info, log_entry_request_data; simpl in *; smash_pbft.
  Qed.
  Hint Resolve entry2prepared_info_some_implies_equal_views : pbft.

  Lemma entry2prepared_info_some_implies_equal_seqs :
    forall entry nfo,
      entry2prepared_info entry = Some nfo
      -> entry2seq entry = prepared_info2seq nfo.
  Proof.
    introv j.
    destruct entry, log_entry_pre_prepare_info, log_entry_request_data; simpl in *; smash_pbft.
  Qed.
  Hint Resolve entry2prepared_info_some_implies_equal_seqs : pbft.

  Lemma entry2pre_prepare_some_implies_equal_views :
    forall entry pp,
      entry2pre_prepare entry = Some pp
      -> entry2view entry = pre_prepare2view pp.
  Proof.
    introv h.
    destruct entry, log_entry_request_data, log_entry_pre_prepare_info; simpl in *; smash_pbft.
  Qed.
  Hint Resolve entry2pre_prepare_some_implies_equal_views : pbft.

  Lemma entry2pre_prepare_some_implies_equal_seqs :
    forall entry pp,
      entry2pre_prepare entry = Some pp
      -> entry2seq entry = pre_prepare2seq pp.
  Proof.
    introv h.
    destruct entry, log_entry_request_data, log_entry_pre_prepare_info; simpl in *; smash_pbft.
  Qed.
  Hint Resolve entry2pre_prepare_some_implies_equal_seqs : pbft.

  Lemma entry2pre_prepare_some_implies_equal_digests :
    forall entry pp,
      well_formed_log_entry entry
      -> entry2pre_prepare entry = Some pp
      -> entry2digest entry = pre_prepare2digest pp.
  Proof.
    introv wf h.
    destruct entry, log_entry_request_data, log_entry_pre_prepare_info; simpl in *; smash_pbft.
    unfold pre_prepare2digest; simpl.
    apply well_formed_log_entry_correct_digest in wf; simpl in *.
    unfold same_digests in *; smash_pbft.
  Qed.
  Hint Resolve entry2pre_prepare_some_implies_equal_digests : pbft.

  Lemma entry2prepared_info_some_implies_equal_digests :
    forall entry nfo,
      entry2prepared_info entry = Some nfo
      -> entry2digest entry = prepared_info2digest nfo.
  Proof.
    introv j.
    destruct entry, log_entry_pre_prepare_info, log_entry_request_data; simpl in *; smash_pbft.
  Qed.
  Hint Resolve entry2prepared_info_some_implies_equal_digests : pbft.

  Lemma prepared_log_add_new_pre_prepare2log_implies :
    forall rd pp d L,
      prepared_log rd (add_new_pre_prepare2log pp d L) = true
      -> prepared_log rd L = true \/ similar_pre_prepare_and_request_data pp d rd = true.
  Proof.
    induction L; introv prep; simpl in *; tcsp; smash_pbft.

    - clear IHL prep.
      right.
      unfold is_request_data_for_entry, eq_request_data in *; smash_pbft;[].
      unfold similar_entry_and_pre_prepare in *; destruct a; simpl in *.
      unfold eq_request_data in *; smash_pbft;[].
      unfold similar_pre_prepare_and_request_data, eq_request_data; smash_pbft.

    - clear IHL prep.
      assert False; tcsp.
      unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.

    - clear IHL prep.
      assert False; tcsp.
      unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
  Qed.

  Lemma check_send_replies_preserves_prepared_log :
    forall i v keys giop s1 n msgs s2 rd,
      check_send_replies i v keys giop s1 n = (msgs, s2)
      -> prepared_log rd (log s2) = true
      -> prepared_log rd (log s1) = true.
  Proof.
    introv check prep.
    unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_prepared_log_backward :
    forall rd L K pp d Fp Fc giop slf,
      add_new_pre_prepare_and_prepare2log slf L pp d Fp Fc = (giop, K)
      -> prepared_log rd K = true
      -> prepared_log rd L = true \/ similar_pre_prepare_and_request_data pp d rd = true.
  Proof.
    induction L; introv add prep; repeat (simpl in *; smash_pbft).

    - right; clear IHL.
      rename_hyp_with fill_out_pp_info_with_prepare fill.
      apply fill_out_pp_info_with_prepare_preserves_request_data in fill.
      remember (gi_entry x) as entry; clear Heqentry.
      unfold similar_pre_prepare_and_request_data.
      destruct a; simpl in *.
      unfold is_request_data_for_entry in *; simpl in *.
      unfold eq_request_data in *; smash_pbft.

    - clear prep IHL.
      assert False; tcsp.
      rename_hyp_with fill_out_pp_info_with_prepare fill.
      apply fill_out_pp_info_with_prepare_preserves_request_data in fill.
      remember (gi_entry x) as entry; clear Heqentry.
      unfold similar_pre_prepare_and_request_data.
      destruct a; simpl in *.
      unfold is_request_data_for_entry in *; simpl in *.
      unfold eq_request_data in *; smash_pbft.

    - clear prep IHL.
      assert False; tcsp.
      rename_hyp_with fill_out_pp_info_with_prepare fill.
      apply fill_out_pp_info_with_prepare_preserves_request_data in fill.
      remember (gi_entry x) as entry; clear Heqentry.
      unfold similar_pre_prepare_and_request_data.
      destruct a; simpl in *.
      unfold is_request_data_for_entry in *; simpl in *.
      unfold eq_request_data in *; smash_pbft.
  Qed.

  Lemma request_data2view_prepare_2request_data :
    forall pp d,
      request_data2view (pre_prepare2request_data pp d)
      = pre_prepare2view pp.
  Proof.
    introv; destruct pp, b; tcsp.
  Qed.
  Hint Rewrite request_data2view_prepare_2request_data : pbft.

  Lemma add_new_prepare2log_preserves_prepared_log_backward :
    forall rd L K p Fc giop slf,
      add_new_prepare2log slf L p Fc = (giop, K)
      -> prepared_log rd K = true
      -> prepared_log rd L = true \/ rd = prepare2request_data p.
  Proof.
    induction L; introv add prep; repeat (simpl in *; smash_pbft).

    - right; clear IHL prep.
      rename_hyp_with add_prepare2entry add.
      apply gi_entry_of_add_prepare2entry_some in add.
      remember (gi_entry x) as entry; clear Heqentry.
      unfold is_prepare_for_entry in *.
      destruct a; simpl in *.
      unfold is_request_data_for_entry in *; simpl in *.
      unfold eq_request_data in *; smash_pbft.

    - clear prep IHL.
      assert False; tcsp.
      rename_hyp_with add_prepare2entry add.
      apply gi_entry_of_add_prepare2entry_some in add.
      remember (gi_entry x) as entry; clear Heqentry.
      unfold is_prepare_for_entry in *.
      destruct a; simpl in *.
      unfold is_request_data_for_entry in *; simpl in *.
      unfold eq_request_data in *; smash_pbft.

    - clear prep IHL.
      assert False; tcsp.
      rename_hyp_with add_prepare2entry add.
      apply gi_entry_of_add_prepare2entry_some in add.
      remember (gi_entry x) as entry; clear Heqentry.
      unfold is_prepare_for_entry in *.
      destruct a; simpl in *.
      unfold is_request_data_for_entry in *; simpl in *.
      unfold eq_request_data in *; smash_pbft.
  Qed.

  Lemma request_data2view_prepare2request_data :
    forall p,
      request_data2view (prepare2request_data p)
      = prepare2view p.
  Proof.
    introv; destruct p, b; auto.
  Qed.
  Hint Rewrite request_data2view_prepare2request_data : pbft.

  Lemma request_data2seq_prepare2request_data :
    forall p,
      request_data2seq (prepare2request_data p)
      = prepare2seq p.
  Proof.
    introv; destruct p, b; auto.
  Qed.
  Hint Rewrite request_data2seq_prepare2request_data : pbft.

  Lemma add_new_commit2log_preserves_prepared_log_backward :
    forall rd L K com gi,
      add_new_commit2log L com = (gi, K)
      -> prepared_log rd K = true
      -> prepared_log rd L = true.
  Proof.
    induction L; introv add prep; repeat (simpl in *; tcsp; smash_pbft2).

    - destruct a; simpl in *; smash_pbft.

    - clear IHL prep.
      assert False; tcsp.
      rename_hyp_with add_commit2entry add.
      apply add_commit2entry_preserves_log_entry_request_data in add.
      unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.

    - clear IHL prep.
      assert False; tcsp.
      rename_hyp_with add_commit2entry add.
      apply add_commit2entry_preserves_log_entry_request_data in add.
      unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
  Qed.
  Hint Resolve add_new_commit2log_preserves_prepared_log_backward : pbft.

  Lemma clear_log_checkpoint_preserves_prepared_log2 :
    forall rd L sn,
      well_formed_log L
      -> prepared_log rd (clear_log_checkpoint L sn) = true
      -> prepared_log rd L = true /\ sn < request_data2seq rd.
  Proof.
    induction L; simpl in *; introv wf h; tcsp.
    inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
    smash_pbft.

    - assert False; tcsp.

      apply IHL in h; repnd; auto.

      match goal with
      | [ H : prepared_log _ _ = _ |- _ ] => apply entry_of_prepared_log in H
      end.
      exrepnd.
      pose proof (imp entry) as q; autodimp q hyp; apply q; auto.
      allrw; auto.
      unfold is_request_data_for_entry in *. unfold eq_request_data in *. smash_pbft.

    - dands; auto.
      unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
      destruct a; simpl in *; auto.
  Qed.

  Lemma check_stable_preserves_prepared_backward :
    forall rd slf state entry state',
      well_formed_log (log state)
      -> check_stable slf state entry = Some state'
      -> prepared rd state' = true
      -> prepared rd state = true
         /\ cp_sn entry < request_data2seq rd.
  Proof.
    introv wf h q.
    unfold check_stable in h; smash_pbft;[].
    unfold prepared in *; simpl in *.
    apply clear_log_checkpoint_preserves_prepared_log2 in q; auto.
  Qed.
  Hint Resolve check_stable_preserves_prepared_backward : pbft.

  Lemma find_and_execute_requests_preserves_prepared_backward :
    forall msg i s1 s2 rd v keys,
      find_and_execute_requests i v keys s1 = (msg, s2)
      -> prepared rd s2 = true
      -> prepared rd s1 = true.
  Proof.
    introv fexec prep.
    unfold find_and_execute_requests in fexec; smash_pbft.
    unfold prepared in *; simpl in *.
    unfold execute_requests in *.
    destruct (ready s1); smash_pbft;[].
    unfold check_broadcast_checkpoint in *; smash_pbft2.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_prepared_backward : pbft.

  Lemma update_state_new_view_preserves_prepared_log2 :
    forall rd i s1 nv s2 msgs,
      correct_new_view nv = true
      -> well_formed_log (log s1)
      -> update_state_new_view i s1 nv = (s2, msgs)
      -> prepared_log rd (log s2) = true
      -> exists n,
          view_change_cert2max_seq (new_view2cert nv) = Some n
          /\ prepared_log rd (log s1) = true
          /\
          (
            (
              low_water_mark s1 < n
              /\ low_water_mark s2 < request_data2seq rd
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
    unfold update_state_new_view in upd; smash_pbft;[| |].

    - rename_hyp_with log_checkpoint_cert_from_new_view chk.
      rename_hyp_with view_change_cert2max_seq_vc mseq.

      applydup sn_of_view_change_cert2max_seq_vc in mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      applydup correct_new_view_implies_correct_view_change in mseq1;auto.

      applydup log_checkpoint_cert_from_new_view_preserves_log in chk.
      subst; rewrite chk0.

      eapply clear_log_checkpoint_preserves_prepared_log2 in prep; eauto;
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

  Lemma prepared_log_log_pre_prepares_implies :
    forall rd P L n,
      prepared_log rd (log_pre_prepares L n P) = true
      -> prepared_log rd L = true
         \/
         exists pp d,
           In (pp,d) P
           /\ similar_pre_prepare_and_request_data pp d rd = true
           /\ n < request_data2seq rd.
  Proof.
    induction P; introv prep; simpl in *; tcsp;[].
    repnd; smash_pbft;[|].

    - apply IHP in prep.
      repndors;[|].

      + apply prepared_log_add_new_pre_prepare2log_implies in prep.
        repndors; tcsp;[].

        right.
        exists a0 a; dands; tcsp.
        clear IHP.
        unfold similar_pre_prepare_and_request_data, eq_request_data in *; smash_pbft.

      + exrepnd.
        right.
        exists pp d; dands; auto.

    - apply IHP in prep; repndors; tcsp;[].
      exrepnd.
      right.
      exists pp d; dands; auto.
  Qed.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_prepared_log_backward :
    forall i rd pp d s1 s2 msgs,
      add_prepare_to_log_from_new_view_pre_prepare i s1 (pp,d) = (s2, msgs)
      -> prepared_log rd (log s2) = true
      -> prepared_log rd (log s1) = true
         \/
         (
           similar_pre_prepare_and_request_data pp d rd = true
           /\ low_water_mark s1 < pre_prepare2seq pp
         ).
  Proof.
    introv add prep.
    unfold add_prepare_to_log_from_new_view_pre_prepare in add; smash_pbft;[].
    eapply check_send_replies_preserves_prepared_log in prep;[|eauto]; simpl in *.
    eapply add_new_pre_prepare_and_prepare2log_preserves_prepared_log_backward in prep;[|eauto].
    repndors; tcsp.
  Qed.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_prepared_log_backward :
    forall i rd pps s1 s2 msgs,
      add_prepares_to_log_from_new_view_pre_prepares i s1 pps = (s2, msgs)
      -> prepared_log rd (log s2) = true
      -> prepared_log rd (log s1) = true
         \/
         exists pp d,
           In (pp,d) pps
           /\ similar_pre_prepare_and_request_data pp d rd = true
           /\ low_water_mark s1 < pre_prepare2seq pp.
  Proof.
    induction pps; introv add prep; repeat (simpl in *; tcsp; smash_pbft).
    dup prep as prep'.

    rename_hyp_with add_prepare_to_log_from_new_view_pre_prepare add.
    applydup add_prepare_to_log_from_new_view_pre_prepare_preserves_low_water_mark in add.

    eapply IHpps in prep';[|eauto].
    repndors; repnd; tcsp.

    - eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_prepared_log_backward in prep';[|eauto].
      repndors; repnd; tcsp.
      right.
      exists a0 a; dands; auto.

    - exrepnd.
      right.
      exists pp d; dands; auto; try congruence.
  Qed.

  Lemma prepared_log_check_one_stable_implies :
    forall rd i s l,
      well_formed_log (log s)
      -> prepared_log rd (log (check_one_stable i s l)) = true
      -> prepared_log rd (log s) = true.
  Proof.
    induction l; introv wf prep; simpl in *; smash_pbft.
    eapply check_stable_preserves_prepared_backward in prep;[| |eauto]; tcsp.
  Qed.
  Hint Resolve prepared_log_check_one_stable_implies : pbft.

  Lemma prepared_log_from_matching_view_and_seq :
    forall (eo : EventOrdering) (e : Event) i st rd,
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> prepared_log rd (log st) = true
      ->
      exists e' st',
        e' ⊑ e
        /\ state_sm_on_event (PBFTreplicaSM i) e' = Some st'
        /\ prepared_log rd (log st') = true
        /\ current_view st' = request_data2view rd
        /\ low_water_mark st' < request_data2seq rd.
  Proof.
    intros eo e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv eqst prep.

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
      (* request *)

      rename_hyp_with check_new_request check.

      applydup prepared_log_add_new_pre_prepare2log_implies in prep; repndors;
        [try (smash_pbft_ind ind)|];[].

      unfold similar_pre_prepare_and_request_data, eq_request_data in prep0;smash_pbft;[].

      exists e; eexists; dands; eauto; eauto 2 with eo; simpl.
      autorewrite with pbft.
      apply check_new_requests_some_iff in check; repnd; simpl in *.
      subst; simpl in *; autorewrite with pbft in *.

      rename_hyp_with check_between_water_marks bwm.
      apply check_between_water_marks_implies_lt in bwm; auto.
    }

    {
      (* pre-prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_pre_prepare_and_prepare2log add.
      rename_hyp_with check_between_water_marks bwm.

      dup prep as prep'.
      eapply check_send_replies_preserves_prepared_log in prep';[|eauto].
      simpl in *.

      eapply add_new_pre_prepare_and_prepare2log_preserves_prepared_log_backward in prep';[|eauto].
      repndors;[try (smash_pbft_ind ind)|];[].

      applydup check_send_replies_preserves_current_view in check.
      applydup PBFTordering.check_send_replies_preserves_low_water_mark in check.
      simpl in *; autorewrite with pbft in *.

      unfold similar_pre_prepare_and_request_data, eq_request_data in prep';smash_pbft;[].
      apply check_between_water_marks_implies_lt in bwm; auto.

      exists e; eexists; dands; eauto; eauto 2 with eo; simpl; autorewrite with pbft in *;
        try congruence;
        try (complete (rewrite <- check1; auto)).
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_prepare2log add.
      rename_hyp_with check_between_water_marks bwm.

      dup prep as prep'.
      eapply check_send_replies_preserves_prepared_log in prep';[|eauto].
      simpl in *.

      eapply add_new_prepare2log_preserves_prepared_log_backward in prep';[|eauto].
      repndors;[try (smash_pbft_ind ind)|];[].

      applydup check_send_replies_preserves_current_view in check.
      applydup PBFTordering.check_send_replies_preserves_low_water_mark in check.
      simpl in *; autorewrite with pbft in *.

      subst.
      apply check_between_water_marks_implies_lt in bwm; auto.

      exists e; eexists; dands; eauto; eauto 2 with eo; simpl; autorewrite with pbft in *;
        try congruence;
        try (complete (rewrite <- check1; auto)).
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_commit2log add.
      rename_hyp_with check_between_water_marks bwm.

      dup prep as prep'.
      eapply check_send_replies_preserves_prepared_log in prep';[|eauto].
      simpl in *.

      eapply add_new_commit2log_preserves_prepared_log_backward in prep';[|eauto].
      try (smash_pbft_ind ind).
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.
      dup prep as prep'.
      eapply find_and_execute_requests_preserves_prepared_backward in prep';[|eauto].
      unfold prepared in *.
      try (smash_pbft_ind ind).
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with CheckBCastNewView2entry cb.

      apply CheckBCastNewView2entry_some_implies in cb.

      applydup update_state_new_view_preserves_current_view in upd; simpl in *.
      applydup check_broadcast_new_view_implies in check.

      dup prep as prep'.
      eapply update_state_new_view_preserves_prepared_log2 in prep';
        [| | |eauto];simpl in *; autorewrite with pbft in *; eauto 4 with pbft;[].

      exrepnd.
      match goal with
      | [ H : new_view2cert _ = _ |- _ ] => rename H into eqcert
      end.

      match goal with
      | [ H1 : view_change_cert2max_seq _ = _, H2 : view_change_cert2max_seq _ = _ |- _ ] =>
        rename H1 into mseq1; rename H2 into mseq2
      end.
      rewrite <- eqcert in mseq1.
      rewrite mseq2 in mseq1; inversion mseq1 as [xx].
      rewrite xx in *; clear mseq1 xx.

      hide_hyp upd.
      apply prepared_log_log_pre_prepares_implies in prep'2.
      destruct prep'2 as [prep'|prep'];[try (smash_pbft_ind ind)|];[].

      exrepnd.

      dup prep'1 as j.
      eapply in_check_broadcast_new_view_implies_between_water_marks2 in j as bwm;
        [|eauto|eauto];[].
      apply check_between_water_marks_implies_lt in bwm; auto.

      dup prep'1 as k.
      eapply check_broadcast_new_view_preserves_view in k;[|eauto];[].

      unfold similar_pre_prepare_and_request_data, eq_request_data in prep'3;smash_pbft;[].

      exists e; eexists; dands; eauto; eauto 2 with eo; simpl; autorewrite with pbft in *;
        try congruence;
        try (complete (repndors; repnd; tcsp; rewrite <- prep'0; auto)).

      applydup check_broadcast_new_view_implies_eq_views in check;[|eauto 3 with pbft];[].

      rewrite k in *.
      rewrite upd0.
      rewrite check2.
      rewrite less_max_view; auto.
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with has_new_view hnv.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_low_water_mark in add.
      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_current_view in add.
      applydup update_state_new_view_preserves_current_view in upd.
      simpl in *; autorewrite with pbft in *.

      dup prep as prep'.
      eapply update_state_new_view_preserves_prepared_log2 in prep';
        [| | |eauto];simpl in *; autorewrite with pbft in *; eauto 4 with pbft;[].
      exrepnd.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_prepared_log_backward in prep'2;[|eauto];[].
      simpl in *; autorewrite with pbft in *.

      destruct prep'2 as [prep'|prep'];[try (smash_pbft_ind ind)|];[].
      exrepnd.

      unfold similar_pre_prepare_and_request_data, eq_request_data in prep'4;smash_pbft;[].

      dup prep'2 as j.
      apply pre_prepare_in_map_correct_new_view_implies2 in j; auto; simpl in *.

      rename_hyp_with view_change_cert2max_seq mseq.
      unfold view_change_cert2max_seq in mseq; smash_pbft;[].

      dup prep'2 as k.
      eapply correct_new_view_implies_between_water_marks in k;auto;[|eauto].

      apply check_between_water_marks_implies_lt in k; auto.

      exists e; eexists; dands; eauto; eauto 2 with eo; simpl; autorewrite with pbft in *;
        try congruence;
        try (complete (repndors; repnd; tcsp; congruence)).

      rewrite <- j.
      rewrite upd1.
      rewrite add2.
      rewrite less_max_view; auto.
    }
  Qed.

  Lemma pre_prepares_dont_get_garbage_collected :
    forall i (eo : EventOrdering) (e1 e2 : Event) state1 state2 pp d,
      e1 ⊏ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> pre_prepare_in_log pp d (log state1) = true
      -> low_water_mark state2 < pre_prepare2seq pp
      -> pre_prepare_in_log pp d (log state2) = true.
  Proof.
    introv ltes eqst1 eqst2 prep1 lwm.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    assert False; tcsp.
    pose proof (pre_prepares_get_garbage_collected_v2 i eo e1 e2 state1 state2 pp d) as q.
    repeat (autodimp q hyp); try omega.
  Qed.

  Lemma prepares_dont_get_garbage_collected :
    forall i (eo : EventOrdering) (e1 e2 : Event) state1 state2 p,
      e1 ⊏ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> prepare_in_log p (log state1) = true
      -> low_water_mark state2 < prepare2seq p
      -> prepare_in_log p (log state2) = true.
  Proof.
    introv ltes eqst1 eqst2 prep1 lwm.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    assert False; tcsp.

    apply prepare_somewhere_in_log_iff_prepare_in_log in prep1;[|eauto 3 with pbft].
    apply prepare_somewhere_in_log_false_iff_prepare_in_log_false in Heqb;[|eauto 3 with pbft].

    pose proof (prepares_get_garbage_collected_v2 i eo e1 e2 state1 state2 p) as q.
    repeat (autodimp q hyp); try omega.
  Qed.

  Lemma pre_prepare2digest_as_requests2digests :
    forall v s r a,
      pre_prepare2digest (mk_pre_prepare v s r a)
      = requests2digest r.
  Proof.
    tcsp.
  Qed.

  Lemma pre_prepare2request_data_pre_prepare2digest :
    forall pp,
      pre_prepare2request_data pp (pre_prepare2digest pp)
      = pre_prepare2rd pp.
  Proof.
    destruct pp, b; simpl; tcsp.
  Qed.
  Hint Rewrite pre_prepare2request_data_pre_prepare2digest : pbft.

  Lemma prepared_implies2 :
    forall rd L,
      well_formed_log L
      -> prepared_log rd L = true
      ->
      exists (R : list Rep) (pp : Pre_prepare),
        2 * F <= length R
        /\ no_repeats R
        /\ pre_prepare_in_log pp (pre_prepare2digest pp) L = true
        /\ pre_prepare2rd pp = rd
        /\ forall i,
            In i R
            -> exists rt,
              prepare_in_log (request_data_and_rep_toks2prepare rd rt) L = true
              /\ rt_rep rt = i.
  Proof.
    induction L; introv wf prep; simpl in *; tcsp.
    inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
    smash_pbft;[|].

    - destruct a; simpl in *; smash_pbft;[].
      unfold is_request_data_for_entry, eq_request_data in *; simpl in *; smash_pbft;[].
      destruct log_entry_pre_prepare_info; simpl in *; ginv.

      applydup well_formed_log_entry_prepares in wf1; simpl in *.
      applydup well_formed_log_entry_correct_digest in wf1; simpl in *.

      hide_hyp wf1.
      hide_hyp imp.

      unfold same_digests in *; smash_pbft.

      exists (map rt_rep log_entry_prepares)
             (request_data2pre_prepare rd (map fst reqs) auth).
      autorewrite with pbft list in *.
      dands; auto.

      + smash_pbft.
        destruct rd; simpl in *; autorewrite with pbft in *.
        subst; tcsp.
        fold (mk_pre_prepare v s (map fst reqs) auth) in *.
        rewrite pre_prepare2digest_as_requests2digests in *.
        rewrite requests2digest_map_fst_as_requests_and_replies2digest in n; tcsp.

      + destruct rd; simpl in *; subst.
        rewrite requests2digest_map_fst_as_requests_and_replies2digest; tcsp.

      + introv j.
        allrw in_map_iff; exrepnd; subst.
        exists x; simpl.
        unfold is_prepare_for_entry, eq_request_data; simpl; autorewrite with pbft.
        smash_pbft.
        dands; auto.
        rewrite existsb_exists.
        exists x; dands; auto.
        autorewrite with pbft; auto.

    - repeat (autodimp IHL hyp).
      exrepnd.

      applydup well_formed_log_entry_prepares in wf1; simpl in *.
      applydup well_formed_log_entry_correct_digest in wf1; simpl in *.

      hide_hyp wf1.
      hide_hyp imp.

      exists R pp; dands; auto.

      + smash_pbft.
        destruct a; simpl in *.
        unfold is_request_data_for_entry, eq_request_data in *; simpl in *; smash_pbft.

      + introv j.
        applydup IHL1 in j.
        exrepnd; subst.
        exists rt; simpl; autorewrite with pbft.
        smash_pbft.
        dands; auto.

        unfold is_request_data_for_entry in *.
        unfold is_prepare_for_entry in *.
        unfold eq_request_data in *.
        simpl in *; smash_pbft.
  Qed.

  Lemma request_data2seq_pre_prepare2rd :
    forall pp,
      request_data2seq (pre_prepare2rd pp)
      = pre_prepare2seq pp.
  Proof.
    introv; destruct pp, b; auto.
  Qed.
  Hint Rewrite request_data2seq_pre_prepare2rd : pbft.

  Lemma implies_no_repeats_map_rt_rep_remove_elt :
    forall L x,
      no_repeats (map rt_rep L)
      -> no_repeats (map rt_rep (remove_elt RepToksDeq x L)).
  Proof.
    induction L; introv norep; simpl in *; tcsp.
    inversion norep as [|? ? diff nr]; subst; clear norep.
    smash_pbft;[].
    constructor; tcsp;[].
    introv j.
    destruct diff.
    allrw in_map_iff; exrepnd.
    allrw @in_remove_elt; repnd.
    exists x0; dands; auto.
  Qed.
  Hint Resolve implies_no_repeats_map_rt_rep_remove_elt : pbft.

  Lemma no_repeats_map_rt_rep_implies :
    forall L,
      no_repeats (map rt_rep L)
      -> no_repeats L.
  Proof.
    induction L; introv norep; simpl in *; tcsp.
    inversion norep as [|? ? diff nr]; subst; clear norep.
    constructor; auto.
    introv j; destruct diff.
    allrw in_map_iff.
    eexists; dands; eauto.
  Qed.
  Hint Resolve no_repeats_map_rt_rep_implies : pbft.

  Lemma implies_le_length_of_len_of_reps :
    forall R n L,
      n <= length R
      -> no_repeats R
      -> no_repeats (map rt_rep L)
      -> (forall i, In i R -> exists rt, existsb (same_rep_tok rt) L = true /\ rt_rep rt = i)
      -> n <= length L.
  Proof.
    induction R; introv len norep norep' imp; simpl in *; try omega;[].
    inversion norep as [|? ? diff nr]; subst; clear norep.
    destruct n; try omega.
    assert (n <= length R) as len' by omega.
    pose proof (imp a) as q; autodimp q hyp; exrepnd; subst; simpl in *.
    rewrite existsb_exists in q1; exrepnd.
    unfold same_rep_tok in *; smash_pbft;[].
    pose proof (IHR n (remove_elt RepToksDeq x L)) as h; clear IHR.
    repeat (autodimp h hyp); eauto 3 with pbft;[|].

    {
      introv j.
      pose proof (imp i) as q; autodimp q hyp; exrepnd.
      allrw existsb_exists; exrepnd; smash_pbft.
      destruct (RepToksDeq x x0); subst; tcsp.

      exists x0; dands; auto.
      allrw existsb_exists.
      exists x0; smash_pbft; dands; auto.
      apply in_remove_elt; dands; auto.
    }

    {
      rewrite length_remove_elt_if_no_repeats in h; eauto 3 with pbft.
      smash_pbft; try omega.
      destruct L; simpl in *; try omega.
    }
  Qed.

  Lemma implies_prepared :
    forall R rd pp d L,
      well_formed_log L
      -> 2 * F <= length R
      -> no_repeats R
      -> pre_prepare_in_log pp d L = true
      -> similar_pre_prepare_and_request_data pp d rd = true
      -> (forall i,
             In i R
             -> exists rt,
               prepare_in_log (request_data_and_rep_toks2prepare rd rt) L = true
               /\ rt_rep rt = i)
      -> prepared_log rd L = true.
  Proof.
    induction L; introv wf len norep prep sim imp; simpl in *; tcsp;[].
    inversion wf as [|? ? diff wf1 wf2]; subst; clear wf.
    smash_pbft.

    - destruct a; simpl in *.
      allrw requests_matches_logEntryPrePrepareInfo_true_iff; repnd.
      destruct log_entry_pre_prepare_info; simpl in *; tcsp;[].
      unfold is_request_data_for_entry, eq_request_data in *; simpl in *.
      smash_pbft;[].
      dands; auto; GC;[].

      applydup well_formed_log_entry_prepares in wf1; simpl in *.

      clear diff wf1 IHL sim wf2.

      unfold is_prepare_for_entry in *; simpl in *.

      assert (forall i : Rep,
                 In i R
                 ->
                 exists rt,
                   existsb (same_rep_tok rt) log_entry_prepares = true
                   /\ rt_rep rt = i) as imp'.
      {
        introv k.
        apply imp in k; clear imp.
        exrepnd; autorewrite with pbft in *.
        exists rt; auto.
      }
      clear imp.

      eapply implies_le_length_of_len_of_reps; eauto.

    - clear IHL imp wf1 wf2 diff prep prep0.

      destruct a; simpl in *.
      unfold is_request_data_for_entry in *; simpl in *.
      unfold similar_pre_prepare_and_request_data in *.
      unfold eq_request_data in *; smash_pbft.

    - clear IHL imp wf1 wf2 diff prep.

      destruct a; simpl in *.
      unfold is_request_data_for_entry in *; simpl in *.
      unfold similar_pre_prepare_and_request_data in *.
      unfold eq_request_data in *; smash_pbft.

    - repeat (autodimp IHL hyp).
      introv j.
      applydup imp in j; exrepnd; clear imp.
      autorewrite with pbft in *.
      smash_pbft.

      clear diff wf1 wf2.

      destruct a; simpl in *.
      unfold is_request_data_for_entry in *; simpl in *.
      unfold is_prepare_for_entry in *; simpl in *.
      unfold eq_request_data in *; smash_pbft.
  Qed.

  Lemma prepared_get_garbage_collected :
    forall i (eo : EventOrdering) (e1 e2 : Event) state1 state2 rd,
      e1 ⊏ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> prepared rd state1 = true
      -> prepared rd state2 = false
      -> request_data2seq rd <= low_water_mark state2.
  Proof.
    introv ltes eqst1 eqst2 prep1 prep2.

    destruct (le_dec (request_data2seq rd) (low_water_mark state2)) as [d|d]; tcsp;[].
    rewrite <- not_true_iff_false in prep2; destruct prep2.
    assert (low_water_mark state2 < request_data2seq rd) as ltrd by omega.
    clear d.

    applydup prepared_implies2 in prep1;[|eauto 2 with pbft].
    exrepnd.

    eapply pre_prepares_dont_get_garbage_collected in prep4;
      [| |exact eqst1|exact eqst2|]; auto;
        [|subst;autorewrite with pbft in *; auto];[].

    assert (forall i : Rep,
               In i R
               ->
               exists rt,
                 prepare_in_log (request_data_and_rep_toks2prepare rd rt) (log state2) = true
                 /\ rt_rep rt = i) as imp.
    {
      introv j.
      applydup prep0 in j; exrepnd.
      exists rt; dands; auto.
      eapply prepares_dont_get_garbage_collected in j0;
        [| |exact eqst1|exact eqst2|]; auto; autorewrite with pbft in *; auto.
    }

    hide_hyp prep0.

    eapply implies_prepared;[|eauto|eauto|eauto| |];auto;[eauto 2 with pbft|].
    subst.
    unfold similar_pre_prepare_and_request_data, eq_request_data; smash_pbft.
  Qed.

End PBFT_A_1_9_misc4.


Hint Resolve entry2prepared_info_preserves_request_data : pbft.
Hint Resolve is_prepared_entry_implies_info_is_prepared : pbft.
Hint Resolve entry2prepared_info_some_implies_is_prepared_entry : pbft.
Hint Resolve in_gather_prepared_messages_implies_prepared : pbft.
Hint Resolve entry2prepared_info_some_implies_equal_views : pbft.
Hint Resolve entry2prepared_info_some_implies_equal_seqs : pbft.
Hint Resolve entry2pre_prepare_some_implies_equal_views : pbft.
Hint Resolve entry2pre_prepare_some_implies_equal_seqs : pbft.
Hint Resolve entry2pre_prepare_some_implies_equal_digests : pbft.
Hint Resolve entry2prepared_info_some_implies_equal_digests : pbft.
Hint Resolve add_new_commit2log_preserves_prepared_log_backward : pbft.
Hint Resolve check_stable_preserves_prepared_backward : pbft.
Hint Resolve find_and_execute_requests_preserves_prepared_backward : pbft.
Hint Resolve implies_no_repeats_map_rt_rep_remove_elt : pbft.
Hint Resolve no_repeats_map_rt_rep_implies : pbft.
Hint Resolve prepared_log_check_one_stable_implies : pbft.


Hint Rewrite @pre_prepare2view_prepared_info_pre_prepare : pbft.
Hint Rewrite @request_data2view_prepare_2request_data : pbft.
Hint Rewrite @request_data2view_prepare2request_data : pbft.
Hint Rewrite @request_data2seq_prepare2request_data : pbft.
Hint Rewrite @pre_prepare2request_data_pre_prepare2digest : pbft.
Hint Rewrite @request_data2seq_pre_prepare2rd : pbft.
