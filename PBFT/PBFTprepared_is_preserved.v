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


Require Export PBFTin_log.
Require Export PBFTprops3.
Require Export PBFTcommit_in_log_preserves.


Section PBFTprepared_is_preserved.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma check_send_replies_preserves_prepared_reverse :
    forall rd slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> prepared rd state = true
      -> prepared rd state' = true.
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_prepared_reverse : pbft.

  Lemma check_send_replies_preserves_prepared :
    forall rd slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> prepared rd state' = true
      -> prepared rd state = true.
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_prepared : pbft.

  Lemma check_send_replies_update_log_preserves_prepared_reverse :
    forall state'' rd slf entryop state sn msgs state',
      check_send_replies slf (current_view state) (local_keys state) entryop (update_log state (log state'')) sn = (msgs, state')
      -> prepared rd state' = true
      -> prepared rd state'' = true.
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_prepared_reverse : pbft.

  Lemma check_send_replies_update_log_preserves_prepared :
    forall rd slf view keys  entryop state sn msgs state' state'',
      check_send_replies slf view keys entryop (update_log state (log state'')) sn = (msgs, state')
      -> prepared rd state'' = true
      -> prepared rd state' = true.
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_prepared : pbft.

  Lemma update_ready_preserves_prepared :
    forall rd st l,
      prepared rd (update_ready st l) = true
      -> prepared rd st = true.
  Proof.
    unfold prepared.
    unfold update_ready. simpl in *. tcsp.
  Qed.
  Hint Resolve update_ready_preserves_prepared : pbft.

  Lemma add_replies2entry_preserves_is_prepared_entry :
    forall entry reps,
      is_prepared_entry (add_replies2entry entry reps) = is_prepared_entry entry.
  Proof.
    unfold add_replies2entry.
    induction entry; introv; simpl in *; ginv; simpl in *; smash_pbft;  tcsp.
    unfold add_replies2info.
    destruct log_entry_pre_prepare_info; simpl in *; auto.
  Qed.
  Hint Resolve add_replies2entry_preserves_is_prepared_entry : pbft.

  Lemma change_entry_add_replies2entry_preserves_prepared_log :
    forall entry reps L n rd,
      prepared_log rd (change_entry L (add_replies2entry entry reps)) = true
      -> find_entry L n = Some entry
      -> prepared_log rd L = true.
  Proof.
    induction L; introv h fe; simpl in *; tcsp.
    smash_pbft;
      try (complete (applydup entry2seq_if_find_entry in fe as eqsn;
                     match goal with
                     | [ H : similar_entry _ _ = _ |- _ ] =>
                       apply entry2seq_if_similar_entry in H
                     end;
                     match goal with
                     | [ H : _ <> _ |- _ ] => destruct H; allrw; auto
                     end)).

    { allrw add_replies2entry_preserves_is_prepared_entry; auto. }

    {
      unfold is_request_data_for_entry in *.
      unfold eq_request_data in *. smash_pbft.
    }
    {
      unfold is_request_data_for_entry in *.
      unfold eq_request_data in *. smash_pbft.
    }
  Qed.
  Hint Resolve change_entry_add_replies2entry_preserves_prepared_log : pbft.

  Lemma change_log_entry_add_replies2entry_preserves_prepared_log :
    forall n rd entry state reps,
      prepared_log
        rd
        (log
           (change_log_entry
              state
              (add_replies2entry entry reps))) = true
      -> find_entry (log state) n = Some entry
      -> prepared_log rd (log state) = true.
  Proof.
    introv h fe.
    destruct state; simpl in *.

    eapply change_entry_add_replies2entry_preserves_prepared_log in h;[|eauto].
    auto.
  Qed.
  Hint Resolve change_log_entry_add_replies2entry_preserves_prepared_log : pbft.

  Lemma change_pre_prepare_info_of_entry_preserves_is_prepared_entry :
    forall pp a,
      is_prepared_entry a = true
      -> is_prepared_entry (change_pre_prepare_info_of_entry pp a) = true.
  Proof.
    destruct a; simpl; introv h; smash_pbft; dands; tcsp.
    destruct log_entry_pre_prepare_info; simpl in *; tcsp.
  Qed.
  Hint Resolve change_pre_prepare_info_of_entry_preserves_is_prepared_entry : pbft.

  Lemma implies_prepared_log_add_new_pre_prepare2log :
    forall rd pp d L,
      prepared_log rd L = true
      -> prepared_log rd (add_new_pre_prepare2log pp d L) = true.
  Proof.
    induction L; introv h; simpl in *; tcsp; smash_pbft;
      unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
  Qed.
  Hint Resolve implies_prepared_log_add_new_pre_prepare2log : pbft.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_prepared_log :
    forall rd L K pp d Fp Fc giop slf,
      add_new_pre_prepare_and_prepare2log slf L pp d Fp Fc = (giop, K)
      -> prepared_log rd L = true
      -> prepared_log rd K = true.
  Proof.
    induction L; introv add prep; repeat (progress (simpl in *; smash_pbft));
      try (unfold is_request_data_for_entry, eq_request_data in *; smash_pbft;
           allrw similar_entry_and_pre_prepare_true_iff;
           allrw similar_entry_and_pre_prepare_false_iff;
           try (rename_hyp_with fill_out_pp_info_with_prepare fill);
           try (apply fill_out_pp_info_with_prepare_preserves_request_data in fill);
           congruence).

    unfold fill_out_pp_info_with_prepare in *; destruct a; smash_pbft.
  Qed.
  Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_prepared_log : pbft.

  Lemma add_new_prepare2log_preserves_prepared_log :
    forall rd L K pp Fc giop slf,
      add_new_prepare2log slf L pp Fc = (giop, K)
      -> prepared_log rd L = true
      -> prepared_log rd K = true.
  Proof.
    induction L; introv add prep; repeat (progress (simpl in *; smash_pbft));
      try (unfold is_request_data_for_entry, eq_request_data in *; smash_pbft;
           try (rename_hyp_with add_prepare2entry add);
           try (apply gi_entry_of_add_prepare2entry_some in add);
           congruence);[].

    unfold add_prepare2entry in *; destruct a; smash_pbft.
    dands; auto.
    unfold add_prepare_if_not_enough in *; smash_pbft; try omega.
  Qed.
  Hint Resolve add_new_prepare2log_preserves_prepared_log : pbft.

  Lemma change_entry_add_replies2entry_preserves_prepared_log_backward :
    forall rd L entry reps,
      well_formed_log L
      -> In entry L
      -> prepared_log rd L = true
      -> prepared_log rd (change_entry L (add_replies2entry entry reps)) = true.
  Proof.
    induction L; introv wf i prep; simpl in *; smash_pbft.

    - inversion wf as [|? ? imp wfe wfl]; subst; clear wf.
      repndors; subst; tcsp.

      + destruct entry; simpl in *; smash_pbft; dands; auto.
        destruct log_entry_pre_prepare_info; simpl in *; auto.

      + apply imp in i.
        unfold entries_have_different_request_data in *.
        unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.

    - inversion wf as [|? ? imp wfe wfl]; subst; clear wf.
      repndors; subst; tcsp.

      + destruct entry; simpl in *; smash_pbft; dands; auto.
        unfold is_request_data_for_entry, eq_request_data in *; simpl in *; smash_pbft.

      + apply imp in i.
        unfold entries_have_different_request_data in *.
        unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
        allrw similar_entry_true_iff; tcsp.

    - inversion wf as [|? ? imp wfe wfl]; subst; clear wf.
      repndors; subst; tcsp.

      + unfold is_request_data_for_entry, eq_request_data in *; simpl in *; smash_pbft.

      + apply imp in i.
        unfold entries_have_different_request_data in *.
        unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
        allrw similar_entry_true_iff; tcsp.

    - inversion wf as [|? ? imp wfe wfl]; subst; clear wf.
      repndors; subst; tcsp.

      unfold is_request_data_for_entry, eq_request_data in *; simpl in *; smash_pbft.
  Qed.
  Hint Resolve change_entry_add_replies2entry_preserves_prepared_log_backward : pbft.

  Lemma find_and_execute_requests_preserves_prepared :
    forall msg i s1 s2 rd v keys,
      well_formed_log (log s1)
      -> find_and_execute_requests i v keys s1 = (msg, s2)
      -> prepared rd s1 = true
      -> prepared rd s2 = true.
  Proof.
    introv wf find prep.

    unfold find_and_execute_requests in *; smash_pbft.
    unfold execute_requests in *.
    destruct (ready s1); simpl in *;smash_pbft.

    unfold prepared in *; simpl.

    rename_hyp_with check_broadcast_checkpoint check.
    apply check_broadcast_checkpoint_preserves_log in check; simpl in check.
    rewrite <- check.

    rename_hyp_with find_entry fentry.
    apply find_entry_implies_in in fentry.
    eauto 2 with pbft.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_prepared : pbft.

  Lemma add_new_commit2log_preserves_prepared_log :
    forall rd L K com gi,
      add_new_commit2log L com = (gi, K)
      -> prepared_log rd L = true
      -> prepared_log rd K = true.
  Proof.
    induction L; introv IH1 IH2; repeat (simpl in *; ginv; smash_pbft; tcsp);
      try (complete (unfold is_request_data_for_entry in *;
                     unfold eq_request_data in *; smash_pbft;
                     unfold is_prepared_entry in *;
                     destruct a; simpl in *; smash_pbft)).
  Qed.
  Hint Resolve add_new_commit2log_preserves_prepared_log : pbft.

  Lemma entry_of_prepared_log :
    forall rd L,
      prepared_log rd L = true
      -> exists entry,
        In entry L
        /\ log_entry_request_data entry = rd.
  Proof.
    induction L; introv h; simpl in *; tcsp; smash_pbft.

    - exists a; dands; tcsp.
      unfold is_request_data_for_entry in *. unfold eq_request_data in *. smash_pbft.

    - apply IHL in h; exrepnd; exists entry; auto.
  Qed.
  (*Hint Rewrite entry_of_prepared_log : pbft.*)

  Lemma clear_log_checkpoint_preserves_prepared_log :
    forall rd L sn,
      well_formed_log L
      -> prepared_log rd (clear_log_checkpoint L sn) = true
      -> prepared_log rd L = true.
    Proof.
      induction L; simpl in *; introv wf h; tcsp.
      smash_pbft.

      - assert False; tcsp.

      inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.

      allrw is_commit_for_entry_true_iff.

      match goal with
      | [ H : prepared_log _ _ = _ |- _ ] => apply entry_of_prepared_log in H
      end.
      exrepnd.
      pose proof (imp entry) as q; autodimp q hyp; apply q; auto.
      allrw; auto.
      unfold is_request_data_for_entry in *. unfold eq_request_data in *. smash_pbft.

    - inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.

    - inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.
  Qed.
  Hint Resolve clear_log_checkpoint_preserves_prepared_log : pbft.

  Lemma clear_log_checkpoint_preserves_prepared_log_reverse :
    forall rd L (sn : SeqNum),
      sn < request_data2seq rd
      -> prepared_log rd L = true
      -> prepared_log rd (clear_log_checkpoint L sn) = true.
  Proof.
    induction L; introv h prep; simpl in *; smash_pbft.
    unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
    destruct a; simpl in *; omega.
  Qed.

  Lemma check_stable_preserves_prepared_reverse :
    forall rd slf state entry state',
      well_formed_log (log state)
      -> check_stable slf state entry = Some state'
      -> prepared rd state' = true
      -> prepared rd state = true.
  Proof.
    introv wf h q.
    unfold check_stable in h; smash_pbft.
    unfold prepared in *.
    apply clear_log_checkpoint_preserves_prepared_log in q; auto.
  Qed.
  Hint Resolve check_stable_preserves_prepared_reverse : pbft.

  Lemma add_new_checkpoint2cp_state_preserves_prepared :
    forall p x1 x0 rd c sm lastr,
      add_new_checkpoint2cp_state (cp_state p) sm lastr c = (x0, x1)
      -> prepared rd p = true
      -> prepared rd (update_checkpoint_state p x1) = true.
  Proof.
    unfold add_new_checkpoint2cp_state. smash_pbft.
  Qed.
  Hint Resolve add_new_checkpoint2cp_state_preserves_prepared : pbft.

  Lemma add_new_checkpoint2cp_state_preserves_prepared_reverse :
    forall p x1 x0 rd c sm lastr,
      add_new_checkpoint2cp_state (cp_state p) sm lastr c = (x0, x1)
      -> prepared rd (update_checkpoint_state p x1) = true
      -> prepared rd p = true.
  Proof.
    unfold add_new_checkpoint2cp_state. smash_pbft.
  Qed.
  Hint Resolve add_new_checkpoint2cp_state_preserves_prepared_reverse : pbft.

  Lemma update_checkpoint_from_new_view_preserves_prepared :
    forall state s maxV rd,
      prepared rd (update_checkpoint_from_new_view state s maxV) = prepared rd state.
  Proof.
    introv; unfold update_checkpoint_from_new_view. smash_pbft.
  Qed.
  Hint Rewrite update_checkpoint_from_new_view_preserves_prepared : pbft.

  Lemma trim_checkpoint_preserves_prepared :
    forall state chkop rd,
      prepared rd (trim_checkpoint state chkop) = prepared rd state.
  Proof.
    introv; unfold trim_checkpoint; simpl; auto.
  Qed.
  Hint Rewrite trim_checkpoint_preserves_prepared : pbft.

  Lemma update_log_preserves_prepared_log :
    forall rd L p,
      prepared_log rd (log (update_log p L)) = true
      -> prepared_log rd L = true.
  Proof.
    unfold update_log. simpl in *. auto.
  Qed.
  Hint Resolve update_log_preserves_prepared_log : pbft.

  Lemma update_log_preserves_prepared_log_reverse :
    forall rd L p,
      prepared_log rd L = true
      -> prepared_log rd (log (update_log p L)) = true.
  Proof.
    unfold update_log. simpl in *. auto.
  Qed.
  Hint Resolve update_log_preserves_prepared_log_reverse : pbft.

  Lemma update_state_new_view_preserves_prepared :
    forall i st nv st' msgs rd,
      well_formed_log (log st)
      -> update_state_new_view i st nv = (st', msgs)
      -> prepared rd st' = true
      -> prepared rd st = true.
  Proof.
    introv wf u h.
    unfold update_state_new_view in *. smash_pbft.
    unfold prepared in *.
    eapply update_log_preserves_prepared_log in h; eauto.

    rename_hyp_with log_checkpoint_cert_from_new_view H1.
    eapply log_checkpoint_cert_from_new_view_preserves_log in H1.
    rewrite <- H1 in *. clear H1.
    eapply clear_log_checkpoint_preserves_prepared_log in h; eauto.
  Qed.
  Hint Resolve update_state_new_view_preserves_prepared : pbft.

  Lemma update_state_new_view_preserves_prepared_reverse :
    forall i st nv st' msgs rd,
      well_formed_log (log st)
      -> correct_new_view nv = true
      -> update_state_new_view i st nv = (st', msgs)
      -> prepared rd st = true
      -> prepared rd st' = true
         \/
         (
           request_data2seq rd <= low_water_mark st'
           /\ low_water_mark st < low_water_mark st'
         ).
  Proof.
    introv wf cor u h.
    clear wf.
    unfold update_state_new_view in *; smash_pbft;[].
    unfold prepared in *; simpl in *.

    unfold log_checkpoint_cert_from_new_view in *; simpl in *.
    smash_pbft; simpl in *.

    - unfold low_water_mark in *; simpl.

      rename_hyp_with view_change_cert2max_seq_vc maxs.
      applydup view_change_cert2_max_seq_vc_some_in in maxs.
      applydup sn_of_view_change_cert2max_seq_vc in maxs.
      subst.

      destruct (lt_dec (view_change2seq x2) (request_data2seq rd)) as [d|d].

      { left; apply clear_log_checkpoint_preserves_prepared_log_reverse; auto. }

      rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext;
        eauto 3 with pbft.
      subst; simpl in *; right; simpl; dands; try omega.

    - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      apply extract_seq_and_digest_from_checkpoint_certificate_none_implies in ext.
      rewrite ext in *.
      simpl in *; ginv.

    - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft;[].
      subst.
      unfold low_water_mark in *; simpl in *.

      rename_hyp_with view_change_cert2max_seq_vc maxs.
      applydup view_change_cert2_max_seq_vc_some_in in maxs.
      applydup sn_of_view_change_cert2max_seq_vc in maxs.
      subst.

      destruct (lt_dec (view_change2seq x2) (request_data2seq rd)) as [d|d].

      { left; apply clear_log_checkpoint_preserves_prepared_log_reverse; auto. }

      simpl in *; right; omega.

    - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      apply extract_seq_and_digest_from_checkpoint_certificate_none_implies in ext.

      rename_hyp_with view_change_cert2max_seq_vc maxs.
      applydup view_change_cert2_max_seq_vc_some_in in maxs.
      applydup sn_of_view_change_cert2max_seq_vc in maxs.
      subst.

      assert (correct_view_change (new_view2view nv) x2 = true) as cvc by eauto 3 with pbft;[].
      unfold correct_view_change, correct_view_change_cert in cvc; smash_pbft.
      rewrite ext in *.
      simpl in *; ginv; try omega.
  Qed.
  (*Hint Rewrite update_state_new_view_preserves_prepared_reverse : pbft.*)

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_prepared_forward :
    forall slf rd state pp d state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state (pp, d) = (state', msgs)
      -> prepared rd state = true
      -> prepared rd state' = true.
  Proof.
    introv h q.
    unfold add_prepare_to_log_from_new_view_pre_prepare in h.
    smash_pbft.
    rename_hyp_with check_send_replies check.
    eapply check_send_replies_preserves_prepared_reverse in check; eauto 3 with pbft.
    unfold prepared in *.
    eauto 3 with pbft.
  Qed.
  Hint Resolve  add_prepare_to_log_from_new_view_pre_prepare_preserves_prepared_forward : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_prepared_log_forward :
    forall slf rd pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> prepared rd state = true
      -> prepared rd state' = true.
  Proof.
    induction pps; introv h q; simpl in *; smash_pbft; repnd.
    eapply IHpps; eauto with pbft.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_prepared_log_forward : pbft.

  Lemma log_pre_prepares_preserves_prepared_log :
    forall rd P L lwm,
      prepared_log rd L = true
      -> prepared_log rd (log_pre_prepares L lwm P) = true.
  Proof.
    induction P; introv h; simpl in *; tcsp; repnd; smash_pbft.
  Qed.
  Hint Resolve log_pre_prepares_preserves_prepared_log : pbft.

  Lemma check_send_replies_update_log_preserves_prepared2 :
    forall rd slf view keys  entryop state sn msgs state' L,
      check_send_replies slf view keys entryop (update_log state L) sn = (msgs, state')
      -> prepared_log rd L = true
      -> prepared rd state' = true.
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_prepared2 : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_prepared_log :
    forall i rd ppd s1 s2 msgs,
      add_prepare_to_log_from_new_view_pre_prepare i s1 ppd = (s2, msgs)
      -> prepared_log rd (log s1) = true
      -> prepared_log rd (log s2) = true.
  Proof.
    introv add prep.
    unfold add_prepare_to_log_from_new_view_pre_prepare in add; smash_pbft.
    rename_hyp_with check_send_replies check.
    rename_hyp_with add_new_pre_prepare_and_prepare2log add.
    eapply add_new_pre_prepare_and_prepare2log_preserves_prepared_log in add;[|eauto].
    eapply check_send_replies_update_log_preserves_prepared2 in check; eauto.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_prepared_log : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_prepared_log :
    forall i rd pps s1 s2 msgs,
      add_prepares_to_log_from_new_view_pre_prepares i s1 pps = (s2, msgs)
      -> prepared_log rd (log s1) = true
      -> prepared_log rd (log s2) = true.
  Proof.
    induction pps; introv add prep; simpl in *; smash_pbft.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_prepared_log : pbft.

  (* should we move this one to PBFTcommit_in_log_preserves? *)
  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log2 :
    forall slf com pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> commit_in_log com (log state') = true
      -> commit_in_log com (log state) = true
         \/
         (
           exists pp d,
             In (pp,d) pps
             /\ com
                = request_data_and_rep_toks2commit
                    (pre_prepare2request_data pp d)
                    (pre_prepare2rep_toks_of_commit slf (local_keys state) pp d)
             /\ low_water_mark state < pre_prepare2seq pp
             /\ prepared_log (pre_prepare2request_data pp d) (log state') = true
             /\ commit_in_log com (log state) = false).
  Proof.
    induction pps; introv h q; simpl in *; smash_pbft; repnd.

    match goal with
    | [ H : add_prepares_to_log_from_new_view_pre_prepares _ _ _ = _ |- _ ] =>
      applydup IHpps in H;auto;[]
    end.
    repndors; tcsp.

    {
      match goal with
      | [ H : add_prepare_to_log_from_new_view_pre_prepare _ _ _ = _ |- _ ] =>
        eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_commit_in_log in H;[|eauto]
      end.

      repndors; tcsp; subst.

      exrepnd.
      right.
      exists a0 a; dands; auto; eauto 3 with pbft.
    }

    {
      exrepnd; subst.
      right.

      rename_hyp_with add_prepare_to_log_from_new_view_pre_prepare add.
      applydup add_prepare_to_log_from_new_view_pre_prepare_preserves_cp_state in add.
      apply eq_low_water_marks_if_eq_cp_states in add0.
      rewrite <- add0.

      exists pp d; dands; tcsp; eauto 3 with pbft.

      match goal with
      | [ H : add_prepare_to_log_from_new_view_pre_prepare _ _ _ = _ |- _ ] =>
        apply add_prepare_to_log_from_new_view_pre_prepare_preserves_local_keys in H
      end.
      allrw; auto.
    }
  Qed.
  (*Hint Rewrite add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log2 : pbft.*)

End PBFTprepared_is_preserved.


Hint Resolve check_send_replies_preserves_prepared_reverse : pbft.
Hint Resolve check_send_replies_preserves_prepared : pbft.
Hint Resolve check_send_replies_update_log_preserves_prepared_reverse : pbft.
Hint Resolve check_send_replies_update_log_preserves_prepared : pbft.
Hint Resolve add_replies2entry_preserves_is_prepared_entry : pbft.
Hint Resolve change_pre_prepare_info_of_entry_preserves_is_prepared_entry : pbft.
Hint Resolve implies_prepared_log_add_new_pre_prepare2log : pbft.
Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_prepared_log : pbft.
Hint Resolve add_new_prepare2log_preserves_prepared_log : pbft.
Hint Resolve change_entry_add_replies2entry_preserves_prepared_log_backward : pbft.
Hint Resolve find_and_execute_requests_preserves_prepared : pbft.
Hint Resolve add_new_commit2log_preserves_prepared_log : pbft.
Hint Resolve  add_prepare_to_log_from_new_view_pre_prepare_preserves_prepared_forward : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_prepared_log_forward : pbft.
Hint Resolve check_send_replies_update_log_preserves_prepared2 : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_prepared_log : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_prepared_log : pbft.
Hint Resolve update_ready_preserves_prepared : pbft.
Hint Resolve change_entry_add_replies2entry_preserves_prepared_log : pbft.
Hint Resolve change_log_entry_add_replies2entry_preserves_prepared_log : pbft.
Hint Resolve clear_log_checkpoint_preserves_prepared_log : pbft.
Hint Resolve check_stable_preserves_prepared_reverse : pbft.
Hint Resolve add_new_checkpoint2cp_state_preserves_prepared : pbft.
Hint Resolve add_new_checkpoint2cp_state_preserves_prepared_reverse : pbft.
Hint Resolve update_log_preserves_prepared_log : pbft.
Hint Resolve update_log_preserves_prepared_log_reverse : pbft.
Hint Resolve update_state_new_view_preserves_prepared : pbft.
Hint Resolve log_pre_prepares_preserves_prepared_log : pbft.


Hint Rewrite @update_checkpoint_from_new_view_preserves_prepared : pbft.
Hint Rewrite @trim_checkpoint_preserves_prepared : pbft.
(*Hint Rewrite @add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log2 : pbft.*)
(*Hint Rewrite @entry_of_prepared_log : pbft.*)
