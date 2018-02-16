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


Section PBFTprops2.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Hint Resolve implies_authenticated_messages_were_sent_non_byz_usys : pbft.

  Lemma is_prepare_for_entry_true_implies :
    forall entry p,
      is_prepare_for_entry entry p = true
      -> log_entry_request_data entry = prepare2request_data p.
  Proof.
    introv h.
    unfold is_prepare_for_entry, eq_request_data in h.
    dest_cases w.
  Qed.

  Lemma is_prepare_for_entry_false_implies :
    forall entry p,
      is_prepare_for_entry entry p = false
      -> log_entry_request_data entry <> prepare2request_data p.
  Proof.
    introv h.
    unfold is_prepare_for_entry, eq_request_data in h.
    dest_cases w.
  Qed.

  Lemma sequence_number_update_timestamp :
    forall st c t,
      sequence_number (update_timestamp_op st c t)
      = sequence_number st.
  Proof.
    destruct c; introv; simpl; auto.
  Qed.
  Hint Rewrite sequence_number_update_timestamp : pbft.

  Lemma check_send_replies_preserves_log :
    forall slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> log state' = log state.
  Proof.
    introv e.
    unfold check_send_replies in e.
    smash_pbft.
    destruct x.
    smash_pbft.
  Qed.

  Lemma check_send_replies_preserves_keys :
    forall slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> local_keys state' = local_keys state.
  Proof.
    introv e.
    unfold check_send_replies in e.
    pbft_dest_all w.
    destruct w.
    pbft_dest_all w.
  Qed.

  Lemma add_commit2entry_preserves_log_entry_pre_prepare_info :
    forall entry1 entry2 c,
      add_commit2entry entry1 c = Some entry2
      -> log_entry_pre_prepare_info entry1 = log_entry_pre_prepare_info entry2.
  Proof.
    introv h.
    unfold add_commit2entry in h.
    destruct entry1; simpl in *.
    dest_cases w.
  Qed.


  Lemma add_commit2entry_preserves_log_entry_prepares :
    forall entry1 entry2 c,
      add_commit2entry entry1 c = Some entry2
      -> log_entry_prepares entry1 = log_entry_prepares entry2.
  Proof.
    introv h.
    unfold add_commit2entry in h.
    destruct entry1; simpl in *.
    dest_cases w.
  Qed.

  Lemma add_commit2entry_preserves_is_prepare_for_entry :
    forall p entry1 entry2 c,
      add_commit2entry entry1 c = Some entry2
      -> is_prepare_for_entry entry1 p = is_prepare_for_entry entry2 p.
  Proof.
    introv h.
    unfold add_commit2entry in h.
    destruct entry1; simpl in *.
    dest_cases w.
  Qed.

  Definition entries_have_different_request_data
             (entry1 entry2 : PBFTlogEntry) : Prop :=
    log_entry_request_data entry1 <> log_entry_request_data entry2.

  Definition entries_have_same_request_data
             (entry1 entry2 : PBFTlogEntry) : Prop :=
    log_entry_request_data entry1 = log_entry_request_data entry2.

  Lemma log_update_checkpoint_state :
    forall state cpstate, log (update_checkpoint_state state cpstate) = log state.
  Proof.
    destruct state; simpl; tcsp.
  Qed.
  Hint Rewrite log_update_checkpoint_state : pbft.

  Lemma check_stable_preserves_keys :
    forall slf state entryop state',
      check_stable slf state entryop = Some state'
      -> local_keys state' = local_keys state.
  Proof.
    introv h.
    unfold check_stable in h.
    pbft_dest_all x.
  Qed.

  Lemma log_entry_request_data_of_change_pre_prepare_info_of_entry :
    forall pp entry,
      log_entry_request_data (change_pre_prepare_info_of_entry pp entry)
      = log_entry_request_data entry.
  Proof.
    introv; destruct entry; simpl in *; tcsp.
  Qed.
  Hint Rewrite log_entry_request_data_of_change_pre_prepare_info_of_entry : pbft.

  Lemma similar_entry_and_pre_prepare_same_pre_prepare2entry :
    forall pp d,
      similar_entry_and_pre_prepare (pre_prepare2entry pp d) pp d = true.
  Proof.
    introv.
    unfold similar_entry_and_pre_prepare, pre_prepare2entry, eq_request_data.
    pbft_dest_all x.
  Qed.
  Hint Rewrite similar_entry_and_pre_prepare_same_pre_prepare2entry : pbft.

  Lemma similar_entry_and_pre_prepare_true_iff :
    forall entry pp d,
      similar_entry_and_pre_prepare entry pp d = true
      <-> log_entry_request_data entry = pre_prepare2request_data pp d.
  Proof.
    introv.
    unfold similar_entry_and_pre_prepare, eq_request_data;
      destruct entry; simpl in *; pbft_dest_all x; split; tcsp.
  Qed.

  Lemma similar_entry_and_pre_prepare_false_iff :
    forall entry pp d,
      similar_entry_and_pre_prepare entry pp d = false
      <-> log_entry_request_data entry <> pre_prepare2request_data pp d.
  Proof.
    introv.
    unfold similar_entry_and_pre_prepare, eq_request_data;
      destruct entry; simpl in *; pbft_dest_all x; split; tcsp.
  Qed.

  Lemma entry_in_add_new_pre_prepare2log_implies :
    forall entry pp d L,
      In entry (add_new_pre_prepare2log pp d L)
      -> In entry L
         \/ similar_entry_and_pre_prepare entry pp d = true.
  Proof.
    induction L; introv i; simpl in *; tcsp; repndors; subst;
      autorewrite with pbft in *; tcsp.

    pbft_dest_all x; repndors; subst; tcsp.

    unfold similar_entry_and_pre_prepare, eq_request_data in *.
    destruct a; simpl in *.
    pbft_dest_all x.
    (* FIX: how did it get that? *)
  Qed.

  Lemma gi_entry_of_fill_out_pp_info_with_prepare_some :
    forall i entry pp Fp Fc gi,
      fill_out_pp_info_with_prepare i entry pp Fp Fc = Some gi
      -> log_entry_request_data (gi_entry gi) = log_entry_request_data entry.
  Proof.
    introv h.
    destruct entry; simpl in *.
    destruct log_entry_pre_prepare_info; simpl in *; ginv.
    pbft_dest_all x.
  Qed.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_request_data :
    forall i L pp d Fp Fc giop K entry,
      add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> In entry K
      -> (exists entry',
             In entry' L
             /\ log_entry_request_data entry = log_entry_request_data entry')
         \/
         similar_entry_and_pre_prepare entry pp d = true.
  Proof.
    induction L; introv h j; simpl in *.

    { pbft_simplifier; simpl in *; repndors; tcsp; subst; simpl in *.
      unfold eq_request_data; pbft_dest_all x. }

    { pbft_dest_all x; repndors; subst; simpl in *; tcsp;
        try (complete (left; exists entry; tcsp)).

      - match goal with
        | [ H : fill_out_pp_info_with_prepare _ _ _ _ _ = _ |- _ ] =>
          apply gi_entry_of_fill_out_pp_info_with_prepare_some in H
        end; simpl in *.
        allrw similar_entry_and_pre_prepare_true_iff.
        right; allrw; auto.

      - match goal with
        | [ H : add_new_pre_prepare_and_prepare2log _ _ _ _ _ _ = _ |- _ ] =>
          eapply IHL in H;[|eauto]
        end.
        repndors; exrepnd; tcsp.
        left.
        exists entry'; dands; tcsp. }
  Qed.

  Lemma gi_entry_of_add_prepare2entry_some :
    forall i entry p Fc gi,
      add_prepare2entry i entry p Fc = Some gi
      -> log_entry_request_data (gi_entry gi) = log_entry_request_data entry.
  Proof.
    introv h.
    destruct entry; simpl in *.
    pbft_dest_all x.
  Qed.

  Lemma is_prepare_for_entry_true_iff :
    forall entry p,
      is_prepare_for_entry entry p = true
      <-> log_entry_request_data entry = prepare2request_data p.
  Proof.
    introv.
    unfold is_prepare_for_entry, eq_request_data;
      destruct entry; simpl in *; pbft_dest_all x; split; tcsp.
  Qed.

  Lemma is_prepare_for_entry_false_iff :
    forall entry p,
      is_prepare_for_entry entry p = false
      <-> log_entry_request_data entry <> prepare2request_data p.
  Proof.
    introv.
    unfold is_prepare_for_entry, eq_request_data;
      destruct entry; simpl in *; pbft_dest_all x; split; tcsp.
  Qed.

  Lemma add_new_prepare2log_preserves_request_data :
    forall slf L p Fc giop K entry,
      add_new_prepare2log slf L p Fc = (giop, K)
      -> In entry K
      -> (exists entry',
             In entry' L
             /\ log_entry_request_data entry = log_entry_request_data entry')
         \/ is_prepare_for_entry entry p = true.
  Proof.
    induction L; introv h i; repeat (simpl in *; smash_pbft); repndors; subst; tcsp;
      try (complete (unfold is_prepare_for_entry, eq_request_data; simpl; smash_pbft));
      try (complete (left; exists entry; tcsp)).

    - match goal with
      | [ H : add_prepare2entry _ _ _ _ = _ |- _ ] =>
        apply gi_entry_of_add_prepare2entry_some in H
      end; simpl in *.

      allrw is_prepare_for_entry_true_iff.
      allrw; tcsp.

    - match goal with
      | [ H : add_new_prepare2log _ _ _ _ = _ |- _ ] =>
        eapply IHL in H;[|eauto]
      end.
      repndors; exrepnd; tcsp.
      left.
      exists entry'; dands; tcsp.
  Qed.

  Lemma gi_entry_of_add_commit2entry_some :
    forall entry c gi,
      add_commit2entry entry c = Some gi
      -> log_entry_request_data gi = log_entry_request_data entry.
  Proof.
    introv h.
    destruct entry; simpl in *.
    pbft_dest_all x.
  Qed.

  Lemma is_commit_for_entry_true_iff :
    forall entry c,
      is_commit_for_entry entry c = true
      <-> log_entry_request_data entry = commit2request_data c.
  Proof.
    introv.
    unfold is_commit_for_entry, eq_request_data; destruct entry; simpl in *;
      pbft_dest_all x; split; tcsp.
  Qed.

  Lemma is_commit_for_entry_false_iff :
    forall entry c,
      is_commit_for_entry entry c = false
      <-> log_entry_request_data entry <> commit2request_data c.
  Proof.
    introv.
    unfold is_commit_for_entry, eq_request_data; destruct entry; simpl in *;
      pbft_dest_all x; split; tcsp.
  Qed.

  Lemma add_new_commit2log_preserves_request_data :
    forall L c giop K entry,
      add_new_commit2log L c = (giop, K)
      -> In entry K
      -> (exists entry',
             In entry' L
             /\ log_entry_request_data entry = log_entry_request_data entry')
         \/ is_commit_for_entry entry c = true.
  Proof.
    induction L; introv h i; simpl in *.

    { pbft_simplifier; simpl in *; repndors; tcsp; subst; simpl in *.
      unfold is_commit_for_entry, eq_request_data; simpl; pbft_dest_all x. }

    { pbft_dest_all x; repndors; subst; simpl in *; tcsp;
        try (complete (left; exists entry; tcsp)).

      - match goal with
        | [ H : add_commit2entry _ _ = _ |- _ ] =>
          apply gi_entry_of_add_commit2entry_some in H
        end; simpl in *.

        allrw is_commit_for_entry_true_iff.
        allrw; tcsp.

      - match goal with
        | [ H : add_new_commit2log _ _ = _ |- _ ] =>
          eapply IHL in H;[|eauto]
        end.
        repndors; exrepnd; tcsp.
        left.
        exists entry'; dands; tcsp. }
  Qed.

  Lemma in_clear_log_checkpoint_implies :
    forall entry L sn,
      In entry (clear_log_checkpoint L sn)
      -> In entry L.
  Proof.
    induction L; introv i; simpl in *; tcsp.
    pbft_dest_all x.
    - apply IHL in i; auto.
    - repndors; tcsp.
      apply IHL in i; auto.
  Qed.

  Lemma log_decrement_requests_in_progress_if_primary :
    forall i v state,
      log (decrement_requests_in_progress_if_primary i v state) = log state.
  Proof.
    introv; unfold decrement_requests_in_progress_if_primary; pbft_dest_all x.
  Qed.
  Hint Rewrite log_decrement_requests_in_progress_if_primary : pbft.

  Lemma similar_entry_true_iff :
    forall entry1 entry2,
      similar_entry entry1 entry2 = true
      <-> entries_have_same_request_data entry1 entry2.
  Proof.
    introv; unfold similar_entry, eq_request_data; pbft_dest_all x; split; intro w; tcsp.
  Qed.

  Lemma similar_entry_false_iff :
    forall entry1 entry2,
      similar_entry entry1 entry2 = false
      <-> entries_have_different_request_data entry1 entry2.
  Proof.
    introv; unfold similar_entry, entries_have_different_request_data, eq_request_data;
      pbft_dest_all x; split; intro w; tcsp.
  Qed.

  Lemma in_change_entry_implies :
    forall entry' L entry,
      In entry' (change_entry L entry)
      -> In entry' L \/ entry' = entry.
  Proof.
    induction L; simpl in *; introv i; tcsp.
    pbft_dest_all x; repndors; subst; tcsp.
    apply IHL in i; repndors; tcsp.
  Qed.

  Lemma change_last_reply_state_preserves_log :
    forall state lastr, log (change_last_reply_state state lastr) = log state.
  Proof.
    introv; destruct state; simpl; auto.
  Qed.
  Hint Rewrite change_last_reply_state_preserves_log : pbft.

  Lemma change_sm_state_preserves_log :
    forall state smst, log (change_sm_state state smst) = log state.
  Proof.
    introv; destruct state; simpl; auto.
  Qed.
  Hint Rewrite change_sm_state_preserves_log : pbft.

  Lemma increment_next_to_execute_preserves_log :
    forall state, log (increment_next_to_execute state) = log state.
  Proof.
    introv; destruct state; simpl; auto.
  Qed.
  Hint Rewrite increment_next_to_execute_preserves_log : pbft.

  Lemma log_checkpoint_cert_from_new_view_preserves_log :
    forall slf state v maxV C s state' chkop,
      log_checkpoint_cert_from_new_view slf state v maxV C s = (state', chkop)
      -> log state = log state'.
  Proof.
    introv h; unfold log_checkpoint_cert_from_new_view in h.
    pbft_dest_all x.
  Qed.

  Lemma update_checkpoint_from_new_view_preserves_log :
    forall state s maxV,
      log (update_checkpoint_from_new_view state s maxV) = log state.
  Proof.
    introv; unfold update_checkpoint_from_new_view.
    pbft_dest_all x.
  Qed.
  Hint Rewrite update_checkpoint_from_new_view_preserves_log : pbft.

  Lemma trim_checkpoint_preserves_log :
    forall state chkop,
      log (trim_checkpoint state chkop) = log state.
  Proof.
    introv; unfold trim_checkpoint; simpl; auto.
  Qed.
  Hint Rewrite trim_checkpoint_preserves_log : pbft.

  Lemma check_stable_preserves_local_keys :
    forall i s eop s',
      check_stable i s eop = Some s'
      -> local_keys s' = local_keys s.
  Proof.
    introv check; unfold check_stable in check; smash_pbft.
  Qed.
  Hint Resolve check_stable_preserves_local_keys : pbft.

  Lemma local_keys_on_check_stable :
    forall i s eop,
      local_keys (on_check_stable i s eop) = local_keys s.
  Proof.
    introv; unfold on_check_stable; smash_pbft.
  Qed.
  Hint Rewrite local_keys_on_check_stable : pbft.

  Lemma check_broadcast_checkpoint_preserves_keys:
    forall slf sn view keys msgs state1 state2,
      check_broadcast_checkpoint slf sn view keys state1 = (state2, msgs)
      -> local_keys state1 = local_keys state2.
  Proof.
    introv h; unfold check_broadcast_checkpoint in h; smash_pbft.
  Qed.

  Lemma check_broadcast_checkpoint_preserves_log:
    forall slf sn view keys msgs state1 state2,
      check_broadcast_checkpoint slf sn view keys state1 = (state2, msgs)
      -> log state1 = log state2.
  Proof.
    introv h; unfold check_broadcast_checkpoint in h; smash_pbft.
  Qed.

  Lemma rep_toks_matches_logEntryPrePrepareInfo_log_entry_pre_prepare_info_add_replies2entry_right :
    forall rt slf entry reps,
      rep_toks_matches_logEntryPrePrepareInfo
        rt slf
        (log_entry_pre_prepare_info (add_replies2entry entry reps))
      = rep_toks_matches_logEntryPrePrepareInfo
          rt slf
          (log_entry_pre_prepare_info entry).
  Proof.
    introv; unfold rep_toks_matches_logEntryPrePrepareInfo.
    destruct entry; simpl.
    destruct log_entry_pre_prepare_info; simpl; auto.
  Qed.
  Hint Rewrite rep_toks_matches_logEntryPrePrepareInfo_log_entry_pre_prepare_info_add_replies2entry_right : pbft.

  Lemma auth_matches_logEntryPrePrepareInfo_log_entry_pre_prepare_info_add_replies2entry :
    forall a entry reps,
      auth_matches_logEntryPrePrepareInfo a (log_entry_pre_prepare_info (add_replies2entry entry reps))
      = auth_matches_logEntryPrePrepareInfo a (log_entry_pre_prepare_info entry).
  Proof.
    introv; destruct entry; simpl.
    destruct log_entry_pre_prepare_info; simpl; auto.
  Qed.
  Hint Rewrite auth_matches_logEntryPrePrepareInfo_log_entry_pre_prepare_info_add_replies2entry : pbft.

  Lemma log_entry_prepares_add_replies2entry :
    forall entry reps,
      log_entry_prepares (add_replies2entry entry reps)
      = log_entry_prepares entry.
  Proof.
    destruct entry; introv; simpl; auto.
  Qed.
  Hint Rewrite log_entry_prepares_add_replies2entry : pbft.

  Lemma rep_toks_matches_logEntryPrePrepareInfo_pre_prepare2pp_info_true_iff :
    forall rt slf pp,
      rep_toks_matches_logEntryPrePrepareInfo rt slf (pre_prepare2pp_info pp) = true
      <->
      rt = pre_prepare2rep_toks pp slf.
  Proof.
    introv; unfold rep_toks_matches_logEntryPrePrepareInfo;
      destruct pp; simpl; destruct b; simpl.
    split; intro h; pbft_dest_all x.
  Qed.

  Lemma auth_matches_logEntryPrePrepareInfo_pre_prepare2pp_info_true_iff :
    forall a pp,
      auth_matches_logEntryPrePrepareInfo a (pre_prepare2pp_info pp) = true
      <->
      a = pre_prepare2auth pp.
  Proof.
    introv; unfold auth_matches_logEntryPrePrepareInfo;
      destruct pp; simpl; destruct b; simpl.
    split; intro h; pbft_dest_all x.
  Qed.

  Lemma rep_toks_matches_logEntryPrePrepareInfo_pre_prepare2pp_info_true_implies :
    forall rt slf pp,
      rep_toks_matches_logEntryPrePrepareInfo rt slf (pre_prepare2pp_info pp) = true
      -> rt = pre_prepare2rep_toks pp slf.
  Proof.
    introv h; apply rep_toks_matches_logEntryPrePrepareInfo_pre_prepare2pp_info_true_iff in h; auto.
  Qed.
  Hint Resolve rep_toks_matches_logEntryPrePrepareInfo_pre_prepare2pp_info_true_implies : pbft.

  Lemma auth_matches_logEntryPrePrepareInfo_pre_prepare2pp_info_true_implies :
    forall a pp,
      auth_matches_logEntryPrePrepareInfo a (pre_prepare2pp_info pp) = true
      -> a = pre_prepare2auth pp.
  Proof.
    introv h; apply auth_matches_logEntryPrePrepareInfo_pre_prepare2pp_info_true_iff in h; auto.
  Qed.
  Hint Resolve auth_matches_logEntryPrePrepareInfo_pre_prepare2pp_info_true_implies : pbft.

  Lemma log_entry_request_data_add_replies2entry :
    forall entry reps,
      log_entry_request_data (add_replies2entry entry reps)
      = log_entry_request_data entry.
  Proof.
    introv; destruct entry; simpl; auto.
  Qed.
  Hint Rewrite log_entry_request_data_add_replies2entry : pbft.

  Lemma is_prepare_for_entry_add_replies2entry :
    forall entry reps prep,
      is_prepare_for_entry (add_replies2entry entry reps) prep
      = is_prepare_for_entry entry prep.
  Proof.
    introv; unfold is_prepare_for_entry, eq_request_data; smash_pbft; tcsp.
  Qed.
  Hint Rewrite is_prepare_for_entry_add_replies2entry : pbft.

  Lemma similar_entry_add_replies2entry_right :
    forall entry1 entry2 reps,
      similar_entry entry1 (add_replies2entry entry2 reps)
      = similar_entry entry1 entry2.
  Proof.
    introv; unfold similar_entry, eq_request_data; smash_pbft; tcsp.
  Qed.
  Hint Rewrite similar_entry_add_replies2entry_right : pbft.

  Lemma similar_entry_same_eq :
    forall entry, similar_entry entry entry = true.
  Proof.
    destruct entry; unfold similar_entry, eq_request_data; smash_pbft.
  Qed.
  Hint Rewrite similar_entry_same_eq : pbft.

  Lemma entry2seq_if_find_entry :
    forall L sn entry,
      find_entry L sn = Some entry
      -> entry2seq entry = sn.
  Proof.
    induction L; introv e; simpl in *; tcsp.
    pbft_dest_all x.
  Qed.

  Lemma entry2seq_if_similar_entry :
    forall entry1 entry2,
      similar_entry entry1 entry2 = true
      -> entry2seq entry1 = entry2seq entry2.
  Proof.
    introv h; unfold similar_entry, eq_request_data in h; pbft_dest_all x.
    destruct entry1, entry2; simpl in *; subst; auto.
  Qed.

  Lemma change_log_entry_preserves_keys:
    forall entry st st',
      change_log_entry st entry = st'
      -> local_keys st = local_keys st'.
  Proof.
    introv IH.
    destruct st, st'; simpl in *.
    unfold change_log_entry in *. simpl in *.
    ginv. tcsp.
  Qed.

  Lemma find_and_execute_requests_preserves_keys :
    forall msg i st p,
      find_and_execute_requests i (current_view p) (local_keys p) p = (msg, st)
      -> local_keys p = local_keys st.
  Proof.
    introv IH.
    unfold find_and_execute_requests in *.
    pbft_dest_all x;[].
    unfold execute_requests in *.
    destruct (ready p); [ inversion Heqx; tcsp | ].
    pbft_dest_all x;[].

    match goal with
    | [H : check_broadcast_checkpoint _ _ _ _ _ = _ |- _ ] =>
      apply check_broadcast_checkpoint_preserves_keys in H
    end.

    ginv.
  Qed.

  Lemma decrement_requests_in_progress_preserves_keys :
    forall i v state,
      local_keys (decrement_requests_in_progress_if_primary i v state)
      = local_keys state.
  Proof.
    introv.
    unfold decrement_requests_in_progress_if_primary.
    pbft_dest_all w.
  Qed.

  Lemma is_prepare_for_entry_change_pre_prepare_info_of_entry :
    forall pp entry p,
      is_prepare_for_entry (change_pre_prepare_info_of_entry pp entry) p
      = is_prepare_for_entry entry p.
  Proof.
    introv; destruct entry; unfold is_prepare_for_entry; simpl; auto.
  Qed.
  Hint Rewrite is_prepare_for_entry_change_pre_prepare_info_of_entry : pbft.

  Lemma is_prepare_for_entry_preserves_similar_entry_and_pre_prepare :
    forall entry pp d p,
      similar_entry_and_pre_prepare entry pp d = true
      -> is_prepare_for_entry entry p = true
      -> similar_pre_prepare_and_prepare pp d p = true.
  Proof.
    introv h q.
    unfold similar_entry_and_pre_prepare in *.
    unfold similar_pre_prepare_and_prepare in *.
    unfold is_prepare_for_entry, eq_request_data in *.
    destruct entry; simpl in *.
    smash_pbft.
  Qed.
  Hint Resolve is_prepare_for_entry_preserves_similar_entry_and_pre_prepare : pbft.

  Lemma log_entry_prepares_change_pre_prepare_info_of_entry :
    forall pp entry,
      log_entry_prepares (change_pre_prepare_info_of_entry pp entry)
      = log_entry_prepares entry.
  Proof.
    destruct entry; simpl; auto.
  Qed.
  Hint Rewrite log_entry_prepares_change_pre_prepare_info_of_entry : pbft.

  Lemma prepare_in_log_add_new_pre_prepare2log :
    forall prep pp d L,
      prepare_in_log prep (add_new_pre_prepare2log pp d L)
      = prepare_in_log prep L.
  Proof.
    induction L; simpl in *; smash_pbft.
  Qed.
  Hint Rewrite prepare_in_log_add_new_pre_prepare2log : pbft.

  Lemma similar_pre_prepare_and_prepare_true_iff :
    forall pp d p,
      similar_pre_prepare_and_prepare pp d p = true
      <-> pre_prepare2request_data pp d = prepare2request_data p.
  Proof.
    introv.
    unfold similar_pre_prepare_and_prepare in *; simpl in *.
    unfold eq_request_data in *; split; intro h; pbft_dest_all x.
  Qed.

  Lemma pre_prepare2rep_toks_pre_prepare :
    forall b a slf,
      pre_prepare2rep_toks (pre_prepare b a) slf = MkRepToks slf a.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite pre_prepare2rep_toks_pre_prepare : pbft.

  Lemma check_send_replies_preserves_low_water_mark :
    forall slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> low_water_mark state' = low_water_mark state.
  Proof.
    introv chk.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_low_water_mark : pbft.

  Lemma same_rep_tok_true_iff :
    forall rt1 rt2,
      same_rep_tok rt1 rt2 = true
      <-> rt1 = rt2.
  Proof.
    introv; unfold same_rep_tok; split; intro h; smash_pbft.
  Qed.

  Lemma decomp_propose :
    forall prep,
      request_data_and_rep_toks2prepare
        (prepare2request_data prep)
        (prepare2rep_toks prep)
      = prep.
  Proof.
    destruct prep; simpl.
    destruct b; simpl; auto.
  Qed.
  Hint Rewrite decomp_propose : pbft.

  Lemma fill_out_pp_info_with_prepare_preserves_request_data :
    forall i entry pp Fp Fc gi,
      fill_out_pp_info_with_prepare i entry pp Fp Fc = Some gi
      -> log_entry_request_data (gi_entry gi) = log_entry_request_data entry.
  Proof.
    destruct entry; introv h; simpl in *.
    destruct log_entry_pre_prepare_info; ginv.
    smash_pbft.
  Qed.

  Lemma eq_request_data_preserves_is_prepare_for_entry :
    forall entry1 entry2 prep,
      log_entry_request_data entry1 = log_entry_request_data entry2
      -> is_prepare_for_entry entry1 prep = true
      -> is_prepare_for_entry entry2 prep = true.
  Proof.
    introv h q.
    unfold is_prepare_for_entry, eq_request_data in *; smash_pbft.
  Qed.
  Hint Resolve eq_request_data_preserves_is_prepare_for_entry : pbft.

  Lemma in_list_rep_toks_false_implies_existsb_same_rep_toks_false :
    forall L rt,
      in_list_rep_toks (rt_rep rt) L = false
      -> existsb (same_rep_tok rt) L = false.
  Proof.
    introv h; unfold in_list_rep_toks in h.
    induction L; simpl in *; auto.
    pbft_simplifier; repnd.
    autodimp IHL hyp.
    dands; auto.
    clear IHL.
    allrw @existsb_false.
    unfold same_rep_tok; pbft_dest_all x; tcsp.
  Qed.

  Fixpoint find_entry_with_request_data (L : PBFTlog) (rd : RequestData) : option PBFTlogEntry :=
    match L with
    | [] => None
    | entry :: entries =>
      if is_request_data_for_entry entry rd then Some entry
      else find_entry_with_request_data entries rd
    end.

  Lemma similar_entry_and_pre_prepare_iff_is_request_data_for_entry :
    forall entry pp d,
      similar_entry_and_pre_prepare entry pp d = true
      <-> is_request_data_for_entry entry (pre_prepare2request_data pp d) = true.
  Proof.
    introv.
    destruct entry; simpl; unfold is_request_data_for_entry, eq_request_data; simpl; tcsp.
  Qed.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_prepare_in_log :
    forall i L pp d Fp Fc giop K prep,
      i = rt_rep (Fp tt)
      -> add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> prepare_in_log prep K = true
      -> prepare_in_log prep L = true
         \/
         (
           prep = request_data_and_rep_toks2prepare (pre_prepare2request_data pp d) (Fp tt)
           /\ prepare_in_log prep L = false
(*           /\ forall entry,
               find_entry_with_request_data L (pre_prepare2request_data pp d) = Some entry
               -> length (log_entry_prepares entry) < 2 * F
                  /\ in_list_rep_toks i (log_entry_prepares entry) = false*)
         ).
  Proof.
    induction L; introv eqi h q; simpl in *; smash_pbft.

    - simpl in *; smash_pbft; repndors; tcsp.
      allrw is_prepare_for_entry_true_iff; simpl in *.
      allrw same_rep_tok_true_iff.
      allrw; simpl.
      rewrite <- q.
      autorewrite with pbft; auto.
(*      right; dands; tcsp.*)

    - destruct x; simpl in *.
      unfold fill_out_pp_info_with_prepare in *.
      destruct a; simpl in *.
      destruct log_entry_pre_prepare_info; ginv.
      pbft_dest_all x.
      unfold is_prepare_for_entry, eq_request_data in *; simpl in *.
      pbft_dest_all x.

      unfold add_prepare_if_not_enough in *; pbft_dest_all x.
      repndors; tcsp;[].

      allrw same_rep_tok_true_iff.

      right.

      dands; tcsp.

      { allrw <-; autorewrite with pbft; dands; auto. }

      {
        rewrite <- q in *; simpl in *.
        apply in_list_rep_toks_false_implies_existsb_same_rep_toks_false; auto.
      }

(*      { introv h; ginv; simpl in *. }*)

(*    - match goal with
      | [ H : similar_entry_and_pre_prepare _ _ _ = _ |- _ ] =>
        apply similar_entry_and_pre_prepare_iff_is_request_data_for_entry in H; pbft_simplifier
      end.*)

    - match goal with
      | [ H : fill_out_pp_info_with_prepare _ _ _ _ _ = _ |- _ ] =>
        applydup fill_out_pp_info_with_prepare_preserves_request_data in H as z;
          eapply eq_request_data_preserves_is_prepare_for_entry in z;[|eauto];pbft_simplifier
      end.

(*    - match goal with
      | [ H : similar_entry_and_pre_prepare _ _ _ = _ |- _ ] =>
        apply similar_entry_and_pre_prepare_iff_is_request_data_for_entry in H; pbft_simplifier
      end.*)

    - match goal with
      | [ H : fill_out_pp_info_with_prepare _ _ _ _ _ = _ |- _ ] =>
        applydup fill_out_pp_info_with_prepare_preserves_request_data in H as z;
          symmetry in z;
          eapply eq_request_data_preserves_is_prepare_for_entry in z;[|eauto];pbft_simplifier
      end.

(*    - match goal with
      | [ H : similar_entry_and_pre_prepare _ _ _ = _ |- _ ] =>
        apply similar_entry_and_pre_prepare_iff_is_request_data_for_entry in H; pbft_simplifier
      end.

    - match goal with
      | [ H : is_request_data_for_entry _ _ = _ |- _ ] =>
        apply similar_entry_and_pre_prepare_iff_is_request_data_for_entry in H; pbft_simplifier
      end.*)
  Qed.

 Lemma log_update_log:
    forall p l,
      log (update_log p l) = l.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite log_update_log : pbft.

(*  Lemma add_rep_toks_some_implies_not_in :
    forall rt preps preps',
      add_rep_toks rt preps = Some preps'
      -> ~In rt preps.
  Proof.
    induction preps; introv h q; simpl in *; tcsp.
    repndors; subst; tcsp; smash_pbft.
    eapply IHpreps in q; eauto.
  Qed.*)

(*  Lemma add_rep_toks_some_implies_eq :
    forall rt preps preps',
      add_rep_toks rt preps = Some preps'
      -> preps' = snoc preps rt.
  Proof.
    induction preps; introv h; simpl in *; tcsp; smash_pbft.
    f_equal; apply IHpreps; auto.
  Qed.*)

  Lemma in_list_rep_toks_true_iff :
    forall i preps,
      in_list_rep_toks i preps = true
      <-> exists rt, i = rt_rep rt /\ In rt preps.
  Proof.
    induction preps; simpl; introv; split; intro h; tcsp; smash_pbft.

    - eexists; dands; eauto.

    - apply IHpreps in h; clear IHpreps; exrepnd.
      eexists; dands; eauto.

    - apply IHpreps; exrepnd.
      eexists; dands; eauto.
      repndors; subst; tcsp.
  Qed.

  Lemma in_list_rep_toks_false_iff :
    forall i preps,
      in_list_rep_toks i preps = false
      <-> forall rt, In rt preps -> i <> rt_rep rt.
  Proof.
    induction preps; simpl; introv; split; intro h; tcsp; smash_pbft.

    - introv j; repndors; subst; tcsp.
      rewrite IHpreps in h.
      apply h; auto.

    - pose proof (h a) as q; autodimp q hyp; tcsp.

    - apply IHpreps; exrepnd.
      introv j; apply h; tcsp.
  Qed.

  Lemma add_prepare_if_not_enough_already_in_implies_eq :
    forall i preps Fp rtop preps',
      add_prepare_if_not_enough i preps Fp = (rtop, preps')
      -> in_list_rep_toks i preps = true
      -> preps' = preps.
  Proof.
    introv h q.
    unfold add_prepare_if_not_enough in h; smash_pbft.
  Qed.

  Lemma rt_rep_prepare2rep_toks_as_prepare2sender :
    forall prep,
      rt_rep (prepare2rep_toks prep)
      = prepare2sender prep.
  Proof.
    introv; destruct prep, b; simpl; auto.
  Qed.
  Hint Rewrite rt_rep_prepare2rep_toks_as_prepare2sender : pbft.

  Lemma find_rep_toks_in_list_implies_in :
    forall i L rt,
      find_rep_toks_in_list i L = Some rt
      -> In rt L.
  Proof.
    induction L; introv h; simpl in *; ginv.
    smash_pbft.
  Qed.

  Lemma add_prepare_if_not_enough_already_not_in_implies_eq :
    forall i preps Fp rtop preps' rt,
      rt = Fp tt
      -> add_prepare_if_not_enough i preps Fp = (rtop, preps')
      -> in_list_rep_toks i preps = false
      -> preps' = rt :: preps.
  Proof.
    introv eqrt addp ir.
    unfold add_prepare_if_not_enough in addp; smash_pbft; try omega.
  Qed.

(*  Lemma add_prepare_if_not_enough_already_enough_implies_eq :
    forall i preps Fp rtop preps',
      add_prepare_if_not_enough i preps Fp = (rtop, preps')
      -> 2 * F <= length preps
      -> preps' = preps.
  Proof.
    introv addp len.
    unfold add_prepare_if_not_enough in addp; smash_pbft; try omega.
  Qed.*)

  Lemma add_prepare2entry_some_implies_log_entry_prepares_gi_entry_or :
    forall slf entry prep Fc gi,
      add_prepare2entry slf entry prep Fc = Some gi
      -> if in_list_rep_toks (prepare2sender prep) (log_entry_prepares entry)
         then log_entry_prepares (gi_entry gi) = log_entry_prepares entry
         else log_entry_prepares (gi_entry gi) = prepare2rep_toks prep :: log_entry_prepares entry.
  Proof.
    introv h.
    unfold add_prepare2entry in h.
    destruct entry; simpl in *.
    smash_pbft.

    - eapply add_prepare_if_not_enough_already_in_implies_eq; eauto.

    - eapply add_prepare_if_not_enough_already_not_in_implies_eq; eauto; simpl; auto.
  Qed.

  Lemma add_prepare2entry_some_implies_log_entry_request_data :
    forall slf entry prep Fc gi,
      add_prepare2entry slf entry prep Fc = Some gi
      -> log_entry_request_data (gi_entry gi) = log_entry_request_data entry.
  Proof.
    introv h.
    unfold add_prepare2entry in h.
    destruct entry; simpl in *; smash_pbft.
  Qed.

  Hint Rewrite orb_false_r : bool.

  Lemma existsb_snoc :
    forall {A} (l : list A) a F,
      existsb F (snoc l a) = existsb F l || F a.
  Proof.
    induction l; simpl in *; introv; autorewrite with bool in *; auto.
    rewrite IHl; auto.
    rewrite orb_assoc; auto.
  Qed.

  Lemma check_send_replies_preserves_local_keys :
    forall slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> local_keys state' = local_keys state.
  Proof.
    introv chk.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_local_keys :
    forall slf pp d state state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state (pp,d) = (state', msgs)
      -> local_keys state' = local_keys state.
  Proof.
    introv h.
    unfold add_prepare_to_log_from_new_view_pre_prepare in h; smash_pbft.

    match goal with
    | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
      apply check_send_replies_preserves_local_keys in H; simpl in *; subst; auto
    end.
  Qed.

  Lemma ViewLt_true_iff :
    forall v1 v2, ViewLt v1 v2 = true <-> v1 < v2.
  Proof.
    introv; unfold ViewLt.
    allrw Nat.ltb_lt; tcsp.
  Qed.
  Hint Rewrite ViewLt_true_iff : pbft.

  Lemma ViewLe_true_iff :
    forall v1 v2, ViewLe v1 v2 = true <-> v1 <= v2.
  Proof.
    introv; unfold ViewLe.
    allrw Nat.leb_le; tcsp.
  Qed.
  Hint Rewrite ViewLe_true_iff : pbft.

  Lemma add_commit2entry_preserves_log_entry_request_data :
    forall entry1 entry2 c,
      add_commit2entry entry1 c = Some entry2
      -> log_entry_request_data entry1 = log_entry_request_data entry2.
  Proof.
    introv h.
    unfold add_commit2entry in h.
    destruct entry1; simpl in *.
    dest_cases w.
  Qed.

  Lemma matching_requests_map_fst_combine_replies :
    forall rs reqs reps,
      matching_requests rs (map fst (combine_replies reqs reps))
      = matching_requests rs (map fst reqs).
  Proof.
    induction rs; introv; simpl; destruct reqs; simpl; repnd;
      destruct reps; simpl in *; tcsp; smash_pbft.
  Qed.
  Hint Rewrite matching_requests_map_fst_combine_replies : pbft.

  Lemma requests_matches_logEntryPrePrepareInfo_log_entry_pre_prepare_info_add_replies2entry_right :
    forall rt entry reps,
      requests_matches_logEntryPrePrepareInfo
        rt
        (log_entry_pre_prepare_info (add_replies2entry entry reps))
      = requests_matches_logEntryPrePrepareInfo
          rt
          (log_entry_pre_prepare_info entry).
  Proof.
    introv; unfold requests_matches_logEntryPrePrepareInfo.
    destruct entry; simpl.
    destruct log_entry_pre_prepare_info; simpl; smash_pbft.
  Qed.
  Hint Rewrite requests_matches_logEntryPrePrepareInfo_log_entry_pre_prepare_info_add_replies2entry_right : pbft.

  Lemma eq_request_data_preserves_similar_entry_and_pre_prepare :
    forall entry1 entry2 prep d,
      log_entry_request_data entry1 = log_entry_request_data entry2
      -> similar_entry_and_pre_prepare entry1 prep d = true
      -> similar_entry_and_pre_prepare entry2 prep d = true.
  Proof.
    introv h q.
    allrw similar_entry_and_pre_prepare_true_iff.
    rewrite h in q. auto.
  Qed.
  Hint Resolve eq_request_data_preserves_similar_entry_and_pre_prepare : pbft.

  Definition pp_info_is_filled_out (nfo : logEntryPrePrepareInfo) : Prop :=
    match nfo with
    | pp_info_pre_prep _ _ => True
    | _ => False
    end.

  Definition pp_info_is_filled_out_b (nfo : logEntryPrePrepareInfo) : bool :=
    match nfo with
    | pp_info_pre_prep _ _ => true
    | _ => false
    end.

  Lemma log_entry_pre_prepare_info_change_pre_prepare_info_of_entry :
    forall pp entry,
      log_entry_pre_prepare_info (change_pre_prepare_info_of_entry pp entry)
      = if pp_info_is_filled_out_b (log_entry_pre_prepare_info entry)
        then log_entry_pre_prepare_info entry
        else pre_prepare2pp_info pp.
  Proof.
    destruct entry; simpl; auto.
    destruct log_entry_pre_prepare_info; simpl; auto.
  Qed.
  Hint Rewrite log_entry_pre_prepare_info_change_pre_prepare_info_of_entry : pbft.

  Lemma matching_requests_true_iff :
    forall reqs1 reqs2,
      matching_requests reqs1 reqs2 = true <-> reqs1 = reqs2.
  Proof.
    induction reqs1; destruct reqs2; simpl in *; split; intro h; tcsp.
    - smash_pbft.
      f_equal; apply IHreqs1; auto.
    - ginv.
      destruct (RequestDeq r r); subst; tcsp.
      apply IHreqs1; auto.
  Qed.

  Lemma requests_matches_logEntryPrePrepareInfo_true_iff :
    forall reqs nfo,
      requests_matches_logEntryPrePrepareInfo reqs nfo = true
      <-> (pp_info_is_filled_out nfo /\ reqs = pp_info2requests nfo).
  Proof.
    destruct nfo; simpl; autorewrite with pbft in *;
      allrw matching_requests_true_iff; split; intro h; repnd; tcsp.
  Qed.

  Lemma pp_info2requests_pre_prepare2pp_info :
    forall pp,
      pp_info2requests (pre_prepare2pp_info pp)
      = pre_prepare2requests pp.
  Proof.
    destruct pp; destruct b; simpl; auto.
    allrw map_map; simpl.
    apply map_id.
  Qed.
  Hint Rewrite pp_info2requests_pre_prepare2pp_info : pbft.

  Lemma eq_pre_prepares_if_eq_request_data_and_rep_toks :
    forall pp1 pp2 d1 d2 i,
      pre_prepare2request_data pp1 d1 = pre_prepare2request_data pp2 d2
      -> pre_prepare2rep_toks pp1 i = pre_prepare2rep_toks pp2 i
      -> pre_prepare2requests pp1 = pre_prepare2requests pp2
      -> pp1 = pp2.
  Proof.
    introv h1 h2 h3; destruct pp1 as [b1 a1], pp2 as [b2 a2]; simpl in *;
      destruct b1, b2; simpl in *; ginv; auto.
  Qed.
  Hint Resolve eq_pre_prepares_if_eq_request_data_and_rep_toks : pbft.

  Lemma eq_pre_prepares_if_eq_request_data_and_auth :
    forall pp1 pp2 d1 d2,
      pre_prepare2request_data pp1 d1 = pre_prepare2request_data pp2 d2
      -> pre_prepare2auth pp1 = pre_prepare2auth pp2
      -> pre_prepare2requests pp1 = pre_prepare2requests pp2
      -> pp1 = pp2.
  Proof.
    introv h1 h2 h3; destruct pp1 as [b1 a1], pp2 as [b2 a2]; simpl in *;
      destruct b1, b2; simpl in *; ginv; auto.
  Qed.
  Hint Resolve eq_pre_prepares_if_eq_request_data_and_auth : pbft.

  Lemma similar_entry_and_pre_prepare_change_pre_prepare_info_of_entry :
    forall npp entry pp d,
      similar_entry_and_pre_prepare (change_pre_prepare_info_of_entry npp entry) pp d
      = similar_entry_and_pre_prepare entry pp d.
  Proof.
    destruct entry; introv; simpl; auto.
  Qed.
  Hint Rewrite similar_entry_and_pre_prepare_change_pre_prepare_info_of_entry : pbft.

  Lemma eq_pre_prepare2request_data_implies_eq_digest :
    forall pp1 pp2 d1 d2,
      pre_prepare2request_data pp1 d1 = pre_prepare2request_data pp2 d2
      -> d1 = d2.
  Proof.
    introv h; destruct pp1 as [b1 a1], pp2 as [b2 a2];
      destruct b1, b2; simpl in *; ginv; auto.
  Qed.
  Hint Resolve eq_pre_prepare2request_data_implies_eq_digest : pbft.

  Lemma check_new_requests_some_cons_implies :
    forall i l s r s' r' rs,
      check_new_request i l s r = (s', Some (r' :: rs)) -> r' = r.
  Proof.
    introv h.
    unfold check_new_request in h; smash_pbft.
  Qed.

  Lemma check_new_requests_some_iff :
    forall i l s r s' rs,
      check_new_request i l s r = (s', Some rs)
      <->
      in_progress s < PBFTmax_in_progress
      /\ check_between_water_marks l (next_seq (sequence_number s)) = true
      /\ valid_timestamp s (request2sender r) (request2timestamp r) = true
      /\ rs = r :: request_buffer s
      /\ s' = reset_request_buffer (increment_in_progress (update_timestamp_op s (request2sender r) (request2timestamp r))).
  Proof.
    introv.
    unfold check_new_request; split; intro h; repnd; subst; smash_pbft; try omega.
    repndors; pbft_simplifier; try omega.
  Qed.

  Lemma view_changed_entry_some_implies :
    forall state entry vc' entry',
      view_changed_entry state entry = Some (vc',entry')
      ->
      exists vc,
        vce_view_change entry = Some vc
        /\ vc' = refresh_view_change vc state
        /\ entry' = replace_own_view_change_in_entry vc' entry.
  Proof.
    introv h.
    unfold view_changed_entry in *; smash_pbft.
    eexists; dands; eauto.
  Qed.

  Lemma check_broadcast_new_view_some_implies :
    forall i state entry nv entry' OP NP,
      check_broadcast_new_view i state entry = Some (nv, entry', OP, NP)
      ->
      exists vc vc',
        is_primary (vce_view entry) i = true
        /\ vce_view_change entry = Some vc
        /\ view_changed_entry state entry = Some (vc', entry')
        /\ vc' = refresh_view_change vc state
        /\ entry' = replace_own_view_change_in_entry vc' entry
        /\ create_new_prepare_messages
             (from_min_to_max_of_view_changes entry')
             (view_change2view vc')
             (local_keys state)
             (view_change_cert2prep (view_change_entry2view_changes entry')) = (OP, NP)
        /\ nv = mk_auth_new_view
                  (view_change2view vc')
                  (view_change_entry2view_changes entry')
                  (map fst OP) (map fst NP)
                  (local_keys state).
  Proof.
    introv h.
    unfold check_broadcast_new_view in h; smash_pbft;[].
    rename_hyp_with view_changed_entry vce.
    applydup view_changed_entry_some_implies in vce; exrepnd.
    eexists; eexists; dands; eauto.
  Qed.

  Lemma o_pre_prepare_in_create_new_prepare_messages_implies :
    forall L nview keys cert OP NP pp d,
      create_new_prepare_messages L nview keys cert = (OP, NP)
      -> In (pp,d) OP
      -> exists sn,
          In sn L
          /\ create_new_prepare_message sn nview keys cert = (true, (pp,d)).
  Proof.
    induction L; introv h i; simpl in *; smash_pbft; simpl in *; tcsp;
      repndors; repnd; ginv; subst; tcsp.

    - eexists; dands; eauto.

    - match goal with
      | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
        eapply IHL in H;[|eauto]
      end.
      exrepnd.
      eexists; dands; eauto.

    - match goal with
      | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
        eapply IHL in H;[|eauto]
      end.
      exrepnd.
      eexists; dands; eauto.
  Qed.

  Lemma n_pre_prepare_in_create_new_prepare_messages_implies :
    forall L nview keys cert OP NP pp d,
      create_new_prepare_messages L nview keys cert = (OP, NP)
      -> In (pp,d) NP
      -> exists sn,
          In sn L
          /\ create_new_prepare_message sn nview keys cert = (false, (pp,d)).
  Proof.
    induction L; introv h i; simpl in *; smash_pbft; simpl in *; tcsp;
      repndors; repnd; ginv; subst; tcsp.

    - match goal with
      | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
        eapply IHL in H;[|eauto]
      end.
      exrepnd.
      eexists; dands; eauto.

    - eexists; dands; eauto.

    - match goal with
      | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
        eapply IHL in H;[|eauto]
      end.
      exrepnd.
      eexists; dands; eauto.
  Qed.

(*  Lemma create_new_prepare_message_implies :
    forall sn nview keys P b pp d,
      create_new_prepare_message sn nview keys P = (b, (pp,d))
      ->
      exists reqs,
        find_pre_prepare_certificate_in_prepared_infos (valid_prepared_info P) sn P = Some ppinfo
        /\ pp = mk_auth_pre_prepare nview sn reqs keys.
  Proof.
    introv h.
    unfold create_new_prepare_message in h.
    smash_pbft.
  Qed.*)

  Lemma sequence_number_reset_request_buffer :
    forall s, sequence_number (reset_request_buffer s) = sequence_number s.
  Proof.
    introv; destruct s; simpl; auto.
  Qed.
  Hint Rewrite sequence_number_reset_request_buffer : pbft.

  Lemma sequence_number_increment_in_progress :
    forall s, sequence_number (increment_in_progress s) = sequence_number s.
  Proof.
    introv; destruct s; simpl; auto.
  Qed.
  Hint Rewrite sequence_number_increment_in_progress : pbft.

  Lemma primary_state_update_checkpoint_from_new_view :
    forall st chk sn,
      primary_state (update_checkpoint_from_new_view st chk sn)
      = primary_state st.
  Proof.
    introv; unfold update_checkpoint_from_new_view; smash_pbft.
  Qed.
  Hint Rewrite primary_state_update_checkpoint_from_new_view : pbft.

  Lemma primary_state_trim_checkpoint :
    forall st chk,
      primary_state (trim_checkpoint st chk)
      = primary_state st.
  Proof.
    introv; unfold trim_checkpoint; smash_pbft.
  Qed.
  Hint Rewrite primary_state_trim_checkpoint : pbft.

  Lemma log_checkpoint_cert_from_new_view_preserves_primary_state :
    forall i st v x0 cert chk st' msgs,
      log_checkpoint_cert_from_new_view i st v x0 cert chk = (st', msgs)
      -> primary_state st' = primary_state st.
  Proof.
    introv h.
    unfold log_checkpoint_cert_from_new_view in h.
    smash_pbft.
  Qed.
  Hint Resolve log_checkpoint_cert_from_new_view_preserves_primary_state : pbft.

(*  Lemma primary_state_update_low_water_mark :
    forall s n,
      primary_state (update_low_water_mark s n) = primary_state s.
  Proof.
    introv; destruct s; simpl; tcsp.
  Qed.
  Hint Rewrite primary_state_update_low_water_mark : pbft.*)

  Lemma primary_state_update_log :
    forall s L, primary_state (update_log s L) = primary_state s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite primary_state_update_log : pbft.

  Lemma update_state_new_view_preserves_primary_state :
    forall i st nv st' msgs,
      update_state_new_view i st nv = (st', msgs)
      -> primary_state st' = primary_state st.
  Proof.
    introv h; unfold update_state_new_view in h; smash_pbft.
  Qed.
  Hint Resolve update_state_new_view_preserves_primary_state : pbft.

  Lemma update_state_new_view_preserves_sequence_number :
    forall i st nv st' msgs,
      update_state_new_view i st nv = (st', msgs)
      -> sequence_number (primary_state st') = sequence_number (primary_state st).
  Proof.
    introv h.
    apply update_state_new_view_preserves_primary_state in h; allrw; auto.
  Qed.
  Hint Resolve update_state_new_view_preserves_sequence_number : pbft.

  Lemma check_send_replies_preserves_primary_state :
    forall i v keys giop st sn msgs st',
      check_send_replies i v keys giop st sn = (msgs, st')
      -> primary_state st' = primary_state st.
  Proof.
    introv h; unfold check_send_replies in h; destruct giop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_primary_state : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_primary_state :
    forall i p st st' msgs,
      add_prepare_to_log_from_new_view_pre_prepare i st p = (st', msgs)
      -> primary_state st' = primary_state st.
  Proof.
    introv h; unfold add_prepare_to_log_from_new_view_pre_prepare in h; repnd.
    smash_pbft.
    match goal with
    | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
      apply check_send_replies_preserves_primary_state in H
    end.
    simpl in *; auto.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_primary_state : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_primary_state :
    forall i P st st' msgs,
      add_prepares_to_log_from_new_view_pre_prepares i st P = (st', msgs)
      -> primary_state st' = primary_state st.
  Proof.
    induction P; simpl in *; introv h; smash_pbft.
    match goal with
    | [ H : add_prepare_to_log_from_new_view_pre_prepare _ _ _ = _ |- _ ] =>
      apply add_prepare_to_log_from_new_view_pre_prepare_preserves_primary_state in H
    end.
    allrw <-.
    eapply IHP; eauto.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_primary_state : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_sequence_number :
    forall i P st st' msgs,
      add_prepares_to_log_from_new_view_pre_prepares i st P = (st', msgs)
      -> sequence_number (primary_state st') = sequence_number (primary_state st).
  Proof.
    introv h; apply add_prepares_to_log_from_new_view_pre_prepares_preserves_primary_state in h.
    allrw; auto.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_sequence_number : pbft.

  Lemma check_send_replies_preserves_sequence_number :
    forall i v keys giop st sn msgs st',
      check_send_replies i v keys giop st sn = (msgs, st')
      -> sequence_number (primary_state st') = sequence_number (primary_state st).
  Proof.
    introv h; f_equal; eauto 2 with pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_sequence_number : pbft.

  Lemma check_send_replies_update_log_preserves_sequence_number :
    forall i v keys giop st L sn msgs st',
      check_send_replies i v keys giop (update_log st L) sn = (msgs, st')
      -> sequence_number (primary_state st') = sequence_number (primary_state st).
  Proof.
    introv h.
    apply check_send_replies_preserves_sequence_number in h; simpl in h; auto.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_sequence_number : pbft.

  Lemma max_O_as_pre_prepares2max_seq :
    forall P, max_O P = pre_prepares2max_seq (map fst P).
  Proof.
    induction P; simpl; repnd; simpl; tcsp.
    allrw; auto.
  Qed.

  Lemma PBFTnever_stops :
    forall (eo : EventOrdering) (e : Event) slf,
      has_correct_trace_bounded e
      -> exists st, state_sm_before_event (PBFTreplicaSM slf) e = Some st.
  Proof.
    introv.
    induction e as [e ind] using predHappenedBeforeInd;[]; introv hct.

    rewrite state_sm_before_event_unroll.
    destruct (dec_isFirst e) as [d|d]; simpl in *.

    { eexists; eauto. }

    pose proof (ind (local_pred e)) as q; clear ind; repeat (autodimp q hyp); eauto 3 with eo.
    exrepnd.
    allrw; simpl.

    applydup (has_correct_trace_bounded_implies_message e (local_pred e)) in hct; eauto 3 with eo.
    exrepnd.
    allrw; unfold op_state; simpl.

    unfold PBFTreplica_update.

    destruct m; simpl in *; ginv; subst; tcsp;
      try (complete (eexists; reflexivity));
      smash_handlers_concl.
  Qed.

  Lemma PBFTnever_stops_on_event :
    forall (eo : EventOrdering) (e : Event) slf,
      has_correct_trace_bounded e
      -> exists st, state_sm_on_event (PBFTreplicaSM slf) e = Some st.
  Proof.
    introv cor.
    rewrite state_sm_on_event_unroll2.
    pose proof (PBFTnever_stops eo e slf) as q.
    repeat (autodimp q hyp); exrepnd; allrw; simpl.
    unfold PBFTreplica_update.

    applydup (has_correct_trace_bounded_implies_message e e) in cor; eauto 3 with eo.
    exrepnd; allrw.
    unfold op_state; simpl.

    destruct m;
      simpl in *; ginv; subst; tcsp;
        try (complete (eexists; reflexivity));
        try (complete smash_handlers_concl).
  Qed.

(*
   Lemma update_state_new_view_preserves_log :
    forall slf state nv state' msgs,
      update_state_new_view slf state nv = (state', msgs)
      -> log state = log state'.
  Proof.
    introv h.
    unfold update_state_new_view in h.
    pbft_dest_all x; autorewrite with pbft in *; simpl.
    match goal with
    | [ H : log_checkpoint_cert_from_new_view _ _ _ _ _ _ = _ |- _ ] =>
      apply log_checkpoint_cert_from_new_view_preserves_log in H; auto
    end.
*)

  Lemma low_water_mark_update_checkpoint_from_new_view :
    forall s S n,
      low_water_mark (update_checkpoint_from_new_view s S n) = low_water_mark s.
  Proof.
    introv; unfold update_checkpoint_from_new_view; smash_pbft.
  Qed.
  Hint Rewrite low_water_mark_update_checkpoint_from_new_view : pbft.

  Lemma low_water_mark_trim_checkpoint :
    forall s n,
      low_water_mark (trim_checkpoint s n) = low_water_mark s.
  Proof.
    introv; destruct s; simpl; unfold trim_checkpoint, low_water_mark; simpl.
    destruct cp_state; simpl; auto.
  Qed.
  Hint Rewrite low_water_mark_trim_checkpoint : pbft.

  Lemma low_water_mark_update_log :
    forall s n,
      low_water_mark (update_log s n) = low_water_mark s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite low_water_mark_update_log : pbft.

  Lemma sn_of_view_change_cert2max_seq_vc :
    forall C n vc,
      view_change_cert2max_seq_vc C = Some (n, vc)
      -> n = view_change2seq vc.
  Proof.
    induction C; introv h; simpl in *; ginv.
    smash_pbft.
  Qed.

  Lemma local_keys_update_checkpoint_from_new_view :
    forall s S n,
      local_keys (update_checkpoint_from_new_view s S n) = local_keys s.
  Proof.
    introv; unfold update_checkpoint_from_new_view; smash_pbft.
  Qed.
  Hint Rewrite local_keys_update_checkpoint_from_new_view : pbft.

  Lemma local_keys_trim_checkpoint :
    forall s n,
      local_keys (trim_checkpoint s n) = local_keys s.
  Proof.
    introv; destruct s; simpl; unfold trim_checkpoint, low_water_mark; simpl.
    destruct cp_state; simpl; auto.
  Qed.
  Hint Rewrite local_keys_trim_checkpoint : pbft.

  Lemma local_keys_update_log :
    forall s n,
      local_keys (update_log s n) = local_keys s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite local_keys_update_log : pbft.

  Lemma update_state_new_view_preserves_local_keys :
    forall i s1 v s2 msgs,
      update_state_new_view i s1 v = (s2, msgs)
      -> local_keys s2 = local_keys s1.
  Proof.
    introv upd.
    unfold update_state_new_view in upd; smash_pbft.
    unfold log_checkpoint_cert_from_new_view in *; smash_pbft.
  Qed.

  Lemma correct_new_view_implies_correct_cert :
    forall nv,
      correct_new_view nv = true
      -> forallb (correct_view_change (new_view2view nv)) (new_view2cert nv) = true.
  Proof.
    introv cor.
    unfold correct_new_view in cor; smash_pbft.
  Qed.

  Lemma view_change_cert2_max_seq_vc_some_in :
    forall C n vc,
      view_change_cert2max_seq_vc C = Some (n, vc)
      -> In vc C.
  Proof.
    induction C; introv h; simpl in *; tcsp.
    smash_pbft.
  Qed.
  Hint Resolve view_change_cert2_max_seq_vc_some_in : pbft.

  Lemma correct_change_cert_one_implies_equal_seq_nums :
    forall n v s c,
      correct_view_change_cert_one n v s c = true
      -> n = checkpoint2seq c.
  Proof.
    introv cor; unfold correct_view_change_cert_one in cor; smash_pbft.
    unfold same_seq_nums in *; smash_pbft.
  Qed.
  Hint Resolve correct_change_cert_one_implies_equal_seq_nums : pbft.

  Lemma extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq :
    forall vc view n d,
      extract_seq_and_digest_from_checkpoint_certificate (view_change2cert vc) = Some (n, d)
      -> correct_view_change view vc = true
      -> view_change2seq vc = n.
  Proof.
    introv h cor.
    destruct vc, v; simpl in *.
    destruct C; simpl in *; ginv.
    unfold correct_view_change in cor; simpl in cor.
    unfold view_change2prep in cor; simpl in cor.
    allrw andb_true; repnd.
    unfold correct_view_change_cert in *; smash_pbft.
  Qed.
  Hint Resolve extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq : pbft.

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

  Lemma extract_seq_and_digest_from_checkpoint_certificate_none_implies :
    forall l,
      extract_seq_and_digest_from_checkpoint_certificate l = None
      -> l = [].
  Proof.
    destruct l; simpl; tcsp.
  Qed.

  Lemma rt_rep_pre_prepare2rep_toks_of_prepare :
    forall i keys pp d,
      rt_rep (pre_prepare2rep_toks_of_prepare i keys pp d) = i.
  Proof.
    introv; destruct pp, b; simpl; auto.
  Qed.
  Hint Rewrite rt_rep_pre_prepare2rep_toks_of_prepare : pbft.

  Lemma check_send_replies_preserves_cp_state :
    forall i v keys giop s1 n msgs s2,
      check_send_replies i v keys giop s1 n = (msgs, s2)
      -> cp_state s2 = cp_state s1.
  Proof.
    introv check; unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_cp_state :
    forall i s1 ppd s2 msgs,
      add_prepare_to_log_from_new_view_pre_prepare i s1 ppd = (s2, msgs)
      -> cp_state s2 = cp_state s1.
  Proof.
    introv add.
    unfold add_prepare_to_log_from_new_view_pre_prepare in add; smash_pbft.

    rename_hyp_with check_send_replies check.
    apply check_send_replies_preserves_cp_state in check; simpl in *; auto.
  Qed.

  Lemma eq_low_water_marks_if_eq_cp_states :
    forall s1 s2,
      cp_state s1 = cp_state s2
      -> low_water_mark s1 = low_water_mark s2.
  Proof.
    introv h.
    unfold low_water_mark; allrw; auto.
  Qed.

  Lemma local_pred_preserves_eq_local_pred :
    forall (eo : EventOrdering) (e : Event) i,
      loc e = i
      -> loc (local_pred e) = i.
  Proof.
    introv eqloc.
    autorewrite with eo; auto.
  Qed.
  Hint Resolve local_pred_preserves_eq_local_pred : eo pbft.

End PBFTprops2.


Hint Rewrite @primary_state_update_log : pbft.
Hint Rewrite @sequence_number_update_timestamp : pbft.
Hint Rewrite @log_update_checkpoint_state : pbft.
Hint Rewrite @log_entry_request_data_of_change_pre_prepare_info_of_entry : pbft.
Hint Rewrite @similar_entry_and_pre_prepare_same_pre_prepare2entry : pbft.
Hint Rewrite @log_decrement_requests_in_progress_if_primary : pbft.
Hint Rewrite @change_last_reply_state_preserves_log : pbft.
Hint Rewrite @change_sm_state_preserves_log : pbft.
Hint Rewrite @increment_next_to_execute_preserves_log : pbft.
Hint Rewrite @update_checkpoint_from_new_view_preserves_log : pbft.
Hint Rewrite @trim_checkpoint_preserves_log : pbft.
Hint Rewrite @rep_toks_matches_logEntryPrePrepareInfo_log_entry_pre_prepare_info_add_replies2entry_right : pbft.
Hint Rewrite @log_entry_prepares_add_replies2entry : pbft.
Hint Rewrite @log_entry_request_data_add_replies2entry : pbft.
Hint Rewrite @is_prepare_for_entry_add_replies2entry : pbft.
Hint Rewrite @similar_entry_add_replies2entry_right : pbft.
Hint Rewrite @similar_entry_same_eq : pbft.
Hint Rewrite @decrement_requests_in_progress_preserves_keys : pbft.
Hint Rewrite @log_entry_pre_prepare_info_change_pre_prepare_info_of_entry : pbft.
Hint Rewrite @is_prepare_for_entry_change_pre_prepare_info_of_entry : pbft.
Hint Rewrite @log_entry_prepares_change_pre_prepare_info_of_entry : pbft.
Hint Rewrite @prepare_in_log_add_new_pre_prepare2log : pbft.
Hint Rewrite @pre_prepare2rep_toks_pre_prepare : pbft.
Hint Rewrite @decomp_propose : pbft.
Hint Rewrite @log_update_log : pbft.
Hint Rewrite @ViewLt_true_iff : pbft.
Hint Rewrite @ViewLe_true_iff : pbft.
Hint Rewrite @matching_requests_map_fst_combine_replies : pbft.
Hint Rewrite @requests_matches_logEntryPrePrepareInfo_log_entry_pre_prepare_info_add_replies2entry_right : pbft.
Hint Rewrite @pp_info2requests_pre_prepare2pp_info : pbft.
Hint Rewrite @similar_entry_and_pre_prepare_change_pre_prepare_info_of_entry : pbft.
Hint Rewrite @sequence_number_reset_request_buffer : pbft.
Hint Rewrite @sequence_number_increment_in_progress : pbft.
Hint Rewrite @rt_rep_prepare2rep_toks_as_prepare2sender : pbft.
Hint Rewrite @primary_state_update_checkpoint_from_new_view : pbft.
Hint Rewrite @primary_state_trim_checkpoint : pbft.
Hint Rewrite @auth_matches_logEntryPrePrepareInfo_log_entry_pre_prepare_info_add_replies2entry : pbft.
(*Hint Rewrite @primary_state_update_low_water_mark : pbft.*)
Hint Rewrite @low_water_mark_update_checkpoint_from_new_view : pbft.
Hint Rewrite @low_water_mark_trim_checkpoint : pbft.
Hint Rewrite @low_water_mark_update_log : pbft.
Hint Rewrite @local_keys_update_checkpoint_from_new_view : pbft.
Hint Rewrite @local_keys_trim_checkpoint : pbft.
Hint Rewrite @local_keys_update_log : pbft.
Hint Rewrite @rt_rep_pre_prepare2rep_toks_of_prepare : pbft.
Hint Rewrite @local_keys_on_check_stable : pbft.


Hint Resolve implies_authenticated_messages_were_sent_non_byz_usys : pbft.
Hint Resolve is_prepare_for_entry_preserves_similar_entry_and_pre_prepare : pbft.
Hint Resolve rep_toks_matches_logEntryPrePrepareInfo_pre_prepare2pp_info_true_implies : pbft.
Hint Resolve check_send_replies_preserves_low_water_mark : pbft.
Hint Resolve eq_request_data_preserves_is_prepare_for_entry : pbft.
Hint Resolve eq_request_data_preserves_similar_entry_and_pre_prepare : pbft.
Hint Resolve eq_pre_prepares_if_eq_request_data_and_rep_toks : pbft.
Hint Resolve eq_pre_prepare2request_data_implies_eq_digest : pbft.
Hint Resolve log_checkpoint_cert_from_new_view_preserves_primary_state : pbft.
Hint Resolve update_state_new_view_preserves_primary_state : pbft.
Hint Resolve update_state_new_view_preserves_sequence_number : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_primary_state : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_primary_state : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_sequence_number : pbft.
Hint Resolve check_send_replies_preserves_primary_state : pbft.
Hint Resolve check_send_replies_preserves_sequence_number : pbft.
Hint Resolve check_send_replies_update_log_preserves_sequence_number : pbft.
Hint Resolve auth_matches_logEntryPrePrepareInfo_pre_prepare2pp_info_true_implies : pbft.
Hint Resolve eq_pre_prepares_if_eq_request_data_and_auth : pbft.
Hint Resolve view_change_cert2_max_seq_vc_some_in : pbft.
Hint Resolve extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq : pbft.
Hint Resolve correct_new_view_implies_correct_view_change : pbft.
Hint Resolve local_pred_preserves_eq_local_pred : eo pbft.
Hint Resolve correct_change_cert_one_implies_equal_seq_nums : pbft.
Hint Resolve check_stable_preserves_local_keys : pbft.
