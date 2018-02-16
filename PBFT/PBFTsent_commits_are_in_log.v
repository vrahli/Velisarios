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
Require Export PBFTcommit_in_log_preserves.
Require Export PBFTprepared_is_preserved.
Require Export PBFTprops4.
Require Export PBFTordering.
Require Export PBFTreceived_prepare_like.
Require Export PBFTprepare_like2request_data.
Require Export PBFTdelay_of_send_commits.


Section PBFTsent_commits_are_in_log.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Fixpoint committed_log
           (d : RequestData)
           (l : PBFTlog) : bool :=
    match l with
    | [] => false
    | entry :: entries =>
      if is_request_data_for_entry entry d
      then is_committed_entry entry
      else committed_log d entries
    end.

  Lemma is_committed_log_implies_is_committed_entry :
    forall rd L,
      committed_log rd L = true
      ->
      exists entry,
        is_committed_entry entry = true
        /\ rd = log_entry_request_data entry
        /\ In entry L.
  Proof.
    induction L; introv comm; simpl in *; tcsp; smash_pbft.
    - exists a; dands; auto.
      unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
    - apply IHL in comm; exrepnd; exists entry; tcsp.
  Qed.

  Lemma is_committed_entry_implies :
    forall entry,
      is_committed_entry entry = true
      -> is_prepared_entry entry = true
         /\ 2 * F + 1 <= length (log_entry_commits entry).
  Proof.
    introv comm.
    destruct entry; simpl in *; smash_pbft.
  Qed.

  Lemma is_prepared_entry_implies :
    forall entry,
      is_prepared_entry entry = true
      ->
      exists a R,
        2 * F <= length (log_entry_prepares entry)
        /\ log_entry_pre_prepare_info entry = pp_info_pre_prep a R.
  Proof.
    introv prep.
    destruct entry; simpl in *; smash_pbft.
    destruct log_entry_pre_prepare_info; simpl in *; tcsp; GC.
    eexists; eexists; dands; eauto.
  Qed.

  Lemma length_remove_elt_le :
    forall {A} dec (a : A) l,
      length (remove_elt dec a l) <= length l.
  Proof.
    induction l; introv; simpl in *; tcsp; smash_pbft; try omega.
  Qed.
  Hint Resolve length_remove_elt_le : list.

  Lemma length_remove_elt_if_in :
    forall {A} dec (a : A) l,
      In a l
      -> length (remove_elt dec a l) < length l.
  Proof.
    induction l; introv i; simpl in *; tcsp.
    repndors; subst; tcsp; smash_pbft; tcsp.

    - pose proof (length_remove_elt_le dec a l) as q; omega.

    - apply IHl in i; omega.
  Qed.
  Hint Resolve length_remove_elt_if_in : list.

  Lemma disjoint_remove_elt_right_and_not_in_implies :
    forall {A} dec (a : A) l1 l2,
      disjoint l1 (remove_elt dec a l2)
      -> ~ In a l1
      -> disjoint l1 l2.
  Proof.
    introv disj ni i j.
    applydup disj in i.
    destruct i0.
    apply in_remove_elt.
    dands; auto; introv xx; subst; tcsp.
  Qed.
  Hint Resolve disjoint_remove_elt_right_and_not_in_implies : list.

  Lemma length_cons :
    forall {A} (a : A) l, length (a :: l) = S (length l).
  Proof.
    tcsp.
  Qed.

  Definition entry2sender (e : PBFTlogEntry) : Rep := PBFTprimary (entry2view e).

  Definition entry2prep_senders (e : PBFTlogEntry) : list Rep :=
    entry2sender e :: map rt_rep (log_entry_prepares e).

  Lemma implies_no_repeats_entry2prep_senders :
    forall entry,
      well_formed_log_entry entry
      -> no_repeats (entry2prep_senders entry).
  Proof.
    introv wf.
    unfold entry2prep_senders.
    constructor; try apply wf.
  Qed.
  Hint Resolve implies_no_repeats_entry2prep_senders : pbft.

  Lemma length_entry2prep_senders :
    forall entry,
      length (entry2prep_senders entry)
      = S (length (log_entry_prepares entry)).
  Proof.
    introv; unfold entry2prep_senders; simpl.
    rewrite map_length; auto.
  Qed.

  Lemma in_entry2prep_senders_implies_prepare_like_in_log :
    forall k entry L a R,
      well_formed_log_entry entry
      -> log_entry_pre_prepare_info entry = pp_info_pre_prep a R
      -> In k (entry2prep_senders entry)
      -> In entry L
      ->
      exists pl,
        prepare_like2sender pl = k
        /\ prepare_like_in_log pl L
        /\ prepare_like2request_data pl = log_entry_request_data entry.
  Proof.
    introv wf nfo i j.
    unfold entry2prep_senders in i; simpl in i.
    repndors; subst; tcsp;[|].

    - destruct entry; simpl in *.
      unfold entry2sender; simpl; subst.
      destruct log_entry_request_data.

      exists (prepare_like_pre_prepare (mk_pre_prepare v s (map fst R) a)).
      simpl; dands; auto;[|].

      + eapply implies_prepare_like_in_log;[|eauto].
        simpl; tcsp.

      + f_equal.
        apply well_formed_log_entry_correct_digest in wf; simpl in *.
        unfold same_digests in wf; smash_pbft.
        unfold pre_prepare2digest; simpl; eauto 3 with pbft.

    - allrw in_map_iff; exrepnd; subst.
      destruct x as [rep auth]; simpl in *.
      destruct entry; simpl in *.
      destruct log_entry_request_data; simpl in *.

      exists (prepare_like_prepare (mk_prepare v s d rep auth)); simpl; dands; auto.
      eapply implies_prepare_like_in_log;[|eauto].
      unfold entry2prepares_like; simpl.
      allrw; simpl.

      right.
      unfold entry2prepares; simpl.
      allrw map_map.
      apply in_map_iff.
      eexists; dands; eauto; simpl; auto.
  Qed.

  Definition entry2com_senders (e : PBFTlogEntry) : list Rep :=
    map rt_rep (log_entry_commits e).

  Lemma implies_no_repeats_entry2com_senders :
    forall entry,
      well_formed_log_entry entry
      -> no_repeats (entry2com_senders entry).
  Proof.
    introv wf; try apply wf.
  Qed.
  Hint Resolve implies_no_repeats_entry2com_senders : pbft.

  Lemma length_entry2com_senders :
    forall entry,
      length (entry2com_senders entry)
      = length (log_entry_commits entry).
  Proof.
    introv; unfold entry2com_senders; simpl.
    rewrite map_length; auto.
  Qed.

  Lemma commit2request_data_request_data_and_rep_toks2commit :
    forall rd rt,
      commit2request_data (request_data_and_rep_toks2commit rd rt)
      = rd.
  Proof.
    introv; destruct rd, rt; simpl; tcsp.
  Qed.
  Hint Rewrite commit2request_data_request_data_and_rep_toks2commit : pbft.

  Lemma commit2sender_request_data_and_rep_toks2commit :
    forall rd rt,
      commit2sender (request_data_and_rep_toks2commit rd rt) = rt_rep rt.
  Proof.
    introv; destruct rd, rt; simpl; tcsp.
  Qed.
  Hint Rewrite commit2sender_request_data_and_rep_toks2commit : pbft.

  Lemma commit2rep_toks_request_data_and_rep_toks2commit :
    forall rd rt,
      commit2rep_toks (request_data_and_rep_toks2commit rd rt) = rt.
  Proof.
    introv; destruct rd, rt; simpl; tcsp.
  Qed.
  Hint Rewrite commit2rep_toks_request_data_and_rep_toks2commit : pbft.

  Lemma same_rep_tok_same :
    forall rt, same_rep_tok rt rt = true.
  Proof.
    introv; unfold same_rep_tok; smash_pbft.
  Qed.
  Hint Rewrite same_rep_tok_same : pbft.

  Lemma implies_commit_in_log :
    forall L entry rt,
      well_formed_log L
      -> In rt (log_entry_commits entry)
      -> In entry L
      -> commit_in_log (request_data_and_rep_toks2commit (log_entry_request_data entry) rt) L = true.
  Proof.
    induction L; introv wf i j; simpl in *; tcsp.
    inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
    repndors; subst; smash_pbft.

    - rewrite existsb_exists.
      eexists; dands; eauto.
      autorewrite with pbft; auto.

    - apply imp in j.
      unfold entries_have_different_request_data in j; tcsp.
  Qed.
  Hint Resolve implies_commit_in_log : pbft.

  Lemma in_entry2com_senders_implies_commit_in_log :
    forall k entry L,
      well_formed_log L
      -> In k (entry2com_senders entry)
      -> In entry L
      ->
      exists com,
        commit_in_log com L = true
        /\ commit2request_data com = log_entry_request_data entry
        /\ commit2sender com = k.
  Proof.
    introv wf i j.
    unfold entry2com_senders in i; simpl in i.
    allrw in_map_iff; exrepnd; subst.

    exists (request_data_and_rep_toks2commit (log_entry_request_data entry) x).
    autorewrite with pbft.
    dands; auto; eauto 2 with pbft.
  Qed.

  Lemma rt_rep_prepare2rep_toks_of_commit :
    forall i keys p,
      rt_rep (prepare2rep_toks_of_commit i keys p) = i.
  Proof.
    introv; destruct p, b; simpl; auto.
  Qed.
  Hint Rewrite rt_rep_prepare2rep_toks_of_commit : pbft.

  Lemma check_one_stable_preserves_commit_in_log :
    forall com i s l,
      well_formed_log (log s)
      -> commit_in_log com (log (check_one_stable i s l)) = true
      -> commit_in_log com (log s) = true.
  Proof.
    induction l; introv wf comm; simpl in *; smash_pbft.
  Qed.
  Hint Resolve check_one_stable_preserves_commit_in_log : pbft.

  Lemma commits_are_received_or_generated :
    forall (eo : EventOrdering) c i,
      received_or_generated
        eo
        (PBFTreplicaSM i)
        (fun e st => commit_in_log c (log st) = true)
        (fun e' st1 st2 e st =>
           verify_commit i (local_keys st1) c = true
           /\ event_triggered_by_message e' (PBFTcommit c))
        (fun e' st1 st2 e st => commit2sender c = i).
  Proof.
    intros eo c i e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv eqst ilog.

    try (rewrite loc_local_pred in ind).

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

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_pre_prepare_and_prepare2log add.

      eapply check_send_replies_preserves_commit_in_log in check;[|eauto].
      simpl in check.
      eapply add_new_pre_prepare_and_prepare2log_preserves_commit_in_log in add;
        [| |eauto]; autorewrite with pbft;auto;[].

      repndors;[try (smash_pbft_ind ind)|];[].
      repnd.
      exists e p st.
      dands; auto; eauto 3 with eo.

      right. subst.
      autorewrite with pbft in *. auto.
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_prepare2log add.

      eapply check_send_replies_preserves_commit_in_log in check;[|eauto].
      simpl in check.
      eapply add_new_prepare2log_preserves_commit_in_log in add;[|eauto].

      repndors;[try (smash_pbft_ind ind)|];[].
      repnd.
      exists e p st.
      dands; auto; eauto 3 with eo.

      right. subst.
      autorewrite with pbft in *. auto.
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_commit2log add.

      eapply check_send_replies_preserves_commit_in_log in check;[|eauto].
      simpl in check.
      eapply add_new_commit2log_preserves_commit_in_log in add;[|eauto].

      repndors;[try (smash_pbft_ind ind)|];[].
      repnd.

      exists e p st.
      dands; auto; eauto 3 with eo.
      left. subst. dands;
      autorewrite with pbft in *; auto.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with update_state_new_view upd.
      eapply update_state_new_view_preserves_commit_in_log in upd;[| |eauto];
        simpl in *; eauto 4 with pbft;[].
      simpl in *.
      autorewrite with pbft in *.
      try (smash_pbft_ind ind).
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      eapply update_state_new_view_preserves_commit_in_log in upd;[| |eauto];simpl in *; auto.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log2 in add;[|eauto];[].
      repndors;[|exrepnd; subst; autorewrite with pbft; auto];[|].

      {
        autorewrite with pbft in *.
        try (smash_pbft_ind ind).
      }

      {
        exists e p st.
        dands; auto; eauto 3 with eo.
      }
    }
  Qed.

  Lemma PBFTdata_auth_commit2auth_data_some_implies :
    forall i k c,
      PBFTdata_auth (PBFTreplica i) (commit2auth_data c) = Some k
      -> k = PBFTreplica (commit2sender c).
  Proof.
    introv h.
    destruct c; simpl in *; ginv; auto.
  Qed.

  Lemma in_checkpoints2auth_data_implies :
    forall m C,
      In m (checkpoints2auth_data C)
      -> exists c a, m = MkAuthData (PBFTmsg_bare_checkpoint c) a.
  Proof.
    induction C; introv i; simpl in *; tcsp.
    repndors; tcsp.
    subst.
    destruct a; simpl; eexists; eexists; eauto.
  Qed.

  Lemma in_prepared_info2auth_data_implies :
    forall m P,
      In m (prepared_infos2auth_data P)
      -> (exists p a, m = MkAuthData (PBFTmsg_bare_pre_prepare p) a)
         \/ (exists p a, m = MkAuthData (PBFTmsg_bare_prepare p) a)
         \/ (exists r a, m = MkAuthData (PBFTmsg_bare_request r) a).
  Proof.
    induction P; introv i; simpl in *; tcsp.
    allrw in_app_iff.
    repndors; subst; tcsp.

    - destruct a; simpl in *.
      destruct prepared_info_pre_prepare; simpl in *.
      left; eexists; eexists; eauto.

    - clear IHP.
      destruct a; simpl in *.
      destruct prepared_info_pre_prepare, b; simpl in *.
      unfold pre_prepare2auth_data_req in *; simpl in *.
      allrw in_map_iff; exrepnd; subst.
      destruct x, b; simpl in *; right; right; eexists; eexists; eauto.

    - clear IHP.
      destruct a; simpl in *.
      right; left.
      induction prepared_info_prepares; simpl in *; tcsp; repndors; subst; tcsp.
      destruct a; simpl.
      eexists; eexists; eauto.
  Qed.

  Lemma in_view_change2auth_data_implies :
    forall m v,
      In m (view_change2auth_data v)
      -> (exists v a, m = MkAuthData (PBFTmsg_bare_view_change v) a)
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

  Lemma in_view_changes2auth_data_implies :
    forall m v,
      In m (view_changes2auth_data v)
      -> (exists v a, m = MkAuthData (PBFTmsg_bare_view_change v) a)
         \/ (exists c a, m = MkAuthData (PBFTmsg_bare_checkpoint c) a)
         \/ (exists p a, m = MkAuthData (PBFTmsg_bare_pre_prepare p) a)
         \/ (exists p a, m = MkAuthData (PBFTmsg_bare_prepare p) a)
         \/ (exists r a, m = MkAuthData (PBFTmsg_bare_request r) a).
  Proof.
    induction v; introv i; simpl in i; tcsp.
    allrw in_app_iff; repndors; tcsp.
    apply in_view_change2auth_data_implies in i; auto.
  Qed.

  Lemma in_pre_prepares2auth_data_implies :
    forall m P,
      In m (pre_prepares2auth_data P)
      -> (exists p a, m = MkAuthData (PBFTmsg_bare_pre_prepare p) a)
         \/ (exists r a, m = MkAuthData (PBFTmsg_bare_request r) a).
  Proof.
    induction P; introv i; simpl in i; tcsp.
    allrw in_app_iff; repndors; tcsp.
    - subst; destruct a; simpl; left; eexists; eexists; eauto.
    - destruct a, b; simpl in *.
      unfold pre_prepare2auth_data_req in i; simpl in i.
      allrw in_map_iff; exrepnd; subst.
      destruct x, b; simpl in *; right; eexists; eexists; eauto.
  Qed.

  Lemma in_new_view2auth_data_implies :
    forall m v,
      In m (new_view2auth_data v)
      -> (exists v a, m = MkAuthData (PBFTmsg_bare_new_view v) a)
         \/ (exists v a, m = MkAuthData (PBFTmsg_bare_view_change v) a)
         \/ (exists c a, m = MkAuthData (PBFTmsg_bare_checkpoint c) a)
         \/ (exists p a, m = MkAuthData (PBFTmsg_bare_pre_prepare p) a)
         \/ (exists p a, m = MkAuthData (PBFTmsg_bare_prepare p) a)
         \/ (exists r a, m = MkAuthData (PBFTmsg_bare_request r) a).
  Proof.
    introv i.
    destruct v, v; simpl in *; repndors; subst; ginv; auto.

    { left; eexists; eexists; eauto. }

    allrw in_app_iff; repndors; tcsp; ginv.

    - apply in_view_changes2auth_data_implies in i; right; auto.

    - apply in_pre_prepares2auth_data_implies in i; right; right; right; repndors; tcsp;
        try (complete (left; auto));
        try (complete (right; auto)).

    - apply in_pre_prepares2auth_data_implies in i; right; right; right; repndors; tcsp;
        try (complete (left; auto));
        try (complete (right; auto)).
  Qed.

  Lemma in_pre_prepare2auth_data_req_implies :
    forall m p,
      In m (pre_prepare2auth_data_req p)
      -> exists r a, m = MkAuthData (PBFTmsg_bare_request r) a.
  Proof.
    destruct p, b; introv i; simpl in *.
    unfold pre_prepare2auth_data_req in i; simpl in i.
    allrw in_map_iff; exrepnd; subst.
    destruct x, b; simpl in *; eexists; eexists; eauto.
  Qed.

  Lemma commit2auth_data_in_get_contained_auth_data_implies :
    forall c m,
      In (commit2auth_data c) (PBFTget_contained_auth_data m)
      -> m = PBFTcommit c.
  Proof.
    introv i.
    destruct m, c, b; simpl in *; repndors; tcsp;
      try (complete (destruct r; simpl in *; ginv));
      try (complete (destruct p; simpl in *; ginv));
      try (complete (destruct c0; simpl in *; ginv; auto));[| |].

    { apply in_pre_prepare2auth_data_req_implies in i; repndors; exrepnd; ginv. }

    { apply in_view_change2auth_data_implies in i; repndors; exrepnd; ginv. }

    { apply in_new_view2auth_data_implies in i; repndors; exrepnd; ginv. }
  Qed.

  Lemma in_check_broadcast_commit_implies2 :
    forall x i rd entryop,
      In x (check_broadcast_commit i rd entryop)
      ->
      exists c prep entry,
        entryop = Some (MkGeneratedInfo prep (add_commit_status_added c) entry)
        /\ is_prepared_entry entry = true
        /\ x = send_commit (request_data_and_rep_toks2commit rd c) (other_names i).
  Proof.
    introv j.
    destruct entryop; simpl in *; tcsp.
    destruct g; smash_pbft.
    destruct gi_commit; simpl in *; tcsp; smash_pbft.
    eexists; eexists; eexists; eauto.
  Qed.

  Lemma add_new_pre_prepare_and_prepare2log_add_commit_status_added_implies_commit_in_log :
    forall i L pp d Fp Fc prep rt entry K,
      add_new_pre_prepare_and_prepare2log i L pp d Fp Fc
      = (Some (MkGeneratedInfo prep (add_commit_status_added rt) entry), K)
      -> commit_in_log (request_data_and_rep_toks2commit (pre_prepare2request_data pp d) rt) K = true.
  Proof.
    induction L; introv add; simpl in *; pbft_simplifier; simpl in *; smash_pbft;[| |].

    - destruct a, log_entry_pre_prepare_info; simpl in *; ginv.
      smash_pbft;[].
      subst; simpl in *.
      unfold add_commit_if_prepared in *; smash_pbft.

    - destruct a, log_entry_pre_prepare_info; simpl in *; smash_pbft.

    - allrw similar_entry_and_pre_prepare_false_iff; tcsp.
  Qed.
  Hint Resolve add_new_pre_prepare_and_prepare2log_add_commit_status_added_implies_commit_in_log : pbft.

  Lemma add_new_prepare2log_add_commit_status_added_implies_commit_in_log :
    forall i L p Fc prep rt entry K,
      add_new_prepare2log i L p Fc
      = (Some (MkGeneratedInfo prep (add_commit_status_added rt) entry), K)
      -> commit_in_log (request_data_and_rep_toks2commit (prepare2request_data p) rt) K = true.
  Proof.
    induction L; introv add; simpl in *; pbft_simplifier; simpl in *; smash_pbft;[| |].

    - destruct a, log_entry_pre_prepare_info; simpl in *; ginv; smash_pbft;[].
      subst; simpl in *.
      unfold add_commit_if_prepared in *; smash_pbft.

    - destruct a, log_entry_pre_prepare_info; simpl in *; ginv; smash_pbft;[].
      unfold is_prepare_for_entry, eq_request_data in *; simpl in *; smash_pbft.

    - unfold is_prepare_for_entry, eq_request_data in *; simpl in *; smash_pbft.
  Qed.
  Hint Resolve add_new_prepare2log_add_commit_status_added_implies_commit_in_log : pbft.

  Lemma commit_in_add_prepare_to_log_from_new_view_pre_prepare_is_in_log :
    forall c dst i s1 a s2 msgs,
      add_prepare_to_log_from_new_view_pre_prepare i s1 a = (s2, msgs)
      -> In (send_commit c dst) msgs
      -> commit_in_log c (log s2) = true.
  Proof.
    introv add j.
    unfold add_prepare_to_log_from_new_view_pre_prepare in add; smash_pbft;
      allrw in_app_iff; repndors; try conflicting_sends;
        try (rename_hyp_with add_new_pre_prepare_and_prepare2log add);
        try (rename_hyp_with check_send_replies check);[| |].

    - eapply check_send_replies_preserves_commit_in_log_forward;[eauto|].
      simpl.
      clear check.

      destruct x2; simpl in *; smash_pbft;[].
      destruct g; smash_pbft;[].
      destruct gi_prepare; smash_pbft.

    - eapply check_send_replies_preserves_commit_in_log_forward;[eauto|].
      simpl.
      clear check.

      destruct x2; simpl in *; smash_pbft;[].
      destruct g; smash_pbft;[].
      destruct gi_commit; smash_pbft.

      unfold broadcast2others in *; ginv.
      eauto 3 with pbft.

    - eapply check_send_replies_preserves_commit_in_log_forward;[eauto|].
      simpl.
      eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
  Qed.
  Hint Resolve commit_in_add_prepare_to_log_from_new_view_pre_prepare_is_in_log : pbft.

  Lemma commit_in_add_prepares_to_log_from_new_view_pre_prepares_is_in_log :
    forall c dst i L s1 s2 msgs,
      In (send_commit c dst) msgs
      -> add_prepares_to_log_from_new_view_pre_prepares i s1 L = (s2, msgs)
      -> commit_in_log c (log s2) = true.
  Proof.
    induction L; introv j add; simpl in *; pbft_simplifier; simpl in *; tcsp.
    smash_pbft;[].
    allrw in_app_iff;repndors;[|eapply IHL;eauto];[].

    rename_hyp_with add_prepare_to_log_from_new_view_pre_prepare add.
    rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares adds.
    eauto 3 with pbft.
  Qed.
  Hint Resolve commit_in_add_prepares_to_log_from_new_view_pre_prepares_is_in_log : pbft.

  Lemma send_commit_in_trim_outputs_with_low_water_mark :
    forall c dst msgs st,
      In (send_commit c dst) (trim_outputs_with_low_water_mark msgs st)
      -> In (send_commit c dst) msgs
         /\ low_water_mark st < commit2seq c.
  Proof.
    introv i.
    unfold trim_outputs_with_low_water_mark in i.
    apply filter_In in i; repnd.
    unfold trim_output_with_low_water_mark in i; simpl in i; smash_pbft.
  Qed.

  Lemma sent_commits_are_in_log :
    forall (eo : EventOrdering) (e : Event) c dst st i,
      loc e = PBFTreplica i
      -> In (send_commit c dst) (output_system_on_event_ldata PBFTsys e)
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> commit_in_log c (log st) = true.
  Proof.
    introv eqloce j eqst.
    apply in_output_system_on_event_ldata in j.

    unfold PBFTsys in j.
    rewrite eqloce in j.

    rw @loutput_sm_on_event_unroll2 in j.
    fold (@DirectedMsgs _ _) in *.
    simpl in *.
    rewrite state_sm_on_event_unroll2 in eqst.

    match goal with
    | [ H : context[state_sm_before_event ?a ?b] |- _ ] =>
      remember (state_sm_before_event a b) as q; clear Heqq
    end.
    destruct q; simpl in *; ginv;[].

    op_st_some m eqtrig; rewrite eqtrig in *; simpl in *.

    unfold PBFTreplica_update in *.
    destruct m; simpl in *; ginv; subst; tcsp;
      smash_handlers; try conflicting_sends; try (repndors; ginv; smash_pbft).

    {
      (* pre-prepare *)

      allrw in_app_iff.

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_pre_prepare_and_prepare2log add.

      applydup check_send_replies_preserves_log in check; rewrite check0; clear check0.
      simpl.
      repndors;[| |].

      - apply in_check_broadcast_prepare_implies in j; exrepnd; subst; ginv.

      - apply in_check_broadcast_commit_implies2 in j; exrepnd.
        subst; simpl in *; ginv; eauto 2 with pbft.

      - eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.

      allrw in_app_iff.
      repndors;[|].

      - apply in_check_broadcast_commit_implies2 in j; exrepnd.
        subst; simpl in *; ginv; eauto 2 with pbft; smash_pbft.

      - eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.
      eapply message_in_find_and_execute_requests_implies in fexec;[|eauto].
      repndors; exrepnd; conflicting_sends.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with update_state_new_view upd.

      unfold broadcast2others in *; repndors; ginv;[].
      eapply message_in_update_state_new_view_implies in upd;[|eauto].
      exrepnd; ginv.
    }

    {
      (* new_view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      allrw in_app_iff; repndors;
        [|eapply message_in_update_state_new_view_implies in upd;
          [|eauto];exrepnd;ginv];[].

      apply send_commit_in_trim_outputs_with_low_water_mark in j; repnd.
      eapply commit_in_add_prepares_to_log_from_new_view_pre_prepares_is_in_log in add;[|eauto].
      match goal with
      | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
      end.
      eapply update_state_new_view_preserves_commit_in_log_false_forward in upd; eauto.
    }
  Qed.

  Lemma commit_received_from_good_replica_was_in_log :
    forall (eo : EventOrdering) (e : Event) good c i,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> node_has_correct_trace_before e good
      -> commit2sender c = good
      -> verify_commit i (keys e) c = true
      -> event_triggered_by_message e (PBFTcommit c)
      ->
      exists e' st,
        e' ≺ e
        /\ loc e' = PBFTreplica good
        /\ state_sm_on_event (PBFTreplicaSM good) e' = Some st
        /\ commit_in_log c (log st) = true.
  Proof.
    introv sendbyz ckeys eqloc cortrace goodprep verif iauth.

    apply implies_authenticated_messages_were_sent_non_byz in sendbyz.
    pose proof (sendbyz e (commit2auth_data c) (PBFTreplica good)) as sb.
    rewrite eqloc in sb; simpl in sb; repeat (autodimp sb hyp); eauto 2 with pbft;
      try (complete (unfold auth_data_in_trigger; allrw; simpl; tcsp));
      try (complete (subst; destruct c; simpl; auto)).

    exrepnd.

    clear sb2 sendbyz verif iauth.

    applydup commit2auth_data_in_get_contained_auth_data_implies in sb3.
    subst m; simpl in *; autodimp sb4 hyp; repndors; tcsp; GC;[].

    pose proof (PBFTnever_stops_on_event eo e' good) as q.
    repeat (autodimp q hyp); eauto 3 with pbft eo;[].
    exrepnd.

    rename_hyp_with @output_system_on_event_ldata sendprep.
    apply send_commit_no_delay in sendprep.
    eapply sent_commits_are_in_log in sendprep;[| |eauto]; auto;[].

    exists e' st.
    dands; auto; eauto 3 with pbft.
  Qed.

End PBFTsent_commits_are_in_log.


Hint Resolve length_remove_elt_le : list.
Hint Resolve length_remove_elt_if_in : list.
Hint Resolve disjoint_remove_elt_right_and_not_in_implies : list.
Hint Resolve subset_diff_l_same_r : list.
Hint Resolve disjoint_nil_r : list.
Hint Resolve disjoint_diff_l_same_l : list.
Hint Resolve implies_no_repeats_remove : list.
Hint Resolve implies_no_repeats_diff : list.
Hint Resolve no_repeats_implies_le_length_diff : list.


Hint Rewrite @diff_same : list.


Hint Resolve implies_no_repeats_entry2prep_senders : pbft.
Hint Resolve implies_no_repeats_entry2com_senders : pbft.
Hint Resolve implies_commit_in_log : pbft.
Hint Resolve add_new_pre_prepare_and_prepare2log_add_commit_status_added_implies_commit_in_log : pbft.
Hint Resolve add_new_prepare2log_add_commit_status_added_implies_commit_in_log : pbft.
Hint Resolve commit_in_add_prepare_to_log_from_new_view_pre_prepare_is_in_log : pbft.
Hint Resolve commit_in_add_prepares_to_log_from_new_view_pre_prepares_is_in_log : pbft.
Hint Resolve check_one_stable_preserves_commit_in_log : pbft.


Hint Rewrite @commit2request_data_request_data_and_rep_toks2commit : pbft.
Hint Rewrite @commit2sender_request_data_and_rep_toks2commit : pbft.
Hint Rewrite @commit2rep_toks_request_data_and_rep_toks2commit : pbft.
Hint Rewrite @same_rep_tok_same : pbft.
Hint Rewrite @rt_rep_prepare2rep_toks_of_commit : pbft.
