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


Require Export PBFTview_changes_from_good.
Require Export PBFTwf_checkpoint_state.
Require Export PBFTexecute.
Require Export PBFT_A_1_2_6.
Require Export PBFTdelay_of_send_checkpoints.
Require Export PBFTwf_view_change_state_no_repeats.
Require Export PBFTnew_view_learns_or_knows.
Require Export PBFTknows_own_new_view.


Section PBFTcheckpoints_from_good.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma verify_view_change_implies_verify_checkpoint :
    forall i keys vc cp,
      In cp (view_change2cert vc)
      -> verify_view_change i keys vc = true
      -> verify_checkpoint i keys cp = true.
  Proof.
    introv j verif.
    destruct vc, v; simpl in *.
    unfold verify_view_change in verif; simpl in *; smash_pbft.
    clear verif.
    allrw verify_list_auth_data_app; smash_pbft.
    clear verif1.
    induction C; simpl in *; tcsp; repndors; subst; tcsp; smash_pbft.
  Qed.
  Hint Resolve verify_view_change_implies_verify_checkpoint : pbft.

  Lemma implies_checkpoint2auth_data_in_new_view2auth_data :
    forall nv vc cp,
      In vc (new_view2cert nv)
      -> In cp (view_change2cert vc)
      -> In (checkpoint2auth_data cp) (new_view2auth_data nv).
  Proof.
    introv i j.
    destruct nv, v; simpl in *.
    destruct vc, v0; simpl in *.
    right.
    allrw in_app_iff.
    left.
    induction V; simpl in *; tcsp; repndors; subst; tcsp; smash_pbft.

    clear IHV.
    right.
    allrw in_app_iff.
    left; left.
    induction C; simpl in *; tcsp; repndors; subst; tcsp; smash_pbft.
  Qed.
  Hint Resolve implies_checkpoint2auth_data_in_new_view2auth_data : pbft.

  Lemma PBFT_data_auth_checkpoint2auth_data_some_implies :
    forall i cp k,
      PBFTdata_auth (PBFTreplica i) (checkpoint2auth_data cp) = Some k
      -> k = PBFTreplica (checkpoint2sender cp).
  Proof.
    destruct cp, b; introv h; simpl in *; ginv; auto.
  Qed.

  Lemma in_checkpoints2auth_data_implies2 :
    forall m C,
      In m (checkpoints2auth_data C)
      -> exists c a,
        m = MkAuthData (PBFTmsg_bare_checkpoint c) a
        /\ In (checkpoint c a) C.
  Proof.
    induction C; introv i; simpl in *; tcsp.
    repndors; tcsp; subst; tcsp.
    - destruct a; simpl; eexists; eexists; eauto.
    - autodimp IHC hyp; exrepnd; subst.
      exists c a0; dands; auto.
  Qed.

  Lemma in_view_change2auth_data_implies3 :
    forall m v,
      In m (view_change2auth_data v)
      -> (exists w a, m = MkAuthData (PBFTmsg_bare_view_change w) a /\ v = view_change w a)
         \/ (exists c a, m = MkAuthData (PBFTmsg_bare_checkpoint c) a /\ In (checkpoint c a) (view_change2cert v))
         \/ (exists p a, m = MkAuthData (PBFTmsg_bare_pre_prepare p) a)
         \/ (exists p a, m = MkAuthData (PBFTmsg_bare_prepare p) a)
         \/ (exists r a, m = MkAuthData (PBFTmsg_bare_request r) a).
  Proof.
    introv i.
    destruct v, v; simpl in *; repndors; subst; ginv; auto.

    { left; eexists; eexists; eauto. }

    allrw in_app_iff; repndors.

    - apply in_checkpoints2auth_data_implies2 in i; tcsp.
      right; left; auto.

    - apply in_prepared_info2auth_data_implies in i; repndors; tcsp;
        try (complete (right; right; left; auto));
        try (complete (right; right; right; auto)).
  Qed.

  Lemma in_view_changes2auth_data_implies3 :
    forall m V,
      In m (view_changes2auth_data V)
      -> (exists v a, m = MkAuthData (PBFTmsg_bare_view_change v) a /\ In (view_change v a) V)
         \/ (exists vc c a, m = MkAuthData (PBFTmsg_bare_checkpoint c) a /\ In vc V /\ In (checkpoint c a) (view_change2cert vc))
         \/ (exists p a, m = MkAuthData (PBFTmsg_bare_pre_prepare p) a)
         \/ (exists p a, m = MkAuthData (PBFTmsg_bare_prepare p) a)
         \/ (exists r a, m = MkAuthData (PBFTmsg_bare_request r) a).
  Proof.
    induction V; introv i; simpl in i; tcsp.
    allrw in_app_iff; repndors; tcsp.

    - apply in_view_change2auth_data_implies3 in i; auto.
      repndors; tcsp;
        try (complete (right; left; tcsp));
        try (complete (right; right; left; tcsp));
        try (complete (right; right; right; tcsp));
        try (complete (right; right; right; left; tcsp));
        try (complete (right; right; right; right; tcsp)).

      + left.
        simpl.
        exrepnd; subst.
        eexists; eexists; dands; eauto.

      + exrepnd; subst.
        right; left.
        eexists; eexists; eexists; dands; eauto; simpl; tcsp.

    - autodimp IHV hyp.
      repndors; tcsp;
        try (complete (right; left; tcsp));
        try (complete (right; right; left; tcsp));
        try (complete (right; right; right; tcsp));
        try (complete (right; right; right; left; tcsp));
        try (complete (right; right; right; right; tcsp)).

      + left.
        simpl.
        exrepnd; subst.
        eexists; eexists; dands; eauto.

      + exrepnd; subst.
        right; left.
        eexists; eexists; eexists; dands; eauto; simpl; tcsp.
  Qed.

  Lemma checkpoint2auth_data_in_get_contained_auth_data_implies :
    forall cp m,
      In (checkpoint2auth_data cp) (PBFTget_contained_auth_data m)
      -> m = PBFTcheckpoint cp
         \/ (exists vc, m = PBFTview_change vc /\ In cp (view_change2cert vc))
         \/ (exists nv vc, m = PBFTnew_view nv /\ In vc (new_view2cert nv) /\ In cp (view_change2cert vc)).
  Proof.
    introv i.
    destruct m, cp, b; simpl in *; repndors; tcsp;
      try (complete (destruct r; simpl in *; ginv; tcsp));
      try (complete (destruct p; simpl in *; ginv; tcsp));
      try (complete (destruct c; simpl in *; ginv; tcsp));[| |].

    - unfold pre_prepare2auth_data_req in i; simpl in i.
      allrw in_map_iff; exrepnd.
      destruct x, b; simpl in *; ginv.

    - destruct v, v; simpl in *; repndors; ginv; tcsp;[].
      apply in_app_iff in i; repndors.

      + apply in_checkpoints2auth_data_implies2 in i; exrepnd; ginv.
        right; left.
        eexists; dands; eauto.

      + apply in_prepared_info2auth_data_implies in i; repndors; exrepnd; ginv.

    - destruct v, v; simpl in *; repndors; ginv; tcsp;[].
      allrw in_app_iff; repndors;
        try (complete (eapply in_pre_prepares2auth_data_implies in i; repndors; exrepnd; ginv));[].

      applydup in_view_changes2auth_data_implies3 in i.
      repndors; exrepnd; ginv.
      right; right.
      eexists; eexists; dands; eauto.
  Qed.

  Definition state2hash (s : PBFTstate) : PBFTdigest :=
    create_hash_state_last_reply (PBFT.sm_state s) (last_reply_state s).

  Lemma checkpoint_in_output_of_find_and_execute_requests_implies :
    forall i v keys s1 msgs s2 cp dst,
      find_and_execute_requests i v keys s1 = (msgs, s2)
      -> In (send_checkpoint cp dst) msgs
      -> checkpoint2seq cp = next_to_execute s1
         /\ next_to_execute s2 = next_seq (next_to_execute s1)
         /\ checkpoint2digest cp = state2hash s2.
  Proof.
    introv fexec j.
    unfold find_and_execute_requests in fexec; smash_pbft.
    unfold execute_requests in *.
    destruct (ready s1); pbft_simplifier; simpl in *; tcsp.
    smash_pbft.
    allrw in_app_iff; simpl in *.
    repndors; ginv;[allrw in_map_iff; exrepnd; ginv|].

    rename_hyp_with check_broadcast_checkpoint check.
    unfold check_broadcast_checkpoint in check; simpl in *; smash_pbft.
    repndors; ginv; tcsp.
    unfold broadcast2others in *; ginv.
  Qed.

  Definition mk_checkpoint
             (v : View)
             (n : SeqNum)
             (d : PBFTdigest)
             (i : Rep)
             (a : Tokens) : Checkpoint :=
    checkpoint (bare_checkpoint v n d i) a.

  Lemma message_in_update_state_new_view_implies :
    forall i s1 nv s2 msgs x,
      update_state_new_view i s1 nv = (s2, msgs)
      -> In x msgs
      -> exists maxV vc a dst,
          view_change_cert2max_seq_vc (new_view2cert nv) = Some (maxV, vc)
          /\ low_water_mark s1 < maxV
          /\ x = send_checkpoint
                   (mk_checkpoint
                      (view_change2view vc)
                      maxV
                      (create_hash_state_last_reply (si_state (view_change2stable vc)) (si_lastr (view_change2stable vc)))
                      i
                      a)
                   dst.
  Proof.
    introv upd j.
    unfold update_state_new_view in upd; smash_pbft;[].
    unfold broadcast_checkpoint_op in j; smash_pbft;[].
    unfold log_checkpoint_cert_from_new_view in *; simpl in *; smash_pbft.
    simpl in *; autorewrite with pbft.
    unfold mk_checkpoint, mk_auth_checkpoint, broadcast2others.
    repeat (eexists;[]); dands; eauto.
  Qed.

  Lemma correct_view_change_implies_no_repeats :
    forall v vc,
      correct_view_change v vc = true
      -> no_repeats (map checkpoint2sender (view_change2cert vc)).
  Proof.
    introv cor.
    unfold correct_view_change, correct_view_change_cert in cor; smash_pbft.
    apply norepeatsb_as_no_repeats in cor2; auto.
  Qed.
  Hint Resolve correct_view_change_implies_no_repeats : pbft.

  Lemma correct_view_change_implies_length :
    forall v vc,
      correct_view_change v vc = true
      -> F + 1 <= length (map checkpoint2sender (view_change2cert vc)).
  Proof.
    introv cor; unfold correct_view_change, correct_view_change_cert in cor; smash_pbft.
    autorewrite with list; auto.
  Qed.
  Hint Resolve correct_view_change_implies_length : pbft.

  Lemma correct_view_change_implies_correct_view_change_cert_one :
    forall v vc cp,
      correct_view_change v vc = true
      -> In cp (view_change2cert vc)
      -> correct_view_change_cert_one
           (view_change2seq vc)
           (view_change2view vc)
           (view_change2stable vc)
           cp = true.
  Proof.
    introv cor i; unfold correct_view_change, correct_view_change_cert in cor; smash_pbft.
    allrw forallb_forall; tcsp.
  Qed.

  Lemma correct_view_change_cert_one_implies :
    forall n v s cp,
      correct_view_change_cert_one n v s cp = true
      -> n = checkpoint2seq cp
         /\ checkpoint2view cp < v
         /\ checkpoint2digest cp = StableChkPt2digest s.
  Proof.
    introv cor; unfold correct_view_change_cert_one in cor; smash_pbft.
    unfold same_digests, same_seq_nums in *; smash_pbft.
  Qed.

  Lemma send_checkpoint_in_trim_outputs_with_low_water_mark :
    forall c dst msgs st,
      In (send_checkpoint c dst) (trim_outputs_with_low_water_mark msgs st)
      -> In (send_checkpoint c dst) msgs.
  Proof.
    introv i.
    unfold trim_outputs_with_low_water_mark in i.
    apply filter_In in i; repnd.
    unfold trim_output_with_low_water_mark in i; simpl in i; smash_pbft.
  Qed.
  Hint Resolve send_checkpoint_in_trim_outputs_with_low_water_mark : pbft.

  Lemma check_send_replies_preserves_checkpoint_certificate_of_last_stable_checkpoint :
    forall i v keys giop s1 n msgs s2,
      check_send_replies i v keys giop s1 n = (msgs, s2)
      -> checkpoint_certificate_of_last_stable_checkpoint s2
         = checkpoint_certificate_of_last_stable_checkpoint s1.
  Proof.
    introv check; unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.

  Lemma checkpoint_certificate_of_last_stable_checkpoint_update_log :
    forall s L,
      checkpoint_certificate_of_last_stable_checkpoint (update_log s L)
      = checkpoint_certificate_of_last_stable_checkpoint s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite checkpoint_certificate_of_last_stable_checkpoint_update_log : pbft.

  Lemma checkpoint_certificate_of_last_stable_checkpoint_trim_checkpoint :
    forall s n,
      checkpoint_certificate_of_last_stable_checkpoint (trim_checkpoint s n)
      = checkpoint_certificate_of_last_stable_checkpoint s.
  Proof.
    introv; unfold trim_checkpoint, checkpoint_certificate_of_last_stable_checkpoint; simpl.
    unfold trim_checkpoint_state; destruct s, cp_state; simpl; auto.
  Qed.
  Hint Rewrite checkpoint_certificate_of_last_stable_checkpoint_trim_checkpoint : pbft.

  Lemma checkpoint_certificate_of_last_stable_checkpoint_update_log_checkpoint_stable :
    forall s e,
      checkpoint_certificate_of_last_stable_checkpoint (update_log_checkpoint_stable s e)
      = scp_checkpoint e.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite checkpoint_certificate_of_last_stable_checkpoint_update_log_checkpoint_stable : pbft.

  Lemma checkpoint_entry2stable_preserves_in_checkpoints :
    forall e se,
      checkpoint_entry2stable e = Some se
      -> scp_checkpoint se = cp_checkpoint e.
  Proof.
    introv check; destruct e; simpl in *; smash_pbft.
  Qed.

  Lemma checkpoint_entry2stable_preserves_in_checkpoints_backward :
    forall e se cp,
      checkpoint_entry2stable e = Some se
      -> In cp (scp_checkpoint se)
      -> In cp (cp_checkpoint e).
  Proof.
    introv check i.
    apply checkpoint_entry2stable_preserves_in_checkpoints in check.
    rewrite <- check; auto.
  Qed.
  Hint Resolve checkpoint_entry2stable_preserves_in_checkpoints_backward : pbft.

  Lemma checkpoint_entry2stable_preserves_in_checkpoints_forward :
    forall e se cp,
      checkpoint_entry2stable e = Some se
      -> In cp (cp_checkpoint e)
      -> In cp (scp_checkpoint se).
  Proof.
    introv check i.
    apply checkpoint_entry2stable_preserves_in_checkpoints in check.
    rewrite check; auto.
  Qed.
  Hint Resolve checkpoint_entry2stable_preserves_in_checkpoints_forward : pbft.

  Lemma check_stable_preserves_checkpoint_certificate_of_last_stable_checkpoint :
    forall i s1 e s2 cp,
      check_stable i s1 e = Some s2
      -> In cp (checkpoint_certificate_of_last_stable_checkpoint s2)
      -> is_stable_checkpoint_entry e = true
         /\ In cp (cp_checkpoint e).
  Proof.
    introv check j; unfold check_stable in check; smash_pbft.
  Qed.

  Lemma add_new_checkpoint2cp_log_preserves_sn_and_digest :
    forall l1 smstate lr c e l2,
      add_new_checkpoint2cp_log l1 smstate lr c = (Some e, l2)
      ->
      cp_sn e = checkpoint2seq c
      /\ cp_d e = checkpoint2digest c
      /\ In e l2.
  Proof.
    induction l1; introv add; repeat (simpl in *; smash_pbft);
      try (complete (dands; tcsp)); try (complete (discover; tcsp)).

    unfold is_checkpoint_for_entry in *.
    unfold similar_sn_and_checkpoint_sn in *; smash_pbft.
    unfold add_checkpoint2entry in *; destruct a; simpl in *; smash_pbft.
  Qed.

  Lemma add_new_checkpoint2cp_state_preserves_sn_and_digest :
    forall cpstate smstate lr c ce cs,
      add_new_checkpoint2cp_state cpstate smstate lr c = (Some ce, cs)
      ->
      cp_sn ce = checkpoint2seq c
      /\ cp_d ce = checkpoint2digest c
      /\ In ce (chk_state_others cs).
  Proof.
    introv add.
    unfold add_new_checkpoint2cp_state in add; smash_pbft.
    eapply add_new_checkpoint2cp_log_preserves_sn_and_digest; eauto.
  Qed.

  Lemma wf_checkpoint_state_implies_wf_stable :
    forall s,
      wf_checkpoint_state s = true
      -> wf_stable_checkpoint_entry (chk_state_stable s) = true.
  Proof.
    introv wf.
    unfold wf_checkpoint_state in wf; smash_pbft.
  Qed.
  Hint Resolve wf_checkpoint_state_implies_wf_stable : pbft.

  Lemma in_wf_checkpoint_entry_implies :
    forall cp e,
      In cp (cp_checkpoint e)
      -> wf_checkpoint_entry e = true
      -> cp_sn e = checkpoint2seq cp
         /\ cp_d e = checkpoint2digest cp.
  Proof.
    introv i wf.
    unfold wf_checkpoint_entry in wf; smash_pbft.
    unfold wf_checkpoint_entry_same_seq_and_digest in *; smash_pbft.
    allrw forallb_forall.
    apply wf in i; clear wf; smash_pbft.
    unfold same_digests, same_seq_nums in *; smash_pbft.
  Qed.

  Lemma add_checkpoint2checkpoint_some_implies_in :
    forall c l k,
      add_checkpoint2checkpoint c l = Some k
      -> In c k.
  Proof.
    induction l; introv add; simpl in *; smash_pbft; simpl; tcsp.
  Qed.
  Hint Resolve add_checkpoint2checkpoint_some_implies_in : pbft.

  Lemma add_new_checkpoint2cp_log_preserves_sn_and_digest2 :
    forall l1 smstate lr c e l2,
      add_new_checkpoint2cp_log l1 smstate lr c = (Some e, l2)
      ->
      cp_sn e = checkpoint2seq c
      /\ cp_d e = checkpoint2digest c
      /\ In e l2
      /\ In c (cp_checkpoint e).
  Proof.
    induction l1; introv add; repeat (simpl in *; smash_pbft);
      try (complete (dands; tcsp)); try (complete (discover; tcsp));[].

    unfold is_checkpoint_for_entry in *.
    unfold similar_sn_and_checkpoint_sn in *; smash_pbft.
    unfold add_checkpoint2entry in *; destruct a; simpl in *; smash_pbft.
    dands; tcsp; eauto 2 with pbft.
  Qed.

  Lemma add_new_checkpoint2cp_state_preserves_sn_and_digest2 :
    forall cpstate smstate lr c ce cs,
      add_new_checkpoint2cp_state cpstate smstate lr c = (Some ce, cs)
      ->
      cp_sn ce = checkpoint2seq c
      /\ cp_d ce = checkpoint2digest c
      /\ In ce (chk_state_others cs)
      /\ In c (cp_checkpoint ce).
  Proof.
    introv add.
    unfold add_new_checkpoint2cp_state in add; smash_pbft.
    eapply add_new_checkpoint2cp_log_preserves_sn_and_digest2; eauto.
  Qed.

  Lemma wf_checkpoint_entry_no_repeats :
    forall e,
      wf_checkpoint_entry e = true
      -> no_repeats (map checkpoint2sender (cp_checkpoint e)).
  Proof.
    introv wf; unfold wf_checkpoint_entry in wf; smash_pbft.
    unfold wf_checkpoint_entry_no_repeats in *.
    apply norepeatsb_as_no_repeats in wf0; auto.
  Qed.

  Lemma is_stable_checkpoint_entry_implies_le :
    forall e,
      is_stable_checkpoint_entry e = true
      -> F + 1 <= length (cp_checkpoint e).
  Proof.
    introv stable; unfold is_stable_checkpoint_entry in stable; smash_pbft.
  Qed.
  Hint Resolve is_stable_checkpoint_entry_implies_le : pbft.

  Definition checkpoint_in_log (c : Checkpoint) (l : PBFTcheckpoint_log) : Prop :=
    exists e, In e l /\ In c (cp_checkpoint e).

  Definition checkpoint_in_state (c : Checkpoint) (s : PBFTcheckpointState) : Prop :=
    checkpoint_in_log c (chk_state_others s).

  Lemma in_add_checkpoint2entry_implies_or :
    forall a c e cp sm lastr,
      In cp (cp_checkpoint e)
      -> add_checkpoint2entry a c sm lastr = Some e
      -> cp = c \/ In cp (cp_checkpoint a).
  Proof.
    introv i add.
    destruct a; simpl in *; smash_pbft.
    revert dependent x.
    rename cp_checkpoint into l.
    induction l; introv add i; simpl in *; ginv; simpl in *; tcsp; smash_pbft.
    repndors; subst; tcsp.
    discover.
    rename_hyp_with In j.
    apply IHl in j; tcsp.
  Qed.

  Lemma implies_checkpoint_in_log_cons :
    forall cp a l,
      checkpoint_in_log cp l
      -> checkpoint_in_log cp (a :: l).
  Proof.
    introv check; unfold checkpoint_in_log in *; exrepnd.
    exists e; simpl; dands; tcsp.
  Qed.
  Hint Resolve implies_checkpoint_in_log_cons : pbft.

  Lemma in_add_new_checkpoint2cp_log_implies_or :
    forall l smst lastr c e k cp,
      In cp (cp_checkpoint e)
      -> add_new_checkpoint2cp_log l smst lastr c = (Some e, k)
      -> cp = c \/ checkpoint_in_log cp l.
  Proof.
    induction l; introv i add; repeat (simpl in *; tcsp; smash_pbft).

    - rename_hyp_with add_checkpoint2entry add.
      eapply in_add_checkpoint2entry_implies_or in add;[|eauto]; repndors; tcsp.
      right; exists a; simpl; dands; tcsp.

    - eapply IHl in i;[|eauto]; repndors; tcsp; right; eauto 3 with pbft.
  Qed.

  Lemma in_add_new_checkpoint2cp_state_implies_or :
    forall s1 smst lastr c e s2 cp,
      In cp (cp_checkpoint e)
      -> add_new_checkpoint2cp_state s1 smst lastr c = (Some e, s2)
      -> cp = c \/ checkpoint_in_state cp s1.
  Proof.
    introv i add.
    unfold add_new_checkpoint2cp_state in add; smash_pbft.
    unfold checkpoint_in_state.
    eapply in_add_new_checkpoint2cp_log_implies_or in i;[|eauto];auto.
  Qed.

  Definition checkpoint_in_new_view (cp : Checkpoint) (s : PBFTviewChangeState) :=
    exists nv vc,
      new_view_in_log nv s
      /\ In vc (new_view2cert nv)
      /\ In cp (view_change2cert vc).

  Definition checkpoint_somewhere_in_log (cp : Checkpoint) (s : PBFTstate) :=
    checkpoint_in_new_view cp (view_change_state s)
(*    \/ checkpoint_in_view_change cp (view_change_state s)*)
    \/ In cp (checkpoint_certificate_of_last_stable_checkpoint s)
    \/ checkpoint_in_state cp (cp_state s).

  Lemma checkpoint_in_new_view_implies_somewhere_in_log :
    forall s nv vc cp,
      new_view_in_log nv (view_change_state s)
      -> In vc (new_view2cert nv)
      -> In cp (view_change2cert vc)
      -> checkpoint_somewhere_in_log cp s.
  Proof.
    introv nvinlog vcincert cpincert; left; eexists; eexists; eauto.
  Qed.
  Hint Resolve checkpoint_in_new_view_implies_somewhere_in_log : pbft.

  Lemma checkpoint_in_stable_implies_somewhere_in_log :
    forall cp st,
      In cp (checkpoint_certificate_of_last_stable_checkpoint st)
      -> checkpoint_somewhere_in_log cp st.
  Proof.
    tcsp.
  Qed.
  Hint Resolve checkpoint_in_stable_implies_somewhere_in_log : pbft.

  Lemma implies_checkpoint2auth_data_in_view_change2auth_data :
    forall vc cp,
      In cp (view_change2cert vc)
      -> In (checkpoint2auth_data cp) (view_change2auth_data vc).
  Proof.
    introv i.
    destruct vc, v; simpl in *.
    right.
    allrw in_app_iff.
    left.
    induction C; simpl in *; tcsp; repndors; subst; tcsp; smash_pbft.
  Qed.
  Hint Resolve implies_checkpoint2auth_data_in_view_change2auth_data : pbft.

  Lemma add_new_checkpoint2cp_state_preserves_in_stable :
    forall s1 smst lastr c e s2 cp,
      In cp (scp_checkpoint (chk_state_stable s2))
      -> add_new_checkpoint2cp_state s1 smst lastr c = (e, s2)
      -> In cp (scp_checkpoint (chk_state_stable s1)).
  Proof.
    introv i add.
    unfold add_new_checkpoint2cp_state in add; smash_pbft.
  Qed.
  Hint Resolve add_new_checkpoint2cp_state_preserves_in_stable : pbft.

  Lemma checkpoint_certificate_of_last_stable_checkpoint_decrement_requests_in_progress_if_primary :
    forall i v s,
      checkpoint_certificate_of_last_stable_checkpoint
        (decrement_requests_in_progress_if_primary i v s)
      = checkpoint_certificate_of_last_stable_checkpoint s.
  Proof.
    introv.
    unfold decrement_requests_in_progress_if_primary; smash_pbft.
  Qed.
  Hint Rewrite checkpoint_certificate_of_last_stable_checkpoint_decrement_requests_in_progress_if_primary : pbft.

  Lemma find_and_execute_requests_preserves_in_checkpoint_certificate_of_last_stable_checkpoint :
    forall i v keys s1 msgs s2 cp,
      find_and_execute_requests i v keys s1 = (msgs, s2)
      -> In cp (checkpoint_certificate_of_last_stable_checkpoint s2)
      -> In cp (checkpoint_certificate_of_last_stable_checkpoint s1).
  Proof.
    introv fexec j.
    unfold find_and_execute_requests in fexec; smash_pbft.
    unfold execute_requests in *.
    destruct (ready s1); smash_pbft.
    unfold checkpoint_certificate_of_last_stable_checkpoint in *; simpl in *.
    unfold check_broadcast_checkpoint in *; smash_pbft.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_in_checkpoint_certificate_of_last_stable_checkpoint : pbft.

  Lemma checkpoint_certificate_of_last_stable_checkpoint_change_next_to_execute :
    forall s n,
      checkpoint_certificate_of_last_stable_checkpoint (change_next_to_execute s n)
      = checkpoint_certificate_of_last_stable_checkpoint s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite checkpoint_certificate_of_last_stable_checkpoint_change_next_to_execute : pbft.

  Lemma checkpoint_certificate_of_last_stable_checkpoint_change_sm_state :
    forall s n,
      checkpoint_certificate_of_last_stable_checkpoint (change_sm_state s n)
      = checkpoint_certificate_of_last_stable_checkpoint s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite checkpoint_certificate_of_last_stable_checkpoint_change_sm_state : pbft.

  Lemma checkpoint_certificate_of_last_stable_checkpoint_change_last_reply_state :
    forall s n,
      checkpoint_certificate_of_last_stable_checkpoint (change_last_reply_state s n)
      = checkpoint_certificate_of_last_stable_checkpoint s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite checkpoint_certificate_of_last_stable_checkpoint_change_last_reply_state : pbft.

  Lemma correct_view_change_cert_one_implies_eq_digests :
    forall n v s c,
      correct_view_change_cert_one v n s c = true
      -> checkpoint2digest c = create_hash_state_last_reply (si_state s) (si_lastr s).
  Proof.
    introv cor.
    unfold correct_view_change_cert_one in cor; smash_pbft.
    unfold same_digests in *; smash_pbft.
  Qed.
  Hint Resolve correct_view_change_cert_one_implies_eq_digests : pbft.

  Definition similar_checkpoint_in_new_view (cp : Checkpoint) (nv : NewView) :=
    exists cp' vc,
      In vc (new_view2cert nv)
      /\ checkpoint2digest cp' = checkpoint2digest cp
      /\ checkpoint2seq cp' = checkpoint2seq cp
      /\ In cp' (view_change2cert vc).

  Lemma correct_view_change_cert_one_implies_eq_seq :
    forall n v s c,
      correct_view_change_cert_one n v s c = true
      -> checkpoint2seq c = n.
  Proof.
    introv cor.
    unfold correct_view_change_cert_one in cor; smash_pbft.
    unfold same_seq_nums in *; smash_pbft.
  Qed.
  Hint Resolve correct_view_change_cert_one_implies_eq_seq : pbft.

  Lemma correct_view_change_implies_similar_checkpoint_in_new_view :
    forall vc nv v w i keys,
      In vc (new_view2cert nv)
      -> correct_view_change v vc = true
      -> similar_checkpoint_in_new_view
           (mk_auth_checkpoint
              w
              (view_change2seq vc)
              (StableChkPt2digest (view_change2stable vc))
              i
              keys) nv.
  Proof.
    introv j cor.
    unfold correct_view_change in cor; smash_pbft.
    unfold correct_view_change_cert in cor0; smash_pbft.
    remember (view_change2cert vc) as l.
    destruct l; simpl in *; try omega;[]; smash_pbft.
    exists c vc; simpl.

    assert (In c (view_change2cert vc)) as k.
    { rewrite <- Heql; simpl; tcsp. }

    clear cor4.
    unfold correct_view_change_cert_one in *; smash_pbft.
    unfold same_seq_nums, same_digests in *; smash_pbft.
  Qed.
  Hint Resolve correct_view_change_implies_similar_checkpoint_in_new_view : pbft.


  Lemma update_state_new_view_preserves_checkpoint_certificate_of_last_stable_checkpoint :
    forall i s1 nv s2 msgs cp,
      correct_new_view nv = true
      -> update_state_new_view i s1 nv = (s2, msgs)
      -> In cp (checkpoint_certificate_of_last_stable_checkpoint s2)
      -> similar_checkpoint_in_new_view cp nv
         \/
         In cp (checkpoint_certificate_of_last_stable_checkpoint s1).
  Proof.
    introv cor upd j.
    unfold update_state_new_view in upd; smash_pbft;[].
    autorewrite with pbft in *.

    rename_hyp_with view_change_cert2max_seq_vc mseq.
    applydup view_change_cert2_max_seq_vc_some_in in mseq.
    applydup sn_of_view_change_cert2max_seq_vc in mseq.

    dup mseq0 as corvc.
    apply correct_new_view_implies_correct_view_change in corvc; auto;[].

    unfold update_checkpoint_from_new_view in *; smash_pbft;[|].

    - unfold log_checkpoint_cert_from_new_view in *; smash_pbft; simpl in *; tcsp;[|].

      + left; exists cp; dands; auto; eexists; dands; eauto.

      + fold (StableChkPt2digest (view_change2stable x2)) in *.
        repndors; subst; tcsp;[left; eauto 3 with pbft|];[].
        eauto 3 with pbft.
        left.
        exists cp x2; dands; auto.

    - unfold log_checkpoint_cert_from_new_view in *; smash_pbft; simpl in *; tcsp;[|].

      + left; exists cp; dands; auto; eexists; dands; eauto.

      + fold (StableChkPt2digest (view_change2stable x2)) in *.
        repndors; subst; tcsp;[left; eauto 3 with pbft|];[].
        eauto 3 with pbft.
        left.
        exists cp x2; dands; auto.
  Qed.

  Lemma checkpoint_certificate_of_last_stable_checkpoint_update_view :
    forall s v,
      checkpoint_certificate_of_last_stable_checkpoint (update_view s v)
      = checkpoint_certificate_of_last_stable_checkpoint s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite checkpoint_certificate_of_last_stable_checkpoint_update_view : pbft.

  Lemma checkpoint_certificate_of_last_stable_checkpoint_change_sequence_number :
    forall s v,
      checkpoint_certificate_of_last_stable_checkpoint (change_sequence_number s v)
      = checkpoint_certificate_of_last_stable_checkpoint s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite checkpoint_certificate_of_last_stable_checkpoint_change_sequence_number : pbft.

  Lemma checkpoint_certificate_of_last_stable_checkpoint_log_pre_prepares_of_new_view :
    forall P s,
      checkpoint_certificate_of_last_stable_checkpoint (log_pre_prepares_of_new_view s P)
      = checkpoint_certificate_of_last_stable_checkpoint s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite checkpoint_certificate_of_last_stable_checkpoint_log_pre_prepares_of_new_view : pbft.

  Lemma checkpoint_certificate_of_last_stable_checkpoint_log_new_view_and_entry_state :
    forall s nv e,
      checkpoint_certificate_of_last_stable_checkpoint (log_new_view_and_entry_state s nv e)
      = checkpoint_certificate_of_last_stable_checkpoint s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite checkpoint_certificate_of_last_stable_checkpoint_log_new_view_and_entry_state : pbft.

  Definition checkpoint_in_view_change (cp : Checkpoint) (s : PBFTviewChangeState) :=
    exists vc,
      view_change_in_log vc s
      /\ In cp (view_change2cert vc).

  Definition similar_checkpoint_in_view_change (cp : Checkpoint) (s : PBFTviewChangeState) :=
    exists cp',
      checkpoint2digest cp' = checkpoint2digest cp
      /\ checkpoint2seq cp' = checkpoint2seq cp
      /\ checkpoint_in_view_change cp' s.

  Lemma checkpoint_in_view_change_implies_similar_checkpoint_in_view_change :
    forall cp s,
      checkpoint_in_view_change cp s
      -> similar_checkpoint_in_view_change cp s.
  Proof.
    introv check; exists cp; dands; auto.
  Qed.
  Hint Resolve checkpoint_in_view_change_implies_similar_checkpoint_in_view_change : pbft.

  Definition similar_checkpoint_in_stable (cp : Checkpoint) (s : PBFTstate) :=
    exists cp',
      checkpoint2digest cp' = checkpoint2digest cp
      /\ checkpoint2seq cp' = checkpoint2seq cp
      /\ In cp' (checkpoint_certificate_of_last_stable_checkpoint s).

  Lemma checkpoint_certificate_of_last_stable_checkpoint_log_new_view_state :
    forall s nv,
      checkpoint_certificate_of_last_stable_checkpoint (log_new_view_state s nv)
      = checkpoint_certificate_of_last_stable_checkpoint s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite checkpoint_certificate_of_last_stable_checkpoint_log_new_view_state : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_checkpoint_certificate_of_last_stable_checkpoint :
    forall i ppd s1 s2 msgs cp,
      add_prepare_to_log_from_new_view_pre_prepare i s1 ppd = (s2, msgs)
      -> In cp (checkpoint_certificate_of_last_stable_checkpoint s2)
      -> In cp (checkpoint_certificate_of_last_stable_checkpoint s1).
  Proof.
    introv add j.
    unfold add_prepare_to_log_from_new_view_pre_prepare in add; smash_pbft.
    erewrite check_send_replies_preserves_checkpoint_certificate_of_last_stable_checkpoint in j;[|eauto]; tcsp.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_checkpoint_certificate_of_last_stable_checkpoint : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_checkpoint_certificate_of_last_stable_checkpoint :
    forall i P s1 s2 msgs cp,
      add_prepares_to_log_from_new_view_pre_prepares i s1 P = (s2, msgs)
      -> In cp (checkpoint_certificate_of_last_stable_checkpoint s2)
      -> In cp (checkpoint_certificate_of_last_stable_checkpoint s1).
  Proof.
    induction P; introv add j; simpl in *; tcsp; smash_pbft.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_checkpoint_certificate_of_last_stable_checkpoint : pbft.

  Lemma checkpoint_certificate_of_last_stable_checkpoint_update_checkpoint_state :
    forall s cs,
      checkpoint_certificate_of_last_stable_checkpoint
        (update_checkpoint_state s cs)
      = scp_checkpoint (chk_state_stable cs).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite checkpoint_certificate_of_last_stable_checkpoint_update_checkpoint_state : pbft.

  Lemma in_checkpoint_certificate_of_last_stable_checkpoint_check_one_stable :
    forall cp i s l,
      In cp (checkpoint_certificate_of_last_stable_checkpoint (check_one_stable i s l))
      -> In cp (checkpoint_certificate_of_last_stable_checkpoint s) \/ checkpoint_in_log cp l.
  Proof.
    induction l; introv j; simpl in *; smash_pbft.

    - eapply check_stable_preserves_checkpoint_certificate_of_last_stable_checkpoint in j;[|eauto].
      repnd.
      right.
      exists a; simpl; tcsp.

    - apply IHl in j; repndors; tcsp.
      right; eauto 3 with pbft.

    - apply IHl in j; repndors; tcsp.
      right; eauto 3 with pbft.
  Qed.

  Lemma trace_back_checkpoint_in_certificate :
    forall (eo : EventOrdering) (e : Event) cp i st,
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> In cp (checkpoint_certificate_of_last_stable_checkpoint st)
      -> exists e' st',
          e' ⊑ e
          /\ state_sm_before_event (PBFTreplicaSM i) e' = Some st'
          /\
          (
            (* either we received the checkpoint directly *)
            (
              event_triggered_by_message e' (PBFTcheckpoint cp)
              /\ verify_checkpoint i (local_keys st') cp = true
            )
            \/
            (* or we received a similar checkpoint in a new-view *)
            (
              exists nv,
                event_triggered_by_message e' (PBFTnew_view nv)
                /\ verify_new_view i (local_keys st') nv = true
                /\ correct_new_view nv = true
                /\ similar_checkpoint_in_new_view cp nv
            )
            (* or the checkpoint was in our state *)
            \/ checkpoint_in_state cp (cp_state st')
            (* or a similar checkpoint was in a view change in our state *)
            \/ similar_checkpoint_in_view_change cp (view_change_state st')
            (* or a similar checkpoint was stable *)
            \/ similar_checkpoint_in_stable cp st'
          ).
  Proof.
    intros eo e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv eqst j.

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
      applydup check_send_replies_preserves_checkpoint_certificate_of_last_stable_checkpoint in check as eqcert.
      rewrite eqcert in j; clear eqcert; autorewrite with pbft in *.
      try (smash_pbft_ind ind).
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.
      applydup check_send_replies_preserves_checkpoint_certificate_of_last_stable_checkpoint in check as eqcert.
      rewrite eqcert in j; clear eqcert; autorewrite with pbft in *.
      try (smash_pbft_ind ind).
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      applydup check_send_replies_preserves_checkpoint_certificate_of_last_stable_checkpoint in check as eqcert.
      rewrite eqcert in j; clear eqcert; autorewrite with pbft in *.
      try (smash_pbft_ind ind).
    }

    {
      (* checkpoint *)

      autorewrite with pbft in *.
      eapply add_new_checkpoint2cp_state_preserves_in_stable in j;[|eauto].
      fold (checkpoint_certificate_of_last_stable_checkpoint p) in *.
      try (smash_pbft_ind ind).
    }

    {
      (* check-stable *)

      apply in_checkpoint_certificate_of_last_stable_checkpoint_check_one_stable in j.
      repndors;[try (smash_pbft_ind ind)|];[].

      exists e p; dands; eauto 2 with eo.
      repndors; subst; tcsp.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with update_state_new_view upd.

      apply CheckBCastNewView2entry_some_implies in cb.
      applydup update_state_new_view_preserves_wf in upd; simpl;[|eauto 4 with pbft];[].
      applydup wf_view_change_state_implies_all_entries in cb;[|eauto 3 with pbft];[].

      applydup check_broadcast_new_view_generates in check as cornv.
      eapply update_state_new_view_preserves_checkpoint_certificate_of_last_stable_checkpoint in j;[| |eauto]; auto;[].
      simpl in *; autorewrite with pbft in *.

      repndors;[|try (smash_pbft_ind ind)];[].

      apply check_broadcast_new_view_implies in check.
      exrepnd.
      unfold similar_checkpoint_in_new_view in j; exrepnd.

      dup j0 as corvc.
      apply correct_new_view_implies_correct_view_change in corvc; auto;[].
      applydup correct_view_change_implies_length in corvc;[].

      match goal with
      | [ H1 : new_view2cert _ = _, H2 : In _ (new_view2cert _) |- _ ] => rewrite H1 in H2
      end.
      match goal with
      | [ H1 : view_change_entry2view_changes _ = _, H2 : In _ (view_change_entry2view_changes _) |- _ ] => rewrite H1 in H2
      end.
      simpl in *; repndors.

      - subst vc0.
        subst vc'.
        simpl in *.
        exists e p; dands; eauto 2 with eo.
        right; right; right; right.
        exists cp'; dands; auto.

      - subst; simpl in *.
        autorewrite with pbft in *; GC.

        exists e p; dands; eauto 2 with eo.
        right; right; right; left.
        exists cp'; dands; auto.
        exists vc0; dands; auto; eauto 4 with pbft.
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with correct_new_view cor.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      eapply update_state_new_view_preserves_checkpoint_certificate_of_last_stable_checkpoint in j;[| |eauto]; auto;[].
      simpl in *; autorewrite with pbft in *.

      repndors;
        [|eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_checkpoint_certificate_of_last_stable_checkpoint in j;[|eauto];
          autorewrite  with pbft in *; try (smash_pbft_ind ind)];[].

      exists e p; dands; eauto 2 with eo.
      right; left.
      exists v; dands; auto.
    }
  Qed.

  Lemma two_in_view_change2cert_implies_same_digests :
    forall a b vc v,
      In a (view_change2cert vc)
      -> In b (view_change2cert vc)
      -> correct_view_change v vc = true
      -> checkpoint2digest a = checkpoint2digest b.
  Proof.
    introv i j cor.
    unfold correct_view_change in cor; smash_pbft.
    unfold correct_view_change_cert in *; smash_pbft.
    allrw forallb_forall.
    applydup cor0 in i.
    applydup cor0 in j.
    clear cor0.
    unfold correct_view_change_cert_one in *; smash_pbft.
    unfold same_seq_nums, same_digests in *; smash_pbft.
  Qed.
  Hint Resolve two_in_view_change2cert_implies_same_digests : pbft.

  Lemma two_in_view_change2cert_implies_same_seq_nums :
    forall a b vc v,
      In a (view_change2cert vc)
      -> In b (view_change2cert vc)
      -> correct_view_change v vc = true
      -> checkpoint2seq a = checkpoint2seq b.
  Proof.
    introv i j cor.
    unfold correct_view_change in cor; smash_pbft.
    unfold correct_view_change_cert in *; smash_pbft.
    allrw forallb_forall.
    applydup cor0 in i.
    applydup cor0 in j.
    clear cor0.
    unfold correct_view_change_cert_one in *; smash_pbft.
    unfold same_seq_nums, same_digests in *; smash_pbft.
  Qed.
  Hint Resolve two_in_view_change2cert_implies_same_seq_nums : pbft.

  Lemma view_change_in_log_implies_somewhere :
    forall vc s,
      view_change_in_log vc s
      -> view_change_somewhere_in_log vc s.
  Proof.
    induction s; introv inlog; simpl in *; tcsp; smash_pbft.
    left; apply view_change_in_log_entry_implies_in in inlog.
    destruct a, vce_view_change; simpl in *; simpl in *; tcsp.
  Qed.
  Hint Resolve view_change_in_log_implies_somewhere : pbft.

  Fixpoint checkpoint_in_others (cp : Checkpoint) (l : PBFTcheckpoint_log) :=
    match l with
    | [] => False
    | entry :: entries =>
      In cp (cp_checkpoint entry) \/ checkpoint_in_others cp entries
    end.

  Lemma checkpoint_in_state_as_checkpoint_in_others :
    forall cp s,
      checkpoint_in_state cp s <-> checkpoint_in_others cp (chk_state_others s).
  Proof.
    introv; unfold checkpoint_in_state, checkpoint_in_log.
    remember (chk_state_others s) as l; clear Heql.
    induction l; simpl in *; split; intro h; exrepnd; tcsp; repndors; subst; tcsp.

    - right; apply IHl; eexists; dands; eauto.

    - exists a; dands; tcsp.

    - apply IHl in h; exrepnd; eexists; dands; eauto.
  Qed.

  Lemma checkpoint_in_others_trim_checkpoint_log_implies :
    forall cp n l,
      wf_checkpoint_log l = true
      -> checkpoint_in_others cp (trim_checkpoint_log n l)
      -> checkpoint_in_others cp l
         /\ n <= checkpoint2seq cp.
  Proof.
    induction l; introv wf check; simpl in *; tcsp; smash_pbft.

    - autodimp IHl hyp; tcsp.

    - repndors; tcsp.
      dands; tcsp.
      unfold wf_checkpoint_entry in wf; smash_pbft.
      unfold wf_checkpoint_entry_same_seq_and_digest in *.
      allrw forallb_forall.
      discover; unfold same_seq_nums in *; smash_pbft.
  Qed.

  Lemma wf_checkpoint_state_implies_wf_checkpoint_log :
    forall s,
      wf_checkpoint_state s = true
      -> wf_checkpoint_log (chk_state_others s) = true.
  Proof.
    introv wf; unfold wf_checkpoint_state in wf; smash_pbft.
  Qed.
  Hint Resolve wf_checkpoint_state_implies_wf_checkpoint_log : pbft.

  Lemma check_stable_preserves_checkpoint_in_others :
    forall i cp s1 cop s2,
      wf_checkpoint_state (cp_state s1) = true
      -> check_stable i s1 cop = Some s2
      -> checkpoint_in_others cp (chk_state_others (cp_state s2))
      -> checkpoint_in_others cp (chk_state_others (cp_state s1)).
  Proof.
    introv wf check j.
    unfold check_stable in check; smash_pbft.
    apply checkpoint_in_others_trim_checkpoint_log_implies in j; repnd; auto.
    eauto 3 with pbft.
  Qed.
  Hint Resolve check_stable_preserves_checkpoint_in_others : pbft.

  Hint Resolve add_new_checkpoint2cp_state_preserves_wf_checkpoint_state : pbft.

  Lemma add_new_checkpoint2cp_log_preserves_checkpoint_in_others :
    forall s1 smst lastr c cop s2 cp,
      add_new_checkpoint2cp_log s1 smst lastr c = (cop, s2)
      -> checkpoint_in_others cp s2
      -> checkpoint_in_others cp s1 \/ cp = c.
  Proof.
    induction s1; introv add check; repeat (simpl in *; smash_pbft);[|].

    - repndors; tcsp;[].
      eapply in_add_checkpoint2entry_implies_or in check;[|eauto]; tcsp.

    - repndors; tcsp;[].
      rename_hyp_with add_new_checkpoint2cp_log add.
      eapply IHs1 in add;[|eauto]; tcsp.
  Qed.

  Lemma add_new_checkpoint2cp_state_preserves_checkpoint_in_others :
    forall s1 smst lastr c cop s2 cp,
      add_new_checkpoint2cp_state s1 smst lastr c = (cop, s2)
      -> checkpoint_in_others cp (chk_state_others s2)
      -> checkpoint_in_others cp (chk_state_others s1) \/ cp = c.
  Proof.
    introv add check.
    unfold add_new_checkpoint2cp_state in add; smash_pbft.
    eapply add_new_checkpoint2cp_log_preserves_checkpoint_in_others; eauto.
  Qed.

  Lemma cp_state_decrement_requests_in_progress_if_primary :
    forall i v s,
      cp_state (decrement_requests_in_progress_if_primary i v s)
      = cp_state s.
  Proof.
    introv; unfold decrement_requests_in_progress_if_primary; smash_pbft.
  Qed.
  Hint Rewrite cp_state_decrement_requests_in_progress_if_primary : pbft.

  Lemma find_and_execute_requests_preserves_cp_state :
    forall i v keys s1 msgs s2 cp,
      find_and_execute_requests i v keys s1 = (msgs, s2)
      -> checkpoint_in_others cp (chk_state_others (cp_state s2))
      -> checkpoint_in_others cp (chk_state_others (cp_state s1))
         \/
         (
           checkpoint2seq cp = next_to_execute s1
           /\ next_to_execute s2 = next_seq (next_to_execute s1)
           /\ checkpoint2digest cp = state2hash s2
         ).
  Proof.
    introv fexec check; unfold find_and_execute_requests in *; smash_pbft;[].
    unfold execute_requests in *.
    destruct (ready s1); simpl in *; smash_pbft;[].
    unfold check_broadcast_checkpoint in *; simpl in *; smash_pbft.

    rename_hyp_with add_new_checkpoint2cp_state add.
    eapply add_new_checkpoint2cp_state_preserves_checkpoint_in_others in add;[|eauto].
    simpl in *; autorewrite with pbft in *.
    repndors; tcsp.
    right; subst; simpl; tcsp.
  Qed.

  Lemma state2hash_decrement_requests_in_progress_if_primary :
    forall i v s,
      state2hash (decrement_requests_in_progress_if_primary i v s)
      = state2hash s.
  Proof.
    introv; unfold decrement_requests_in_progress_if_primary; smash_pbft.
  Qed.
  Hint Rewrite state2hash_decrement_requests_in_progress_if_primary : pbft.

  Lemma cp_state_update_checkpoint_from_new_view :
    forall s C n,
      cp_state (update_checkpoint_from_new_view s C n)
      = cp_state s.
  Proof.
    introv; unfold update_checkpoint_from_new_view; smash_pbft.
  Qed.
  Hint Rewrite cp_state_update_checkpoint_from_new_view : pbft.

  Lemma checkpoint_in_others_trim_checkpoint_state_implies :
    forall cp n s,
      wf_checkpoint_log (chk_state_others s) = true
      -> checkpoint_in_others cp (chk_state_others (trim_checkpoint_state n s))
      -> checkpoint_in_others cp (chk_state_others s) /\ n <= checkpoint2seq cp.
  Proof.
    introv wf check.
    unfold trim_checkpoint_state in check.
    destruct s; simpl in *.
    apply checkpoint_in_others_trim_checkpoint_log_implies in check; auto.
  Qed.

  Lemma update_state_new_view_preserves_checkpoint_in_others :
    forall i s1 nv s2 msgs cp,
      wf_checkpoint_log (chk_state_others (cp_state s1)) = true
      -> update_state_new_view i s1 nv = (s2, msgs)
      -> checkpoint_in_others cp (chk_state_others (cp_state s2))
      -> checkpoint_in_others cp (chk_state_others (cp_state s1)).
  Proof.
    introv wf upd check.
    unfold update_state_new_view in upd; smash_pbft.
    unfold trim_checkpoint in *; simpl in *.

    unfold log_checkpoint_cert_from_new_view in *; simpl in *; smash_pbft;
      try (complete (apply checkpoint_in_others_trim_checkpoint_log_implies in check; tcsp));
      try (complete (apply checkpoint_in_others_trim_checkpoint_state_implies in check; tcsp)).
  Qed.

  Lemma checkpoint_in_others_check_on_stable :
    forall c i s l,
      wf_checkpoint_state (cp_state s) = true
      -> checkpoint_in_others c (chk_state_others (cp_state (check_one_stable i s l)))
      -> checkpoint_in_others c (chk_state_others (cp_state s)).
  Proof.
    induction l; introv wf check; simpl in *; smash_pbft.
  Qed.
  Hint Resolve checkpoint_in_others_check_on_stable : pbft.

  Lemma trace_back_checkpoint_in_log :
    forall (eo : EventOrdering) cp i,
      received_or_generated
        eo
        (PBFTreplicaSM i)
        (fun e st => checkpoint_in_others cp (chk_state_others (cp_state st)))
        (fun e' st1 st2 e st =>
           verify_checkpoint i (local_keys st1) cp = true
           /\ event_triggered_by_message e' (PBFTcheckpoint cp))
        (fun e' st1 st2 e st =>
           checkpoint2seq cp = next_to_execute st1
           /\ next_to_execute st2 = next_seq (next_to_execute st1)
           /\ checkpoint2digest cp = state2hash st2).
  Proof.
    intros eo c i e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv eqst j.

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
      apply check_send_replies_preserves_cp_state in check; simpl in *.
      rewrite check in j.
      try (smash_pbft_ind ind).
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.
      apply check_send_replies_preserves_cp_state in check; simpl in *.
      rewrite check in j.
      try (smash_pbft_ind ind).
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      apply check_send_replies_preserves_cp_state in check; simpl in *.
      rewrite check in j.
      try (smash_pbft_ind ind).
    }

    {
      (* checkpoint *)

      eapply add_new_checkpoint2cp_state_preserves_checkpoint_in_others in j;[|eauto].
      repndors;[try (smash_pbft_ind ind)|];[].
      subst.
      exists e; eexists; eexists; dands; eauto 2 with eo; tcsp.
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.
      autorewrite with pbft in *.
      eapply find_and_execute_requests_preserves_cp_state in fexec;[|eauto].
      repndors;[try (smash_pbft_ind ind)|];[].
      exists e; eexists; eexists; dands;
        eauto 3 with eo; autorewrite with pbft in *; tcsp.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with update_state_new_view upd.

      eapply update_state_new_view_preserves_checkpoint_in_others in j;[| |eauto];
        simpl in *; eauto 3 with pbft;[].
      try (smash_pbft_ind ind).
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      apply add_prepares_to_log_from_new_view_pre_prepares_preserves_cp_state in add; simpl in *.

      eapply update_state_new_view_preserves_checkpoint_in_others in j;[| |eauto];
        simpl in *; eauto 3 with pbft; rewrite add in*;[|eauto 3 with pbft];[].
      try (smash_pbft_ind ind).
    }
  Qed.

  Lemma similar_checkpoint_in_new_view_implies :
    forall (eo : EventOrdering) (e : Event) nv cp,
      exists_at_most_f_faulty [e] F
      -> correct_new_view nv = true
      -> similar_checkpoint_in_new_view cp nv
      ->
      exists cp' vc,
        In vc (new_view2cert nv)
        /\ checkpoint2digest cp' = checkpoint2digest cp
        /\ checkpoint2seq cp' = checkpoint2seq cp
        /\ In cp' (view_change2cert vc)
        /\ node_has_correct_trace_before e (checkpoint2sender cp').
  Proof.
    introv atmost cor sim.
    unfold similar_checkpoint_in_new_view in sim; exrepnd.

    dup sim0 as corvc.
    apply correct_new_view_implies_correct_view_change in corvc; auto;[].
    applydup correct_view_change_implies_length in corvc.
    applydup correct_view_change_implies_no_repeats in corvc.
    pose proof (there_is_one_good_guy_before eo (map checkpoint2sender (view_change2cert vc)) [e]) as q.
    repeat (autodimp q hyp); exrepnd.
    allrw in_map_iff; exrepnd; subst.
    rewrite <- sim2, <- sim3.
    exists x vc; dands; auto; eauto 3 with pbft;[].
    introv w z; apply (q0 e); simpl; tcsp.
  Qed.

  Lemma similar_checkpoint_in_view_change_implies :
    forall (eo : EventOrdering) (e : Event) cp s,
      exists_at_most_f_faulty [e] F
      -> (forall vc,
             view_change_in_log vc s
             -> correct_view_change (view_change2view vc) vc = true)
      -> similar_checkpoint_in_view_change cp s
      ->
      exists cp' vc,
        view_change_in_log vc s
        /\ checkpoint2digest cp' = checkpoint2digest cp
        /\ checkpoint2seq cp' = checkpoint2seq cp
        /\ In cp' (view_change2cert vc)
        /\ node_has_correct_trace_before e (checkpoint2sender cp').
  Proof.
    introv atmost imp sim.
    unfold similar_checkpoint_in_view_change in sim; exrepnd.
    unfold checkpoint_in_view_change in sim0; exrepnd.
    applydup imp in sim0.

    applydup correct_view_change_implies_length in sim4.
    applydup correct_view_change_implies_no_repeats in sim4.
    pose proof (there_is_one_good_guy_before eo (map checkpoint2sender (view_change2cert vc)) [e]) as q.
    repeat (autodimp q hyp); exrepnd.
    allrw in_map_iff; exrepnd; subst.
    rewrite <- sim1, <- sim2.
    fold (node_has_correct_trace eo (checkpoint2sender x)) in *.
    exists x vc; dands; auto; eauto 3 with pbft;[].
    introv w z; apply (q0 e); simpl; tcsp.
  Qed.

  Lemma similar_checkpoint_in_stable_implies :
    forall (eo : EventOrdering) (e : Event) cp s,
      exists_at_most_f_faulty [e] F
      -> wf_checkpoint_state (cp_state s) = true
      -> similar_checkpoint_in_stable cp s
      ->
      exists cp',
        In cp' (checkpoint_certificate_of_last_stable_checkpoint s)
        /\ checkpoint2digest cp' = checkpoint2digest cp
        /\ checkpoint2seq cp' = checkpoint2seq cp
        /\ node_has_correct_trace_before e (checkpoint2sender cp').
  Proof.
    introv atmost wf sim.
    unfold similar_checkpoint_in_stable in sim; exrepnd.

    unfold wf_checkpoint_state in *; smash_pbft.
    unfold wf_stable_checkpoint in *; smash_pbft.
    unfold wf_stable_checkpoint_entry in *; smash_pbft.
    unfold wf_stable_checkpoint_entry_no_repeats in *.
    unfold wf_stable_checkpoint_entry_same_seq_and_digest in *.

    allrw forallb_forall.
    allrw @norepeatsb_as_no_repeats.

    fold (checkpoint_certificate_of_last_stable_checkpoint s) in *.

    repndors;
      [destruct (checkpoint_certificate_of_last_stable_checkpoint s);
       simpl in *; tcsp|];[].

    pose proof (there_is_one_good_guy_before eo (map checkpoint2sender (checkpoint_certificate_of_last_stable_checkpoint s)) [e]) as q.
    repeat (autodimp q hyp); autorewrite with list; auto;[].
    exrepnd.
    allrw in_map_iff; exrepnd; subst.

    applydup wf in q2; smash_pbft.
    applydup wf in sim0; smash_pbft.
    unfold same_seq_nums, same_digests in *; smash_pbft.

    exists x; dands; auto; try congruence.
  Qed.

  Lemma sent_checkpoint_contains_state :
    forall (eo : EventOrdering) (e : Event) cp dst i st,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> (forall e' i good vc nv cp st,
             e' ≼ e
             -> loc e' = PBFTreplica i
             -> node_has_correct_trace_before e good
             -> checkpoint2sender cp = good
             -> state_sm_on_event (PBFTreplicaSM i) e' = Some st
             -> new_view_in_log nv (view_change_state st)
             -> In vc (new_view2cert nv)
             -> In cp (view_change2cert vc)
             ->
             exists e'' good' st2,
               e'' ≼ e'
               /\ loc e'' = PBFTreplica good'
               /\ state_sm_on_event (PBFTreplicaSM good') e'' = Some st2
               /\ next_to_execute st2 = next_seq (checkpoint2seq cp)
               /\ checkpoint2digest cp = state2hash st2)
      -> loc e = PBFTreplica i
      -> In (send_checkpoint cp dst) (output_system_on_event_ldata PBFTsys e)
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> exists e' good st2,
          e' ≼ e
          /\ loc e' = PBFTreplica good
          /\ state_sm_on_event (PBFTreplicaSM good) e' = Some st2
          /\ next_to_execute st2 = next_seq (checkpoint2seq cp)
          /\ checkpoint2digest cp = create_hash_state_last_reply (PBFT.sm_state st2) (last_reply_state st2).
  Proof.
    introv sendbyz ckeys atMostF IND eqloce j eqst.
    apply in_output_system_on_event_ldata in j.

    unfold PBFTsys in j.
    rewrite eqloce in j.

    rw @loutput_sm_on_event_unroll2 in j.
    fold (@DirectedMsgs _ _) in *.
    simpl in *.
    dup eqst as eqst_backup.
    rewrite state_sm_on_event_unroll2 in eqst.

    match goal with
    | [ H : context[state_sm_before_event ?a ?b] |- _ ] =>
      remember (state_sm_before_event a b) as q; symmetry in Heqq
    end.
    destruct q; simpl in *; ginv;[].

    op_st_some m eqtrig; rewrite eqtrig in *; simpl in *.

    unfold PBFTreplica_update in *.
    destruct m; simpl in *; ginv; subst; tcsp;
      smash_handlers; try conflicting_sends.

    {
      (* pre-prepare *)

      allrw in_app_iff; repndors;
        [apply in_check_broadcast_prepare_implies in j; exrepnd; subst; ginv
        |apply in_check_broadcast_commit_implies2 in j; exrepnd; subst; ginv
        |];[].

      rename_hyp_with check_send_replies check.
      eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
    }

    {
      (* prepare *)

      allrw in_app_iff; repndors;
        [apply in_check_broadcast_commit_implies in j; exrepnd;subst;ginv
        |].

      rename_hyp_with check_send_replies check.
      eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.
      eapply checkpoint_in_output_of_find_and_execute_requests_implies in fexec;[|eauto].
      repnd.
      exists e i; eexists; dands; eauto; eauto 2 with eo;
        simpl; autorewrite with pbft; allrw; tcsp.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with CheckBCastNewView2entry cb.

      apply CheckBCastNewView2entry_some_implies in cb.
      applydup update_state_new_view_preserves_wf in upd; simpl;[|eauto 4 with pbft];[].
      applydup wf_view_change_state_implies_all_entries in cb;[|eauto 3 with pbft];[].

      applydup check_broadcast_new_view_implies in check.
      applydup check_broadcast_new_view_implies_eq_views in check;auto;[].

      unfold broadcast2others in *; repndors; ginv;[].
      dup upd as h.
      eapply message_in_update_state_new_view_implies in h;[|eauto].
      simpl in *; autorewrite with pbft in *.

      assert (new_view_in_log x2 (view_change_state st)) as nvinlog.
      {
        apply update_state_new_view_preserves_view_change_state in upd.
        rewrite upd; simpl; eauto 3 with pbft.
        apply new_view_in_log_log_new_view_and_entry;
          exrepnd; subst; simpl in *; autorewrite with pbft in *; auto.
      }

      hide_hyp check0.
      exrepnd; ginv; simpl in *.

      dup nvinlog as cornv.
      eapply PBFT_A_1_2_5 in cornv; eauto;[].

      applydup view_change_cert2_max_seq_vc_some_in in h0 as inv.
      applydup sn_of_view_change_cert2max_seq_vc in h0 as eqsn.
      dup inv as corvc.
      apply correct_new_view_implies_correct_view_change in corvc; auto;[].

      pose proof (there_is_one_good_guy_before eo (map checkpoint2sender (view_change2cert vc)) [e]) as q.
      repeat (autodimp q hyp); eauto 3 with pbft;[].
      exrepnd.
      apply in_map_iff in q1; exrepnd.

      dup q2 as corcp.
      eapply correct_view_change_implies_correct_view_change_cert_one in corcp;[|eauto].
      apply correct_view_change_cert_one_implies in corcp; repnd.

      pose proof (IND e i good vc x2 x0 st) as q.
      repeat (autodimp q hyp); eauto 2 with eo;
        try (complete (introv w z; apply (q0 e); simpl; tcsp));[].
      exrepnd.
      exists e'' good' st2; dands; allrw; auto; try congruence.
      eauto 3 with eo pbft.
      rewrite corcp in q3; auto.
    }

    {
      (* expired-timer *)

      repndors; ginv; smash_pbft.
    }

    {
      (* new_view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      allrw in_app_iff; repndors;
        [apply send_checkpoint_in_trim_outputs_with_low_water_mark in j;
         eapply in_add_prepares_to_log_from_new_view_pre_prepares_implies in add;[|eauto];
         repndors; exrepnd; ginv|];[].

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state in add as eqvcs.
      simpl in *.

      eapply message_in_update_state_new_view_implies in j;[|eauto].
      simpl in *; autorewrite with pbft in *.

      assert (new_view_in_log v (view_change_state st)) as nvinlog.
      {
        apply update_state_new_view_preserves_view_change_state in upd.
        rewrite upd; simpl; eauto 3 with pbft.
        rewrite eqvcs.
        apply implies_new_view_in_log_log_new_view; auto;[].
        introv k eqnv.
        eapply PBFT_A_1_2_5_before; try (exact Heqsop); auto; eauto.
        eauto 3 with pbft.
      }

      exrepnd; ginv; simpl in *.

      dup nvinlog as cornv.
      eapply PBFT_A_1_2_5 in cornv; eauto;[].

      applydup view_change_cert2_max_seq_vc_some_in in j0 as inv.
      applydup sn_of_view_change_cert2max_seq_vc in j0 as eqsn.
      dup inv as corvc.
      apply correct_new_view_implies_correct_view_change in corvc; auto;[].

      pose proof (there_is_one_good_guy_before eo (map checkpoint2sender (view_change2cert vc)) [e]) as q.
      repeat (autodimp q hyp); eauto 3 with pbft;[].
      exrepnd.
      apply in_map_iff in q1; exrepnd.

      dup q2 as corcp.
      eapply correct_view_change_implies_correct_view_change_cert_one in corcp;[|eauto].
      apply correct_view_change_cert_one_implies in corcp; repnd.

      pose proof (IND e i good vc v x st) as q.
      repeat (autodimp q hyp); eauto 2 with eo;
        try (complete (introv w z; apply (q0 e); simpl; tcsp));[].
      exrepnd.
      exists e'' good' st2; dands; auto; try congruence.
      rewrite corcp in q3; auto.
    }
  Qed.

  Lemma checkpoint_somewhere_in_log_received_from_good_replica_was_logged :
    forall (eo : EventOrdering) (e : Event) good cp i st,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> loc e = PBFTreplica i
      -> node_has_correct_trace_before e good
      -> checkpoint2sender cp = good
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> checkpoint_somewhere_in_log cp st
      ->
      exists e' good' st2,
        e' ≼ e
        /\ loc e' = PBFTreplica good'
        /\ state_sm_on_event (PBFTreplicaSM good') e' = Some st2
        /\ next_to_execute st2 = next_seq (checkpoint2seq cp)
        /\ checkpoint2digest cp = create_hash_state_last_reply (PBFT.sm_state st2) (last_reply_state st2).
  Proof.
    intros eo e.
    induction e as [? ind] using HappenedBeforeInd;[].
    introv sendbyz ckeys atMostF eqloc ctrace vcgood eqst cpinlog.

    unfold checkpoint_somewhere_in_log in cpinlog.
    repndors;[| |].

    {
      (* the checkpoint is in a view-change in a new-view in the log *)

      unfold checkpoint_in_new_view in cpinlog.
      destruct cpinlog as [nv [vc [nvinlog [vcincert cpincert]]]].

      assert (knows2 e nv) as kn by (eexists; eexists; simpl; dands; eauto).

      pose proof (new_views_learns_or_knows eo) as lok; autodimp lok hyp.
      applydup lok in kn.
      repeat (autodimp kn0 hyp); eauto 3 with pbft eo;[].

      (* either the new-view was received or it was sent *)
      repndors; exrepnd;[|].

      - (* the new-view was received *)

        unfold learned, learns in kn0; exrepnd; simpl in *.
        eapply pbft_nv_verify_verify_new_view in kn2;[|eauto|reflexivity].
        dup vcincert as verifvc.
        eapply verify_new_view_implies_verify_view_change_in_cert in verifvc; eauto.
        dup cpincert as verifcp.
        eapply verify_view_change_implies_verify_checkpoint in verifcp; eauto.
        pose proof (in_bind_op_list_implies_auth_data_in_trigger (pbft_nv_data2main_auth_data nv) e') as q.
        simpl in q; apply q in kn3; clear q.
        applydup pbft_nv_data2main_auth_data_in_trigger_implies in kn3.

        assert (auth_data_in_trigger (checkpoint2auth_data cp) e')
          as iauth by (unfold auth_data_in_trigger; allrw; simpl; eauto 2 with pbft).

        pose proof (state_sm_before_event_some_between3 e' e (PBFTreplicaSM i) st) as ns.
        repeat (autodimp ns hyp); auto;[].
        exrepnd.

        pose proof (ckeys e' i s') as eqkeys1; autodimp eqkeys1 hyp; eauto 3 with pbft eo;[].
        applydup localLe_implies_loc in kn0.

        applydup implies_authenticated_messages_were_sent_non_byz in sendbyz.
        apply (sendbyz0 _ _ (PBFTreplica good)) in iauth; simpl in *; eauto 2 with pbft eo;
          try (complete (allrw; simpl; tcsp));
          try (complete (subst; destruct cp, b; simpl; tcsp));[].

        exrepnd.
        pose proof (PBFTnever_stops eo e'0 (checkpoint2sender cp)) as w.
        repeat (autodimp w hyp); try (complete (apply ctrace; eauto 4 with eo));[].
        pose proof (PBFTnever_stops_on_event eo e'0 (checkpoint2sender cp)) as z.
        repeat (autodimp z hyp); try (complete (apply ctrace; eauto 4 with eo));[].
        exrepnd.

        applydup checkpoint2auth_data_in_get_contained_auth_data_implies in iauth3.

        (* either
           (1) the good guy sent the checkpoint
           (2) or he sent a view-change containing the checkpoint
           (3) or he sent a new-view containing a view-change containing the checkpoint *)
        repndors;[| |].

        + (* the good guy sent the checkpoint *)

          subst; simpl in *.
          autodimp iauth4 hyp;[].
          repndors; tcsp;[].

          assert (e'0 ≺ e) as lte by eauto 3 with eo.

          apply send_checkpoint_no_delay in iauth4.
          eapply sent_checkpoint_contains_state in iauth4;
            try (exact z0); auto; tcsp; eauto 3 with pbft eo;[|].

          {
            exrepnd.
            exists e'1 good st2; dands; auto; eauto 5 with eo pbft.
          }

          {
            introv lee eqloc' ctrace' eqgood' eqst' nvinlog' innvcert' invccert'.
            pose proof (ind e'1) as q; autodimp q hyp; eauto 5 with eo;[].
            pose proof (q good cp0 i0 st2) as q; repeat (autodimp q hyp);
              eauto 4 with pbft eo; try (complete (allrw; auto)).
          }

        + (* the good guy sent a view-change containing the checkpoint*)

          exrepnd.
          subst; simpl in *.
          autodimp iauth4 hyp;[].

          (* WARNING *)
          clear iauth3.

          apply send_view_change_no_delay in iauth4.
          eapply sent_view_change_is_in_log2 in iauth4; [| |eauto|eauto]; auto;[].
          repnd; subst; simpl in *.

          rewrite <- ite_first_state_sm_on_event_as_before in w0.
          unfold ite_first in w0.
          destruct (dec_isFirst e'0) as [d|d];[ginv;simpl in *; tcsp|].

          assert ((local_pred e'0) ⊑ e'0) as caus1 by eauto 2 with eo.
          assert ((local_pred e'0) ≺ e') as caus2 by eauto 3 with eo.
          assert ((local_pred e'0) ≺ e) as caus3 by eauto 3 with eo.

          pose proof (ind (local_pred e'0)) as q; autodimp q hyp;[]; clear ind.
          pose proof (q (checkpoint2sender cp) cp (checkpoint2sender cp) st1) as q.
          repeat (autodimp q hyp); autorewrite with eo; auto; eauto 2 with pbft eo;
            try (complete (introv w z; apply ctrace; auto; eauto 3 with eo));
            try (complete (allrw; eauto 3 with pbft eo));[].
          exrepnd.
          exists e'1 good' st2; dands; auto; eauto 3 with eo.

        + (* the good guy sent a new-view containing a view-change containing the checkpoint *)

          exrepnd; subst; simpl in *.
          autodimp iauth4 hyp;[].

          apply send_new_view_no_delay in iauth4.
          eapply sent_new_views_are_in_log in iauth4;[| |eauto]; auto;[].

          assert (e'0 ≺ e') as caus2 by eauto 3 with eo.
          assert (e'0 ≺ e) as caus3 by eauto 3 with eo.

          pose proof (ind e'0) as q; autodimp q hyp;[]; clear ind.
          pose proof (q (checkpoint2sender cp) cp (checkpoint2sender cp) st0) as q.
          repeat (autodimp q hyp); autorewrite with eo; auto; eauto 3 with pbft eo;
            try (complete (introv w z; apply ctrace; auto; eauto 3 with eo));
            try (complete (allrw; eauto 3 with eo pbft));[].
          exrepnd.
          exists e'1 good' st2; dands; auto; eauto 3 with eo.

      - (* the new-view was sent *)

        applydup knows_own_new_view in kn; auto;[].
        exrepnd.

        applydup kn1 in vcincert as vcinlog.
        eapply view_changes_are_received_or_created2 in vcinlog;[allrw; auto |eauto]; auto; try congruence;[].
        exrepnd.

        applydup localLe_implies_loc in vcinlog1 as eqloc1.
        applydup localLe_implies_loc in kn2 as eqloc0.
        unfold lak_data2node in *; simpl in *.
        unfold pbft_nv_data2loc in *; simpl in *.

        rewrite eqloc in kn0; inversion kn0 as [eqi]; rewrite eqi in *.

        (* either we received the view-change or we generated it *)
        repndors; repnd;[|].

        + (* we received the view-change *)

          dup vcinlog4 as verifcp.
          eapply verify_view_change_implies_verify_checkpoint in verifcp; eauto;[].

          assert (auth_data_in_trigger (checkpoint2auth_data cp) e'0)
            as iauth by (unfold auth_data_in_trigger; allrw; simpl; eauto 2 with pbft).

          pose proof (ckeys e'0 i st0) as eqkeys1; autodimp eqkeys1 hyp;
            try (complete (rewrite eqloc in *; eauto 3 with pbft eo));[].
          (*applydup localLe_implies_loc in nvinlog1.*)

          applydup implies_authenticated_messages_were_sent_non_byz in sendbyz.
          apply (sendbyz0 _ _ (PBFTreplica good)) in iauth; simpl in *; eauto 3 with pbft eo;
            try (complete (allrw; simpl; tcsp));
            try (complete (subst; destruct cp, b; simpl; tcsp));[].
          exrepnd.

          assert (e'1 ≺ e) as lee' by eauto 4 with eo.

          pose proof (PBFTnever_stops eo e'1 (checkpoint2sender cp)) as w.
          repeat (autodimp w hyp); try (complete (apply ctrace; eauto 4 with eo));[].
          pose proof (PBFTnever_stops_on_event eo e'1 (checkpoint2sender cp)) as z.
          repeat (autodimp z hyp); try (complete (apply ctrace; eauto 4 with eo));[].
          exrepnd.

          applydup checkpoint2auth_data_in_get_contained_auth_data_implies in iauth3.

          (* either
           (1) the good guy sent the checkpoint
           (2) or he sent a view-change containing the checkpoint
           (3) or he sent a new-view containing a view-change containing the checkpoint *)
          repndors;[| |].

          * (* the good guy sent the checkpoint *)

            subst; simpl in *.
            autodimp iauth4 hyp;[].
            repndors; tcsp;[].

            apply send_checkpoint_no_delay in iauth4.
            eapply sent_checkpoint_contains_state in iauth4;
              try (exact z0); auto; tcsp; eauto 3 with pbft eo;[|].

            {
              exrepnd.
              exists e'2 good st6; dands; auto; eauto 5 with eo.
            }

            {
              introv lee eqloc' ctrace' eqgood' eqst' nvinlog' innvcert' invccert'.
              pose proof (ind e'2) as q; autodimp q hyp; eauto 5 with eo;[].
              pose proof (q good cp0 i st6) as q; repeat (autodimp q hyp); eauto 3 with pbft eo;
                try (complete (allrw; eauto 3 with eo pbft)).
            }

          * (* the good guy sent a view-change containing the checkpoint*)

            exrepnd.
            subst; simpl in *.
            autodimp iauth4 hyp;[].

            (* WARNING *)
            clear iauth3.

            apply send_view_change_no_delay in iauth4.
            eapply sent_view_change_is_in_log2 in iauth4; [| |eauto|eauto]; auto;[].
            repnd; subst; simpl in *.

            rewrite <- ite_first_state_sm_on_event_as_before in w0.
            unfold ite_first in w0.
            destruct (dec_isFirst e'1) as [d|d];[ginv;simpl in *; tcsp|].

            assert ((local_pred e'1) ⊑ e'1) as caus1 by eauto 2 with eo.
            assert ((local_pred e'1) ≺ e'0) as caus2 by eauto 4 with eo.
            assert ((local_pred e'1) ≺ e') as caus3 by eauto 4 with eo.
            assert ((local_pred e'1) ≺ e) as caus4 by eauto 3 with eo.

            pose proof (ind (local_pred e'1)) as q; autodimp q hyp;[]; clear ind.
            pose proof (q (checkpoint2sender cp) cp (checkpoint2sender cp) st5) as q.
            repeat (autodimp q hyp); autorewrite with eo; auto; eauto 3 with pbft eo;
              try (complete (introv w z; apply ctrace; auto; eauto 3 with eo));
              try (complete (allrw; eauto 3 with pbft eo));[].
            exrepnd.
            exists e'2 good' st6; dands; auto; eauto 3 with eo.

          * (* the good guy sent a new-view containing a view-change containing the checkpoint *)

            exrepnd; subst; simpl in *.
            autodimp iauth4 hyp;[].

            apply send_new_view_no_delay in iauth4.
            eapply sent_new_views_are_in_log in iauth4;[| |eauto]; auto;[].

            assert (e'1 ≺ e'0) as caus2 by eauto 4 with eo.
            assert (e'1 ≺ e') as caus3 by eauto 4 with eo.
            assert (e'1 ≺ e) as caus4 by eauto 3 with eo.

            pose proof (ind e'1) as q; autodimp q hyp;[]; clear ind.
            pose proof (q (checkpoint2sender cp) cp (checkpoint2sender cp) st4) as q.
            repeat (autodimp q hyp); autorewrite with eo; auto; eauto 3 with pbft;
              try (complete (introv w z; apply ctrace; auto; eauto 3 with eo));
              try (complete (allrw; eauto 3 with pbft eo));[].
            exrepnd.
            exists e'2 good' st6; dands; auto; eauto 3 with eo.

        + (* the view-change is our own *)
          exrepnd.
          subst.
          simpl in *.

          rewrite <- ite_first_state_sm_on_event_as_before in vcinlog2.
          unfold ite_first in vcinlog2.
          destruct (dec_isFirst e'0) as [d|d];[ginv;simpl in *; tcsp|];[].

          assert ((local_pred e'0) ⊑ e'0) as caus1 by eauto 2 with eo.
          assert ((local_pred e'0) ≺ e') as caus3 by eauto 4 with eo.
          assert ((local_pred e'0) ≺ e) as caus4 by eauto 3 with eo.

          pose proof (ind (local_pred e'0)) as q; autodimp q hyp;[]; clear ind.
          pose proof (q (checkpoint2sender cp) cp (new_view2sender nv) st0) as q.
          repeat (autodimp q hyp); autorewrite with eo; auto; eauto 4 with pbft; try congruence;
            try (complete (introv w z; apply ctrace; auto; eauto 3 with eo));
            try (complete (allrw; rewrite eqloc in *; eauto 3 with pbft eo));[].
          exrepnd.
          exists e'1 good' st4; dands; auto; eauto 3 with eo.
    }

    {
      (* the checkpoint is in the stable checkpoint *)

      eapply trace_back_checkpoint_in_certificate in cpinlog;[|eauto]; auto.
      exrepnd.

      repndors;[| | | |].

      - (* either we received the checkpoint directly *)

        repnd.

        assert (auth_data_in_trigger (checkpoint2auth_data cp) e')
          as iauth by (unfold auth_data_in_trigger; allrw; simpl; eauto 2 with pbft).

        pose proof (ckeys e' i st') as eqkeys1; autodimp eqkeys1 hyp;eauto 3 with pbft eo;[].
        applydup localLe_implies_loc in cpinlog0.

        applydup implies_authenticated_messages_were_sent_non_byz in sendbyz.
        apply (sendbyz0 _ _ (PBFTreplica good)) in iauth; simpl in *; eauto 3 with pbft eo;
          try (complete (allrw; simpl; tcsp));
          try (complete (subst; destruct cp, b; simpl; tcsp));
          try (complete (allrw; eauto 3 with eo pbft)).
        exrepnd.

        pose proof (PBFTnever_stops eo e'0 (checkpoint2sender cp)) as w.
        repeat (autodimp w hyp); try (complete (apply ctrace; eauto 4 with eo));[].
        pose proof (PBFTnever_stops_on_event eo e'0 (checkpoint2sender cp)) as z.
        repeat (autodimp z hyp); try (complete (apply ctrace; eauto 4 with eo));[].
        exrepnd.

        applydup checkpoint2auth_data_in_get_contained_auth_data_implies in iauth3.

        (* either
           (1) the good guy sent the checkpoint
           (2) or he sent a view-change containing the checkpoint
           (3) or he sent a new-view containing a view-change containing the checkpoint *)
        repndors;[| |].

        + (* the good guy sent the checkpoint *)

          subst; simpl in *.
          autodimp iauth4 hyp;[].
          repndors; tcsp;[].

          apply send_checkpoint_no_delay in iauth4.
          eapply sent_checkpoint_contains_state in iauth4;
            try (exact z0); auto; tcsp; eauto 4 with pbft eo;[|].

          {
            exrepnd.
            exists e'1 good st2; dands; auto; eauto 5 with eo.
          }

          {
            introv lee eqloc' ctrace' eqgood' eqst' nvinlog' innvcert' invccert'.
            pose proof (ind e'1) as q; autodimp q hyp; eauto 4 with eo;[].
            pose proof (q good cp0 i0 st2) as q; repeat (autodimp q hyp); eauto 5 with pbft eo;
              try (complete (allrw; eauto 3 with pbft eo)).
          }

        + (* the good guy sent a view-change containing the checkpoint*)

          exrepnd.
          subst; simpl in *.
          autodimp iauth4 hyp;[].

          (* WARNING *)
          clear iauth3.

          apply send_view_change_no_delay in iauth4.
          eapply sent_view_change_is_in_log2 in iauth4; [| |eauto|eauto]; auto;[].
          repnd; subst; simpl in *.

          rewrite <- ite_first_state_sm_on_event_as_before in w0.
          unfold ite_first in w0.
          destruct (dec_isFirst e'0) as [d|d];[ginv;simpl in *; tcsp|].

          assert ((local_pred e'0) ⊑ e'0) as caus1 by eauto 2 with eo.
          assert ((local_pred e'0) ≺ e') as caus3 by eauto 4 with eo.
          assert ((local_pred e'0) ≺ e) as caus4 by eauto 3 with eo.

          pose proof (ind (local_pred e'0)) as q; autodimp q hyp;[]; clear ind.
          pose proof (q (checkpoint2sender cp) cp (checkpoint2sender cp) st1) as q.
          repeat (autodimp q hyp); autorewrite with eo; auto; eauto 3 with pbft;
            try (complete (introv w z; apply ctrace; auto; eauto 3 with eo));
            try (complete (allrw; eauto 3 with pbft eo));[].
          exrepnd.
          exists e'1 good' st2; dands; auto; eauto 3 with eo.

        + (* the good guy sent a new-view containing a view-change containing the checkpoint *)

          exrepnd; subst; simpl in *.
          autodimp iauth4 hyp;[].

          apply send_new_view_no_delay in iauth4.
          eapply sent_new_views_are_in_log in iauth4;[| |eauto]; auto;[].

          assert (e'0 ≺ e') as caus3 by eauto 4 with eo.
          assert (e'0 ≺ e) as caus4 by eauto 3 with eo.

          pose proof (ind e'0) as q; autodimp q hyp;[]; clear ind.
          pose proof (q (checkpoint2sender cp) cp (checkpoint2sender cp) st0) as q.
          repeat (autodimp q hyp); autorewrite with eo; auto; eauto 3 with pbft;
            try (complete (introv w z; apply ctrace; auto; eauto 3 with eo));
            try (complete (allrw; eauto 3 with pbft eo));[].
          exrepnd.
          exists e'1 good' st2; dands; auto; eauto 3 with eo.

      - (* or we received a similar checkpoint in a new-view *)

        exrepnd.

        eapply similar_checkpoint_in_new_view_implies in cpinlog3;eauto.
        exrepnd.

        dup cpinlog4 as verifvc.
        eapply verify_new_view_implies_verify_view_change_in_cert in verifvc; eauto.
        dup cpinlog9 as verifcp.
        eapply verify_view_change_implies_verify_checkpoint in verifcp; eauto.

        assert (auth_data_in_trigger (checkpoint2auth_data cp') e')
          as iauth by (unfold auth_data_in_trigger; allrw; simpl; eauto 2 with pbft).

        pose proof (ckeys e' i st') as eqkeys1; autodimp eqkeys1 hyp; eauto 3 with pbft eo;[].
        applydup localLe_implies_loc in cpinlog0.

        applydup implies_authenticated_messages_were_sent_non_byz in sendbyz.
        apply (sendbyz0 _ _ (PBFTreplica (checkpoint2sender cp'))) in iauth; simpl in *; eauto 3 with pbft eo;
          try (complete (allrw; simpl; tcsp));
          try (complete (subst; destruct cp', b; simpl; tcsp));[].
        exrepnd.

        pose proof (PBFTnever_stops eo e'0 (checkpoint2sender cp')) as w.
        repeat (autodimp w hyp); try (complete (apply cpinlog3; eauto 5 with eo));[].
        pose proof (PBFTnever_stops_on_event eo e'0 (checkpoint2sender cp')) as z.
        repeat (autodimp z hyp); try (complete (apply cpinlog3; eauto 5 with eo));[].
        exrepnd.

        applydup checkpoint2auth_data_in_get_contained_auth_data_implies in iauth3.

        (* either
           (1) the good guy sent the checkpoint
           (2) or he sent a view-change containing the checkpoint
           (3) or he sent a new-view containing a view-change containing the checkpoint *)
        repndors;[| |].

        + (* the good guy sent the checkpoint *)

          subst; simpl in *.
          autodimp iauth4 hyp;[].
          repndors; tcsp;[].

          apply send_checkpoint_no_delay in iauth4.
          eapply sent_checkpoint_contains_state in iauth4;
            try (exact z0); auto; tcsp; eauto 4 with pbft eo;[|].

          {
            exrepnd.
            exists e'1 good st2; dands; auto; eauto 5 with eo; try congruence.
          }

          {
            introv lee eqloc' ctrace' eqgood' eqst' nvinlog' innvcert' invccert'.
            pose proof (ind e'1) as q; autodimp q hyp; eauto 4 with eo;[].
            pose proof (q good cp0 i0 st2) as q; repeat (autodimp q hyp); eauto 5 with pbft eo;
              try (complete (allrw; eauto 3 with pbft eo)).
          }

        + (* the good guy sent a view-change containing the checkpoint *)

          exrepnd.
          subst; simpl in *.
          autodimp iauth4 hyp;[].

          (* WARNING *)
          clear iauth3.

          apply send_view_change_no_delay in iauth4.
          eapply sent_view_change_is_in_log2 in iauth4; [| |eauto|eauto]; auto;[].
          repnd; subst; simpl in *.

          rewrite <- ite_first_state_sm_on_event_as_before in w0.
          unfold ite_first in w0.
          destruct (dec_isFirst e'0) as [d|d];[ginv;simpl in *; tcsp|].

          assert ((local_pred e'0) ⊑ e'0) as caus1 by eauto 2 with eo.
          assert ((local_pred e'0) ≺ e') as caus3 by eauto 4 with eo.
          assert ((local_pred e'0) ≺ e) as caus4 by eauto 3 with eo.

          pose proof (ind (local_pred e'0)) as q; autodimp q hyp;[]; clear ind.
          pose proof (q (checkpoint2sender cp') cp' (checkpoint2sender cp') st1) as q.
          repeat (autodimp q hyp); autorewrite with eo; auto; eauto 3 with pbft;
            try (complete (introv w z; apply cpinlog3; auto; eauto 3 with eo));
            try (complete (allrw; eauto 3 with pbft eo));[].
          exrepnd.
          exists e'1 good' st2; dands; auto; try congruence; eauto 3 with eo.

        + (* the good guy sent a new-view containing a view-change containing the checkpoint *)

          exrepnd; subst; simpl in *.
          autodimp iauth4 hyp;[].

          apply send_new_view_no_delay in iauth4.
          eapply sent_new_views_are_in_log in iauth4;[| |eauto]; auto;[].

          assert (e'0 ≺ e') as caus3 by eauto 4 with eo.
          assert (e'0 ≺ e) as caus4 by eauto 3 with eo.

          pose proof (ind e'0) as q; autodimp q hyp;[]; clear ind.
          pose proof (q (checkpoint2sender cp') cp' (checkpoint2sender cp') st0) as q.
          repeat (autodimp q hyp); autorewrite with eo; auto; eauto 3 with pbft; try congruence;
            try (complete (introv w z; apply cpinlog3; auto; eauto 3 with eo));
            try (complete (allrw; eauto 3 with pbft eo));[].
          exrepnd.
          exists e'1 good' st2; dands; auto; try congruence; eauto 3 with eo.

      - (* or the checkpoint was in our state *)

          rewrite <- ite_first_state_sm_on_event_as_before in cpinlog2.
          unfold ite_first in cpinlog2.
          destruct (dec_isFirst e') as [d|d];
            [ginv;simpl in *; tcsp;
             unfold checkpoint_in_state, checkpoint_in_log in *;
             simpl in *; tcsp|];[].

          applydup localLe_implies_loc in cpinlog0.

          pose proof (ind (local_pred e')) as q; autodimp q hyp; clear ind;[eauto 4 with eo|];[].
          pose proof (q good cp i st') as q; repeat (autodimp q hyp); autorewrite with eo; auto;
            try congruence; tcsp; eauto 5 with pbft eo;
              try (complete (allrw; rewrite eqloc in *; eauto 3 with pbft eo)).

          exrepnd.

          exists e'0 good' st2; dands; auto; eauto 4 with eo.

      - (* or a similar checkpoint was in a view change in our state *)

        applydup localLe_implies_loc in cpinlog0.

        assert (forall vc,
                   view_change_in_log vc (view_change_state st')
                   -> correct_view_change (view_change2view vc) vc = true) as imp.
        { introv vcinlog.
          eapply PBFT_A_1_2_6.PBFT_A_1_2_6_before in cpinlog2;[|eauto];
            auto; try congruence. }

        eapply similar_checkpoint_in_view_change_implies in cpinlog1;[|eauto|];auto;[].
        clear imp.
        exrepnd.
        apply view_change_in_log_implies_somewhere in cpinlog4.

        rewrite <- ite_first_state_sm_on_event_as_before in cpinlog2.
        unfold ite_first in cpinlog2.
        destruct (dec_isFirst e') as [d|d];[ginv;simpl in *; tcsp|];[].

        eapply view_changes_are_received_or_created2 in cpinlog4;[|eauto];[].
        exrepnd.

        assert (e'0 ⊑ e) as lee by eauto 3 with eo.
        applydup localLe_implies_loc in lee.

        (* either we received the view-change or we generated it *)
        repndors; repnd;[|].

        + (* we received the view-change *)

          dup cpinlog11 as verifcp.
          eapply verify_view_change_implies_verify_checkpoint in verifcp; eauto;[].

          assert (auth_data_in_trigger (checkpoint2auth_data cp') e'0)
            as iauth by (unfold auth_data_in_trigger; allrw; simpl; eauto 2 with pbft).

          pose proof (ckeys e'0 i st1) as eqkeys1; autodimp eqkeys1 hyp;
            try (complete (rewrite eqloc in *; eauto 3 with pbft eo)).

          applydup implies_authenticated_messages_were_sent_non_byz in sendbyz.
          apply (sendbyz0 _ _ (PBFTreplica (checkpoint2sender cp'))) in iauth; simpl in *; eauto 3 with pbft eo;
            try (complete (allrw; simpl; tcsp));
            try (complete (subst; destruct cp', b; simpl; tcsp));[].
          exrepnd.

          assert (e'1 ≺ e) as lee' by eauto 4 with eo.

          pose proof (PBFTnever_stops eo e'1 (checkpoint2sender cp')) as w.
          repeat (autodimp w hyp); try (complete (apply cpinlog1; eauto 4 with eo));[].
          pose proof (PBFTnever_stops_on_event eo e'1 (checkpoint2sender cp')) as z.
          repeat (autodimp z hyp); try (complete (apply cpinlog1; eauto 4 with eo));[].
          exrepnd.

          applydup checkpoint2auth_data_in_get_contained_auth_data_implies in iauth3.

          (* either
           (1) the good guy sent the checkpoint
           (2) or he sent a view-change containing the checkpoint
           (3) or he sent a new-view containing a view-change containing the checkpoint *)
          repndors;[| |].

          * (* the good guy sent the checkpoint *)

            subst; simpl in *.
            autodimp iauth4 hyp;[].
            repndors; tcsp;[].

            apply send_checkpoint_no_delay in iauth4.
            eapply sent_checkpoint_contains_state in iauth4;
              try (exact z0); auto; tcsp; eauto 3 with pbft eo;[|].

            {
              exrepnd.
              exists e'2 good st4; dands; auto; eauto 5 with eo; try congruence.
            }

            {
              introv lee'' eqloc' ctrace' eqgood' eqst' nvinlog' innvcert' invccert'.
              pose proof (ind e'2) as q; autodimp q hyp; eauto 5 with eo;[].
              pose proof (q good cp0 i0 st4) as q; repeat (autodimp q hyp); eauto 3 with pbft eo;
                try (complete (allrw; eauto 3 with pbft eo)).
            }

          * (* the good guy sent a view-change containing the checkpoint*)

            exrepnd.
            subst; simpl in *.
            autodimp iauth4 hyp;[].

            (* WARNING *)
            clear iauth3.

            apply send_view_change_no_delay in iauth4.
            eapply sent_view_change_is_in_log2 in iauth4; [| |eauto|eauto]; auto;[].
            repnd; subst; simpl in *.

            rewrite <- ite_first_state_sm_on_event_as_before in w0.
            unfold ite_first in w0.
            destruct (dec_isFirst e'1) as [d'|d'];[ginv;simpl in *; tcsp|].

            assert ((local_pred e'1) ⊑ e'1) as caus1 by eauto 2 with eo.
            assert ((local_pred e'1) ≺ e) as caus4 by eauto 3 with eo.

            pose proof (ind (local_pred e'1)) as q; autodimp q hyp;[]; clear ind.
            pose proof (q (checkpoint2sender cp') cp' (checkpoint2sender cp') st3) as q.
            repeat (autodimp q hyp); autorewrite with eo; auto; eauto 3 with pbft;
              try (complete (introv w z; apply cpinlog1; auto; eauto 3 with eo));
              try (complete (allrw; eauto 3 with pbft eo));[].
            exrepnd.
            exists e'2 good' st4; dands; auto; try congruence; eauto 3 with eo.

          * (* the good guy sent a new-view containing a view-change containing the checkpoint *)

            exrepnd; subst; simpl in *.
            autodimp iauth4 hyp;[].

            apply send_new_view_no_delay in iauth4.
            eapply sent_new_views_are_in_log in iauth4;[| |eauto]; auto;[].

            pose proof (ind e'1) as q; autodimp q hyp;[]; clear ind.
            pose proof (q (checkpoint2sender cp') cp' (checkpoint2sender cp') st0) as q.
            repeat (autodimp q hyp); autorewrite with eo; auto; eauto 3 with pbft; try congruence;
              try (complete (introv w z; apply cpinlog1; auto; eauto 3 with eo));
              try (complete (allrw; eauto 3 with pbft eo));[].
            exrepnd.
            exists e'2 good' st4; dands; auto; try congruence; eauto 3 with eo.

        + (* the view-change is our own *)
          exrepnd.
          subst.
          simpl in *.

          rewrite <- ite_first_state_sm_on_event_as_before in cpinlog9.
          unfold ite_first in cpinlog9.
          destruct (dec_isFirst e'0) as [d'|d'];[ginv;simpl in *; tcsp|];[].

          assert ((local_pred e'0) ⊑ e'0) as caus1 by eauto 2 with eo.
          assert ((local_pred e'0) ≺ e) as caus4 by eauto 5 with eo.

          pose proof (ind (local_pred e'0)) as q; autodimp q hyp;[]; clear ind.
          pose proof (q (checkpoint2sender cp') cp' i st1) as q.
          repeat (autodimp q hyp); autorewrite with eo; auto; eauto 4 with pbft; try congruence;
            try (complete (introv w z; apply cpinlog1; auto; eauto 3 with eo));
            try (complete (allrw; rewrite eqloc in *; eauto 3 with pbft eo));[].
          exrepnd.
          exists e'1 good' st0; dands; auto; try congruence; eauto 3 with eo.

      - (* or a similar checkpoint was stable *)

        assert (wf_checkpoint_state (cp_state st') = true) as wfcp by eauto 3 with pbft.

        eapply similar_checkpoint_in_stable_implies in cpinlog1;[|eauto|];auto.
        exrepnd.

        applydup localLe_implies_loc in cpinlog0.

        rewrite <- ite_first_state_sm_on_event_as_before in cpinlog2.
        unfold ite_first in cpinlog2.
        destruct (dec_isFirst e') as [d'|d'];[ginv;simpl in *; tcsp|];[].

        assert ((local_pred e') ⊑ e') as caus1 by eauto 2 with eo.
        assert ((local_pred e') ≺ e) as caus4 by eauto 5 with eo.

        pose proof (ind (local_pred e')) as q; autodimp q hyp;[]; clear ind.
        pose proof (q (checkpoint2sender cp') cp' i st') as q.
        repeat (autodimp q hyp); autorewrite with eo; auto; eauto 4 with pbft; try congruence;
          try (complete (introv w z; apply cpinlog3; auto; eauto 3 with eo));
          try (complete (allrw; rewrite eqloc in *; eauto 3 with pbft eo));[].
        exrepnd.
        exists e'0 good' st2; dands; auto; try congruence; eauto 3 with eo.
    }

    {
      (* the checkpoint is in the checkpoint log *)

      apply checkpoint_in_state_as_checkpoint_in_others in cpinlog.
      eapply trace_back_checkpoint_in_log in cpinlog;[|eauto]; auto.

      exrepnd.
      repndors;[|].

      - (* either we received the checkpoint message *)

        repnd.

        assert (auth_data_in_trigger (checkpoint2auth_data cp) e')
          as iauth by (unfold auth_data_in_trigger; allrw; simpl; eauto 2 with pbft).

        pose proof (ckeys e' i st1) as eqkeys1; autodimp eqkeys1 hyp; eauto 3 with pbft eo;[].
        applydup localLe_implies_loc in cpinlog1.

        applydup implies_authenticated_messages_were_sent_non_byz in sendbyz.
        apply (sendbyz0 _ _ (PBFTreplica good)) in iauth; simpl in *; eauto 3 with pbft eo;
          try (complete (allrw; simpl; tcsp));
          try (complete (subst; destruct cp, b; simpl; tcsp));[].
        exrepnd.

        pose proof (PBFTnever_stops eo e'0 (checkpoint2sender cp)) as w.
        repeat (autodimp w hyp); try (complete (apply ctrace; eauto 4 with eo));[].
        pose proof (PBFTnever_stops_on_event eo e'0 (checkpoint2sender cp)) as z.
        repeat (autodimp z hyp); try (complete (apply ctrace; eauto 4 with eo));[].
        exrepnd.

        applydup checkpoint2auth_data_in_get_contained_auth_data_implies in iauth3.

        (* either
           (1) the good guy sent the checkpoint
           (2) or he sent a view-change containing the checkpoint
           (3) or he sent a new-view containing a view-change containing the checkpoint *)
        repndors;[| |].

        + (* the good guy sent the checkpoint *)

          subst; simpl in *.
          autodimp iauth4 hyp;[].
          repndors; tcsp;[].

          apply send_checkpoint_no_delay in iauth4.
          eapply sent_checkpoint_contains_state in iauth4;
            try (exact z0); auto; tcsp; eauto 4 with pbft eo;[|].

          {
            exrepnd.
            exists e'1 good st4; dands; auto; eauto 5 with eo.
          }

          {
            introv lee eqloc' ctrace' eqgood' eqst' nvinlog' innvcert' invccert'.
            pose proof (ind e'1) as q; autodimp q hyp; eauto 4 with eo;[].
            pose proof (q good cp0 i0 st4) as q; repeat (autodimp q hyp); eauto 5 with pbft eo;
              try (complete (allrw; eauto 3 with pbft eo)).
          }

        + (* the good guy sent a view-change containing the checkpoint*)

          exrepnd.
          subst; simpl in *.
          autodimp iauth4 hyp;[].

          (* WARNING *)
          clear iauth3.

          apply send_view_change_no_delay in iauth4.
          eapply sent_view_change_is_in_log2 in iauth4; [| |eauto|eauto]; auto;[].
          repnd; subst; simpl in *.

          rewrite <- ite_first_state_sm_on_event_as_before in w0.
          unfold ite_first in w0.
          destruct (dec_isFirst e'0) as [d|d];[ginv;simpl in *; tcsp|].

          assert ((local_pred e'0) ⊑ e'0) as caus1 by eauto 2 with eo.
          assert ((local_pred e'0) ≺ e) as caus4 by eauto 5 with eo.

          pose proof (ind (local_pred e'0)) as q; autodimp q hyp;[]; clear ind.
          pose proof (q (checkpoint2sender cp) cp (checkpoint2sender cp) st3) as q.
          repeat (autodimp q hyp); autorewrite with eo; auto; eauto 3 with pbft;
            try (complete (introv w z; apply ctrace; auto; eauto 3 with eo));
            try (complete (allrw; eauto 3 with pbft eo));[].
          exrepnd.
          exists e'1 good' st4; dands; auto; eauto 3 with eo.

        + (* the good guy sent a new-view containing a view-change containing the checkpoint *)

          exrepnd; subst; simpl in *.
          autodimp iauth4 hyp;[].

          apply send_new_view_no_delay in iauth4.
          eapply sent_new_views_are_in_log in iauth4;[| |eauto]; auto;[].

          assert (e'0 ≺ e) as caus4 by eauto 5 with eo.

          pose proof (ind e'0) as q; autodimp q hyp;[]; clear ind.
          pose proof (q (checkpoint2sender cp) cp (checkpoint2sender cp) st0) as q.
          repeat (autodimp q hyp); autorewrite with eo; auto; eauto 3 with pbft;
            try (complete (introv w z; apply ctrace; auto; eauto 3 with eo));
            try (complete (allrw; eauto 3 with pbft eo));[].
          exrepnd.
          exists e'1 good' st4; dands; auto;[].
          eauto 5 with eo.

      - (* or we generated it the checkpoint message *)

        repnd.
        applydup localLe_implies_loc in cpinlog1.
        exists e' i st2; dands; eauto 2 with eo; try congruence;
          try (complete (rewrite eqloc in *; eauto 3 with pbft eo)).
    }
  Qed.

  Lemma checkpoint_of_new_view_received_from_good_replica_was_logged :
    forall (eo : EventOrdering) (e : Event) good vc nv cp i st,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> loc e = PBFTreplica i
      -> node_has_correct_trace_before e good
      -> checkpoint2sender cp = good
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> new_view_in_log nv (view_change_state st)
      -> In vc (new_view2cert nv)
      -> In cp (view_change2cert vc)
      ->
      exists e' good' st2,
        e' ≺ e
        /\ loc e' = PBFTreplica good'
        /\ state_sm_on_event (PBFTreplicaSM good') e' = Some st2
        /\ next_to_execute st2 = next_seq (checkpoint2seq cp)
        /\ checkpoint2digest cp = create_hash_state_last_reply (PBFT.sm_state st2) (last_reply_state st2).
  Proof.
    introv sendbyz ckeys atMostF eqloc ctrace vcgood eqst;
      introv nvinlog vcincert cpincert.

    assert (knows2 e nv) as kn by (eexists; eexists; simpl; dands; eauto).

    pose proof (new_views_learns_or_knows eo) as lok; autodimp lok hyp.
    applydup lok in kn.
    repeat (autodimp kn0 hyp); try (complete (allrw; auto)).

    repndors.

    - (* the new-view was received *)

      unfold learned, learns in kn0; exrepnd; simpl in *.
      eapply pbft_nv_verify_verify_new_view in kn2;[|eauto|reflexivity].
      dup vcincert as verifvc.
      eapply verify_new_view_implies_verify_view_change_in_cert in verifvc; eauto.
      dup cpincert as verifcp.
      eapply verify_view_change_implies_verify_checkpoint in verifcp; eauto.
      pose proof (in_bind_op_list_implies_auth_data_in_trigger (pbft_nv_data2main_auth_data nv) e') as q.
      simpl in q; apply q in kn3; clear q.
      applydup pbft_nv_data2main_auth_data_in_trigger_implies in kn3.

      assert (auth_data_in_trigger (checkpoint2auth_data cp) e')
        as iauth by (unfold auth_data_in_trigger; allrw; simpl; eauto 2 with pbft).

      pose proof (state_sm_before_event_some_between3 e' e (PBFTreplicaSM i) st) as ns.
      repeat (autodimp ns hyp); auto;[].
      exrepnd.

      pose proof (ckeys e' i s') as eqkeys1; autodimp eqkeys1 hyp; eauto 3 with pbft eo;[].
      applydup localLe_implies_loc in kn0.

      applydup implies_authenticated_messages_were_sent_non_byz in sendbyz.
      apply (sendbyz0 _ _ (PBFTreplica good)) in iauth; simpl in *; eauto 3 with pbft eo;
        try (complete (allrw; simpl; tcsp));
        try (complete (subst; destruct cp, b; simpl; tcsp));[].
      exrepnd.

      pose proof (PBFTnever_stops eo e'0 (checkpoint2sender cp)) as w.
      repeat (autodimp w hyp); try (complete (apply ctrace; eauto 4 with eo));[].
      pose proof (PBFTnever_stops_on_event eo e'0 (checkpoint2sender cp)) as z.
      repeat (autodimp z hyp); try (complete (apply ctrace; eauto 4 with eo));[].
      exrepnd.

      applydup checkpoint2auth_data_in_get_contained_auth_data_implies in iauth3.

      (* either
           (1) the good guy sent the checkpoint
           (2) or he sent a view-change containing the checkpoint
           (3) or he sent a new-view containing a view-change containing the checkpoint *)
      repndors;[| |].

      + (* the good guy sent the checkpoint *)

        subst; simpl in *.
        autodimp iauth4 hyp;[].
        repndors; tcsp;[].

        apply send_checkpoint_no_delay in iauth4.
        eapply sent_checkpoint_contains_state in iauth4;
          try (exact z0); auto; tcsp; eauto 4 with pbft eo;[|].

        {
          exrepnd.
          exists e'1 good st2; dands; allrw; auto; eauto 5 with eo pbft.
        }

        {
          introv lee eqloc' ctrace' eqgood' eqst' nvinlog' innvcert' invccert'.
          pose proof (checkpoint_somewhere_in_log_received_from_good_replica_was_logged
                        eo e'1 good cp0 i0 st2) as q.
          repeat (autodimp q hyp); allrw; eauto 5 with pbft eo.
        }

      + (* the good guy sent a view-change containing the checkpoint*)

        exrepnd.
        subst; simpl in *.
        autodimp iauth4 hyp;[].

        (* WARNING *)
        clear iauth3.

        apply send_view_change_no_delay in iauth4.
        eapply sent_view_change_is_in_log2 in iauth4; [| |eauto|eauto]; auto;[].
        repnd; subst; simpl in *.

        rewrite <- ite_first_state_sm_on_event_as_before in w0.
        unfold ite_first in w0.
        destruct (dec_isFirst e'0) as [d|d];[ginv;simpl in *; tcsp|].

        assert ((local_pred e'0) ⊑ e'0) as caus1 by eauto 2 with eo.
        assert ((local_pred e'0) ≺ e) as caus4 by eauto 5 with eo.

        pose proof (checkpoint_somewhere_in_log_received_from_good_replica_was_logged
                      eo (local_pred e'0) (checkpoint2sender cp) cp (checkpoint2sender cp) st1) as q.
        repeat (autodimp q hyp); eauto 5 with pbft eo;
          try (complete (autorewrite with eo pbft in *; allrw; eauto 3 with pbft eo));[].
        exrepnd.
        exists e'1 good' st2; dands; auto; eauto 3 with eo.

      + (* the good guy sent a new-view containing a view-change containing the checkpoint *)

        exrepnd; subst; simpl in *.
        autodimp iauth4 hyp;[].

        apply send_new_view_no_delay in iauth4.
        eapply sent_new_views_are_in_log in iauth4;[| |eauto]; auto;[].

        pose proof (checkpoint_somewhere_in_log_received_from_good_replica_was_logged
                      eo e'0 (checkpoint2sender cp) cp (checkpoint2sender cp) st0) as q.
        repeat (autodimp q hyp); eauto 6 with pbft eo;
          try (complete (autorewrite with eo pbft in *; allrw; eauto 4 with pbft eo));[].
        exrepnd.
        exists e'1 good' st2; dands; auto; eauto 5 with eo.

    - (* the new-view was sent *)

      applydup knows_own_new_view in kn; auto;[].
      exrepnd.

      applydup kn1 in vcincert as vcinlog.
      eapply view_changes_are_received_or_created2 in vcinlog;[allrw; auto |eauto]; auto; try congruence;[].
      exrepnd.

      applydup localLe_implies_loc in vcinlog1 as eqloc1.
      applydup localLe_implies_loc in kn2 as eqloc0.
      unfold lak_data2node in *; simpl in *.
      unfold pbft_nv_data2loc in *; simpl in *.

      (* either we received the view-change or we generated it *)
      repndors; repnd;[|].

      + (* we received the view-change *)
        exrepnd.
        dup vcinlog4 as verifcp.
        eapply verify_view_change_implies_verify_checkpoint in verifcp; eauto;[].

        assert (auth_data_in_trigger (checkpoint2auth_data cp) e'0)
          as iauth by (unfold auth_data_in_trigger; allrw; simpl; eauto 2 with pbft).

        pose proof (ckeys e'0 (new_view2sender nv) st0) as eqkeys1; autodimp eqkeys1 hyp;
          try (complete (eapply state_sm_on_event_some_implies_node_has_correct_trace_before;[|eauto]; simpl; allrw; auto));[].

        applydup localLe_implies_loc in kn2.

        applydup implies_authenticated_messages_were_sent_non_byz in sendbyz.
        apply (sendbyz0 _ _ (PBFTreplica good)) in iauth; simpl in *; eauto 3 with pbft eo;
          try (complete (allrw; simpl; tcsp));
          try (complete (subst; destruct cp, b; simpl; tcsp));
          try (complete (allrw; destruct cp, b; simpl in *; tcsp));[].
        exrepnd.

        assert (e'1 ≺ e) as lee' by eauto 4 with eo.

        pose proof (PBFTnever_stops eo e'1 (checkpoint2sender cp)) as w.
        repeat (autodimp w hyp); try (complete (apply ctrace; eauto 4 with eo));[].
        pose proof (PBFTnever_stops_on_event eo e'1 (checkpoint2sender cp)) as z.
        repeat (autodimp z hyp); try (complete (apply ctrace; eauto 4 with eo));[].
        exrepnd.

        applydup checkpoint2auth_data_in_get_contained_auth_data_implies in iauth3.

        (* either
           (1) the good guy sent the checkpoint
           (2) or he sent a view-change containing the checkpoint
           (3) or he sent a new-view containing a view-change containing the checkpoint *)
        repndors;[| |].

        * (* the good guy sent the checkpoint *)

          subst; simpl in *.
          autodimp iauth4 hyp;[].
          repndors; tcsp;[].

          apply send_checkpoint_no_delay in iauth4.
          eapply sent_checkpoint_contains_state in iauth4;
            try (exact z0); auto; tcsp; eauto 4 with pbft eo;[|].

          {
            exrepnd.
            exists e'2 good st6; dands; allrw; auto; eauto 5 with eo.
          }

          {
            introv lee eqloc' ctrace' eqgood' eqst' nvinlog' innvcert' invccert'.

            pose proof (checkpoint_somewhere_in_log_received_from_good_replica_was_logged
                          eo e'2 good cp0 i0 st6) as q.
            repeat (autodimp q hyp); eauto 4 with pbft eo;
              try (complete (allrw; eauto 3 with pbft eo)).
          }

        * (* the good guy sent a view-change containing the checkpoint*)

          exrepnd.
          subst; simpl in *.
          autodimp iauth4 hyp;[].

          (* WARNING *)
          clear iauth3.

          apply send_view_change_no_delay in iauth4.
          eapply sent_view_change_is_in_log2 in iauth4; [| |eauto|eauto]; auto;[].
          repnd; subst; simpl in *.

          rewrite <- ite_first_state_sm_on_event_as_before in w0.
          unfold ite_first in w0.
          destruct (dec_isFirst e'1) as [d|d];[ginv;simpl in *; tcsp|].

          pose proof (checkpoint_somewhere_in_log_received_from_good_replica_was_logged
                        eo (local_pred e'1) (checkpoint2sender cp) cp (checkpoint2sender cp) st5) as q.
          repeat (autodimp q hyp); eauto 6 with pbft eo;
            try (complete (autorewrite with pbft eo; allrw; eauto 4 with pbft eo));[].
          exrepnd.
          exists e'2 good' st6; dands; auto; eauto 5 with eo.

        * (* the good guy sent a new-view containing a view-change containing the checkpoint *)

          exrepnd; subst; simpl in *.
          autodimp iauth4 hyp;[].

          apply send_new_view_no_delay in iauth4.
          eapply sent_new_views_are_in_log in iauth4;[| |eauto]; auto;[].

          pose proof (checkpoint_somewhere_in_log_received_from_good_replica_was_logged
                        eo e'1 (checkpoint2sender cp) cp (checkpoint2sender cp) st4) as q.
          repeat (autodimp q hyp); eauto 5 with pbft eo;
            try (complete (autorewrite with pbft eo; allrw; eauto 4 with pbft eo));[].

          exrepnd.
          exists e'2 good' st6; dands; auto; eauto 4 with eo.

      + (* the view-change is our own *)
        exrepnd.
        subst.
        simpl in *.

        rewrite <- ite_first_state_sm_on_event_as_before in vcinlog2.
        unfold ite_first in vcinlog2.
        destruct (dec_isFirst e'0) as [d|d];[ginv;simpl in *; tcsp|];[].

        pose proof (checkpoint_somewhere_in_log_received_from_good_replica_was_logged
                      eo (local_pred e'0) (checkpoint2sender cp) cp (new_view2sender nv) st0) as q.
        repeat (autodimp q hyp); autorewrite with eo in *; eauto 6 with pbft eo; try congruence;
          try (complete (allrw; eauto 4 with pbft eo));[].
        exrepnd.
        exists e'1 good' st4; dands; auto; eauto 6 with eo.
  Qed.

End PBFTcheckpoints_from_good.



Hint Resolve verify_view_change_implies_verify_checkpoint : pbft.
Hint Resolve implies_checkpoint2auth_data_in_new_view2auth_data : pbft.
Hint Resolve correct_view_change_implies_no_repeats : pbft.
Hint Resolve correct_view_change_implies_length : pbft.
Hint Resolve send_checkpoint_in_trim_outputs_with_low_water_mark : pbft.
Hint Resolve wf_checkpoint_state_implies_wf_stable : pbft.
Hint Resolve add_checkpoint2checkpoint_some_implies_in : pbft.
Hint Resolve is_stable_checkpoint_entry_implies_le : pbft.
Hint Resolve implies_checkpoint_in_log_cons : pbft.
Hint Resolve checkpoint_in_new_view_implies_somewhere_in_log : pbft.
Hint Resolve checkpoint_in_stable_implies_somewhere_in_log : pbft.
Hint Resolve implies_checkpoint2auth_data_in_view_change2auth_data : pbft.
Hint Resolve add_new_checkpoint2cp_state_preserves_in_stable : pbft.
Hint Resolve correct_view_change_cert_one_implies_eq_digests : pbft.
Hint Resolve correct_view_change_cert_one_implies_eq_seq : pbft.
Hint Resolve correct_view_change_implies_similar_checkpoint_in_new_view : pbft.
Hint Resolve checkpoint_in_view_change_implies_similar_checkpoint_in_view_change : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_checkpoint_certificate_of_last_stable_checkpoint : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_checkpoint_certificate_of_last_stable_checkpoint : pbft.
Hint Resolve in_implies_view_change_in_log : pbft.
Hint Resolve two_in_view_change2cert_implies_same_digests : pbft.
Hint Resolve two_in_view_change2cert_implies_same_seq_nums : pbft.
Hint Resolve view_change_in_log_implies_somewhere : pbft.
Hint Resolve wf_checkpoint_state_implies_wf_checkpoint_log : pbft.
Hint Resolve check_stable_preserves_checkpoint_in_others : pbft.
Hint Resolve add_new_checkpoint2cp_state_preserves_wf_checkpoint_state : pbft.
Hint Resolve checkpoint_entry2stable_preserves_in_checkpoints_backward : pbft.
Hint Resolve checkpoint_entry2stable_preserves_in_checkpoints_forward : pbft.
Hint Resolve checkpoint_in_others_check_on_stable : pbft.


Hint Rewrite @checkpoint_certificate_of_last_stable_checkpoint_update_log : pbft.
Hint Rewrite @checkpoint_certificate_of_last_stable_checkpoint_trim_checkpoint : pbft.
Hint Rewrite @checkpoint_certificate_of_last_stable_checkpoint_update_log_checkpoint_stable : pbft.
Hint Rewrite @checkpoint_certificate_of_last_stable_checkpoint_decrement_requests_in_progress_if_primary : pbft.
Hint Resolve @find_and_execute_requests_preserves_in_checkpoint_certificate_of_last_stable_checkpoint : pbft.
Hint Rewrite @checkpoint_certificate_of_last_stable_checkpoint_change_next_to_execute : pbft.
Hint Rewrite @checkpoint_certificate_of_last_stable_checkpoint_change_sm_state : pbft.
Hint Rewrite @checkpoint_certificate_of_last_stable_checkpoint_change_last_reply_state : pbft.
Hint Rewrite @checkpoint_certificate_of_last_stable_checkpoint_update_view : pbft.
Hint Rewrite @checkpoint_certificate_of_last_stable_checkpoint_change_sequence_number : pbft.
Hint Rewrite @checkpoint_certificate_of_last_stable_checkpoint_log_pre_prepares_of_new_view : pbft.
Hint Rewrite @checkpoint_certificate_of_last_stable_checkpoint_log_new_view_and_entry_state : pbft.
Hint Rewrite @checkpoint_certificate_of_last_stable_checkpoint_log_new_view_state : pbft.
Hint Rewrite @cp_state_decrement_requests_in_progress_if_primary : pbft.
Hint Rewrite @state2hash_decrement_requests_in_progress_if_primary : pbft.
Hint Rewrite @cp_state_update_checkpoint_from_new_view : pbft.
Hint Rewrite @checkpoint_certificate_of_last_stable_checkpoint_update_checkpoint_state : pbft.
