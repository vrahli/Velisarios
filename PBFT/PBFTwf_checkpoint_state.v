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


Require Export PBFTprops2.
Require Export PBFTtactics.
Require Export PBFTwf_prepared_info.
Require Export PBFTordering.
Require Export PBFTtactics3.

Require Export List.
Require Export Peano.


Section PBFTwf_checkpoint_state.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.

  Definition wf_checkpoint_entry_same_seq_and_digest (entry : PBFTcheckpointEntry) : bool :=
    forallb
      (fun c =>
         (same_seq_nums (cp_sn entry) (checkpoint2seq c))
           && (same_digests (cp_d entry) (checkpoint2digest c)))
      (cp_checkpoint entry).

  Definition wf_checkpoint_entry_no_repeats (entry : PBFTcheckpointEntry) : bool :=
    norepeatsb rep_deq (map checkpoint2sender (cp_checkpoint entry)).

  Definition wf_checkpoint_entry (entry : PBFTcheckpointEntry) : bool :=
    (wf_checkpoint_entry_same_seq_and_digest entry)
      && (wf_checkpoint_entry_no_repeats entry).

  Definition wf_stable_checkpoint_entry_same_seq_and_digest (entry : PBFTstableCheckpointEntry) : bool :=
    forallb
      (fun c =>
         (same_seq_nums (scp_sn entry) (checkpoint2seq c))
           && (same_digests (scp_d entry) (checkpoint2digest c)))
      (scp_checkpoint entry).

  Definition wf_stable_checkpoint_entry_no_repeats (entry : PBFTstableCheckpointEntry) : bool :=
    norepeatsb rep_deq (map checkpoint2sender (scp_checkpoint entry)).

  Definition wf_stable_checkpoint_entry (entry : PBFTstableCheckpointEntry) : bool :=
    (wf_stable_checkpoint_entry_same_seq_and_digest entry)
      && (wf_stable_checkpoint_entry_no_repeats entry).

  Fixpoint wf_checkpoint_log (s : PBFTcheckpoint_log) : bool :=
    match s with
    | [] => true
    | entry :: entries => wf_checkpoint_entry entry && wf_checkpoint_log entries
    end.

  Definition wf_stable_checkpoint (entry : PBFTstableCheckpointEntry) : bool :=
    (* either the initial stable checkpoint *)
    (length (scp_checkpoint entry) =? 0)
    ||
    (* or a stable checkpoint *)
    ((F + 1) <=? length (scp_checkpoint entry)).

  Definition wf_checkpoint_state (s : PBFTcheckpointState) : bool :=
    (wf_stable_checkpoint_entry (chk_state_stable s))
      && (wf_stable_checkpoint  (chk_state_stable s))
      && (wf_checkpoint_log (chk_state_others s)).

  Lemma check_send_replies_preserves_cp_state :
    forall i v keys giop s1 n msgs s2,
      check_send_replies i v keys giop s1 n = (msgs, s2)
      -> cp_state s2 = cp_state s1.
  Proof.
    introv check; unfold check_send_replies in check; smash_pbft.
    destruct x; simpl in *; smash_pbft.
  Qed.

  Lemma check_send_replies_update_log_preserves_wf_checkpoint_state :
    forall i v keys giop s1 L n msgs s2,
      check_send_replies i v keys giop (update_log s1 L) n = (msgs, s2)
      -> wf_checkpoint_state (cp_state s1) = true
      -> wf_checkpoint_state (cp_state s2) = true.
  Proof.
    introv check wf.
    apply check_send_replies_preserves_cp_state in check; simpl in check.
    allrw; tcsp.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_wf_checkpoint_state : pbft.

  Definition wf_checkpoint_entry_op (eop : option PBFTcheckpointEntry) : bool :=
    match eop with
    | Some entry => wf_checkpoint_entry entry
    | None => true
    end.

  Lemma implies_wf_checkpoint_log_trim_checkpoint_log :
    forall n L,
      wf_checkpoint_log L = true
      -> wf_checkpoint_log (trim_checkpoint_log n L) = true.
  Proof.
    induction L; introv wf; simpl in *; tcsp; smash_pbft.
  Qed.
  Hint Resolve implies_wf_checkpoint_log_trim_checkpoint_log : pbft.

  Lemma is_stable_checkpoint_entry_implies_wf_stable_checkpoint :
    forall e se,
      is_stable_checkpoint_entry e = true
      -> checkpoint_entry2stable e = Some se
      -> wf_stable_checkpoint se = true.
  Proof.
    introv h check; unfold is_stable_checkpoint_entry in h.
    destruct e; simpl in *; smash_pbft.
    unfold wf_stable_checkpoint; smash_pbft.
  Qed.
  Hint Resolve is_stable_checkpoint_entry_implies_wf_stable_checkpoint : pbft.

  Lemma checkpoint_entry2stable_implies_wf_stable_checkpoint_entry :
    forall e se,
      checkpoint_entry2stable e = Some se
      -> wf_checkpoint_entry e = true
      -> wf_stable_checkpoint_entry se = true.
  Proof.
    introv check wf.
    destruct e; simpl in *; smash_pbft.
  Qed.
  Hint Resolve checkpoint_entry2stable_implies_wf_stable_checkpoint_entry : pbft.

  Lemma check_stable_preserves_wf_checkpoint_state :
    forall i s1 e s2,
      check_stable i s1 e = Some s2
      -> wf_checkpoint_entry e = true
      -> wf_checkpoint_state (cp_state s1) = true
      -> wf_checkpoint_state (cp_state s2) = true.
  Proof.
    introv check wf1 wf2.
    unfold check_stable in check; smash_pbft.
    unfold wf_checkpoint_state; simpl; smash_pbft; dands; eauto 3 with pbft.
    apply implies_wf_checkpoint_log_trim_checkpoint_log; tcsp.
    unfold wf_checkpoint_state in *.
    allrw andb_true; tcsp.
  Qed.
  Hint Resolve check_stable_preserves_wf_checkpoint_state : pbft.

  Lemma same_seq_nums_same :
    forall n, same_seq_nums n n = true.
  Proof.
    introv; unfold same_seq_nums; smash_pbft.
  Qed.
  Hint Resolve same_seq_nums_same : pbft.
  Hint Rewrite same_seq_nums_same : pbft.

  Lemma same_digests_same :
    forall d, same_digests d d = true.
  Proof.
    introv; unfold same_digests; smash_pbft.
  Qed.
  Hint Resolve same_digests_same : pbft.
  Hint Rewrite same_digests_same : pbft.

  Lemma in_sender_of_add_checkpoint2checkpoint_implies :
    forall c l k s,
      add_checkpoint2checkpoint c l = Some k
      -> In s (map checkpoint2sender k)
      -> s = checkpoint2sender c
         \/ In s (map checkpoint2sender l).
  Proof.
    induction l; introv add i; repeat (simpl in *; tcsp; smash_pbft).
    repndors; subst; tcsp.
    pose proof (IHl x s) as q; repeat (autodimp q hyp); tcsp.
  Qed.

  Lemma add_checkpoint2entry_preserves_wf_checkpoint_entry :
    forall a c sm lastr x,
      add_checkpoint2entry a c sm lastr = Some x
      -> is_checkpoint_for_entry a c = true
      -> wf_checkpoint_entry a = true
      -> wf_checkpoint_entry x = true.
  Proof.
    introv add isc wf.
    unfold is_checkpoint_for_entry in isc.
    unfold similar_sn_and_checkpoint_sn in isc; smash_pbft.
    destruct a; simpl in *.
    smash_pbft.
    unfold wf_checkpoint_entry in *; simpl in *.
    unfold wf_checkpoint_entry_same_seq_and_digest in *; simpl in *.
    unfold wf_checkpoint_entry_no_repeats in *; simpl in *.
    smash_pbft.
    revert dependent x0.
    induction cp_checkpoint; introv add; simpl in *; ginv; simpl in *; smash_pbft;
      dands; tcsp;
        try (complete (repeat (autodimp IHcp_checkpoint hyp); tcsp; apply IHcp_checkpoint; auto)).
    eapply in_sender_of_add_checkpoint2checkpoint_implies in i;[|eauto]; tcsp.
  Qed.
  Hint Resolve add_checkpoint2entry_preserves_wf_checkpoint_entry : pbft.

  Lemma add_new_checkpoint2cp_log_preserves_wf_checkpoint_entry_op :
    forall L smstate R c eop K,
      add_new_checkpoint2cp_log L smstate R c = (eop, K)
      -> wf_checkpoint_log L = true
      -> wf_checkpoint_entry_op eop = true.
  Proof.
    induction L; introv add wf; simpl in *; tcsp; ginv; smash_pbft.

    unfold wf_checkpoint_entry_op; simpl.
    unfold wf_checkpoint_entry; simpl.
    unfold wf_checkpoint_entry_same_seq_and_digest; simpl.
    unfold wf_checkpoint_entry_no_repeats; simpl.
    unfold same_seq_nums, same_digests; simpl; smash_pbft.
  Qed.
  Hint Resolve add_new_checkpoint2cp_log_preserves_wf_checkpoint_entry_op : pbft.

  Lemma add_new_checkpoint2cp_log_preserves_wf_checkpoint_log :
    forall L smstate R c eop K,
      add_new_checkpoint2cp_log L smstate R c = (eop, K)
      -> wf_checkpoint_log L = true
      -> wf_checkpoint_log K = true.
  Proof.
    induction L; introv add wf; simpl in *; tcsp; ginv; smash_pbft.

    unfold wf_checkpoint_log; simpl.
    unfold wf_checkpoint_entry; simpl.
    unfold wf_checkpoint_entry_same_seq_and_digest; simpl.
    unfold wf_checkpoint_entry_no_repeats; simpl.
    unfold same_seq_nums, same_digests; simpl; smash_pbft.
  Qed.
  Hint Resolve add_new_checkpoint2cp_log_preserves_wf_checkpoint_log : pbft.

  Lemma add_new_checkpoint2cp_state_preserves_wf_checkpoint_entry_op :
    forall s1 smstate R c eop s2,
      add_new_checkpoint2cp_state s1 smstate R c = (eop, s2)
      -> wf_checkpoint_state s1 = true
      -> wf_checkpoint_entry_op eop = true.
  Proof.
    introv add wf.
    unfold add_new_checkpoint2cp_state in add; smash_pbft.
    destruct s1; simpl in *.
    unfold wf_checkpoint_state in *; simpl in *.
    allrw andb_true; repnd; smash_pbft.
  Qed.
  Hint Resolve add_new_checkpoint2cp_state_preserves_wf_checkpoint_entry_op : pbft.

  Lemma add_new_checkpoint2cp_state_preserves_wf_checkpoint_state :
    forall s1 smstate R c eop s2,
      add_new_checkpoint2cp_state s1 smstate R c = (eop, s2)
      -> wf_checkpoint_state s1 = true
      -> wf_checkpoint_state s2 = true.
  Proof.
    introv add wf.
    unfold add_new_checkpoint2cp_state in add; smash_pbft.
    destruct s1; simpl in *.
    unfold wf_checkpoint_state in *; simpl in *; smash_pbft; dands; eauto 3 with pbft.
  Qed.
  Hint Resolve add_new_checkpoint2cp_state_preserves_wf_checkpoint_state : pbft.

  Lemma cp_state_decrement_requests_in_progress_if_primary :
    forall i v s,
      cp_state (decrement_requests_in_progress_if_primary i v s) = cp_state s.
  Proof.
    introv; destruct s; simpl.
    unfold decrement_requests_in_progress_if_primary; simpl; smash_pbft.
  Qed.
  Hint Rewrite cp_state_decrement_requests_in_progress_if_primary : pbft.

  Lemma implies_wf_checkpoint_state_cp_state_decrement_requests_in_progress_if_primary :
    forall i v s,
      wf_checkpoint_state (cp_state s) = true
      -> wf_checkpoint_state (cp_state (decrement_requests_in_progress_if_primary i v s)) = true.
  Proof.
    introv wf; smash_pbft.
  Qed.
  Hint Resolve implies_wf_checkpoint_state_cp_state_decrement_requests_in_progress_if_primary : pbft.

  Lemma execute_requests_preserves_wf_checkpoint_state :
    forall R i v keys s1 msgs l s2,
      execute_requests i v keys s1 R = (msgs, l, s2)
      -> wf_checkpoint_state (cp_state s1) = true
      -> wf_checkpoint_state (cp_state s2) = true.
  Proof.
    induction R; introv exec wf; simpl in *; smash_pbft.
    unfold check_broadcast_checkpoint in *; simpl in *; smash_pbft.
  Qed.
  Hint Resolve execute_requests_preserves_wf_checkpoint_state : pbft.

  Lemma find_and_execute_requests_preserves_wf_checkpoint_state :
    forall i v keys s1 msgs s2,
      find_and_execute_requests i v keys s1 = (msgs, s2)
      -> wf_checkpoint_state (cp_state s1) = true
      -> wf_checkpoint_state (cp_state s2) = true.
  Proof.
    introv find wf.
    unfold find_and_execute_requests in find; smash_pbft.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_wf_checkpoint_state : pbft.

  Lemma implies_wf_checkpoint_state_trim_checkpoint_state :
    forall n s,
      wf_checkpoint_state s = true
      -> wf_checkpoint_state (trim_checkpoint_state n s) = true.
  Proof.
    introv wf; destruct s; simpl in *.
    unfold wf_checkpoint_state in *; simpl in *; smash_pbft; dands; eauto 3 with pbft.
  Qed.
  Hint Resolve implies_wf_checkpoint_state_trim_checkpoint_state : pbft.

(*  Lemma implies_forallb_add_own_checkpoint_to_certificate_true :
    forall F c C,
      F c = true
      -> forallb F C = true
      -> forallb F (add_own_checkpoint_to_certificate c C) = true.
  Proof.
    introv h q; destruct C; simpl in *; smash_pbft.
  Qed.*)

  Lemma correct_view_change_cert_one_implies_same_seq_nums :
    forall s v S e,
      correct_view_change_cert_one s v S e = true
      -> same_seq_nums s (checkpoint2seq e) = true.
  Proof.
    introv cor.
    unfold correct_view_change_cert_one in cor; smash_pbft.
  Qed.
  Hint Resolve correct_view_change_cert_one_implies_same_seq_nums : pbft.

  Definition view_change2digest (vc : ViewChange) : PBFTdigest :=
    StableChkPt2digest (view_change2stable vc).

  Lemma correct_view_change_cert_one_implies_same_digests :
    forall s v S e,
      correct_view_change_cert_one s v S e = true
      -> same_digests (StableChkPt2digest S) (checkpoint2digest e) = true.
  Proof.
    introv cor.
    unfold correct_view_change_cert_one in cor; smash_pbft.
    unfold same_digests in *; smash_pbft.
  Qed.
  Hint Resolve correct_view_change_cert_one_implies_same_digests : pbft.

  Lemma correct_view_change_implies_all_same_seq_nums :
    forall v vc,
      correct_view_change v vc = true
      -> forallb
           (fun c =>
              (same_seq_nums (view_change2seq vc) (checkpoint2seq c))
                && (same_digests (view_change2digest vc) (checkpoint2digest c)))
           (view_change2cert vc) = true.
  Proof.
    introv cor.
    unfold correct_view_change in cor; smash_pbft.
    unfold correct_view_change_cert in *; smash_pbft.
    allrw forallb_forall.
    introv xx; apply cor0 in xx; smash_pbft.
    dands; unfold view_change2digest; eauto 2 with pbft.
  Qed.
  Hint Resolve correct_view_change_implies_all_same_seq_nums : pbft.

  Lemma correct_view_change_cert_one_implies_eq_digests :
    forall s v S e,
      correct_view_change_cert_one s v S e = true
      -> StableChkPt2digest S = checkpoint2digest e.
  Proof.
    introv cor.
    unfold correct_view_change_cert_one in cor; smash_pbft.
    unfold same_digests in *; smash_pbft.
  Qed.
  Hint Resolve correct_view_change_cert_one_implies_eq_digests : pbft.

  Lemma extract_seq_and_digest_from_checkpoint_certificate_implies_eq_seq_and_digest :
    forall vc n d view,
      extract_seq_and_digest_from_checkpoint_certificate (view_change2cert vc) = Some (n, d)
      -> correct_view_change view vc = true
      -> view_change2seq vc = n
         /\ view_change2digest vc = d.
  Proof.
    introv h cor.
    destruct vc, v; simpl in *.
    destruct C; simpl in *; ginv.
    unfold correct_view_change in cor; simpl in cor.
    unfold view_change2prep in cor; simpl in cor.
    allrw andb_true; repnd.
    unfold correct_view_change_cert, view_change2digest in *; dands; smash_pbft.
  Qed.

  Lemma correct_view_change_implies_norepeatsb :
    forall v vc,
      correct_view_change v vc = true
      -> norepeatsb rep_deq (map checkpoint2sender (view_change2cert vc)) = true.
  Proof.
    introv cor.
    unfold correct_view_change in cor; smash_pbft.
    unfold correct_view_change_cert in *; smash_pbft.
  Qed.
  Hint Resolve correct_view_change_implies_norepeatsb : pbft.

  Lemma in_senders_implies_contains_our_own_checkpoint_message :
    forall i l,
      In i (map checkpoint2sender l)
      -> contains_our_own_checkpoint_message i l = true.
  Proof.
    induction l; introv j; simpl in *; tcsp; repndors; subst; smash_pbft.
  Qed.
  Hint Resolve in_senders_implies_contains_our_own_checkpoint_message : pbft.

(*  Lemma implies_norepeatsb_add_own_checkpoint_to_certificate :
    forall cp l,
      contains_our_own_checkpoint_message (checkpoint2sender cp) l = false
      -> norepeatsb rep_deq (map checkpoint2sender l) = true
      -> norepeatsb rep_deq (map checkpoint2sender (add_own_checkpoint_to_certificate cp l)) = true.
  Proof.
    induction l; introv own norep; simpl in *; tcsp; smash_pbft.
  Qed.
  Hint Resolve implies_norepeatsb_add_own_checkpoint_to_certificate : pbft.*)

  Lemma correct_view_change_implies_stable :
    forall v vc,
      correct_view_change v vc = true
      -> F + 1 <= length (view_change2cert vc).
  Proof.
    introv cor; unfold correct_view_change in cor; smash_pbft.
    unfold correct_view_change_cert in cor0; smash_pbft.
  Qed.
  Hint Resolve correct_view_change_implies_stable : pbft.

  Lemma view_change_cert2max_seq_vc_implies_stable :
    forall nv n vc,
      correct_new_view nv = true
      -> view_change_cert2max_seq_vc (new_view2cert nv) = Some (n, vc)
      -> F + 1 <= length (view_change2cert vc).
  Proof.
    introv cor mseq.
    apply view_change_cert2_max_seq_vc_some_in in mseq.
    apply correct_new_view_implies_correct_view_change in mseq; auto; eauto 3 with pbft.
  Qed.
  Hint Resolve view_change_cert2max_seq_vc_implies_stable : pbft.

  Lemma update_state_new_view_preserves_wf_checkpoint_state :
    forall i s1 nv s2 msgs,
      correct_new_view nv = true
      -> update_state_new_view i s1 nv = (s2, msgs)
      -> wf_checkpoint_state (cp_state s1) = true
      -> wf_checkpoint_state (cp_state s2) = true.
  Proof.
    introv cor upd wf.
    unfold update_state_new_view in upd; smash_pbft.
    unfold update_checkpoint_from_new_view; smash_pbft;
      apply implies_wf_checkpoint_state_trim_checkpoint_state.

    - unfold log_checkpoint_cert_from_new_view in *; smash_pbft.

      + unfold update_stable_sp_log; simpl.
        unfold wf_checkpoint_state in *; smash_pbft.
        unfold wf_stable_checkpoint in *; smash_pbft.
        dands; auto; eauto 3 with pbft;[].

        unfold wf_stable_checkpoint_entry; simpl.

        match goal with
        | [ H : context[view_change_cert2max_seq_vc] |- _ ] => rename H into vcert
        end.
        applydup view_change_cert2_max_seq_vc_some_in in vcert.
        applydup correct_new_view_implies_correct_cert in cor.
        rewrite forallb_forall in cor0.

        applydup cor0 in vcert0.

        match goal with
        | [ H : context[extract_seq_and_digest_from_checkpoint_certificate] |- _ ] => rename H into ext
        end.

        dup ext as ext'.
        eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_seq_and_digest in ext; auto; repnd.
        subst; eauto 3 with pbft.
        unfold wf_stable_checkpoint_entry_same_seq_and_digest; simpl.
        unfold wf_stable_checkpoint_entry_no_repeats; simpl.
        smash_pbft; dands; eauto 2 with pbft.

      + unfold update_stable_sp_log; simpl.
        unfold wf_checkpoint_state in *; smash_pbft.
        unfold wf_stable_checkpoint in *; smash_pbft.
        dands; auto; eauto 3 with pbft;[].
        unfold wf_stable_checkpoint_entry; simpl.

        match goal with
        | [ H : context[view_change_cert2max_seq_vc] |- _ ] => rename H into vcert
        end.

        match goal with
        | [ H : context[extract_seq_and_digest_from_checkpoint_certificate] |- _ ] => rename H into ext
        end.

        applydup sn_of_view_change_cert2max_seq_vc in vcert; subst.

        applydup view_change_cert2_max_seq_vc_some_in in vcert.
        applydup correct_new_view_implies_correct_cert in cor.
        rewrite forallb_forall in cor0.

        applydup cor0 in vcert0.

        dup ext as ext'.
        eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_seq_and_digest in ext; auto; repnd.
        subst.

        unfold wf_stable_checkpoint_entry_same_seq_and_digest,
        wf_stable_checkpoint_entry_no_repeats; simpl; smash_pbft;
          dands; eauto 3 with pbft;
            eapply correct_view_change_implies_all_same_seq_nums; eauto.

    - unfold log_checkpoint_cert_from_new_view in *; smash_pbft.

      + unfold update_stable_sp_log; simpl.
        unfold wf_checkpoint_state in *; smash_pbft.
        unfold wf_stable_checkpoint in *; smash_pbft.
        dands; auto; eauto 3 with pbft;[].
        unfold wf_stable_checkpoint_entry; simpl.

        match goal with
        | [ H : context[view_change_cert2max_seq_vc] |- _ ] => rename H into vcert
        end.
        applydup view_change_cert2_max_seq_vc_some_in in vcert.
        applydup correct_new_view_implies_correct_cert in cor.
        rewrite forallb_forall in cor0.

        applydup cor0 in vcert0.

        match goal with
        | [ H : context[extract_seq_and_digest_from_checkpoint_certificate] |- _ ] => rename H into ext
        end.

        dup ext as ext'.
        eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_seq_and_digest in ext; auto; repnd.
        subst; eauto 3 with pbft.
        unfold wf_stable_checkpoint_entry_same_seq_and_digest; simpl.
        unfold wf_stable_checkpoint_entry_no_repeats; simpl.
        smash_pbft; dands; eauto 2 with pbft.

      + unfold update_stable_sp_log; simpl.
        unfold wf_checkpoint_state in *; smash_pbft.
        unfold wf_stable_checkpoint in *; smash_pbft.
        dands; auto; eauto 3 with pbft;[].
        unfold wf_stable_checkpoint_entry; simpl.

        match goal with
        | [ H : context[view_change_cert2max_seq_vc] |- _ ] => rename H into vcert
        end.

        match goal with
        | [ H : context[extract_seq_and_digest_from_checkpoint_certificate] |- _ ] => rename H into ext
        end.

        applydup sn_of_view_change_cert2max_seq_vc in vcert; subst.

        applydup view_change_cert2_max_seq_vc_some_in in vcert.
        applydup correct_new_view_implies_correct_cert in cor.
        rewrite forallb_forall in cor0.

        applydup cor0 in vcert0.

        dup ext as ext'.
        eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_seq_and_digest in ext; auto; repnd.
        subst.
        unfold wf_stable_checkpoint_entry_same_seq_and_digest; simpl.
        unfold wf_stable_checkpoint_entry_no_repeats; simpl.
        smash_pbft; dands; eauto 3 with pbft;
          eapply correct_view_change_implies_all_same_seq_nums; eauto.
  Qed.
  Hint Resolve update_state_new_view_preserves_wf_checkpoint_state : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_cp_state :
    forall i L s1 s2 msgs,
      add_prepares_to_log_from_new_view_pre_prepares i s1 L = (s2, msgs)
      -> cp_state s2 = cp_state s1.
  Proof.
    induction L; introv add; simpl in *; smash_pbft.
    match goal with
    | [ H : context[add_prepares_to_log_from_new_view_pre_prepares] |- _ ] =>
      apply IHL in H; allrw
    end.

    unfold add_prepare_to_log_from_new_view_pre_prepare in *; smash_pbft.

    match goal with
    | [ H : context[check_send_replies] |- _ ] =>
      apply check_send_replies_preserves_cp_state in H
    end.
    allrw; simpl; auto.
  Qed.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_wf_checkpoint_state :
    forall i L s1 s2 msgs,
      add_prepares_to_log_from_new_view_pre_prepares i s1 L = (s2, msgs)
      -> wf_checkpoint_state (cp_state s1) = true
      -> wf_checkpoint_state (cp_state s2) = true.
  Proof.
    introv add wf.
    apply add_prepares_to_log_from_new_view_pre_prepares_preserves_cp_state in add.
    allrw; auto.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_wf_checkpoint_state : pbft.

  Lemma wf_checkpoint_state_check_one_stable :
    forall i s l,
      wf_checkpoint_state (cp_state s) = true
      -> wf_checkpoint_log l = true
      -> wf_checkpoint_state (cp_state (check_one_stable i s l)) = true.
  Proof.
    induction l; introv wf1 wf2; simpl in *; smash_pbft.
  Qed.
  Hint Resolve wf_checkpoint_state_check_one_stable : pbft.

  Lemma wf_checkpoint_state_implies_wf_checkpoint_log :
    forall s,
      wf_checkpoint_state s = true
      -> wf_checkpoint_log (chk_state_others s) = true.
  Proof.
    introv wf.
    unfold wf_checkpoint_state in wf; smash_pbft.
  Qed.
  Hint Resolve wf_checkpoint_state_implies_wf_checkpoint_log : pbft.

  Lemma implies_wf_checkpoint_state_cp_state_log_new_view_state :
    forall s nv,
      wf_checkpoint_state (cp_state s) = true
      -> wf_checkpoint_state (cp_state (log_new_view_state s nv)) = true.
  Proof.
    tcsp.
  Qed.
  Hint Resolve implies_wf_checkpoint_state_cp_state_log_new_view_state : pbft.

  Lemma implies_wf_checkpoint_state_cp_state :
    forall s v,
      wf_checkpoint_state (cp_state s) = true
      -> wf_checkpoint_state (cp_state (update_view s v)) = true.
  Proof.
    tcsp.
  Qed.
  Hint Resolve implies_wf_checkpoint_state_cp_state : pbft.

  Lemma wf_checkpoint_state_state_preserved_on_event :
    forall (eo  : EventOrdering)
           (e   : Event)
           (slf : Rep)
           (st  : PBFTstate),
      state_sm_on_event (PBFTreplicaSM slf) e = Some st
      -> wf_checkpoint_state (cp_state st) = true.
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers3 smash_pbft_ind6_7.
  Qed.

  Lemma wf_checkpoint_state_state_preserved_before_event :
    forall (eo  : EventOrdering)
           (e   : Event)
           (slf : Rep)
           (st  : PBFTstate),
      state_sm_before_event (PBFTreplicaSM slf) e = Some st
      -> wf_checkpoint_state (cp_state st) = true.
  Proof.
    introv eqst.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d|d]; ginv; subst; simpl in *;tcsp;[].
    eapply wf_checkpoint_state_state_preserved_on_event in eqst; eauto.
  Qed.

End PBFTwf_checkpoint_state.


Hint Resolve check_send_replies_update_log_preserves_wf_checkpoint_state : pbft.
Hint Resolve wf_checkpoint_state_state_preserved_on_event : pbft.
Hint Resolve wf_checkpoint_state_state_preserved_before_event : pbft.
Hint Resolve correct_view_change_cert_one_implies_same_seq_nums : pbft.
Hint Resolve correct_view_change_cert_one_implies_same_digests : pbft.
Hint Resolve correct_view_change_implies_all_same_seq_nums : pbft.
Hint Resolve correct_view_change_cert_one_implies_eq_digests : pbft.
Hint Resolve same_seq_nums_same : pbft.
Hint Resolve same_digests_same : pbft.
Hint Resolve in_senders_implies_contains_our_own_checkpoint_message : pbft.
(*Hint Resolve implies_norepeatsb_add_own_checkpoint_to_certificate : pbft.*)
Hint Resolve is_stable_checkpoint_entry_implies_wf_stable_checkpoint : pbft.
Hint Resolve correct_view_change_implies_stable : pbft.
Hint Resolve view_change_cert2max_seq_vc_implies_stable : pbft.
Hint Resolve checkpoint_entry2stable_implies_wf_stable_checkpoint_entry : pbft.
Hint Resolve wf_checkpoint_state_check_one_stable : pbft.
Hint Resolve wf_checkpoint_state_implies_wf_checkpoint_log : pbft.


Hint Rewrite @same_seq_nums_same : pbft.
Hint Rewrite @same_digests_same : pbft.
