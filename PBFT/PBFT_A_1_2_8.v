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


Require Export PBFTpre_prepare_in_log_preserves.
Require Export PBFTprepare_in_log_preserves.
Require Export PBFTordering.
Require Export PBFTprops3.
Require Export PBFTreceived_prepare_like.
Require Export PBFTgarbage_collect.


Section PBFT_A_1_2_8.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.

  Lemma check_send_replies_preserves_prepare_in_log_reverse :
    forall prep slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> prepare_in_log prep (log state) = true
      -> prepare_in_log prep (log state') = true.
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_prepare_in_log_reverse : pbft.

  Lemma check_send_replies_preserves_pre_prepare_in_log_reverse :
    forall d prep slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> pre_prepare_in_log d prep (log state) = true
      -> pre_prepare_in_log d prep (log state') = true.
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_pre_prepare_in_log_reverse : pbft.

  Lemma pre_prepare_in_log_clear_log_checkpoint_false_if_seq_num_le :
    forall pp d L (n : SeqNum),
      pre_prepare2seq pp <= n
      -> pre_prepare_in_log pp d (clear_log_checkpoint L n) = false.
  Proof.
    induction L; introv len; simpl in *; smash_pbft.
    allrw SeqNumLe_false.
    allrw similar_entry_and_pre_prepare_true_iff.
    destruct pp, a, b; simpl in *; subst; simpl in *; omega.
  Qed.

  Lemma prepare_in_log_clear_log_checkpoint_true_if_seq_num_gt :
    forall p L (n : SeqNum),
      n < prepare2seq p
      -> prepare_in_log p L = true
      -> prepare_in_log p (clear_log_checkpoint L n) = true.
  Proof.
    induction L; introv lgtn prep; simpl in *; smash_pbft.
    allrw SeqNumLe_true.
    allrw is_prepare_for_entry_true_iff.
    destruct p, a, b; simpl in *; subst; simpl in *; omega.
  Qed.

  Lemma pre_prepare2request_data_eq_log_entry_request_data_implies_eq_seq_nums :
    forall pp d e,
      pre_prepare2request_data pp d = log_entry_request_data e
      -> pre_prepare2seq pp = entry2seq e.
  Proof.
    destruct pp, b, e; simpl; introv h; subst; simpl in *; auto.
  Qed.

  Lemma prepare2request_data_eq_log_entry_request_data_implies_eq_seq_nums :
    forall p e,
      prepare2request_data p = log_entry_request_data e
      -> prepare2seq p = entry2seq e.
  Proof.
    destruct p, b, e; simpl; introv h; subst; simpl in *; auto.
  Qed.

  Lemma clear_log_checkpoint_preserves_prepare_in_log_reverse :
    forall p L n pp d,
      prepare_in_log p L = true
      -> pre_prepare2request_data pp d = prepare2request_data p
      -> pre_prepare_in_log pp d (clear_log_checkpoint L n) = true
      -> prepare_in_log p (clear_log_checkpoint L n) = true.
  Proof.
    induction L; simpl in *; introv pinlog eqrd ppinlog; smash_pbft.

    - rewrite pre_prepare_in_log_clear_log_checkpoint_false_if_seq_num_le in ppinlog; auto.
      allrw SeqNumLe_true.
      allrw is_prepare_for_entry_true_iff.
      match goal with
      | [ H1 : _ = prepare2request_data ?x, H2 : _ = prepare2request_data ?x |- _ ] =>
        rewrite <- H1 in H2;
          apply pre_prepare2request_data_eq_log_entry_request_data_implies_eq_seq_nums in H2;
          rewrite H2; auto
      end.

    - apply prepare_in_log_clear_log_checkpoint_true_if_seq_num_gt; auto.
      allrw SeqNumLe_false.
      allrw similar_entry_and_pre_prepare_true_iff.
      match goal with
      | [ H1 : pre_prepare2request_data ?x ?y = _, H2 : _ = pre_prepare2request_data ?x ?y |- _ ] =>
        rewrite H1 in H2; symmetry in H2;
          apply prepare2request_data_eq_log_entry_request_data_implies_eq_seq_nums in H2;
          rewrite H2; auto
      end.
  Qed.

  Lemma check_stable_preserves_prepare_in_log_reverse :
    forall slf st1 st2 giop p pp d,
      check_stable slf st1 giop = Some st2
      -> pre_prepare2request_data pp d = prepare2request_data p
      -> pre_prepare_in_log pp d (log st2) = true
      -> prepare_in_log p (log st1) = true
      -> prepare_in_log p (log st2) = true.
  Proof.
    introv check eqrd ppinlog pinlog.
    unfold check_stable in check.
    destruct giop; smash_pbft.
    eapply clear_log_checkpoint_preserves_prepare_in_log_reverse; eauto.
  Qed.
  Hint Resolve check_stable_preserves_prepare_in_log_reverse : pbft.

  Lemma change_entry_add_replies2entry_preserves_prepare_in_log_reverse :
    forall prep sn entry L reps,
      prepare_in_log prep L = true
      -> find_entry L sn = Some entry
      ->  prepare_in_log
            prep
            (change_entry L (add_replies2entry entry reps)) = true.
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
  Qed.

  Lemma change_log_entry_add_replies2entry_preserves_prepare_in_log_reverse :
      forall prep sn entry state reps,
        prepare_in_log prep (log state) = true
      -> find_entry (log state) sn = Some entry
      -> prepare_in_log
        prep
        (log
           (change_log_entry
              state
              (add_replies2entry entry reps))) = true.
  Proof.
    introv h fe.
    destruct state; simpl in *.
    eapply change_entry_add_replies2entry_preserves_prepare_in_log_reverse in h;[|eauto].
    apply h.
  Qed.

  Lemma find_and_execute_requests_preserves_prepare_in_log_reverse :
    forall msg i prep st p,
      find_and_execute_requests i (current_view p) (local_keys p) p = (msg, st)
      -> prepare_in_log prep (log p) = true
        -> prepare_in_log prep (log st) = true.
  Proof.
    introv H1 H2.

    unfold find_and_execute_requests in *. smash_pbft.
    rename x1 into st.
    unfold execute_requests in *.
    destruct (ready p); simpl in *; [ inversion Heqx; subst; tcsp |].

    pbft_dest_all y.

    match goal with
    | [ H : context[reply2requests] |- _ ] => hide_hyp H
    end.

    match goal with
    | [ H : check_broadcast_checkpoint _ _ _ _ _ = _ |- _ ] =>
      apply check_broadcast_checkpoint_preserves_log in H
    end.

    match goal with
    | [ H : _ = log ?s |- _ ] =>
      rewrite <- H; clear H
    end.

    eapply change_log_entry_add_replies2entry_preserves_prepare_in_log_reverse; [| eauto].
    simpl in *. tcsp.
  Qed.

  (*Fixpoint find_entry (l : PBFTlog) (rd  : RequestData) : option PBFTlogEntry :=
    match l with
    | [] => None
    | entry :: entries =>
      if is_request_data_for_entry entry rd then Some entry

      else find_entry entries rd
    end.

  Definition not_in_list_rep_toks_but_in_log
             (i      : Rep)
             (entry  : PBFTlogEntry)
             (L      : PBFTlog)
             (rd     :  RequestData) : Prop :=
    forall entry',
      in_list_rep_toks i (log_entry_prepares entry) = false
      -> find_entry L rd = Some entry'
      -> log_entry_pre_prepare_info entry' = pp_info_no_pre_prep
         /\ 2 * F <= length (log_entry_prepares entry').*)

  Lemma find_rep_toks_in_list_implies_in :
    forall i preps p,
      find_rep_toks_in_list i preps = Some p
      -> in_list_rep_toks i preps = true.
  Proof.
    induction preps; introv find; simpl in *; ginv; smash_pbft.
  Qed.

  Lemma add_prepare_if_not_enough_does_not_add_implies_length_ge :
    forall i preps1 Fp st preps2,
      rt_rep (Fp tt) = i
      -> add_prepare_if_not_enough i preps1 Fp = (st, preps2)
      -> in_list_rep_toks i preps2 = false
      -> 2 * F <= length preps1.
  Proof.
    introv ei add k.
    unfold add_prepare_if_not_enough in add; smash_pbft.
  Qed.


(*  Lemma add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log_v2 :
    forall i L pp d Fp Fc giop K prep d',
      rt_rep (Fp tt) = i
      -> add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> pre_prepare_in_log prep d' K = true
      -> pre_prepare_in_log prep d' L = true
         \/
         exists rd p_status c_status entry,
           giop = Some (MkGeneratedInfo p_status c_status entry)
           /\ find_entry K rd = Some entry
           /\ prep = pp
           /\ d = d'
           /\ pre_prepare_in_log prep d' L = false
           /\ pre_prepare2request_data pp d = rd
           /\
           not_in_list_rep_toks_but_in_log i entry L rd.
  Proof.
    induction L as [|entry entries ind]; introv eqi h q; simpl in *; ginv; simpl in *; smash_pbft; tcsp.

    {
      simpl in *; smash_pbft.
      unfold eq_request_data in *; smash_pbft.

      right.

      eexists; eexists; eexists; eexists.
      dands; auto; [| | |].

      {
        unfold is_request_data_for_entry.
        unfold eq_request_data in *.
        pbft_dest_all x.
      }

      {
        destruct pp, b. simpl in *.
        destruct prep, b. simpl in *.
        smash_pbft.
        allrw matching_requests_true_iff.
        allrw map_map; simpl.
        allrw map_id; subst; tcsp.
      }

      {
        destruct pp, b. simpl in *.
        destruct prep, b. simpl in *.
        ginv.
      }

      {
        introv j find; ginv.
      }
    }

    {
      unfold not_in_list_rep_toks_but_in_log.
      unfold fill_out_pp_info_with_prepare in *.
      destruct entry as [rd nfo preps comms]; simpl in *.
      destruct nfo; simpl in *; ginv;[].
      smash_pbft.

      right.

      allrw auth_matches_logEntryPrePrepareInfo_pre_prepare2pp_info_true_iff.
      allrw requests_matches_logEntryPrePrepareInfo_true_iff; repnd.
      unfold eq_request_data in *; smash_pbft.

      eexists; eexists; eexists; eexists.
      dands; auto;[| | |]; simpl;
        unfold is_request_data_for_entry, eq_request_data; simpl;
          smash_pbft; tcsp.

      introv j find; ginv; simpl in *.
      dands; auto.

      eapply add_prepare_if_not_enough_does_not_add_implies_length_ge;[|eauto|]; auto.
    }

    {
      allrw similar_entry_and_pre_prepare_true_iff.
      allrw similar_entry_and_pre_prepare_false_iff.

      match goal with
      | [ H : fill_out_pp_info_with_prepare _ _ _ _ _ = _ |- _ ] =>
        applydup fill_out_pp_info_with_prepare_preserves_request_data in H as z;
          symmetry in z
      end.

      rewrite <-  Heqx1 in Heqx2. tcsp.
    }

    {

      match goal with
      | [ H : fill_out_pp_info_with_prepare _ _ _ _ _ = _ |- _ ] =>
        applydup fill_out_pp_info_with_prepare_preserves_request_data in H as z;
          symmetry in z;
          eapply  eq_request_data_preserves_similar_entry_and_pre_prepare in z;[|eauto];pbft_simplifier
      end.
    }

    {
      unfold not_in_list_rep_toks_but_in_log.
      match goal with
      | [ H : context[add_new_pre_prepare_and_prepare2log] |- _ ] => rename H into add
      end.
      eapply ind in add;[| |eauto]; auto.
      repndors; tcsp.
      exrepnd; subst.
      right.
      eexists; eexists; eexists; eexists; dands; eauto; smash_pbft.

      - assert False; tcsp.
        unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
        allrw similar_entry_and_pre_prepare_false_iff; tcsp.

      - assert False; tcsp.
        unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
        allrw similar_entry_and_pre_prepare_false_iff; tcsp.
    }
  Qed.*)


  Fixpoint prepare_of_pre_in_log
           (pp : Pre_prepare)
           (d  : PBFTdigest)
           (i  : Rep)
           (l  : PBFTlog) : bool :=
    match l with
    | [] => false
    | entry :: entries =>
      if similar_entry_and_pre_prepare entry pp d then

        in_list_rep_toks i (log_entry_prepares entry)

      else prepare_of_pre_in_log pp d i entries
    end.

  Lemma add_new_pre_prepare2log_preserves_prepare_of_pre_in_log :
    forall pp d i pp' d' L,
      prepare_of_pre_in_log pp d i L = true
      -> prepare_of_pre_in_log pp d i (add_new_pre_prepare2log pp' d' L) = true.
  Proof.
    induction L; introv prep; simpl in *; tcsp; smash_pbft.
  Qed.
  Hint Resolve add_new_pre_prepare2log_preserves_prepare_of_pre_in_log : pbft.

  Lemma check_send_replies_preserves_prepare_of_pre_in_log :
    forall j v keys giop st1 n msgs st2 pp d i,
      check_send_replies j v keys giop st1 n = (msgs, st2)
      -> prepare_of_pre_in_log pp d i (log st1) = true
      -> prepare_of_pre_in_log pp d i (log st2) = true.
  Proof.
    introv check prep.
    unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_prepare_of_pre_in_log : pbft.

  Lemma add_prepare_if_not_enough_implies_in_list_rep_toks_true :
    forall i L Fp gi K,
      i = rt_rep (Fp tt)
      -> add_prepare_if_not_enough i L Fp = (gi, K)
      -> in_list_rep_toks i K = true.
  Proof.
    introv eqi add; unfold add_prepare_if_not_enough in add; smash_pbft.
  Qed.
  Hint Resolve add_prepare_if_not_enough_implies_in_list_rep_toks_true : pbft.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log_v2 :
    forall i L pp d Fp Fc giop K prep d',
      rt_rep (Fp tt) = i
      -> add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> pre_prepare_in_log prep d' K = true
      -> pre_prepare_in_log prep d' L = true
         \/
         (
           prep = pp
           /\ d' = d
           /\ pre_prepare_in_log prep d' L = false
           /\ prepare_of_pre_in_log pp d i K = true
         ).
  Proof.
    induction L; introv eqi h q; repeat (simpl in *; smash_pbft);
      try (complete (assert False; tcsp;
                     allrw similar_entry_and_pre_prepare_true_iff;
                     allrw similar_entry_and_pre_prepare_false_iff;
                     rename_hyp_with fill_out_pp_info_with_prepare fill;
                     applydup fill_out_pp_info_with_prepare_preserves_request_data in fill;
                     congruence));[|].

    {
      destruct pp, prep, b, b0; simpl in *; smash_pbft.
      unfold eq_request_data in *; simpl in *; smash_pbft; ginv.
      rename_hyp_with matching_requests ma.
      apply matching_requests_true_iff in ma.
      allrw map_map; simpl.
      allrw map_id; subst; tcsp.
    }

    {
      destruct pp, prep, b, b0; simpl in *; smash_pbft.
      rename_hyp_with fill_out_pp_info_with_prepare fill.
      destruct x, gi_entry, a, log_entry_pre_prepare_info0; simpl in *; subst; ginv.
      unfold eq_request_data in *; smash_pbft; ginv.
      allrw matching_requests_true_iff; subst.
      allrw map_map; simpl in *; allrw map_id.
      right; dands; tcsp.
      eapply add_prepare_if_not_enough_implies_in_list_rep_toks_true; eauto.
    }
  Qed.

  Lemma add_prepare_if_not_enough_preserves_in_list_rep_toks :
    forall i L Fp st K j,
      add_prepare_if_not_enough i L Fp = (st, K)
      -> in_list_rep_toks j L = true
      -> in_list_rep_toks j K = true.
  Proof.
    introv add il; unfold add_prepare_if_not_enough in add; smash_pbft.
  Qed.
  Hint Resolve add_prepare_if_not_enough_preserves_in_list_rep_toks : pbft.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_prepare_of_pre_in_log :
    forall i L pp d Fp Fc giop K pp' d' j,
      add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> prepare_of_pre_in_log pp' d' j L = true
      -> prepare_of_pre_in_log pp' d' j K = true.
  Proof.
    induction L; introv add prep; repeat (simpl in *; smash_pbft);
      try (complete (rename_hyp_with fill_out_pp_info_with_prepare fill;
                     apply fill_out_pp_info_with_prepare_preserves_request_data in fill;
                     destruct x, gi_entry, a; simpl in *;
                     unfold eq_request_data in *; smash_pbft));[].

    destruct a, log_entry_pre_prepare_info; simpl in *; ginv; smash_pbft.
  Qed.
  Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_prepare_of_pre_in_log : pbft.

  Lemma add_new_prepare2log_preserves_prepare_of_pre_in_log :
    forall i L p Fc giop K pp d j,
      add_new_prepare2log i L p Fc = (giop, K)
      -> prepare_of_pre_in_log pp d j L = true
      -> prepare_of_pre_in_log pp d j K = true.
  Proof.
    induction L; introv add prep; repeat (simpl in *; smash_pbft);
      try (complete (destruct a; simpl in *; smash_pbft)).
  Qed.
  Hint Resolve add_new_prepare2log_preserves_prepare_of_pre_in_log : pbft.

  Lemma add_new_commit2log_preserves_prepare_of_pre_in_log :
    forall L c x K pp d i,
      add_new_commit2log L c = (x, K)
      -> prepare_of_pre_in_log pp d i L = true
      -> prepare_of_pre_in_log pp d i K = true.
  Proof.
    induction L; introv add prep; simpl in *; smash_pbft;
      try (complete (destruct a; simpl in *; smash_pbft)).
  Qed.
  Hint Resolve add_new_commit2log_preserves_prepare_of_pre_in_log : pbft.

  Lemma check_stable_preserves_pre_prepare_in_log_v2 :
    forall d slf state entry state' p,
      well_formed_log (log state)
      -> check_stable slf state entry = Some state'
      -> pre_prepare_in_log p d (log state') = true
      -> pre_prepare_in_log p d (log state) = true
         /\ cp_sn entry < pre_prepare2seq p.
  Proof.
    introv wf check prep.
    unfold check_stable in check; smash_pbft.
    rename_hyp_with checkpoint_entry2stable check.
    apply checkpoint_entry2stable_implies_same_sn in check; rewrite check; simpl.
    destruct (lt_dec (scp_sn x) (pre_prepare2seq p)) as [d1|d1].
    - dands; apply clear_log_checkpoint_preserves_pre_prepare_in_log in prep; auto; try omega.
    - rewrite pre_prepare_in_log_clear_log_checkpoint_false_if_seq_num_le in prep;
        ginv; try rewrite check; try omega.
  Qed.

  Lemma check_stable_preserves_prepare_of_pre_in_log :
    forall (n : SeqNum) pp d j L,
      n < pre_prepare2seq pp
      -> prepare_of_pre_in_log pp d j L = true
      -> prepare_of_pre_in_log pp d j (clear_log_checkpoint L n) = true.
  Proof.
    induction L; introv h prep; simpl in *; ginv; smash_pbft.
    destruct a; simpl in *.
    unfold eq_request_data in *; smash_pbft.
    destruct pp, b; simpl in *; try omega.
  Qed.
  Hint Resolve check_stable_preserves_prepare_of_pre_in_log : pbft.

  Lemma change_entry_add_replies2entry_preserves_prepare_of_pre_in_log :
    forall pp d i sn entry L reps,
      prepare_of_pre_in_log pp d i L = true
      -> PBFT.find_entry L sn = Some entry
      -> prepare_of_pre_in_log pp d i (change_entry L (add_replies2entry entry reps)) = true.
  Proof.
    induction L; introv prep fe; simpl in *; tcsp; smash_pbft;
      try (complete (destruct entry; simpl in *;
                     unfold is_request_data_for_entry, eq_request_data in *;
                     simpl in *; smash_pbft));
      try (complete (applydup entry2seq_if_find_entry in fe;
                     match goal with
                     | [ H : similar_entry _ _ = _ |- _ ] =>
                       apply entry2seq_if_similar_entry in H
                     end;
                     match goal with
                     | [ H : _ <> _ |- _ ] => destruct H; allrw; auto
                     end)).
  Qed.
  Hint Resolve change_entry_add_replies2entry_preserves_prepare_of_pre_in_log : pbft.

  Lemma find_and_execute_requests_preserves_prepare_of_pre_in_log :
    forall i v keys s1 msgs s2 pp d j,
      find_and_execute_requests i v keys s1 = (msgs, s2)
      -> prepare_of_pre_in_log pp d j (log s1) = true
      -> prepare_of_pre_in_log pp d j (log s2) = true.
  Proof.
    introv fexec prep.
    unfold find_and_execute_requests in fexec; smash_pbft.
    destruct (ready s1); simpl in *; smash_pbft.

    rename_hyp_with check_broadcast_checkpoint check.
    apply check_broadcast_checkpoint_preserves_log in check; simpl in check.
    rewrite <- check in *.
    eapply change_entry_add_replies2entry_preserves_prepare_of_pre_in_log;[|eauto];auto.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_prepare_of_pre_in_log : pbft.

  Lemma log_checkpoint_cert_from_new_view_preserves_prepare_of_pre_in_log :
    forall i st v n C S st' cop pp d j,
      log_checkpoint_cert_from_new_view i st v n C S = (st', cop)
      -> prepare_of_pre_in_log pp d j (log st') = prepare_of_pre_in_log pp d j (log st).
  Proof.
    introv h.
    unfold log_checkpoint_cert_from_new_view in h; smash_pbft.
  Qed.
  Hint Resolve log_checkpoint_cert_from_new_view_preserves_prepare_of_pre_in_log : pbft.

  Lemma log_pre_prepares_preserves_prepare_of_pre_in_log :
    forall pp d i P n L,
      prepare_of_pre_in_log pp d i L = true
      -> prepare_of_pre_in_log pp d i (log_pre_prepares L n P) = true.
  Proof.
    induction P; introv prep; simpl in *; smash_pbft.
  Qed.
  Hint Resolve log_pre_prepares_preserves_prepare_of_pre_in_log : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_in_log_v2 :
    forall d' slf prep pp d state state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state (pp,d) = (state', msgs)
      -> pre_prepare_in_log prep d' (log state') = true
      -> pre_prepare_in_log prep d' (log state) = true
         \/
         (
           prep = pp
           /\ d = d'
           /\ low_water_mark state < pre_prepare2seq pp
           /\ pre_prepare_in_log prep d' (log state) = false
           /\ prepare_of_pre_in_log pp d slf (log state') = true
         ).
  Proof.
    introv h q.
    unfold add_prepare_to_log_from_new_view_pre_prepare in h; smash_pbft.

    rename_hyp_with check_send_replies check.
    rename_hyp_with add_new_pre_prepare_and_prepare2log add.
    apply check_send_replies_preserves_log in check; simpl in *; subst.

    eapply add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log_v2 in q;
      [| |eauto];simpl;autorewrite with pbft;auto.
    repndors; tcsp.
  Qed.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_of_pre_in_log :
    forall i s1 ppd s2 msgs pp d j,
      add_prepare_to_log_from_new_view_pre_prepare i s1 ppd = (s2, msgs)
      -> prepare_of_pre_in_log pp d j (log s1) = true
      -> prepare_of_pre_in_log pp d j (log s2) = true.
  Proof.
    introv add prep.
    unfold add_prepare_to_log_from_new_view_pre_prepare in add; smash_pbft.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_of_pre_in_log : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_of_pre_in_log :
    forall pp d j i pps s1 s2 msgs,
      add_prepares_to_log_from_new_view_pre_prepares i s1 pps = (s2, msgs)
      -> prepare_of_pre_in_log pp d j (log s1) = true
      -> prepare_of_pre_in_log pp d j (log s2) = true.
  Proof.
    induction pps; introv add prep; simpl in *; smash_pbft.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_of_pre_in_log : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_v2 :
    forall d' slf prep pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> pre_prepare_in_log prep d' (log state') = true
      -> pre_prepare_in_log prep d' (log state) = true
         \/
         exists pp d,
           In (pp,d) pps
           /\ prep = pp
           /\ d = d'
           /\ low_water_mark state < pre_prepare2seq pp
           /\ pre_prepare_in_log prep d' (log state) = false
           /\ prepare_of_pre_in_log pp d slf (log state') = true.
  Proof.
    induction pps; introv h q; simpl in *; smash_pbft; repnd.

    rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares adds.
    rename_hyp_with add_prepare_to_log_from_new_view_pre_prepare add.

    eapply IHpps in q;[|eauto].
    clear IHpps.

    repndors; tcsp;[|].

    {
      eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_in_log_v2 in q;[|eauto].
      repndors; repnd; tcsp; subst.
      right.
      exists a0 d'; dands; auto.
      eauto 3 with pbft.
    }

    {
      exrepnd; repnd; subst; tcsp.
      applydup add_prepare_to_log_from_new_view_pre_prepare_preserves_cp_state in add.
      apply eq_low_water_marks_if_eq_cp_states in add0.
      rewrite <- add0.

      remember (pre_prepare_in_log pp d' (log state)) as b.
      symmetry in Heqb; destruct b; tcsp.
      right.
      exists pp d'; dands; auto.
    }
  Qed.

  Lemma update_state_new_view_preserves_prepare_of_pre_in_log_true_forward :
    forall i s1 nv s2 msgs pp d j,
      correct_new_view nv = true
      -> update_state_new_view i s1 nv = (s2, msgs)
      -> low_water_mark s2 < pre_prepare2seq pp
      -> prepare_of_pre_in_log pp d j (log s1) = true
      -> prepare_of_pre_in_log pp d j (log s2) = true.
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
      eauto 2 with pbft.

    - rewrite extract_seq_and_digest_from_checkpoint_certificate_none_implies_correct_view_change_false in mseq0;auto.

    - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext;[|eauto];subst.
      eauto 2 with pbft.

    - rewrite extract_seq_and_digest_from_checkpoint_certificate_none_implies_correct_view_change_false in mseq0;auto.
  Qed.
  Hint Resolve update_state_new_view_preserves_prepare_of_pre_in_log_true_forward : pbft.

  Lemma check_one_stable_preserves_pre_prepare_in_log3 :
    forall (eo : EventOrdering) e i s l p d,
      well_formed_log (log s)
      -> state_sm_before_event (PBFTreplicaSM i) e = Some s
      -> pre_prepare_in_log p d (log (check_one_stable i s l)) = true
      -> pre_prepare_in_log p d (log s) = true /\
         low_water_mark (check_one_stable i s l) < pre_prepare2seq p.
  Proof.
    introv wf eqst prep.
    applydup pre_prepare_in_log_check_one_stable in prep; auto;[].
    eapply pre_prepares_are_between_water_marks_if_in_log_before in eqst; eauto.
    unfold check_between_water_marks in *; smash_pbft.
    apply pre_prepare_in_log_check_one_stable2; auto.
  Qed.
  Hint Resolve  check_one_stable_preserves_pre_prepare_in_log3 : pbft.

  Lemma check_one_stable_preserves_prepare_of_pre_in_log :
    forall i s l pp d j,
      low_water_mark (check_one_stable i s l) < pre_prepare2seq pp
      -> prepare_of_pre_in_log pp d j (log s) = true
      -> prepare_of_pre_in_log pp d j (log (check_one_stable i s l)) = true.
  Proof.
    induction l; introv lwm prep; simpl in *; smash_pbft.
    unfold check_stable in *; smash_pbft.
    rename_hyp_with checkpoint_entry2stable check.
    apply checkpoint_entry2stable_implies_same_sn in check.
    apply check_stable_preserves_prepare_of_pre_in_log; auto;
      try rewrite check; simpl; auto.
  Qed.
  Hint Resolve check_one_stable_preserves_prepare_of_pre_in_log : pbft.

  Lemma check_send_replies_preserves_prepare_of_pre_in_log_reverse :
    forall j v keys giop st1 n msgs st2 pp d i,
      check_send_replies j v keys giop st1 n = (msgs, st2)
      -> prepare_of_pre_in_log pp d i (log st2) = true
      -> prepare_of_pre_in_log pp d i (log st1) = true.
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct giop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_prepare_of_pre_in_log_reverse : pbft.

  Lemma check_send_replies_update_log_preserves_prepare_of_pre_in_log :
    forall pp d slf view keys entryop state sn msgs state' L,
      check_send_replies slf view keys entryop (update_log state L) sn = (msgs, state')
      -> pre_prepare_in_log pp d (log state') = true
      -> prepare_of_pre_in_log pp d slf (log state') = true
      -> prepare_of_pre_in_log pp d slf L = true.
  Proof.
    introv check h1 h2.
    dup check as check1.
    eapply check_send_replies_preserves_pre_prepare_in_log in check;[|eauto]. simpl in *.
    eapply check_send_replies_preserves_prepare_of_pre_in_log_reverse in check1;[eauto|]; simpl. auto.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_prepare_of_pre_in_log : pbft.

  Lemma check_send_replies_update_log_preserves_pre_prepare_in_log :
    forall d slf view keys entryop state sn msgs state' L prep,
       check_send_replies slf view keys entryop (update_log state L) sn = (msgs, state') ->
       pre_prepare_in_log d prep (log state') = true ->
       pre_prepare_in_log d prep L= true.
  Proof.
    introv check h.
    eapply check_send_replies_preserves_pre_prepare_in_log in check; eauto.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_pre_prepare_in_log : pbft.

  Lemma check_send_update_log_replies_preserves_prepare_of_pre_in_log :
    forall d slf view keys entryop state sn msgs state' L pp,
      check_send_replies slf view keys entryop (update_log state L) sn = (msgs, state')
      -> prepare_of_pre_in_log pp d slf L = true
      -> prepare_of_pre_in_log pp d slf (log state') = true.
  Proof.
    introv check h; eapply  check_send_replies_preserves_prepare_of_pre_in_log; eauto.
  Qed.
  Hint Resolve  check_send_update_log_replies_preserves_prepare_of_pre_in_log : pbft.

  Lemma check_send_update_log_replies_preserves_prepare_of_pre_in_log_reverse :
    forall d slf view keys entryop state sn msgs state' L pp,
      check_send_replies slf view keys entryop (update_log state L) sn = (msgs, state')
      -> prepare_of_pre_in_log pp d slf (log state') = true
      -> prepare_of_pre_in_log pp d slf L = true.
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve  check_send_update_log_replies_preserves_prepare_of_pre_in_log_reverse : pbft.


   (* see Invariant A.1.2 (8) in PBFT PhD p.145 *)
  Lemma PBFT_A_1_2_8 :
    forall (eo    : EventOrdering)
           (e     : Event)
           (i     : Rep)
           (pp    : Pre_prepare)
           (d     : PBFTdigest)
           (state : PBFTstate),
      is_primary (pre_prepare2view pp) i = false
      -> state_sm_on_event (PBFTreplicaSM i) e = Some state
      -> pre_prepare_in_log pp d (log state) = true
      -> prepare_of_pre_in_log pp d i (log state) = true.
  Proof.
    intros eo e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv notprim eqst prep.

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

      eapply add_new_pre_prepare2log_preserves_prepare_of_pre_in_log.
      apply pre_prepare_in_log_add_new_prepare2log in prep.
      repndors; repnd;[try (smash_pbft_ind ind)|];[].
      subst; simpl in *.
      autorewrite with pbft in *; ginv.
    }

    {
      (* pre-prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_pre_prepare_and_prepare2log add.

      eapply check_send_replies_preserves_pre_prepare_in_log in prep;[|eauto].
      simpl in *.
      eapply check_send_replies_preserves_prepare_of_pre_in_log;[eauto|]; simpl.
      clear check.

      eapply add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log_v2 in prep;
        [| |eauto]; simpl; autorewrite with pbft; auto.
      repndors; repnd;[|subst pp d; simpl in *; eauto 3 with pbft];[].
      eapply add_new_pre_prepare_and_prepare2log_preserves_prepare_of_pre_in_log;[eauto|].
      try (smash_pbft_ind ind).
    }

    {
      (* prepare *)

      rename_hyp_with add_new_prepare2log add.
      rename_hyp_with check_send_replies check.
      eapply check_send_replies_update_log_preserves_pre_prepare_in_log in prep; eauto.
      eapply check_send_update_log_replies_preserves_prepare_of_pre_in_log; eauto.
      eapply add_new_prepare2log_preserves_pre_prepare_in_log in prep;[|eauto].
      eapply add_new_prepare2log_preserves_prepare_of_pre_in_log;[eauto|].
      try (smash_pbft_ind ind).
    }

    { (* commit *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_commit2log add.
      applydup check_send_replies_preserves_log in check; simpl in *; subst.
      clear check.
      erewrite add_new_commit2log_preserves_pre_prepare_in_log in prep;[|eauto].
      eapply add_new_commit2log_preserves_prepare_of_pre_in_log;[eauto|].
      try (smash_pbft_ind ind).
    }

    {
      (* handle check-stable *)

      eapply check_one_stable_preserves_pre_prepare_in_log3 in prep;
        [| |eauto];[|eauto 2 with pbft]; repnd.
      apply check_one_stable_preserves_prepare_of_pre_in_log; auto.
      try (smash_pbft_ind ind).
    }

    {
      (* check_bcast_new_view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with CheckBCastNewView2entry cb.

      apply CheckBCastNewView2entry_some_implies in cb.

      unfold update_state_new_view in upd; smash_pbft;[| |].

      - rename_hyp_with log_checkpoint_cert_from_new_view chk.
        applydup log_checkpoint_cert_from_new_view_preserves_well_formed_log in chk;[|simpl];[|eauto 4 with pbft];[].
        applydup clear_log_checkpoint_preserves_pre_prepare_in_log in prep;auto;[].

        destruct (lt_dec x7 (pre_prepare2seq pp)) as [d1|d1];
          [|rewrite pre_prepare_in_log_clear_log_checkpoint_false_if_seq_num_le
             in prep;auto;omega];[].
        eapply check_stable_preserves_prepare_of_pre_in_log;auto.
        erewrite log_checkpoint_cert_from_new_view_preserves_pre_prepare_in_log in prep0;[|eauto].
        simpl in *.
        erewrite log_checkpoint_cert_from_new_view_preserves_prepare_of_pre_in_log;[|eauto].
        simpl.

        apply pre_prepare_in_log_log_pre_prepares_implies in prep0.
        repndors.

        + apply log_pre_prepares_preserves_prepare_of_pre_in_log.
          try (smash_pbft_ind ind).

        + assert False; tcsp.
          repnd.
          dup prep1 as eqnv.
          eapply check_broadcast_new_view_preserves_view in eqnv;[|eauto];[].
          rewrite <- eqnv in *; clear eqnv.
          applydup check_broadcast_new_view_some_implies in check.
          exrepnd.
          subst; simpl in *; autorewrite with pbft in *.

          assert (wf_view_change_entry x) as wfx by eauto 3 with pbft.
          rename_hyp_with vce_view_change vvc.
          apply wfx in vvc.
          rewrite vvc in *.
          pbft_simplifier.

      - apply pre_prepare_in_log_log_pre_prepares_implies in prep.
        repndors.

        + apply log_pre_prepares_preserves_prepare_of_pre_in_log.
          try (smash_pbft_ind ind).

        + assert False; tcsp.
          repnd.
          dup prep0 as eqnv.
          eapply check_broadcast_new_view_preserves_view in eqnv;[|eauto];[].
          rewrite <- eqnv in *; clear eqnv.
          applydup check_broadcast_new_view_some_implies in check.
          exrepnd.
          subst; simpl in *; autorewrite with pbft in *.

          assert (wf_view_change_entry x) as wfx by eauto 3 with pbft.
          rename_hyp_with vce_view_change vvc.
          apply wfx in vvc.
          rewrite vvc in *.
          pbft_simplifier.

      - apply pre_prepare_in_log_log_pre_prepares_implies in prep.
        repndors.

        + apply log_pre_prepares_preserves_prepare_of_pre_in_log.
          try (smash_pbft_ind ind).

        + assert False; tcsp.
          repnd.
          dup prep0 as eqnv.
          eapply check_broadcast_new_view_preserves_view in eqnv;[|eauto];[].
          rewrite <- eqnv in *; clear eqnv.
          applydup check_broadcast_new_view_some_implies in check.
          exrepnd.
          subst; simpl in *; autorewrite with pbft in *.

          assert (wf_view_change_entry x) as wfx by eauto 3 with pbft.
          rename_hyp_with vce_view_change vvc.
          apply wfx in vvc.
          rewrite vvc in *.
          pbft_simplifier.
    }

    {
      (* new_view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with has_new_view hnv.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      eapply update_state_new_view_preserves_pre_prepare_in_log2 in prep;
        [| | |eauto];simpl; auto;[].
      exrepnd.
      simpl in *; autorewrite with pbft in *.
      hide_hyp prep0.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_low_water_mark in add.
      autorewrite with pbft in *.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_v2 in prep2;
        [|eauto];[].
      simpl in *.

      repndors;[|].

      - dup prep2 as bwm.
        eapply pre_prepares_are_between_water_marks_if_in_log_before in bwm;[|eauto].
        unfold check_between_water_marks in *; smash_pbft.

        assert (prepare_of_pre_in_log pp d i (log p) = true) as h by (smash_pbft_ind ind).
        eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_of_pre_in_log in add;
          simpl;[|eauto].

        eapply update_state_new_view_preserves_prepare_of_pre_in_log_true_forward;
          [|eauto| |]; simpl; auto.

        show_hyp prep0.
        repndors; repnd; tcsp; try omega; try congruence.

      - exrepnd; subst.
        simpl in *; autorewrite with pbft in *.

        eapply update_state_new_view_preserves_prepare_of_pre_in_log_true_forward;
          [|eauto| |]; simpl; auto.

        show_hyp prep0.
        repndors; repnd; tcsp; try omega; try congruence.
    }
  Qed.
  Hint Resolve PBFT_A_1_2_8 : pbft.

  Lemma PBFT_A_1_2_8_before :
    forall (eo    : EventOrdering)
           (e     : Event)
           (i     : Rep)
           (pp    : Pre_prepare)
           (d     : PBFTdigest)
           (state : PBFTstate),
      is_primary (pre_prepare2view pp) i = false
      -> state_sm_before_event (PBFTreplicaSM i) e = Some state
      -> pre_prepare_in_log pp d (log state) = true
      -> prepare_of_pre_in_log pp d i (log state) = true.
  Proof.
    introv nprim eqst prep.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d1|d1]; ginv; subst; simpl in *;[].
    eauto 3 with pbft.
  Qed.
  Hint Resolve PBFT_A_1_2_8_before : pbft.

End PBFT_A_1_2_8.


Hint Resolve check_send_replies_preserves_prepare_in_log_reverse : pbft.
Hint Resolve check_send_replies_preserves_pre_prepare_in_log_reverse : pbft.
Hint Resolve check_stable_preserves_prepare_in_log_reverse : pbft.
Hint Resolve add_new_pre_prepare2log_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve check_send_replies_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve add_prepare_if_not_enough_implies_in_list_rep_toks_true : pbft.
Hint Resolve add_prepare_if_not_enough_preserves_in_list_rep_toks : pbft.
Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve add_new_prepare2log_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve add_new_commit2log_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve check_stable_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve change_entry_add_replies2entry_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve find_and_execute_requests_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve log_checkpoint_cert_from_new_view_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve log_pre_prepares_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve update_state_new_view_preserves_prepare_of_pre_in_log_true_forward : pbft.
Hint Resolve check_one_stable_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve PBFT_A_1_2_8 : pbft.
Hint Resolve PBFT_A_1_2_8_before : pbft.
Hint Resolve check_one_stable_preserves_pre_prepare_in_log3 : pbft.
Hint Resolve check_send_replies_preserves_prepare_of_pre_in_log_reverse : pbft.
Hint Resolve check_send_replies_update_log_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve check_send_replies_update_log_preserves_pre_prepare_in_log : pbft.
Hint Resolve check_send_update_log_replies_preserves_prepare_of_pre_in_log : pbft.
Hint Resolve check_send_update_log_replies_preserves_prepare_of_pre_in_log_reverse : pbft.
