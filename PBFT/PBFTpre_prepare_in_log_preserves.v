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


Require Export PBFTprops3.
Require Export PBFTwell_formed_log.


Section PBFTpre_prepare_in_log_preserves.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma add_new_commit2log_preserves_pre_prepare_in_log :
    forall d p c L1 L2 i,
      add_new_commit2log L1 c = (i, L2)
      -> pre_prepare_in_log p d L2 = pre_prepare_in_log p d L1.
  Proof.
    induction L1; introv h; simpl in *; tcsp; smash_pbft.

    { pbft_simplifier; simpl in *; pbft_dest_all w. }

    - match goal with
      | [H : add_commit2entry _ _ = _ |- _ ] =>
        apply add_commit2entry_preserves_log_entry_pre_prepare_info in H
      end.
      allrw. auto.

    - match goal with
      | [H : add_commit2entry _ _ = _ |- _ ] =>
        apply add_commit2entry_preserves_log_entry_request_data in H
      end.
      allrw similar_entry_and_pre_prepare_true_iff.
      allrw similar_entry_and_pre_prepare_false_iff.
      rewrite <- Heqx1 in Heqx2. tcsp.

    - match goal with
      | [H : add_commit2entry _ _ = _ |- _ ] =>
        apply add_commit2entry_preserves_log_entry_request_data in H
      end.
      allrw similar_entry_and_pre_prepare_true_iff.
      allrw similar_entry_and_pre_prepare_false_iff.
      rewrite <- Heqx1 in Heqx2. tcsp.
  Qed.

  Lemma entry_of_pre_prepare_in_log :
    forall d p L,
      pre_prepare_in_log p d L = true
      -> exists entry,
        In entry L
        /\ log_entry_request_data entry = pre_prepare2request_data p d.
  Proof.
    induction L; introv h; simpl in *; tcsp.
    pbft_dest_all x.

    - exists a; dands; tcsp.
      allrw similar_entry_and_pre_prepare_true_iff; auto.

    - apply IHL in h; exrepnd; exists entry; auto.
  Qed.

  Lemma clear_log_checkpoint_preserves_pre_prepare_in_log :
    forall d p L sn,
      well_formed_log L
      -> pre_prepare_in_log p d (clear_log_checkpoint L sn) = true
      -> pre_prepare_in_log p d L = true.
  Proof.
    induction L; simpl in *; introv wf h; tcsp.
    pbft_dest_all x.

    - assert False; tcsp.

      inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.

      allrw similar_entry_and_pre_prepare_true_iff.

      match goal with
      | [ H : pre_prepare_in_log _ _ _ = _ |- _ ] => apply entry_of_pre_prepare_in_log in H
      end.
      exrepnd.
      pose proof (imp entry) as q; autodimp q hyp; apply q; auto.
      allrw; auto.

    - inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.

    - inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.
  Qed.

  Lemma check_stable_preserves_pre_prepare_in_log :
    forall d slf state entryop state' p,
      well_formed_log (log state)
      -> check_stable slf state entryop = Some state'
      -> pre_prepare_in_log p d (log state') = true
      -> pre_prepare_in_log p d (log state) = true.
  Proof.
    introv wf h q.
    unfold check_stable in h.
    pbft_dest_all x;[].
    apply clear_log_checkpoint_preserves_pre_prepare_in_log in q; auto.
  Qed.

  Lemma change_entry_add_replies2entry_preserves_pre_prepare_in_log :
    forall d prep sn entry L reps,
      pre_prepare_in_log
        d prep
        (change_entry L (add_replies2entry entry reps)) = true
      -> find_entry L sn = Some entry
      -> pre_prepare_in_log d prep L = true.
  Proof.
    induction L; introv h fe; simpl in *; tcsp.
    smash_pbft;[| | | |];
      try (complete (applydup entry2seq_if_find_entry in fe as eqsn;
                     match goal with
                     | [ H : similar_entry _ _ = _ |- _ ] => apply entry2seq_if_similar_entry in H
                     end;
                     match goal with
                     | [ H : _ <> _ |- _ ] => destruct H; allrw; auto
                     end));[|].

    - repnd.
      allrw similar_entry_and_pre_prepare_false_iff.

      match goal with
      | [ H : _ <> _ |- _ ] => destruct H; allrw; auto
      end.

      unfold rep_toks_matches_logEntryPrePrepareInfo in *.
      destruct (log_entry_pre_prepare_info entry);[|]; simpl in *; tcsp.
      smash_pbft.
      allrw similar_entry_and_pre_prepare_true_iff.

      rewrite log_entry_request_data_add_replies2entry in Heqx0.
      auto.

    - allrw similar_entry_and_pre_prepare_false_iff.
      rewrite log_entry_request_data_add_replies2entry in Heqx0.
      unfold rep_toks_matches_logEntryPrePrepareInfo in *.
      destruct (log_entry_pre_prepare_info entry);simpl in *;
        allrw similar_entry_and_pre_prepare_true_iff; tcsp.
  Qed.

  Lemma change_log_entry_add_replies2entry_preserves_pre_prepare_in_log :
    forall d prep sn entry state reps,
      pre_prepare_in_log
        d prep
        (log
           (change_log_entry
              state
              (add_replies2entry entry reps))) = true
      -> find_entry (log state) sn = Some entry
      -> pre_prepare_in_log d prep (log state) = true.
  Proof.
    introv h fe.
    destruct state; simpl in *.
    eapply change_entry_add_replies2entry_preserves_pre_prepare_in_log in h;[|eauto].
    auto.
  Qed.

  Lemma find_and_execute_requests_preserves_pre_prepare_in_log :
    forall d msg i prep st p,
      find_and_execute_requests i (current_view p) (local_keys p) p = (msg, st)
      -> pre_prepare_in_log d prep (log st) = true
      -> pre_prepare_in_log d prep (log p) = true.
  Proof.
    introv H1 H2.

    unfold find_and_execute_requests in *.
    pbft_dest_all x;[].
    rename x1 into st.
    unfold execute_requests in *.
    destruct (ready p); simpl in *;[ inversion Heqx; allrw; tcsp |].

    pbft_dest_all y.

    match goal with
    | [ H : context[reply2requests] |- _ ] => hide_hyp H
    end.

    match goal with
    | [ H : check_broadcast_checkpoint _ _ _ _ _ = _ |- _ ] =>
      apply check_broadcast_checkpoint_preserves_log in H
    end.

    match goal with
    | [ H1 : pre_prepare_in_log _ _ (log ?s) = _, H2 : _ = log ?s |- _ ] =>
      rewrite <- H2 in H1; clear H2
    end.

    pose proof (change_log_entry_add_replies2entry_preserves_pre_prepare_in_log
                  d prep (next_to_execute p) y p y3) as xx.
    apply xx in H2; auto.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_pre_prepare_in_log : pbft.

  Lemma check_send_replies_preserves_pre_prepare_in_log :
    forall d prep slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> pre_prepare_in_log d prep (log state') = true
      -> pre_prepare_in_log d prep (log state) = true.
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_pre_prepare_in_log : pbft.

  Lemma add_new_prepare2log_preserves_pre_prepare_in_log :
    forall i d gi Fc prep new_prep L new_log,
      add_new_prepare2log i L new_prep Fc = (gi, new_log)
      -> pre_prepare_in_log d prep new_log = true
      -> pre_prepare_in_log d prep L = true.
  Proof.
    induction L; introv IH1 IH2; simpl in *; smash_pbft;
    try (complete(allrw is_prepare_for_entry_true_iff;
                  allrw is_prepare_for_entry_false_iff;
                  destruct x;[]; simpl in *;
                  unfold add_prepare2entry in *;
                  destruct a;[]; simpl in *;
                  smash_pbft)).

    { pbft_simplifier; simpl in *; pbft_dest_all w. }
  Qed.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log :
    forall i L pp d Fp Fc giop K prep d',
      add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> pre_prepare_in_log prep d' K = true
      -> pre_prepare_in_log prep d' L = true
         \/
         (
           prep = pp
           /\ d = d'
           /\ pre_prepare_in_log prep d' L = false
         ).
  Proof.
    induction L; introv h q; simpl in *; smash_pbft.

    {
      simpl in *; smash_pbft.

      destruct pp, prep.
      destruct b, b0.
      simpl in *.
      smash_pbft.
      unfold eq_request_data in *; simpl in *; smash_pbft; ginv.
      match goal with
      | [ H : matching_requests _ _ = _ |- _ ] =>
        apply matching_requests_true_iff in H
      end.
      allrw map_map; simpl.
      allrw map_id; subst; tcsp.
    }

    {
      exrepnd.
      destruct x; simpl in *.
      unfold fill_out_pp_info_with_prepare in *.
      destruct a; simpl in *.
      destruct log_entry_pre_prepare_info; simpl in *; ginv; simpl in *; tcsp.
      smash_pbft;[].

      unfold eq_request_data in *.
      pbft_dest_all y;[].

      allrw auth_matches_logEntryPrePrepareInfo_pre_prepare2pp_info_true_iff.
      allrw requests_matches_logEntryPrePrepareInfo_true_iff.

      exrepnd.

      unfold add_prepare_if_not_enough in *.
      smash_pbft;[|];
        try (complete (right; destruct pp, prep; destruct b, b0;
                       simpl in *; subst; GC; ginv)).
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
  Qed.

  Lemma rep_toks_matches_logEntryPrePrepareInfo_true_iff :
    forall rt i nfo,
      rep_toks_matches_logEntryPrePrepareInfo rt i nfo = true
      <->
      exists auth reqs,
        nfo = pp_info_pre_prep auth reqs
        /\ rt = MkRepToks i auth.
  Proof.
    introv; unfold rep_toks_matches_logEntryPrePrepareInfo; split;
      intro h; destruct nfo; exrepnd; subst; smash_pbft; ginv; eauto.
  Qed.

  Lemma auth_matches_logEntryPrePrepareInfo_true_iff :
    forall a nfo,
      auth_matches_logEntryPrePrepareInfo a nfo = true
      <->
      exists reqs,
        nfo = pp_info_pre_prep a reqs.
  Proof.
    introv; unfold auth_matches_logEntryPrePrepareInfo; split;
      intro h; destruct nfo; exrepnd; subst; smash_pbft; ginv; eauto.
  Qed.

  Lemma pre_prepare_in_log_add_new_prepare2log :
    forall pp d npp nd L,
      pre_prepare_in_log pp d (add_new_pre_prepare2log npp nd L) = true
      -> pre_prepare_in_log pp d L = true
         \/
         (pp = npp /\ d = nd /\ pre_prepare_in_log pp d L = false).
  Proof.
    induction L; introv h; simpl in *; smash_pbft;[|].

    - right.
      unfold eq_request_data in *; smash_pbft.
      repnd.
      allrw auth_matches_logEntryPrePrepareInfo_pre_prepare2pp_info_true_iff.
      allrw requests_matches_logEntryPrePrepareInfo_true_iff; repnd.
      autorewrite with pbft in *; dands; eauto 3 with pbft.

    - clear IHL.
      repnd; GC.
      allrw auth_matches_logEntryPrePrepareInfo_pre_prepare2pp_info_true_iff.
      allrw requests_matches_logEntryPrePrepareInfo_true_iff; repnd.
      allrw similar_entry_and_pre_prepare_true_iff.

      match goal with
      | [ H1 : log_entry_request_data ?x = _, H2 : log_entry_request_data ?x = _ |- _ ] =>
        rewrite H1 in H2
      end.

      smash_pbft.

      match goal with
      | [ |- context[auth_matches_logEntryPrePrepareInfo ?x ?y] ] =>
        remember (auth_matches_logEntryPrePrepareInfo x y) as b
      end.
      symmetry in Heqb; destruct b; tcsp;
        [|right; dands; eauto 3 with pbft].

      rewrite auth_matches_logEntryPrePrepareInfo_true_iff in Heqb; exrepnd.
      rewrite Heqb0 in *; simpl in *.

      remember (matching_requests (pre_prepare2requests pp) (map fst reqs)) as w.
      symmetry in Heqw; destruct w; tcsp.
  Qed.

  Lemma pre_prepare_in_log_add_new_pre_prepare2log_false_implies :
    forall pp d pp' d' L,
      pre_prepare_in_log pp d (add_new_pre_prepare2log pp' d' L) = false
      -> pre_prepare_in_log pp d L = false.
  Proof.
    induction L; introv h; simpl in *; smash_pbft.
    repndors; smash_pbft; tcsp; GC;
      destruct a, log_entry_pre_prepare_info; simpl in *; tcsp.
  Qed.
  Hint Resolve pre_prepare_in_log_add_new_pre_prepare2log_false_implies : pbft.

  Lemma pre_prepare_in_log_log_pre_prepares_implies :
    forall pp d P L lwm,
      pre_prepare_in_log pp d (log_pre_prepares L lwm P) = true
      -> pre_prepare_in_log pp d L = true
         \/
         (
           In (pp,d) P
           /\ pre_prepare_in_log pp d L = false
           /\ lwm < pre_prepare2seq pp
         ).
  Proof.
    induction P; introv h; simpl in *; tcsp.
    repnd; simpl in *; smash_pbft; apply IHP in h; repndors; repnd; tcsp;[|].

    - apply pre_prepare_in_log_add_new_prepare2log in h; repndors; repnd; subst; tcsp.

    - apply pre_prepare_in_log_add_new_pre_prepare2log_false_implies in h1; tcsp.
  Qed.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_in_log :
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
         ).
  Proof.
    introv h q.
    unfold add_prepare_to_log_from_new_view_pre_prepare in h; smash_pbft.

    match goal with
    | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
      apply check_send_replies_preserves_log in H; simpl in *; subst
    end.

    match goal with
    | [ H : add_new_pre_prepare_and_prepare2log _ _ _ _ _ _ = _ |- _ ] =>
      eapply add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log in H;[|eauto]
    end.

    repndors; tcsp.
  Qed.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log :
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
           /\ pre_prepare_in_log prep d' (log state) = false.
  Proof.
    induction pps; introv h q; simpl in *; smash_pbft; repnd.

    match goal with
    | [ H : add_prepares_to_log_from_new_view_pre_prepares _ _ _ = _ |- _ ] =>
      applydup IHpps in H;auto;[]
    end.
    repndors; tcsp;[|].

    {
      match goal with
      | [ H : add_prepare_to_log_from_new_view_pre_prepare _ _ _ = _ |- _ ] =>
        eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_in_log in H;[|eauto]
      end.

      repndors; repnd; tcsp; subst.
      right.
      exists a0 d'; dands; auto.
    }

    {
      exrepnd; repnd; subst; tcsp.

      rename_hyp_with add_prepare_to_log_from_new_view_pre_prepare add.
      applydup add_prepare_to_log_from_new_view_pre_prepare_preserves_cp_state in add.
      apply eq_low_water_marks_if_eq_cp_states in add0.
      rewrite <- add0.

      remember (pre_prepare_in_log pp d' (log state)) as b.
      symmetry in Heqb; destruct b; tcsp.
      right.
      exists pp d'; dands; auto.
    }
  Qed.

  (*Lemma update_state_new_view_preserves_pre_prepare_in_log :
    forall i st nv st' msgs pp d,
      update_state_new_view i st nv = (st', msgs)
      -> pre_prepare_in_log pp d (log st) = true
      -> pre_prepare_in_log pp d (log st') = true.
  Proof.
    introv u prep.
    unfold update_state_new_view in u; smash_pbft.
    rename_hyp_with log_checkpoint_cert_from_new_view chk.
    apply log_checkpoint_cert_from_new_view_preserves_log in chk.
    rewrite <- chk.

    SearchAbout clear_log_checkpoint.
XXXXXXXX
    Check clear_log_checkpoint_preserves_pre_prepare_in_log.
    eapply clear_log_checkpoint_preserves_pre_prepare_in_log; eauto.
    allrw <- ; auto.
    apply update_state_new_view_preserves_log in u; allrw <-; auto.
  Qed.
  Hint Resolve update_state_new_view_preserves_pre_prepare_in_log : pbft.*)

  Lemma pre_prepare_in_log_log_pre_prepares_false :
    forall pp d P L lwm,
      pre_prepare_in_log pp d (log_pre_prepares L lwm P) = false
      -> pre_prepare_in_log pp d L = false.
  Proof.
    induction P; introv h; simpl in *; auto.
    repnd; simpl in *; smash_pbft.
  Qed.
  Hint Resolve pre_prepare_in_log_log_pre_prepares_false : pbft.

  Lemma log_checkpoint_cert_from_new_view_preserves_pre_prepare_in_log :
    forall i st v x1 C S st' x3 pp d,
      log_checkpoint_cert_from_new_view i st v x1 C S = (st', x3)
      -> pre_prepare_in_log pp d (log st') = pre_prepare_in_log pp d (log st).
  Proof.
    introv h.
    unfold log_checkpoint_cert_from_new_view in h; smash_pbft.
  Qed.
  Hint Resolve log_checkpoint_cert_from_new_view_preserves_pre_prepare_in_log : pbft.

  (*Lemma log_update_low_water_mark :
    forall s n, log (update_low_water_mark s n) = log s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite log_update_low_water_mark : pbft.*)

  Lemma update_state_new_view_preserves_pre_prepare_in_log :
    forall i st nv st' msgs pp d,
      well_formed_log (log st)
      -> update_state_new_view i st nv = (st', msgs)
      -> pre_prepare_in_log pp d (log st') = true
      -> pre_prepare_in_log pp d (log st) = true.
  Proof.
    introv wf upd prep; unfold update_state_new_view in upd; smash_pbft.
    rename_hyp_with log_checkpoint_cert_from_new_view chk.
    apply log_checkpoint_cert_from_new_view_preserves_log in chk.
    rewrite chk.
    eapply clear_log_checkpoint_preserves_pre_prepare_in_log; eauto.
    allrw <- ; auto.
  Qed.
  Hint Resolve update_state_new_view_preserves_pre_prepare_in_log : pbft.

  Lemma pre_prepare_in_log_check_one_stable :
    forall pp d i s l,
      well_formed_log (log s)
      -> pre_prepare_in_log pp d (log (check_one_stable i s l)) = true
      -> pre_prepare_in_log pp d (log s) = true.
  Proof.
    induction l; introv wf prep; simpl in *; smash_pbft.
    rename_hyp_with check_stable check.
    eapply check_stable_preserves_pre_prepare_in_log; eauto.
  Qed.
  Hint Resolve pre_prepare_in_log_check_one_stable : pbft.

End PBFTpre_prepare_in_log_preserves.


Hint Resolve check_send_replies_preserves_pre_prepare_in_log : pbft.
Hint Resolve pre_prepare_in_log_log_pre_prepares_false : pbft.
Hint Resolve log_checkpoint_cert_from_new_view_preserves_pre_prepare_in_log : pbft.
Hint Resolve update_state_new_view_preserves_pre_prepare_in_log : pbft.
Hint Resolve pre_prepare_in_log_add_new_pre_prepare2log_false_implies : pbft.
Hint Resolve pre_prepare_in_log_check_one_stable : pbft.
Hint Resolve find_and_execute_requests_preserves_pre_prepare_in_log : pbft.
(*Hint Rewrite @log_update_low_water_mark : pbft.*)
