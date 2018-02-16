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
Require Export PBFTtactics3.


Section PBFTordering.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma check_new_request_sequence_number_increases :
    forall i l st r st' o,
      check_new_request i l st r = (st', o)
      -> sequence_number st <= sequence_number st'.
  Proof.
    introv check.
    unfold check_new_request in check; smash_pbft.
  Qed.
  Hint Resolve check_new_request_sequence_number_increases : pbft.

  Lemma check_send_replies_sequence_number_increases :
    forall i v keys gi st n msgs st',
      check_send_replies i v keys gi st n = (msgs, st')
      -> sequence_number (primary_state st) <= sequence_number (primary_state st').
  Proof.
    introv check.
    unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_sequence_number_increases : pbft.

  Lemma check_send_replies_update_log_sequence_number_increases :
    forall i v keys gi st L n msgs st',
      check_send_replies i v keys gi (update_log st L) n = (msgs, st')
      -> sequence_number (primary_state st) <= sequence_number (primary_state st').
  Proof.
    introv check.
    unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_update_log_sequence_number_increases : pbft.

  Lemma check_stable_sequence_number_increases :
        forall slf cp_entry st st',
        check_stable slf st cp_entry = Some st'
        -> sequence_number (primary_state st) <= sequence_number (primary_state st').
  Proof.
    introv check.
    unfold check_stable in check; smash_pbft.
  Qed.
  Hint Resolve check_stable_sequence_number_increases : pbft.

  Lemma check_stable_update_checkpoint_state_sequence_number_increases :
        forall slf cp_state cp_entry st st',
        check_stable slf (update_checkpoint_state st cp_state) cp_entry = Some st'
        -> sequence_number (primary_state st) <= sequence_number (primary_state st').
  Proof.
    introv check.
    unfold check_stable in check; smash_pbft.
  Qed.
  Hint Resolve check_stable_update_checkpoint_state_sequence_number_increases : pbft.

  Lemma find_and_execute_requests_sequence_number_increases :
    forall v keys slf msg st st',
      find_and_execute_requests slf v keys st = (msg, st')
      -> sequence_number (primary_state st) <= sequence_number (primary_state st').
  Proof.
    introv find.
    unfold find_and_execute_requests in find; smash_pbft.
    unfold execute_requests in *.
    remember (ready st) as xx.
    destruct xx;  symmetry in Heqxx; inversion Heqx; tcsp;
      unfold check_broadcast_checkpoint in *; smash_pbft.
  Qed.
  Hint Resolve find_and_execute_requests_sequence_number_increases : pbft.

 Lemma find_and_execute_requests_decrement_requests_in_progress_sequence_number_increases :
    forall v keys slf msg st st',
      find_and_execute_requests slf v keys st = (msg, st')
      -> sequence_number (primary_state st)
         <=
         sequence_number (primary_state (decrement_requests_in_progress_if_primary slf v st')).
  Proof.
    introv find.
    unfold decrement_requests_in_progress_if_primary in *.
    unfold find_and_execute_requests in find; smash_pbft;
      unfold execute_requests in *;
      remember (ready st) as xx;
      destruct xx;  symmetry in Heqxx; inversion Heqx; tcsp; smash_pbft;
        unfold check_broadcast_checkpoint in *; smash_pbft.
  Qed.
  Hint Resolve find_and_execute_requests_decrement_requests_in_progress_sequence_number_increases : pbft.

  Lemma update_state_new_view_sequence_number_increases:
    forall slf v msg st st',
      update_state_new_view slf st v = (st', msg)
      ->  sequence_number (primary_state st) <= sequence_number (primary_state st').
  Proof.
    introv up_state.
    unfold update_state_new_view in *; smash_pbft.
    unfold update_checkpoint_from_new_view.
    unfold log_checkpoint_cert_from_new_view in *; smash_pbft.
  Qed.
  Hint Resolve update_state_new_view_sequence_number_increases : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_sequence_number_increases :
    forall slf ppd msg st st',
      add_prepare_to_log_from_new_view_pre_prepare slf st ppd = (st', msg)
      -> sequence_number (primary_state st) <= sequence_number (primary_state st').
  Proof.
    introv add_pp.
    unfold add_prepare_to_log_from_new_view_pre_prepare in *. smash_pbft.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_sequence_number_increases : pbft.

  Hint Resolve Nat.le_trans : pbft num.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_sequence_number_increases :
    forall slf L st st' msg,
      add_prepares_to_log_from_new_view_pre_prepares slf st L = (st', msg)
      -> sequence_number (primary_state st) <= sequence_number (primary_state st').
  Proof.
    induction L; introv add_pp; simpl in *; smash_pbft.
    match goal with
    | [ H : add_prepares_to_log_from_new_view_pre_prepares _ _ _ = _ |- _ ] =>
      apply IHL in H
    end.
    eauto 3 with pbft.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_sequence_number_increases : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_xxx_sequence_number_increases :
    forall i st v K nv L st' msgs,
      add_prepares_to_log_from_new_view_pre_prepares
        i
        (log_new_view_state (log_pre_prepares_of_new_view (update_view st v) K) nv)
        L =  (st', msgs)
      -> sequence_number (primary_state st) <= sequence_number (primary_state st').
  Proof.
    introv h; apply add_prepares_to_log_from_new_view_pre_prepares_sequence_number_increases in h.
    simpl in *; auto.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_xxx_sequence_number_increases : pbft.

  Lemma check_stable_preserves_primary_state :
    forall i e s s',
      check_stable i s e = Some s'
      -> primary_state s' = primary_state s.
  Proof.
    introv check; unfold check_stable in check; smash_pbft.
  Qed.

  Lemma sequence_number_primary_state_check_one_stable :
    forall i s l,
      sequence_number (primary_state (check_one_stable i s l))
      = sequence_number (primary_state s).
  Proof.
    induction l; introv; simpl; tcsp; smash_pbft.
    erewrite check_stable_preserves_primary_state;[|eauto]; auto.
  Qed.
  Hint Rewrite sequence_number_primary_state_check_one_stable : pbft.

  Lemma update_state_new_view_sequence_number_increases2 :
    forall slf v msg st st' n,
      update_state_new_view slf st v = (st', msg)
      -> n <= sequence_number (primary_state st)
      -> n <= sequence_number (primary_state st').
  Proof.
    introv upd h.
    eapply le_trans;[eauto|]; eauto 2 with pbft.
  Qed.
  Hint Resolve update_state_new_view_sequence_number_increases2 : pbft.

  Lemma le_sequence_number_update_view :
    forall n s v,
      n <= sequence_number (primary_state s)
      -> n <= sequence_number (primary_state (update_view s v)).
  Proof.
    tcsp.
  Qed.
  Hint Resolve le_sequence_number_update_view : pbft.

  Lemma le_sequence_number_change_sequence_number :
    forall n m s,
      n <= max_seq_num (sequence_number (primary_state s)) m
      -> n <= sequence_number (primary_state (change_sequence_number s m)).
  Proof.
    tcsp.
  Qed.
  Hint Resolve le_sequence_number_change_sequence_number : pbft.

  Lemma le_sequence_number_change_sequence_number_log_pre_prepares_of_new_view :
    forall n m s p,
      n <= sequence_number (primary_state (change_sequence_number s m))
      -> n <= sequence_number (primary_state (change_sequence_number (log_pre_prepares_of_new_view s p) m)).
  Proof.
    tcsp.
  Qed.
  Hint Resolve le_sequence_number_change_sequence_number_log_pre_prepares_of_new_view : pbft.

  Lemma le_sequence_number_change_sequence_number_log_new_view_and_entry :
    forall n m s nv e,
      n <= sequence_number (primary_state (change_sequence_number s m))
      -> n <= sequence_number (primary_state (change_sequence_number (log_new_view_and_entry_state s nv e) m)).
  Proof.
    tcsp.
  Qed.
  Hint Resolve le_sequence_number_change_sequence_number_log_new_view_and_entry : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_sequence_number_increases2 :
    forall slf L st st' msg n,
      add_prepares_to_log_from_new_view_pre_prepares slf st L = (st', msg)
      -> n <= sequence_number (primary_state st)
      -> n <= sequence_number (primary_state st').
  Proof.
    introv h q; eapply le_trans; eauto 3 with pbft.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_sequence_number_increases2 : pbft.

  Lemma le_sequence_number_log_new_view_state :
    forall n s nv,
      n <= sequence_number (primary_state s)
      -> n <= sequence_number (primary_state (log_new_view_state s nv)).
  Proof.
    tcsp.
  Qed.
  Hint Resolve le_sequence_number_log_new_view_state : pbft.

  Lemma PBFTsequence_number_increases_local_pred :
    forall (eo : EventOrdering) (e : Event) slf st1 st2,
      state_sm_before_event (PBFTreplicaSM slf) e = Some st1
      -> state_sm_on_event (PBFTreplicaSM slf) e = Some st2
      -> sequence_number (primary_state st1) <= sequence_number (primary_state st2).
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers4 smash_pbft_ind3.
  Qed.

  Lemma PBFTseq_number_increases :
    forall (eo : EventOrdering) (e1 e2 : Event) slf st1 st2,
      e1 ⊑ e2
      -> state_sm_before_event (PBFTreplicaSM slf) e1 = Some st1
      -> state_sm_before_event (PBFTreplicaSM slf) e2 = Some st2
      -> sequence_number (primary_state st1) <= sequence_number (primary_state st2).
  Proof.
    introv.
    revert st2.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv h1 h2 h3.

    apply localHappenedBeforeLe_implies_or2 in h1; repndors; subst; tcsp;[|].

    {
      match goal with
      | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; ginv
      end.
    }

    apply local_implies_pred_or_local in h1; repndors; exrepnd.

    {
      eapply state_sm_on_event_if_before_event_direct_pred in h1;[|eauto].
      eapply PBFTsequence_number_increases_local_pred in h1;[|eauto]; auto.
    }

    pose proof (ind e) as q; autodimp q hyp; clear ind.

    pose proof (state_sm_before_event_some_between e e2 (PBFTreplicaSM slf) st2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    pose proof (q s') as h; clear q; repeat (autodimp h hyp); eauto 4 with eo.

    eapply state_sm_on_event_if_before_event_direct_pred in h1;[|eauto].
    eapply PBFTsequence_number_increases_local_pred in h1;[|eauto]; auto.
    omega.
  Qed.

  Lemma PBFTseq_number_increases_on_event :
    forall (eo : EventOrdering) (e1 e2 : Event) slf st1 st2,
      e1 ⊑ e2
      -> state_sm_on_event (PBFTreplicaSM slf) e1 = Some st1
      -> state_sm_on_event (PBFTreplicaSM slf) e2 = Some st2
      -> sequence_number (primary_state st1) <= sequence_number (primary_state st2).
  Proof.
    introv.
    revert st2.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv h1 h2 h3.

    apply localHappenedBeforeLe_implies_or2 in h1; repndors; subst; tcsp;[|].

    {
      match goal with
      | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; ginv
      end.
    }

    apply local_implies_pred_or_local in h1; repndors; exrepnd.

    {
      eapply state_sm_before_event_if_on_event_direct_pred in h1; [|eauto].
      eapply PBFTsequence_number_increases_local_pred in h1;[|eauto]; auto.
    }

    pose proof (ind e) as q. autodimp q hyp.

    pose proof (state_sm_on_event_some_between e e2 (PBFTreplicaSM slf) st2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    pose proof (q s') as h; clear q. repeat (autodimp h hyp); eauto 2 with eo.

    eapply state_sm_before_event_if_on_event_direct_pred in h1;[|eauto].
    eapply PBFTsequence_number_increases_local_pred in h1;[|eauto]; auto.
    omega.
  Qed.

  Lemma check_send_replies_preserves_low_water_mark :
    forall i v keys giop st1 sn msgs st2,
      check_send_replies i v keys giop st1 sn = (msgs, st2)
      -> low_water_mark st1 = low_water_mark st2.
  Proof.
    introv check.
    unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.

  Lemma check_send_replies_update_log_preserves_low_water_mark :
    forall i v keys giop st1 L sn msgs st2,
      check_send_replies i v keys giop (update_log st1 L) sn = (msgs, st2)
      -> low_water_mark st1 = low_water_mark st2.
  Proof.
    introv check.
    apply check_send_replies_preserves_low_water_mark in check; simpl in *.
    allrw; auto.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_low_water_mark : pbft.

  Lemma low_water_mark_update_log :
    forall st L,
      low_water_mark (update_log st L) = low_water_mark st.
  Proof.
    introv; destruct st; simpl; unfold update_log, low_water_mark; simpl; tcsp.
  Qed.
  Hint Rewrite low_water_mark_update_log : pbft.

  Lemma check_send_replies_update_log_preserves_low_water_mark_le :
    forall i v keys giop st1 L sn msgs st2,
      check_send_replies i v keys giop (update_log st1 L) sn = (msgs, st2)
      -> low_water_mark st1 <= low_water_mark st2.
  Proof.
    introv check.
    apply check_send_replies_preserves_low_water_mark in check; simpl in *.
    autorewrite with pbft in *; allrw; tcsp.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_low_water_mark_le : pbft.

  Lemma low_water_mark_trim_checkpoint :
    forall st n, low_water_mark (trim_checkpoint st n) = low_water_mark st.
  Proof.
    introv.
    destruct st; simpl; unfold trim_checkpoint, low_water_mark; simpl.
    destruct cp_state; simpl; auto.
  Qed.
  Hint Rewrite low_water_mark_trim_checkpoint : pbft.

  Lemma low_water_mark_update_log_checkpoint_stable :
    forall s e,
      low_water_mark (update_log_checkpoint_stable s e)
      = scp_sn e.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite low_water_mark_update_log_checkpoint_stable : pbft.

(*  Lemma check_state_preserves_low_water_mark :
    forall i st1 ce c st2,
      check_stable i st1 ce = Some st2
      -> low_water_mark st2 = cp_sn ce.
  Proof.
    introv check; unfold check_stable in check; destruct ce; ginv.
    smash_pbft.
    simpl.
  Qed.*)

  (*Lemma check_stable_update_checkpoint_state_preserves_low_water_mark :
    forall i st1 checkst ce c st2,
      check_stable i (update_checkpoint_state st1 checkst) ce c = Some st2
      -> low_water_mark st2 = checkpoint2seq c.
  Proof.
    introv check; apply check_state_preserves_low_water_mark in check; auto.
  Qed.*)

  Lemma check_between_water_marks_true :
    forall sn1 sn2,
      check_between_water_marks sn1 sn2 = true
      <-> (sn1 < sn2 /\ sn2 <= sn1 + PBFTwater_mark_range).
  Proof.
    introv; unfold check_between_water_marks; split; introv h; smash_pbft;
      allrw SeqNumLe_true; allrw SeqNumLt_true; tcsp.
  Qed.

  Lemma decrement_requests_in_progress_if_primary_preserves_low_water_mark :
    forall i v st,
      low_water_mark (decrement_requests_in_progress_if_primary i v st)
      = low_water_mark st.
  Proof.
    introv; unfold decrement_requests_in_progress_if_primary; smash_pbft.
  Qed.
  Hint Rewrite decrement_requests_in_progress_if_primary_preserves_low_water_mark : pbft.

  Lemma low_water_mark_update_checkpoint_state :
    forall s cs,
      low_water_mark (update_checkpoint_state s cs)
      = scp_sn (chk_state_stable cs).
  Proof.
    introv.
    destruct s; simpl.
    unfold update_checkpoint_state, low_water_mark; simpl; auto.
  Qed.
  Hint Rewrite low_water_mark_update_checkpoint_state : pbft.

  Lemma low_water_mark_of_add_new_checkpoint2cp_state :
    forall cpstate smstate lr c ceop cs,
      add_new_checkpoint2cp_state cpstate smstate lr c = (ceop, cs)
      -> scp_sn (chk_state_stable cs) = scp_sn (chk_state_stable cpstate).
  Proof.
    introv h; unfold add_new_checkpoint2cp_state in h; smash_pbft.
  Qed.

  Lemma check_broadcast_checkpoint_preserves_low_water_mark :
    forall i next v keys st1 st2 msgs,
      check_broadcast_checkpoint i next v keys st1 = (st2, msgs)
      -> low_water_mark st2 = low_water_mark st1.
  Proof.
    introv check; unfold check_broadcast_checkpoint in check; smash_pbft.
    match goal with
    | [ H : context[add_new_checkpoint2cp_state] |- _ ] => rename H into add
    end.
    apply low_water_mark_of_add_new_checkpoint2cp_state in add.
    tcsp.
  Qed.

  Lemma execute_requests_preserves_low_water_mark :
    forall i v keys st1 R msgs sns st2,
      execute_requests i v keys st1 R = (msgs, sns, st2)
      -> low_water_mark st1 = low_water_mark st2.
  Proof.
    introv e; unfold execute_requests in e; destruct R;
      try (complete (inversion e; subst; auto)).
    smash_pbft.
    match goal with
    | [ H : check_broadcast_checkpoint _ _ _ _ _ = _ |- _ ] =>
      apply check_broadcast_checkpoint_preserves_low_water_mark in H
    end.
    simpl in *; auto.
  Qed.
  Hint Resolve execute_requests_preserves_low_water_mark : pbft.

  Lemma low_water_mark_update_ready :
    forall s R, low_water_mark (update_ready s R) = low_water_mark s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite low_water_mark_update_ready : pbft.

  Lemma find_and_execute_requests_preserves_low_water_mark :
    forall i v keys st1 msgs st2,
      find_and_execute_requests i v keys st1 = (msgs, st2)
      -> low_water_mark st1 = low_water_mark st2.
  Proof.
    introv f; unfold find_and_execute_requests in f; smash_pbft.
  Qed.

  Lemma find_and_execute_requests_preserves_low_water_mark_le :
    forall i v keys st1 msgs st2,
      find_and_execute_requests i v keys st1 = (msgs, st2)
      -> low_water_mark st1 <= low_water_mark st2.
  Proof.
    introv f; apply find_and_execute_requests_preserves_low_water_mark in f; allrw; auto.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_low_water_mark_le : pbft.

  Lemma update_checkpoint_from_new_view_preserves_low_water_mark :
    forall st stable n,
      low_water_mark (update_checkpoint_from_new_view st stable n)
      = low_water_mark st.
  Proof.
    introv; unfold update_checkpoint_from_new_view; smash_pbft.
  Qed.
  Hint Rewrite update_checkpoint_from_new_view_preserves_low_water_mark : pbft.

(*  Lemma log_checkpoint_cert_from_new_view_preserves_low_water_mark :
    forall i st1 v sn cert stable st2 msgs,
      log_checkpoint_cert_from_new_view i st1 v sn cert stable = (st2, msgs)
      -> low_water_mark st2 = low_water_mark st1.
  Proof.
    introv h; unfold log_checkpoint_cert_from_new_view in h; smash_pbft.

    - simpl.
  Qed.
  Hint Resolve log_checkpoint_cert_from_new_view_preserves_low_water_mark : pbft.*)

  Lemma trim_checkpoint_preserves_low_water_mark :
    forall st sn,
      low_water_mark (trim_checkpoint st sn)
      = low_water_mark st.
  Proof.
    introv; destruct st; simpl.
    unfold low_water_mark, trim_checkpoint; simpl.
    destruct cp_state; simpl; auto.
  Qed.
  Hint Rewrite trim_checkpoint_preserves_low_water_mark : pbft.

(*  Lemma update_state_new_view_preserves_low_water_mark :
    forall i st1 nv st2 msgs,
      update_state_new_view i st1 nv = (st2, msgs)
      -> low_water_mark st2 = fst (view_change_cert2max_seq_vc (new_view2cert nv)).
  Proof.
    introv upd; unfold update_state_new_view in upd; smash_pbft.
    simpl.
    match goal with
    | [ H : context[log_checkpoint_cert_from_new_view] |- _ ] => rename H into h
    end.
    apply log_checkpoint_cert_from_new_view_preserves_low_water_mark in h.

    Print seq_num_of_last_stable_checkpoint.

  Qed.*)

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_low_water_mark :
    forall i st1 p st2 msgs,
      add_prepare_to_log_from_new_view_pre_prepare i st1 p = (st2, msgs)
      -> low_water_mark st1 = low_water_mark st2.
  Proof.
    introv h; unfold add_prepare_to_log_from_new_view_pre_prepare in h; smash_pbft.
  Qed.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_low_water_mark :
    forall i P st1 st2 msgs,
      add_prepares_to_log_from_new_view_pre_prepares i st1 P = (st2, msgs)
      -> low_water_mark st1 = low_water_mark st2.
  Proof.
    induction P; introv h; simpl in *; smash_pbft.
    match goal with
    | [ H : add_prepares_to_log_from_new_view_pre_prepares _ _ _ = _ |- _ ] =>
      apply IHP in H
    end.
    match goal with
    | [ H : add_prepare_to_log_from_new_view_pre_prepare _ _ _ = _ |- _ ] =>
      apply add_prepare_to_log_from_new_view_pre_prepare_preserves_low_water_mark in H
    end.
    allrw; auto.
  Qed.

  Lemma cp_sn_of_add_new_checkpoint2cp_log :
    forall L smstate lr c ce K,
      add_new_checkpoint2cp_log L smstate lr c = (Some ce, K)
      -> cp_sn ce = checkpoint2seq c.
  Proof.
    induction L; introv h; simpl in *; smash_pbft.
    destruct a; simpl in *; smash_pbft.
    unfold is_checkpoint_for_entry in *; simpl in *.
    unfold similar_sn_and_checkpoint_sn in *; smash_pbft.
  Qed.

  Lemma cp_sn_of_add_new_checkpoint2cp_state :
    forall cpstate smstate lr c ce cs,
      add_new_checkpoint2cp_state cpstate smstate lr c = (Some ce, cs)
      -> cp_sn ce = checkpoint2seq c.
  Proof.
    introv h; unfold add_new_checkpoint2cp_state in h; smash_pbft.
    eapply cp_sn_of_add_new_checkpoint2cp_log; eauto.
  Qed.

  Lemma low_water_mark_log_new_view_state :
    forall s nv,
      low_water_mark (log_new_view_state s nv) = low_water_mark s.
  Proof.
    introv; destruct s; simpl; tcsp.
  Qed.
  Hint Rewrite low_water_mark_log_new_view_state : pbft.

  Lemma low_water_mark_log_pre_prepares_of_new_view :
    forall s P,
      low_water_mark (log_pre_prepares_of_new_view s P)
      = low_water_mark s.
  Proof.
    introv; destruct s; simpl; tcsp.
  Qed.
  Hint Rewrite low_water_mark_log_pre_prepares_of_new_view : pbft.

  Lemma low_water_mark_update_view :
    forall s v,
      low_water_mark (update_view s v)
      = low_water_mark s.
  Proof.
    introv; destruct s; simpl; tcsp.
  Qed.
  Hint Rewrite low_water_mark_update_view : pbft.

  Lemma sn_of_view_change_cert2max_seq_vc :
    forall C n vc,
      view_change_cert2max_seq_vc C = Some (n, vc)
      -> n = view_change2seq vc.
  Proof.
    induction C; introv h; simpl in *; ginv.
    smash_pbft.
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

  Lemma extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq :
    forall vc n d view,
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

  Lemma low_water_mark_change_sequence_number :
    forall s n,
      low_water_mark (change_sequence_number s n) = low_water_mark s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite low_water_mark_change_sequence_number : pbft.

  Lemma checkpoint_entry2stable_implies_same_sn :
    forall e se,
      checkpoint_entry2stable e = Some se
      -> cp_sn e = scp_sn se.
  Proof.
    introv h; destruct e; simpl in *; tcsp; smash_pbft.
  Qed.
  Hint Resolve checkpoint_entry2stable_implies_same_sn : pbft.

  Lemma checkpoint_entry2stable_implies_same_sn2 :
    forall e se,
      checkpoint_entry2stable e = Some se
      -> scp_sn se = cp_sn e.
  Proof.
    introv h; destruct e; simpl in *; tcsp; smash_pbft.
  Qed.
  Hint Resolve checkpoint_entry2stable_implies_same_sn2 : pbft.

  Lemma add_new_checkpoint2cp_state_preserves_sn_stable :
    forall s1 sm lastr c eop s2,
      add_new_checkpoint2cp_state s1 sm lastr c = (eop, s2)
      -> scp_sn (chk_state_stable s2) = scp_sn (chk_state_stable s1).
  Proof.
    introv add.
    unfold add_new_checkpoint2cp_state in add; smash_pbft.
  Qed.

  Lemma low_water_mark_of_check_stable :
    forall i s e s',
      check_stable i s e = Some s'
      -> low_water_mark s' = cp_sn e.
  Proof.
    introv check; unfold check_stable in check; smash_pbft.
  Qed.
  Hint Resolve low_water_mark_of_check_stable : pbft.

  Lemma low_water_mark_check_one_stable :
    forall i s l,
      low_water_mark s
      <= low_water_mark (check_one_stable i s l).
  Proof.
    induction l; introv; simpl in *; smash_pbft.
    erewrite (low_water_mark_of_check_stable _ _ _ x);[|eauto]; omega.
  Qed.
  Hint Resolve low_water_mark_check_one_stable : pbft.

  Lemma add_new_checkpoint2cp_state_preserves_sn_stable2 :
    forall s1 sm lastr c eop s2 n,
      add_new_checkpoint2cp_state s1 sm lastr c = (eop, s2)
      -> n <= scp_sn (chk_state_stable s1)
      -> n <= scp_sn (chk_state_stable s2).
  Proof.
    introv h q; eapply le_trans;[eauto|].
    apply add_new_checkpoint2cp_state_preserves_sn_stable in h; allrw; auto.
  Qed.
  Hint Resolve add_new_checkpoint2cp_state_preserves_sn_stable2 : pbft.

  Lemma view_change_cert2max_seq_vc_implies_in :
    forall c n vc,
      view_change_cert2max_seq_vc c = Some (n, vc) -> In vc c.
  Proof.
    induction c; introv h; smash_pbft.
  Qed.
  Hint Resolve view_change_cert2max_seq_vc_implies_in : pbft.

  Lemma update_state_new_view_implies_le_low_water_mark :
    forall i s1 nv s2 msgs n,
      correct_new_view nv = true
      -> update_state_new_view i s1 nv = (s2, msgs)
      -> n <= low_water_mark s1
      -> n <= low_water_mark s2.
  Proof.
    introv cor upd h.
    unfold update_state_new_view in upd; smash_pbft.
    unfold log_checkpoint_cert_from_new_view in *; smash_pbft; simpl in *.

    - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup sn_of_view_change_cert2max_seq_vc in mseq; subst.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft.
      subst; omega.

    - rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup sn_of_view_change_cert2max_seq_vc in mseq; subst.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft.
      subst; omega.
  Qed.
  Hint Resolve update_state_new_view_implies_le_low_water_mark : pbft.

  Lemma implies_le_low_water_mark_log_new_view_state :
    forall s nv n,
      n <= low_water_mark s
      -> n <= low_water_mark (log_new_view_state s nv).
  Proof.
    tcsp.
  Qed.
  Hint Resolve implies_le_low_water_mark_log_new_view_state : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_implies_le_low_water_mark :
    forall i P s1 s2 msgs n,
      add_prepares_to_log_from_new_view_pre_prepares i s1 P = (s2, msgs)
      -> n <= low_water_mark s1
      -> n <= low_water_mark s2.
  Proof.
    introv h q.
    apply add_prepares_to_log_from_new_view_pre_prepares_preserves_low_water_mark in h; allrw; auto.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_implies_le_low_water_mark : pbft.


  Lemma PBFTlow_water_mark_increases_local_pred :
    forall (eo : EventOrdering) (e : Event) slf st1 st2,
      state_sm_before_event (PBFTreplicaSM slf) e = Some st1
      -> state_sm_on_event (PBFTreplicaSM slf) e = Some st2
      -> low_water_mark st1 <= low_water_mark st2.
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers4 smash_pbft_ind3.
  Qed.

  Lemma PBFTlow_water_mark_increases_before_event :
    forall (eo : EventOrdering) (e1 e2 : Event) slf st1 st2,
      e1 ⊑ e2
      -> state_sm_before_event (PBFTreplicaSM slf) e1 = Some st1
      -> state_sm_before_event (PBFTreplicaSM slf) e2 = Some st2
      -> low_water_mark st1 <= low_water_mark st2.
  Proof.
    introv.
    revert st2.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv h1 h2 h3.

    apply localHappenedBeforeLe_implies_or2 in h1; repndors; subst; tcsp;[|].

    {
      match goal with
      | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; ginv
      end.
    }

    apply local_implies_pred_or_local in h1; repndors; exrepnd.

    {
      eapply state_sm_on_event_if_before_event_direct_pred in h1;[|eauto].
      eapply PBFTlow_water_mark_increases_local_pred in h1;[|eauto]; auto.
    }

    pose proof (ind e) as q; autodimp q hyp; clear ind.

    pose proof (state_sm_before_event_some_between e e2 (PBFTreplicaSM slf) st2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    pose proof (q s') as h; clear q; repeat (autodimp h hyp); eauto 2 with eo.

    eapply state_sm_on_event_if_before_event_direct_pred in h1;[|eauto].
    eapply PBFTlow_water_mark_increases_local_pred in h1;[|eauto]; auto.
    omega.
  Qed.

  Lemma PBFTlow_water_mark_increases_on_event :
    forall (eo : EventOrdering) (e1 e2 : Event) slf st1 st2,
      e1 ⊑ e2
      -> state_sm_on_event (PBFTreplicaSM slf) e1 = Some st1
      -> state_sm_on_event (PBFTreplicaSM slf) e2 = Some st2
      -> low_water_mark st1 <= low_water_mark st2.
  Proof.
    introv.
    revert st2.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv h1 h2 h3.

    apply localHappenedBeforeLe_implies_or2 in h1; repndors; subst; tcsp;[|].

    {
      match goal with
      | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; ginv
      end.
    }

    apply local_implies_pred_or_local in h1; repndors; exrepnd.

    {
      eapply state_sm_before_event_if_on_event_direct_pred in h1; [|eauto].
      eapply PBFTlow_water_mark_increases_local_pred in h1;[|eauto]; auto.
    }

    pose proof (ind e) as q. autodimp q hyp.

    pose proof (state_sm_on_event_some_between e e2 (PBFTreplicaSM slf) st2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    pose proof (q s') as h; clear q. repeat (autodimp h hyp); eauto 2 with eo.

    eapply state_sm_before_event_if_on_event_direct_pred in h1;[|eauto].
    eapply PBFTlow_water_mark_increases_local_pred in h1;[|eauto]; auto.
    omega.
  Qed.

  Lemma check_send_replies_preserves_current_view :
    forall i v keys giop st1 s msgs st2,
      check_send_replies i v keys giop st1 s = (msgs, st2)
      -> current_view st2 = current_view st1.
  Proof.
    introv check; unfold check_send_replies in check.
    destruct giop; smash_pbft.
    destruct g; smash_pbft.
  Qed.

  Lemma check_send_replies_update_log_preserves_current_view_le :
    forall i v keys giop st1 L s msgs st2,
      check_send_replies i v keys giop (update_log st1 L) s = (msgs, st2)
      -> current_view st1 <= current_view st2.
  Proof.
    introv check; apply check_send_replies_preserves_current_view in check; simpl in *; allrw; auto.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_current_view_le : pbft.

  Lemma check_send_replies_update_log_preserves_current_view :
    forall i v keys giop st1 L s msgs st2,
      check_send_replies i v keys giop (update_log st1 L) s = (msgs, st2)
      -> current_view st2 = current_view st1.
  Proof.
    introv check; apply check_send_replies_preserves_current_view in check; simpl in *; allrw; auto.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_current_view : pbft.

  Lemma check_stable_preserves_current_view :
    forall i st1 cs st2,
      check_stable i st1 cs = Some st2
      -> current_view st2 = current_view st1.
  Proof.
    introv check; unfold check_stable in check.
    destruct cs; ginv; smash_pbft.
  Qed.
  Hint Resolve check_stable_preserves_current_view : pbft.

  Lemma check_stable_update_checkpoint_state_preserves_current_view_le :
    forall i st1 cs cs' st2,
      check_stable i (update_checkpoint_state st1 cs') cs = Some st2
      -> current_view st1 <= current_view st2.
  Proof.
    introv check; apply check_stable_preserves_current_view in check.
    simpl in *; allrw; auto.
  Qed.
  Hint Resolve check_stable_update_checkpoint_state_preserves_current_view_le : pbft.

  Lemma decrement_requests_in_progress_if_primary_preserves_current_view :
    forall i v st,
      current_view (decrement_requests_in_progress_if_primary i v st)
      = current_view st.
  Proof.
    introv; unfold decrement_requests_in_progress_if_primary; smash_pbft.
  Qed.
  Hint Rewrite decrement_requests_in_progress_if_primary_preserves_current_view : pbft.

  Lemma check_broadcast_checkpoint_preserves_current_view :
    forall i n v keys st1 st2 msgs,
      check_broadcast_checkpoint i n v keys st1 = (st2, msgs)
      -> current_view st2 = current_view st1.
  Proof.
    introv h.
    unfold check_broadcast_checkpoint in h; smash_pbft.
  Qed.

  Lemma execute_requests_preserves_current_view :
    forall i v keys st1 L msgs K st2,
      execute_requests i v keys st1 L = (msgs, K, st2)
      -> current_view st2 = current_view st1.
  Proof.
    introv exec; unfold execute_requests in exec.
    destruct L; smash_pbft.
    match goal with
    | [ H : check_broadcast_checkpoint _ _ _ _ _ = _ |- _ ] =>
      apply check_broadcast_checkpoint_preserves_current_view in H
    end; simpl in *; auto.
  Qed.
  Hint Resolve execute_requests_preserves_current_view : pbft.

  Lemma find_and_execute_requests_preserves_current_view :
    forall i v keys st1 msgs st2,
      find_and_execute_requests i v keys st1 = (msgs, st2)
      -> current_view st2 = current_view st1.
  Proof.
    introv h; unfold find_and_execute_requests in h; smash_pbft.
  Qed.

  Lemma find_and_execute_requests_preserves_current_view_le :
    forall i v keys st1 msgs st2,
      find_and_execute_requests i v keys st1 = (msgs, st2)
      -> current_view st1 <= current_view st2.
  Proof.
    introv h; apply find_and_execute_requests_preserves_current_view in h; allrw; auto.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_current_view_le : pbft.

  Lemma update_checkpoint_from_new_view_preserves_current_view :
    forall st stable n,
      current_view (update_checkpoint_from_new_view st stable n)
      = current_view st.
  Proof.
    introv; unfold update_checkpoint_from_new_view; smash_pbft.
  Qed.
  Hint Rewrite update_checkpoint_from_new_view_preserves_current_view : pbft.

  Lemma log_checkpoint_cert_from_new_view_preserves_current_view :
    forall i st1 v sn cert stable st2 msgs,
      log_checkpoint_cert_from_new_view i st1 v sn cert stable = (st2, msgs)
      -> current_view st2 = current_view st1.
  Proof.
    introv h; unfold log_checkpoint_cert_from_new_view in h; smash_pbft.
  Qed.
  Hint Resolve log_checkpoint_cert_from_new_view_preserves_current_view : pbft.

  Lemma trim_checkpoint_preserves_current_view :
    forall st sn,
      current_view (trim_checkpoint st sn)
      = current_view st.
  Proof.
    sp.
  Qed.
  Hint Rewrite trim_checkpoint_preserves_current_view : pbft.

  Lemma update_state_new_view_preserves_current_view :
    forall i st1 nv st2 msgs,
      update_state_new_view i st1 nv = (st2, msgs)
      -> current_view st2 = current_view st1.
  Proof.
    introv upd; unfold update_state_new_view in upd; smash_pbft.
    rename_hyp_with log_checkpoint_cert_from_new_view chk.
    apply log_checkpoint_cert_from_new_view_preserves_current_view in chk; auto.
  Qed.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_current_view :
    forall i st1 p st2 msgs,
      add_prepare_to_log_from_new_view_pre_prepare i st1 p = (st2, msgs)
      -> current_view st2 = current_view st1.
  Proof.
    introv h; unfold add_prepare_to_log_from_new_view_pre_prepare in h; smash_pbft.
  Qed.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_current_view :
    forall i P st1 st2 msgs,
      add_prepares_to_log_from_new_view_pre_prepares i st1 P = (st2, msgs)
      -> current_view st2 = current_view st1.
  Proof.
    induction P; introv h; simpl in *; smash_pbft.
    match goal with
    | [ H : add_prepares_to_log_from_new_view_pre_prepares _ _ _ = _ |- _ ] =>
      apply IHP in H
    end.
    match goal with
    | [ H : add_prepare_to_log_from_new_view_pre_prepare _ _ _ = _ |- _ ] =>
      apply add_prepare_to_log_from_new_view_pre_prepare_preserves_current_view in H
    end.
    allrw; auto.
  Qed.

  Lemma current_view_check_one_stable :
    forall i s l,
      current_view (check_one_stable i s l) = current_view s.
  Proof.
    induction l; introv; simpl; smash_pbft.
  Qed.
  Hint Rewrite current_view_check_one_stable : pbft.

  Lemma update_state_new_view_preserves_le_current_view :
    forall i st1 nv st2 msgs n,
      update_state_new_view i st1 nv = (st2, msgs)
      -> n <= current_view st1
      -> n <= current_view st2.
  Proof.
    introv h q.
    apply update_state_new_view_preserves_current_view in h; allrw; auto.
  Qed.
  Hint Resolve update_state_new_view_preserves_le_current_view : pbft.

  Lemma le_current_view_update_view :
    forall n s (v : View),
      n <= max_view (current_view s) v
      -> n <= current_view (update_view s v).
  Proof.
    tcsp.
  Qed.
  Hint Resolve le_current_view_update_view : pbft.

  Lemma le_current_view_update_view_change_sequence_number :
    forall n s sn v,
      n <= current_view (update_view s v)
      -> n <= current_view (update_view (change_sequence_number s sn) v).
  Proof.
    tcsp.
  Qed.
  Hint Resolve le_current_view_update_view_change_sequence_number : pbft.

  Lemma le_current_view_update_view_log_pre_prepares_of_new_view :
    forall n s P v,
      n <= current_view (update_view s v)
      -> n <= current_view (update_view (log_pre_prepares_of_new_view s P) v).
  Proof.
    tcsp.
  Qed.
  Hint Resolve le_current_view_update_view_log_pre_prepares_of_new_view : pbft.

  Lemma le_current_view_update_view_log_new_view_and_entry_state :
    forall n s nv e v,
      n <= current_view (update_view s v)
      -> n <= current_view (update_view (log_new_view_and_entry_state s nv e) v).
  Proof.
    tcsp.
  Qed.
  Hint Resolve le_current_view_update_view_log_new_view_and_entry_state : pbft.

  Lemma le_current_view_log_new_view_state :
    forall n s nv,
      n <= current_view s
      -> n <= current_view (log_new_view_state s nv).
  Proof.
    tcsp.
  Qed.
  Hint Resolve le_current_view_log_new_view_state : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_le_current_view :
    forall i P s1 s2 msgs n,
      add_prepares_to_log_from_new_view_pre_prepares i s1 P = (s2, msgs)
      -> n <= current_view s1
      -> n <= current_view s2.
  Proof.
    introv h q.
    apply add_prepares_to_log_from_new_view_pre_prepares_preserves_current_view in h; allrw; auto.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_le_current_view : pbft.


  Lemma PBFTcurrent_view_increases_local_pred :
    forall (eo : EventOrdering) (e : Event) slf st1 st2,
      state_sm_before_event (PBFTreplicaSM slf) e = Some st1
      -> state_sm_on_event (PBFTreplicaSM slf) e = Some st2
      -> current_view st1 <= current_view st2.
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers5 smash_pbft_ind3.
  Qed.

  Lemma PBFTcurrent_view_increases_before_event :
    forall (eo : EventOrdering) (e1 e2 : Event) slf st1 st2,
      e1 ⊑ e2
      -> state_sm_before_event (PBFTreplicaSM slf) e1 = Some st1
      -> state_sm_before_event (PBFTreplicaSM slf) e2 = Some st2
      -> current_view st1 <= current_view st2.
  Proof.
    introv.
    revert st2.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv h1 h2 h3.

    apply localHappenedBeforeLe_implies_or2 in h1; repndors; subst; tcsp;[|].

    {
      match goal with
      | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; ginv
      end.
    }

    apply local_implies_pred_or_local in h1; repndors; exrepnd.

    {
      eapply state_sm_on_event_if_before_event_direct_pred in h1;[|eauto].
      eapply PBFTcurrent_view_increases_local_pred in h1;[|eauto]; auto.
    }

    pose proof (ind e) as q; autodimp q hyp; clear ind.

    pose proof (state_sm_before_event_some_between e e2 (PBFTreplicaSM slf) st2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    pose proof (q s') as h; clear q; repeat (autodimp h hyp); eauto 2 with eo.

    eapply state_sm_on_event_if_before_event_direct_pred in h1;[|eauto].
    eapply PBFTcurrent_view_increases_local_pred in h1;[|eauto]; auto.
    omega.
  Qed.

  Lemma PBFTcurrent_view_increases_on_event :
    forall (eo : EventOrdering) (e1 e2 : Event) slf st1 st2,
      e1 ⊑ e2
      -> state_sm_on_event (PBFTreplicaSM slf) e1 = Some st1
      -> state_sm_on_event (PBFTreplicaSM slf) e2 = Some st2
      -> current_view st1 <= current_view st2.
  Proof.
    introv.
    revert st2.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv h1 h2 h3.

    apply localHappenedBeforeLe_implies_or2 in h1; repndors; subst; tcsp;[|].

    {
      match goal with
      | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; ginv
      end.
    }

    apply local_implies_pred_or_local in h1; repndors; exrepnd.

    {
      eapply state_sm_before_event_if_on_event_direct_pred in h1; [|eauto].
      eapply PBFTcurrent_view_increases_local_pred in h1;[|eauto]; auto.
    }

    pose proof (ind e) as q. autodimp q hyp.

    pose proof (state_sm_on_event_some_between e e2 (PBFTreplicaSM slf) st2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    pose proof (q s') as h; clear q. repeat (autodimp h hyp); eauto 2 with eo.

    eapply state_sm_before_event_if_on_event_direct_pred in h1;[|eauto].
    eapply PBFTcurrent_view_increases_local_pred in h1;[|eauto]; auto.
    omega.
  Qed.

  Lemma less_max_view:
    forall (a b : View),
      a <= b
      ->  max_view a b = b.
  Proof.
    introv h.
    unfold max_view. smash_pbft.
    allrw ViewLe_false. try omega.
  Qed.
(*  Hint Rewrite less_max_view : pbft.*)

End PBFTordering.


Hint Resolve check_new_request_sequence_number_increases : pbft.
Hint Resolve check_send_replies_sequence_number_increases : pbft.
Hint Resolve check_send_replies_update_log_sequence_number_increases : pbft.
Hint Resolve check_stable_sequence_number_increases : pbft.
Hint Resolve check_stable_update_checkpoint_state_sequence_number_increases : pbft.
Hint Resolve find_and_execute_requests_sequence_number_increases : pbft.
Hint Resolve find_and_execute_requests_decrement_requests_in_progress_sequence_number_increases : pbft.
Hint Resolve update_state_new_view_sequence_number_increases : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_sequence_number_increases : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_sequence_number_increases : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_xxx_sequence_number_increases : pbft.
Hint Resolve check_send_replies_update_log_preserves_low_water_mark : pbft.
Hint Resolve check_send_replies_update_log_preserves_low_water_mark_le : pbft.
Hint Resolve execute_requests_preserves_low_water_mark : pbft.
Hint Resolve find_and_execute_requests_preserves_low_water_mark_le : pbft.
Hint Resolve check_send_replies_update_log_preserves_current_view_le : pbft.
Hint Resolve check_send_replies_update_log_preserves_current_view : pbft.
Hint Resolve check_stable_update_checkpoint_state_preserves_current_view_le : pbft.
Hint Resolve execute_requests_preserves_current_view : pbft.
Hint Resolve find_and_execute_requests_preserves_current_view_le : pbft.
Hint Resolve log_checkpoint_cert_from_new_view_preserves_current_view : pbft.
Hint Resolve checkpoint_entry2stable_implies_same_sn : pbft.
Hint Resolve checkpoint_entry2stable_implies_same_sn2 : pbft.
Hint Resolve low_water_mark_of_check_stable : pbft.
Hint Resolve low_water_mark_check_one_stable : pbft.
Hint Resolve check_stable_preserves_current_view : pbft.


Hint Rewrite @low_water_mark_update_log : pbft.
Hint Rewrite @low_water_mark_trim_checkpoint : pbft.
Hint Rewrite @low_water_mark_update_log_checkpoint_stable : pbft.
Hint Rewrite @decrement_requests_in_progress_if_primary_preserves_low_water_mark : pbft.
Hint Rewrite @low_water_mark_update_checkpoint_state : pbft.
Hint Rewrite @low_water_mark_update_ready : pbft.
Hint Rewrite @update_checkpoint_from_new_view_preserves_low_water_mark : pbft.
Hint Rewrite @trim_checkpoint_preserves_low_water_mark : pbft.
Hint Rewrite @low_water_mark_log_new_view_state : pbft.
Hint Rewrite @low_water_mark_log_pre_prepares_of_new_view : pbft.
Hint Rewrite @low_water_mark_update_view : pbft.
Hint Rewrite @low_water_mark_change_sequence_number : pbft.
Hint Rewrite @decrement_requests_in_progress_if_primary_preserves_current_view : pbft.
Hint Rewrite @update_checkpoint_from_new_view_preserves_current_view : pbft.
Hint Rewrite @trim_checkpoint_preserves_current_view : pbft.
Hint Rewrite @sequence_number_primary_state_check_one_stable : pbft.
Hint Rewrite @current_view_check_one_stable : pbft.


Hint Resolve Nat.le_trans : pbft num.
