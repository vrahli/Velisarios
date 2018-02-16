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


Require Export PBFTexecute3.


Section PBFTsame_states.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context     : PBFTcontext      }.
  Context { pbft_auth        : PBFTauth         }.
  Context { pbft_keys        : PBFTinitial_keys }.
  Context { pbft_hash        : PBFThash         }.
  Context { pbft_hash_axioms : PBFThash_axioms  }.


  Lemma same_states_if_same_next_to_execute :
    forall (eo : EventOrdering) (ei ej : Event) i j sti stj,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [ei,ej] F
      -> loc ei = PBFTreplica i
      -> loc ej = PBFTreplica j
      -> state_sm_on_event (PBFTreplicaSM i) ei = Some sti
      -> state_sm_on_event (PBFTreplicaSM j) ej = Some stj
      -> next_to_execute sti = next_to_execute stj
      -> PBFT.sm_state sti = PBFT.sm_state stj /\ last_reply_state sti = last_reply_state stj.
  Proof.
    intros eo ei.
    induction ei as [? INDi] using HappenedBeforeInd;[].
    induction ej as [? INDj] using HappenedBeforeInd;[].
    introv sendbyz ckeys atMostF eqloci eqlocj eqsti eqstj eqnext.

    autorewrite with eo in *.

    (* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
    (* Let's first get that the next_to_execute are greater than 1 *)
    applydup next_to_execute_is_greater_than_one in eqsti as gti1; auto;[].
    applydup next_to_execute_is_greater_than_one in eqstj as gtj1; auto;[].

    apply le_lt_eq_dec in gti1.
    destruct gti1 as [gti1|gti1];
      [|assert (seqnum2nat (next_to_execute stj) = 1) as xx by (allrw; auto);
        symmetry in gti1;
        assert (1 = seqnum2nat 1) as q by (simpl; omega);
        rewrite q in gti1, xx;
        apply implies_eq_seq_nums in xx;
        apply implies_eq_seq_nums in gti1;
        apply state_if_initial_next_to_execute in eqsti; auto; try omega;
        apply state_if_initial_next_to_execute in eqstj; auto; try omega;
        repnd; allrw; auto];[].

    assert (1 < next_to_execute stj) as gtj2 by (rewrite <- eqnext; auto).
    clear gtj1.
    (* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

    pose proof (next_to_execute_from i eo ei sti) as q.
    repeat (autodimp q hyp); try omega;[].

    pose proof (next_to_execute_from j eo ej stj) as h.
    repeat (autodimp h hyp); try omega;[].

    exrepnd.

    assert (loc e'0 = PBFTreplica i) as eqloce'0 by (apply localLe_implies_loc in q1; allrw; auto).
    assert (loc e' = PBFTreplica j) as eqloce' by (apply localLe_implies_loc in h1; allrw; auto).

    repndors; exrepnd;[| | |].

    - (* both are from executing requests *)

      rewrite <- q5.
      rewrite <- h5.

      (* WARNING *)
      hide_hyp q5.
      hide_hyp h5.

      rewrite <- q4 in eqnext.
      rewrite <- h4 in eqnext.

      (* WARNING *)
      hide_hyp q4.
      hide_hyp h4.

      rewrite q7 in eqnext.
      rewrite h7 in eqnext.

      (* WARNING *)
      hide_hyp q7.
      hide_hyp h7.

      unfold next_seq in eqnext; simpl in eqnext.
      inversion eqnext as [xx].
      apply implies_eq_seq_nums in xx.

      applydup localLe_implies_loc in q1 as eqloc1.
      applydup localLe_implies_loc in h1 as eqloc2.

      applydup entry2seq_if_find_entry in q8 as eqni.
      applydup entry2seq_if_find_entry in h8 as eqnj.

      applydup is_committed_entry_implies_is_committed_log in q8 as comi;auto.
      applydup is_committed_entry_implies_is_committed_log in h8 as comj;auto.

      rewrite (split_log_entry_request_data entry0) in comi.
      rewrite (split_log_entry_request_data entry) in comj.
      rewrite eqni in comi.
      rewrite eqnj in comj.
      rewrite xx in comi.

      dup comi as eqdigests.
      eapply PBFT_A_1_11_before in eqdigests; try (exact comj);
        try (exact q2); try (exact h2); auto; try congruence;
          eauto 5 with pbft eo;[].

      assert (PBFT.sm_state st0 = PBFT.sm_state st1
              /\ last_reply_state st0 = last_reply_state st1)
        as eqb.
      {
        rewrite <- ite_first_state_sm_on_event_as_before in q2.
        unfold ite_first in q2.

        destruct (dec_isFirst e'0) as [z|z]; pbft_gen_inv;
          try (complete (try clear_current_view; simpl in *; subst; simpl in *;
                         pbft_simplifier; smash_pbft; try congruence; try omega));[].

        rewrite <- ite_first_state_sm_on_event_as_before in h2.
        unfold ite_first in h2.
        destruct (dec_isFirst e') as [w|w]; pbft_gen_inv;
          try (complete (try clear_current_view; simpl in *; subst; simpl in *;
                         pbft_simplifier; smash_pbft; try congruence; try omega));[].

        assert ((local_pred e'0) ≼ ei) as less1 by eauto 4 with eo.
        assert ((local_pred e') ≼ ej) as less2 by eauto 4 with eo.

        pose proof (INDi (local_pred e'0)) as INDi.
        autodimp INDi hyp;[eapply local_trans_le_r;[|eauto]; apply local_pred_is_localCausal; auto|].
        pose proof (INDi (local_pred e') i j st0 st1) as INDi; autorewrite with eo in *.
        repeat (autodimp INDi hyp); try congruence; eauto 3 with pbft eo.
      }

      applydup find_entry_implies_in in q8 as finde1.
      applydup find_entry_implies_in in h8 as finde2.

      destruct eqb as [eqsmst eqlast].
      apply implies_equal_log_entry2requests in eqdigests; eauto 3 with pbft;[].
      rewrite eqdigests in h0.
      rewrite eqlast in q0.
      rewrite eqsmst in q0.

      eapply matching_reply2requests_implies in q0; try (exact h0); auto; eauto 2 with pbft.
      repnd; dands; auto; try congruence.

    - (* one is from a new-view and one from executing a request *)

      rewrite <- q5.
      rewrite <- h5.

      (* WARNING *)
      hide_hyp q5.
      hide_hyp h5.

      rewrite <- q4 in eqnext.
      rewrite <- h4 in eqnext.

      (* WARNING *)
      hide_hyp q4.
      hide_hyp h4.

      rewrite q13 in eqnext.
      rewrite h7 in eqnext.

      (* WARNING *)
      hide_hyp q7.
      hide_hyp h7.

      unfold next_seq in eqnext; simpl in eqnext.
      inversion eqnext as [xx].
      apply implies_eq_seq_nums in xx.

      applydup localLe_implies_loc in q1 as eqloc1.
      applydup localLe_implies_loc in h1 as eqloc2.

      applydup sn_of_view_change_cert2max_seq_vc in q11 as eqsn1.
      applydup view_change_cert2_max_seq_vc_some_in in q11 as innv1.

      assert (correct_new_view nv = true) as cornv1.
      { eapply PBFT_A_1_2_5; try (exact q3); auto; try congruence. }

      pose proof (view_change_of_new_view_received_from_good_replica_was_logged
                    eo e'0 vc i) as ww.
      repeat (autodimp ww hyp); try congruence; eauto 4 with pbft eo;[].
      exrepnd.

      assert (e'1 ≼ ei) as less1 by eauto 4 with eo.
      assert (e' ≼ ej) as less2 by eauto 4 with eo.

      pose proof (INDi e'1) as k; autodimp k hyp; eauto 3 with eo;[]; clear INDi.
      pose proof (k e' good' j st4 st2) as k.
      repeat (autodimp k hyp); autorewrite with eo; try congruence; eauto 3 with pbft eo;[].
      repnd.

      unfold view_change2digest in ww1.
      unfold StableChkPt2digest in ww1.
      apply create_hash_state_last_reply_collision_resistant in ww0.
      repnd.
      dands; congruence.

    - (* one is from a new-view and one from executing a request *)

      rewrite <- q5.
      rewrite <- h5.

      (* WARNING *)
      hide_hyp q5.
      hide_hyp h5.

      rewrite <- q4 in eqnext.
      rewrite <- h4 in eqnext.

      (* WARNING *)
      hide_hyp q4.
      hide_hyp h4.

      rewrite h13 in eqnext.
      rewrite q7 in eqnext.

      (* WARNING *)
      hide_hyp h13.
      hide_hyp q7.

      unfold next_seq in eqnext; simpl in eqnext.
      inversion eqnext as [xx].
      apply implies_eq_seq_nums in xx.

      applydup localLe_implies_loc in q1 as eqloc1.
      applydup localLe_implies_loc in h1 as eqloc2.

      applydup sn_of_view_change_cert2max_seq_vc in h11 as eqsn1.
      applydup view_change_cert2_max_seq_vc_some_in in h11 as innv1.

      assert (correct_new_view nv = true) as cornv1.
      { eapply PBFT_A_1_2_5; try (exact h3); auto; try congruence. }

      pose proof (view_change_of_new_view_received_from_good_replica_was_logged
                    eo e' vc j) as ww.
      repeat (autodimp ww hyp); try congruence; eauto 4 with pbft eo;[].
      exrepnd.

      apply localHappenedBeforeLe_implies_or2 in q1.

      assert (e'1 ≼ ej) as less1 by eauto 4 with eo.

      repndors; subst.

      {
        clear INDi.
        pose proof (INDj e'1) as k; autodimp k hyp; eauto 3 with eo;[]; clear INDj.
        pose proof (k i good' sti st4) as k.
        repeat (autodimp k hyp); autorewrite with eo; try congruence; eauto 3 with pbft eo;[].
        repnd.

        unfold view_change2digest in ww0.
        unfold StableChkPt2digest in ww0.
        apply create_hash_state_last_reply_collision_resistant in ww0.
        repnd.
        dands; congruence.
      }

      {
        assert (e'0 ≼ ei) as less2 by eauto 4 with eo.

        clear INDj.
        pose proof (INDi e'0) as k; autodimp k hyp; eauto 5 with eo;[]; clear INDi.
        pose proof (k e'1 i good' st3 st4) as k.
        repeat (autodimp k hyp); autorewrite with eo; try congruence; eauto 3 with pbft eo;[].
        repnd.

        unfold view_change2digest in ww0.
        unfold StableChkPt2digest in ww0.
        apply create_hash_state_last_reply_collision_resistant in ww0.
        repnd.
        dands; congruence.
      }

    - (* both are from a new-view *)

      (* WARNING *)
      hide_hyp INDi.

      rewrite <- q4 in eqnext.
      rewrite <- h4 in eqnext.
      rewrite q13 in eqnext.
      rewrite h13 in eqnext.

      (* WARNING *)
      hide_hyp q4.
      hide_hyp h4.
      hide_hyp q13.
      hide_hyp h13.

      unfold next_seq in eqnext.
      inversion eqnext as [xx].
      apply implies_eq_seq_nums in xx.
      subst maxV0.
      GC.

      applydup localLe_implies_loc in q1 as eqloc1.
      applydup localLe_implies_loc in h1 as eqloc2.

      applydup sn_of_view_change_cert2max_seq_vc in q11 as eqsn1.
      applydup sn_of_view_change_cert2max_seq_vc in h11 as eqsn2.
      applydup view_change_cert2_max_seq_vc_some_in in q11 as innv1.
      applydup view_change_cert2_max_seq_vc_some_in in h11 as innv2.

      rewrite <- q5.
      rewrite <- h5.
      rewrite <- q6.
      rewrite <- h6.
      rewrite q15.
      rewrite h15.
      rewrite q7.
      rewrite h7.

      assert (correct_new_view nv0 = true) as cornv1.
      { eapply PBFT_A_1_2_5; try (exact q3); auto; try congruence. }

      assert (correct_new_view nv = true) as cornv2.
      { eapply PBFT_A_1_2_5; try (exact h3); auto; try congruence. }

      pose proof (view_change_of_new_view_received_from_good_replica_was_logged
                    eo e'0 vc0 i) as w.
      repeat (autodimp w hyp); try congruence; eauto 4 with pbft eo;[].
      exrepnd.

      pose proof (view_change_of_new_view_received_from_good_replica_was_logged
                    eo e' vc j) as z.
      repeat (autodimp z hyp); try congruence; eauto 4 with pbft eo;[].
      exrepnd.

      show_hyp INDi.

      assert (e'1 ≼ ei) as less1 by eauto 4 with eo.
      assert (e'2 ≼ ej) as less2 by eauto 4 with eo.

      pose proof (INDi e'1) as k; autodimp k hyp; eauto 3 with eo;[]; clear INDi.
      pose proof (k e'2 good' good'0 st4 st5) as k.
      repeat (autodimp k hyp); try congruence; eauto 3 with pbft eo;[].
      repnd.

      unfold view_change2digest in w0, z0.
      unfold StableChkPt2digest in w0, z0.
      apply create_hash_state_last_reply_collision_resistant in w0.
      apply create_hash_state_last_reply_collision_resistant in z0.
      repnd.
      dands; congruence.
  Qed.

  Lemma next_to_execute_from_before :
    forall (eo : EventOrdering) (ei ej : Event) (i j : Rep) (sti stj : PBFTstate),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [ei,ej] F
      -> loc ei = PBFTreplica i
      -> loc ej = PBFTreplica j
      -> state_sm_before_event (PBFTreplicaSM i) ei = Some sti
      -> state_sm_before_event (PBFTreplicaSM j) ej = Some stj
      -> next_to_execute sti = next_to_execute stj
      -> PBFT.sm_state sti = PBFT.sm_state stj /\ last_reply_state sti = last_reply_state stj.
  Proof.
    introv sendby ckeys atmost eqloc1 eqloc2 eqst1 eqst2 eqnext.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst1.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst2.
    unfold ite_first in *.
    destruct (dec_isFirst ei) as [d1|d1];
      destruct (dec_isFirst ej) as [d2|d2];
      ginv; subst; simpl in *; eauto 3 with pbft.

    - apply state_if_initial_next_to_execute in eqst2; auto; autorewrite with eo; auto.
      repnd; allrw; tcsp.

    - apply state_if_initial_next_to_execute in eqst1; auto; autorewrite with eo; auto.

    - eapply same_states_if_same_next_to_execute in eqst1; try (exact eqst2); auto;
        autorewrite with eo; tcsp; eauto 5 with pbft eo.
  Qed.

  Lemma replicas_never_stop :
    forall i (x : PBFTstate) m, exists s, fst (sm_update (PBFTreplicaSM i) x m) = Some s.
  Proof.
    introv.
    unfold PBFTreplicaSM; simpl.
    unfold PBFTreplica_update; destruct m; simpl.
    - unfold PBFThandle_request; smash_pbft.
    - unfold PBFThandle_pre_prepare; smash_pbft.
    - unfold PBFThandle_prepare; smash_pbft.
    - unfold PBFThandle_commit; smash_pbft.
    - eexists; eauto.
    - unfold PBFThandle_checkpoint; smash_pbft.
    - unfold PBFThandle_check_ready; smash_pbft.
    - eexists; eauto.
    - unfold PBFThandle_check_bcast_new_view; smash_pbft.
    - unfold PBFThandle_start_timer; smash_pbft.
    - unfold PBFThandle_expired_timer; smash_pbft.
    - unfold PBFThandle_view_change; smash_pbft.
    - unfold PBFThandle_new_view; smash_pbft.
    - eexists; eauto.
  Qed.
  Hint Resolve replicas_never_stop : pbft.

End PBFTsame_states.


Hint Resolve replicas_never_stop : pbft.
