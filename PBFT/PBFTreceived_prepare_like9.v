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


Require Export PBFTreceived_prepare_like2.
Require Export PBFTreceived_prepare_like8.
Require Export PBFTprepare_like2request_data.


Section PBFTreceived_prepare_like9.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma correct_in_intersection :
    forall (eo : EventOrdering) (l1 l2 : list Rep) (E : list Event),
      no_repeats l1
      -> no_repeats l2
      -> 2 * F + 1 <= length l1
      -> 2 * F + 1 <= length l2
      -> exists_at_most_f_faulty E F
      -> exists good,
          In good l1
          /\ In good l2
          /\ forall e, In e E -> node_has_correct_trace_before e good.
  Proof.
    introv nrep1 nrep2 len1 len2 atmost.
    pose proof (two_quorums l1 l2) as quor; repeat (autodimp quor hyp).
    exrepnd.
    pose proof (there_is_one_good_guy_before eo l E) as gg.
    repeat (autodimp gg hyp).
    exrepnd.
    exists good; dands; auto.
  Qed.

(*  Lemma prepare_like_in_log_from_good_replica :
    forall (eo : EventOrdering) (e : Event) good pl i st,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> replica_has_correct_trace_before eo e good
      -> prepare_like2sender pl = good
      -> prepare_like_in_log pl (log st)
      -> state_sm_on_event (PBFTreplicaSM i) eo e = Some st
      ->
      exists e' st,
        e' ≼ e
        /\ loc e' = PBFTreplica good
        /\ state_sm_on_event (PBFTreplicaSM good) eo e' = Some st
        /\ prepare_like_in_log pl (log st).
  Proof.
    introv auth ckeys eqloc ctrace goodsender inlog eqst.

    pose proof (correct_prepare_like_messages_are_sent _ pl i e st) as sent.
    repeat (autodimp sent hyp);[].
    exrepnd.

    applydup localLe_implies_loc in sent1.
    pose proof (ckeys e' i st1) as ck1; autodimp ck1 hyp.

    repndors; repnd;[|].

    - pose proof (prepare_like_received_from_good_replica_was_in_log eo e' good pl i) as h.
      repeat (autodimp h hyp); allrw; eauto 3 with eo pbft; try congruence;[].

      exrepnd.

      exists e'0 st0; dands; auto; eauto 4 with eo.

    - exists e st; dands; auto; eauto 3 with eo; try congruence.
  Qed.*)

  Lemma pbft_knows_prepare_like_propagates1 :
    forall (eo : EventOrdering) (e : Event) good pl i st,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> node_has_correct_trace_before e good
      -> prepare_like2sender pl = good
      -> prepare_like_in_log pl (log st)
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      ->
      exists e' st,
        e' ≼ e
        /\ loc e' = PBFTreplica good
        /\ state_sm_on_event (PBFTreplicaSM good) e' = Some st
        /\ prepare_like_in_log pl (log st).
  Proof.
    introv auth ckeys eqloc ctrace goodsender inlog eqst.
    pose proof (knows_propagates e pl) as q.
    repeat (autodimp q hyp); eauto 3 with pbft;
      try (complete (eexists; eexists; simpl; dands; eauto));
      try (complete (simpl; allrw; subst; auto)).
    exrepnd; unfold knows in *; simpl in *; exrepnd.
    try unfold pbft_pl_data2loc in *.
    eexists; eexists; dands; eauto; try congruence.
  Qed.

  Lemma pbft_knows_prepare_like_propagates :
    forall (eo : EventOrdering) (e : Event) pl,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> node_has_correct_trace_before e (prepare_like2sender pl)
      -> knows e pl
      ->
      exists e',
        e' ≼ e
        /\ loc e' = PBFTreplica (prepare_like2sender pl)
        /\ knows e' pl.
  Proof.
    introv auth ckeys ctrace kn.
    apply knows_propagates in kn; eauto 3 with pbft.
  Qed.

  Lemma prepare_somewhere_in_log_not_from_primary :
    forall p L,
      well_formed_log L
      -> prepare_somewhere_in_log p L = true
      -> prepare2sender p <> PBFTprimary (prepare2view p).
  Proof.
    induction L; introv wf prep; simpl in *; tcsp;[].
    inversion wf as [|? ? imp wf1 wf2]; subst; clear wf; smash_pbft.
    repndors; tcsp;[].
    applydup well_formed_log_entry_no_prepare_from_leader in wf1.
    unfold prepare_in_entry in *; smash_pbft.
    allrw existsb_exists; exrepnd.
    intro e; destruct wf0.
    apply in_map_iff.
    eexists; dands; eauto.
    unfold same_rep_tok in *; smash_pbft.
    unfold is_prepare_for_entry, eq_request_data in *; smash_pbft.
    destruct a, p, b; simpl in *; subst; simpl in *; tcsp.
  Qed.
  Hint Resolve prepare_somewhere_in_log_not_from_primary : pbft.

  Lemma two_own_prepare_like_in_state :
    forall (eo : EventOrdering) (e1 e2 : Event) i pl1 pl2 st1 st2,
      loc e1 = loc e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some st1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some st2
      -> prepare_like_in_log pl1 (log st1)
      -> prepare_like_in_log pl2 (log st2)
      -> prepare_like2sender pl1 = i
      -> prepare_like2sender pl2 = i
      -> prepare_like2seq pl1 = prepare_like2seq pl2
      -> prepare_like2view pl1 = prepare_like2view pl2
      -> prepare_like2digest pl1 = prepare_like2digest pl2.
  Proof.
    introv eqloc eqst1 eqst2 prep1 prep2 send1 send2 eqseq eqview.

    apply prepare_like_in_log_implies_or in prep1.
    apply prepare_like_in_log_implies_or in prep2.
    repndors; exrepnd; subst; simpl in *.

    - destruct prep3, prep, b, b0; simpl in *; ginv; subst; eauto 2 with pbft.

    - destruct pp, prep, b, b0; simpl in *; subst.
      apply prepare_somewhere_in_log_not_from_primary in prep0; eauto 2 with pbft.
      simpl in *; tcsp.

    - destruct pp, prep, b, b0; simpl in *; subst.
      apply prepare_somewhere_in_log_not_from_primary in prep3; eauto 2 with pbft.
      simpl in *; tcsp.

    - destruct pp, pp0, b, b0; simpl in *; subst.

      eapply pre_prepare_in_somewhere_in_log_implies_pre_prepare_in_log in prep2;[|eauto].
      eapply pre_prepare_in_somewhere_in_log_implies_pre_prepare_in_log in prep1;[|eauto].

      applydup well_formed_log_implies_correct_digest in prep1;[|eauto 2 with pbft].
      applydup well_formed_log_implies_correct_digest in prep2;[|eauto 2 with pbft].

      pose proof (PBFT_A_1_2_2_local
                    eo e1 e2 (PBFTprimary v)
                    s v d2 d1 a0 a d0 d st1 st2) as q.
      repeat (autodimp q hyp); eauto 2 with pbft; subst; auto.
  Qed.

  Lemma two_know_own_prepare_like :
    forall (eo : EventOrdering) (e1 e2 : Event) pl1 pl2,
      loc e1 = loc e2
      -> knows e1 pl1
      -> knows e2 pl2
      -> loc e1 = PBFTreplica (prepare_like2sender pl1)
      -> loc e2 = PBFTreplica (prepare_like2sender pl2)
      -> prepare_like2seq pl1 = prepare_like2seq pl2
      -> prepare_like2view pl1 = prepare_like2view pl2
      -> prepare_like2digest pl1 = prepare_like2digest pl2.
  Proof.
    introv eqloc kna knb send1 send2 eqseq eqview.
    unfold knows in *; exrepnd; simpl in *.
    assert (PBFTreplica n0 = PBFTreplica n) as xx by congruence; ginv.
    eapply two_own_prepare_like_in_state;
      try (exact eqloc); try (exact kna1); try (exact knb1); auto;
        rewrite send1, send2 in *; ginv;
          try (complete (inversion eqloc; auto)).
  Qed.

  Lemma similar_prepare_like2request_data_implies_same_seq :
    forall pl1 pl2 v1 v2 n d1 d2,
      prepare_like2request_data pl1 = request_data v1 n d1
      -> prepare_like2request_data pl2 = request_data v2 n d2
      -> prepare_like2seq pl1 = prepare_like2seq pl2.
  Proof.
    introv h q.
    destruct pl1 as [p1|p1], pl2 as [p2|p2], p1 as [b1], p2 as [b2], b1, b2;
      simpl in *; ginv; auto.
  Qed.
  Hint Resolve similar_prepare_like2request_data_implies_same_seq : pbft.

  Lemma similar_prepare_like2request_data_implies_same_view :
    forall pl1 pl2 v n1 n2 d1 d2,
      prepare_like2request_data pl1 = request_data v n1 d1
      -> prepare_like2request_data pl2 = request_data v n2 d2
      -> prepare_like2view pl1 = prepare_like2view pl2.
  Proof.
    introv h q.
    destruct pl1 as [p1|p1], pl2 as [p2|p2], p1 as [b1], p2 as [b2], b1, b2;
      simpl in *; ginv; auto.
  Qed.
  Hint Resolve similar_prepare_like2request_data_implies_same_view : pbft.

  Lemma implies_prepare_like_have_same_digests :
    forall pl1 pl2 v1 v2 n1 n2 d1 d2,
      prepare_like2request_data pl1 = request_data v1 n1 d1
      -> prepare_like2request_data pl2 = request_data v2 n2 d2
      -> prepare_like2digest pl1 = prepare_like2digest pl2
      -> d1 = d2.
  Proof.
    introv h q.
    destruct pl1 as [p1|p1], pl2 as [p2|p2], p1 as [b1], p2 as [b2], b1, b2;
      simpl in *; ginv; auto.
  Qed.

End PBFTreceived_prepare_like9.


Hint Resolve prepare_somewhere_in_log_not_from_primary : pbft.
Hint Resolve similar_prepare_like2request_data_implies_same_seq : pbft.
Hint Resolve similar_prepare_like2request_data_implies_same_view : pbft.
