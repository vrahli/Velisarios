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


Require Export PBFTexecute4.


Section PBFTexecute5.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma next_to_execute_from_before :
    forall (eo : EventOrdering) (ei ej : Event) (i j : Rep) (sti stj : PBFTstate),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> PBFT_at_most_f_byz2 eo [ei,ej]
      -> loc ei = PBFTreplica i
      -> loc ej = PBFTreplica j
      -> state_sm_before_event (PBFTreplicaSM i) eo ei = Some sti
      -> state_sm_before_event (PBFTreplicaSM j) eo ej = Some stj
      -> next_to_execute sti = next_to_execute stj
      -> sm_state sti = sm_state stj /\ last_reply_state sti = last_reply_state stj.
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

    - eapply next_to_execute_from in eqst1; try (exact eqst2); auto;
        autorewrite with eo; tcsp; eauto 5 with pbft eo.
  Qed.

  Lemma replies_match :
    forall (eo : EventOrdering) (e1 e2 : Event) v1 v2 ts c j1 j2 r1 r2 a1 a2 i1 i2,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> PBFT_at_most_f_byz2 eo [e1,e2]
      -> loc e1 = PBFTreplica i1
      -> loc e2 = PBFTreplica i2
      -> In (send_reply (mk_reply v1 ts c j1 r1 a1)) (output_system_on_event_ldata PBFTsys eo e1)
      -> In (send_reply (mk_reply v2 ts c j2 r2 a2)) (output_system_on_event_ldata PBFTsys eo e2)
      -> r1 = r2.
  Proof.
    introv sendbyz ckeys atmost eqloc1 eqloc2 out1 out2.

    pose proof (PBFTnever_stops eo e1 i1) as q.
    pose proof (PBFTnever_stops_on_event eo e1 i1) as h.
    pose proof (PBFTnever_stops eo e2 i2) as w.
    pose proof (PBFTnever_stops_on_event eo e2 i2) as z.
    exrepnd.

    eapply replies_from in out1; eauto.
    eapply replies_from in out2; eauto.
    exrepnd.

    subst.

    match goal with
    | [ H1 : committed_log _ _ = _, H2 : committed_log _ _ = _ |- _ ] =>
      rename H1 into com1; rename H2 into com2; dup com1 as com
    end.

    match goal with
    | [ H1 : find_first_reply _ _ _ = _, H2 : find_first_reply _ _ _ = _ |- _ ] =>
      rename H1 into ffr1; rename H2 into ffr2
    end.

    match goal with
    | [ H1 : find_last_reply_entry_corresponding_to_client _ _ = _,
             H2 : find_last_reply_entry_corresponding_to_client _ _ = _,
                  H3 : find_last_reply_entry_corresponding_to_client _ _ = _,
                       H4 : find_last_reply_entry_corresponding_to_client _ _ = _ |- _ ] =>
      rename H1 into fl1; rename H2 into fl2; rename H3 into fl3; rename H4 into fl4
    end.

    match goal with
    | [ H1 : reply2requests _ _ _ _ _ _ = _, H2 : reply2requests _ _ _ _ _ _ = _ |- _ ] =>
      rename H1 into r2rs1; rename H2 into r2rs2
    end.

    match goal with
    | [ H1 : request2info _ = _, H2 : request2info _ = _ |- _ ] =>
      rename H1 into r2i1; rename H2 into r2i2
    end.

    destruct (SeqNumDeq (next_to_execute st0) (next_to_execute st2)) as [d|d].

    {
      rewrite d in *.

      eapply PBFT_A_1_11_before in com;
        try exact com2; try (exact q0); try (exact w0); auto; eauto 3 with pbft;[].
      apply eq_digests_implies_eq_requests in com; subst.

      rewrite ffr1 in ffr2; ginv.

      pose proof (next_to_execute_from_before eo e1 e2 j1 j2 st2 st0) as u.
      repeat (autodimp u hyp);[].
      repnd.
      rewrite u0 in *.
      rewrite u in *.

      pose proof (next_to_execute_from eo e1 e2 j1 j2 st1 st) as v.
      repeat (autodimp v hyp); try (complete (allrw; tcsp));[].
      repnd.
      try rewrite v0 in *.
      try rewrite v in *.

      eapply matching_reply2requests_implies in r2rs1; try (exact r2rs2).
      repnd; subst.

      rewrite fl1 in *; ginv.
      rewrite fl2 in *; ginv.

      rewrite r2i1 in *; ginv.
      smash_pbft.
    }

    assert (seqnum2nat (next_to_execute st0) <> seqnum2nat (next_to_execute st2)) as d'.
    { intro xx; destruct d.
      destruct (next_to_execute st0), (next_to_execute st2); simpl in *; tcsp. }

    apply not_eq in d'; repndors;[|].

    {
      assert (next_to_execute st <= next_to_execute st2) as lenext by (allrw; simpl; omega).
      applydup next_to_execute_is_greater_than_one in z0; auto;[].

      rewrite <- ite_first_state_sm_on_event_as_before in q0.
      unfold ite_first in *.
      destruct (dec_isFirst e1) as [d1|d1]; ginv; subst; simpl in *;[].
      pose proof (last_reply_state_increases
                    eo (local_pred e1) j1 st2
                    (next_to_execute st)) as u.
      repeat (autodimp u hyp); autorewrite with eo; auto;
        try omega; eauto 3 with pbft;[].
      exrepnd.

      pose proof (next_to_execute_from eo e' e2 j j2 st' st) as v.
      repeat (autodimp v hyp); try (complete (allrw; auto)); eauto 4 with pbft eo;[].
      repnd.
      rewrite v in u0.

      applydup u0 in fl4.
      exrepnd.

      applydup reply2requests_implies_last_reply_state_extends in r2rs2 as ext.
      applydup ext in fl0.
      exrepnd.
      rewrite fl8 in *; ginv.

      assert (ts <= lre_timestamp e4) as lets by omega.

      autodimp fl5 hyp;[apply eq_nats_implies_eq_timestamps; omega|].
      autodimp fl9 hyp;[apply eq_nats_implies_eq_timestamps; omega|].
      autodimp out0 hyp;[apply eq_nats_implies_eq_timestamps; omega|].

      assert (lre_reply e4 = Some r1) as eqr1 by (dest_all x; try omega).

      assert (Some r1 = Some r2) as eqrs by congruence.
      ginv.
    }

    {
      assert (next_to_execute st1 <= next_to_execute st0) as lenext by (allrw; simpl; omega).
      applydup next_to_execute_is_greater_than_one in h0; auto;[].

      rewrite <- ite_first_state_sm_on_event_as_before in w0.
      unfold ite_first in *.
      destruct (dec_isFirst e2) as [d1|d1]; ginv; subst; simpl in *;[].
      pose proof (last_reply_state_increases
                    eo (local_pred e2) j2 st0
                    (next_to_execute st1)) as u.
      repeat (autodimp u hyp); autorewrite with eo; auto; try omega; eauto 3 with pbft eo;[].
      exrepnd.

      pose proof (next_to_execute_from eo e' e1 j j1 st' st1) as v.
      repeat (autodimp v hyp); try (complete (allrw; auto)); eauto 5 with pbft eo;[].
      repnd.
      rewrite v in u0.

      applydup u0 in fl2.
      exrepnd.

      applydup reply2requests_implies_last_reply_state_extends in r2rs1 as ext.
      applydup ext in fl0.
      exrepnd.
      rewrite fl8 in *; ginv.

      assert (ts <= lre_timestamp e0) as lets by omega.

      autodimp fl5 hyp;[apply eq_nats_implies_eq_timestamps; omega|].
      autodimp fl9 hyp;[apply eq_nats_implies_eq_timestamps; omega|].
      autodimp out14 hyp;[apply eq_nats_implies_eq_timestamps; omega|].

      assert (lre_reply e0 = Some r2) as eqr2 by (dest_all x; try omega).

      assert (Some r1 = Some r2) as eqrs by congruence.
      ginv.
    }
  Qed.

End PBFTexecute5.
