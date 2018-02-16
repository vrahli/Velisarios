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


Require Export PBFTreceived_prepare_like.


Section PBFT_A_1_4.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition node0 : Rep := bij_inv nodes_bij nat_n_2Fp1_0.

  Definition nat2node (n : nat) : node_type.
  Proof.
    destruct nodes_bij as [f a b].
    destruct (lt_dec n num_nodes) as [d|d].
    - exact (f (mk_nat_n d)). (* here we now that n < num_replicas so we can use our bijection *)
    - exact node0. (* here num_replicas <= n, so we return a default value: replica0 *)
  Defined.

  Lemma A_1_4 :
    forall (eo : EventOrdering)
           (e1  : Event)
           (e2  : Event)
           (i   : Rep)
           (j   : Rep)
           (n   : SeqNum)
           (v   : View)
           (d1  : PBFTdigest)
           (d2  : PBFTdigest)
           (st1 : PBFTstate)
           (st2 : PBFTstate),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> PBFT_at_most_f_byz2 eo [e1, e2]
      -> loc e1 = PBFTreplica i                               (* e1 happened at location i *)
      -> loc e2 = PBFTreplica j                               (* e2 happened at location j *)
      (* We don't need these here because they follow the protocol *)
      (*      -> isCorrect e1                                         (* i was correct at e1 *)
      -> isCorrect e2                                         (* j was correct at e2 *)*)
      -> state_sm_on_event (PBFTreplicaSM i) eo e1 = Some st1 (* state of i at e1 *)
      -> state_sm_on_event (PBFTreplicaSM j) eo e2 = Some st2 (* state of j at e2 *)
      -> prepared (request_data v n d1) st1 = true            (* the entry for <v,n,d1> is prepared at e1 *)
      -> prepared (request_data v n d2) st2 = true            (* the entry for <v,n,d2> is prepared at e2 *)
      -> d1 = d2.
  Proof.
    introv sendbyz corkeys fbyz eqloc1 eqloc2 (*iscor1 iscor2*) eqst1 eqst2 prep1 prep2.

    destruct (PBFTdigestdeq d1 d2) as [d|d]; auto.
    assert False; tcsp.

    assert (well_formed_log (log st1)) as wf1 by eauto 2 with pbft.
    assert (well_formed_log (log st2)) as wf2 by eauto 2 with pbft.

    unfold prepared in *.
    applydup prepared_log_implies_first in prep1 as h.
    applydup prepared_log_implies_first in prep2 as w.
    destruct h as [entry1 [iseg1 h]]; repnd.
    destruct w as [entry2 [iseg2 w]]; repnd.

    pose proof (well_formed_log_entry_if_in entry1 (log st1)) as wfe1.
    repeat (autodimp wfe1 hyp); eauto 2 with list.
    pose proof (well_formed_log_entry_if_in entry2 (log st2)) as wfe2.
    repeat (autodimp wfe2 hyp); eauto 2 with list.

    apply is_prepared_entry_implies_prepares_like in h; auto.
    apply is_prepared_entry_implies_prepares_like in w; auto.
    repnd.

    pose proof (correct_in_intersection
                  eo
                  (map prepare_like2sender (entry2prepares_like entry1))
                  (map prepare_like2sender (entry2prepares_like entry2))
                  [e1,e2])
      as gg.
    autorewrite with list in *.
    repeat (autodimp gg hyp);[].
    exrepnd.

    allrw in_map_iff.
    destruct gg1 as [pl1 [i1 j1]].
    destruct gg2 as [pl2 [i2 j2]].

    assert (prepare_like_in_log pl1 (log st1)) as ilog1 by (eauto 3 with pbft list).
    assert (prepare_like_in_log pl2 (log st2)) as ilog2 by (eauto 3 with pbft list).

    assert (replica_has_correct_trace_before eo e1 good) as ctrace1 by (apply gg0; tcsp).
    assert (replica_has_correct_trace_before eo e2 good) as ctrace2 by (apply gg0; tcsp).

    pose proof (prepare_like_in_log_from_good_replica eo e1 good pl1 i st1) as sent1.
    repeat (autodimp sent1 hyp);[].

    pose proof (prepare_like_in_log_from_good_replica eo e2 good pl2 j st2) as sent2.
    repeat (autodimp sent2 hyp);[].

    destruct sent1 as [e'1 [st'1 [sent1x1 [sent1x2 [sent1x3 sent1x4]]]]].
    destruct sent2 as [e'2 [st'2 [sent2x1 [sent2x2 [sent2x3 sent2x4]]]]].

    pose proof (in_entry2prepares_like_implies_prepare_like2request_data entry1 pl1) as eqrd1.
    repeat (autodimp eqrd1 hyp);[].

    pose proof (in_entry2prepares_like_implies_prepare_like2request_data entry2 pl2) as eqrd2.
    repeat (autodimp eqrd2 hyp);[].

    rewrite <- h2 in eqrd1.
    rewrite <- w2 in eqrd2.

    pose proof (two_own_prepare_like_in_state eo e'1 e'2 good pl1 pl2 st'1 st'2) as q.
    repeat (autodimp q hyp); eauto 2 with pbft.
    eapply implies_prepare_like_have_same_digests in q;[|eauto|eauto]; tcsp.
  Qed.

End PBFT_A_1_4.
