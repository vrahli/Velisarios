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
Require Export PBFTknows_prepared.


Section PBFT_A_1_4.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition node0 : Rep := bij_inv node_bij nat_n_2Fp1_0.

  Definition nat2node (n : nat) : node_type.
  Proof.
    destruct node_bij as [f a b].
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
      -> exists_at_most_f_faulty [e1, e2] F
      -> loc e1 = PBFTreplica i                               (* e1 happened at location i *)
      -> loc e2 = PBFTreplica j                               (* e2 happened at location j *)
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some st1 (* state of i at e1 *)
      -> state_sm_on_event (PBFTreplicaSM j) e2 = Some st2 (* state of j at e2 *)
      -> prepared (request_data v n d1) st1 = true            (* the entry for <v,n,d1> is prepared at e1 *)
      -> prepared (request_data v n d2) st2 = true            (* the entry for <v,n,d2> is prepared at e2 *)
      -> d1 = d2.
  Proof.
    introv sendbyz corkeys fbyz eqloc1 eqloc2 eqst1 eqst2; introv prep1 prep2.

    destruct (PBFTdigestdeq d1 d2) as [d|d]; auto.
    assert False; tcsp.

    assert (well_formed_log (log st1)) as wf1 by eauto 2 with pbft.
    assert (well_formed_log (log st2)) as wf2 by eauto 2 with pbft.

    eapply prepared_as_pbft_knows_rd in prep1;[| |eauto|];auto;[].
    eapply prepared_as_pbft_knows_rd in prep2;[| |eauto|];auto;[].

    pose proof (knows_in_intersection
                  e1 e2
                  (2 * F + 1)
                  (request_data v n d1)
                  (request_data v n d2)
                  one_pre_prepare
                  [e1,e2]
                  F) as q.
    repeat (autodimp q hyp); simpl; eauto 3 with pbft;
      try (complete (unfold num_replicas; try omega));[].
    destruct q as [e1' [e2' [pl1 [pl2 q]]]]; repnd.

    pose proof (two_know_own_prepare_like eo e1' e2' pl1 pl2) as z.
    repeat (autodimp z hyp); eauto 2 with pbft; try congruence;[].
    eapply implies_prepare_like_have_same_digests in z;[|eauto|eauto]; tcsp.
  Qed.

End PBFT_A_1_4.
