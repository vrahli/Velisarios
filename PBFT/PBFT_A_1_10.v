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


Require Export PBFT_A_1_4.
Require Export PBFT_A_1_9.


Section PBFT_A_1_10.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context     : PBFTcontext      }.
  Context { pbft_auth        : PBFTauth         }.
  Context { pbft_keys        : PBFTinitial_keys }.
  Context { pbft_hash        : PBFThash         }.
  Context { pbft_hash_axioms : PBFThash_axioms  }.


  Definition more_than_F_have_prepared_before
             (eo : EventOrdering)
             (e  : Event)
             (R  : list Rep)
             (v  : View)
             (n  : SeqNum)
             (d  : PBFTdigest) :=
    no_repeats R
    /\ F < length R
    /\
    forall (k : Rep),
      In k R
      ->
      exists (e' : Event) (st' : PBFTstate),
        e' ≼ e
        /\ loc e' = PBFTreplica k
        /\ state_sm_on_event (PBFTreplicaSM k) e' = Some st'
        /\ prepared (request_data v n d) st' = true.

  Lemma more_than_F_have_prepared_before_implies :
    forall (eo : EventOrdering) (e : Event) R v n d,
      more_than_F_have_prepared_before eo e R v n d
      -> more_than_F_have_prepared eo R v n d.
  Proof.
    introv moreThanF.
    unfold more_than_F_have_prepared, more_than_F_have_prepared_before in *.
    repnd; dands; auto.
    introv i.
    applydup moreThanF in i; exrepnd.
    eexists; eexists; dands; eauto.
  Qed.
  Hint Resolve more_than_F_have_prepared_before_implies : pbft.

  Lemma A_1_10_lt :
    forall (eo    : EventOrdering)
           (e1 e2 : Event)
           (R1 R2 : list Rep)
           (n     : SeqNum)
           (v1 v2 : View)
           (d1 d2 : PBFTdigest),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> v1 < v2
      -> exists_at_most_f_faulty [e2] F
      -> nodes_have_correct_traces_before R1 [e2]
      -> more_than_F_have_prepared_before eo e1 R1 v1 n d1
      -> more_than_F_have_prepared_before eo e2 R2 v2 n d2
      -> d1 = d2.
  Proof.
    introv sendbyz corkeys ltv atmost ctraces moreThanF1 moreThanF2.

    unfold more_than_F_have_prepared in moreThanF2.
    destruct moreThanF2 as [norep2 [len2 moreThanF2]].

    destruct (PBFTdigestdeq d1 d2); auto.
    assert False; tcsp;[].

    pose proof (there_is_one_good_guy_before eo R2 [e2]) as h.
    repeat (autodimp h hyp); try omega;[].
    exrepnd.
    pose proof (moreThanF2 good) as prep; autodimp prep hyp.
    exrepnd.

    pose proof (PBFT_A_1_9 eo) as q; repeat (autodimp q hyp).
    pose proof (q R1 v1 n d1) as q; autodimp q hyp; eauto 3 with pbft;[].
    pose proof (q e' good st') as q.
    repeat (autodimp q hyp); eauto 3 with pbft eo;[].

    unfold prepared in prep1.
    eapply prepared_implies2 in prep1;[|eauto 3 with pbft].
    exrepnd.
    destruct pp, b; simpl in *; ginv; simpl in *.
    unfold pre_prepare2digest in *; simpl in *.
    fold (mk_pre_prepare v2 n d a) in *.

    hide_hyp prep1.

    pose proof (h0 e2) as h0; autodimp h0 hyp.

    pose proof (q v2 d a (requests2digest d)) as q.
    repeat (autodimp q hyp); eauto 3 with pbft eo.
  Qed.

  Lemma A_1_10 :
    forall (eo    : EventOrdering)
           (e1 e2 : Event)
           (R1 R2 : list Rep)
           (n     : SeqNum)
           (v1 v2 : View)
           (d1 d2 : PBFTdigest),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e1,e2] F
      -> nodes_have_correct_traces_before R1 [e2]
      -> nodes_have_correct_traces_before R2 [e1]
      -> more_than_F_have_prepared_before eo e1 R1 v1 n d1
      -> more_than_F_have_prepared_before eo e2 R2 v2 n d2
      -> d1 = d2.
  Proof.
    introv sendbyz corkeys atmost ctraces1 ctraces2 moreThanF1 moreThanF2.

    destruct (lt_dec v1 v2) as [e|e].

    { eapply A_1_10_lt; try exact moreThanF1; try exact moreThanF2; eauto 3 with pbft eo. }

    destruct (lt_dec v2 v1) as [f|f].

    { symmetry; eapply A_1_10_lt; eauto; eauto 3 with pbft eo. }

    assert (v1 = v2) as xx by (apply equal_nats_implies_equal_views; omega).
    subst.
    clear e f.

    destruct moreThanF1 as [norep1 [len1 moreThanF1]].
    destruct moreThanF2 as [norep2 [len2 moreThanF2]].

    pose proof (there_is_one_good_guy_before eo R1 [e1,e2]) as h.
    pose proof (there_is_one_good_guy_before eo R2 [e1,e2]) as q.
    repeat (autodimp h hyp); try omega;[].
    repeat (autodimp q hyp); try omega;[].
    exrepnd.

    applydup moreThanF1 in h1; exrepnd.
    applydup moreThanF2 in q1; exrepnd.

    pose proof (h0 e1) as h0; simpl in h0; autodimp h0 hyp; auto.
    pose proof (q0 e2) as q0; simpl in q0; autodimp q0 hyp; auto.

    eapply A_1_4; try (exact h2); try (exact q2); try (exact h5); try (exact q5);
      auto; allrw; eauto 3 with pbft eo.
  Qed.

End PBFT_A_1_10.


Hint Resolve more_than_F_have_prepared_before_implies : pbft.
