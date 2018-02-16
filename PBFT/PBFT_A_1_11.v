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


Require Export PBFT_A_1_7.
Require Export PBFT_A_1_10.


Section PBFT_A_1_11.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context     : PBFTcontext      }.
  Context { pbft_auth        : PBFTauth         }.
  Context { pbft_keys        : PBFTinitial_keys }.
  Context { pbft_hash        : PBFThash         }.
  Context { pbft_hash_axioms : PBFThash_axioms  }.


  (* the difference with PBFT_A_1_7 is that we have here [replica_has_correct_trace]
     instead of [isCorrect] *)
  Lemma PBFT_A_1_7_v2 :
    forall (eo : EventOrdering)
           (e  : Event)
           (L  : list Event)
           (i  : Rep)
           (rd : RequestData)
           (st : PBFTstate),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> In e L
      -> exists_at_most_f_faulty L F
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> committed_log rd (log st) = true
      ->
      exists (R : list Rep),
        no_repeats R
        /\ F < length R
        /\ nodes_have_correct_traces_before R L
        /\ forall (k : Rep),
            In k R
            ->
            exists (e' : Event) (st' : PBFTstate),
              e' ≼ e
              /\ loc e' = PBFTreplica k
              /\ state_sm_on_event (PBFTreplicaSM k) e' = Some st'
              /\ prepared_log rd (log st') = true.
  Proof.
    introv sendbyz ieL atmostbyz ckeys eqloc eqst comm.
    apply is_committed_log_implies_is_committed_entry in comm; exrepnd; subst.
    apply is_committed_entry_implies in comm1; repnd.
    apply is_prepared_entry_implies in comm2; exrepnd.

    assert (well_formed_log (log st)) as wfL by (eauto 3 with pbft).
    assert (well_formed_log_entry entry) as wfe by (eapply well_formed_log_entry_if_in; eauto).

    pose proof (select_good_guys_before eo (entry2com_senders entry) L F) as sel.
    repeat (autodimp sel hyp);
      try (apply implies_no_repeats_entry2com_senders; eauto 3 with pbft eo);[].
    destruct sel as [G sel]; repnd; simpl in *.
    rewrite length_entry2com_senders in sel1.

    exists G; dands; auto; try omega;
      try (complete (introv w z u v; subst; allrw in_map_iff; exrepnd; subst;
                     eapply sel; eauto));[].

    introv ik.
    applydup sel0 in ik.

    pose proof (in_entry2com_senders_implies_commit_in_log k entry (log st)) as expl.
    repeat (autodimp expl hyp);[].
    exrepnd.

    dup expl1 as ilog.
    eapply commits_are_received_or_generated in expl1;[|eauto];auto.
    exrepnd.
    apply or_comm in expl3; repndors;[|].

    - destruct com, b; simpl in *.
      subst i0 k.
      pose proof (PBFT_A_1_6 eo e i s v a0 d st) as q.
      repeat (autodimp q hyp);[].

      exists e st; dands; eauto 2 with eo;
        try (complete (rewrite <- expl2; auto));
        try (complete (eapply sel; eauto; eauto 3 with eo;
                       allrw; apply in_map_iff; eexists; dands; eauto)).

    - exrepnd.
      applydup localLe_implies_loc in expl1.

      pose proof (ckeys e' i st1) as ck1; repeat (autodimp ck1 hyp); eauto 3 with eo pbft;[].

      pose proof (commit_received_from_good_replica_was_in_log
                    eo e' k com i) as w.
      repeat (autodimp w hyp); try congruence;
        try (complete (introv w z; eapply sel; eauto 3 with pbft eo));[].
      exrepnd.

      destruct com, b; simpl in *.
      subst i0.
      pose proof (PBFT_A_1_6 eo e'0 k s v a0 d st0) as q.
      repeat (autodimp q hyp);[].

      exists e'0 st0; dands; eauto 4 with eo;
        try (complete (rewrite <- expl2; auto));
        try (complete (apply (sel e'0 e); eauto; eauto 4 with eo;
                       allrw; apply in_map_iff; eexists; dands; eauto)).
  Qed.
  Hint Resolve PBFT_A_1_7_v2 : pbft.

  Lemma PBFT_A_1_11 :
    forall (eo : EventOrdering)
           (e1  : Event)
           (e2  : Event)
           (i   : Rep)
           (j   : Rep)
           (n   : SeqNum)
           (v1  : View)
           (v2  : View)
           (d1  : PBFTdigest)
           (d2  : PBFTdigest)
           (st1 : PBFTstate)
           (st2 : PBFTstate),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e1,e2] F
      -> loc e1 = PBFTreplica i
      -> loc e2 = PBFTreplica j
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some st1
      -> state_sm_on_event (PBFTreplicaSM j) e2 = Some st2
      -> committed_log (request_data v1 n d1) (log st1) = true
      -> committed_log (request_data v2 n d2) (log st2) = true
      -> d1 = d2.
  Proof.
    introv auth ckeys atMost loci locj eqst1 eqst2 comm1 comm2.

    eapply PBFT_A_1_7_v2 in comm1; try exact eqst1; auto; eauto 2 with pbft; simpl; tcsp;[].
    eapply PBFT_A_1_7_v2 in comm2; try exact eqst2; auto; eauto 2 with pbft; simpl; tcsp;[].
    exrepnd.

    pose proof (A_1_10 eo e1 e2 R0 R n v1 v2 d1 d2) as q;
      repeat (autodimp q hyp); eauto 3 with pbft eo;[|];
        unfold more_than_F_have_prepared_before; dands; auto.
  Qed.

End PBFT_A_1_11.
