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


Require Export PBFT_A_1_6.
Require Export PBFTsent_commits_are_in_log.


Section PBFT_A_1_7.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  (* Invariant 1.7 pg 149 *)
  Lemma PBFT_A_1_7 :
    forall (eo : EventOrdering)
           (e  : Event)
           (i  : Rep)
           (rd : RequestData)
           (st : PBFTstate),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> exists_at_most_f_faulty [e] F
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> committed_log rd (log st) = true
      ->
      exists (R : list Rep),
        no_repeats R
        /\ F < length R
        /\ forall (k : Rep),
            In k R
            ->
            exists (e' : Event) (st' : PBFTstate),
              isCorrect e'
              /\ e' ≼ e
              /\ loc e' = PBFTreplica k
              /\ state_sm_on_event (PBFTreplicaSM k) e' = Some st'
              /\ prepared_log rd (log st') = true.
  Proof.
    introv sendbyz atmostbyz ckeys eqloc eqst comm.
    apply is_committed_log_implies_is_committed_entry in comm; exrepnd; subst.
    apply is_committed_entry_implies in comm1; repnd.
    apply is_prepared_entry_implies in comm2; exrepnd.

    assert (well_formed_log (log st)) as wfL by (eauto 3 with pbft).
    assert (well_formed_log_entry entry) as wfe by (eapply well_formed_log_entry_if_in; eauto).

    pose proof (select_good_guys_before eo (entry2com_senders entry) [e] F) as sel.
    repeat (autodimp sel hyp); auto; eauto 3 with pbft;
      try (apply implies_no_repeats_entry2com_senders; eauto 3 with pbft);[].
    destruct sel as [G sel]; repnd; simpl in *.
    rewrite length_entry2com_senders in sel1.

    assert (forall (good : Rep), In good G -> node_has_correct_trace_before e good) as sel' by (simpl in *; tcsp).
    clear sel; rename sel' into sel.

    exists G; dands; auto; try omega;[].
    introv ik.
    applydup sel0 in ik.
    applydup sel in ik; clear sel.

    pose proof (in_entry2com_senders_implies_commit_in_log k entry (log st)) as expl.
    repeat (autodimp expl hyp);[].
    exrepnd.

    dup expl1 as ilog.
    eapply commits_are_received_or_generated in expl1;[|eauto];auto.

    exrepnd.
    apply or_comm in expl3. repndors;[|].

    - destruct com, b; simpl in *.
      subst i0 k.
      pose proof (PBFT_A_1_6 eo e i s v a0 d st) as q.
      repeat (autodimp q hyp);[].

      exists e st; dands; eauto 2 with eo;
        try (complete (rewrite <- expl2; auto)).

      pose proof (ik1 e) as w; repeat (autodimp w hyp); eauto 3 with eo.

    - exrepnd.
      applydup localLe_implies_loc in expl1.

      pose proof (ckeys e' i st1) as ck1; repeat (autodimp ck1 hyp); eauto 3 with eo pbft;[].

      pose proof (commit_received_from_good_replica_was_in_log
                    eo e' k com i) as w.
      repeat (autodimp w hyp); try congruence; eauto 3 with pbft eo;[].

      try (complete (introv z1 z2;
                     pose proof (sel e'0 e) as w; simpl in w;
                     repeat (autodimp w hyp); eauto 3 with eo;
                     try (complete (allrw; apply in_map_iff; eexists; dands; eauto))));[].

      exrepnd.

      destruct com, b; simpl in *.
      subst i0.
      pose proof (PBFT_A_1_6 eo e'0 k s v a0 d st0) as q.
      repeat (autodimp q hyp);[].

      exists e'0 st0; dands; eauto 4 with eo;
        try (complete (rewrite <- expl2; auto));
        try (complete (pose proof (ik1 e'0) as w; simpl in w;
                       repeat (autodimp w hyp); eauto 4 with eo)).
  Qed.
  Hint Resolve PBFT_A_1_7 : pbft.

End PBFT_A_1_7.


Hint Resolve PBFT_A_1_7 : pbft.
