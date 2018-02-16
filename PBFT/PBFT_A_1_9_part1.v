(*

  Copyright 2016 Luxembourg University
  Copyright 2017 Luxembourg University
  Copyright 2019 Luxembourg University

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


Require Export PBFT_A_1_2_1.
Require Export PBFT_A_1_2_2.
Require Export PBFTview_changes_from_good.


Section PBFT_A_1_9_part1.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition more_than_F_have_prepared
             (eo : EventOrdering)
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
        loc e' = PBFTreplica k
        /\ state_sm_on_event (PBFTreplicaSM k) e' = Some st'
        /\ prepared (request_data v n d) st' = true.

  Lemma more_than_F_have_prepared_implies_len :
    forall (eo : EventOrdering) R v n d,
      more_than_F_have_prepared eo R v n d -> F < length R.
  Proof.
    introv moreThanF; unfold more_than_F_have_prepared in *; tcsp.
  Qed.
  Hint Resolve more_than_F_have_prepared_implies_len : pbft.

  Lemma more_than_F_have_prepared_implies_len_le :
    forall (eo : EventOrdering) R v n d,
      more_than_F_have_prepared eo R v n d -> F + 1 <= length R.
  Proof.
    introv moreThanF; unfold more_than_F_have_prepared in *; repnd; try omega.
  Qed.
  Hint Resolve more_than_F_have_prepared_implies_len_le : pbft.

  Lemma more_than_F_have_prepared_implies_no_repeats :
    forall (eo : EventOrdering) R v n d,
      more_than_F_have_prepared eo R v n d -> no_repeats R.
  Proof.
    introv moreThanF; unfold more_than_F_have_prepared in *; repnd; auto.
  Qed.
  Hint Resolve more_than_F_have_prepared_implies_no_repeats : pbft.

  Definition exists_more_than_F_that_have_prepared
             (eo : EventOrdering)
             (v  : View)
             (n  : SeqNum)
             (d  : PBFTdigest) :=
    exists (R : list Rep),
      more_than_F_have_prepared eo R v n d.

  Lemma more_than_F_have_prepared_implies_exists_requests :
    forall eo R v n d,
      F < length R
      -> more_than_F_have_prepared eo R v n d
      -> exists rs, d = requests2digest rs.
  Proof.
    introv len moreThanF.
    destruct R as [|k]; simpl in *; tcsp.
    unfold more_than_F_have_prepared in moreThanF; repnd.
    pose proof (moreThanF k) as q; simpl in q; autodimp q hyp.
    exrepnd.

    rename_hyp_with prepared prep.
    unfold prepared in prep.

    apply prepared_log_implies in prep; exrepnd.

    assert (well_formed_log (log st')) as wf by eauto 3 with pbft.
    eapply well_formed_log_entry_if_in in wf;[|eauto].
    apply well_formed_log_entry_correct_digest in wf.

    destruct entry; simpl in *; smash_pbft.
    destruct log_entry_pre_prepare_info; simpl in *; tcsp; GC.
    unfold same_digests in *; smash_pbft.

    exists (map fst reqs); auto.
    subst; eauto 2 with pbft.
  Qed.

  Lemma exists_more_than_F_that_have_prepared_implies_exists_requests :
    forall eo v n d,
      exists_more_than_F_that_have_prepared eo v n d
      -> exists rs, d = requests2digest rs.
  Proof.
    introv e.
    unfold exists_more_than_F_that_have_prepared in e; exrepnd.
    eapply more_than_F_have_prepared_implies_exists_requests; eauto 3 with pbft.
  Qed.

  Definition PBFT_A_1_9a_sub_Def
             (eo : EventOrdering)
             (v  : View)
             (n  : SeqNum)
             (d  : PBFTdigest)
             (e  : Event)
             (i  : Rep)
             (st : PBFTstate) :=
    forall (nv : NewView)
           (rs : list Request),
      loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> v < new_view2view nv
      -> low_water_mark st < n
      -> new_view_in_log nv (view_change_state st)
      -> same_digests d (requests2digest rs) = true
      -> exists a, In (mk_pre_prepare (new_view2view nv) n rs a) (new_view2oprep nv).

  Definition PBFT_A_1_9a_Def : Prop :=
    forall (eo : EventOrdering),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      ->
      forall (R : list Rep)
             (v : View)
             (n : SeqNum)
             (d : PBFTdigest),
        more_than_F_have_prepared eo R v n d
        -> forall (e  : Event)
                  (i  : Rep)
                  (st : PBFTstate),
          nodes_have_correct_traces_before R [e]
          -> exists_at_most_f_faulty [e] F
          -> PBFT_A_1_9a_sub_Def eo v n d e i st.

  Definition PBFT_A_1_9_sub_Def
             (eo : EventOrdering)
             (v  : View)
             (n  : SeqNum)
             (d  : PBFTdigest)
             (e  : Event)
             (i  : Rep)
             (st : PBFTstate) :=
    forall (v' : View)
           (rs : list Request)
           (a  : Tokens)
           (d' : PBFTdigest),
      loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> v < v'
      -> pre_prepare_in_log (mk_pre_prepare v' n rs a) d' (log st) = true
      -> d = d'.

  Definition PBFT_A_1_9_Def : Prop :=
    forall (eo : EventOrdering),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      ->
      forall (R : list Rep)
             (v : View)
             (n : SeqNum)
             (d : PBFTdigest),
        more_than_F_have_prepared eo R v n d
        -> forall (e  : Event)
                  (i  : Rep)
                  (st : PBFTstate),
          nodes_have_correct_traces_before R [e]
          -> exists_at_most_f_faulty [e] F
          -> PBFT_A_1_9_sub_Def eo v n d e i st.

  Lemma PBFT_A_1_9_part1 :
    forall (eo : EventOrdering),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      ->
      forall (R : list Rep)
             (v : View)
             (n : SeqNum)
             (d : PBFTdigest),
        more_than_F_have_prepared eo R v n d
        -> forall (e  : Event)
                  (i  : Rep)
                  (st : PBFTstate),
          nodes_have_correct_traces_before R [e]
          -> exists_at_most_f_faulty [e] F
          -> PBFT_A_1_9a_sub_Def eo v n d e i st
          -> PBFT_A_1_9_sub_Def eo v n d e i st.
  Proof.
    introv sendbyz ckeys moreThanF ctraces atmostbyz a19a;
      introv eqloc eqst ltv prep.

    dup prep as hnv.
    eapply pre_prepare_in_log_implies_has_new_view in hnv;[|eauto];auto;[].
    simpl in hnv.
    unfold has_new_view in hnv; smash_pbft; simpl in *; try omega;[].

    unfold has_new_view1 in hnv.
    rewrite existsb_exists in hnv.
    destruct hnv as [entry hnv]; repnd.
    smash_pbft;[].

    rename n1 into nv.
    rename_hyp_with vce_new_view nvsome.

    assert (wf_view_change_state (view_change_state st)) as wfvc by eauto 2 with pbft.
    eapply wf_view_change_state_implies_all_entries in wfvc;[|eauto].
    applydup wfvc in nvsome.

    assert (new_view_in_log nv (view_change_state st))
      as nvinlog by (eauto 3 with pbft).

    applydup more_than_F_have_prepared_implies_exists_requests in moreThanF;
      auto; eauto 3 with pbft;[].
    exrepnd.

    dup prep as bwm.
    eapply pre_prepares_are_between_water_marks_if_in_log in bwm;[|eauto].
    simpl in *.
    unfold check_between_water_marks in bwm; smash_pbft.

    pose proof (a19a nv rs0) as q.
    repeat (autodimp q hyp);
      try (complete (subst; eauto 2 with pbft));
      try (complete (rewrite nvsome0; auto)).
    eauto 3 with pbft eo;[].
    exrepnd.

    eapply new_views_are_received3 in q0;[|eauto| |]; simpl; auto; eauto 2 with pbft.
    rewrite nvsome0 in q0.

    remember (is_primary (vce_view entry) i) as b; symmetry in Heqb; destruct b.

    { eapply PBFT_A_1_2_2 in prep;[| |eauto|exact q0]; simpl in *; auto;[].
      unfold pre_prepare2digest in prep; simpl in prep;try congruence. }

    eapply PBFT_A_1_2_8 in prep;[| |eauto]; simpl; auto.
    eapply PBFT_A_1_2_8 in q0;[| |eauto]; simpl; auto.
    apply prepare_of_pre_in_log_implies_prepare_in_log in prep.
    apply prepare_of_pre_in_log_implies_prepare_in_log in q0.
    exrepnd.
    eapply PBFT_A_1_2_1 in q1;try (exact prep0); eauto.
    subst; auto.
  Qed.

End PBFT_A_1_9_part1.


Hint Resolve more_than_F_have_prepared_implies_len : pbft.
Hint Resolve more_than_F_have_prepared_implies_len_le : pbft.
Hint Resolve more_than_F_have_prepared_implies_no_repeats : pbft.
