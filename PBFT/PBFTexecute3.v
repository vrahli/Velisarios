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


Require Export PBFTexecute2.
Require Export PBFT_A_1_11.
Require Export PBFTcheckpoints_from_good.

Require Export PBFTlearns_or_knows_vc_nv.
Require Export PBFTlearns_or_knows_cp_vc_nv.


Section PBFTexecute3.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context     : PBFTcontext      }.
  Context { pbft_auth        : PBFTauth         }.
  Context { pbft_keys        : PBFTinitial_keys }.
  Context { pbft_hash        : PBFThash         }.
  Context { pbft_hash_axioms : PBFThash_axioms  }.


  Lemma is_committed_entry_implies_is_committed_log :
    forall L n e,
      find_entry L n = Some e
      -> is_committed_entry e = true
      -> committed_log (log_entry_request_data e) L = true.
  Proof.
    induction L; introv find com; simpl in *; tcsp; smash_pbft.

    - unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.

    - unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
      apply entry2seq_if_find_entry in find; subst.
      destruct a, e, log_entry_request_data0, log_entry_request_data; simpl in *; ginv.
  Qed.

  Lemma PBFT_A_1_11_before :
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
      -> state_sm_before_event (PBFTreplicaSM i) e1 = Some st1
      -> state_sm_before_event (PBFTreplicaSM j) e2 = Some st2
      -> committed_log (request_data v1 n d1) (log st1) = true
      -> committed_log (request_data v2 n d2) (log st2) = true
      -> d1 = d2.
  Proof.
    introv sendbyz ckeys atmost eqloc1 eqloc2 eqst1 eqst2 com1 com2.

    rewrite <- ite_first_state_sm_on_event_as_before in eqst1.
    unfold ite_first in *.
    destruct (dec_isFirst e1) as [e|e]; ginv; subst; simpl in *;[].

    rewrite <- ite_first_state_sm_on_event_as_before in eqst2.
    unfold ite_first in *.
    destruct (dec_isFirst e2) as [f|f]; ginv; subst; simpl in *;[].

    eapply PBFT_A_1_11;
      try (exact com1); try (exact com2);
        try (exact eqst1); try (exact eqst2);
          auto; autorewrite with eo; auto;
            eauto 4 with pbft eo.
  Qed.

  Lemma split_log_entry_request_data :
    forall entry,
      log_entry_request_data entry
      = request_data (entry2view entry) (entry2seq entry) (entry2digest entry).
  Proof.
    destruct entry, log_entry_request_data; simpl; auto.
  Qed.

  Lemma eq_map_req_rep_implies_eq_map_fst :
    forall (reqs1 reqs2 : list (Request * option Reply)),
      map (fun x => PBFTrequest (fst x)) reqs1 = map (fun x => PBFTrequest (fst x)) reqs2
      -> map fst reqs1 = map fst reqs2.
  Proof.
    induction reqs1; introv e; simpl in *; destruct reqs2; simpl in *; smash_pbft.
    inversion e; f_equal; tcsp.
  Qed.
  Hint Resolve eq_map_req_rep_implies_eq_map_fst : pbft.

  Lemma implies_equal_log_entry2requests :
    forall entry1 entry2,
      well_formed_log_entry entry1
      -> well_formed_log_entry entry2
      -> is_committed_entry entry1 = true
      -> is_committed_entry entry2 = true
      -> entry2digest entry1 = entry2digest entry2
      -> log_entry2requests entry1 = log_entry2requests entry2.
  Proof.
    introv wf1 wf2 com1 com2 eqd.
    destruct entry1, entry2, log_entry_request_data, log_entry_request_data0; simpl in *; subst.
    apply well_formed_log_entry_correct_digest in wf1.
    apply well_formed_log_entry_correct_digest in wf2.
    simpl in *; smash_pbft.
    unfold log_entry2requests; simpl.
    destruct log_entry_pre_prepare_info, log_entry_pre_prepare_info0; simpl in *; tcsp.
    unfold same_digests in *; smash_pbft.
    unfold requests_and_replies2digest in *.
    rename_hyp_with create_hash_messages cr.
    apply create_hash_messages_collision_resistant in cr; eauto 2 with pbft.
  Qed.

  Lemma matching_reply2request_implies :
    forall i j v1 v2 keys1 keys2 req smst lastr oprep1 oprep2 smst1 smst2 lastr1 lastr2,
      reply2request i v1 keys1 req smst lastr = (oprep1, smst1, lastr1)
      -> reply2request j v2 keys2 req smst lastr = (oprep2, smst2, lastr2)
      -> smst1 = smst2 /\ lastr1 = lastr2.
  Proof.
    introv rep2req1 rep2req2.
    unfold reply2request in *.
    destruct req, b; simpl in *; smash_pbft.
  Qed.

  Lemma matching_reply2requests_implies :
    forall i j v1 v2 keys1 keys2 reqs smst lastr reps1 reps2 smst1 smst2 lastr1 lastr2,
      reply2requests i v1 keys1 reqs smst lastr = (reps1, smst1, lastr1)
      -> reply2requests j v2 keys2 reqs smst lastr = (reps2, smst2, lastr2)
      -> smst1 = smst2 /\ lastr1 = lastr2.
  Proof.
    induction reqs; introv repreq1 repreq2; simpl in *; smash_pbft.
    match goal with
    | [ H1 : context[reply2request], H2 : context[reply2request] |- _ ] =>
      eapply matching_reply2request_implies in H1; try exact H2; repnd; subst
    end.
    eapply IHreqs; eauto.
  Qed.

  (*Lemma correct_view_change_implies_exists_good_checkpoint :
    forall (eo : EventOrdering) (e : Event) v vc,
      PBFT_at_most_f_byz2 eo [e]
      -> correct_view_change v vc = true
      ->
      exists cp,
        In cp (view_change2cert vc)
        /\ replica_has_correct_trace_before eo e (checkpoint2sender cp)
        /\ checkpoint2digest cp = view_change2digest vc
        /\ checkpoint2seq cp = view_change2seq vc.
  Proof.
    introv atmost cor.
    unfold correct_view_change in cor; smash_pbft.
    clear cor1 cor.
    unfold correct_view_change_cert in *; smash_pbft.
    allrw @norepeatsb_as_no_repeats.

    pose proof (there_is_one_good_guy_before eo (map checkpoint2sender (view_change2cert vc)) [e]) as q.
    autorewrite with list in *.
    repeat (autodimp q hyp);[].
    exrepnd.
    allrw in_map_iff; exrepnd; subst.
    fold (replica_has_correct_trace eo (checkpoint2sender x)) in *.

    allrw forallb_forall.
    discover; clear cor0.
    unfold correct_view_change_cert_one in *; smash_pbft.
    unfold same_seq_nums, same_digests in *; smash_pbft.

    exists x; dands; auto; eauto 3 with pbft eo.
  Qed.*)

  Lemma knows4_received_from_good_replica_was_logged :
    forall (eo : EventOrdering) (e : Event) good cp i,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> loc e = PBFTreplica i
      -> node_has_correct_trace_before e good
      -> checkpoint2sender cp = good
      -> knows4 e cp
      ->
      exists e' good' st2,
        e' ≺ e
        /\ loc e' = PBFTreplica good'
        /\ state_sm_on_event (PBFTreplicaSM good') e' = Some st2
        /\ next_to_execute st2 = next_seq (checkpoint2seq cp)
        /\ checkpoint2digest cp = create_hash_state_last_reply (PBFT.sm_state st2) (last_reply_state st2).
  Proof.
    introv auth ckeys atmost eqloc ctrace eqgood kn.
    unfold knows4, knows in kn; exrepnd; simpl in *.
    unfold pbft_cp_vc_nv_knows in *; exrepnd; simpl in *.
    eapply checkpoint_of_new_view_received_from_good_replica_was_logged; eauto.
  Qed.

  Lemma view_change_of_new_view_received_from_good_replica_was_logged_xxx :
    forall (eo : EventOrdering) (e : Event) vc nv i st,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> new_view_in_log nv (view_change_state st)
      -> In vc (new_view2cert nv)
      ->
      exists e' good' st2,
        e' ≺ e
        /\ loc e' = PBFTreplica good'
        /\ state_sm_on_event (PBFTreplicaSM good') e' = Some st2
        /\ next_to_execute st2 = next_seq (view_change2seq vc)
        /\ view_change2digest vc = create_hash_state_last_reply (sm_state st2) (last_reply_state st2).
  Proof.
    introv sendbyz ckeys atMostF eqloc eqst nvinlog vcincert.
    assert (knows3 e vc) as kn by (exists st i; simpl; dands; auto; exists nv; dands; auto).
    apply knows3_implies_knows4 in kn; auto.
    exrepnd.
    allrw <-.
    eapply knows4_received_from_good_replica_was_logged; eauto.
  Qed.

  Lemma view_change_of_new_view_received_from_good_replica_was_logged :
    forall (eo : EventOrdering) (e : Event) vc i,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> loc e = PBFTreplica i
      -> knows3 e vc
      ->
      exists e' good' st2,
        e' ≺ e
        /\ loc e' = PBFTreplica good'
        /\ state_sm_on_event (PBFTreplicaSM good') e' = Some st2
        /\ next_to_execute st2 = next_seq (view_change2seq vc)
        /\ view_change2digest vc = create_hash_state_last_reply (sm_state st2) (last_reply_state st2).
  Proof.
    introv sendbyz ckeys atMostF eqloc kn.
    apply knows3_implies_knows4 in kn; auto.
    exrepnd.
    allrw <-.
    eapply knows4_received_from_good_replica_was_logged; eauto.
  Qed.

  (* TODO: get rid of: *)
  Lemma implies_knows3 :
    forall {eo : EventOrdering} (e : Event) i s nv vc,
      loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some s
      -> new_view_in_log nv (view_change_state s)
      -> In vc (new_view2cert nv)
      -> knows3 e vc.
  Proof.
    introv eqloc eqst nvin vcin.
    exists s i; dands; auto.
    exists nv; dands; auto.
  Qed.
  Hint Resolve implies_knows3 : pbft.

End PBFTexecute3.


Hint Resolve eq_map_req_rep_implies_eq_map_fst : pbft.
Hint Resolve implies_knows3 : pbft.
