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
Require Export List.


Section PBFTexecute4.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context     : PBFTcontext      }.
  Context { pbft_auth        : PBFTauth         }.
  Context { pbft_keys        : PBFTinitial_keys }.
  Context { pbft_hash        : PBFThash         }.
  Context { pbft_hash_axioms : PBFThash_axioms  }.


  (* [lastr1] extends [lastr2] *)
  Definition last_reply_state_extends (lastr1 lastr2 : LastReplyState) : Prop :=
    forall c e2,
      find_last_reply_entry_corresponding_to_client lastr2 c = Some e2
      ->
      exists e1,
        find_last_reply_entry_corresponding_to_client lastr1 c = Some e1
        /\ lre_client e2 = lre_client e1
        /\ lre_timestamp e2 <= lre_timestamp e1
        /\ (lre_timestamp e2 = lre_timestamp e1 -> lre_reply e2 = lre_reply e1).

  Lemma last_reply_state_extends_refl :
    forall s, last_reply_state_extends s s.
  Proof.
    introv i; exists e2; dands; auto.
  Qed.
  Hint Resolve last_reply_state_extends_refl : pbft.

  Lemma last_reply_state_extends_update_last_reply_timestamp_and_result :
    forall lastr cl e (ts : Timestamp) res,
      find_last_reply_entry_corresponding_to_client lastr cl = Some e
      -> lre_timestamp e < ts
      -> last_reply_state_extends
           (update_last_reply_timestamp_and_result lastr cl ts res)
           lastr.
  Proof.
    induction lastr; introv find ltts i; simpl in *; tcsp; repndors;
      subst; tcsp; smash_pbft;
        try (complete (exists e2; dands; tcsp));
        try (complete (destruct e; simpl in *; ginv)).

    - unfold update_last_reply_entry_timestamp_and_result.
      destruct e; simpl in *.
      eexists; dands; eauto; simpl; try omega.
      introv j; subst; simpl in *; try omega.

    - eapply IHlastr in find;[|eauto]; clear IHlastr.
      apply find in i; clear find.
      exrepnd.
      exists e1; dands; eauto.
  Qed.
  Hint Resolve last_reply_state_extends_update_last_reply_timestamp_and_result : pbft.

  Lemma reply2request_implies_last_reply_state_extends :
    forall i v keys r smst1 lastr1 opr smst2 lastr2,
      reply2request i v keys r smst1 lastr1 = (opr, smst2, lastr2)
      -> last_reply_state_extends lastr2 lastr1.
  Proof.
    introv h.
    unfold reply2request in h; smash_pbft.
  Qed.
  Hint Resolve reply2request_implies_last_reply_state_extends : pbft.

  Lemma eq_nats_implies_eq_timestamps :
    forall (t1 t2 : Timestamp),
      timestamp2nat t1 = timestamp2nat t2 -> t1 = t2.
  Proof.
    destruct t1, t2; simpl in *; tcsp.
  Qed.

  Lemma last_reply_state_extends_trans :
    forall lastr3 lastr2 lastr1,
      last_reply_state_extends lastr3 lastr2
      -> last_reply_state_extends lastr2 lastr1
      -> last_reply_state_extends lastr3 lastr1.
  Proof.
    introv ext1 ext2 i.
    apply ext2 in i.
    exrepnd.
    apply ext1 in i1.
    exrepnd.
    eexists; dands; eauto; try congruence; try omega.
    introv xx.
    assert (lre_timestamp e2 = lre_timestamp e1) as yy;
      [rewrite xx in *; apply eq_nats_implies_eq_timestamps; omega
      |discover; allrw; auto].
  Qed.
  Hint Resolve last_reply_state_extends_trans : pbft.

  Lemma reply2requests_implies_last_reply_state_extends :
    forall i v keys reqs reps smst1 lastr1 smst2 lastr2,
      reply2requests i v keys reqs smst1 lastr1 = (reps, smst2, lastr2)
      -> last_reply_state_extends lastr2 lastr1.
  Proof.
    induction reqs; introv h; simpl in *; smash_pbft.
    rename_hyp_with reply2request r2r.
    rename_hyp_with reply2requests r2rs.
    apply reply2request_implies_last_reply_state_extends in r2r.
    apply IHreqs in r2rs; eauto 3 with pbft.
  Qed.
  Hint Resolve reply2requests_implies_last_reply_state_extends : pbft.

  Lemma last_reply_state_increases :
    forall (eo : EventOrdering) (e : Event) i st n,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> 1 <= n <= next_to_execute st
      ->
      exists e' j st',
        e' ≼ e
        /\ loc e' = PBFTreplica j
        /\ state_sm_on_event (PBFTreplicaSM j) e' = Some st'
        /\ next_to_execute st' = n
        /\ last_reply_state_extends (last_reply_state st) (last_reply_state st').
  Proof.
    introv sendby ckeys atmost.
    revert e i st n atmost.
    induction e as [? ind] using HappenedBeforeInd;[].
    introv atmost eqloc eqst h.

    destruct (deq_nat 1 (next_to_execute st)) as [d|d].

    {
      assert (n = 1) as xx by omega.
      subst.
      dup eqst as q.
      apply state_if_initial_next_to_execute in eqst; auto; repnd;
        [|allrw; simpl in *; autorewrite with pbft; auto];[].

      exists e i st.
      dands; auto; eauto 3 with eo pbft;
        try (complete (allrw; simpl in *; autorewrite with pbft; auto)).
    }

    assert (1 < next_to_execute st) as gt1 by omega; clear d.

    destruct (deq_nat n (next_to_execute st)) as [d|d].

    {
      subst.
      exists e i st; dands; autorewrite with pbft; auto; eauto 3 with eo pbft.
    }

    assert (1 <= n) as gt1n by omega.
    assert (n < next_to_execute st) as gtn by omega; clear h d.

    dup eqst as q.
    apply PBFTexecute.next_to_execute_from in q; auto.
    exrepnd.

    assert (loc e' = PBFTreplica i) as eqloce' by (apply localLe_implies_loc in q1; allrw; auto).

    rewrite <- q6.

    applydup localLe_implies_loc in q1 as eqloc1.

    (* either
         (1) we execute a request because committed became true
         (2) or we update the state because of a new-view we got
     *)
    repndors; exrepnd;[|].

    - (* we execute a request because committed became true *)

      applydup reply2requests_implies_last_reply_state_extends in q0 as ext.

      rewrite <- ite_first_state_sm_on_event_as_before in q2.
      unfold ite_first in q2.
      destruct (dec_isFirst e') as [d'|d']; [simpl in *; ginv|];[].

      assert (n <= next_to_execute st1) as ltst1.
      {
        rewrite <- q4 in *.
        rewrite q7 in *.
        simpl in *.
        omega.
      }

      pose proof (ind (local_pred e')) as q; clear ind.
      autodimp q hyp;eauto 4 with eo.

      autorewrite with eo in q.
      pose proof (q i st1 n) as q.
      repeat (autodimp q hyp); try congruence; eauto 4 with pbft eo;[].
      exrepnd.
      exists e'0 j st'; dands; auto; try congruence; eauto 4 with eo pbft.

    - (* we update the state because of a new-view we got *)

      rewrite q7.

      assert (n <= maxV) as ltst1.
      {
        rewrite <- q4 in *.
        rewrite q13 in *.
        simpl in *.
        omega.
      }

      rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup sn_of_view_change_cert2max_seq_vc in mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      subst maxV.

      eapply implies_knows3 in mseq1; eauto.
      eapply view_change_of_new_view_received_from_good_replica_was_logged in mseq1;
        try (exact q3); eauto; try congruence; eauto 4 with pbft eo;[].
      exrepnd.

      assert (n <= next_to_execute st0) as lt1.
      {
        allrw; simpl; omega.
      }

      pose proof (ind e'0) as q; clear ind; autodimp q hyp; eauto 3 with eo;[].
      pose proof (q good' st0 n) as q.
      repeat (autodimp q hyp); try omega; eauto 4 with pbft eo;[].
      exrepnd.
      exists e'1 j st'; dands; auto; try congruence; eauto 5 with eo;[].

      unfold view_change2digest, StableChkPt2digest in mseq0.
      apply create_hash_state_last_reply_collision_resistant in mseq0.
      repnd.
      rewrite mseq0; auto.
  Qed.

  Lemma send_reply_in_trim_outputs_with_low_water_mark :
    forall r msgs st,
      In (send_reply r) (trim_outputs_with_low_water_mark msgs st)
      -> In (send_reply r) msgs.
  Proof.
    introv i.
    unfold trim_outputs_with_low_water_mark in i.
    apply filter_In in i; repnd.
    unfold trim_output_with_low_water_mark in i; simpl in i; smash_pbft.
  Qed.
  Hint Resolve send_reply_in_trim_outputs_with_low_water_mark : pbft.

  Definition mk_reply
             (v : View)
             (t : Timestamp)
             (c : Client)
             (i : Rep)
             (r : PBFTresult)
             (a : Tokens) : Reply :=
    reply (bare_reply v t c i r) a.

  Lemma in_list_option2list :
    forall {A} (a : A) l,
      In a (list_option2list l)
      -> In (Some a) l.
  Proof.
    induction l; introv i; simpl in *; tcsp.
    destruct a0; simpl in *; tcsp.
    repndors; subst; tcsp.
  Qed.

  Lemma find_committed_entry_implies_committed_log :
    forall l n e,
      find_entry l n = Some e
      -> is_committed_entry e = true
      -> committed_log (request_data (entry2view e) n (entry2digest e)) l = true.
  Proof.
    induction l; introv find com; simpl in *; ginv; smash_pbft;[|].

    - destruct e, log_entry_request_data; simpl in *.
      unfold is_request_data_for_entry, eq_request_data in *; simpl in *; smash_pbft.

    - destruct a, log_entry_request_data; simpl in *.
      unfold is_request_data_for_entry, eq_request_data in *; simpl in *; smash_pbft.
  Qed.
  Hint Resolve find_committed_entry_implies_committed_log : pbft.

  Lemma implies_find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result :
    forall lastr c e ts r,
      find_last_reply_entry_corresponding_to_client lastr c = Some e
      ->
      exists e',
        find_last_reply_entry_corresponding_to_client
          (update_last_reply_timestamp_and_result lastr c ts r) c = Some e'
        /\ lre_timestamp e' = ts.
  Proof.
    induction lastr; introv f; simpl in *; ginv; smash_pbft;
      destruct e; simpl in *; GC; tcsp.
    eexists; dands; eauto.
  Qed.

  Lemma find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result_diff :
    forall lastr c c' ts r,
      c <> c'
      -> find_last_reply_entry_corresponding_to_client
           (update_last_reply_timestamp_and_result lastr c' ts r) c
         = find_last_reply_entry_corresponding_to_client lastr c.
  Proof.
    induction lastr; introv f; simpl in *; ginv; smash_pbft.
    destruct a; simpl in *; GC; tcsp.
  Qed.

  Lemma reply2requests_preserves_find_last_reply_corresponding_to_client :
    forall i w keys rs smst1 lastr1 reps smst2 lastr2 c e1,
      reply2requests i w keys rs smst1 lastr1 = (reps, smst2, lastr2)
      -> find_last_reply_entry_corresponding_to_client lastr1 c = Some e1
      -> exists e2,
          find_last_reply_entry_corresponding_to_client lastr2 c = Some e2
          /\ lre_timestamp e1 <= lre_timestamp e2.
  Proof.
    induction rs; introv r2r k; repeat (simpl in *; smash_pbft).
    unfold reply2request in *; simpl in *; smash_pbft; try omega.

    rename_hyp_with reply2requests r2rs.

    destruct (client_deq c x6) as [d|d]; subst.

    {
      rewrite k in *; ginv.
      eapply implies_find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result in k.
      exrepnd.

      eapply IHrs in r2rs;[|eauto].
      subst; simpl in *.
      exrepnd.
      exists e2; dands; auto; try omega.
    }

    {
      eapply IHrs in r2rs;[|rewrite find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result_diff;eauto].
      exrepnd.
      exists e2; dands; auto; try omega.
    }
  Qed.

  Lemma in_reply2requests_implies_find_last_reply_entry_corresponding_to_client :
    forall i w keys rs smst1 lastr1 reps smst2 lastr2 v ts c j r a,
      reply2requests i w keys rs smst1 lastr1 = (reps, smst2, lastr2)
      -> In (Some (mk_reply v ts c j r a)) reps
      -> exists e1 e2,
          find_last_reply_entry_corresponding_to_client lastr1 c = Some e1
          /\ find_last_reply_entry_corresponding_to_client lastr2 c = Some e2
          /\ lre_timestamp e1 <= ts <= lre_timestamp e2.
  Proof.
    induction rs; introv r2r k; repeat (simpl in *; smash_pbft).

    repndors; subst; simpl in *; tcsp.

    - destruct a, b; simpl in *; ginv.
      unfold reply2request in *; simpl in *; smash_pbft; try omega.

      + match goal with
        | [ H : _ = Some x |- _ ] => rename H into f
        end.
        dup f as h.
        rename_hyp_with reply2requests r2rs.
        eapply implies_find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result in f.
        exrepnd.
        eapply reply2requests_preserves_find_last_reply_corresponding_to_client in r2rs;[|eauto].
        exrepnd.
        subst; simpl in *.
        eexists; eexists; dands; eauto.

      + match goal with
        | [ H : _ = Some x |- _ ] => rename H into f
        end.
        dup f as h.
        rename_hyp_with reply2requests r2rs.
        eapply reply2requests_preserves_find_last_reply_corresponding_to_client in r2rs;[|eauto].
        exrepnd.
        subst; simpl in *.
        eexists; eexists; dands; eauto; try omega.

    - rename_hyp_with reply2requests r2rs.
      eapply IHrs in r2rs;[|eauto].
      exrepnd.

      unfold reply2request in *; smash_pbft;
        try (complete (eexists; eexists; dands; eauto)).

      destruct (client_deq x6 c) as [d|d]; subst.

      * eexists; eexists; dands; eauto; try omega.
        match goal with
        | [ H : _ = Some x |- _ ] => rename H into q
        end.
        eapply implies_find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result in q.
        exrepnd.
        rewrite q1 in *; ginv; try omega.

      * rewrite find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result_diff in r2rs0;auto.
        eexists; eexists; dands; eauto; try omega.
  Qed.

  Fixpoint find_first_reply
           (rs  : list Request)
           (ts  : Timestamp)
           (c   : Client) : option (list Request * Request * list Request) :=
    match rs with
    | [] => None
    | r :: rs =>
      match request2info r with
      | Some (opr, ts', c') =>

        if client_deq c c' then

          if ts <? ts' then None
          else if TimestampDeq ts' ts then Some ([], r, rs)
               else match find_first_reply rs ts c with
                    | Some (l, a, k) => Some (r :: l, a, k)
                    | None => None
                    end

        else match find_first_reply rs ts c with
             | Some (l, a, k) => Some (r :: l, a, k)
             | None => None
             end

      | None =>
        match find_first_reply rs ts c with
        | Some (l, a, k) => Some (r :: l, a, k)
        | None => None
        end
      end
    end.

  Lemma find_first_reply_some_implies :
    forall rs ts c l a k,
      find_first_reply rs ts c = Some (l, a, k)
      -> rs = l ++ a :: k
         /\ (exists opr, request2info a = Some (opr, ts, c))
         /\ (forall r o (ts' : Timestamp),
                In r l
                -> request2info r = Some (o, ts', c)
                -> ts' < ts).
  Proof.
    induction rs; introv f; simpl in *; ginv.
    destruct a, b; simpl in *; tcsp; smash_pbft.

    - rename_hyp_with find_first_reply f.
      apply IHrs in f; exrepnd; subst.
      dands; tcsp.

      + allrw; eexists; dands; auto.

      + introv xx yy; repndors; subst; tcsp; simpl in *; ginv.
        apply f in yy; auto.

    - dands; auto; tcsp.
      eexists; dands; eauto.

    - rename_hyp_with find_first_reply f.
      apply IHrs in f; exrepnd; subst.
      dands; tcsp.

      + allrw; eexists; dands; auto.

      + introv xx yy; repndors; subst; tcsp; simpl in *; ginv.

        * apply Nat.le_neq; dands; auto.
          introv xx; subst.
          destruct ts, ts'; simpl in *; subst; tcsp.

        * apply f in yy; tcsp.

    - rename_hyp_with find_first_reply f.
      apply IHrs in f; exrepnd; subst.
      dands; tcsp.

      + allrw; eexists; eauto.

      + introv xx yy; repndors; subst; simpl in *; tcsp; ginv.
        apply f in yy; tcsp.
  Qed.

  Lemma reply2request_preserves_find_last_reply_entry_corresponding_to_client_backward :
    forall i w keys opr ts cl a smst1 lastr1 rep smst2 lastr2 e2,
      reply2request i w keys (req (bare_req opr ts cl) a) smst1 lastr1
      = (rep, smst2, lastr2)
      -> find_last_reply_entry_corresponding_to_client lastr2 cl = Some e2
      ->
      exists e1,
        find_last_reply_entry_corresponding_to_client lastr1 cl = Some e1
        /\ ts <= lre_timestamp e2
        /\ lre_timestamp e1 <= lre_timestamp e2.
  Proof.
    introv h f.
    unfold reply2request in h; simpl in *; smash_pbft;
      try (complete (rewrite f in *; ginv; eexists; dands; eauto; try omega)).

    match goal with
    | [ H : _ = Some x |- _ ] => rename H into q
    end.
    eapply implies_find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result in q; exrepnd.
    rewrite q1 in f; ginv.
    eexists; dands; eauto.
  Qed.

  Lemma reply2requests_implies_find_first_reply_some :
    forall i w keys rs smst1 lastr1 reps smst2 lastr2 v ts c j r a,
      reply2requests i w keys rs smst1 lastr1 = (reps, smst2, lastr2)
      -> In (Some (mk_reply v ts c j r a)) reps
      -> exists l a k, find_first_reply rs ts c = Some (l, a, k).
  Proof.
    induction rs; introv r2r k; repeat (simpl in *; smash_pbft);
      try (complete (eexists; eexists; eexists; eauto)).

    - assert False; tcsp.
      repndors; subst; simpl in *; tcsp.

      + destruct a, b; simpl in *; ginv.
        unfold reply2request in *; simpl in *; smash_pbft; try omega.

      + destruct a, b; simpl in *; ginv.

        rename_hyp_with reply2requests r2rs.
        rename_hyp_with reply2request r2r.
        dup r2rs as h.
        eapply in_reply2requests_implies_find_last_reply_entry_corresponding_to_client in h;[|eauto].
        exrepnd.

        dup r2r as q.
        eapply reply2request_preserves_find_last_reply_entry_corresponding_to_client_backward in q;[|eauto].
        exrepnd; omega.

    - assert False; tcsp.

      assert (x7 < ts) as xx.
      { apply Nat.le_neq; dands; auto.
        introv xx; subst.
        destruct x7, ts; simpl in *; tcsp. }
      repndors; subst; simpl in *; tcsp.

      + destruct a, b; simpl in *; ginv.
        unfold reply2request in *; simpl in *; smash_pbft; try omega.

      + destruct a, b; simpl in *; ginv.

        rename_hyp_with reply2requests r2rs.
        rename_hyp_with reply2request r2r.

        eapply IHrs in r2rs;[|eauto]; exrepnd.
        pbft_simplifier.

    - assert False; tcsp.
      repndors; subst; simpl in *; tcsp.

      + destruct a, b; simpl in *; ginv.
        unfold reply2request in *; simpl in *; smash_pbft; try omega.

      + destruct a, b; simpl in *; ginv.

        rename_hyp_with reply2requests r2rs.

        eapply IHrs in r2rs;[|eauto]; exrepnd.
        pbft_simplifier.

    - assert False; tcsp.
      repndors; subst; simpl in *; tcsp.

      + destruct a, b; simpl in *; ginv.

      + destruct a, b; simpl in *; ginv.

        rename_hyp_with reply2requests r2rs.

        eapply IHrs in r2rs;[|eauto]; exrepnd.
        pbft_simplifier.
  Qed.

  Fixpoint apply_requests (s : PBFTsm_state) (l : list Request) : list PBFTresult * PBFTsm_state :=
    match l with
    | [] => ([], s)
    | r :: rs =>
      match request2info r with
      | Some (opr, ts, c) =>
        let (R,s1) := PBFTsm_update c s opr in
        let (RS,s2) := apply_requests s1 rs in
        (R :: RS, s2)
      | None => apply_requests s rs
      end
    end.

  Lemma find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result_implies_timestamp :
    forall lastr c e ts r,
      find_last_reply_entry_corresponding_to_client
        (update_last_reply_timestamp_and_result lastr c ts r) c = Some e
      -> lre_timestamp e = ts.
  Proof.
    induction lastr; introv f; simpl in *; ginv; smash_pbft;
      destruct a; simpl in *; auto; tcsp.
  Qed.

  Lemma find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result_implies_reply :
    forall lastr c e ts r,
      find_last_reply_entry_corresponding_to_client
        (update_last_reply_timestamp_and_result lastr c ts r) c = Some e
      -> lre_reply e = Some r.
  Proof.
    induction lastr; introv f; simpl in *; ginv; smash_pbft;
      destruct a; simpl in *; auto; tcsp.
  Qed.

  Lemma reply2request_some_preserves_find_last_reply_entry_corresponding_to_client_backward :
    forall i w keys opr ts cl a smst1 lastr1 rep smst2 lastr2,
      reply2request i w keys (req (bare_req opr ts cl) a) smst1 lastr1
      = (Some rep, smst2, lastr2)
      ->
      exists e1 e2,
        find_last_reply_entry_corresponding_to_client lastr1 cl = Some e1
        /\ find_last_reply_entry_corresponding_to_client lastr2 cl = Some e2
        /\ lre_timestamp e1 <= ts
        /\ lre_timestamp e2 = ts
        /\ reply2timestamp rep = ts.
  Proof.
    introv h.
    unfold reply2request in h; simpl in *; smash_pbft.

    - rename_hyp_with find_last_reply_entry_corresponding_to_client f.
      eapply implies_find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result in f; exrepnd.
      rewrite f1.
      subst; simpl in *.
      eexists; eexists; dands; eauto; try omega.

    - eexists; eexists; dands; eauto; try omega.
      apply eq_nats_implies_eq_timestamps; simpl; omega.
  Qed.

  Lemma reply2requests_constant_timestamp_implies :
    forall j v keys rs smst1 lastr1 reps smst2 lastr2 cl e1 e2,
      find_last_reply_entry_corresponding_to_client lastr1 cl = Some e1
      -> find_last_reply_entry_corresponding_to_client lastr2 cl = Some e2
      -> lre_timestamp e1 = lre_timestamp e2
      -> reply2requests j v keys rs smst1 lastr1 = (reps, smst2, lastr2)
      -> lre_reply e2 = lre_reply e1.
  Proof.
    induction rs; introv f1 f2 eqts r2rs; simpl in *; smash_pbft.
    unfold reply2request in *; smash_pbft.

    destruct a, b; simpl in *; ginv.

    destruct (client_deq cl x6) as [d|d]; subst.

    - rewrite f1 in *; ginv.
      rename_hyp_with reply2requests r2rs.
      dup r2rs as q.

      match goal with
      | [ H : _ = Some x |- _ ] => rename H into fx
      end.
      eapply implies_find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result in fx.
      exrepnd.

      eapply reply2requests_preserves_find_last_reply_corresponding_to_client in q;[|eauto].
      exrepnd.
      rewrite q1 in *; ginv.
      rewrite eqts in *; simpl in *; try omega.

    - rename_hyp_with reply2requests r2rs.
      eapply IHrs in r2rs;
        [|rewrite find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result_diff;[|eauto]; eauto
         |eauto|]; auto.
  Qed.

  Lemma reply2requests_app :
    forall i v keys rs1 rs2 smst1 lastr1 reps smst2 lastr2,
      reply2requests i v keys (rs1 ++ rs2) smst1 lastr1 = (reps, smst2, lastr2)
      ->
      exists reps1 reps2 smst' lastr',
        reply2requests i v keys rs1 smst1 lastr1 = (reps1, smst', lastr')
        /\ reply2requests i v keys rs2 smst' lastr' = (reps2, smst2, lastr2)
        /\ reps = reps1 ++ reps2.
  Proof.
    induction rs1; introv r2rs; simpl in *.

    - exists ([] : list (option Reply)) reps smst1 lastr1; dands; auto.

    - smash_pbft.
      match goal with
      | [ H : reply2requests _ _ _ (_ ++ _) _ _ = _ |- _ ] => rename H into r2rs
      end.
      apply IHrs1 in r2rs; exrepnd.
      rewrite r2rs0 in *; ginv.
      exists (x2 :: x6) reps2 x7 x4; simpl; dands; auto.
  Qed.

  Lemma reply2request_different_client :
    forall i v keys o t c' a smst1 lastr1 rep smst2 lastr2 c e,
      c <> c'
      -> reply2request i v keys (req (bare_req o t c') a) smst1 lastr1 = (rep, smst2, lastr2)
      -> find_last_reply_entry_corresponding_to_client lastr1 c = Some e
      -> find_last_reply_entry_corresponding_to_client lastr2 c = Some e.
  Proof.
    introv d r2r f.
    unfold reply2request in r2r; simpl in *.
    smash_pbft.
    rewrite find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result_diff; auto.
  Qed.

  Lemma reply2requests_no_progress :
    forall i v keys l smst1 lastr1 reps smst2 lastr2 e1 e2 ts c,
      (forall r o ts', In r l -> request2info r = Some (o, ts', c) -> ts' < ts)
      -> reply2requests i v keys l smst1 lastr1 = (reps, smst2, lastr2)
      -> find_last_reply_entry_corresponding_to_client lastr1 c = Some e1
      -> find_last_reply_entry_corresponding_to_client lastr2 c = Some e2
      -> lre_timestamp e1 <= ts
      -> lre_timestamp e2 <= ts.
  Proof.
    induction l; introv imp r2rs f1 f2 lets; simpl in *; smash_pbft.
    destruct a, b; simpl in *;
      [unfold reply2request in *; simpl in *; ginv; eapply IHl; eauto|].

    rename_hyp_with reply2requests r2rs.
    rename_hyp_with reply2request r2r.

    destruct (client_deq c0 c); subst.

    - pose proof (imp (req (bare_req o t c) a) o t) as q; simpl in q; repeat (autodimp q hyp).
      unfold reply2request in *; smash_pbft; try omega;
        try (complete (eapply IHl in r2rs;[| |eauto|eauto|];
                       [|introv w z; eapply imp;eauto|];
                       try omega));[].

      match goal with
      | [ H : _ = Some e1 |- _ ] => rename H into f1
      end.
      dup f1 as f'.
      eapply implies_find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result in f'; exrepnd.
      eapply IHl in r2rs;[| |eauto|eauto|];[|introv w z; eapply imp;eauto|]; try omega.
      allrw; try omega.

    - eapply reply2request_different_client in r2r;[| |eauto]; auto.
      eapply IHl in r2rs;[| |eauto|eauto|];[|introv w z;eapply imp;eauto|]; tcsp.
  Qed.

  Lemma reply2requests_no_progress_response :
    forall i v keys l smst1 lastr1 reps smst2 lastr2 ts c,
      (forall r o ts', In r l -> request2info r = Some (o, ts', c) -> ts' < ts)
      -> reply2requests i v keys l smst1 lastr1 = (reps, smst2, lastr2)
      -> forall r,
          In (Some r) reps
          -> reply2client r = c
          -> reply2timestamp r < ts.
  Proof.
    induction l; introv imp r2rs j eqc; simpl in *; smash_pbft; simpl in *; tcsp.
    repndors; subst; tcsp.

    - destruct a, b; simpl in *;
        [unfold reply2request in *; simpl in *; ginv; eapply IHl; eauto|].

      unfold reply2request in *; smash_pbft.

      + eapply imp; eauto; simpl; eauto.

      + eapply imp; eauto; simpl; eauto.

    - eapply IHl; eauto.
  Qed.

  Lemma reply2request_preserves_find_last_reply_entry_corresponding_to_client_backward2 :
    forall i w keys r opr ts cl smst1 lastr1 rep smst2 lastr2 e2,
      reply2request i w keys r smst1 lastr1
      = (rep, smst2, lastr2)
      -> request2info r = Some (opr, ts, cl)
      -> find_last_reply_entry_corresponding_to_client lastr2 cl = Some e2
      ->
      exists e1,
        find_last_reply_entry_corresponding_to_client lastr1 cl = Some e1
        /\ ts <= lre_timestamp e2
        /\ lre_timestamp e1 <= lre_timestamp e2.
  Proof.
    introv h q f.
    destruct r, b; simpl in *; ginv.
    eapply reply2request_preserves_find_last_reply_entry_corresponding_to_client_backward; eauto.
  Qed.

  Lemma reply2request_preserves_find_last_reply_entry_corresponding_to_client_backward3 :
    forall i w keys r opr ts cl smst1 lastr1 rep smst2 lastr2 e1,
      reply2request i w keys r smst1 lastr1
      = (rep, smst2, lastr2)
      -> request2info r = Some (opr, ts, cl)
      -> find_last_reply_entry_corresponding_to_client lastr1 cl = Some e1
      ->
      exists e2,
        find_last_reply_entry_corresponding_to_client lastr2 cl = Some e2
        /\ ts <= lre_timestamp e2
        /\ lre_timestamp e1 <= lre_timestamp e2.
  Proof.
    introv h q f.
    destruct r, b; simpl in *; ginv.
    unfold reply2request in h; simpl in *; smash_pbft;
      try (complete (eexists; dands; eauto; try omega)).

    rename_hyp_with find_last_reply_entry_corresponding_to_client f.
    dup f as g.
    eapply implies_find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result in g; exrepnd.
    rewrite g1.
    subst; simpl in *.
    eexists; dands; eauto; try omega.
  Qed.

  Lemma reply2request_inc_timestamp_records_update :
    forall i v keys req smst1 lastr1 repop smst2 lastr2 c e1 e2 opr ts,
      reply2request i v keys req smst1 lastr1 = (repop, smst2, lastr2)
      -> find_last_reply_entry_corresponding_to_client lastr1 c = Some e1
      -> find_last_reply_entry_corresponding_to_client lastr2 c = Some e2
      -> request2info req = Some (opr, ts, c)
      -> lre_timestamp e1 < lre_timestamp e2
      -> lre_reply e2 = Some (fst (PBFTsm_update c smst1 opr)).
  Proof.
    introv r2r f1 f2 nfo lte.
    unfold reply2request in r2r.
    rewrite nfo in *.
    rewrite f1 in *.
    smash_pbft; try (complete (rewrite f1 in *; ginv; try omega)).
    apply find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result_implies_reply in f2; auto.
  Qed.

  Lemma reply2request_from_stored :
    forall i v keys a smst1 lastr1 r smst2 lastr2 e,
      reply2request i v keys a smst1 lastr1 = (Some r, smst2, lastr2)
      -> find_last_reply_entry_corresponding_to_client lastr1 (reply2client r) = Some e
      -> reply2timestamp r <= lre_timestamp e
      -> lre_reply e = Some (reply2result r) /\ reply2timestamp r = lre_timestamp e.
  Proof.
    introv r2r f lets.
    unfold reply2request in *.
    smash_pbft;
      destruct a, b; simpl in *; ginv;
        rewrite f in *; ginv; dands; auto; try omega;
          apply eq_nats_implies_eq_timestamps; auto; try omega.
  Qed.

  Lemma reply2request_preserves_find_last_reply_entry_corresponding_forward :
    forall i w keys r smst1 lastr1 rep smst2 lastr2 cl e1,
      reply2request i w keys r smst1 lastr1 = (rep, smst2, lastr2)
      -> find_last_reply_entry_corresponding_to_client lastr1 cl = Some e1
      ->
      exists e2,
        find_last_reply_entry_corresponding_to_client lastr2 cl = Some e2
        /\ lre_timestamp e1 <= lre_timestamp e2.
  Proof.
    introv r2r f.
    destruct r, b; simpl in *; ginv;
      unfold reply2request in r2r; simpl in *; smash_pbft;
        try (complete (eexists; dands; eauto; try omega)).

    destruct (client_deq c cl); subst.

    - rewrite f in *; ginv.
      eapply implies_find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result in f; exrepnd.
      exists e'; dands; eauto.
      subst; auto.

    - rewrite find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result_diff; auto.
      eexists; dands; eauto.
  Qed.

  Lemma reply2requests_after_progress_response :
    forall i v keys l smst1 lastr1 reps smst2 lastr2 (ts : Timestamp) c e,
      reply2requests i v keys l smst1 lastr1 = (reps, smst2, lastr2)
      -> find_last_reply_entry_corresponding_to_client lastr1 c = Some e
      -> ts <= lre_timestamp e
      -> forall r,
          In (Some r) reps
          -> reply2client r = c
          -> reply2timestamp r = ts
          -> lre_reply e = Some (reply2result r) /\ ts = lre_timestamp e.
  Proof.
    induction l; introv r2rs f ltes j eqcl eqts; simpl in *; smash_pbft; simpl in *; tcsp.
    rename_hyp_with reply2requests r2rs.
    rename_hyp_with reply2request r2r.
    repndors; subst; tcsp.

    - eapply reply2request_from_stored in r2r;[|eauto|]; auto.

    - destruct a, b; simpl in *;
        [unfold reply2request in *; simpl in *; ginv; eapply IHl; eauto|];[].

      dup r2r as w.
      eapply reply2request_preserves_find_last_reply_entry_corresponding_forward in w;[|eauto]; exrepnd.

      destruct (client_deq c (reply2client r)) as [d|d]; subst.

      {
        unfold reply2request in *; simpl in *.
        rewrite f in *.
        smash_pbft.

        - applydup find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result_implies_timestamp in w1; subst.

          eapply IHl in r2rs;
            [|eauto| |eauto|reflexivity|reflexivity]; auto; try omega;[].
          repnd.
          rewrite r2rs in *.
          omega.

        - assert (t = lre_timestamp e) as xx.
          { apply eq_nats_implies_eq_timestamps; omega. }
          subst.

          eapply IHl in r2rs;
            [|eauto| |eauto|reflexivity|reflexivity]; auto; try omega;[].
          repnd.
          dands; auto; try congruence.

        - assert False; tcsp.
          assert (t = lre_timestamp e) as xx.
          { apply eq_nats_implies_eq_timestamps; omega. }
          subst.

          eapply IHl in r2rs;
            [|eauto| |eauto|reflexivity|reflexivity]; auto; try omega;[].
          repnd.
          dands; auto; try congruence.
      }

      {
        eapply reply2request_different_client in r2r;[| |eauto]; tcsp;[].
        rewrite r2r in *; ginv.

        eapply IHl in r2rs;
          [|eauto| |eauto|reflexivity|reflexivity]; auto; try omega.
      }
  Qed.

  Lemma reply2request_preserves_lre_reply :
    forall i v keys req smst1 lastr1 res smst2 lastr2 c e1 e2,
      reply2request i v keys req smst1 lastr1 = (res, smst2, lastr2)
      -> find_last_reply_entry_corresponding_to_client lastr1 c = Some e1
      -> find_last_reply_entry_corresponding_to_client lastr2 c = Some e2
      -> lre_timestamp e1 = lre_timestamp e2
      -> lre_reply e1 = lre_reply e2.
  Proof.
    introv r2r f1 f2 eqts.
    unfold reply2request in r2r; smash_pbft.

    destruct (client_deq x2 c) as [d|d]; subst.

    - rewrite f1 in *; ginv.
      apply find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result_implies_timestamp in f2; subst.
      rewrite eqts in *; try omega.

    - rewrite find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result_diff in f2; auto.
      rewrite f2 in *; ginv.
  Qed.

  Lemma replica_and_view_of_message_in_reply2request :
    forall i w keys a smst1 lastr1 v ts c j r b smst2 lastr2,
      reply2request i w keys a smst1 lastr1 = (Some (mk_reply v ts c j r b), smst2, lastr2)
      -> i = j /\ v = w.
  Proof.
    introv r2r.
    unfold reply2request in r2r; smash_pbft.
  Qed.

  Lemma replica_and_view_of_message_in_reply2requests :
    forall i w keys rs smst1 lastr1 res smst2 lastr2 v ts c j r a,
      reply2requests i w keys rs smst1 lastr1 = (res, smst2, lastr2)
      -> In (Some (mk_reply v ts c j r a)) res
      -> i = j /\ v = w.
  Proof.
    induction rs; introv r2rs k; repeat (simpl in *; smash_pbft).
    repndors; subst; simpl in *; tcsp;[|eapply IHrs; eauto];[].
    eapply replica_and_view_of_message_in_reply2request; eauto.
  Qed.

  Lemma reply2requests_implies_find_first_reply_some2 :
    forall i w keys rs smst1 lastr1 reps smst2 lastr2 v ts c j r a,
      reply2requests i w keys rs smst1 lastr1 = (reps, smst2, lastr2)
      -> In (Some (mk_reply v ts c j r a)) reps
      ->
      exists l req k opr reps' smst' lastr' e1 e2,
        i = j
        /\ v = w
        /\ find_first_reply rs ts c = Some (l, req, k)
        /\ request2info req = Some (opr, ts, c)
        /\ reply2requests i w keys l smst1 lastr1 = (reps', smst', lastr')
        /\ find_last_reply_entry_corresponding_to_client lastr' c = Some e1
        /\ find_last_reply_entry_corresponding_to_client lastr2 c = Some e2
        /\ lre_timestamp e1 <= ts <= lre_timestamp e2
        /\ (if lre_timestamp e1 <? ts
            then r = fst (PBFTsm_update c smst' opr)
            else lre_reply e1 = Some r)
        /\ (lre_timestamp e2 = ts -> lre_reply e2 = Some r).
  Proof.
    introv r2rs k.

    dup r2rs as q.
    eapply reply2requests_implies_find_first_reply_some in q;[|eauto]; exrepnd.

    dup r2rs as h.
    eapply in_reply2requests_implies_find_last_reply_entry_corresponding_to_client in h;[|eauto]; exrepnd.

    allrw.
    exists l a0 k0.

    applydup find_first_reply_some_implies in q0.
    exrepnd; subst.
    allrw.
    exists opr.

    apply reply2requests_app in r2rs; exrepnd.
    simpl in *; smash_pbft;[].

    dup r2rs0 as z.
    eapply reply2requests_preserves_find_last_reply_corresponding_to_client in z;[|eauto]; exrepnd.

    dup r2rs0 as noprog.
    eapply reply2requests_no_progress in noprog;[|eauto|eauto|eauto|];auto;[].

    pose proof (reply2requests_no_progress_response i w keys l smst1 lastr1 reps1 smst' lastr' ts c) as noprog'.
    repeat (autodimp noprog' hyp).

    allrw in_app_iff.
    repndors;[|];
      [assert False; tcsp; apply noprog' in k; simpl in *; auto; try omega|];[].

    match goal with
    | [ H : reply2requests _ _ _ l _ _ = _ |- _ ] => rename H into r2rs'
    end.

    rename_hyp_with reply2request r2r.
    dup r2r as m.
    eapply reply2request_preserves_find_last_reply_entry_corresponding_to_client_backward3 in m;eauto.
    exrepnd.

    simpl in k; repndors; subst; simpl in *.

    {
      unfold reply2request in r2r.
      rewrite q4 in *.
      rewrite z1 in *.
      pbft_dest_all x;[|].

      - exists reps1 smst' lastr' e0 e2.
        dands; auto;[|].

        + allrw; simpl.
          smash_pbft; try omega.

        + introv xx; subst; simpl in *; try omega.
          rename_hyp_with reply2requests r2rs''.
          applydup find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result_implies_timestamp in m1.
          applydup find_last_reply_entry_corresponding_to_client_update_last_reply_timestamp_and_result_implies_reply in m1.
          eapply reply2requests_constant_timestamp_implies in r2rs'';
            [|eauto|eauto|]; auto; try congruence.

      - assert (ts = (lre_timestamp e0)) as eq1 by (apply eq_nats_implies_eq_timestamps; omega).
        subst; GC.

        exists reps1 x3 x1 e0 e2.
        dands; auto;[|].

        + allrw; smash_pbft; try omega.

        + introv xx.
          match goal with
          | [ H : reply2requests _ _ _ k0 _ _ = _ |- _ ] => rename H into r2rs''
          end.
          eapply reply2requests_constant_timestamp_implies in r2rs'';
            [|eauto|eauto|]; auto; try congruence.
    }

    match goal with
    | [ H : reply2requests _ _ _ k0 _ _ = _ |- _ ] => rename H into r2rs''
    end.
    dup r2rs'' as u.
    eapply in_reply2requests_implies_find_last_reply_entry_corresponding_to_client in u;[|eauto].
    exrepnd.
    rewrite u0 in *; ginv.
    rewrite u2 in *; ginv.

    assert (ts = (lre_timestamp e3)) as eq1 by (apply eq_nats_implies_eq_timestamps; omega).
    subst; GC.
    clear m2.

    clear noprog' q1.

    dup r2rs'' as eqrv.
    eapply replica_and_view_of_message_in_reply2requests in eqrv;[|eauto].
    repnd; subst.

    exists reps1 smst' lastr' e0 e2.
    dands; auto;[|].

    - smash_pbft.

      + eapply reply2request_inc_timestamp_records_update in r2r;
          [|eauto|eauto|eauto|]; auto.

        eapply reply2requests_after_progress_response in k;
          [|eauto|eauto| | |];simpl;[| | |reflexivity];auto.
        repnd; simpl in *.
        rewrite k1 in *; ginv.

      + assert (lre_timestamp e0 = lre_timestamp e3) as xx.
        { apply eq_nats_implies_eq_timestamps; omega. }

        eapply reply2requests_after_progress_response in k;
          [|eauto|eauto| | |];simpl;[| | |reflexivity];auto.
        repnd; simpl in *.

        eapply reply2request_preserves_lre_reply in r2r;[|eauto|eauto|]; auto.
        congruence.

    - introv xx.

      dup r2rs'' as z.
      eapply reply2requests_constant_timestamp_implies in z;[|eauto|eauto|];auto.
      rewrite z; clear z.

      eapply reply2requests_after_progress_response in k;
        [|eauto|eauto| | |];simpl;[| | |reflexivity];auto.
      repnd; simpl in *; auto.
  Qed.

  Lemma reply_in_find_and_execute_requests_implies :
    forall i w keys s1 msgs s2 v ts c j r a,
      well_formed_log (log s1)
      -> find_and_execute_requests i w keys s1 = (msgs, s2)
      -> In (send_reply (mk_reply v ts c j r a)) msgs
      -> exists v' rs l req k opr reps' smst' lastr' e1 e2,
          i = j
          /\ v = w
          /\ next_to_execute s2 = next_seq (next_to_execute s1)
          /\ committed_log (request_data v' (next_to_execute s1) (requests2digest rs)) (log s1) = true
          /\ find_first_reply rs ts c = Some (l, req, k)
          /\ request2info req = Some (opr, ts, c)
          /\ reply2requests i w keys l (PBFT.sm_state s1) (last_reply_state s1) = (reps', smst', lastr')
          /\ find_last_reply_entry_corresponding_to_client lastr' c = Some e1
          /\ find_last_reply_entry_corresponding_to_client (last_reply_state s2) c = Some e2
          /\ lre_timestamp e1 <= ts <= lre_timestamp e2
          /\ (if lre_timestamp e1 <? ts
              then r = fst (PBFTsm_update c smst' opr)
              else lre_reply e1 = Some r)
          /\ (lre_timestamp e2 = ts -> lre_reply e2 = Some r).
  Proof.
    introv wf find inmsgs.
    unfold find_and_execute_requests in find; smash_pbft.
    rename_hyp_with execute_requests exec.
    unfold execute_requests in exec.
    destruct (ready s1); smash_pbft; simpl in *; tcsp.
    rename_hyp_with check_broadcast_checkpoint check.
    rename_hyp_with reply2requests rep2req.

    allrw in_app_iff; simpl in *; repndors; ginv;[|];
      [|eapply message_in_check_broadcast_checkpoint_implies in check;[|eauto];
        repndors; exrepnd; ginv];[].
    allrw in_map_iff; exrepnd.
    destruct x0, b; unfold mk_reply in inmsgs1; ginv.
    fold (mk_reply v ts c j r a) in *.
    apply in_list_option2list in inmsgs0.

    applydup check_broadcast_checkpoint_preserves_next_to_execute in check; simpl in *.
    rewrite check0; clear check0.
    applydup check_broadcast_checkpoint_preserves_last_reply_state in check; simpl in *.
    rewrite check0; clear check0.
    clear check.

    rename_hyp_with find_entry fentry.
    rename_hyp_with is_committed_entry iscom.

    assert (committed_log
              (request_data (entry2view x) (next_to_execute s1) (entry2digest x))
              (log s1) = true) as com by eauto 3 with pbft.

    applydup find_entry_implies_in in fentry as ilog.

    assert (well_formed_log_entry x) as wfx by eauto 3 with pbft.

    assert (requests2digest (log_entry2requests x) = entry2digest x) as eqd.
    {
      clear com rep2req inmsgs0 fentry wf ilog.
      apply well_formed_log_entry_correct_digest in wfx.
      destruct x, log_entry_pre_prepare_info; simpl in *; smash_pbft.
      unfold same_digests in wfx; smash_pbft.
      unfold log_entry2requests; simpl.
      allrw; eauto 3 with pbft.
    }

    dup rep2req as r2r.

    exists (entry2view x) (log_entry2requests x); rewrite eqd, com.

    eapply reply2requests_implies_find_first_reply_some2 in r2r;[|eauto].
    exrepnd.
    exists l req k opr reps' smst' lastr' e1 e2.
    dands; auto.
  Qed.

  Lemma replies_from :
    forall (eo : EventOrdering) (e : Event) v ts c j r a i st1 st2,
      loc e = PBFTreplica i
      -> In (send_reply (mk_reply v ts c j r a)) (output_system_on_event_ldata PBFTsys e)
      -> state_sm_before_event (PBFTreplicaSM i) e = Some st1
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st2
      -> exists v' rs l req k opr reps' smst' lastr' e1 e2,
          i = j
          /\ v = current_view st1
          /\ next_to_execute st2 = next_seq (next_to_execute st1)
          /\ committed_log (request_data v' (next_to_execute st1) (requests2digest rs)) (log st1) = true
          /\ find_first_reply rs ts c = Some (l, req, k)
          /\ request2info req = Some (opr, ts, c)
          /\ reply2requests i (current_view st1) (local_keys st1) l (PBFT.sm_state st1) (last_reply_state st1) = (reps', smst', lastr')
          /\ find_last_reply_entry_corresponding_to_client lastr' c = Some e1
          /\ find_last_reply_entry_corresponding_to_client (last_reply_state st2) c = Some e2
          /\ lre_timestamp e1 <= ts <= lre_timestamp e2
          /\ (if lre_timestamp e1 <? ts
              then r = fst (PBFTsm_update c smst' opr)
              else lre_reply e1 = Some r)
          /\ (lre_timestamp e2 = ts -> lre_reply e2 = Some r).
  Proof.
    introv eqloce inout eqst1 eqst2.
    apply in_output_system_on_event_ldata in inout.

    unfold PBFTsys in inout.
    rewrite eqloce in inout.

    dup eqst2 as eqst2_At_e.
    rewrite state_sm_on_event_unroll2 in eqst2.

    rw @loutput_sm_on_event_unroll2 in inout.
    fold (@DirectedMsgs _ _) in *.
    simpl in *.

    match goal with
    | [ H : context[map_option _ ?s] |- _ ] =>
      remember s as sop; symmetry in Heqsop; destruct sop; simpl in *;[|ginv]
    end.

    op_st_some m eqtrig.
    rewrite eqtrig in *; simpl in *.
    ginv.

    unfold PBFTreplica_update in *.
    destruct m; simpl in *; ginv; subst; tcsp;
      smash_handlers; try conflicting_sends.

    {
      (* pre-prepare *)

      allrw in_app_iff; repndors;
        [apply in_check_broadcast_prepare_implies in inout; exrepnd; subst; ginv
        |apply in_check_broadcast_commit_implies2 in inout; exrepnd; subst; ginv
        |];[].

      rename_hyp_with check_send_replies check.
      eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
    }

    {
      (* prepare *)

      allrw in_app_iff; repndors;
        [apply in_check_broadcast_commit_implies in inout; exrepnd;subst;ginv
        |].

      rename_hyp_with check_send_replies check.
      eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.
      eapply reply_in_find_and_execute_requests_implies in fexec;[| |eauto]; eauto 3 with pbft.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with CheckBCastNewView2entry cb.

      apply CheckBCastNewView2entry_some_implies in cb.
      allrw in_app_iff.
      repndors; smash_pbft;[].
      eapply message_in_update_state_new_view_implies in inout;[|eauto].
      exrepnd; ginv.
    }

    {
      (* expired-timer *)

      repndors; ginv; smash_pbft.
    }

    {
      (* new_view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      allrw in_app_iff; repndors;
        [apply send_reply_in_trim_outputs_with_low_water_mark in inout;
         eapply in_add_prepares_to_log_from_new_view_pre_prepares_implies in add;[|eauto];
         repndors; exrepnd; ginv|].

      eapply message_in_update_state_new_view_implies in inout;[|eauto].
      exrepnd; ginv.
    }
  Qed.

End PBFTexecute4.


Hint Resolve last_reply_state_extends_refl : pbft.
Hint Resolve last_reply_state_extends_update_last_reply_timestamp_and_result : pbft.
Hint Resolve reply2request_implies_last_reply_state_extends : pbft.
Hint Resolve last_reply_state_extends_trans : pbft.
Hint Resolve reply2requests_implies_last_reply_state_extends : pbft.
Hint Resolve send_reply_in_trim_outputs_with_low_water_mark : pbft.
Hint Resolve find_committed_entry_implies_committed_log : pbft.
