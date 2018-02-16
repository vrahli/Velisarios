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


Require Export PBFTexecute4.
Require Export PBFTsame_states.


Section PBFTagreement.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.
  Context { pbft_hash_axioms : PBFThash_axioms  }.


  Lemma agreement :
    forall (eo : EventOrdering) (e1 e2 : Event) v1 v2 ts c j1 j2 r1 r2 a1 a2 i1 i2,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e1,e2] F
      -> loc e1 = PBFTreplica i1
      -> loc e2 = PBFTreplica i2
      -> In (send_reply (mk_reply v1 ts c j1 r1 a1)) (output_system_on_event_ldata PBFTsys e1)
      -> In (send_reply (mk_reply v2 ts c j2 r2 a2)) (output_system_on_event_ldata PBFTsys e2)
      -> r1 = r2.
  Proof.
    introv sendbyz ckeys atmost eqloc1 eqloc2 out1 out2.

    applydup @output_system_on_event_ldata_implies_state_sm_on_event in out1 as h;
      [|introv; simpl in *; unfold PBFTsys, PBFTnstate; remember (loc e1); destruct n; ginv; eauto 3 with pbft; try apply replicas_never_stop].
    revert h; unfold PBFTnstate; rewrite eqloc1; introv h; exrepnd.

    applydup @output_system_on_event_ldata_implies_state_sm_on_event in out2 as z;
      [|introv; simpl in *; unfold PBFTsys, PBFTnstate; remember (loc e2); destruct n; ginv; eauto 3 with pbft; try apply replicas_never_stop].
    revert z; unfold PBFTnstate; rewrite eqloc2; introv z; exrepnd.

    pose proof (state_sm_before_event_some_between3 e1 e1 (PBFTreplicaSM i1) st) as q.
    repeat (autodimp q hyp); eauto 3 with eo; exrepnd.

    pose proof (state_sm_before_event_some_between3 e2 e2 (PBFTreplicaSM i2) st0) as w.
    repeat (autodimp w hyp); eauto 3 with eo; exrepnd.

    rename st into st1.
    rename st0 into st.
    rename s' into st2.
    rename s'0 into st0.

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
        try exact com2; try (exact q0); try (exact w0); auto; eauto 3 with pbft eo;[].
      apply eq_digests_implies_eq_requests in com; subst.

      rewrite ffr1 in ffr2; ginv.

      pose proof (next_to_execute_from_before eo e1 e2 j1 j2 st2 st0) as u.
      repeat (autodimp u hyp);[].
      repnd.
      rewrite u0 in *.
      rewrite u in *.

      pose proof (same_states_if_same_next_to_execute eo e1 e2 j1 j2 st1 st) as v.
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
        try omega; eauto 3 with pbft eo;[].
      exrepnd.

      pose proof (same_states_if_same_next_to_execute eo e' e2 j j2 st' st) as v.
      repeat (autodimp v hyp); try (complete (allrw; auto)); eauto 4 with pbft eo;[].
      repnd.
      rewrite v in u0.

      applydup u0 in fl4.
      exrepnd.

      match goal with
      | [ H : context[reply2requests j1] |- _ ] => rename H into rep2req
      end.
      applydup reply2requests_implies_last_reply_state_extends in rep2req as ext.
      applydup ext in fl0.
      exrepnd.
      rewrite fl8 in *; ginv.

      assert (ts <= lre_timestamp e4) as lets by omega.

      autodimp fl5 hyp;[apply eq_nats_implies_eq_timestamps; omega|].
      autodimp fl9 hyp;[apply eq_nats_implies_eq_timestamps; omega|].
      autodimp out0 hyp;[apply eq_nats_implies_eq_timestamps; omega|].

      assert (lre_reply e4 = Some r1) as eqr1 by (pbft_dest_all x; try omega).

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

      pose proof (same_states_if_same_next_to_execute eo e' e1 j j1 st' st1) as v.
      repeat (autodimp v hyp); try (complete (allrw; auto)); eauto 5 with pbft eo;[].
      repnd.
      rewrite v in u0.

      applydup u0 in fl2.
      exrepnd.

      match goal with
      | [ H : context[reply2requests j2] |- _ ] => rename H into rep2req
      end.
      applydup reply2requests_implies_last_reply_state_extends in rep2req as ext.
      applydup ext in fl0.
      exrepnd.
      rewrite fl8 in *; ginv.

      assert (ts <= lre_timestamp e0) as lets by omega.

      autodimp fl5 hyp;[apply eq_nats_implies_eq_timestamps; omega|].
      autodimp fl9 hyp;[apply eq_nats_implies_eq_timestamps; omega|].
      autodimp out14 hyp;[apply eq_nats_implies_eq_timestamps; omega|].

      assert (lre_reply e0 = Some r2) as eqr2 by (pbft_dest_all x; try omega).

      assert (Some r1 = Some r2) as eqrs by congruence.
      ginv.
    }
  Qed.


(*  Definition mk_reply
             (v : View)
             (t : Timestamp)
             (c : Client)
             (i : Rep)
             (r : PBFTresult)
             (a : Tokens) : Reply :=
    reply (bare_reply v t c i r) a.

  Lemma sent_replies_are_committed :
    forall (eo : EventOrdering) (e : Event) p dst st i,
      loc e = PBFTreplica i
      -> In (send_reply v t c i r) (output_system_on_event_ldata PBFTsys eo e)
      -> state_sm_on_event (PBFTreplicaSM i) eo e = Some st
      -> prepare_in_log p (log st) = true
      -> exists n,
          committed_log (request_data ) (log e).
  Proof.
  Qed.*)


(*
  Lemma in_check_send_replies_implies :
    forall i v ks
           (giop : option GeneratedInfo)
           (msgs : DirectedMsgs)
           (sn   : SeqNum)
           (m    : DirectedMsg)
           (st1 st2 : PBFTstate),
      check_send_replies i v ks giop st1 sn = (msgs, st2)
      -> In m msgs
      -> exists (prepop : option Prepare)
                (commop : option Commit)
                (entry : PBFTlogEntry),
          giop = Some (MkGeneratedInfo prepop commop entry)
          /\ is_committed_entry entry = true
          /\ m = send_check_ready check_ready (PBFTreplica i)
          /\ st2 = add_to_ready st1 sn.
  Proof.
    introv h j.
    unfold check_send_replies in h.
    destruct giop; simpl in *; tcsp.
    - destruct g.
      dest_cases x; ginv; simpl in *; tcsp.
      + inversion h; subst; clear h; simpl in *; repndors; subst; tcsp.
        eexists; eexists; eexists; dands; eauto.
      + inversion h; subst; clear h; simpl in *; tcsp.
    - inversion h; subst; simpl in *; tcsp.
  Qed.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_returns_prep_comm_rep :
    forall (slf  : Rep)
           (pps  : list (Pre_prepare * PBFTdigest))
           (st1 st2 : PBFTstate)
           (msgs : DirectedMsgs)
           (m    : DirectedMsg),
      add_prepares_to_log_from_new_view_pre_prepares slf st1 pps = (st2, msgs)
      -> In m msgs
      -> (exists i p, m = MkDMsg i (PBFTprepare p))
         \/
         (exists i c, m = MkDMsg i (PBFTcommit c))
         \/
         (exists i r, m = MkDMsg i (PBFTcheck_ready r)).
  Proof.
    induction pps; introv e i; simpl in *; ginv.

    - inversion e; clear e; subst; simpl in *; tcsp.

    - dest_cases w; symmetry in Heqw.
      dest_cases x; symmetry in Heqx.
      inversion e; clear e; subst.
      apply in_app_iff in i; repndors.

      + unfold add_prepare_to_log_from_new_view_pre_prepare in Heqw.
        repnd; simpl in *.
        dest_cases y; symmetry in Heqy; simpl in *; tcsp;[|].

        * dest_cases u; symmetry in Hequ; simpl in *; tcsp;[].
          dest_cases v; symmetry in Heqv; simpl in *; tcsp;[].
          inversion Heqw; subst; clear Heqw.
          apply in_app_iff in i; repndors.

          { unfold check_broadcast_prepare in i.
            dest_cases q; subst; simpl in *.
            destruct q; simpl in *.
            dest_cases p; symmetry in Heqp; simpl in *; tcsp;[|].

            - inversion Heqv; subst; clear Heqv; simpl in *.
              dest_cases k; symmetry in Heqk; simpl in *; tcsp;[].
              dest_cases r; subst; simpl in *;tcsp;[|].

              + apply in_broadcast2others in i; exrepnd; subst; simpl in *.
                left.
                eexists; eexists; reflexivity.

              + apply in_broadcast2others in i; exrepnd; subst; simpl in *.
                left.
                eexists; eexists; reflexivity.

            - inversion Heqv; clear Heqv; subst; simpl in *.
              dest_cases k; symmetry in Heqk; simpl in *; tcsp.
              dest_cases r; symmetry in Heqr; simpl in *; tcsp;[|].

              + apply in_broadcast2others in i; exrepnd; subst; simpl in *.
                left.
                eexists; eexists; reflexivity.

              + apply in_broadcast2others in i; exrepnd; subst; simpl in *.
                left.
                eexists; eexists; reflexivity. }

          { unfold check_broadcast_commit in i.
            dest_cases q; symmetry in Heqq; subst; simpl in *; tcsp;[|].

            - destruct q; simpl in *.
              dest_cases k; symmetry in Heqk; simpl in *; tcsp;[|].

              + inversion Heqv; clear Heqv; subst; simpl in *.
                apply in_app_iff in i; simpl in *; repndors; tcsp.

                * dest_cases r; symmetry in Heqr; simpl in *; tcsp;[].
                  dest_cases p; subst; simpl in *; tcsp;[|].

                  { apply in_broadcast2others in i; exrepnd; subst.
                    right; left.
                    eexists; eexists; reflexivity. }

                  { apply in_broadcast2others in i; exrepnd; subst.
                    right; left.
                    eexists; eexists; reflexivity. }

                * subst; simpl in *.
                  right; right.
                  eexists; eexists; reflexivity.

              + inversion Heqv; clear Heqv; subst; simpl in *; tcsp.
                allrw app_nil_r.
                dest_cases q; symmetry in Heqq.
                dest_cases r; subst; simpl in *; tcsp;[|].

                * apply in_broadcast2others in i; exrepnd; subst; simpl in *.
                  right; left.
                  eexists; eexists; reflexivity.

                * apply in_broadcast2others in i; exrepnd; subst; simpl in *.
                  right; left.
                  eexists; eexists; reflexivity.

            - inversion Heqv; clear Heqv; subst; simpl in *; tcsp. }

        * inversion Heqw; clear Heqw; subst; simpl in *.
          apply in_broadcast2others in i; exrepnd; subst.
          left.
          eexists; eexists; reflexivity.

      + eapply IHpps in Heqx;[|eauto]; auto.
  Qed.

  Lemma update_state_new_view_returns_checkpoint :
    forall (slf  : Rep)
           (nv   : NewView)
           (st1 st2 : PBFTstate)
           (msgs : DirectedMsgs)
           (m    : DirectedMsg),
      update_state_new_view slf st1 nv = (st2, msgs)
      -> In m msgs
      -> (exists i c, m = MkDMsg i (PBFTcheckpoint c)).
  Proof.
    introv h i.
    unfold update_state_new_view in h.
    dest_cases w; symmetry in Heqw;[].
    dest_cases y; symmetry in Heqy;[|].

    - dest_cases z; subst; simpl in *;[|].

      + dest_cases x; symmetry in Heqx.
        inversion h; subst; clear h.
        unfold broadcast_checkpoint_op in i.
        dest_cases q; subst; simpl in *.
        apply in_broadcast2others in i; exrepnd; subst; simpl in *.
        exists o q; auto.

      + inversion h; subst; clear h; simpl in *; tcsp.

    - inversion h; subst; clear h; simpl in *; tcsp.
  Qed.

  (* replies are sent on receipt of check_ready messages *)
  Lemma send_reply_iff :
    forall (eo : EventOrdering) (e : Event) v t c i r a,
      In (send_reply (mk_reply v t c i r a)) (output_system_on_event_ldata PBFTsys eo e)
      <->
      (
        exists (n      : Rep)
               (cr     : CheckReady)
               (st st' : PBFTstate)
               (sns    : list SeqNum)
               (entry  : PBFTlogEntry)
               (reps   : list (option Reply))
               (smst   : PBFTsm_state)
               (lastr  : LastReplyState)
               (msgs   : DirectedMsgs),
          loc e = PBFTreplica n
          /\ trigger e = PBFTcheck_ready cr
          /\ state_sm_before_event (PBFTreplicaSM n) eo e = Some st
          /\ find_entry (log st) (next_to_execute st) = Some entry
          /\ reply2requests
               n
               (current_view st)
               (local_keys st)
               (log_entry2requests entry)
               (sm_state st)
               (last_reply_state st) = (reps, smst, lastr)
          /\ check_broadcast_checkpoint
               n
               (next_to_execute st)
               (current_view st)
               (local_keys st)
               (change_log_entry
                  (change_last_reply_state
                     (change_sm_state (increment_next_to_execute st) smst) lastr)
                  (add_replies2entry entry reps)) = (st', msgs)
          /\ ready st = next_to_execute st :: sns
          /\ In (mk_reply v t c i r a) (list_option2list reps)

      ).
  Proof.
    introv.
    rewrite in_output_system_on_event_ldata.
    split; intro h.

    - unfold PBFTsys in h.
      remember (loc e) as n; destruct n; simpl in *;
        unfold MStateMachine in *; ginv;
          [|apply MhaltedSM_output in h; tcsp];[].

      rw @loutput_sm_on_event_unroll2 in h; simpl in h.

      unfold PBFTreplica_update in h at 1; simpl in h.

      remember (trigger e) as trig; symmetry in Heqtrig.
      match goal with
      | [ H : context[option_map _ ?s] |- _ ] =>
        remember s as sop; symmetry in Heqsop; destruct sop; simpl in *; tcsp
      end.

      destruct trig; simpl in *; tcsp.

      + unfold PBFThandle_request in h; simpl in h.
        dest_all w.
        repndors; tcsp; ginv.

      + unfold PBFThandle_pre_prepare in h; simpl in *.
        dest_all w;[].

        apply in_app_iff in h; repndors;[|].

        * unfold check_broadcast_prepare in h.
          dest_all x.
          destruct x; simpl in *.
          fold DirectedMsgs in *.
          dest_all x.

        * apply in_app_iff in h;repndors;[|].

          { unfold check_broadcast_commit in h.
            dest_all x.
            destruct x; simpl in *.
            fold DirectedMsgs in *.
            dest_all x. }

          { match goal with
            | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
              eapply in_check_send_replies_implies in H;[|exact h]
            end.
            exrepnd; subst; simpl in *; ginv. }

      + unfold PBFThandle_prepare in h; simpl in *.
        dest_cases x; symmetry in Heqx; simpl in *;[].
        dest_cases y;[].
        dest_cases y; symmetry in Heqy; simpl in *;[].
        dest_cases z;[].
        dest_cases z; symmetry in Heqz; simpl in *;[].
        dest_cases w; symmetry in Heqw; simpl in *;[].
        dest_cases u; symmetry in Hequ; simpl in *;[].

        apply in_app_iff in h; repndors.

        { unfold check_broadcast_commit in h.
          destruct w0; simpl in *; tcsp;[].
          destruct g; simpl in *; tcsp;[].
          dest_cases d; symmetry in Heqd;[].
          dest_cases q; symmetry in Heqq; ginv;[|].

          { dest_cases t; simpl in *;[|].
            - apply in_broadcast2others in h; exrepnd; ginv.
            - apply in_broadcast2others in h; exrepnd; ginv. }

          { dest_cases t; simpl in *;[|].
            - apply in_broadcast2others in h; exrepnd; ginv.
            - apply in_broadcast2others in h; exrepnd; ginv. }
        }

        { eapply in_check_send_replies_implies in Hequ;[|exact h].
          exrepnd; subst; simpl in *; ginv. }

      + unfold PBFThandle_commit in h; simpl in *.
        dest_cases x; symmetry in Heqx; simpl in *;[].
        dest_cases y;[].
        dest_cases y; symmetry in Heqy; simpl in *;[].
        dest_cases z;[].
        dest_cases z; symmetry in Heqz; simpl in *;[].
        dest_cases w; symmetry in Heqw; simpl in *;[].
        dest_cases u; symmetry in Hequ; simpl in *;[].

        eapply in_check_send_replies_implies in Hequ;[|exact h].
        exrepnd; subst; simpl in *; ginv.

      + unfold PBFThandle_checkpoint in h.
        dest_cases x;[].
        dest_cases x; symmetry in Heqx; simpl in *;[].
        dest_cases y; symmetry in Heqy; simpl in *;[].
        dest_cases z; symmetry in Heqz; simpl in *;[].
        dest_cases w; symmetry in Heqw; simpl in *;[].
        dest_cases u; symmetry in Hequ; simpl in *;[].
        repndors; tcsp; ginv.

      + unfold PBFThandle_check_ready in h; simpl in *.
        dest_cases x; symmetry in Heqx; simpl in *;[].

        unfold find_and_execute_requests in Heqx.
        dest_cases w; symmetry in Heqw; repnd; ginv;[].

        unfold execute_requests in Heqw.
        remember (ready p) as rd; symmetry in Heqrd.
        destruct rd; [inversion Heqw; subst; simpl in *; tcsp|];[].

        dest_cases y; subst; simpl in *; tcsp;[|];
          [|inversion Heqw; subst; simpl in *; tcsp];[].

        dest_cases y; symmetry in Heqy; simpl in *; tcsp;[|];
          [|inversion Heqw; subst; simpl in *; tcsp];[].
        dest_cases u; symmetry in Hequ; repnd; simpl in *.
        dest_cases q; symmetry in Heqq.
        inversion Heqw; subst; clear Heqw; simpl in *.

        apply in_app_iff in h; simpl in *; repndors; ginv;[|].

        {
          apply in_map_iff in h; exrepnd.
          inversion h1; clear h1.
          remember (reply2client x) as cl.
          subst; simpl in *; GC.

          exists n c0 p w1 w0 y u2 u0 u1 q1.
          dands; auto.
        }

        {
          unfold check_broadcast_checkpoint in Heqq; simpl in *.
          dest_cases w; symmetry in Heqw; simpl in *; tcsp;[|].

          - dest_cases z; symmetry in Heqz; ginv.
            apply in_broadcast2others in h; exrepnd; ginv.

          - inversion Heqq; subst; simpl in *; tcsp.
        }

      + repndors; tcsp; ginv.

      + unfold PBFThandle_expired_timer in h.
        dest_cases x;[].
        dest_cases x; symmetry in Heqx; simpl in *;[].
        dest_cases y; symmetry in Heqy; simpl in *; tcsp;[|].

        * repnd; simpl in *.
          apply in_broadcast2others in h; exrepnd; ginv.

        * apply in_broadcast2others in h; exrepnd; ginv.

      + unfold PBFThandle_view_change in h.
        dest_cases x; simpl in *;[].
        dest_cases x; symmetry in Heqx; simpl in *;[].
        dest_cases y; symmetry in Heqy; simpl in *;[].
        dest_cases z; symmetry in Heqz; simpl in *;[].
        dest_cases q; symmetry in Heqq; simpl in *;[].
        repnd; simpl in *.
        dest_cases w; symmetry in Heqw; repnd; simpl in *;[].
        apply in_broadcast2others in h; exrepnd; ginv.

      + unfold PBFThandle_new_view in h.
        dest_cases x;[].
        dest_cases x; symmetry in Heqx; simpl in *;[].
        dest_cases y; symmetry in Heqy; simpl in *;[].
        dest_cases z; symmetry in Heqz; simpl in *;[].
        dest_cases w; symmetry in Heqw; simpl in *;[].
        dest_cases q; symmetry in Heqq; simpl in *;[].
        dest_cases u; symmetry in Hequ; simpl in *;[].
        dest_cases k; symmetry in Heqk; simpl in *;[].
        apply in_app_iff in h; repndors.

        * eapply add_prepares_to_log_from_new_view_pre_prepares_returns_prep_comm_rep in Hequ;[|exact h].
          repndors; exrepnd; ginv.

        * eapply update_state_new_view_returns_checkpoint in Heqk;[|eauto].
          exrepnd; ginv.

    - exrepnd.
      unfold PBFTsys.

      allrw; simpl.

      rw @loutput_sm_on_event_unroll2; simpl.

      unfold PBFTreplica_update at 1; simpl.
      allrw.
      fold DirectedMsgs in *.

      match goal with
      | [ |- context[option_map _ ?s] ] =>
        remember s as sop; symmetry in Heqsop; destruct sop; simpl in *; tcsp
      end;[].
      ginv.

      unfold PBFThandle_check_ready.
      unfold find_and_execute_requests.
      unfold execute_requests.
      allrw; simpl.

      dest_cases w.
      allrw; simpl.
      apply in_app_iff; simpl.

      left.
      apply in_map_iff; eexists; dands;[reflexivity|].
      auto.
  Qed.

  Definition hidden_check_broadcast_checkpoint
             (slf    : Rep)
             (sn     : SeqNum)
             (vn     : View)
             (keys   : local_key_map)
             (s      : PBFTstate)
             (s'     : PBFTstate)
             (msgs   : DirectedMsgs) : Prop
    := check_broadcast_checkpoint slf sn vn keys s = (s', msgs).

  Notation "'CHECK_BROADCAST_CHECKPOINT'" :=
    (hidden_check_broadcast_checkpoint _ _ _ _ _ _ _).

  Lemma hide_check_broadcast_checkpoint :
    forall slf sn vn keys s s' msgs,
      (check_broadcast_checkpoint slf sn vn keys s = (s', msgs))
      = hidden_check_broadcast_checkpoint slf sn vn keys s s' msgs.
  Proof. auto. Qed.

  Definition hidden_reply2requests
             (slf    : Rep)
             (view   : View)
             (keys   : local_key_map)
             (reqs   : list Request)
             (state  : PBFTsm_state)
             (lastr  : LastReplyState)
             (reps   : list (option Reply))
             (state' : PBFTsm_state)
             (lastr' : LastReplyState) : Prop
    := reply2requests slf view keys reqs state lastr = (reps, state', lastr').

  Notation "'REPLY2REQUESTS'" :=
    (hidden_reply2requests _ _ _ _ _ _ _ _ _).

  Lemma hide_reply2requests :
    forall slf view keys reqs state lastr reps state' lastr',
      (reply2requests slf view keys reqs state lastr = (reps, state', lastr'))
      = hidden_reply2requests slf view keys reqs state lastr reps state' lastr'.
  Proof. auto. Qed.

  Ltac hide_hyps :=
    repeat match goal with
           | [ H : check_broadcast_checkpoint _ _ _ _ _ = (_, _) |- _ ] =>
             rewrite hide_check_broadcast_checkpoint in H
           | [ H : reply2requests _ _ _ _ _ _ = (_, _, _) |- _ ] =>
             rewrite hide_reply2requests in H
           end.

  Ltac unhide_hyps :=
    repeat match goal with
           | [ H : hidden_check_broadcast_checkpoint _ _ _ _ _ _ _ |- _ ] =>
             rewrite <- hide_check_broadcast_checkpoint in H
           | [ H : hidden_check_broadcast_checkpoint _ _ _ _ _ _ _ _ _ |- _ ] =>
             rewrite <- hide_reply2requests in H
           end.

  Lemma in_reply2requests :
    forall slf view keys reqs state lastr rep reps state' lastr',
      reply2requests slf view keys reqs state lastr = (reps, state', lastr')
      -> In rep (list_option2list reps)
      ->
      exists (req : Request)
             (reqs1 reqs2 : list Request)
             (reps1 reps2 : list (option Reply))
             (state1 state2 : PBFTsm_state)
             (lastr1 lastr2 : LastReplyState),
        reqs = reqs1 ++ req :: reqs2
        /\ reply2requests slf view keys reqs1 state lastr = (reps1, state1, lastr1)
        /\ reply2request slf view keys req state1 lastr1 = (Some rep, state2, lastr2)
        /\ reply2requests slf view keys reqs2 state2 lastr2 = (reps2, state', lastr').
  Proof.
    induction reqs; introv e i; simpl in *; ginv; simpl in *; tcsp.
    dest_cases w; symmetry in Heqw; repnd.
    dest_cases y; symmetry in Heqy; repnd.
    ginv; simpl in *.
    dest_cases x; subst; simpl in *; repndors; subst; tcsp;[| |].

    - exists a ([] : list Request) reqs ([] : list (option Reply)) y2 state w0 lastr w1.
      simpl; dands; auto.

    - eapply IHreqs in Heqy;[|eauto]; clear IHreqs.
      exrepnd; subst.
      exists req (a :: reqs1) reqs2 (Some x :: reps1) reps2 state1 state2 lastr1 lastr2; simpl.
      allrw; simpl; dands; auto.

    - eapply IHreqs in Heqy;[|eauto]; clear IHreqs.
      exrepnd; subst.
      exists req (a :: reqs1) reqs2 (None :: reps1) reps2 state1 state2 lastr1 lastr2; simpl.
      allrw; simpl; dands; auto.
  Qed.

  Lemma eq_timestamps : forall t1 t2, timestamp2nat t1 = timestamp2nat t2 -> t1 = t2.
  Proof.
    introv; destruct t1, t2; simpl in *; auto.
  Qed.

  Lemma in_reply2request :
    forall slf view keys req state lastr rep state' lastr',
      reply2request slf view keys req state lastr = (Some rep, state', lastr')
      ->
      exists opr ts c entry result,
        request2info req = Some (opr, ts, c)
        /\ find_last_reply_entry_corresponding_to_client lastr c = Some entry
        /\ rep = reply (bare_reply view ts c slf result) (authenticate (PBFTmsg_bare_reply (bare_reply view ts c slf result)) keys)
        /\
        (
          (
            lre_timestamp entry < ts
            /\ PBFTsm_update c state opr = (result, state')
            /\ lastr' = update_last_reply_timestamp_and_result lastr c ts result
          )
          \/
          (
            lre_timestamp entry = ts
            /\ lre_reply entry = Some result
            /\ lastr' = lastr
            /\ state' = state
          )
        ).

  Proof.
    introv e.
    unfold reply2request in e.
    dest_all w;[|].

    - exists w0 w3 w2 w w1; dands; auto.

    - exists w0 w3 w2 w w5; dands; tcsp.
      right; dands; auto; try omega.
      apply eq_timestamps; omega.
  Qed.

  Lemma PBFTagreement :
    forall (eo : EventOrdering),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> internal_messages_were_sent_usys eo PBFTsys
      -> forall (e1 e2 : Event)
                (c     : Client)
                (t     : Timestamp)
                (v1 v2 : View)
                (i1 i2 : Rep)
                (r1 r2 : PBFTresult)
                (tok1 tok2 : Tokens),
        isCorrect e1
        -> isCorrect e2
        -> In (send_reply (mk_reply v1 t c i1 r1 tok1)) (output_system_on_event_ldata PBFTsys eo e1)
        -> In (send_reply (mk_reply v2 t c i2 r2 tok2)) (output_system_on_event_ldata PBFTsys eo e2)
        -> r1 = r2.
  Proof.
    introv sentbyz sentint isCor1 isCor2 send1 send2.

    destruct (PBFTresdeq r1 r2) as [d|d]; auto.
    assert False; tcsp.

    (* replies are sent in response to check-ready messages *)
    apply send_reply_iff in send1.
    apply send_reply_iff in send2.
    exrepnd.

    repeat match goal with
           | [ H : reply2requests _ _ _ _ _ _ = _ |- _ ] =>
             eapply in_reply2requests in  H;[|eauto];[]
           end.
    exrepnd.

    match goal with
    | [ H : reply2request _ _ _ _ _ _ = _ |- _ ] => apply in_reply2request in H
    end.

    SearchAbout reply2requests.

  (*
    hide_hyps.

    pose proof (sentint e2) as q.
    match goal with
    | [ H1 : trigger ?e = _ , H2 : context[is_internal_message (trigger ?e)] |- _ ] =>
      rewrite H1 in H2
    end.
    repeat (autodimp q hyp);[].
    exrepnd.
*)


  Qed.
*)

End PBFTagreement.
