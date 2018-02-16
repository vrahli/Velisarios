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


Require Export PBFTreceived_prepare_like3.
Require Export PBFTreceived_prepare_like4.
Require Export PBFTreceived_prepare_like5.
Require Export PBFTreceived_prepare_like6.
Require Export PBFTreceived_prepare_like7.
Require Export PBFTlearns_or_knows_pl.
Require Export PBFTdelay_of_send_prepares.
Require Export PBFTdelay_of_send_pre_prepares.
Require Export PBFTdelay_of_send_view_changes.
Require Export PBFTdelay_of_send_new_views.


Section PBFTreceived_prepare_like8.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma prepare_like_received_from_correct_replica_was_in_log :
    forall (eo : EventOrdering) (e : Event) good pl i,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> node_has_correct_trace_before e good
      -> prepare_like2sender pl = good
      -> verify_main_prepare_like i (keys e) pl = true
      -> auth_data_in_trigger (prepare_like2main_auth_data pl) e
      ->
      exists e' st,
        e' ≺ e
        /\ loc e' = PBFTreplica good
        /\ state_sm_on_event (PBFTreplicaSM good) e' = Some st
        /\ prepare_like_in_log pl (log st).
  Proof.
    introv sendbyz ckeys.
    revert e good pl i.
    induction e as [? ind] using HappenedBeforeInd;[].
    introv eqloc cortrace goodprep verif iauth.

    apply implies_authenticated_messages_were_sent_non_byz_usys in sendbyz.
    dup iauth as sb.
    apply (sendbyz _ _ (PBFTreplica good)) in sb; auto;
      try rewrite eqloc in *; eauto 3 with pbft;
        try (complete (simpl; subst; autorewrite with pbft; eauto 3 with pbft));[].

    exrepnd; simpl in *.

    (* WARNING *)
    clear sb2.
    clear iauth.
    clear verif.

    applydup prepare_like2main_auth_data_in_get_contained_auth_data_implies in sb3.

    repndors; exrepnd; subst m; simpl in *; autodimp sb4 hyp; repndors; tcsp;
      try (complete (apply prepare_like2main_auth_data_not_in_pre_prepare2auth_data_req in sb3; tcsp));
      [| | |].

    - (* prepare *)

      apply prepare2auth_data_equal_prepare_like2main_auth_data_implies in sb3.
      subst pl.
      simpl in *.

      pose proof (PBFTnever_stops_on_event eo e' good) as q.
      repeat (autodimp q hyp); eauto 3 with pbft eo.
      exrepnd.

      rename_hyp_with @output_system_on_event_ldata sendprep.
      apply send_prepare_no_delay in sendprep.
      eapply send_prepares_are_in_log in sendprep;[| |eauto]; auto;[].

      exists e' st.
      dands; auto; eauto 3 with pbft.

    - (* pre-prepare *)

      apply pre_prepare_data2auth_data_pre_equal_prepare_like2main_auth_data_implies in sb3.
      subst pl.
      simpl in *.

      pose proof (PBFTnever_stops_on_event eo e' good) as q.
      repeat (autodimp q hyp); eauto 3 with pbft eo.
      exrepnd.

      rename_hyp_with @output_system_on_event_ldata sendprep.
      apply send_pre_prepare_no_delay in sendprep.
      eapply send_pre_prepares_are_in_log in sendprep;[| |eauto]; auto;[].

      exists e' st.
      dands; auto; eauto 3 with pbft.

    - (* view-change *)

      apply prepare_like2main_auth_data_in_view_change2auth_data_implies in sb3.
      destruct sb3 as [pi pip]; repnd.

      pose proof (PBFTnever_stops_on_event eo e' good) as q.
      repeat (autodimp q hyp); eauto 3 with pbft eo.
      exrepnd.

      rename_hyp_with @output_system_on_event_ldata sendvc.
      apply send_view_change_no_delay in sendvc.
      eapply prepare_like_of_send_view_change_are_in_log in sendvc;
        [| |eauto|eauto|eauto];auto;[].

      exists e' st; dands; auto.

    - (* new_view *)

      pose proof (PBFTnever_stops_on_event eo e' good) as q.
      repeat (autodimp q hyp); eauto 3 with pbft eo.
      exrepnd.

      rename_hyp_with @output_system_on_event_ldata sendprep.
      apply send_new_view_no_delay in sendprep.
      eapply prepare_like_of_send_new_view_are_in_log in sendprep;
        [| | |]; eauto.
      repndors;[exists e' st; dands; auto|];[].
      exrepnd.

      rename_hyp_with view_change_somewhere_in_log vcinlog.
      dup vcinlog as vcinlog_backup.
      eapply view_changes_are_received_or_created in vcinlog;[eauto|eauto 2 with pbft];[].
      exrepnd.

      applydup localLe_implies_loc in vcinlog1.

      (* either the view-change message was received or it was created *)
      repndors; exrepnd;[|].

      + (* the view-change messages was received *)

        pose proof (ind e'0) as q; clear ind; autodimp q hyp; eauto 3 with eo;[].
        pose proof (q good pl good) as h; clear q.
        repeat (autodimp h hyp); eauto 3 with pbft eo;
          [allrw;auto| | |];
          [|unfold auth_data_in_trigger;allrw;simpl;eauto 2 with pbft|];
          [|exrepnd; exists e'1 st0; dands; eauto 4 with eo];[].

        assert (e'0 ≺ e) as caus by eauto 4 with eo.
        pose proof (ckeys e'0 good st1) as eqkeys; autodimp eqkeys hyp; eauto 3 with eo pbft.
        rewrite eqkeys; clear eqkeys; eauto 2 with pbft.

      + (* the view-change messages was create *)

        pose proof (vcinlog0 pl pi) as prep; repeat (autodimp prep hyp).
        rewrite state_sm_before_event_as_state_sm_on_event_pred in vcinlog2;[|eauto 2 with pbft];[].
        exists (local_pred e'0) st1; dands; eauto 4 with eo pbft.
        rewrite loc_local_pred; allrw;auto.
  Qed.

  Lemma pbft_learns_if_knows_prepare_like :
    forall (eo : EventOrdering),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> learns_if_knows eo.
  Proof.
    introv sendauth ckeys l ctrace.
    unfold learns in *; exrepnd; simpl in *.
    unfold pbft_pl_verify in *; exrepnd; simpl in *.

    rewrite l1 in *.
    rewrite verify_authenticated_data_iff_verify_main_prepare_like in l0.
    pose proof (prepare_like_received_from_correct_replica_was_in_log
                  eo e (prepare_like2sender d) d n) as q.
    repeat (autodimp q hyp); eauto 3 with eo pbft;[].

    exrepnd.
    exists e'; dands; auto.
    exists st; eexists; dands; eauto.
  Qed.
  Hint Resolve pbft_learns_if_knows_prepare_like : pbft.

End PBFTreceived_prepare_like8.


Hint Resolve pbft_learns_if_knows_prepare_like : pbft.
