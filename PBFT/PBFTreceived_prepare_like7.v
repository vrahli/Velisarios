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


Require Export PBFTreceived_prepare_like1.
Require Export Received_or_generated.


Section PBFTreceived_prepare_like7.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.

    Lemma check_send_replies_update_preserves_view_change_state :
    forall slf view keys entryop state sn msgs state' L,
      check_send_replies slf view keys entryop (update_log state L) sn = (msgs, state')
      -> view_change_state state' = view_change_state state.
  Proof.
    introv H; eapply check_send_replies_preserves_view_change_state in H; eauto.
  Qed.
  Hint Resolve check_send_replies_update_preserves_view_change_state : pbft.

  Lemma check_send_replies_view_change_somewhere_in_log_view_change_state :
    forall slf view keys entryop state sn msgs state' L vc,
      check_send_replies slf view keys entryop (update_log state L) sn = (msgs, state')
      -> view_change_somewhere_in_log vc (view_change_state state')
      -> view_change_somewhere_in_log vc (view_change_state state).
  Proof.
    introv check h.
    eapply check_send_replies_update_preserves_view_change_state in check. allrw <-. auto.
  Qed.
  Hint Resolve check_send_replies_view_change_somewhere_in_log_view_change_state : pbft.

  Lemma find_and_execute_requests_view_change_somewhere_in_log :
    forall slf view keys msg state state' vc,
      find_and_execute_requests slf view keys state = (msg, state')
      -> view_change_somewhere_in_log vc (view_change_state state')
      -> view_change_somewhere_in_log vc (view_change_state state).
  Proof.
    introv find h.
    eapply  find_and_execute_preserves_view_change_state in find. allrw <-. auto.
  Qed.
  Hint Resolve find_and_execute_requests_view_change_somewhere_in_log : pbft.

  Lemma view_changes_are_received_or_created :
    forall (eo : EventOrdering) vc i,
      received_or_generated
        eo
        (PBFTreplicaSM i)
        (fun e st => PBFTreceived_prepare_like1.view_change_somewhere_in_log vc (view_change_state st))
        (fun e' st1 st2 e st =>
           verify_view_change i (local_keys st1) vc = true
           /\ event_triggered_by_message e' (PBFTview_change vc))
        (fun e' st1 st2 e st =>
           ((exists c, event_triggered_by_message e' (PBFTcheck_bcast_new_view c))
            \/ (exists t, event_triggered_by_message e' (PBFTexpired_timer t)))
           /\
           forall pl pi,
             In pi (view_change2prep vc)
             -> prepare_like_in_prepared_info pl pi
             -> prepare_like_in_log pl (log st1)).
  Proof.
    intros eo c i e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv eqst vcinlog.

    try (rewrite loc_local_pred in ind).

    dup eqst as eqst_At_e; hide_hyp eqst_At_e.
    rewrite state_sm_on_event_unroll2 in eqst.

    match goal with
    | [ H : context[map_option _ ?s] |- _ ] =>
      remember s as sop; symmetry in Heqsop; destruct sop; simpl in *;[|ginv];op_st_some m eqtrig
    end.

    unfold PBFTreplica_update in eqst.

    destruct m;
      simpl in *; ginv; subst; tcsp;
        try smash_handlers; try (smash_pbft_ind ind).

    {
      (* check-bcast_new_view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with check_broadcast_new_view check.

      apply CheckBCastNewView2entry_some_implies in cb.

      apply update_state_new_view_preserves_view_change_state in upd; simpl in *.
      rewrite upd in vcinlog; clear upd.

      apply view_change_somewhere_in_log_log_new_view_and_entry_implies in vcinlog;
        repndors;[try (smash_pbft_ind ind)|];[].

      unfold check_broadcast_new_view in check; smash_pbft;[].
      unfold view_changed_entry in *; smash_pbft;[].

      rename_hyp_with create_new_prepare_messages cr.
      simpl in *; smash_pbft; repndors;
        [|eapply in_vce_view_changes_implies_in_view_change_somewhere_in_log in vcinlog;
          [|eauto];try (smash_pbft_ind ind)];[].

      subst.
      rewrite view_change2prep_refresh_view_change.

      exists e p st; dands; eauto 2 with eo.
      right; dands; eauto 2 with pbft; try (complete (left; dands; eauto)).
    }

    {
      (* expired-timer *)

      rename_hyp_with start_view_change start.
      eapply start_view_change_preserves_view_change_somewhere_in_log in start;[|eauto].
      repndors;[try (smash_pbft_ind ind)|];[].

      subst; simpl in *.

      exists e p; eexists; dands; eauto 2 with eo.
      right; dands; eauto 2 with pbft; try (complete (right; dands; eauto));[].
      introv a b.
      rewrite view_change2prep_mk_current_view_change in a; eauto 2 with pbft.
    }

    {
      (* view-change *)

      rename_hyp_with add_other_view_change add.
      eapply PBFTreceived_prepare_like1.add_other_view_change_preserves_view_change_somewhere_in_log in add;[|eauto].
      repndors; subst;[try (smash_pbft_ind ind)|];[].
      exists e p; eexists; dands; eauto 2 with eo; tcsp.
    }

    {
      (* new-view *)

      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with update_state_new_view upd.

      apply add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state in add; simpl in *.
      apply update_state_new_view_preserves_view_change_state in upd; simpl in *.
      rewrite upd in vcinlog; clear upd.
      rewrite add in vcinlog; clear add.

      rewrite view_change_somewhere_in_log_new_view_iff in vcinlog.
      try (smash_pbft_ind ind).
    }
  Qed.

End PBFTreceived_prepare_like7.
