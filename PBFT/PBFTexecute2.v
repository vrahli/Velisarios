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


Require Export PBFTexecute.


Section PBFTexecute2.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma check_send_update_log_replies_preserves_next_to_execute :
    forall slf view keys giop state n msgs state' L,
      check_send_replies slf view keys giop (update_log state L) n = (msgs, state')
      -> next_to_execute state' = next_to_execute state.
  Proof.
    introv check; eapply check_send_replies_preserves_next_to_execute in check; allrw <-; auto.
  Qed.
  Hint Resolve check_send_update_log_replies_preserves_next_to_execute : pbft.

  Lemma next_to_execute_is_greater_than_one :
    forall i (eo : EventOrdering) (e : Event) st,
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> 1 <= next_to_execute st.
  Proof.
    intros i eo e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv eqst.

    dup eqst as eqst_At_e.
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
      (* pre-prepare *)

      rename_hyp_with check_send_replies check.
      applydup check_send_update_log_replies_preserves_next_to_execute in check as eqnext. subst.
      try (smash_pbft_ind ind).
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.
      applydup check_send_update_log_replies_preserves_next_to_execute in check as eqnext; subst.
      try (smash_pbft_ind ind).
    }

    {
      (* commit *)
      rename_hyp_with check_send_replies check.
      applydup check_send_update_log_replies_preserves_next_to_execute in check as eqnext; subst.
      try (smash_pbft_ind ind).
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.
      autorewrite with pbft in *.
      applydup find_and_execute_requests_preserves_next_to_execute2 in fexec.
      repndors; repnd;[try rewrite fexec1; try (smash_pbft_ind ind)|].

      exrepnd.
      rewrite fexec3 in *.
      unfold next_seq; simpl; omega.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with update_state_new_view upd.

      applydup update_state_new_view_preserves_next_to_execute in upd;
        simpl;[|eauto 2 with pbft|eauto 4 with pbft];[].
      simpl in *; autorewrite with pbft in *.

      exrepnd; repndors; repnd;
        [|rewrite upd5; try (smash_pbft_ind ind)
         |rewrite upd4; try (smash_pbft_ind ind)];[].
      rewrite upd5.
      unfold next_seq; simpl; omega.
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with correct_new_view cor.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_next_to_execute in add.
      simpl in *.

      applydup update_state_new_view_preserves_next_to_execute in upd;
        simpl;[|eauto 2 with pbft|eauto 4 with pbft];[].
      simpl in *; autorewrite with pbft in *.

      exrepnd; repndors; repnd;
        [|assert (1 <= next_to_execute p) as xx by (smash_pbft_ind ind); congruence
         |assert (1 <= next_to_execute p) as xx by (smash_pbft_ind ind); congruence];[].
      rewrite upd6.
      unfold next_seq; simpl; omega.
    }
  Qed.
  Hint Resolve next_to_execute_is_greater_than_one : pbft.

  Lemma next_to_execute_is_greater_than_one_before :
    forall i (eo : EventOrdering) (e : Event) st,
      state_sm_before_event (PBFTreplicaSM i) e = Some st
      -> 1 <= next_to_execute st.
  Proof.
    introv eqst.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d|d]; ginv; subst; simpl in *; try omega; eauto 3 with pbft.
  Qed.
  Hint Resolve next_to_execute_is_greater_than_one_before : pbft.

  Lemma state_if_initial_next_to_execute :
    forall i (eo : EventOrdering) (e : Event) st,
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> next_to_execute st = 1 (* initial one is 1 *)
      -> sm_state st = PBFTsm_initial_state
         /\ last_reply_state st = initial_last_reply.
  Proof.
    intros i eo e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv eqst next.

    dup eqst as eqst_At_e.
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
      (* pre-prepare *)

      rename_hyp_with check_send_replies check.
      applydup check_send_replies_preserves_next_to_execute in check as eqnext; simpl in *.
      applydup check_send_replies_preserves_sm_state in check as eqsm; simpl in *.
      applydup check_send_replies_preserves_last_reply_state in check as eqlast; simpl in *.
      allrw.
      try (smash_pbft_ind ind).
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.
      applydup check_send_replies_preserves_next_to_execute in check as eqnext; simpl in *.
      applydup check_send_replies_preserves_sm_state in check as eqsm; simpl in *.
      applydup check_send_replies_preserves_last_reply_state in check as eqlast; simpl in *.
      allrw.
      try (smash_pbft_ind ind).
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      applydup check_send_replies_preserves_next_to_execute in check as eqnext; simpl in *.
      applydup check_send_replies_preserves_sm_state in check as eqsm; simpl in *.
      applydup check_send_replies_preserves_last_reply_state in check as eqlast; simpl in *.
      allrw.
      try (smash_pbft_ind ind).
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.
      autorewrite with pbft in *.
      applydup find_and_execute_requests_preserves_next_to_execute2 in fexec.
      repndors; repnd;[try rewrite fexec1 in next; try (smash_pbft_ind ind)|].

      exrepnd.
      rewrite fexec3 in *.

      apply next_to_execute_is_greater_than_one_before in Heqsop; auto.
      unfold next_seq in *; simpl in *.
      remember (next_to_execute p) as m.
      destruct m; simpl in *; inversion next; subst; omega.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with update_state_new_view upd.

      apply CheckBCastNewView2entry_some_implies in cb.
      applydup update_state_new_view_preserves_wf in upd; simpl;[|eauto 4 with pbft];[].
      applydup wf_view_change_state_implies_all_entries in cb;[|eauto 3 with pbft];[].

      applydup update_state_new_view_preserves_next_to_execute in upd;
        simpl;[|eauto 2 with pbft|eauto 4 with pbft];[].
      simpl in *; autorewrite with pbft in *.

      exrepnd; repndors; repnd;
        [|allrw; try (smash_pbft_ind ind)
         |allrw; try (smash_pbft_ind ind)];[].

      apply next_to_execute_is_greater_than_one_before in Heqsop; auto.
      rewrite next in *.
      unfold next_seq in *; simpl in *.
      destruct maxV as [m]; simpl in *.
      inversion upd6; destruct m; try omega.
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with correct_new_view cor.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_next_to_execute in add.
      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_sm_state in add.
      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_last_reply_state in add.
      applydup PBFTnew_view_in_log.add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state in add as eqvcs.
      simpl in *.

      applydup update_state_new_view_preserves_next_to_execute in upd;
        simpl;[|eauto 2 with pbft|eauto 4 with pbft];[].
      simpl in *; autorewrite with pbft in *.

      exrepnd; repndors; repnd;
        [|allrw; try (smash_pbft_ind ind)
         |allrw; try (smash_pbft_ind ind)];[].

      apply next_to_execute_is_greater_than_one_before in Heqsop; auto.
      rewrite next in *.
      unfold next_seq in *; simpl in *.
      destruct maxV as [m]; simpl in *.
      inversion upd6; destruct m; try omega.
    }
  Qed.

End PBFTexecute2.


Hint Resolve next_to_execute_is_greater_than_one : pbft.
Hint Resolve next_to_execute_is_greater_than_one_before : pbft.
