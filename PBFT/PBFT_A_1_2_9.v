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


Require Export PBFTwell_formed_log.
Require Export PBFTpre_prepare_in_log_preserves.
Require Export PBFTordering.
Require Export PBFTprops3.
Require Export PBFTprops5.
Require Export PBFTgarbage_collect.


Section PBFT_A_1_2_9.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  (* see Invariant A.1.2 (9) in PBFT PhD p.145 *)
  Lemma PBFT_A_1_2_9 :
    forall (eo : EventOrdering)
           (e       : Event)
           (slf     : Rep)
           (pp      : Pre_prepare)
           (d       : PBFTdigest)
           (state   : PBFTstate),
      state_sm_on_event (PBFTreplicaSM slf) e = Some state
      -> pre_prepare_in_log pp d (log state) = true
      -> pre_prepare2view pp <= current_view state.
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers3 smash_pbft_ind3.

    {
      (* requests *)

      rename_hyp_with pre_prepare_in_log prep.
      apply pre_prepare_in_log_add_new_prepare2log in prep.
      repndors; repnd; try (smash_pbft_ind ind).
      subst; simpl in *; auto.
    }

    {
      (* pre-prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with pre_prepare_in_log prep.

      applydup check_send_replies_update_log_preserves_current_view in check.
      rewrite check0.
      eapply check_send_replies_preserves_pre_prepare_in_log in check;[|eauto].
      simpl in *.

      match goal with
      | [ H : context[add_new_pre_prepare_and_prepare2log] |- _ ] => rename H into add
      end.
      eapply add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log in add;
        [|eauto].
      repndors; repnd; subst; simpl in *; try (smash_pbft_ind ind); ginv.
    }

    {
      (* prepare *)

      match goal with
      | [ H : context[check_send_replies] |- _ ] => rename H into check
      end.
      applydup check_send_replies_update_log_preserves_current_view in check.
      rewrite check0.
      eapply check_send_replies_preserves_pre_prepare_in_log in check;[|eauto].
      simpl in *.

      match goal with
      | [ H : context[add_new_prepare2log] |- _ ] => rename H into add
      end.
      eapply add_new_prepare2log_preserves_pre_prepare_in_log in add;
        [|eauto].
      repndors; repnd; subst; simpl in *; try (smash_pbft_ind ind).
    }

    {
      (* commit *)

      match goal with
      | [ H : context[check_send_replies] |- _ ] => rename H into check
      end.
      applydup check_send_replies_update_log_preserves_current_view in check.
      rewrite check0.
      eapply check_send_replies_preserves_pre_prepare_in_log in check;[|eauto].
      simpl in *.

      match goal with
      | [ H : context[add_new_commit2log] |- _ ] => rename H into add
      end.
      eapply add_new_commit2log_preserves_pre_prepare_in_log in add.
      rewrite add in check.
      repndors; repnd; subst; simpl in *; try (smash_pbft_ind ind).
    }

    {
      (* check-ready *)

      match goal with
      | [ H : context[find_and_execute_requests] |- _ ] => rename H into find
      end.
      applydup find_and_execute_requests_preserves_current_view in find.
      rewrite find0.
      eapply find_and_execute_requests_preserves_pre_prepare_in_log in find;[|eauto].

      try (smash_pbft_ind ind).
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with update_state_new_view upd.

      applydup update_state_new_view_preserves_current_view in upd.
      simpl in upd0; rewrite upd0; clear upd0.

      eapply update_state_new_view_preserves_pre_prepare_in_log in upd;[| |eauto];
        simpl in *; eauto 4 with pbft.

      apply pre_prepare_in_log_log_pre_prepares_implies in upd.
      repndors; repnd.

      { eapply le_trans;[|apply le_max_view_left].
        try (smash_pbft_ind ind). }

      match goal with
      | [ H : context[check_broadcast_new_view] |- _ ] => rename H into check
      end.
      eapply check_broadcast_new_view_preserves_view in check;[|eauto].
      allrw <- .
      apply le_max_view_right.
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      applydup update_state_new_view_preserves_current_view in upd.
      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_current_view in add.
      simpl in *.
      rewrite upd1; clear upd1.
      rewrite add1; clear add1.

      eapply update_state_new_view_preserves_pre_prepare_in_log in upd;[| |eauto];simpl;auto;[].
      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log in add;[|eauto].
      simpl in *; autorewrite with pbft in *.

      repndors;[|].

      {
        assert (pre_prepare2view pp <= current_view p) as q by (smash_pbft_ind ind).
        eapply le_trans;[exact q|].
        apply le_max_view_left.
      }

      {
        exrepnd; subst; simpl in *.
        apply pre_prepare_in_map_correct_new_view_implies2 in add1; simpl in *; auto.
        rewrite add1.
        apply le_max_view_right.
      }
    }
  Qed.
  Hint Resolve PBFT_A_1_2_9 : pbft.

  Lemma PBFT_A_1_2_9_before :
    forall (eo : EventOrdering)
           (e       : Event)
           (slf     : Rep)
           (pp      : Pre_prepare)
           (d       : PBFTdigest)
           (state   : PBFTstate),
      state_sm_before_event (PBFTreplicaSM slf) e = Some state
      -> pre_prepare_in_log pp d (log state) = true
      -> pre_prepare2view pp <= current_view state.
  Proof.
    introv eqst prep.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d1|d1]; ginv; subst; simpl in *;[].
    eauto 3 with pbft.
  Qed.
  Hint Resolve PBFT_A_1_2_9_before : pbft.

End PBFT_A_1_2_9.


Hint Resolve PBFT_A_1_2_9 : pbft.
Hint Resolve PBFT_A_1_2_9_before : pbft.
