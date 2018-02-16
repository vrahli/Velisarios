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
Require Export PBFTgarbage_collect.


Section PBFT_A_1_2_3.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  (* see Invariant A.1.2 (3) in PBFT PhD p.145 *)
  Lemma PBFT_A_1_2_3 :
    forall (eo : EventOrdering)
           (e       : Event)
           (slf     : Rep)
           (n       : SeqNum)
           (v       : View)
           (a       : Tokens)
           (d       : PBFTdigest)
           (rs      : list Request)
           (state   : PBFTstate),
      state_sm_on_event (PBFTreplicaSM slf) e = Some state
      -> pre_prepare_in_log (mk_pre_prepare v n rs a) d (log state) = true
      -> is_primary v slf = true
      -> n <= (sequence_number (primary_state state)).
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers3 smash_pbft_ind3.

    {
      (* request *)

      rename_hyp_with check_new_request check.
      rename_hyp_with add_new_pre_prepare2log add.

      applydup check_new_request_sequence_number_increases in check.
      apply pre_prepare_in_log_add_new_prepare2log in add; repndors; try (smash_pbft_ind ind).

      repnd.
      unfold mk_auth_pre_prepare, mk_pre_prepare in add0; ginv.
    }

    {
      (* pre-prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_pre_prepare_and_prepare2log add.

      applydup check_send_replies_preserves_sequence_number in check; simpl in *.
      rewrite check0; clear check0.

      eapply check_send_replies_preserves_pre_prepare_in_log in check;[|eauto]; simpl in *.

      eapply add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log in add;[|eauto].

      repndors; try (smash_pbft_ind ind).
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_prepare2log add.

      applydup check_send_replies_preserves_sequence_number in check; simpl in *.
      rewrite check0; clear check0.

      eapply check_send_replies_preserves_pre_prepare_in_log in check;[|eauto]; simpl in *.

      eapply add_new_prepare2log_preserves_pre_prepare_in_log in add;[|eauto].

      try (smash_pbft_ind ind).
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_commit2log add.

      applydup check_send_replies_preserves_sequence_number in check; simpl in *.
      rewrite check0; clear check0.

      eapply check_send_replies_preserves_pre_prepare_in_log in check;[|eauto]; simpl in *.

      eapply add_new_commit2log_preserves_pre_prepare_in_log in add.
      rewrite add in check; clear add.

      try (smash_pbft_ind ind).
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.

      applydup find_and_execute_requests_decrement_requests_in_progress_sequence_number_increases in fexec.
      eapply find_and_execute_requests_preserves_pre_prepare_in_log in fexec;[|eauto].

      assert (n <= sequence_number (primary_state p)) as q by (smash_pbft_ind ind).
      omega.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with check_broadcast_new_view check.

      applydup update_state_new_view_preserves_sequence_number in upd.
      simpl in *.
      rewrite upd0; clear upd0.

      eapply update_state_new_view_preserves_pre_prepare_in_log in upd;
        [| |eauto]; simpl in *; eauto 4 with pbft;[].

      apply pre_prepare_in_log_log_pre_prepares_implies in upd.
      repndors; repnd; try (smash_pbft_ind ind).

      applydup check_broadcast_new_view_some_implies in check; exrepnd.
      eapply (view_changed_entry_some_and_check_broadcast_new_view_implies_le n) in check;[| |eauto]; eauto 2 with pbft.

      subst; simpl in *.

      allrw in_app_iff; repndors.

      - eapply o_pre_prepare_in_create_new_prepare_messages_implies in check6;[|eauto].
        exrepnd.
        apply create_new_prepare_message_implies_same_sequence_number in check0; simpl in *; subst; auto.

      - eapply n_pre_prepare_in_create_new_prepare_messages_implies in check6;[|eauto].
        exrepnd.
        apply create_new_prepare_message_implies_same_sequence_number in check0; simpl in *; subst; auto.
    }

    { (* new view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      applydup update_state_new_view_preserves_sequence_number in upd.
      simpl in *.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      eapply update_state_new_view_preserves_pre_prepare_in_log in upd;[| |eauto];simpl;auto;[].
      simpl in *.

      applydup add_prepares_to_log_from_new_view_pre_prepares_sequence_number_increases in add; simpl in *.
      rewrite upd0; clear upd0.
      eapply le_trans;[|eauto]; clear add0.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log in add;[|eauto].
      simpl in *; autorewrite with pbft in *.

      repndors;[try (smash_pbft_ind ind)|];[].

      exrepnd; subst; simpl in *.
      allrw in_map_iff; exrepnd.
      unfold add_digest in *; ginv.
      allrw in_app_iff; repndors; simpl in *.

      - destruct v0, v0; simpl in *.
        unfold correct_new_view in *; smash_pbft.

        match goal with
        | [ H : forallb _ OP = _ |- _] =>
          erewrite forallb_forall in H;
            pose proof (H (mk_pre_prepare v n rs a)) as tt; clear H;
              autodimp tt hyp
        end.

        unfold correct_new_view_opre_prepare_op, correct_new_view_opre_prepare in *.
        smash_pbft.

      - destruct v0, v0; simpl in *.
        unfold correct_new_view in *; smash_pbft.

        match goal with
        | [ H : forallb _ NP = _ |- _] =>
          erewrite forallb_forall in H;
            pose proof (H (mk_pre_prepare v n rs a)) as tt; clear H;
              autodimp tt hyp
        end.

        unfold correct_new_view_npre_prepare_op, correct_new_view_npre_prepare in *.
        smash_pbft.
    }
  Qed.
  Hint Resolve PBFT_A_1_2_3 : pbft.

  Lemma PBFT_A_1_2_3_before :
    forall (eo : EventOrdering)
           (e       : Event)
           (slf     : Rep)
           (n       : SeqNum)
           (v       : View)
           (a       : Tokens)
           (d       : PBFTdigest)
           (rs      : list Request)
           (state   : PBFTstate),
      state_sm_before_event (PBFTreplicaSM slf) e = Some state
      -> pre_prepare_in_log (mk_pre_prepare v n rs a) d (log state) = true
      -> is_primary v slf = true
      -> n <= (sequence_number (primary_state state)).
  Proof.
    introv eqst prep isprim.

    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in eqst.
    destruct (dec_isFirst e) as [di|di]; ginv; eauto 3 with pbft.
  Qed.
  Hint Resolve PBFT_A_1_2_3_before : PBFT.

End PBFT_A_1_2_3.


Hint Resolve PBFT_A_1_2_3 : pbft.
Hint Resolve PBFT_A_1_2_3_before : PBFT.
