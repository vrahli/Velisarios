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
Require Export PBFTwf_view_change_state.
Require Export PBFTordering.
Require Export PBFTprops4.
Require Export PBFTnew_view_in_log.


Section PBFT_A_1_2_5.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.



  (* Invariant A.1.2 (5) in PBFT PhD p.145 *)
  Lemma PBFT_A_1_2_5 :
    forall (eo      : EventOrdering)
           (e       : Event)
           (nv      : NewView)
           (slf     : Rep)
           (state   : PBFTstate),
      state_sm_on_event (PBFTreplicaSM slf) e = Some state
      -> new_view_in_log nv (view_change_state state)
      -> correct_new_view nv = true.
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers3 smash_pbft_ind3.

    {
      (* check-bcast-new-view *)

      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with update_state_new_view upd.

      applydup CheckBCastNewView2entry_some_implies in cb.
      eapply update_state_new_view_preserves_new_view_in_log in upd;[|eauto].
      simpl in *.
      apply log_new_view_and_entry_preserves_new_view_in_log in upd;
        repndors; subst; tcsp; smash_pbft; try (smash_pbft_ind ind).

      symmetry;eapply check_broadcast_new_view_implies_equal_views;[|eauto];
        eauto 3 with pbft.
    }

    {
      (* new-view *)

      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with update_state_new_view upd.
      rename_hyp_with new_view_in_log nvi.

      eapply update_state_new_view_preserves_new_view_in_log in nvi;[|eauto].
      simpl in *.

      match goal with
      | [ H : new_view_in_log _ (log_new_view _ _) |- _ ] =>
        apply log_new_view_preserves_new_view_in_log in H
      end.

      repndors;[|subst;auto];[].

      apply add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state in add.
      simpl in *.
      rewrite add in *.
      try (smash_pbft_ind ind).
    }
  Qed.
  Hint Resolve PBFT_A_1_2_5 : pbft.

  Lemma PBFT_A_1_2_5_before :
    forall (eo      : EventOrdering)
           (e       : Event)
           (nv      : NewView)
           (slf     : Rep)
           (state   : PBFTstate),
      state_sm_before_event (PBFTreplicaSM slf) e = Some state
      -> new_view_in_log nv (view_change_state state)
      -> correct_new_view nv = true.
  Proof.
    introv eqst nview.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d|d]; ginv; subst; simpl in *; tcsp; eauto 3 with pbft.
  Qed.
  Hint Resolve PBFT_A_1_2_5_before : pbft.

End PBFT_A_1_2_5.


Hint Resolve PBFT_A_1_2_5 : pbft.
Hint Resolve PBFT_A_1_2_5_before : pbft.
