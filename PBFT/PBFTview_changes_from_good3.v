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


Require Export PBFTview_changes_from_good1.


Section PBFTview_changes_from_good3.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma view_of_own_view_changes :
    forall (eo : EventOrdering) (e : Event) i st vc,
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> own_view_change_in_log vc (view_change_state st)
      -> view_change2view vc <= current_view st.
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers3 smash_pbft_ind3.

    {
      (* check-bcast_new_view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with own_view_change_in_log vcinlog.

      apply CheckBCastNewView2entry_some_implies in cb.

      applydup update_state_new_view_preserves_current_view in upd as xx; simpl in *.
      rewrite xx; clear xx.
      apply update_state_new_view_preserves_view_change_state in upd; simpl in *.
      rewrite upd in vcinlog; clear upd.
      applydup check_broadcast_new_view_implies in check.
      exrepnd.
      applydup check_broadcast_new_view_implies_eq_views in check as eqv;[|eauto 3 with pbft];[].
      rewrite eqv.

      apply own_view_change_log_new_view_and_entry_implies in vcinlog; repndors;[|].

      {
        eapply le_trans;[|apply le_max_view_left].
        try (smash_pbft_ind ind).
      }

      rewrite vcinlog in *; ginv.
      autorewrite with pbft in *.

      applydup wf_view_change_state_implies_all_entries in cb as wf;[|eauto 2 with pbft].
      applydup wf_view_change_entry_view_change in check0 as xx; auto.
      rewrite xx.
      apply le_max_view_right.
    }

    {
      (* expired-timer *)

      rename_hyp_with start_view_change start.
      rename_hyp_with own_view_change_in_log vcinlog.
      eapply start_view_change_preserves_own_view_change_in_log in vcinlog;[|eauto].
      simpl in *; repndors; subst; tcsp.
      try (smash_pbft_ind ind).
    }

    {
      (* new-view *)

      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with update_state_new_view upd.
      rename_hyp_with own_view_change_in_log vcinlog.

      applydup update_state_new_view_preserves_current_view in upd as eqv; simpl in *.
      rewrite eqv; clear eqv.
      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_current_view in add as eqv; simpl in *.
      rewrite eqv; clear eqv.
      apply update_state_new_view_preserves_view_change_state in upd; simpl in *.
      rewrite upd in vcinlog; clear upd.
      apply add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state in add; simpl in *.
      rewrite add in vcinlog; clear add.

      apply own_view_change_log_new_view_implies in vcinlog.
      eapply le_trans;[|apply le_max_view_left].
      try (smash_pbft_ind ind).
    }

    (* What's up with that? *)
    Unshelve.

    {
      exact [].
    }
  Qed.
  Hint Resolve view_of_own_view_changes : pbft.

  Lemma view_of_own_view_changes_before :
    forall (eo : EventOrdering) (e : Event) i st vc,
      state_sm_before_event (PBFTreplicaSM i) e = Some st
      -> own_view_change_in_log vc (view_change_state st)
      -> view_change2view vc <= current_view st.
  Proof.
    introv eqst own.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d1|d1]; ginv; subst; simpl in *; tcsp.
    eauto 3 with pbft.
  Qed.
  Hint Resolve view_of_own_view_changes_before : pbft.

End PBFTview_changes_from_good3.


Hint Resolve view_of_own_view_changes : pbft.
Hint Resolve view_of_own_view_changes_before : pbft.
