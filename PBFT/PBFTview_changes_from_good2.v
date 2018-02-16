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
Require Export PBFTtactics4.


Section PBFTview_changes_from_good2.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma sent_new_views_are_in_log :
    forall (eo : EventOrdering) (e : Event) nv dst st i,
      loc e = PBFTreplica i
      -> In (send_new_view nv dst) (output_system_on_event_ldata PBFTsys e)
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> new_view_in_log nv (view_change_state st).
  Proof.
    prove_by_ind2 ind h eqst sop p m eqtrig trig smash_handlers3 smash_pbft_ind3.

    {
      (* check-bcast-new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with check_broadcast_new_view check.

      apply CheckBCastNewView2entry_some_implies in cb.

      allrw in_app_iff.
      repndors;[|];
        [|eapply message_in_update_state_new_view_implies in upd;[|eauto];
          exrepnd; ginv];[].

      unfold broadcast2others in *; exrepnd; ginv;[].

      applydup check_broadcast_new_view_implies in check.
      exrepnd.
      eapply update_state_new_view_preserves_new_view_in_log_backward;[eauto|].
      simpl.
      eapply implies_new_view_in_log_log_new_view_and_entry;[eauto| | | |];
        auto; eauto 2 with pbft;
          try (complete (subst; autorewrite with pbft; auto));
          try (complete (allrw <- ;eauto 4 with pbft)).
    }

    {
      (* new_view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      allrw in_app_iff; repndors;
        [|eapply message_in_update_state_new_view_implies in upd;
          [|eauto];exrepnd;ginv];[].

      rename_hyp_with trim_outputs_with_low_water_mark trim.
      apply send_new_view_in_trim_outputs_with_low_water_mark in trim.
      eapply in_add_prepares_to_log_from_new_view_pre_prepares_implies in add;[|eauto].
      repndors; exrepnd; ginv.
    }

  Qed.

End PBFTview_changes_from_good2.
