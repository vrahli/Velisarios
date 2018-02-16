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


Require Export PBFTview_changes_from_good3.


Section PBFTview_changes_from_good7.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma sent_view_change_is_in_log2 :
    forall (eo : EventOrdering) (e : Event) vc dst st1 st2 i,
      loc e = PBFTreplica i
      -> In (send_view_change vc dst) (output_system_on_event_ldata PBFTsys e)
      -> state_sm_before_event (PBFTreplicaSM i) e = Some st1
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st2
      -> own_view_change_in_log vc (view_change_state st2)
         /\ vc = mk_current_view_change i (current_view st2) st1.
  Proof.
    introv eqloce j eqst1 eqst2.
    apply in_output_system_on_event_ldata in j.

    unfold PBFTsys in j.
    rewrite eqloce in j.

    rw @loutput_sm_on_event_unroll2 in j.
    fold (@DirectedMsgs _ _) in *.
    simpl in *.
    rewrite state_sm_on_event_unroll2 in eqst2.
    rewrite eqst1 in eqst2; simpl in eqst2.
    rewrite eqst1 in j; simpl in j.

    op_st_some m eqtrig.
    rewrite eqtrig in *; simpl in *.

    unfold PBFTreplica_update in *.
    destruct m; simpl in *; ginv; subst; tcsp;
      smash_handlers; try conflicting_sends.

    {
      (* pre-prepare *)

      allrw in_app_iff; repndors;
        [apply in_check_broadcast_prepare_implies in j;exrepnd;subst;ginv
        |apply in_check_broadcast_commit_implies in j; exrepnd;subst;ginv
        |].

      rename_hyp_with check_send_replies check.
      eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
    }

    {
      (* prepare *)

      allrw in_app_iff; repndors;
        [apply in_check_broadcast_commit_implies in j; exrepnd;subst;ginv
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
      eapply message_in_find_and_execute_requests_implies in fexec;[|eauto].
      repndors; exrepnd; conflicting_sends.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with update_state_new_view upd.

      unfold broadcast2others in *; repndors; ginv.
      eapply message_in_update_state_new_view_implies in upd;[|eauto].
      exrepnd; ginv.
    }

    {
      (* expired-timer *)

      repndors; ginv; smash_pbft.
      unfold broadcast2others in *; exrepnd; ginv; simpl in *.
      autorewrite with pbft.
      dands; auto;[].
      eapply start_view_change_implies_own_view_change_in_log;[| |eauto]; eauto 2 with pbft.

      introv own; simpl.
      eapply view_of_own_view_changes_before in own;[|eauto];auto; omega.
    }

    {
      (* new_view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      allrw in_app_iff; repndors;
        [|eapply message_in_update_state_new_view_implies in upd;
          [|eauto];exrepnd;ginv];[].

      apply send_view_change_in_trim_outputs_with_low_water_mark in j.
      eapply in_add_prepares_to_log_from_new_view_pre_prepares_implies in add;[|eauto].
      repndors; exrepnd; ginv.
    }
  Qed.
  Hint Resolve sent_view_change_is_in_log2 : pbft.

End PBFTview_changes_from_good7.


Hint Resolve sent_view_change_is_in_log2 : pbft.
