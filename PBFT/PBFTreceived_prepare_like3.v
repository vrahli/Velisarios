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


Section PBFTreceived_prepare_like3.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma send_prepares_are_in_log :
    forall (eo : EventOrdering) (e : Event) p dst st i,
      loc e = PBFTreplica i
      -> In (send_prepare p dst) (output_system_on_event_ldata PBFTsys e)
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> prepare_in_log p (log st) = true.
  Proof.
    introv eqloce j eqst.
    apply in_output_system_on_event_ldata in j.

    unfold PBFTsys in j.
    rewrite eqloce in j.

    rw @loutput_sm_on_event_unroll2 in j.
    fold (@DirectedMsgs _ _) in *.
    simpl in *.
    rewrite state_sm_on_event_unroll2 in eqst.

    match goal with
    | [ H : context[state_sm_before_event ?a ?b] |- _ ] =>
      remember (state_sm_before_event a b) as q; clear Heqq
    end.
    destruct q; simpl in *; ginv;[].

    op_st_some m eqtrig; rewrite eqtrig in *; simpl in *.

    unfold PBFTreplica_update in *.
    destruct m; simpl in *; ginv; subst; tcsp;
      smash_handlers; try conflicting_sends;
        try (repndors; ginv; smash_pbft).

    {
      (* pre-prepare *)

      allrw in_app_iff.

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_pre_prepare_and_prepare2log add.

      applydup check_send_replies_preserves_log in check; rewrite check0; clear check0.
      simpl.
      repndors;
        [|apply in_check_broadcast_commit_implies in j; exrepnd; conflicting_sends
         |];[|].

      - apply in_check_broadcast_prepare_implies in j; exrepnd.
        subst; simpl in *; ginv; eauto 2 with pbft.

      - eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.

      allrw in_app_iff.
      repndors;[apply in_check_broadcast_commit_implies in j; exrepnd; conflicting_sends|];[].
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
      (* new_view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      allrw in_app_iff; repndors;
        [|eapply message_in_update_state_new_view_implies in upd;
          [|eauto];exrepnd;ginv];[].

      apply send_prepare_in_trim_outputs_with_low_water_mark in j; repnd.
      eapply prepare_in_add_prepares_to_log_from_new_view_pre_prepares_is_in_log in add;[|eauto].
      eapply update_state_new_view_preserves_prepare_in_log_true_forward; eauto.
    }
  Qed.

End PBFTreceived_prepare_like3.
