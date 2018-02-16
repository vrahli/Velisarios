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


Section PBFTdelay_of_send_new_views.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma delay_of_send_new_views :
    forall (eo : EventOrdering) (e : Event) p dst delay,
      In (MkDMsg (PBFTnew_view p) dst delay) (output_system_on_event_ldata PBFTsys e)
      -> delay = 0.
  Proof.
    introv j.
    apply in_output_system_on_event_ldata in j.
    unfold PBFTsys in j.
    destruct (loc e); simpl in *;[|apply MhaltedSM_output in j; tcsp];[].

    rw @loutput_sm_on_event_unroll2 in j.
    fold (@DirectedMsgs _ _) in *.
    simpl in *.

    match goal with
    | [ H : context[state_sm_before_event ?a ?b] |- _ ] =>
      remember (state_sm_before_event a b) as q; clear Heqq
    end.
    destruct q; simpl in *; ginv; tcsp;[].

    remember (trigger e) as trig; symmetry in Heqtrig.
    destruct trig; simpl in *; tcsp.
    unfold PBFTreplica_update in *.
    destruct m; simpl in *; ginv; subst; tcsp;
      smash_handlers; try conflicting_sends;
        try (complete (repndors; tcsp; ginv));
        try (complete (unfold broadcast2others in *; ginv)).

    {
      (* pre-prepare *)
      allrw in_app_iff; repndors.
      - apply in_check_broadcast_prepare_implies in j; exrepnd; subst; unfold send_prepare in *; ginv.
      - apply in_check_broadcast_commit_implies in j; exrepnd; ginv.
      - eapply message_in_check_send_replies_implies in j;[|eauto]; ginv.
    }

    {
      (* prepare *)
      allrw in_app_iff; repndors.
      - apply in_check_broadcast_commit_implies in j; exrepnd; ginv.
      - eapply message_in_check_send_replies_implies in j;[|eauto]; ginv.
    }

    {
      (* commit *)
      eapply message_in_check_send_replies_implies in j;[|eauto]; ginv.
    }

    {
      (* check-ready *)
      eapply message_in_find_and_execute_requests_implies in j;[|eauto]; repndors; exrepnd; ginv.
    }

    {
      (* check-bcast-new-view *)
      repndors; unfold broadcast2others, send_new_view in *; ginv.
      eapply message_in_update_state_new_view_implies in j;[|eauto]; exrepnd; ginv.
    }

    {
      (* expired-timer *)
      allrw in_app_iff; repndors.
      - apply send_message_in_trim_outputs_with_low_water_mark in j.
        eapply in_add_prepares_to_log_from_new_view_pre_prepares_implies in j;[|eauto].
        repndors; exrepnd; unfold send_prepare in *; ginv.
      - eapply message_in_update_state_new_view_implies in j;[|eauto]; exrepnd; ginv.
    }
  Qed.

  Lemma send_new_view_no_delay :
    forall (eo : EventOrdering) (e : Event) p dst delay,
      In (MkDMsg (PBFTnew_view p) dst delay) (output_system_on_event_ldata PBFTsys e)
      -> In (send_new_view p dst) (output_system_on_event_ldata PBFTsys e).
  Proof.
    introv i.
    applydup delay_of_send_new_views in i; subst; auto.
  Qed.

End PBFTdelay_of_send_new_views.
