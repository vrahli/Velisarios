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


Section PBFTreceived_prepare_like5.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  (* MOVE *)
  Lemma send_view_change_not_in_check_broadcast_prepare :
    forall vc dst i rd giop,
      In (send_view_change vc dst) (check_broadcast_prepare i rd giop)
      -> False.
  Proof.
    introv j; apply in_check_broadcast_prepare_implies in j;exrepnd;subst;ginv.
  Qed.
  Hint Resolve send_view_change_not_in_check_broadcast_prepare : pbft_false.

  (* MOVE *)
  Hint Extern 1 =>
  match goal with
  | [ H : In (send_view_change _ _) (check_broadcast_prepare _ _ _) |- _ ] =>
    apply send_view_change_not_in_check_broadcast_prepare in H; destruct H
  end : pbft_false.

  (* MOVE *)
  Hint Extern 1 =>
  match goal with
  | [ H : False |- _ ] => destruct H
  end : pbft_false.

  (* MOVE *)
  Lemma send_view_change_not_in_check_broadcast_commit :
    forall vc dst i rd giop,
      In (send_view_change vc dst) (check_broadcast_commit i rd giop)
      -> False.
  Proof.
    introv j; apply in_check_broadcast_commit_implies in j; exrepnd;subst;ginv.
  Qed.

  (* MOVE *)
  Hint Extern 1 =>
  match goal with
  | [ H : In (send_view_change _ _) (check_broadcast_commit _ _ _) |- _ ] =>
    apply send_view_change_not_in_check_broadcast_commit in H; destruct H
  end : pbft_false.

  (* MOVE *)
  Lemma send_view_change_not_in_check_send_replies_implies :
    forall i v keys entryop s1 n msgs s2 vc dst,
      check_send_replies i v keys entryop s1 n = (msgs, s2)
      -> In (send_view_change vc dst) msgs
      -> False.
  Proof.
    introv check j.
    eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
  Qed.
  Hint Resolve send_view_change_not_in_check_send_replies_implies : pbft_false.

  (* MOVE *)
  Hint Extern 1 =>
  match goal with
  | [ H : check_send_replies _ _ _ _ _ _ = (?x, _), J : In (send_view_change _ _) ?x |- _ ] =>
    eapply message_in_check_send_replies_implies in H;[|exact J]; ginv
  end : pbft_false.

  Lemma prepare_like_of_send_view_change_are_in_log :
    forall (eo : EventOrdering) (e : Event) vc dst st i pi pl,
      loc e = PBFTreplica i
      -> In (send_view_change vc dst) (output_system_on_event_ldata PBFTsys e)
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> In pi (view_change2prep vc)
      -> prepare_like_in_prepared_info pl pi
      -> prepare_like_in_log pl (log st).
  Proof.
    introv eqloce j eqst invc inpi.
    apply in_output_system_on_event_ldata in j.

    unfold PBFTsys in j.
    rewrite eqloce in j.

    rw @loutput_sm_on_event_unroll2 in j.
    fold (@DirectedMsgs _ _) in *.
    simpl in *.
    rewrite state_sm_on_event_unroll2 in eqst.

    match goal with
    | [ H : context[state_sm_before_event ?a ?b] |- _ ] =>
      remember (state_sm_before_event a b) as q; symmetry in Heqq; hide_hyp Heqq
    end.
    destruct q; simpl in *; ginv;[].

    op_st_some m eqtrig; rewrite eqtrig in *; simpl in *.

    unfold PBFTreplica_update in *.
    destruct m; simpl in *; ginv; subst; tcsp;
      smash_handlers; try conflicting_sends;
        try (complete (allrw in_app_iff; repndors; eauto 3 with pbft pbft_false)).

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
      unfold view_change2prep in *; simpl in *; eauto 3 with pbft.
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
  Hint Resolve prepare_like_of_send_view_change_are_in_log : pbft.

End PBFTreceived_prepare_like5.


Hint Resolve prepare_like_of_send_view_change_are_in_log : pbft.
