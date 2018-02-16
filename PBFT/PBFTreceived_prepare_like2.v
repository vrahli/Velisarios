(*

  Copyright 2016 Luxembourg University
  Copyright 2017 Luxembourg University
  Copyright 2018 Luxembourg University

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
Require Export Received_or_generated.
Require Export PBFTlearns_or_knows_pl.


Section PBFTreceived_prepare_like2.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma prepare_like_messages_are_received_or_generated :
    forall (eo : EventOrdering) p i,
      received_or_generated
        eo
        (PBFTreplicaSM i)
        (fun e st => prepare_like_in_log p (log st))
        (fun e' st1 st2 e st =>
           verify_prepare_like i (local_keys st1) p = true
           /\ auth_data_in_trigger (prepare_like2main_auth_data p) e')
        (fun e' st1 st2 e st => prepare_like2sender p = i).
  Proof.
    intros eo c i e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv eqst ilog.

    try (rewrite loc_local_pred in ind).

    dup eqst as eqst_At_e; hide_hyp eqst_At_e.
    rewrite state_sm_on_event_unroll2 in eqst.

    match goal with
    | [ H : context[map_option _ ?s] |- _ ] =>
      remember s as sop; symmetry in Heqsop; destruct sop; simpl in *;[|ginv];op_st_some m eqtrig
    end.

    simpl in *.

    unfold PBFTreplica_update in eqst.

    destruct m;
      simpl in *; ginv; subst; tcsp;
        try smash_handlers; try (smash_pbft_ind ind).

    {
      (* request *)
      eapply prepare_like_in_log_add_new_pre_prepare2log in ilog.

      repndors; [ try (smash_pbft_ind ind) | ];[].
      repnd.
      subst; simpl in *; tcsp.

      hide_hyp ind.

      exists e p; eexists. dands; auto; eauto 3 with eo.

    }

    {
      (* pre-prepare *)

      match goal with
      | [ H : context[check_send_replies] |- _ ] => rename H into check
      end.

      dup check as check'.
      eapply check_send_replies_preserves_prepare_like_in_log in check';[|eauto].
      simpl in *.

      match goal with
      | [ H : context[add_new_pre_prepare_and_prepare2log] |- _ ] => rename H into add
      end.

      dup add as add'.
      eapply add_new_pre_prepare_and_prepare2log_preserves_prepare_like_in_log in add';
        [| |eauto];autorewrite with pbft; auto.

      repndors; try (smash_pbft_ind ind);[|].

      {
        repnd; subst; tcsp.
        exists e p st.
        dands; auto; eauto 2 with eo.
        unfold auth_data_in_trigger; allrw; simpl; tcsp.

      }

      {
        repnd; subst; tcsp.
        exists e p st.
        dands; auto; eauto 2 with eo.
        right.
        autorewrite with pbft in *. auto.
      }

    }

    {
      (* prepare *)

      match goal with
      | [ H : context[check_send_replies] |- _ ] => rename H into check
      end.

      dup check as check'.
      eapply check_send_replies_preserves_prepare_like_in_log in check';[|eauto].
      simpl in *.

      match goal with
      | [ H : context[add_new_prepare2log] |- _ ] => rename H into add
      end.

      dup add as add'.
      eapply add_new_prepare2log_preserves_prepare_like_in_log in add';[|eauto].
      repndors; subst; tcsp; try (smash_pbft_ind ind);[].

      repndors; try (smash_pbft_ind ind);[].

      repnd; subst; tcsp.
      exists e p st.
      dands; auto; eauto 2 with eo.
      unfold auth_data_in_trigger; allrw; simpl; tcsp.
    }

    {
      (* commit *)

      match goal with
      | [ H : context[check_send_replies] |- _ ] => rename H into check
      end.

      dup check as check'.
      eapply check_send_replies_preserves_prepare_like_in_log in check';[|eauto].
      simpl in *.

      match goal with
      | [ H : context[add_new_commit2log] |- _ ] => rename H into add
      end.

      dup add as add'.
      eapply add_new_commit2log_preserves_prepare_like_in_log in add';[|eauto].
      repndors; subst; tcsp; try (smash_pbft_ind ind).
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with update_state_new_view upd.
      eapply update_state_new_view_preserves_prepare_like_in_log in ilog;[|eauto].
      simpl in *.
      clear upd.

      apply prepare_like_in_log_log_pre_prepares_implies in ilog.
      repndors; exrepnd; subst; try (smash_pbft_ind ind);[].

      autorewrite with pbft in *.

      match goal with
      | [ H : context[CheckBCastNewView2entry] |- _ ] => rename H into j
      end.
      apply CheckBCastNewView2entry_some_implies in j.

      match goal with
      | [ H : context[check_broadcast_new_view] |- _ ] => rename H into check
      end.
      eapply check_broadcast_new_view_preserves_sender in check;[| |eauto]; eauto 3 with pbft.

      subst; tcsp.
      exists e p st.
      dands; auto; eauto 2 with eo.
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      eapply update_state_new_view_preserves_prepare_like_in_log in upd;[|eauto].
      simpl in *.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_like_in_log in add;[|eauto].
      simpl in *; autorewrite with pbft in *.

      repndors; exrepnd; repndors; repnd; subst; simpl in *; tcsp; try (smash_pbft_ind ind);[|].

      {
        allrw in_map_iff; exrepnd.
        unfold add_digest in *; ginv; simpl in *.

        rename_hyp_with correct_new_view cor.

        dup cor as cor'.
        eapply correct_new_view_implies_pre_prepare2view_eq_new_view2view in cor';[|eauto].
        dup cor as cor''.
        apply correct_new_view_implies_from_primary in cor''.

        exists e p st; dands; eauto 3 with eo pbft.
        left; dands; auto;
          unfold auth_data_in_trigger; allrw; simpl; eauto 2 with pbft.
      }

      {
        exists e p st.
        dands; auto; eauto 2 with eo.
        right.
        autorewrite with pbft in *. auto.
      }
    }
  Qed.

  Lemma pbft_learns_or_knows_prepare_like :
    forall (eo : EventOrdering),
      PBFTcorrect_keys eo
      -> learns_or_knows eo.
  Proof.
    introv ckeys k.
    unfold knows in *; exrepnd.
    pose proof (prepare_like_messages_are_received_or_generated _ d n e mem) as q; simpl in *.
    repeat (autodimp q hyp); exrepnd; repndors; repnd;[left|right];
      try (complete (try unfold pbft_pl_data2loc; allrw; auto)).
    applydup localLe_implies_loc in q1 as eqloc.
    exists e'; dands; auto.
    exists n; dands; auto; simpl; eauto 3 with pbft eo; try congruence;
      try (complete (apply in_bind_op_list_as_auth_data_in_trigger in q0; simpl in *; auto)).

    unfold pbft_pl_verify.
    rewrite eqloc, k0.
    apply verify_prepare_like_implies_verify_main_authenticated_data.
    assert (e' ≼ e) as caus1 by eauto 4 with pbft eo.

    pose proof (ckeys e' n st1) as eqk; autodimp eqk hyp; rewrite k0 in *;
      eauto 3 with pbft eo; try rewrite eqk; auto.
  Qed.
  Hint Resolve pbft_learns_or_knows_prepare_like : pbft.

End PBFTreceived_prepare_like2.


Hint Resolve pbft_learns_or_knows_prepare_like : pbft.
Hint Resolve trigger_implies_auth_data_in_trigger_pre_prepare_data2auth_data_pre : pbft.
