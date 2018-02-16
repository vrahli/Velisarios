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


Require Export PBFTview_change_somewhere_in_log.


Section PBFTview_changes_are_received.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma log_new_view_and_entry_preserves_view_change_somewhere_in_log :
    forall vc nv e S,
      view_change_somewhere_in_log vc (log_new_view_and_entry S nv e)
      -> view_change_somewhere_in_log vc S
         \/ vce_view_change e = Some vc
         \/ In vc (vce_view_changes e).
  Proof.
    introv lnw.
    induction S; simpl in *; tcsp; smash_pbft; repndors; tcsp.
  Qed.

  Lemma in_vce_view_changes_implies_view_change_somewhere_in_log :
    forall e vc S,
      In e S
      -> In vc (vce_view_changes e)
      -> view_change_somewhere_in_log vc S.
  Proof.
    induction S; introv i j; simpl in *; tcsp; repndors; subst; tcsp.
  Qed.
  Hint Resolve in_vce_view_changes_implies_view_change_somewhere_in_log : pbft.

  Lemma in_vce_view_changes_implies_view_change_somewhere_in_log_if_check_broadcast_new_view :
    forall i s e nv e' O N vc,
      check_broadcast_new_view i s e = Some (nv, e', O, N)
      -> In e (view_change_state s)
      -> In vc (vce_view_changes e')
      -> view_change_somewhere_in_log vc (view_change_state s).
  Proof.
    introv check j k.
    unfold check_broadcast_new_view in check; smash_pbft;[].
    unfold view_changed_entry in *; smash_pbft.
  Qed.
  Hint Resolve in_vce_view_changes_implies_view_change_somewhere_in_log_if_check_broadcast_new_view : pbft.

  Lemma view_changes_are_received :
    forall (eo      : EventOrdering)
           (e       : Event)
           (vc      : ViewChange)
           (slf     : Rep)
           (state   : PBFTstate),
      loc e = PBFTreplica slf
      -> state_sm_on_event (PBFTreplicaSM slf) e = Some state
      -> view_change_somewhere_in_log vc(view_change_state state)
      -> exists e' st',
          e' ⊑ e
          /\ state_sm_before_event (PBFTreplicaSM slf) e' = Some st'
          /\
          (
            (
              event_triggered_by_message e' (PBFTview_change vc)
              /\ slf <> view_change2sender vc
              /\ verify_view_change slf (local_keys st') vc = true
              /\ valid_view (view_change2view vc) (current_view st') = true
              /\ correct_view_change (view_change2view vc) vc = true
            )
            \/
            (
              exists t,
                event_triggered_by_message e' (PBFTexpired_timer t)
                /\ current_view st' = expired_timer2view t
                /\ vc = mk_current_view_change slf (next_view (current_view st')) st'
            )
            \/
            (
              exists c entry entry',
                event_triggered_by_message e' (PBFTcheck_bcast_new_view c)
                /\ CheckBCastNewView2entry c (view_change_state st') = Some entry
                /\ is_primary (vce_view entry) slf = true
                /\ view_changed_entry st' entry = Some (vc, entry')
            )
          ).
  Proof.
    intros eo e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv eqloc eqst prep1.

    rewrite loc_local_pred in ind.

    dup eqst as eqst_At_e.
    rewrite state_sm_on_event_unroll2 in eqst.

    match goal with
    | [ H : context[map_option _ ?s] |- _ ] =>
      remember s as sop; symmetry in Heqsop; destruct sop; simpl in *;[|ginv];
          op_st_some m eqtrig
    end.

    unfold PBFTreplica_update in eqst.

    destruct m;
      simpl in *; ginv; subst; tcsp;
       (try smash_handlers; try (smash_pbft_ind ind)).

    { (* check_bcast_new *)

      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with update_state_new_view upd.

      applydup CheckBCastNewView2entry_some_implies in cb.
      eapply update_state_new_view_preserves_view_change_somewhere_in_log in upd;[|eauto].
      simpl in *.
      eapply log_new_view_and_entry_preserves_view_change_somewhere_in_log in upd.
      repndors; try (smash_pbft_ind ind);[].

      eexists; eexists; dands; eauto; eauto 2 with eo.
      right; right.
      unfold check_broadcast_new_view in *; smash_pbft;[].
      rename_hyp_with view_changed_entry vce.
      applydup view_changed_entry_some_implies in vce.
      exrepnd; subst; autorewrite with pbft in *; ginv.

      eexists; eexists; eexists; dands; eauto; eauto 3 with pbft.
    }

    { (* expired-timer *)

      match goal with
      | [ H : start_view_change _ _ = _ |- _] =>
        eapply add_own_view_change_to_state_preserves_view_change_somewhere_in_log_own in H;[|eauto];[]
      end.

      repndors; exrepnd; try (smash_pbft_ind ind);[].

      exists e p. dands; auto; eauto 2 with eo.

      right; left.
      exists t; dands; auto.
    }

    { (* view-change *)

      match goal with
       | [ H : add_other_view_change _ _ = _ |- _ ] =>
         eapply add_other_view_change_preserves_view_change_somewhere_in_log in H; [| eauto]
       end.

      repndors; [|];  exrepnd; try (smash_pbft_ind ind); [].

      subst.

      exists e p.
      dands; auto; eauto 2 with eo.
      left. dands; auto.
    }

    { (* new_view *)

      match goal with
        [ H : update_state_new_view _ _ _ = _ |-_ ] =>
        eapply update_state_new_view_preserves_view_change_somewhere_in_log in H;[|eauto]; simpl in *
      end.

      match goal with
      | [ H : add_prepares_to_log_from_new_view_pre_prepares _ _ _ = _ |- _] =>
        apply add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state in H;
          simpl in H; rewrite H in *
      end.
      simpl in *.

      match goal with
      | [ H : view_change_somewhere_in_log _ (log_new_view _ _) |- _ ] =>
        apply log_new_view_preserves_view_change_somewhere_in_log in H
      end.

      try (smash_pbft_ind ind).
    }
  Qed.

  Lemma view_changes_are_received_before_event :
    forall (eo      : EventOrdering)
           (e       : Event)
           (vc      : ViewChange)
           (slf     : Rep)
           (state   : PBFTstate),
      loc e = PBFTreplica slf
      -> state_sm_before_event (PBFTreplicaSM slf) e = Some state
      -> view_change_somewhere_in_log vc(view_change_state state)
      -> exists e' st',
          e' ⊑ (local_pred e)
          /\ state_sm_before_event (PBFTreplicaSM slf) e' = Some st'
          /\
          (
            (
              event_triggered_by_message e' (PBFTview_change vc)
              /\ slf <> view_change2sender vc
              /\ verify_view_change slf (local_keys st') vc = true
              /\ valid_view (view_change2view vc) (current_view st') = true
              /\ correct_view_change (view_change2view vc) vc = true
            )
            \/
            (
              exists t,
                event_triggered_by_message e' (PBFTexpired_timer t)
                /\ current_view st' = expired_timer2view t
                /\ vc = mk_current_view_change slf (next_view (current_view st')) st'
            )
            \/
            (
              exists c entry entry',
                event_triggered_by_message e' (PBFTcheck_bcast_new_view c)
                /\ CheckBCastNewView2entry c (view_change_state st') = Some entry
                /\ is_primary (vce_view entry) slf = true
                /\ view_changed_entry st' entry = Some (vc, entry')
            )
          ).
  Proof.
    introv eqloc eqst nview.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d|d]; ginv; subst; simpl in *;[ ginv; tcsp|].
    eapply view_changes_are_received in eqst; eauto.

    autorewrite with eo; auto.
  Qed.


End PBFTview_changes_are_received.


Hint Resolve in_vce_view_changes_implies_view_change_somewhere_in_log : pbft.
Hint Resolve in_vce_view_changes_implies_view_change_somewhere_in_log_if_check_broadcast_new_view : pbft.
