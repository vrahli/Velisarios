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


Require Export PBFTin_log.
Require Export PBFTordering.
Require Export PBFTpre_prepare_in_log_preserves.
Require Export PBFTprops5.


Section PBFTpre_prepares_are_received.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.



  Lemma pre_prepares_are_received :
    forall (eo  : EventOrdering)
           (e   : Event)
           (slf : Rep)
           (n   : SeqNum)
           (v   : View)
           (rs  : list Request)
           (a   : Tokens)
           (d   : PBFTdigest)
           (st  : PBFTstate),
      state_sm_on_event (PBFTreplicaSM slf) e = Some st
      -> pre_prepare_in_log (mk_pre_prepare v n rs a) d (log st) = true
      -> exists e' st1 st2,
          e' ⊑ e
          /\ state_sm_before_event (PBFTreplicaSM slf) e' = Some st1
          /\ state_sm_on_event (PBFTreplicaSM slf) e' = Some st2
          /\ pre_prepare_in_log (mk_pre_prepare v n rs a) d (log st1) = false
          /\ pre_prepare_in_log (mk_pre_prepare v n rs a) d (log st2) = true
          /\

          (
            (* either we generated the pre-prepare from a request *)
            (
              exists r,
                event_triggered_by_message e' (PBFTrequest r)
                /\ v = current_view st1
                /\ n = next_seq (sequence_number (primary_state st1))
                /\ rs = r :: request_buffer (primary_state st1)
                /\ a = authenticate (PBFTmsg_bare_pre_prepare (bare_pre_prepare v n rs)) (local_keys st1)
                /\ d = create_hash_messages (map PBFTrequest rs)
                /\ has_new_view (view_change_state st1) v = true
                /\ verify_request slf (local_keys st1) r = true
                /\ is_primary v slf = true
                /\ in_progress (primary_state st1) < PBFTmax_in_progress
                /\ check_between_water_marks (low_water_mark st1) n = true
                /\ valid_timestamp (primary_state st1) (request2sender r) (request2timestamp r) = true

                (* properties about the state after the event *)
                /\ sequence_number (primary_state st2) = n
            )

            \/

            (* or we received the pre-prepare *)
            (
              event_triggered_by_message e' (PBFTpre_prepare (mk_pre_prepare v n rs a))
              /\ has_new_view (view_change_state st1) v = true
              /\ is_primary v slf = false
              /\ verify_pre_prepare slf (local_keys st1)
                   (mk_pre_prepare v n rs a) = true
              /\ v = current_view st1
              /\ check_between_water_marks (low_water_mark st1) n = true
              /\ d = create_hash_messages (map PBFTrequest rs)
              /\ slf <> PBFTprimary v

              (* properties about the state after the event *)
              /\ sequence_number (primary_state st2) = sequence_number (primary_state st1)
            )

            \/

            (* or we generated the pre-prepare because we received a
               check-bcast-new-view, which triggered a new-view *)
            (
              exists pos entry vc entry' b nv opreps npreps,
                event_triggered_by_message e' (PBFTcheck_bcast_new_view (check_bcast_new_view pos))
                /\ select pos (view_change_state st1) = Some entry
                /\ v = view_change2view vc
                /\ In n (from_min_to_max_of_view_changes entry')
                /\ a = authenticate (PBFTmsg_bare_pre_prepare (bare_pre_prepare v n rs)) (local_keys st1)
                /\ is_primary (vce_view entry') slf = true
                /\ view_changed_entry st1 entry = Some (vc, entry')
                /\ create_new_prepare_message
                     n
                     (view_change2view vc)
                     (local_keys st1)
                     (view_change_cert2prep (view_change_entry2view_changes entry'))
                   = (b, (mk_pre_prepare v n rs a, d))

                (* properties about the state after the event *)
                /\ check_broadcast_new_view slf st1 entry = Some (nv, entry', opreps, npreps)
                /\ sequence_number (primary_state st2) = max_seq_num (sequence_number (primary_state st1)) (max_O opreps)
                /\ current_view st2 = max_view (current_view st1) v
                (* **NEW** *)
                /\ view_change_state st2 = log_new_view_and_entry (view_change_state st1) nv entry'
        (*has_new_view (view_change_state st2) v = true*)
            )

            \/


            (* or we logged it because the view change *)
            (
              (* what are those requests? *)
              exists nv,
                event_triggered_by_message e' (PBFTnew_view nv)
                /\ slf <> new_view2sender nv
                /\ verify_new_view slf (local_keys st1) nv = true
                /\ current_view st1 <= new_view2view nv
                /\ correct_new_view nv = true
                /\ has_new_view (view_change_state st1) (new_view2view nv) = false
                /\ initial_view < (new_view2view nv)
                /\ In (mk_pre_prepare v n rs a, d)
                      (map (fun p : Pre_prepare => add_digest p) (new_view2oprep nv ++ new_view2nprep nv))

                (* properties about the state after the event *)
                /\ sequence_number (primary_state st2) = sequence_number (primary_state st1)
                /\ view_change_state st2 = log_new_view (view_change_state st1) nv

            (* /\ i = slf
                /\ a = authenticate (PBFTmsg_bare_prepare (bare_prepare v n d slf)) (local_keys st1)
                /\ In (pre_prepare (bare_pre_prepare v n reqs) a', d)
                      (map add_digest (new_view2oprep nv ++ new_view2nprep nv))

 *)
            )
          ).
  Proof.
    introv eqst prep.

    revert dependent st.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].

    introv eqst prep.

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
        try smash_handlers; try (smash_pbft_ind ind).

    {
      (* requests *)

      hide_hyp ind.
      hide_hyp eqst_At_e.
      hide_concl.

      applydup pre_prepare_in_log_add_new_prepare2log in prep.
      show_concl; show_hyp ind;
        repndors; repnd; try (smash_pbft_ind ind);[];
          hide_concl; hide_hyp ind.

      subst.
      unfold mk_pre_prepare, mk_auth_pre_prepare in *; ginv.

      match goal with
      | [ H : context[check_new_request] |- _ ] =>
        apply check_new_requests_some_iff in H; repnd
      end.
      subst.

      show_hyp eqst_At_e.

      eexists; eexists; eexists; dands;[|eauto|eauto| | |]; eauto 3 with eo;[].

      left.
      autorewrite with pbft in *.
      exists r.
      dands; auto;
        try (complete (apply is_primary_true; auto));
        try (complete (simpl; autorewrite with pbft; auto)).
    }

    { (* handle pre-prepare *)

      match goal with
      | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
        applydup check_send_replies_preserves_low_water_mark in H as eqlwm
      end.
      simpl in *.

      match goal with
      | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
        dup H as check;
          eapply check_send_replies_preserves_pre_prepare_in_log in H;[|eauto]
      end.
      simpl in *.

      match goal with
      | [ H : add_new_pre_prepare_and_prepare2log _ _ _ _ _ _ = _ |- _ ] =>
        eapply (add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log) in H;
          [|eauto];[]
      end.

      repndors; repnd; try (smash_pbft_ind ind);[].

      clear ind.

(*      match goal with
      | [ H : mk_pre_prepare _ _ _ _ = _ |- _ ] => rewrite <- H in *; clear H
      end.*)
      exists e p st; dands; auto; eauto 3 with eo;
        try (complete (repndors; tcsp; try cpltLR));[].

      right.
      left.
      subst; simpl in *; ginv.
      allrw; dands; auto; autorewrite with pbft in *; eauto 2 with pbft.
    }

    { (* handle prepare *)

      hide_hyp ind.

      match goal with
      | [H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
        eapply check_send_replies_preserves_pre_prepare_in_log in H;[|eauto]
      end.
      autorewrite with pbft in *.

      match goal with
      | [ H : add_new_prepare2log _ _ _ _ = _ |- _ ] =>
        eapply add_new_prepare2log_preserves_pre_prepare_in_log in H;[|eauto]
      end.

      repndors; show_hyp ind; try (smash_pbft_ind ind).
    }

    { (* handle commit *)

      hide_hyp ind.
      hide_concl.

      match goal with
      | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
        applydup check_send_replies_preserves_log in H as eqlogs;
          simpl in *; subst; simpl in *
      end.

      match goal with
      | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
        applydup check_send_replies_preserves_keys in H as eqkeys;
          simpl in *; subst; simpl in *; try (rewrite eqkeys)
      end.

      match goal with
      | [ H1 : add_new_commit2log _ _ = _, H2 : pre_prepare_in_log _ _ _ = _ |- _ ] =>
        eapply add_new_commit2log_preserves_pre_prepare_in_log in H1;
          rewrite H1 in H2; clear H1
      end.

      show_hyp ind.
      show_concl.
      try (smash_pbft_ind ind).
    }

    { (* handle check_ready *)

      hide_hyp ind.

      autorewrite with pbft in *.
      match goal with
      | [ H : find_and_execute_requests _ _ _ _ = _ |- _ ] =>
        eapply find_and_execute_requests_preserves_pre_prepare_in_log in H;[|eauto]
      end.

      show_hyp ind.
      try (smash_pbft_ind ind).
    }

    { (* handle check-bcast-new-view *)

      hide_concl.
      hide_hyp ind.

      rename_hyp_with update_state_new_view upd.

      applydup update_state_new_view_preserves_local_keys in upd.
      applydup update_state_new_view_preserves_sequence_number in upd.
      applydup update_state_new_view_preserves_current_view in upd.
      applydup update_state_new_view_preserves_view_change_state in upd.
      simpl in *.

      dup upd as upd'.
      eapply update_state_new_view_preserves_pre_prepare_in_log in upd';
        eauto 2 with pbft;[|simpl; eauto 4 with pbft];[].
      simpl in *; autorewrite with pbft in *.

      apply pre_prepare_in_log_log_pre_prepares_implies in upd'.

      show_concl.

      repndors; repnd;[show_concl;show_hyp ind; try (smash_pbft_ind ind)|];[].

      hide_concl.

      rename_hyp_with check_broadcast_new_view check.
      applydup check_broadcast_new_view_some_implies in check.
      show_concl; exrepnd; hide_concl; subst; simpl in *.

      rewrite in_app_iff in *; show_concl; repndors; hide_concl;[|].

      + match goal with
        | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
          eapply o_pre_prepare_in_create_new_prepare_messages_implies in H;[|eauto];[]
        end.
        show_concl; exrepnd; hide_concl.

        match goal with
        | [ H : create_new_prepare_message _ _ _ _ = _ |- _ ] =>
          applydup create_new_prepare_message_implies_same_sequence_number in H;
            applydup create_new_prepare_message_implies_same_view in H;
            applydup create_new_prepare_message_implies_auth in H
        end.
        simpl in *.
        subst.

        eexists; eexists; eexists; dands; eauto 2 with eo;[].
        right; right; left.

        destruct c; simpl in *.

        eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
        dands; eauto; autorewrite with pbft; auto.

      + match goal with
        | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
          eapply n_pre_prepare_in_create_new_prepare_messages_implies in H;[|eauto];[]
        end.
        show_concl; exrepnd; hide_concl.

        match goal with
        | [ H : create_new_prepare_message _ _ _ _ = _ |- _ ] =>
          applydup create_new_prepare_message_implies_same_sequence_number in H;
            applydup create_new_prepare_message_implies_same_view in H;
            applydup create_new_prepare_message_implies_auth in H
        end.
        simpl in *.
        subst.

        eexists; eexists; eexists; dands; eauto 2 with eo;[].
        right; right; left.

        destruct c; simpl in *.

        eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
        dands; eauto; autorewrite with pbft; auto.
    }

    { (* new view *)

      hide_hyp ind.
      hide_hyp eqst_At_e.

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      applydup update_state_new_view_preserves_local_keys in upd.
      applydup update_state_new_view_preserves_sequence_number in upd.
      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_sequence_number in add.
      simpl in *.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; eauto 3 with pbft;[].

      dup prep as prep'.
      eapply update_state_new_view_preserves_pre_prepare_in_log in prep;
        [| |eauto]; simpl; auto;[].
      simpl in *.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log
        in prep;[|eauto]; simpl in *;[].

      repndors;[|].

      - show_hyp ind; try (smash_pbft_ind ind).

      - exrepnd.

        destruct pp as [b' a']; simpl in *.
        destruct b' as [v' s' reqs]; simpl in *.
        unfold mk_pre_prepare in *; ginv.
        autorewrite with pbft in *.

        applydup seq_of_pre_prepare_in_new_view in prep0; exrepnd; simpl in *; auto.

        exists e p st; dands; auto; eauto 3 with pbft eo;
          try (complete (repndors; tcsp; try cpltLR));[].

        right; right; right.

        exists v0; dands; tcsp;[|].

        + apply add_prepares_to_log_from_new_view_pre_prepares_preserves_sequence_number in add.
          apply update_state_new_view_preserves_sequence_number in upd.
          simpl in *.
          allrw; auto.

        + apply update_state_new_view_preserves_view_change_state in upd.
          apply add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state in add.
          allrw; simpl.
          allrw; simpl; auto.
    }
  Qed.

End PBFTpre_prepares_are_received.
