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


Section PBFTreceived_prepare_like6.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  (*
     (1) first we prove that if we send a new-view that contains a prepare-like
         then we have a view-change message in the log that contains our prepare-like
         message.

     (2) then we'll prove that if we have a view-change message in our log then either
         we received it or we generated it and it contains only prepare-like messages
         that are in our log.
   *)

  Lemma prepare_like_of_send_new_view_are_in_log :
    forall (eo : EventOrdering) (e : Event) nv dst st i pl,
      loc e = PBFTreplica i
      -> In (send_new_view nv dst) (output_system_on_event_ldata PBFTsys e)
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> In (prepare_like2main_auth_data pl) (new_view2auth_data nv)
      ->
      prepare_like_in_log pl (log st)
      \/
      (* the prepare_like might not be in the log *)
      exists vc pi,
        view_change_somewhere_in_log vc (view_change_state st)
        /\ In pi (view_change2prep vc)
        /\ prepare_like_in_prepared_info pl pi.
  Proof.
    introv eqloce j eqst innv.
    apply in_output_system_on_event_ldata in j.

    unfold PBFTsys in j.
    rewrite eqloce in j.

    rw @loutput_sm_on_event_unroll2 in j.
    fold (@DirectedMsgs _ _) in *.
    simpl in *.
    dup eqst as eqst_backup; hide_hyp eqst_backup.
    rewrite state_sm_on_event_unroll2 in eqst.

    match goal with
    | [ H : context[state_sm_before_event ?a ?b] |- _ ] =>
      remember (state_sm_before_event a b) as q; symmetry in Heqq; hide_hyp Heqq
    end.
    destruct q; simpl in *; ginv;[].

    op_st_some m eqtrig; rewrite eqtrig in *; simpl in *.

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
      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with check_broadcast_new_view check.

      apply CheckBCastNewView2entry_some_implies in cb.

      allrw in_app_iff.
      repndors;[|];
        [|eapply message_in_update_state_new_view_implies in upd;[|eauto];
          exrepnd; ginv];[].

      unfold broadcast2others in *; ginv.
      simpl in *.

      applydup check_broadcast_new_view_implies in check.
      exrepnd.

      apply prepare_like2main_auth_data_in_new_view2auth_data_implies in innv.

      applydup update_state_new_view_preserves_view_change_state in upd as eqs.
      simpl in eqs.
      rewrite eqs.

      assert (has_new_view (view_change_state p) (vce_view x) = false)
        as hnvf by eauto 3 with pbft.

      match goal with
      | [ H : new_view2cert _ = view_change_entry2view_changes _ |- _ ] => rename H into eqcert
      end.
      match goal with
      | [ H : view_change_entry2view_changes _ = _ :: _ |- _ ] => rename H into eqvs
      end.

      repndors; exrepnd;[| |].

      - rewrite eqcert in *.
        rewrite eqvs in *.
        simpl in *.

        repndors;subst;[|].

        + subst.
          right.
          exists (refresh_view_change vc p) pi; dands; auto.
          apply implies_view_change_somewhere_in_log_log_new_view_and_entry.
          autorewrite with pbft; simpl; tcsp.

        + right.
          autorewrite with pbft in *; GC.
          exists vc0 pi; dands; auto.
          apply implies_view_change_somewhere_in_log_log_new_view_and_entry.
          autorewrite with pbft; simpl; tcsp.

      - applydup check_broadcast_new_view_implies_equal_new_view2oprep in check as eqnv.
        rewrite eqnv in *.
        allrw in_map_iff; exrepnd; subst; simpl in *.
        match goal with
        | [ H : In (?a,?b) _ |- _ ] => rename a into pp; rename b into d
        end.
        autorewrite with pbft in *; GC.

        dup check as nfo.
        eapply check_broadcast_new_view_preserves_view in nfo;
          (*eapply check_broadcast_new_view_implies_digest_and_auth in nfo;*)
          [|rewrite in_app_iff;left;eauto];[].

        dup check as eqvs.
        eapply check_broadcast_new_view_implies_eq_views in eqvs;[|eauto 3 with pbft];[].

        assert (forall pp' d',
                   pre_prepare_in_log pp' d' (log p) = true
                   -> pre_prepare2view pp' <> pre_prepare2view pp) as diffvs.
        {
          introv h w.
          eapply pre_prepare_in_log_implies_has_new_view_before in Heqq;[|eauto];auto;[].
          rewrite w in Heqq; rewrite <- nfo in Heqq; rewrite eqvs in Heqq; pbft_simplifier.
        }

        dup check as bmarks.
        eapply in_check_broadcast_new_view_implies_between_water_marks2 in bmarks;
          [|rewrite in_app_iff;left;eauto|];[|rewrite eqcert;eauto];[].
        unfold check_between_water_marks in *; smash_pbft;[].

        left.
        eapply (implies_prepare_like_in_log_prepare_like_pre_prepare _ d);
          [eauto 2 with pbft|];[].

        dup upd as eqlog.
        eapply update_state_new_view_preserves_log in eqlog;[|rewrite eqcert;eauto].
        simpl in *; autorewrite with pbft in *.

        smash_pbft;rewrite eqlog; clear eqlog;[|];
          [|eapply implies_pre_prepare_in_log_log_pre_prepares;
            [|introv h w; eapply diffvs; eauto
             |apply in_app_iff;left;auto|auto;omega];
            eauto 2 with pbft];[].

        apply clear_log_checkpoint_preserves_pre_prepare_in_log_true; auto;[].
        eapply implies_pre_prepare_in_log_log_pre_prepares;
          [|introv h w; eapply diffvs; eauto
           |apply in_app_iff;left;auto|auto;omega];
          eauto 2 with pbft.

      - applydup check_broadcast_new_view_implies_equal_new_view2nprep in check as eqnv.
        rewrite eqnv in *.
        allrw in_map_iff; exrepnd; subst; simpl in *.
        match goal with
        | [ H : In (?a,?b) _ |- _ ] => rename a into pp; rename b into d
        end.
        autorewrite with pbft in *; GC.

        dup check as nfo.
        eapply check_broadcast_new_view_preserves_view in nfo;
          (*eapply check_broadcast_new_view_implies_digest_and_auth in nfo;*)
          [|rewrite in_app_iff;right;eauto];[].

        dup check as eqvs.
        eapply check_broadcast_new_view_implies_eq_views in eqvs;[|eauto 3 with pbft];[].

        assert (forall pp' d',
                   pre_prepare_in_log pp' d' (log p) = true
                   -> pre_prepare2view pp' <> pre_prepare2view pp) as diffvs.
        {
          introv h w.
          eapply pre_prepare_in_log_implies_has_new_view_before in Heqq;[|eauto];auto;[].
          rewrite w in Heqq; rewrite <- nfo in Heqq; rewrite eqvs in Heqq; pbft_simplifier.
        }

        dup check as bmarks.
        eapply in_check_broadcast_new_view_implies_between_water_marks2 in bmarks;
          [|rewrite in_app_iff;right;eauto|];[|rewrite eqcert;eauto];[].
        unfold check_between_water_marks in *; smash_pbft;[].

        left.
        eapply (implies_prepare_like_in_log_prepare_like_pre_prepare _ d);
          [eauto 2 with pbft|];[].

        dup upd as eqlog.
        eapply update_state_new_view_preserves_log in eqlog;[|rewrite eqcert;eauto].
        simpl in *; autorewrite with pbft in *.

        smash_pbft;rewrite eqlog; clear eqlog;[|];
          [|eapply implies_pre_prepare_in_log_log_pre_prepares;
            [|introv h w; eapply diffvs; eauto
             |apply in_app_iff;right;auto|auto;omega];
            eauto 2 with pbft];[].

        apply clear_log_checkpoint_preserves_pre_prepare_in_log_true; auto;[].
        eapply implies_pre_prepare_in_log_log_pre_prepares;
          [|introv h w; eapply diffvs; eauto
           |apply in_app_iff;right;auto|auto;omega];
          eauto 2 with pbft.
    }

    {
      (* expired-timer *)

      repndors; ginv; smash_pbft.
    }

    {
      (* new_view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      allrw in_app_iff; repndors;
        [|eapply message_in_update_state_new_view_implies in upd;
          [|eauto];exrepnd;ginv];[].

      apply send_new_view_in_trim_outputs_with_low_water_mark in j.
      eapply in_add_prepares_to_log_from_new_view_pre_prepares_implies in add;[|eauto].
      repndors; exrepnd; ginv.
    }
  Qed.

End PBFTreceived_prepare_like6.
