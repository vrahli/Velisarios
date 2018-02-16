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


Require Export PBFT_A_1_2_2.


Section PBFT_A_1_2_2_direct_pred.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma PBFT_A_1_2_2_direct_pred :
    forall (eo      : EventOrdering)
           (e       : Event)
           (i       : Rep)
           (n       : SeqNum)
           (v       : View)
           (rs1 rs2 : list Request)
           (a1 a2   : Tokens)
           (d1 d2   : PBFTdigest)
           (s1 s2   : PBFTstate),
      is_primary v i = true
      -> state_sm_before_event (PBFTreplicaSM i) e = Some s1
      -> state_sm_on_event (PBFTreplicaSM i) e = Some s2
      -> pre_prepare_in_log (mk_pre_prepare v n rs1 a1) d1 (log s1) = true
      -> pre_prepare_in_log (mk_pre_prepare v n rs2 a2) d2 (log s2) = true
      -> d1 = d2.
  Proof.
    intros eo e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].

    introv isprim eqst1 eqst2 prep1 prep2.

    dup eqst2 as eqst2_At_e.
    hide_hyp eqst2_At_e.
    rewrite state_sm_on_event_unroll2 in eqst2.

    match goal with
    | [ H : context[map_option _ ?s] |- _ ] =>
      remember s as sop; symmetry in Heqsop; destruct sop; simpl in *;[|ginv];op_st_some m eqtrig
    end.
    ginv.

    unfold PBFTreplica_update in eqst2.

    destruct m;
      simpl in *; ginv; subst; tcsp;
        try smash_handlers; try (smash_pbft_ind ind).

    (* 8 subgoals *)

    { (* request *)

      apply pre_prepare_in_log_add_new_prepare2log in prep2.
      repndors; eauto 3 with pbft.
      repnd.

      assert False; [|tcsp].

      match goal with
      | [ H : context[check_new_request] |- _ ] =>
        apply check_new_request_sequence_number_increases in H
      end.

      unfold mk_auth_pre_prepare, mk_pre_prepare in prep0; ginv.

      match goal with
      | [ H : state_sm_before_event _ _ = _ |- _ ] =>
        eapply PBFT_A_1_2_3_before in H;[|eauto|];eauto with pbft
      end.

      match goal with
      | [ H : context[next_seq ?a] |- _ ] =>
        assert (next_seq a <= a) as f by omega;
          apply next_seq_not_le in f; auto
      end.
    }

    { (* pre-prepare *)

      rename_hyp_with check_send_replies check.
      eapply check_send_replies_preserves_pre_prepare_in_log in check;[|exact prep2].
      simpl in *.
      clear prep2.

      rename_hyp_with add_new_pre_prepare_and_prepare2log add.
      eapply add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log in add;[|exact check].
      simpl in *.
      clear check.

      repndors; repnd; eauto 3 with pbft;[].

      match goal with
      | [ H : own_prepare_is_already_logged_with_different_digest _ _ _ _ _ = _ |- _ ] =>
        apply (own_prepare_is_already_logged_with_different_digest_false_and_prepare_in_log_implies_same_digest _ _ _ _ _ d1 a1) in H;
          subst; simpl in *; auto
      end.
    }

    { (* prepare *)

      rename_hyp_with check_send_replies check.
      eapply check_send_replies_preserves_pre_prepare_in_log in check;[|exact prep2].
      simpl in *.
      clear prep2.

      rename_hyp_with add_new_prepare2log add.
      eapply add_new_prepare2log_preserves_pre_prepare_in_log in add;[|exact check].
      simpl in *; eauto 3 with pbft.
    }

    { (* commit *)

      rename_hyp_with check_send_replies check.
      eapply check_send_replies_preserves_pre_prepare_in_log in check;[|exact prep2].
      simpl in *.
      clear prep2.

      rename_hyp_with add_new_commit2log add.
      eapply add_new_commit2log_preserves_pre_prepare_in_log in add.
      rewrite check in add; symmetry in add.

      simpl in *; eauto 3 with pbft.
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.
      eapply find_and_execute_requests_preserves_pre_prepare_in_log in fexec;[|exact prep2].
      eauto 3 with pbft.
    }

    {
      (* checkpoint *)

      apply pre_prepare_in_log_check_one_stable in prep2; smash_pbft.
    }

    { (* check-bcast-new-view *)

      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with update_state_new_view eqlog.

      applydup CheckBCastNewView2entry_some_implies in cb.

      match goal with
      | [ H : check_broadcast_new_view _ _ _ = Some (?a, ?b, ?c, ?d) |- _ ] =>
        rename a into nv; rename b into entry'; rename c into OP; rename d into NP
      end.

      (* This means that we started changing view, which means that all
         pre-prepares that are in the log have a view strictly lower than
         the current view *)

      (* view_changed_entry should imply that has_new_view is false *)

      eapply update_state_new_view_preserves_pre_prepare_in_log in prep2;[| |eauto];
        simpl; eauto 4 with pbft;[].
      simpl in *.

      apply pre_prepare_in_log_log_pre_prepares_implies in prep2.

      repndors; repnd; eauto 3 with pbft.

      applydup check_broadcast_new_view_some_implies in check; exrepnd.
      dup check as eqvs1.
      eapply check_broadcast_new_view_preserves_view in eqvs1;[|eauto]; simpl in eqvs1.
      dup check as eqvs2.
      apply check_broadcast_new_view_implies_eq_views in eqvs2; eauto 3 with pbft list;[].

      rename_hyp_with view_changed_entry vce.

      dup vce as vce'.
      eapply view_changed_entry_some_implies_has_new_view_false in vce';[| |eauto]; eauto 2 with pbft.

      match goal with
      | [ H : pre_prepare_in_log _ _ _ = true |- _ ] => rename H into pp_in_log
      end.
      dup pp_in_log as pp_in_log'.
      eapply pre_prepare_in_log_implies_has_new_view_before in pp_in_log';[|eauto]; auto.
      simpl in *.

      rewrite <- eqvs2 in vce'; rewrite eqvs1 in vce'; pbft_simplifier.
    }

    { (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with correct_new_view cor.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      eapply update_state_new_view_preserves_pre_prepare_in_log in prep2;[| |eauto];
        simpl; auto;[].
      simpl in *.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log in prep2;[|eauto].
      simpl in *; autorewrite with pbft in *.

      repndors; exrepnd; try (smash_pbft_ind ind); eauto 3 with pbft.

      subst.
      eapply pre_prepare_in_map_correct_new_view_implies in cor;[|eauto].
      subst.
      match goal with
      | [ H : new_view2sender _ <> _ |- _ ] => destruct H; eauto 2 with pbft
      end.
    }
  Qed.
  Hint Resolve PBFT_A_1_2_2_direct_pred : pbft.

End PBFT_A_1_2_2_direct_pred.


Hint Resolve PBFT_A_1_2_2_direct_pred : pbft.
