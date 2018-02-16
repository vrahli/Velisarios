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


Require Export PBFT_A_1_9_misc2.


Section PBFT_A_1_9_misc3.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma low_water_mark_increases_with_new_views :
    forall (eo : EventOrdering) (e : Event) i st nv maxV,
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> new_view_in_log nv (view_change_state st)
      -> view_change_cert2max_seq (new_view2cert nv) = Some maxV
      -> maxV <= low_water_mark st.
  Proof.
    introv eqst nvil mv.

    revert dependent st.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].

    introv eqst nvil.

    dup eqst as eqst_At_e.
    rewrite state_sm_on_event_unroll2 in eqst.

    match goal with
      | [ H : context[map_option _ ?s] |- _ ] =>
        remember s as sop; symmetry in Heqsop; destruct sop; simpl in *;[|ginv];op_st_some m eqtrig
    end.

    unfold PBFTreplica_update in eqst.

    destruct m;
      simpl in *; ginv; subst; tcsp;
        try smash_handlers; try (smash_pbft_ind ind).

    (* 3 subgoals *)

    {
      (* checkpoint *)

      assert (maxV <= low_water_mark p) by (smash_pbft_ind ind).
      rename_hyp_with add_new_checkpoint2cp_state add.
      apply add_new_checkpoint2cp_state_preserves_sn_stable in add; rewrite add.
      fold (low_water_mark p) in *; try omega.
    }

    {
      (* check_bcast_new_view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with CheckBCastNewView2entry cb.

      apply CheckBCastNewView2entry_some_implies in cb.

      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 4 with pbft;[].

      assert (correct_new_view nv = true) as cornv1 by eauto 2 with pbft.
      applydup check_broadcast_new_view_generates in check as cornv2.

      eapply update_state_new_view_preserves_new_view_in_log in nvil;[|eauto].
      simpl in *.

      applydup check_broadcast_new_view_implies in check; exrepnd.
      unfold update_state_new_view in upd.
      unfold view_change_cert2max_seq in *; smash_pbft.

      - match goal with
        | [ H : new_view2cert _ = _ |- _ ] => rewrite <- H in *
        end.

        match goal with
        | [ H1 : ?a = _, H2 : ?a = _ |- _ ] => rewrite H1 in H2; ginv
        end.

        match goal with
        | [ H : view_change_cert2max_seq_vc _ = Some (maxV0, _) |- _ ] =>
          applydup view_change_cert2_max_seq_vc_some_in in H;
            applydup sn_of_view_change_cert2max_seq_vc in H; subst
        end.

        dup cornv2 as corvc.
        eapply correct_new_view_implies_correct_view_change in corvc;[|eauto].

        rename_hyp_with log_checkpoint_cert_from_new_view lchk.
        eapply log_checkpoint_cert_from_new_view_preserves_low_water_mark2 in lchk;
          [| |eauto];simpl; autorewrite with pbft; auto;[].

        applydup check_broadcast_new_view_implies_eq_views in check;[|eauto 3 with pbft];[].

        applydup log_new_view_and_entry_preserves_new_view_in_log in nvil;
          simpl in *; autorewrite with pbft in *; auto;[].

        repndors;[| |].

        + assert (maxV <= low_water_mark p) as xx by (smash_pbft_ind ind).
          rewrite lchk; omega.

        + subst x2.

          match goal with
          | [ H1 : view_change_cert2max_seq_vc ?a = _, H2 : view_change_cert2max_seq_vc ?a = _ |- _ ]
            => rewrite H1 in H2; ginv
          end.

        + assert (new_view_in_log nv (view_change_state p)) as nvinlog2 by (eauto 3 with pbft).
          assert (maxV <= low_water_mark p) as xx by (smash_pbft_ind ind).
          rewrite lchk; omega.

      - match goal with
        | [ H : new_view2cert _ = _ |- _ ] => rewrite <- H in *
        end.

        match goal with
        | [ H1 : ?a = _, H2 : ?a = _ |- _ ] => rewrite H1 in H2; ginv
        end.

        match goal with
        | [ H : view_change_cert2max_seq_vc _ = Some (maxV0, _) |- _ ] =>
          applydup view_change_cert2_max_seq_vc_some_in in H;
            applydup sn_of_view_change_cert2max_seq_vc in H; subst
        end.

        dup cornv2 as corvc.
        eapply correct_new_view_implies_correct_view_change in corvc;[|eauto].

        applydup check_broadcast_new_view_implies_eq_views in check;[|eauto 3 with pbft];[].

        applydup log_new_view_and_entry_preserves_new_view_in_log in nvil;
          simpl in *; autorewrite with pbft in *; auto;[].

        repndors;[| |].

        + assert (maxV <= low_water_mark p) as xx by (smash_pbft_ind ind).
          omega.

        + subst x2.

          match goal with
          | [ H1 : view_change_cert2max_seq_vc  ?a = _,
                   H2 : view_change_cert2max_seq_vc ?a = _ |- _ ] => rewrite H1 in H2; ginv
          end.

        + assert (new_view_in_log nv (view_change_state p)) as nvinlog2 by (eauto 3 with pbft).
          assert (maxV <= low_water_mark p) as xx by (smash_pbft_ind ind).
          omega.
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with correct_new_view cornv2.
      rename_hyp_with has_new_view hnv.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      assert (correct_new_view nv = true) as cornv1 by eauto 2 with pbft.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_low_water_mark in add.
      autorewrite with pbft in *.
      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state in add.
      simpl in *.

      clear add.

      unfold update_state_new_view in upd.
      unfold view_change_cert2max_seq in *; smash_pbft.

      - simpl in *.

        match goal with
        | [ H : view_change_cert2max_seq_vc _ = Some (x4, _) |- _ ] =>
          applydup view_change_cert2_max_seq_vc_some_in in H;
            applydup sn_of_view_change_cert2max_seq_vc in H; subst
        end.

        dup cornv2 as corvc.
        eapply correct_new_view_implies_correct_view_change in corvc;[|eauto].

        rename_hyp_with log_checkpoint_cert_from_new_view lchk.
        applydup log_checkpoint_cert_from_new_view_preserves_view_change_state in lchk.
        eapply log_checkpoint_cert_from_new_view_preserves_low_water_mark2 in lchk;
          [| |eauto];simpl; autorewrite with pbft; auto;[].
        rewrite lchk0 in *.

        applydup log_new_view_preserves_new_view_in_log in nvil;
          simpl in *; autorewrite with pbft in *; auto;[].

        rewrite add2 in *.
        rewrite lchk in *.

        repndors;[|].

        + assert (maxV <= low_water_mark p) as xx by (smash_pbft_ind ind).
          rewrite add1 in *.
          omega.

        + subst v.

          match goal with
          | [ H1 : view_change_cert2max_seq_vc ?a = _, H2 : view_change_cert2max_seq_vc ?a = _ |- _ ]
            => rewrite H1 in H2; ginv
          end.

      - rewrite <- add1 in *.
        rewrite add2 in *.

        applydup log_new_view_preserves_new_view_in_log in nvil;
          simpl in *; autorewrite with pbft in *; auto;[].

        repndors;[|].

        + assert (maxV <= low_water_mark p) as xx by (smash_pbft_ind ind).
          omega.

        + subst v.

          match goal with
          | [ H1 : view_change_cert2max_seq_vc ?a = _, H2 : view_change_cert2max_seq_vc ?a = _ |- _ ]
            => rewrite H1 in H2; ginv
          end.

      - rewrite <- add1 in *.
        rewrite add2 in *.

        applydup log_new_view_preserves_new_view_in_log in nvil;
          simpl in *; autorewrite with pbft in *; auto;[].

        repndors;[|].

        + assert (maxV <= low_water_mark p) as xx by (smash_pbft_ind ind).
          omega.

        + subst v.

          match goal with
          | [ H1 : view_change_cert2max_seq_vc ?a = _, H2 : view_change_cert2max_seq_vc ?a = _ |- _ ]
            => rewrite H1 in H2; ginv
          end.
    }
  Qed.
  Hint Resolve low_water_mark_increases_with_new_views : pbft.

End PBFT_A_1_9_misc3.


Hint Resolve low_water_mark_increases_with_new_views : pbft.
