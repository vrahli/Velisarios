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


Require Export PBFTprops4.
Require Export PBFTnew_view_in_log.
Require Export PBFTreceived_prepare_like.
Require Export PBFTlearns_or_knows_nv.


Section PBFTnew_view_learns_of_knows.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma new_views_learns_or_knows :
    forall (eo : EventOrdering),
      PBFTcorrect_keys eo
      -> learns_or_knows2 eo.
  Proof.
    intros eo ckeys d e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv k.
    try (rewrite loc_local_pred in ind).

    apply knows_implies in k; exrepnd; simpl in *.
    unfold pbft_nv_knows in *.

    op_st_some m eqtrig.

    unfold PBFTreplica_update in k2.

    destruct m;
      simpl in *; ginv; subst; tcsp;
        try smash_handlers; try (custom_smash_pbft_ind ind).

    {
      (* check-bcast-new-view *)

      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with update_state_new_view upd.
      rename_hyp_with check_broadcast_new_view check.

      applydup CheckBCastNewView2entry_some_implies in cb.
      dup upd as upd'.
      eapply update_state_new_view_preserves_new_view_in_log in upd;[|eauto].
      simpl in *.

      applydup log_new_view_and_entry_preserves_new_view_in_log in upd;
        auto;[|symmetry;eapply check_broadcast_new_view_implies_equal_views;[|eauto];
               eauto 3 with pbft].

      repndors;[try (custom_smash_pbft_ind ind)| |];[|].

      - subst.
        right.
        allrw.
        unfold pbft_nv_data2loc.
        erewrite check_broadcast_new_view_implies_new_view2sender;[| |eauto]; eauto 3 with pbft.

      - dup check as check'.
        eapply check_broadcast_new_view_implies_new_view_in_log in check';
          [| |eauto|]; eauto 3 with pbft.
        try (custom_smash_pbft_ind ind).
    }

    {
      (* new-view *)

      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with update_state_new_view upd.

      eapply update_state_new_view_preserves_new_view_in_log in upd;[|eauto].
      apply add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state in add.
      simpl in *.
      apply log_new_view_preserves_new_view_in_log in upd.
      rewrite add in *.

      repndors;[|]; try (custom_smash_pbft_ind ind);[].

      subst; dands; eauto 2 with eo; auto.
      left.
      exists e; dands; eauto 2 with eo.
      exists n; unfold auth_data_in_trigger; allrw; simpl; dands;
        unfold pbft_nv_data2main_auth_data; eauto 3 with eo pbft.

      eapply verify_new_view_implies_pbft_nv_verify;[| |eauto];auto.
      eapply ckeys;[|eauto]; rewrite k1 in *; auto; eauto 3 with eo proc pbft.
    }
  Qed.

End PBFTnew_view_learns_of_knows.
