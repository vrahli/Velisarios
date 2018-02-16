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


Section PBFTknows_own_new_view.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition all_view_changes_of_new_view_in_log
             (nv : NewView)
             (st : PBFTstate) :=
    forall vc,
      In vc (new_view2cert nv)
      -> view_change_somewhere_in_log vc (view_change_state st).

  Lemma in_new_view_cert_of_check_broadcast_new_view_implies :
    forall i s e nv e' O N vc,
      check_broadcast_new_view i s e = Some (nv, e', O, N)
      -> In vc (new_view2cert nv)
      -> In vc (view_change_entry2view_changes e').
  Proof.
    introv check j.
    unfold check_broadcast_new_view in check; smash_pbft.
  Qed.
  Hint Resolve in_new_view_cert_of_check_broadcast_new_view_implies : pbft.

  Lemma knows_own_new_view :
    forall nv (eo : EventOrdering) e,
      knows2 e nv
      -> loc e = PBFTreplica (new_view2sender nv)
      -> exists e' st1 st2 c entry entry' OP NP,
          e' ⊑ e
          /\ state_sm_before_event (PBFTreplicaSM (new_view2sender nv)) e' = Some st1
          /\ state_sm_on_event (PBFTreplicaSM (new_view2sender nv)) e' = Some st2
          /\ event_triggered_by_message e' (PBFTcheck_bcast_new_view c)
          /\ CheckBCastNewView2entry c (view_change_state st1) = Some entry
          /\ check_broadcast_new_view (new_view2sender nv) st1 entry = Some (nv, entry', OP, NP)
          /\ all_view_changes_of_new_view_in_log nv st2.
  Proof.
    intros nv eo.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv k eqloc.
    try (rewrite loc_local_pred in ind).

    apply knows_implies_before_after in k; exrepnd; simpl in *.

    assert (n = new_view2sender nv) by congruence; subst n.
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
        exists e; eexists; eexists; eexists; eexists; eexists; eexists; eexists; dands; eauto; eauto 3 with eo.

        unfold all_view_changes_of_new_view_in_log in *.
        introv ii.
        apply update_state_new_view_preserves_view_change_state in upd'; simpl in upd'.
        rewrite upd'; clear upd'; eauto 4 with pbft.

      - dup check as check'.
        eapply check_broadcast_new_view_implies_new_view_in_log in check';
          [| |eauto|]; eauto 3 with pbft.
        try (smash_pbft_ind ind).
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

      repndors;[|]; try (custom_smash_pbft_ind ind).
    }
  Qed.

End PBFTknows_own_new_view.


Hint Resolve in_new_view_cert_of_check_broadcast_new_view_implies : pbft.
