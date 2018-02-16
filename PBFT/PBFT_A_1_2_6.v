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


Require Export PBFTview_change_in_log.



Section PBFT_A_1_2_6.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma log_new_view_and_entry_preserves_view_change_in_log :
    forall vc nv e S e',
      wf_view_change_state S
      -> vce_view_changes e = vce_view_changes e'
      -> In e' S
      -> vce_view e = vce_view e'
      -> new_view2view nv = vce_view e
      -> view_change_in_log vc (log_new_view_and_entry S nv e)
      -> view_change_in_log vc S.
  Proof.
    induction S; introv wf eqvcs i eqvs1 eqvs2 lnw; simpl in *; tcsp; smash_pbft;
      repndors; subst; tcsp;
        try (inversion wf as [|? ? imp wf1 wf2]; clear wf; subst; simpl in * ).

    - allrw <- ; auto.

    - applydup imp in i; try  congruence.

    - try congruence.

    - eapply IHS; eauto.
  Qed.
  Hint Resolve log_new_view_and_entry_preserves_view_change_in_log : pbft.

  Lemma check_broadcast_new_view_implies_same_vce_view_changes :
    forall i s e nv e' O N,
      check_broadcast_new_view i s e = Some (nv, e', O, N)
      -> vce_view_changes e' = vce_view_changes e.
  Proof.
    introv check; unfold check_broadcast_new_view in check; smash_pbft.
    unfold view_changed_entry in *; smash_pbft.
  Qed.
  Hint Resolve check_broadcast_new_view_implies_same_vce_view_changes : pbft.

  Lemma check_broadcast_new_view_implies_same_views :
    forall i s e nv e' O N,
      check_broadcast_new_view i s e = Some (nv, e', O, N)
      -> vce_view e' = vce_view e.
  Proof.
    introv check; unfold check_broadcast_new_view in check; smash_pbft.
    unfold view_changed_entry in *; smash_pbft.
  Qed.
  Hint Resolve check_broadcast_new_view_implies_same_views : pbft.

  (* Invariant A.1.2 (6) in PBFT PhD p.145 *)
  (* this lemma is defined for view_change messages that we received from others *)
  Lemma PBFT_A_1_2_6 :
    forall (eo      : EventOrdering)
           (e       : Event)
           (v       : View)
           (n       : SeqNum)
           (s       : StableChkPt)
           (C       : CheckpointCert)
           (P       : list PreparedInfo)
           (i       : Rep)
           (a       : Tokens)
           (slf     : Rep)
           (state   : PBFTstate),
      state_sm_on_event (PBFTreplicaSM slf) e = Some state
      -> view_change_in_log (mk_view_change v n s C P i a) (view_change_state state)
      -> correct_view_change v (mk_view_change v n s C P i a) = true.
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers3 smash_pbft_ind3.

    { (* check_bcast_new *)

      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with check_broadcast_new_view check.

      applydup CheckBCastNewView2entry_some_implies in cb.
      applydup check_broadcast_new_view_implies_equal_views in check;[|eauto 3 with pbft];[].

      match goal with
        [ H : update_state_new_view _ _ _ = _ |-_ ] =>
        eapply update_state_new_view_preserves_view_change_in_log in H;[|eauto]
      end.

      simpl in *.

      match goal with
      | [ H : view_change_in_log _ _ |- _] =>
        eapply (log_new_view_and_entry_preserves_view_change_in_log _ _ _ _ x) in H
      end; auto; eauto 3 with pbft.

      try (smash_pbft_ind ind).
    }

    { (* view-change *)

      match goal with
       | [ H : add_other_view_change _ _ = _ |- _ ] =>
         eapply add_other_view_change_preserves_view_change_in_log in H; [| eauto]
       end.

      repndors; exrepnd; try (smash_pbft_ind ind).
    }

    { (* new_view *)

      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with update_state_new_view upd.

      eapply update_state_new_view_preserves_view_change_in_log in upd;[|eauto].
      simpl in *.
      apply log_new_view_preserves_view_change_in_log in upd.

      apply add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state in add.
      simpl in *.
      rewrite add in *.

      try (smash_pbft_ind ind).
    }
  Qed.
  Hint Resolve PBFT_A_1_2_6 : pbft.

  Lemma PBFT_A_1_2_6_before :
    forall (eo : EventOrdering)
           (e  : Event)
           (vc : ViewChange)
           (i  : Rep)
           (st : PBFTstate),
      state_sm_before_event (PBFTreplicaSM i) e = Some st
      -> view_change_in_log vc (view_change_state st)
      -> correct_view_change (view_change2view vc) vc = true.
  Proof.
    introv eqst vcinlog.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d|d]; ginv; subst; simpl in *; tcsp.
    destruct vc, v; simpl in *; unfold view_change2view; simpl.
    eapply PBFT_A_1_2_6; try (exact eqst); auto; autorewrite with eo; auto.
  Qed.
  Hint Resolve PBFT_A_1_2_6_before : pbft.

End PBFT_A_1_2_6.


Hint Resolve log_new_view_and_entry_preserves_view_change_in_log : pbft.
Hint Resolve check_broadcast_new_view_implies_same_vce_view_changes : pbft.
Hint Resolve check_broadcast_new_view_implies_same_views : pbft.
Hint Resolve PBFT_A_1_2_6 : pbft.
Hint Resolve PBFT_A_1_2_6_before : pbft.
