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


Require Export PBFT_A_1_2_1.
Require Export PBFTgarbage_collect.


Section PBFT_A_1_2_1_somewhere.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  (* Invariant A.1.2 (1) in PBFT PhD p.145 *)
  Lemma PBFT_A_1_2_1_somewhere :
    forall (eo    : EventOrdering)
           (e     : Event)
           (i     : Rep)
           (n     : SeqNum)
           (v     : View)
           (a1 a2 : Tokens)
           (d1 d2 : PBFTdigest)
           (state : PBFTstate),
      state_sm_on_event (PBFTreplicaSM i) e = Some state
      -> prepare_somewhere_in_log (mk_prepare v n d1 i a1) (log state) = true
      -> prepare_somewhere_in_log (mk_prepare v n d2 i a2) (log state) = true
      -> d1 = d2.
  Proof.
    introv eqst prep1 prep2.
    eapply PBFT_A_1_2_1; eauto;
      eapply prepare_in_somewhere_in_log_implies_prepare_in_log; eauto.
  Qed.
  Hint Resolve PBFT_A_1_2_1_somewhere : pbft.

  (* Uses if_prepare_in_log_digest_unique *)
  Lemma PBFT_A_1_2_1_direct_pred_somewhere :
    forall (eo : EventOrdering)
           (e1 e2   : Event)
           (i       : Rep)
           (n       : SeqNum)
           (v       : View)
           (a1 a2   : Tokens)  (* these two should be different!!! *)
           (d1 d2   : PBFTdigest)
           (state1 state2 : PBFTstate),
      e1 ⊂ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> prepare_somewhere_in_log (mk_prepare v n d1 i a1) (log state1) = true
      -> prepare_somewhere_in_log (mk_prepare v n d2 i a2) (log state2) = true
      -> d1 = d2.
  Proof.
    introv ltev eqst1 eqst2 pl1 pl2.
    eapply PBFT_A_1_2_1_direct_pred; eauto;
      eapply prepare_in_somewhere_in_log_implies_prepare_in_log; eauto.
  Qed.
  Hint Resolve PBFT_A_1_2_1_direct_pred_somewhere : pbft.

  Lemma PBFT_A_1_2_1_local_pred_somewhere :
    forall (eo : EventOrdering)
           (e1 e2   : Event)
           (i       : Rep)
           (n       : SeqNum)
           (v       : View)
           (a1 a2   : Tokens)  (* these two should be different!!! *)
           (d1 d2   : PBFTdigest)
           (state1 state2 : PBFTstate),
      e1 ⊏ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> prepare_somewhere_in_log (mk_prepare v n d1 i a1) (log state1) = true
      -> prepare_somewhere_in_log (mk_prepare v n d2 i a2) (log state2) = true
      -> d1 = d2.
  Proof.
    intros eo e1 e2.
    induction e2 as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv ltev eqst1 eqst2 pl1 pl2.

    pose proof (local_implies_pred_or_local e1 e2) as q; autodimp q hyp.
    repndors; eauto 3 with pbft.

    exrepnd.

    pose proof (state_sm_on_event_some_between e e2 (PBFTreplicaSM i) state2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    remember (prepare_somewhere_in_log (mk_prepare v n d2 i a2) (log s')) as b.
    symmetry in Heqb; destruct b.

    + apply pred_implies_local_pred in q1; subst.
      eapply ind; eauto; autorewrite with eo; eauto 3 with eo pbft.

    + remember (prepare_somewhere_in_log (mk_prepare v n d1 i a1) (log s')) as w.
      symmetry in Heqw; destruct w; eauto 3 with pbft.

      pose proof (prepares_get_garbage_collected_v2
                    i eo e1 e state1 s' (mk_prepare v n d1 i a1)) as q.
      repeat (autodimp q hyp); simpl in q;[].

      pose proof (prepares_are_between_water_marks_if_in_log
                    (mk_prepare v n d2 i a2) i eo e2 state2) as z.
      repeat (autodimp z hyp); eauto 4 with pbft; simpl in z;[].

      pose proof (PBFTlow_water_mark_increases_on_event
                    eo e e2 i s' state2) as u.
      repeat (autodimp u hyp); eauto 3 with eo;[].

      unfold check_between_water_marks in *; smash_pbft; try omega.
  Qed.
  Hint Resolve PBFT_A_1_2_1_local_pred_somewhere : pbft.

  Lemma PBFT_A_1_2_1_local_somewhere :
    forall (eo : EventOrdering)
           (e1 e2   : Event)
           (i       : Rep)
           (n       : SeqNum)
           (v       : View)
           (a1 a2   : Tokens)  (* these two should be different!!! *)
           (d1 d2   : PBFTdigest)
           (state1 state2 : PBFTstate),
      loc e1 = loc e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some state1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some state2
      -> prepare_somewhere_in_log (mk_prepare v n d1 i a1) (log state1) = true
      -> prepare_somewhere_in_log (mk_prepare v n d2 i a2) (log state2) = true
      -> d1 = d2.
  Proof.
    introv eqloc eqst1 eqst2 pl1 pl2.

    pose proof (tri_if_same_loc e1 e2) as h; autodimp h hyp; try congruence.
    repndors; subst;
      [|rewrite eqst1 in eqst2; ginv;
        eapply PBFT_A_1_2_1_somewhere; eauto
       |].

    - eapply PBFT_A_1_2_1_local_pred_somewhere;
        try (exact pl1); try (exact pl2); try (exact h); auto.

    - symmetry.
      eapply PBFT_A_1_2_1_local_pred_somewhere;
        try (exact pl1); try (exact pl2); try (exact h); auto.
  Qed.
  Hint Resolve PBFT_A_1_2_1_local_somewhere : pbft.

End PBFT_A_1_2_1_somewhere.


Hint Resolve PBFT_A_1_2_1_somewhere : pbft.
Hint Resolve PBFT_A_1_2_1_direct_pred_somewhere : pbft.
Hint Resolve PBFT_A_1_2_1_local_pred_somewhere : pbft.
Hint Resolve PBFT_A_1_2_1_local_somewhere : pbft.
