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
Require Export PBFT_A_1_2_2_direct_pred.
Require Export PBFTgarbage_collect.


Section PBFT_A_1_2_2_somewhere.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma PBFT_A_1_2_2_direct_pred_on :
    forall (eo      : EventOrdering)
           (e1 e2   : Event)
           (i       : Rep)
           (n       : SeqNum)
           (v       : View)
           (rs1 rs2 : list Request)
           (a1 a2   : Tokens)
           (d1 d2   : PBFTdigest)
           (s1 s2   : PBFTstate),
      e1 ⊂ e2
      -> is_primary v i = true
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some s1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some s2
      -> pre_prepare_in_log (mk_pre_prepare v n rs1 a1) d1 (log s1) = true
      -> pre_prepare_in_log (mk_pre_prepare v n rs2 a2) d2 (log s2) = true
      -> d1 = d2.
  Proof.
    introv ltev isprim eqst1 eqst2 prep1 prep2.
    eapply state_sm_before_event_if_on_event_direct_pred in ltev;[|eauto].
    eauto 3 with pbft.
  Qed.
  Hint Resolve PBFT_A_1_2_2_direct_pred_on : pbft.

  Lemma PBFT_A_1_2_2_local_pred :
    forall (eo      : EventOrdering)
           (e1 e2   : Event)
           (i       : Rep)
           (n       : SeqNum)
           (v       : View)
           (rs1 rs2 : list Request)
           (a1 a2   : Tokens)
           (d1 d2   : PBFTdigest)
           (s1 s2   : PBFTstate),
      e1 ⊏ e2
      -> is_primary v i = true
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some s1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some s2
      -> pre_prepare_in_log (mk_pre_prepare v n rs1 a1) d1 (log s1) = true
      -> pre_prepare_in_log (mk_pre_prepare v n rs2 a2) d2 (log s2) = true
      -> d1 = d2.
  Proof.
    intros eo e1 e2.
    induction e2 as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv ltev isprim eqst1 eqst2 pl1 pl2.

    pose proof (local_implies_pred_or_local e1 e2) as q; autodimp q hyp.
    repndors; eauto 3 with pbft;[].

    exrepnd.

    pose proof (state_sm_on_event_some_between e e2 (PBFTreplicaSM i) s2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    remember (pre_prepare_in_log (mk_pre_prepare v n rs2 a2) d2 (log s')) as b.
    symmetry in Heqb; destruct b.

    + apply pred_implies_local_pred in q1; subst.
      eapply ind; eauto; autorewrite with eo; eauto 3 with eo pbft.

    + remember (pre_prepare_in_log (mk_pre_prepare v n rs1 a1) d1 (log s')) as w.
      symmetry in Heqw; destruct w; eauto 3 with pbft;[].

      pose proof (pre_prepares_get_garbage_collected_v2
                    i eo e1 e s1 s' (mk_pre_prepare v n rs1 a1) d1) as q.
      repeat (autodimp q hyp); simpl in q;[].

      pose proof (pre_prepares_are_between_water_marks_if_in_log
                    (mk_pre_prepare v n rs2 a2) d2 i eo e2 s2) as z.
      repeat (autodimp z hyp); eauto 4 with pbft; simpl in z;[].

      pose proof (PBFTlow_water_mark_increases_on_event
                    eo e e2 i s' s2) as u.
      repeat (autodimp u hyp); eauto 3 with eo;[].

      unfold check_between_water_marks in *; smash_pbft; try omega.
  Qed.
  Hint Resolve PBFT_A_1_2_2_local_pred : pbft.

  Lemma PBFT_A_1_2_2_local :
    forall (eo      : EventOrdering)
           (e1 e2   : Event)
           (i       : Rep)
           (n       : SeqNum)
           (v       : View)
           (rs1 rs2 : list Request)
           (a1 a2   : Tokens)
           (d1 d2   : PBFTdigest)
           (s1 s2   : PBFTstate),
      loc e1 = loc e2
      -> is_primary v i = true
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some s1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some s2
      -> pre_prepare_in_log (mk_pre_prepare v n rs1 a1) d1 (log s1) = true
      -> pre_prepare_in_log (mk_pre_prepare v n rs2 a2) d2 (log s2) = true
      -> d1 = d2.
  Proof.
    introv eqloc isprim eqst1 eqst2 pl1 pl2.

    pose proof (tri_if_same_loc e1 e2) as h; autodimp h hyp; try congruence.
    repndors; subst;
      [|rewrite eqst1 in eqst2; ginv;
        eapply PBFT_A_1_2_2; eauto
       |].

    - eapply PBFT_A_1_2_2_local_pred;
        try (exact pl1); try (exact pl2); try (exact h); try (exact isprim); auto.

    - symmetry.
      eapply PBFT_A_1_2_2_local_pred;
        try (exact pl1); try (exact pl2); try (exact h); try (exact isprim); auto.
  Qed.
  Hint Resolve PBFT_A_1_2_2_local : pbft.

End PBFT_A_1_2_2_somewhere.


Hint Resolve PBFT_A_1_2_2_direct_pred_on : pbft.
Hint Resolve PBFT_A_1_2_2_local_pred : pbft.
Hint Resolve PBFT_A_1_2_2_local : pbft.
