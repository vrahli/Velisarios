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


Require Export PBFTgarbage_collect.


Section PBFT_A_1_2_7.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma implies_pre_prepare_in_log_add_new_pre_prepare2log :
    forall pp d pp' d' L,
      pre_prepare_in_log pp d L = true
      -> pre_prepare_in_log pp d (add_new_pre_prepare2log pp' d' L) = true.
  Proof.
    introv h.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    apply pre_prepare_in_log_add_new_pre_prepare2log_false_implies in Heqb; pbft_simplifier.
  Qed.
  Hint Resolve implies_pre_prepare_in_log_add_new_pre_prepare2log : pbft.

  Lemma matching_requests_same :
    forall x, matching_requests x x = true.
  Proof.
    introv.
    induction x; simpl in *; tcsp; smash_pbft.
  Qed.
  Hint Rewrite matching_requests_same : pbft.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_prepare_in_log2 :
    forall i L pp d Fp Fc giop K prep,
      i = rt_rep (Fp tt)
      -> add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> prepare_in_log prep K = true
      -> prepare_in_log prep L = true
         \/
         (
           prep = request_data_and_rep_toks2prepare (pre_prepare2request_data pp d) (Fp tt)
           /\ prepare_in_log prep L = false
           /\ pre_prepare_in_log pp d K = true
         ).
  Proof.
    induction L; introv eqi h q; repeat (simpl in *; smash_pbft);
      try (complete (destruct x, a, log_entry_pre_prepare_info; simpl in *; ginv; smash_pbft;
                     unfold is_prepare_for_entry in *; simpl in *;
                     unfold eq_request_data in *; smash_pbft));[|].

    - allrw is_prepare_for_entry_true_iff; simpl in *.
      allrw same_rep_tok_true_iff.
      repndors; tcsp.
      allrw; simpl.
      rewrite <- q.
      autorewrite with pbft; auto.
      destruct pp, b; simpl in *; smash_pbft.
      allrw map_map; simpl; rewrite map_id.
      autorewrite with pbft in *; tcsp.

    - destruct x, a, log_entry_pre_prepare_info; simpl in *; ginv; smash_pbft;[].
      unfold is_prepare_for_entry in *; simpl in *.
      unfold eq_request_data in *; smash_pbft;[].
      destruct prep, b, pp, b; simpl in *; ginv.
      unfold add_prepare_if_not_enough in *; pbft_dest_all x.
      repndors; tcsp;[].

      allrw same_rep_tok_true_iff.
      right.
      allrw map_map; simpl; allrw map_id; autorewrite with pbft.

      dands; tcsp; eauto 3 with pbft;[|].

      { allrw <-; autorewrite with pbft; dands; auto. }

      { rewrite <- q in *; simpl in *.
        apply in_list_rep_toks_false_implies_existsb_same_rep_toks_false; auto. }
  Qed.

  Lemma add_new_prepare2log_preserves_pre_prepare_in_log_true_backward :
    forall i L P Fc gi K pp d,
      add_new_prepare2log i L P Fc = (gi, K)
      -> pre_prepare_in_log pp d L = true
      -> pre_prepare_in_log pp d K = true.
  Proof.
    introv add prep.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    eapply add_new_prepare2log_preserves_pre_prepare_in_log_false in add; eauto.
  Qed.
  Hint Resolve add_new_prepare2log_preserves_pre_prepare_in_log_true_backward : pbft.

  Lemma add_new_commit2log_preserves_pre_prepare_in_log_true_backward :
    forall L c gi K pp d,
      add_new_commit2log L c = (gi, K)
      -> pre_prepare_in_log pp d L = true
      -> pre_prepare_in_log pp d K = true.
  Proof.
    introv add prep.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    eapply add_new_commit2log_preserves_pre_prepare_in_log_false in add; eauto.
  Qed.
  Hint Resolve add_new_commit2log_preserves_pre_prepare_in_log_true_backward : pbft.

  Lemma implies_pre_prepare_in_log_clear_log_checkpoint :
    forall (n : SeqNum) pp d L,
      n < pre_prepare2seq pp
      -> pre_prepare_in_log pp d L = true
      -> pre_prepare_in_log pp d (clear_log_checkpoint L n) = true.
  Proof.
    introv h prep.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    apply pre_prepare_in_log_clear_log_checkpoint_false_implies in Heqb; pbft_simplifier; auto.
  Qed.
  Hint Resolve implies_pre_prepare_in_log_clear_log_checkpoint : pbft.

  Lemma implies_pre_prepare_in_log_log_pre_prepares :
    forall pp d P L lwm,
      pre_prepare_in_log pp d L = true
      -> pre_prepare_in_log pp d (log_pre_prepares L lwm P) = true.
  Proof.
    introv prep.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    apply pre_prepare_in_log_log_pre_prepares_false in Heqb; pbft_simplifier.
  Qed.
  Hint Resolve implies_pre_prepare_in_log_log_pre_prepares : pbft.

  Hint Resolve pre_prepares_are_between_water_marks_if_in_log : pbft.

  Lemma pre_prepares_are_between_water_marks_if_in_log_before :
    forall p d i (eo : EventOrdering) (e : Event) st,
      state_sm_before_event (PBFTreplicaSM i) e = Some st
      -> pre_prepare_in_log p d (log st) = true
      -> check_between_water_marks (low_water_mark st) (pre_prepare2seq p) = true.
  Proof.
    introv eqst prep.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d1|d1]; ginv; subst; simpl in *;[].
    eauto 3 with pbft.
  Qed.
  Hint Resolve pre_prepares_are_between_water_marks_if_in_log_before : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_in_log2 :
    forall slf prep pp d state state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state (pp,d) = (state', msgs)
      -> prepare_in_log prep (log state') = true
      -> prepare_in_log prep (log state) = true
         \/
         (
           prep
           = request_data_and_rep_toks2prepare
               (pre_prepare2request_data pp d)
               (pre_prepare2rep_toks_of_prepare slf (local_keys state) pp d)
           /\ low_water_mark state < pre_prepare2seq pp
           /\ prepare_in_log prep (log state) = false
           /\ pre_prepare_in_log pp d (log state') = true
         ).
  Proof.
    introv h q.
    unfold add_prepare_to_log_from_new_view_pre_prepare in h; smash_pbft.

    match goal with
    | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
      apply check_send_replies_preserves_log in H; simpl in *; subst
    end.

    match goal with
    | [ H : add_new_pre_prepare_and_prepare2log _ _ _ _ _ _ = _ |- _ ] =>
      eapply add_new_pre_prepare_and_prepare2log_preserves_prepare_in_log2 in H;[| |eauto];
        autorewrite with pbft;auto
    end.
    autorewrite with pbft in *.
    repndors; repnd; tcsp.
  Qed.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log2 :
    forall slf prep pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> prepare_in_log prep (log state') = true
      -> prepare_in_log prep (log state) = true
         \/
         exists pp d,
           In (pp,d) pps
           /\ prep
              = request_data_and_rep_toks2prepare
                  (pre_prepare2request_data pp d)
                  (pre_prepare2rep_toks_of_prepare slf (local_keys state) pp d)
           /\ low_water_mark state < pre_prepare2seq pp
           /\ prepare_in_log prep (log state) = false
           /\ pre_prepare_in_log pp d (log state') = true.
  Proof.
    induction pps; introv h q; simpl in *; smash_pbft; repnd.

    match goal with
    | [ H : add_prepares_to_log_from_new_view_pre_prepares _ _ _ = _ |- _ ] =>
      applydup IHpps in H;auto;[]
    end.
    repndors; tcsp.

    {
      match goal with
      | [ H : add_prepare_to_log_from_new_view_pre_prepare _ _ _ = _ |- _ ] =>
        eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_in_log2 in H;[|eauto]
      end.

      repndors; repnd; tcsp; subst.
      right.
      exists a0 a; dands; auto.
      autorewrite with pbft in *.
      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_forward;[eauto|];auto.
    }

    {
      exrepnd; subst.
      right.

      rename_hyp_with add_prepare_to_log_from_new_view_pre_prepare add.
      applydup add_prepare_to_log_from_new_view_pre_prepare_preserves_cp_state in add.
      apply eq_low_water_marks_if_eq_cp_states in add0.
      rewrite <- add0.

      exists pp d; dands; tcsp; eauto 3 with pbft.

      match goal with
      | [ H : add_prepare_to_log_from_new_view_pre_prepare _ _ _ = _ |- _ ] =>
        apply add_prepare_to_log_from_new_view_pre_prepare_preserves_local_keys in H
      end.
      allrw; auto.
    }
  Qed.

  Lemma prepares_are_between_water_marks_if_in_log_before :
    forall p i (eo : EventOrdering) (e : Event) st,
      state_sm_before_event (PBFTreplicaSM i) e = Some st
      -> prepare_in_log p (log st) = true
      -> check_between_water_marks (low_water_mark st) (prepare2seq p) = true.
  Proof.
    introv eqst prep.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d|d]; ginv; subst; simpl in *; tcsp;
      eauto 3 with pbft;
      try (complete (eapply prepares_are_between_water_marks_if_in_log; eauto)).
  Qed.
  Hint Resolve prepares_are_between_water_marks_if_in_log_before : pbft.

  Lemma check_one_stable_preserves_prepare_in_log3 :
    forall (eo : EventOrdering) e i s l p,
      well_formed_log (log s)
      -> state_sm_before_event (PBFTreplicaSM i) e = Some s
      -> prepare_in_log p (log (check_one_stable i s l)) = true
      -> prepare_in_log p (log s) = true /\
         low_water_mark (check_one_stable i s l) < prepare2seq p.
  Proof.
    introv wf eqst prep.
    applydup check_one_stable_preserves_prepare_in_log in prep; auto.
    eapply prepares_are_between_water_marks_if_in_log_before in eqst; eauto.
    unfold check_between_water_marks in *; smash_pbft.
    apply check_one_stable_preserves_prepare_in_log2; auto.
  Qed.

  Lemma implies_prepare_in_log_check_one_stable :
    forall p i s l,
      prepare_in_log p (log s) = true
      -> low_water_mark (check_one_stable i s l) < prepare2seq p
      -> prepare_in_log p (log (check_one_stable i s l)) = true.
  Proof.
    induction l; introv prep lwm; simpl in *; smash_pbft;[].
    clear IHl.
    unfold check_stable in *; smash_pbft.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    rename_hyp_with checkpoint_entry2stable check.
    apply checkpoint_entry2stable_implies_same_sn2 in check.
    rewrite check in *; simpl in *.
    apply prepare_in_log_clear_log_checkpoint_false_implies in Heqb; pbft_simplifier.
  Qed.
  Hint Resolve implies_prepare_in_log_check_one_stable : pbft.

  Lemma implies_pre_prepare_in_log_check_one_stable :
    forall p d i s l,
      pre_prepare_in_log p d (log s) = true
      -> low_water_mark (check_one_stable i s l) < pre_prepare2seq p
      -> pre_prepare_in_log p d (log (check_one_stable i s l)) = true.
  Proof.
    induction l; introv prep lwm; simpl in *; smash_pbft;[].
    clear IHl.
    unfold check_stable in *; smash_pbft.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    rename_hyp_with checkpoint_entry2stable check.
    apply checkpoint_entry2stable_implies_same_sn2 in check.
    rewrite check in *; simpl in *.
    apply pre_prepare_in_log_clear_log_checkpoint_false_implies in Heqb; pbft_simplifier.
  Qed.
  Hint Resolve implies_pre_prepare_in_log_check_one_stable : pbft.

  Lemma PBFT_A_1_2_7 :
    forall (eo : EventOrdering)
           (e  : Event)
           (i  : Rep)
           (v  : View)
           (n  : SeqNum)
           (d  : PBFTdigest)
           (a  : Tokens)
           (st : PBFTstate),
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> prepare_in_log (mk_prepare v n d i a) (log st) = true
      -> exists r a', pre_prepare_in_log (mk_pre_prepare v n r a') d (log st) = true.
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers3 smash_pbft_ind3.

    (* 7 subgoals left! *)

    {
      (* pre-prepare *)

      rename_hyp_with add_new_pre_prepare_and_prepare2log add.
      rename_hyp_with own_prepare_is_already_logged_with_different_digest own.
      rename_hyp_with check_send_replies check.
      rename_hyp_with prepare_in_log prep.

      eapply check_send_replies_preserves_prepare_in_log in prep;[|eauto].
      simpl in prep.

      eapply add_new_pre_prepare_and_prepare2log_preserves_prepare_in_log2 in prep;
        [| |eauto]; simpl in *; autorewrite with pbft in *; auto;[].

      repndors.

      - assert (exists r a', pre_prepare_in_log (mk_pre_prepare v n r a') d (log p) = true)
          as h by (smash_pbft_ind ind).
        exrepnd.
        exists r a'.

        eapply check_send_replies_preserves_pre_prepare_in_log_forward;[eauto|]; simpl.
        eapply add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log_forward;[eauto|];auto.

      - repnd.
        destruct p0, b; simpl in *.
        unfold mk_prepare, pre_prepare2prepare in *; simpl in *.
        ginv.

        eexists; eexists.

        eapply check_send_replies_preserves_pre_prepare_in_log_forward;[eauto|]; simpl.
        unfold mk_pre_prepare.
        eauto.
    }

    {
      (* prepare *)

      rename_hyp_with add_new_prepare2log add.
      rename_hyp_with check_send_replies check.
      rename_hyp_with prepare_in_log prep.

      eapply check_send_replies_preserves_prepare_in_log in prep;[|eauto].
      simpl in prep.

      eapply add_new_prepare2log_preserves_prepare_in_log in prep;[|eauto].
      repndors;[|repnd; subst; simpl in *; tcsp];[].

      assert (exists r a', pre_prepare_in_log (mk_pre_prepare v n r a') d (log p) = true)
        as h by (smash_pbft_ind ind).
      exrepnd.
      eexists; eexists.

      eapply check_send_replies_preserves_pre_prepare_in_log_forward;[eauto|]; simpl.
      eapply add_new_prepare2log_preserves_pre_prepare_in_log_true_backward;[eauto|]; eauto.
    }

    {
      (* commit *)

      rename_hyp_with add_new_commit2log add.
      rename_hyp_with check_send_replies check.
      rename_hyp_with prepare_in_log prep.

      eapply check_send_replies_preserves_prepare_in_log in prep;[|eauto].
      simpl in prep.
      dup add as add'.
      eapply add_new_commit2log_preserves_prepare_in_log in add'.
      rewrite add' in prep; clear add'.

      assert (exists r a', pre_prepare_in_log (mk_pre_prepare v n r a') d (log p) = true)
        as h by (smash_pbft_ind ind).
      exrepnd.
      eexists; eexists.

      eapply check_send_replies_preserves_pre_prepare_in_log_forward;[eauto|]; simpl.
      eapply add_new_commit2log_preserves_pre_prepare_in_log_true_backward;[eauto|]; eauto.
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.
      rename_hyp_with prepare_in_log prep.

      eapply find_and_execute_requests_preserves_prepare_in_log in prep;[|eauto].

      assert (exists r a', pre_prepare_in_log (mk_pre_prepare v n r a') d (log p) = true)
        as h by (smash_pbft_ind ind).
      exrepnd.
      eexists; eexists.
      eapply find_and_execute_requests_preserves_pre_prepare_in_log_forward; eauto.
    }

    {
      (* check-stable *)

      rename_hyp_with prepare_in_log prep.

      dup prep as prep'.
      eapply check_one_stable_preserves_prepare_in_log3 in prep';[|eauto 2 with pbft|eauto].
      repnd; simpl in *.

      assert (exists r a', pre_prepare_in_log (mk_pre_prepare v n r a') d (log p) = true)
        as h by (smash_pbft_ind ind).
      exrepnd.
      eexists; eexists; eauto 3 with pbft.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with CheckBCastNewView2entry cb.
      rename_hyp_with update_state_new_view upd.
      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with prepare_in_log prep.

      applydup CheckBCastNewView2entry_some_implies in cb.

      match goal with
      | [ H : check_broadcast_new_view ?u ?v ?w = Some (?a, ?b, ?c, ?d) |- _ ] =>
        rename w into entry; rename a into nv; rename b into entry'; rename c into OP; rename d into NP
      end.

      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 4 with pbft;[].

      eapply update_state_new_view_preserves_prepare_in_log2 in prep;
        [| | |eauto]; simpl in *; autorewrite with pbft in *; eauto 4 with pbft;[].
      exrepnd.

      assert (exists r a', pre_prepare_in_log (mk_pre_prepare v n r a') d (log p) = true)
        as h by (smash_pbft_ind ind).
      exrepnd.
      eexists; eexists.
      eapply update_state_new_view_preserves_pre_prepare_in_log_true_forward;
        [|eauto| |];simpl;[| |apply implies_pre_prepare_in_log_log_pre_prepares;eauto];
          eauto 3 with pbft.
      repndors; repnd; tcsp; try omega.

      eapply pre_prepares_are_between_water_marks_if_in_log_before in h1;[|eauto]; simpl in *.
      unfold check_between_water_marks in *; smash_pbft.
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with correct_new_view cor.
      rename_hyp_with prepare_in_log prep.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_low_water_mark in add.
      simpl in *; autorewrite with pbft in *.

      eapply update_state_new_view_preserves_prepare_in_log2 in prep;
        [| | |eauto]; simpl in *; autorewrite with pbft in *; eauto 4 with pbft;[].
      exrepnd.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log2 in prep2;[|eauto].
      simpl in *; autorewrite with pbft in *.

      hide_hyp prep0.
      repndors;[|].

      - assert (exists r a', pre_prepare_in_log (mk_pre_prepare v n r a') d (log p) = true)
          as h by (smash_pbft_ind ind).
        exrepnd.
        dup h1 as bwm.
        eapply pre_prepares_are_between_water_marks_if_in_log_before in bwm;[|eauto]; simpl in *.
        unfold check_between_water_marks in *; smash_pbft.

        eexists; eexists.

        eapply update_state_new_view_preserves_pre_prepare_in_log_true_forward;
          [|eauto| |];simpl; auto;
            [show_hyp prep0; repndors; repnd; tcsp; try omega; try congruence|];[].

        eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_in_log_forward;[eauto|].
        simpl; eauto.

      - exrepnd.
        destruct pp, b; simpl in *.
        unfold mk_prepare in prep4; ginv; simpl in *.

        eexists; eexists.
        eapply update_state_new_view_preserves_pre_prepare_in_log_true_forward; eauto.
        simpl.
        show_hyp prep0.
        repndors; repnd; tcsp; try omega; try congruence.
    }
  Qed.
  Hint Resolve PBFT_A_1_2_7 : pbft.

  Lemma PBFT_A_1_2_7_before :
    forall (eo : EventOrdering)
           (e  : Event)
           (i  : Rep)
           (v  : View)
           (n  : SeqNum)
           (d  : PBFTdigest)
           (a  : Tokens)
           (st : PBFTstate),
      state_sm_before_event (PBFTreplicaSM i) e = Some st
      -> prepare_in_log (mk_prepare v n d i a) (log st) = true
      -> exists r a', pre_prepare_in_log (mk_pre_prepare v n r a') d (log st) = true.
  Proof.
    introv eqst prep.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in eqst.
    destruct (dec_isFirst e) as [di|di]; ginv; eauto 3 with pbft.
  Qed.
  Hint Resolve PBFT_A_1_2_7_before : pbft.

End PBFT_A_1_2_7.


Hint Resolve implies_pre_prepare_in_log_add_new_pre_prepare2log : pbft.
Hint Resolve add_new_prepare2log_preserves_pre_prepare_in_log_true_backward : pbft.
Hint Resolve add_new_commit2log_preserves_pre_prepare_in_log_true_backward : pbft.
Hint Resolve implies_pre_prepare_in_log_clear_log_checkpoint : pbft.
Hint Resolve implies_pre_prepare_in_log_log_pre_prepares : pbft.
Hint Resolve pre_prepares_are_between_water_marks_if_in_log : pbft.
Hint Resolve pre_prepares_are_between_water_marks_if_in_log_before : pbft.
Hint Resolve prepares_are_between_water_marks_if_in_log_before : pbft.
Hint Resolve implies_prepare_in_log_check_one_stable : pbft.
Hint Resolve implies_pre_prepare_in_log_check_one_stable : pbft.
Hint Resolve PBFT_A_1_2_7 : pbft.
Hint Resolve PBFT_A_1_2_7_before : pbft.


Hint Rewrite @matching_requests_same : pbft.
