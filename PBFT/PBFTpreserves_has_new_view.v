(*

  Copyright 2016 Luxembourg University
  Copyright 2017 Luxembourg University
  Copyright 2018 Luxembourg University

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


Require Export PBFTwell_formed_log.
Require Export PBFTwf_view_change_state.
Require Export PBFThas_new_view.
Require Export PBFTpre_prepares_are_received.
Require Export PBFTordering.
Require Export PBFTprops3.
Require Export PBFT_A_1_2_5.
Require Export PBFTnew_view_in_log.
Require Export PBFTcheck_broadcast_new_view.
Require Export PBFTnew_view_util.


Section PBFTpreserves_has_new_view.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  (* !!MOVE to wf_view_change_state *)
  Lemma wf_view_change_state_implies_same_entries_if_same_views :
    forall s e1 e2,
      wf_view_change_state s
      -> In e1 s
      -> In e2 s
      -> vce_view e1 = vce_view e2
      -> e1 = e2.
  Proof.
    induction s; introv wf i1 i2 h; simpl in *; tcsp.
    inversion wf as [|? ? imp wfe wfs]; clear wf; subst.
    repndors; subst; tcsp.

    - apply imp in i1; tcsp.

    - apply imp in i2; tcsp.
  Qed.

  Lemma view_changed_entry_some_implies_has_new_view_false :
    forall cview entry vc s,
      wf_view_change_state s
      -> In entry s
      -> view_changed_entry cview entry = Some vc
      -> has_new_view s (vce_view entry) = false.
  Proof.
    introv wf i h.
    unfold view_changed_entry in h; smash_pbft.
    unfold has_new_view; smash_pbft.

    { match goal with
      | [ H : vce_view entry = _ |- _ ] => rewrite H in *; simpl in *; omega
      end. }

    unfold has_new_view1.
    rewrite existsb_false.
    introv j; smash_pbft.

    match goal with
    | [ H : vce_view _ = vce_view _ |- _ ] =>
      eapply wf_view_change_state_implies_same_entries_if_same_views in H;
        [|eauto| |]; auto; subst
    end.

    match goal with
    | [ H : vce_new_view _ = _ |- _ ] => rewrite H in *; simpl in *; ginv
    end.
  Qed.

  Lemma check_broadcast_new_view_implies_eq_views :
    forall i s entry nv e' OP NP,
      wf_view_change_entry entry
      -> check_broadcast_new_view i s entry = Some (nv, e', OP, NP)
      -> new_view2view nv = vce_view entry.
  Proof.
    introv wf check.
    unfold check_broadcast_new_view in check; smash_pbft.
    symmetry.
    eapply view_changed_entry_some_implies_vce_view_equal_view_change2view; eauto.
  Qed.

  Hint Resolve select_some_implies_in : list.

  Lemma vce_view_add_new_view_to_entry :
    forall entry nv,
      vce_view (add_new_view_to_entry entry nv) = vce_view entry.
  Proof.
    introv; destruct entry; simpl.
    destruct vce_new_view; simpl; auto.
  Qed.
  Hint Rewrite vce_view_add_new_view_to_entry : pbft.

  Fixpoint find_view_entry
             (s : PBFTviewChangeState)
             (v : View) : option PBFTviewChangeEntry :=
    match s with
    | [] => None
    | entry :: entries =>
      if ViewDeq v (vce_view entry) then Some entry
      else find_view_entry entries v
    end.

  Lemma find_view_entry_implies_in :
    forall s v e,
      find_view_entry s v = Some e
      -> In e s /\ vce_view e = v.
  Proof.
    induction s; introv find; simpl in *; ginv; smash_pbft.
    apply IHs in find; tcsp.
  Qed.

  Lemma implies_in_log_new_view :
    forall s nv,
    exists e nv',
      find_view_entry (log_new_view s nv) (new_view2view nv) = Some e
      /\ vce_new_view e = Some nv'
      /\
      (
        nv' = nv
        \/
        find_view_entry s (new_view2view nv) = Some e
      ).
  Proof.
    induction s; introv; simpl; smash_pbft; tcsp.

    - eexists; eexists; dands; eauto.
      simpl; auto.

    - exists (add_new_view_to_entry a nv); simpl.
      destruct a; simpl in *.
      destruct vce_new_view; simpl in *; GC; subst; simpl in *.

      + exists n; simpl; dands; auto; smash_pbft.

      + exists nv; simpl; dands; auto; smash_pbft.
  Qed.

  Lemma find_view_entry_implies_new_view_in_log :
    forall s e nv v,
      new_view2view nv = vce_view e
      -> vce_new_view e = Some nv
      -> find_view_entry s v = Some e
      -> new_view_in_log nv s.
  Proof.
    induction s; introv eqv eqnv find; simpl in *; ginv.
    smash_pbft.
    destruct a; simpl in *; subst; tcsp.
    destruct e; simpl in *; subst; tcsp.
    apply find_view_entry_implies_in in find; simpl in find; repnd; subst; tcsp.
  Qed.
  Hint Resolve find_view_entry_implies_new_view_in_log : pbft.

  Lemma implies_in_log_new_view_and_entry :
    forall s nv entry,
      vce_view entry = new_view2view nv
      ->
      exists e nv',
        find_view_entry (log_new_view_and_entry s nv entry) (new_view2view nv) = Some e
        /\ vce_new_view e = Some nv'
        /\
        (
          nv' = nv
          \/
          (
            e = entry
            /\ vce_new_view entry = Some nv'
          )
        ).
  Proof.
    induction s; introv eqvs; simpl; smash_pbft; tcsp.

    - exists (add_new_view_to_entry entry nv).
      destruct entry, vce_new_view; simpl in *.

      + exists n; simpl; dands; auto.

      + exists nv; simpl; dands; auto.

    - exists (add_new_view_to_entry entry nv).
      destruct entry, vce_new_view; simpl in *.

      + exists n; simpl; dands; auto.

      + exists nv; simpl; dands; auto.
  Qed.

  Lemma create_new_prepare_messages_seq_num :
    forall L v keys P OP NP pp d,
      create_new_prepare_messages L v keys P = (OP, NP)
      -> In (pp, d) (OP ++ NP)
      -> In (pre_prepare2seq pp) L.
  Proof.
    induction L; introv create i; simpl in *; pbft_simplifier; simpl in *; tcsp.
    smash_pbft; repndors; subst; simpl in *.

    - match goal with
      | [ H : create_new_prepare_message _ _ _ _ = _ |- _ ] =>
        apply create_new_prepare_message_implies_same_sequence_number in H
      end; subst; tcsp.

    - eapply IHL in i; [|eauto]; tcsp.

    - apply in_app_cons_implies_in_cons_app in i; repndors; subst; tcsp.

      + match goal with
        | [ H : create_new_prepare_message _ _ _ _ = _ |- _ ] =>
          apply create_new_prepare_message_implies_same_sequence_number in H
        end; subst; tcsp.

      + eapply IHL in i; [|eauto]; tcsp.
  Qed.

  Lemma create_new_prepare_messages_unique_seq :
    forall L v keys P OP NP pp1 pp2 d1 d2,
      no_repeats L
      -> create_new_prepare_messages L v keys P =(OP, NP)
      -> In (pp1, d1) (OP ++ NP)
      -> In (pp2, d2) (OP ++ NP)
      -> pre_prepare2seq pp1 = pre_prepare2seq pp2
      -> pp1 = pp2 /\ d1 = d2.
  Proof.
    induction L; introv norep create i1 i2 eqseqs; simpl in *; pbft_simplifier; simpl in *; tcsp.
    smash_pbft; repndors; subst; simpl in *; pbft_simplifier; allrw no_repeats_cons; repnd; tcsp.

    - match goal with
      | [ H : create_new_prepare_message _ _ _ _ = _ |- _ ] =>
        apply create_new_prepare_message_implies_same_sequence_number in H
      end; subst.

      match goal with
      | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
        eapply create_new_prepare_messages_seq_num in H;[|eauto]
      end.

      congruence.

    - match goal with
      | [ H : create_new_prepare_message _ _ _ _ = _ |- _ ] =>
        apply create_new_prepare_message_implies_same_sequence_number in H
      end; subst.

      match goal with
      | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
        eapply create_new_prepare_messages_seq_num in H;[|eauto]
      end.

      congruence.

    - eapply IHL; eauto.

    - match goal with
      | [ H : create_new_prepare_message _ _ _ _ = _ |- _ ] =>
        apply create_new_prepare_message_implies_same_sequence_number in H
      end; subst.

      apply in_app_cons_implies_in_cons_app in i1.
      apply in_app_cons_implies_in_cons_app in i2.
      repndors; ginv.

      + match goal with
        | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
          eapply create_new_prepare_messages_seq_num in H;[|eauto]
        end.

        congruence.

      + match goal with
        | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
          eapply create_new_prepare_messages_seq_num in H;[|eauto]
        end.

        congruence.

      + eapply IHL; eauto.
  Qed.

  Lemma check_broadcast_new_view_unique_seq :
    forall i state entry nv OP NP pp1 pp2 d1 d2,
      check_broadcast_new_view i state entry = Some (nv, OP, NP)
      -> In (pp1, d1) (OP ++ NP)
      -> In (pp2, d2) (OP ++ NP)
      -> pre_prepare2seq pp1 = pre_prepare2seq pp2
      -> pp1 = pp2 /\ d1 = d2.
  Proof.
    introv check i1 i2 epreps.
    unfold check_broadcast_new_view in check; smash_pbft;[].

    match goal with
    | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
      eapply create_new_prepare_messages_unique_seq in H;[| |exact i1|exact i2|]
    end; auto; eauto 2 with pbft.
  Qed.

  Lemma pre_prepare_in_log_implies_has_new_view :
    forall (eo : EventOrdering)
           (e  : Event)
           (i  : Rep)
           (pp : Pre_prepare)
           (d  : PBFTdigest)
           (st : PBFTstate),
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> pre_prepare_in_log pp d (log st) = true
      -> has_new_view (view_change_state st) (pre_prepare2view pp) = true.
  Proof.
    introv eqst prep.

    dup prep as prep'.
    destruct pp, b.
    eapply pre_prepares_are_received in prep'; exrepnd;[|eauto]; auto;[].

    repndors; exrepnd; subst; simpl in *; tcsp;[| | |].

    - rename_hyp_with has_new_view has_new_view_true.

      dup has_new_view_true as has_new_view_true'.
      applydup localLe_implies_loc in prep'1.
      eapply PBFThas_new_view_is_preserved2 in has_new_view_true';
        [| |eauto|exact eqst]; auto; try congruence.

    - rename_hyp_with has_new_view has_new_view_true.

      dup has_new_view_true as has_new_view_true'.
      applydup localLe_implies_loc in prep'1.
      eapply PBFThas_new_view_is_preserved2 in has_new_view_true';
        [| |eauto|exact eqst]; auto; try congruence.

    - assert (wf_view_change_state (view_change_state st1)) as wfs1 by eauto 2 with pbft.
      assert (wf_view_change_entry entry) as wfe by eauto 3 with pbft list.

      rename_hyp_with check_broadcast_new_view check.
      rename_hyp_with view_changed_entry ch.
      rename_hyp_with @select sel.

      applydup @select_some_implies_in in sel.

      applydup check_broadcast_new_view_generates in check.
      applydup check_broadcast_new_view_implies_eq_views in check; auto;[].

      applydup view_changed_entry_some_implies_vce_view_equal_view_change2view in ch; auto;[].

      assert (has_new_view (view_change_state st2) (view_change2view vc) = true) as has_new_view_true.
      {
        allrw.
        unfold has_new_view; smash_pbft;[].
        unfold has_new_view1.
        rewrite existsb_exists.

        pose proof (implies_in_log_new_view_and_entry (view_change_state st1) nv entry') as q.
        autodimp q hyp;
          [symmetry; eapply check_broadcast_new_view_implies_equal_views;[|eauto];
           eauto 3 with pbft|];[].
        exrepnd.

        applydup find_view_entry_implies_in in q0; repnd.
        exists e0; dands; auto.
        allrw; smash_pbft.
      }

      eapply PBFThas_new_view_is_preserved3; eauto.

    - assert (wf_view_change_state (view_change_state st1)) as wfs1 by eauto 2 with pbft.

      match goal with
      | [ H : context[correct_new_view] |- _ ] => rename H into cor
      end.
      dup cor as cor'.
      eapply pre_prepare_in_map_correct_new_view_implies in cor';[|eauto].

      assert (has_new_view (view_change_state st2) v = true) as has_new_view_true.
      {
        allrw.
        unfold has_new_view; smash_pbft;[].
        unfold has_new_view1.
        rewrite existsb_exists.

        pose proof (implies_in_log_new_view (view_change_state st1) nv) as q; exrepnd.
        applydup find_view_entry_implies_in in q0; repnd.
        exists e0; dands; auto.
        allrw; smash_pbft.
      }

      eapply PBFThas_new_view_is_preserved3; eauto.
  Qed.

  Lemma pre_prepare_in_log_implies_has_new_view_before :
    forall (eo : EventOrdering)
           (e  : Event)
           (i  : Rep)
           (pp : Pre_prepare)
           (d  : PBFTdigest)
           (st : PBFTstate),
      state_sm_before_event (PBFTreplicaSM i) e = Some st
      -> pre_prepare_in_log pp d (log st) = true
      -> has_new_view (view_change_state st) (pre_prepare2view pp) = true.
  Proof.
    introv eqst prep.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d1|d1]; ginv; subst; simpl in *;[].
    eapply pre_prepare_in_log_implies_has_new_view in eqst; eauto.
  Qed.

End PBFTpreserves_has_new_view.


Hint Resolve select_some_implies_in : list.


Hint Resolve find_view_entry_implies_new_view_in_log : pbft.


Hint Rewrite @vce_view_add_new_view_to_entry : pbft.
