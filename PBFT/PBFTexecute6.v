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


Require Export PBFTexecute5.


Section PBFTexecute6.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context     : PBFTcontext      }.
  Context { pbft_auth        : PBFTauth         }.
  Context { pbft_keys        : PBFTinitial_keys }.
  Context { pbft_hash        : PBFThash         }.
  Context { pbft_hash_axioms : PBFThash_axioms  }.

  Record Coperation :=
    MKCoperation
      {
        cop_op :> PBFToperation;
        cop_c  : Client;
      }.

  Record EventOp (eo : EventOrdering) :=
    MkEventOp
      {
        eop_e  :> Event;
        eop_op : Coperation;
      }.

  Definition state_doesnt_change_between_events {eo : EventOrdering} (i : Rep) (e1 e2 : Event) :=
    forall e,
      e1 ⊏ e
      -> e ⊏ e2
      -> exists s1 s2,
          state_sm_before_event (PBFTreplicaSM i) e = Some s1
          /\ state_sm_on_event (PBFTreplicaSM i) e = Some s2
          /\ PBFT.sm_state s1 = PBFT.sm_state s2
          /\ next_to_execute s1 = next_to_execute s2.

  Definition state_doesnt_change_initial {eo : EventOrdering} (i : Rep) (e : Event) :=
    forall e' s,
      e' ⊏ e
      -> state_sm_on_event (PBFTreplicaSM i) e' = Some s
      -> PBFT.sm_state s = PBFTsm_initial_state
         /\ last_reply_state s = initial_last_reply
         /\ next_to_execute s = 1.

  Definition state_is_updated {eo : EventOrdering} (i : Rep) (e : EventOp eo) (len : nat) :=
    exists s1 s2,
      state_sm_before_event (PBFTreplicaSM i) e = Some s1
      /\ state_sm_on_event (PBFTreplicaSM i) e = Some s2
      /\ PBFT.sm_state s2 = snd (PBFTsm_update (cop_c (eop_op eo e)) (PBFT.sm_state s1) (eop_op eo e))
      /\ next_to_execute s2 = S (next_to_execute s1)
      /\ next_to_execute s1 = S len.

  Definition EventOps (eo : EventOrdering) := list (EventOp eo).

  (*
      We should we also link the operations to the client requests.
      Something along the lines:
        we received the operation from a client with the right timestamp
        such that timestamps are increasing
   *)
  Inductive ordered_eops {eo : EventOrdering} (i : Rep) : Event -> EventOps eo -> Prop :=
  | ordered_eop_nil :
      forall e,
        state_doesnt_change_initial i e
        -> ordered_eops i e []
  | ordered_eop_cons :
      forall e l (x : EventOp eo),
        ordered_eops i x l
        -> loc e = PBFTreplica i
        -> loc x = PBFTreplica i
        -> state_is_updated i x (length l)
        -> state_doesnt_change_between_events i e x
        -> ordered_eops i e (x :: l).
  Hint Constructors ordered_eops : pbft.

  Inductive similar_eventops {eo : EventOrdering} : EventOps eo -> EventOps eo -> Prop :=
  | sim_eventops_nil : similar_eventops [] []
  | sim_eventops_cons :
      forall x y l k,
        similar_eventops l k
        -> eop_op eo x = eop_op eo y
        -> similar_eventops (x :: l) (y :: k).
  Hint Constructors similar_eventops : pbft.

  (* the head is more recent so the first list has to be a final segment of the second one *)
  Inductive sub_eventops {eo : EventOrdering} : EventOps eo -> EventOps eo -> Prop :=
  | sub_eventops_nil :
      forall l k,
        similar_eventops l k
        -> sub_eventops l k
  | sub_eventops_cons :
      forall x l k,
        sub_eventops l k
        -> sub_eventops l (x :: k).
  Hint Constructors sub_eventops : pbft.

  Lemma state_doesnt_change_initial_if_isFirst :
    forall {eo : EventOrdering} (e : Event) i,
      isFirst e
      -> state_doesnt_change_initial i e.
  Proof.
    introv isf lee.
    apply no_local_predecessor_if_first in lee; tcsp.
  Qed.
  Hint Resolve state_doesnt_change_initial_if_isFirst : pbft.

  Lemma next_to_execute_update_checkpoint_form_new_view :
    forall s c n,
      next_to_execute s <= next_to_execute (update_checkpoint_from_new_view s c n).
  Proof.
    introv.
    unfold update_checkpoint_from_new_view; smash_pbft.
  Qed.

  Lemma next_to_execute_trim_checkpoint :
    forall s n,
      next_to_execute (trim_checkpoint s n) = next_to_execute s.
  Proof.
    introv; tcsp.
  Qed.
  Hint Rewrite next_to_execute_trim_checkpoint : pbft.

  Definition update_state_new_view_preserves_next_to_execute :
    forall i s1 nv s2 msgs,
      update_state_new_view i s1 nv = (s2, msgs)
      -> next_to_execute s1 <= next_to_execute s2.
  Proof.
    introv upd; unfold update_state_new_view in upd; smash_pbft.
    rename_hyp_with log_checkpoint_cert_from_new_view check.
    apply log_checkpoint_cert_from_new_view_preserves_next_to_execute in check.
    rewrite <- check.
    eapply le_trans;[|apply next_to_execute_update_checkpoint_form_new_view].
    autorewrite with pbft; simpl; auto.
  Qed.
  Hint Resolve update_state_new_view_preserves_next_to_execute : pbft.

  Lemma next_to_execute_log_new_view_state :
    forall s nv,
      next_to_execute (log_new_view_state s nv) = next_to_execute s.
  Proof.
    introv.
    unfold log_new_view_state; simpl; tcsp.
  Qed.
  Hint Rewrite next_to_execute_log_new_view_state : pbft.

  Lemma next_to_execute_increases_step :
    forall {eo : EventOrdering} (e : Event) i s1 s2,
      state_sm_before_event (PBFTreplicaSM i) e = Some s1
      -> state_sm_on_event (PBFTreplicaSM i) e = Some s2
      -> next_to_execute s1 <= next_to_execute s2.
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers4 smash_pbft_ind3.

    {
      (* pre-prepare *)

      rename_hyp_with check_send_replies check.
      apply check_send_update_log_replies_preserves_next_to_execute in check; allrw; auto.
    }

    {
      (* prepare *)

      rename_hyp_with check_send_replies check.
      apply check_send_update_log_replies_preserves_next_to_execute in check; allrw; auto.
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      apply check_send_update_log_replies_preserves_next_to_execute in check; allrw; auto.
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.
      apply find_and_execute_requests_preserves_next_to_execute in fexec.
      repndors; try rewrite fexec; auto.
      exrepnd; rewrite fexec0; simpl; auto.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with update_state_new_view upd.
      apply update_state_new_view_preserves_next_to_execute in upd;
        simpl in *; eauto 3 with pbft eo.
    }

    {
      (* new-view *)

      rename_hyp_with update_state_new_view upd.
      apply update_state_new_view_preserves_next_to_execute in upd.
      autorewrite with pbft in *.
      rewrite <- upd; clear upd.

      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      apply add_prepares_to_log_from_new_view_pre_prepares_preserves_next_to_execute in add.
      simpl in *; rewrite add; simpl; auto.
    }
  Qed.

  Lemma next_to_execute_increases :
    forall {eo : EventOrdering} (e1 e2 : Event) i s1 s2,
      e1 ⊑ e2
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some s1
      -> state_sm_on_event (PBFTreplicaSM i) e2 = Some s2
      -> next_to_execute s1 <= next_to_execute s2.
  Proof.
    introv.
    revert s2.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[].
    introv lee eqst1 eqst2.

    apply localHappenedBeforeLe_implies_or2 in lee; repndors; subst; tcsp;[|].

    {
      match goal with
      | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; ginv
      end.
    }

    apply local_implies_pred_or_local in lee; repndors; exrepnd.

    {
      eapply state_sm_before_event_if_on_event_direct_pred in lee; [|eauto].
      eapply next_to_execute_increases_step; eauto.
    }

    pose proof (ind e) as q; autodimp q hyp; clear ind.

    pose proof (state_sm_on_event_some_between e e2 (PBFTreplicaSM i) s2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    pose proof (q s') as h; clear q. repeat (autodimp h hyp); eauto 2 with eo.

    eapply state_sm_before_event_if_on_event_direct_pred in lee1;[|eauto].
    eapply next_to_execute_increases_step in lee1;[|eauto]; auto.
    omega.
  Qed.

  Ltac smash_pbft_dands3 := let tac := fun _ => (dands; eauto 3 with pbft) in smash_pbft_tac tac.

  Ltac smash_pbft_ind_dands3 ind :=
    let base_tac := (fun _ => smash_pbft_dands3) in
    let ind_tac  := (fun _ => eauto 2 with pbft) in
    smash_pbft_ind_tac ind base_tac ind_tac.

  Definition state_doesnt_change_initial_le {eo : EventOrdering} (i : Rep) (e : Event) :=
    forall e',
      e' ⊑ e
      ->
      exists s,
        state_sm_on_event (PBFTreplicaSM i) e' = Some s
        /\ PBFT.sm_state s = PBFTsm_initial_state
        /\ last_reply_state s = initial_last_reply
        /\ next_to_execute s = 1.

  (* a bit more general than [state_if_initial_next_to_execute] in PBFTexecute2.v *)
  Lemma state_doesnt_change_if_initial_next_to_execute :
    forall i (eo : EventOrdering) (e : Event) s,
      state_sm_on_event (PBFTreplicaSM i) e = Some s
      -> next_to_execute s = 1 (* initial one is 1 *)
      -> state_doesnt_change_initial_le i e.
  Proof.
    introv eqst next lee.

    pose proof (state_sm_on_event_some_between2 e' e (PBFTreplicaSM i) s) as q.
    repeat (autodimp q hyp); exrepnd.
    exists s'.

    pose proof (next_to_execute_increases e' e i s' s) as w.
    repeat (autodimp w hyp).
    rewrite next in w.
    applydup next_to_execute_is_greater_than_one in q0; simpl in *.
    assert (next_to_execute s' = 1) as y by (apply implies_eq_seq_nums; simpl in *; omega).
    clear w q1.

    applydup state_if_initial_next_to_execute in q0; tcsp.
  Qed.

  Hint Resolve localHappenedBefore_implies_le_local_pred : eo.

  Lemma state_doesnt_change_initial_le_local_pred_implies :
    forall {eo : EventOrdering} (e : Event) i,
      state_doesnt_change_initial_le i (local_pred e)
      -> state_doesnt_change_initial i e.
  Proof.
    introv init lee eqst.
    pose proof (init e') as init.
    autodimp init hyp; eauto 3 with eo.
    exrepnd.
    rewrite eqst in init1; ginv.
  Qed.
  Hint Resolve state_doesnt_change_initial_le_local_pred_implies : pbft.

  Lemma local_ordered_state :
    forall (eo : EventOrdering) (e : Event) (i : Rep),
      has_correct_trace_bounded e
      -> loc e = PBFTreplica i
      -> exists (L : EventOps eo),
          ordered_eops i e L.
  Proof.
    intros eo e.
    induction e as [? ind] using HappenedBeforeInd.
    introv cor eqloci.

    pose proof (PBFTnever_stops _ e i cor) as eqst; exrepnd.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst0.
    unfold ite_first in eqst0.
    destruct (dec_isFirst e); ginv.

    { exists ([] : EventOps eo); eauto 3 with pbft. }

    applydup next_to_execute_is_greater_than_one in eqst0.
    destruct (SeqNumDeq (next_to_execute st) 1) as [d|d].

    {
      (* we'll need to generalize this one to say something about the events in between *)
      pose proof (state_if_initial_next_to_execute i _ (local_pred e) st) as h.
      repeat (autodimp h hyp);[];repnd.
      exists ([] : EventOps eo).
      constructor.

      applydup state_doesnt_change_if_initial_next_to_execute in eqst0; eauto 3 with pbft.
    }

    SearchAbout next_to_execute.

    pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo.
    pose proof (ind i) as ind; autorewrite with eo in ind.
    repeat (autodimp ind hyp); eauto 3 with eo pbft;[].
    exrepnd.

  Qed.

  (* the head is more recent *)
  Inductive sub_operations : list PBFToperation -> list PBFToperation eo -> Prop :=
  | sub_ops_nil :
      forall l, sub_operations l l
  | sub_ops_cons :
      forall x l k,
        sub_operations l k
        -> sub_operations l (x :: k).
  Hint Constructors sub_operations : pbft.

  Fixpoint apply_operations (l : list PBFToperation) (s : PBFTsm_state) : PBFTsm_state :=
    match l with
    | [] => s
    | op :: ops => snd (PBFTsm_update c (apply_operations ops s) op)
    end.

  Definition simple_ordered (eo : EventOrdering) :=
    forall i j e1 e2 s1 s2,
      loc e1 = PBFTreplica i
      -> loc e2 = PBFTreplica j
      -> state_sm_on_event (PBFTreplicaSM i) e1 = Some s1
      -> state_sm_on_event (PBFTreplicaSM j) e2 = Some s2
      ->
      exists (ops1 ops2 : list PBFToperation),
        PBFT.sm_state s1 = apply_operations ops1 PBFTsm_initial_state
        /\ PBFT.sm_state s2 = apply_operations ops2 PBFTsm_initial_state
        /\ (sub_operations ops1 ops2 \/ sub_operations ops2 ops1).

  Lemma ordered_states :
    forall (eo : EventOrdering) (e1 e2 : Event) (i j : Rep),
      has_correct_trace_bounded e1
      -> has_correct_trace_bounded e2
      -> loc e1 = PBFTreplica i
      -> loc e2 = PBFTreplica j
      -> exists (L1 L2 : EventOps eo),
          ordered_eops i e1 L1
          /\ ordered_eops j e2 L2
          /\ (sub_eventops L1 L2 \/ sub_eventops L2 L1).
  Proof.
    intros eo e1.
    induction e1 as [? ind] using HappenedBeforeInd.
    introv cor1 cor2 eqloci eqlocj.

    pose proof (PBFTnever_stops _ e1 i cor1) as eqst; exrepnd.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst0.
    unfold ite_first in eqst0.
    destruct (dec_isFirst e1); ginv.

    {
      
    }

    SearchAbout state_sm_before_event state_sm_on_event.

    SearchAbout next_to_execute.
    Locate PBFTexecute.next_to_execute_from.
  Qed.

End PBFTexecute6.
