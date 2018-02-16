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


Require Export PBFT.
Require Export PBFTprops2.
Require Export PBFTtactics.
Require Export PBFTwell_formed_log.
Require Export PBFTordering.
(*Require Export PBFTprops3.*)
Require Export PBFTnew_view_in_log. (* there are some lemmas that preserve state *)
Require Export PBFTwf_view_change_state.



Section PBFTview_new_in_log.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition mk_view_change
             (v   : View)
             (n   : SeqNum)
             (s   : StableChkPt)
             (C   : CheckpointCert)
             (P   : list PreparedInfo)
             (i   : Rep)
             (a  : Tokens) : ViewChange :=
    view_change (bare_view_change v n s C P i) a.

  Fixpoint view_change_in_log_entry
           (vc : ViewChange)
           (L  : list ViewChange) : Prop :=
    match L with
    | [] => False
    | entry :: entries =>
      if rep_deq (view_change2sender vc) (view_change2sender entry) then

        entry = vc

      else view_change_in_log_entry vc entries
    end.

  Fixpoint view_change_in_log
           (vc : ViewChange)
           (S  : PBFTviewChangeState) : Prop :=
    match S with
    | [] => False
    | entry :: entries =>
      if ViewDeq (view_change2view vc) (vce_view entry) then
        view_change_in_log_entry vc (vce_view_changes entry)
      else view_change_in_log vc entries
    end.

  Lemma check_send_replies_preserves_view_change_in_log :
    forall vc slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> view_change_in_log vc (view_change_state state')
      -> view_change_in_log vc (view_change_state state).
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_view_change_in_log : pbft.

  Lemma check_send_replies_update_log_preserves_view_change_in_log :
    forall vc slf view keys entryop state L sn msgs state',
      check_send_replies slf view keys entryop (update_log state L) sn = (msgs, state')
      -> view_change_in_log vc (view_change_state state')
      -> view_change_in_log vc (view_change_state state).
  Proof.
    introv chk pil.
    eapply check_send_replies_preserves_view_change_in_log in chk;[|eauto].
    simpl in *; auto.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_view_change_in_log : pbft.

  Lemma check_stable_preserves_view_change_in_log :
    forall vc slf state entryop state',
      check_stable slf state entryop = Some state'
      -> view_change_in_log vc (view_change_state state')
      -> view_change_in_log vc (view_change_state state).
  Proof.
    introv h; unfold check_stable in h; smash_pbft.
  Qed.
  Hint Resolve check_stable_preserves_view_change_in_log : pbft.

  Lemma change_log_entry_preserves_view_change_in_log :
    forall vc new_log st,
      view_change_in_log vc (view_change_state (change_log_entry st new_log))
      =
      view_change_in_log vc (view_change_state st).
  Proof.
    unfold change_log_entry in *.
    simpl in *.
    tcsp.
  Qed.
  Hint Rewrite change_log_entry_preserves_view_change_in_log : pbft.

  Lemma change_last_reply_preserves_view_change_in_log :
    forall vc new_log st,
      view_change_in_log vc (view_change_state (change_last_reply_state st new_log))
      =
      view_change_in_log vc (view_change_state st).
  Proof.
    unfold change_last_reply_state in *.
    simpl in *.
    tcsp.
  Qed.
  Hint Rewrite change_last_reply_preserves_view_change_in_log : pbft.

  Lemma change_sm_state_preserves_view_change_in_log :
    forall vc new_log st,
      view_change_in_log vc (view_change_state (change_sm_state st new_log))
      =
      view_change_in_log vc (view_change_state st).
  Proof.
    unfold change_sm_state in *.
    simpl in *.
      tcsp.
  Qed.
  Hint Rewrite change_sm_state_preserves_view_change_in_log : pbft.

  Lemma increment_next_to_execute_preserves_view_change_in_log :
    forall vc st,
      view_change_in_log vc (view_change_state (increment_next_to_execute st))
      =
      view_change_in_log vc (view_change_state st).
  Proof.
      unfold increment_next_to_execute in *.
      simpl in *.
      tcsp.
  Qed.
  Hint Rewrite increment_next_to_execute_preserves_view_change_in_log : pbft.

  Lemma find_and_execute_requests_preserves_view_change_in_log :
    forall vc msg i v keys st p,
      find_and_execute_requests i v keys p = (msg, st)
      -> view_change_in_log vc (view_change_state st)
      -> view_change_in_log vc (view_change_state p).
  Proof.
    introv H1 H2.

    unfold find_and_execute_requests in *.
    smash_pbft.
    rename x1 into st.
    unfold execute_requests in *.
    smash_pbft.
    destruct (ready p); simpl in *;[ inversion Heqx; allrw; tcsp |].

    pbft_dest_all y.

    match goal with
    | [ H : context[reply2requests] |- _ ] => hide_hyp H
    end.

    match goal with
    | [ H : check_broadcast_checkpoint _ _ _ _ _ = _ |- _ ] =>
      eapply check_broadcast_checkpoint_preserves_view_change_state in H
    end.

    match goal with
    | [ H1 : view_change_in_log _ (view_change_state ?s), H2 : _ = view_change_state ?s |- _ ] =>
      rewrite <- H2 in H1; clear H2
    end.

    match goal with
    | [ H : view_change_in_log _ _ |- _ ] =>
      rewrite change_log_entry_preserves_view_change_in_log in H
    end.


    match goal with
    | [ H : view_change_in_log _ _ |- _ ] =>
      rewrite change_last_reply_preserves_view_change_in_log in H
    end.

    match goal with
    | [ H : view_change_in_log _ _ |- _ ] =>
      rewrite change_sm_state_preserves_view_change_in_log in H
    end.

    match goal with
    | [ H : view_change_in_log _ _ |- _ ] =>
      rewrite increment_next_to_execute_preserves_view_change_in_log in H
    end.
    auto.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_view_change_in_log : pbft.

 Lemma add_own_view_change_to_state_preserves_view_change_in_log :
    forall vc vc' vc_state vc_state' vc_entry,
      start_view_change vc vc_state = (vc_entry, vc_state')
      -> view_change_in_log vc' vc_state'
      -> view_change_in_log vc' vc_state.
  Proof.
    induction vc_state; introv svc h; simpl in *; ginv; simpl in *; smash_pbft; tcsp.

    unfold own_view_change2initial_entry in *.
    simpl in *; smash_pbft.
  Qed.
  Hint Resolve add_own_view_change_to_state_preserves_view_change_in_log : pbft.

  Lemma view_change_in_log_entry_implies_in :
    forall vc L,
      view_change_in_log_entry vc L
      -> In vc L.
  Proof.
    induction L; introv H; simpl in *; ginv; simpl in *; smash_pbft; tcsp.
  Qed.
  Hint Resolve view_change_in_log_entry_implies_in : pbft.

  Lemma in_implies_view_change_in_log_entry :
    forall vc L,
      In vc L
      ->  view_change_in_log_entry vc L
          \/
          exists entry, vc = entry.
  Proof.
    induction L; introv H; simpl in *; auto; smash_pbft; tcsp.
  Qed.

  Lemma add_view_change2view_changes_preserves_view_change_in_log :
    forall vc vc' L1 L2,
      view_change_in_log_entry vc' L2
      -> add_view_change2view_changes vc L1 = Some L2
      -> view_change_in_log_entry vc' L1 \/ vc = vc'.
  Proof.
    induction L1; introv i h; repeat (simpl in *; smash_pbft).
  Qed.
  Hint Resolve add_view_change2view_changes_preserves_view_change_in_log : pbft.

  Lemma add_other_view_change2entry_preserves_view_change_in_log :
    forall vc vc' entry1 entry2,
      view_change_in_log_entry vc' (vce_view_changes entry2)
      -> add_other_view_change2entry vc entry1 = Some entry2
      -> view_change_in_log_entry vc' (vce_view_changes entry1) \/ vc = vc'.
  Proof.
    destruct entry1, entry2; introv h q; simpl in *; smash_pbft.
  Qed.
  Hint Resolve add_other_view_change2entry_preserves_view_change_in_log : pbft.

  Lemma add_other_view_change2entry_preserves_view :
    forall vc entry1 entry2,
      add_other_view_change2entry vc entry1 = Some entry2
      -> vce_view entry2 = vce_view entry1.
  Proof.
    destruct entry1, entry2; introv h; simpl in *; smash_pbft.
  Qed.
  Hint Resolve add_other_view_change2entry_preserves_view : pbft.

  Lemma add_other_view_change_preserves_view_change_in_log :
    forall vc vc' vc_state vc_entry vc_state',
      add_other_view_change vc vc_state = Some (vc_entry, vc_state')
      -> view_change_in_log vc' vc_state'
      -> view_change_in_log vc' vc_state
         \/
         vc = vc'.
  Proof.
    induction vc_state; introv svc h; simpl in *; ginv; simpl in *; smash_pbft; tcsp.

    {
      unfold other_view_change2initial_entry in *.
      simpl in *; smash_pbft; tcsp.
    }

    {
      match goal with
      | [ H : add_other_view_change2entry _ _ = _ |- _ ] =>
        apply add_other_view_change2entry_preserves_view in H
      end.
      match goal with
      | [ H : _ <> _ |- _ ] => destruct H; congruence
      end.
    }

    {
      unfold add_other_view_change2entry in *.
      destruct a; smash_pbft; tcsp.
    }
  Qed.
  Hint Resolve add_other_view_change_preserves_view_change_in_log : pbft.

  Lemma update_checkpoint_from_new_view_preserves_view_change_in_log :
    forall stablech sn vc state state',
      update_checkpoint_from_new_view state stablech sn = state'
      -> view_change_in_log vc (view_change_state state')
         =
         view_change_in_log vc (view_change_state state).
  Proof.
    introv up.
    unfold update_checkpoint_from_new_view in *. smash_pbft.
  Qed.
  Hint Resolve update_checkpoint_from_new_view_preserves_view_change_in_log : pbft.

  Lemma trim_checkpoint_preserves_view_change_in_log :
    forall vc sn state state',
      trim_checkpoint state sn = state'
      -> view_change_in_log vc (view_change_state state')
         =
         view_change_in_log vc (view_change_state state).
  Proof.
    introv H. unfold trim_checkpoint in *.
    destruct state, state'. simpl in *. inversion H. auto.
  Qed.
  Hint Resolve trim_checkpoint_preserves_view_change_in_log : pbft.

  Lemma log_checkpoint_cert_from_new_view_preserves_view_change_in_log :
    forall vc slf v sn C s och state state',
      log_checkpoint_cert_from_new_view slf state v sn C s = (state', och)
      -> view_change_in_log vc (view_change_state state')
      -> view_change_in_log vc (view_change_state state).
  Proof.
    introv lcp h.
    unfold log_checkpoint_cert_from_new_view in *. smash_pbft.
  Qed.
  Hint Resolve log_checkpoint_cert_from_new_view_preserves_view_change_in_log: pbft.


  Lemma update_state_new_view_preserves_view_change_in_log :
    forall slf vc nv msg state state',
      update_state_new_view slf state nv = (state', msg)
      -> view_change_in_log vc (view_change_state state')
      -> view_change_in_log vc (view_change_state state).
  Proof.
    introv up h.
    unfold update_state_new_view in *; smash_pbft.
  Qed.
  Hint Resolve update_state_new_view_preserves_view_change_in_log : pbft.

  Lemma log_new_view_preserves_view_change_in_log :
    forall vc nv' S,
      view_change_in_log vc (log_new_view S nv')
      -> view_change_in_log vc S.
  Proof.
    introv lnw.

    induction S; simpl in *; tcsp; smash_pbft;
      destruct a; simpl in *; ginv;
        destruct vce_new_view; simpl in *; ginv; tcsp.
  Qed.
  Hint Resolve log_new_view_preserves_view_change_in_log : pbft.

End PBFTview_new_in_log.


Hint Resolve check_send_replies_preserves_view_change_in_log : pbft.
Hint Resolve check_send_replies_update_log_preserves_view_change_in_log : pbft.
Hint Resolve check_stable_preserves_view_change_in_log : pbft.
Hint Resolve add_view_change2view_changes_preserves_view_change_in_log : pbft.
Hint Resolve add_other_view_change2entry_preserves_view_change_in_log : pbft.
Hint Resolve add_other_view_change2entry_preserves_view : pbft.
Hint Resolve find_and_execute_requests_preserves_view_change_in_log : pbft.
Hint Resolve add_own_view_change_to_state_preserves_view_change_in_log : pbft.
Hint Resolve view_change_in_log_entry_implies_in : pbft.
Hint Resolve log_new_view_preserves_view_change_in_log : pbft.
Hint Resolve update_state_new_view_preserves_view_change_in_log : pbft.
Hint Resolve log_checkpoint_cert_from_new_view_preserves_view_change_in_log: pbft.
Hint Resolve trim_checkpoint_preserves_view_change_in_log : pbft.
Hint Resolve update_checkpoint_from_new_view_preserves_view_change_in_log : pbft.
Hint Resolve add_other_view_change_preserves_view_change_in_log : pbft.

Hint Rewrite @change_log_entry_preserves_view_change_in_log : pbft.
Hint Rewrite @change_last_reply_preserves_view_change_in_log : pbft.
Hint Rewrite @change_sm_state_preserves_view_change_in_log : pbft.
Hint Rewrite @increment_next_to_execute_preserves_view_change_in_log : pbft.







