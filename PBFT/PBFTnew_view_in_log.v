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
Require Export PBFTwf_view_change_state.


Section PBFTnew_view_in_log.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition mk_new_view
             (v  : View)
             (V  : ViewChangeCert)
             (OP : list Pre_prepare)
             (NP : list Pre_prepare)
             (a  : Tokens) : NewView :=
    new_view (bare_new_view v V OP NP) a.

  Fixpoint new_view_in_log
           (nv : NewView)
           (S  : PBFTviewChangeState) : Prop :=
    match S with
    | [] => False
    | entry :: entries =>
      if ViewDeq (vce_view entry) (new_view2view nv) then

        vce_new_view entry = Some nv

      else new_view_in_log nv entries
    end.

  Lemma check_send_replies_preserves_new_view_in_log :
    forall nv slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> new_view_in_log nv (view_change_state state')
      -> new_view_in_log nv (view_change_state state).
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_new_view_in_log : pbft.


  Lemma update_log_preserves_new_view_in_log :
    forall nv new_log st,
      new_view_in_log nv (view_change_state (update_log st new_log))
      -> new_view_in_log nv (view_change_state st).
  Proof.
    introv H.
    unfold update_log in *.
    simpl in *.
    tcsp.
  Qed.
(*  Hint Resolve update_log_preserves_new_view_in_log : pbft.*)

  Lemma check_stable_preserves_new_view_in_log :
    forall nv slf state entryop state',
      check_stable slf state entryop = Some state'
      -> new_view_in_log nv (view_change_state state')
      -> new_view_in_log nv (view_change_state state).
  Proof.
    introv h; unfold check_stable in h; smash_pbft.
  Qed.
  Hint Resolve check_stable_preserves_new_view_in_log : pbft.

  Lemma check_stable_preserves_view_change_state :
    forall slf state entryop state',
      check_stable slf state entryop = Some state'
      -> view_change_state state' = view_change_state state.
  Proof.
    introv h; unfold check_stable in h; smash_pbft.
  Qed.

  Lemma check_broadcast_checkpoint_preserves_view_change_state:
    forall slf sn view keys msgs state1 state2,
      check_broadcast_checkpoint slf sn view keys state1 = (state2, msgs)
      -> view_change_state state1 = view_change_state state2.
  Proof.
    introv h; unfold check_broadcast_checkpoint in h.
    pbft_dest_all x.
  Qed.

  Lemma change_log_entry_preserves_new_view_in_log :
    forall nv new_log st,
      new_view_in_log nv (view_change_state (change_log_entry st new_log))
      = new_view_in_log nv (view_change_state st).
  Proof.
    unfold change_log_entry in *.
    simpl in *.
    tcsp.
  Qed.
  Hint Rewrite change_log_entry_preserves_new_view_in_log : pbft.

  Lemma change_last_reply_preserves_new_view_in_log :
    forall nv new_log st,
      new_view_in_log nv (view_change_state (change_last_reply_state st new_log))
      = new_view_in_log nv (view_change_state st).
  Proof.
    unfold change_last_reply_state in *.
    simpl in *.
    tcsp.
  Qed.
  Hint Rewrite change_last_reply_preserves_new_view_in_log : pbft.

  Lemma change_sm_state_preserves_new_view_in_log :
    forall nv new_log st,
      new_view_in_log nv (view_change_state (change_sm_state st new_log))
      = new_view_in_log nv (view_change_state st).
  Proof.
    unfold change_sm_state in *.
    simpl in *.
      tcsp.
  Qed.
  Hint Rewrite change_sm_state_preserves_new_view_in_log : pbft.

  Lemma increment_next_to_execute_preserves_new_view_in_log :
    forall nv st,
      new_view_in_log nv (view_change_state (increment_next_to_execute st))
      = new_view_in_log nv (view_change_state st).
  Proof.
      unfold increment_next_to_execute in *.
      simpl in *.
      tcsp.
  Qed.
  Hint Rewrite increment_next_to_execute_preserves_new_view_in_log : pbft.

  Lemma find_and_execute_requests_initial :
    forall i v k,
      find_and_execute_requests i v k (initial_state i) = ([], initial_state i).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite find_and_execute_requests_initial : pbft.

  Lemma find_and_execute_requests_preserves_new_view_in_log :
    forall nv msg i v keys st p,
      find_and_execute_requests i v keys p = (msg, st)
      -> new_view_in_log nv (view_change_state st)
      -> new_view_in_log nv (view_change_state p).
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
      apply check_broadcast_checkpoint_preserves_view_change_state in H
    end.

    match goal with
    | [ H1 : new_view_in_log _ (view_change_state ?s), H2 : _ = view_change_state ?s |- _ ] =>
      rewrite <- H2 in H1; clear H2
    end.

    match goal with
    | [ H : new_view_in_log _ _ |- _ ] =>
      rewrite change_log_entry_preserves_new_view_in_log in H
    end.

    match goal with
    | [ H : new_view_in_log _ _ |- _ ] =>
      rewrite change_last_reply_preserves_new_view_in_log in H
    end.

    match goal with
    | [ H : new_view_in_log _ _ |- _ ] =>
      rewrite change_sm_state_preserves_new_view_in_log in H
    end.

    match goal with
    | [ H : new_view_in_log _ _ |- _ ] =>
      rewrite increment_next_to_execute_preserves_new_view_in_log in H
    end.
    auto.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_new_view_in_log : pbft.

  Lemma view_change_state_decrement_requests_in_progress_if_primary :
    forall i v st,
      view_change_state (decrement_requests_in_progress_if_primary i v st)
      = view_change_state st.
  Proof.
    introv; unfold decrement_requests_in_progress_if_primary; smash_pbft.
  Qed.
  Hint Rewrite view_change_state_decrement_requests_in_progress_if_primary : pbft.

(*  Lemma decrement_requests_in_progress_preserves_prepare_in_log :
    forall i nv p st,
      new_view_in_log nv (view_change_state (decrement_requests_in_progress_if_primary i (current_view p) st))
      = new_view_in_log  nv (view_change_state st).
  Proof.
    introv.
    unfold decrement_requests_in_progress_if_primary.
    pbft_dest_all x.
  Qed.
  Hint Rewrite decrement_requests_in_progress_preserves_prepare_in_log : pbft.*)

  Lemma change_view_change_state_implies:
    forall st vcstate,
      view_change_state (change_view_change_state st vcstate) = vcstate.
  Proof.
    unfold change_view_change_state in *. simpl in *. tcsp.
  Qed.
  Hint Rewrite change_view_change_state_implies : pbft.

  Lemma update_checkpoint_from_new_view_preserves_new_view_in_log :
    forall stablech sn nv state state',
      update_checkpoint_from_new_view state stablech sn = state'
      -> new_view_in_log nv (view_change_state state')
         =
         new_view_in_log nv (view_change_state state).
  Proof.
    introv up.
    unfold update_checkpoint_from_new_view in *. smash_pbft.
  Qed.
  (*Hint Rewrite update_checkpoint_from_new_view_preserves_new_view_in_log : pbft.*)

  Lemma trim_checkpoint_preserves_new_view_in_log :
    forall nv sn state state',
      trim_checkpoint state sn = state'
      -> new_view_in_log nv (view_change_state state')
         =
         new_view_in_log nv (view_change_state state).
  Proof.
    introv H. unfold trim_checkpoint in *.
    destruct state, state'. simpl in *. inversion H. auto.
  Qed.
  (*Hint Rewrite trim_checkpoint_preserves_new_view_in_log : pbft.*)

  Lemma log_checkpoint_cert_from_new_view_preserves_new_view_in_log :
    forall nv slf v sn C s och state state',
      log_checkpoint_cert_from_new_view slf state v sn C s = (state', och)
      -> new_view_in_log nv (view_change_state state')
      -> new_view_in_log nv (view_change_state state).
  Proof.
    introv lcp h.
    unfold log_checkpoint_cert_from_new_view in *. smash_pbft.
  Qed.
  Hint Resolve log_checkpoint_cert_from_new_view_preserves_new_view_in_log : pbft.

  Lemma update_state_new_view_preserves_new_view_in_log :
    forall slf nv' nv msg state state',
      update_state_new_view slf state nv = (state', msg)
      -> new_view_in_log nv' (view_change_state state')
      -> new_view_in_log nv' (view_change_state state).
  Proof.
    introv up h.
    unfold update_state_new_view in *; smash_pbft.
  Qed.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_new_view_in_log :
    forall nv slf pp d Fp Fc gi log' state,
      add_new_pre_prepare_and_prepare2log slf (log state) pp d Fp Fc = (gi, log')
      -> new_view_in_log nv (view_change_state state)
      -> new_view_in_log nv (view_change_state (update_log state log')).
  Proof.
    introv ad h.
    remember (log state) as L.
    destruct L; simpl in *; ginv; simpl in *; tcsp.
  Qed.
  Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_new_view_in_log : pbft.

  Lemma check_send_replies_preserves_new_view_in_log_backward :
    forall nv slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> new_view_in_log nv (view_change_state state)
      -> new_view_in_log nv (view_change_state state').
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_new_view_in_log_backward : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_new_view_in_log :
    forall nv slf pp d msg state state',
      add_prepare_to_log_from_new_view_pre_prepare slf state (pp, d) = (state', msg)
      -> new_view_in_log nv (view_change_state state)
      -> new_view_in_log nv (view_change_state state').
  Proof.
      introv ad h.
      unfold add_prepare_to_log_from_new_view_pre_prepare in *. smash_pbft.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_new_view_in_log : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_new_view_in_log  :
    forall slf nv pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> new_view_in_log nv (view_change_state state)
      -> new_view_in_log nv (view_change_state state').
  Proof.
    induction pps; introv h q; simpl in *; smash_pbft; repnd.
    eapply IHpps; eauto with pbft.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_new_view_in_log : pbft.

  Lemma log_new_view_state_preserves_new_view_in_log :
    forall nv nv' state state',
      log_new_view_state state nv = state'
      -> new_view_in_log nv' (view_change_state state')
      -> new_view_in_log nv' (view_change_state state)
         \/
         nv = nv'.
(*         exists entry,
           In entry (view_change_state state)
           /\ nv = nv'
           /\ vce_new_view entry = None.*)
  Proof.
    introv lnw h1.
    unfold log_new_view_state in *.
    destruct state'; simpl in *; ginv.

    match goal with
    | [ H : context[view_change_state ?s] |- _ ] =>
      remember (view_change_state s) as S
    end; clear HeqS.

    induction S; simpl in *; tcsp; smash_pbft;
      destruct a; simpl in *; ginv;
        destruct vce_new_view; simpl in *; ginv; tcsp.
  Qed.
  (*Hint Rewrite log_new_view_state_preserves_new_view_in_log : pbft.*)

  Lemma log_pre_prepares_of_new_view_preserves_new_view_in_log :
    forall nv L state state',
      log_pre_prepares_of_new_view state L = state'
      -> new_view_in_log nv (view_change_state state)
         =
         new_view_in_log nv (view_change_state state').
  Proof.
    introv lpp.
    unfold log_pre_prepares_of_new_view in *.
    ginv.
  Qed.
  Hint Resolve log_pre_prepares_of_new_view_preserves_new_view_in_log : pbft.

  Lemma update_view_preserves_new_view_in_log :
    forall nv v state state',
      update_view state v = state'
      -> new_view_in_log nv (view_change_state state)
         =
         new_view_in_log nv (view_change_state state').
  Proof.
    introv lpp.
    unfold update_view in *.
    ginv.
  Qed.
  Hint Resolve update_view_preserves_new_view_in_log : pbft.

  Lemma check_send_replies_update_log_preserves_new_view_in_log :
    forall nv slf view keys entryop state L sn msgs state',
      check_send_replies slf view keys entryop (update_log state L) sn = (msgs, state')
      -> new_view_in_log nv (view_change_state state')
      -> new_view_in_log nv (view_change_state state).
  Proof.
    introv chk pil.
    eapply check_send_replies_preserves_new_view_in_log in chk;[|eauto].
    simpl in *; auto.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_new_view_in_log : pbft.

  Lemma check_send_replies_preserves_view_change_state :
    forall slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> view_change_state state' = view_change_state state.
  Proof.
    introv chk.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_view_change_state : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_view_change_state :
    forall slf pps state state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state pps = (state', msgs)
      -> view_change_state state' = view_change_state state.
  Proof.
    introv h.
    unfold add_prepare_to_log_from_new_view_pre_prepare in h; smash_pbft.

    match goal with
    | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
      apply check_send_replies_preserves_view_change_state in H; allrw; simpl; auto
    end.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_view_change_state : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state :
    forall slf pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> view_change_state state' = view_change_state state.
  Proof.
    induction pps; introv h; simpl in *; pbft_simplifier; auto.
    smash_pbft.
    match goal with
    | [ H : add_prepares_to_log_from_new_view_pre_prepares _ _ _ = _ |- _ ] =>
      apply IHpps in H; allrw; eauto 2 with pbft
    end.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state : pbft.

  Lemma log_new_view_preserves_new_view_in_log :
    forall nv nv' S,
      new_view_in_log nv (log_new_view S nv')
      -> new_view_in_log nv S
         \/
         nv = nv'.
  Proof.
    introv lnw.

    induction S; simpl in *; tcsp; smash_pbft;
      destruct a; simpl in *; ginv;
        destruct vce_new_view; simpl in *; ginv; tcsp.
  Qed.

  Lemma log_new_view_and_entry_preserves_new_view_in_log :
    forall nv nv' S e,
      vce_view e = new_view2view nv
      -> new_view_in_log nv' (log_new_view_and_entry S nv e)
      -> new_view_in_log nv' S
         \/ nv' = nv
         \/ vce_new_view e = Some nv'.
  Proof.
    induction S; introv eqv h; simpl in *; tcsp; smash_pbft;
      destruct e; simpl in *; ginv;
        destruct vce_new_view; simpl in *; ginv; tcsp;
          destruct a; simpl in *; subst; tcsp.
  Qed.

  Lemma execute_requests_preserves_view_change_state :
    forall i v keys st L msgs st',
      execute_requests i v keys st L = (msgs, st')
      -> view_change_state st' = view_change_state st.
  Proof.
    induction L; introv h; simpl in *; smash_pbft.

    match goal with
    | [ H : check_broadcast_checkpoint _ _ _ _ _ = _ |- _ ] =>
      apply check_broadcast_checkpoint_preserves_view_change_state in H
    end; simpl in *; auto.
  Qed.
  Hint Resolve execute_requests_preserves_view_change_state : pbft.

  Lemma find_and_execute_requests_preserves_view_change_state :
    forall i v keys st msgs st',
      find_and_execute_requests i v keys st = (msgs, st')
      -> view_change_state st' = view_change_state st.
  Proof.
    introv h; unfold find_and_execute_requests in h; smash_pbft.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_view_change_state : pbft.

  Lemma start_view_change_preserves_new_view_in_log :
    forall vc vc_state vc_state' nv vc_entry,
      start_view_change vc vc_state = (vc_entry, vc_state')
      -> new_view_in_log nv vc_state'
      -> new_view_in_log nv vc_state.
  Proof.
    induction vc_state; introv svc h; simpl in *; ginv; simpl in *; smash_pbft; tcsp;[].

    {
      unfold own_view_change2initial_entry in *.
      simpl in *. smash_pbft.
    }
  Qed.
  Hint Resolve start_view_change_preserves_new_view_in_log : pbft.

  Lemma add_other_view_change_preserves_new_view_in_log :
    forall vc nv vc_entry vc_state vc_state',
      add_other_view_change vc vc_state = Some (vc_entry, vc_state')
      -> new_view_in_log nv vc_state'
      -> new_view_in_log nv vc_state.
  Proof.
    induction vc_state; introv svc h; simpl in *; ginv; simpl in *; smash_pbft; tcsp.

    {
      unfold own_view_change2initial_entry in *.
      simpl in *. smash_pbft.
    }

    {
      unfold add_other_view_change2entry in *.
      destruct a. smash_pbft.
    }

    {
      unfold add_other_view_change2entry in *.
      destruct a. smash_pbft.
    }

    {
      unfold add_other_view_change2entry in *.
      destruct a. smash_pbft.
    }
  Qed.
  Hint Resolve add_other_view_change_preserves_new_view_in_log : pbft.

  Lemma in_implies_new_view_in_log :
    forall e nv S,
      wf_view_change_state S
      -> In e S
      -> vce_new_view e = Some nv
      -> new_view_in_log nv S.
  Proof.
    induction S; introv wf i eqnv; simpl in *; tcsp.
    inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
    repndors; tcsp; smash_pbft.

    - destruct n.
      symmetry; apply wf1; auto.

    - applydup imp in i; clear imp.
      repeat (autodimp IHS hyp).
      apply wf_view_change_state_implies_all_entries in i; auto.
      destruct i0; allrw.
      apply i; auto.
  Qed.
  Hint Resolve in_implies_new_view_in_log : pbft.

  Lemma check_broadcast_new_view_implies_new_view_in_log :
    forall i s e nv' e' O N nv,
      wf_view_change_state (view_change_state s)
      -> check_broadcast_new_view i s e = Some (nv', e', O, N)
      -> vce_new_view e' = Some nv
      -> In e (view_change_state s)
      -> new_view_in_log nv (view_change_state s).
  Proof.
    introv wf check eqnv j.
    dup check as check'.
    unfold check_broadcast_new_view in check; smash_pbft.
    unfold view_changed_entry in *; smash_pbft2.
  Qed.
  Hint Resolve check_broadcast_new_view_implies_new_view_in_log : pbft.

End PBFTnew_view_in_log.


Hint Resolve check_send_replies_preserves_new_view_in_log : pbft.
Hint Resolve check_send_replies_preserves_new_view_in_log_backward : pbft.
Hint Resolve log_pre_prepares_of_new_view_preserves_new_view_in_log : pbft.
Hint Resolve update_view_preserves_new_view_in_log : pbft.
Hint Resolve check_send_replies_update_log_preserves_new_view_in_log : pbft.
Hint Resolve check_send_replies_preserves_view_change_state : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_view_change_state : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state : pbft.
Hint Resolve check_stable_preserves_new_view_in_log : pbft.
Hint Resolve find_and_execute_requests_preserves_view_change_state : pbft.
Hint Resolve execute_requests_preserves_view_change_state : pbft.
(*Hint Resolve update_log_preserves_new_view_in_log : pbft.*)
Hint Resolve log_checkpoint_cert_from_new_view_preserves_new_view_in_log : pbft.
Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_new_view_in_log : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_new_view_in_log : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_new_view_in_log : pbft.
Hint Resolve start_view_change_preserves_new_view_in_log : pbft.
Hint Resolve add_other_view_change_preserves_new_view_in_log : pbft.
Hint Resolve in_implies_new_view_in_log : pbft.
Hint Resolve check_broadcast_new_view_implies_new_view_in_log : pbft.
Hint Resolve find_and_execute_requests_preserves_new_view_in_log : pbft.


Hint Rewrite @change_log_entry_preserves_new_view_in_log : pbft.
Hint Rewrite @change_last_reply_preserves_new_view_in_log : pbft.
Hint Rewrite @change_sm_state_preserves_new_view_in_log : pbft.
Hint Rewrite @increment_next_to_execute_preserves_new_view_in_log : pbft.
Hint Rewrite @change_view_change_state_implies : pbft.
Hint Rewrite @view_change_state_decrement_requests_in_progress_if_primary : pbft.
Hint Rewrite @find_and_execute_requests_initial : pbft.


(*Hint Rewrite @decrement_requests_in_progress_preserves_prepare_in_log : pbft.*)
(*Hint Rewrite @update_checkpoint_from_new_view_preserves_new_view_in_log : pbft.*)
(*Hint Rewrite @trim_checkpoint_preserves_new_view_in_log : pbft.*)
(*Hint Rewrite @log_new_view_state_preserves_new_view_in_log : pbft.*)
