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


Require Export PBFThas_new_view.
Require Export PBFTcheck_broadcast_new_view.
Require Export PBFTview_change_in_log.


Section PBFTwf_view_change_state_no_repeats.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Record wf_view_change_entry_no_repeats i (e : PBFTviewChangeEntry) :=
    {
      wf_vc_norep_norep : no_repeats (map view_change2sender (vce_view_changes e));
      wf_vc_norep_vc    : forall vc, vce_view_change e = Some vc -> view_change2sender vc = i;
      wf_vc_norep_vcs   : forall vc, In vc (vce_view_changes e) -> view_change2sender vc <> i;
    }.

  Inductive wf_view_change_state_no_repeats (i : Rep) : PBFTviewChangeState -> Prop :=
  | wf_view_change_state_no_repeats_nil : wf_view_change_state_no_repeats i []
  | wf_view_change_state_no_repeats_cons :
      forall e s,
        wf_view_change_entry_no_repeats i e
        -> wf_view_change_state_no_repeats i s
        -> wf_view_change_state_no_repeats i (e :: s).
  Hint Constructors wf_view_change_state_no_repeats.

  Lemma wf_view_change_entry_no_repeats_implies :
    forall i e,
      wf_view_change_entry_no_repeats i e
      -> no_repeats (map view_change2sender (vce_view_changes e)).
  Proof.
    introv wf.
    inversion wf; auto.
  Qed.
  Hint Resolve wf_view_change_entry_no_repeats_implies : pbft.

  Lemma implies_wf_view_change_entry_no_repeats_add_new_view_to_entry :
    forall i e nv,
      wf_view_change_entry_no_repeats i e
      -> wf_view_change_entry_no_repeats i (add_new_view_to_entry e nv).
  Proof.
    destruct e, vce_view_change, vce_new_view; introv wf; simpl in *;
      inversion wf; simpl in *; tcsp; constructor; simpl; tcsp.
  Qed.
  Hint Resolve implies_wf_view_change_entry_no_repeats_add_new_view_to_entry : pbft.

  Lemma wf_view_change_state_no_repeats_log_new_view_and_entry :
    forall i s nv e,
      wf_view_change_entry_no_repeats i e
      -> wf_view_change_state_no_repeats i s
      -> wf_view_change_state_no_repeats i (log_new_view_and_entry s nv e).
  Proof.
    induction s; introv wfe wf; simpl in *; auto; smash_pbft.

    - inversion wf as [|? ? wf1 wf2]; subst; clear wf.
      constructor; tcsp; eauto 3 with pbft.

    - inversion wf as [|? ? wf1 wf2]; subst; clear wf.
      constructor; tcsp; eauto 3 with pbft.
  Qed.
  Hint Resolve wf_view_change_state_no_repeats_log_new_view_and_entry : pbft.

  Lemma in_implies_wf_view_change_entry_no_repeats :
    forall j e s,
      In e s
      -> wf_view_change_state_no_repeats j s
      -> wf_view_change_entry_no_repeats j e.
  Proof.
    induction s; introv i wf; simpl in *; tcsp.
    inversion wf as [|? ? wf1 wf2]; subst; clear wf.
    repndors; subst; tcsp.
  Qed.
  Hint Resolve in_implies_wf_view_change_entry_no_repeats : pbft.

  Lemma check_send_replies_update_log_preserves_wf_view_change_state_no_repeats :
    forall i j v keys giop s1 L n msgs s2,
      check_send_replies i v keys giop (update_log s1 L) n = (msgs, s2)
      -> wf_view_change_state_no_repeats j (view_change_state s1)
      -> wf_view_change_state_no_repeats j (view_change_state s2).
  Proof.
    introv check wf.
    apply check_send_replies_preserves_view_change_state in check.
    rewrite check; simpl; auto.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_wf_view_change_state_no_repeats : pbft.

  Lemma check_stable_update_checkpoint_state_wf_view_change_state_no_repeats :
    forall i j s1 s cop s2,
      check_stable i (update_checkpoint_state s1 s) cop = Some s2
      -> wf_view_change_state_no_repeats j (view_change_state s1)
      -> wf_view_change_state_no_repeats j (view_change_state s2).
  Proof.
    introv check wf.
    apply check_stable_preserves_view_change_state in check.
    rewrite check; simpl; auto.
  Qed.
  Hint Resolve check_stable_update_checkpoint_state_wf_view_change_state_no_repeats : pbft.

  Lemma find_and_execute_requests_preserves_wf_view_change_state_no_repeats :
    forall i j v keys s1 msgs s2,
      find_and_execute_requests i v keys s1 = (msgs, s2)
      -> wf_view_change_state_no_repeats j (view_change_state s1)
      -> wf_view_change_state_no_repeats j (view_change_state s2).
  Proof.
    introv fexec wf.
    apply find_and_execute_preserves_view_change_state in fexec.
    rewrite fexec; auto.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_wf_view_change_state_no_repeats : pbft.

  Lemma check_broadcast_new_view_preserves_wf_view_change_entry_no_repeats :
    forall i j s e1 nv e2 O N,
      check_broadcast_new_view i s e1 = Some (nv, e2, O, N)
      -> wf_view_change_entry_no_repeats j e1
      -> wf_view_change_entry_no_repeats j e2.
  Proof.
    introv check wf.
    apply check_broadcast_new_view_implies in check; exrepnd; subst; simpl in *.
    inversion wf; constructor; simpl in *; autorewrite with pbft in *; tcsp.
    introv xx; ginv; simpl; tcsp.
  Qed.
  Hint Resolve check_broadcast_new_view_preserves_wf_view_change_entry_no_repeats : pbft.

  Lemma implies_wf_view_change_entry_no_repeats_add_own_view_change2entry :
    forall i e vc,
      view_change2sender vc = i
      -> wf_view_change_entry_no_repeats i e
      -> wf_view_change_entry_no_repeats i (add_own_view_change2entry vc e).
  Proof.
    introv h wf.
    inversion wf.
    unfold add_own_view_change2entry; destruct e, vce_view_change; constructor; simpl in *; tcsp.
    introv xx; ginv; tcsp.
  Qed.
  Hint Resolve implies_wf_view_change_entry_no_repeats_add_own_view_change2entry : pbft.

  Lemma add_own_view_change_to_state_wf_view_change_state_no_repeats :
    forall j vc s1 e n s2,
      view_change2sender vc = j
      -> add_own_view_change_to_state vc s1 = (e, n, s2)
      -> wf_view_change_state_no_repeats j s1
      -> wf_view_change_state_no_repeats j s2.
  Proof.
    induction s1; introv eqsender add wf; simpl in *; smash_pbft.

    - constructor; auto.
      constructor; simpl; tcsp.
      introv xx; ginv; auto.

    - inversion wf as [|? ? wf1 wf2]; subst; clear wf.
      constructor; auto; eauto 3 with pbft.

    - inversion wf.
      constructor; auto.
      eapply IHs1; eauto.
  Qed.
  Hint Resolve add_own_view_change_to_state_wf_view_change_state_no_repeats : pbft.

  Lemma start_view_change_preserves_wf_view_change_state_no_repeats :
    forall j vc s1 e n s2,
      view_change2sender vc = j
      -> start_view_change vc s1 = (e, n, s2)
      -> wf_view_change_state_no_repeats j s1
      -> wf_view_change_state_no_repeats j s2.
  Proof.
    introv start wf.
    unfold start_view_change in *; eauto 3 with pbft.
  Qed.
  Hint Resolve start_view_change_preserves_wf_view_change_state_no_repeats : pbft.

  Lemma add_view_change2view_changes_preserves_sender_in :
    forall s vc l k,
      add_view_change2view_changes vc l = Some k
      -> In s (map view_change2sender k)
      -> In s (map view_change2sender l) \/ s = view_change2sender vc.
  Proof.
    induction l; introv add i; repeat (simpl in *; smash_pbft).
    repndors; subst; tcsp.
    apply IHl in i; tcsp.
  Qed.

  Lemma add_view_change2view_changes_preserves_no_repeats :
    forall vc l k,
      add_view_change2view_changes vc l = Some k
      -> no_repeats (map view_change2sender l)
      -> no_repeats (map view_change2sender k).
  Proof.
    induction l; introv add norep; simpl in *; tcsp; smash_pbft.

    - constructor; tcsp.

    - inversion norep as [|? ? ni nrep]; subst; clear norep.
      constructor; tcsp.
      introv xx; destruct ni; eauto 3 with pbft.
      eapply add_view_change2view_changes_preserves_sender_in in xx;[|eauto].
      repndors; tcsp.
  Qed.
  Hint Resolve add_view_change2view_changes_preserves_no_repeats : pbft.

  Lemma add_view_change2view_changes_preserves_in :
    forall x vc l1 l2,
      add_view_change2view_changes x l1 = Some l2
      -> In vc l2
      -> In vc l1 \/ x = vc.
  Proof.
    induction l1; introv add i; simpl in *; ginv; simpl in *; tcsp; smash_pbft.
    repndors; subst; tcsp.
    pose proof (IHl1 x0) as q; repeat (autodimp q hyp); repndors; tcsp.
  Qed.

  Lemma add_other_view_change2entry_preserves_wf_view_change_entry_no_repeats :
    forall vc i e a,
      view_change2sender vc <> i
      -> add_other_view_change2entry vc a = Some e
      -> wf_view_change_entry_no_repeats i a
      -> wf_view_change_entry_no_repeats i e.
  Proof.
    introv d add wf.
    destruct a; simpl in *; smash_pbft.
    inversion wf; simpl in *; clear wf.
    constructor; simpl; tcsp; eauto 3 with pbft.
    introv j.
    eapply add_view_change2view_changes_preserves_in in j;[|eauto].
    repndors; subst; tcsp.
    discover; tcsp.
  Qed.
  Hint Resolve add_other_view_change2entry_preserves_wf_view_change_entry_no_repeats : pbft.

  Lemma add_other_view_change_preserves_wf_view_change_state_no_repeats :
    forall vc i s1 e n s2,
      view_change2sender vc <> i
      -> add_other_view_change vc s1 = Some (e, n, s2)
      -> wf_view_change_state_no_repeats i s1
      -> wf_view_change_state_no_repeats i s2.
  Proof.
    induction s1; introv d add wf; simpl in *; smash_pbft.

    - repeat (constructor; simpl; tcsp).
      introv xx; repndors; tcsp; subst; auto.

    - inversion wf as [|? ? wf1 wf2]; subst; clear wf.
      constructor; tcsp; eauto 3 with pbft.

    - inversion wf as [|? ? wf1 wf2]; subst; clear wf.
      constructor; tcsp; eauto 3 with pbft.
  Qed.
  Hint Resolve add_other_view_change_preserves_wf_view_change_state_no_repeats : pbft.

  Lemma add_new_view_to_entry_preserves_wf_view_change_entry_no_repeats :
    forall i a nv,
      wf_view_change_entry_no_repeats i a
      -> wf_view_change_entry_no_repeats i (add_new_view_to_entry a nv).
  Proof.
    introv wf.
    destruct a, vce_new_view; simpl in *; inversion wf; constructor; simpl in *; tcsp.
  Qed.
  Hint Resolve add_new_view_to_entry_preserves_wf_view_change_entry_no_repeats : pbft.

  Lemma wf_view_change_state_no_repeats_log_new_view :
    forall i s nv,
      wf_view_change_state_no_repeats i s
      -> wf_view_change_state_no_repeats i (log_new_view s nv).
  Proof.
    induction s; introv wf; simpl in *; auto; smash_pbft;
      inversion wf as [|? ? wf1 wf2]; subst; clear wf.

    - repeat (constructor; simpl; tcsp).

    - constructor; auto; eauto 3 with pbft.

    - constructor; auto; eauto 3 with pbft.
  Qed.
  Hint Resolve wf_view_change_state_no_repeats_log_new_view : pbft.

  Lemma view_change_in_log_entry_implies_in_senders :
    forall vc l,
      view_change_in_log_entry vc l
      -> In (view_change2sender vc) (map view_change2sender l).
  Proof.
    induction l; introv wf; simpl in *; tcsp; smash_pbft.
  Qed.
  Hint Resolve view_change_in_log_entry_implies_in_senders : pbft.

  Lemma in_implies_view_change_in_log_entry :
    forall vc l,
      In vc l
      -> no_repeats (map view_change2sender l)
      -> view_change_in_log_entry vc l.
  Proof.
    induction l; introv i norep; simpl in *; tcsp.
    inversion norep as [|? ? ni nrep]; subst; clear norep.
    repndors; subst; tcsp; smash_pbft.
    repeat (autodimp IHl hyp).
    rewrite <- e in *.
    destruct ni; eauto 3 with pbft.
  Qed.
  Hint Resolve in_implies_view_change_in_log_entry : pbft.

  Lemma in_implies_view_change_in_log :
    forall i s e vc,
      wf_view_change_state s
      -> wf_view_change_state_no_repeats i s
      -> In e s
      -> In vc (vce_view_changes e)
      -> view_change_in_log vc s.
  Proof.
    induction s; introv wf norep k j; simpl in *; tcsp.
    inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
    inversion norep as [|? ? wfnr1 wfnr2]; subst; clear norep.
    repndors; subst; smash_pbft;[|].

    - eapply wf_view_change_entry_view_changes in wf1; eauto; tcsp.

    - applydup imp in k.
      apply wf_view_change_state_implies_all_entries in k; auto.
      eapply wf_view_change_entry_view_changes in k; eauto.
      congruence.
  Qed.
  Hint Resolve in_implies_view_change_in_log : pbft.

  Lemma update_state_new_view_preserves_wf_view_change_no_repeats :
    forall i s1 nv s2 msgs,
      update_state_new_view i s1 nv = (s2, msgs)
      -> wf_view_change_state_no_repeats i (view_change_state s1)
      -> wf_view_change_state_no_repeats i (view_change_state s2).
  Proof.
    introv upd wf.
    apply update_state_new_view_preserves_view_change_state in upd; allrw; auto.
  Qed.
  Hint Resolve update_state_new_view_preserves_wf_view_change_no_repeats : pbft.

  Lemma implies_wf_view_change_state_no_repeats_update_view :
    forall i s v,
      wf_view_change_state_no_repeats i (view_change_state s)
      -> wf_view_change_state_no_repeats i (view_change_state (update_view s v)).
  Proof.
    auto.
  Qed.
  Hint Resolve implies_wf_view_change_state_no_repeats_update_view : pbft.

  Lemma implies_wf_view_change_state_no_repeats_change_sequence_number :
    forall i s n,
      wf_view_change_state_no_repeats i (view_change_state s)
      -> wf_view_change_state_no_repeats i (view_change_state (change_sequence_number s n)).
  Proof.
    auto.
  Qed.
  Hint Resolve implies_wf_view_change_state_no_repeats_change_sequence_number : pbft.

  Lemma implies_wf_view_change_state_no_repeats_log_pre_prepares_of_new_view :
    forall i s p,
      wf_view_change_state_no_repeats i (view_change_state s)
      -> wf_view_change_state_no_repeats i (view_change_state (log_pre_prepares_of_new_view s p)).
  Proof.
    auto.
  Qed.
  Hint Resolve implies_wf_view_change_state_no_repeats_log_pre_prepares_of_new_view : pbft.

  Lemma implies_wf_view_change_state_no_repeats_log_new_view_and_entry_state :
    forall i s nv e,
      wf_view_change_state_no_repeats i (log_new_view_and_entry (view_change_state s) nv e)
      -> wf_view_change_state_no_repeats i (view_change_state (log_new_view_and_entry_state s nv e)).
  Proof.
    auto.
  Qed.
  Hint Resolve implies_wf_view_change_state_no_repeats_log_new_view_and_entry_state : pbft.

  Lemma wf_view_change_entry_no_repeats_own_view_change2initial_entry :
    forall i vc,
      view_change2sender vc = i
      -> wf_view_change_entry_no_repeats i (own_view_change2initial_entry vc).
  Proof.
    introv h.
    constructor; simpl; tcsp; introv xx; ginv; auto.
  Qed.
  Hint Resolve wf_view_change_entry_no_repeats_own_view_change2initial_entry : pbft.

  Lemma view_change2sender_mk_current_view_change :
    forall i v s,
      view_change2sender (mk_current_view_change i v s) = i.
  Proof.
    auto.
  Qed.
  Hint Rewrite view_change2sender_mk_current_view_change : pbft.
  Hint Resolve view_change2sender_mk_current_view_change : pbft.

  Lemma wf_view_change_entry_no_repeats_other_view_change2initial_entry :
    forall i vc,
      view_change2sender vc <> i
      -> wf_view_change_entry_no_repeats i (other_view_change2initial_entry vc).
  Proof.
    introv h.
    constructor; simpl; tcsp; introv xx; repndors; subst; tcsp; ginv; auto.
  Qed.
  Hint Resolve wf_view_change_entry_no_repeats_other_view_change2initial_entry : pbft.

  Lemma implies_wf_view_change_state_no_repeats_log_new_view_state :
    forall i s nv,
      wf_view_change_state_no_repeats i (view_change_state s)
      -> wf_view_change_state_no_repeats i (view_change_state (log_new_view_state s nv)).
  Proof.
    introv wf; simpl; eauto 3 with pbft.
  Qed.
  Hint Resolve implies_wf_view_change_state_no_repeats_log_new_view_state : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state_no_repeats :
    forall i s1 P s2 msgs,
      add_prepares_to_log_from_new_view_pre_prepares i s1 P = (s2, msgs)
      -> wf_view_change_state_no_repeats i (view_change_state s1)
      -> wf_view_change_state_no_repeats i (view_change_state s2).
  Proof.
    introv add wf.
    apply PBFTprops5.add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state in add; allrw; auto.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state_no_repeats : pbft.

  Lemma wf_view_change_state_no_repeats_on_events :
    forall (eo : EventOrdering) (e : Event) i st,
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> wf_view_change_state_no_repeats i (view_change_state st).
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers4 smash_pbft_ind6_10.
  Qed.
  Hint Resolve wf_view_change_state_no_repeats_on_events : pbft.

  Lemma wf_view_change_state_no_repeats_before_events :
    forall (eo : EventOrdering) (e : Event) i st,
      state_sm_before_event (PBFTreplicaSM i) e = Some st
      -> wf_view_change_state_no_repeats i (view_change_state st).
  Proof.
    introv eqst.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d|d]; ginv; subst; simpl in *;tcsp;[].
    eauto 3 with pbft.
  Qed.
  Hint Resolve wf_view_change_state_no_repeats_before_events : pbft.

End PBFTwf_view_change_state_no_repeats.


Hint Constructors wf_view_change_state_no_repeats.


Hint Resolve wf_view_change_entry_no_repeats_implies : pbft.
Hint Resolve implies_wf_view_change_entry_no_repeats_add_new_view_to_entry : pbft.
Hint Resolve in_implies_wf_view_change_entry_no_repeats : pbft.
Hint Resolve check_broadcast_new_view_preserves_wf_view_change_entry_no_repeats : pbft.
Hint Resolve implies_wf_view_change_entry_no_repeats_add_own_view_change2entry : pbft.
Hint Resolve add_other_view_change2entry_preserves_wf_view_change_entry_no_repeats : pbft.
Hint Resolve add_new_view_to_entry_preserves_wf_view_change_entry_no_repeats : pbft.
Hint Resolve wf_view_change_state_no_repeats_log_new_view_and_entry : pbft.
Hint Resolve check_send_replies_update_log_preserves_wf_view_change_state_no_repeats : pbft.
Hint Resolve check_stable_update_checkpoint_state_wf_view_change_state_no_repeats : pbft.
Hint Resolve find_and_execute_requests_preserves_wf_view_change_state_no_repeats : pbft.
Hint Resolve add_own_view_change_to_state_wf_view_change_state_no_repeats : pbft.
Hint Resolve start_view_change_preserves_wf_view_change_state_no_repeats : pbft.
Hint Resolve add_other_view_change_preserves_wf_view_change_state_no_repeats : pbft.
Hint Resolve wf_view_change_state_no_repeats_log_new_view : pbft.
Hint Resolve wf_view_change_state_no_repeats_on_events : pbft.
Hint Resolve wf_view_change_state_no_repeats_before_events : pbft.
Hint Resolve add_view_change2view_changes_preserves_no_repeats : pbft.
Hint Resolve in_implies_view_change_in_log_entry : pbft.
Hint Resolve in_implies_view_change_in_log : pbft.
Hint Resolve view_change_in_log_entry_implies_in_senders : pbft.
Hint Resolve view_change2sender_mk_current_view_change : pbft.


Hint Rewrite @view_change2sender_mk_current_view_change : pbft.
