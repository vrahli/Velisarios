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
Require Export PBFTtactics.
Require Export PBFTtactics2.
Require Export PBFTwf_prepared_info.


Section PBFTwf_view_change_state.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.

  Definition wf_view_change (vc : ViewChange) : bool :=
    forallb wf_prepared_info (view_change2prep vc).

  Definition wf_view_changes (L : list ViewChange) : bool :=
    forallb wf_view_change L.

  Record wf_view_change_entry (entry : PBFTviewChangeEntry) :=
    {
      wf_view_change_entry_view_change :
        forall vc,
          vce_view_change entry = Some vc
          -> view_change2view vc = vce_view entry;

      wf_view_change_entry_view_changes :
        forall vc,
          In vc (vce_view_changes entry)
          -> view_change2view vc = vce_view entry;

      wf_view_change_entry_new_view :
        forall nv,
          vce_new_view entry = Some nv
          -> new_view2view nv = vce_view entry;

      wf_view_change_entry_view_change_preps :
        forall vc,
          vce_view_change entry = Some vc
          -> wf_view_change vc = true;

      wf_view_change_entry_view_changes_preps :
        forall vc,
          In vc (vce_view_changes entry)
          -> wf_view_change vc = true;

(*      wf_view_change_entry_view_change_correct :
        forall vc,
          vce_view_change entry = Some vc
          -> correct_view_change vc = true;

      wf_view_change_entry_view_changes_correct :
        forall vc,
          In vc (vce_view_changes entry)
          -> correct_view_change vc = true;

      wf_view_change_entry_new_view_correct :
        forall nv,
          vce_new_view entry = Some nv
          -> correct_new_view nv = true;*)
    }.

  Inductive wf_view_change_state : PBFTviewChangeState -> Prop :=
  | wf_view_change_state_nil : wf_view_change_state []
  | wf_view_change_state_cons :
      forall entry L,
        (forall entry', In entry' L -> vce_view entry <> vce_view entry')
        -> wf_view_change_entry entry
        -> wf_view_change_state L
        -> wf_view_change_state (entry :: L).
  Hint Constructors wf_view_change_state.

  Lemma wf_view_change_state_implies_all_entries :
    forall S entry,
      wf_view_change_state S
      -> In entry S
      -> wf_view_change_entry entry.
  Proof.
    induction S; introv wf i; simpl in *; tcsp.
    repndors; subst; tcsp; inversion wf; tcsp.
  Qed.
  Hint Resolve wf_view_change_state_implies_all_entries : pbft.

  Lemma check_send_replies_preserves_wf_view_change_state :
    forall i v keys giop st n msgs st',
      check_send_replies i v keys giop st n = (msgs, st')
      -> wf_view_change_state (view_change_state st)
      -> wf_view_change_state (view_change_state st').
  Proof.
    introv check wf.
    unfold check_send_replies in check.
    destruct giop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_wf_view_change_state : pbft.

  Lemma check_send_replies_update_log_preserves_wf_view_change_state :
    forall i v keys giop st L n msgs st',
      check_send_replies i v keys giop (update_log st L) n = (msgs, st')
      -> wf_view_change_state (view_change_state st)
      -> wf_view_change_state (view_change_state st').
  Proof.
    introv check wf.
    apply check_send_replies_preserves_wf_view_change_state in check; simpl in *; tcsp.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_wf_view_change_state : pbft.

  Lemma check_stable_preserves_wf_view_change_state :
    forall i st entryop st',
      check_stable i st entryop = Some st'
      -> wf_view_change_state (view_change_state st)
      -> wf_view_change_state (view_change_state st').
  Proof.
    introv check wf.
    unfold check_stable in check.
    destruct entryop; smash_pbft.
  Qed.
  Hint Resolve check_stable_preserves_wf_view_change_state : pbft.

  Lemma check_stable_update_checkpoint_state_preserves_wf_view_change_state :
    forall i st S entryop st',
      check_stable i (update_checkpoint_state st S) entryop = Some st'
      -> wf_view_change_state (view_change_state st)
      -> wf_view_change_state (view_change_state st').
  Proof.
    introv check wf.
    apply check_stable_preserves_wf_view_change_state in check; simpl in *; auto.
  Qed.
  Hint Resolve check_stable_update_checkpoint_state_preserves_wf_view_change_state : pbft.

  Lemma view_change_state_decrement_requests_in_progress_if_primary :
    forall i v s,
      view_change_state (decrement_requests_in_progress_if_primary i v s)
      = view_change_state s.
  Proof.
    introv; unfold decrement_requests_in_progress_if_primary; smash_pbft.
  Qed.
  Hint Rewrite view_change_state_decrement_requests_in_progress_if_primary : pbft.

  Lemma check_broadcast_checkpoint_preserves_wf_view_change_state :
    forall i n v keys st st' msgs,
      check_broadcast_checkpoint i n v keys st = (st', msgs)
      -> wf_view_change_state (view_change_state st)
      -> wf_view_change_state (view_change_state st').
  Proof.
    introv check wf.
    unfold check_broadcast_checkpoint in check; smash_pbft.
  Qed.
  Hint Resolve check_broadcast_checkpoint_preserves_wf_view_change_state : pbft.

  Lemma execute_requests_preserves_wf_view_change_state :
    forall i v keys st R msgs sns st',
      execute_requests i v keys st R = (msgs, sns, st')
      -> wf_view_change_state (view_change_state st)
      -> wf_view_change_state (view_change_state st').
  Proof.
    introv exec wf.
    unfold execute_requests in exec.
    destruct R; smash_pbft.
  Qed.
  Hint Resolve execute_requests_preserves_wf_view_change_state : pbft.

  Lemma find_and_execute_requests_preserves_wf_view_change_state :
    forall i v keys st msgs st',
      find_and_execute_requests i v keys st = (msgs, st')
      -> wf_view_change_state (view_change_state st)
      -> wf_view_change_state (view_change_state st').
  Proof.
    introv find wf.
    unfold find_and_execute_requests in find; smash_pbft.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_wf_view_change_state : pbft.

  Lemma vce_view_add_new_view_to_entry :
    forall e nv,
      vce_view (add_new_view_to_entry e nv)
      = vce_view e.
  Proof.
    introv; destruct e; simpl.
    destruct vce_new_view; simpl; auto.
  Qed.
  Hint Rewrite vce_view_add_new_view_to_entry : pbft.

  Lemma vce_view_change_add_new_view_to_entry :
    forall e nv,
      vce_view_change (add_new_view_to_entry e nv)
      = vce_view_change e.
  Proof.
    introv; destruct e; simpl.
    destruct vce_new_view; simpl; auto.
  Qed.
  Hint Rewrite vce_view_change_add_new_view_to_entry : pbft.

  Lemma vce_view_changes_add_new_view_to_entry :
    forall e nv,
      vce_view_changes (add_new_view_to_entry e nv)
      = vce_view_changes e.
  Proof.
    introv; destruct e; simpl.
    destruct vce_new_view; simpl; auto.
  Qed.
  Hint Rewrite vce_view_changes_add_new_view_to_entry : pbft.

  Lemma in_log_new_view_implies_or :
    forall entry S nv,
      In entry (log_new_view S nv)
      -> In entry S
         \/
         (
           vce_new_view entry = Some nv
           /\
           vce_view entry = new_view2view nv
         ).
  Proof.
    induction S; introv h; simpl in *; tcsp; repndors; subst; tcsp;
      smash_pbft; repndors; subst; simpl in *; tcsp; autorewrite with pbft in *; tcsp.

    - destruct a; simpl in *; tcsp.
      destruct vce_new_view; simpl in *; tcsp; subst.

    - apply IHS in h; tcsp.
  Qed.

  Lemma add_new_view_to_entry_preserves_wf_view_change_entry :
    forall entry nv,
      (*correct_new_view nv = true
      ->*) new_view2view nv = vce_view entry
      -> wf_view_change_entry entry
      -> wf_view_change_entry (add_new_view_to_entry entry nv).
  Proof.
    introv (*cor*) eqv wf; inversion wf as [wfvc wfvcs wfnv]; clear wf.
    constructor; autorewrite with pbft in *; tcsp;[].

    {
      introv i; autorewrite with pbft in *.
      destruct entry; simpl in *.
      destruct vce_new_view; simpl in *; ginv; tcsp.
    }

(*    {
      introv i; autorewrite with pbft in *.
      destruct entry; simpl in *.
      destruct vce_new_view; simpl in *; ginv; tcsp.
    }*)
  Qed.
  Hint Resolve add_new_view_to_entry_preserves_wf_view_change_entry : pbft.

  Lemma log_new_view_preserves_wf_view_change_state :
    forall S nv,
      (*correct_new_view nv = true
      ->*) wf_view_change_state S
      -> wf_view_change_state (log_new_view S nv).
  Proof.
    induction S; introv (*cor*) wf; simpl in *.

    - constructor; simpl; tcsp.
      constructor; simpl; introv h; ginv; tcsp.

    - inversion wf as [|? ? wfd wfe wfS]; subst; clear wf.
      smash_pbft.

      + constructor; autorewrite with pbft in *; tcsp; eauto 2 with pbft.

      + constructor; autorewrite with pbft in *; tcsp; eauto 2 with pbft.

        introv i; autorewrite with pbft in *.
        apply in_log_new_view_implies_or in i; repndors; repnd; tcsp.

        * apply wfd in i; auto.

        * destruct entry'; simpl in *; subst; tcsp.
  Qed.
  Hint Resolve log_new_view_preserves_wf_view_change_state : pbft.

  Lemma diff_views_implies_in_log_new_view :
    forall nv entry S,
      new_view2view nv <> vce_view entry
      -> In entry S
      -> In entry (log_new_view S nv).
  Proof.
    induction S; introv d i; simpl in *; tcsp.
    repndors; subst; smash_pbft; tcsp.
  Qed.
  Hint Resolve diff_views_implies_in_log_new_view : pbft.

  Lemma wf_view_change_state_add_new_view_to_entry_implies :
    forall entry nv,
      (*correct_new_view nv = true
      ->*) new_view2view nv = vce_view entry
      -> wf_view_change_entry (add_new_view_to_entry entry nv)
      -> wf_view_change_entry entry.
  Proof.
    introv (*cor*) eqv wf;
      inversion wf as [wfvc wfvcs wfnv wfvc' wfvcs' (*corvc corvcs cornv*)];
      clear wf.
    constructor; autorewrite with pbft in *; tcsp.

    {
      introv i.
      destruct entry; simpl in *; subst; simpl in *; eauto.
    }

(*    {
      introv i.
      destruct entry; simpl in *; subst; simpl in *; eauto.
    }*)
  Qed.
  Hint Resolve wf_view_change_state_add_new_view_to_entry_implies : pbft.

  Lemma log_new_view_preserves_wf_view_change_state_iff :
    forall S nv (*(cor : correct_new_view nv = true)*),
      wf_view_change_state (log_new_view S nv)
      <-> wf_view_change_state S.
  Proof.
    introv (*cor*); split; intro wf; eauto 2 with pbft.
    induction S; simpl in *; auto.
    smash_pbft.

    - inversion wf as [|? ? wfd wfe wfS]; subst; clear wf.
      autorewrite with pbft in *.
      constructor; tcsp; eauto 2 with pbft.

    - inversion wf as [|? ? wfd wfe wfS]; subst; clear wf.
      autorewrite with pbft in *.
      constructor; tcsp.

      introv i xx.

      destruct a; simpl in *; subst; simpl in *.
      pose proof (wfd entry') as q; autodimp q hyp; tcsp; eauto 2 with pbft.
  Qed.
  (*Hint Rewrite log_new_view_preserves_wf_view_change_state_iff : pbft.*)

  Lemma vce_view_add_own_view_change2entry :
    forall vc entry,
      vce_view (add_own_view_change2entry vc entry) = vce_view entry.
  Proof.
    introv; destruct entry; simpl; auto.
    destruct vce_view_change; simpl; auto.
  Qed.
  Hint Rewrite vce_view_add_own_view_change2entry : pbft.

  Lemma vce_view_changes_add_own_view_change2entry :
    forall vc entry,
      vce_view_changes (add_own_view_change2entry vc entry) = vce_view_changes entry.
  Proof.
    introv; destruct entry; simpl; auto.
    destruct vce_view_change; simpl; auto.
  Qed.
  Hint Rewrite vce_view_changes_add_own_view_change2entry : pbft.

  Lemma vce_new_view_add_own_view_change2entry :
    forall vc entry,
      vce_new_view (add_own_view_change2entry vc entry) = vce_new_view entry.
  Proof.
    introv; destruct entry; simpl; auto.
    destruct vce_view_change; simpl; auto.
  Qed.
  Hint Rewrite vce_new_view_add_own_view_change2entry : pbft.

  Lemma in_add_own_view_change_to_state_or :
    forall vc s1 e s2 entry,
      add_own_view_change_to_state vc s1 = (e, s2)
      -> In entry s2
      -> In entry s1
         \/
         (
           vce_view_change entry = Some vc
           /\
           vce_view entry = view_change2view vc
         ).
  Proof.
    induction s1; introv add i; simpl in *; tcsp; repndors; subst; tcsp; smash_pbft;
      simpl in *; repndors; subst; tcsp.

    - destruct a; simpl in *.
      destruct vce_view_change; simpl in *; tcsp.

    - eapply IHs1 in i;[|reflexivity]; tcsp.
  Qed.

  Lemma add_own_view_change2entry_preserves_wf_view_change_entry :
    forall entry vc,
      view_change2view vc = vce_view entry
      (*-> correct_view_change vc = true*)
      -> wf_view_change vc = true
      -> wf_view_change_entry entry
      -> wf_view_change_entry (add_own_view_change2entry vc entry).
  Proof.
    introv eqv (*cor*) wfc wf; inversion wf as [wfvc wfvcs wfnv]; clear wf.
    constructor; autorewrite with pbft in *; tcsp.

    {
      introv.
      destruct entry; simpl in *.
      destruct vce_view_change; simpl in *; tcsp.
      introv xx; ginv; auto.
    }

    {
      introv e.
      destruct entry; simpl in *.
      destruct vce_view_change; simpl in *; ginv; tcsp.
    }

(*    {
      introv e.
      destruct entry; simpl in *.
      destruct vce_view_change; simpl in *; ginv; tcsp.
    }*)
  Qed.
  Hint Resolve add_own_view_change2entry_preserves_wf_view_change_entry : pbft.

  Lemma start_view_change_preserves_wf_view_change_state :
    forall vc s1 e s2,
      start_view_change vc s1 = (e, s2)
(*      -> correct_view_change vc = true*)
      -> wf_view_change vc = true
      -> wf_view_change_state s1
      -> wf_view_change_state s2.
  Proof.
    introv start (*cor*) wfc wf.
    unfold start_view_change in start.
    revert e s2 start wf.
    induction s1; introv own wf; simpl in *; tcsp.

    - unfold own_view_change2initial_entry in own; simpl in *; smash_pbft.
      constructor; simpl; tcsp.
      constructor; simpl; tcsp; introv xx; ginv; auto.

    - smash_pbft.

      + inversion wf as [|? ? wfd wfe wfS]; subst; clear wf.
        constructor; autorewrite with pbft in *; tcsp; eauto 2 with pbft.

      + inversion wf as [|? ? wfd wfe wfS]; subst; clear wf.
        constructor; autorewrite with pbft in *; tcsp;[|eapply IHs1; eauto].

        introv i xx.
        eapply in_add_own_view_change_to_state_or in i;[|eauto].
        repndors; repnd; tcsp.

        * apply wfd in i; tcsp.

        * destruct entry'; simpl in *; subst; tcsp.
  Qed.
  Hint Resolve start_view_change_preserves_wf_view_change_state : pbft.

  Lemma in_add_view_change2view_changes_or :
    forall vc vcs1 vcs2 vc',
      add_view_change2view_changes vc vcs1 = Some vcs2
      -> In vc' vcs2
      ->
      (
        In vc' vcs1
        \/
        (
          vc' = vc
          /\
          forall x, In x vcs1 -> view_change2sender vc <> view_change2sender x
        )
      ).
  Proof.
    induction vcs1; simpl in *; introv add i; smash_pbft; simpl in *;
      repndors; subst; tcsp.

    applydup IHvcs1 in i; auto; repndors; repnd; subst; tcsp.

    right; dands; tcsp.
    introv xx; repndors; subst; tcsp.
    apply i0; auto.
  Qed.

  Lemma in_add_other_view_change_or :
    forall vc s1 e s2 entry,
      add_other_view_change vc s1 = Some (e, s2)
      -> In entry s2
      ->
      (
        In entry s1
        \/
        (exists entry',
            In entry' s1
            /\ view_change2view vc = vce_view entry'
            /\ add_other_view_change2entry vc entry' = Some entry)
        \/
        (
          entry = other_view_change2initial_entry vc
          /\ forall x, In x s1 -> view_change2view vc <> vce_view x
        )
      ).
  Proof.
    induction s1; introv add i; simpl in *; smash_pbft;
      simpl in *; repndors; subst; tcsp.

    - right; left.
      exists a; dands; tcsp.

    - dup i as j; eapply IHs1 in i;[|eauto]; clear IHs1.
      repndors; exrepnd; tcsp.

      + right; left.
        exists entry'; dands; tcsp.

      + subst; simpl in *.
        right; right; dands; tcsp.
        introv xx; repndors; subst; tcsp.
        apply i in xx; tcsp.
  Qed.

  Lemma add_other_view_change_preserves_wf_view_change_state :
    forall vc s1 e s2,
      add_other_view_change vc s1 = Some (e, s2)
(*      -> correct_view_change vc = true*)
      -> wf_view_change vc = true
      -> wf_view_change_state s1
      -> wf_view_change_state s2.
  Proof.
    induction s1; simpl in *; introv add (*cor*) wfc wf; smash_pbft.

    - constructor; simpl; tcsp.
      constructor; simpl; tcsp; introv xx; repndors; subst; tcsp.

    - unfold add_other_view_change2entry in *.
      destruct a; simpl in *; smash_pbft.

      inversion wf as [|? ? wfd wfe wfS]; subst; clear wf; simpl in *.
      constructor; autorewrite with pbft in *; simpl in *; tcsp.

      inversion wfe as [wfvc wfvcs wfnv]; clear wfe; simpl in *.
      constructor; simpl in *; autorewrite with pbft in *; tcsp.

      { introv i.
        eapply in_add_view_change2view_changes_or in i;[|eauto].
        repndors; repnd; subst; tcsp. }

      { introv i.
        eapply in_add_view_change2view_changes_or in i;[|eauto].
        repndors; repnd; subst; tcsp. }

(*      { introv i.
        eapply in_add_view_change2view_changes_or in i;[|eauto].
        repndors; repnd; subst; tcsp. }*)

    - inversion wf as [|? ? wfd wfe wfS]; subst; clear wf; simpl in *.
      constructor; autorewrite with pbft in *; simpl in *; tcsp.

      + introv i.
        dup i as j.
        eapply in_add_other_view_change_or in i;[|eauto].
        repndors; exrepnd; subst; tcsp.

        * apply wfd in i; tcsp.

        * apply wfd in i1; tcsp.
          destruct entry'0; simpl in *; smash_pbft.

      + eapply IHs1; eauto.
  Qed.
  Hint Resolve add_other_view_change_preserves_wf_view_change_state : pbft.

  Lemma view_change_state_update_checkpoint_from_new_view :
    forall st cp n,
      view_change_state (update_checkpoint_from_new_view st cp n)
      = view_change_state st.
  Proof.
    introv; unfold update_checkpoint_from_new_view; smash_pbft.
  Qed.
  Hint Rewrite view_change_state_update_checkpoint_from_new_view : pbft.

  Lemma log_checkpoint_cert_from_new_view_preserves_wf_view_change_state :
    forall i st1 v n cp s st2 msgs,
      log_checkpoint_cert_from_new_view i st1 v n cp s = (st2, msgs)
      -> wf_view_change_state (view_change_state st1)
      -> wf_view_change_state (view_change_state st2).
  Proof.
    introv log wf.
    unfold log_checkpoint_cert_from_new_view in log; simpl in *; smash_pbft.
  Qed.
  Hint Resolve log_checkpoint_cert_from_new_view_preserves_wf_view_change_state : pbft.

  Lemma view_change_state_trim_checkpoint :
    forall st n,
      view_change_state (trim_checkpoint st n)
      = view_change_state st.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite view_change_state_trim_checkpoint : pbft.

  (*Lemma view_change_state_update_low_water_mark :
    forall s n,
      view_change_state (update_low_water_mark s n) = view_change_state s.
  Proof.
    introv; destruct s; simpl; tcsp.
  Qed.
  Hint Rewrite view_change_state_update_low_water_mark : pbft.*)

(*  Lemma implies_wf_view_change_state_update_low_water_mark :
    forall s n,
      wf_view_change_state (view_change_state s)
      -> wf_view_change_state (view_change_state (update_low_water_mark s n)).
  Proof.
    introv wf; autorewrite with pbft; auto.
  Qed.
  Hint Resolve implies_wf_view_change_state_update_low_water_mark : pbft.*)

  Lemma wf_view_change_state_view_change_state_update_log :
    forall s L,
      wf_view_change_state (view_change_state s)
      -> wf_view_change_state (view_change_state (update_log s L)).
  Proof.
    tcsp.
  Qed.
  Hint Resolve wf_view_change_state_view_change_state_update_log : pbft.

  Lemma update_state_new_view_preserves_wf_view_change_state :
    forall i st1 nv st2 msgs,
      update_state_new_view i st1 nv = (st2, msgs)
      -> wf_view_change_state (view_change_state st1)
      -> wf_view_change_state (view_change_state st2).
  Proof.
    introv upd wf; unfold update_state_new_view in upd; smash_pbft.
  Qed.
  Hint Resolve update_state_new_view_preserves_wf_view_change_state : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_wf_view_change_state :
    forall i P st1 msgs st2,
      add_prepare_to_log_from_new_view_pre_prepare i st1 P = (st2, msgs)
      -> wf_view_change_state (view_change_state st1)
      -> wf_view_change_state (view_change_state st2).
  Proof.
    introv add wf; unfold add_prepare_to_log_from_new_view_pre_prepare in add.
    smash_pbft.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_wf_view_change_state : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_wf_view_change_state :
    forall i P st1 msgs st2,
      add_prepares_to_log_from_new_view_pre_prepares i st1 P = (st2, msgs)
      -> wf_view_change_state (view_change_state st1)
      -> wf_view_change_state (view_change_state st2).
  Proof.
    induction P; introv add wf; simpl in *; smash_pbft.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_wf_view_change_state : pbft.

  Lemma wf_prepared_infos_gather_valid_prepared_messages :
    forall L n, wf_prepared_infos (gather_valid_prepared_messages L n) = true.
  Proof.
    introv.
    unfold wf_prepared_infos.
    rewrite forallb_forall.
    introv i.
    unfold gather_valid_prepared_messages in i.
    apply filter_In in i; repnd.
    unfold valid_prepared_info in *.
    allrw andb_true; repnd.
    unfold info_is_prepared in *.
    allrw andb_true; repnd; tcsp.
  Qed.
  Hint Resolve wf_prepared_infos_gather_valid_prepared_messages : pbft.

  Lemma correct_view_change_implies_wf_view_change :
    forall v view,
      correct_view_change view v = true
      -> wf_view_change v = true.
  Proof.
    introv cor.
    unfold correct_view_change in cor.
    allrw andb_true; repnd.
    unfold wf_view_change.
    unfold correct_view_change_preps in *.
    allrw forallb_forall.
    introv i.
    discover.

    allrw andb_true; repnd.
    unfold valid_prepared_info in *.
    allrw andb_true; repnd.
    unfold info_is_prepared in *.
    allrw andb_true; repnd; tcsp.
  Qed.
  Hint Resolve correct_view_change_implies_wf_view_change : pbft.

  Lemma in_log_new_view_and_entry_implies_or :
    forall entry S nv e,
      In entry (log_new_view_and_entry S nv e)
      -> In entry S
         \/
         (
           vce_new_view entry = Some nv
           /\
           vce_view entry = vce_view e
         )
         \/
         entry = e.
  Proof.
    induction S; introv h; simpl in *; tcsp; repndors; subst; tcsp;
      smash_pbft; repndors; subst; simpl in *; tcsp; autorewrite with pbft in *; tcsp.

    - destruct e; simpl in *; tcsp.
      destruct vce_new_view; simpl in *; tcsp.

    - destruct a, e, vce_new_view, vce_new_view0; simpl in *; tcsp.

    - apply IHS in h; tcsp.
  Qed.

  Lemma check_broadcast_new_view_implies_wf_view_change_state_log_new_view_and_entry :
    forall s e nv,
      new_view2view nv = vce_view e
      -> wf_view_change_entry e
      -> wf_view_change_state s
      -> wf_view_change_state (log_new_view_and_entry s nv e).
  Proof.
    induction s; introv h wfe wfs; simpl in *; tcsp.

    - constructor; tcsp; eauto 3 with pbft.

    - inversion wfs as [|? ? imp wf1 wf2]; subst; clear wfs.
      smash_pbft; tcsp.

      + constructor; tcsp; eauto 3 with pbft.
        introv x.
        applydup imp in x; autorewrite with pbft; congruence.

      + constructor; tcsp; eauto 3 with pbft.
        introv x.
        apply in_log_new_view_and_entry_implies_or in x; repndors; repnd; tcsp; try congruence.
        applydup imp in x; autorewrite with pbft; congruence.
  Qed.
  Hint Resolve check_broadcast_new_view_implies_wf_view_change_state_log_new_view_and_entry : pbft.

  Lemma view_change2view_refresh_view_change :
    forall vc s,
      view_change2view (refresh_view_change vc s) = view_change2view vc.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite view_change2view_refresh_view_change : pbft.

  Lemma vce_view_replace_own_view_change_in_entry :
    forall vc e,
      vce_view (replace_own_view_change_in_entry vc e)
      = vce_view e.
  Proof.
    destruct e; simpl; auto.
  Qed.
  Hint Rewrite vce_view_replace_own_view_change_in_entry : pbft.

  Lemma check_broadcast_new_view_implies_equal_views :
    forall i s e nv e' O N,
      wf_view_change_entry e
      -> check_broadcast_new_view i s e = Some (nv, e', O, N)
      -> new_view2view nv = vce_view e'.
  Proof.
    introv wf check.
    unfold check_broadcast_new_view in check; smash_pbft.
    unfold view_changed_entry in *; smash_pbft.
    apply wf; auto.
  Qed.
  Hint Resolve check_broadcast_new_view_implies_equal_views : pbft.

  Lemma vce_view_change_replace_own_view_change_in_entry :
    forall vc e,
      vce_view_change (replace_own_view_change_in_entry vc e)
      = Some vc.
  Proof.
    introv; destruct e; simpl in *; auto.
  Qed.
  Hint Rewrite vce_view_change_replace_own_view_change_in_entry : pbft.

  Lemma vce_new_view_replace_own_view_change_in_entry :
    forall vc e,
      vce_new_view (replace_own_view_change_in_entry vc e)
      = vce_new_view e.
  Proof.
    introv; destruct e; simpl in *; auto.
  Qed.
  Hint Rewrite vce_new_view_replace_own_view_change_in_entry : pbft.

  Lemma wf_view_change_entry_replace_own_view_change_in_entry :
    forall vc e,
      vce_view e = view_change2view vc
      -> wf_view_change vc = true
      -> wf_view_change_entry e
      -> wf_view_change_entry (replace_own_view_change_in_entry vc e).
  Proof.
    introv eqvs wfvc wf; destruct wf; constructor; simpl; introv h;
      autorewrite with pbft in *; ginv; tcsp.
  Qed.
  Hint Resolve wf_view_change_entry_replace_own_view_change_in_entry : pbft.

  Lemma check_broadcast_new_view_implies_wf_view_change_entry :
    forall i s e nv e' O N,
      wf_view_change_entry e
      -> check_broadcast_new_view i s e = Some (nv, e', O, N)
      -> wf_view_change_entry e'.
  Proof.
    introv wf check.
    unfold check_broadcast_new_view in check; smash_pbft.
    unfold view_changed_entry in *; smash_pbft.

    apply wf_view_change_entry_replace_own_view_change_in_entry;
      auto; autorewrite with pbft; auto;
        try (complete (symmetry; apply wf; auto)).
    destruct e; simpl in *; smash_pbft.
  Qed.
  Hint Resolve check_broadcast_new_view_implies_wf_view_change_entry : pbft.

  Lemma wf_view_change_state_update_view :
    forall s v,
      wf_view_change_state (view_change_state s)
      -> wf_view_change_state (view_change_state (update_view s v)).
  Proof.
    tcsp.
  Qed.
  Hint Resolve wf_view_change_state_update_view : pbft.

  Lemma wf_view_change_state_change_sequence_number :
    forall s n,
      wf_view_change_state (view_change_state s)
      -> wf_view_change_state (view_change_state (change_sequence_number s n)).
  Proof.
    tcsp.
  Qed.
  Hint Resolve wf_view_change_state_change_sequence_number : pbft.

  Lemma wf_view_change_state_log_pre_prepares_of_new_view :
    forall s P,
      wf_view_change_state (view_change_state s)
      -> wf_view_change_state (view_change_state (log_pre_prepares_of_new_view s P)).
  Proof.
    tcsp.
  Qed.
  Hint Resolve wf_view_change_state_log_pre_prepares_of_new_view : pbft.

  Lemma wf_view_change_state_log_new_view_and_entry :
    forall s nv e,
      new_view2view nv = vce_view e
      -> wf_view_change_entry e
      -> wf_view_change_state s
      -> wf_view_change_state (log_new_view_and_entry s nv e).
  Proof.
    induction s; introv eqv wfe wf; simpl in *; smash_pbft.

    - constructor; simpl; tcsp; eauto 3 with pbft.

    - inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
      constructor; tcsp; eauto 3 with pbft.
      introv i eqv'.
      applydup imp in i.
      rewrite <- eqv' in i0; simpl in *.
      autorewrite with pbft in *; try congruence.

    - inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
      constructor; tcsp; eauto 3 with pbft.
      introv i eqv'.

      apply in_log_new_view_and_entry_implies_or in i; repndors; repnd; try congruence;[].

      applydup imp in i.
      rewrite <- eqv' in i0; simpl in *.
      autorewrite with pbft in *; try congruence.
  Qed.
  Hint Resolve wf_view_change_state_log_new_view_and_entry : pbft.

  Lemma wf_view_change_state_log_new_view_and_entry_state :
    forall s nv e,
      new_view2view nv = vce_view e
      -> wf_view_change_entry e
      -> wf_view_change_state (view_change_state s)
      -> wf_view_change_state (view_change_state (log_new_view_and_entry_state s nv e)).
  Proof.
    introv eqv wfe wf.
    unfold log_new_view_and_entry_state; simpl; eauto 3 with pbft.
  Qed.
  Hint Resolve wf_view_change_state_log_new_view_and_entry_state : pbft.

  Lemma CheckBCastNewView2entry_initial_state :
    forall c i,
      CheckBCastNewView2entry c (view_change_state (initial_state i)) = None.
  Proof.
    introv; destruct c; simpl.
    destruct i0; simpl; auto.
  Qed.
  Hint Rewrite CheckBCastNewView2entry_initial_state : pbft.

  Lemma CheckBCastNewView2entry_initial_view_change_state :
    forall c, CheckBCastNewView2entry c initial_view_change_state = None.
  Proof.
    introv; destruct c; simpl.
    destruct i; simpl; auto.
  Qed.
  Hint Rewrite CheckBCastNewView2entry_initial_view_change_state : pbft.

  Lemma CheckBCastNewView2entry_implies_wf_view_change_entry :
    forall c s e,
      CheckBCastNewView2entry c s = Some e
      -> wf_view_change_state s
      -> wf_view_change_entry e.
  Proof.
    introv check wf; eauto 3 with pbft.
  Qed.
  Hint Resolve CheckBCastNewView2entry_implies_wf_view_change_entry : pbft.

  Lemma wf_view_change_state_own_view_change2initial_entry :
    forall vc,
      wf_view_change vc = true
      -> wf_view_change_state [own_view_change2initial_entry vc].
  Proof.
    introv wfvc.
    constructor; simpl; tcsp.
    constructor; simpl; tcsp; introv h; ginv; tcsp.
  Qed.
  Hint Resolve wf_view_change_state_own_view_change2initial_entry : pbft.

  Lemma wf_view_change_mk_current_view_change :
    forall i v s,
      wf_view_change (mk_current_view_change i v s) = true.
  Proof.
    introv.
    unfold wf_view_change, mk_current_view_change, view_change2prep; simpl.
    apply forallb_forall.
    introv j.
    unfold gather_valid_prepared_messages in j.
    apply filter_In in j; repnd; eauto 3 with pbft.
  Qed.
  Hint Resolve wf_view_change_mk_current_view_change : pbft.

  Lemma wf_view_change_state_other_view_change2initial_entry :
    forall vc,
      wf_view_change vc = true
      -> wf_view_change_state [other_view_change2initial_entry vc].
  Proof.
    introv wfvc.
    constructor; simpl; tcsp.
    constructor; simpl; tcsp; introv h; ginv; repndors; subst; tcsp.
  Qed.
  Hint Resolve wf_view_change_state_other_view_change2initial_entry : pbft.

  Lemma wf_view_change_state_log_new_view_state :
    forall s nv,
      wf_view_change_state (view_change_state s)
      -> wf_view_change_state (view_change_state (log_new_view_state s nv)).
  Proof.
    introv wf.
    unfold log_new_view_state; simpl; eauto 3 with pbft.
  Qed.
  Hint Resolve wf_view_change_state_log_new_view_state : pbft.

  Lemma check_stable_preserves_view_change_state :
    forall i s e s',
      check_stable i s e = Some s'
      -> view_change_state s' = view_change_state s.
  Proof.
    introv check; unfold check_stable in check; smash_pbft.
  Qed.
  Hint Resolve check_stable_preserves_view_change_state : pbft.

  Lemma view_change_state_check_one_stable :
    forall i s l,
      view_change_state (check_one_stable i s l) = view_change_state s.
  Proof.
    induction l; introv; simpl; smash_pbft.
  Qed.
  Hint Rewrite view_change_state_check_one_stable : pbft.

  Lemma wf_view_change_state_preserved_on_event :
    forall (eo  : EventOrdering)
           (e   : Event)
           (slf : Rep)
           (st  : PBFTstate),
      state_sm_on_event (PBFTreplicaSM slf) e = Some st
      -> wf_view_change_state (view_change_state st).
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers4 smash_pbft_ind6_10.
  Qed.
  Hint Resolve wf_view_change_state_preserved_on_event : pbft.

  Lemma wf_view_change_state_preserved_before_event :
    forall (eo  : EventOrdering)
           (e   : Event)
           (slf : Rep)
           (st  : PBFTstate),
      state_sm_before_event (PBFTreplicaSM slf) e = Some st
      -> wf_view_change_state (view_change_state st).
  Proof.
    introv eqst.

    pose proof (ite_first_state_sm_on_event_as_before (PBFTreplicaSM slf) e) as q.

    remember (state_sm_on_event (PBFTreplicaSM slf) (local_pred e)) as stsm.
    symmetry in Heqstsm.
    unfold ite_first in q; smash_pbft; rewrite eqst in q; ginv.
    eapply wf_view_change_state_preserved_on_event; eauto.
  Qed.
  Hint Resolve wf_view_change_state_preserved_before_event : pbft.

End PBFTwf_view_change_state.


Hint Constructors wf_view_change_state.


Hint Rewrite @view_change_state_decrement_requests_in_progress_if_primary : pbft.
Hint Rewrite @view_change_state_trim_checkpoint : pbft.
Hint Rewrite @view_change_state_update_checkpoint_from_new_view : pbft.
Hint Rewrite @vce_new_view_add_own_view_change2entry : pbft.
Hint Rewrite @vce_view_changes_add_new_view_to_entry : pbft.
Hint Rewrite @vce_view_change_add_new_view_to_entry : pbft.
Hint Rewrite @vce_view_add_new_view_to_entry : pbft.
Hint Rewrite @vce_view_changes_add_own_view_change2entry : pbft.
Hint Rewrite @vce_view_add_own_view_change2entry : pbft.
Hint Rewrite @log_new_view_preserves_wf_view_change_state_iff : pbft.
Hint Rewrite @view_change2view_refresh_view_change : pbft.
Hint Rewrite @vce_view_replace_own_view_change_in_entry : pbft.
Hint Rewrite @vce_view_change_replace_own_view_change_in_entry : pbft.
Hint Rewrite @vce_new_view_replace_own_view_change_in_entry : pbft.
Hint Rewrite @CheckBCastNewView2entry_initial_state : pbft.
Hint Rewrite @CheckBCastNewView2entry_initial_view_change_state : pbft.
Hint Rewrite @view_change_state_check_one_stable : pbft.


Hint Resolve check_send_replies_preserves_wf_view_change_state : pbft.
Hint Resolve check_send_replies_update_log_preserves_wf_view_change_state : pbft.
Hint Resolve check_stable_preserves_wf_view_change_state : pbft.
Hint Resolve check_stable_update_checkpoint_state_preserves_wf_view_change_state : pbft.
Hint Resolve correct_view_change_implies_wf_view_change : pbft.
Hint Resolve wf_prepared_infos_gather_valid_prepared_messages : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_wf_view_change_state : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_wf_view_change_state : pbft.
Hint Resolve update_state_new_view_preserves_wf_view_change_state : pbft.
(*Hint Resolve implies_wf_view_change_state_update_low_water_mark : pbft.*)
Hint Resolve log_checkpoint_cert_from_new_view_preserves_wf_view_change_state : pbft.
Hint Resolve add_other_view_change_preserves_wf_view_change_state : pbft.
Hint Resolve start_view_change_preserves_wf_view_change_state : pbft.
Hint Resolve add_own_view_change2entry_preserves_wf_view_change_entry : pbft.
Hint Resolve diff_views_implies_in_log_new_view : pbft.
Hint Resolve log_new_view_preserves_wf_view_change_state : pbft.
Hint Resolve add_new_view_to_entry_preserves_wf_view_change_entry : pbft.
Hint Resolve find_and_execute_requests_preserves_wf_view_change_state : pbft.
Hint Resolve execute_requests_preserves_wf_view_change_state : pbft.
Hint Resolve check_broadcast_checkpoint_preserves_wf_view_change_state : pbft.
Hint Resolve wf_view_change_state_implies_all_entries : pbft.
Hint Resolve wf_view_change_state_preserved_on_event : pbft.
Hint Resolve wf_view_change_state_preserved_before_event : pbft.
Hint Resolve wf_view_change_state_add_new_view_to_entry_implies : pbft.
Hint Resolve wf_view_change_state_view_change_state_update_log : pbft.
Hint Resolve check_broadcast_new_view_implies_wf_view_change_state_log_new_view_and_entry : pbft.
Hint Resolve check_broadcast_new_view_implies_equal_views : pbft.
Hint Resolve wf_view_change_entry_replace_own_view_change_in_entry : pbft.
Hint Resolve check_broadcast_new_view_implies_wf_view_change_entry : pbft.
Hint Resolve wf_view_change_state_update_view : pbft.
Hint Resolve wf_view_change_state_change_sequence_number : pbft.
Hint Resolve wf_view_change_state_log_pre_prepares_of_new_view : pbft.
Hint Resolve wf_view_change_state_log_new_view_and_entry : pbft.
Hint Resolve wf_view_change_state_log_new_view_and_entry_state : pbft.
Hint Resolve CheckBCastNewView2entry_implies_wf_view_change_entry : pbft.
Hint Resolve wf_view_change_state_own_view_change2initial_entry : pbft.
Hint Resolve wf_view_change_mk_current_view_change : pbft.
Hint Resolve wf_view_change_state_other_view_change2initial_entry : pbft.
Hint Resolve wf_view_change_state_log_new_view_state : pbft.
Hint Resolve check_stable_preserves_view_change_state : pbft.
