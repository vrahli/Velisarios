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



Require Export PBFTin_log.
Require Export PBFTprepare_in_log_preserves.


Section PBFTsomewhere_in_log.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition prepare_in_entry (p : Prepare) (e : PBFTlogEntry) :=
    (is_prepare_for_entry e p)
      &&
      (existsb
         (same_rep_tok (prepare2rep_toks p))
         (log_entry_prepares e)).


  Fixpoint prepare_somewhere_in_log
           (p : Prepare)
           (l : PBFTlog) : bool :=
    match l with
    | [] => false
    | entry :: entries =>
      prepare_in_entry p entry
      || prepare_somewhere_in_log p entries
    end.

  Definition pre_prepare_in_entry
             (pp : Pre_prepare)
             (d  : PBFTdigest)
             (e  : PBFTlogEntry) : bool :=
      let a    := pre_prepare2auth pp in
      let reqs := pre_prepare2requests pp in
      let nfo  := log_entry_pre_prepare_info e in
      (similar_entry_and_pre_prepare e pp d)
        && (auth_matches_logEntryPrePrepareInfo a nfo)
        && (requests_matches_logEntryPrePrepareInfo reqs nfo).

  Fixpoint pre_prepare_somewhere_in_log
           (pp : Pre_prepare)
           (d  : PBFTdigest)
           (l  : PBFTlog) : bool :=
    match l with
    | [] => false
    | entry :: entries =>
      pre_prepare_in_entry pp d entry
      || pre_prepare_somewhere_in_log pp d entries
    end.

  Lemma prepare_in_somewhere_in_log_implies_prepare_in_log :
    forall (eo : EventOrdering)
           (e  : Event)
           (i  : Rep)
           (p  : Prepare)
           (st : PBFTstate),
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> prepare_somewhere_in_log p (log st) = true
      -> prepare_in_log p (log st) = true.
  Proof.
    introv eqst prep.
    apply log_is_well_formed_on_event in eqst.
    remember (log st) as L.
    clear dependent st.
    clear dependent i.

    induction L; simpl in *; tcsp; smash_pbft; repndors; tcsp;
      try (inversion eqst as [|? ? imp wfe wfl]; subst; clear eqst);
      try (complete (unfold prepare_in_entry in *; smash_pbft)).

    repeat (autodimp IHL hyp).
    applydup entry_of_prepare_in_log in IHL; exrepnd.
    applydup imp in IHL0.
    unfold entries_have_different_request_data in *.
    unfold is_prepare_for_entry in *.
    unfold eq_request_data in *; smash_pbft.
  Qed.

  Lemma entry_of_pre_prepare_in_log :
    forall pp d L,
      pre_prepare_in_log pp d L = true
      -> exists entry,
        In entry L
        /\ log_entry_request_data entry = pre_prepare2request_data pp d.
  Proof.
    induction L; introv h; simpl in *; tcsp.
    pbft_dest_all x.

    - exists a; dands; tcsp.
      allrw similar_entry_and_pre_prepare_true_iff; auto.

    - apply IHL in h; exrepnd; exists entry; auto.
  Qed.

  Lemma pre_prepare_in_somewhere_in_log_implies_pre_prepare_in_log :
    forall (eo : EventOrdering)
           (e  : Event)
           (i  : Rep)
           (pp : Pre_prepare)
           (d  : PBFTdigest)
           (st : PBFTstate),
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> pre_prepare_somewhere_in_log pp d (log st) = true
      -> pre_prepare_in_log pp d (log st) = true.
  Proof.
    introv eqst prep.
    apply log_is_well_formed_on_event in eqst.
    remember (log st) as L.
    clear dependent st.
    clear dependent i.

    induction L; simpl in *; tcsp; smash_pbft; repndors; tcsp;
      try (inversion eqst as [|? ? imp wfe wfl]; subst; clear eqst);
      try (complete (unfold pre_prepare_in_entry in *; smash_pbft)).

    repeat (autodimp IHL hyp).

    applydup entry_of_pre_prepare_in_log in IHL; exrepnd.
    applydup imp in IHL0.
    unfold entries_have_different_request_data in *.
    allrw similar_entry_and_pre_prepare_true_iff.
    congruence.
  Qed.

End PBFTsomewhere_in_log.
