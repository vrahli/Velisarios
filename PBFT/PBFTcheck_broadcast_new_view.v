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


Require Export PBFTwell_formed_log.
Require Export PBFTwf_view_change_state.
Require Export PBFTgarbage_collect_misc1.


Section PBFTcheck_broadcast_new_view.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma check_broadcast_new_view_preserves_sender :
    forall i state entry nv entry' OP NP pp d,
      wf_view_change_entry entry
      -> check_broadcast_new_view i state entry = Some (nv, entry', OP, NP)
      -> In (pp, d) (OP ++ NP)
      -> pre_prepare2sender pp = i.
  Proof.
    introv wf check k.

    dup check as check'.
    eapply check_broadcast_new_view_preserves_view in check';[|eauto].

    unfold check_broadcast_new_view in check; smash_pbft.
    destruct pp, b; simpl in *.
    subst.

    unfold view_changed_entry in *; smash_pbft.
    destruct entry; simpl in *.

    erewrite wf_view_change_entry_view_change; eauto.
    simpl; auto.
  Qed.
  Hint Resolve check_broadcast_new_view_preserves_sender : pbft.

  Lemma is_some_false_implies_none :
    forall {T} (x : option T), is_some x = false -> x = None.
  Proof.
    introv h; destruct x; simpl in *; tcsp.
  Qed.
  Hint Resolve is_some_false_implies_none : pbft opt.

  Lemma check_broadcast_new_view_implies_equal_new_view2oprep :
    forall i s1 e nv e' O N,
      check_broadcast_new_view i s1 e = Some (nv, e', O, N)
      -> new_view2oprep nv = map fst O.
  Proof.
    introv check.
    unfold check_broadcast_new_view in check; smash_pbft.
  Qed.

  Lemma check_broadcast_new_view_implies_equal_new_view2nprep :
    forall i s1 e nv e' O N,
      check_broadcast_new_view i s1 e = Some (nv, e', O, N)
      -> new_view2nprep nv = map fst N.
  Proof.
    introv check.
    unfold check_broadcast_new_view in check; smash_pbft.
  Qed.

  Lemma create_new_prepare_messages_implies_no_repeats_seqs :
    forall L v keys P O N,
      no_repeats L
      -> create_new_prepare_messages L v keys P = (O, N)
      -> no_repeats (map (fun p => pre_prepare2seq (fst p)) (O ++ N)).
  Proof.
    introv norep cr.
    apply create_new_prepare_messages_implies_eqset_and_norepeatsb in cr; repnd.

    - apply norepeatsb_as_no_repeats in cr.
      allrw map_app; allrw map_map; unfold compose in *; auto.

    - apply norepeatsb_as_no_repeats; auto.
  Qed.
  Hint Resolve create_new_prepare_messages_implies_no_repeats_seqs : pbft.

  Lemma no_repeats_from_min_to_max_of_view_changes :
    forall entry,
      no_repeats (from_min_to_max_of_view_changes entry).
  Proof.
    introv.
    pose proof (norepeatsb_from_min_to_max_of_view_changes entry) as h.
    apply norepeatsb_as_no_repeats in h; auto.
  Qed.
  Hint Resolve no_repeats_from_min_to_max_of_view_changes : pbft.

  Lemma check_broadcast_new_view_implies_no_repeats_seqs :
    forall i s e nv e' O N,
      check_broadcast_new_view i s e = Some (nv, e', O, N)
      -> no_repeats (map (fun p => pre_prepare2seq (fst p)) (O ++ N)).
  Proof.
    introv check; unfold check_broadcast_new_view in check; smash_pbft.
  Qed.
  Hint Resolve check_broadcast_new_view_implies_no_repeats_seqs : pbft.

  Definition auth_pre_prepare (pp : Pre_prepare) (keys : local_key_map) :=
    authenticate (PBFTmsg_bare_pre_prepare (pre_prepare2bare pp)) keys.

  Lemma create_new_prepare_messages_implies_equal_auth :
    forall L v keys P O N pp d,
      create_new_prepare_messages L v keys P = (O, N)
      -> In (pp,d) (O ++ N)
      -> pre_prepare2auth pp = auth_pre_prepare pp keys.
  Proof.
    induction L; introv cr j; simpl in *; pbft_simplifier; simpl in *; tcsp;[].
    smash_pbft; repndors; subst; tcsp.

    - unfold create_new_prepare_message in *; smash_pbft.

    - eapply IHL; eauto.

    - allrw in_app_iff; simpl in *; repndors; subst.

      + eapply IHL; eauto; allrw in_app_iff; eauto.

      + unfold create_new_prepare_message in *; smash_pbft.

      + eapply IHL; eauto; allrw in_app_iff; eauto.
  Qed.
  Hint Resolve create_new_prepare_messages_implies_equal_auth : pbft.

  Lemma check_broadcast_new_view_implies_digest_and_auth :
    forall i s e nv e' O N pp d,
      check_broadcast_new_view i s e = Some (nv, e', O, N)
      -> In (pp, d) (O ++ N)
      -> digest_for_pre_prepare d pp = true
         /\ pre_prepare2auth pp = auth_pre_prepare pp (local_keys s).
  Proof.
    introv check j.
    unfold check_broadcast_new_view in check; smash_pbft;[].
    rename_hyp_with create_new_prepare_messages cr.
    dup cr as cr'.
    eapply create_new_prepare_messages_implies_well_formed_pre_prepare_and_digest in cr';
      [| |eauto];
      [|eapply all_correct_view_change_implies_wf_prepared_infos;
        unfold view_changed_entry in *; smash_pbft];[].
    dands; eauto 3 with pbft.
  Qed.

  Lemma in_check_broadcast_new_view_implies_between_water_marks2 :
    forall i state e nv e' opreps npreps pp d m,
      check_broadcast_new_view i state e = Some (nv, e', opreps, npreps)
      -> In (pp,d) (opreps ++ npreps)
      -> view_change_cert2max_seq (new_view2cert nv) = Some m
      -> check_between_water_marks m (pre_prepare2seq pp) = true.
  Proof.
    introv check j vc.
    unfold view_change_cert2max_seq in *; smash_pbft.
    eapply in_check_broadcast_new_view_implies_between_water_marks; eauto.
  Qed.

  Lemma view_change_entry2view_changes_replace_own_view_change_in_entry :
    forall vc e,
      view_change_entry2view_changes (replace_own_view_change_in_entry vc e)
      = vc :: vce_view_changes e.
  Proof.
    introv; destruct e; simpl; tcsp.
  Qed.
  Hint Rewrite view_change_entry2view_changes_replace_own_view_change_in_entry : pbft.

  Lemma check_broadcast_new_view_implies :
    forall i s e nv e' O N,
      check_broadcast_new_view i s e = Some (nv, e', O, N)
      ->
      exists (vc vc' : ViewChange) (maxV : SeqNum),
        vce_view_change e = Some vc
        /\ vce_view_change e' = Some vc'
        /\ vc' = refresh_view_change vc s
        /\ e' = replace_own_view_change_in_entry vc' e
        /\ vce_new_view e = None
        /\ view_change_cert2max_seq (view_change_entry2view_changes e') = Some maxV
        /\ new_view2cert nv = view_change_entry2view_changes e'
        /\ view_change_entry2view_changes e' = vc' :: vce_view_changes e'
        /\ vce_view_changes e' = vce_view_changes e
        /\ low_water_mark s <= maxV
        /\ vce_view e' = vce_view e
        /\ current_view s <= vce_view e
        /\ initial_view < vce_view e
  (*          /\ new_view2view nv = vce_view e'*).
  Proof.
    introv check.
    unfold check_broadcast_new_view in check; smash_pbft;[].
    unfold view_changed_entry in *; smash_pbft;[].
    unfold view_change_cert2max_seq; simpl.
    smash_pbft;[| |]; eexists; eexists; eexists; dands; eauto;
      eauto 2 with opt; try omega.
  Qed.

End PBFTcheck_broadcast_new_view.


Hint Resolve is_some_false_implies_none : pbft opt.
Hint Resolve no_repeats_from_min_to_max_of_view_changes : pbft.
Hint Resolve create_new_prepare_messages_implies_no_repeats_seqs : pbft.
Hint Resolve check_broadcast_new_view_preserves_view : pbft.
Hint Resolve check_broadcast_new_view_preserves_sender : pbft.
Hint Resolve check_broadcast_new_view_implies_no_repeats_seqs : pbft.
Hint Resolve create_new_prepare_messages_implies_equal_auth : pbft.


Hint Rewrite @view_change_entry2view_changes_replace_own_view_change_in_entry : pbft.
