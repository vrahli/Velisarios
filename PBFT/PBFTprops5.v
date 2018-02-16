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


Require Export PBFTwf_view_change_state.


Section PBFTprops5.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.

  Lemma check_broadcast_new_view_some_implies_current_view_le_new_view2view :
    forall i state entry nv entry' OP NP,
      check_broadcast_new_view i state entry = Some (nv, entry', OP, NP)
      -> wf_view_change_entry entry
      -> current_view state <= new_view2view nv.
  Proof.
    introv check wf.
    unfold check_broadcast_new_view in *; smash_pbft.
    unfold view_changed_entry in *; smash_pbft.

    match goal with
    | [ H : vce_view_change _ = Some _ |- _ ] =>
      apply (wf_view_change_entry_view_change entry) in H
    end; auto.
    allrw; auto.
  Qed.
  Hint Resolve check_broadcast_new_view_some_implies_current_view_le_new_view2view : pbft.

  Lemma view_change_state_update_checkpoint_from_new_view :
    forall s C maxV,
      view_change_state (update_checkpoint_from_new_view s C maxV)
      = view_change_state s.
  Proof.
    introv.
    unfold update_checkpoint_from_new_view; smash_pbft.
  Qed.
  Hint Rewrite view_change_state_update_checkpoint_from_new_view : pbft.

  Lemma view_change_state_trim_checkpoint :
    forall s n,
      view_change_state (trim_checkpoint s n) = view_change_state s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite view_change_state_trim_checkpoint : pbft.

  Lemma log_checkpoint_cert_from_new_view_preserves_view_change_state :
    forall i s1 v n C S s2 opchk,
      log_checkpoint_cert_from_new_view i s1 v n C S = (s2, opchk)
      -> view_change_state s2 = view_change_state s1.
  Proof.
    introv chk.
    unfold log_checkpoint_cert_from_new_view in chk; smash_pbft.
  Qed.
  Hint Resolve log_checkpoint_cert_from_new_view_preserves_view_change_state : pbft.

(*  Lemma view_change_state_update_low_water_mark :
    forall s n,
      view_change_state (update_low_water_mark s n) = view_change_state s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite view_change_state_update_low_water_mark : pbft.*)

  Lemma update_state_new_view_preserves_view_change_state :
    forall i s1 nv s2 msgs,
      update_state_new_view i s1 nv = (s2, msgs)
      -> view_change_state s2 = view_change_state s1.
  Proof.
    introv upd.
    unfold update_state_new_view in upd; smash_pbft.
    simpl.
    rename_hyp_with log_checkpoint_cert_from_new_view chk.
    apply log_checkpoint_cert_from_new_view_preserves_view_change_state in chk; auto.
  Qed.
  Hint Resolve update_state_new_view_preserves_view_change_state : pbft.

  Lemma check_send_replies_preserves_view_change_state :
    forall i view keys entryop state1 sn state2 msgs,
      check_send_replies i view keys entryop state1 sn = (msgs, state2)
      -> view_change_state state2 = view_change_state state1.
  Proof.
    introv check; unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_view_change_state : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_view_change_state :
    forall i s1 P s2 msgs,
      add_prepare_to_log_from_new_view_pre_prepare i s1 P = (s2, msgs)
      -> view_change_state s2 = view_change_state s1.
  Proof.
    introv add; unfold add_prepare_to_log_from_new_view_pre_prepare in add; smash_pbft.
    match goal with
    | [ H : context[check_send_replies] |- _ ] =>
      apply check_send_replies_preserves_view_change_state in H; simpl in H; auto
    end.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_view_change_state : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state :
    forall i P s1 s2 msgs,
      add_prepares_to_log_from_new_view_pre_prepares i s1 P = (s2, msgs)
      -> view_change_state s2 = view_change_state s1.
  Proof.
    induction P; introv add; simpl in *; smash_pbft.
    erewrite IHP;[|eauto].
    eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_view_change_state; eauto.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state : pbft.

  Lemma switch_log_new_view_state_log_pre_prepares_of_new_view :
    forall s L nv,
      log_new_view_state (log_pre_prepares_of_new_view s L) nv
      = log_pre_prepares_of_new_view (log_new_view_state s nv) L.
  Proof.
    introv; destruct s; simpl; auto.
  Qed.

  Lemma view_change_state_log_pre_prepares_of_new_view :
    forall s L,
      view_change_state (log_pre_prepares_of_new_view s L)
      = view_change_state s.
  Proof.
    introv; destruct s; simpl; auto.
  Qed.
  Hint Rewrite view_change_state_log_pre_prepares_of_new_view : pbft.

  Lemma swap_log_new_view_state_update_view :
    forall s v nv,
      log_new_view_state (update_view s v) nv
      = update_view (log_new_view_state s nv) v.
  Proof.
    introv; destruct s; auto.
  Qed.

  Lemma view_change_state_update_view :
    forall s v, view_change_state (update_view s v) = view_change_state s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite view_change_state_update_view : pbft.

  Lemma pre_prepare_in_log_clear_log_checkpoint_false_implies :
    forall (n : SeqNum) pp d L,
      n < pre_prepare2seq pp
      -> pre_prepare_in_log pp d (clear_log_checkpoint L n) = false
      -> pre_prepare_in_log pp d L = false.
  Proof.
    induction L; introv h prep; simpl in *; smash_pbft.
    repeat (autodimp IHL hyp).
    allrw SeqNumLe_true.
    destruct a; simpl in *.
    unfold eq_request_data in *; smash_pbft.
    destruct pp, b, log_entry_request_data; simpl in *; ginv; try omega.
  Qed.
  Hint Resolve pre_prepare_in_log_clear_log_checkpoint_false_implies : pbft.

  Lemma update_state_new_view_preserves_pre_prepare_in_log_false_forward :
    forall pp d i s1 v s2 msgs,
      correct_new_view v = true
      -> update_state_new_view i s1 v = (s2, msgs)
      -> low_water_mark s2 < pre_prepare2seq pp
      -> pre_prepare_in_log pp d (log s2) = false
      -> pre_prepare_in_log pp d (log s1) = false.
  Proof.
    introv cor upd h prep.

    unfold update_state_new_view in upd; smash_pbft.
    unfold log_checkpoint_cert_from_new_view in *; smash_pbft.

    - unfold update_log_checkpoint_stable, low_water_mark in *; simpl in *.
      apply pre_prepare_in_log_clear_log_checkpoint_false_implies in prep; eauto 3 with pbft.

      rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      apply sn_of_view_change_cert2max_seq_vc in mseq; subst.

      rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft;[].
      subst; auto.

    - rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      apply sn_of_view_change_cert2max_seq_vc in mseq; subst.

      rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      apply extract_seq_and_digest_from_checkpoint_certificate_none_implies in ext.
      rewrite ext in *.
      simpl in *; ginv.

    - unfold update_log_checkpoint_stable, low_water_mark in *; simpl in *.
      apply pre_prepare_in_log_clear_log_checkpoint_false_implies in prep; eauto 3 with pbft.

      rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      apply sn_of_view_change_cert2max_seq_vc in mseq; subst.

      rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft;[].
      subst; auto.

    - rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      apply sn_of_view_change_cert2max_seq_vc in mseq; subst.

      rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      apply extract_seq_and_digest_from_checkpoint_certificate_none_implies in ext.
      rewrite ext in *.
      simpl in *; ginv.

      apply correct_new_view_implies_correct_view_change in mseq0; auto.
      unfold correct_view_change, correct_view_change_cert in *; smash_pbft.
      rewrite ext in *; simpl in *; omega.
  Qed.
  Hint Resolve update_state_new_view_preserves_pre_prepare_in_log_false_forward : pbft.

  Lemma seq_of_pre_prepare_in_new_view :
    forall pp d nv,
      In (pp,d) (map add_digest (new_view2oprep nv ++ new_view2nprep nv))
      -> correct_new_view nv = true
      ->
      exists (n : SeqNum),
        view_change_cert2max_seq (new_view2cert nv) = Some n
        /\ n < pre_prepare2seq pp.
  Proof.
    introv i cor.
    unfold correct_new_view in cor; smash_pbft.
    allrw map_app.
    allrw forallb_forall.
    allrw in_app_iff.
    allrw in_map_iff.
    repndors; exrepnd; unfold add_digest in *; ginv; discover.

    - unfold correct_new_view_opre_prepare_op in *; smash_pbft.
      eexists; dands; eauto.
      unfold correct_new_view_opre_prepare in *; smash_pbft.

    - unfold correct_new_view_npre_prepare_op in *; smash_pbft.
      eexists; dands; eauto.
      unfold correct_new_view_npre_prepare in *; smash_pbft.
  Qed.

  Lemma vce_view_replace_own_view_change_in_entry :
    forall vc e,
      vce_view (replace_own_view_change_in_entry vc e)
      = vce_view e.
  Proof.
    destruct e; simpl; auto.
  Qed.
  Hint Rewrite vce_view_replace_own_view_change_in_entry : pbft.

End PBFTprops5.


Hint Resolve check_broadcast_new_view_some_implies_current_view_le_new_view2view : slow.
Hint Resolve log_checkpoint_cert_from_new_view_preserves_view_change_state : pbft.
Hint Resolve update_state_new_view_preserves_view_change_state : pbft.
Hint Resolve check_send_replies_preserves_view_change_state : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_view_change_state : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_view_change_state : pbft.
Hint Resolve pre_prepare_in_log_clear_log_checkpoint_false_implies : pbft.
Hint Resolve update_state_new_view_preserves_pre_prepare_in_log_false_forward : pbft.


Hint Rewrite @view_change_state_update_checkpoint_from_new_view : pbft.
Hint Rewrite @view_change_state_trim_checkpoint : pbft.
Hint Rewrite @view_change_state_log_pre_prepares_of_new_view : pbft.
Hint Rewrite @view_change_state_update_view : pbft.
Hint Rewrite @vce_view_replace_own_view_change_in_entry : pbft.
