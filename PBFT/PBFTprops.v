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


Section PBFTprops.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext }.
  Context { pbft_auth : PBFTauth }.
  Context { pbft_keys : PBFTinitial_keys }.
  Context { pbft_hash : PBFThash }.


  Lemma is_primary_false :
    forall v n, is_primary v n = false <-> n <> PBFTprimary v.
  Proof.
    introv.
    unfold is_primary.
    dest_cases w; split; intro h; tcsp.
  Qed.

  Lemma is_primary_true :
    forall v n, is_primary v n = true <-> n = PBFTprimary v.
  Proof.
    introv.
    unfold is_primary.
    dest_cases w; split; intro h; tcsp.
  Qed.

  Lemma SeqNumLe_true :
    forall s1 s2, SeqNumLe s1 s2 = true <-> s1 <= s2.
  Proof.
    introv; unfold SeqNumLe.
    rewrite Nat.leb_le; tcsp.
  Qed.

  Lemma SeqNumLe_false :
    forall s1 s2, SeqNumLe s1 s2 = false <-> s1 > s2.
  Proof.
    introv; unfold SeqNumLe.
    rewrite leb_iff_conv. tcsp.
  Qed.

  Lemma SeqNumLt_true :
    forall (s1 s2 : SeqNum), SeqNumLt s1 s2 = true <-> s1 < s2.
  Proof.
    introv; destruct s1, s2; unfold SeqNumLt; simpl in *; split; intro h;
      allrw Nat.ltb_lt; auto.
  Qed.

  Lemma SeqNumLt_false :
    forall (s1 s2 : SeqNum), SeqNumLt s1 s2 = false <-> s2 <= s1.
  Proof.
    introv; destruct s1, s2; unfold SeqNumLt; simpl in *; split;
      intro h; allrw Nat.ltb_ge; auto.
  Qed.

(*  Lemma in_broadcast2others :
    forall m r F,
      In m (broadcast2others r F) <-> exists o, In o (other_names r) /\ m = F o.
  Proof.
    introv.
    unfold broadcast2others.
    rewrite in_map_iff.
    split; intro h; exrepnd; eexists; dands; eauto.
  Qed.*)


  (* ====== CONFLICTING SENDS FOR send_request *)

  Lemma send_request_send_reply :
    forall a b c, send_request a b = send_reply c -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_request_send_pre_prepare :
    forall a b c d, send_request a b = send_pre_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_request_send_prepare :
    forall a b c d, send_request a b = send_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_request_send_commit :
    forall a b c d, send_request a b = send_commit c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_request_send_checkpoint :
    forall a b c d, send_request a b = send_checkpoint c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_request_send_debug :
    forall a b c d, send_request a b = send_debug c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_request_send_view_change :
    forall a b c d, send_request a b = send_view_change c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_request_send_new_view :
    forall a b c d, send_request a b = send_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_request_send_check_ready :
    forall a b d, send_request a b = send_check_ready d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_request_send_check_stable :
    forall a b d, send_request a b = send_check_stable d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_request_send_check_bcast_new_view :
    forall a b c d, send_request a b = send_check_bcast_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_request_send_start_timer :
    forall a b c d, send_request a b = send_start_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_request_send_expired_timer :
    forall a b c d, send_request a b = send_expired_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.


  (* ====== CONFLICTING SENDS FOR send_reply *)

  Lemma send_reply_send_request :
    forall a c d, send_reply a = send_request c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_reply_send_pre_prepare :
    forall a c d, send_reply a = send_pre_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_reply_send_prepare :
    forall a c d, send_reply a = send_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_reply_send_commit :
    forall a c d, send_reply a = send_commit c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_reply_send_checkpoint :
    forall a c d, send_reply a = send_checkpoint c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_reply_send_debug :
    forall a c d, send_reply a = send_debug c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_reply_send_view_change :
    forall a c d, send_reply a = send_view_change c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_reply_send_new_view :
    forall a c d, send_reply a = send_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_reply_send_check_ready :
    forall a d, send_reply a = send_check_ready d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_reply_send_check_stable :
    forall a d, send_reply a = send_check_stable d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_reply_send_check_bcast_new_view :
    forall a c d, send_reply a = send_check_bcast_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_reply_send_start_timer :
    forall a c d, send_reply a = send_start_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_reply_send_expired_timer :
    forall a c d, send_reply a = send_expired_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.


  (* ====== CONFLICTING SENDS FOR send_pre_prepare *)

  Lemma send_pre_prepare_send_request :
    forall a b c d, send_pre_prepare a b = send_request c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_pre_prepare_send_reply :
    forall a b c, send_pre_prepare a b = send_reply c -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_pre_prepare_send_prepare :
    forall a b c d, send_pre_prepare a b = send_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_pre_prepare_send_commit :
    forall a b c d, send_pre_prepare a b = send_commit c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_pre_prepare_send_checkpoint :
    forall a b c d, send_pre_prepare a b = send_checkpoint c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_pre_prepare_send_debug :
    forall a b c d, send_pre_prepare a b = send_debug c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_pre_prepare_send_view_change :
    forall a b c d, send_pre_prepare a b = send_view_change c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_pre_prepare_send_new_view :
    forall a b c d, send_pre_prepare a b = send_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_pre_prepare_send_check_ready :
    forall a b d, send_pre_prepare a b = send_check_ready d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_pre_prepare_send_check_stable :
    forall a b d, send_pre_prepare a b = send_check_stable d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_pre_prepare_send_check_bcast_new_view :
    forall a b c d, send_pre_prepare a b = send_check_bcast_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_pre_prepare_send_start_timer :
    forall a b c d, send_pre_prepare a b = send_start_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_pre_prepare_send_expired_timer :
    forall a b c d, send_pre_prepare a b = send_expired_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.


  (* ====== CONFLICTING SENDS FOR send_prepare *)

  Lemma send_prepare_send_request :
    forall a b c d, send_prepare a b = send_request c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_prepare_send_reply :
    forall a b c, send_prepare a b = send_reply c -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_prepare_send_pre_prepare :
    forall a b c d, send_prepare a b = send_pre_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_prepare_send_commit :
    forall a b c d, send_prepare a b = send_commit c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_prepare_send_checkpoint :
    forall a b c d, send_prepare a b = send_checkpoint c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_prepare_send_debug :
    forall a b c d, send_prepare a b = send_debug c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_prepare_send_view_change :
    forall a b c d, send_prepare a b = send_view_change c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_prepare_send_new_view :
    forall a b c d, send_prepare a b = send_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_prepare_send_check_ready :
    forall a b d, send_prepare a b = send_check_ready d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_prepare_send_check_stable :
    forall a b d, send_prepare a b = send_check_stable d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_prepare_send_check_bcast_new_view :
    forall a b c d, send_prepare a b = send_check_bcast_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_prepare_send_start_timer :
    forall a b c d, send_prepare a b = send_start_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_prepare_send_expired_timer :
    forall a b c d, send_prepare a b = send_expired_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.


  (* ====== CONFLICTING SENDS FOR send_commit *)

  Lemma send_commit_send_request :
    forall a b c d, send_commit a b = send_request c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_commit_send_reply :
    forall a b c, send_commit a b = send_reply c -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_commit_send_pre_prepare :
    forall a b c d, send_commit a b = send_pre_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_commit_send_prepare :
    forall a b c d, send_commit a b = send_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_commit_send_checkpoint :
    forall a b c d, send_commit a b = send_checkpoint c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_commit_send_debug :
    forall a b c d, send_commit a b = send_debug c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_commit_send_view_change :
    forall a b c d, send_commit a b = send_view_change c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_commit_send_new_view :
    forall a b c d, send_commit a b = send_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_commit_send_check_ready :
    forall a b d, send_commit a b = send_check_ready d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_commit_send_check_stable :
    forall a b d, send_commit a b = send_check_stable d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_commit_send_check_bcast_new_view :
    forall a b c d, send_commit a b = send_check_bcast_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_commit_send_start_timer :
    forall a b c d, send_commit a b = send_start_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_commit_send_expired_timer :
    forall a b c d, send_commit a b = send_expired_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.


  (* ====== CONFLICTING SENDS FOR send_checkpoint *)

  Lemma send_checkpoint_send_request :
    forall a b c d, send_checkpoint a b = send_request c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_checkpoint_send_reply :
    forall a b c, send_checkpoint a b = send_reply c -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_checkpoint_send_pre_prepare :
    forall a b c d, send_checkpoint a b = send_pre_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_checkpoint_send_prepare :
    forall a b c d, send_checkpoint a b = send_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_checkpoint_send_commit :
    forall a b c d, send_checkpoint a b = send_commit c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_checkpoint_send_debug :
    forall a b c d, send_checkpoint a b = send_debug c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_checkpoint_send_view_change :
    forall a b c d, send_checkpoint a b = send_view_change c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_checkpoint_send_new_view :
    forall a b c d, send_checkpoint a b = send_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_checkpoint_send_check_ready :
    forall a b d, send_checkpoint a b = send_check_ready d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_checkpoint_send_check_stable :
    forall a b d, send_checkpoint a b = send_check_stable d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_checkpoint_send_check_bcast_new_view :
    forall a b c d, send_checkpoint a b = send_check_bcast_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_checkpoint_send_start_timer :
    forall a b c d, send_checkpoint a b = send_start_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_checkpoint_send_expired_timer :
    forall a b c d, send_checkpoint a b = send_expired_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.


  (* ====== CONFLICTING SENDS FOR send_debug *)

  Lemma send_debug_send_request :
    forall a b c d, send_debug a b = send_request c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_debug_send_reply :
    forall a b c, send_debug a b = send_reply c -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_debug_send_pre_prepare :
    forall a b c d, send_debug a b = send_pre_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_debug_send_prepare :
    forall a b c d, send_debug a b = send_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_debug_send_commit :
    forall a b c d, send_debug a b = send_commit c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_debug_send_checkpoint :
    forall a b c d, send_debug a b = send_checkpoint c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_debug_send_view_change :
    forall a b c d, send_debug a b = send_view_change c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_debug_send_new_view :
    forall a b c d, send_debug a b = send_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_debug_send_check_ready :
    forall a b d, send_debug a b = send_check_ready d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_debug_send_check_stable :
    forall a b d, send_debug a b = send_check_stable d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_debug_send_check_bcast_new_view :
    forall a b c d, send_debug a b = send_check_bcast_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_debug_send_start_timer :
    forall a b c d, send_debug a b = send_start_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_debug_send_expired_timer :
    forall a b c d, send_debug a b = send_expired_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.


  (* ====== CONFLICTING SENDS FOR send_view_change *)

  Lemma send_view_change_send_request :
    forall a b c d, send_view_change a b = send_request c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_view_change_send_reply :
    forall a b c, send_view_change a b = send_reply c -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_view_change_send_pre_prepare :
    forall a b c d, send_view_change a b = send_pre_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_view_change_send_prepare :
    forall a b c d, send_view_change a b = send_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_view_change_send_commit :
    forall a b c d, send_view_change a b = send_commit c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_view_change_send_checkpoint :
    forall a b c d, send_view_change a b = send_checkpoint c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_view_change_send_debug :
    forall a b c d, send_view_change a b = send_debug c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_view_change_send_new_view :
    forall a b c d, send_view_change a b = send_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_view_change_send_check_ready :
    forall a b d, send_view_change a b = send_check_ready d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_view_change_send_check_stable :
    forall a b d, send_view_change a b = send_check_stable d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_view_change_send_check_bcast_new_view :
    forall a b c d, send_view_change a b = send_check_bcast_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_view_change_send_start_timer :
    forall a b c d, send_view_change a b = send_start_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_view_change_send_expired_timer :
    forall a b c d, send_view_change a b = send_expired_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.


  (* ====== CONFLICTING SENDS FOR send_new_view *)

  Lemma send_new_view_send_request :
    forall a b c d, send_new_view a b = send_request c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_new_view_send_reply :
    forall a b c, send_new_view a b = send_reply c -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_new_view_send_pre_prepare :
    forall a b c d, send_new_view a b = send_pre_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_new_view_send_prepare :
    forall a b c d, send_new_view a b = send_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_new_view_send_commit :
    forall a b c d, send_new_view a b = send_commit c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_new_view_send_checkpoint :
    forall a b c d, send_new_view a b = send_checkpoint c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_new_view_send_debug :
    forall a b c d, send_new_view a b = send_debug c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_new_view_send_view_change :
    forall a b c d, send_new_view a b = send_view_change c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_new_view_send_check_ready :
    forall a b d, send_new_view a b = send_check_ready d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_new_view_send_check_stable :
    forall a b d, send_new_view a b = send_check_stable d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_new_view_send_check_bcast_new_view :
    forall a b c d, send_new_view a b = send_check_bcast_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_new_view_send_start_timer :
    forall a b c d, send_new_view a b = send_start_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_new_view_send_expired_timer :
    forall a b c d, send_new_view a b = send_expired_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.


  (* ====== CONFLICTING SENDS FOR send_check_ready *)

  Lemma send_check_ready_send_request :
    forall a c d, send_check_ready a = send_request c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_ready_send_reply :
    forall a c, send_check_ready a = send_reply c -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_ready_send_pre_prepare :
    forall a c d, send_check_ready a = send_pre_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_ready_send_prepare :
    forall a c d, send_check_ready a = send_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_ready_send_commit :
    forall a c d, send_check_ready a = send_commit c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_ready_send_checkpoint :
    forall a c d, send_check_ready a = send_checkpoint c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_ready_send_debug :
    forall a c d, send_check_ready a = send_debug c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_ready_send_view_change :
    forall a c d, send_check_ready a = send_view_change c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_ready_send_new_view :
    forall a c d, send_check_ready a = send_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_ready_send_check_bcast_new_view :
    forall a c d, send_check_ready a = send_check_bcast_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_ready_send_start_timer :
    forall a c d, send_check_ready a = send_start_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_ready_send_expired_timer :
    forall a c d, send_check_ready a = send_expired_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_ready_send_check_stable :
    forall a b, send_check_ready a = send_check_stable b -> False.
  Proof.
    introv h; inversion h.
  Qed.


  (* ====== CONFLICTING SENDS FOR send_check_stable *)

  Lemma send_check_stable_send_request :
    forall a c d, send_check_stable a = send_request c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_stable_send_reply :
    forall a c, send_check_stable a = send_reply c -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_stable_send_pre_prepare :
    forall a c d, send_check_stable a = send_pre_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_stable_send_prepare :
    forall a c d, send_check_stable a = send_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_stable_send_commit :
    forall a c d, send_check_stable a = send_commit c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_stable_send_checkpoint :
    forall a c d, send_check_stable a = send_checkpoint c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_stable_send_debug :
    forall a c d, send_check_stable a = send_debug c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_stable_send_view_change :
    forall a c d, send_check_stable a = send_view_change c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_stable_send_new_view :
    forall a c d, send_check_stable a = send_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_stable_send_check_bcast_new_view :
    forall a c d, send_check_stable a = send_check_bcast_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_stable_send_start_timer :
    forall a c d, send_check_stable a = send_start_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_stable_send_expired_timer :
    forall a c d, send_check_stable a = send_expired_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_stable_send_check_ready :
    forall a b, send_check_stable a = send_check_ready b -> False.
  Proof.
    introv h; inversion h.
  Qed.


  (* ====== CONFLICTING SENDS FOR send_check_bcast_new_view *)

  Lemma send_check_bcast_new_view_send_request :
    forall a b c d, send_check_bcast_new_view a b = send_request c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_bcast_new_view_send_reply :
    forall a b c, send_check_bcast_new_view a b = send_reply c -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_bcast_new_view_send_pre_prepare :
    forall a b c d, send_check_bcast_new_view a b = send_pre_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_bcast_new_view_send_prepare :
    forall a b c d, send_check_bcast_new_view a b = send_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_bcast_new_view_send_commit :
    forall a b c d, send_check_bcast_new_view a b = send_commit c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_bcast_new_view_send_checkpoint :
    forall a b c d, send_check_bcast_new_view a b = send_checkpoint c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_bcast_new_view_send_debug :
    forall a b c d, send_check_bcast_new_view a b = send_debug c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_bcast_new_view_send_view_change :
    forall a b c d, send_check_bcast_new_view a b = send_view_change c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_bcast_new_view_send_new_view :
    forall a b c d, send_check_bcast_new_view a b = send_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_bcast_new_view_send_check_ready :
    forall a b d, send_check_bcast_new_view a b = send_check_ready d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_bcast_new_view_send_check_stable :
    forall a b d, send_check_bcast_new_view a b = send_check_stable d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_bcast_new_view_send_start_timer :
    forall a b c d, send_check_bcast_new_view a b = send_start_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_check_bcast_new_view_send_expired_timer :
    forall a b c d, send_check_bcast_new_view a b = send_expired_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.


  (* ====== CONFLICTING SENDS FOR send_start_timer *)

  Lemma send_start_timer_send_request :
    forall a b c d, send_start_timer a b = send_request c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_start_timer_send_reply :
    forall a b c, send_start_timer a b = send_reply c -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_start_timer_send_pre_prepare :
    forall a b c d, send_start_timer a b = send_pre_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_start_timer_send_prepare :
    forall a b c d, send_start_timer a b = send_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_start_timer_send_commit :
    forall a b c d, send_start_timer a b = send_commit c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_start_timer_send_checkpoint :
    forall a b c d, send_start_timer a b = send_checkpoint c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_start_timer_send_debug :
    forall a b c d, send_start_timer a b = send_debug c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_start_timer_send_view_change :
    forall a b c d, send_start_timer a b = send_view_change c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_start_timer_send_new_view :
    forall a b c d, send_start_timer a b = send_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_start_timer_send_check_ready :
    forall a b d, send_start_timer a b = send_check_ready d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_start_timer_send_check_stable :
    forall a b d, send_start_timer a b = send_check_stable d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_start_timer_send_check_bcast_new_view :
    forall a b c d, send_start_timer a b = send_check_bcast_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_start_timer_send_expired_timer :
    forall a b c d, send_start_timer a b = send_expired_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.


  (* ====== CONFLICTING SENDS FOR send_expired_timer *)

  Lemma send_expired_timer_send_request :
    forall a b c d, send_expired_timer a b = send_request c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_expired_timer_send_reply :
    forall a b c, send_expired_timer a b = send_reply c -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_expired_timer_send_pre_prepare :
    forall a b c d, send_expired_timer a b = send_pre_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_expired_timer_send_prepare :
    forall a b c d, send_expired_timer a b = send_prepare c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_expired_timer_send_commit :
    forall a b c d, send_expired_timer a b = send_commit c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_expired_timer_send_checkpoint :
    forall a b c d, send_expired_timer a b = send_checkpoint c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_expired_timer_send_debug :
    forall a b c d, send_expired_timer a b = send_debug c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_expired_timer_send_view_change :
    forall a b c d, send_expired_timer a b = send_view_change c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_expired_timer_send_new_view :
    forall a b c d, send_expired_timer a b = send_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_expired_timer_send_check_ready :
    forall a b d, send_expired_timer a b = send_check_ready d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_expired_timer_send_check_stable :
    forall a b d, send_expired_timer a b = send_check_stable d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_expired_timer_send_check_bcast_new_view :
    forall a b c d, send_expired_timer a b = send_check_bcast_new_view c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

  Lemma send_expired_timer_send_start_timer :
    forall a b c d, send_expired_timer a b = send_start_timer c d -> False.
  Proof.
    introv h; inversion h.
  Qed.

End PBFTprops.
