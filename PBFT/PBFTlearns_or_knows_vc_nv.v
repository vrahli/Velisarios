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


Require Export PBFTreceived_prepare_like1.
Require Export PBFTprepare_like2request_data.
Require Export PBFTnew_view_util.
Require Export PBFTcheckpoints_from_good.
Require Export PBFTstate_info.
Require Export LearnAndKnows.


Section PBFTlearns_or_knows_vc_nv.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition pbft_vc_nv_data := ViewChange.

  Definition pbft_vc_nv_info := StateInfo.

  Definition pbft_vc_nv_knows (d : pbft_vc_nv_data) (s : PBFTstate) : Prop :=
    exists nv,
      new_view_in_log nv (view_change_state s)
      /\ In d (new_view2cert nv).

  Definition view_change2main_auth_data (vc : ViewChange) : AuthenticatedData :=
    match vc with
    | view_change vc a => MkAuthData (PBFTmsg_bare_view_change vc) a
    end.

  Definition pbft_vc_nv_data2main_auth_data (d : pbft_vc_nv_data) : AuthenticatedData :=
    view_change2main_auth_data d.

  Definition pbft_vc_nv_verify (eo : EventOrdering) (e : Event) (d : pbft_vc_nv_data) : bool :=
    verify_list_auth_data (loc e) (keys e) (view_change2auth_data d).

  Definition pbft_vc_nv_data2loc (d : pbft_vc_nv_data) : Rep :=
    view_change2sender d.

  Lemma pbft_vc_nv_no_initial_memory :
    forall n d, ~ pbft_vc_nv_knows d (Process.sm_state (PBFTreplicaSM n)).
  Proof.
    introv h.
    unfold pbft_vc_nv_knows in h; exrepnd; simpl in *; auto.
  Qed.

  Instance PBFT_I_LearnAndKnow_vc_nv : LearnAndKnow 3.
  Proof.
    exact (MkLearnAndKnow
             3
             pbft_vc_nv_data
             pbft_vc_nv_info
             view_change2state_info
             PBFTstate
             pbft_vc_nv_knows
             pbft_vc_nv_data2loc
             pbft_vc_nv_data2main_auth_data
             pbft_vc_nv_verify
             _ _ pbft_vc_nv_no_initial_memory).
  Defined.

  Definition knows3
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 3 PBFT_I_LearnAndKnow_vc_nv) :=
    @knows PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 3 PBFT_I_LearnAndKnow_vc_nv eo e d.

  Definition knew3
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 3 PBFT_I_LearnAndKnow_vc_nv) :=
    @knew PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 3 PBFT_I_LearnAndKnow_vc_nv eo e d.

  Definition learns3
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 3 PBFT_I_LearnAndKnow_vc_nv) :=
    @learns PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok PBFT_I_ContainedAuthData 3 PBFT_I_LearnAndKnow_vc_nv eo e d.

  Definition learned3
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 3 PBFT_I_LearnAndKnow_vc_nv) :=
    @learned PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok PBFT_I_ContainedAuthData 3 PBFT_I_LearnAndKnow_vc_nv eo e d.

  Definition learns_or_knows3 (eo : EventOrdering) :=
    @learns_or_knows PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok PBFT_I_ContainedAuthData 3 PBFT_I_LearnAndKnow_vc_nv eo.

  Definition knows_certificate3
             {eo : EventOrdering}
             (e : Event)
             (n : nat)
             (i : @lak_info PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 3 PBFT_I_LearnAndKnow_vc_nv) :=
    @knows_certificate PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 3 PBFT_I_LearnAndKnow_vc_nv eo e n i (fun _ => True).

  Lemma knows3_implies_no_repeats_checkpoints2senders :
    forall {eo : EventOrdering} (e : Event) vc,
      knows3 e vc
      -> no_repeats (map checkpoint2sender (view_change2cert vc)).
  Proof.
    introv kn.
    unfold knows3, knows in *; simpl in *; exrepnd.
    unfold pbft_vc_nv_knows in *; simpl in *; exrepnd.

    dup kn3 as corvc.
    apply correct_new_view_implies_correct_view_change in corvc;
      auto;eauto 3 with pbft.
  Qed.
  Hint Resolve knows3_implies_no_repeats_checkpoints2senders : pbft.

  Lemma knows3_implies_ge_length_checkpoints2senders :
    forall {eo : EventOrdering} (e : Event) vc,
      knows3 e vc
      -> F + 1 <= length (map checkpoint2sender (view_change2cert vc)).
  Proof.
    introv kn.
    unfold knows3, knows in *; simpl in *; exrepnd.
    unfold pbft_vc_nv_knows in *; simpl in *; exrepnd.

    dup kn3 as corvc.
    apply correct_new_view_implies_correct_view_change in corvc; eauto 3 with pbft.
  Qed.
  Hint Resolve knows3_implies_ge_length_checkpoints2senders : pbft.

  Lemma knows3_implies_ge_length_checkpoints :
    forall {eo : EventOrdering} (e : Event) vc,
      knows3 e vc
      -> F + 1 <= length (view_change2cert vc).
  Proof.
    introv kn.
    unfold knows3, knows in *; simpl in *; exrepnd.
    unfold pbft_vc_nv_knows in *; simpl in *; exrepnd.

    dup kn3 as corvc.
    apply correct_new_view_implies_correct_view_change in corvc; eauto 3 with pbft.
  Qed.
  Hint Resolve knows3_implies_ge_length_checkpoints : pbft.

  Lemma correct_view_change_implies_same_state_info :
    forall vc cp v,
      In cp (view_change2cert vc)
      -> correct_view_change v vc = true
      -> view_change2state_info vc = checkpoint2state_info cp.
  Proof.
    introv i cor.
    unfold correct_view_change in *; smash_pbft.
    unfold correct_view_change_cert in *; smash_pbft.
    allrw forallb_forall.
    apply cor0 in i.
    unfold correct_view_change_cert_one in i; smash_pbft.
    unfold same_seq_nums, same_digests in *; smash_pbft.
    unfold view_change2state_info, checkpoint2state_info.
    allrw; auto.
  Qed.
  Hint Resolve correct_view_change_implies_same_state_info : pbft.

  Lemma knows3_implies_same_state_info :
    forall {eo : EventOrdering} (e : Event) vc cp,
      knows3 e vc
      -> In cp (view_change2cert vc)
      -> view_change2state_info vc = checkpoint2state_info cp.
  Proof.
    introv kn i.
    unfold knows3, knows in *; simpl in *; exrepnd.
    unfold pbft_vc_nv_knows in *; simpl in *; exrepnd.

    dup kn3 as corvc.
    apply correct_new_view_implies_correct_view_change in corvc; eauto 3 with pbft.
  Qed.
  Hint Resolve knows3_implies_same_state_info : pbft.

End PBFTlearns_or_knows_vc_nv.


Hint Resolve knows3_implies_no_repeats_checkpoints2senders : pbft.
Hint Resolve knows3_implies_ge_length_checkpoints2senders : pbft.
Hint Resolve knows3_implies_ge_length_checkpoints : pbft.
Hint Resolve correct_view_change_implies_same_state_info : pbft.
Hint Resolve knows3_implies_same_state_info : pbft.
