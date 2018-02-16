(*

  Copyright 2016 Luxembourg University
  Copyright 2017 Luxembourg University
  Copyright 2018 Luxembourg University

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


Require Export PBFTlearns_or_knows_vc_nv.


Section PBFTlearns_or_knows_cp_vc_nv.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition pbft_cp_vc_nv_data := Checkpoint.

  Definition pbft_cp_vc_nv_info := StateInfo.

  Definition pbft_cp_vc_nv_knows (d : pbft_cp_vc_nv_data) (s : PBFTstate) : Prop :=
    exists nv vc,
      new_view_in_log nv (view_change_state s)
      /\ In vc (new_view2cert nv)
      /\ In d (view_change2cert vc).

  Definition checkpoint2main_auth_data (cp : Checkpoint) : AuthenticatedData :=
    match cp with
    | checkpoint cp a => MkAuthData (PBFTmsg_bare_checkpoint cp) a
    end.

  Definition pbft_cp_vc_nv_data2main_auth_data (d : pbft_cp_vc_nv_data) : AuthenticatedData :=
    checkpoint2main_auth_data d.

  Definition pbft_cp_vc_nv_verify (eo : EventOrdering) (e : Event) (d : pbft_cp_vc_nv_data) : bool :=
    verify_one_auth_data (loc e) (keys e) (checkpoint2auth_data d).

  Definition pbft_cp_vc_nv_data2loc (d : pbft_cp_vc_nv_data) : Rep :=
    checkpoint2sender d.

  Lemma pbft_cp_vc_nv_no_initial_memory :
    forall n d, ~ pbft_cp_vc_nv_knows d (Process.sm_state (PBFTreplicaSM n)).
  Proof.
    introv h.
    unfold pbft_cp_vc_nv_knows in h; exrepnd; simpl in *; auto.
  Qed.

  Instance PBFT_I_LearnAndKnow_cp_vc_nv : LearnAndKnow 4.
  Proof.
    exact (MkLearnAndKnow
             4
             pbft_cp_vc_nv_data
             pbft_cp_vc_nv_info
             checkpoint2state_info
             PBFTstate
             pbft_cp_vc_nv_knows
             pbft_cp_vc_nv_data2loc
             pbft_cp_vc_nv_data2main_auth_data
             pbft_cp_vc_nv_verify
             _ _ pbft_cp_vc_nv_no_initial_memory).
  Defined.

  Definition knows4
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 4 PBFT_I_LearnAndKnow_cp_vc_nv) :=
    @knows PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 4 PBFT_I_LearnAndKnow_cp_vc_nv eo e d.

  Definition knew4
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 4 PBFT_I_LearnAndKnow_cp_vc_nv) :=
    @knew PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 4 PBFT_I_LearnAndKnow_cp_vc_nv eo e d.

  Definition learns4
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 4 PBFT_I_LearnAndKnow_cp_vc_nv) :=
    @learns PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok PBFT_I_ContainedAuthData 4 PBFT_I_LearnAndKnow_cp_vc_nv eo e d.

  Definition learned4
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 4 PBFT_I_LearnAndKnow_cp_vc_nv) :=
    @learned PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok PBFT_I_ContainedAuthData 4 PBFT_I_LearnAndKnow_cp_vc_nv eo e d.

  Definition learns_or_knows4 (eo : EventOrdering) :=
    @learns_or_knows PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok PBFT_I_ContainedAuthData 4 PBFT_I_LearnAndKnow_cp_vc_nv eo.

  Definition knows_certificate4
             {eo : EventOrdering}
             (e : Event)
             (n : nat)
             (i : @lak_info PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 4 PBFT_I_LearnAndKnow_cp_vc_nv) :=
    @knows_certificate PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 4 PBFT_I_LearnAndKnow_cp_vc_nv eo e n i (fun _ => True).

  Lemma in_knows3_implies_knows4 :
    forall {eo : EventOrdering} (e : Event) vc cp,
      knows3 e vc
      -> In cp (view_change2cert vc)
      -> knows4 e cp.
  Proof.
    introv kn i.
    unfold knows4, knows3, knows in *; simpl in *; exrepnd.
    unfold pbft_vc_nv_knows in *; simpl in *; exrepnd.
    exists mem n; dands; auto.
    exists nv vc; dands; auto.
  Qed.
  Hint Resolve @in_knows3_implies_knows4 : pbft.

  Lemma knows3_implies_knows_certificate4 :
    forall {eo : EventOrdering} (e : Event) vc,
      knows3 e vc
      -> knows_certificate4 e (F + 1) (view_change2state_info vc).
  Proof.
    introv kn.
    exists (view_change2cert vc); simpl in *; dands;
      eauto 3 with pbft;
      try (eapply knows3_implies_ge_length_checkpoints; eauto);
      try (eapply knows3_implies_no_repeats_checkpoints2senders; eauto).
    introv i; try (fold (knows4 e d)); dands; auto; eauto 3 with pbft;
      try (eapply knows3_implies_same_state_info; eauto).
  Qed.

  Lemma split_eq_state_info :
    forall si1 si2,
      si1 = si2
      -> si_digest si1 = si_digest si2 /\ si_seq si1 = si_seq si2.
  Proof.
    introv e; destruct si1, si2; simpl in *; inversion e; auto.
  Qed.

  Lemma knows3_implies_knows4 :
    forall {eo : EventOrdering} (e : Event) vc,
      exists_at_most_f_faulty [e] F
      -> knows3 e vc
      ->
      exists cp,
        knows4 e cp
        /\ node_has_correct_trace_before e (checkpoint2sender cp)
        /\ checkpoint2digest cp = view_change2digest vc
        /\ checkpoint2seq cp = view_change2seq vc.
  Proof.
    introv atmost kn.
    apply knows3_implies_knows_certificate4 in kn.
    apply (knows_weak_certificate _ _ _ _ [e] F) in kn; simpl in *; auto; try omega.
    exrepnd; subst.
    apply split_eq_state_info in kn0; repnd; simpl in *.
    exists d; dands; auto.
  Qed.

End PBFTlearns_or_knows_cp_vc_nv.


Hint Resolve in_knows3_implies_knows4 : pbft.
