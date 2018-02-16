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


Require Export PBFTlearns_or_knows_pl.


Section PBFTlearns_or_knows_pl_nv.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition pbft_pl_nv_knows (d : pbft_pl_data) (s : PBFTstate) : Prop :=
    exists nv pi,
      new_view_in_log nv (view_change_state s)
      /\ In pi (mergeP (new_view2cert nv))
      /\ prepare_like_in_prepared_info d pi.

  Lemma pbft_pl_nv_no_initial_memory :
    forall n d, ~ pbft_pl_nv_knows d (Process.sm_state (PBFTreplicaSM n)).
  Proof.
    introv h; simpl in h.
    unfold pbft_pl_nv_knows in h; exrepnd; simpl in *; auto.
  Qed.

  Instance PBFT_I_LearnAndKnow_pl_nv : LearnAndKnow 1.
  Proof.
    exact (MkLearnAndKnow
             1
             pbft_pl_data
             pbft_pl_info
             prepare_like2request_data
             PBFTstate
             pbft_pl_nv_knows
             pbft_pl_data2loc
             pbft_pl_data2main_auth_data
             pbft_pl_verify
             _ _ pbft_pl_nv_no_initial_memory).
  Defined.

  Definition knows_certificate1
             {eo : EventOrdering}
             (e : Event)
             (n : nat)
             (i : @lak_info PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 1 PBFT_I_LearnAndKnow_pl_nv)
             (P : list (@lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 1 PBFT_I_LearnAndKnow_pl_nv) -> Prop):=
    @knows_certificate PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 1 PBFT_I_LearnAndKnow_pl_nv eo e n i P.

  Definition pbft_knows_rd1 {eo : EventOrdering} (e : Event) (rd : RequestData) :=
    knows_certificate1 e (2 * F + 1) rd one_pre_prepare.

  Definition knows1
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 1 PBFT_I_LearnAndKnow_pl_nv) :=
    @knows PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 1 PBFT_I_LearnAndKnow_pl_nv eo e d.

  Definition knew1
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 1 PBFT_I_LearnAndKnow_pl_nv) :=
    @knew PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 1 PBFT_I_LearnAndKnow_pl_nv eo e d.

  Definition learns1
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 1 PBFT_I_LearnAndKnow_pl_nv) :=
    @learns PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok PBFT_I_ContainedAuthData 1 PBFT_I_LearnAndKnow_pl_nv eo e d.

  Definition learned1
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 1 PBFT_I_LearnAndKnow_pl_nv) :=
    @learned PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok PBFT_I_ContainedAuthData 1 PBFT_I_LearnAndKnow_pl_nv eo e d.

  Lemma prepared_as_pbft_knows_rd :
    forall (eo : EventOrdering) (e : Event) pi i s nv,
      loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some s
      -> well_formed_log (log s)
      -> info_is_prepared pi = true
      -> new_view_in_log nv (view_change_state s)
      -> In pi (mergeP (new_view2cert nv))
      -> pbft_knows_rd1 e (prepared_info2request_data pi).
  Proof.
    introv eqloc eqst wf prep nvinlog piin.
    unfold info_is_prepared in *; smash_pbft.

    allrw @norepeatsb_as_no_repeats.
    allrw forallb_forall.

    exists ((prepare_like_pre_prepare (prepared_info_pre_prepare pi))
              :: map prepare_like_prepare (prepared_info_prepares pi)).

    simpl; autorewrite with pbft list; dands; auto;
      try (complete (rewrite <- length_prepared_info2senders_eq_length_prepared_info_prepares; omega)).

    - constructor; auto.
      introv xx.
      apply prep1 in xx.
      smash_pbft.

    - unfold one_pre_prepare; simpl.
      f_equal.
      apply length_zero_iff_nil.
      match goal with
      | [ |- ?x = _ ] => remember x as l; destruct l; auto
      end.
      assert False; tcsp.
      pose proof (filter_In is_pre_prepare_like p (map prepare_like_prepare (prepared_info_prepares pi))) as q.
      destruct q as [q q']; clear q'.
      rewrite <- Heql in q; simpl in q; autodimp q hyp.
      repnd.
      apply in_map_iff in q0; exrepnd; subst.
      destruct x; simpl in *; ginv.

    - introv h; repndors; subst; tcsp; dands.

      + exists s i; dands; auto; exists nv pi; dands; auto.
        destruct pi; simpl; auto.

      + destruct pi, prepared_info_pre_prepare, b; simpl.
        unfold prepared_info2request_data, pre_prepare2digest; simpl.
        f_equal.
        unfold prepared_info_has_correct_digest, prepared_info2requests in *; simpl in *; smash_pbft.

      + allrw in_map_iff; exrepnd; subst; auto.
        exists s i; dands; auto; exists nv pi; dands; auto.

      + allrw in_map_iff; exrepnd; subst; auto.
        destruct pi, prepared_info_pre_prepare, b; simpl.
        unfold PBFTheader.prepared_info_prepares in *.
        unfold prepared_info2request_data, pre_prepare2digest in *; simpl.
        apply prep0 in h0.
        simpl in h0; smash_pbft.
  Qed.

  Definition knows_in_intersection1
             {eo : EventOrdering}
             (e1 e2 : Event)
             (n : nat)
             (i1 i2 : @lak_info PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 1 PBFT_I_LearnAndKnow_pl_nv)
             P E N :=
    @knows_in_intersection PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok PBFT_I_ContainedAuthData 1 PBFT_I_LearnAndKnow_pl_nv eo e1 e2 n i1 i2 P E N.

  Definition local_knows_in_intersection1
             {eo : EventOrdering}
             (e : Event)
             (n : nat)
             (i1 i2 : @lak_info PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 1 PBFT_I_LearnAndKnow_pl_nv)
             P E N :=
    @local_knows_in_intersection PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 1 PBFT_I_LearnAndKnow_pl_nv eo e n i1 i2 P E N.

End PBFTlearns_or_knows_pl_nv.
