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
Require Export LearnAndKnows.


Section PBFTlearns_or_knows_pl.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition pbft_pl_data := Prepare_like.

  Definition pbft_pl_info := RequestData.

  Definition pbft_pl_knows (d : pbft_pl_data) (s : PBFTstate) : Prop :=
    prepare_like_in_log d (log s).

  Definition pbft_pl_data2main_auth_data (d : pbft_pl_data) : AuthenticatedData :=
    prepare_like2main_auth_data d.

  Definition pbft_pl_data2loc (d : pbft_pl_data) : Rep :=
    prepare_like2sender d.

  Lemma pbft_pl_no_initial_memory :
    forall n d, ~ pbft_pl_knows d (Process.sm_state (PBFTreplicaSM n)).
  Proof.
    introv h; simpl in h; auto.
  Qed.

  Definition pbft_pl_verify (eo : EventOrdering) (e : Event) (d : pbft_pl_data) : bool :=
    verify_authenticated_data (loc e) (pbft_pl_data2main_auth_data d) (keys e).

  Global Instance PBFT_I_LearnAndKnow_pl : LearnAndKnow 0.
  Proof.
    exact (MkLearnAndKnow
             0
             pbft_pl_data
             pbft_pl_info
             prepare_like2request_data
             PBFTstate
             pbft_pl_knows
             pbft_pl_data2loc
             pbft_pl_data2main_auth_data
             pbft_pl_verify
             _ _ pbft_pl_no_initial_memory).
  Defined.

  Definition one_pre_prepare (l : list Prepare_like) : Prop :=
    length (filter is_pre_prepare_like l) = 1.

  Definition pbft_knows_rd {eo : EventOrdering} (e : Event) (rd : RequestData) :=
    knows_certificate e (2 * F + 1) rd one_pre_prepare.

  Definition knows0
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 0 PBFT_I_LearnAndKnow_pl) :=
    @knows PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 0 PBFT_I_LearnAndKnow_pl eo e d.

  Definition knew0
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 0 PBFT_I_LearnAndKnow_pl) :=
    @knew PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 0 PBFT_I_LearnAndKnow_pl eo e d.

  Definition learns0
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 0 PBFT_I_LearnAndKnow_pl) :=
    @learns PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok PBFT_I_ContainedAuthData 0 PBFT_I_LearnAndKnow_pl eo e d.

  Definition learned0
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 0 PBFT_I_LearnAndKnow_pl) :=
    @learned PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok PBFT_I_ContainedAuthData 0 PBFT_I_LearnAndKnow_pl eo e d.

End PBFTlearns_or_knows_pl.
