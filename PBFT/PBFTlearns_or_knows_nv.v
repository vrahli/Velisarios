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
Require Export LearnAndKnows.
Require Export PBFTlearns_or_knows_pl_nv.


Section PBFTlearns_or_knows_nv.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition pbft_nv_data := NewView.

  Definition pbft_nv_info := NewView.

  Definition pbft_nv_knows (d : pbft_nv_data) (s : PBFTstate) : Prop :=
    new_view_in_log d (view_change_state s).

  Definition pbft_nv_data2main_auth_data (d : pbft_nv_data) : AuthenticatedData :=
    new_view2main_auth_data d.

  Definition pbft_nv_verify (eo : EventOrdering) (e : Event) (d : pbft_nv_data) : bool :=
    verify_list_auth_data (loc e) (keys e) (new_view2auth_data d).

  Definition pbft_nv_data2loc (d : pbft_nv_data) : Rep :=
    new_view2sender d.

  Lemma pbft_nv_no_initial_memory :
    forall n d, ~ pbft_nv_knows d (Process.sm_state (PBFTreplicaSM n)).
  Proof.
    introv h; simpl in h; auto.
  Qed.

  Instance PBFT_I_LearnAndKnow_nv : LearnAndKnow 2.
  Proof.
    exact (MkLearnAndKnow
             2
             pbft_nv_data
             pbft_nv_info
             (fun x => x)
             PBFTstate
             pbft_nv_knows
             pbft_nv_data2loc
             pbft_nv_data2main_auth_data
             pbft_nv_verify
             _ _ pbft_nv_no_initial_memory).
  Defined.

  Definition knows2
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 2 PBFT_I_LearnAndKnow_nv) :=
    @knows PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 2 PBFT_I_LearnAndKnow_nv eo e d.

  Definition knew2
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 2 PBFT_I_LearnAndKnow_nv) :=
    @knew PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 2 PBFT_I_LearnAndKnow_nv eo e d.

  Definition learns2
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 2 PBFT_I_LearnAndKnow_nv) :=
    @learns PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok PBFT_I_ContainedAuthData 2 PBFT_I_LearnAndKnow_nv eo e d.

  Definition learned2
             {eo : EventOrdering}
             (e : Event)
             (d : @lak_data PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok 2 PBFT_I_LearnAndKnow_nv) :=
    @learned PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok PBFT_I_ContainedAuthData 2 PBFT_I_LearnAndKnow_nv eo e d.

  Definition learns_or_knows2 (eo : EventOrdering) :=
    @learns_or_knows PBFT_I_Data PBFT_I_Node PBFT_I_Key PBFT_I_Msg PBFT_I_Quorum PBFT_I_AuthTok PBFT_I_ContainedAuthData 2 PBFT_I_LearnAndKnow_nv eo.


  Lemma knows_pl_nv_implies_knows_nv :
    forall (eo : EventOrdering) (e : Event) pl,
      knows1 e pl
      ->
      exists nv pi,
        knows2 e nv
        /\ In pi (mergeP (new_view2cert nv))
        /\ prepare_like_in_prepared_info pl pi.
  Proof.
    introv k.
    unfold knows1, knows in k; simpl in *; exrepnd.
    unfold pbft_pl_nv_knows in *; exrepnd.
    exists nv pi; dands; auto.
    exists mem n; dands; auto.
  Qed.

  Lemma pl_in_nv_in_get_contained_authenticated_data_implies :
    forall nv pl pi trig,
      In (pbft_nv_data2main_auth_data nv) (get_contained_authenticated_data trig)
      -> In pi (mergeP (new_view2cert nv))
      -> prepare_like_in_prepared_info pl pi
      -> In (pbft_pl_data2main_auth_data pl) (get_contained_authenticated_data trig).
  Proof.
    introv i j k.
    destruct trig, nv, v; simpl in *; repndors; tcsp; ginv;
      try (complete (destruct r; simpl in *; ginv));
      try (complete (destruct p; simpl in *; ginv));
      try (complete (destruct c; simpl in *; ginv)).

    - destruct p, b; simpl in *.
      unfold pre_prepare2auth_data_req in *; simpl in *.
      allrw in_map_iff; exrepnd; ginv.
      destruct x; simpl in *; ginv.

    - destruct v; simpl in *; repndors; ginv.
      allrw in_app_iff; repndors.

      + assert False; tcsp.
        induction C; simpl in *; tcsp.
        repndors; tcsp.
        destruct a1; ginv.

      + assert False; tcsp.
        induction P; simpl in *; tcsp.
        repndors; tcsp.

        * destruct a1; simpl in *.
          destruct prepared_info_pre_prepare; simpl in *; ginv.

        * destruct a1; simpl in *.
          destruct prepared_info_pre_prepare, b; simpl in *; ginv.
          allrw in_app_iff; repndors; tcsp.

          {
            unfold pre_prepare2auth_data_req in *; simpl in *.
            allrw in_map_iff; exrepnd.
            destruct x; ginv.
          }

          {
            induction prepared_info_prepares; simpl in *; tcsp.
            repndors; tcsp.
            destruct a2; ginv.
          }

    - destruct v; simpl in *; repndors; ginv.

      + unfold mergeP in *; simpl in *.

        allrw in_app_iff.
        right; left.
        induction V; simpl in *; tcsp.
        allrw in_app_iff; repndors; tcsp.
        left.
        clear IHV.
        destruct a0, v0; simpl in *.
        allrw in_app_iff.
        right; right.
        unfold view_change2prep in j; simpl in j.
        induction P; simpl in *; tcsp.
        allrw in_app_iff; repndors; subst; tcsp.

        clear IHP.
        destruct pi, pl; simpl in *; subst; tcsp.
        right; left; right.
        induction prepared_info_prepares; simpl in *; repndors; subst; tcsp.

      + allrw in_app_iff.
        repndors.

        * assert False; tcsp.
          clear j k.
          induction V; simpl in *; tcsp.
          allrw in_app_iff; repndors; tcsp.
          clear IHV.
          destruct a1, v1; simpl in *; repndors; tcsp; ginv.
          allrw in_app_iff.
          repndors; tcsp.

          {
            induction C; simpl in *; tcsp.
            destruct a2, b; simpl in *; repndors; tcsp; ginv.
          }

          {
            induction P; simpl in *; tcsp.
            destruct a2; simpl in *; repndors; tcsp; ginv.
            destruct prepared_info_pre_prepare; ginv.
            allrw in_app_iff; repndors; tcsp.

            - destruct prepared_info_pre_prepare, b; simpl in *; ginv.
              unfold pre_prepare2auth_data_req in i; simpl in *.
              allrw in_map_iff; exrepnd; destruct x; ginv.

            - induction prepared_info_prepares; simpl in *; repndors; tcsp.
              destruct a2; ginv.
          }

        *  assert False; tcsp; clear j k.
           induction OP; simpl in *; tcsp.
           destruct a1, b; repndors; simpl in *; ginv.
           allrw in_app_iff; repndors; tcsp.
           unfold pre_prepare2auth_data_req in *; simpl in *.
           allrw in_map_iff; exrepnd; destruct x; ginv.

        *  assert False; tcsp; clear j k.
           induction NP; simpl in *; tcsp.
           destruct a1, b; repndors; simpl in *; ginv.
           allrw in_app_iff; repndors; tcsp.
           unfold pre_prepare2auth_data_req in *; simpl in *.
           allrw in_map_iff; exrepnd; destruct x; ginv.
  Qed.
  Hint Resolve pl_in_nv_in_get_contained_authenticated_data_implies : pbft.

  Lemma pbft_nv_verify_implies_pbft_pl_verify :
    forall (eo : EventOrdering) (e : Event) nv pl pi,
      pbft_nv_verify eo e nv = true
      -> In pi (mergeP (new_view2cert nv))
      -> prepare_like_in_prepared_info pl pi
      -> pbft_pl_verify eo e pl = true.
  Proof.
    introv verif i j.
    destruct nv, v; simpl in *.
    unfold pbft_nv_verify in verif; simpl in *; smash_pbft.
    allrw verify_list_auth_data_app; smash_pbft.
    clear verif verif1 verif2.

    induction V; simpl in *; tcsp.
    allrw verify_list_auth_data_app; smash_pbft.
    allrw in_app_iff; repndors; tcsp;[].
    clear verif1 IHV.
    destruct a0, v0; simpl in *; smash_pbft.
    clear verif0.
    unfold view_change2prep in *; simpl in *.
    allrw verify_list_auth_data_app; smash_pbft.
    clear verif1.

    induction P; simpl in *; tcsp; smash_pbft.
    allrw verify_list_auth_data_app; smash_pbft.
    repndors; subst; tcsp; smash_pbft.
    clear IHP verif1 verif2.

    destruct pi, pl; simpl in *; subst; tcsp.

    clear verif0.

    induction prepared_info_prepares; simpl in *; tcsp; smash_pbft.
    repndors; subst; tcsp.
  Qed.
  Hint Resolve pbft_nv_verify_implies_pbft_pl_verify : pbft.

  Lemma auth_data_in_trigger_nv_implies_pl :
    forall (eo : EventOrdering) (e : Event) nv pl pi,
      auth_data_in_trigger (pbft_nv_data2main_auth_data nv) e
      -> In pi (mergeP (new_view2cert nv))
      -> prepare_like_in_prepared_info pl pi
      -> auth_data_in_trigger (pbft_pl_data2main_auth_data pl) e.
  Proof.
    introv ad i prep.
    unfold auth_data_in_trigger in *.
    remember (trigger e) as trig; destruct trig; auto; eauto 3 with pbft.
  Qed.
  Hint Resolve auth_data_in_trigger_nv_implies_pl : pbft.

  Lemma in_bind_op_list_nv_implies_pl :
    forall (eo : EventOrdering) (e : Event) nv pl pi,
      In (pbft_nv_data2main_auth_data nv) (bind_op_list PBFTget_contained_auth_data (trigger e))
      -> In pi (mergeP (new_view2cert nv))
      -> prepare_like_in_prepared_info pl pi
      -> In (pbft_pl_data2main_auth_data pl) (bind_op_list PBFTget_contained_auth_data (trigger e)).
  Proof.
    introv ad i prep.
    allrw in_bind_op_list_as_auth_data_in_trigger; eauto 3 with pbft.
  Qed.
  Hint Resolve in_bind_op_list_nv_implies_pl : pbft.

  Lemma learns_nv_implies_learns_pl :
    forall (eo : EventOrdering) (e : Event) nv pl pi,
      learns2 e nv
      -> In pi (mergeP (new_view2cert nv))
      -> prepare_like_in_prepared_info pl pi
      -> learns0 e pl.
  Proof.
    introv ln i j.
    unfold learns2, learns0, learns in *; simpl in *.
    exrepnd.
    exists n; dands; auto; eauto 3 with pbft eo.
  Qed.
  Hint Resolve learns_nv_implies_learns_pl : pbft.

  Lemma learned_nv_implies_learned_pl :
    forall (eo : EventOrdering) (e : Event) nv pl pi,
      learned2 e nv
      -> In pi (mergeP (new_view2cert nv))
      -> prepare_like_in_prepared_info pl pi
      -> learned0 e pl.
  Proof.
    introv ln i j.
    unfold learned2, learned0, learned in *; exrepnd.
    eexists; dands; eauto; eauto 3 with pbft;
      try (eapply learns_nv_implies_learns_pl; eauto).
  Qed.
  Hint Resolve learned_nv_implies_learned_pl : pbft.

  Lemma verify_new_view_implies_pbft_nv_verify :
    forall (eo : EventOrdering) (e : Event) n nv ks,
      loc e = PBFTreplica n
      -> keys e = ks
      -> verify_new_view n ks nv = true
      -> pbft_nv_verify eo e nv = true.
  Proof.
    introv eqloc eqks verif.
    unfold verify_new_view in verif.
    unfold pbft_nv_verify.
    allrw; auto.
  Qed.
  Hint Resolve verify_new_view_implies_pbft_nv_verify : pbft.

  Lemma pbft_nv_verify_verify_new_view :
    forall (eo : EventOrdering) (e : Event) (n : Rep) (nv : NewView) (ks : local_key_map),
      loc e = PBFTreplica n
      -> keys e = ks
      -> pbft_nv_verify eo e nv = true
      -> verify_new_view n ks nv = true.
  Proof.
    introv eqloc eqks verif.
    unfold verify_new_view.
    unfold pbft_nv_verify in verif.
    rw <- eqloc; subst; auto.
  Qed.

  Lemma pbft_nv_data2main_auth_data_in_trigger_implies :
    forall (eo : EventOrdering) (e : Event) nv,
      auth_data_in_trigger (pbft_nv_data2main_auth_data nv) e
      -> event_triggered_by_message e (PBFTnew_view nv).
  Proof.
    introv j; unfold event_triggered_by_message.
    unfold auth_data_in_trigger in j.
    remember (trigger e) as trig; destruct trig; simpl in *; tcsp.
    destruct m; simpl in *; repndors; ginv; tcsp;
      try (complete (destruct r, nv; simpl in *; ginv));
      try (complete (destruct p, nv; simpl in *; ginv));
      try (complete (destruct c, nv; simpl in *; ginv)).

    - destruct p, nv, b; simpl in *.
      unfold pre_prepare2auth_data_req in j; simpl in j.
      apply in_map_iff in j; exrepnd.
      destruct x; simpl in *; ginv.

    - destruct nv, v, v; simpl in *; repndors; ginv.
      allrw in_app_iff; repndors.

      + clear Heqtrig; assert False; tcsp.
        induction C; simpl in *; repndors; tcsp.
        destruct a1; simpl in *; ginv.

      + clear Heqtrig; assert False; tcsp.
        induction P; simpl in *; allrw in_app_iff; repndors; tcsp.

        * destruct a1, prepared_info_pre_prepare; simpl in *; ginv.

        * destruct a1, prepared_info_pre_prepare, b; simpl in *.
          unfold pre_prepare2auth_data_req in *; simpl in *.
          allrw in_map_iff; exrepnd.
          destruct x; ginv.

        * destruct a1; simpl in *.
          clear IHP.
          induction prepared_info_prepares; simpl in *; repndors; tcsp.
          destruct a1; ginv.

    - destruct nv, v, v; simpl in *.
      repndors; ginv.
      allrw in_app_iff; repndors.

      + clear Heqtrig; assert False; tcsp.
        induction V; simpl in *; repndors; tcsp.
        allrw in_app_iff; repndors; tcsp.
        destruct a1, v1; simpl in *; repndors; ginv.
        allrw in_app_iff; repndors.

        * clear IHV.
          induction C; simpl in *; repndors; tcsp.
          destruct a2; simpl in *; ginv.

        * clear IHV.
          induction P; simpl in *; allrw in_app_iff; repndors; tcsp.

          { destruct a2, prepared_info_pre_prepare; simpl in *; ginv. }

          { destruct a2, prepared_info_pre_prepare, b; simpl in *.
            unfold pre_prepare2auth_data_req in *; simpl in *.
            allrw in_map_iff; exrepnd.
            destruct x; ginv. }

          { destruct a2; simpl in *.
            clear IHP.
            induction prepared_info_prepares; simpl in *; repndors; tcsp.
            destruct a2; ginv. }

      + clear Heqtrig; assert False; tcsp.
        induction OP; simpl in *; repndors; tcsp.

        * destruct a1; ginv.

        * destruct a1, b; allrw in_app_iff; repndors; ginv; tcsp.

          unfold pre_prepare2auth_data_req in j; allrw in_map_iff; simpl in *.
          exrepnd; destruct x; simpl in *; ginv.

      + clear Heqtrig; assert False; tcsp.
        induction NP; simpl in *; repndors; tcsp.

        * destruct a1; ginv.

        * destruct a1, b; allrw in_app_iff; repndors; ginv; tcsp.

          unfold pre_prepare2auth_data_req in j; allrw in_map_iff; simpl in *.
          exrepnd; destruct x; simpl in *; ginv.
  Qed.

End PBFTlearns_or_knows_nv.


Ltac custom_prove_knows :=
  eapply implies_knows; eauto; autorewrite with pbft eo; simpl; auto;
  unfold pbft_nv_knows;
  eauto 4 with pbft.

Ltac custom_smash_pbft_ind ind :=
  let base_tac := (fun _ => smash_pbft3) in
  let ind_tac  := (fun _ => eauto 4 with pbft; try (complete custom_prove_knows)) in
  smash_pbft_ind_tac ind base_tac ind_tac.


Hint Resolve pl_in_nv_in_get_contained_authenticated_data_implies : pbft.
Hint Resolve pbft_nv_verify_implies_pbft_pl_verify : pbft.
Hint Resolve learns_nv_implies_learns_pl : pbft.
Hint Resolve learned_nv_implies_learned_pl : pbft.
Hint Resolve verify_new_view_implies_pbft_nv_verify : pbft.
Hint Resolve auth_data_in_trigger_nv_implies_pl : pbft.
Hint Resolve in_bind_op_list_nv_implies_pl : pbft.
