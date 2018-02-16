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
Require Export PBFTprepared_is_preserved.
Require Export PBFTprops4.
Require Export PBFTreceived_prepare_like.
Require Export PBFT_A_1_9_part1.
Require Export PBFT_A_1_2_5.
Require Export PBFT_A_1_4.
Require Export PBFT_A_1_5.
Require Export PBFTcollision_resistant.


Section PBFT_A_1_9_misc1.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma length_view_change2sender_V :
      forall V,
        length (map view_change2sender V) = length V.
  Proof.
    induction V; introv; simpl in *; ginv; smash_pbft; tcsp.
  Qed.
  Hint Rewrite length_view_change2sender_V : pbft.

  Lemma length_view_change2sender_V_2F :
    forall F V,
      F + (F + 0) + 1 <= length V
      ->  2 * F + 1 <= length (map view_change2sender V).
  Proof.
    induction V; introv h; simpl in *; ginv; smash_pbft; tcsp.
  Qed.
  Hint Resolve length_view_change2sender_V_2F : pbft.

  Lemma in_view_change2sender_implies_exists_vc :
    forall V sender,
      In sender (map view_change2sender V)
      -> exists vc,
        In vc V
        /\ view_change2sender vc = sender.
  Proof.
    induction V; introv InV; simpl in *; smash_pbft; tcsp.
    repndors;[|].

    {  exists a. dands; auto. }
    { apply IHV in InV.
      exrepnd.
      exists vc. dands; auto.
    }
  Qed.

  Definition pre_prepares_of_view_change (vc : ViewChange) : list Pre_prepare :=
    map prepared_info_pre_prepare (view_change2prep vc).

  Lemma pp_vc_dec :
    forall vc n d,
      Decidable.decidable
        (exists v r a,
            In (mk_pre_prepare v n r a) (pre_prepares_of_view_change vc)
            /\ d = requests2digest r).
  Proof.
    introv.
    destruct vc, v; simpl in *.
    unfold pre_prepares_of_view_change; simpl.
    unfold view_change2prep; simpl.

    induction P; simpl in *; ginv; smash_pbft; tcsp.

    { right; intro xx; tcsp. }

    {
      destruct IHP as [IHP|IHP].

      - exrepnd.
        left.
        eexists; eexists; eexists; dands; eauto.

      - destruct a0; simpl in *.
        destruct prepared_info_pre_prepare; simpl in *.
        destruct b; simpl in *.

        destruct (SeqNumDeq s0 n) as [dn|dn]; subst.

        + destruct (PBFTdigestdeq d (requests2digest d0)) as [dd|dd]; subst.

          {
            left.
            exists v0 d0 a0; dands; tcsp.
          }

          {
            right; introv xx; exrepnd; subst.
            unfold mk_pre_prepare in *.
            repndors; ginv;[].
            destruct IHP.
            eexists; eexists; eexists; dands; eauto.
          }

        + right; introv xx; exrepnd; subst.
          unfold mk_pre_prepare in *.
          repndors; ginv;[].
          destruct IHP.
          eexists; eexists; eexists; dands; eauto.
    }
  Qed.

  Lemma p_info_in_V_implies_exists_vc :
    forall p_info V,
      In p_info (mergeP V)
      -> exists vc,
        In vc V
        /\ In p_info (view_change2prep vc).
  Proof.
    induction V; introv i; simpl in *; tcsp.

    allrw in_app_iff; repndors; tcsp.

    { exists a; tcsp. }

    {
      apply IHV in i.
      exrepnd.
      exists vc. tcsp.
    }
  Qed.

  Lemma p_info_in_cert_of_nv_implies_p_info_is_prepared :
    forall (eo     : EventOrdering)
           (e      : Event)
           (nv     : NewView)
           (p_info : PreparedInfo)
           (slf    : Rep)
           (state  : PBFTstate),
      loc e = PBFTreplica slf
      -> state_sm_on_event (PBFTreplicaSM slf) e = Some state
      -> new_view_in_log nv (view_change_state state)
      -> In p_info (mergeP (new_view2cert nv))
      -> info_is_prepared p_info = true.
  Proof.
    introv eqloc eqst nvil piM.

    dup piM as e_vc.
    eapply p_info_in_V_implies_exists_vc in e_vc.
    destruct e_vc as [vc [in_vc_V in_p_info_vc]].

    dup nvil as corr.
    eapply PBFT_A_1_2_5 in corr; eauto.
    unfold correct_new_view in *. smash_pbft.

    rename_hyp_with correct_new_view_opre_prepare_op corr_O.
    rename_hyp_with correct_new_view_npre_prepare_op corr_N.
    rename_hyp_with correct_view_change corr_vc.

    hide_hyp corr_O.
    hide_hyp corr_N.
    hide_hyp corr.

    allrw forallb_forall.
    pose proof (corr_vc vc) as corr_vc_vc. clear corr_vc.
    autodimp corr_vc_vc hyp.

    unfold correct_view_change in *.
    allrw andb_true.
    exrepnd.

    rename_hyp_with correct_view_change_preps corr_vc_prep.

    unfold correct_view_change_preps in *.
    allrw forallb_forall.

    pose proof (corr_vc_prep p_info) as corr_prep. clear corr_vc_prep.
    autodimp corr_prep hyp.

    allrw andb_true.
    exrepnd.

    unfold valid_prepared_info in *.
    allrw andb_true.
    exrepnd. auto.
  Qed.

  Lemma correct_new_view_implies_large_enough_certificate :
    forall nv,
      correct_new_view nv = true
      -> 2 * F + 1 <= length (new_view2cert nv)
         /\ no_repeats (map view_change2sender (new_view2cert nv)).
  Proof.
    introv cor.
    unfold correct_new_view in cor; smash_pbft.
    allrw @norepeatsb_as_no_repeats.
    dands; auto.
  Qed.

End PBFT_A_1_9_misc1.


Hint Resolve length_view_change2sender_V_2F : pbft.


Hint Rewrite @length_view_change2sender_V : pbft.
