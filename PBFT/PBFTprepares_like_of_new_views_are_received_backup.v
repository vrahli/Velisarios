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


Require Export PBFTreceived_prepare_like.
Require Export PBFTprops3.
Require Export PBFTnew_view_are_received2.
Require Export PBFTview_changes_are_received.
Require Export PBFTprepare_like2request_data.
Require Export PBFTnew_view_learns_or_knows.
Require Export PBFTknows_own_new_view.


Section PBFTprepares_like_of_new_views_are_received.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma in_implies_view_change_somewhere_in_log :
    forall entry vc S,
      In entry S
      -> In vc (view_change_entry2view_changes entry)
      -> view_change_somewhere_in_log vc S.
  Proof.
    induction S; introv iS ie; simpl in *; tcsp.
    repndors; subst; tcsp.
    clear IHS.
    destruct entry; simpl in *.
    destruct vce_view_change; simpl in *; tcsp.
    repndors; subst; tcsp.
  Qed.
  Hint Resolve in_implies_view_change_somewhere_in_log : pbft.

  Lemma same_view_change_somewhere_in_log :
    forall vc s,
      PBFTview_change_somewhere_in_log.view_change_somewhere_in_log vc s
      <->
      PBFTreceived_prepare_like1.view_change_somewhere_in_log vc s.
  Proof.
    induction s; introv; simpl; split; intro h; tcsp; repndors; tcsp.

    - destruct a; simpl in *; allrw; simpl; tcsp.

    - destruct a, vce_view_change; simpl in *; simpl; tcsp.

    - rewrite <- IHs; tcsp.

    - destruct a, vce_view_change; simpl in *; simpl; tcsp; repndors; subst; tcsp.

    - rewrite <- IHs in h; tcsp.
  Qed.

  Lemma view_change_somewhere_in_log_implies1 :
    forall vc s,
      PBFTview_change_somewhere_in_log.view_change_somewhere_in_log vc s
      -> PBFTreceived_prepare_like1.view_change_somewhere_in_log vc s.
  Proof.
    introv h; apply same_view_change_somewhere_in_log; auto.
  Qed.
  Hint Resolve view_change_somewhere_in_log_implies1 : pbft.

  Lemma view_change_somewhere_in_log_implies2 :
    forall vc s,
      PBFTreceived_prepare_like1.view_change_somewhere_in_log vc s
      -> PBFTview_change_somewhere_in_log.view_change_somewhere_in_log vc s.
  Proof.
    introv h; apply same_view_change_somewhere_in_log; auto.
  Qed.
  Hint Resolve view_change_somewhere_in_log_implies2 : pbft.

  (*Lemma in_check_broadcast_new_view_implies_in_view_change :
    forall pinfo nv i state entry entry' S OP NP,
      In pinfo (mergeP (new_view2cert nv))
      -> In entry S
      -> check_broadcast_new_view i state entry = Some (nv, entry', OP, NP)
      ->
      exists vc,
        view_change_somewhere_in_log vc S
        /\ In pinfo (view_change2prep vc).
  Proof.
    introv inv iS check.
    unfold check_broadcast_new_view in check; smash_pbft.

    rename_hyp_with create_new_prepare_messages cr.
    clear cr.

    apply in_view_change_cert2prep_implies in inv; exrepnd.
    exists vc; dands; auto; eauto 3 with pbft.
    eapply in_implies_view_change_somewhere_in_log; eauto.
  Qed.*)

  Lemma in_prep_implies_in_prepare2auth_data :
    forall prep L,
      In prep L
      -> In (prepare2auth_data prep) (prepares2auth_data L).
  Proof.
    induction L; introv H; simpl in *; ginv; simpl in *; smash_pbft; tcsp.

    repndors;[|].

    { destruct a, prep, b. simpl in *. ginv. tcsp. }

    { eapply IHL in H. dands; auto. }
  Qed.
  Hint Resolve in_prep_implies_in_prepare2auth_data : pbft.

  Lemma prepare_like_in_prepared_info_vc_implies_auth :
    forall p p_info vc,
      prepare_like_in_prepared_info p p_info
      -> In p_info (view_change2prep vc)
      -> In (prepare_like2main_auth_data p) (view_change2auth_data vc).
  Proof.
    introv plip pinfovc.

    destruct vc, v; simpl in *.
    unfold view_change2prep in *; simpl in *.
    allrw in_app_iff; right; right.
    unfold prepared_infos2auth_data.
    apply in_flat_map.
    eexists; dands; eauto.

    destruct p; simpl in *; tcsp; subst; simpl in *; tcsp;[].

    allrw in_app_iff.
    right; right.
    apply in_prep_implies_in_prepare2auth_data; auto.
  Qed.
  Hint Resolve prepare_like_in_prepared_info_vc_implies_auth : pbft.

  Lemma implies_prepare_like2auth_data_in_PBFTget_contained_auth_data_PBFTview_change :
    forall p p_info vc,
      prepare_like_in_prepared_info p p_info
      -> In p_info (view_change2prep vc)
      -> In (prepare_like2main_auth_data p) (PBFTget_contained_auth_data (PBFTview_change vc)).
  Proof.
    introv prep i.
    destruct vc, v; simpl in *.
    unfold view_change2prep in *; simpl in *.

    right.

    induction P; simpl in *; smash_pbft.

    repndors; subst; simpl in *; tcsp.

    - apply in_app_iff; simpl.
      destruct p; simpl in *; subst; tcsp.
      allrw in_app_iff.
      right; right; left.
      destruct p_info; simpl in *.

      clear IHP.

      rename prepared_info_prepares into L.
      induction L; simpl in *; tcsp.
      repndors; subst; tcsp.

    - autodimp IHP hyp.
      repeat (allrw in_app_iff; simpl in *; repndors; tcsp).
  Qed.
  Hint Resolve implies_prepare_like2auth_data_in_PBFTget_contained_auth_data_PBFTview_change : pbft.

  Lemma verify_new_view_implies_verify_prepare_like :
    forall pi pl nv keys i,
      In pi (mergeP (new_view2cert nv))
      -> prepare_like_in_prepared_info pl pi
      -> verify_new_view i keys nv = true
      -> verify_prepare_like i keys pl = true.
  Proof.
    introv j prep verif.
    destruct nv, v; simpl in *.
    unfold mergeP in *.
    unfold verify_new_view in *; simpl in *; smash_pbft.
    clear verif.

    repeat (rewrite verify_list_auth_data_app in verif0).
    smash_pbft.
    clear verif1 verif2.

    induction V; simpl in *; tcsp.
    repeat (rewrite verify_list_auth_data_app in verif0); smash_pbft.
    allrw in_app_iff; repndors; tcsp;[].
    clear IHV verif1.

    destruct a0, v0; simpl in *; smash_pbft.
    unfold view_change2prep in *; simpl in *.
    repeat (rewrite verify_list_auth_data_app in verif1); smash_pbft.
    clear verif0 verif1.

    induction P; simpl in *; tcsp; repndors; subst; tcsp; smash_pbft;
      repeat (rewrite verify_list_auth_data_app in verif0); smash_pbft;[].
    clear IHP verif1.

    destruct pl; simpl in *; subst; simpl in *; destruct pi; simpl in *; tcsp;
      try (complete (unfold verify_pre_prepare; simpl; smash_pbft)).
    clear verif2.
    induction prepared_info_prepares; simpl in *; tcsp; repndors;
      subst; tcsp; smash_pbft.
  Qed.
  Hint Resolve verify_new_view_implies_verify_prepare_like : pbft.

  Lemma implies_prepare_like2auth_data_in_new_view2auth_data :
    forall pi pl nv,
      In pi (mergeP (new_view2cert nv))
      -> prepare_like_in_prepared_info pl pi
      -> In (prepare_like2main_auth_data pl) (new_view2auth_data nv).
  Proof.
    introv i prep.
    destruct nv, v; simpl in *.
    unfold mergeP in *.
    allrw in_app_iff.

    right.
    left.

    induction V; simpl in *; tcsp;[].
    allrw in_app_iff; repndors; tcsp;[].
    clear IHV.

    destruct a0, v0; simpl in *; smash_pbft.
    unfold view_change2prep in *; simpl in *.
    allrw in_app_iff.
    left; right; right.

    induction P; simpl in *; tcsp; repndors; subst; tcsp; smash_pbft;
      allrw in_app_iff; tcsp;[].
    clear IHP.

    destruct pl; simpl in *; subst; simpl in *; destruct pi; simpl in *; tcsp;[].
    right; left.
    induction prepared_info_prepares; simpl in *; tcsp; repndors;
      subst; tcsp; smash_pbft.
  Qed.
  Hint Resolve implies_prepare_like2auth_data_in_new_view2auth_data : pbft.

  Lemma in_mergeP_implies :
    forall pi pl C,
      In pi (mergeP C)
      -> prepare_like_in_prepared_info pl pi
      ->
      exists vc,
        In vc C /\ In pi (view_change2prep vc).
  Proof.
    induction C; introv i prep; simpl in *; tcsp.
    allrw in_app_iff; repndors; tcsp.

    - exists a; tcsp.

    - repeat (autodimp IHC hyp); exrepnd.
      exists vc; tcsp.
  Qed.

(*  Lemma correct_prepare_like_messages_are_sent_before :
    forall (eo : EventOrdering) e p st i,
      prepare_like_in_log p (log st)
      -> state_sm_before_event (PBFTreplicaSM i) e = Some st
      ->
      (* either we received it *)
      (
        exists e' st',
          e' ⊑ e
          /\ state_sm_before_event (PBFTreplicaSM i) e' = Some st'
          /\ verify_prepare_like i (local_keys st') p = true
          /\ In (prepare_like2main_auth_data p) (get_contained_authenticated_data (trigger e'))
      )
      \/
      (* or we sent it *)
      prepare_like2sender p = i.
  Proof.
    introv prep eqst.
    rewrite state_sm_before_event_as_state_sm_on_event_pred in eqst; eauto 3 with pbft.
    eapply prepare_like_messages_are_received_or_generated in eqst;[eauto];
      autorewrite with eo; auto.
    apply eqst in prep. clear eqst.
    exrepnd.
    repndors;exrepnd;[|].
    {
      left.
      exists e' st1; dands; auto; eauto 2 with eo.
    }
    {
      right. auto.
    }
  Qed.*)

  Lemma correct_prepare_like_messages_are_sent_before :
    forall (eo : EventOrdering),
      PBFTcorrect_keys eo
      -> learns_or_knows_if_knew eo.
  Proof.
    introv cor.
    apply learns_or_knows_implies_learns_or_knows_if_new.
    apply pbft_learns_or_knows_prepare_like; auto.
  Qed.

  Lemma forallb_map :
    forall {A B} f (g : A -> B) (l : list A),
      forallb f (map g l) = forallb (compose f g) l.
  Proof.
    induction l; simpl in *; auto.
    unfold compose; f_equal; auto.
  Qed.

  Lemma correct_new_view_implies_correct_prepare_like :
    forall nv pi pl,
      correct_new_view nv = true
      -> In pi (mergeP (new_view2cert nv))
      -> prepare_like_in_prepared_info pl pi
      -> prepare_like2view pl = prepared_info2view pi
         /\ prepare_like2seq pl = prepared_info2seq pi
         /\ prepare_like2digest pl = prepared_info2digest pi.
  Proof.
    introv cor i prep.
    destruct nv, v; simpl in *.
    unfold correct_new_view in *; smash_pbft;[].
    unfold mergeP in *.

    rename_hyp_with correct_view_change cv.
    rename_hyp_with correct_new_view_opre_prepare_op co.
    rename_hyp_with correct_new_view_npre_prepare_op cn.
    rename_hyp_with view_change2sender nrep.
    rename_hyp_with length leV.
    clear co cn nrep cor leV.

    induction V; simpl in *; tcsp.
    smash_pbft.
    allrw in_app_iff; repndors; tcsp;[].
    clear IHV cv0.

    destruct a0, v0; simpl in *.
    unfold correct_view_change in *; simpl in *; smash_pbft.
    unfold view_change2prep in *; simpl in *.
    unfold view_change2view in *; simpl in *.

    rename_hyp_with correct_view_change_cert cc.
    clear cc.

    unfold correct_view_change_preps in *.

    rewrite forallb_forall in cv1.
    applydup cv1 in i; clear cv1; smash_pbft.

    rename_hyp_with prepared_info2view pv.
    rename_hyp_with check_between_water_marks bwm.
    clear pv bwm.

    unfold valid_prepared_info in *; smash_pbft.
    unfold info_is_prepared in *; smash_pbft.

    destruct pl, pi; simpl in *;
      unfold
        prepared_info2pp_sender,
      prepared_info2senders,
      prepared_info2view,
      prepared_info_has_correct_digest,
      prepared_info2request_data,
      prepared_info2seq,
      prepared_info2requests in *; simpl in *;
        subst; simpl in *; smash_pbft;[].

    allrw @forallb_map; unfold compose in *.
    allrw forallb_forall.

    applydup i3 in prep; clear i3.
    applydup i4 in prep; clear i4.
    smash_pbft.

    destruct p, b; simpl in *.
    destruct prepared_info_pre_prepare, b; simpl in *; ginv.
  Qed.

  Lemma well_formed_log_implies_prepare_somewhere_in_log_primary_false :
    forall v n d a L,
      well_formed_log L
      -> prepare_somewhere_in_log (mk_prepare v n d (PBFTprimary v) a) L = false.
  Proof.
    induction L; introv wf; simpl in *; tcsp.
    inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
    autodimp IHL hyp.
    smash_pbft; dands; auto.
    clear IHL wf2 imp.

    unfold prepare_in_entry; smash_pbft.

    destruct (ViewDeq v (entry2view a0)) as [d1|d1]; subst.

    - right.
      rewrite existsb_false.
      introv i.
      unfold same_rep_tok; smash_pbft.
      assert False; tcsp;[].

      pose proof (well_formed_log_entry_no_prepare_from_leader a0 wf1) as h.
      destruct h.
      apply in_map_iff; eexists; dands; eauto.
      simpl; tcsp.

    - left.
      unfold is_prepare_for_entry, eq_request_data; smash_pbft.
      destruct a0; simpl in *; subst; simpl in *; tcsp.
  Qed.

  Lemma verify_view_change_implies_pbft_pl_verify :
    forall pi pl vc i ks (eo : EventOrdering) (e : Event),
      In pi (view_change2prep vc)
      -> prepare_like_in_prepared_info pl pi
      -> verify_view_change i ks vc = true
      -> loc e = PBFTreplica i
      -> keys e = ks
      -> pbft_pl_verify eo e pl = true.
  Proof.
    introv j prep verify eqloc eqks.
    unfold pbft_pl_verify.
    allrw.
    apply verify_prepare_like_implies_verify_main_authenticated_data; eauto 3 with pbft.
  Qed.
  Hint Resolve verify_view_change_implies_pbft_pl_verify : pbft.

  Lemma prepares_like_of_new_views_are_received0 :
    forall (eo : EventOrdering) (e : Event) pl good,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> replica_has_correct_trace_before eo e good
      -> PBFTcorrect_keys eo
      -> knows1 e pl
      -> prepare_like2sender pl = good
      ->
      exists e',
        e' ≺ e
        /\ loc e' = PBFTreplica good
        /\ knows0 e' pl.
  Proof.
    introv sendbyz correct ckeys k sender.
    applydup knows_pl_nv_implies_knows_nv in k as knv; exrepnd.
    applydup new_views_learns_or_knows in knv0 as lok; auto.

    repndors; exrepnd;[|].

    - eapply learned_nv_implies_learned_pl in lok; eauto.
      pose proof (pbft_learns_if_knows_prepare_like eo) as q.
      repeat (autodimp q hyp);[].
      apply learns_if_knows_implies_learned_if_knows in q.
      apply q in lok; simpl in *.
      autodimp lok hyp; unfold pbft_pl_data2loc in *; rewrite sender in *; auto.

    - eapply in_mergeP_implies in knv2;[|eauto]; exrepnd;[].
      applydup knows_own_new_view in knv0 as own; auto;[].
      exrepnd.
      applydup localLe_implies_loc in own0.

      rename_hyp_with all_view_changes_of_new_view_in_log av.
      apply av in knv2.

      (* TODO: Instantiate the learn-and-know stuff for view-changes too *)
      eapply view_changes_are_received_or_created in knv2;[ |eauto 3 with pbft]; smash_pbft.
      exrepnd.

      applydup localLe_implies_loc in knv2.
      pose proof (ckeys e'0 (new_view2sender nv) st0) as ck2; repeat (autodimp ck2 hyp).

      assert (loc e'0 = PBFTreplica (new_view2sender nv))
        as eqloc by (unfold pbft_nv_data2loc in *; auto; congruence).

      repndors; repnd;[|].

      + rename_hyp_with PBFTview_change trig'.
        pose proof (pbft_learns_if_knows_prepare_like eo) as q.
        repeat (autodimp q hyp);[].
        pose proof (q pl e'0) as q; repeat (autodimp q hyp);
          simpl in *; try (unfold pbft_pl_data2loc in * );
            allrw; eauto 3 with pbft eo;
              try (complete (eexists; simpl; allrw; simpl; dands; eauto 3 with pbft)).
        exrepnd.
        eexists; dands; eauto 4 with eo; try congruence.

      + eapply knv4 in knv3 as pilog;[|eauto].
        assert (knew e'0 pl) as ke by (repeat eexists; simpl; eauto; try congruence).
        applydup knew_implies_knows in ke as ke'.
        apply correct_prepare_like_messages_are_sent_before in ke; auto;[].
        destruct ke as [ke|ke].

        * pose proof (pbft_learns_if_knows_prepare_like eo) as q; repeat (autodimp q hyp);[].
          apply learns_if_knows_implies_learned_if_knows in q.
          apply q in ke; clear q; repeat (autodimp ke hyp);
            try (complete (simpl; unfold pbft_pl_data2loc; allrw; eauto 4 with pbft eo)).
          exrepnd.
          simpl in *; unfold pbft_pl_data2loc in *; rewrite sender in *.
          exists e'1; dands; eauto 5 with eo; try congruence.

        * simpl in *; unfold pbft_pl_data2loc in *.
          rewrite sender in *.
          rewrite state_sm_before_event_as_state_sm_on_event_pred in knv5; eauto 3 with pbft.
          exists (local_pred e'0); dands; eauto 4 with eo; autorewrite with eo; try congruence.

          destruct (dec_isFirst e'0) as [d|d];
            [|pose proof (local_pred_is_direct_pred e'0) as q;
              autodimp q hyp; eauto 5 with eo];[].
          rewrite isFirst_implies_local_pred_eq; auto.
          assert (e'0 ≼ e) as xx by (eauto 4 with eo).

          destruct xx as [xx|xx]; subst; auto.
          assert False; tcsp.

          assert (e = e') as xx.
          {
            apply localHappenedBeforeLe_implies_or2 in own0.
            apply localHappenedBeforeLe_implies_or2 in knv2.
            repndors; try subst ; tcsp.
            {
              assert (e ⊏ e) as xx by eauto 3 with eo.
              apply localCausal_anti_reflexive in xx; tcsp.
            }
            {
              assert (e ⊏ e) as xx by eauto 3 with eo.
              apply localCausal_anti_reflexive in xx; tcsp.
              }
          }
          subst e'.

          pbft_simplifier.
          rewrite state_sm_before_event_unroll in own2.
          destruct (dec_isFirst e); tcsp;[]; ginv.
          simpl in *.

          unfold CheckBCastNewView2entry in *.
          destruct c; simpl in *.
          unfold initial_view_change_state in *; simpl in *.
          destruct i0; simpl in *; ginv.
  Qed.

  Lemma prepares_like_of_new_views_are_received :
    forall (eo : EventOrdering) (e : Event) nv i st pi pl good,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> replica_has_correct_trace_before eo e good
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> new_view_in_log nv (view_change_state st)
      -> In pi (mergeP (new_view2cert nv))
      -> prepare_like_in_prepared_info pl pi
      -> prepare_like2sender pl = good
      ->
      exists e' st',
        e' ≺ e
        /\ loc e' = PBFTreplica good
        /\ state_sm_on_event (PBFTreplicaSM good) e' = Some st'
        /\ prepare_like_in_log pl (log st').
  Proof.
    introv sendbyz correct ckeys eqloc eqst nvinlog ipi prep sender.
    pose proof (prepares_like_of_new_views_are_received0 eo e pl good) as q.
    repeat (autodimp q hyp); eauto 3 with eo pbft; try (complete (repeat eexists; simpl; eauto)).
    exrepnd.
    unfold knows0, knows in q0; exrepnd; simpl in *.
    rewrite q3 in *; inversion q2; subst n.
    repeat eexists; eauto.
  Qed.

End PBFTprepares_like_of_new_views_are_received.


Hint Resolve in_implies_view_change_somewhere_in_log : pbft.
Hint Resolve view_change_somewhere_in_log_implies1 : pbft.
Hint Resolve view_change_somewhere_in_log_implies2 : pbft.
Hint Resolve in_prep_implies_in_prepare2auth_data : pbft.
Hint Resolve prepare_like_in_prepared_info_vc_implies_auth : pbft.
Hint Resolve implies_prepare_like2auth_data_in_PBFTget_contained_auth_data_PBFTview_change : pbft.
Hint Resolve verify_new_view_implies_verify_prepare_like : pbft.
Hint Resolve implies_prepare_like2auth_data_in_new_view2auth_data : pbft.
Hint Resolve verify_view_change_implies_pbft_pl_verify : pbft.
