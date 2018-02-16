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


Require Export PBFTview_changes_from_good1.
Require Export PBFTview_changes_from_good2.
Require Export PBFTview_changes_from_good3.
Require Export PBFTview_changes_from_good4.
Require Export PBFTview_changes_from_good5.
Require Export PBFTview_changes_from_good6.
Require Export PBFTview_changes_from_good7.

Require Export PBFTnew_view_learns_or_knows.
Require Export PBFTknows_own_new_view.


Section PBFTview_changes_from_good.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma view_change_of_new_view_received_from_good_replica_was_logged :
    forall (eo : EventOrdering) (e : Event) good vc nv i st,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> node_has_correct_trace_before e good
      -> view_change2sender vc = good
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> new_view_in_log nv (view_change_state st)
      -> In vc (new_view2cert nv)
      ->
      exists e' st1 st2 v,
        e' ≼ e
        /\ loc e' = PBFTreplica good
        /\ state_sm_before_event (PBFTreplicaSM good) e' = Some st1
        /\ state_sm_on_event (PBFTreplicaSM good) e' = Some st2
        /\ own_view_change_in_log vc (view_change_state st2)
        /\ vc = mk_current_view_change good v st1
        /\ current_view st1 <= v <= current_view st2.
  Proof.
    intros eo e.
    induction e as [? ind] using HappenedBeforeInd;[].
    introv sendbyz ckeys eqloc ctrace vcgood eqst nvinlog icert.

    assert (knows2 e nv) as kn by (eexists; eexists; simpl; dands; eauto).

    pose proof (new_views_learns_or_knows eo) as lok; autodimp lok hyp.
    applydup lok in kn.
    repeat (autodimp kn0 hyp); eauto 3 with pbft eo;[].

    (* either the new-view was received or it was sent *)
    repndors; exrepnd;[|].

    - (* the new-view was received *)

      unfold learned, learns in kn0; exrepnd; simpl in *.
      eapply pbft_nv_verify_verify_new_view in kn2;[|eauto|reflexivity].
      dup kn2 as verifvc.
      eapply verify_new_view_implies_verify_view_change_in_cert in verifvc;[|eauto].
      pose proof (in_bind_op_list_implies_auth_data_in_trigger (pbft_nv_data2main_auth_data nv) e') as q.
      simpl in q; apply q in kn3; clear q.
      applydup pbft_nv_data2main_auth_data_in_trigger_implies in kn3.

      assert (node_has_correct_trace_before e' good) as cor' by eauto 3 with pbft eo.

      assert (auth_data_in_trigger (view_change2main_auth_data vc) e')
        as iauth by (unfold auth_data_in_trigger; allrw; simpl; eauto 2 with pbft).

      pose proof (state_sm_before_event_some_between3 e' e (PBFTreplicaSM i) st) as ns.
      repeat (autodimp ns hyp).
      exrepnd.

      pose proof (ckeys e' i s') as eqkeys1; autodimp eqkeys1 hyp; eauto 3 with eo pbft;
        try (complete (rewrite eqloc in *; eauto 3 with pbft eo));[].
      applydup localLe_implies_loc in kn0.

      assert (PBFTreplica n = PBFTreplica i) as eqreps by (allrw <- ; auto).
      inversion eqreps; subst n; clear eqreps.

      applydup implies_authenticated_messages_were_sent_non_byz in sendbyz.
      apply (sendbyz0 _ _ (PBFTreplica good)) in iauth; simpl in *; eauto 3 with pbft;
        try (complete (allrw; subst; simpl; eauto 2 with eo pbft));
        try (complete (subst; destruct vc, v; simpl; tcsp));
        try (complete (subst; allrw; rewrite <- eqkeys1; eauto 3 with pbft));
        try (complete (rewrite kn1; eauto 3 with pbft));[].
      exrepnd.

      pose proof (PBFTnever_stops eo e'0 (view_change2sender vc)) as w.
      repeat (autodimp w hyp); eauto 3 with pbft eo;[].
      pose proof (PBFTnever_stops_on_event eo e'0 (view_change2sender vc)) as z.
      repeat (autodimp z hyp); eauto 3 with pbft eo;[].
      exrepnd.

      applydup view_change2main_auth_data_in_get_contained_auth_data_implies in iauth3.

      (* either the good guy sent the view-change directly
         or he sent a new-view containing the view-change *)
      repndors;[|].

      + (* the good guy sent the view-change *)

        subst; simpl in *.
        autodimp iauth4 hyp;[].

        apply send_view_change_no_delay in iauth4.
        eapply sent_view_change_is_in_log2 in iauth4;[| |eauto|eauto];auto;[].
        repnd.

        exists e'0; eexists; eexists; exists (current_view st0); dands; eauto 4 with pbft eo.

      + (* the good guy sent a new-view containing the view-change *)

        exrepnd; subst; simpl in *.
        autodimp iauth4 hyp;[].

        apply send_new_view_no_delay in iauth4.
        eapply sent_new_views_are_in_log in iauth4;[| |eauto]; auto;[].
        pose proof (ind e'0) as q; clear ind; autodimp q hyp; eauto 3 with eo;[].
        pose proof (q (view_change2sender vc) vc nv0 (view_change2sender vc) st0) as q.
        repeat (autodimp q hyp);
          try (complete (introv z1 z2; apply ctrace; eauto 5 with eo));
          try (complete (allrw; eauto 3 with pbft eo));[].
        exrepnd.
        exists e'1 st2 st3 v; dands; auto; eauto 5 with eo.

    - (* the new-view was sent *)

      applydup knows_own_new_view in kn; auto;[].
      exrepnd.

      applydup localLe_implies_loc in kn2 as eqloc0.
      unfold lak_data2node in *; simpl in *.
      unfold pbft_nv_data2loc in *; simpl in *.

      rewrite <- kn0 in eqloc; symmetry in eqloc; inversion eqloc; subst i; clear eqloc.
      symmetry in kn0.

      applydup kn1 in icert.
      dup icert0 as vcinlog.
      eapply view_changes_are_received_or_created2 in vcinlog; [allrw; auto |eauto]; auto; try congruence;[].
      exrepnd.
      applydup localLe_implies_loc in vcinlog1 as eqlocs2.

      repndors;repnd;[|].

      + assert (auth_data_in_trigger (view_change2main_auth_data vc) e'0)
          as iauth by (unfold auth_data_in_trigger; allrw; simpl; eauto 2 with pbft).

        pose proof (ckeys e'0 (new_view2sender nv) st0) as eqkeys1; autodimp eqkeys1 hyp;
          try (complete (rewrite kn0 in *; eauto 3 with pbft eo)); [].

        applydup implies_authenticated_messages_were_sent_non_byz in sendbyz.
        apply (sendbyz0 _ _ (PBFTreplica good)) in iauth; simpl in *; eauto 3 with pbft;
          try (complete (allrw; subst; simpl; eauto 3 with eo pbft));
          try (complete (subst; destruct vc, v; simpl; tcsp));
          try (complete (subst; allrw; rewrite <- eqkeys1; eauto 3 with pbft));[].
        exrepnd.

        pose proof (PBFTnever_stops eo e'1 (view_change2sender vc)) as w.
        repeat (autodimp w hyp); try (complete (apply ctrace; eauto 5 with eo));[].
        pose proof (PBFTnever_stops_on_event eo e'1 (view_change2sender vc)) as z.
        repeat (autodimp z hyp); try (complete (apply ctrace; eauto 5 with eo));[].
        exrepnd.

        applydup view_change2main_auth_data_in_get_contained_auth_data_implies in iauth3.

        (* either the good guy sent the view-change directly
           or he sent a new-view containing the view-change *)
        repndors;[|].

        * (* the good guy sent the view-change *)

          subst; simpl in *.
          autodimp iauth4 hyp;[].

          apply send_view_change_no_delay in iauth4.
          eapply sent_view_change_is_in_log2 in iauth4;[| |eauto|eauto];auto;[].
          repnd.

          exists e'1; eexists; eexists; exists (current_view st4); dands; eauto 5 with pbft eo.

        * (* the good guy sent a new-view containing the view-change *)

          exrepnd; subst; simpl in *.
          autodimp iauth4 hyp;[].

          apply send_new_view_no_delay in iauth4.
          eapply sent_new_views_are_in_log in iauth4;[| |eauto]; auto;[].
          pose proof (ind e'1) as q; clear ind; autodimp q hyp; eauto 4 with eo;[].
          pose proof (q (view_change2sender vc) vc nv0 (view_change2sender vc) st4) as q.
          repeat (autodimp q hyp);
            try (complete (rewrite iauth1; eauto 5 with eo));
            try (complete (introv z1 z2; apply ctrace; eauto 6 with eo));[].
          exrepnd.
          exists e'2 st6 st7 v; dands; auto; eauto 6 with eo.

      + exrepnd.
        subst; simpl in *; autorewrite with pbft in *.
        exists e'0 st0 st3 v.
        dands; auto; eauto 3 with eo; try congruence.
  Qed.

End PBFTview_changes_from_good.
