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


Require Export PBFT_A_1_9_part1.
Require Export PBFT_A_1_2_5.
Require Export PBFT_A_1_9_misc1.
Require Export PBFT_A_1_9_misc2.
Require Export PBFT_A_1_9_misc3.
Require Export PBFT_A_1_9_misc4.
Require Export PBFT_A_1_9_misc5.


Section PBFT_A_1_9.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context     : PBFTcontext      }.
  Context { pbft_auth        : PBFTauth         }.
  Context { pbft_keys        : PBFTinitial_keys }.
  Context { pbft_hash        : PBFThash         }.
  Context { pbft_hash_axioms : PBFThash_axioms  }.


  Lemma PBFT_A_1_9 : PBFT_A_1_9_Def.
  Proof.
    introv sendbyz ckeys moreThanF.
    intro e.

    induction e as [? IND] using HappenedBeforeInd;[].
    introv ctraces atmost eqloc eqst ltv prep.

    assert (forall e' : Event,
               (e') ≺ (e) ->
               forall (i : Rep) (st : PBFTstate),
                 PBFT_A_1_9_sub_Def eo v n d e' i st) as IND'.
    { introv lte; introv; apply IND; auto; eauto 3 with pbft eo. }

    clear IND; rename IND' into IND.
    hide_hyp IND.

    dup prep as hnv.
    eapply pre_prepare_in_log_implies_has_new_view in hnv;[|eauto];auto;[].
    simpl in hnv.
    apply has_new_view_implies_new_view_in_log in hnv; try omega;[|eauto 2 with pbft].
    exrepnd.
    subst.

    rename_hyp_with new_view_in_log nvinlog.

    applydup more_than_F_have_prepared_implies_exists_requests in moreThanF;
      auto; eauto 2 with pbft;[].
    exrepnd.
    rename moreThanF1 into digest_d_eq_requests.
    hide_hyp digest_d_eq_requests.

    dup prep as bwm.
    eapply pre_prepares_are_between_water_marks_if_in_log in bwm;[|eauto].
    simpl in *.
    apply check_between_water_marks_implies_lt in bwm.

    assert (correct_new_view nv = true) as cornv by (eauto 3 with pbft).

    applydup correct_new_view_implies_large_enough_certificate in cornv; repnd.

    unfold exists_more_than_F_that_have_prepared in moreThanF; exrepnd.

    pose proof (two_quorums_one (map view_change2sender (new_view2cert nv)) R) as w.
    repeat (autodimp w hyp); autorewrite with list; auto; try omega; eauto 2 with pbft;[].
    destruct w as [good [incert inR]].

    applydup in_view_change2sender_implies_exists_vc in incert.
    destruct incert0 as [vc [innvcert vcsender]].

    pose proof (dec_exists_pre_prepare_with_higher_view vc v n d) as dec.
    destruct dec as [dec|dec].

    {
      (* either we have a matching pre-prepare in the good view-change *)

      destruct dec as [v' [rs' [a' [invc [levs eqrs]]]]].

      show_hyp digest_d_eq_requests.
      rewrite digest_d_eq_requests in eqrs.
      hide_hyp digest_d_eq_requests.
      apply eq_digests_implies_eq_requests in eqrs; subst.

      applydup correct_new_view_implies_all_sequence_numbers_are_accounted_for_op in cornv as acc.

      unfold all_sequence_numbers_are_accounted_for_op in acc; smash_pbft;[].
      rename x into maxV.

      unfold pre_prepares_of_view_change in invc.
      apply in_map_iff in invc.
      destruct invc as [pi [eqpi invc]].

      assert (info_is_prepared pi = true) as preppi.
      {
        eapply p_info_in_cert_of_nv_implies_p_info_is_prepared;
          [|eauto|eauto|];auto; eauto 3 with pbft.
      }

      dup acc as accpi.
      eapply all_sequence_numbers_are_accounted_for_implies1 in accpi;[| |eauto];auto.
      unfold sequence_number_is_accounted_for in accpi.
      smash_pbft;[| |].

      - (* should be straightforward *)

        (* XXXXXX GOING BACK TO THE O SET XXXXXX *)

        assert ((exists a, In (mk_pre_prepare (new_view2view nv) n rs' a) (new_view2oprep nv))
                -> d = d') as part1;[introv ex_pp|apply part1;clear part1].
        {
          exrepnd.
          dup nvinlog as nvinlog'.

          eapply new_views_are_received3 in nvinlog;
            [|eauto| |eauto]; simpl; auto.

          remember (is_primary (new_view2view nv) i) as b; symmetry in Heqb; destruct b.

          { eapply PBFT_A_1_2_2 in prep;[| |eauto|exact nvinlog]; simpl in *; auto;[].
            unfold pre_prepare2digest in prep; simpl in prep;try congruence. }

          eapply PBFT_A_1_2_8 in prep;[| |eauto]; simpl; auto.
          eapply PBFT_A_1_2_8 in nvinlog;[| |eauto]; simpl; auto.
          apply prepare_of_pre_in_log_implies_prepare_in_log in prep.
          apply prepare_of_pre_in_log_implies_prepare_in_log in nvinlog.
          exrepnd.
          eapply PBFT_A_1_2_1 in nvinlog0;try (exact prep0); eauto.
          subst; auto.
        }

        (* XXXXXX *)

        clear prep.

        unfold exists_prepared_info_in_pre_prepares in *.
        allrw existsb_exists.

        destruct accpi as [ppx [ppx_in_nv q]].
        allrw andb_true.
        destruct q as [eqd_pi_ppx eqseq_pi_ppx].

        unfold same_seq_nums in *; smash_pbft;[].

        assert (low_water_mark st < pre_prepare2seq ppx) as lwmppx.
        {
          apply prepared_info_pre_prepare_mk_pre_prepare_seq in eqpi.
          subst; congruence.
        }

        exists (pre_prepare2auth ppx).

        dup eqpi as n_eq.
        apply prepared_info_pre_prepare_mk_pre_prepare_seq in n_eq.
        rewrite n_eq in *.

        dup eqpi as v_eq.
        apply prepared_info_pre_prepare_mk_pre_prepare_view in v_eq.
        rewrite v_eq in *.

        dup eqpi as rs_eq.
        apply prepared_info_pre_prepare_mk_pre_prepare_req in rs_eq.
        rewrite rs_eq in *.

        unfold same_digests in eqd_pi_ppx. smash_pbft.
        unfold same_seq_nums in *. smash_pbft.
        unfold mk_pre_prepare in *. simpl in *.

        dup cornv as j.
        eapply pre_prepare_in_map_correct_new_view_implies2 in j;
          [|apply in_map_iff; unfold add_digest; exists ppx; dands; try reflexivity;
            apply in_app_iff;left; auto].
        simpl in j.

        allrw; tcsp.

        destruct ppx, b; simpl in *; auto.
        unfold pre_prepare2digest in e1; simpl in e1.

        assert (d0 = prepared_info2requests pi) as xx;[|subst; auto];[].

        dup cornv as corvc.
        eapply PBFTgarbage_collect_misc1.correct_new_view_implies_correct_view_change in corvc;[|eauto].
        apply correct_view_change_implies_correct_view_change_preps in corvc.

        unfold correct_view_change_preps in corvc.
        rewrite forallb_forall in corvc.
        applydup corvc in invc as valid; clear corvc; smash_pbft.
        unfold valid_prepared_info in valid; smash_pbft.
        apply info_is_prepared_implies_prepared_info_has_correct_digest in valid.
        unfold prepared_info_has_correct_digest in valid; smash_pbft.

        assert (requests2digest d0 = requests2digest (prepared_info2requests pi)) as xx by congruence.
        apply eq_digests_implies_eq_requests in xx; auto.

      - (* should be impossible *)

        assert (n = prepared_info2seq pi) as xx by eauto 2 with pbft; subst.
        assert (low_water_mark st < maxV) as ltmaxV by omega.

        assert (maxV <= low_water_mark st) as xx;[|omega].
        eapply low_water_mark_increases_with_new_views; eauto.

      - (* should follow from IH *)

        rename_hyp_with valid_prepared_info valid.
        applydup valid_prepared_info_false_implies2 in valid;auto;[].
        destruct valid0 as [nfo validnfo]; repnd.
        repndors; repnd;[|].

        + (* should follow from A.1.5 *)

          pose proof (PBFT_A_1_5 eo e) as a15; repeat (autodimp a15 hyp);
            try (complete (allrw; auto));[].
          pose proof (a15 nv pi nfo i st) as a15.
          repeat (autodimp a15 hyp); tcsp; eauto 3 with pbft.

        + (* should follow from IH *)

          dup validnfo0 as nfoinnv.
          eapply all_sequence_numbers_are_accounted_for_implies2 in nfoinnv;[|eauto].
          unfold sequence_number_is_accounted_for in nfoinnv; smash_pbft;[| |].

          * (* should follow form IH *)

            assert (d = prepared_info2digest nfo) as eqd.
            {
              pose proof (there_is_one_good_guy_before eo (prepared_info2all_senders nfo) [e]) as nfogood.
              repeat (autodimp nfogood hyp); eauto 2 with pbft;[].
              destruct nfogood as [G' nfogood]; repnd.

              applydup in_prepared_info2all_senders_implies_exits_prepare_like in nfogood0.
              exrepnd.

              pose proof (nfogood e) as ge; simpl in ge; autodimp ge hyp; tcsp;[].

              pose proof (prepares_like_of_new_views_are_received
                            eo e nv i st nfo pl G') as q.
              repeat (autodimp q hyp);
                try (complete (introv w z; eapply nfogood; eauto; simpl; tcsp));
                try (complete (allrw; auto));[].
              exrepnd.

              eapply own_prepare_like_message_in_log_implies_pre_prepare_in_log in q1;
                [| |eauto]; auto;[].
              exrepnd.

              pose proof (IND
                            e' q0 G' st'
                            (pre_prepare2view pp)
                            (pre_prepare2requests pp)
                            (pre_prepare2auth pp)
                            (prepared_info2digest nfo)) as h.
              repeat (autodimp h hyp);
                try (complete (allrw; eauto 3 with pbft eo)).

              {
                assert (v' = prepared_info2view pi) as eqvs1 by eauto 2 with pbft.
                subst v'.
                apply prepare_like2request_data_pre_prepare2request_data_implies_eq_views in q1.
                rewrite <- q1.
                assert (v < prepared_info2view nfo) as ltv1 by omega.
                assert (prepare_like2view pl = prepared_info2view nfo) as eqvs;[|rewrite eqvs;auto];[].

                applydup in_view_change_cert2prep_implies in validnfo0 as ivc'.
                exrepnd.
                dup cornv as corvc.
                eapply PBFTgarbage_collect_misc1.correct_new_view_implies_correct_view_change in corvc;[|exact ivc'1];[].
                apply correct_view_change_implies_correct_view_change_preps in corvc.

                unfold correct_view_change_preps in corvc.
                rewrite forallb_forall in corvc.
                applydup corvc in ivc'0 as valid'; clear corvc; smash_pbft.
              }

              match goal with
              | [ H : pre_prepare_in_log ?pp1 ?d1 ?l = true
                  |-  pre_prepare_in_log ?pp2 ?d2 ?l = true] =>
                assert (pp1 = pp2 /\ d1 = d2) as xx;[|repnd;rewrite <- xx0, <- xx;auto];[]
              end.

              dands.

              {
                assert (n = pre_prepare2seq pp) as xx;
                  [|subst; destruct pp, b; simpl; auto];[].
                assert (n = prepared_info2seq pi) as xx by eauto 2 with pbft.
                assert (n = prepared_info2seq nfo) as yy by congruence.
                apply prepare_like2request_data_pre_prepare2request_data_implies_eq_seqs in q1; rewrite <- q1; clear q1.
                symmetry; rewrite yy; eauto 2 with pbft.
              }

              apply prepare_like2request_data_pre_prepare2request_data_implies_eq_digests in q1.
              rewrite <- q1; clear q1.
              eauto 3 with pbft.
            }

            assert ((exists a, In (mk_pre_prepare (new_view2view nv) n rs' a) (new_view2oprep nv))
                    -> d = d') as part1;[introv ex_pp|apply part1;clear part1].
            {
              exrepnd.
              dup nvinlog as nvinlog'.

              eapply new_views_are_received3 in nvinlog;
                [|eauto| |eauto]; simpl; auto.

              remember (is_primary (new_view2view nv) i) as b; symmetry in Heqb; destruct b.

              { eapply PBFT_A_1_2_2 in prep;[| |eauto|exact nvinlog]; simpl in *; auto;[].
                unfold pre_prepare2digest in prep; simpl in prep;try congruence. }

              eapply PBFT_A_1_2_8 in prep;[| |eauto]; simpl; auto.
              eapply PBFT_A_1_2_8 in nvinlog;[| |eauto]; simpl; auto.
              apply prepare_of_pre_in_log_implies_prepare_in_log in prep.
              apply prepare_of_pre_in_log_implies_prepare_in_log in nvinlog.
              exrepnd.
              eapply PBFT_A_1_2_1 in nvinlog0;try (exact prep0); eauto.
              subst; auto.
            }

            unfold exists_prepared_info_in_pre_prepares in nfoinnv.
            allrw existsb_exists.

            destruct nfoinnv as [ppx [ppx_in_nv q]].
            allrw andb_true.
            destruct q as [eqd_pi_ppx eqseq_pi_ppx].

            unfold same_seq_nums in *; smash_pbft;[].

            assert (low_water_mark st < pre_prepare2seq ppx) as lwmppx.
            {
              apply prepared_info_pre_prepare_mk_pre_prepare_seq in eqpi.
              subst; congruence.
            }

            exists (pre_prepare2auth ppx).

            dup eqpi as n_eq.
            apply prepared_info_pre_prepare_mk_pre_prepare_seq in n_eq.
            rewrite n_eq in *.

            dup eqpi as v_eq.
            apply prepared_info_pre_prepare_mk_pre_prepare_view in v_eq.
            rewrite v_eq in *.

            dup eqpi as rs_eq.
            apply prepared_info_pre_prepare_mk_pre_prepare_req in rs_eq.
            rewrite rs_eq in *.

            unfold same_digests in eqd_pi_ppx; smash_pbft;[].
            unfold same_seq_nums in *; smash_pbft;[].
            unfold mk_pre_prepare in *; simpl in *.

            dup cornv as j.
            eapply pre_prepare_in_map_correct_new_view_implies2 in j;
              [|apply in_map_iff; unfold add_digest; exists ppx; dands; try reflexivity;
                apply in_app_iff;left; auto].
            simpl in j.

            allrw; tcsp.

            destruct ppx, b; simpl in *; auto.
            unfold pre_prepare2digest in e1; simpl in e1.

            assert (d = prepared_info2requests pi) as xx;[|subst; auto];[].

            dup cornv as corvc.

            applydup in_view_change_cert2prep_implies in validnfo0 as ivc'.
            exrepnd.
            dup cornv as corvc'.
            eapply PBFTgarbage_collect_misc1.correct_new_view_implies_correct_view_change in corvc';[|exact ivc'1];[].
            apply correct_view_change_implies_correct_view_change_preps in corvc'.

            unfold correct_view_change_preps in corvc'.
            rewrite forallb_forall in corvc'.
            applydup corvc' in ivc'0 as valid'; clear corvc'; smash_pbft;[].
            unfold valid_prepared_info in valid'; smash_pbft;[].
            apply info_is_prepared_implies_prepared_info_has_correct_digest in valid'.
            unfold prepared_info_has_correct_digest in valid'; smash_pbft.

            assert (requests2digest d = requests2digest (prepared_info2requests pi)) as xx by congruence.
            apply eq_digests_implies_eq_requests in xx; auto.

          * (* should be impossible *)

            assert (n = prepared_info2seq pi) as xx by eauto 2 with pbft; subst.
            rewrite validnfo2 in *.
            assert (low_water_mark st < maxV) as ltmaxV by omega.

            assert (maxV <= low_water_mark st) as xx;[|omega].
            eapply low_water_mark_increases_with_new_views; eauto.

          * (* should be impossible because nfo is the valid already *)

            match goal with
            | [ H : valid_prepared_info _ nfo = false |- _ ] => rename H into validF
            end.
            rewrite prepared_info_with_highest_view_implies_valid in validF; auto; ginv;[].

            introv jx prepx seqx viewx.

            pose proof (PBFT_A_1_5 eo e) as a15; repeat (autodimp a15 hyp); try (complete (allrw; eauto 3 with pbft eo)).
    }

    {
      (* or we don't have a matching pre-prepare in the good view-change *)

      applydup PBFTgarbage_collect_misc1.correct_new_view_implies_correct_view_change in innvcert as corvc;auto;[].
      applydup correct_view_change_implies_same_views in corvc.
      rewrite corvc0 in *.

      pose proof (view_change_of_new_view_received_from_good_replica_was_logged
                    eo e good vc nv i st) as vcinlog.
      repeat (autodimp vcinlog hyp);
        try (complete (introv lee eqgood; eapply ctraces; eauto; simpl; tcsp; allrw in_map_iff; eexists; dands; eauto));
        try (complete (allrw; auto));[].

      exrepnd.

      applydup moreThanF in inR as prepGood; exrepnd.

      remember (view_change_cert2max_seq (new_view2cert nv)) as m.
      symmetry in Heqm.

      (* we need to get that the sequence number of the view-change is less than [n] *)
      assert (view_change2seq vc < n) as vcltn.
      {
        applydup correct_new_view_implies_view_change_cert2max_seq_vc_some in cornv as maxvc.
        exrepnd.

        dup eqst as lwm.
        eapply low_water_mark_increases_with_new_views in lwm;
          [|eauto|unfold view_change_cert2max_seq;rewrite maxvc0;eauto];auto;[].
        eapply in_view_change_cert2max_seq_vc_implies_view_change2seq_le in maxvc0; eauto.
        omega.
      }

      (* WARNING *)
      clear dependent nv.
      clear dependent st.

      (* WARNING *)
      destruct dec.

      assert (view_change2view vc = v0) as eqv0 by (subst vc; simpl in *; tcsp).
      rewrite eqv0 in *; clear eqv0.

      remember (prepared (request_data v n d) st1) as b; symmetry in Heqb; destruct b.

      {
        (* the request-data <v,n,d> was prepared just before e' *)

        dup Heqb as gather.

        unfold prepared in gather.
        eapply prepared_implies in gather; simpl;[| |eauto];eauto 2 with pbft; exrepnd;[].
        subst vc; simpl in *.
        unfold pre_prepares_of_view_change, mk_current_view_change, view_change2prep; simpl.
        unfold gather_valid_prepared_messages; simpl.

        remember (valid_prepared_info (gather_prepared_messages (log st1) (low_water_mark st1)) pi) as w.
        symmetry in Heqw; destruct w;[|].

        - (* the prepared-info is the valid *)

          exists (pre_prepare2view (prepared_info_pre_prepare pi))
                 (pre_prepare2requests (prepared_info_pre_prepare pi))
                 (pre_prepare2auth (prepared_info_pre_prepare pi)).
          simpl in *; autorewrite with pbft in *; GC.
          rewrite requests2digest_pre_prepare2requests_prepared_info_pre_prepare;auto.
          erewrite prepared_info2request_data_eq_request_data_implies_prepared_info2view;[|eauto];[].
          erewrite prepared_info2request_data_eq_request_data_implies_prepared_info2digest;[|eauto];[].
          dands; auto;[].

          apply in_map_iff.
          exists pi.
          dands.

          { destruct pi, prepared_info_pre_prepare, b; simpl in *.
            unfold prepared_info2request_data in *; simpl in *; ginv. }

          apply filter_In; dands; auto.

        - (* the prepared-info is not valid *)

          applydup valid_prepared_info_false_implies2 in Heqw as HIGHprep; auto;[].
          exrepnd.
          repndors; repnd;[|].

          {
            (* either we have another prepared with same view but different digest *)

            pose proof (PBFT_A_1_4_same_loc_before eo) as a14; repeat (autodimp a14 hyp).
            pose proof (a14
                          e' good
                          (prepared_info2seq pi)
                          (prepared_info2view pi)
                          (prepared_info2digest pi)
                          (prepared_info2digest nfo)
                          st1) as a14.
            repeat (autodimp a14 hyp); tcsp; eauto 2 with pbft eo;[|].

            - applydup prepared_info2request_data_eq_request_data_implies_prepared_info2digest in gather0 as hd.
              applydup prepared_info2request_data_eq_request_data_implies_prepared_info2view in gather0 as hv.
              applydup prepared_info2request_data_eq_request_data_implies_prepared_info2seq in gather0 as hs.

              rewrite hd, hs, hv; auto.

            - rewrite HIGHprep3, HIGHprep4.
              eapply in_gather_prepared_messages_implies_prepared; eauto.
              eauto 3 with pbft.
          }

          {
            (* or we have another prepared with a higher view *)

            assert (prepared_info2digest nfo = d) as xx.
            {
              (* By induction *)

              (* We have to get back to when nfo was sent *)

              applydup in_gather_prepared_messages_implies in HIGHprep1 as inlog; exrepnd.
              applydup entry2prepared_info_some_implies_entry2pre_prepare_some in inlog0.
              exrepnd.

              assert (pre_prepare_in_log pp (pre_prepare2digest pp) (log st1) = true) as ppinlog.
              { eapply in_entry_implies_pre_prepare_in_log; eauto; eauto 2 with pbft. }

              dup vcinlog3 as inpred.
              eapply pre_prepare_in_log_before_implies_in_on in inpred;[|eauto].
              exrepnd.

              applydup eo_direct_pred_local in inpred1.

              pose proof (IND e'1) as q; autodimp q hyp; eauto 3 with eo;[].
              pose proof (q good st1
                            (pre_prepare2view pp)
                            (pre_prepare2requests pp)
                            (pre_prepare2auth pp)
                            (prepared_info2digest nfo)) as q.
              repeat (autodimp q hyp); try congruence;[|].

              {
                applydup prepared_info2request_data_eq_request_data_implies_prepared_info2view in gather0 as hv.
                rewrite hv in *; clear hv.
                assert (pre_prepare2view pp = prepared_info2view nfo) as xx;[|rewrite xx;auto];[].
                applydup entry2prepared_info_some_implies_equal_views in inlog0 as eqv.
                rewrite <- eqv; clear eqv.
                symmetry; eauto 3 with pbft.
              }

              match goal with
              | [ H : pre_prepare_in_log ?pp1 ?d1 ?l = true
                  |-  pre_prepare_in_log ?pp2 ?d2 ?l = true] =>
                assert (pp1 = pp2 /\ d1 = d2) as xx;[|repnd;rewrite <- xx0, <- xx;auto];[]
              end.

              dands;[|].

              {
                assert (n = pre_prepare2seq pp) as xx;
                  [|subst; destruct pp, b; simpl; auto];[].
                applydup entry2pre_prepare_some_implies_equal_seqs in inlog4 as eqs.
                rewrite <- eqs; clear eqs.
                applydup prepared_info2request_data_eq_request_data_implies_prepared_info2seq in gather0 as hs.
                rewrite <- hs; clear hs.
                rewrite HIGHprep3; symmetry.
                applydup entry2prepared_info_some_implies_equal_seqs in inlog0 as eqs; auto.
              }

              {
                applydup entry2pre_prepare_some_implies_equal_digests in inlog4 as eqd;[|eauto 3 with pbft];[].
                rewrite <- eqd; clear eqd.
                apply entry2prepared_info_some_implies_equal_digests; auto.
              }
            }

            exists (pre_prepare2view (prepared_info_pre_prepare nfo))
                   (pre_prepare2requests (prepared_info_pre_prepare nfo))
                   (pre_prepare2auth (prepared_info_pre_prepare nfo)).
            simpl in *; autorewrite with pbft in *; GC.
            rewrite requests2digest_pre_prepare2requests_prepared_info_pre_prepare;auto.
            applydup prepared_info2request_data_eq_request_data_implies_prepared_info2view in gather0 as eqv.
            rewrite eqv in *.
            dands; auto; try omega;[].

            apply in_map_iff.
            exists nfo.
            dands.

            { destruct nfo, prepared_info_pre_prepare, b; simpl in *.
              destruct pi, prepared_info_pre_prepare, b; simpl in *.
              unfold prepared_info2view in *; simpl in *.
              unfold prepared_info2seq in *; simpl in *; subst.
              unfold prepared_info2request_data in *; simpl in *; ginv. }

            apply filter_In; dands; auto; eauto 3 with pbft.
            apply prepared_info_with_highest_view_implies_valid; auto;
              try (complete (allrw <-; auto)).

            introv ix prepx seqx viewx.

            pose proof (PBFT_A_1_4_same_loc_before eo) as a14; repeat (autodimp a14 hyp).
            pose proof (a14
                          e' good
                          (prepared_info2seq nfo)
                          (prepared_info2view nfo)
                          (prepared_info2digest nfo)
                          (prepared_info2digest x)
                          st1) as a14.
            repeat (autodimp a14 hyp); tcsp; eauto 2 with pbft eo;[|].

            - eapply in_gather_prepared_messages_implies_prepared; eauto.
              eauto 3 with pbft.

            - rewrite <- seqx, <- viewx.
              eapply in_gather_prepared_messages_implies_prepared; eauto.
              eauto 3 with pbft.
          }
      }

      {
        (* the request-data <v,n,d> wasn't prepared just before e' *)

        dup prepGood1 as prepVS.
        unfold prepared in prepVS.
        eapply prepared_log_from_matching_view_and_seq in prepVS;[|eauto];auto;[].
        exrepnd; simpl in *.
        applydup localLe_implies_loc in prepVS0.

        assert (loc e'1 = loc e') as eqlocs by congruence.
        applydup tri_if_same_loc in eqlocs.

        repndors;
          [|subst e'1 vc; rewrite prepVS2 in *; pbft_simplifier; omega
           |eapply PBFTcurrent_view_increases_on_event in prepVS2;
            try (exact vcinlog4); eauto 2 with eo;subst v;omega];[].

        assert (low_water_mark st1 < n) as lwm1 by (subst vc; simpl in *; tcsp).
        rewrite state_sm_before_event_as_state_sm_on_event_pred in vcinlog3;[|eauto 3 with eo];[].
        apply localHappenedBefore_implies_le_local_pred in eqlocs0.
        apply localHappenedBeforeLe_implies_or2 in eqlocs0;
          repndors;
          [subst e'1 vc; rewrite prepVS2 in *; smash_pbft;
           unfold prepared in *; rewrite Heqb in *; ginv|];[].

        eapply prepared_get_garbage_collected in prepVS3;
          try (exact Heqb); eauto;[]; simpl in *; try omega.
      }
    }
  Qed.

End PBFT_A_1_9.
