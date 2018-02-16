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


Require Export PBFTprepares_like_of_new_views_are_received.


Section PBFT_A_1_5.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma prepared_info2request_data_equal_prepare_like2request_data_implies :
    forall pi pl,
      prepared_info2request_data pi = prepare_like2request_data pl
      -> prepared_info2seq pi = prepare_like2seq pl
         /\ prepared_info2view pi = prepare_like2view pl
         /\ prepared_info2digest pi = prepare_like2digest pl.
  Proof.
    introv e.
    destruct pi, pl as [p|p], p, b, prepared_info_pre_prepare, b; simpl in *;
      unfold prepared_info2request_data in *; simpl in *; ginv; tcsp.
  Qed.

  (* Invariant A.1.5 in PBFT PhD p.148 *)
  Lemma PBFT_A_1_5 :
    forall (eo : EventOrdering) (e : Event),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      ->
      forall (nv      : NewView)
             (p_info1 : PreparedInfo)
             (p_info2 : PreparedInfo)
             (slf     : Rep)
             (state   : PBFTstate),
        loc e = PBFTreplica slf
        -> state_sm_on_event (PBFTreplicaSM slf) e = Some state
        -> new_view_in_log nv (view_change_state state)
        -> In p_info1 (mergeP (new_view2cert nv))
        -> In p_info2 (mergeP (new_view2cert nv))
        -> info_is_prepared p_info1 = true
        -> info_is_prepared p_info2 = true
        -> prepared_info2view p_info1 = prepared_info2view p_info2
        -> prepared_info2seq p_info1 = prepared_info2seq p_info2
        -> prepared_info2digest p_info1 = prepared_info2digest p_info2.
  Proof.
    introv sentbyz ckeys fbyz;
      introv eqloc eqst in_nv in_e1 in_e2;
      introv ip1 ip2 eqv eqs.

    destruct (PBFTdigestdeq (prepared_info2digest p_info1) (prepared_info2digest p_info2)); auto;[].
    assert False; tcsp.

    assert (well_formed_log (log state)) as wf by eauto 2 with pbft;[].

    eapply prepared_as_pbft_knows_rd in ip1; try (exact eqst); try (exact in_nv); auto.
    eapply prepared_as_pbft_knows_rd in ip2; try (exact eqst); try (exact in_nv); auto.

    pose proof (local_knows_in_intersection1
                  e
                  (2 * F + 1)
                  (prepared_info2request_data p_info1)
                  (prepared_info2request_data p_info2)
                  one_pre_prepare
                  [e]
                  F) as q.
    repeat (autodimp q hyp); simpl; eauto 3 with pbft;
      try (complete (unfold num_replicas; try omega));[].
    exrepnd; unfold lak_data2owner in *; simpl in *; unfold pbft_pl_data2loc in *.

    apply (prepares_like_of_new_views_are_received0 _ _ _ correct) in q3; auto;[].
    apply (prepares_like_of_new_views_are_received0 _ _ _ correct) in q4; auto;[].
    destruct q3 as [e1 kna]; repnd.
    destruct q4 as [e2 knb]; repnd.

    apply pbft_knows_prepare_like_propagates in kna; allrw; eauto 3 with eo pbft;[].
    apply pbft_knows_prepare_like_propagates in knb; allrw; eauto 3 with eo pbft;[].

    destruct kna as [e'1 kna]; repnd.
    destruct knb as [e'2 knb]; repnd.

    apply prepared_info2request_data_equal_prepare_like2request_data_implies in q5; repnd.
    apply prepared_info2request_data_equal_prepare_like2request_data_implies in q6; repnd.
    pose proof (two_know_own_prepare_like eo e'1 e'2 d1 d2) as z.
    repeat (autodimp z hyp); eauto 2 with pbft; try congruence.
  Qed.

End PBFT_A_1_5.
