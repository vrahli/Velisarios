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


Section PBFT_A_1_9_misc2.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma correct_new_view_implies_all_sequence_numbers_are_accounted_for_op :
    forall nv,
      correct_new_view nv = true
      -> all_sequence_numbers_are_accounted_for_op
           (view_change_cert2prep (new_view2cert nv))
           (view_change_cert2max_seq  (new_view2cert nv))
           (new_view2oprep nv) = true.
  Proof.
    introv cor; unfold correct_new_view in cor; smash_pbft.
  Qed.

  Lemma all_sequence_numbers_are_accounted_for_implies1 :
    forall nv vc pi maxV P,
      all_sequence_numbers_are_accounted_for
        (view_change_cert2prep (new_view2cert nv))
        maxV P = true
      -> In vc (new_view2cert nv)
      -> In pi (view_change2prep vc)
      -> sequence_number_is_accounted_for
           (view_change_cert2prep (new_view2cert nv))
           maxV P pi = true.
  Proof.
    introv acc i j.
    unfold all_sequence_numbers_are_accounted_for in acc.
    rewrite forallb_forall in acc.
    apply acc; eauto 2 with pbft.
  Qed.

  Lemma all_sequence_numbers_are_accounted_for_implies2 :
    forall nv pi maxV P,
      all_sequence_numbers_are_accounted_for
        (view_change_cert2prep (new_view2cert nv))
        maxV P = true
      -> In pi (view_change_cert2prep (new_view2cert nv))
      -> sequence_number_is_accounted_for
           (view_change_cert2prep (new_view2cert nv))
           maxV P pi = true.
  Proof.
    introv acc i.
    unfold all_sequence_numbers_are_accounted_for in acc.
    rewrite forallb_forall in acc.
    apply acc; auto.
  Qed.

  Lemma forallb_false :
    forall {A} f (l : list A),
      forallb f l = false <-> exists a, In a l /\ f a = false.
  Proof.
    induction l; simpl; split; intro h; exrepnd; tcsp; smash_pbft;
      repndors; subst; tcsp.

    - exists a; tcsp.

    - apply IHl in h; exrepnd; exists a0; tcsp.

    - right; apply IHl; exists a0; tcsp.
  Qed.

  Hint Resolve equal_nats_implies_equal_views : pbft.

  Lemma valid_prepared_info_false_implies :
    forall P pi,
      info_is_prepared pi = true
      -> valid_prepared_info P pi = false
      ->
      exists nfo,
        In nfo P
        /\ info_is_prepared nfo = true
        /\ prepared_info2seq pi = prepared_info2seq nfo
        /\
        (
          (
            prepared_info2view pi = prepared_info2view nfo
            /\ prepared_info2digest pi <> prepared_info2digest nfo
          )
          \/
          prepared_info2view pi < prepared_info2view nfo
        ).
  Proof.
    introv prep val.
    unfold valid_prepared_info in val; smash_pbft.
    repndors; tcsp; pbft_simplifier;[].
    unfold last_prepared_info in *.
    apply forallb_false in val.
    exrepnd.
    exists a; dands; auto; smash_pbft.

    - unfold same_digests in *; smash_pbft;[].
      left; dands; auto.
      symmetry; eauto 3 with pbft.

    - right; omega.
  Qed.

  Lemma decidable_exists_prepared_info :
    forall (n : SeqNum) P,
      Decidable.decidable
        (exists nfo,
            In nfo P
            /\ info_is_prepared nfo = true
            /\ n = prepared_info2seq nfo).
  Proof.
    induction P; simpl;[right; tcsp|].
    destruct IHP as [IHP|IHP]; exrepnd.

    - left; exists nfo; tcsp.

    - remember (info_is_prepared a) as prepa; symmetry in Heqprepa; destruct prepa.

      + destruct (SeqNumDeq n (prepared_info2seq a)) as [d|d].

        * left; exists a; tcsp.

        * right; intro xx; exrepnd; repndors; subst; tcsp.
          destruct IHP; eexists; dands; eauto.

      + right; intro xx; exrepnd; repndors; subst; tcsp; pbft_simplifier.
        destruct IHP; eexists; dands; eauto.
  Qed.

  Definition prepared_info_with_highest_view
             (P : list PreparedInfo)
             (n : SeqNum)
             (nfo : PreparedInfo) :=
    forall x,
      In x P
      -> info_is_prepared x = true
      -> n = prepared_info2seq x
      -> prepared_info2view x <= prepared_info2view nfo.

  Lemma exists_prepared_info_with_highest_view :
    forall P nfo,
      In nfo P
      -> info_is_prepared nfo = true
      ->
      exists nfo',
        In nfo' P
        /\ info_is_prepared nfo' = true
        /\ prepared_info2seq nfo' = prepared_info2seq nfo
        /\ prepared_info_with_highest_view P (prepared_info2seq nfo) nfo'.
  Proof.
    induction P; introv i prep; simpl in *; tcsp; repndors; subst; tcsp.

    - destruct (decidable_exists_prepared_info (prepared_info2seq nfo) P) as [d|d].

      + exrepnd.
        applydup IHP in d1; auto.
        exrepnd.

        destruct (le_dec (prepared_info2view nfo) (prepared_info2view nfo')) as [f|f].

        * exists nfo'; dands; tcsp; try congruence.
          introv j w z; simpl in *; repndors; subst; tcsp; GC.
          apply d4; eauto; try congruence.

        * exists nfo; dands; tcsp.
          introv j w z; simpl in *; repndors; subst; tcsp; GC.
          apply d4 in j; repeat (autodimp j hyp); tcsp; try omega.

      + exists nfo; dands; tcsp.
        introv j w z; simpl in *; repndors; subst; tcsp; GC.
        destruct (le_dec (prepared_info2view x) (prepared_info2view nfo)); tcsp.
        destruct d.
        exists x; tcsp.

    - applydup IHP in i; exrepnd; auto.

      destruct (le_dec (prepared_info2view a) (prepared_info2view nfo')) as [f|f].

      + exists nfo'. dands; auto.
        introv j w z; simpl in *; repndors; subst; tcsp; GC.

      + remember (info_is_prepared a) as prepa; symmetry in Heqprepa; destruct prepa.

        * destruct (SeqNumDeq (prepared_info2seq a) (prepared_info2seq nfo)) as [e|e].

          {
            exists a; dands; tcsp.
            introv j w z; simpl in *; repndors; subst; tcsp.
            applydup i1 in j; repeat (autodimp j0 hyp); auto.
            destruct (le_dec (prepared_info2view x) (prepared_info2view a)); try omega.
          }

          {
            exists nfo'; dands; tcsp.
            introv j w z; simpl in *; repndors; subst; tcsp.
          }

        * exists nfo'; dands; tcsp.
          introv j w z; simpl in *; repndors; subst; tcsp; pbft_simplifier.
  Qed.

  Lemma valid_prepared_info_false_implies2 :
    forall P pi,
      info_is_prepared pi = true
      -> valid_prepared_info P pi = false
      ->
      exists nfo,
        In nfo P
        /\ info_is_prepared nfo = true
        /\ prepared_info2seq pi = prepared_info2seq nfo
        /\
        (
          (
            prepared_info2view pi = prepared_info2view nfo
            /\ prepared_info2digest pi <> prepared_info2digest nfo
          )
          \/
          (
            prepared_info2view pi < prepared_info2view nfo
            /\ prepared_info_with_highest_view P (prepared_info2seq pi) nfo
          )
        ).
  Proof.
    introv prep val.
    unfold valid_prepared_info in val; smash_pbft.
    repndors; tcsp; pbft_simplifier;[].
    unfold last_prepared_info in *.
    apply forallb_false in val.
    exrepnd.
    smash_pbft;[|].

    - unfold same_digests in *; smash_pbft;[].
      exists a; dands; auto.
      left; dands; auto.
      symmetry; eauto 3 with pbft.

    - pose proof (exists_prepared_info_with_highest_view P a) as q.
      repeat (autodimp q hyp); exrepnd.
      exists nfo'; dands; auto; try congruence;[].
      applydup q0 in val1; repeat (autodimp val2 hyp); auto;[].
      right; dands; auto; try omega;[].
      introv j w z.
      applydup q0 in j; repeat (autodimp j0 hyp); auto; try congruence.
  Qed.

  Lemma prepared_info_with_highest_view_implies_valid :
    forall P nfo,
      (forall x,
          In x P
          -> info_is_prepared x = true
          -> prepared_info2seq x = prepared_info2seq nfo
          -> prepared_info2view x = prepared_info2view nfo
          -> prepared_info2digest x = prepared_info2digest nfo)
      -> info_is_prepared nfo = true
      -> prepared_info_with_highest_view P (prepared_info2seq nfo) nfo
      -> valid_prepared_info P nfo = true.
  Proof.
    introv imp prep hv.
    unfold prepared_info_with_highest_view in hv.
    unfold valid_prepared_info; smash_pbft; dands; auto;[].
    unfold last_prepared_info.
    rewrite forallb_forall.
    introv j; smash_pbft;[|applydup hv in j; auto; omega];[].
    unfold same_digests; smash_pbft;[].
    apply imp in j; auto; eauto 3 with pbft.
  Qed.

  Lemma wf_view_change_state_implies_correct_view_of_new_view :
    forall s entry nv,
      wf_view_change_state s
      -> In entry s
      -> vce_new_view entry = Some nv
      -> vce_view entry = new_view2view nv.
  Proof.
    introv wf i vcenv.
    assert (wf_view_change_entry entry) as wfe by eauto 3 with pbft.
    apply wf_view_change_entry_new_view in vcenv; auto.
  Qed.
  Hint Resolve wf_view_change_state_implies_correct_view_of_new_view : pbft.

  Lemma has_new_view_implies_new_view_in_log :
    forall s (v : View),
      0 < v
      -> wf_view_change_state s
      -> has_new_view s v = true
      -> exists nv,
          new_view_in_log nv s
          /\ v = new_view2view nv
          (*/\ correct_new_view nv = true*).
  Proof.
    introv gt0 wf hnv.
    unfold has_new_view in hnv; smash_pbft; simpl in *; try omega.
    unfold has_new_view1 in hnv.
    rewrite existsb_exists in hnv.
    destruct hnv as [entry hnv]; repnd.
    smash_pbft;[].
    exists n0; dands; auto; eauto 3 with pbft.
  Qed.

  Definition prepared_info2all_senders (nfo : PreparedInfo) : list Rep :=
    prepared_info2pp_sender nfo :: prepared_info2senders nfo.

  Lemma info_is_prepared_implies_no_repeats_senders :
    forall nfo,
      info_is_prepared nfo = true
      -> no_repeats (prepared_info2all_senders nfo).
  Proof.
    introv prep.
    unfold info_is_prepared in prep; smash_pbft.
    allrw @norepeatsb_as_no_repeats; auto.
    unfold prepared_info2all_senders.
    constructor; auto.
    intro i.
    allrw forallb_forall.
    apply prep1 in i; smash_pbft.
  Qed.
  Hint Resolve info_is_prepared_implies_no_repeats_senders : pbft.

  Lemma info_is_prepared_implies_length_gt_F :
    forall nfo,
      info_is_prepared nfo = true
      -> F + 1 <= length (prepared_info2all_senders nfo).
  Proof.
    introv prep.
    unfold info_is_prepared in prep; smash_pbft; try omega.
  Qed.
  Hint Resolve info_is_prepared_implies_length_gt_F : pbft.

  Lemma in_prepared_info2all_senders_implies_exits_prepare_like :
    forall r nfo,
      In r (prepared_info2all_senders nfo)
      ->
      exists pl,
        prepare_like_in_prepared_info pl nfo
        /\ prepare_like2sender pl = r.
  Proof.
    introv i.
    unfold prepared_info2all_senders in i; simpl in *; repndors; subst.

    - exists (prepare_like_pre_prepare (prepared_info_pre_prepare nfo)).
      simpl; autorewrite with pbft; tcsp.

    - unfold prepared_info2senders in i.
      allrw in_map_iff; exrepnd; subst.
      exists (prepare_like_prepare x); simpl; tcsp.
  Qed.

  Hint Resolve well_formed_log_entry_if_in : pbft.

  Lemma entry_of_pre_prepare_in_log2 :
    forall d p L,
      pre_prepare_in_log p d L = true
      ->
      exists entry rs,
        In entry L
        /\ log_entry_request_data entry = pre_prepare2request_data p d
        /\ log_entry_pre_prepare_info entry = pp_info_pre_prep (pre_prepare2auth p) rs
        /\ map fst rs = pre_prepare2requests p.
  Proof.
    induction L; introv h; simpl in *; tcsp; smash_pbft;[|].

    - allrw auth_matches_logEntryPrePrepareInfo_true_iff.
      allrw requests_matches_logEntryPrePrepareInfo_true_iff.
      allrw similar_entry_and_pre_prepare_true_iff.
      exrepnd.
      exists a reqs; dands; tcsp.
      allrw; tcsp.

    - apply IHL in h; exrepnd; exists entry rs; auto.
  Qed.

  Lemma own_prepare_like_message_in_log_implies_pre_prepare_in_log :
    forall (eo : EventOrdering)
           (e  : Event)
           (st : PBFTstate)
           (i  : Rep)
           (pl : Prepare_like),
      prepare_like2sender pl = i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> prepare_like_in_log pl (log st)
      ->
      exists pp d,
        pre_prepare_in_log pp d (log st) = true
        /\ prepare_like2request_data pl = pre_prepare2request_data pp d.
  Proof.
    introv eqi eqst prep.
    apply prepare_like_in_log_implies_or in prep.
    repndors; exrepnd; subst; simpl in *.

    - apply prepare_somewhere_in_log_iff_prepare_in_log in prep1;[|eauto 2 with pbft];[].
      destruct prep0, b; simpl in *.
      eapply PBFT_A_1_2_7 in prep1;[|eauto]; auto;[].
      exrepnd.
      eexists; eexists; dands; eauto.

    - eapply pre_prepare_in_somewhere_in_log_implies_pre_prepare_in_log in prep1;[|eauto];[].
      eexists; eexists; dands; eauto.
      f_equal.

      applydup entry_of_pre_prepare_in_log2 in prep1; exrepnd.

      assert (well_formed_log_entry entry) as wf by (eauto 3 with pbft).
      apply well_formed_log_entry_correct_digest in wf.
      clear prep2.
      destruct entry; simpl in *; subst.
      unfold pp_info_has_correct_digest in wf.
      unfold same_digests in *; smash_pbft.
      subst.
      unfold pre_prepare2digest.
      allrw <- ; eauto 2 with pbft.
  Qed.

  Lemma correct_view_change_implies_correct_view_change_preps :
    forall v vc,
      correct_view_change v vc = true
      -> correct_view_change_preps (view_change2seq vc) v (view_change2prep vc) = true.
  Proof.
    introv cor.
    unfold correct_view_change in cor; smash_pbft.
    unfold same_views in *; smash_pbft.
  Qed.

  Lemma dec_exists_pre_prepare_with_higher_view :
    forall vc v n d,
      Decidable.decidable
        (exists v' r a,
            In (mk_pre_prepare v' n r a) (pre_prepares_of_view_change vc)
            /\ v <= v'
            /\ d = requests2digest r).
  Proof.
    introv.
    destruct vc, v0; simpl in *.
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

        + destruct (le_dec v v1) as [dv|dv].

          * destruct (PBFTdigestdeq d (requests2digest d0)) as [dd|dd]; subst.

            {
              left.
              exists v1 d0 a0; dands; tcsp.
            }

            {
              right; introv xx; exrepnd; subst.
              unfold mk_pre_prepare in *.
              repndors; ginv;[].
              destruct IHP.
              eexists; eexists; eexists; dands; eauto.
            }

          * right; introv xx; exrepnd; subst.
            unfold mk_pre_prepare in *.
            repndors; ginv; try omega;[].
            destruct IHP.
            eexists; eexists; eexists; dands; eauto.

        + right; introv xx; exrepnd; subst.
          unfold mk_pre_prepare in *.
          repndors; ginv;[].
          destruct IHP.
          eexists; eexists; eexists; dands; eauto.
    }
  Qed.

  Lemma prepared_info_pre_prepare_mk_pre_prepare_seq :
    forall pi v n rs a,
      prepared_info_pre_prepare pi = mk_pre_prepare v n rs a
      -> n = prepared_info2seq pi.
  Proof.
    introv H.
    unfold mk_pre_prepare in *.
    unfold prepared_info2seq.
    unfold pre_prepare2seq.
    destruct (prepared_info_pre_prepare pi), b. simpl in *.
    inversion H. auto.
  Qed.
  Hint Resolve prepared_info_pre_prepare_mk_pre_prepare_seq : pbft.

  Lemma prepared_info_pre_prepare_mk_pre_prepare_view :
    forall pi v n rs a,
      prepared_info_pre_prepare pi = mk_pre_prepare v n rs a
      -> v = prepared_info2view pi.
  Proof.
    introv H.
    unfold mk_pre_prepare in *.
    unfold prepared_info2view.
    unfold pre_prepare2view.
    destruct (prepared_info_pre_prepare pi), b. simpl in *.
    inversion H. auto.
  Qed.
  Hint Resolve prepared_info_pre_prepare_mk_pre_prepare_view : pbft.

  Lemma prepared_info_pre_prepare_mk_pre_prepare_req :
    forall pi v n rs a,
      prepared_info_pre_prepare pi = mk_pre_prepare v n rs a
      -> rs = prepared_info2requests pi.
  Proof.
    introv H.
    unfold mk_pre_prepare in *.
    unfold prepared_info2requests.
    unfold pre_prepare2requests.
    destruct (prepared_info_pre_prepare pi), b. simpl in *.
    inversion H. auto.
  Qed.
  Hint Resolve prepared_info_pre_prepare_mk_pre_prepare_req : pbft.

  Lemma prepare_like2request_data_pre_prepare2request_data_implies_eq_views :
    forall pl pp d,
      prepare_like2request_data pl = pre_prepare2request_data pp d
      -> prepare_like2view pl = pre_prepare2view pp.
  Proof.
    introv h; destruct pl, pp, b; simpl in *.

    - destruct pp0, b; simpl in *; ginv; auto.

    - destruct p, b; simpl in *; ginv; auto.
  Qed.
  Hint Resolve prepare_like2request_data_pre_prepare2request_data_implies_eq_views : pbft.

  Lemma valid_prepared_info_implies_prepare_like2view_equal_prepared_info2view :
    forall P pl nfo,
      prepare_like_in_prepared_info pl nfo
      -> valid_prepared_info P nfo = true
      -> prepare_like2view pl = prepared_info2view nfo.
  Proof.
    introv prep valid.
    unfold valid_prepared_info in valid; smash_pbft.
    clear valid0.
    unfold info_is_prepared in valid; smash_pbft.
    destruct pl; simpl in *; subst; simpl in *; autorewrite with pbft in *.

    - destruct nfo; simpl in *; auto.

    - allrw forallb_forall.
      apply valid0 in prep; clear valid0; smash_pbft.
      destruct p, b, nfo; simpl in *; tcsp.
      unfold prepared_info2request_data in *; simpl in *.
      unfold prepared_info2view in *; simpl in *.
      destruct prepared_info_pre_prepare, b; simpl in *; ginv.
  Qed.
  Hint Resolve valid_prepared_info_implies_prepare_like2view_equal_prepared_info2view : pbft.

  Lemma prepare_like2request_data_pre_prepare2request_data_implies_eq_seqs :
    forall pl pp d,
      prepare_like2request_data pl = pre_prepare2request_data pp d
      -> prepare_like2seq pl = pre_prepare2seq pp.
  Proof.
    introv h; destruct pl, pp, b; simpl in *.

    - destruct pp0, b; simpl in *; ginv; auto.

    - destruct p, b; simpl in *; ginv; auto.
  Qed.
  Hint Resolve prepare_like2request_data_pre_prepare2request_data_implies_eq_seqs : pbft.

  Lemma valid_prepared_info_implies_prepare_like2seq_equal_prepared_info2seq :
    forall P pl nfo,
      prepare_like_in_prepared_info pl nfo
      -> valid_prepared_info P nfo = true
      -> prepare_like2seq pl = prepared_info2seq nfo.
  Proof.
    introv prep valid.
    unfold valid_prepared_info in valid; smash_pbft.
    clear valid0.
    unfold info_is_prepared in valid; smash_pbft.
    destruct pl; simpl in *; subst; simpl in *; autorewrite with pbft in *.

    - destruct nfo; simpl in *; auto.

    - allrw forallb_forall.
      apply valid0 in prep; clear valid0; smash_pbft.
      destruct p, b, nfo; simpl in *; tcsp.
      unfold prepared_info2request_data in *; simpl in *.
      unfold prepared_info2seq in *; simpl in *.
      destruct prepared_info_pre_prepare, b; simpl in *; ginv.
  Qed.
  Hint Resolve valid_prepared_info_implies_prepare_like2seq_equal_prepared_info2seq : pbft.

  Lemma prepare_like2request_data_pre_prepare2request_data_implies_eq_digests :
    forall pl pp d,
      prepare_like2request_data pl = pre_prepare2request_data pp d
      -> prepare_like2digest pl = d.
  Proof.
    introv h; destruct pl, pp, b; simpl in *.

    - destruct pp0, b; simpl in *; ginv; auto.

    - destruct p, b; simpl in *; ginv; auto.
  Qed.
  Hint Resolve prepare_like2request_data_pre_prepare2request_data_implies_eq_digests : pbft.

  Lemma valid_prepared_info_implies_prepare_like2digest_equal_prepared_info2digest :
    forall P pl nfo,
      prepare_like_in_prepared_info pl nfo
      -> valid_prepared_info P nfo = true
      -> prepare_like2digest pl = prepared_info2digest nfo.
  Proof.
    introv prep valid.
    unfold valid_prepared_info in valid; smash_pbft.
    clear valid0.
    unfold info_is_prepared in valid; smash_pbft.
    destruct pl; simpl in *; subst; simpl in *; autorewrite with pbft in *.

    - unfold prepared_info_has_correct_digest in *; smash_pbft.

    - allrw forallb_forall.
      apply valid0 in prep; clear valid0; smash_pbft.
      destruct p, b, nfo; simpl in *; tcsp.
      unfold prepared_info2request_data in *; simpl in *.
      unfold prepared_info2seq in *; simpl in *.
      destruct prepared_info_pre_prepare, b; simpl in *; ginv.
  Qed.
  Hint Resolve valid_prepared_info_implies_prepare_like2digest_equal_prepared_info2digest : pbft.

End PBFT_A_1_9_misc2.


Hint Resolve equal_nats_implies_equal_views : pbft.
Hint Resolve wf_view_change_state_implies_correct_view_of_new_view : pbft.
Hint Resolve info_is_prepared_implies_no_repeats_senders : pbft.
Hint Resolve info_is_prepared_implies_length_gt_F : pbft.
Hint Resolve well_formed_log_entry_if_in : pbft.
Hint Resolve prepared_info_pre_prepare_mk_pre_prepare_seq : pbft.
Hint Resolve prepared_info_pre_prepare_mk_pre_prepare_view : pbft.
Hint Resolve prepared_info_pre_prepare_mk_pre_prepare_req : pbft.
Hint Resolve prepare_like2request_data_pre_prepare2request_data_implies_eq_views : pbft.
Hint Resolve valid_prepared_info_implies_prepare_like2view_equal_prepared_info2view : pbft.
Hint Resolve prepare_like2request_data_pre_prepare2request_data_implies_eq_seqs : pbft.
Hint Resolve valid_prepared_info_implies_prepare_like2seq_equal_prepared_info2seq : pbft.
Hint Resolve prepare_like2request_data_pre_prepare2request_data_implies_eq_digests : pbft.
Hint Resolve valid_prepared_info_implies_prepare_like2digest_equal_prepared_info2digest : pbft.
