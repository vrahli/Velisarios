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


Require Export PBFTprops3.


Section PBFTprops4.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma find_pre_prepare_certificate_in_prepared_infos_some_implies :
    forall F n P nfo,
      find_pre_prepare_certificate_in_prepared_infos F n P = Some nfo
      -> In nfo P
         /\ n = prepared_info2seq nfo
         /\ F nfo = true.
  Proof.
    induction P; introv find; simpl in *; ginv.
    smash_pbft; apply IHP in find; tcsp.
  Qed.

  Lemma info_is_prepared_implies_prepared_info_has_correct_digest :
    forall p, info_is_prepared p = true -> prepared_info_has_correct_digest p = true.
  Proof.
    introv h.
    unfold info_is_prepared in h; smash_pbft.
  Qed.
  Hint Resolve info_is_prepared_implies_prepared_info_has_correct_digest : pbft.

  Lemma valid_prepared_info_implies_prepared_info_has_correct_digest :
    forall L p, valid_prepared_info L p = true -> prepared_info_has_correct_digest p = true.
  Proof.
    introv h.
    unfold valid_prepared_info in h; smash_pbft.
  Qed.
  Hint Resolve valid_prepared_info_implies_prepared_info_has_correct_digest : pbft.

  Lemma create_new_prepare_message_true_implies_correct :
    forall (sn : SeqNum) v keys P pp d (n : SeqNum),
      n < sn
      -> create_new_prepare_message sn v keys P = (true,(pp,d))
      -> correct_new_view_opre_prepare v n P pp = true.
  Proof.
    introv ltsn create.
    unfold create_new_prepare_message in create; smash_pbft.

    unfold correct_new_view_opre_prepare; simpl; smash_pbft;
      allrw SeqNumLt_true; allrw SeqNumLt_false; simpl in *; try omega; GC.

    unfold oexists_last_prepared; simpl.

    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto;[]
    end.
    assert False; tcsp.
    rewrite existsb_false in Heqb.

    pose proof (Heqb x) as q; clear Heqb.

    match goal with
    | [ H : find_pre_prepare_certificate_in_prepared_infos _ _ _ = _ |- _ ] =>
      apply find_pre_prepare_certificate_in_prepared_infos_some_implies in H
    end.
    repnd.
    autodimp q hyp.
    smash_pbft.

    match goal with
    | [ H : _ <> _ |- _ ] => destruct H
    end.
    match goal with
    | [ H : valid_prepared_info _ _ = _ |- _ ] =>
      apply valid_prepared_info_implies_prepared_info_has_correct_digest in H
    end.
    unfold prepared_info_has_correct_digest in *; smash_pbft.
  Qed.

  Lemma create_new_prepare_messages_implies_correct_OPs :
    forall n sns v keys P OP NP,
      (forall (x : SeqNum) ppd,
          In x sns
          -> create_new_prepare_message x v keys P = (true, ppd)
          -> n < x)
      -> create_new_prepare_messages sns v keys P = (OP, NP)
      -> forallb
           (correct_new_view_opre_prepare v n P)
           (map fst OP) = true.
  Proof.
    induction sns; introv imp create; simpl in *; smash_pbft; dands; tcsp;
      try (complete (eapply IHsns; eauto)).
    repnd; simpl in *.

    pose proof (imp a (x2,x1)) as q.
    repeat (autodimp q hyp).

    eapply create_new_prepare_message_true_implies_correct;[|eauto]; tcsp.
  Qed.

  Lemma view_change2view_refresh_view_change :
    forall e st,
      view_change2view (refresh_view_change e st) = view_change2view e.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite view_change2view_refresh_view_change : pbft.

  Lemma correct_view_change_implies_same_views :
    forall v vc,
      correct_view_change v vc = true
      -> v = view_change2view vc.
  Proof.
    introv cor; unfold correct_view_change in cor; smash_pbft.
    unfold same_views in *; smash_pbft.
  Qed.

  Lemma ViewLe_true :
    forall v1 v2, ViewLe v1 v2 = true <-> v1 <= v2.
  Proof.
    introv; unfold ViewLe.
    rewrite Nat.leb_le; tcsp.
  Qed.

  Lemma ViewLe_false :
    forall v1 v2, ViewLe v1 v2 = false <-> v1 > v2.
  Proof.
    introv; unfold ViewLe.
    rewrite leb_iff_conv. tcsp.
  Qed.

  Lemma le_max_view_left :
    forall (a b : View), a <= max_view a b.
  Proof.
    introv; destruct a, b; unfold max_view; smash_pbft.
  Qed.
  Hint Resolve le_max_view_left : pbft.

  Lemma le_max_view_right :
    forall (a b : View), a <= max_view b a.
  Proof.
    introv; destruct a, b; unfold max_view; smash_pbft.
    allrw ViewLe_false; simpl in *; omega.
  Qed.
  Hint Resolve le_max_view_right : pbft.

  Lemma le_max_seq_num :
    forall (a b : SeqNum), a <= max_seq_num a b.
  Proof.
    introv; destruct a, b; unfold max_seq_num; simpl; smash_pbft;
      allrw SeqNumLe_true; auto; try omega.
  Qed.
  Hint Resolve le_max_seq_num : pbft.

  Lemma le_max_seq_num_right :
    forall (a b : SeqNum), b <= max_seq_num a b.
  Proof.
    introv; destruct a, b; unfold max_seq_num; simpl; smash_pbft;
      allrw SeqNumLe_true; auto; try omega.
  Qed.
  Hint Resolve le_max_seq_num_right : pbft.

  Lemma le_max_seq_num_op :
    forall (a : SeqNum) b, a <= max_seq_num_op a b.
  Proof.
    introv; destruct b; simpl; eauto 3 with pbft.
  Qed.
  Hint Resolve le_max_seq_num_op : pbft.

  Lemma PreparedInfos2max_seq_none_implies :
    forall F l,
      PreparedInfos2max_seq F l = None
      -> forall p, In p l -> F p = false.
  Proof.
    induction l; introv prep i; simpl in *; smash_pbft.
    repndors; subst; tcsp.
  Qed.

  Lemma PreparedInfos2max_seq_is_max :
    forall pi F l n,
      In pi l
      -> F pi = true
      -> PreparedInfos2max_seq F l = Some n
      -> prepared_info2seq pi <= n.
  Proof.
    induction l; introv i Fpi prep; simpl in *; tcsp; repndors; subst; smash_pbft;[].
    remember (PreparedInfos2max_seq F l) as m; symmetry in Heqm; destruct m; simpl in *; smash_pbft.
    eapply PreparedInfos2max_seq_none_implies in Heqm;[|eauto]; pbft_simplifier.
  Qed.
  Hint Resolve PreparedInfos2max_seq_is_max : pbft.

  Lemma implies_in_from_min_to_max :
    forall (n x m : SeqNum),
      n < x
      -> x <= m
      -> In x (from_min_to_max n m).
  Proof.
    introv h q.
    unfold from_min_to_max; smash_pbft; simpl in *; try omega;[].
    apply in_map_iff.
    exists x; simpl; dands; autorewrite with pbft; auto.
    apply in_seq; simpl; dands; try omega.
  Qed.
  Hint Resolve implies_in_from_min_to_max : pbft.

  Lemma in_from_min_to_max_trans :
    forall (x n m k : SeqNum),
      k <= m
      -> In x (from_min_to_max n k)
      -> In x (from_min_to_max n m).
  Proof.
    introv lek i.
    unfold from_min_to_max in *; smash_pbft.

    - apply in_map_iff in i; exrepnd; subst; simpl in *.
      allrw in_seq; repnd; try omega.

    - allrw in_map_iff; exrepnd; subst; simpl in *.
      allrw in_seq; repnd; try omega.
      exists x0; simpl; dands; auto.
      apply in_seq; dands; simpl; try omega.
  Qed.
  Hint Resolve in_from_min_to_max_trans : pbft.

  Lemma view_change_cert2max_seq_preps_vc_none_implies :
    forall F l,
      view_change_cert2max_seq_preps_vc F l = None
      -> forall p, In p (view_change_cert2prep l) -> F p = false.
  Proof.
    induction l; introv prep i; simpl in *; smash_pbft.
    allrw in_app_iff; repndors; tcsp.
    unfold view_change2max_seq_preps in *.
    eapply PreparedInfos2max_seq_none_implies; eauto.
  Qed.

  Lemma implies_prepared_info2max_seq_in_from_min_to_max :
    forall l pi (n m : SeqNum) vc F,
      In pi (view_change_cert2prep l)
      -> F pi = true
      -> n < prepared_info2seq pi
      -> view_change_cert2max_seq_preps_vc F l = Some (m, vc)
      -> In (prepared_info2seq pi) (from_min_to_max n m).
  Proof.
    induction l; introv i Ft ltn eqv; simpl in *; tcsp;
      smash_pbft; simpl in *; try omega.

    - allrw in_app_iff; repndors; tcsp.

      + unfold view_change2max_seq_preps in *.
        dup i as les.
        eapply PreparedInfos2max_seq_is_max in les;[| |eauto];auto;[].
        eapply implies_in_from_min_to_max; simpl in *; try omega.

      + eapply IHl; eauto.

    - allrw in_app_iff; repndors; tcsp.

      + unfold view_change2max_seq_preps in *.
        dup i as les.
        eapply PreparedInfos2max_seq_is_max in les;[| |eauto];auto;[].
        eapply implies_in_from_min_to_max; simpl in *; try omega.

      + dup i as j.
        eapply IHl in j;[| |eauto|eauto];auto; eauto 3 with pbft.

    - allrw in_app_iff; repndors; tcsp.

      + unfold view_change2max_seq_preps in *.
        dup i as les.
        eapply PreparedInfos2max_seq_is_max in les;[| |eauto];auto;[].
        eapply implies_in_from_min_to_max; simpl in *; try omega.

      + eapply view_change_cert2max_seq_preps_vc_none_implies in i;[|eauto]; pbft_simplifier.

    - allrw in_app_iff; repndors; tcsp.

      + unfold view_change2max_seq_preps in *.
        dup i as les.
        eapply PreparedInfos2max_seq_none_implies in i;[|eauto]; pbft_simplifier.

      + eapply IHl; eauto.
  Qed.
  Hint Resolve implies_prepared_info2max_seq_in_from_min_to_max : pbft.

  Lemma from_min_to_max_of_view_changes_nil_implies_all_sequence_numbers_are_accounted_for_op_true :
    forall entry OP,
      is_some (vce_view_change entry) = true
      -> from_min_to_max_of_view_changes entry = []
      -> all_sequence_numbers_are_accounted_for_op
           (view_change_cert2prep (view_change_entry2view_changes entry))
           (view_change_cert2max_seq (view_change_entry2view_changes entry))
           OP = true.
  Proof.
    introv issome h.
    unfold from_min_to_max_of_view_changes in h.
    destruct entry, vce_view_change; simpl in *; tcsp; GC.
    unfold all_sequence_numbers_are_accounted_for_op.
    unfold all_sequence_numbers_are_accounted_for.

    remember (view_change_cert2max_seq (v :: vce_view_changes)) as maxVop.
    symmetry in HeqmaxVop.
    destruct maxVop; simpl in *;
      [|unfold view_change_cert2max_seq in *; simpl in *; smash_pbft];[].

    unfold from_min_to_max_op in h.

    rewrite forallb_forall.
    introv i.
    unfold sequence_number_is_accounted_for; smash_pbft;[].

    unfold from_min_to_max_of_view_changes_cert in *.
    rewrite HeqmaxVop in *; simpl in *.

    (* WARNING *)
    clear HeqmaxVop.

    assert (view_change2prep v ++ view_change_cert2prep vce_view_changes
            = view_change_cert2prep (v :: vce_view_changes)) as xx by tcsp.
    rewrite xx in *; clear xx.

    (* WARNING *)
    remember (v :: vce_view_changes) as l; clear Heql.
    remember (valid_prepared_info (view_change_cert2prep l)) as F; clear HeqF.

    smash_pbft;[|].

    - unfold view_change_cert2max_seq_preps in *; smash_pbft;[].
      eapply implies_prepared_info2max_seq_in_from_min_to_max in i;
        [| |eauto|eauto];auto.
      rewrite h in *; simpl in *; tcsp.

    - unfold view_change_cert2max_seq_preps in *; smash_pbft;[].
      eapply view_change_cert2max_seq_preps_vc_none_implies in i;[|eauto]; pbft_simplifier.
  Qed.
  Hint Resolve from_min_to_max_of_view_changes_nil_implies_all_sequence_numbers_are_accounted_for_op_true : pbft.

  Lemma view_change_cert_max_seq_preps_vc_none_implies_all_sequence_numbers_are_accounted_for :
    forall k min OP,
      view_change_cert2max_seq_preps_vc (valid_prepared_info (view_change_cert2prep k)) k = None
      -> all_sequence_numbers_are_accounted_for (view_change_cert2prep k) min OP = true.
  Proof.
    introv vcmax.
    unfold all_sequence_numbers_are_accounted_for.
    apply forallb_forall.
    introv i.
    unfold sequence_number_is_accounted_for; smash_pbft.
    assert False; tcsp.
    remember (valid_prepared_info (view_change_cert2prep k)) as F; clear HeqF.
    eapply view_change_cert2max_seq_preps_vc_none_implies in vcmax;[|eauto]; pbft_simplifier.
  Qed.
  Hint Resolve view_change_cert_max_seq_preps_vc_none_implies_all_sequence_numbers_are_accounted_for : pbft.

  Lemma create_new_prepare_message_true_of_valid_prepared_info_in_implies :
    forall x l v keys ppd,
      In x l
      -> valid_prepared_info l x = true
      -> create_new_prepare_message (prepared_info2seq x) v keys l = (true, ppd)
      -> same_digests (prepared_info2digest x) (pre_prepare2digest (fst ppd)) = true
         /\ same_seq_nums (prepared_info2seq x) (pre_prepare2seq (fst ppd)) = true.
  Proof.
    introv i valid create.
    repnd; simpl in *.
    unfold create_new_prepare_message in create; smash_pbft.
    rename_hyp_with find_pre_prepare_certificate_in_prepared_infos fprep.
    apply find_pre_prepare_certificate_in_prepared_infos_some_implies in fprep.
    repnd.

    unfold same_seq_nums; smash_pbft; dands; auto;[].
    unfold pre_prepare2digest; simpl.

    unfold valid_prepared_info in *; smash_pbft.
    unfold last_prepared_info in *.
    allrw forallb_forall.
    applydup valid0 in fprep0.
    smash_pbft;[|].

    - match goal with
      | [ H : info_is_prepared x0 = true |- _ ] => rename H into isprep
      end.
      unfold info_is_prepared in isprep.
      smash_pbft.
      unfold prepared_info_has_correct_digest in *; smash_pbft.

    - applydup fprep2 in i.
      smash_pbft;[].
      try omega.
  Qed.
  Hint Resolve create_new_prepare_message_true_of_valid_prepared_info_in_implies : pbft.

  Lemma create_new_prepare_message_false_of_valid_prepared_info_in_implies :
    forall x l v keys ppd,
      In x l
      -> valid_prepared_info l x = true
      -> create_new_prepare_message (prepared_info2seq x) v keys l = (false, ppd)
      -> False.
  Proof.
    introv i valid create.
    repnd; simpl in *.
    unfold create_new_prepare_message in create; smash_pbft.
    rename_hyp_with find_pre_prepare_certificate_in_prepared_infos fprep.
    eapply find_pre_prepare_certificate_in_prepared_infos_none_implies in i; eauto.
    repndors; pbft_simplifier.
  Qed.
  Hint Resolve create_new_prepare_message_false_of_valid_prepared_info_in_implies : pbft.

  Lemma create_new_prepare_messages_of_valid_prepared_info_in_implies :
    forall N v keys l OP NP x,
      create_new_prepare_messages N v keys l = (OP, NP)
      -> In x l
      -> valid_prepared_info l x = true
      -> In (prepared_info2seq x) N
      -> exists_prepared_info_in_pre_prepares x (map fst OP) = true.
  Proof.
    induction N; introv create i valid j; simpl in *; tcsp.
    repndors; subst; smash_pbft.
  Qed.
  Hint Resolve create_new_prepare_messages_of_valid_prepared_info_in_implies : pbft.

  Lemma create_new_prepare_messages_implies_all_sequence_numbers_are_accounted_for :
    forall l v keys OP NP min max vc,
      create_new_prepare_messages (from_min_to_max min max) v keys (view_change_cert2prep l) = (OP, NP)
      -> view_change_cert2max_seq l = Some min
      -> view_change_cert2max_seq_preps_vc (valid_prepared_info (view_change_cert2prep l)) l = Some (max, vc)
      -> all_sequence_numbers_are_accounted_for (view_change_cert2prep l) min (map fst OP) = true.
  Proof.
    introv create vcmin vcmax.
    unfold all_sequence_numbers_are_accounted_for.
    apply forallb_forall.
    introv i.
    unfold sequence_number_is_accounted_for; smash_pbft.
  Qed.
  Hint Resolve create_new_prepare_messages_implies_all_sequence_numbers_are_accounted_for : pbft.

  Lemma check_broadcast_new_view_generates :
    forall i state entry nv entry' OP NP,
      check_broadcast_new_view i state entry = Some (nv, entry', OP, NP)
      -> correct_new_view nv = true.
  Proof.
    introv check.
    dup check as check_backup.
    hide_hyp check_backup.
    unfold check_broadcast_new_view in check; smash_pbft.

    rename_hyp_with view_changed_entry changed.
    dup changed as changed_backup.
    hide_hyp changed_backup.
    unfold view_changed_entry in changed; smash_pbft.

    pose proof (implies_length_view_change_entry2view_changes entry (length (vce_view_changes entry))) as lenvcs.
    repeat (autodimp lenvcs hyp); allrw; auto;[].

    remember (replace_own_view_change_in_entry (refresh_view_change x state) entry) as entry'.
    remember (view_change_cert2max_seq (view_change_entry2view_changes entry')) as minop.
    symmetry in Heqminop.
    rename_hyp_with create_new_prepare_messages cr.
    destruct minop as [min|];
      [|applydup create_new_prepare_messages_view_change_cert2max_seq_none_implies in cr as eqs; auto;
        repnd; subst; simpl in *;
        rewrite eqs in *; simpl in *; GC;
        unfold correct_new_view; simpl; smash_pbft; try omega;
        destruct entry, vce_view_change; simpl in *; smash_pbft; try omega;
        [eapply from_min_to_max_of_view_changes_nil_implies_all_sequence_numbers_are_accounted_for_op_true in eqs;
         simpl in *; auto; exact eqs|];[];
        match goal with
        | [ H : correct_view_change _ _ = _ |- _ ] =>
          applydup correct_view_change_implies_same_views in H as sv; simpl in sv
        end; autorewrite with pbft in *; subst; tcsp];[].

    assert (forall n, In n (from_min_to_max_of_view_changes entry') -> n <= max_O OP) as imp1.
    { introv i; eapply view_changed_entry_some_and_check_broadcast_new_view_implies_le; eauto. }

    clear check_backup.
    clear changed_backup.

    rename_hyp_with correct_view_change corvcs.
    assert (vce_view entry = view_change2view x) as eqviews.
    {
      unfold view_change_entry2view_changes in corvcs.
      subst entry'; simpl in *.
      destruct entry; simpl in *; smash_pbft.
      unfold correct_view_change in *; smash_pbft.
      unfold same_views in *; smash_pbft.
    }

    unfold correct_new_view; simpl; smash_pbft; try omega;
      try (complete (destruct entry, vce_view_change; simpl in *; smash_pbft; try omega));
      [| |].

    - rename_hyp_with correct_new_view_opre_prepare_op coro.
      rename_hyp_with correct_new_view_npre_prepare_op corn.
      rename_hyp_with SeqNumDeq nrep1.

      hide_hyp imp1.
      hide_hyp coro.
      hide_hyp corn.
      hide_hyp nrep1.

      rewrite Heqminop; simpl.
      remember (replace_own_view_change_in_entry (refresh_view_change x state) entry) as l.

      unfold from_min_to_max_of_view_changes in *; simpl in *.
      unfold from_min_to_max_of_view_changes_cert in *; simpl in *.
      rewrite Heqminop in *; simpl in *.

      unfold view_change_cert2max_seq_preps in *; smash_pbft.

    - match goal with
      | [ H1 : create_new_prepare_messages _ _ _ _ = _, H2 : forallb _ _ = false |- _ ] =>
        apply (create_new_prepare_messages_implies_correct_NPs
                 min (pre_prepares2max_seq (map fst OP))) in H1
      end.

      {
        rewrite Heqminop in *; simpl in *; autorewrite with pbft in *; smash_pbft.
      }

      introv i create; repnd.
      dands; eauto 2 with pbft.
      rewrite <- max_O_as_pre_prepares2max_seq.

      applydup imp1 in i.
      apply le_lt_or_eq in i0; repndors; tcsp;[].
      apply implies_eq_seq_nums in i0.

      assert False; tcsp.

      clear imp1.
      unfold from_min_to_max_of_view_changes in *.
      unfold from_min_to_max_of_view_changes_cert in *.

      applydup in_from_min_to_max_op_implies in i.
      exrepnd.
      rewrite i2 in *; ginv.
      rewrite i3 in *; ginv.
      simpl in *.

      pose proof (max_O_in OP) as q.

      apply (view_change_cert2max_seq_preps_implies_exists_create_new_prepare_message
               (view_change2view x) (local_keys state)) in i3.
      exrepnd.

      match goal with
      | [ H1 : create_new_prepare_message _ _ _ _ = (false, _),
          H2 : create_new_prepare_messages _ _ _ _ = _
      |- _ ] =>
        applydup create_new_prepare_message_implies_same_sequence_number in H1 as eqsn;
          dup H2 as c1; dup H2 as c2; dup H2 as c3; rename H1 into fcreate
      end.

      (* c1 part *)
      eapply create_new_prepare_message_true_implies_oprep_not_nil in c1;
        [| |eauto]; eauto 2 with pbft;[].

      (* c2 part *)
      eapply false_implies_in_create_new_prepare_messages_n_pre_prepare in c2;
        [| |exact fcreate];[|unfold from_min_to_max_of_view_changes;allrw;simpl;auto];[].

      (* c3 part *)
      apply create_new_prepare_messages_implies_norepeatsb in c3; eauto 2 with pbft;[].

      autodimp q hyp; eauto 2 with pbft;[].
      exrepnd.

      eapply norepeatsb_pre_prepare2seq_oprep_nprep_implies;[eauto| |eauto|eauto].
      congruence.

    - match goal with
      | [ H1 : create_new_prepare_messages _ _ _ _ = _, H2 : forallb _ _ = false |- _ ] =>
        apply (create_new_prepare_messages_implies_correct_OPs min) in H1
      end.

      {
        rewrite Heqminop in *; simpl in *; autorewrite with pbft in *; smash_pbft.
      }

      introv i create.
      dands; eauto 2 with pbft.
  Qed.
  Hint Resolve check_broadcast_new_view_generates : pbft.

End PBFTprops4.


Hint Resolve info_is_prepared_implies_prepared_info_has_correct_digest : pbft.
Hint Resolve valid_prepared_info_implies_prepared_info_has_correct_digest : pbft.
Hint Resolve le_max_view_left : pbft.
Hint Resolve le_max_view_right : pbft.
Hint Resolve le_max_seq_num : pbft.
Hint Resolve le_max_seq_num_right : pbft.
Hint Resolve le_max_seq_num_op : pbft.
Hint Resolve PreparedInfos2max_seq_is_max : pbft.
Hint Resolve implies_in_from_min_to_max : pbft.
Hint Resolve in_from_min_to_max_trans : pbft.
Hint Resolve implies_prepared_info2max_seq_in_from_min_to_max : pbft.
Hint Resolve from_min_to_max_of_view_changes_nil_implies_all_sequence_numbers_are_accounted_for_op_true : pbft.
Hint Resolve view_change_cert_max_seq_preps_vc_none_implies_all_sequence_numbers_are_accounted_for : pbft.
Hint Resolve create_new_prepare_message_true_of_valid_prepared_info_in_implies : pbft.
Hint Resolve create_new_prepare_message_false_of_valid_prepared_info_in_implies : pbft.
Hint Resolve create_new_prepare_messages_of_valid_prepared_info_in_implies : pbft.
Hint Resolve create_new_prepare_messages_implies_all_sequence_numbers_are_accounted_for : pbft.
Hint Resolve check_broadcast_new_view_generates : pbft.


Hint Rewrite @view_change2view_refresh_view_change : pbft.
