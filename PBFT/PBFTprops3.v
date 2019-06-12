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


Require Export list_util1.
Require Export PBFTprops2.
Require Export List.


Section PBFTprops3.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.



  Lemma request_data_and_rep_toks2prepare_as_pre_prepare2prepare :
    forall pp d i keys,
      request_data_and_rep_toks2prepare
        (pre_prepare2request_data pp d)
        (pre_prepare2rep_toks_of_prepare i keys pp d)
      = pre_prepare2prepare i keys pp d.
  Proof.
    introv; auto.
    destruct pp, b; simpl; auto.
  Qed.
  Hint Rewrite request_data_and_rep_toks2prepare_as_pre_prepare2prepare : pbft.

  Lemma is_primary_PBFTprimary :
    forall v, is_primary v (PBFTprimary v) = true.
  Proof.
    introv.
    unfold is_primary; simpl; pbft_dest_all x.
  Qed.
  Hint Rewrite is_primary_PBFTprimary : pbft.

  Lemma eq_request_data_same :
    forall x, eq_request_data x x = true.
  Proof.
    introv; unfold eq_request_data; pbft_dest_all x.
  Qed.
  Hint Rewrite eq_request_data_same : pbft.

  Hint Rewrite orb_false_r : bool.

  Lemma find_rep_toks_in_list_none_iff :
    forall i preps,
      find_rep_toks_in_list i preps = None
      <-> forall rt, In rt preps -> i <> rt_rep rt.
  Proof.
    induction preps; simpl; introv; split; intro h; tcsp; smash_pbft.

    - introv j; repndors; subst; tcsp.
      rewrite IHpreps in h.
      apply h; auto.

    - pose proof (h a) as q; autodimp q hyp; tcsp.

    - apply IHpreps; exrepnd.
      introv j; apply h; tcsp.
  Qed.

  Lemma own_prepare_is_already_in_entry_with_different_digest_false_and_same_request_data_implies_same_digest :
    forall i s v d d' a entry,
      own_prepare_is_already_in_entry_with_different_digest i s v d entry = None
      -> log_entry_request_data entry = request_data v s d'
      -> In (MkRepToks i a) (log_entry_prepares entry)
      -> d = d'.
  Proof.
    introv h q k.
    unfold own_prepare_is_already_in_entry_with_different_digest in h.
    smash_pbft.

    { rewrite q; simpl; auto. }

    { allrw find_rep_toks_in_list_none_iff.
      discover; simpl in *; tcsp. }

    { match goal with
      | [ H : _ <> _ |- _ ] => destruct H; rewrite q; simpl; auto
      end. }

    { match goal with
      | [ H : _ <> _ |- _ ] => destruct H; rewrite q; simpl; auto
      end. }
  Qed.

  Lemma own_prepare_is_already_logged_with_different_digest_false_and_prepare_in_log_implies_same_digest :
    forall L i s v d d' a,
      own_prepare_is_already_logged_with_different_digest i s v d L = None
      -> prepare_in_log (mk_prepare v s d' i a) L = true
      -> d = d'.
  Proof.
    induction L; introv h w; simpl in *; pbft_simplifier.
    smash_pbft.

    allrw is_prepare_for_entry_true_iff; simpl in *.
    allrw existsb_exists; exrepnd.
    allrw same_rep_tok_true_iff; subst.

    rename_hyp_with own_prepare_is_already_in_entry_with_different_digest own.
    eapply own_prepare_is_already_in_entry_with_different_digest_false_and_same_request_data_implies_same_digest in own; eauto.
  Qed.

  Lemma mk_prepare_eq_pre_prepare2prepare_implies_eq :
    forall v n d1 i1 a i2 keys pp d2,
      mk_prepare v n d1 i1 a = pre_prepare2prepare i2 keys pp d2
      -> i1 = i2 /\ d1 = d2.
  Proof.
    introv h.
    destruct pp, b; simpl in *.
    unfold pre_prepare2prepare, mk_prepare in *; ginv; tcsp.
  Qed.

  Lemma mk_prepare_eq_pre_prepare2prepare_implies_eq_seq :
    forall v n d1 i1 a i2 keys pp d2,
      mk_prepare v n d1 i1 a = pre_prepare2prepare i2 keys pp d2
      -> pre_prepare2seq pp = n.
  Proof.
    introv h.
    destruct pp, b; simpl in *.
    unfold pre_prepare2prepare, mk_prepare in *; ginv; tcsp.
  Qed.

  Lemma correct_new_view_implies_norepeatsb :
    forall nv,
      correct_new_view nv = true
      -> norepeatsb
           SeqNumDeq
           (map pre_prepare2seq (new_view2oprep nv ++ new_view2nprep nv)) = true.
  Proof.
    introv cor; unfold correct_new_view in cor; smash_pbft.
  Qed.

  Lemma norepeatsb_and_in_map_digest_same_seq_implies_eq :
    forall pp1 d1 pp2 d2 L,
      norepeatsb SeqNumDeq (map pre_prepare2seq L) = true
      -> In (pp1, d1) (map add_digest L)
      -> In (pp2, d2) (map add_digest L)
      -> pre_prepare2seq pp1 = pre_prepare2seq pp2
      -> pp1 = pp2 /\ d1 = d2.
  Proof.
    induction L; introv norep i1 i2 e; simpl in *; tcsp.
    smash_pbft.
    repndors; tcsp.

    - rewrite i1 in i2; ginv.

    - clear IHL.
      match goal with
      | [ H : ~ _ |- _ ] => destruct H
      end.
      unfold add_digest in i2; ginv.
      apply in_map_iff in i1; exrepnd.
      unfold add_digest in i1; ginv.
      allrw <-.
      apply in_map_iff; eexists; eauto.

    - clear IHL.
      match goal with
      | [ H : ~ _ |- _ ] => destruct H
      end.
      unfold add_digest in i1; ginv.
      apply in_map_iff in i2; exrepnd.
      unfold add_digest in i1; ginv.
      allrw <-.
      apply in_map_iff; eexists; eauto.
  Qed.

  Lemma eq_primary_implies_eq_primary :
    forall v i,
      i = PBFTprimary v
      -> is_primary v i = true.
  Proof.
    introv h.
    subst; autorewrite with pbft; auto.
  Qed.
  Hint Resolve eq_primary_implies_eq_primary : pbft.

  Lemma nat_seq_num:
    forall (n : nat) (s : SeqNum),
      n = s -> seq_num n = seq_num s.
  Proof.
    tcsp.
  Qed.
  Hint Resolve nat_seq_num : pbft.

  Lemma in_map_seq_num:
    forall (n A B : SeqNum),
      In n (map seq_num (seq A B))
      -> A <= n <= (A + B).
  Proof.
    introv H.
     apply in_map_iff in H.
    exrepnd.
    apply in_seq in H0.
    rewrite <- H1.
    smash_pbft. omega.
  Qed.
  Hint Resolve in_map_seq_num : pbft.


  Lemma in_map_seq_num_natAB:
    forall n A B,
      In n (map seq_num (seq A B))
      -> A <= n <= (A + B).
  Proof.
    introv H.
    apply in_map_iff in H.
    exrepnd.
    apply in_seq in H0.
    rewrite <- H1.
    smash_pbft. omega.
  Qed.
  Hint Resolve in_map_seq_num_natAB : pbft.

  Lemma max_seq_num_left :
    forall (n n1 n2 : SeqNum), n <= n1 -> n <= max_seq_num n1 n2.
  Proof.
    introv h; destruct n, n1, n2; unfold max_seq_num; simpl in *; smash_pbft.
    allrw SeqNumLe_true; auto; simpl in *; omega.
  Qed.
  Hint Resolve max_seq_num_left : pbft.

  Lemma max_seq_num_right :
    forall (n n1 n2 : SeqNum), n <= n2 -> n <= max_seq_num n1 n2.
  Proof.
    introv h; destruct n1, n2; unfold max_seq_num; simpl in *; smash_pbft.
    allrw SeqNumLe_false; simpl in *; omega.
  Qed.
  Hint Resolve max_seq_num_right : pbft.

  Lemma in_from_min_to_max_op_implies :
    forall n minop maxop,
      In n (from_min_to_max_op minop maxop)
      ->
      exists min max,
        minop = Some min
        /\ maxop = Some max
        /\ min <= max
        /\ min < n
        /\ n <= max.
  Proof.
    introv h; unfold from_min_to_max_op, from_min_to_max in h;
      smash_pbft; repndors; subst; tcsp.

    apply in_map_iff in h; exrepnd; subst.
    apply in_seq in h0.
    rewrite plus_Sn_m in h0; rewrite le_plus_minus_r in h0; smash_pbft.
    eexists; eexists; dands; eauto; try omega.
  Qed.

  Lemma vce_view_changes_replace_own_view_change_in_entry :
    forall vc e,
      vce_view_changes (replace_own_view_change_in_entry vc e)
      = vce_view_changes e.
  Proof.
    destruct e; simpl; auto.
  Qed.
  Hint Rewrite vce_view_changes_replace_own_view_change_in_entry : pbft.

  Lemma view_changed_entry_some_implies_eq_vce_view_changes :
    forall state entry vc entry',
      view_changed_entry state entry = Some (vc, entry')
      -> vce_view_changes entry' = vce_view_changes entry.
  Proof.
    introv h; unfold view_changed_entry in h; smash_pbft.
  Qed.

  Lemma view_changed_entry_some_implies_cons :
    forall state entry vc entry',
      view_changed_entry state entry = Some (vc, entry')
      -> view_change_entry2view_changes entry' = vc :: vce_view_changes entry.
  Proof.
    introv h; unfold view_changed_entry in h; smash_pbft.
    unfold view_change_entry2view_changes.
    destruct entry; simpl in *.
    destruct vce_view_change; simpl in *; ginv.
  Qed.

  Fixpoint max_seq_nums (L : list SeqNum) : SeqNum :=
    match L with
    | [] => seq_num 0
    | s :: sn => max_seq_num s (max_seq_nums sn)
    end.

  Fixpoint ordered {T} (R : T -> T -> bool) (L : list T) : Prop :=
    match L with
    | [] => True
    | x :: xs =>
      (forall a, In a xs -> R x a = true)
      /\ ordered R xs
    end.

  Lemma max_seq_num_assoc :
    forall (a b c : SeqNum),
      max_seq_num a (max_seq_num b c) = max_seq_num (max_seq_num a b) c.
  Proof.
    introv; destruct a, b, c; unfold max_seq_num; smash_pbft;
      allrw SeqNumLe_true;
      allrw SeqNumLe_false; simpl in *; omega.
  Qed.

  Lemma max_seq_num_eq_right :
    forall (a b : SeqNum),
      a < b
      -> max_seq_num a b = b.
  Proof.
    introv h; destruct a, b; unfold max_seq_num; smash_pbft.
    allrw SeqNumLe_false; simpl in *; omega.
  Qed.

  Lemma max_seq_num_eq_left :
    forall (a b : SeqNum),
      b <= a
      -> max_seq_num a b = a.
  Proof.
    introv h; destruct a, b; unfold max_seq_num; smash_pbft.
    allrw SeqNumLe_true; simpl in *.
    assert (n = n0) as xx by omega; subst; auto.
  Qed.

  Lemma max_seq_num_0_right :
    forall (a : SeqNum),
      max_seq_num a 0 = a.
  Proof.
    introv; pose proof (max_seq_num_eq_left a (seq_num 0)) as h.
    apply h; destruct a; simpl in *; omega.
  Qed.
  Hint Rewrite max_seq_num_0_right : pbft.

  Lemma max_seq_nums_right_if_lt :
    forall K a,
      (forall x : SeqNum, In x K -> SeqNumLt a x = true)
      -> K <> []
      -> max_seq_num a (max_seq_nums K) = max_seq_nums K.
  Proof.
    destruct K; introv h w; simpl in *; autorewrite with pbft in *; tcsp.
    pose proof (h s) as q; autodimp q hyp.
    allrw SeqNumLt_true.
    rewrite max_seq_num_assoc.
    rewrite (max_seq_num_eq_right a s); auto.
  Qed.

  Lemma nullb_false_iff :
    forall {T} (L : list T),
      nullb L = false <-> L <> [].
  Proof.
    introv; destruct L; simpl; split; intro q; tcsp.
  Qed.

  Lemma implies_eq_seq_nums :
    forall (s1 s2 : SeqNum), seqnum2nat s1 = seqnum2nat s2 -> s1 = s2.
  Proof.
    introv; destruct s1, s2; simpl in *; tcsp.
  Qed.

  Lemma max_seq_num_diff_left_implies_gt :
    forall (a b : SeqNum),
      max_seq_num a b <> a -> a < b.
  Proof.
    introv h; unfold max_seq_num in *; smash_pbft.
    allrw SeqNumLe_true; simpl in *.
    destruct a as [n], b as [m]; simpl in *.
    assert (n <> m); try omega.
    intro xx; subst; tcsp.
  Qed.

  Lemma diff_nat_implies_diff_seq_num :
    forall (a b : SeqNum),
      seqnum2nat a <> seqnum2nat b -> a <> b.
  Proof.
    introv h; destruct a, b; simpl in *; intro xx; subst; destruct h; tcsp.
    inversion xx; auto.
  Qed.

(*  Lemma exists_find_pre_prepare_certificate_in_prepared_infos :
    forall vc n,
      view_change2max_seq_preps vc = Some n
      ->
      exists ppi,
        find_pre_prepare_certificate_in_prepared_infos
          (view_change2max_seq_preps vc) (view_change2prep vc) = Some ppi.
  Proof.
    introv n0.
    destruct vc, v; simpl.
    unfold view_change2max_seq in *; simpl in *.
    unfold view_change2prep in *; simpl in *.
    induction P; simpl in *; tcsp.
    smash_pbft.

    match goal with
    | [ H : _ <> _ |- _ ] =>
      apply max_seq_num_diff_left_implies_gt in H
    end.
    autodimp IHP hyp.
    { apply diff_nat_implies_diff_seq_num; simpl; omega. }

    rewrite max_seq_num_eq_right; auto.
  Qed.*)

  Lemma create_new_prepare_message_implies_same_sequence_number :
    forall n v keys cert b p d,
      create_new_prepare_message n v keys cert = (b,(p,d))
      -> pre_prepare2seq p = n.
  Proof.
    introv create.
    unfold create_new_prepare_message in create; smash_pbft.
  Qed.

  Lemma create_new_prepare_message_implies_same_view :
    forall n v keys cert b p d,
      create_new_prepare_message n v keys cert = (b,(p,d))
      -> pre_prepare2view p = v.
  Proof.
    introv create.
    unfold create_new_prepare_message in create; smash_pbft.
  Qed.

  Lemma create_new_prepare_message_implies_auth :
    forall n v keys cert b p d,
      create_new_prepare_message n v keys cert = (b,(p,d))
      -> pre_prepare2auth p = authenticate (PBFTmsg_bare_pre_prepare (pre_prepare2bare p)) keys.
  Proof.
    introv create.
    unfold create_new_prepare_message in create; smash_pbft.
  Qed.

  Lemma eqset_cons_lr :
    forall {A} (a : A) l1 l2,
      eqset l1 l2
      -> eqset (a :: l1) (a :: l2).
  Proof.
    introv eqs; introv; split; intro h; simpl in *; repndors; tcsp; right;
      apply eqs; auto.
  Qed.

  Lemma eqset_cons_middle :
    forall {A} (a : A) l1 l2,
      eqset (l1 ++ a :: l2) (a :: l1 ++ l2).
  Proof.
    repeat introv; split; intro h; simpl in *; allrw in_app_iff; simpl in *; tcsp.
  Qed.

  Lemma implies_norepeatsb_middle :
    forall {A} (deq : Deq A) (a : A) l1 l2,
      norepeatsb deq (a :: l1 ++ l2) = true
      -> norepeatsb deq (l1 ++ a :: l2) = true.
  Proof.
    induction l1; introv norep; simpl in *; smash_pbft.

    - allrw in_app_iff; simpl in *.
      repeat match goal with
             | [ H : ~ (_ \/ _) |- _ ] => apply not_or in H; repnd
             end.
      repndors; tcsp.

    - allrw in_app_iff; simpl in *.
      repeat match goal with
             | [ H : ~ (_ \/ _) |- _ ] => apply not_or in H; repnd
             end.
      repndors; tcsp.
      apply IHl1; smash_pbft.
      allrw in_app_iff; tcsp.
  Qed.

  Lemma create_new_prepare_messages_implies_eqset_and_norepeatsb :
    forall sns v keys cert OP NP,
      norepeatsb SeqNumDeq sns = true
      -> create_new_prepare_messages sns v keys cert = (OP, NP)
      -> eqset sns (map pre_prepare2seq (map fst OP ++ map fst NP))
         /\ norepeatsb SeqNumDeq (map pre_prepare2seq (map fst OP ++ map fst NP)) = true.
  Proof.
    induction sns; introv norep create; simpl in *; smash_pbft; repnd; simpl in *.

    - assert False; tcsp.

      match goal with
      | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
        eapply IHsns in H; auto;[]; repnd
      end.

      match goal with
      | [ H : create_new_prepare_message _ _ _ _ = _ |- _ ] =>
        apply create_new_prepare_message_implies_same_sequence_number in H;
          rewrite H in *
      end.

      match goal with
      | [ H1 : In _ ?x, H2 : eqset _ ?x |- _ ] => apply H2 in H1; tcsp
      end.

    - match goal with
      | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
        eapply IHsns in H; auto;[]; repnd
      end.

      match goal with
      | [ H : create_new_prepare_message _ _ _ _ = _ |- _ ] =>
        dup H as create;
          apply create_new_prepare_message_implies_same_sequence_number in create;
          rewrite create in *
      end.

      dands; tcsp.
      apply eqset_cons_lr; auto.

    - match goal with
      | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
        eapply IHsns in H; auto;[]; repnd
      end.

      match goal with
      | [ H : create_new_prepare_message _ _ _ _ = _ |- _ ] =>
        dup H as create;
          apply create_new_prepare_message_implies_same_sequence_number in create
      end.

      allrw map_app; simpl in *.

      rewrite create.
      dands.

      + eapply eqset_trans;[apply eqset_cons_lr;eauto|].
        apply eqset_sym; apply eqset_cons_middle.

      + apply implies_norepeatsb_middle; auto.
        simpl; smash_pbft.

        match goal with
        | [ H1 : In _ ?x, H2 : eqset _ ?x |- _ ] => apply H2 in H1; tcsp
        end.
  Qed.

  Lemma create_new_prepare_messages_implies_norepeatsb :
    forall sns v keys cert OP NP,
      norepeatsb SeqNumDeq sns = true
      -> create_new_prepare_messages sns v keys cert = (OP, NP)
      -> norepeatsb SeqNumDeq (map pre_prepare2seq (map fst OP ++ map fst NP)) = true.
  Proof.
    introv norep create.
    eapply create_new_prepare_messages_implies_eqset_and_norepeatsb in create; eauto; tcsp.
  Qed.
  Hint Resolve create_new_prepare_messages_implies_norepeatsb : pbft.

  Lemma implies_norepeatsb_map_seq_num :
    forall l,
      norepeatsb deq_nat l = true
      -> norepeatsb SeqNumDeq (map seq_num l) = true.
  Proof.
    induction l; introv norep; simpl in *; smash_pbft.
    apply in_map_iff in i; exrepnd; subst.
    inversion i1; simpl in *; subst; GC; tcsp.
  Qed.
  Hint Resolve implies_norepeatsb_map_seq_num : pbft.

  Lemma norepeatsb_seq :
    forall len pos,
      norepeatsb deq_nat (seq pos len) = true.
  Proof.
    induction len; introv; simpl in *; smash_pbft.
    apply in_seq in i; omega.
  Qed.
  Hint Resolve norepeatsb_seq : pbft.

  Lemma norepeatsb_from_min_to_max :
    forall a b, norepeatsb SeqNumDeq (from_min_to_max a b) = true.
  Proof.
    introv; unfold from_min_to_max; smash_pbft; simpl in *.
  Qed.
  Hint Resolve norepeatsb_from_min_to_max : pbft.

  Lemma norepeatsb_from_min_to_max_op :
    forall a b, norepeatsb SeqNumDeq (from_min_to_max_op a b) = true.
  Proof.
    introv; unfold from_min_to_max_op; smash_pbft.
  Qed.
  Hint Resolve norepeatsb_from_min_to_max_op : pbft.

  Lemma norepeatsb_from_min_to_max_of_view_changes :
    forall entry,
      norepeatsb SeqNumDeq (from_min_to_max_of_view_changes entry) = true.
  Proof.
    introv; unfold from_min_to_max_of_view_changes, from_min_to_max_of_view_changes_cert; smash_pbft.
  Qed.
  Hint Resolve norepeatsb_from_min_to_max_of_view_changes : pbft.

  Lemma pre_prepare2seq_mk_auth_pre_prepare :
    forall v sn rs keys,
      pre_prepare2seq (mk_auth_pre_prepare v sn rs keys) = sn.
  Proof.
    sp.
  Qed.
  Hint Rewrite pre_prepare2seq_mk_auth_pre_prepare : pbft.

  Lemma implies_le_max_seq_nums :
    forall (n : SeqNum) (L : list SeqNum),
      In n L
      -> n <= max_seq_nums L.
  Proof.
    induction L; introv i; simpl in *; tcsp.
    repndors; subst; simpl in *; tcsp; eauto 2 with pbft.
    autodimp IHL hyp.
    eauto 2 with pbft.
  Qed.

  (*Lemma implies_create_new_prepare_message_cons_true :
    forall n v keys c C ppd,
      create_new_prepare_message n v keys C = (true, ppd)
      -> exists ppd1, create_new_prepare_message n v keys (c :: C) = (true, ppd1).
  Proof.
    introv h.
    unfold create_new_prepare_message in *; simpl in *.
    unfold find_request_info_in_view_change_cert in *; simpl in *.
    smash_pbft.
  Qed.
  Hint Resolve implies_create_new_prepare_message_cons_true : pbft.*)

(*  Lemma PreparedInfos2max_seq_implies_find_pre_prepare_certificate_in_prepared_infos_some :
    forall L n,
      PreparedInfos2max_seq L = Some n
      -> exists x, find_pre_prepare_certificate_in_prepared_infos n L = Some x.
  Proof.
    induction L; introv h; simpl in *; smash_pbft.
  Qed.*)

(*  Lemma view_change2max_seq_preps_some_implies_create_new_prepare_message_true :
    forall vc n v keys C,
      view_change2max_seq_preps vc = Some n
      -> exists ppd, create_new_prepare_message n v keys (vc :: C) = (true, ppd).
  Proof.
    introv h; unfold view_change2max_seq_preps in h.
    unfold create_new_prepare_message; simpl.
    unfold find_request_info_in_view_change_cert; simpl.
    smash_pbft.
    assert False; tcsp.
  Qed.*)

  Lemma PreparedInfos2max_seq_some_implies_ex :
    forall F L n,
      PreparedInfos2max_seq F L = Some n
      -> exists p, In p L /\ n = prepared_info2seq p /\ F p = true.
  Proof.
    induction L; introv h; simpl in *; ginv.
    remember (PreparedInfos2max_seq F L) as m; symmetry in Heqm; destruct m.

    - pose proof (IHL s) as q; autodimp q hyp; clear IHL; exrepnd; simpl in *.
      unfold max_seq_num in *; smash_pbft; allrw SeqNumLe_true; allrw SeqNumLe_false.

      + exists p; dands; tcsp.

      + exists a; dands; tcsp.

      + exists p; dands; tcsp.

    - clear IHL; simpl in *; smash_pbft.
      exists a; dands; tcsp.
  Qed.

  Lemma view_change_cert2max_seq_preps_some_implies :
    forall F C n vc,
      view_change_cert2max_seq_preps_vc F C = Some (n,vc)
      -> In vc C
         /\
         exists p,
           In p (view_change2prep vc)
           /\ n = prepared_info2seq p
           /\ F p = true.
  Proof.
    induction C; introv h; simpl in *; ginv; simpl in *; tcsp.
    smash_pbft; allrw SeqNumLt_true; allrw SeqNumLt_false.

    - pose proof (IHC n vc) as q; autodimp q hyp; clear IHC; repnd; tcsp.

    - dands; tcsp.
      apply PreparedInfos2max_seq_some_implies_ex; auto.

    - dands; tcsp.
      apply PreparedInfos2max_seq_some_implies_ex; auto.

    - pose proof (IHC n vc) as q; clear IHC; autodimp q hyp; dands; tcsp.
  Qed.

  (*Lemma implies_pre_prepare_certificate_in_prepared_infos_some :
    forall p L,
      In p L
      ->
      exists x,
        find_pre_prepare_certificate_in_prepared_infos (prepared_info2seq p) L = Some x.
  Proof.
    induction L; introv i; simpl in *; tcsp.
    repndors; subst; smash_pbft.
  Qed.*)

(*  Lemma implies_in_view_change2prep_implies_create_new_prepare_message_true :
    forall vc p v keys C,
      In vc C
      -> In p (view_change2prep vc)
      -> exists ppd, create_new_prepare_message (prepared_info2seq p) v keys C = (true, ppd).
  Proof.
    induction C; introv i j; simpl in *; tcsp.
    repndors; subst; tcsp.

    - unfold create_new_prepare_message; simpl.
      unfold find_request_info_in_view_change_cert; simpl.
      smash_pbft.

      apply implies_pre_prepare_certificate_in_prepared_infos_some in j; exrepnd.
      allrw j0; ginv.

    - repeat (autodimp IHC hyp); exrepnd.
      unfold create_new_prepare_message in *; simpl in *.
      unfold find_request_info_in_view_change_cert in *; simpl in *.
      smash_pbft.
  Qed.*)

(*  Lemma view_change_cert2max_seq_preps_vc_implies_exists_or_zero :
    forall v keys C n vc,
      view_change_cert2max_seq_preps_vc C = Some (n,vc)
      -> exists ppd, create_new_prepare_message n v keys C = (true, ppd).
  Proof.
    introv cert.
    apply view_change_cert2max_seq_preps_some_implies in cert.
    exrepnd.
    subst.
    eapply implies_in_view_change2prep_implies_create_new_prepare_message_true; eauto.
  Qed.*)

(*  Lemma view_change_cert2max_seq_preps_implies_exists_or_zero :
    forall v keys C n,
      view_change_cert2max_seq_preps C = Some n
      -> exists ppd, create_new_prepare_message n v keys C = (true, ppd).
  Proof.
    introv cert.
    unfold view_change_cert2max_seq_preps in cert; smash_pbft.
    eapply view_change_cert2max_seq_preps_vc_implies_exists_or_zero; eauto.
  Qed.*)

(*  Lemma view_change_cert2max_seq_preps_and_create_new_prepare_messages_implies_le :
    forall K sn v keys C OP NP,
      view_change_cert2max_seq_preps C = Some sn
      -> create_new_prepare_messages K v keys C = (OP, NP)
      -> ordered SeqNumLt K
      -> sn = max_seq_nums K
      -> K <> []
      -> sn <= max_O OP.
  Proof.
    induction K; introv h q ord w knn; simpl in *; ginv.
    smash_pbft; repnd.

    - remember (nullb K) as b; symmetry in Heqb.
      destruct b.

      + rewrite nullb_true_iff in Heqb; subst; simpl in *; ginv; simpl in *; GC.
        clear ord knn.
        autorewrite with pbft in *.

        match goal with
        | [ H : create_new_prepare_message _ _ _ _ = _ |- _ ] =>
          apply create_new_prepare_message_implies in H; exrepnd; subst; simpl; auto
        end.

      + apply nullb_false_iff in Heqb.
        eapply IHK in h;[|eauto| | |]; auto; eauto 2 with pbft.
        apply max_seq_nums_right_if_lt; auto.

    - remember (nullb K) as b; symmetry in Heqb.
      destruct b.

      + rewrite nullb_true_iff in Heqb; subst; simpl in *; ginv; simpl in *; GC.
        clear ord knn.
        autorewrite with pbft in *.

        apply (view_change_cert2max_seq_preps_implies_exists_or_zero v keys) in h.
        repndors; subst; tcsp;[].
        exrepnd.
        rewrite h0 in *; ginv.

      + apply nullb_false_iff in Heqb.
        eapply IHK in h;[|eauto| | |]; auto; eauto 2 with pbft.
        apply max_seq_nums_right_if_lt; auto.
  Qed.*)

(*  Lemma pre_prepares2max_seq_OP_of_create_new_prepare_messages :
    forall L v keys C sn ovc OP NP,
      view_change_cert2max_seq C = (sn, ovc)
      -> sn = max_seq_nums L
      -> ordered SeqNumLt L
      -> L <> []
      -> create_new_prepare_messages L v keys C = (OP, NP)
      -> forall n, In n L -> n <= pre_prepares2max_seq (map fst OP).
  Proof.
    introv vmax eqsn ord diff create i.
    eapply view_change_cert2max_seq_and_create_new_prepare_messages_implies_le in create;
      [|eauto|eauto| |]; auto.
    rewrite <- max_O_as_pre_prepares2max_seq.
    eapply le_trans;[|eauto].
    subst.
    apply implies_le_max_seq_nums; auto.
  Qed.*)

  Lemma implies_ordered_map_seq_num :
    forall (L : list nat),
      ordered Nat.ltb L
      -> ordered SeqNumLt (map seq_num L).
  Proof.
    induction L; simpl in *; introv h; auto.
    repnd.
    dands; auto.
    introv i.
    apply in_map_iff in i; exrepnd; subst.
    apply SeqNumLt_true.
    apply h0 in i0; pbft_simplifier; auto.
  Qed.

  Lemma ordered_seq :
    forall (len n : nat),
      ordered Nat.ltb (seq n len).
  Proof.
    induction len; simpl; auto.
    introv; dands; auto.
    introv i.
    apply Nat.ltb_lt; auto.
    apply in_seq in i; tcsp.
  Qed.
  Hint Resolve ordered_seq : num.

(*  Lemma le_seq_num_implies_from_min_to_max_not_null :
    forall (sn1 sn2 : SeqNum),
      sn1 < sn2
      -> from_min_to_max sn1 sn2 <> [].
  Proof.
    introv d.
    unfold from_min_to_max; smash_pbft; try omega; tcsp.

  Qed.
  Hint Resolve le_seq_num_implies_from_min_to_max_not_null : pbft.*)

  Lemma in_list_implies_diff_nil :
    forall {A} (l : list A) a,
      In a l -> l <> [].
  Proof.
    introv i; destruct l; simpl in *; tcsp.
  Qed.
  Hint Resolve in_list_implies_diff_nil : pbft.

  Lemma ordered_from_min_to_max :
    forall (sn1 sn2 : SeqNum),
      ordered SeqNumLt (from_min_to_max sn1 sn2).
  Proof.
    introv; unfold from_min_to_max; smash_pbft.
    apply implies_ordered_map_seq_num; eauto 3 with num.
  Qed.
  Hint Resolve ordered_from_min_to_max : pbft.

  Lemma ordered_from_min_to_max_op :
    forall (sn1 sn2 : option SeqNum),
      ordered SeqNumLt (from_min_to_max_op sn1 sn2).
  Proof.
    introv; unfold from_min_to_max_op; smash_pbft.
  Qed.
  Hint Resolve ordered_from_min_to_max_op : pbft.

  Lemma max_seq_nums_map_seq_num_seq :
    forall (len n : nat),
      0 < len
      -> max_seq_nums (map seq_num (seq (S n) len)) = len + n.
  Proof.
    induction len; introv h; simpl; autorewrite with pbft; auto; try omega.
    simpl in *.
    destruct (lt_dec 0 len) as [d|d].
    { rewrite IHlen; auto.
      rewrite max_seq_num_eq_right; auto; simpl; try omega. }
    { assert (len = 0) by omega; subst; simpl in *; autorewrite with pbft; auto. }
  Qed.

  Lemma max_seq_nums_from_min_to_max :
    forall (sn1 sn2 : SeqNum),
      sn1 < sn2
      -> max_seq_nums (from_min_to_max sn1 sn2) = sn2.
  Proof.
    Opaque seq.
    introv h; unfold from_min_to_max; smash_pbft; try omega.
    rewrite max_seq_nums_map_seq_num_seq; simpl in *; try omega.
    rewrite Nat.sub_add; simpl; auto.
    destruct sn2; simpl; auto.
  Qed.

  Lemma in_from_min_to_max_implies_lt :
    forall n (min max : SeqNum),
      In n (from_min_to_max min max)
      -> min < max.
  Proof.
    introv i; unfold from_min_to_max in i; smash_pbft.
    apply in_map_iff in i; exrepnd; subst.
    apply in_seq in i0.
    omega.
  Qed.
  Hint Resolve in_from_min_to_max_implies_lt : pbft.

(*  Lemma view_changed_entry_some_and_check_broadcast_new_view_implies_le :
    forall n entry vc i keys nv opreps npreps,
      In n (from_min_to_max_of_view_changes entry)
      -> view_changed_entry (vce_view entry) entry = Some vc
      -> check_broadcast_new_view i keys entry = Some (nv, opreps, npreps)
      -> n <= max_O opreps.
  Proof.
    introv k vce c.
    unfold check_broadcast_new_view in c; smash_pbft.
    unfold from_min_to_max_of_view_changes in *; smash_pbft.

    applydup in_from_min_to_max_op_implies in k; exrepnd.
    eapply le_trans;[eauto|].

    match goal with
    | [ H : view_changed_entry _ _ = _ |- _ ] =>
      applydup view_changed_entry_some_implies_cons in H as eqvcs;
        rewrite eqvcs in *
    end.

    match goal with
    | [ H : context[vce_view_changes ?e] |- _ ] =>
      remember (vce_view_changes e) as VCS
    end.

    match goal with
    | [ H : context[view_change_cert2max_seq ?a] |- _ ] =>
      remember (view_change_cert2max_seq a) as sn1
    end.

    subst.
    allrw k1.
    allrw k2.
    simpl in *.

    match goal with
    | [ H : create_new_prepare_messages _ _ _ _ = _ |- _ ] =>
      eapply view_change_cert2max_seq_preps_and_create_new_prepare_messages_implies_le in H;
        [|eauto| | |]; auto; allrw; simpl; eauto 2 with pbft;[]
    end.

    rewrite max_seq_nums_from_min_to_max; eauto 2 with pbft.
  Qed.*)

  Lemma next_seq_not_le :
    forall (sn : SeqNum),
      next_seq sn <= sn -> False.
  Proof.
    introv h; destruct sn; unfold next_seq in h; simpl in *; omega.
  Qed.

  Lemma pre_prepare_in_map_correct_new_view_implies :
    forall v n rs a d nv,
      In (mk_pre_prepare v n rs a, d) (map add_digest (new_view2oprep nv ++ new_view2nprep nv))
      -> correct_new_view nv = true
      -> new_view2view nv = v.
  Proof.
    introv i cor.
    unfold correct_new_view in cor; smash_pbft.
    destruct nv, v0; simpl in *.
    allrw forallb_forall.
    allrw in_map_iff; exrepnd.
    unfold add_digest in *; ginv.
    allrw in_app_iff; repndors.

    - match goal with
      | [ H : context[forall _ : _, In _ OP -> _], H' : In _ OP |- _ ] =>
        apply H in H'; clear H
      end.
      unfold correct_new_view_opre_prepare_op in *; smash_pbft.
      unfold correct_new_view_opre_prepare in *; smash_pbft.

    - match goal with
      | [ H : context[forall _ : _, In _ NP -> _], H' : In _ NP |- _ ] =>
        apply H in H'; clear H
      end.
      unfold correct_new_view_npre_prepare_op in *; smash_pbft.
      unfold correct_new_view_npre_prepare in *; smash_pbft.
  Qed.

  Lemma new_view2sender_eq_primary :
    forall nv, new_view2sender nv = PBFTprimary (new_view2view nv).
  Proof.
    destruct nv, v; simpl; auto.
  Qed.
  Hint Resolve new_view2sender_eq_primary : pbft.

  Lemma nexists_last_prepared_true_implies :
    forall pp P,
      nexists_last_prepared pp P = true
      ->
      exists nfo,
        In nfo P
        /\ pre_prepare2seq pp = prepared_info2seq nfo
        /\ valid_prepared_info P nfo = true.
  Proof.
    introv h; unfold nexists_last_prepared in h.
    apply existsb_exists in h; exrepnd; smash_pbft.
    exists x; tcsp.
  Qed.

  Lemma last_prepared_info_app_true :
    forall nfo l1 l2,
      last_prepared_info nfo (l1 ++ l2)
      = last_prepared_info nfo l1 && last_prepared_info nfo l2.
  Proof.
    induction l1; introv; simpl; auto.
    smash_pbft; try (rewrite IHl1); auto;
      try (complete (rewrite andb_assoc; auto)).
  Qed.

  Lemma create_new_prepare_messages_view_change_cert2max_seq_none_implies :
    forall entry view keys OP NP,
      create_new_prepare_messages
        (from_min_to_max_of_view_changes entry)
        view keys
        (view_change_cert2prep (view_change_entry2view_changes entry)) = (OP, NP)
      -> view_change_cert2max_seq (view_change_entry2view_changes entry) = None
      -> OP = []
         /\ NP = []
         /\ from_min_to_max_of_view_changes entry = [].
  Proof.
    introv h q.
    unfold from_min_to_max_of_view_changes, from_min_to_max_of_view_changes_cert in *.
    rewrite q in *; simpl in *; ginv.
  Qed.

  Lemma in_from_min_to_max_of_view_changes_implies_lt_min :
    forall entry min n,
      view_change_cert2max_seq (view_change_entry2view_changes entry) = Some min
      -> In n (from_min_to_max_of_view_changes entry)
      -> min < n.
  Proof.
    introv h i.
    apply in_from_min_to_max_op_implies in i; exrepnd.
    rewrite h in *; ginv.
  Qed.
  Hint Resolve in_from_min_to_max_of_view_changes_implies_lt_min : pbft.

  Lemma implies_length_view_change_entry2view_changes :
    forall entry n,
      is_some (vce_view_change entry) = true
      -> n = length (vce_view_changes entry)
      -> n + 1 = length (view_change_entry2view_changes entry).
  Proof.
    introv h q; destruct entry; simpl in *.
    destruct vce_view_change; simpl in *; ginv; omega.
  Qed.

  Lemma oexists_last_prepared_false_implies :
    forall pp d P,
      oexists_last_prepared pp d P = false
      ->
      forall nfo,
        In nfo P
        -> pre_prepare2seq pp <> prepared_info2seq nfo
           \/  d <> prepared_info2digest nfo
           \/ valid_prepared_info P nfo = false.
  Proof.
    introv h i; unfold oexists_last_prepared in h.
    rewrite existsb_false in h.
    apply h in i; smash_pbft.
  Qed.

  Lemma max_O_in :
    forall L,
      L <> []
      ->
      exists pp d,
        max_O L = pre_prepare2seq pp
        /\ In (pp,d) L.
  Proof.
    induction L; intro h; tcsp; repnd; simpl in *.
    clear h.
    destruct L; simpl in *; tcsp.

    - clear IHL.
      autorewrite with pbft.
      eexists; dands; eauto.

    - autodimp IHL hyp; tcsp;[].
      exrepnd.
      repndors; ginv; tcsp;
        allrw;
        unfold max_seq_num; simpl; smash_pbft;
          eexists; eexists; dands; eauto.
  Qed.

  Lemma false_implies_in_create_new_prepare_messages_n_pre_prepare :
    forall n ppd L view keys C OP NP,
      create_new_prepare_messages L view keys C = (OP, NP)
      -> In n L
      -> create_new_prepare_message n view keys C = (false, ppd)
      -> In ppd NP.
  Proof.
    induction L; introv creates i create; simpl in *; smash_pbft.

    - repndors; subst; tcsp.

      + rewrite create in *; ginv.

      + eapply IHL; eauto.

    - repndors; subst; tcsp.

      + rewrite create in *; ginv.

      + right; eapply IHL; eauto.
  Qed.

  Lemma create_new_prepare_message_true_implies_oprep_not_nil :
    forall L view keys C OP NP n ppd,
      create_new_prepare_messages L view keys C = (OP, NP)
      -> In n L
      -> create_new_prepare_message n view keys C = (true,ppd)
      -> In ppd OP.
  Proof.
    induction L; introv creates i create; simpl in *; tcsp.
    smash_pbft; repndors; subst; tcsp.

    - rewrite create in *; ginv.

    - right; eapply IHL; eauto.

    - rewrite create in *; ginv.

    - eapply IHL; eauto.
  Qed.

  Lemma seq_num_seqnum2nat :
    forall (n : SeqNum), seq_num (seqnum2nat n) = n.
  Proof.
    destruct n; simpl; auto.
  Qed.
  Hint Rewrite seq_num_seqnum2nat : pbft.

  Lemma implies_max_in_from_min_to_max :
    forall n min max,
      In n (from_min_to_max min max)
      -> In max (from_min_to_max min max).
  Proof.
    unfold from_min_to_max; introv h; smash_pbft; simpl in *.
    allrw in_map_iff; exrepnd; subst.
    exists max; dands; simpl in *; autorewrite with pbft in *; auto.
    allrw in_seq; omega.
  Qed.
  Hint Resolve implies_max_in_from_min_to_max : pbft.

  Lemma norepeatsb_pre_prepare2seq_oprep_nprep_implies :
    forall (OP NP : list (Pre_prepare * PBFTdigest)) pp1 d1 pp2 d2,
      norepeatsb SeqNumDeq (map pre_prepare2seq (map fst OP ++ map fst NP)) = true
      -> pre_prepare2seq pp1 = pre_prepare2seq pp2
      -> In (pp1, d1) NP
      -> In (pp2, d2) OP
      -> False.
  Proof.
    introv norep e i1 i2.
    apply norepeatsb_as_no_repeats in norep.
    rewrite map_app in norep.
    apply no_repeats_app in norep; repnd.

    apply (norep (pre_prepare2seq pp1)); apply in_map_iff.

    - exists pp2; dands; auto.
      apply in_map_iff; eexists; dands; eauto; simpl; auto.

    - exists pp1; dands; auto.
      apply in_map_iff; eexists; dands; eauto; simpl; auto.
  Qed.

(*  Lemma find_pre_prepare_certificate_in_prepared_infos_none_implies :
    forall sn L,
      find_pre_prepare_certificate_in_prepared_infos sn L = None
      -> ~ In sn (map prepared_info2seq L).
  Proof.
    induction L; introv i j; simpl in *; tcsp.
    smash_pbft.
    repndors; subst; tcsp.
  Qed.*)

(*  Lemma find_pre_prepare_certificate_in_view_change_cert_none_implies :
    forall sn C,
      find_pre_prepare_certificate_in_view_change_cert sn C = None
      -> ~ In sn (map prepared_info2seq (view_change_cert2prep C)).
  Proof.
    induction C; introv h i; simpl in *; tcsp.
    allrw map_app.
    allrw in_app_iff.
    smash_pbft.
    autodimp IHC hyp.
    repndors; tcsp.

    match goal with
    | [ H : find_pre_prepare_certificate_in_prepared_infos _ _ = _ |- _ ] =>
      apply find_pre_prepare_certificate_in_prepared_infos_none_implies in H
    end; tcsp.
  Qed.*)

(*  Lemma implies_find_pre_prepare_certificate_in_view_change_cert_some :
    forall sn C nfo,
      In nfo (view_change_cert2prep C)
      -> sn = prepared_info2seq nfo
      -> last_prepared_info nfo (view_change_cert2prep C) = true
      -> exists nfo', find_pre_prepare_certificate_in_view_change_cert sn C = Some nfo'.
  Proof.
    induction C; introv i h q; simpl in *; tcsp.
    allrw in_app_iff.
    allrw last_prepared_info_app_true.
    allrw andb_true; repnd.
    repndors; tcsp; smash_pbft.

    - unfold pick_prepared_info_with_highest_view; smash_pbft.
  Qed.*)

(*  Lemma find_pre_prepare_certificate_in_view_change_cert_none_implies_nexists_last_prepared_none :
    forall sn vcs v rs keys,
      find_pre_prepare_certificate_in_view_change_cert sn vcs = None
      -> nexists_last_prepared
           (mk_auth_pre_prepare v sn rs keys)
           (view_change_cert2prep vcs) = false.
  Proof.
    introv h.
    match goal with
    | [ |- ?a = _ ] => remember a as b; destruct b; auto; symmetry in Heqb
    end.

    assert False; tcsp.
    apply nexists_last_prepared_true_implies in Heqb; exrepnd; simpl in *.

    Check find_pre_prepare_certificate_in_view_change_cert.

    apply find_pre_prepare_certificate_in_view_change_cert_none_implies in h.
    destruct h.
    apply in_map_iff.
    exists nfo; dands; auto.
  Qed.*)

(*  Lemma create_new_prepare_message_false_implies_correct :
    forall (sn : SeqNum) v keys vcs pp d (n max : SeqNum),
      n < sn
      -> sn < max
      -> create_new_prepare_message sn v keys vcs = (false,(pp,d))
      -> correct_new_view_npre_prepare v n max (view_change_cert2prep vcs) pp = true.
  Proof.
    introv ltsn ltmax create.
    unfold create_new_prepare_message in create; smash_pbft.
    unfold find_request_info_in_view_change_cert in *; smash_pbft.

    unfold correct_new_view_npre_prepare; simpl; smash_pbft;
      allrw SeqNumLt_true; allrw SeqNumLt_false; simpl in *; try omega; GC.

    apply negb_true_iff.
    apply find_pre_prepare_certificate_in_view_change_cert_none_implies_nexists_last_prepared_none; auto.
  Qed.*)

(*  Lemma create_new_prepare_messages_implies_correct_NPs :
    forall n max sns v keys vcs OP NP,
      (forall (x : SeqNum) ppd,
          In x sns
          -> create_new_prepare_message x v keys vcs = (false, ppd)
          -> n < x /\ x < max)
      -> create_new_prepare_messages sns v keys vcs = (OP, NP)
      -> forallb
           (correct_new_view_npre_prepare v n max (view_change_cert2prep vcs))
           (map fst NP) = true.
  Proof.
    induction sns; introv imp create; simpl in *; smash_pbft; dands; tcsp;
      try (complete (eapply IHsns; eauto)).
    repnd; simpl in *.

    pose proof (imp a (x0,x1)) as q.
    autodimp q hyp.

    eapply create_new_prepare_message_false_implies_correct;[| |eauto];tcsp.
  Qed.*)

  (*Lemma find_pre_prepare_certificate_in_view_change_cert_some_implies :
    forall sn L nfo,
      find_pre_prepare_certificate_in_view_change_cert sn L = Some nfo
      -> In nfo (view_change_cert2prep L)
         /\ sn = prepared_info2seq nfo
         /\ last_prepared_info nfo (view_change_cert2prep L) = true.
  Proof.
    induction L; introv i; simpl in *; tcsp.
    smash_pbft.

    - pose proof (IHL x0) as q; autodimp q hyp; repnd; clear IHL.

      unfold pick_prepared_info_with_highest_view; smash_pbft.

      + rewrite in_app_iff; dands; tcsp.
        rewrite last_prepared_info_app_true.
        apply andb_true_iff; dands; auto;[].

  Qed.*)

  (*Lemma find_pre_prepare_certificate_in_view_change_cert_some_implies_oexists_last_prepared_true :
    forall sn vcs v keys nfo,
      find_pre_prepare_certificate_in_view_change_cert sn vcs = Some nfo
      -> oexists_last_prepared
           (mk_auth_pre_prepare v sn (prepared_info2requests nfo) keys)
           (create_hash_messages (map PBFTrequest (prepared_info2requests nfo)))
           (view_change_cert2prep vcs) = true.
  Proof.
    introv h.
    match goal with
    | [ |- ?a = _ ] => remember a as b; destruct b; auto; symmetry in Heqb
    end.

    assert False; tcsp.

    match goal with
    | [ H : oexists_last_prepared ?a ?b ?c = _ |- _ ] =>
      pose proof (oexists_last_prepared_false_implies a b c H) as q; clear H; simpl in q
    end.



XXXXXX

    apply find_pre_prepare_certificate_in_view_change_cert_none_implies in h.
    apply nexists_last_prepared_true_implies in Heqb; exrepnd; simpl in *.
    destruct h.
    apply in_map_iff.
    exists nfo; dands; auto.
  Qed.*)

  (*Lemma create_new_prepare_message_true_implies_correct :
    forall (sn : SeqNum) v keys vcs pp d (n : SeqNum),
      n < sn
      -> create_new_prepare_message sn v keys vcs = (true,(pp,d))
      -> correct_new_view_opre_prepare v n (view_change_cert2prep vcs) pp = true.
  Proof.
    introv ltsn create.
    unfold create_new_prepare_message in create; smash_pbft.
    unfold find_request_info_in_view_change_cert in *; smash_pbft.

    unfold correct_new_view_opre_prepare; simpl; smash_pbft;
      allrw SeqNumLt_true; allrw SeqNumLt_false; simpl in *; try omega; GC.

    apply find_pre_prepare_certificate_in_view_change_cert_none_implies_nexists_last_prepared_none; auto.
  Qed.*)

  (*Lemma create_new_prepare_messages_implies_correct_OPs :
    forall n max sns v keys vcs OP NP,
      (forall (x : SeqNum) ppd,
          In x sns
          -> create_new_prepare_message x v keys vcs = (true, ppd)
          -> n < x)
      -> create_new_prepare_messages sns v keys vcs = (OP, NP)
      -> forallb
           (correct_new_view_npre_prepare v n max (view_change_cert2prep vcs))
           (map fst OP) = true.
  Proof.
    induction sns; introv imp create; simpl in *; smash_pbft; dands; tcsp;
      try (complete (eapply IHsns; eauto)).
    repnd; simpl in *.

    pose proof (imp a (x2,x1)) as q.
    autodimp q hyp.

    eapply create_new_prepare_message_implies_correct;[| |eauto];tcsp.
  Qed.*)

  Lemma find_pre_prepare_certificate_in_prepared_infos_none_implies :
    forall F n P,
      find_pre_prepare_certificate_in_prepared_infos F n P = None
      ->
      forall p, In p P -> n <> prepared_info2seq p \/ F p = false.
  Proof.
    induction P; introv find; simpl in *; tcsp.
    introv i; repndors; subst; tcsp; smash_pbft.
  Qed.

  Lemma create_new_prepare_message_false_implies_correct :
    forall (sn : SeqNum) v keys P pp d (n max : SeqNum),
      n < sn
      -> sn < max
      -> create_new_prepare_message sn v keys P = (false,(pp,d))
      -> correct_new_view_npre_prepare v n max P pp = true.
  Proof.
    introv ltsn ltmax create.
    unfold create_new_prepare_message in create; smash_pbft.

    unfold correct_new_view_npre_prepare; simpl; smash_pbft;
      allrw SeqNumLt_true; allrw SeqNumLt_false; simpl in *; try omega; GC.

    unfold nexists_last_prepared; simpl.
    apply existsb_false.
    introv i.
    smash_pbft;[].

    unfold valid_prepared_info.

    apply andb_false_iff.
    match goal with
    | [ |- _ \/ ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    match goal with
    | [ |- ?x = _ \/ _ ] => remember x as c; symmetry in Heqc; destruct c; auto
    end.
    assert False; tcsp.

    eapply find_pre_prepare_certificate_in_prepared_infos_none_implies in i;[|eauto].
    repndors; tcsp.

    unfold valid_prepared_info in i.
    rewrite andb_false_iff in i; repndors; smash_pbft.
  Qed.

  Lemma create_new_prepare_messages_implies_correct_NPs :
    forall n max sns v keys P OP NP,
      (forall (x : SeqNum) ppd,
          In x sns
          -> create_new_prepare_message x v keys P = (false, ppd)
          -> n < x /\ x < max)
      -> create_new_prepare_messages sns v keys P = (OP, NP)
      -> forallb
           (correct_new_view_npre_prepare v n max P)
           (map fst NP) = true.
  Proof.
    induction sns; introv imp create; simpl in *; smash_pbft; dands; tcsp;
      try (complete (eapply IHsns; eauto)).
    repnd; simpl in *.

    pose proof (imp a (x0,x1)) as q.
    repeat (autodimp q hyp).
    eapply create_new_prepare_message_false_implies_correct;[| |eauto]; tcsp.
  Qed.

  Lemma implies_in_view_change_cert2prep :
    forall vc p C,
      In vc C
      -> In p (view_change2prep vc)
      -> In p (view_change_cert2prep C).
  Proof.
    induction C; introv i j; simpl in *; tcsp; repndors; subst; tcsp;
      allrw in_app_iff; tcsp.
  Qed.
  Hint Resolve implies_in_view_change_cert2prep : pbft.

  Lemma view_change_cert2max_seq_preps_vc_implies_exists_create_new_prepare_message :
    forall v keys C n vc,
      view_change_cert2max_seq_preps_vc (valid_prepared_info (view_change_cert2prep C)) C = Some (n,vc)
      -> exists ppd, create_new_prepare_message n v keys (view_change_cert2prep C) = (true, ppd).
  Proof.
    introv cert.
    apply view_change_cert2max_seq_preps_some_implies in cert.
    exrepnd.
    subst.
    unfold create_new_prepare_message; smash_pbft.

    assert False; tcsp.

    match goal with
    | [ H : find_pre_prepare_certificate_in_prepared_infos _ _ _ = _ |- _ ] =>
      eapply find_pre_prepare_certificate_in_prepared_infos_none_implies in H;
        [|eauto 2 with pbft]
    end.
    repndors; smash_pbft.
  Qed.

  Lemma view_change_cert2max_seq_preps_implies_exists_create_new_prepare_message :
    forall v keys C n,
      view_change_cert2max_seq_preps (valid_prepared_info (view_change_cert2prep C)) C = Some n
      -> exists ppd, create_new_prepare_message n v keys (view_change_cert2prep C) = (true, ppd).
  Proof.
    introv cert.
    unfold view_change_cert2max_seq_preps in cert; smash_pbft.
    eapply view_change_cert2max_seq_preps_vc_implies_exists_create_new_prepare_message; eauto.
  Qed.

  Lemma view_change_cert2max_seq_preps_and_create_new_prepare_messages_implies_le :
    forall K sn v keys C OP NP,
      view_change_cert2max_seq_preps (valid_prepared_info (view_change_cert2prep C)) C = Some sn
      -> create_new_prepare_messages K v keys (view_change_cert2prep C) = (OP, NP)
      -> ordered SeqNumLt K
      -> sn = max_seq_nums K
      -> K <> []
      -> sn <= max_O OP.
  Proof.
    induction K; introv h q ord w knn; simpl in *; ginv.
    smash_pbft; repnd.

    - remember (nullb K) as b; symmetry in Heqb.
      destruct b.

      + rewrite nullb_true_iff in Heqb; subst; simpl in *; ginv; simpl in *; GC.
        clear ord knn.
        autorewrite with pbft in *.

        match goal with
        | [ H : create_new_prepare_message _ _ _ _ = _ |- _ ] =>
          apply create_new_prepare_message_implies_same_sequence_number in H;subst;auto
        end.

      + apply nullb_false_iff in Heqb.
        eapply IHK in h;[|eauto| | |]; auto; eauto 2 with pbft.
        apply max_seq_nums_right_if_lt; auto.

    - remember (nullb K) as b; symmetry in Heqb.
      destruct b.

      + rewrite nullb_true_iff in Heqb; subst; simpl in *; ginv; simpl in *; GC.
        clear ord knn.
        autorewrite with pbft in *.
        apply (view_change_cert2max_seq_preps_implies_exists_create_new_prepare_message v keys) in h.
        exrepnd.
        rewrite h0 in *; ginv.

      + apply nullb_false_iff in Heqb.
        eapply IHK in h;[|eauto| | |]; auto; eauto 2 with pbft.
        apply max_seq_nums_right_if_lt; auto.
  Qed.

  Lemma view_changed_entry_some_and_check_broadcast_new_view_implies_le :
    forall n entry state vc entry' i nv  opreps npreps,
      In n (from_min_to_max_of_view_changes entry')
      -> view_changed_entry state entry = Some (vc, entry')
      -> check_broadcast_new_view i state entry = Some (nv, entry', opreps, npreps)
      -> n <= max_O opreps.
  Proof.
    introv k vce c.
    unfold check_broadcast_new_view in c; smash_pbft.
    unfold from_min_to_max_of_view_changes, from_min_to_max_of_view_changes_cert in *; smash_pbft.

    applydup in_from_min_to_max_op_implies in k; exrepnd.
    eapply le_trans;[eauto|].

    match goal with
    | [ H : view_changed_entry _ _ = _ |- _ ] =>
      applydup view_changed_entry_some_implies_cons in H as eqvcs;
        rewrite eqvcs in *
    end.

    match goal with
    | [ H : context[vce_view_changes ?e] |- _ ] =>
      remember (vce_view_changes e) as VCS
    end.

    match goal with
    | [ H : context[view_change_cert2max_seq ?a] |- _ ] =>
      remember (view_change_cert2max_seq a) as sn1
    end.

    subst.
    allrw k1.
    allrw k2.
    simpl in *.

    rename_hyp_with create_new_prepare_messages cr.
    eapply (view_change_cert2max_seq_preps_and_create_new_prepare_messages_implies_le
              _ _ _ _ (vc :: _)) in cr;
        [|simpl;eauto| | |]; auto; allrw; simpl; eauto 2 with pbft;[].
    rewrite max_seq_nums_from_min_to_max; eauto 2 with pbft; omega.
  Qed.

  Lemma create_new_prepare_messages_preserves_view :
    forall L v keys P OP NP pp d,
      create_new_prepare_messages L v keys P = (OP, NP)
      -> In (pp,d) (OP ++ NP)
      -> v = pre_prepare2view pp.
  Proof.
    induction L; introv create i; simpl in *; smash_pbft; simpl in *; tcsp.

    - repndors; subst; simpl in *; tcsp.

      + symmetry; eapply create_new_prepare_message_implies_same_view; eauto.

      + eapply IHL; eauto.

    - allrw in_app_iff; simpl in *; repndors; subst; tcsp.

      + eapply IHL;[eauto|]; apply in_app_iff; eauto.

      + symmetry; eapply create_new_prepare_message_implies_same_view; eauto.

      + eapply IHL;[eauto|]; apply in_app_iff; eauto.
  Qed.
  Hint Resolve create_new_prepare_messages_preserves_view : pbft.

  Lemma check_broadcast_new_view_preserves_view :
    forall i state entry nv entry' OP NP pp d,
      check_broadcast_new_view i state entry = Some (nv, entry', OP, NP)
      -> In (pp, d) (OP ++ NP)
      -> new_view2view nv = pre_prepare2view pp.
  Proof.
    introv check k.
    unfold check_broadcast_new_view in check; smash_pbft.
  Qed.
  Hint Resolve check_broadcast_new_view_preserves_view : pbft.

  Lemma pre_prepare_in_map_correct_new_view_implies2 :
    forall p nv,
      In p (map add_digest (new_view2oprep nv ++ new_view2nprep nv))
      -> correct_new_view nv = true
      -> new_view2view nv = pre_prepare2view (fst p).
  Proof.
    introv i cor.
    destruct p, p, b.
    eapply pre_prepare_in_map_correct_new_view_implies in i; simpl; auto.
  Qed.

End PBFTprops3.


Hint Resolve eq_primary_implies_eq_primary : pbft.
Hint Resolve nat_seq_num : pbft.
Hint Resolve in_map_seq_num : pbft.
Hint Resolve in_map_seq_num_natAB : pbft.
Hint Resolve max_seq_num_left : pbft.
Hint Resolve max_seq_num_right : pbft.
Hint Resolve ordered_seq : num.
Hint Resolve in_list_implies_diff_nil : pbft.
(*Hint Resolve le_seq_num_implies_from_min_to_max_not_null : pbft.*)
Hint Resolve ordered_from_min_to_max : pbft.
Hint Resolve ordered_from_min_to_max_op : pbft.
Hint Resolve new_view2sender_eq_primary : pbft.
Hint Resolve create_new_prepare_messages_implies_norepeatsb : pbft.
Hint Resolve implies_norepeatsb_map_seq_num : pbft.
Hint Resolve norepeatsb_seq : pbft.
Hint Resolve norepeatsb_from_min_to_max : pbft.
Hint Resolve norepeatsb_from_min_to_max_of_view_changes : pbft.
Hint Resolve implies_in_view_change_cert2prep : pbft.
Hint Resolve in_from_min_to_max_of_view_changes_implies_lt_min : pbft.
Hint Resolve implies_max_in_from_min_to_max : pbft.
Hint Resolve create_new_prepare_messages_preserves_view : pbft.
Hint Resolve check_broadcast_new_view_preserves_view : pbft.


Hint Rewrite @request_data_and_rep_toks2prepare_as_pre_prepare2prepare : pbft.
Hint Rewrite @is_primary_PBFTprimary : pbft.
Hint Rewrite @eq_request_data_same : pbft.
Hint Rewrite @orb_false_r : bool.
Hint Rewrite @max_seq_num_0_right : pbft.
Hint Rewrite @pre_prepare2seq_mk_auth_pre_prepare : pbft.
Hint Rewrite @seq_num_seqnum2nat : pbft.
Hint Rewrite @vce_view_changes_replace_own_view_change_in_entry : pbft.
