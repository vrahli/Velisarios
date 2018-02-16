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


Require Export generic_tactics.
Require Export list_util1.


Section Quorum.

  Context { pn  : @Node }.

  Definition nat_n (n : nat) : Set := {m : nat | m <? n = true}.

  Record bijective {A B} (f : A -> B) :=
    {
      bij_inv : B -> A;
      bij_id1 : forall x : A, bij_inv (f x) = x;
      bij_id2 : forall y : B, f (bij_inv y) = y;
    }.
  Arguments bij_inv [A] [B] [f] _ _.

  Lemma nat_n_deq: forall n, Deq (nat_n n).
  Proof.
    introv; introv.
    destruct x as [n1 p1], y as [n2 p2].
    destruct (deq_nat n1 n2);[left|right].

    - subst.
      f_equal.
      apply UIP_dec.
      apply bool_dec.

    - introv xx; inversion xx; tcsp.
  Defined.

  Definition injective {A B} (F : A -> B) :=
    forall n m, F n = F m -> n = m.

  Class Quorum_context :=
    MkQuorumContext
      {
        node_type     : Set;
        num_nodes     : nat;
        node_deq      : Deq node_type;
        node2nat      : node_type -> nat_n num_nodes;
        node_bij      : bijective node2nat;
        node2name     : node_type -> name;
        node2name_inj : injective node2name;
      }.

  Context { quorum_context : Quorum_context }.

  Definition mk_nat_n {x n : nat} (p : x < n) : nat_n n :=
    exist _ x (leb_correct _ _ p).

  Definition nodes : list node_type :=
    mapin
      (seq 0 num_nodes)
      (fun n i => bij_inv node_bij (mk_nat_n (seq_0_lt i))).

  Lemma nodes_no_repeats : no_repeats nodes.
  Proof.
    apply no_repeats_mapin; eauto 3 with list.
    introv d.
    assert (node2nat (bij_inv node_bij (mk_nat_n (seq_0_lt i)))
            = node2nat (bij_inv node_bij (mk_nat_n (seq_0_lt j))))
      as h by (allrw; auto).
    repeat rewrite (bij_id2 _ node_bij) in h.
    clear d.
    unfold mk_nat_n in h.
    inversion h; auto.
  Qed.

  Lemma length_nodes : length nodes = num_nodes.
  Proof.
    introv; unfold nodes; autorewrite with list; auto.
  Qed.

  Lemma nodes_prop : forall (x : node_type), In x nodes.
  Proof.
    introv.
    unfold nodes.
    apply in_mapin.

    remember (node2nat x) as nx.
    destruct nx as [nx condnx].

    pose proof (leb_complete _ _ condnx) as c.

    assert (In nx (seq O num_nodes)) as i.
    { apply in_seq; omega. }

    exists nx i; simpl.

    unfold mk_nat_n.
    unfold bij_inv.
    destruct node_bij.
    pose proof (bij_id3 x) as h.
    rewrite <- Heqnx in h; subst; simpl.

    f_equal; f_equal.
    apply UIP_dec; apply bool_dec.
  Qed.

  Lemma num_nodes_list_le :
    forall (l : NRlist node_type), length l <= num_nodes.
  Proof.
    introv.
    apply (le_trans _ (length nodes));[|rewrite length_nodes;auto].

    assert (subset l nodes) as ss.
    { introv j; apply nodes_prop. }

    pose proof (no_repeats_implies_remove_repeats_eq node_deq l (nrl_no_repeats _ l)) as e.

    apply (subset_implies_eq_length_remove_repeats node_deq) in ss.
    rewrite e in ss.
    eapply le_trans;[exact ss|].
    eauto with list.
  Qed.

  Lemma overlapping_quorums :
    forall (l1 l2 : NRlist node_type) n m,
      n <= length l1
      -> m <= length l2
      -> exists good,
          (n + m) - num_nodes <= length good
          /\ no_repeats good
          /\ subset good l1
          /\ subset good l2.
  Proof.
    introv len1 len2.

    exists (keep node_deq l1 l2).
    dands; eauto 3 with list;[].

    destruct (le_lt_dec ((n + m) - num_nodes) (length (keep node_deq l1 l2))) as [d|d]; auto.
    assert False; tcsp.

    assert (no_repeats (remove_repeats node_deq (l1 ++ l2))) as nr by eauto 3 with list.

    pose proof (num_nodes_list_le (MkNRlist _ (remove_repeats node_deq (l1 ++ l2)) nr)) as q.
    simpl in *.
    rewrite remove_repeats_app in q.
    rewrite app_length in q.
    rewrite (no_repeats_implies_remove_repeats_eq _ l2) in q; auto; eauto 3 with list.
    rewrite (no_repeats_implies_remove_repeats_eq _ l1) in q; auto; eauto 3 with list.

    pose proof (split_length_as_keep_remove_list node_deq l1 l2) as w; try omega.
  Qed.

  Lemma overlapping_quorums_same_size :
    forall (l1 l2 : NRlist node_type) n,
      n <= length l1
      -> n <= length l2
      -> exists l,
          (2 * n) - num_nodes <= length l
          /\ no_repeats l
          /\ subset l l1
          /\ subset l l2.
  Proof.
    introv len1 len2.

    assert (n + n = 2 * n) as eqn by omega.

    pose proof (overlapping_quorums l1 l2 n n) as q.
    rewrite eqn in q.
    repeat (autodimp q hyp); try omega.
  Qed.

  Lemma overlapping_quorums_different_sizes :
    forall (l1 l2 : NRlist node_type) n m,
      num_nodes - n < m
      -> n <= length l1
      -> m <= length l2
      -> exists good,
          1 <= length good
          /\ no_repeats good
          /\ subset good l1
          /\ subset good l2.
  Proof.
    introv cond len1 len2.
    pose proof (overlapping_quorums l1 l2 n m) as q.
    repeat (autodimp q hyp).
    exrepnd.
    exists good; dands; auto; try omega.
  Qed.

End Quorum.


Arguments bij_inv [A] [B] [f] _ _.
