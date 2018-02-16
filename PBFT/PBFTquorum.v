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


Require Export PBFTprops3.
Require Export PBFTat_most_f_byz.


Section PBFTquorum.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.

  Lemma length_reps : length reps = 3 * F + 1.
  Proof.
    exact length_nodes.
  Qed.

  Lemma rep_list_le :
    forall (l : list Rep),
      no_repeats l
      -> length l <= 3 * F + 1.
  Proof.
    introv norep.
    pose proof (num_nodes_list_le (MkNRlist _ l norep)) as h; simpl in *; auto.
  Qed.

  Lemma num_nodes_gt_2fp1 :
    2 * F + 1 <= num_nodes.
  Proof.
    unfold num_nodes. simpl in *. unfold num_replicas. try omega.
  Qed.
  Hint Resolve num_nodes_gt_2fp1 : pbft.

  Lemma num_nodes_lt_4fp2 :
    num_nodes < 2 * (2 * F + 1).
  Proof.
    unfold num_nodes. simpl in *. unfold num_replicas. try omega.
  Qed.
  Hint Resolve num_nodes_lt_4fp2 : pbft.

  Lemma length_l_fp1 :
    forall (l : list node_type),
      2 * (2 * F + 1) - num_nodes <= length l
      ->  F + 1 <= length l.
  Proof.
    introv h; unfold num_nodes in *; simpl in *; unfold num_replicas in *; try omega.
  Qed.
  Hint Resolve length_l_fp1 : pbft.

  Lemma two_quorums :
    forall (l1 l2 : list Rep),
      no_repeats l1
      -> no_repeats l2
      -> 2 * F + 1 <= length l1
      -> 2 * F + 1 <= length l2
      -> exists l,
          F + 1 <= length l
          /\ no_repeats l
          /\ subset l l1
          /\ subset l l2.
  Proof.
    introv norep1 norep2 len1 len2.
    pose proof (overlapping_quorums_same_size (MkNRlist _ l1 norep1) (MkNRlist _ l2 norep2) (2*F+1)) as q.
    repeat (autodimp q hyp);[].

    exrepnd.
    exists l; dands; auto; tcsp. smash_pbft.
  Qed.

  Inductive Prepare_like :=
  | prepare_like_pre_prepare (pp : Pre_prepare)
  | prepare_like_prepare (p : Prepare).

  Definition prepare_like2sender (p : Prepare_like) : Rep :=
    match p with
    | prepare_like_pre_prepare pp => pre_prepare2sender pp
    | prepare_like_prepare p => prepare2sender p
    end.

  Definition prepare_like_in_prepared_info (p : Prepare_like) (nfo : PreparedInfo) :=
    match p with
    | prepare_like_pre_prepare pp => pp = prepared_info_pre_prepare nfo
    | prepare_like_prepare p => In p (prepared_info_prepares nfo)
    end.

  Lemma pre_prepare2sender_prepared_info_pre_prepare_prepared_info2pp_sender :
    forall nfo,
      pre_prepare2sender (prepared_info_pre_prepare nfo)
      = prepared_info2pp_sender nfo.
  Proof.
    introv; destruct nfo; simpl; auto.
  Qed.
  Hint Rewrite pre_prepare2sender_prepared_info_pre_prepare_prepared_info2pp_sender : pbft.

  Hint Rewrite map_map : list.

  Lemma length_prepared_info2senders_eq_length_prepared_info_prepares :
    forall nfo,
      length (prepared_info2senders nfo)
      = length (prepared_info_prepares nfo).
  Proof.
    introv; unfold prepared_info2senders; autorewrite with list; auto.
  Qed.

  Lemma map_prepare_like2sender_prepare_like_prepare :
    forall l,
      map (fun x => prepare_like2sender (prepare_like_prepare x)) l
      = map (fun x => prepare2sender x) l.
  Proof.
    introv; apply map_ext; introv.
    destruct a; simpl; auto.
  Qed.
  Hint Rewrite map_prepare_like2sender_prepare_like_prepare : pbft.

  Lemma map_prepare2sender_prepared_info_prepares :
    forall nfo,
      map prepare2sender (prepared_info_prepares nfo)
      = prepared_info2senders nfo.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite map_prepare2sender_prepared_info_prepares : pbft.

  Lemma info_is_prepared2list :
    forall nfo,
      info_is_prepared nfo = true
      ->
      exists (L : list Prepare_like),
        no_repeats (map prepare_like2sender L)
        /\ (2 * F) + 1 <= length L
        /\ forall p, In p L -> prepare_like_in_prepared_info p nfo.
  Proof.
    introv isprep.
    unfold info_is_prepared in isprep; smash_pbft.
    exists ((prepare_like_pre_prepare (prepared_info_pre_prepare nfo))
              :: map prepare_like_prepare (prepared_info_prepares nfo)).

    simpl; autorewrite with pbft list; dands; auto;
      [|rewrite <- length_prepared_info2senders_eq_length_prepared_info_prepares;
        try omega|];[|].

    - constructor; eauto 2 with list.
      intro i.
      allrw forallb_forall.
      discover; smash_pbft.

    - introv h; repndors; subst; simpl in *; auto.
      allrw in_map_iff; exrepnd; subst; simpl in *; auto.
  Qed.

  Lemma in_remove_iff :
    forall {A} (dec : Deq A) x a l,
      In x (remove dec a l) <-> (In x l /\ x <> a).
  Proof.
    induction l; introv; simpl; split; intro h; tcsp;
      smash_pbft; repndors; subst; tcsp;
        try (complete (apply IHl in h; repnd; tcsp));
        try (complete (apply IHl; tcsp)).
    right; apply IHl; tcsp.
  Qed.

(*  Lemma there_is_one_good_guy :
    forall (eo : EventOrdering) (L : list Rep),
      no_repeats L
      -> F + 1 <= length L
      -> PBFT_at_most_f_byz1 eo
      -> exists (good : Rep),
          In good L
          /\ node_has_correct_trace eo good.
  Proof.
    introv norep lell byz.
    unfold PBFT_at_most_f_byz1 in byz.
    exrepnd.

    pose proof (member_of_larger_list2 rep_deq L faulty) as q.
    repeat (autodimp q hyp); try omega.
    destruct q as [Good q]; repnd.
    exists Good.
    dands; auto.
    introv i.
    apply byz0.
    intro j.
    rewrite in_map_iff in j; exrepnd.
    rewrite i in j1; ginv.
  Qed.*)

  Lemma there_is_one_good_guy_before :
    forall (eo : EventOrdering) (L : list Rep) (E : list Event),
      no_repeats L
      -> F + 1 <= length L
      -> exists_at_most_f_faulty E F
      -> exists (good : Rep),
          In good L
          /\ forall e, In e E -> node_has_correct_trace_before e good.
  Proof.
    introv norep lell byz.
    pose proof (there_is_one_correct_before eo L E F) as q.
    repeat (autodimp q hyp).
  Qed.

(*  Lemma select_good_guys :
    forall (eo : EventOrdering) (L : list Rep),
      no_repeats L
      -> PBFT_at_most_f_byz1 eo
      -> exists (G : list Rep),
          subset G L
          /\ length L - F <= length G
          /\ no_repeats G
          /\ nodes_have_correct_traces eo G.
  Proof.
    introv norep byz.
    unfold PBFT_at_most_f_byz1 in byz.
    exrepnd.

    pose proof (members_of_larger_list rep_deq L faulty) as q.
    repeat (autodimp q hyp); try omega;[].

    destruct q as [G q]; repnd.
    exists G.
    dands; auto; try omega;[].

    introv i j.
    allrw in_map_iff; exrepnd; subst.
    apply (byz0 e); intro k.
    rewrite in_map_iff in k; exrepnd.
    rewrite j in *; ginv; tcsp.
    apply q1 in k0; tcsp.
  Qed.*)

  Lemma num_nodes_gt_fp1 :
    F + 1 <= num_nodes.
  Proof.
    unfold num_nodes. simpl in *. unfold num_replicas. try omega.
  Qed.
  Hint Resolve num_nodes_gt_fp1 : pbft.

  Lemma num_nodes_mf1_gt_2fp1 :
    num_nodes - (F + 1) < 2 * F + 1.
  Proof.
    unfold num_nodes. simpl in *. unfold num_replicas. try omega.
  Qed.
  Hint Resolve num_nodes_mf1_gt_2fp1 : pbft.

(*  Lemma two_quorums_f_and_2f :
    forall (l1 l2 : list Rep),
      no_repeats l1
      -> no_repeats l2
      -> F + 1 <= length l1
      -> 2 * F + 1 <= length l2
      -> exists good,
          1 <= length good
          /\ no_repeats good
          /\ subset good l1
          /\ subset good l2.
  Proof.
    introv norep1 norep2 len1 len2.

    pose proof (QUORUM_diff_size (MkNRlist _ l1 norep1) (MkNRlist _ l2 norep2) (F+1) (2*F+1)) as q.
    repeat (autodimp q hyp); smash_pbft.
  Qed.*)

  Lemma two_quorums_one :
    forall (l1 l2 : list Rep),
      no_repeats l1
      -> no_repeats l2
      -> 2 * F + 1 <= length l1
      -> F + 1 <= length l2
      -> exists x,
          In x l1
          /\ In x l2.
  Proof.
    introv norep1 norep2 len1 len2.
    pose proof (overlapping_quorums_different_sizes (MkNRlist _ l2 norep2) (MkNRlist _ l1 norep1) (F+1) (2*F+1)) as q.
    repeat (autodimp q hyp); smash_pbft.
    exrepnd.
    destruct good as [|G]; simpl in *; try omega;[].
    exists G; dands; eauto 3 with list.
  Qed.

End PBFTquorum.


Hint Resolve num_nodes_gt_2fp1 : pbft.
Hint Resolve num_nodes_lt_4fp2 : pbft.
Hint Resolve length_l_fp1 : pbft.
Hint Resolve num_nodes_gt_fp1 : pbft.
Hint Resolve num_nodes_mf1_gt_2fp1 : pbft.


Hint Rewrite @map_map : list.


Hint Rewrite @pre_prepare2sender_prepared_info_pre_prepare_prepared_info2pp_sender : pbft.
Hint Rewrite @map_prepare_like2sender_prepare_like_prepare : pbft.
Hint Rewrite @map_prepare2sender_prepared_info_prepares : pbft.
