(*

  Copyright 2016 University of Luxembourg

  This file is part of our formalization of Platzer's
    "A Complete Uniform Substitution Calculus for Differential Dynamic Logic"
  available here: http://arxiv.org/pdf/1601.06183.pdf (July 27, 2016).
  We refer to this formalization as DdlCoq here.

  DdlCoq is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  DdlCoq is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with DdlCoq.  If not, see <http://www.gnu.org/licenses/>.

  authors:
    Vincent Rahli
    Marcus Völp
    Ivana Vukotic

 *)


Require Export Coq.Lists.List.
Export List.ListNotations.
Require Export tactics2.
Require Export tactics_util.
Require Export Omega.


Hint Rewrite app_nil_r : core.

(** subset of two lists *)
Definition subset {T} (l1 l2 : list T) :=
  forall v, List.In v l1 -> List.In v l2.

(** nil is subset of any lists *)
Lemma subset_nil_l :
  forall {T} (l : list T), subset [] l.
Proof.
  repeat introv; simpl; tcsp.
Qed.
Hint Resolve subset_nil_l : core.

(** nil is subset of any list *)
Lemma subset_nil_l_iff :
  forall {T} (l : list T), subset [] l <-> True.
Proof.
  introv; split; intro h; auto.
Qed.
Hint Rewrite @subset_nil_l_iff : core.

(** iff some list is subset of list l2,
than head of that list is subset of l2
and the tail of that list is also subset of l2 *)
Lemma subset_cons_l :
  forall {T} v (l1 l2 : list T),
    subset (v :: l1) l2 <-> (List.In v l2 /\ subset l1 l2).
Proof.
  repeat introv; unfold subset; simpl; split; intro h; dands; tcsp.
  introv q; repndors; subst; tcsp.
Qed.
Hint Rewrite @subset_cons_l : core.

(** reflexivity for subsets of lists *)
Lemma subset_refl : forall {T} (l : list T), subset l l.
Proof.
  introv i; auto.
Qed.
Hint Resolve subset_refl : core.

Inductive sublist {A} : list A -> list A -> Prop :=
| sublist_nil : forall l, sublist [] l
| sublist_in  : forall v l1 l2, sublist l1 l2 -> sublist (v :: l1) (v :: l2)
| sublist_out : forall v l1 l2, sublist l1 l2 -> sublist l1 (v :: l2).
Hint Constructors sublist.

Lemma sublist_nil_r :
  forall T (l : list T), sublist l [] <-> l = [].
Proof.
  destruct l; split; intro h; auto; ginv.
  inversion h.
Qed.

Lemma sublist_app_r_weak :
  forall {T} (l l1 l2 : list T),
    sublist l l2
    -> sublist l (l1 ++ l2).
Proof.
  induction l1; simpl; auto.
Qed.

Lemma sublist_cons_l :
  forall T v (l1 l2 : list T),
    sublist (v :: l1) l2
    <-> exists la lb, l2 = la ++ (v :: lb) /\ sublist l1 lb.
Proof.
  induction l2; introv; split; intro h; exrepnd; subst; auto.

  { inversion h. }

  { destruct la; simpl in *; ginv. }

  { inversion h as [|? ? ? ss|? ? ? ss]; subst; clear h.

    { exists (@nil T) l2; dands; auto. }

    { apply IHl2 in ss; clear IHl2; auto; exrepnd; subst.
      exists (a :: la) lb; dands; auto. }
  }

  { destruct la; simpl in *; ginv.

    { apply sublist_in; auto. }

    { apply sublist_out.
      apply IHl2.
      exists la lb; dands; auto. }
  }
Qed.

Lemma sublist_app_l :
  forall T (l l1 l2 : list T),
    sublist (l1 ++ l2) l
    <-> exists la lb, l = la ++ lb /\ sublist l1 la /\ sublist l2 lb.
Proof.
  induction l; split; intro h; exrepnd; subst; simpl in *; tcsp.

  { apply sublist_nil_r in h.
    apply app_eq_nil in h; repnd; subst.
    exists (@nil T) (@nil T); dands; auto. }

  { symmetry in h0.
    apply app_eq_nil in h0; repnd; subst.
    apply sublist_nil_r in h1.
    apply sublist_nil_r in h2.
    subst; simpl; auto. }

  { inversion h as [? e|? ? ? ss|? ? ? ss]; subst.

    { symmetry in e.
      apply app_eq_nil in e; repnd; subst; simpl in *.
      exists (a :: l) (@nil T); autorewrite with core; simpl; dands; auto. }

    { destruct l1; simpl in *; ginv.

      { destruct l2; ginv.
        exists (@nil T) (t :: l); simpl; dands; auto. }

      { apply IHl in ss; exrepnd; subst.
        exists (t :: la) lb; dands; auto. }
    }

    { apply IHl in ss; exrepnd; subst.
      exists (a :: la) lb; dands; auto. }
  }

  { destruct la; simpl in *; ginv.

    { destruct lb; ginv.
      apply sublist_nil_r in h2; subst; simpl; auto. }

    { inversion h2; subst; simpl in *; auto.

      { apply sublist_out.
        apply sublist_app_r_weak; auto. }

      { apply sublist_in.
        apply IHl.
        exists la lb; dands; auto. }

      { apply sublist_out.
        apply IHl.
        exists la lb; dands; auto. }
    }
  }
Qed.

(** [sublist] is reflexive  *)
Lemma sublist_refl : forall {T} (l : list T), sublist l l.
Proof.
  induction l; auto.
Qed.

(** [sublist] is transitive *)
Lemma sublist_trans :
  forall {T} (l1 l2 l3 : list T),
    sublist l1 l2 -> sublist l2 l3 -> sublist l1 l3.
Proof.
  induction l1; introv ss1 ss2; auto.
  rewrite sublist_cons_l in *; exrepnd; subst.
  apply sublist_app_l in ss2; exrepnd.
  apply sublist_cons_l in ss2; exrepnd; subst.
  exists (la0 ++ la1) lb1; dands; auto.

  { rewrite app_assoc; auto. }

  { eapply IHl1; eauto. }
Qed.

Lemma sublist_cons_r :
  forall T v (l1 l2 : list T),
    sublist l1 (v :: l2)
    <->
    (
      l1 = []
      \/
      (exists l, l1 = v :: l /\ sublist l l2)
      \/
      sublist l1 l2
    ).
Proof.
  induction l1; introv; split; intro h; repndors; exrepnd; subst; auto; ginv.

  { inversion h as [|? ? ? ss|? ? ? ss]; subst; clear h; tcsp.
    right; left.
    exists l1; dands; auto. }

  { constructor; auto. }
Qed.

(** disjoint for two lists *)
Definition disjoint {T} (l1 l2 : list T) :=
  forall v, List.In v l1 -> not (List.In v l2).

(** nil is disjoint with any list *)
Lemma disjoint_nil_l :
  forall {T} (l : list T), disjoint [] l.
Proof.
  repeat introv; simpl; tcsp.
Qed.
Hint Resolve disjoint_nil_l : core.
(** nil is disjoint with any list *)
Lemma disjoint_nil_l_iff :
  forall {T} (l : list T), disjoint [] l <-> True.
Proof.
  introv; split; intro h; auto.
Qed.
Hint Rewrite @disjoint_nil_l_iff : core.

(** if l1 is disjoint with l2, then l2 is disjoint with l2 *)
Lemma disjoint_sym_impl :
  forall {T} (l1 l2 : list T),
    disjoint l1 l2 -> disjoint l2 l1.
Proof.
  unfold disjoint; introv ss h1 h2.
  apply_in_hyp p; sp.
Qed.

(** symmetry fro disjoint *)
Lemma disjoint_sym :
  forall {T} (l1 l2 : list T),
    disjoint l1 l2 <-> disjoint l2 l1.
Proof.
  introv; split; introv ss i j;
    apply disjoint_sym_impl in ss; apply ss in i; sp.
Qed.

(** if l2 is disjoint with some list,
then l2 is disjoint with head of that list, as well as with the tail of that list *)
Lemma disjoint_cons_l :
  forall {T} v (l1 l2 : list T),
    disjoint (v :: l1) l2 <-> ((not (List.In v l2)) /\ disjoint l1 l2).
Proof.
  repeat introv; unfold disjoint; simpl; split; introv h1; dands;
    try (apply h1; complete sp); introv h2;
      try (complete (apply h1; sp)).
  repnd; repndors; intro h; repndors; subst; tcsp.
  apply h1 in h2; sp.
Qed.
Hint Rewrite @disjoint_cons_l : core.

Lemma disjoint_cons_r :
  forall (T : Type) (v : T) (l1 l2 : list T),
    disjoint l1 (v :: l2) <-> disjoint l1 l2 /\ ~ In v l1.
Proof.
  introv; split; intro h; repnd; dands; auto.
  { introv i j; apply h in i; simpl in i; tcsp. }
  { intro i; apply h in i; simpl in i; tcsp. }
  { introv i j; simpl in j; repndors; subst; tcsp.
    apply h0 in i; tcsp. }
Qed.

Lemma list_ind_len :
  forall (A : Type) (P : list A -> Prop),
    (forall l, (forall k, (List.length k < List.length l)%nat -> P k) -> P l) ->
    forall l, P l.
Proof.
  introv imp; introv.
  remember (List.length l) as n.
  revert imp l Heqn.
  induction n as [m ind] using comp_ind_type; introv imp e; subst.
  destruct l.

  { apply imp; simpl; tcsp. }

  { apply imp; simpl; introv h.
    apply (ind (List.length k)); simpl; auto. }
Qed.

Fixpoint snoc {X} (l:list X) (v:X) : list X :=
  match l with
  | []     => [v]
  | h :: t => h :: (snoc t v)
  end.

Lemma last_snoc :
  forall {T} (l : list T) v w,
    last (snoc l v) w = v.
Proof.
  induction l; simpl; introv; auto.
  rewrite IHl.
  destruct l; simpl; auto.
Qed.
Hint Rewrite @last_snoc : core.

Lemma removelast_snoc :
  forall {T} (l : list T) v, removelast (snoc l v) = l.
Proof.
  induction l; introv; simpl; auto.
  rewrite IHl.
  destruct l; simpl; auto.
Qed.
Hint Rewrite @removelast_snoc : core.

Lemma snoc_cases :
  forall {T} (l : list T),
    l = [] [+] {a : T $ {k : list T $ l = snoc k a}}.
Proof.
  induction l; tcsp.
  repndors; exrepnd; subst; tcsp; right.
  { exists a ([] : list T); simpl; auto. }
  { exists a0 (a :: k); simpl; auto. }
Qed.

Lemma length_snoc :
  forall T (n : T) (l : list T),
    length (snoc l n) = S (length l).
Proof.
  induction l; simpl; sp.
Qed.
Hint Rewrite length_snoc : core.

Lemma list_ind_snoc :
  forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall (a : A) (l : list A), P l -> P (snoc l a)) ->
    forall l : list A, P l.
Proof.
  introv B I; introv.
  assert ({n : nat $ length l = n}) as p by (exists (length l); auto).
  destruct p as [n e].
  revert l e.
  induction n; intros.
  { destruct l; allsimpl; ginv;auto. }
  destruct (snoc_cases l) as [h|h]; exrepnd; subst; auto.
  allrw length_snoc; ginv.
  apply I; auto.
Qed.

Lemma in_snoc :
  forall {T} (a b : T) l,
    In a (snoc l b) <-> (In a l \/ a = b).
Proof.
  induction l; simpl; split; intro h; repndors; tcsp.

  { apply IHl in h; repndors; tcsp. }

  { right; apply IHl; tcsp. }

  { subst; right; apply IHl; tcsp. }
Qed.

Lemma disjoint_snoc_r :
  forall {T} (a : T) l1 l2,
    disjoint l1 (snoc l2 a)
    <-> (disjoint l1 l2 /\ ~ In a l1).
Proof.
  introv; split; intro h; repnd; dands.

  { introv i j; apply h in i; destruct i; apply in_snoc; tcsp. }

  { intro i; apply h in i; destruct i; apply in_snoc; tcsp. }

  { introv i j; apply in_snoc in j; repndors; subst; tcsp.
    apply h0 in i; tcsp. }
Qed.

Lemma app_snoc :
  forall {T} (a : T) l1 l2,
    (l1 ++ snoc l2 a)%list = snoc (l1 ++ l2) a.
Proof.
  induction l1; introv; simpl; auto.
  rewrite IHl1; auto.
Qed.

Lemma sublist_in_implies :
  forall {T} (l1 l2 : list T) v,
    sublist l1 l2 -> In v l1 -> In v l2.
Proof.
  introv sl.
  induction sl; introv i; simpl in *; tcsp.
Qed.

Fixpoint remove_elt {T} (dec : Deq T) z (l : list T) : list T :=
  match l with
  | [] => []
  | x :: xs =>
    if dec z x
    then remove_elt dec z xs
    else x :: remove_elt dec z xs
  end.

(** equality of two lists *)
Definition eqset {T} (l1 l2 : list T) :=
  forall x, List.In x l1 <-> List.In x l2.

(** reflexivity for equality on two lists *)
Lemma eqset_refl :
  forall {T} (l : list T), eqset l l.
Proof.
  introv; introv; sp.
Qed.
Hint Resolve eqset_refl : core.

(** transitivity for equality on two lists *)
Lemma eqset_trans :
  forall {T} (l1 l2 l3 : list T),
    eqset l1 l2
    -> eqset l2 l3
    -> eqset l1 l3.
Proof.
  introv eqs1 eqs2; introv.
  rewrite (eqs1 x).
  rewrite <- (eqs2 x); sp.
Qed.

(** if first two elements in list can change orders *)
Lemma eqset_cons_swap :
  forall {T} a b (l : list T),
    eqset (a :: b :: l) (b :: a :: l).
Proof.
  introv; introv; simpl.
  repeat (rewrite <- or_assoc).
  rewrite (or_comm (a = x) (b = x)); sp.
Qed.

(*used in definition of interpretation of teta prime*)
(** Removes duplicates from list **)
Fixpoint remove_duplicates {T} (dec : Deq T) (l : list T) : list T :=
  match l with
  | [] => []
  | x::xs =>
    if in_dec dec x xs
    then remove_duplicates dec xs
    else x :: remove_duplicates dec xs
  end.

(** remove duplicate from the list *)
Lemma remove_duplicates_eqset :
  forall {T} dec (l : list T), eqset (remove_duplicates dec l) l.
Proof.
  induction l; simpl; auto.
  dest_cases w; auto;
    introv; split; intro j; allsimpl; tcsp.
  { apply IHl in j; sp. }
  { apply IHl; repndors; subst; tcsp. }
  { repndors; tcsp; apply IHl in j; tcsp. }
  { repndors; tcsp; apply IHl in j; tcsp. }
Qed.

Lemma eqset_redundant_left :
  forall {T} (v : T) l1 l2,
    eqset (v :: l1) l2
    -> List.In v l1
    -> eqset l1 l2.
Proof.
  introv eqs i; introv; split; intro h.
  { apply eqs; simpl; tcsp. }
  { apply eqs in h; simpl in h; repndors; substs; tcsp. }
Qed.

Lemma in_remove_elt :
  forall {T} (x v : T) dec l,
    List.In x (remove_elt dec v l)
    <-> (List.In x l /\ x <> v).
Proof.
  induction l; simpl; split; intro h; repndors; tcsp;
    dest_cases w; subst; tcsp;
      simpl in *; repndors; subst; tcsp;
        try (complete (apply IHl in h; tcsp)).
  { apply IHl; tcsp. }
  { repnd; repndors; subst; tcsp.
    right; apply IHl; tcsp. }
Qed.

Lemma eqset_not_redundant_left :
  forall {T} (v : T) l1 l2 dec,
    eqset (v :: l1) l2
    -> ~ List.In v l1
    -> (eqset l1 (remove_elt dec v l2) /\ List.In v l2).
Proof.
  introv eqs i; introv.
  dands.

  { split; intro h.
    { apply in_remove_elt; dands.
      { apply eqs; simpl; tcsp. }
      { intro xx; subst; tcsp. }
    }
    { apply in_remove_elt in h; repnd.
      apply eqs in h0; simpl in h0; repndors; subst; tcsp. }
  }

  { apply eqs; simpl; tcsp. }
Qed.

Lemma remove_elt_if_not_in :
  forall {T} (v : T) l dec,
    ~ List.In v l
    -> remove_elt dec v l = l.
Proof.
  induction l; introv q; simpl in *; tcsp.
  apply not_or in q; repnd.
  dest_cases w; GC.
  rewrite IHl; auto.
Qed.

Lemma not_in_remove_elt :
  forall {T} (v : T) l dec,
    ~ In v (remove_elt dec v l).
Proof.
  induction l; introv; simpl; auto.
  dest_cases w.
Qed.
Hint Resolve not_in_remove_elt : core.

Lemma snoc_cons :
  forall {T} (a b : T) l, snoc (a :: l) b = a :: snoc l b.
Proof.
  auto.
Qed.

Fixpoint list_const {T} (n : nat) (x : T) : list T :=
  match n with
  | 0 => []
  | S n => x :: list_const n x
  end.

Lemma length_list_const :
  forall {T} n (x : T), length (list_const n x) = n.
Proof.
  induction n; introv; simpl; auto.
Qed.
Hint Rewrite @length_list_const : core.

Lemma disjoint_app_r :
  forall {T} (l1 l2 l3 : list T),
    disjoint l1 (l2 ++ l3) <-> (disjoint l1 l2 /\ disjoint l1 l3).
Proof.
  introv; split; intro h; repnd; dands; introv i j.
  { apply h in i; destruct i; apply in_app_iff; auto. }
  { apply h in i; destruct i; apply in_app_iff; auto. }
  { apply in_app_iff in j; repndors.
    { apply h0 in i; sp. }
    { apply h in j; sp. }
  }
Qed.

Lemma sublist_app_r :
  forall (T : Type) (l1 l2 l : list T),
    sublist l (l1 ++ l2)
    <->
    exists la lb, l = (la ++ lb)%list /\ sublist la l1 /\ sublist lb l2.
Proof.
  induction l1; introv; split; intro h; exrepnd; subst; simpl in *; auto.

  { exists ([] : list T) l; simpl; dands; auto. }

  { inversion h2; subst; simpl; auto. }

  { apply sublist_cons_r in h; repndors; subst; simpl in *.

    { exists ([] : list T) ([] : list T); simpl; auto. }

    { exrepnd; subst.
      apply IHl1 in h0; exrepnd; subst.
      exists (a :: la) lb; simpl; dands; auto. }

    { apply IHl1 in h; exrepnd; subst.
      exists la lb; dands; auto. }
  }

  { apply sublist_cons_r in h2; repndors; exrepnd; subst; simpl in *.

    { apply sublist_cons_r; right; right.
      apply IHl1.
      exists ([] : list T) lb; simpl; dands; auto. }

    { constructor.
      apply IHl1.
      exists l lb; dands; auto. }

    { constructor.
      apply IHl1.
      exists la lb; dands; auto. }
  }
Qed.

Lemma disjoint_sublist_app_l_implies :
  forall {T} (l1 l2 l : list T),
    disjoint l l1
    -> sublist (l1 ++ l2) l
    -> l1 = [].
Proof.
  destruct l1; introv disj sl; auto; simpl in *.
  apply sublist_cons_l in sl; exrepnd; subst.
  apply disjoint_cons_r in disj; repnd; simpl in *.
  rewrite in_app_iff in disj; simpl in disj.
  destruct disj; auto.
Qed.

Lemma disjoint_sublist_app_implies :
  forall {T} (la lb l1 l2 : list T),
    disjoint lb l1
    -> sublist (l1 ++ l2) (la ++ lb)
    -> exists l l', l2 = (l ++ l')%list /\ sublist (l1 ++ l) la /\ sublist l' lb.
Proof.
  induction la; introv disj sl; simpl in *.

  { applydup @disjoint_sublist_app_l_implies in sl; subst; simpl in *; auto.
    exists ([] : list T) l2; auto. }

  { apply sublist_cons_r in sl; repndors; exrepnd; subst; ginv.

    { destruct l1; simpl in *; ginv; subst; auto.
      exists ([] : list T) ([] : list T); dands; auto. }

    { destruct l1; simpl in *; subst; ginv.

      { apply sublist_app_r in sl0; exrepnd; subst.
        exists (a :: la0) lb0; auto. }

      { apply disjoint_cons_r in disj; repnd.
        pose proof (IHla lb l1 l2) as q; repeat (autodimp q hyp); exrepnd; subst.
        exists l l'; dands; auto. }
    }

    { pose proof (IHla lb l1 l2) as q; repeat (autodimp q hyp); exrepnd; subst.
      exists l l'; dands; auto. }
  }
Qed.

Lemma disjoint_app_l:
  forall (T : Type) (l1 l2 l : list T),
    disjoint (l1 ++ l2) l <-> (disjoint l1 l /\ disjoint l2 l).
Proof.
  introv.
  rewrite disjoint_sym.
  rewrite disjoint_app_r; split; sp; apply disjoint_sym; auto.
Qed.

Lemma disjoint_sublist_implies_nil :
  forall {T} (l1 l2 : list T),
    sublist l1 l2
    -> disjoint l1 l2
    -> l1 = [].
Proof.
  introv sl disj.
  destruct l1; auto.
  apply sublist_cons_l in sl; exrepnd; subst.
  apply disjoint_cons_l in disj; repnd.
  destruct disj0.
  apply in_app_iff; simpl; auto.
Qed.

Lemma disjoint_eq_app_implies :
  forall {T} (la lb l1 l2 : list T),
    disjoint lb l1
    -> (l1 ++ l2)%list = (la ++ lb)%list
    -> exists l, l2 = (l ++ lb)%list /\ la = (l1 ++ l)%list.
Proof.
  induction la; introv disj sl; simpl in *; subst.

  { destruct l1; simpl in *.

    { exists ([] : list T); auto. }

    { apply disjoint_cons_l in disj; repnd; simpl in *.
      destruct disj0; auto. }
  }

  { destruct l1; simpl in *; subst; ginv.

    { clear disj.
      exists (a :: la); simpl; dands; auto. }

    { inversion sl; subst; clear sl.
      match goal with | [ H : _ = _ |- _ ] => rename H into e end.
      apply disjoint_cons_r in disj; repnd.
      pose proof (IHla lb l1 l2) as q; repeat (autodimp q hyp); exrepnd; subst.
      exists l; dands; auto. }
  }
Qed.

Lemma sublist_cons_app_prop1 :
  forall {T} (v1 v2 : T) l1 l2 la lb,
    ~ In v2 lb
    -> disjoint lb l1
    -> sublist (v1 :: (l1 ++ l2)%list) (v2 :: (la ++ lb)%list)
    ->
    (
      (In v1 lb /\ l1 = [])
      \/
      (In v1 (v2 :: la) /\ sublist (v1 :: l1) (v2 :: la))
    ).
Proof.
  introv ni disj sl.
  apply sublist_cons_r in sl; repndors; ginv; exrepnd; ginv.

  { right; simpl; dands; auto.
    pose proof (disjoint_sublist_app_implies la lb l1 l2) as q.
    repeat (autodimp q hyp); exrepnd; subst.
    constructor.
    apply sublist_app_l in q2; exrepnd; subst; auto.
    apply sublist_app_r.
    exists l1 ([] : list T); autorewrite with core; auto. }

  { apply sublist_app_r in sl; exrepnd.
    destruct la0; simpl in *; subst; ginv.

    { apply sublist_cons_l in sl1; exrepnd; subst.
      apply disjoint_app_l in disj; repnd.
      apply disjoint_cons_l in disj; repnd.
      apply sublist_app_l in sl1; exrepnd; subst.
      apply disjoint_app_l in disj; repnd.
      pose proof (disjoint_sublist_implies_nil l1 la1) as q.
      repeat (autodimp q hyp);[apply disjoint_sym;auto|]; subst.
      left; dands; auto.
      apply in_app_iff; simpl; auto. }

    { inversion sl0; subst; clear sl0.
      match goal with | [ H : _ = _ |- _ ] => rename H into e end.
      apply sublist_cons_l in sl2; exrepnd; subst.
      apply disjoint_eq_app_implies in e; auto;
        [|introv i j; apply disj in j; auto; eapply sublist_in_implies; eauto].
      exrepnd; subst.
      apply sublist_app_l in sl2; exrepnd; subst.
      right; dands; auto.
      { right; apply in_app_iff; simpl; auto. }
      constructor.
      apply sublist_app_r_weak.
      constructor.
      apply sublist_app_r.
      exists l1 ([] : list T); autorewrite with core; dands; auto.
    }
  }
Qed.

Lemma sublist_implies_le_length :
  forall {T} (l1 l2 : list T),
    sublist l1 l2 -> length l1 <= length l2.
Proof.
  induction l1; introv sl; simpl; try omega.
  apply sublist_cons_l in sl; exrepnd; subst.
  apply IHl1 in sl1.
  rewrite app_length; simpl; omega.
Qed.

Lemma implies_sublist_cons_r_weak :
  forall {T} (v : T) l1 l2,
    sublist l1 l2
    -> sublist l1 (v :: l2).
Proof.
  introv sl.
  apply sublist_cons_r.
  destruct l1; auto.
Qed.

Lemma implies_sublist_snoc_r_weak :
  forall {T} (v : T) l1 l2,
    sublist l1 l2
    -> sublist l1 (snoc l2 v).
Proof.
  induction l1; introv sl; auto.
  apply sublist_cons_l in sl; exrepnd; subst.
  apply sublist_cons_l.
  exists la (snoc lb v); simpl; dands; auto.
  rewrite <- app_snoc; simpl; auto.
Qed.

Inductive no_repeats {T} : list T -> Prop :=
| no_rep_nil : no_repeats []
| no_rep_cons :
    forall x xs,
      ~ In x xs
      -> no_repeats xs
      -> no_repeats (x :: xs).
Hint Constructors no_repeats.

Fixpoint norepeatsb {T} (d : Deq T) (l : list T) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    if in_dec d x xs
    then false
    else norepeatsb d xs
  end.

Definition norepeats {T} (d : Deq T) (l : list T) : Prop :=
  norepeatsb d l = true.

Lemma norepeatsb_is_no_repeats :
  forall {T} (d : Deq T) (l : list T),
    norepeats d l <-> no_repeats l.
Proof.
  induction l; unfold norepeats; introv; simpl; split; intro h; auto; dest_cases w; auto.

  { constructor; auto; apply IHl; auto. }

  { inversion h; tcsp. }

  { apply IHl; inversion h; auto. }
Qed.

Lemma norepeatsb_proof_irrelevance :
  forall {T} (d : Deq T) (l : list T) (x y : norepeats d l), x = y.
Proof.
  introv.
  apply Eqdep_dec.UIP_dec.
  apply bool_dec.
Qed.

Lemma subset_trans :
  forall {T} (l1 l2 l3 : list T),
    subset l1 l2
    -> subset l2 l3
    -> subset l1 l3.
Proof.
  introv ss1 ss2 i.
  apply ss1 in i; apply ss2 in i; tcsp.
Qed.

Definition null {T} (l : list T) : Prop :=
  l = [].

Definition nullb {T} (l : list T) : bool :=
  if l then true else false.

Lemma nullb_prop :
  forall {T} (l : list T), nullb l = true <-> null l.
Proof.
  destruct l; unfold null; simpl; split; introv h; tcsp.
Qed.

Lemma null_app :
  forall {T} (l1 l2 : list T),
    null (l1 ++ l2) <-> (null l1 /\ null l2).
Proof.
  introv; unfold null; split; intro h; repnd; subst; auto.
  apply app_eq_nil in h; auto.
Qed.

Lemma implies_subset_app_lr :
  forall (T : Type) (l1 l2 la lb : list T),
    subset l1 la
    -> subset l2 lb
    -> subset (l1 ++ l2) (la ++ lb).
Proof.
  introv ss1 ss2.
  introv i; allrw in_app_iff; repndors;[apply ss1 in i|apply ss2 in i]; auto.
Qed.

Lemma implies_subset_app_r :
  forall (T : Type) (l1 l2 l : list T),
    (subset l l1 \/ subset l l2)
    -> subset l (l1 ++ l2).
Proof.
  introv imp i; apply in_app_iff.
  repndors; apply imp in i; sp.
Qed.

Lemma implies_subset_map_lr :
  forall {A B} (l1 l2 : list A) (f : A -> B),
    subset l1 l2
    -> subset (map f l1) (map f l2).
Proof.
  introv ss i; allrw in_map_iff; exrepnd; subst.
  apply ss in i0; eexists; dands; eauto.
Qed.

Lemma subset_eqset_l :
  forall {T} (l1 l2 l3 : list T),
    subset l1 l2
    -> eqset l1 l3
    -> subset l3 l2.
Proof.
  introv ss eqs i.
  apply eqs in i; apply ss in i; auto.
Qed.

Lemma eqset_sym :
  forall {T} (l1 l2 : list T), eqset l1 l2 -> eqset l2 l1.
Proof.
  introv eqs; introv.
  rewrite (eqs x); sp.
Qed.

Lemma implies_eqset_app_lr :
  forall {T} (l1 l2 l3 l4 : list T),
    eqset l1 l2
    -> eqset l3 l4
    -> eqset (l1 ++ l3) (l2 ++ l4).
Proof.
  introv eqs1 eqs2; introv.
  allrw in_app_iff.
  split; introv i; repndors;
    try (complete (apply eqs1 in i; tcsp));
    try (complete (apply eqs2 in i; tcsp)).
Qed.

Lemma subset_app_l :
  forall {T} (l1 l2 : list T) l,
    subset (l1 ++ l2) l <-> (subset l1 l /\ subset l2 l).
Proof.
  introv; split; intro h; repnd; dands; introv i.
  - apply h; rw in_app_iff; sp.
  - apply h; rw in_app_iff; sp.
  - rw in_app_iff in i; repndors;[apply h0|apply h];auto.
Qed.

Inductive adjacent {T} (a b : T) : list T -> Prop :=
| adjacent_head : forall l, adjacent a b (a :: b :: l)
| adjacent_tail : forall l c, adjacent a b l -> adjacent a b (c :: l).
Hint Constructors adjacent.

Lemma adjacent_in_left :
  forall T a b (l : list T),
    adjacent a b l -> In a l.
Proof.
  induction l; introv h; simpl.
  - inversion h.
  - inversion h as [?|]; subst; auto.
Qed.
Hint Resolve adjacent_in_left : list.

Lemma adjacent_in_left2 :
  forall T a b c (l : list T),
    adjacent a b (snoc l c) -> In a l.
Proof.
  induction l; introv h; allsimpl.
  - inversion h as [|?? xx]; subst; inversion xx.
  - inversion h as [?|]; subst; auto.
Qed.
Hint Resolve adjacent_in_left2 : list.

Lemma adjacent_in_right :
  forall T a b (l : list T),
    adjacent a b l -> In b l.
Proof.
  induction l; introv h; simpl.
  - inversion h.
  - inversion h as [?|]; subst; simpl; auto.
Qed.
Hint Resolve adjacent_in_right : list.

Lemma adjacent_app :
  forall T a b (l1 l2 : list T),
    adjacent a b (l1 ++ l2)
    <-> (adjacent a b l1
         \/ adjacent a b l2
         \/ exists l k, l1 = snoc l a /\ l2 = b :: k).
Proof.
  induction l1; introv; simpl; split; intro h; repndors; tcsp; tcsp.
  - inversion h.
  - exrepnd; subst.
    assert (length ([] : list T) = length (snoc l a)) as xx;
      [rewrite <- h0; auto|]; simpl in xx.
    rewrite length_snoc in xx; allsimpl; omega.
  - inversion h as [|? ? adj]; clear h; subst.
    + destruct l1; allsimpl; subst; ginv.
      * right; right.
        exists ([] : list T) l; simpl; auto.
      * left; auto.
    + rewrite IHl1 in adj; repndors; clear IHl1; auto.
      exrepnd; subst.
      right; right.
      exists (a0 :: l) k; simpl; dands; auto.
  - inversion h as [|? ? adj]; clear h; subst; simpl; auto.
    constructor.
    rewrite IHl1; auto.
  - constructor.
    rewrite IHl1; auto.
  - exrepnd; subst.
    destruct l; allsimpl; ginv; allsimpl; auto.
    constructor.
    rewrite IHl1.
    right; right.
    exists l k; auto.
Qed.

Lemma adjacent_snoc :
  forall T a b (l : list T) t,
    adjacent a b (snoc l t)
    <-> (adjacent a b l
         \/ exists k, l = snoc k a /\ t = b).
Proof.
  induction l; introv; simpl; split; intro h; repndors; tcsp.
  - inversion h; subst; tcsp.
  - exrepnd; subst.
    assert (length ([] : list T) = length (snoc k a)) as xx;
      [rewrite <- h1; auto|]; simpl in xx.
    rewrite length_snoc in xx; allsimpl; omega.
  - inversion h as [|? ? adj]; clear h; subst.
    + destruct l; allsimpl; subst; ginv; tcsp.
      right.
      exists ([] : list T); simpl; auto.
    + rewrite IHl in adj; repndors; clear IHl; auto.
      exrepnd; subst.
      right.
      exists (a0 :: k); simpl; dands; auto.
  - inversion h as [|? ? adj]; clear h; subst; simpl; auto.
    constructor.
    rewrite IHl; auto.
  - exrepnd; subst.
    destruct k; allsimpl; ginv; allsimpl; tcsp.
    constructor.
    rewrite IHl.
    right.
    exists k; auto.
Qed.

Lemma in_implies_adjacent :
  forall A (l1 l2 : list A) a,
    0 < length l2
    -> In a l1
    -> exists b, adjacent a b (l1 ++ l2).
Proof.
  induction l1; introv; simpl; tcsp.
  introv h q; repndors; subst.
  - destruct l1; allsimpl; try omega.
    + destruct l2; allsimpl; try omega.
      exists a; auto.
    + exists a; auto.
  - pose proof (IHl1 l2 a0) as xx; repeat (autodimp xx hyp); exrepnd.
    exists b; auto.
Qed.

Fixpoint mapOption {A B} (f : A -> option B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: xs =>
    match f x with
    | Some y => y :: mapOption f xs
    | None => mapOption f xs
    end
  end.

Lemma map_snoc :
  forall {A B} (l : list A) a (F : A -> B),
    map F (snoc l a) = snoc (map F l) (F a).
Proof.
  induction l; simpl; introv; auto; rewrite IHl; auto.
Qed.

Definition map_option {T U} (f : T -> option U) (top : option T) : option U :=
  match top with
  | Some t => f t
  | None => None
  end.

Lemma map_option_option_map :
  forall {A B C} (f : B -> option C) (g : A -> B) (o : option A),
    map_option f (option_map g o)
    = map_option (compose f g) o.
Proof.
  destruct o; simpl; auto.
Qed.
Hint Rewrite @map_option_option_map : option.

Lemma option_map_option_map :
  forall {T A B} (f : T -> A) (g : A -> B) (top : option T),
    option_map g (option_map f top) = option_map (compose g f) top.
Proof.
  introv.
  destruct top; simpl; auto.
Qed.
Hint Rewrite @option_map_option_map : option.

Lemma seq_n_lt :
  forall m x n, In x (seq n m) -> x < n + m.
Proof.
  induction m; introv i; simpl in *; tcsp.
  repndors; subst; tcsp; try omega.
  apply IHm in i; try omega.
Qed.

Lemma seq_0_lt :
  forall {x n}, In x (seq 0 n) -> x < n.
Proof.
  introv i.
  apply seq_n_lt in i; simpl in *; auto.
Qed.

Fixpoint mapin {A B} (l : list A) : (forall a : A, In a l -> B) -> list B :=
  match l with
  | [] => fun _ => []
  | x :: xs =>
    fun f =>
      f x (@or_introl (x = x) (In x xs) eq_refl)
        :: mapin xs (fun a i => f a (or_intror i))
  end.

Lemma map_as_mapin :
  forall {A B} (l : list A) (f : A -> B),
    map f l = mapin l (fun a _ => f a).
Proof.
  induction l; introv; simpl; auto.
  f_equal; auto.
Qed.

Lemma in_mapin :
  forall {A B}
         (l : list A)
         (f : forall a : A, In a l -> B)
         (b : B),
    In b (mapin l f) <-> exists a i, b = f a i.
Proof.
  induction l; introv; simpl in *; tcsp.
  - split; sp.
  - split; intro k; exrepnd; subst; repndors; subst; tcsp.
    + eexists; eexists; eauto.
    + apply IHl in k; exrepnd; subst.
      eexists; eexists; eauto.
    + right.
      apply IHl.
      eexists; eexists; eauto.
Defined.

Lemma ap_in_mapin :
  forall {A B}
         (l : list A)
         (f : forall a : A, In a l -> B)
         (a : A)
         (i : In a l),
    In (f a i) (mapin l f).
Proof.
  introv.
  apply in_mapin.
  eexists; eexists; auto.
Defined.

Lemma mapin_mapin :
  forall {A B C}
         (l : list A)
         (f : forall a : A, In a l -> B)
         (g : forall b : B, In b (mapin l f) -> C),
    mapin (mapin l f) g = mapin l (fun a i => g (f a i) (ap_in_mapin l f a i)).
Proof.
  induction l; introv; simpl; auto; f_equal; auto.
  apply IHl.
Qed.

Lemma eq_mapins :
  forall {A B}
         (l : list A)
         (f g : forall a : A, In a l -> B),
    (forall (a : A) (i : In a l), f a i = g a i)
    -> mapin l f = mapin l g.
Proof.
  induction l; simpl; introv h; auto; f_equal; auto.
Qed.

Definition olist2list {T} (o : option (list T)) : list T :=
  match o with
  | Some l => l
  | None => []
  end.

Lemma in_olist2list :
  forall {T} (o : option (list T)) (x : T),
    In x (olist2list o) <-> exists l, o = Some l /\ In x l.
Proof.
  introv; split; intro h; destruct o; simpl in *; tcsp.
  - eexists; dands; eauto.
  - exrepnd; repnd; ginv; auto.
Qed.

Definition opt2list {T} (top : option T) : list T :=
  match top with
  | Some t => [t]
  | None => []
  end.
Lemma flat_map_map :
  forall A B C ,
  forall f : B -> list C,
  forall g : A -> B,
  forall l : list A,
    flat_map f (map g l) = flat_map (compose f g) l.
Proof.
  induction l; simpl; sp.
  rewrite IHl.
  unfold compose; auto.
Qed.

Lemma null_cons :
  forall T x (l : list T),
    ~ null (x :: l).
Proof.
  unfold null; sp.
Qed.
Hint Immediate null_cons : list.

Lemma null_flat_map :
  forall (A B : Type) (f : A -> list B) (l : list A),
    null (flat_map f l)
    <-> (forall a : A, In a l -> null (f a)).
Proof.
  induction l; allsimpl; split; introv k; tcsp.
  - apply null_app in k; repnd.
    introv i; repndors; subst; tcsp.
    rw IHl in k; apply k; auto.
  - apply null_app; dands; tcsp.
    apply IHl; introv i.
    apply k; tcsp.
Qed.

Lemma not_null_flat_map_implies :
  forall {A B} (f : A -> list B) (l : list A),
    ~ null (flat_map f l) <-> exists a, In a l /\ ~ null (f a).
Proof.
  induction l; simpl; split; intro h; tcsp.

  - destruct h; constructor.

  - rewrite null_app in h.
    apply Decidable.not_and in h;
      [|destruct (f a);[left;constructor|right;intro xx;inversion xx] ].
    repndors.

    + exists a; dands; tcsp.

    + apply IHl in h; exrepnd.
      exists a0; dands; tcsp.

  - rewrite null_app; introv q; repnd.
    exrepnd; repndors; subst; tcsp.
    apply IHl in q; auto.
    exists a0; tcsp.
Qed.

Lemma flat_map_app:
  forall (A B : Type) (f : A -> list B) (l l' : list A),
    flat_map f (l ++ l') = flat_map f l ++ flat_map f l'.
Proof.
  induction l as [| a l Hind]; introv; tcsp; simpl in *.
  rw <- app_assoc; tcsp.
  f_equal; tcsp.
Qed.

Lemma nullb_true_iff :
  forall {T} (l : list T), nullb l = true <-> l = [].
Proof.
  destruct l; split; intro h; simpl in *; subst; tcsp.
Qed.

Lemma mapOption_map :
  forall {A B C} (l : list A) (f : A -> B) (g : B -> option C),
    mapOption g (map f l)
    = mapOption (compose g f) l.
Proof.
  induction l; introv; simpl; auto.
  unfold compose.
  destruct (g (f a)); rewrite IHl; auto.
Qed.

Lemma mapOption_app :
  forall {A B} (l1 l2 : list A) (f : A -> option B),
    mapOption f (l1 ++ l2)
    = mapOption f l1 ++ mapOption f l2.
Proof.
  induction l1; introv; simpl; auto.
  destruct (f a); simpl; rewrite IHl1; auto.
Qed.

Lemma in_mapOption :
  forall {A B} (l : list A) (f : A -> option B) (b : B),
    In b (mapOption f l)
    <-> exists a, In a l /\ f a = Some b.
Proof.
  induction l; simpl; introv; split; intro h; repndors; exrepnd; tcsp.

  - remember (f a) as faop; destruct faop; simpl in *; repndors; subst; auto.

    + exists a; dands; auto.

    + apply IHl in h; exrepnd.
      exists a0; dands; auto.

    + apply IHl in h; exrepnd.
      exists a0; dands; auto.

  - repndors; subst.

    + remember (f a0) as faop; destruct faop; simpl in *; ginv.

    + remember (f a) as faop; destruct faop; simpl in *; ginv.

      * right; apply IHl; exists a0; dands; auto.

      * apply IHl; exists a0; dands; auto.
Qed.

Lemma mapOption_nil :
  forall {A B} (l : list A) (f : A -> option B),
    mapOption f l = []
    <-> forall a, In a l -> f a = None.
Proof.
  induction l; introv; simpl; split; intro h; tcsp.

  - remember (f a) as faop; destruct faop; simpl in *; ginv.
    introv i; repndors; subst; auto.
    eapply IHl in h;[|eauto]; auto.

  - remember (f a) as faop; destruct faop; simpl in *; ginv.

    + pose proof (h a) as q; autodimp q hyp; rewrite q in Heqfaop; ginv.

    + apply IHl; introv i; apply h; auto.
Qed.

Lemma in_olist2list_option_map_opt2list :
  forall {T} (top : option (option T)) t,
    In t (olist2list (option_map opt2list top))
    <-> top = Some (Some t).
Proof.
  introv.
  destruct top; simpl; try (complete (split; tcsp)).
  destruct o; simpl; try (complete (split; tcsp)).
  - split; intro h; ginv; tcsp.
    repndors; subst; tcsp.
  - split; intro h; tcsp; ginv.
Qed.

Lemma no_repeats_cons :
  forall T (x : T) l,
    no_repeats (x :: l) <-> (no_repeats l /\ ~ In x l).
Proof.
  introv; split; intro k.
  inversion k; subst; auto.
  constructor; sp.
Qed.

Lemma no_repeats_app :
  forall T (l1 l2 : list T),
    no_repeats (l1 ++ l2) <-> (no_repeats l1 /\ no_repeats l2 /\ disjoint l1 l2).
Proof.
  induction l1; introv; allsimpl; split; intro k;
    repnd; dands; auto; try (complete sp); allrw no_repeats_cons;
      repnd; dands; auto; allrw in_app_iff; allrw not_over_or;
        repnd; dands; auto; allrw @disjoint_cons_l;
          repnd; dands; auto;
            try (complete (discover; sp)).
  apply IHl1; sp.
Qed.

Lemma existsb_false :
  forall {T} (l : list T) f,
    existsb f l = false <-> (forall x, In x l -> f x = false).
Proof.
  induction l; simpl; dands; split; intro h; tcsp.

  - apply orb_false_iff in h; exrepnd.
    introv i; repndors; subst; auto.
    rewrite IHl in h; apply h; auto.

  - apply orb_false_iff.
    pose proof (h a) as q; autodimp q hyp.
    dands; auto.
    apply IHl; tcsp.
Qed.

Lemma length_mapin :
  forall {A B} (l : list A) (f : forall (a : A), In a l -> B),
    length (mapin l f) = length l.
Proof.
  induction l; introv; simpl; auto.
Qed.
Hint Rewrite @length_mapin : list.

Fixpoint remove_repeats {T} (deq : Deq T) l :=
  match l with
  | [] => []
  | x :: l =>
    if in_dec deq x l
    then remove_repeats deq l
    else x :: remove_repeats deq l
  end.

Lemma in_remove_repeats :
  forall {T} deq x (l : list T),
    In x (remove_repeats deq l) <-> In x l.
Proof.
  induction l; simpl; tcsp.
  dest_cases w; simpl; try (rewrite IHl; clear IHl);
    split; intro h; repndors; subst; tcsp.
Qed.

Lemma no_repeats_remove_repeats :
  forall {T} deq (l : list T),
    no_repeats (remove_repeats deq l).
Proof.
  induction l; simpl; auto; dest_cases w.
  constructor; auto.
  rw @in_remove_repeats; auto.
Qed.
Hint Resolve no_repeats_remove_repeats : list.

Lemma length_remove_repeats_le :
  forall {T} deq (l : list T),
    length (remove_repeats deq l) <= length l.
Proof.
  induction l; simpl; auto; dest_cases w; simpl; try omega.
Qed.
Hint Resolve length_remove_repeats_le : list.

Lemma decidable_no_repeats :
  forall {T} (deq : Deq T) (l : list T), decidable (no_repeats l).
Proof.
  induction l; simpl; tcsp.
  destruct (in_dec deq a l) as [d|d].
  - right; introv h.
    apply no_repeats_cons in h; tcsp.
  - destruct IHl as [d1|d1];[left|right].
    + apply no_repeats_cons; tcsp.
    + intro xx; apply no_repeats_cons in xx; tcsp.
Qed.

Lemma decidable_subset :
  forall {T} (deq : Deq T) (l1 l2 : list T), decidable (subset l1 l2).
Proof.
  induction l1; introv; simpl.

  - left; auto.

  - destruct (in_dec deq a l2) as [d|d].

    + destruct (IHl1 l2) as [d1|d1].

      * left; introv i; simpl in i; repndors; subst; tcsp.

      * right; introv ss; destruct d1; introv i; apply ss; simpl; tcsp.

    + right; intro ss; destruct d.
      apply ss; simpl; tcsp.
Qed.

(* keeps the elements of l1 that are in l2 too *)
Fixpoint keep {T} (deq : Deq T) (l1 l2 : list T) : list T :=
  match l1 with
  | [] => []
  | x :: l =>
    if in_dec deq x l2 then x :: keep deq l l2
    else keep deq l l2
  end.

Lemma in_keep :
  forall {T} (deq : Deq T) a (l1 l2 : list T),
    In a (keep deq l1 l2) <-> (In a l1 /\ In a l2).
Proof.
  induction l1; simpl; introv; auto; split; intro h; tcsp;
    dest_cases w; simpl in *; repnd; repndors; subst; tcsp.
  - apply IHl1 in h; repnd; tcsp.
  - apply IHl1 in h; repnd; tcsp.
  - rewrite IHl1; tcsp.
  - rewrite IHl1; tcsp.
Qed.

Lemma implies_no_repeats_keep :
  forall {T} (deq : Deq T) (l1 l2 : list T),
    no_repeats l1 -> no_repeats (keep deq l1 l2).
Proof.
  induction l1; simpl; introv h; auto.
  inversion h as [|? ? ni nr]; clear h; subst.
  dest_cases w.
  constructor; auto.
  intro j.
  apply in_keep in j; tcsp.
Qed.
Hint Resolve implies_no_repeats_keep : list.

Lemma subset_keep_left :
  forall {T} (deq : Deq T) (l1 l2 : list T),
    subset (keep deq l1 l2) l1.
Proof.
  induction l1; simpl; introv h; auto; simpl in *; dest_cases w;
    simpl in *; repndors; subst; tcsp; apply IHl1 in h; tcsp.
Qed.
Hint Resolve subset_keep_left : list.

Lemma subset_keep_right :
  forall {T} (deq : Deq T) (l1 l2 : list T),
    subset (keep deq l1 l2) l2.
Proof.
  induction l1; simpl; introv h; auto; simpl in *; tcsp; dest_cases w;
    simpl in *; repndors; subst; tcsp; apply IHl1 in h; tcsp.
Qed.
Hint Resolve subset_keep_right : list.

Lemma subset_remove_repeats_l :
  forall {T} (deq : Deq T) (l : list T),
    subset (remove_repeats deq l) l.
Proof.
  introv i; apply in_remove_repeats in i; auto.
Qed.
Hint Resolve subset_remove_repeats_l : list.

Lemma keep_remove_repeats :
  forall {T} (deq : Deq T) l1 l2,
    keep deq (remove_repeats deq l1) l2
    = remove_repeats deq (keep deq l1 l2).
Proof.
  induction l1; introv; simpl; auto.
  repeat (dest_cases w; simpl; ginv; tcsp); try (rewrite IHl1;auto).
  - rewrite in_keep in n; destruct n; tcsp.
  - rewrite in_keep in i0; destruct n; tcsp.
Qed.

(* keeps the elements of l1 that are not in l2 *)
Fixpoint remove_list {T} (deq : Deq T) (l1 l2 : list T) : list T :=
  match l1 with
  | [] => []
  | x :: l =>
    if in_dec deq x l2 then remove_list deq l l2
    else x :: remove_list deq l l2
  end.

Lemma remove_list_nil_r :
  forall {T} (deq : Deq T) l,
    remove_list deq l [] = l.
Proof.
  induction l; simpl; auto; rewrite IHl; auto.
Qed.
Hint Rewrite @remove_list_nil_r : list.

Lemma remove_list_cons_r :
  forall {T} (deq : Deq T) l1 l2 a,
    remove_list deq l1 (a :: l2) = remove_elt deq a (remove_list deq l1 l2).
Proof.
  induction l1; simpl; auto; introv;
    repeat (dest_cases w; simpl; subst; tcsp);
    try (complete (destruct n; tcsp)).
  rewrite IHl1; auto.
Qed.

Lemma remove_list_cons_r_in :
  forall {T} (deq : Deq T) l1 l2 a,
    In a l2
    -> remove_list deq l1 (a :: l2) = remove_list deq l1 l2.
Proof.
  induction l1; simpl; auto; introv i;
    repeat (dest_cases w; simpl; subst; tcsp);
    try (complete (destruct n; tcsp));
    try (rewrite IHl1; auto).
  repndors; subst; tcsp.
Qed.

Lemma remove_repeats_app :
  forall {T} (deq : Deq T) l1 l2,
    remove_repeats deq (l1 ++ l2)
    = remove_list deq (remove_repeats deq l1) l2 ++ remove_repeats deq l2.
Proof.
  induction l1; simpl; simpl; introv; autorewrite with list; auto.
  repeat (dest_cases w; simpl; tcsp); try (rewrite IHl1; tcsp).

  - rewrite in_app_iff in i; tcsp.

  - rewrite in_app_iff in n; destruct n; tcsp.

  - rewrite in_app_iff in n; destruct n; tcsp.
Qed.

Lemma split_length_as_keep_remove_list :
  forall {T} (deq : Deq T) (l1 l2 : list T),
    length l1 = length (keep deq l1 l2) + length (remove_list deq l1 l2).
Proof.
  induction l1; introv; simpl; auto.
  dest_cases w; simpl.
  rewrite <- plus_n_Sm; rewrite <- IHl1; auto.
Qed.

Fixpoint find_pos {T} (deq : Deq T) (x : T) (l : list T) (d : nat) : nat :=
  match l with
  | [] => d
  | a :: k => if deq a x then 0 else S (find_pos deq x k d)
  end.

(* finds the positions in l1 of the elements in l2 *)
Fixpoint find_positions {T} (deq : Deq T) (l1 l2 : list T) : list nat :=
  match l1 with
  | [] => []
  | a :: k =>
    if in_dec deq a l2
    then 0 :: map S (find_positions deq k (remove_elt deq a l2))
    else map S (find_positions deq k l2)
  end.

Lemma subset_nil_r :
  forall {T} (l : list T), subset l [] <-> l = [].
Proof.
  introv; split; intro h; subst; auto.
  destruct l; auto.
  pose proof (h t) as q; simpl in q; autodimp q hyp; tcsp.
Qed.

Lemma implies_no_repeats_remove_elt :
  forall {T} (deq : Deq T) x (l : list T),
    no_repeats l -> no_repeats (remove_elt deq x l).
Proof.
  induction l; simpl; introv h; auto.
  inversion h as [|? ? ni nr]; clear h; subst.
  dest_cases w.
  constructor; tcsp.
  introv i.
  apply in_remove_elt in i; tcsp.
Qed.
Hint Resolve implies_no_repeats_remove_elt : list.

Lemma no_repeats_implies_remove_repeats_eq :
  forall {T} deq (l : list T),
    no_repeats l
    -> remove_repeats deq l = l.
Proof.
  induction l; introv norep; simpl; auto.
  inversion norep; subst; clear norep.
  rewrite IHl; auto.
  dest_cases w.
Qed.

Lemma remove_repeats_remove_elt :
  forall {T} deq (a : T) l,
    remove_repeats deq (remove_elt deq a l)
    = remove_elt deq a (remove_repeats deq l).
Proof.
  induction l; simpl; auto.
  repeat (dest_cases w; simpl; tcsp).
  - apply in_remove_elt in i; tcsp.
  - destruct n0; apply in_remove_elt; tcsp.
Qed.

Lemma length_remove_elt_if_no_repeats :
  forall {T} deq (a : T) l,
    no_repeats l
    -> length (remove_elt deq a l)
       = if in_dec deq a l
         then pred (length l)
         else length l.
Proof.
  induction l; simpl; introv norep; auto.
  inversion norep as [|? ? ni nr]; clear norep; subst.
  autodimp IHl hyp.
  repeat (dest_cases w; simpl; repndors; subst; tcsp);
    try (rewrite IHl; simpl; auto); try omega.
  { apply Nat.succ_pred_pos; destruct l; simpl in *; tcsp; try omega. }
  { destruct n0; tcsp. }
  { destruct n0; tcsp. }
Qed.

Lemma subset_implies_eq_length_remove_repeats :
  forall {T} deq (l1 l2 : list T),
    subset l1 l2
    -> length (remove_repeats deq l1) <= length (remove_repeats deq l2).
Proof.
  induction l1; simpl; introv ss; try omega.
  apply subset_cons_l in ss; repnd.
  dest_cases w; simpl.

  assert (subset l1 (remove_elt deq a l2)) as ss1.
  { introv i; apply in_remove_elt.
    destruct (deq v a); subst; tcsp. }

  apply IHl1 in ss1.

  eapply le_trans;[apply le_n_S;exact ss1|clear ss1].
  rewrite remove_repeats_remove_elt.
  remember (remove_repeats deq l2) as L.

  rewrite length_remove_elt_if_no_repeats;[|subst;eauto with list].
  dest_cases w.
  { rewrite Nat.succ_pred_pos; auto; destruct L; simpl in*; tcsp; omega. }
  { destruct n0; subst; apply in_remove_repeats; auto. }
Qed.

Lemma length_find_positions_if_subset_and_no_repeats :
  forall {T} (deq : Deq T) l1 l2,
    subset l2 l1
    -> no_repeats l2
    -> length (find_positions deq l1 l2) = length l2.
Proof.
  induction l1; simpl; introv ss norep.

  - apply subset_nil_r in ss; subst; simpl; auto.

  - dest_cases w; simpl in *.

    + assert (subset (remove_elt deq a l2) l1) as ss2.
      {
        introv j; apply in_remove_elt in j; repnd.
        apply ss in j0; simpl in j0; repndors; tcsp.
      }
      apply IHl1 in ss2; eauto 2 with list.
      rewrite map_length.
      rewrite ss2.
      rewrite length_remove_elt_if_no_repeats; auto.
      dest_cases w.
      rewrite Nat.succ_pred; auto.
      destruct l2; simpl in *; tcsp.

    + rewrite map_length.
      assert (subset l2 l1) as ss2.
      { introv j; applydup ss in j; simpl in *; repndors; subst; tcsp. }
      apply IHl1 in ss2; eauto 2 with list.
Qed.

Lemma sublist_map_nth_find_positions_if_same_length :
  forall {A B} (deq : Deq A) (l1 l2 : list A) (l : list B) x,
    length l1 <= length l
    -> sublist (map (fun i => nth i l x) (find_positions deq l1 l2)) l.
Proof.
  induction l1; introv eqlen; simpl in *; auto.
  dest_cases w; simpl.

  - destruct l; simpl in *; try omega.
    apply le_S_n in eqlen.
    constructor.
    rewrite map_map.
    apply IHl1; auto.

  - rewrite map_map.
    destruct l; simpl in *; try omega.
    apply le_S_n in eqlen.
    constructor.
    apply IHl1; auto.
Qed.

Lemma in_find_positions_implies_lt :
  forall {T} (deq : Deq T) l1 l2 x,
    In x (find_positions deq l1 l2)
    -> x < length l1.
Proof.
  induction l1; introv i; simpl in *; tcsp.
  dest_cases w; simpl in *; repndors; subst; simpl in *; try omega.

  - apply in_map_iff in i; exrepnd; subst; simpl in *.
    apply IHl1 in i1; try omega.

  - apply in_map_iff in i; exrepnd; subst.
    apply IHl1 in i0; try omega.
Qed.

Lemma in_find_positions_implies_nth_in :
  forall {T} (deq : Deq T) l1 l2 x t,
    In x (find_positions deq l1 l2)
    -> In (nth x l1 t) l2.
Proof.
  induction l1; simpl; introv i; tcsp.
  dest_cases w; simpl in *; repndors; subst; simpl in *; auto; destruct x; auto.

  - apply in_map_iff in i; exrepnd; subst; ginv.
    eapply IHl1 in i1.
    apply in_remove_elt in i1; repnd.
    exact i2.

  - apply in_map_iff in i; exrepnd; omega.

  - apply in_map_iff in i; exrepnd; ginv.
    apply IHl1; auto.
Qed.

Lemma sublist_singleton_r :
  forall {T} (l : list T) x,
    sublist l [x] <-> (l = [] \/ l = [x]).
Proof.
  introv; split; intro h; repndors; subst; auto.
  inversion h as [|? ? ? ss|? ? ? ss]; subst; tcsp; clear h;
    inversion ss; subst; tcsp.
Qed.

Lemma cons_as_snoc_if_all_same :
  forall {T} (l : list T) z,
    (forall a, In a l -> a = z)
    -> z :: l = snoc l z.
Proof.
  induction l; introv imp; simpl in *; auto.
  pose proof (imp a) as q; autodimp q hyp; subst.
  rewrite IHl; auto.
Qed.

Lemma implies_sublist_snoc :
  forall {T} (l k : list T) z,
    sublist l k
    -> sublist (snoc l z) (snoc k z).
Proof.
  introv ss; induction ss; simpl; auto.
  induction l; simpl; auto.
Qed.

Lemma subset_cons_r_snoc_if_all_same :
  forall {T} z x (l k : list T),
    sublist l (x :: k)
    -> (forall a, In a l -> a = z)
    -> sublist l (snoc k x).
Proof.
  induction l; introv ss imp; auto.
  inversion ss as [|? ? ? ss1|? ? ? ss1]; subst; simpl in *; try omega; clear ss.

  - pose proof (imp x) as q; autodimp q hyp; subst.
    rewrite (cons_as_snoc_if_all_same l z); auto.
    apply implies_sublist_snoc; auto.

  - pose proof (imp a) as q; autodimp q hyp; subst.
    apply implies_sublist_snoc_r_weak; auto.
Qed.

Lemma subset_cons_r_not_in_implies :
  forall {T} c z (l k : list T),
    sublist l (z :: k)
    -> (forall a, In a l -> a = c)
    -> z <> c
    -> sublist l k.
Proof.
  induction l; simpl; introv ss imp d; auto.
  inversion ss as [|? ? ? ss1|? ? ? ss1]; subst; simpl in *; try omega; clear ss; auto.
  pose proof (imp z) as q; autodimp q hyp; tcsp.
Qed.

Definition contains_only {T} (l : list T) (x : T) : Prop :=
  forall a, In a l -> a = x.

Fixpoint count_in {T} (deq : Deq T) l x : nat :=
  match l with
  | [] => 0
  | a :: k => if deq a x then S (count_in deq k x) else count_in deq k x
  end.

Fixpoint count_out {T} (deq : Deq T) l x : nat :=
  match l with
  | [] => 0
  | a :: k => if deq a x then count_out deq k x else S (count_out deq k x)
  end.

Lemma count_in_pos_implies :
  forall {T} (deq : Deq T) l x,
    0 < count_in deq l x
    -> In x l.
Proof.
  induction l; introv h; simpl in *; tcsp.
  dest_cases w.
Qed.

Lemma implies_count_out_pos :
  forall {T} (deq : Deq T) l x y,
    In y l
    -> x <> y
    -> 0 < count_out deq l x.
Proof.
  induction l; introv i d; simpl in *; tcsp.
  repndors; subst; tcsp; dest_cases w; subst; try omega.
  eapply IHl; eauto.
Qed.

Lemma count_out_0_implies :
  forall {T} (deq : Deq T) l x y,
    count_out deq l x = 0
    -> x <> y
    -> ~ In y l.
Proof.
  induction l; introv e d; simpl in *; tcsp.
  dest_cases w; subst.
  intro xx; repndors; subst; tcsp.
  eapply IHl in e;[|exact d]; tcsp.
Qed.

Hint Rewrite Nat.sub_0_r : nat.
Hint Rewrite Nat.add_0_r : nat.

Lemma unique_largest_count_in :
  forall {T} (deq : Deq T) l x y k,
    x <> y
    ->
    (
      (count_out deq l x + k = count_in deq l x
       -> count_in deq l y + k <= count_out deq l y)

      /\

      (count_out deq l x = count_in deq l x + k
       -> count_in deq l y <= count_out deq l y + k)
    ).
Proof.
  induction l; introv d; simpl in *; auto.

  { dands; tcsp; try omega. }

  dest_cases w; subst; dest_cases w; dands; intro ltc; try omega; GC.

  - destruct k; autorewrite with nat in *.

    + pose proof (IHl x y 1 d) as q; repnd.
      autodimp q hyp; try omega.

    + rewrite Nat.add_succ_r in *.
      inversion ltc as [lc]; clear ltc.
      pose proof (IHl x y k d) as q; repnd.
      autodimp q0 hyp; try omega.

  - simpl in *.
    rewrite plus_n_Sm in *.
    pose proof (IHl x y (S k) d) as q; repnd; tcsp.

  - subst; simpl in *.
    rewrite plus_n_Sm in *.
    pose proof (IHl x y (S k) d) as q; repnd.
    autodimp q0 hyp; try omega.

  - subst; simpl in *.

    destruct k; autorewrite with nat in *.

    + pose proof (IHl x y 1 d) as q; repnd.
      autodimp q0 hyp; try omega.

    + rewrite Nat.add_succ_r in *.
      inversion ltc as [lc]; clear ltc.
      pose proof (IHl x y k d) as q; repnd.
      autodimp q hyp; try omega.

  - simpl in *.
    rewrite plus_n_Sm in *.
    pose proof (IHl x y (S k) d) as q; repnd; tcsp.
    autodimp q0 hyp; try omega.

  - simpl in *.
    destruct k; autorewrite with nat in *.

    + pose proof (IHl x y 1 d) as q; repnd.
      autodimp q0 hyp; try omega.

    + rewrite Nat.add_succ_r in *.
      inversion ltc as [lc]; clear ltc.
      pose proof (IHl x y k d) as q; repnd.
      autodimp q hyp; try omega.
Qed.

Lemma unique_largest_count_in2 :
  forall {T} (deq : Deq T) l x y,
    x <> y
    -> count_out deq l x < count_in deq l x
    -> count_in deq l y < count_out deq l y.
Proof.
  introv d ltc.
  pose proof (unique_largest_count_in
                deq l x y
                (count_in deq l x - count_out deq l x)
                d) as q; repnd; omega.
Qed.

Lemma contains_only_cons :
  forall {T} (x : T) l a,
    contains_only (x :: l) a
    <-> (contains_only l a /\ x = a).
Proof.
  introv; split; intro h; repnd; dands; auto.
  - introv i; apply h; simpl; tcsp.
  - apply h; simpl; tcsp.
  - subst; introv i; simpl in i; repndors; subst; tcsp.
Qed.

Lemma sublist_implies_count_in :
  forall {T} (deq : Deq T) l2 l1 x,
    sublist l1 l2
    -> contains_only l1 x
    -> length l1 <= count_in deq l2 x.
Proof.
  induction l2; simpl; introv ss cont.

  - inversion ss; subst; simpl in *; auto.

  - inversion ss as [|? ? ? ss1|? ? ? ss1];
      subst; simpl in *; try omega; clear ss;
        dest_cases w; subst; tcsp.

    + apply contains_only_cons in cont; repnd.
      apply le_n_S.
      apply IHl2; auto.

    + apply contains_only_cons in cont; repnd.
      tcsp.
Qed.

Lemma length_count_in_out :
  forall {T} (deq : Deq T) x l,
    length l = count_in deq l x + count_out deq l x.
Proof.
  induction l; simpl; auto.
  dest_cases w.
  rewrite IHl; omega.
Qed.

Lemma implies_subset_cons_lr_same :
  forall {T} (x : T) l1 l2,
    subset l1 l2
    -> subset (x :: l1) (x :: l2).
Proof.
  introv ss i; simpl in *; repndors; tcsp.
Qed.
Hint Resolve implies_subset_cons_lr_same : list.

Lemma implies_subset_cons_r_weak :
  forall {T} (x : T) l1 l2,
    subset l1 l2
    -> subset l1 (x :: l2).
Proof.
  introv ss i; simpl in *; repndors; tcsp.
Qed.
Hint Resolve implies_subset_cons_r_weak : list.

Inductive hasn {A} (a : A) : list A -> nat -> Prop :=
| hasn_nil : hasn a [] 0
| hasn_in  : forall l n, hasn a l n -> hasn a (a :: l) (S n)
| hasn_out : forall v l n, hasn a l n -> a <> v -> hasn a (v :: l) n.
Hint Constructors hasn.

Inductive has_at_least_n {A} (a : A) : list A -> nat -> Prop :=
| has_at_least_n_nil : has_at_least_n a [] 0
| has_at_least_n_in  : forall l n, has_at_least_n a l n -> has_at_least_n a (a :: l) (S n)
| has_at_least_n_out : forall v l n, has_at_least_n a l n -> has_at_least_n a (v :: l) n.
Hint Constructors has_at_least_n.

Lemma has_at_least_0 :
  forall {A} (a : A) l, has_at_least_n a l 0.
Proof.
  induction l; auto.
Qed.
Hint Resolve has_at_least_0 : list.

Lemma has_at_least_le :
  forall {A} (a : A) l n m,
    m <= n
    -> has_at_least_n a l n
    -> has_at_least_n a l m.
Proof.
  induction l; introv lemn h; auto.

  - inversion h; subst; clear h.
    assert (m = 0) as xx by omega; subst; auto.

  - inversion h as [|? ? q|? ? ? q]; subst; clear h; auto.

    + destruct m; eauto with list.
      assert (m <= n0) as h by omega; clear lemn.
      constructor.
      eapply IHl; eauto.

    + constructor.
      eapply IHl; eauto.
Qed.
Hint Resolve has_at_least_le : list.
