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


Require Export QArith_base.
Require Export list_util.
Require Export Eqdep_dec.


Require Export Node.
Require Export Msg.
Require Export Crypto.
Require Export AuthMsg.


Section EventOrdering.

  Context { pd  : @Data }.
  Context { pn  : @Node }.
  Context { pk  : @Key }.
  Context { pat : @AuthTok }.
  Context { paf : @AuthFun pn pk pat pd }.
  Context { m   : @Msg }.


  Definition Qpos := {q : Q | Qle 0 q}.

  Definition Qpos_lt (q1 q2 : Qpos) := Qlt (proj1_sig q1) (proj1_sig q2).

  (*
  Inductive Faulty :=
(*  | crashed   : Faulty*)
  | byzantine : Faulty.

  Inductive EventStatus :=
  | correct
  | faulty (f : Faulty).
   *)

  Definition trigger_info := option msg.

  Class EventOrdering :=
    {
      Event          :> Type;                     (* Type of Events *)

      happenedBefore : Event -> Event -> Prop;    (* Causal ordering between events *)
      (* QUESTION: shouldn't loc have type Event -> iname?  Do we care about the events that happen outside the system *)
      loc            : Event -> name;             (* Each event happens at a node (location) *)
      direct_pred    : Event -> option Event;     (* Each event is either the first at a node or it has a local predecessor *)
      trigger        : Event -> trigger_info;     (* Each event is triggered the receipt of a message *)
      time           : Event -> Qpos;             (* Each event happens at a time w.r.t. a global clock *)
(*      mode           : Event -> EventStatus;    (* At each point in time (event), a node can either be running or byzantine *)*)
      keys           : Event -> local_key_map;    (* At each point in time (event), a node holds a set of keys *)

      (* AXIOMS *)

      (* Equality between events has to be decidable *)
      eventDeq    : Deq Event;

      (* Causal order has to be well-founded *)
      causalWf : well_founded happenedBefore;

      (* ... and transitive *)
      causalTrans : transitive _ happenedBefore;

      (* The predecessor of an event occurs on the same node *)
      eo_direct_pred_local :
        forall e1 e2 : Event, direct_pred e1 = Some e2 -> loc e1 = loc e2;

      (* The predecessor e2 of an event e1 happens causally before e1 *)
      eo_direct_pred_ord :
        forall e1 e2 : Event, direct_pred e1 = Some e2 -> happenedBefore e2 e1;

      (* An event e does not have a predecessor iff there is no event that happens locally before *)
      eo_direct_pred_first :
        forall e : Event,
          direct_pred e = None
          -> forall e', loc e' = loc e -> e <> e' -> happenedBefore e e';

      (* The predecessor function is injective *)
      eo_direct_pred_inj :
        forall e1 e2 : Event,
          loc e1 = loc e2
          -> direct_pred e1 = direct_pred e2
          -> e1 = e2;

      (* If an event e1 happens causally and locally before e2 then e is the predecessor of e2
       then either e = e1 or e1 happens causally before e *)
      eo_local_order :
        forall e1 e2 e : Event,
          loc e1 = loc e2
          -> happenedBefore e1 e2
          -> direct_pred e2 = Some e
          -> (e = e1 [+] happenedBefore e1 e);

      (* If e1 happens causally before e2 then the time e1 happens is strictly less than
         the time e2 happens *)
      eo_causal_time :
        forall e1 e2, happenedBefore e1 e2 -> Qpos_lt (time e1) (time e2)
    }.

  Context { eo : EventOrdering }.

  (* returns e' if e has a direct predecessor, and otherwise returns e *)
  Definition local_pred (e : Event) : Event :=
    match direct_pred e with
    | Some e' => e'
    | None => e
    end.

  Notation "a ⊂ b" := (direct_pred b = Some a) (at level 0).
  Notation "a ⊆ b" := (local_pred b = a) (at level 0).
  Notation "a ≺ b" := (happenedBefore a b) (at level 0).

  Definition happenedBeforeLe (a b : Event) : Prop :=
    (a ≺ b) \/ a = b.

  Notation "a ≼ b" := (happenedBeforeLe a b) (at level 0).

  (* This defines what it means for a node [n] to be correct in a partial cut [L]
     of an event ordering [eo]: the keys of all events [e1] happening before [e]
     (an event of the partial cut [L]) at location [n], are different from the keys
     held at other locations at events [e2] prior to [e] *)
  Definition isCorrectCut (n : name) (L : list Event) : Prop :=
    forall e e1 e2,
      In e L
      -> e1 ≼ e
      -> e2 ≼ e
      -> loc e1 = n
      -> loc e2 <> n
      -> disjoint
           (map dsk_key (lkm_sending_keys (keys e1)))
           (map dsk_key (lkm_sending_keys (keys e2))).

  Definition isCorrect0 (e : Event) : Prop :=
    isCorrectCut (loc e) [e].

  Definition isCorrect (e : Event) : Prop :=
    match trigger e with
    | Some _ => True
    | _ => False
    end.

(*  Definition isCorrect (e : Event) : Prop :=
    mode e = correct.*)

(*  Definition isCrashed (e : Event) : Prop :=
    mode e = faulty crashed.*)

  Definition isByz (e : Event) : Prop :=
    ~ isCorrect e.

(*  Definition isByz (e : Event) : Prop :=
    mode e = faulty byzantine.*)

  Lemma correct_is_not_byzantine :
    forall (e : Event), isCorrect e -> ~ isByz e.
  Proof.
    introv h q; unfold isByz; tcsp.
  Qed.

  Lemma happenedBeforeLe_refl :
    forall e, e ≼ e.
  Proof.
    introv; right; auto.
  Qed.
  Hint Resolve happenedBeforeLe_refl : eo.

  Definition localHappenedBefore (a b : Event) : Prop :=
    (a ≺ b) /\ loc a = loc b.

  Notation "a ⊏ b" := (localHappenedBefore a b) (at level 0).

  Definition localHappenedBeforeLe (a b : Event) : Prop :=
    (a ≼ b) /\ loc a = loc b.

  Notation "a ⊑ b" := (localHappenedBeforeLe a b) (at level 0).

  Lemma localHappenedBeforeLe_refl :
    forall (e : Event), e ⊑ e.
  Proof.
    introv; split; dands; auto; right; auto.
  Qed.
  Hint Resolve localHappenedBeforeLe_refl : eo.

  Lemma eo_causal : well_founded happenedBefore.
  Proof.
    introv; destruct eo; auto.
  Qed.

  Lemma local_implies_loc :
    forall (e1 e2 : Event), e1 ⊏ e2 -> loc e1 = loc e2.
  Proof.
    introv l; unfold localHappenedBefore in l; sp.
  Qed.
  Hint Resolve local_implies_loc : eo.

  Lemma localLe_implies_loc :
    forall (e1 e2 : Event), e1 ⊑ e2 -> loc e1 = loc e2.
  Proof.
    introv xx; destruct xx as [a b]; auto.
  Qed.
  Hint Resolve localLe_implies_loc : eo.

  Lemma localLe_implies_causalLe :
    forall (e1 e2 : Event), e1 ⊑ e2 -> e1 ≼ e2.
  Proof.
    introv xx; destruct xx as [a b]; auto.
  Qed.
  Hint Resolve localLe_implies_causalLe : eo.

  Lemma pred_implies_causal :
    forall (e1 e2 : Event), e1 ⊂ e2 -> e1 ≺ e2.
  Proof.
    introv l; destruct eo; auto.
    apply eo_direct_pred_ord; auto.
  Qed.
  Hint Resolve pred_implies_causal : eo.

  Lemma pred_implies_loc :
    forall (e1 e2 : Event), e1 ⊂ e2 -> loc e1 = loc e2.
  Proof.
    introv l; destruct eo; auto.
    symmetry.
    apply eo_direct_pred_local; auto.
  Qed.
  Hint Resolve pred_implies_loc : eo.

  Lemma pred_implies_local :
    forall (e1 e2 : Event), e1 ⊂ e2 -> e1 ⊏ e2.
  Proof.
    introv l; split; eauto 3 with eo.
  Qed.
  Hint Resolve pred_implies_local : eo.

  Lemma local_implies_causal :
    forall (e1 e2 : Event), e1 ⊏ e2 -> e1 ≺ e2.
  Proof.
    introv c; destruct c; auto.
  Qed.
  Hint Resolve local_implies_causal : eo.

  Lemma HappenedBeforeInd :
    forall P : Event -> Prop,
      (forall e, (forall e', e' ≺ e -> P e') -> P e)
      -> forall e, P e.
  Proof.
    introv imp; introv.
    pose proof (eo_causal e) as causal.
    induction causal as [e' ih h].
    apply imp; auto.
  Qed.

  Lemma HappenedBeforeInd_type :
    forall P : Event -> Type,
      (forall e, (forall e', e' ≺ e -> P e') -> P e)
      -> forall e, P e.
  Proof.
    introv imp; introv.
    pose proof (eo_causal e) as causal.
    induction causal as [e' ih h].
    apply imp; auto.
  Qed.

  Lemma causal_trans :
    forall (e1 e2 e3 : Event),
      e1 ≺ e2 -> e2 ≺ e3 -> e1 ≺ e3.
  Proof.
    introv c1 c2; destruct eo.
    eapply causalTrans; eauto.
  Qed.
  Hint Resolve causal_trans : eo.

  Lemma causal_le_r_trans :
    forall (e1 e2 e3 : Event),
      e1 ≺ e2 -> e2 ≼ e3 -> e1 ≺ e3.
  Proof.
    introv c1 c2.
    destruct c2; subst; eauto with eo.
  Qed.
  Hint Resolve causal_le_r_trans : eo.

  Lemma causal_le_l_trans :
    forall (e1 e2 e3 : Event),
      e1 ≼ e2 -> e2 ≺ e3 -> e1 ≺ e3.
  Proof.
    introv c1 c2.
    destruct c1; subst; eauto with eo.
  Qed.
  Hint Resolve causal_le_l_trans : eo.

  Lemma local_trans :
    forall (e1 e2 e3 : Event),
      e1 ⊏ e2 -> e2 ⊏ e3 -> e1 ⊏ e3.
  Proof.
    introv c1 c2.
    allunfold localHappenedBefore; repnd; dands; eauto with eo.
    rewrite c1; auto.
  Qed.
  Hint Resolve local_trans : eo.

  Lemma local_trans_le_r :
    forall (e1 e2 e3 : Event),
      e1 ⊏ e2 -> e2 ⊑ e3 -> e1 ⊏ e3.
  Proof.
    introv c1 c2.
    destruct c1 as [a b], c2 as [c d].
    split; allrw; auto.
    destruct c; subst; eauto with eo.
  Qed.
  Hint Resolve local_trans_le_r : eo.

  Lemma local_trans_le_l :
    forall (e1 e2 e3 : Event),
      e1 ⊑ e2 -> e2 ⊏ e3 -> e1 ⊏ e3.
  Proof.
    introv c1 c2.
    destruct c1 as [a b], c2 as [c d].
    split; allrw; auto.
    destruct a; subst; eauto with eo.
  Qed.
  Hint Resolve local_trans_le_l : eo.

  Lemma local_implies_le :
    forall (e1 e2 : Event), e1 ⊏ e2 -> e1 ⊑ e2.
  Proof.
    introv c.
    destruct c as [a b].
    split; auto.
    left; auto.
  Qed.
  Hint Resolve local_implies_le : eo.

  Lemma local_pred_le :
    forall (e : Event), (local_pred e) ⊑ e.
  Proof.
    introv.
    unfold local_pred.
    remember (direct_pred e) as d; symmetry in Heqd; destruct d; eauto 3 with eo.
  Qed.
  Hint Resolve local_pred_le : eo.

  Lemma localHappenedBeforeInd :
    forall P : Event -> Prop,
      (forall e, (forall e', e' ⊏ e -> P e') -> P e)
      -> forall e, P e.
  Proof.
    introv imp; introv.
    pose proof (eo_causal e) as causal.
    induction causal as [e' ih h].
    apply imp; auto.
    introv l.
    apply h; eauto with eo.
  Qed.

  Lemma localHappenedBeforeInd_type :
    forall P : Event -> Type,
      (forall e, (forall e', e' ⊏ e -> P e') -> P e)
      -> forall e, P e.
  Proof.
    introv imp; introv.
    pose proof (eo_causal e) as causal.
    induction causal as [e' ih h].
    apply imp; auto.
    introv l.
    apply h; eauto with eo.
  Qed.

  Definition isFirst (e : Event) : Prop :=
    direct_pred e = None.

  Lemma dec_isFirst :
    forall e, decidable (isFirst e).
  Proof.
    introv.
    unfold isFirst.
    destruct (direct_pred e); prove_dec.
  Qed.

  Lemma local_pred_is_direct_pred :
    forall e,
      ~ isFirst e
      -> (local_pred e) ⊂ e .
  Proof.
    introv ni.
    unfold local_pred.
    unfold isFirst in ni.
    destruct (direct_pred e); tcsp.
  Qed.
  Hint Resolve local_pred_is_direct_pred : eo.

  Lemma local_pred_is_localCausal :
    forall e,
      ~ isFirst e
      -> (local_pred e) ⊏ (e).
  Proof.
    introv ni.
    apply local_pred_is_direct_pred in ni.
    apply pred_implies_local; auto.
  Qed.
  Hint Resolve local_pred_is_localCausal : eo.

  Lemma local_pred_is_causal :
    forall e,
      ~ isFirst e
      -> (local_pred e) ≺ (e).
  Proof.
    introv ni.
    apply local_pred_is_localCausal in ni.
    destruct ni; auto.
  Qed.
  Hint Resolve local_pred_is_causal : eo.

  Lemma predHappenedBeforeInd :
    forall P : Event -> Prop,
      (forall e, (forall e', e' ⊂ e -> P e') -> P e)
      -> forall e, P e.
  Proof.
    introv imp; introv.
    pose proof (eo_causal e) as causal.
    induction causal as [e' ih h].
    apply imp; auto.
    introv l.
    apply h; eauto with eo.
  Qed.

  Lemma predHappenedBeforeInd_local_pred :
    forall P : Event -> Prop,
      (forall e, (~ isFirst e -> P (local_pred e)) -> P e)
      -> forall e, P e.
  Proof.
    introv imp; introv.
    pose proof (eo_causal e) as causal.
    induction causal as [e' ih h].
    apply imp; auto.
    introv l.
    apply h; eauto with eo.
  Qed.

  Lemma predHappenedBeforeInd_type :
    forall P : Event -> Type,
      (forall e, (forall e', e' ⊂ e -> P e') -> P e)
      -> forall e, P e.
  Proof.
    introv imp; introv.
    pose proof (eo_causal e) as causal.
    induction causal as [e' ih h].
    apply imp; auto.
    introv l.
    apply h; eauto with eo.
  Qed.

  Lemma predHappenedBeforeInd_local_pred_type :
    forall P : Event -> Type,
      (forall e, (~ isFirst e -> P (local_pred e)) -> P e)
      -> forall e, P e.
  Proof.
    introv imp; introv.
    pose proof (eo_causal e) as causal.
    induction causal as [e' ih h].
    apply imp; auto.
    introv l.
    apply h; eauto with eo.
  Qed.

  Lemma not_direct_pred :
    forall (e e1 e2 : Event),
      e1 ⊂ e
      -> e2 ⊏ e
      -> e1 <> e2
      -> e2 ⊏ e1.
  Proof.
    introv p l d.
    applydup eo_direct_pred_local in p.
    allunfold localHappenedBefore; repnd; dands;[|rewrite l;auto];[].
    pose proof (eo_local_order e2 e e1) as h.
    repeat (autodimp h hyp); repndors; subst; auto; try (complete (destruct d;auto)).
  Qed.

  Lemma causal_anti_reflexive :
    forall (e : Event), ~ e ≺ e.
  Proof.
    introv.
    induction e as [e ind] using HappenedBeforeInd.
    introv h.
    pose proof (ind e h h) as q; auto.
  Qed.

  Lemma localCausal_anti_reflexive :
    forall (e : Event), ~ e ⊏ e.
  Proof.
    introv h.
    apply local_implies_causal in h.
    apply causal_anti_reflexive in h; auto.
  Qed.

  Lemma pred_anti_reflexive :
    forall (e : Event), ~ e ⊂ e.
  Proof.
    introv h.
    apply (causal_anti_reflexive e); eauto with eo.
  Qed.

  Lemma local_implies_pred_or_local :
    forall (e1 e2 : Event),
      e1 ⊏ e2
      -> (e1 ⊂ e2 [+] {e : Event & e ⊂ e2 /\ e1 ⊏ e}).
  Proof.
    introv l.
    induction e2 as [e ind] using predHappenedBeforeInd_type.
    remember (direct_pred e) as q; destruct q as [e'|].
    - symmetry in Heqq.
      pose proof (ind e') as h; clear ind.
      pose proof (eo_local_order e1 e e') as q; repeat (autodimp q hyp); eauto with eo.
      repndors; subst; auto.
      right; exists e'; dands; auto.
      applydup local_implies_loc in l.
      applydup pred_implies_loc in Heqq.
      repeat (autodimp h hyp); eauto with eo.
      { split; eauto with eo.
        rewrite l0; auto. }
      repndors; eauto with eo.
      exrepnd; eauto with eo.
    - clear ind.
      symmetry in Heqq.
      pose proof (eo_direct_pred_first e Heqq) as q.
      clear Heqq; rename q into Heqq.
      pose proof (Heqq e1) as h; clear Heqq.
      destruct (eventDeq e e1) as [d|d]; subst.
      { apply localCausal_anti_reflexive in l; tcsp. }
      repeat (autodimp h hyp); eauto with eo.
      pose proof (causal_trans e1 e e1) as q.
      repeat (autodimp q hyp); eauto with eo.
      apply causal_anti_reflexive in q; sp.
  Qed.

  Lemma local_implies_local_or_pred :
    forall (e1 e2 : Event),
      e1 ⊏ e2
      -> (e1 ⊂ e2 [+] {e : Event & e1 ⊂ e /\ e ⊏ e2}).
  Proof.
    introv l.
    induction e2 as [e ind] using predHappenedBeforeInd_type.
    remember (direct_pred e) as q; destruct q as [e'|].
    - symmetry in Heqq.
      pose proof (ind e') as h; clear ind.
      pose proof (eo_local_order e1 e e') as q; repeat (autodimp q hyp); eauto with eo.
      repndors; subst; auto.
      right.
      applydup local_implies_loc in l.
      applydup pred_implies_loc in Heqq.
      repeat (autodimp h hyp); eauto with eo.
      { split; eauto with eo.
        rewrite l0; auto. }
      repndors; exrepnd; eexists; dands; eauto with eo.
    - clear ind.
      symmetry in Heqq.
      pose proof (eo_direct_pred_first e Heqq) as q.
      clear Heqq; rename q into Heqq.
      pose proof (Heqq e1) as h; clear Heqq.
      destruct (eventDeq e e1) as [d|d]; subst.
      { apply localCausal_anti_reflexive in l; tcsp. }
      repeat (autodimp h hyp); eauto with eo.
      pose proof (causal_trans e1 e e1) as q.
      repeat (autodimp q hyp); eauto with eo.
      apply causal_anti_reflexive in q; sp.
  Qed.

  Lemma snoc_inj :
    forall {A} (l k : list A) a b,
      snoc l a = snoc k b
      -> l = k /\ a = b.
  Proof.
    induction l; simpl; introv h.
    - destruct k; simpl in *; ginv; tcsp.
      destruct k; simpl in *; ginv.
    - destruct k; simpl in *; ginv; tcsp.
      + destruct l; simpl in *; ginv; tcsp.
      + inversion h; subst; clear h.
        match goal with
        | [ H : _ |- _ ] => apply IHl in H
        end; repnd; subst; tcsp.
  Qed.

  (* @Ivana localPred is history *)
  Lemma localPreds_lem :
    forall (e : Event),
      {l : list Event
           & forall a b, adjacent a b (snoc l e) <-> (a ⊂ b /\ a ⊏ e) }.
  Proof.
    introv.
    induction e as [e ind] using predHappenedBeforeInd_type.
    remember (direct_pred e) as q; destruct q as [e'|].
    - symmetry in Heqq.
      pose proof (ind e') as h; clear ind; autodimp h hyp; exrepnd.
      exists (snoc l e'); dands.
      introv; split; intro h.
      + rewrite adjacent_snoc in h; repndors;
          try (complete (apply h0 in h; repnd; dands; eauto with eo));
          try (complete (inversion h as [|? ? xx]; subst; inversion xx)).
        exrepnd; ginv; subst.
        apply snoc_inj in h2; repnd; subst.
        dands; eauto with eo.
      + repnd.
        apply local_implies_pred_or_local in h; repndors.
        * rewrite Heqq in h; ginv.
          pose proof (eo_direct_pred_inj b e) as q.
          rewrite h1 in q; rewrite Heqq in q; repeat (autodimp q hyp); subst; GC.
          { apply pred_implies_loc in h1.
            apply pred_implies_loc in Heqq.
            allrw <-; auto. }
          apply adjacent_snoc; right.
          exists l; auto.
        * exrepnd.
          rewrite Heqq in h3; ginv.
          apply adjacent_snoc; left.
          apply h0; dands; eauto with eo.
    - clear ind.
      exists ([] : list Event); simpl; split; introv h; repnd; dands; eauto with eo;
        try (complete (inversion h as [|? ? xx]; subst; inversion xx)).
      apply local_implies_pred_or_local in h; repndors; exrepnd.
      + rewrite h in Heqq; ginv.
      + rewrite h2 in Heqq; ginv.
  Qed.

  Definition localPreds (e : Event) : list Event :=
    projT1 (localPreds_lem e).

  Notation "History( a )" := (localPreds a) (at level 0).

  Lemma snoc_as_app {T} :
    forall (a : T) (l : list T),
      snoc l a = l ++ [a].
  Proof.
    induction l; simpl; introv; tcsp.
    rewrite IHl; simpl; auto.
  Qed.

  Lemma localPreds_prop1 :
    forall (e e' : Event),
      In e' (localPreds e) <-> e' ⊏ e.
  Proof.
    introv.
    unfold localPreds.
    remember (localPreds_lem e) as h; exrepnd; simpl; clear Heqh.
    split; intro q.
    - pose proof (in_implies_adjacent _ l [e] e') as x; simpl in x.
      repeat (autodimp x hyp); exrepnd.
      rewrite <- snoc_as_app in x0.
      apply h0 in x0; tcsp.
    - apply local_implies_local_or_pred in q; repndors.
      + pose proof (h0 e' e) as h; clear h0.
        destruct h as [h1 h2]; clear h1.
        autodimp h2 hyp; dands; eauto with eo.
        apply adjacent_in_left in h2.
        rewrite in_snoc in h2; repndors; auto; subst.
        apply pred_anti_reflexive in q; sp.
      + exrepnd.
        pose proof (h0 e' e0) as h; clear h0.
        destruct h as [h1 h2]; clear h1.
        autodimp h2 hyp; eauto with eo list.
  Qed.

  Definition get_first (e : Event) : Event :=
    match localPreds e with
    | [] => e
    | e' :: _ => e'
    end.

  Definition is_first (e : Event) : bool :=
    match direct_pred e with
    | Some _ => false
    | None => true
    end.

  Definition if_not_first (e : Event) (P : Prop) : Prop:=
    ~ isFirst e -> P.

  Lemma if_not_first_if_first :
    forall e P,
      isFirst e
      -> if_not_first e P.
  Proof.
    introv h q; tcsp.
  Qed.
  Hint Resolve if_not_first_if_first : eo.

  Lemma if_not_first_implies_or :
    forall e P,
      if_not_first e P
      -> (isFirst e \/ (~ isFirst e /\ P)).
  Proof.
    introv h.
    unfold if_not_first in h.
    destruct (dec_isFirst e) as [d|d]; tcsp.
  Qed.

  Lemma localPreds_cond_implies_in :
    forall a b e l,
      adjacent a b l
      -> (forall a b : Event, adjacent a b (snoc l e) -> (a) ⊂ (b) /\ (a) ⊏ (e))
      -> (b) ⊏ (e).
  Proof.
    induction l; simpl; introv adj cond.

    - inversion adj.

    - inversion adj as [|? ? adj1]; subst; clear adj; simpl in *.

      + destruct l0; simpl in *.

        * pose proof (cond b e) as q.
          autodimp q hyp; tcsp.

        * pose proof (cond b e0) as q.
          autodimp q hyp; tcsp.

      + apply IHl in adj1; auto.
  Qed.

  Lemma localPreds_cond_implies_in2 :
    forall b l x,
      In b l
      -> (forall a b : Event, adjacent a b (snoc l x) -> (a) ⊂ (b))
      -> (b) ⊏ (x).
  Proof.
    induction l using list_ind_snoc; introv i cond; simpl in *; tcsp.
    apply in_snoc in i; repndors; subst; tcsp.
    { pose proof (IHl a) as q.
      repeat (autodimp q hyp).
      { introv adj.
        apply cond.
        apply adjacent_snoc; tcsp. }
      pose proof (cond a x) as h.
      autodimp h hyp.
      { apply adjacent_snoc; right; eexists; dands; eauto. }
      repnd.
      eapply local_trans;[exact q|].
      eauto 3 with eo. }

    clear IHl.
    pose proof (cond a x) as h.
    autodimp h hyp.
    { apply adjacent_snoc; right; eexists; dands; eauto. }
    repnd.
    eauto 3 with eo.
  Qed.

  Lemma localPreds_cond_implies_in3 :
    forall l2 l1 b,
      In b l1
      -> (forall a b : Event, adjacent a b (l1 ++ l2) -> (a) ⊂ (b))
      -> forall x, In x l2 -> (b) ⊏ (x).
  Proof.
    induction l2 using list_ind_snoc; simpl; introv i cond j; tcsp.

    apply in_snoc in j; repndors; subst.

    { apply (IHl2 l1 _); auto.
      introv adj; apply cond.
      rewrite app_snoc; simpl.
      apply adjacent_snoc; tcsp. }

    rewrite app_snoc in cond.
    pose proof (IHl2 l1 b) as q; repeat (autodimp q hyp).

    { introv adj; apply cond.
      apply adjacent_snoc; tcsp. }

    destruct (snoc_cases l2); exrepnd; subst; autorewrite with core in *; simpl in *; tcsp.

    { clear q IHl2.
      apply (localPreds_cond_implies_in2 b l1 a); auto. }

    pose proof (q a0) as h; rewrite in_snoc in h; autodimp h hyp.

    pose proof (cond a0 a) as z; autodimp z hyp.

    { rewrite app_snoc.
      apply adjacent_snoc; right; eexists; dands; auto. }
    repnd.

    eapply local_trans;[exact h|]; auto; eauto with eo.
  Qed.

  Lemma localPreds_cond_implies_in4 :
    forall b l x,
      In b l
      -> (forall a b : Event, adjacent a b (x :: l) -> (a) ⊂ (b))
      -> (x) ⊏ (b).
  Proof.
    induction l; introv i cond; simpl in *; tcsp.
    repndors; subst; tcsp.

    {
      pose proof (cond x b) as q; autodimp q hyp.
      apply pred_implies_local; auto.
    }

    {
      pose proof (cond x a) as q; autodimp q hyp.
      pose proof (IHl a) as h; repeat (autodimp h hyp).
      eapply local_trans;[|eauto].
      apply pred_implies_local; auto.
    }
  Qed.

  Lemma adjacent_single :
    forall {T} (a b c : T), ~ adjacent a b [c].
  Proof.
    introv adj.
    inversion adj as [|? ? adj1]; subst; clear adj.
    inversion adj1.
  Qed.

  Lemma pred_implies_local_pred :
    forall a b, (a) ⊂ (b) -> a = local_pred b.
  Proof.
    introv h.
    unfold local_pred.
    rewrite h; auto.
  Qed.

  Lemma pred_implies_not_first :
    forall a b,
      a ⊂ b ->  ~ isFirst b.
  Proof.
    introv h.
    unfold isFirst.
    rewrite h; tcsp.
  Qed.
  Hint Resolve pred_implies_not_first : eo.

  Lemma local_causal_implies_not_first :
    forall a b,
      a ⊏ b ->  ~ isFirst b.
  Proof.
    introv h.
    apply local_implies_pred_or_local in h; repndors; exrepnd; eauto with eo.
  Qed.
  Hint Resolve local_causal_implies_not_first : eo.

  Lemma isFirst_implies_local_pred_eq :
    forall e, isFirst e -> local_pred e = e.
  Proof.
    introv isf.
    unfold local_pred.
    rewrite isf; auto.
  Qed.

  Lemma isFirst_implies_localPreds_eq :
    forall e, isFirst e -> localPreds e = [].
  Proof.
    introv isf.
    unfold localPreds.
    remember (localPreds_lem e) as lp; exrepnd; simpl in *; clear Heqlp.
    destruct (snoc_cases l) as [d|d]; auto.
    assert False; tcsp.
    exrepnd; subst.
    pose proof (lp0 a e) as q; destruct q as [q q']; clear q'.
    autodimp q hyp.
    { apply adjacent_snoc; right; eexists; dands; auto. }
    repnd.
    apply pred_implies_not_first in q0; tcsp.
  Qed.

  Lemma loc_local_pred :
    forall (e : Event), loc (local_pred e) = loc e.
  Proof.
    introv; unfold local_pred.
    remember (direct_pred e) as dp; destruct dp; auto; symmetry in Heqdp.
    apply pred_implies_loc; auto.
  Qed.
  Hint Rewrite loc_local_pred : eo.

  Lemma localHappenedBefore_if_isFirst :
    forall e1 e2,
      loc e1 = loc e2
      -> isFirst e1
      -> e1 <> e2
      -> e1 ⊏ e2.
  Proof.
    intro e1; induction e2 as [e2 ind] using predHappenedBeforeInd; introv eqloc isf de.

    destruct (dec_isFirst e2) as [d1|d1].

    - clear ind.
      destruct de.
      unfold isFirst in *.
      rewrite <- isf in d1.
      apply eo_direct_pred_inj in d1; auto.

    - destruct (eventDeq e1 (local_pred e2)) as [d|d]; subst; eauto with eo.
      pose proof (ind (local_pred e2)) as q.
      autorewrite with eo in q.
      repeat (autodimp q hyp); eauto with eo.
  Qed.

  Lemma causalLe_trans :
    forall (e1 e2 e3 : Event),
      e1 ≼ e2 -> e2 ≼ e3 -> e1 ≼ e3.
  Proof.
    introv c1 c2.
    destruct c1, c2; subst; tcsp.
    left; eapply causal_trans; eauto.
  Qed.
  Hint Resolve causalLe_trans : eo.

  Lemma isFirst_loc_implies_causal :
    forall (e e' : Event),
      isFirst e
      -> loc e = loc e'
      -> e ≼ e'.
  Proof.
    induction e' as [e' ind] using predHappenedBeforeInd_type.
    introv isF eqloc.
    remember (direct_pred e') as dp; symmetry in Heqdp; destruct dp.
    - applydup pred_implies_loc in Heqdp.
      pose proof (ind e0) as h; repeat (autodimp h hyp); allrw; auto.
      eapply causalLe_trans;[eauto|].
      left.
      apply pred_implies_causal; auto.
    - clear ind.
      unfold isFirst in isF.
      pose proof (eo_direct_pred_first e isF) as h.
      destruct (eventDeq e e');subst;[right;auto|];[].
      pose proof (h e') as q; clear isF.
      repeat (autodimp q hyp).
      left; auto.
  Qed.

  Lemma no_local_predecessor_if_first :
    forall (e e' : Event),
      isFirst e
      -> ~ (e' ⊏ e).
  Proof.
    introv isf lte.
    destruct lte as [a b].
    pose proof (isFirst_loc_implies_causal e e') as q; repeat (autodimp q hyp).
    destruct q as [q|q]; subst.
    { eapply causal_trans in q;[|exact a].
      apply causal_anti_reflexive in q; tcsp. }
    apply causal_anti_reflexive in a; tcsp.
  Qed.

  Lemma tri_if_same_loc :
    forall e1 e2,
      loc e1 = loc e2
      -> (e1 ⊏ e2 \/ e1 = e2 \/ e2 ⊏ e1).
  Proof.
    induction e1 as [e1 ind] using predHappenedBeforeInd; introv eqloc.

    destruct (dec_isFirst e1) as [d1|d1].

    - clear ind.
      destruct (eventDeq e1 e2) as [d2|d2]; subst; tcsp.
      left.
      apply localHappenedBefore_if_isFirst; auto.

    - pose proof (ind (local_pred e1)) as q; clear ind; autodimp q hyp; eauto with eo.
      autorewrite with eo in *.
      pose proof (q e2) as h; clear q; autodimp h hyp.
      repndors.

      + apply local_implies_local_or_pred in h; repndors; exrepnd.

        { rewrite <- local_pred_is_direct_pred in h; auto.
          apply eo_direct_pred_inj in h; tcsp. }

        { rewrite <- local_pred_is_direct_pred in h1; auto.
          apply eo_direct_pred_inj in h1; subst; tcsp.
          apply local_implies_loc in h0; allrw; auto. }

      + subst.
        right; right; eauto with eo.

      + right; right; eauto with eo.
  Qed.

  Lemma causal_implies_causalLe :
    forall (e1 e2 : Event), e1 ≺ e2 -> e1 ≼ e2.
  Proof.
    introv c; left; auto.
  Qed.
  Hint Resolve causal_implies_causalLe : eo.

  Lemma localLe_trans :
    forall (e1 e2 e3 : Event),
      e1 ⊑ e2 -> e2 ⊑ e3 -> e1 ⊑ e3.
  Proof.
    introv c1 c2.
    destruct c1, c2; subst; tcsp.
    split; allrw; auto.
    eapply causalLe_trans; eauto.
  Qed.
  Hint Resolve localLe_trans : eo.

  Definition subEventOrdering_cond (e e' : Event) : Prop :=
    loc e' = loc e -> e ≼ e'.

  Lemma subEventOrdering_causalLe_loc_dec :
    forall e e', loc e = loc e' -> decidable (e ≼ e').
  Proof.
    introv.
    revert dependent e'.
    induction e' as [e' ind] using predHappenedBeforeInd_type.
    introv eqloc.
    remember (direct_pred e') as d; symmetry in Heqd; destruct d.

    - applydup pred_implies_loc in Heqd.
      pose proof (ind e0) as q; repeat (autodimp q hyp);[allrw; auto|].
      destruct q as [q|q].

      + left.
        eapply causalLe_trans;[exact q|].
        left; apply pred_implies_causal; auto.

      + destruct (eventDeq e e'); subst;[left;right;auto|];[].
        right; intro xx.
        destruct (eventDeq e e0); subst;[destruct q;right; auto|];[].
        destruct xx as [xx|xx]; tcsp;[].
        pose proof (not_direct_pred e' e0 e) as z.
        repeat (autodimp z hyp).
        { split; auto. }
        destruct q; left; destruct z; auto.

    - clear ind.
      destruct (eventDeq e e'); subst;[left;right;auto|];[].
      right; intro xx.
      destruct xx as [xx|xx]; tcsp;[].

      pose proof (local_implies_pred_or_local e e') as z.
      autodimp z hyp;[split; auto|];[].
      repndors.

      + rewrite Heqd in z; ginv.

      + exrepnd.
        rewrite Heqd in z1; ginv.
  Qed.

  Lemma subEventOrdering_cond_dec :
    forall e e', decidable (subEventOrdering_cond e e').
  Proof.
    introv.
    destruct (name_dec (loc e') (loc e)) as [d|d].

    - destruct (subEventOrdering_causalLe_loc_dec e e'); auto.

      + left; intro q; auto.

      + right; intro q.
        unfold subEventOrdering_cond in q.
        autodimp q hyp.

    - left.
      intro h; tcsp.
  Qed.

  Definition subEventOrdering_cond_bool (e e' : Event) : Prop :=
    (if subEventOrdering_cond_dec e e' then true else false) = true.

  Lemma subEventOrdering_cond_bool_iff :
    forall e e',
      subEventOrdering_cond_bool e e'
      <-> subEventOrdering_cond e e'.
  Proof.
    introv; split; intro h; unfold subEventOrdering_cond_bool in *; dest_cases w.
  Qed.

  Record subEventOrdering_type (e : Event) :=
    MkSubEvent
      {
        sub_eo_event :> Event;
        sub_eo_cond : subEventOrdering_cond_bool e sub_eo_event
      }.

  Definition mkSubOrderingLe {e e' : Event} (p : e ⊑ e') : subEventOrdering_type e.
  Proof.
    introv.
    exists e'.
    apply subEventOrdering_cond_bool_iff.
    unfold subEventOrdering_cond.
    introv eqloc.
    destruct p as [p1 p2].
    exact p1.
  Defined.

  Definition subEventOrdering_happenedBefore (e : Event) :
    subEventOrdering_type e
    -> subEventOrdering_type e
    -> Prop.
  Proof.
    intros p q.
    destruct p as [p condp].
    destruct q as [q condq].
    exact (happenedBefore p q).
  Defined.

  Definition subEventOrdering_loc (e : Event) :
    subEventOrdering_type e -> name.
  Proof.
    intros p.
    destruct p as [p cond].
    exact (loc p).
  Defined.

  Lemma subEventOrdering_cond_bool_local_pred :
    forall (e e' : Event),
      subEventOrdering_cond_bool e e'
      -> loc e' = loc e
      ->  e <> e'
      -> subEventOrdering_cond_bool e (local_pred e').
  Proof.
    introv cond eqloc d.
    allrw subEventOrdering_cond_bool_iff.
    unfold subEventOrdering_cond in *.
    autodimp cond hyp.
    destruct cond as [s|s]; tcsp;[].
    unfold local_pred.
    remember (direct_pred e') as dp; symmetry in Heqdp; destruct dp.

    - destruct (subEventOrdering_cond_dec e e0); ginv;[].
      destruct n.
      introv xx.
      destruct (eventDeq e e0);[right;auto|];[].
      pose proof (not_direct_pred e' e0 e) as q.
      repeat (autodimp q hyp).
      { split; auto. }
      { apply local_implies_causal in q; left; auto. }

    - pose proof (local_implies_pred_or_local e e') as q.
      autodimp q hyp;[split;auto|].
      rewrite Heqdp in q; repndors; tcsp.
  Qed.

  Lemma diff_first_iff_not_first :
    forall (e : Event), e <> get_first e <-> ~ isFirst e.
  Proof.
    introv.
    unfold get_first, isFirst; split; intro h.

    - intro q.
      destruct h.
      rewrite isFirst_implies_localPreds_eq; auto.

    - intro q; destruct h.
      remember (localPreds e) as l; symmetry in Heql; destruct l; GC.

      + unfold localPreds in Heql.
        remember (localPreds_lem e) as q; exrepnd; simpl in *; subst.
        clear Heqq; simpl in *.
        remember (direct_pred e) as dp; destruct dp; symmetry in Heqdp; auto.
        pose proof (q0 e0 e) as h; clear q0; destruct h as [q' q]; clear q'.
        autodimp q hyp; dands; auto.
        { apply pred_implies_local; auto. }
        apply adjacent_single in q; tcsp.

      + subst.
        pose proof (localPreds_prop1 e0 e0) as q.
        rewrite Heql in q; simpl in q.
        destruct q as [q q']; clear q'.
        autodimp q hyp.
        apply localCausal_anti_reflexive in q; tcsp.
  Qed.

  Lemma eq_first_iff_first :
    forall (e : Event), e = get_first e <-> isFirst e.
  Proof.
    introv; split; intro h.
    - destruct (dec_isFirst e) as [i|i]; auto.
      apply diff_first_iff_not_first in i; tcsp.
    - destruct (eventDeq e (get_first e)) as [q|q]; auto.
      apply diff_first_iff_not_first in q; tcsp.
  Qed.

  Definition subEventOrdering_direct_pred (e : Event) :
    subEventOrdering_type e -> option (subEventOrdering_type e).
  Proof.
    intros p; exrepnd.
    destruct p as [p cond].
    destruct (name_dec (loc p) (loc e)) as [d|d].

    - (* e and e' happened at the same location *)
      destruct (eventDeq e p);[exact None|].
      left; exists (local_pred p).
      apply subEventOrdering_cond_bool_local_pred; auto.

    - (* e and e' happened at different locations, then we can just take the
         direct predecessor of e' according to the original event ordering eo *)
      destruct (eventDeq p (get_first p));[exact None|left].
      exists (local_pred p).
      apply subEventOrdering_cond_bool_iff.
      introv xx.
      rewrite loc_local_pred in xx; tcsp.
  Defined.

  (*
  Definition subEventOrdering_direct_pred (e : Event) :
    subEventOrdering_type e -> option (subEventOrdering_type e).
  Proof.
    unfold subEventOrdering_type.
    intros p; exrepnd.
    destruct (name_dec (loc e') (loc e)) as [d|d].

    - (* e and e' happened at the same location *)
      destruct (eventDeq e e'); subst;[exact None|].
      left; exists (local_pred e').
      apply subEventOrdering_cond_bool_local_pred; auto.

    - (* e and e' happened at different locations, then we can just take the
         direct predecessor of e' according to the original event ordering eo *)
      remember (direct_pred e') as eop; symmetry in Heqeop; destruct eop;[left|right].
      exists e0.
      unfold subEventOrdering_cond_bool.
      destruct (subEventOrdering_cond_dec e e0);auto.
      destruct n0.
      intro xx.
      apply pred_implies_loc in Heqeop.
      rewrite Heqeop in xx; tcsp.
  Defined.*)

  Definition subEventOrdering_trigger (e : Event) :
    subEventOrdering_type e -> trigger_info.
  Proof.
    intros p; exrepnd.
    destruct p as [p cond].
    exact (trigger p).
  Defined.

  Definition subEventOrdering_time (e : Event) :
    subEventOrdering_type e -> Qpos.
  Proof.
    intros p; exrepnd.
    destruct p as [p cond].
    exact (time p).
  Defined.

(*  Definition subEventOrdering_mode (e : Event) :
    subEventOrdering_type e -> EventStatus.
  Proof.
    intros p; exrepnd.
    destruct p as [p cond].
    exact (mode p).
  Defined.*)

  Definition subEventOrdering_keys (e : Event) :
    subEventOrdering_type e -> local_key_map.
  Proof.
    intros p; exrepnd.
    destruct p as [p cond].
    exact (keys p).
  Defined.

  Lemma subEventOrdering_Deq : forall (e : Event), Deq (subEventOrdering_type e).
  Proof.
    repeat introv.
    destruct x as [x condx].
    destruct y as [y condy].
    destruct (eventDeq x y); subst;[|prove_dec];[].
    left; f_equal; apply UIP_dec; apply bool_dec.
  Qed.

  Lemma subEventOrdering_wf : forall (e : Event), well_founded (subEventOrdering_happenedBefore e).
  Proof.
    introv.
    unfold subEventOrdering_happenedBefore.
    introv.
    destruct a as [a conda]; simpl in *.

    pose proof (causalWf a) as wf.
    induction wf as [e0 ih h].

    constructor; simpl in *.
    introv z.
    destruct y as [y condy].

    pose proof (h y z condy) as q; auto.
  Qed.

  Lemma subEventOrdering_trans :
    forall (e : Event),
      transitive (subEventOrdering_type e) (subEventOrdering_happenedBefore e).
  Proof.
    introv h1 h2.
    destruct x, y, z; simpl in *.
    eapply causalTrans; eauto.
  Qed.

  Lemma subEventOrdering_direct_pred_some_implies :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
      subEventOrdering_direct_pred e e1 = Some e2
      -> direct_pred e1 = Some (sub_eo_event e e2).
  Proof.
    introv h.
    destruct e1 as [e1 conde1], e2 as [e2 conde2]; simpl in *.
    unfold subEventOrdering_direct_pred in h; simpl in *.
    destruct (name_dec (loc e1) (loc e));[|].

    { dest_cases w; subst; ginv; GC;[].
      inversion h as [q]; clear h.
      unfold local_pred.
      remember (direct_pred e1) as dp; symmetry in Heqdp; destruct dp; auto.
      unfold local_pred in q; rewrite Heqdp in q; subst.
      unfold subEventOrdering_cond_bool in *.
      destruct (subEventOrdering_cond_dec e e2); ginv.
      unfold subEventOrdering_cond in *.
      autodimp s hyp.
      destruct s as [s1|s1]; tcsp;[].
      pose proof (local_implies_pred_or_local e e2) as q.
      rewrite Heqdp in q.
      autodimp q hyp;[split; auto|].
      repndors; exrepnd; tcsp. }

    { dest_cases w.
      inversion h; clear h.
      apply diff_first_iff_not_first in n0.
      apply local_pred_is_direct_pred; auto. }
  Qed.

  Lemma subEventOrdering_direct_pred_some_iff :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
      subEventOrdering_direct_pred e e1 = Some e2
      <-> direct_pred e1 = Some (sub_eo_event e e2).
  Proof.
    introv; split; intro h.
    - apply subEventOrdering_direct_pred_some_implies; auto.
    - destruct e1 as [e1 cond1], e2 as [e2 cond2]; simpl in *.
      unfold subEventOrdering_direct_pred; simpl.
      destruct (name_dec (loc e1) (loc e));[|].

      { dest_cases w; subst; ginv; GC;[|].

        - unfold eq_rect_r; simpl.
          assert False; tcsp.
          apply subEventOrdering_cond_bool_iff in cond2.
          unfold subEventOrdering_cond in cond2; autodimp cond2 hyp.
          { apply pred_implies_loc in h; auto. }
          destruct cond2 as [s0|s0]; subst.
          { eapply causal_trans in s0;[|apply pred_implies_causal; eauto].
            apply causal_anti_reflexive in s0; auto. }
          { apply pred_anti_reflexive in h; auto. }

        - f_equal.
          assert (local_pred e1 = e2) as xx; subst;[unfold local_pred;allrw;auto|].
          f_equal.
          remember (subEventOrdering_cond_bool_local_pred e e1 cond1 e0 w) as q.
          apply UIP_dec; apply bool_dec. }

      { dest_cases w;[|].

        - apply eq_first_iff_first in e0.
          unfold isFirst in e0.
          rewrite h in e0; ginv.

        - f_equal.
          apply diff_first_iff_not_first in n0.
          assert (e2 = local_pred e1) as xx.
          { unfold local_pred; rewrite h; auto. }
          subst; f_equal.
          apply UIP_dec; apply bool_dec. }
  Qed.

  Lemma subEventOrdering_axiom_direct_pred_local :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
      subEventOrdering_direct_pred e e1 = Some e2
      -> subEventOrdering_loc e e1 = subEventOrdering_loc e e2.
  Proof.
    introv h.
    apply subEventOrdering_direct_pred_some_iff in h.
    destruct e1, e2; simpl in *.
    apply pred_implies_loc in h; auto.
  Qed.

  Lemma subEventOrdering_axiom_direct_pred_ord :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
      subEventOrdering_direct_pred e e1 = Some e2
      -> subEventOrdering_happenedBefore e e2 e1.
  Proof.
    introv h.
    apply subEventOrdering_direct_pred_some_iff in h.
    destruct e1, e2; simpl in *.
    apply pred_implies_causal in h; auto.
  Qed.

  Lemma loc_get_first :
    forall (e : Event), loc (get_first e) = loc e.
  Proof.
    introv; unfold get_first.
    remember (localPreds e) as lp; destruct lp; auto.
    pose proof (localPreds_prop1 e e0) as q.
    rewrite <- Heqlp in q; simpl in q.
    destruct q as [q q']; clear q'; autodimp q hyp.
    destruct q; auto.
  Qed.
  Hint Rewrite loc_get_first : eo.

  Lemma get_first_le :
    forall (e e' : Event), loc e = loc e'-> (get_first e) ≼ e'.
  Proof.
    introv eqloc.
    apply isFirst_loc_implies_causal;[|rewrite loc_get_first;auto].
    unfold isFirst, get_first, localPreds.
    remember (localPreds_lem e) as lp.
    exrepnd; simpl in *.
    clear Heqlp; simpl.
    destruct l; simpl in *.

    - remember (direct_pred e) as q; symmetry in Heqq; destruct q; auto.
      assert False; tcsp.
      pose proof (lp0 e0 e) as h; destruct h as [h' h]; clear h'.
      autodimp h hyp; dands; auto.
      { apply pred_implies_local in Heqq; auto. }
      apply adjacent_single in h; tcsp.

    - remember (direct_pred e0) as q; symmetry in Heqq; destruct q; auto.
      assert False; tcsp.
      pose proof (localPreds_cond_implies_in2 e0 (e0 :: l) e) as h; simpl in h.
      repeat (autodimp h hyp).
      { introv h; apply lp0 in h; tcsp. }
      pose proof (lp0 e1 e0) as z; destruct z as [z' z]; clear z'.
      autodimp z hyp; dands; auto.
      { eapply local_trans;[|eauto].
        apply pred_implies_local; auto. }

      inversion z as [?|? ? adj]; subst; clear z.

      { apply pred_anti_reflexive in Heqq; auto. }

      pose proof (localPreds_cond_implies_in4 e0 (snoc l e) e0) as q.
      repeat (autodimp q hyp).

      { apply adjacent_in_right in adj; auto. }

      { introv q; apply lp0 in q; tcsp. }

      apply localCausal_anti_reflexive in q; auto.
  Qed.

  (*
 Lemma get_first_get_first_eq :
    forall (e e' : Event), loc e = loc e'-> get_first e = get_first e'.
  Proof.
    intros e e' H.
    unfold get_first.
    unfold localPreds.
    remember (localPreds_lem e) as lp; exrepnd; clear Heqlp; simpl.
    remember (localPreds_lem e') as lp'; exrepnd; clear Heqlp'; simpl.

    destruct l. destruct l0.
    (* e and e' are first *)
    (* based on lp we should be able to prove that e is first
       based on lp' we should be able to prove that e' is first *)
    (* How we state that a and b are empty Events? *)
    simpl in *.
    pose proof (lp0 e e ) as xx. simpl in xx.

    (* @ Ivana, I need somethig like this, but this contradict the def of adjacent
        should we state that list l has to have at least 2 el? *)
    Lemma adjacent_one_element:
      forall a b e, adjacent a b [e] -> a = Nome /\ b = None.
    Proof.
      intros a b e IH.
      unfold isFirst.
      unfold adjacent in *.
   *)

  Lemma subEventOrdering_axiom_direct_pred_first :
    forall (e : Event),
    forall e0 : subEventOrdering_type e,
      subEventOrdering_direct_pred e e0 = None
      ->
      (forall e' : subEventOrdering_type e,
          subEventOrdering_loc e e' = subEventOrdering_loc e e0
          -> e0 <> e'
          -> subEventOrdering_happenedBefore e e0 e').
  Proof.
    introv.
    destruct e0 as [e0 conde0]; simpl in *; intro h.

    introv eloc diff.
    destruct e' as [e' conde']; simpl in *.
    assert (e0 <> e') as d.
    { intro xx;subst.
      destruct diff;f_equal; apply UIP_dec; apply bool_dec. }
    clear diff.
    destruct (name_dec (loc e0) (loc e)) as [dn|dn].

    - dest_cases w; subst.
      unfold eq_rect_r in h; simpl in h; GC.
      apply subEventOrdering_cond_bool_iff in conde'.
      unfold subEventOrdering_cond in conde'; autodimp conde' hyp.
      destruct conde' as [s0|s0]; subst; tcsp.

    - dest_cases w; GC.
      apply eq_first_iff_first in e1.
      pose proof (isFirst_loc_implies_causal e0 e') as q.
      repeat (autodimp q hyp).
      destruct q; subst; tcsp.
  Qed.

  Lemma happenedBeforeLe_implies_eq :
    forall e1 e2, (e1) ≼ (e2) -> (e2) ≼ (e1) -> e1 = e2.
  Proof.
    introv h q; destruct h as [h|h]; auto; destruct q as [q|q]; auto.
    eapply causal_trans in h;[|exact q].
    apply causal_anti_reflexive in h; tcsp.
  Qed.

  Lemma subEventOrdering_axiom_direct_pred_inj :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
      subEventOrdering_loc e e1 = subEventOrdering_loc e e2
      -> subEventOrdering_direct_pred e e1 = subEventOrdering_direct_pred e e2
      -> e1 = e2.
  Proof.
    introv eqlocs eqpreds.
    destruct e1 as [x s], e2 as [x0 s0]; simpl in *.
    destruct (name_dec (loc x) (loc e)) as [nd|nd].

    { dest_cases w; simpl in *; ginv.

      { apply eq_first_iff_first in e0.

        dup s as cond1.
        apply subEventOrdering_cond_bool_iff in cond1.
        unfold subEventOrdering_cond in cond1.
        autodimp cond1 hyp.

        dup s0 as cond2.
        apply subEventOrdering_cond_bool_iff in cond2.
        unfold subEventOrdering_cond in cond2.
        autodimp cond2 hyp;[allrw <-; auto|].

        assert (e = x0) as xx.
        { destruct cond2 as [cond2|cond2]; auto.
          pose proof (isFirst_loc_implies_causal x0 e) as z;
            repeat (autodimp z hyp);[allrw <-; auto|];[].
          destruct z as [z|z]; auto.
          eapply causal_trans in z;[|exact cond2].
          apply causal_anti_reflexive in z; tcsp. }
        subst x0.
        clear cond2.

        dest_cases w; subst; simpl in *; ginv.

        { unfold eq_rect_r in *; simpl in *.
          dest_cases w; subst; simpl in *; ginv.

          dest_cases w; subst; GC.
          f_equal.
          apply UIP_dec; apply bool_dec. }

        { assert False; tcsp.
          dest_cases w; simpl in *; ginv.
          dest_cases w; subst; simpl in *; ginv; GC. }
      }

      {
        apply diff_first_iff_not_first in n.

        dup s as cond1.
        apply subEventOrdering_cond_bool_iff in cond1.
        unfold subEventOrdering_cond in cond1.
        autodimp cond1 hyp.

        dup s0 as cond2.
        apply subEventOrdering_cond_bool_iff in cond2.
        unfold subEventOrdering_cond in cond2.
        autodimp cond2 hyp;[allrw <-; auto|].

        dest_cases w; simpl in *; subst; ginv.

        {
          unfold eq_rect_r in *; simpl in *.
          dest_cases w; subst; simpl in *; ginv; GC.
          dest_cases w; subst; simpl in *; ginv; GC.
          f_equal.
          apply UIP_dec; apply bool_dec.
        }

        {
          dest_cases w; subst; simpl in *; ginv; GC.

          {
            dest_cases w; subst; simpl in *; ginv; GC.
            inversion eqpreds as [zz]; clear eqpreds.

            assert (~ isFirst x) as nfx.
            {
              intro xx.
              destruct cond1 as [cond1|cond1]; tcsp.
              pose proof (local_implies_pred_or_local e x) as q; autodimp q hyp.
              { split; auto. }
              repndors.
              { apply pred_implies_not_first in q; tcsp. }
              { exrepnd; apply pred_implies_not_first in q1; tcsp. }
            }

            pose proof (local_pred_is_direct_pred x0) as xx; autodimp xx hyp.
            pose proof (local_pred_is_direct_pred x) as yy; autodimp yy hyp.

            rewrite <- zz in xx.
            rewrite <- yy in xx.

            pose proof (eo_direct_pred_inj x0 x) as h; repeat (autodimp h hyp); subst.
            f_equal; apply UIP_dec; apply bool_dec.
          }

          {
            inversion eqpreds as [zz]; clear eqpreds.

            assert (~ isFirst x) as nfx.
            {
              intro xx.
              destruct cond1 as [cond1|cond1]; tcsp.
              pose proof (local_implies_pred_or_local e x) as q; autodimp q hyp.
              { split; auto. }
              repndors.
              { apply pred_implies_not_first in q; tcsp. }
              { exrepnd; apply pred_implies_not_first in q1; tcsp. }
            }

            pose proof (local_pred_is_direct_pred x0) as xx; autodimp xx hyp.
            pose proof (local_pred_is_direct_pred x) as yy; autodimp yy hyp.

            rewrite <- zz in xx.
            rewrite <- yy in xx.

            pose proof (eo_direct_pred_inj x0 x) as h; repeat (autodimp h hyp); subst.
            f_equal; apply UIP_dec; apply bool_dec.
          }
        }
      }
    }

    {
      dest_cases w; simpl in *; ginv.

      {
        apply eq_first_iff_first in e0.
        dest_cases w; simpl in *; ginv.

        {
          apply eq_first_iff_first in e1.
          pose proof (isFirst_loc_implies_causal x x0) as h; repeat (autodimp h hyp).
          pose proof (isFirst_loc_implies_causal x0 x) as q; repeat (autodimp q hyp).
          apply happenedBeforeLe_implies_eq in h; auto; subst.
          f_equal; apply UIP_dec; apply bool_dec.
        }

        {
          apply diff_first_iff_not_first in n.
          dest_cases w; subst; simpl in *; ginv.
          dest_cases w; subst; simpl in *; ginv; tcsp.
        }
      }

      {
        apply diff_first_iff_not_first in n.
        dest_cases w; simpl in *; ginv.

        {
          apply eq_first_iff_first in e0.
          dest_cases w; subst; simpl in *; ginv.
          dest_cases w; subst; simpl in *; ginv.
          destruct nd; allrw; auto.
        }

        {
          apply diff_first_iff_not_first in n0.
          dest_cases w; subst; simpl in *; ginv.

          {
            destruct nd; allrw; auto.
          }

          {
            inversion eqpreds as [zz]; clear eqpreds.

            pose proof (local_pred_is_direct_pred x0) as xx; autodimp xx hyp.
            pose proof (local_pred_is_direct_pred x) as yy; autodimp yy hyp.

            rewrite <- zz in xx.
            rewrite <- yy in xx.

            pose proof (eo_direct_pred_inj x0 x) as h; repeat (autodimp h hyp); subst.
            f_equal; apply UIP_dec; apply bool_dec.
          }
        }
      }
    }
  Qed.

  Lemma subEventOrdering_axiom_local_order :
    forall (e : Event),
    forall e1 e2 e0 : subEventOrdering_type e,
      subEventOrdering_loc e e1 = subEventOrdering_loc e e2
      -> subEventOrdering_happenedBefore e e1 e2
      -> subEventOrdering_direct_pred e e2 = Some e0
      -> e0 = e1 [+] subEventOrdering_happenedBefore e e1 e0.
  Proof.
    introv eqlocs caus pred.
    destruct e1 as [x s], e2 as [x0 s0], e0 as [x1 s1]; simpl in *.
    destruct (name_dec (loc x0) (loc e)) as [nd|nd]; simpl in *; ginv.

    {
      dest_cases w; simpl in *; subst.

      inversion pred as [z]; clear pred.
      unfold local_pred in z.
      remember (direct_pred x0) as dp; symmetry in Heqdp; destruct dp; subst; tcsp.

      pose proof (eo_local_order x x0 x1) as h; repeat (autodimp h hyp).
      repndors; subst; auto.
      left; f_equal; apply UIP_dec; apply bool_dec.
    }

    {
      dest_cases w.
      inversion pred as [z]; clear pred.

      unfold local_pred in z.
      remember (direct_pred x0) as dp; symmetry in Heqdp; destruct dp; subst; tcsp.

      pose proof (eo_local_order x x0 x1) as h; repeat (autodimp h hyp).
      repndors; subst; auto.
      left; f_equal; apply UIP_dec; apply bool_dec.
    }
  Qed.

  Lemma subEventOrdering_axiom_causal_time :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
      subEventOrdering_happenedBefore e e1 e2
      -> Qpos_lt (subEventOrdering_time e e1) (subEventOrdering_time e e2).
  Proof.
    introv caus.
    destruct e1, e2; simpl in *.
    apply eo_causal_time; auto.
  Qed.

  Definition subEventOrdering (e : Event) : EventOrdering.
  Proof.
    (*exists
      (subEventOrdering_type e)
      (subEventOrdering_happenedBefore e)
      (subEventOrdering_loc e)
      (subEventOrdering_direct_pred e)
      (subEventOrdering_time e).*)

    eexists.

    { exact (subEventOrdering_trigger e). }

(*    { exact (subEventOrdering_mode e). }*)

    { exact (subEventOrdering_keys e). }

    { exact (subEventOrdering_Deq e). }

    { exact (subEventOrdering_wf e). }

    { exact (subEventOrdering_trans e). }

    { exact (subEventOrdering_axiom_direct_pred_local e). }

    { exact (subEventOrdering_axiom_direct_pred_ord e). }

    { exact (subEventOrdering_axiom_direct_pred_first e). }

    { exact (subEventOrdering_axiom_direct_pred_inj e). }

    { exact (subEventOrdering_axiom_local_order e). }

    { exact (subEventOrdering_axiom_causal_time e). }
  Defined.

  Lemma trigger_mkSubOrderingLe :
    forall (e e' : Event) (p : e ⊑ e'),
      @trigger (subEventOrdering e) (mkSubOrderingLe p) = trigger e'.
  Proof.
    auto.
  Qed.

  Lemma trigger_in_subEventOrdering :
    forall (e : Event) (e' : subEventOrdering_type e),
      @trigger (subEventOrdering e) e' = trigger e'.
  Proof.
    destruct e'; simpl in *; auto.
  Qed.

  Lemma subEventOrdering_loc_as_loc :
    forall (e : Event) (e' : subEventOrdering_type e),
      subEventOrdering_loc e e' = loc e'.
  Proof.
    destruct e'; simpl in *; auto.
  Qed.

  Lemma localPreds_cond_pred :
    forall l e,
      (forall a b : Event,
          adjacent a b (snoc (snoc l (local_pred e)) e) <-> (a) ⊂ (b) /\ (a) ⊏ (e))
      -> forall a b : Event,
        adjacent a b (snoc l (local_pred e)) <-> (a) ⊂ (b) /\ (a) ⊏ (local_pred e).
  Proof.
    introv cond; introv; split; intro h.

    - pose proof (cond a b) as q; destruct q as [q q']; clear q'.
      autodimp q hyp.
      { apply adjacent_snoc; tcsp. }
      repnd; dands; auto.
      apply adjacent_snoc in h; repndors.

      {
        pose proof (localPreds_cond_implies_in3 [local_pred e, e] l a) as z.
        repeat (autodimp z hyp).
        { eapply adjacent_in_left; eauto. }
        { repeat (rewrite snoc_as_app in cond); simpl in cond.
          rewrite <- app_assoc in cond; auto.
          introv xx; apply cond in xx; tcsp. }
        simpl in z.
        apply z; tcsp.
      }

      { exrepnd; subst; eauto with eo. }

    - repnd.
      pose proof (cond a b) as q; destruct q as [q' q]; clear q'.
      autodimp q hyp.
      { dands; auto.
        unfold local_pred in h.
        remember (direct_pred e) as d; symmetry in Heqd; destruct d; auto.
        eapply local_trans;[exact h|]; eauto 3 with eo. }

      apply adjacent_snoc in q; repndors; auto.
      exrepnd; subst.
      apply snoc_inj in q1; repnd; subst.
      apply localCausal_anti_reflexive in h; tcsp.
  Qed.

  Lemma localPreds_unroll :
    forall e,
      ~ isFirst e
      -> localPreds e
         = snoc (localPreds (local_pred e)) (local_pred e).
  Proof.
    introv ni.
    unfold localPreds.
    remember (localPreds_lem e) as lp; destruct lp; simpl in *; clear Heqlp.
    remember (localPreds_lem (local_pred e)) as lp; destruct lp; simpl in *; clear Heqlp.

    revert dependent e.
    revert x0.
    induction x using list_ind_snoc; introv ni cond condPred; simpl in *.

    {
      pose proof (cond (local_pred e) e) as h; destruct h as [d' d]; clear d'.
      autodimp d hyp; dands; eauto with eo.
      apply adjacent_single in d; tcsp.
    }

    {
      assert (a = local_pred e) as apred.

      {
        pose proof (cond (local_pred e) e) as h; destruct h as [d' d]; clear d'.
        autodimp d hyp; dands; eauto with eo.
        apply adjacent_snoc in d; repndors; exrepnd; subst; GC;
          [|apply snoc_inj in d1; tcsp].

        apply (localPreds_cond_implies_in _ _ e) in d;
          [|introv xx; apply cond in xx; tcsp].
        apply localCausal_anti_reflexive in d; tcsp.
      }

      subst.
      f_equal.

      destruct (snoc_cases x0) as [d|d]; subst; simpl in *.

      {
        destruct (snoc_cases x); exrepnd; subst; simpl in *; auto.
        pose proof (cond a (local_pred e)) as q; destruct q as [q q']; clear q'.
        autodimp q hyp.
        {
          apply adjacent_snoc; left.
          apply adjacent_snoc; right.
          eexists; dands; eauto.
        }
        repnd.
        pose proof (condPred a (local_pred e)) as h; destruct h as [h' h]; clear h'.
        autodimp h hyp; dands; auto; eauto 3 with eo.
        apply adjacent_single in h; tcsp.
      }

      exrepnd; subst.

      pose proof (condPred a (local_pred e)) as q;destruct q as [q q']; clear q'.
      autodimp q hyp.
      { apply adjacent_snoc; right; eexists; dands; eauto. }
      repnd.
      applydup pred_implies_local_pred in q0; subst.
      apply IHx; auto; eauto 3 with eo; apply localPreds_cond_pred; auto.
    }
  Qed.

  (* history plus event *)
  Definition localPredsLe (e : Event) : list Event := snoc (localPreds e) e.

  (*
  Record DirectedData :=
    MkDData
      {
        ddDst  : name;
        ddData : Data
      }.

  Definition LDirectedData := list DirectedData.*)

  Definition Observer := forall eo : EventOrdering, @Event eo -> DirectedMsgs.

  Context { pda : DataAuth }.

  (* function that given a message [m], returns a list of authenticated
     messages of the form {msg, mac}, such that {msg, macs}
     is contained in [m] and [mac] is in the Token vector [macs] *)
  Class ContainedAuthData :=
    MkContainedAuthData
      {
        get_contained_authenticated_data : msg -> list (@AuthenticatedData pat pd);
        (*        authMsg2Msg : @AuthenticatedData pd pk auth -> msg*)
      }.
  Context { cad : ContainedAuthData }.
  (*Context { authenticatedData2Msg : AuthenticatedData -> msg }.*)


  (*
  Fixpoint in_trace (d : auth_data) (e : Event) : Prop :=
    exists m,
      In m (map data (localPredsLe e))
      /\ In d (@get_contained_auth_data pGetAD m).
   *)

  (*
  (* For each authenticated piece of data that is contained in a message
     that's sent away by a Byzantine node, we check that (1) either the
     authentication code is not valid; (2) or that the message is in the
     trace and therefore was sent earlier by another node; (3) or was
     authenticated by the Byzantine node.
     - In case (2), do we have to make sure that there is a path from
       the earlier sent message to the new one?
   *)
  Definition check_auth_data
             (src dst : Event) (* Byzantine source [src] *) : Prop :=
    forall m : AuthMsg,
      In m (get_contained_auth_data (data dst))
      -> verify_auth_msg m (keys src)
      ->
      (* then we have to make sure that s had enough information to generate the
         authenticated message *)
      (
        (* either [src] got the authenticated message from someone else *)
        in_trace m src

        \/

        (* or it is able to authenticate the message with one of its keys *)
        verify_keys m (keys src)
      ).*)

  Inductive msg_status :=
  (* messages sent by the system from one replica to another (possibly the same replica) *)
  | MSG_STATUS_PROTOCOL
  (* internal message sent the system sent by one replica to itself *)
  | MSG_STATUS_INTERNAL
  (* external messages are sent by processes not specified by the protocol *)
  | MSG_STATUS_EXTERNAL.

  Class MsgStatus :=
    MkMsgStatus
      {
        get_msg_status : msg -> msg_status
      }.
  Context { gms : MsgStatus }.

  (*Context { get_msg_status : msg -> msg_status }.*)

  Definition is_protocol_message (m : msg) : bool :=
    match get_msg_status m with
    | MSG_STATUS_PROTOCOL => true
    | MSG_STATUS_INTERNAL => true
    | MSG_STATUS_EXTERNAL => false
    end.

  Definition is_internal_message (m : msg) : bool :=
    match get_msg_status m with
    | MSG_STATUS_PROTOCOL => false
    | MSG_STATUS_INTERNAL => true
    | MSG_STATUS_EXTERNAL => false
    end.

  Definition is_external_message (m : msg) : bool :=
    match get_msg_status m with
    | MSG_STATUS_PROTOCOL => false
    | MSG_STATUS_INTERNAL => false
    | MSG_STATUS_EXTERNAL => true
    end.

  Definition auth_data_in_trigger (a : AuthenticatedData) (e : Event) : Prop :=
    match trigger e with
    | Some msg => In a (get_contained_authenticated_data msg)
    | None => False
    end.

  Definition bind_op_list {A B} (F : A -> list B) (i : option A) : list B :=
    match i with
    | Some a => F a
    | None => []
    end.

  Lemma in_bind_op_list_as_auth_data_in_trigger :
    forall a (e : Event),
      In a (bind_op_list get_contained_authenticated_data (trigger e))
      <-> auth_data_in_trigger a e.
  Proof.
    introv; unfold auth_data_in_trigger, bind_op_list.
    destruct (trigger e); tcsp.
  Qed.

  Lemma in_bind_op_list_implies_auth_data_in_trigger :
    forall a (e : Event),
      In a (bind_op_list get_contained_authenticated_data (trigger e))
      -> auth_data_in_trigger a e.
  Proof.
    introv h; apply in_bind_op_list_as_auth_data_in_trigger; auto.
  Qed.
  Hint Resolve in_bind_op_list_implies_auth_data_in_trigger : eo.

  Lemma auth_data_in_trigger_implies_in_bind_op_list :
    forall a (e : Event),
      auth_data_in_trigger a e
      -> In a (bind_op_list get_contained_authenticated_data (trigger e)).
  Proof.
    introv h; apply in_bind_op_list_as_auth_data_in_trigger; auto.
  Qed.
  Hint Resolve auth_data_in_trigger_implies_in_bind_op_list : eo.

  (* Assumption about where messages come from, that talks about
     nodes potentially being Byzantine.
   *)
  Definition authenticated_messages_were_sent_or_byz
             (F : forall (eo : EventOrdering) (e : Event), DirectedMsgs) :=
    forall e (a : AuthenticatedData),
      In a (bind_op_list get_contained_authenticated_data (trigger e))
      (* if we didn't verify the message then it could come from a Byzantine
         node that is impersonating someone else, without the logic knowing it *)
      -> verify_authenticated_data (loc e) a (keys e) = true
      -> exists e',
        e' ≺ e (* event e was triggered by an earlier send event e' *)

        (* e' generated the authentication code *)
        (* QUESTION: Should we say instead that the message was authenticated
           using a subset of the keys? *)
        /\ am_auth a = authenticate (am_data a) (keys e')

        /\
        (
          (
            exists m dst delay,

              In a (get_contained_authenticated_data m)

              /\
              (* e' sent the message to some node "dst"
                 following the protocol as described by F
                 (only if the message is the message is internal though),
                 which eventually got to e *)
              (is_protocol_message m = true -> In (MkDMsg m dst delay) (F eo e'))

              /\
              (* e' is the node mentioned in the authenticated message *)
              data_auth (loc e) (am_data a) = Some (loc e')
          )

          \/

          (* e' is not the node mentioned in the authenticated message
             because he got the keys of some other e''
           *)
          (
            exists e'',
              e'' ≼ e'
              /\
              (* e' is byzantine because it's using the keys of e'' *)
              isByz e'
              /\
              (* e'' is byzantine because it lost it keys *)
              isByz e''
              /\
                (* the sender mentioned in m is actually e'' and not e' but e' sent the message impersonating e''...what a nerve! *)
              data_auth (loc e) (am_data a) = Some (loc e'')
              /\
              (* e' got the key for (loc e) from e'' *)
              got_key_for (loc e) (keys e'') (keys e')
          )
        ).

  Definition is_internal_trigger (e : Event) : bool :=
    match trigger e with
    | Some msg => is_internal_message msg
    | None => false
    end.

  Definition event_triggered_by_message (e : Event) (m : msg) : Prop :=
    trigger e = Some m.

  Lemma event_triggered_by_message_implies_auth_data_in_trigger :
    forall (e : Event) m a,
      event_triggered_by_message e m
      -> In a (get_contained_authenticated_data m)
      -> auth_data_in_trigger a e.
  Proof.
    introv im ia.
    unfold event_triggered_by_message in *.
    unfold auth_data_in_trigger; allrw; auto.
  Qed.
  Hint Resolve event_triggered_by_message_implies_auth_data_in_trigger : eo.

  Lemma event_triggered_by_message_implies_in_bind_op_list :
    forall (e : Event) m a,
      event_triggered_by_message e m
      -> In a (get_contained_authenticated_data m)
      -> In a (bind_op_list get_contained_authenticated_data (trigger e)).
  Proof.
    introv im ia; eauto 3 with eo.
  Qed.
  Hint Resolve event_triggered_by_message_implies_in_bind_op_list : eo.

  (* we assume that internal messages don't get compromised---we don't sign them *)
  Definition internal_messages_were_sent
             (F : forall (eo : EventOrdering) (e : Event), DirectedMsgs) :=
    forall e m,
      event_triggered_by_message e m
      -> is_internal_message m = true
      -> isCorrect e
      ->
      exists e' dst delay,
        e' ⊏ e (* event e was triggered by an earlier send event e' *)
        /\ In (loc e) dst
        /\ In (MkDMsg m dst delay) (F eo e').

  Record message_constraints
         (F : forall (eo : EventOrdering) (e : Event), DirectedMsgs) :=
    MkMessageConstraints
      {
        mc_authenticated : authenticated_messages_were_sent_or_byz F;
        mc_internal      : internal_messages_were_sent F;
      }.

  (*
  (* This is a less informative semantics than sent_byz which doesn't talk about
   authentication codes or keys, and just says that either the message was sent
   by a node who followed the protocol, or there is a byzantine node, but we don't
   tie the node to the supposedly sender of the message.  Could that sometimes be
   enough?  How does this definition relate to [sent_byz] *)
  Definition simple_sent_byz
             (F : forall (eo : EventOrdering) (e : Event), DirectedMsgs) :=
    forall e (a : AuthenticatedData),
      In a (get_contained_authenticated_data (trigger e))
      ->
      exists e' m,
        e' ≺ e (* event e was triggered by an earlier send event e' *)

        /\
        In a (get_contained_authenticated_data m)

        /\
        (
          (exists dst delay, In (MkDMsg m dst delay) (F eo e'))

          \/

          isByz e'
        ).
*)

  Definition authenticated_messages_were_sent_or_byz_observer
             (s : Observer)
    := authenticated_messages_were_sent_or_byz s.

  (*
        (* either the message is what was supposed to be sent at e' *)
        (In (MkDData (loc e) (data e)) (s eo e')
         /\ isCorrect e')

        \/

        (* or the message wasn't what was supposed to be sent at e'
           because the node (@ e') is Byzantine.
           In that case we have to make sure that the data wasn't forged *)
        (check_auth_data e' e
         /\ isByz e')
  ).*)

  (* WARNING: What about rejuvenation?  If we stick with that, when rejuvenating
       a machine, we would have to give it a new name. *)
  Definition failures_dont_change :=
    forall e1 e2,
      e1 ⊏ e2
      ->
      (
(*        (isCrashed e1 -> isCrashed e2)
        /\*)
        (isByz e1 -> isByz e2)
      ).

End EventOrdering.


Hint Resolve happenedBeforeLe_refl          : eo.
Hint Resolve local_implies_loc              : eo.
Hint Resolve localLe_implies_loc            : eo.
Hint Resolve localLe_implies_causalLe       : eo.
Hint Resolve pred_implies_causal            : eo.
Hint Resolve pred_implies_loc               : eo.
Hint Resolve pred_implies_local             : eo.
Hint Resolve local_implies_causal           : eo.
Hint Resolve causal_trans                   : eo.
Hint Resolve causal_le_r_trans              : eo.
Hint Resolve causal_le_l_trans              : eo.
Hint Resolve local_trans                    : eo.
Hint Resolve local_trans_le_r               : eo.
Hint Resolve local_trans_le_l               : eo.
Hint Resolve local_implies_le               : eo.
Hint Resolve local_pred_le                  : eo.
Hint Resolve if_not_first_if_first          : eo.
Hint Resolve local_pred_is_direct_pred      : eo.
Hint Resolve local_pred_is_localCausal      : eo.
Hint Resolve local_pred_is_causal           : eo.
Hint Resolve pred_implies_not_first         : eo.
Hint Resolve local_causal_implies_not_first : eo.
Hint Resolve causalLe_trans                 : eo.
Hint Resolve localLe_trans                  : eo.
Hint Resolve causal_implies_causalLe        : eo.
Hint Resolve localHappenedBeforeLe_refl     : eo.

Hint Rewrite @loc_local_pred          : eo.
Hint Rewrite @loc_get_first           : eo.
Hint Rewrite @trigger_mkSubOrderingLe : eo.

Hint Resolve in_bind_op_list_implies_auth_data_in_trigger : eo.
Hint Resolve auth_data_in_trigger_implies_in_bind_op_list : eo.
Hint Resolve event_triggered_by_message_implies_auth_data_in_trigger : eo.
Hint Resolve event_triggered_by_message_implies_in_bind_op_list : eo.


(* QUESTION: Is there a way to do this inside the EventOrdering section? *)
Delimit Scope eo with eo.
Open Scope eo.
Notation "a ⊂ b" := (direct_pred b = Some a) (at level 0) : eo.
Notation "a ⊆ b" := (local_pred b = a) (at level 0) : eo.
Notation "a ≺ b" := (happenedBefore a b) (at level 0) : eo.
Notation "a ≼ b" := (happenedBeforeLe a b) (at level 0) : eo.
Notation "a ⊏ b" := (localHappenedBefore a b) (at level 0) : eo.
Notation "a ⊑ b" := (localHappenedBeforeLe a b) (at level 0) : eo.
Notation "History( a )" := (localPreds a) (at level 0) : eo.
Close Scope eo.
