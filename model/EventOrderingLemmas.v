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


Require Export EventOrdering.



Section EventOrderingLemmas.
  Context { pd  : @Data }.
  Context { pn  : @Node }.
  Context { pk  : @Key }.
  Context { pat : @AuthTok }.
  Context { paf : @AuthFun pn pk pat pd }.
  Context { pm  : @Msg }.
  Context { pda : @DataAuth pd pn }.


  Local Open Scope eo.


  Lemma isFirst_mkSubOrderingLe_eq :
    forall {eo : EventOrdering} {e : Event} (p : e ⊑ e),
      @isFirst _ _ _ (subEventOrdering e) (mkSubOrderingLe p).
  Proof.
    introv.
    unfold isFirst, mkSubOrderingLe; simpl.
    destruct (name_dec (loc e) (loc e)) as [d|d]; tcsp.
    dest_cases w.
  Qed.

  Lemma not_first_sub_event_ordering :
    forall (eo : EventOrdering) (e e' : Event) (p : (e') ⊑ (e)),
      ~ isFirst e
      -> (e') ⊑ (local_pred e)
      -> ~ @isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe p).
  Proof.
    introv h1 h2.
    unfold isFirst, mkSubOrderingLe; simpl.
    dest_cases w.

    - apply eq_first_iff_first in e0; tcsp.

    - clear n.
      dest_cases w.
      dest_cases y; subst; simpl.
      unfold eq_rect_r; simpl.

      assert False; tcsp.

      apply local_pred_is_localCausal in h1.
      eapply local_trans_le_r in h2;[|eauto].
      apply localCausal_anti_reflexive in h2; auto.
  Qed.

  Definition eq_MkSubEvent
             (eo : EventOrdering)
             (e e1 e2 : Event)
             (b1 : subEventOrdering_cond_bool e e1)
             (b2 : subEventOrdering_cond_bool e e2)
             (eqe : e1 = e2)
             (eqc : match eqe in _ = e2 return subEventOrdering_cond_bool e e2 with eq_refl => b1 end = b2)
    : MkSubEvent e e1 b1 = MkSubEvent e e2 b2
    := match eqe as eqe
             in _ = e2
             return forall b2 : subEventOrdering_cond_bool e e2,
           match eqe in _ = e2 return subEventOrdering_cond_bool e e2
           with eq_refl => b1 end = b2
           -> MkSubEvent e e1 b1 = MkSubEvent e e2 b2
       with
       | eq_refl => fun e2 eqc => match eqc with eq_refl => eq_refl (MkSubEvent e e1 b1) end
       end b2 eqc.

  Lemma local_mkSubOrderingLe :
    forall {eo : EventOrdering}
           {e e' : Event}
           (q : (e') ⊑ (e))
           (p : (e') ⊑ (local_pred e)),
      @local_pred _ _ _ (subEventOrdering e') (mkSubOrderingLe q)
      = mkSubOrderingLe p.
  Proof.
    introv.
    unfold mkSubOrderingLe; simpl.
    unfold local_pred; simpl in *.
    dest_cases w.

    - apply eq_first_iff_first in e0; tcsp.
      dest_cases w; exrepnd; simpl in *.

      + dest_cases w; simpl in *.
        dest_cases w; simpl in *; subst.

        fold (local_pred e).
        inversion Heqw as [z]; clear Heqw; subst.
        f_equal; apply UIP_dec; apply bool_dec.

      + dest_cases w; simpl in *.

        * dest_cases w; simpl in *; subst.
          unfold eq_rect_r in Heqw; simpl in *; GC.
          fold (local_pred e).
          pose proof (isFirst_implies_local_pred_eq e e0) as xx; symmetry in xx.
          apply (eq_MkSubEvent _ _ _ _ _ _ xx).
          apply UIP_dec; apply bool_dec.

        * destruct q; tcsp.

    - apply diff_first_iff_not_first in n; tcsp.
      dest_cases w; exrepnd; simpl in *.

      + dest_cases w; simpl in *.

        * dest_cases w; simpl in *; subst.
          fold (local_pred e).
          inversion Heqw as [z]; clear Heqw; subst.
          f_equal; apply UIP_dec; apply bool_dec.

        * destruct q; tcsp.

      + dest_cases w; simpl in *.
        dest_cases w; simpl in *; subst.
        unfold eq_rect_r in Heqw; simpl in *; GC.
        pose proof (local_pred_is_localCausal e) as h; autodimp h hyp.
        eapply local_trans_le_r in h;[|exact p].
        apply localCausal_anti_reflexive in h; tcsp.
  Qed.

  Lemma localHappenedBeforeLe_subEventOrdering_implies :
    forall (eo : EventOrdering) (e : Event) (e1 e2 : subEventOrdering_type e),
      @localHappenedBeforeLe pn pk pm (subEventOrdering e) e1 e2
      -> @localHappenedBeforeLe pn pk pm eo e1 e2.
  Proof.
    introv h.
    destruct e1 as [e1 cond1], e2 as [e2 cond2]; simpl in *.
    unfold localHappenedBeforeLe, happenedBeforeLe in *; simpl in *.
    repnd; repndors; dands; auto.
    inversion h0; auto.
  Qed.

  Lemma implies_localHappenedBeforeLe_subEventOrdering :
    forall (eo : EventOrdering) (e : Event) (e1 e2 : subEventOrdering_type e),
      @localHappenedBeforeLe pn pk pm eo e1 e2
      -> @localHappenedBeforeLe pn pk pm (subEventOrdering e) e1 e2.
  Proof.
    introv h.
    destruct e1 as [e1 cond1], e2 as [e2 cond2]; simpl in *.
    unfold localHappenedBeforeLe, happenedBeforeLe in *; simpl in *.
    repnd; repndors; dands; auto; subst.
    right.
    f_equal; apply UIP_dec; apply bool_dec.
  Qed.

  Lemma localHappenedBeforeLe_subEventOrdering_iff :
    forall (eo : EventOrdering) (e : Event) (e1 e2 : subEventOrdering_type e),
      @localHappenedBeforeLe pn pk pm (subEventOrdering e) e1 e2
      <->
      @localHappenedBeforeLe pn pk pm eo e1 e2.
  Proof.
    introv; split; intro h.
    - apply localHappenedBeforeLe_subEventOrdering_implies; auto.
    - apply implies_localHappenedBeforeLe_subEventOrdering; auto.
  Qed.

  Lemma localHappenedBefore_subEventOrdering_implies :
    forall (eo : EventOrdering) (e : Event) (e1 e2 : subEventOrdering_type e),
      @localHappenedBefore pn pk pm (subEventOrdering e) e1 e2
      -> @localHappenedBefore pn pk pm eo e1 e2.
  Proof.
    introv h.
    destruct e1 as [e1 cond1], e2 as [e2 cond2]; simpl in *.
    unfold localHappenedBefore in *; simpl in *.
    repnd; repndors; dands; auto.
  Qed.

  Lemma implies_localHappenedBefore_subEventOrdering :
    forall (eo : EventOrdering) (e : Event) (e1 e2 : subEventOrdering_type e),
      @localHappenedBefore pn pk pm eo e1 e2
      -> @localHappenedBefore pn pk pm (subEventOrdering e) e1 e2.
  Proof.
    introv h.
    destruct e1 as [e1 cond1], e2 as [e2 cond2]; simpl in *.
    unfold localHappenedBefore in *; simpl in *.
    repnd; repndors; dands; auto; subst.
  Qed.

  Lemma localHappenedBefore_subEventOrdering_iff :
    forall (eo : EventOrdering) (e : Event) (e1 e2 : subEventOrdering_type e),
      @localHappenedBefore pn pk pm (subEventOrdering e) e1 e2
      <->
      @localHappenedBefore pn pk pm eo e1 e2.
  Proof.
    introv; split; intro h.
    - apply localHappenedBefore_subEventOrdering_implies; auto.
    - apply implies_localHappenedBefore_subEventOrdering; auto.
  Qed.

  Lemma isFirst_mkSubOrderingLe :
    forall (eo : EventOrdering) (e e' : Event) (q : (e') ⊑ (e)),
      @isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe q)
      -> e' = e.
  Proof.
    introv h.
    unfold isFirst, mkSubOrderingLe in h; simpl in *.
    dest_cases w.

    - apply eq_first_iff_first in e0; tcsp.
      dest_cases w; simpl in *; ginv.

      + dest_cases w.

      + destruct q; tcsp.

    - apply diff_first_iff_not_first in n; tcsp.
      dest_cases w.
      dest_cases w.
  Qed.

  Lemma event_le_local_pred :
    forall (eo : EventOrdering) (e : Event),
      (e) ⊑ (local_pred e)
      -> isFirst e.
  Proof.
    introv h.
    destruct (dec_isFirst e) as [d|d]; auto;[].
    assert False; tcsp.
    pose proof (local_pred_is_localCausal e) as q; autodimp q hyp.
    eapply local_trans_le_r in h;[|eauto].
    apply localCausal_anti_reflexive in h; tcsp.
  Qed.

  Lemma localHappenedBeforeLe_implies_or :
    forall {eo : EventOrdering} {e' e : Event} (p : e' ⊑ e),
      e' = e \/ e' ⊑ (local_pred e).
  Proof.
    introv h; destruct h as [h1 h2].
    destruct h1 as [h1|h1]; subst; tcsp.
    right.
    split; allrw loc_local_pred; auto.
    unfold local_pred.
    remember (direct_pred e) as dp; destruct dp; symmetry in Heqdp; tcsp.
    eapply eo_local_order in h1;[| |exact Heqdp]; auto.
    repndors; subst; tcsp.
  Qed.

  Lemma not_isFirst_implies_le_local_pred :
    forall (eo : EventOrdering) (e' e : Event) (p : e' ⊑ e),
      ~ @isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe p)
      -> e' ⊑ (local_pred e).
  Proof.
    introv h.
    unfold mkSubOrderingLe, isFirst in h; simpl in *.
    dest_cases w.

    - apply eq_first_iff_first in e0; tcsp.
      dest_cases w; tcsp.
      dest_cases w; subst; tcsp.
      clear h.
      apply localHappenedBeforeLe_implies_or in p; tcsp.

    - apply diff_first_iff_not_first in n.
      dest_cases w; tcsp;[|destruct p; tcsp].
      dest_cases w; subst.
      clear h.
      apply localHappenedBeforeLe_implies_or in p; tcsp.
  Qed.

  Lemma isFirst_localHappenedBeforeLe_implies_eq :
    forall {eo : EventOrdering} {e' e : Event} (p : e' ⊑ e),
      isFirst e -> e' = e.
  Proof.
    introv p isF.
    destruct p as [p q].
    destruct p as [p|p]; auto.
    symmetry in q.
    apply isFirst_loc_implies_causal in q; auto.
    destruct q as [q|q]; auto.
    eapply causal_trans in q;[|exact p].
    apply causal_anti_reflexive in q; tcsp.
  Qed.

  Lemma not_isFirst_mkSubOrderingLe_implies_isFirst :
    forall (eo : EventOrdering) (e' e : Event) (p : e' ⊑ e),
      ~ @isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe p)
      -> ~ isFirst e.
  Proof.
    introv h.
    unfold mkSubOrderingLe, isFirst in h; simpl in *.
    dest_cases w.

    - apply eq_first_iff_first in e0; tcsp.
      dest_cases w; tcsp.
      dest_cases w; subst; tcsp.
      clear h.
      eapply isFirst_localHappenedBeforeLe_implies_eq in e0;[|exact p]; tcsp.

    - apply diff_first_iff_not_first in n; auto.
  Qed.

  Lemma localHappenedBeforeLe_implies_or2 :
    forall (eo : EventOrdering) (e e' : Event),
      e ⊑ e' <-> (e = e' \/ e ⊏ e').
  Proof.
    introv; split; introv h.
    { destruct h as [h1 h2].
      destruct h1 as [h1|h1]; tcsp.
      right; split; auto. }
    { repndors; subst;[split;auto;right;auto|].
      destruct h.
      split;auto;left;auto. }
  Qed.

  Lemma localHappenedBeforeLe_local_pred_implies_localHappenedBefore :
    forall (eo : EventOrdering) (e e' : Event),
      ~ (isFirst e)
      -> e' ⊑ (local_pred e)
      -> e' ⊏ e.
  Proof.
    introv nfirst locle.
    apply localHappenedBeforeLe_implies_or2 in locle; repndors; subst; eauto 2 with eo.
  Qed.
  Hint Resolve localHappenedBeforeLe_local_pred_implies_localHappenedBefore : eo.

  Lemma localHappenedBefore_implies_le_local_pred :
    forall (eo : EventOrdering) (e e' : Event),
      e ⊏ e'
      -> e ⊑ (local_pred e').
  Proof.
    introv h.
    apply local_implies_pred_or_local in h; repndors.
    - apply pred_implies_local in h.
      assert (e ⊑ e') as xx by (apply localHappenedBeforeLe_implies_or2; tcsp).
      apply localHappenedBeforeLe_implies_or in xx; repndors; subst;
        [apply localCausal_anti_reflexive in h;tcsp|]; auto.
    - exrepnd.
      apply pred_implies_local in h1.
      assert (e0 ⊑ e') as xx by (apply localHappenedBeforeLe_implies_or2; tcsp).
      apply localHappenedBeforeLe_implies_or in xx; repndors; subst;
        [apply localCausal_anti_reflexive in h1;tcsp|]; auto.
      eapply localLe_trans;[|exact xx].
      apply localHappenedBeforeLe_implies_or2; tcsp.
  Qed.

  Lemma happenedBeforeLe_subEventOrdering_implies :
    forall (eo : EventOrdering) (e : Event) (e1 e2 : subEventOrdering_type e),
      @happenedBeforeLe pn pk pm (subEventOrdering e) e1 e2
      -> @happenedBeforeLe pn pk pm eo e1 e2.
  Proof.
    introv h.
    destruct e1 as [e1 cond1], e2 as [e2 cond2]; simpl in *.
    unfold happenedBeforeLe in *; simpl in *.
    repndors; dands; auto.
    inversion h; auto.
  Qed.

  Definition sub_sub_event2sub_event
             (eo  : EventOrdering)
             (e   : Event)
             (e'  : subEventOrdering_type e)
             (e'' : @subEventOrdering_type pn pk pm (subEventOrdering e) e')
    : @subEventOrdering_type pn pk pm eo e'.
  Proof.
    destruct e' as [e' conde']; simpl in *.
    destruct e'' as [e'' conde''1]; simpl in *.
    destruct e'' as [e'' conde''2]; simpl in *.
    exists e''.
    apply subEventOrdering_cond_bool_iff; introv eqloc.
    apply subEventOrdering_cond_bool_iff in conde''1.
    applydup conde''1 in eqloc; simpl in *.
    apply happenedBeforeLe_subEventOrdering_implies in eqloc0; simpl in *; auto.
  Defined.

  Lemma isFirstSubEvent_implies :
    forall (eo : EventOrdering) (e : Event) (e' : subEventOrdering_type e),
      @isFirst _ _ _ (@subEventOrdering _ _ _ eo e) e' ->
      if name_dec (loc e) (loc e')
      then e = e'
      else isFirst (sub_eo_event e e').
  Proof.
    introv.
    destruct e' as [e' conde']; simpl in *.
    unfold isFirst; simpl.
    dest_cases w.

    - apply eq_first_iff_first in e0.
      dest_cases w; dest_cases w; dest_cases w.

    - apply diff_first_iff_not_first in n.
      dest_cases w; dest_cases w; dest_cases w.
  Qed.

  Lemma implies_isFirstSubEvent :
    forall (eo : EventOrdering) (e : Event) (e' : subEventOrdering_type e),
      (if name_dec (loc e) (loc e') then e = e' else isFirst (sub_eo_event e e'))
      -> @isFirst _ _ _ (@subEventOrdering _ _ _ eo e) e'.
  Proof.
    introv.
    destruct e' as [e' conde']; simpl in *.
    unfold isFirst; simpl.
    introv h.
    dest_cases w; subst; dest_cases w.

    - apply eq_first_iff_first in e.
      dest_cases w; dest_cases w.

    - apply diff_first_iff_not_first in n.
      dest_cases w; dest_cases w.

    - apply eq_first_iff_first in e0.
      dest_cases w; dest_cases w.

    - apply diff_first_iff_not_first in n0.
      dest_cases w; dest_cases w.
  Qed.

  Lemma isFirstSubEvent_iff :
    forall (eo : EventOrdering) (e : Event) (e' : subEventOrdering_type e),
      @isFirst _ _ _ (@subEventOrdering _ _ _ eo e) e'
      <->
      if name_dec (loc e) (loc e')
      then e = e'
      else isFirst (sub_eo_event e e').
  Proof.
    introv; split; intro h.
    - apply isFirstSubEvent_implies in h; auto.
    - apply implies_isFirstSubEvent in h; auto.
  Qed.

  Lemma subEventOrdering_trigger_sub_eo :
    forall (eo  : EventOrdering)
           (e   : Event)
           (e'  : subEventOrdering_type e)
           (e'' : @subEventOrdering_type _ _ _ (subEventOrdering e) e'),
      @subEventOrdering_trigger _ _ _ (@subEventOrdering _ _ _ eo e) e' e''
      = @subEventOrdering_trigger _ _ _ eo (@sub_eo_event _ _ _ eo e e') (sub_sub_event2sub_event eo e e' e'').
  Proof.
    introv.
    destruct e' as [e' conde']; simpl.
    destruct e'' as [e'' conde''1]; simpl.
    destruct e'' as [e'' conde''2]; simpl; auto.
  Qed.

  Lemma subEventOrdering_trigger_sub_eo2 :
    forall (eo  : EventOrdering)
           (e   : Event)
           (e'  : subEventOrdering_type e),
      subEventOrdering_trigger e e'
      = trigger e'.
  Proof.
    introv.
    destruct e' as [e' conde']; simpl; auto.
  Qed.

  Lemma sub_eo_event_sub_sub_event2sub_event :
    forall (eo  : EventOrdering)
           (e   : Event)
           (e'  : subEventOrdering_type e)
           (e'' : @subEventOrdering_type _ _ _ (subEventOrdering e) e'),
      @sub_eo_event
        _ _ _
        eo
        (@sub_eo_event pn pk pm eo e e')
        (sub_sub_event2sub_event eo e e' e'')
      = sub_eo_event _ (sub_eo_event _ e'').
  Proof.
    introv.
    destruct e' as [e' conde']; simpl.
    destruct e'' as [e'' conde''1]; simpl.
    destruct e'' as [e'' conde''2]; simpl; auto.
  Qed.

  Lemma implies_eq_in_sub_eo :
    forall (eo : EventOrdering)
           (e : Event)
           (e1 e2 : subEventOrdering_type e),
      sub_eo_event e e1 = sub_eo_event e e2
      -> e1 = e2.
  Proof.
    introv h.
    destruct e1 as [e1 cond1].
    destruct e2 as [e2 cond2].
    simpl in *; subst.
    f_equal; apply UIP_dec; apply bool_dec.
  Qed.

  Lemma sub_eo_local_pred_if_not_first :
    forall (eo : EventOrdering)
           (e  : Event)
           (e' : subEventOrdering_type e),
      ~ @isFirst _ _ _ (@subEventOrdering _ _ _ eo e) e'
      ->
      @sub_eo_event
        _ _ _ eo e
        (@local_pred
           _ _ _
           (@subEventOrdering pn pk pm eo e) e')
      = @local_pred _ _ _ eo (@sub_eo_event _ _ _ eo e e').
  Proof.
    introv.
    destruct e' as [e' conde']; simpl.
    unfold isFirst, local_pred; simpl.
    dest_cases w.

    - apply eq_first_iff_first in e0.
      dest_cases w; dest_cases w; dest_cases w.

    - apply diff_first_iff_not_first in n.
      dest_cases w; dest_cases w; dest_cases w.
  Qed.

  Lemma subEventOrdering_loc_local_pred :
    forall (eo : EventOrdering) (e : Event) (e' : subEventOrdering_type e),
      subEventOrdering_loc e (@local_pred _ _ _ (@subEventOrdering pn pk pm eo e) e')
      = loc e'.
  Proof.
    introv.
    destruct e' as [e' conde']; simpl.
    unfold local_pred; simpl.
    dest_cases w.

    - apply eq_first_iff_first in e0.
      dest_cases w; dest_cases w; dest_cases w; ginv; simpl.
      rewrite loc_local_pred; auto.

    - apply diff_first_iff_not_first in n.
      dest_cases w; dest_cases w; try (dest_cases w); ginv; simpl;
        rewrite loc_local_pred; auto.
  Qed.

  Lemma sub_sub_event2sub_event_mkSubEventOrderingLe :
    forall (eo  : EventOrdering)
           (e   : Event)
           (e'  : Event)
           (e'' : subEventOrdering_type e')
           (p   : e' ⊑ e)
           (q   : e'' ⊑ e)
           (p0  : @localHappenedBeforeLe _ _ _ (subEventOrdering e') e'' (mkSubOrderingLe p)),
      @sub_sub_event2sub_event
        eo e' e''
        (@mkSubOrderingLe
           _ _ _
           (subEventOrdering e')
           e''
           (mkSubOrderingLe p)
           p0)
      = mkSubOrderingLe q.
  Proof.
    introv.
    apply implies_eq_in_sub_eo; simpl.
    rewrite sub_eo_event_sub_sub_event2sub_event; auto.
  Qed.

  Definition all_correct (eo : EventOrdering) := forall (e : Event), isCorrect e.

  Lemma isCorrect_implies_msg :
    forall (eo : EventOrdering)  (e : Event),
      isCorrect e -> exists m, trigger e = Some m.
  Proof.
    introv isc.
    unfold isCorrect in isc.
    destruct (trigger e); tcsp.
    eexists; eauto.
  Qed.

End EventOrderingLemmas.


Hint Resolve isFirst_mkSubOrderingLe_eq : eo.
Hint Resolve localHappenedBeforeLe_local_pred_implies_localHappenedBefore : eo.

Hint Rewrite @subEventOrdering_loc_local_pred  : eo.
Hint Rewrite @subEventOrdering_trigger_sub_eo2 : eo.
