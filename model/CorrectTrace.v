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


Require Export Quorum.
Require Export EventOrderingLemmas.


Section CorrectTrace.

  Context { pd  : @Data }.
  Context { pn  : @Node }.
  Context { pk  : @Key }.
  Context { pm  : @Msg }.
  Context { qc  : @Quorum_context pn}.
  Context { pat : @AuthTok }.
  Context { paf : @AuthFun pn pk pat pd }.
  Context { pda : @DataAuth pd pn }.
  Context { cad : @ContainedAuthData pd pat pm }.
  Context { gms : MsgStatus }.

  Local Open Scope eo.


  (* All the events at [i] are correct *)
  Definition has_correct_trace (eo : EventOrdering) (i : name) :=
    forall e, loc e = i -> isCorrect e.

  Definition node_has_correct_trace (eo : EventOrdering) (i : node_type) :=
    has_correct_trace eo (node2name i).

  Definition have_correct_traces (eo : EventOrdering) (G : list name) :=
    forall good, In good G -> has_correct_trace eo good.

  Definition nodes_have_correct_traces (eo : EventOrdering) (G : list node_type) :=
    have_correct_traces eo (map node2name G).

  (* all the events at [loc e] before [e] are correct *)
  Definition has_correct_trace_bounded {eo : EventOrdering} (e : Event) :=
    forall e', e' ⊑ e -> isCorrect e'.

  Definition have_correct_traces_before
             {eo : EventOrdering}
             (G  : list name)
             (L  : list Event) :=
    forall good e1 e2,
      In good G
      -> In e2 L
      -> e1 ≼ e2
      -> loc e1 = good
      -> has_correct_trace_bounded e1.

  Definition nodes_have_correct_traces_before
             {eo : EventOrdering}
             (G  : list node_type)
             (L  : list Event) :=
    have_correct_traces_before (map node2name G) L.

  Lemma nodes_have_correct_traces_before_causal_le :
    forall (eo : EventOrdering) R (e e' : Event),
      e' ≼ e
      -> nodes_have_correct_traces_before R [e]
      -> nodes_have_correct_traces_before R [e'].
  Proof.
    introv lte ctraces i j w z; simpl in *; repndors; subst; tcsp.
    unfold nodes_have_correct_traces_before, have_correct_traces_before in ctraces.
    pose proof (ctraces (loc e1) e1 e) as q; simpl in q; repeat (autodimp q hyp); eauto 3 with eo.
  Qed.
  Hint Resolve nodes_have_correct_traces_before_causal_le : eo.

  Lemma nodes_have_correct_traces_before_two_left :
    forall (eo : EventOrdering) R (e1 e2 : Event),
      nodes_have_correct_traces_before R [e1, e2]
      -> nodes_have_correct_traces_before R [e1].
  Proof.
    introv ctraces i j w z; simpl in *; repndors; subst; tcsp.
    eapply ctraces; eauto; simpl; tcsp.
  Qed.
  Hint Resolve nodes_have_correct_traces_before_two_left : eo.

  Lemma nodes_have_correct_traces_before_two_right :
    forall (eo : EventOrdering) R (e1 e2 : Event),
      nodes_have_correct_traces_before R [e1, e2]
      -> nodes_have_correct_traces_before R [e2].
  Proof.
    introv ctraces i j w z; simpl in *; repndors; subst; tcsp.
    eapply ctraces; eauto; simpl; tcsp.
  Qed.
  Hint Resolve nodes_have_correct_traces_before_two_right : eo.

  Lemma nodes_have_correct_traces_before_causal :
    forall (eo : EventOrdering) R (e e' : Event),
      e' ≺ e
      -> nodes_have_correct_traces_before R [e]
      -> nodes_have_correct_traces_before R [e'].
  Proof.
    introv lte ctraces i j w z; simpl in *; repndors; subst; tcsp.
    pose proof (ctraces (loc e1) e1 e) as q; simpl in q; repeat (autodimp q hyp); eauto 3 with eo.
  Qed.
  Hint Resolve nodes_have_correct_traces_before_causal : eo.

  Lemma has_correct_trace_bounded_preserves_local_le :
    forall (eo : EventOrdering) e e',
      e' ⊑ e
      -> has_correct_trace_bounded e
      -> has_correct_trace_bounded e'.
  Proof.
    introv lee ctrace i.
    apply ctrace; auto; eauto 3 with eo.
  Qed.
  Hint Resolve has_correct_trace_bounded_preserves_local_le : eo.

  Lemma has_correct_trace_bounded_implies_message :
    forall {eo : EventOrdering} (e e' : Event),
      has_correct_trace_bounded e
      -> e' ⊑ e
      -> exists m, trigger e' = Some m.
  Proof.
    introv cor lee.
    pose proof (cor e' lee) as cor.
    apply isCorrect_implies_msg; auto.
  Qed.

  Definition has_correct_trace_before {eo : EventOrdering} (e : Event) (good : name) :=
    forall e', e' ≼ e -> loc e' = good -> has_correct_trace_bounded e'.

  Definition node_has_correct_trace_before {eo : EventOrdering} (e : Event) (good : node_type) :=
    has_correct_trace_before e (node2name good).

  Definition authenticated_messages_were_sent_non_byz
             (eo : EventOrdering)
             (F : forall (eo : EventOrdering) (e : Event), DirectedMsgs):=
    forall (e : Event) (a : AuthenticatedData) (good : name),
      auth_data_in_trigger a e
      -> has_correct_trace_before e good
      -> verify_authenticated_data (loc e) a (keys e) = true
      -> data_auth (loc e) (am_data a) = Some good
      ->
      exists e' m dst delay,
        e' ≺ e
        /\ am_auth a = authenticate (am_data a) (keys e')
        /\ In a (get_contained_authenticated_data m)
        /\ (is_protocol_message m = true -> In (MkDMsg m dst delay) (F eo e'))
        /\ loc e' = good.

  Lemma implies_authenticated_messages_were_sent_non_byz :
    forall (eo : EventOrdering) F,
      authenticated_messages_were_sent_or_byz F
      -> authenticated_messages_were_sent_non_byz eo F.
  Proof.
    introv auth i ctrace verif sender.
    pose proof (auth e a) as q.
    repeat (autodimp q hyp); exrepnd; eauto 3 with eo;[].
    repndors; exrepnd.

    - exists e' m dst delay; dands; auto.
      rewrite sender in *; ginv.

    - assert False; tcsp.
      rewrite sender in *; ginv.
      pose proof (ctrace e'') as q; repeat (autodimp q hyp); eauto 3 with eo.
(*      pose proof (q e'') as q; autodimp q hyp; eauto 3 with eo.
      apply correct_is_not_byzantine in q; tcsp.*)
  Qed.

  Definition exists_at_most_f_faulty {eo : EventOrdering} (L : list Event) (F : nat) :=
    exists (faulty : list node_type),
      length faulty <= F
      /\
      forall e1 e2,
        In e2 L
        -> e1 ≼ e2
        -> ~ In (loc e1) (map node2name faulty)
        -> has_correct_trace_bounded e1.

  Lemma exists_at_most_f_faulty_two_left :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
      exists_at_most_f_faulty [e1, e2] F
      -> exists_at_most_f_faulty [e1] F.
  Proof.
    introv atmost; unfold exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto; simpl in *.
    introv xx; repndors; subst; tcsp.
    apply atmost0; auto.
  Qed.
  Hint Resolve exists_at_most_f_faulty_two_left : eo.

  Lemma exists_at_most_f_faulty_two_right :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
      exists_at_most_f_faulty [e1, e2] F
      -> exists_at_most_f_faulty [e2] F.
  Proof.
    introv atmost; unfold exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto; simpl in *.
    introv xx; repndors; subst; tcsp.
    apply atmost0; auto.
  Qed.
  Hint Resolve exists_at_most_f_faulty_two_right : eo.

  Lemma implies_atmost_f_faulty_two_causal_le :
    forall (eo : EventOrdering) (e1 e2 e1' e2' : Event) F,
      e1' ≼ e1
      -> e2' ≼ e2
      -> exists_at_most_f_faulty [e1,e2] F
      -> exists_at_most_f_faulty [e1',e2'] F.
  Proof.
    introv lee1 lee2 atmost; unfold exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto.
    simpl in *; introv w z u; repndors; tcsp; subst;[|].
    - pose proof (atmost0 e0 e1) as q; repeat (autodimp q hyp); eauto 3 with eo.
    - pose proof (atmost0 e0 e2) as q; repeat (autodimp q hyp); eauto 3 with eo.
  Qed.
  Hint Resolve implies_atmost_f_faulty_two_causal_le : eo.

  Lemma implies_atmost_f_faulty_two_sym :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
      exists_at_most_f_faulty [e1,e2] F
      -> exists_at_most_f_faulty [e2,e1] F.
  Proof.
    introv atmost; unfold exists_at_most_f_faulty, exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto.
    simpl in *; introv w z u; repndors; tcsp; subst;
      pose proof (atmost0 e0 e3) as q; repeat (autodimp q hyp);
        eauto 3 with eo.
  Qed.
  Hint Resolve implies_atmost_f_faulty_two_sym : eo.

  Lemma exists_at_most_f_faulty_preserves_causal :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
      e1 ≺ e2
      -> exists_at_most_f_faulty [e2] F
      -> exists_at_most_f_faulty [e1] F.
  Proof.
    introv lte atmost.
    unfold exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto; simpl in *.
    introv w z u; repndors; subst; tcsp.
    apply (atmost0 e0 e2); auto; eauto 3 with eo.
  Qed.
  Hint Resolve exists_at_most_f_faulty_preserves_causal : eo.

  Lemma exists_at_most_f_faulty_preserves_causal_le :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
      e1 ≼ e2
      -> exists_at_most_f_faulty [e2] F
      -> exists_at_most_f_faulty [e1] F.
  Proof.
    introv lte atmost.
    unfold exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto; simpl in *.
    introv w z u; repndors; subst; tcsp.
    apply (atmost0 e0 e2); auto; eauto 3 with eo.
  Qed.
  Hint Resolve exists_at_most_f_faulty_preserves_causal_le : eo.

  Lemma exists_at_most_f_faulty_twice :
    forall (eo : EventOrdering) (e : Event) F,
      exists_at_most_f_faulty [e] F
      -> exists_at_most_f_faulty [e, e] F.
  Proof.
    introv atmost.
    unfold exists_at_most_f_faulty in *; exrepnd; exists faulty; dands; auto.
    introv w z u; simpl in *; repndors; subst; tcsp; eapply atmost0; eauto.
  Qed.
  Hint Resolve exists_at_most_f_faulty_twice : eo.

  Lemma implies_atmost_f_faulty_local_pred :
    forall (eo : EventOrdering) (e : Event) F,
      exists_at_most_f_faulty [e] F
      -> exists_at_most_f_faulty [local_pred e] F.
  Proof.
    introv atmost; unfold exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto.
    simpl in *; introv w z u; repndors; tcsp.
    rewrite <- w in z.
    pose proof (atmost0 e1 e) as q; repeat (autodimp q hyp); eauto 3 with eo.
  Qed.
  Hint Resolve implies_atmost_f_faulty_local_pred : eo.

  Lemma implies_atmost_f_faulty_causal :
    forall (eo : EventOrdering) (e e' : Event) F,
      e' ≺ e
      -> exists_at_most_f_faulty [e] F
      -> exists_at_most_f_faulty [e'] F.
  Proof.
    introv lte atmost; unfold exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto.
    simpl in *; introv w z u; repndors; tcsp.
    rewrite <- w in z.
    pose proof (atmost0 e1 e) as q; repeat (autodimp q hyp); eauto 3 with eo.
  Qed.
  Hint Resolve implies_atmost_f_faulty_causal : eo.

  Lemma implies_atmost_f_faulty_causal_le :
    forall (eo : EventOrdering) (e e' : Event) F,
      e' ≼ e
      -> exists_at_most_f_faulty [e] F
      -> exists_at_most_f_faulty [e'] F.
  Proof.
    introv lte atmost; unfold exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto.
    simpl in *; introv w z u; repndors; tcsp.
    rewrite <- w in z.
    pose proof (atmost0 e1 e) as q; repeat (autodimp q hyp); eauto 3 with eo.
  Qed.
  Hint Resolve implies_atmost_f_faulty_causal_le : eo.

  Lemma there_is_one_correct_before :
    forall (eo : EventOrdering) (L : list node_type) (E : list Event) (F : nat),
      no_repeats L
      -> F + 1 <= length L
      -> exists_at_most_f_faulty E F
      -> exists (correct : node_type),
          In correct L
          /\ forall e, In e E -> has_correct_trace_before e (node2name correct).
  Proof.
    introv norep cond atmost.
    unfold exists_at_most_f_faulty in atmost.
    exrepnd.

    pose proof (member_of_larger_list2 node_deq L faulty) as q.
    repeat (autodimp q hyp); try omega.
    destruct q as [c q]; repnd.

    exists c; dands; auto.
    introv i j k.
    apply atmost0 in j; auto.
    intro z.
    rewrite in_map_iff in z; exrepnd.
    rewrite k in z1.
    apply node2name_inj in z1; subst; tcsp.
  Qed.

  Lemma has_correct_trace_before_preserves_local_le :
    forall (eo : EventOrdering) e e' k,
      e' ⊑ e
      -> has_correct_trace_before e k
      -> has_correct_trace_before e' k.
  Proof.
    introv lee ctrace i j.
    apply ctrace; auto; eauto 3 with eo.
  Qed.
  Hint Resolve has_correct_trace_before_preserves_local_le : eo.

  Lemma has_correct_trace_before_preserves_causal_le :
    forall (eo : EventOrdering) e e' k,
      e' ≼ e
      -> has_correct_trace_before e k
      -> has_correct_trace_before e' k.
  Proof.
    introv lee ctrace i j.
    apply ctrace; auto; eauto 3 with eo.
  Qed.
  Hint Resolve has_correct_trace_before_preserves_causal_le : eo.

  Lemma some_trigger_implies_isCorrect :
    forall (eo : EventOrdering) (e : Event) x,
      trigger e = Some x
      -> isCorrect e.
  Proof.
    introv w; unfold isCorrect; allrw; auto.
  Qed.
  Hint Resolve some_trigger_implies_isCorrect : eo.

  Lemma has_correct_trace_before_local_pred_implies :
    forall (eo : EventOrdering) (e : Event) i,
      loc e = i
      -> isCorrect e
      -> has_correct_trace_before (local_pred e) i
      -> has_correct_trace_before e i.
  Proof.
    introv eqloc1 core cor lee1 eqloc2 lee2.
    assert (e' ⊑ e) as lee3 by (split; allrw; auto).
    assert (e'0 ⊑ e) as lee4 by (eauto 3 with eo).
    apply localHappenedBeforeLe_implies_or in lee4; repndors; subst; auto.
    pose proof (cor e'0) as q; repeat (autodimp q hyp); eauto 3 with eo.
  Qed.
  Hint Resolve has_correct_trace_before_local_pred_implies : eo.

  Lemma node_has_correct_trace_before_preserves_local_le :
    forall (eo : EventOrdering) e e' k,
      e' ⊑ e
      -> node_has_correct_trace_before e k
      -> node_has_correct_trace_before e' k.
  Proof.
    introv lee ctrace i j.
    apply ctrace; auto; eauto 3 with eo.
  Qed.
  Hint Resolve node_has_correct_trace_before_preserves_local_le : eo.

  Lemma node_has_correct_trace_before_preserves_causal_le :
    forall (eo : EventOrdering) e e' k,
      e' ≼ e
      -> node_has_correct_trace_before e k
      -> node_has_correct_trace_before e' k.
  Proof.
    introv lee ctrace i j.
    apply ctrace; auto; eauto 3 with eo.
  Qed.
  Hint Resolve node_has_correct_trace_before_preserves_causal_le : eo.

  Lemma node_has_correct_trace_before_preserves_causal :
    forall {eo : EventOrdering} (e1 e2 : Event) i,
      e1 ≺ e2
      -> node_has_correct_trace_before e2 i
      -> node_has_correct_trace_before e1 i.
  Proof.
    introv caus h q w.
    eapply h; eauto 3 with eo.
  Qed.
  Hint Resolve node_has_correct_trace_before_preserves_causal : eo.

  Lemma select_good_guys_before :
    forall (eo : EventOrdering) (L : list node_type) (E : list Event) F,
      no_repeats L
      -> exists_at_most_f_faulty E F
      -> exists (G : list node_type),
          subset G L
          /\ length L - F <= length G
          /\ no_repeats G
          /\ forall e good,
              In e E
              -> In good G
              -> node_has_correct_trace_before e good.
  Proof.
    introv norep byz.
    unfold exists_at_most_f_faulty in byz.
    exrepnd.

    pose proof (members_of_larger_list node_deq L faulty) as q.
    repeat (autodimp q hyp); try omega;[].

    destruct q as [G q]; repnd.
    exists G.
    dands; auto; simpl in *; try omega;[].

    introv i j k w.
    applydup byz0 in k; auto.
    allrw in_map_iff; exrepnd.
    introv z; exrepnd.
    rewrite w in *; ginv.
    apply node2name_inj in z1; subst.
    apply q1 in z0; tcsp.
  Qed.

End CorrectTrace.


Hint Resolve exists_at_most_f_faulty_two_left : eo.
Hint Resolve exists_at_most_f_faulty_two_right : eo.
Hint Resolve implies_atmost_f_faulty_two_causal_le : eo.
Hint Resolve implies_atmost_f_faulty_two_sym : eo.
Hint Resolve exists_at_most_f_faulty_preserves_causal : eo.
Hint Resolve exists_at_most_f_faulty_preserves_causal_le : eo.
Hint Resolve exists_at_most_f_faulty_twice : eo.
Hint Resolve implies_atmost_f_faulty_local_pred : eo.
Hint Resolve implies_atmost_f_faulty_causal : eo.
Hint Resolve implies_atmost_f_faulty_causal_le : eo.

Hint Resolve nodes_have_correct_traces_before_causal_le : eo.
Hint Resolve nodes_have_correct_traces_before_two_left : eo.
Hint Resolve nodes_have_correct_traces_before_two_right : eo.
Hint Resolve nodes_have_correct_traces_before_causal : eo.

Hint Resolve has_correct_trace_before_preserves_local_le : eo.
Hint Resolve has_correct_trace_before_preserves_causal_le : eo.
Hint Resolve has_correct_trace_bounded_preserves_local_le : eo.
Hint Resolve some_trigger_implies_isCorrect : eo.
Hint Resolve has_correct_trace_before_local_pred_implies : eo.
Hint Resolve node_has_correct_trace_before_preserves_local_le : eo.
Hint Resolve node_has_correct_trace_before_preserves_causal_le : eo.
Hint Resolve node_has_correct_trace_before_preserves_causal : eo.
