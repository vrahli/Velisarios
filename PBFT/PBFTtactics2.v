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

Require Export PBFTtactics.


Ltac pred_happened_before_ind_local_pred e ind :=
  induction e as [? ind] using predHappenedBeforeInd_local_pred;[].

Ltac intro_state_step h eqst :=
  match goal with
  | [ |- state_sm_before_event _ _ = _ -> _ ] => let eqst' := fresh eqst in intro eqst'
  | [ |- state_sm_on_event _ _ = _ -> _ ] => let eqst' := fresh eqst in intro eqst'
  | [ |- _ -> _ ] => let h' := fresh h in intro h'
  | _ => idtac
  end.

Ltac intro_state h eqst := repeat (intro_state_step h eqst).

Ltac unroll_state :=
  match goal with
  | [ H : state_sm_before_event _ ?e = _ |- _ ] =>
    let d := fresh "d" in
    rewrite state_sm_before_event_unroll in H; simpl in H;
    destruct (dec_isFirst e) as [d|d];
    [ginv; simpl in *; auto; fail|]
  | [ H : state_sm_on_event _ _ = _ |- _ ] =>
    rewrite state_sm_on_event_unroll2 in H
  end.

Ltac unroll_send :=
  match goal with
  | [ H : In _ (output_system_on_event_ldata ?s _) |- _ ] =>
    apply in_output_system_on_event_ldata in H;
    try unfold PBFTsys in H;
    try match goal with
        | [ K : loc _ = _ |- _ ] => rewrite K in H
        end;
    try rw @loutput_sm_on_event_unroll2 in H
  end.

Ltac destruct_unrolled_state sop p :=
  match goal with
  | [ H : context[map_option _ ?s] |- _ ] =>
    let sop := fresh sop in
    let p := fresh p in
    remember s as sop;
    match goal with
    | [ H : sop = _ |- _ ] =>
      symmetry in H;
      destruct sop as [p|];
      simpl in *;[|ginv;fail]
    end

  | [ H : context[option_map _ ?s] |- _ ] =>
    let sop := fresh sop in
    let p := fresh p in
    remember s as sop;
    match goal with
    | [ H : sop = _ |- _ ] =>
      symmetry in H;
      destruct sop as [p|];
      simpl in *;[|ginv;tcsp;fail]
    end
  end.

Ltac simplify_ind ind :=
  let hyp := fresh "hyp" in
  repeat match type of ind with
         | ~ isFirst ?e -> _ =>
           match goal with
           | [ H : notT (isFirst e) |- _ ] => autodimp ind hyp;[]
           end
         | (forall x : _, Some ?y = Some x -> _) =>
           pose proof (ind y) as ind; autodimp ind hyp;[]
         end.

Ltac unfold_update ind trig tac1 tac2 :=
  match goal with
  | [ H : fst (PBFTreplica_update _ _ ?t) = Some _ |- _ ] =>
    let trig := fresh trig in
    unfold PBFTreplica_update in H;
    remember t as trig;
    match goal with
    | [ H : trig = _ |- _ ] => symmetry in H
    end;
    destruct trig
  end.

Ltac start_ind ind :=
  match goal with
  | [ |- forall x : _, _ ] =>
    intro x;
    match type of x with
    | Event => pred_happened_before_ind_local_pred x ind
    | _ => start_ind ind
    end
  end.

Ltac op_st_some m h :=
  match goal with
  | [ H : op_state _ _ _ = Some _ |- _ ] =>
    apply op_state_some_iff in H;
    destruct H as [m [h H]]
  end.

Ltac prove_by_ind ind h eqst sop p m eqtrig trig tac1 tac2 :=
  start_ind ind;
  introv;
  intro_state h eqst;
  try unroll_state;
  try unroll_send;
  try fold (@DirectedMsgs _ _) in *;
  simpl in *;
  destruct_unrolled_state sop p;
  op_st_some m eqtrig;
  simplify_ind ind;
  unfold_update ind trig tac1 tac2;
  simpl in *; ginv; subst; tcsp;
  try tac1;
  try (first [conflicting_sends|tac2 ind]).
