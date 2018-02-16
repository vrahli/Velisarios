
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


Require Export Quorum.
Require Export Process.


Section Received_or_generated.

  Context { pd  : @Data }.
  Context { pn  : @Node }.
  Context { pk  : @Key }.
  Context { pm  : @Msg }.
  Context { qc  : @Quorum_context pn}.

  Local Open Scope eo.
  Local Open Scope proc.


  Definition received_or_generated {S}
             (eo   : EventOrdering)
             (sm   : MStateMachine S)
             (Cond : Event -> S -> Prop)
             (Rec  : Event -> S -> S -> Event -> S -> Prop)
             (Gen  : Event -> S -> S -> Event -> S  -> Prop) :=
    forall (e : Event) (st : S ),
      state_sm_on_event sm e = Some st
      -> Cond e st
      ->
    exists e' st1 st2,
      e' ⊑ e
      /\ state_sm_before_event sm e' = Some st1
      /\ state_sm_on_event sm e' = Some st2
      /\ (Rec e' st1 st2 e st \/ Gen e' st1 st2 e st).

  Definition received_or_generated_loc {S}
             (eo   : EventOrdering)
             (i    : node_type)
             (sm   : MStateMachine S)
             (Cond : Event -> node_type -> S -> Prop)
             (Rec  : Event -> S -> S -> Event -> node_type -> S -> Prop)
             (Gen  : Event -> S -> S -> Event -> node_type -> S  -> Prop) :=
    forall (e : Event) (st : S ),
      loc e = node2name i
      -> state_sm_on_event sm e = Some st
      -> Cond e i st
      ->
    exists e' st1 st2,
      e' ⊑ e
      /\ state_sm_before_event sm e' = Some st1
      /\ state_sm_on_event sm e' = Some st2
      /\ (Rec e' st1 st2 e i st \/ Gen e' st1 st2 e i st).


(*
Definition received_or_generated
             (eo : EventOrdering)
             (Cond : Event -> Rep -> PBFTstate -> Prop)
             (Rec  : Event -> PBFTstate -> PBFTstate -> Event -> Rep -> PBFTstate -> Prop)
             (Gen  : Event -> PBFTstate -> PBFTstate -> Event -> Rep -> PBFTstate -> Prop) :=
    forall (e : Event) (i : Rep) (st : PBFTstate),
      loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) eo e = Some st
      -> Cond e i st
      ->
    exists e' st1 st2,
      e' ⊑ e
      /\ state_sm_before_event (PBFTreplicaSM i) eo e' = Some st1
      /\ state_sm_on_event (PBFTreplicaSM i) eo e' = Some st2
      /\ (Rec e' st1 st2 e i st \/ Gen e' st1 st2 e i st).
*)

End Received_or_generated.
