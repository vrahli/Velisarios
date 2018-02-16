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


Require Import QArith_base.
Require Import tactics2.
Require Import list_util.
Require Import Eqdep_dec.


Require Import Node.
Require Import Msg.
Require Import Crypto.
Require Import AuthMsg.
Require Import EventOrdering.
Require Import EventOrderingLemmas.
Require Import Process.


Section Components.
  Context { pd     : @Data }.
  Context { pn     : @Node }.
  Context { pk     : @Key }.
  Context { auth   : @Auth pd pk }.
  Context { pm     : @Msg }.
  Context { pda    : @DataAuth pd pn }.

  Local Open Scope eo.
  Local Open Scope proc.

  (* A bunch of components is simply a list of state machines.
     The idea is that instead of using bind, we would add a new state machine
     to the list.
   *)
  Definition Components {S I O} : Type := list (StateMachine S I O).

End Components.