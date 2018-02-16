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


Require Import Process.


Definition pairSM_upd {SX SY I T U : Type}
           (X : Update SX I T)
           (Y : Update SY I U) : Update (pstate SX SY) I (pstate T U) :=
  fun state i =>
    match state with
    | pstate_two sx sy =>
      let (sx', t) := X sx i in
      let (sy', u) := Y sy i in
      (opt_states2pstate sx' sy', pstate_two t u)
    | pstate_left sx =>
      let (sx', t) := X sx i in
      (option_map (fun x => pstate_left x) sx', pstate_left t)
    | pstate_right sy =>
      let (sy', u) := Y sy i in
      (option_map (fun x => pstate_right x) sy', pstate_right u)
    end.

Definition pairSM {SX SY I T U : Type}
           (X : StateMachine SX I T)
           (Y : StateMachine SY I U)
  : StateMachine (pstate SX SY) I (pstate T U) :=
  mkSM (pairSM_upd (sm_update X) (sm_update Y)) (pstate_two (sm_state X) (sm_state Y)).

Definition npairSM {SX SY I T U : Type}
           (X : NStateMachine SX I T)
           (Y : NStateMachine SY I U)
  : NStateMachine (pstate SX SY) I (pstate T U) :=
  fun n => pairSM (X n) (Y n).
