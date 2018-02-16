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


Definition composeSM_upd {SX SY I T U W : Type}
           (f : U -> T -> W)
           (X : Update SX U T)
           (Y : Update SY I (option U)) : Update (pstate SX SY) I (option W) :=
  fun state i =>
    match state with
    | pstate_two sx sy =>
      let (syop, uop) := Y sy i in
      match uop with
      | Some u =>
        let (sxop, t) := X sx u in
        (opt_states2pstate sxop syop, Some (f u t))
      | None => (opt_states2pstate (Some sx) syop, None)
      end
    | pstate_left _ => (Some state, None)
    | pstate_right _ => (None, None)
    end.

Definition composeSM {SX SY I T U W : Type}
           (f : U -> T -> W)
           (X : StateMachine SX U T)
           (Y : StateMachine SY I (option U))
  : StateMachine (pstate SX SY) I (option W) :=
  mkSM (composeSM_upd f (sm_update X) (sm_update Y))
       (pstate_two (sm_state X) (sm_state Y)).

Definition ncomposeSM {SX SY I T U W : Type}
           (f : U -> T -> W)
           (X : NStateMachine SX U T)
           (Y : NStateMachine SY I (option U))
  : NStateMachine (pstate SX SY) I (option W) :=
  fun n => composeSM f (X n) (Y n).
