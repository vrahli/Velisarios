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


(* Pair of states *)
Inductive pstate SX SY :=
| pstate_two (l : SX) (r : SY)
| pstate_left (l : SX)
| pstate_right (r : SY).
Arguments pstate_two [SX] [SY] _ _.
Arguments pstate_left [SX] [SY] _.
Arguments pstate_right [SX] [SY] _.

Definition opt_states2pstate
           {SX SY}
           (sx : option SX)
           (sy : option SY) : option (pstate SX SY) :=
  match sx, sy with
  | Some x, Some y => Some (pstate_two x y)
  | Some x, None => Some (pstate_left x)
  | None, Some y => Some (pstate_right y)
  | None, None => None
  end.
