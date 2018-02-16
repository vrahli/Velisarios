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


(* Halts as soon as [sm] produces something *)
Definition Once {S I O : Type} (sm : StateMachine S I (list O)) : StateMachine S I (list O) :=
  MkSM
    (sm_halted sm)
    (fun s i =>
       match sm_update sm s i with
       | (Some s', l) =>
         if nullb l
         then (Some s', l)
         else (None, l) (* We halt as soon as we produce something *)
       | (None, l) => (None, l)
       end)
    (sm_state sm).

Definition nOnce {S I O : Type} (sm : NStateMachine S I (list O)) : NStateMachine S I (list O) :=
  fun slf => Once (sm slf).
