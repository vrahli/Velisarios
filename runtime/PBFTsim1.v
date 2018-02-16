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


Require Export PBFTsim.


(*
Fixpoint mono_iterate_n_steps
         (s : MonoSimulationState)
         (n : nat) : MonoSimulationState :=
  match n with
  | 0 => s
  | S n =>
    let s1 := run_mono_simulator s in
    mono_iterate_n_steps s1 n
  end.


Definition PBFTinit2 : MonoSimulationState :=
  MkInitMonoSimState PBFTmono_sys (mk_requests 6 17).

(*
Definition PBFTinit2 : MonoSimulationState :=
  MkInitMonoSimState PBFTmono_sys (List.app (mk_requests 2 170) (mk_requests2 7 3 100)).
*)

Definition PBFTsimul_list (L : list nat) : MonoSimulationState :=
  mono_run_n_steps PBFTinit2 L.
 *)


Definition PBFTsimul : MonoSimulationState :=
  let rounds   := [MkRound 0(*position*) 79(*num of steps*)] in
  let switches := [] in
  PBFTsimul_n (MkInitRequests 7 3 100) rounds switches.

Definition PBFTsimul_pp : unit :=
  print_endline (MonoSimulationState2string PBFTsimul).

Extraction "pbft_simul.ml" PBFTsimul_pp.
