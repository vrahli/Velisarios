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


Definition PBFTsimul : MonoSimulationState :=
  let num_requests     := 2  in
  let starting_seq_num := 0  in
  let req_operation    := 17 in
  let rounds   := [MkRound 0(*pos*) 5(*num steps*), MkRound 3 25, MkRound 0 36] in
  let switches := [MkSwitch 1 0] in
  PBFTsimul_n
    (MkInitRequests num_requests starting_seq_num req_operation)
    rounds
    switches.

Definition PBFTsimul_pp : unit :=
  print_endline (MonoSimulationState2string PBFTsimul).

Extraction "pbft_simul.ml" PBFTsimul_pp.



(* =================================================*)



(*
(* This runs forever *)
Eval vm_compute in (PBFTsimul_list [0]).
*)

Goal False.

  assert (PBFTsimul_list [0,0] = (0,PBFTinit,[]));
    simpl; unfold PBFTsimul_list, PBFTsimul, PBFTinit, run_mono_simulator_at; simpl.

3
  (* Too slow!  Could we force the evaluation of expressions? *)


(*    let init := constr:(MkInitSimState PBFTsys [MkDMsg dst req]) in
    assert (run_n_steps init [0,0,0] = (0,init,[]));
      simpl; unfold run_simulator_at; simpl.*)

(*
    unfold lrun_sm; simpl.
    unfold sm_halted; simpl.
    unfold eq_rect; simpl.
    unfold eq_ind_r; simpl.
    unfold eq_ind; simpl.
    unfold eq_rect; simpl.
    unfold eq_sym; simpl.
    unfold eq_trans; simpl.
    unfold f_equal; simpl.
 *)

Qed.
