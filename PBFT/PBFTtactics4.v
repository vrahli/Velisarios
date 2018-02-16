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


Require Export PBFTtactics2.


(* TODO: MERGE with the other one *)
Ltac prove_by_ind2 ind h eqst sop p m eqtrig trig tac1 tac2 :=
  start_ind ind;
  introv;
  intro_state h eqst;
  try unroll_state;
  try unroll_send;
  try fold (@DirectedMsgs _ _) in *;
  simpl in *;
  destruct_unrolled_state sop p;
  op_st_some m eqtrig;
  (*XX-NEW-XX*)try (rewrite eqtrig in *; simpl in *);
  simplify_ind ind;
  unfold_update ind trig tac1 tac2;
  simpl in *; ginv; subst; tcsp;
  try tac1;
  try (first [conflicting_sends|tac2 ind]).
