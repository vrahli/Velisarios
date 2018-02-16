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


Require Export ComponentSM.


Section ComponentSMExample1.

  Definition def_nat : nat := 0.

  Definition CIOnat : ComponentIO :=
    MkComponentIO nat nat def_nat.

  Instance funIOnat : funIO := MkFunIO (fun _ => CIOnat).

  Definition m_counter_update : M_Update 0 "A" nat :=
    fun (s : nat) i =>
      ret _ (Some (s + i), s + i).

  Definition A : M_StateMachine 1 "A" :=
    build_m_sm m_counter_update 0.

  Definition B_update : M_Update 1 "B" nat :=
    fun s i =>
      (call_proc "A" i)
        >>= fun out =>
      ret _ (Some (s + out + 1), s + out + 1).

  Definition B : M_StateMachine 2 "B" :=
    build_m_sm B_update 0.

  Definition C_update : M_Update 2 "C" nat :=
    fun s i =>
      (call_proc "B" i)
        >>= fun out1 =>
      (call_proc "B" i)
        >>= fun out2 =>
      ret _ (Some (s + out1 + out2 + 2), s + out1 + out2 + 2).

  Definition C : M_StateMachine 3 "C" :=
    build_m_sm C_update 0.

  Definition M_update : M_Update 3 "M" unit :=
    fun s i =>
      (call_proc "C" i)
        >>= (fun out => ret _ (Some s, out)).

  Definition M : M_StateMachine 4 "M" :=
    build_m_sm M_update tt.

  Definition progs : n_procs 3 :=
    [existT _ "A" (incr_n_proc (incr_n_proc A)),
     existT _ "B" (incr_n_proc B),
     existT _ "C" C].

  Eval compute in (snd (run_n_proc M [17] progs)).

  Definition ls :=
    MkLocalSystem
      3
      (existT _ "M" M)
      [existT _ "A" (incr_n_proc (incr_n_proc A)),
       existT _ "B" (incr_n_proc B),
       existT _ "C" C].

  Eval compute in (snd (run_local_system ls [17,33,2])).

End ComponentSMExample1.
