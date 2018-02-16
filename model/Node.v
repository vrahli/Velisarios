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


Require Export tactics2.
Require Export EquivDec.


Section Node.

  (* Type with decidable equality *)
  Class Node :=
    MkNode {
        (* The internal nodes for which we're going to assign state machines *)
        name : Set;
        (* The external nodes, to which we can send messages but that are not running our state machines *)
        (*    ename : Type;*)

        (* both these types have to have decidable equality *)
        name_dec : Deq name;
        (*    external_name_dec : Deq ename;*)
      }.

  (* example of Node where both internal and external nodes are modeled as natural numbers *)
  Instance nat_node : Node := MkNode nat eq_nat_dec.

End Node.
