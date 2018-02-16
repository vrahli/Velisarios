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


Require Export Node.


Section Node.

  Context { n : @Node }.

  Class Msg := MkMsg { msg : Type }.

  Context { m : Msg }.

  (* @Ivana: We don't care about source, because:
    "If you don't want to say who you are you don't have to say who you are" *)

  Record DirectedMsg :=
    MkDMsg
      {
        dmMsg   : msg;
        dmDst   : list name; (* list of destinations *)
        dmDelay : nat;       (* delay in ms *)
      }.

  Definition DirectedMsgs := list DirectedMsg.

End Node.
