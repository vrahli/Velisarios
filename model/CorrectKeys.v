(*

  Copyright 2016 Luxembourg University
  Copyright 2017 Luxembourg University
  Copyright 2018 Luxembourg University

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


Require Export Process.


Section CorrectKeys.

  Context { pd  : @Data }.
  Context { pn  : @Node }.
  Context { pk  : @Key }.
  Context { pat : @AuthTok }.
  Context { paf : @AuthFun pn pk pat pd }.
  Context { pm  : @Msg }.
  Context { pda : @DataAuth pd pn }.
  Context { qc  : @Quorum_context pn}.

  Local Open Scope eo.
  Local Open Scope proc.


  Definition correct_keys {F}
             (sm : MUSystem F)
             (K  : forall (i : name), F i -> local_key_map)
             (eo : EventOrdering) : Prop :=
    forall (e : Event) (i : name) (s : F i),
      has_correct_trace_before e i
      -> state_sm_before_event (sm i) e = Some s
      -> keys e = K i s.

End CorrectKeys.
