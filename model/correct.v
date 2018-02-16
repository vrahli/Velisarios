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


Require Export EventOrdering.


Section correct.

  Context { pn  : @Node }.
  Context { pk  : @Key }.
  Context { m   : @Msg }.

  Local Open Scope eo.

  (* This defines what it means for a node [n] to be correct in a partial cut [L]
     of an event ordering [eo]: the keys of all events [e1] happening before [e]
     (an event of the partial cut [L]) at location [n], are different from the keys
     held at other locations at events [e2] prior to [e] *)
  Definition correct (eo : EventOrdering) (n : name) (L : list Event) :=
    forall e e1 e2,
      In e L
      -> e1 ≼ e
      -> e2 ≼ e
      -> loc e1 = n
      -> loc e2 <> n
      -> disjoint (lkm_sending_keys (keys e1)) (lkm_sending_keys (keys e2)).

  Definition correct_e {eo : EventOrdering} (e : Event) :=
    correct eo (loc e) [e].

End correct.
