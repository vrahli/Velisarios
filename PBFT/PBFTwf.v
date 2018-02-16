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


Require Export PBFTwell_formed_log.


Section PBFTwf.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.

  Lemma update_state_new_view_preserves_wf :
    forall i s1 nv s2 msgs,
      update_state_new_view i s1 nv = (s2, msgs)
      -> well_formed_log (log s1)
      -> well_formed_log (log s2).
  Proof.
    introv upd wf.
    unfold update_state_new_view in upd; smash_pbft.
  Qed.
  Hint Resolve update_state_new_view_preserves_wf : pbft.

End PBFTwf.


Hint Resolve update_state_new_view_preserves_wf : pbft.
