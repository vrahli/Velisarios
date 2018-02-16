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


Require Export PBFTwf_checkpoint_state.


Section PBFTstate_info.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.

  Record StateInfo :=
    MkStateInfo
      {
        si_digest : PBFTdigest;
        si_seq    : SeqNum;
      }.

  Definition view_change2state_info (vc : ViewChange) : StateInfo :=
    MkStateInfo (view_change2digest vc) (view_change2seq vc).

  Definition checkpoint2state_info (cp : Checkpoint) : StateInfo :=
    MkStateInfo (checkpoint2digest cp) (checkpoint2seq cp).

End PBFTstate_info.
