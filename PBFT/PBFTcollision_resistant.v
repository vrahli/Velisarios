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


Require Export PBFT.


Section PBFTcollision_resistant.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Class PBFThash_axioms :=
    {
      create_hash_messages_collision_resistant :
        forall msgs1 msgs2,
          create_hash_messages msgs1 = create_hash_messages msgs2
          -> msgs1 = msgs2;

      create_hash_state_last_reply_collision_resistant :
        forall sm1 sm2 last1 last2,
          create_hash_state_last_reply sm1 last1 = create_hash_state_last_reply sm2 last2
          -> sm1 = sm2 /\ last1 = last2
    }.

  Context { pbft_hash_axioms : PBFThash_axioms }.

End PBFTcollision_resistant.
