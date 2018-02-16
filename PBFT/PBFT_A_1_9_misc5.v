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


Require Export PBFTtactics3.
Require Export PBFTcollision_resistant.


Section PBFT_A_1_9_misc5.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context     : PBFTcontext      }.
  Context { pbft_auth        : PBFTauth         }.
  Context { pbft_keys        : PBFTinitial_keys }.
  Context { pbft_hash        : PBFThash         }.
  Context { pbft_hash_axioms : PBFThash_axioms  }.


  Lemma eq_digests_implies_eq_requests :
    forall rs rs',
      requests2digest rs = requests2digest rs'
      -> rs = rs'.
  Proof.
    introv eqrs.
    unfold requests2digest in *.
    apply create_hash_messages_collision_resistant in eqrs.
    revert dependent rs'.
    induction rs; introv eqrs;
      repeat (simpl in *; ginv; smash_pbft; tcsp);
      destruct rs'; simpl in *; smash_pbft.
    inversion eqrs; subst; f_equal; tcsp.
  Qed.

End PBFT_A_1_9_misc5.
