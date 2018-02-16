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


Ltac simplifier_pair :=
  match goal with
  | [ H : (?x,?y) = (?x,?y) |- _ ] => clear H
  | [ H : (_, _) = (_, _) |- _ ] => progress (inversion H; clear H; try subst)
  | [ H : (_, _) = _ _ |- _ ] => symmetry in H
  end.

Ltac simplifier_some :=
  match goal with
  | [ H : Some ?x = Some ?x |- _ ] => clear H
  | [ H : Some _ = Some _ |- _ ] => progress (inversion H; clear H; try subst)
  | [ H : Some _ = _ _ |- _ ] => symmetry in H
  end.

Ltac simplifier_none :=
  match goal with
  | [ H : None = None |- _ ] => clear H
  | [ H : None = _ _ |- _ ] => symmetry in H
  end.

Ltac simplifier_step :=
  match goal with
  | [ H : False |- _ ] => inversion H

  | [ H : true = false |- _ ] => inversion H
  | [ H : false = true |- _ ] => inversion H

  | [ H : Some _ = None |- _ ] => inversion H
  | [ H : None = Some _ |- _ ] => inversion H

  | [ H : ?x = ?x |- _ ] => clear H

  | [ H : ?a = ?b |- _ ] => clear H; assert (a = b) as H by reflexivity; clear H

  | [ H : _ /\ _ |- _ ] => let h := fresh H in destruct H as [H h]

  | [ H : _ \/ False |- _ ] => destruct H as [H|H];[|inversion H];[]
  | [ H : False \/ _ |- _ ] => destruct H as [H|H];[inversion H|];[]

  | [ H : _ \/ True |- _ ] => clear H
  | [ H : True \/ _ |- _ ] => clear H

  | [ H : _ /\ False |- _ ] => let h := fresh H in destruct H as [H h];inversion h;fail
  | [ H : False /\ _ |- _ ] => let h := fresh H in destruct H as [h H];inversion h;fail

  | [ H : _ /\ True |- _ ] => let h := fresh H in destruct H as [H h];inversion h;clear h
  | [ H : True /\ _ |- _ ] => let h := fresh H in destruct H as [h H];inversion h;clear h

  | [ H : true  = _ |- _ ] => symmetry in H
  | [ H : false = _ |- _ ] => symmetry in H

  | [ H : false = true  \/ _ |- _ ] => destruct H as [H|H];[inversion H|];[]
  | [ H : true  = false \/ _ |- _ ] => destruct H as [H|H];[inversion H|];[]

  | [ H : true  = true  \/ _ |- _ ] => clear H
  | [ H : false = false \/ _ |- _ ] => clear H

  | [ H1 : ?x = true, H2 : ?x = false |- _ ] => rewrite H1 in H2; inversion H2

  | [ H : (_, _) = _ |- _ ] => simplifier_pair
  | [ H : Some _ = _ |- _ ] => simplifier_some
  | [ H : None   = _ |- _ ] => simplifier_none

  | [ H : context[_ <=? _ = false] |- _ ] => rewrite Nat.leb_gt in H
  | [ H : context[_ <=? _ = true]  |- _ ] => rewrite Nat.leb_le in H

  | [ |- context[_ <=? _ = false] ] => rewrite Nat.leb_gt
  | [ |- context[_ <=? _ = true]  ] => rewrite Nat.leb_le

  | [ H : context[_ <? _ = false] |- _ ] => rewrite Nat.ltb_ge in H
  | [ H : context[_ <? _ = true]  |- _ ] => rewrite Nat.ltb_lt in H

  | [ |- context[_ <? _ = false] ] => rewrite Nat.ltb_ge
  | [ |- context[_ <? _ = true]  ] => rewrite Nat.ltb_lt

  | [ H : context[_ =? _ = true]  |- _ ] => rewrite Nat.eqb_eq  in H
  | [ H : context[_ =? _ = false] |- _ ] => rewrite Nat.eqb_neq in H

  | [ |- context[_ =? _ = true]  ] => rewrite Nat.eqb_eq
  | [ |- context[_ =? _ = false] ] => rewrite Nat.eqb_neq

  | [ H : context[_ || _ = true]  |- _ ] => rewrite orb_true_iff   in H
  | [ H : context[_ || _ = false] |- _ ] => rewrite orb_false_iff  in H
  | [ H : context[_ && _ = true]  |- _ ] => rewrite andb_true_iff  in H
  | [ H : context[_ && _ = false] |- _ ] => rewrite andb_false_iff in H

  | [ |- context[_ || _ = true]  ] => rewrite orb_true_iff
  | [ |- context[_ || _ = false] ] => rewrite orb_false_iff
  | [ |- context[_ && _ = true]  ] => rewrite andb_true_iff
  | [ |- context[_ && _ = false] ] => rewrite andb_false_iff

  | [ H : context[negb _ = false] |- _ ] => rewrite negb_false_iff in H
  | [ H : context[negb _ = true]  |- _ ] => rewrite negb_true_iff  in H

  | [ |- context[negb _ = false] ] => rewrite negb_false_iff
  | [ |- context[negb _ = true]  ] => rewrite negb_true_iff
  end.

Ltac simplifier stac :=
  repeat
    first
    [congruence
    |simplifier_step
    |stac ()].

Ltac gen_inv stac := (*ginv*) simplifier stac.

Ltac dest_cases_gen_inv_end stac :=
  try (simpl in *; GC; gen_inv stac; fail).

Ltac dest_cases_gen_inv name stac :=
  let rec tac := dest_cases_gen_inv_end stac in
  dest_cases0 name tac.

Ltac dest_one name stac :=
  let h := fresh name in
  dest_cases_gen_inv h stac;
  simpl in *;
  gen_inv stac;
  try subst;
  simpl in *;
  auto.

Ltac dest_all name stac ftac :=
  repeat (dest_one name stac;
          ftac ();
          simplifier stac;
          simpl in *;
          auto).

(* typically:
    - atac is an eauto tactic
    - stac is a simplifying tactic
    - ftac is a folding tactic
    - rtac is a autorewrite tactic
 *)
Ltac smash_byzeml_tac atac stac ftac rtac :=
  let x := fresh "x" in
  simpl in *;
  dest_all x stac ftac;
  rtac ();
  simplifier stac;
  atac ().

Ltac sp_smash_byzeml :=
  let tac := fun _ => auto in
  smash_byzeml_tac tac tac tac tac.
