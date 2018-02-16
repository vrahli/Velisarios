(*

  Copyright 2016 University of Luxembourg

  This file is part of our formalization of Platzer's
    "A Complete Uniform Substitution Calculus for Differential Dynamic Logic"
  available here: http://arxiv.org/pdf/1601.06183.pdf (July 27, 2016).
  We refer to this formalization as DdlCoq here.

  DdlCoq is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  DdlCoq is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with DdlCoq.  If not, see <http://www.gnu.org/licenses/>.

  authors:
    Vincent Rahli
    Marcus Völp
    Ivana Vukotic

 *)

Require Export tactics2.

(**

  Two tactics which we used in order to simplify our proofs.

*)


Ltac dest_cases0 name tac :=
  match goal with

  (* on hypotheses *)

  | [ H : context[if _ then (if _ then _ else _) else _ ] |- _ ] => fail
  | [ H : context[if _ then _ else (if _ then _ else _) ] |- _ ] => fail
  | [ H : context[if (if _ then _ else _) then _ else _ ] |- _ ] => fail
  | [ H : context[if ?c then _ else _ ] |- _ ] =>
    let name1 := fresh name in
    match type of c with
    | deceq _ _ => destruct c
    | {_} + {_} => destruct c
    | _ => remember c as name1; destruct name1
    end; tac
  | [ H : context[ match ?c with | pair _ _ => _ end ] |- _ ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [name1 name2]
  | [ H : context[ match ?c with | Some _ => _ | None => _ end ] |- _ ] =>
    let name1 := fresh name in
    remember c as name1; destruct name1 as [name1|];
    tac
  | [ H : context[ match ?c with | left _ => _ | right _ => _ end ] |- _ ] =>
    let name1 := fresh name in
    destruct c as [name1|name1];
    tac

  (* on conclusion *)

  | [ |- context[if _ then (if _ then _ else _) else _ ] ] => fail
  | [ |- context[if _ then _ else (if _ then _ else _) ] ] => fail
  | [ |- context[if (if _ then _ else _) then _ else _ ] ] => fail
  | [ |- context[if ?c then _ else _ ] ] =>
    let name1 := fresh name in
    match type of c with
    | deceq _ _ => destruct c
    | {_} + {_} => destruct c
    | _ => remember c as name1; destruct name1
    end; tac
  | [ |- context[ match ?c with | pair _ _ => _ end ] ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [name1 name2]
  | [ |- context[ match ?c with | Some _ => _ | None => _ end ] ] =>
    let name1 := fresh name in
    remember c as name1; destruct name1 as [name1|];
    tac
  | [ |- context[ match ?c with | left _ => _ | right _ => _ end ] ] =>
    let name1 := fresh name in
    destruct c as [name1|name1];
    tac

  end.

Ltac dest_cases_end := try (simpl in *; GC; ginv; sp; fail).
Ltac sp_dest_cases_end := try (simpl in *; GC; ginv; fail).

Ltac dest_cases name := dest_cases0 name dest_cases_end.
Ltac sp_dest_cases name := dest_cases0 name sp_dest_cases_end.


Ltac prove_dec :=
  let xx := fresh "xx" in
  try (left; auto; fail);
  try (right; intro xx; inversion xx; subst; auto; fail).


Ltac dLin_hyp name :=
  repeat
    match goal with
    | [ H : forall x : ?T , ((( ?L = x ) \/ _) -> _) |- _ ] =>
      let Hyp := fresh name in
      pose proof (H L (or_introl eq_refl)) as Hyp;
      specialize (fun x y => H x (or_intror y))
    | [ H : forall  x : ?T , False -> _ |- _ ] => clear H
    end.

Ltac clear_diff :=
  repeat match goal with
         | [ H : _ <> _ |- _ ] => clear H
         end.
