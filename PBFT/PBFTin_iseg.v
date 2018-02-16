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


Section PBFTin_iseg.

  Fixpoint In_iseg {A} (iseg : list A) (a : A) (l : list A) {struct l} : Prop :=
    match l with
    | [] => False
    | b :: bs =>
      match iseg with
      | [] => a = b
      | x :: xs => x = b /\ In_iseg xs a bs
      end
    end.

  Lemma in_iseg_prop :
    forall {A} l (iseg : list A) a,
      In_iseg iseg a l <-> exists l', l = iseg ++ (a :: l').
  Proof.
    induction l; simpl; introv.

    - split; intro h; exrepnd; tcsp.
      assert (@length A [] = length (iseg ++ a :: l')) as eqlen.
      { rewrite h0; auto. }
      simpl in eqlen.
      rewrite app_length in eqlen; simpl in eqlen.
      destruct iseg; simpl in *; ginv.

    - destruct iseg.

      + split; intro q; exrepnd; subst; tcsp; simpl in *; ginv; auto.
        exists l; simpl; auto.

      + split; intro q; repnd; subst.

        * apply IHl in q; exrepnd; subst; simpl in *.
          exists l'; dands; auto.

        * exrepnd; simpl in *; ginv.
          dands; auto.
          apply IHl.
          exists l'; auto.
  Qed.

  Fixpoint In_iseg_fseg {A} (iseg fseg : list A) (a : A) (l : list A) {struct l} : Prop :=
    match l with
    | [] => False
    | b :: bs =>
      match iseg with
      | [] => a = b /\ fseg = bs
      | x :: xs => x = b /\ In_iseg_fseg xs fseg a bs
      end
    end.

  Lemma in_iseg_fseg_prop :
    forall {A} l (iseg fseg : list A) a,
      In_iseg_fseg iseg fseg a l <-> l = iseg ++ (a :: fseg).
  Proof.
    induction l; simpl; introv.

    - split; intro h; exrepnd; tcsp.
      assert (@length A [] = length (iseg ++ a :: fseg)) as eqlen.
      { rewrite h; auto. }
      simpl in eqlen.
      rewrite app_length in eqlen; simpl in eqlen.
      destruct iseg; simpl in *; ginv.

    - destruct iseg.

      + split; intro q; exrepnd; subst; tcsp; simpl in *; ginv; auto.

      + split; intro q; repnd; subst.

        * apply IHl in q; exrepnd; subst; simpl in *; auto.

        * exrepnd; simpl in *; ginv.
          dands; auto.
          apply IHl; auto.
  Qed.

  Lemma In_iseg_implies_In :
    forall {T} (L : list T) a iseg, In_iseg iseg a L -> In a L.
  Proof.
    induction L; introv i; simpl in *; tcsp.
    destruct iseg; repnd; subst; tcsp.
    right; eapply IHL; eauto.
  Qed.
  Hint Resolve In_iseg_implies_In : list.

End PBFTin_iseg.

Hint Resolve In_iseg_implies_In : list.
