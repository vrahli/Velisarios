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


Require Export PBFTprops2.


Section PBFTwf_prepared_info.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma select_some_implies_in :
    forall {A} (l : list A) i x,
      select i l = Some x -> In x l.
  Proof.
    induction l; introv h; simpl in *; tcsp; destruct i; simpl in *; ginv; tcsp.
    apply IHl in h; tcsp.
  Qed.
  Hint Resolve select_some_implies_in : list.

  Lemma CheckBCastNewView2entry_some_implies :
    forall c S e,
      CheckBCastNewView2entry c S = Some e
      -> In e S.
  Proof.
    introv check; unfold CheckBCastNewView2entry in check; destruct c; eauto 2 with list.
  Qed.
  Hint Resolve CheckBCastNewView2entry_some_implies : pbft.

  Lemma in_app_cons_implies_in_cons_app :
    forall {A} (a : A) l1 x l2,
      In a (l1 ++ x :: l2)
      -> a = x \/ In a (l1 ++ l2).
  Proof.
    introv i; allrw in_app_iff; simpl in *; tcsp.
  Qed.

  Definition wf_prepared_info (p : PreparedInfo) : bool :=
    prepared_info_has_correct_digest p.

  Definition wf_prepared_infos (l : list PreparedInfo) : bool :=
    forallb wf_prepared_info l.

  Lemma wf_prepared_info_if_in :
    forall e C,
      In e C
      -> wf_prepared_infos C = true
      -> wf_prepared_info e = true.
  Proof.
    introv i wf.
    unfold wf_prepared_infos in wf.
    rw forallb_forall in wf; tcsp.
  Qed.
  Hint Resolve wf_prepared_info_if_in : pbft.

  Lemma in_view_change_cert2prep_implies :
    forall C p,
      In p (view_change_cert2prep C)
      -> exists vc, In vc C /\ In p (view_change2prep vc).
  Proof.
    induction C; introv i; simpl in *; tcsp.
    allrw in_app_iff; repndors; tcsp.
    - exists a; tcsp.
    - apply IHC in i; exrepnd.
      exists vc; tcsp.
  Qed.

  Lemma all_correct_view_change_implies_wf_prepared_infos :
    forall entry view,
      forallb (correct_view_change view) (view_change_entry2view_changes entry) = true
      -> wf_prepared_infos (view_change_cert2prep (view_change_entry2view_changes entry)) = true.
  Proof.
    introv allb.
    unfold wf_prepared_infos.
    allrw forallb_forall.
    introv i.
    destruct entry; simpl in *.
    destruct vce_view_change; simpl in *; tcsp.

    - apply in_app_iff in i; repndors.

      + pose proof (allb v) as q; clear allb; autodimp q hyp.
        unfold correct_view_change in q.
        allrw andb_true; repnd.
        unfold correct_view_change_preps in *.
        rename_hyp_with forallb fb.
        allrw forallb_forall.
        apply fb in i; clear q.
        allrw andb_true; repnd.
        unfold valid_prepared_info in *.
        allrw andb_true; repnd.
        unfold info_is_prepared in *.
        allrw andb_true; repnd; tcsp.

      + apply in_view_change_cert2prep_implies in i; exrepnd.
        pose proof (allb vc) as q; clear allb; autodimp q hyp.
        unfold correct_view_change in q.
        allrw andb_true; repnd.
        unfold correct_view_change_preps in *.
        rename_hyp_with forallb fb.
        allrw forallb_forall.
        apply fb in i0; clear q.
        allrw andb_true; repnd.
        unfold valid_prepared_info in *.
        allrw andb_true; repnd.
        unfold info_is_prepared in *.
        allrw andb_true; repnd; tcsp.

    - apply in_view_change_cert2prep_implies in i; exrepnd.
      pose proof (allb vc) as q; clear allb; autodimp q hyp.
      unfold correct_view_change in q.
      allrw andb_true; repnd.
      unfold correct_view_change_preps in *.
      rename_hyp_with forallb fb.
      allrw forallb_forall.
      apply fb in i0; clear q.
      allrw andb_true; repnd.
      unfold valid_prepared_info in *.
      allrw andb_true; repnd.
      unfold info_is_prepared in *.
      allrw andb_true; repnd; tcsp.
  Qed.
  Hint Resolve all_correct_view_change_implies_wf_prepared_infos : pbft.

End PBFTwf_prepared_info.


Hint Resolve select_some_implies_in : list.
Hint Resolve CheckBCastNewView2entry_some_implies : pbft.
Hint Resolve wf_prepared_info_if_in : pbft.
Hint Resolve all_correct_view_change_implies_wf_prepared_infos : pbft.
