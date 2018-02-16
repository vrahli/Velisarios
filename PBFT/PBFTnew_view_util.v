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
Require Export PBFTtactics.
Require Export PBFTwf_view_change_state.


Section PBFTnew_view_util.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma view_changed_entry_some_implies_vce_view_equal_view_change2view :
    forall v e vc e',
      wf_view_change_entry e
      -> view_changed_entry v e = Some (vc,e')
      -> vce_view e = view_change2view vc.
  Proof.
    introv wf h; unfold view_changed_entry in h; smash_pbft.
    symmetry; apply wf_view_change_entry_view_change; auto.
  Qed.

  Lemma check_broadcast_new_view_implies_new_view2sender :
    forall i s e nv e' o n,
      wf_view_change_entry e
      -> check_broadcast_new_view i s e = Some (nv, e', o, n)
      -> new_view2sender nv = i.
  Proof.
    introv wf check; unfold check_broadcast_new_view in check; smash_pbft.
    rename_hyp_with view_changed_entry vce.
    apply view_changed_entry_some_implies_vce_view_equal_view_change2view in vce; auto.
    allrw; auto.
  Qed.

  Definition new_view2main_auth_data (nv : NewView) : AuthenticatedData :=
    match nv with
    | new_view nv a => MkAuthData (PBFTmsg_bare_new_view nv) a
    end.

  Lemma new_view2main_auth_data_in_new_view2auth_data :
    forall nv, In (new_view2main_auth_data nv) (new_view2auth_data nv).
  Proof.
    introv.
    destruct nv, v; simpl; tcsp.
  Qed.
  Hint Resolve new_view2main_auth_data_in_new_view2auth_data : pbft.

  Lemma verify_new_view_implies_verify_authenticated_data_new_view2main :
    forall n keys nv,
      verify_new_view n keys nv = true
      -> verify_authenticated_data (PBFTreplica n) (new_view2main_auth_data nv) keys = true.
  Proof.
    introv verif.
    destruct nv, v; simpl in *.
    unfold verify_new_view in *; simpl in *; smash_pbft.
  Qed.
  Hint Resolve verify_new_view_implies_verify_authenticated_data_new_view2main : pbft.

End PBFTnew_view_util.


Hint Resolve new_view2main_auth_data_in_new_view2auth_data : pbft.
Hint Resolve verify_new_view_implies_verify_authenticated_data_new_view2main : pbft.
