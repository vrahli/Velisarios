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


Require Export PBFTlearns_or_knows_pl.


Section PBFTknows_prepared.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma prepared_log_implies_prepared_entry :
    forall (rd : RequestData) (L : PBFTlog),
      well_formed_log L
      -> prepared_log rd L = true
      -> exists entry,
          In entry L
          /\ rd = log_entry_request_data entry
          /\ is_prepared_entry entry = true.
  Proof.
    induction L; introv wf prep; simpl in *; tcsp.
    inversion wf as [|? ? imp wf1 wf2]; clear wf; subst; smash_pbft.

    - exists a; dands; auto.
      unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.

    - repeat (autodimp IHL hyp); exrepnd.
      eexists; dands; eauto.
  Qed.

  Hint Resolve well_formed_log_entry_if_in : pbft.

  Lemma filter_is_pre_prepare_like_map_prepare_like_prepare :
    forall rd l,
      filter
        is_pre_prepare_like
        (map (fun x => prepare_like_prepare (request_data_and_rep_toks2prepare rd x)) l)
      = [].
  Proof.
    induction l; simpl; auto.
  Qed.
  Hint Rewrite filter_is_pre_prepare_like_map_prepare_like_prepare : pbft.

  Lemma is_prepared_entry_implies_one_pre_prepare :
    forall entry,
      is_prepared_entry entry = true
      -> one_pre_prepare (entry2prepares_like entry).
  Proof.
    introv isprep.
    destruct entry, log_entry_request_data, log_entry_pre_prepare_info; simpl in *; smash_pbft.
    unfold one_pre_prepare, entry2prepares_like, entry2prepares; simpl.
    allrw map_map; unfold compose; autorewrite with pbft; simpl; auto.
  Qed.
  Hint Resolve is_prepared_entry_implies_one_pre_prepare : pbft.

  Hint Resolve in_entry2prepares_like_implies_prepare_like2request_data : pbft.

  Lemma prepared_as_pbft_knows_rd :
    forall (eo : EventOrdering) (e : Event) (rd : RequestData) i s,
      loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some s
      -> well_formed_log (log s)
      -> prepared rd s = true
      -> pbft_knows_rd e rd.
  Proof.
    introv eqloc eqst wf prep.
    apply prepared_log_implies_prepared_entry in prep; auto;[]; exrepnd; subst.
    applydup is_prepared_entry_implies_prepares_like in prep0; eauto 2 with pbft;[]; repnd.

    exists (entry2prepares_like entry); simpl.
    dands; auto; eauto 3 with pbft.
    introv j.

    dands; try (symmetry; eauto 3 with pbft).
    exists s i; dands; simpl; auto; try unfold pbft_pl_knows; eauto 3 with pbft.
  Qed.

End PBFTknows_prepared.


Hint Resolve well_formed_log_entry_if_in : pbft.
Hint Resolve is_prepared_entry_implies_one_pre_prepare : pbft.
Hint Resolve in_entry2prepares_like_implies_prepare_like2request_data : pbft.


Hint Rewrite @filter_is_pre_prepare_like_map_prepare_like_prepare : pbft.
