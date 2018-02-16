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



Require Export PBFTreceived_prepare_like1.


Section PBFTprepare_like2request_data.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition is_pre_prepare_like (p : Prepare_like) : bool :=
    match p with
    | prepare_like_pre_prepare pp => true
    | prepare_like_prepare p => false
    end.

  Definition is_prepare_like (p : Prepare_like) : bool :=
    match p with
    | prepare_like_pre_prepare pp => false
    | prepare_like_prepare p => true
    end.

  Definition prepare_like2request_data (p : Prepare_like) : RequestData :=
    match p with
    | prepare_like_pre_prepare pp => pre_prepare2request_data pp (pre_prepare2digest pp)
    | prepare_like_prepare p => prepare2request_data p
    end.

  Definition prepare_like2view (p : Prepare_like) : View :=
    match p with
    | prepare_like_pre_prepare pp => pre_prepare2view pp
    | prepare_like_prepare p => prepare2view p
    end.

  Definition prepare_like2seq (p : Prepare_like) : SeqNum :=
    match p with
    | prepare_like_pre_prepare pp => pre_prepare2seq pp
    | prepare_like_prepare p => prepare2seq p
    end.

  Definition prepare_like2digest (p : Prepare_like) : PBFTdigest :=
    match p with
    | prepare_like_pre_prepare pp => pre_prepare2digest pp
    | prepare_like_prepare p => prepare2digest p
    end.

  Lemma requests2digest_map_fst_as_requests_and_replies2digest :
    forall R,
      requests2digest (map fst R) = requests_and_replies2digest R.
  Proof.
    introv.
    unfold requests_and_replies2digest, requests2digest.
    allrw map_map; auto.
  Qed.
  Hint Resolve requests2digest_map_fst_as_requests_and_replies2digest : pbft.

  Lemma in_entry2prepares_like_implies_prepare_like2request_data :
    forall entry pl,
      well_formed_log_entry entry
      -> In pl (entry2prepares_like entry)
      -> prepare_like2request_data pl = log_entry_request_data entry.
  Proof.
    introv wf i.
    destruct entry, pl, log_entry_request_data, log_entry_pre_prepare_info; simpl in *;
      repndors; ginv; tcsp; simpl; autorewrite with pbft; tcsp.

    - unfold pre_prepare2digest; simpl.
      apply well_formed_log_entry_correct_digest in wf; simpl in wf.
      unfold same_digests in *; smash_pbft.
      rewrite requests2digest_map_fst_as_requests_and_replies2digest; auto.

    - unfold entry2prepares in *; simpl in *; autorewrite with list in *.
      allrw in_map_iff; exrepnd; ginv.

    - unfold entry2prepares_like in *; simpl in *.
      unfold entry2prepares in *; simpl in *; autorewrite with list in *.
      allrw in_map_iff; exrepnd; ginv.

    - unfold entry2prepares_like in *; simpl in *.
      unfold entry2prepares in *; simpl in *; autorewrite with list in *.
      allrw in_map_iff; exrepnd; ginv.
      destruct x; simpl in *; auto.

    - unfold entry2prepares_like in *; simpl in *.
      unfold entry2prepares in *; simpl in *; autorewrite with list in *.
      allrw in_map_iff; exrepnd; ginv.
      destruct x; simpl in *; auto.
  Qed.

End PBFTprepare_like2request_data.


Hint Resolve requests2digest_map_fst_as_requests_and_replies2digest : pbft.
