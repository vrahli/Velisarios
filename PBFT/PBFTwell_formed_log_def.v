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


Require Export PBFTwf_prepared_info.
Require Export PBFTtactics2.


Section PBFTwell_formed_log_def.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition entry2view (e : PBFTlogEntry) : View :=
    match e with
    | Build_PBFTlogEntry bp _ _ _ => request_data2view bp
    end.

  Definition entry2digest (e : PBFTlogEntry) : PBFTdigest :=
    match e with
    | Build_PBFTlogEntry bp _ _ _ => request_data2digest bp
    end.

  Definition requests_and_replies2digest (l : list (Request * option Reply)) : PBFTdigest :=
    create_hash_messages (map (fun x => PBFTrequest (fst x)) l).

  Definition pp_info_has_correct_digest (nfo : logEntryPrePrepareInfo) (d : PBFTdigest) : bool :=
    match nfo with
    | pp_info_pre_prep a reqs =>

      same_digests d (requests_and_replies2digest reqs)

    | pp_info_no_pre_prep => true
    end.

  Record well_formed_log_entry (e : PBFTlogEntry) :=
    {
      (* we never log 2 prepares from the same replica *)
      well_formed_log_entry_prepares :
        no_repeats (map rt_rep (log_entry_prepares e));

      (* we never log 2 commits from the same replica *)
      well_formed_log_entry_commits :
        no_repeats (map rt_rep (log_entry_commits e));

      (* we never log a prepare from the leader *)
      well_formed_log_entry_no_prepare_from_leader :
        ~ In (PBFTprimary (entry2view e)) (map rt_rep (log_entry_prepares e));

      (* the digest is correct *)
      well_formed_log_entry_correct_digest :
        pp_info_has_correct_digest (log_entry_pre_prepare_info e) (entry2digest e) = true;

      (* the entry was created because of some pre_prepare, or some prepare, or some commit message *)
      well_formed_log_entry_has_info :
        pp_info_is_pre_prep  (log_entry_pre_prepare_info e) = true
        \/ ~null (log_entry_prepares e)
        \/ ~null (log_entry_commits e);
    }.

  Inductive well_formed_log : PBFTlog -> Prop :=
  | well_formed_log_nil : well_formed_log []
  | well_formed_log_cons :
      forall entry L,
        (forall entry',
            In entry' L
            -> entries_have_different_request_data entry entry')
        -> well_formed_log_entry entry
        -> well_formed_log L
        -> well_formed_log (entry :: L).
  Hint Constructors well_formed_log.

  (* TODO: prove that this well-formedness property is preserved by PBFT *)

  Definition entry_and_pre_prepare_have_same_digests
             (e : PBFTlogEntry)
             (pp : Pre_prepare) :=
    entry2digest e = pre_prepare2digest pp.

  Definition digest_for_pre_prepare (d : PBFTdigest) (pp : Pre_prepare) :=
    same_digests d (pre_prepare2digest pp).

End PBFTwell_formed_log_def.


Hint Constructors well_formed_log.
