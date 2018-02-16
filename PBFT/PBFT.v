(*

  Copyright 2016 Luxembourg University
  Copyright 2017 Luxembourg University
  Copyright 2018 Luxembourg University

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


Require Export PBFTheader.


(* Contains PBFT implementation *)


Section PBFT.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext }.
  Context { pbft_auth : PBFTauth }.
  Context { pbft_keys : PBFTinitial_keys }.
  Context { pbft_hash : PBFThash }.


  (* ===============================================================
     State
     =============================================================== *)

  (* =========== Primary state =========== *)

  Definition timestamps_of_clients : Type  := Client -> Timestamp.

  Record PBFTprimaryState :=
    Build_Primary_State
      {
        (* number of requests being handled *)
        in_progress     : nat;

        (* requests that we've received since we reached the maximum number
           of requests we're allowed to handle at the same time *)
        (* NOTE: this buffer is currently infinite, which is not possible in practice.
            We should add a parameter that defines the size of the buffer. *)
        request_buffer  : list Request;

        (* Latest timestamp for each client *)
        client_info     : timestamps_of_clients;

        (* Current sequence number *)
        sequence_number : SeqNum;
      }.

  Definition buffer_request (s : PBFTprimaryState) (r : Request) : PBFTprimaryState :=
    Build_Primary_State
      (in_progress     s)
      (r :: request_buffer s)
      (client_info     s)
      (sequence_number s).

  Definition update_client_info
             (f : timestamps_of_clients)
             (c : Client)
             (t : Timestamp) : timestamps_of_clients :=
    fun x => if client_deq x c then t else f x.

  Definition update_timestamp
             (s : PBFTprimaryState)
             (c : Client)
             (t : Timestamp) : PBFTprimaryState :=
    Build_Primary_State
      (in_progress s)
      (request_buffer s)
      (update_client_info (client_info s) c t)
      (sequence_number s).

  Definition update_timestamp_op
             (s   : PBFTprimaryState)
             (cop : option Client)
             (t   : Timestamp) : PBFTprimaryState :=
    match cop with
    | Some c => update_timestamp s c t
    | None => s
    end.

  Definition increment_in_progress (s : PBFTprimaryState) : PBFTprimaryState :=
    Build_Primary_State
      (S (in_progress s))
      (request_buffer  s)
      (client_info     s)
      (sequence_number s).

  Definition increment_seq_num (s : PBFTprimaryState) : PBFTprimaryState :=
    Build_Primary_State
      (in_progress    s)
      (request_buffer s)
      (client_info    s)
      (next_seq (sequence_number s)).

  Definition change_seq_num (s : PBFTprimaryState) (sn : SeqNum) : PBFTprimaryState :=
    Build_Primary_State
      (in_progress    s)
      (request_buffer s)
      (client_info    s)
      (max_seq_num (sequence_number s) sn).

  Definition reset_request_buffer (s : PBFTprimaryState) : PBFTprimaryState :=
    Build_Primary_State
      (in_progress     s)
      []
      (client_info     s)
      (sequence_number s).

  Definition decrement_in_progress (s : PBFTprimaryState) : PBFTprimaryState :=
    Build_Primary_State
      (pred (in_progress s))
      (request_buffer  s)
      (client_info     s)
      (sequence_number s).

  Definition initial_primary_state : PBFTprimaryState :=
    Build_Primary_State
      0
      []
      (fun _ => 0)
      initial_sequence_number.


  (* =========== Request Data =========== *)

  Inductive RequestData :=
  | request_data (v : View) (s : SeqNum) (d : PBFTdigest).

  Definition request_data2view (rd : RequestData) : View :=
    match rd with
    | request_data v _ _ => v
    end.

  Definition request_data2seq (rd : RequestData) : SeqNum :=
    match rd with
    | request_data _ s _ => s
    end.

  Definition request_data2digest (rd : RequestData) : PBFTdigest :=
    match rd with
    | request_data _ _ d => d
    end.

  Lemma RequestData_Deq : Deq RequestData.
  Proof.
    repeat introv.
    destruct x as [v1 s1 d1], y as [v2 s2 d2].
    destruct (ViewDeq v1 v2); subst; prove_dec.
    destruct (SeqNumDeq s1 s2); subst; prove_dec.
    destruct (PBFTdigestdeq d1 d2); subst; prove_dec.
  Defined.

  Definition eq_request_data (rd1 rd2 : RequestData) : bool :=
    if RequestData_Deq rd1 rd2 then true else false.

  Definition bare_pre_prepare2request_data (bpp : Bare_Pre_prepare) (d : PBFTdigest) : RequestData :=
    match bpp with
    | bare_pre_prepare v s _ => request_data v s d
    end.

  Definition pre_prepare2request_data (pp : Pre_prepare) (d : PBFTdigest) : RequestData :=
    match pp with
    | pre_prepare b _ => bare_pre_prepare2request_data b d
    end.

  Definition bare_prepare2request_data (bp : Bare_Prepare) : RequestData :=
    match bp with
    | bare_prepare v s d i => request_data v s d
    end.

  Definition prepare2request_data (p : Prepare) : RequestData :=
    match p with
    | prepare b _ => bare_prepare2request_data b
    end.

  Definition bare_commit2request_data (bc : Bare_Commit) : RequestData :=
    match bc with
    | bare_commit v s d i => request_data v s d
    end.

  Definition commit2request_data (c : Commit) : RequestData :=
    match c with
    | commit b _ => bare_commit2request_data b
    end.

  (* =========== General state =========== *)

  Inductive logEntryPrePrepareInfo :=
  | pp_info_pre_prep (auth : Tokens) (reqs : list (Request * option Reply))
  | pp_info_no_pre_prep.

  Definition pp_info_is_pre_prep (nfo : logEntryPrePrepareInfo) : bool :=
    match nfo with
    | pp_info_pre_prep _ _ => true
    | pp_info_no_pre_prep => false
    end.

  Definition pp_info2requests (nfo : logEntryPrePrepareInfo) : list Request :=
    match nfo with
    | pp_info_pre_prep _ reqs => map fst reqs
    | pp_info_no_pre_prep => []
    end.

  Record RepToks :=
    MkRepToks
      {
        rt_rep    : Rep;
        rt_tokens : Tokens;
      }.

  (* The request is in the pre_prepare message *)
  Record PBFTlogEntry :=
    Build_PBFTlogEntry
      {
        log_entry_request_data     : RequestData;
        log_entry_pre_prepare_info : logEntryPrePrepareInfo;
        log_entry_prepares         : list RepToks;
        log_entry_commits          : list RepToks;
      }.

  Record PBFTcheckpointEntry :=
    Build_PBFTcheckpointEntry
      {
        cp_sn               : SeqNum;
        cp_d                : PBFTdigest;  (* see PBFT thesis p.23 *)
        cp_checkpoint       : list Checkpoint;

        (* val_i*)
        cp_sm_state         : option PBFTsm_state;

        (* state that stores the timestamps and results of the requests executed last
           last_rep_i and last_reply_t_i *)
        cp_last_reply_state : option LastReplyState;

      }.

  Definition log_entry2requests (entry : PBFTlogEntry) : list Request :=
    pp_info2requests (log_entry_pre_prepare_info entry).

  Definition is_pre_prepared_entry (entry : PBFTlogEntry) : bool :=
    match entry with
    | Build_PBFTlogEntry _ nfo _ _ => pp_info_is_pre_prep nfo
    end.

  Definition is_prepared_entry (entry : PBFTlogEntry) : bool :=
    match entry with
    | Build_PBFTlogEntry _ nfo preps _ =>
      (2 * F <=? length preps) && pp_info_is_pre_prep nfo
    end.

  Definition is_committed_entry (entry : PBFTlogEntry) : bool :=
    match entry with
    | Build_PBFTlogEntry _ _ _ comms =>
      is_prepared_entry entry && (2 * F + 1 <=? length comms)
    end.

  Definition is_stable_checkpoint_entry (entry : PBFTcheckpointEntry) : bool :=
    F + 1 <=? length (cp_checkpoint entry).

  Definition entry2pre_prepare (e : PBFTlogEntry) : option Pre_prepare :=
    match e with
    | Build_PBFTlogEntry (request_data v s d) (pp_info_pre_prep a reqs as nfo) _ _ =>
      Some (pre_prepare (bare_pre_prepare v s (pp_info2requests nfo)) a)
    | _ => None
    end.

  Definition pre_prepare2pp_info (pp : Pre_prepare) : logEntryPrePrepareInfo :=
    match pp with
    | pre_prepare (bare_pre_prepare _ _ reqs) a =>
      pp_info_pre_prep
        a
        (map (fun r => (r, None)) reqs) (* None means no replies yet *)
    end.

  Definition pre_prepare2entry (pp : Pre_prepare) (d : PBFTdigest) : PBFTlogEntry :=
    Build_PBFTlogEntry
      (pre_prepare2request_data pp d)
      (pre_prepare2pp_info pp)
      []
      [].

  Definition prepare2rep_toks (p : Prepare) : RepToks :=
    match p with
    | prepare (bare_prepare _ _ _ i) a => MkRepToks i a
    end.

  Definition commit2rep_toks (c : Commit) : RepToks :=
    match c with
    | commit (bare_commit _ _ _ i) a => MkRepToks i a
    end.

  Definition MkNewLogEntryWithPrepare
             (pp : Pre_prepare)
             (d  : PBFTdigest)
             (rt : RepToks) : PBFTlogEntry :=
    Build_PBFTlogEntry
      (pre_prepare2request_data pp d)
      (pre_prepare2pp_info pp)
      [rt]
      [].

  Definition MkNewLogEntryFromPrepare (p : Prepare) : PBFTlogEntry :=
    Build_PBFTlogEntry
      (prepare2request_data p)
      pp_info_no_pre_prep
      [prepare2rep_toks p]
      [].

  Definition MkNewLogEntryFromCommit (c : Commit) : PBFTlogEntry :=
    Build_PBFTlogEntry
      (commit2request_data c)
      pp_info_no_pre_prep
      []
      [commit2rep_toks c].

  Definition MkNewCheckpointEntryFromCheckpoint
             (c  : Checkpoint)
             (sm : option PBFTsm_state)
             (lr : option LastReplyState) : PBFTcheckpointEntry :=
    Build_PBFTcheckpointEntry
      (checkpoint2seq c)
      (checkpoint2digest c)
      [c]
      sm
      lr.

  (* Some says that we added the prepare message to the list *)
  Fixpoint add_prepare2prepares (p : Prepare) (ps : list Prepare) : option (list Prepare) :=
    match ps with
    | [] => Some [p]
    | p' :: ps =>
      if rep_deq (prepare2sender p') (prepare2sender p) then
        (* we don't do anything because there's already a prepare
           with the same sender in the list *)
        None
      else
        match add_prepare2prepares p ps with
        | Some l => Some (p' :: l)
        | None => None
        end
    end.

  (* Some says that we added the commit message to the list *)
  Fixpoint add_commit2commits (c : Commit) (cs : list Commit) : option (list Commit) :=
    match cs with
    | [] => Some [c]
    | c' :: cs =>
      if rep_deq (commit2sender c') (commit2sender c) then
        (* we don't do anything because there's already a commit
           with the same sender in the list *)
        None
      else
        match add_commit2commits c cs with
        | Some l => Some (c' :: l)
        | None => None
        end
    end.

  Definition in_list_rep_toks (i : Rep) (L : list RepToks) : bool :=
    existsb (fun rt => if rep_deq i (rt_rep rt) then true else false) L.

  Fixpoint find_rep_toks_in_list (i : Rep) (L : list RepToks) : option RepToks :=
    match L with
    | [] => None
    | rt :: rts =>
      if rep_deq i (rt_rep rt) then Some rt
      else find_rep_toks_in_list i rts
    end.

  (* Some says that we added the checkpoint message to the list *)
  Fixpoint add_checkpoint2checkpoint (c : Checkpoint) (cs : list Checkpoint) : option (list Checkpoint) :=
    match cs with
    | [] => Some [c]
    | c' :: cs =>
      if rep_deq (checkpoint2sender c') (checkpoint2sender c) then
        (* we don't do anything because there's already a checkpoint
           with the same sender in the list *)
        None
      else
        match add_checkpoint2checkpoint c cs with
        | Some l => Some (c' :: l)
        | None => None
        end
    end.

  Definition find_rep_toks_in_list_default
             (i : Rep)
             (L : list RepToks)
             (F : unit -> RepToks) : RepToks :=
    match find_rep_toks_in_list i L with
    | Some rt => rt
    | None => F tt
    end.

  Inductive add_commit_status :=
  | add_commit_status_already_in
  | add_commit_status_added (rt : RepToks)
  | add_commit_status_not_prepared
  | add_commit_status_na.

  (* We return None when the commit message is already in or it's not time to commit *)
  Definition add_commit_if_prepared
             (i     : Rep)
             (nfo   : logEntryPrePrepareInfo)
             (preps : list RepToks)
             (comms : list RepToks)
             (Fc    : unit -> RepToks) : add_commit_status * (list RepToks) :=

    if pp_info_is_pre_prep nfo then

      if 2 * F <=? length preps then

        if in_list_rep_toks i comms then (add_commit_status_already_in, comms)
        else
          let comm := Fc tt in
          (add_commit_status_added comm, comm :: comms)

      else (* not prepared because we don't have the right number of prepares *)
        (add_commit_status_not_prepared, comms)

    else (* not prepared because we don't have a pre-prepare *)
      (add_commit_status_not_prepared, comms).

  Definition add_checkpoint_if_not_enough
             (chs : list Checkpoint)
             (Fp    : unit -> Checkpoint) : list Checkpoint :=
    if length chs <? F then
      Fp tt :: chs
    else chs.

  Definition request_data_and_rep_toks2prepare
             (rd : RequestData)
             (rt : RepToks) : Prepare :=
    match rd, rt with
    | request_data v s d, MkRepToks i a => prepare (bare_prepare v s d i) a
    end.

  Definition request_data_and_rep_toks2commit
             (rd : RequestData)
             (rt : RepToks) : Commit :=
    match rd, rt with
    | request_data v s d, MkRepToks i a => commit (bare_commit v s d i) a
    end.

  Inductive add_prepare_status :=
  (* the prepare message is already logged *)
  | add_prepare_status_already_in
  (* we managed to add the prepare message *)
  | add_prepare_status_added (rt : RepToks)
  | add_prepare_status_na.

  (* We return None when the prepare message is already in *)
  Definition add_prepare_if_not_enough
             (i     : Rep)
             (preps : list RepToks)
             (Fp    : unit -> RepToks) : add_prepare_status * (list RepToks) :=
    if in_list_rep_toks i preps then (add_prepare_status_already_in, preps)
    else
      let prep := Fp tt in
      (add_prepare_status_added prep, prep :: preps).

  Record GeneratedInfo :=
    MkGeneratedInfo
      {
        gi_prepare : add_prepare_status;
        gi_commit  : add_commit_status;
        gi_entry   : PBFTlogEntry;
      }.

  (* returns None if the info part is already filled out *)
  Definition fill_out_pp_info_with_prepare
             (i     : Rep)
             (entry : PBFTlogEntry)
             (pp    : Pre_prepare)
             (Fp    : unit -> RepToks)
             (Fc    : unit -> RepToks) : option GeneratedInfo :=
    match entry with
    | Build_PBFTlogEntry rd (pp_info_pre_prep _ _ ) preps comms => None
    | Build_PBFTlogEntry rd pp_info_no_pre_prep preps comms =>
      let newinfo := pre_prepare2pp_info pp in
      let (prepop, new_preps) := add_prepare_if_not_enough i preps Fp in
      let (commop, new_comms) := add_commit_if_prepared i newinfo new_preps comms Fc in
      Some (MkGeneratedInfo
              prepop
              commop
              (Build_PBFTlogEntry
                 rd
                 newinfo
                 new_preps
                 new_comms))
    end.

  Definition add_commit2entry (entry : PBFTlogEntry) (c : Commit) : option PBFTlogEntry :=
    match entry with
    | Build_PBFTlogEntry bpp nfo preps comms =>

      let rt := commit2rep_toks c in
      let i  := commit2sender c in
      if in_list_rep_toks i comms then None
      else Some (Build_PBFTlogEntry bpp nfo preps (rt :: comms))

    end.

  Definition update_sm_state_if_needed
             (sm1 : option PBFTsm_state)
             (sm2 : option PBFTsm_state) : option PBFTsm_state :=
    match sm1 with
    | Some _ => sm1
    | None => sm2
    end.

  Definition update_last_reply_state_if_needed
             (lr1 : option LastReplyState)
             (lr2 : option LastReplyState) : option LastReplyState :=
    match lr1 with
    | Some _ => lr1
    | None => lr2
    end.

  Definition add_checkpoint2entry
             (entry : PBFTcheckpointEntry)
             (c : Checkpoint)
             (sm  : option PBFTsm_state)
             (lr  : option LastReplyState) : option PBFTcheckpointEntry :=
    match entry with
    | Build_PBFTcheckpointEntry sn d chs sm_state lr_state =>
      match add_checkpoint2checkpoint c chs with
      | Some new_chs =>
        Some (Build_PBFTcheckpointEntry
                sn d new_chs
                (update_sm_state_if_needed sm_state sm)
                (update_last_reply_state_if_needed lr_state lr))
      | None => None
      end
    end.

  (* we only call this function when we know that we have less than
     2 * F prepares in the entry *)
  Definition add_prepare2entry
             (slf   : Rep)
             (entry : PBFTlogEntry)
             (p     : Prepare)
             (Fc    : unit -> RepToks) : option GeneratedInfo :=
    match entry with
    | Build_PBFTlogEntry bpp nfo preps comms =>

      let Fp := fun _ => prepare2rep_toks p in
      let i  := prepare2sender p in
      let (prepop, new_preps) := add_prepare_if_not_enough i preps Fp in
      let (commop, new_comms) := add_commit_if_prepared slf nfo new_preps comms Fc in

        Some (MkGeneratedInfo
                prepop
                commop
                (Build_PBFTlogEntry bpp nfo new_preps new_comms))

    end.

  Fixpoint combine_replies (l : list (Request * option Reply)) (reps : list (option Reply)) : list (Request * option Reply) :=
    match l, reps with
    | [], [] => []
    | (r,_) :: rs, rep :: reps => (r, rep) :: combine_replies rs reps
    | _, _ => l
    end.

  Definition add_replies2info
             (nfo  : logEntryPrePrepareInfo)
             (reps : list (option Reply)) : logEntryPrePrepareInfo :=
    match nfo with
    | pp_info_pre_prep a reqs => pp_info_pre_prep a (combine_replies reqs reps)
    | pp_info_no_pre_prep => pp_info_no_pre_prep
    end.

  Definition add_replies2entry (entry : PBFTlogEntry) (reps : list (option Reply)) : PBFTlogEntry :=
    match entry with
    | Build_PBFTlogEntry bpp nfo prepares commits =>
      Build_PBFTlogEntry bpp (add_replies2info nfo reps) prepares commits
    end.

  Definition PBFTlog := list PBFTlogEntry.
  Definition PBFTcheckpoint_log := list PBFTcheckpointEntry.

  Record PBFTstableCheckpointEntry :=
    Build_PBFTstableCheckpointEntry
      {
        scp_sn               : SeqNum;
        scp_d                : PBFTdigest;  (* see PBFT thesis p.23 *)
        scp_checkpoint       : list Checkpoint;

        (* val_i*)
        scp_sm_state         : PBFTsm_state;

        (* state that stores the timestamps and results of the requests executed last
           last_rep_i and last_reply_t_i *)
        scp_last_reply_state : LastReplyState;

      }.

  Record PBFTcheckpointState :=
    Build_CheckpointState
      {
        chk_state_stable : PBFTstableCheckpointEntry;
        chk_state_others : PBFTcheckpoint_log;
      }.

  Definition similar_pre_prepare_and_commit
             (pp : Pre_prepare)
             (d  : PBFTdigest)
             (c  : Commit) : bool :=
    eq_request_data (pre_prepare2request_data pp d) (commit2request_data c).

  Definition similar_pre_prepare_and_prepare
             (pp : Pre_prepare)
             (d  : PBFTdigest)
             (p  : Prepare) : bool :=
    eq_request_data (pre_prepare2request_data pp d) (prepare2request_data p).

  Definition similar_pre_prepare_and_request_data
             (pp : Pre_prepare)
             (d  : PBFTdigest)
             (rd : RequestData) : bool :=
    eq_request_data (pre_prepare2request_data pp d) rd.

  Definition similar_bare_pre_prepare_and_request_data
             (bpp : Bare_Pre_prepare)
             (d   : PBFTdigest)
             (rd  : RequestData) : bool :=
    eq_request_data (bare_pre_prepare2request_data bpp d) rd.

  Definition similar_bare_pre_prepare_and_commit
             (bpp : Bare_Pre_prepare)
             (d   : PBFTdigest)
             (c   : Commit) : bool :=
    eq_request_data (bare_pre_prepare2request_data bpp d) (commit2request_data c).

  Definition similar_bare_pre_prepare_and_prepare
             (bpp : Bare_Pre_prepare)
             (d   : PBFTdigest)
             (p   : Prepare) : bool :=
    eq_request_data (bare_pre_prepare2request_data bpp d) (prepare2request_data p).

  Definition similar_bare_pre_prepare_and_pre_prepare
             (bpp : Bare_Pre_prepare)
             (d1  : PBFTdigest)
             (pp  : Pre_prepare)
             (d2  : PBFTdigest) : bool :=
    eq_request_data
      (bare_pre_prepare2request_data bpp d1)
      (pre_prepare2request_data pp d2).

  Definition is_request_data_for_entry
             (entry : PBFTlogEntry)
             (rd    : RequestData) : bool :=
    eq_request_data (log_entry_request_data entry) rd.

  (* checks whether the commit corresponds to the pre-prepare of the entry *)
  Definition is_commit_for_entry
             (entry : PBFTlogEntry)
             (c     : Commit) : bool :=
    eq_request_data (log_entry_request_data entry) (commit2request_data c).

  Definition similar_sn_and_checkpoint_sn (sn : SeqNum) (d : PBFTdigest) (c : Checkpoint) : bool :=
    if SeqNumDeq sn (checkpoint2seq c) then
      if PBFTdigestdeq d (checkpoint2digest c) then true
      else false
    else false.

  (* checks whether the checkpoint corresponds to the sn and vn of the entry *)
  Definition is_checkpoint_for_entry
             (entry : PBFTcheckpointEntry)
             (c     : Checkpoint): bool :=
    similar_sn_and_checkpoint_sn (cp_sn entry) (cp_d entry) c.

  (* checks whether the replica that sent this commit has already sent a commit *)
  Definition is_commit_in_entry
             (entry : PBFTlogEntry)
             (c     : Commit) : bool :=
    let sender := commit2sender c in
    existsb
      (fun rt => if rep_deq (rt_rep rt) sender then true else false)
      (log_entry_commits entry).


  (* checks whether the replica that sent this checkpoint has already sent a checkpoint *)
  Definition is_checkpoint_in_entry
             (entry : PBFTcheckpointEntry)
             (c     : Checkpoint) : bool :=
    existsb
      (fun c' => if rep_deq (checkpoint2sender c') (checkpoint2sender c) then true else false)
      (cp_checkpoint entry).

  (* checks whether the prepare corresponds to the pre-prepare of the entry *)
  Definition is_prepare_for_entry
             (entry : PBFTlogEntry)
             (p     : Prepare) : bool :=
    eq_request_data (log_entry_request_data entry) (prepare2request_data p).

  (* checks whether the replica that sent this prepare has already sent a prepare *)
  Definition is_prepare_in_entry
             (entry : PBFTlogEntry)
             (p     : Prepare) : bool :=
    let sender := prepare2sender p in
    existsb
      (fun rt => if rep_deq (rt_rep rt) sender then true else false)
      (log_entry_prepares entry).

  (* [vc] is here our own view-change message *)
  Definition own_view_change2initial_entry (vc : ViewChange) : PBFTviewChangeEntry :=
    MkViewChangeEntry (view_change2view vc) (Some vc) [] None.

  (* [vc] is not our own view-change message *)
  Definition other_view_change2initial_entry (vc : ViewChange) : PBFTviewChangeEntry :=
    MkViewChangeEntry (view_change2view vc) None [vc] None.

  (* [vc] is here our own view-change message *)
  Definition add_own_view_change2entry (vc : ViewChange) (e : PBFTviewChangeEntry) : PBFTviewChangeEntry :=
    match e with
    | MkViewChangeEntry v None vcs nv => MkViewChangeEntry v (Some vc) vcs nv

    | MkViewChangeEntry v (Some _) vcs nv => e
    end.

  Definition PBFTviewChangeState := list PBFTviewChangeEntry.

  Definition initial_view_change_state : PBFTviewChangeState := [].

  (* The first component is the entry we modified/added *)
  Fixpoint add_own_view_change_to_state
           (vc : ViewChange)
           (l  : list PBFTviewChangeEntry)
    : PBFTviewChangeEntry * nat * PBFTviewChangeState :=
    match l with
    | [] =>
      let entry := own_view_change2initial_entry vc in
      (entry, 0, [entry])
    | entry :: entries =>
      if ViewDeq (view_change2view vc) (vce_view entry) then
        (* the view of the view-change message matches the one of the entry *)

        let new_entry := add_own_view_change2entry vc entry in
        (new_entry, 0, new_entry :: entries)

      else (* the view of the view-change message doesn't match one of the entry *)

        match add_own_view_change_to_state vc entries with
        | (changed_entry, changed_entry_pos, new_entries) =>
          (changed_entry, S changed_entry_pos, entry :: new_entries)
        end
    end.

  (* Everytime we call this function, we also increment our view number, which means
     that we cannot have two entries for different view numbers.
     We might have stated an entry for this view though because we might have
     already received view-change messages from other replicas for this view *)
  Definition start_view_change
             (vc : ViewChange)
             (s  : PBFTviewChangeState)
    : PBFTviewChangeEntry * nat * PBFTviewChangeState :=
    add_own_view_change_to_state vc s.

  (* Some says that we added the view-change message to the list *)
  Fixpoint add_view_change2view_changes
           (vc : ViewChange)
           (vcs : list ViewChange) : option (list ViewChange) :=
    match vcs with
    | [] => Some [vc]
    | vc' :: vcs =>
      if rep_deq (view_change2sender vc') (view_change2sender vc) then
        (* we don't do anything because there's already a view-change
           with the same sender in the list *)
        None
      else
        match add_view_change2view_changes vc vcs with
        | Some l => Some (vc' :: l)
        | None => None
        end
    end.

  (* [vc] is not our own view-change message *)
  Definition add_other_view_change2entry
             (vc : ViewChange)
             (e  : PBFTviewChangeEntry) : option PBFTviewChangeEntry :=
    match e with
    | MkViewChangeEntry v ovc vcs nv =>
      match add_view_change2view_changes vc vcs with
      | Some new_vcs => Some (MkViewChangeEntry v ovc new_vcs nv)
      | None => None
      end
    end.

  (* we return Some if we managed to add the view-change message, and in that
     case we also return the modified entry *)
  Fixpoint add_other_view_change
             (vc    : ViewChange)
             (state : PBFTviewChangeState)
    : option (PBFTviewChangeEntry * nat * PBFTviewChangeState) :=
    match state with
    | [] =>
      let entry := other_view_change2initial_entry vc in
      Some (entry, 0, [entry])
    | entry :: entries =>
      if ViewDeq (view_change2view vc) (vce_view entry) then
        (* the view of the View-change message is the same as the one of the entry *)

        match add_other_view_change2entry vc entry with
        | Some new_entry => Some (new_entry, 0, new_entry :: entries)
        | None => None
        end

      else (* the view of the view-change message is not the same as the one of the entry *)
        match add_other_view_change vc entries with
        | Some (new_entry, new_entry_pos, new_entries) =>
          Some (new_entry, new_entry_pos, entry :: new_entries)
        | None => None
        end
    end.

  Definition update_last_reply_entry_timestamp_and_result
             (e : LastReplyEntry)
             (t : Timestamp)
             (r : PBFTresult) : LastReplyEntry :=
    match e with
    | MkLastReplyEntry c _ _ => MkLastReplyEntry c t (Some r)
    end.

  Fixpoint find_last_reply_entry_corresponding_to_client
           (lrs : LastReplyState)
           (c   : Client) : option LastReplyEntry :=
    match lrs with
    | [] => None
    | entry :: entries =>
      if client_deq c (lre_client entry) then Some entry
      else find_last_reply_entry_corresponding_to_client entries c
    end.

  Fixpoint update_last_reply_timestamp_and_result
           (s : LastReplyState)
           (c : Client)
           (t : Timestamp)
           (r : PBFTresult) : LastReplyState :=
    match s with
    | [] => []
    | entry :: entries =>
      if client_deq c (lre_client entry) then
        update_last_reply_entry_timestamp_and_result entry t r :: entries
      else entry :: update_last_reply_timestamp_and_result entries c t r
    end.

  Record PBFTstate :=
    Build_State
      {
        (* The keys that we're holding to communicate with the other replicas and clients *)
        local_keys        : local_key_map;

        (* Current view *)
        current_view      : View;

        (* Log holding the requests being processed, including prepare and commit messages *)
        log               : PBFTlog;

        (* checkpoint state (last stable and log)*)
        cp_state          : PBFTcheckpointState;

        (* state of the local state machine *)
        sm_state          : PBFTsm_state;

        (* request to execute next *)
        next_to_execute   : SeqNum;

        (* list of sequence numbers of requests that are ready to be executed
           but cannot be executed yet because there are gaps
           --- we keep this list ordered and without duplicates *)
        ready             : list SeqNum;

        (* state that stores the timestamps and results of the requests executed last *)
        last_reply_state  : LastReplyState;

        (* view change state *)
        view_change_state : PBFTviewChangeState;

        (* State for when the replica is the primary *)
        primary_state     : PBFTprimaryState
      }.

  Definition changing_view_entry (view : View) (entry : PBFTviewChangeEntry) : bool :=
    if ViewDeq view (vce_view entry) then
      (* someone started to change views for the current view *)

      if is_some (vce_view_change entry) then
        (* we started changing to this view *)

        if is_some (vce_new_view entry) then
          (* we have already received a new-view message for this view-change,
             which means that we are not changing to this view anymore *)

          false

        else (* we have not yet received a new-view message for this view,
                therefore we are still changing view *)
          true

      else (* the view of the entry is our current view, but no timer has expired yet,
              therefore we are not yet changing view *)
        false

    else (* the view of the entry is not our current view *)
      false.

  Definition initial_ready : list SeqNum := [].

  Definition initial_next_to_execute : SeqNum := seq_num 1.

  Definition other_replicas (r : Rep) : list Rep := remove_elt rep_deq r reps.

  Definition other_names (r : Rep) : list name := map PBFTreplica (other_replicas r).

  Definition initial_last_reply : LastReplyState :=
    map (fun c => MkLastReplyEntry c 0 None) clients.

  Definition initial_stable_checkpoint_entry : PBFTstableCheckpointEntry :=
    let smst   := PBFTsm_initial_state in
    let lastr  := initial_last_reply in
    let digest := create_hash_state_last_reply smst lastr in
    Build_PBFTstableCheckpointEntry
      initial_sequence_number
      digest
      []
      smst
      lastr.

  Definition initial_checkpoint_state : PBFTcheckpointState :=
    Build_CheckpointState
      initial_stable_checkpoint_entry (* we still don't have a stable checkpoint---we use a dummy one as in techrep p.24 *)
      [].    (* log is empty*)

  Definition initial_state (r : Rep) : PBFTstate :=
    Build_State
      (initial_keys (PBFTreplica r))
      initial_view
      []
      initial_checkpoint_state
      PBFTsm_initial_state
      initial_next_to_execute
      initial_ready
      initial_last_reply
      initial_view_change_state
      initial_primary_state.

  Definition update_primary_state (s : PBFTstate) (ps : PBFTprimaryState) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      ps.

  Definition increment_view (s : PBFTstate) : PBFTstate :=
    Build_State
      (local_keys        s)
      (next_view (current_view s))
      (log               s)
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (primary_state     s).

  Definition update_view (s : PBFTstate) (v : View) : PBFTstate :=
    Build_State
      (local_keys        s)
      (max_view (current_view s) v)
      (log               s)
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (primary_state     s).

  Definition change_view_change_state (s : PBFTstate) (vcstate : PBFTviewChangeState) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      vcstate
      (primary_state     s).

  Definition pre_prepares2entries (P : list (Pre_prepare * PBFTdigest)) : PBFTlog :=
    map (fun x => match x with (p,d) => pre_prepare2entry p d end) P.

  Definition similar_entry_and_pre_prepare
             (entry : PBFTlogEntry)
             (pp    : Pre_prepare)
             (d     : PBFTdigest) : bool :=
    match entry with
    | Build_PBFTlogEntry rd _ _ _ =>
      eq_request_data rd (pre_prepare2request_data pp d)
    end.

  Definition change_pre_prepare_info
             (pp  : Pre_prepare)
             (nfo : logEntryPrePrepareInfo) : logEntryPrePrepareInfo :=
    match nfo with
    | pp_info_pre_prep _ _ => nfo
    | pp_info_no_pre_prep  => pre_prepare2pp_info pp
    end.

   Definition change_pre_prepare_info_of_entry
             (pp    : Pre_prepare)
             (entry : PBFTlogEntry) : PBFTlogEntry :=
    match entry with
    | Build_PBFTlogEntry rd nfo preps comms =>
      Build_PBFTlogEntry rd (change_pre_prepare_info pp nfo) preps comms
    end.

  Fixpoint add_new_pre_prepare2log
           (pp : Pre_prepare)
           (d : PBFTdigest)
           (L : PBFTlog) : PBFTlog :=
    match L with
    | [] => [pre_prepare2entry pp d]
    | entry :: entries =>
      if similar_entry_and_pre_prepare entry pp d then

        change_pre_prepare_info_of_entry pp entry :: entries

      else entry :: add_new_pre_prepare2log pp d entries
    end.

  Definition log_new_pre_prepare (s : PBFTstate) (pp : Pre_prepare) (d : PBFTdigest) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (add_new_pre_prepare2log pp d (log s))
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (primary_state     s).

  Fixpoint log_pre_prepares
           (l   : PBFTlog)
           (lwm : SeqNum)
           (P   : list (Pre_prepare * PBFTdigest)) : PBFTlog :=
    match P with
    | [] => l
    | (pp,d) :: pps =>
      if lwm <? pre_prepare2seq pp then
        log_pre_prepares (add_new_pre_prepare2log pp d l) lwm pps
      else log_pre_prepares l lwm pps
    end.

  (* here 0 is default number---as defined in the technical report, p.24 *)
  Definition low_water_mark (state : PBFTstate) : SeqNum :=
    scp_sn (chk_state_stable (cp_state state)).

  Definition log_pre_prepares_of_new_view
             (s   : PBFTstate)
             (P   : list (Pre_prepare * PBFTdigest)) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log_pre_prepares (log s) (low_water_mark s) P)
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (primary_state     s).

  Definition add_new_view_to_entry
             (e  : PBFTviewChangeEntry)
             (nv : NewView) : PBFTviewChangeEntry :=
    match e with
    | MkViewChangeEntry v ovc vcs None => MkViewChangeEntry v ovc vcs (Some nv)
    | MkViewChangeEntry v ovc vcs (Some _) => e
    end.

  Definition replace_new_view_in_entry (nv : NewView) (e : PBFTviewChangeEntry) : PBFTviewChangeEntry :=
    match e with
    | MkViewChangeEntry v vcop vcs _ => MkViewChangeEntry v vcop vcs (Some nv)
    end.

  Definition new_view2entry (nv : NewView) : PBFTviewChangeEntry :=
    MkViewChangeEntry (new_view2view nv) None [] (Some nv).

  Fixpoint log_new_view
             (state : PBFTviewChangeState)
             (nv    : NewView) : PBFTviewChangeState :=
    match state with
    | [] => [new_view2entry nv]
    | entry :: entries =>
      if ViewDeq (new_view2view nv) (vce_view entry) then

        add_new_view_to_entry entry nv :: entries

      else entry :: log_new_view entries nv
    end.

  Fixpoint log_new_view_and_entry
             (state : PBFTviewChangeState)
             (nv    : NewView)
             (e     : PBFTviewChangeEntry) : PBFTviewChangeState :=
    match state with
    | [] => [add_new_view_to_entry e nv]
    | entry :: entries =>
      if ViewDeq (new_view2view nv) (vce_view entry) then

        add_new_view_to_entry e nv :: entries

      else entry :: log_new_view_and_entry entries nv e
    end.

  Definition log_new_view_state
             (s  : PBFTstate)
             (nv : NewView) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (log_new_view (view_change_state s) nv)
      (primary_state     s).

  Definition log_new_view_and_entry_state
             (s  : PBFTstate)
             (nv : NewView)
             (e  : PBFTviewChangeEntry) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (log_new_view_and_entry (view_change_state s) nv e)
      (primary_state     s).

  (* we keep the ready list ordered *)
  Fixpoint add2ready (L : list SeqNum) (s : SeqNum) : list SeqNum :=
    match L with
    | [] => [s]
    | sn :: sns =>
      if SeqNumLt s sn then s :: sn :: sns else
        if SeqNumDeq s sn then L else
          sn :: add2ready sns s
    end.

  Definition add2ready_if_ge_next next ready s :=
    if SeqNumLe next s then add2ready ready s else ready.

  Definition add_to_ready (s : PBFTstate) (e : SeqNum) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (add2ready_if_ge_next (next_to_execute s) (ready s) e)
      (last_reply_state  s)
      (view_change_state s)
      (primary_state     s).

  Definition update_ready (s : PBFTstate) (L : list SeqNum) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      L
      (last_reply_state  s)
      (view_change_state s)
      (primary_state     s).

  Definition increment_next_to_execute (s : PBFTstate) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (cp_state          s)
      (sm_state          s)
      (next_seq (next_to_execute s))
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (primary_state     s).

  Definition change_next_to_execute (s : PBFTstate) (sn : SeqNum) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (cp_state          s)
      (sm_state          s)
      sn
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (primary_state     s).

  Definition change_sm_state (s : PBFTstate) (smstate : PBFTsm_state) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (cp_state          s)
      smstate
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (primary_state     s).

  Definition change_last_reply_state (s : PBFTstate) (lastr : LastReplyState) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      lastr
      (view_change_state s)
      (primary_state     s).

  Definition similar_entry (e1 e2 : PBFTlogEntry) : bool :=
    eq_request_data
      (log_entry_request_data e1)
      (log_entry_request_data e2).

  Definition similar_checkpoint_entry (e1 e2 : PBFTcheckpointEntry) : bool :=
    if SeqNumDeq (cp_sn e1) (cp_sn e2) then
      if PBFTdigestdeq (cp_d e1) (cp_d e2) then true
        else false
    else false.

  Fixpoint change_entry (log : PBFTlog) (e : PBFTlogEntry) : PBFTlog :=
    match log with
    | [] => []
    | entry :: entries =>
      if similar_entry entry e then e :: entries
      else entry :: change_entry entries e
    end.

  Definition decrement_requests_in_progress (s : PBFTstate) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (decrement_in_progress (primary_state s)).

  Definition increment_sequence_number (s : PBFTstate) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (increment_seq_num (primary_state s)).

  Definition change_sequence_number (s : PBFTstate) (sn : SeqNum) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (change_seq_num (primary_state s) sn).

  Definition change_log_entry (s : PBFTstate) (e : PBFTlogEntry) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (change_entry (log s) e)
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (primary_state     s).

  (* the option tells us whether we are ready to execute the request corresponding
     to the commit because we've now received 2F+1 commits for this request *)
  Fixpoint add_new_commit2log
           (log : PBFTlog)
           (c   : Commit) : option GeneratedInfo * PBFTlog :=
    match log with
    | [] =>

      (* We couldn't find an entry corresponding to the prepare so we create an
         incomplete one that's missing the information from the pre_prepare,
         which we're still waiting for *)
      let entry := MkNewLogEntryFromCommit c in
      let prepst := add_prepare_status_na in
      let commst := add_commit_status_added (commit2rep_toks c) in
      (Some (MkGeneratedInfo prepst commst entry), [entry])

    | entry :: entries =>
      if is_commit_for_entry entry c then
        (* the commit matches the entry *)

        if length (log_entry_commits entry) <? 2 * F + 1 then
          (* the 'committed' predicate is still false for this entry *)

          match add_commit2entry entry c with
          | Some new_entry => (* we managed to add the commit message to the entry *)

            let prepst := add_prepare_status_na in
            let commst := add_commit_status_added (commit2rep_toks c) in
            (Some (MkGeneratedInfo prepst commst new_entry), new_entry :: entries)

          | None => (* we didn't add the commit message to the entry *)
            (None, log)
          end

        else
          (* the 'committed' predicate is already true for this entry *)
          (None, log)

      else
        (* the commit doesn't match the entry *)
        let (b,l) := add_new_commit2log entries c in
        (b, entry :: l)
    end.

  Fixpoint add_new_checkpoint2cp_log
           (log : PBFTcheckpoint_log)
           (sm  : option PBFTsm_state)
           (lr  : option LastReplyState)
           (c   : Checkpoint) : (option PBFTcheckpointEntry) * PBFTcheckpoint_log :=
    match log with
    | [] =>
      let entry := MkNewCheckpointEntryFromCheckpoint c sm lr in
      (Some entry, [entry])

    | entry :: entries =>
      if is_checkpoint_for_entry entry c then
        (* the checkpoint matches the entry *)

        match add_checkpoint2entry entry c sm lr with
        | Some new_entry => (* we managed to add the checkpoint message to the entry *)
          (Some new_entry, new_entry :: entries)
        | None => (* we didn't add the checkpoint message to the entry *)
          (None, log)
        end

      else
        (* the checkpoint doesn't match the entry *)
        let (b, l) := add_new_checkpoint2cp_log entries sm lr c in
        (b, entry :: l)
    end.

  Definition add_new_checkpoint2cp_state
    (cp_state : PBFTcheckpointState)
    (sm       : option PBFTsm_state)
    (lr       : option LastReplyState)
    (c        : Checkpoint) : (option PBFTcheckpointEntry) * PBFTcheckpointState :=
    let (entryop, new_cp_log) := add_new_checkpoint2cp_log (chk_state_others cp_state) sm lr c in
    let new_cp_state :=
        Build_CheckpointState
          (chk_state_stable cp_state)
          (new_cp_log) in
    (entryop, new_cp_state).

  Definition checkpoint_entry2stable (e : PBFTcheckpointEntry) : option PBFTstableCheckpointEntry :=
    match e with
    | Build_PBFTcheckpointEntry n d l (Some sm) (Some lastr) =>
      Some (Build_PBFTstableCheckpointEntry n d l sm lastr)
    | _ => None
    end.

  (* we received  F + 1 checkpoint messages, i.e. checkpoint becomes stable
     i.e. we copy that entry in chk_state_stable  *)

  Definition update_stable_sp_log
             (state : PBFTcheckpointState)
             (entry : PBFTstableCheckpointEntry) : PBFTcheckpointState :=
    Build_CheckpointState
      entry
      (chk_state_others state).

  Fixpoint add_new_prepare2log
           (slf : Rep)
           (log : PBFTlog)
           (p   : Prepare)
           (Fc  : unit -> RepToks) : option GeneratedInfo * PBFTlog :=
    match log with
    | [] =>

      (* We couldn't find an entry corresponding to the prepare so we create an
         incomplete one that's missing the information from the pre_prepare,
         which we're still waiting for *)
      let entry := MkNewLogEntryFromPrepare p in
      let prepst := add_prepare_status_added (prepare2rep_toks p) in
      let commst := add_commit_status_na in
      (Some (MkGeneratedInfo prepst commst entry), [entry])

    | entry :: entries =>
      if is_prepare_for_entry entry p then
        (* the prepare corresponds to the pre-prepare of the entry *)

        if length (log_entry_prepares entry) <? 2 * F then
          (* the 'prepared' predicate is still false for this entry *)

          match add_prepare2entry slf entry p Fc with
          (* we managed to add the prepare message to the entry *)
          | Some gi =>  (Some gi, gi_entry gi :: entries)
          (* we didn't add the prepare message to the entry *)
          | None => (None, log)
          end

        else
          (* 'prepared' is already true for this entry *)
          (None, log)

      else
        (* the entry doesn't match the prepare *)
        let (b,L) := add_new_prepare2log slf entries p Fc in
        (b, entry :: L)
    end.

    Definition update_log_checkpoint_stable (s : PBFTstate) (entry : PBFTstableCheckpointEntry) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (update_stable_sp_log (cp_state s) entry)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (primary_state     s).

  Definition update_log (s : PBFTstate) (l : PBFTlog) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      l
      (cp_state          s)
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (primary_state     s).

  Definition update_checkpoint_state (s : PBFTstate) (cp_state : PBFTcheckpointState) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      cp_state
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (primary_state     s).


  (* the boolean is true if we logged the pre_prepare *)
  Fixpoint add_new_pre_prepare_and_prepare2log
           (i   : Rep)
           (log : PBFTlog)
           (pp  : Pre_prepare)
           (d   : PBFTdigest)
           (Fp  : unit -> RepToks)
           (Fc  : unit -> RepToks) : option GeneratedInfo * PBFTlog :=
    match log with
    | [] =>

      let prep   := Fp tt in
      let entry  := MkNewLogEntryWithPrepare pp d prep in
      let prepst := add_prepare_status_added prep in
      let commst := add_commit_status_na in
      (Some (MkGeneratedInfo prepst commst entry), [entry])

    | entry :: entries =>
      (* We should check whether the pre_prepare part of the entry corresponds
         our pre_prepare.
         (1) if it does and the info part is filled out, then this pre_prepare
             is not new and we should just discard it.  In that case we don't
             send out any message.
         (2) if it does and the info part is not filled out, then this pre_prepare
             is new and we created the entry because of some prepare or commit
             message that we've received.  In that case we fill out the info
             part and we send then send out prepare messages.
         (3) if the entry doesn't correspond to the pre_prepare then we check
             the next one.
       *)
      if similar_entry_and_pre_prepare entry pp d then
        match fill_out_pp_info_with_prepare i entry pp Fp Fc with
        | Some gi =>
          (* we filled out the entry with the information from the pre_prepare message *)
          (Some gi, gi_entry gi :: entries)
        | None =>
          (* the per_prepare information was already filled out *)
          (None, log)
        end
      else
        (* the entry doesn't match so we keep on searching *)
        let (b,entries') := add_new_pre_prepare_and_prepare2log i entries pp d Fp Fc in
        (b, entry :: entries')
    end.

  Definition valid_timestamp
             (state : PBFTprimaryState)
             (cop   : option Client)
             (ts    : Timestamp) : bool :=
    match cop with
    | Some client => client_info state client <? ts
    | None => true
    end.

  (* we check that the sequence number [s] is between the low water mark and the high water mark *)
  Definition check_between_water_marks (low : SeqNum) (s : SeqNum) : bool :=
    SeqNumLt low s && SeqNumLe s (low + PBFTwater_mark_range).

  Definition check_new_request
             (slf   : Rep)
             (low   : SeqNum)
             (state : PBFTprimaryState)
             (r     : Request)
    : PBFTprimaryState * (option (list Request)) :=

    if (PBFTmax_in_progress <=? in_progress state)
       || negb (check_between_water_marks low (next_seq (sequence_number state))) then

      (* then we buffer the request because we reached the max *)
      let buf := buffer_request state r in
      (buf, None)

    else

      let sender := request2sender r in
      let timestamp := request2timestamp r in

      (* if the timestamp is higher than the one we're storing,
         then we're going to process the request *)
      if valid_timestamp state sender timestamp then

        let all_requests := r :: request_buffer state in

        let state_ts := update_timestamp_op state sender timestamp in
        let state_inc := increment_in_progress state_ts in
        let state_res := reset_request_buffer state_inc in

        (state_res, Some all_requests)

      else

        (state, None).

  Definition broadcast2others (slf : Rep) F : DirectedMsg :=
    F (other_names slf).

  Definition broadcast2all F : DirectedMsgs := map F (map PBFTreplica reps).

  Definition bare_new_view2cert (b : Bare_NewView) : ViewChangeCert :=
    match b with
    | bare_new_view _ C _ _ => C
    end.

  Definition new_view2cert (nv : NewView) : ViewChangeCert :=
    match nv with
    | new_view b _ => bare_new_view2cert b
    end.

  Definition bare_new_view2oprep (b : Bare_NewView) : list Pre_prepare :=
    match b with
    | bare_new_view _ _ OP _ => OP
    end.

  Definition new_view2oprep (nv : NewView) : list Pre_prepare :=
    match nv with
    | new_view b _ => bare_new_view2oprep b
    end.

  Definition bare_new_view2nprep (b : Bare_NewView) : list Pre_prepare :=
    match b with
    | bare_new_view _ _ _ NP => NP
    end.

  Definition new_view2nprep (nv : NewView) : list Pre_prepare :=
    match nv with
    | new_view b _ => bare_new_view2nprep b
    end.

  Fixpoint view_change_cert2max_seq_vc (l : ViewChangeCert) : option (SeqNum * ViewChange) :=
    match l with
    | [] => None
    | vc :: vcs =>
      let n1 := view_change2seq vc in
      match view_change_cert2max_seq_vc vcs with
      | Some (n2, vc2) => if SeqNumLt n1 n2 then Some (n2,vc2) else Some (n1,vc)
      | None => Some (n1,vc)
      end
    end.

  Definition view_change_cert2max_seq (l : ViewChangeCert) : option SeqNum :=
    match view_change_cert2max_seq_vc l with
    | Some (sn, vc) => Some sn
    | None => None
    end.

  Fixpoint pre_prepares2max_seq (l : list Pre_prepare) : SeqNum :=
    match l with
    | [] => seq_num 0
    | p :: ps => max_seq_num (pre_prepare2seq p) (pre_prepares2max_seq ps)
    end.

  Fixpoint view_change_cert2prep (l : ViewChangeCert) : list PreparedInfo :=
    match l with
    | [] => []
    | vc :: vcs => view_change2prep vc ++ view_change_cert2prep vcs
    end.

  Definition prepared_info2request_data (p : PreparedInfo) : RequestData :=
    pre_prepare2request_data
      (prepared_info_pre_prepare p)
      (prepared_info_digest p).

  Definition requests2digest (rs : list Request) : PBFTdigest :=
    create_hash_messages (map PBFTrequest rs).

  Definition pre_prepare2digest (p : Pre_prepare) : PBFTdigest :=
    requests2digest (pre_prepare2requests p).

  Definition prepared_info_has_correct_digest (p : PreparedInfo) : bool :=
    if PBFTdigestdeq
         (prepared_info2digest p)
         (requests2digest (prepared_info2requests p))
    then true
    else false.

  (* This checks that
      (1) the pre_prepare is signed by the primary
      (2) that the prepare messages come from 2F different replicas
          that are not the primary, and the these prepare messages
          have the same data *)
  Definition info_is_prepared (p : PreparedInfo) : bool :=
    let preps    := prepared_info_prepares p in
    let L        := prepared_info2senders p in
    let ppview   := prepared_info2view p in
    let ppsender := prepared_info2pp_sender p in
    let rd       := prepared_info2request_data p in
    (2 * F <=? length L)
      && (if rep_deq ppsender (PBFTprimary ppview) then true else false)
      && prepared_info_has_correct_digest p
      && norepeatsb rep_deq L
      && forallb (fun r => if rep_deq r ppsender then false else true) L
      && forallb (fun prep => if RequestData_Deq (prepare2request_data prep) rd then true else false) preps.

  Definition same_digests (d1 d2 : PBFTdigest) : bool :=
    if PBFTdigestdeq d1 d2 then true else false.

  Definition last_prepared_info (p : PreparedInfo) (L : list PreparedInfo) : bool :=
    let s  := prepared_info2seq p in
    let v  := prepared_info2view p in
    let d  := prepared_info2digest p in
    forallb (fun nfo =>
               let s' := prepared_info2seq nfo in
               let v' := prepared_info2view nfo in
               let d' := prepared_info2digest nfo in
               (* if [nfo] is prepared then we check that:
                   (1) it's not prepared for the same view and sequence number
                       but for a different bunch of requests (identified by the digest)
                   (2) it's not prepared for the same sequence number but a higher view
                *)
               if info_is_prepared nfo then
               (* if the sequence numbers are different we're good,
                  otherwise we have to check things further *)
                 if SeqNumDeq s s' then
                   (* if the views are also the same then we have to make sure that
                      the prepared info is for the same bunch of requests (identified)
                      by the digest *)
                   if v' =? v then
                     same_digests d d'
                   else
                     (* the prepared info has to be for a smaller view *)
                     v' <? v
                 else true (* we're good *)
               else true (* we're good *))
            L.

  Definition valid_prepared_info (L : list PreparedInfo) (p : PreparedInfo) : bool :=
    (info_is_prepared p)
      && last_prepared_info p L.

  Definition bare_view_change2cert (v : Bare_ViewChange) : CheckpointCert :=
    match v with
    | bare_view_change v n s C P i => C
    end.

  Definition view_change2cert (v : ViewChange) : CheckpointCert :=
    match v with
    | view_change bv _ => bare_view_change2cert bv
    end.

  Definition same_seq_nums (s1 s2 : SeqNum) : bool :=
    if SeqNumDeq s1 s2 then true else false.

  Definition StableChkPt2digest (s : StableChkPt) : PBFTdigest :=
    create_hash_state_last_reply (si_state s) (si_lastr s).

  Definition correct_view_change_preps
             (n     : SeqNum)
             (v     : View)
             (preps : list PreparedInfo) : bool :=
    forallb (fun p => (valid_prepared_info preps p)
                        && ((prepared_info2view p) <=? v)
                        && (check_between_water_marks n (prepared_info2seq p)))
            preps.

  Definition correct_view_change_cert_one
             (n : SeqNum)
             (v : View)
             (S : StableChkPt)
             (c : Checkpoint) : bool :=
    (same_seq_nums n (checkpoint2seq c))
      && (checkpoint2view c <? v)
      && (same_digests (checkpoint2digest c) (StableChkPt2digest S)).

  Definition correct_view_change_cert
             (n : SeqNum)
             (v : View)
             (S : StableChkPt)
             (C : CheckpointCert) : bool :=
    (forallb (correct_view_change_cert_one n v S) C)
      && (norepeatsb rep_deq (map checkpoint2sender C))
      && (F + 1 <=? length C).

  Definition same_views (v1 v2 : View) : bool :=
    if ViewDeq v1 v2 then true else false.

  Definition bare_view_change2stable (v : Bare_ViewChange) : StableChkPt :=
    match v with
    | bare_view_change v n s C P i => s
    end.

  Definition view_change2stable (v : ViewChange) : StableChkPt :=
    match v with
    | view_change b _ => bare_view_change2stable b
    end.

  Definition correct_view_change (v  : View) (vc : ViewChange) : bool :=
    let vc_view := view_change2view vc in
    let vc_seq  := view_change2seq vc in
    let preps   := view_change2prep vc in
    let cert    := view_change2cert vc in
    let chk     := view_change2stable vc in
    (same_views v vc_view)
      && (correct_view_change_preps vc_seq vc_view preps)
      && (correct_view_change_cert vc_seq vc_view chk cert).

  Definition oexists_last_prepared
             (p  : Pre_prepare)
             (d  : PBFTdigest)
             (ps : list PreparedInfo) :=
    let s := pre_prepare2seq p in
    existsb
      (fun nfo =>
         let s' := prepared_info2seq nfo in
         let d' := prepared_info2digest nfo in
         if PBFTdigestdeq d d' then
           if SeqNumDeq s s' then
             valid_prepared_info ps nfo
           else false
         else false)
      ps.

  Definition correct_new_view_opre_prepare
             (nvview : View)
             (maxV   : SeqNum)
             (ps     : list PreparedInfo)
             (p      : Pre_prepare) : bool :=
    let sender := pre_prepare2sender p in
    let view   := pre_prepare2view p in
    let reqs   := pre_prepare2requests p in
    let s      := pre_prepare2seq p in

    if ViewDeq view nvview then

      if rep_deq sender (PBFTprimary view) then

        if SeqNumLt maxV s then

          let digest := requests2digest reqs in
          oexists_last_prepared p digest ps

        else (* the sequence number of the pre-prepare message is not larger
                than the largest one in the view-change certificate *)
          false

      else (* the sender of the pre-prepare message is not the primary of the view *)
        false

    else (* the view of the new-view message is not the same as the view
            of the pre-prepare message *)
      false.

  Definition correct_new_view_opre_prepare_op
             (nvview : View)
             (maxVop : option SeqNum)
             (ps     : list PreparedInfo) : Pre_prepare -> bool :=
    match maxVop with
    | Some maxV => correct_new_view_opre_prepare nvview maxV ps
    | None => fun p => false
    end.

  Definition nexists_last_prepared
             (p  : Pre_prepare)
             (ps : list PreparedInfo) :=
    let s := pre_prepare2seq p in
    existsb
      (fun nfo =>
         let s' := prepared_info2seq nfo in
         if SeqNumDeq s s' then
           valid_prepared_info ps nfo
         else false)
      ps.

  Definition is_null_req (reqs : list Request) : bool :=
    match reqs with
    | [req null_req _] => true
    | _ => false
    end.

  Definition correct_new_view_npre_prepare
             (nvview : View)
             (maxV   : SeqNum)
             (maxO   : SeqNum)
             (ps     : list PreparedInfo)
             (p      : Pre_prepare) : bool :=
    let sender := pre_prepare2sender p in
    let view   := pre_prepare2view p in
    let reqs   := pre_prepare2requests p in
    let s      := pre_prepare2seq p in

    if ViewDeq view nvview then

      if is_null_req reqs then

        if rep_deq sender (PBFTprimary view) then

          if SeqNumLt maxV s then

            if SeqNumLt s maxO then

              negb (nexists_last_prepared p ps)

            else (* the sequence number of the pre-prepare message
                    is not smaller than the largest one in the O set *)
              false

          else (* the sequence number of the pre-prepare message is not larger
                  than the largest one in the view-change certificate *)
            false

        else (* the sender of the pre-prepare message is not the primary of the view *)
          false

      else (* the list of requests is not the null-request *)
        false

    else (* the view of the new-view message is not the same as the view of the pre-prepare message *)
      false.

  Definition correct_new_view_npre_prepare_op
             (nvview : View)
             (maxVop : option SeqNum)
             (maxO   : SeqNum)
             (ps     : list PreparedInfo) : Pre_prepare -> bool :=
    match maxVop with
    | Some maxV => correct_new_view_npre_prepare nvview maxV maxO ps
    | None => fun p => false
    end.

  Definition max_seq_num_op (sn : SeqNum) (snop : option SeqNum) : SeqNum :=
    match snop with
    | Some sn' => max_seq_num sn sn'
    | None => sn
    end.

  Fixpoint PreparedInfos2max_seq
           (F : PreparedInfo -> bool)
           (l : list PreparedInfo) : option SeqNum :=
    match l with
    | [] => None
    | p :: ps =>
      let n   := prepared_info2seq p in
      let nop := PreparedInfos2max_seq F ps in
      if F p then
        Some (max_seq_num_op n nop)
      else nop
    end.

  Definition view_change2max_seq_preps
             (F  : PreparedInfo -> bool)
             (vc : ViewChange) : option SeqNum :=
    PreparedInfos2max_seq F (view_change2prep vc).

  Fixpoint view_change_cert2max_seq_preps_vc
           (F : PreparedInfo -> bool)
           (l : ViewChangeCert) : option (SeqNum * ViewChange) :=
    match l with
    | [] => None
    | vc :: vcs =>
      match view_change2max_seq_preps F vc, view_change_cert2max_seq_preps_vc F vcs with
      | Some n1, Some (n2, vc2) => if SeqNumLt n1 n2 then Some (n2,vc2) else Some (n1,vc)
      | Some n1, None => Some (n1,vc)
      | None, Some (n2, vc2) => Some (n2, vc2)
      | None, None => None
      end
    end.

  Definition view_change_cert2max_seq_preps
             (F :  PreparedInfo -> bool)
             (l : ViewChangeCert) : option SeqNum :=
    match view_change_cert2max_seq_preps_vc F l with
    | Some (sn, vc) => Some sn
    | None => None
    end.

  Definition from_min_to_max (mins maxs : SeqNum) : list SeqNum :=
    if maxs <? mins then []
    else map seq_num (seq (S mins) (maxs - mins)).

  Definition from_min_to_max_op (minop maxop : option SeqNum) : list SeqNum :=
    match minop, maxop with
    | Some mins, Some maxs => from_min_to_max mins maxs
    | _, _ => []
    end.

  Definition from_min_to_max_of_view_changes_cert
             (V : ViewChangeCert) : list SeqNum :=
    let minsn := view_change_cert2max_seq V in
    let preps := view_change_cert2prep V in
    let F     := valid_prepared_info preps in
    (* This is the max prepared *)
    let maxop := view_change_cert2max_seq_preps F V in
    from_min_to_max_op minsn maxop.

  Definition view_change_entry2view_changes (e : PBFTviewChangeEntry) : list ViewChange :=
    match e with
    | MkViewChangeEntry _ (Some vc) vcs _ => vc :: vcs
    | MkViewChangeEntry _ None vcs _ => vcs
    end.

  Definition from_min_to_max_of_view_changes
             (entry : PBFTviewChangeEntry) : list SeqNum :=
    let V := view_change_entry2view_changes entry in
    from_min_to_max_of_view_changes_cert V.

  Definition bare_pre_prepare2rd (bpp : Bare_Pre_prepare) : RequestData :=
    match bpp with
    | bare_pre_prepare v s r => request_data v s (requests2digest r)
    end.

  Definition pre_prepare2rd (pp : Pre_prepare) : RequestData :=
    match pp with
    | pre_prepare b _ => bare_pre_prepare2rd b
    end.

  Definition exists_prepared_info_in_pre_prepares
             (nfo : PreparedInfo)
             (OP  : list Pre_prepare) : bool :=
    existsb (fun pp =>
               (same_digests (prepared_info2digest nfo) (pre_prepare2digest pp))
                 && (same_seq_nums (prepared_info2seq nfo) (pre_prepare2seq pp))) OP.

  Definition sequence_number_is_accounted_for
             (P    : list PreparedInfo)
             (maxV : SeqNum)
             (OP   : list Pre_prepare)
             (nfo  : PreparedInfo) : bool :=
    if valid_prepared_info P nfo then
      let n := prepared_info2seq nfo in
      if maxV <? n then
        exists_prepared_info_in_pre_prepares nfo OP
      else true
    else true.

  Definition all_sequence_numbers_are_accounted_for
             (P    : list PreparedInfo)
             (maxV : SeqNum)
             (OP   : list Pre_prepare) : bool :=
    forallb (sequence_number_is_accounted_for P maxV OP) P.

  Definition all_sequence_numbers_are_accounted_for_op
             (P      : list PreparedInfo)
             (maxVop : option SeqNum)
             (OP     : list Pre_prepare) : bool :=
    match maxVop with
    | Some maxV => all_sequence_numbers_are_accounted_for P maxV OP
    | None => false
    end.

  Definition correct_new_view (nv : NewView) : bool :=
    let sender  := new_view2sender nv in
    let nvview  := new_view2view nv in
    let V       := new_view2cert nv in
    let OP      := new_view2oprep nv in
    let NP      := new_view2nprep nv in

    let maxVop  := view_change_cert2max_seq V in
    let maxO    := pre_prepares2max_seq OP in
    let vcPreps := view_change_cert2prep V in

    if rep_deq sender (PBFTprimary nvview) then
      (* the sender of the new-view message is the primary of the view *)

      if 2 * F + 1 <=? length V then

        if norepeatsb rep_deq (map (view_change2sender) V) then
          (* the view-change certificate comes from 2F+1 different replicas *)

          if forallb (correct_view_change nvview) V then

            if forallb (correct_new_view_opre_prepare_op nvview maxVop vcPreps) OP then

              if forallb (correct_new_view_npre_prepare_op nvview maxVop maxO vcPreps) NP then

                if norepeatsb SeqNumDeq (map pre_prepare2seq (OP ++ NP)) then

                  all_sequence_numbers_are_accounted_for_op vcPreps maxVop OP

                else (* the OP++NP set has repeats *)
                  false

              else (* one of the pre-prepare-messages is not correct  *)
                false

            else (* one of the pre-prepare messages is not correct *)
              false

          else (* one of the view-change messages is not correct *)
            false

        else (* the view-change certificate doesn't come from 2F+1 different replicas *)
          false

      else (* the certificate of the new-view message doesn't have enough view-change messages *)
        false

    else (* the sender of the new-view message is not the primary of the view *)
      false.

  Definition has_new_view1 (state : PBFTviewChangeState) (v : View) : bool :=
    existsb
      (fun entry =>
         if ViewDeq v (vce_view entry) then
           match vce_new_view entry with
           | Some nv => true (*correct_new_view nv*)
           | None => false
           end
         else false)
      state.

  Definition has_new_view (state : PBFTviewChangeState) (v : View) : bool :=
    if ViewDeq v initial_view then true
    else has_new_view1 state v.

  Definition next_sequence_number (state : PBFTstate) : SeqNum :=
    next_seq (sequence_number (primary_state state)).

  Definition PBFThandle_request (slf : Rep) : Update PBFTstate Request DirectedMsgs :=
    fun state r =>
      let keys  := local_keys state in
      let cview := current_view state in
      let low   := low_water_mark state in

      if has_new_view (view_change_state state) cview then

        if verify_request slf keys r then

          if is_primary cview slf then

            let (new_primary_state, reqsop) := check_new_request slf low (primary_state state) r in

            (* First, we update the primary state *)
            let upd_state := update_primary_state state new_primary_state in

            match reqsop with
            | Some reqs =>

              (* Next, we update the sequence number *)
              let upd_seq_num := increment_sequence_number upd_state in
              let next_seq_num := sequence_number (primary_state upd_seq_num) in

              (* Next, we log the request *)
              (* we hash the request *)
              let digest := requests2digest reqs in
              (* we create an authenticated pre-prepare message *)
              let pp     := mk_auth_pre_prepare cview next_seq_num reqs keys in
              (* we log the pre-prepare message *)
              let upd_log_pp := log_new_pre_prepare upd_seq_num pp digest in

              (* This is our new state *)
              let new_state := upd_log_pp in

              (* we broadcast the pre-prepare message to all replicas *)
              (Some new_state, [broadcast2others slf (send_pre_prepare pp)])

            | None => (Some upd_state, [(*send_debug slf "primary didn't accept the request"*)])
            end

          else
            let start := start_timer (request2bare r) cview in
            (Some state, [send_start_timer start slf (*send_debug slf "I'm not the primary"*)])

        else (* if we cannot verify the request, we just ignore it *)
          (Some state, [(*send_debug slf "couldn't verify the request"*)])

      else (* we don't have a new-view for the current view *)
        (Some state, []).

  Definition pre_prepare2auth (p : Pre_prepare) : Tokens :=
    match p with
    | pre_prepare b a => a
    end.

  Definition prepare2auth (p : Prepare) : Tokens :=
    match p with
    | prepare b a => a
    end.

  Definition commit2auth (c : Commit) : Tokens :=
    match c with
    | commit b a => a
    end.

  Definition pre_prepare2rep_toks (pp : Pre_prepare) (i : Rep) : RepToks :=
    MkRepToks i (pre_prepare2auth pp).

  Definition pre_prepare2rep_toks_of_prepare
             (n    : Rep)
             (keys : local_key_map)
             (pp   : Pre_prepare)
             (d    : PBFTdigest) : RepToks :=
    prepare2rep_toks (pre_prepare2prepare n keys pp d).

  Definition pre_prepare2rep_toks_of_commit
             (n    : Rep)
             (keys : local_key_map)
             (pp   : Pre_prepare)
             (d    : PBFTdigest) : RepToks :=
    commit2rep_toks (pre_prepare2commit n keys pp d).

  Definition entry2seq (e : PBFTlogEntry) : SeqNum :=
    match e with
    | Build_PBFTlogEntry bp _ _ _ => request_data2seq bp
    end.

  Fixpoint find_entry (log : PBFTlog) (s : SeqNum) : option PBFTlogEntry :=
    match log with
    | [] => None
    | entry :: entries =>
      if SeqNumDeq s (entry2seq entry) then
        Some entry
      else find_entry entries s
    end.

  Definition reply2request
             (slf   : Rep)
             (view  : View)
             (keys  : local_key_map)
             (req   : Request)
             (state : PBFTsm_state)
             (lastr : LastReplyState)
    : (option Reply) * PBFTsm_state * LastReplyState :=
    match request2info req with
    | Some (opr, ts, c) =>

      match find_last_reply_entry_corresponding_to_client lastr c with
      | Some entry =>

        if (lre_timestamp entry) <=? ts then

          if (lre_timestamp entry) <? ts then

            let (result, new_state) := PBFTsm_update c state opr in
            (* we create a reply message *)
            let rep := mk_auth_reply view ts c slf result keys in

            let new_lastr := update_last_reply_timestamp_and_result lastr c ts result in

            (Some rep, new_state, new_lastr)

          else (* then [ts] is the last recorded timestamp *)

            match lre_reply entry with
            | Some res =>

              (* we create a reply message *)
              let rep := mk_auth_reply view ts c slf res keys in

              (Some rep, state, lastr)

            | None => (None, state, lastr)
            end

        else (* then [ts] is strictly smaller than the last recorded timestamp *)
          (None, state, lastr)

      (* if [None] then no entry for the client, so we don't do anything *)
      | None => (None, state, lastr)
      end

    (* None is for the null request *)
    | None => (None, state, lastr)
    end.

  Fixpoint reply2requests
           (slf   : Rep)
           (view  : View)
           (keys  : local_key_map)
           (reqs  : list Request)
           (state : PBFTsm_state)
           (lastr : LastReplyState)
    : list (option Reply) * PBFTsm_state * LastReplyState :=
    match reqs with
    | [] => ([], state, lastr)
    | r :: rs =>
      match reply2request slf view keys r state lastr with
      | (rep, st1, lr1) =>
        match reply2requests slf view keys rs st1 lr1 with
        | (reps, st2, lr2) => (rep :: reps, st2, lr2)
        end
      end
    end.

  Fixpoint list_option2list {T} (l : list (option T)) : list T :=
    match l with
    | [] => []
    | Some t :: l => t :: list_option2list l
    | None :: l => list_option2list l
    end.

  (* in case sn is divisible by PBFTwater_mark_range garbage collection starts *)
  Definition time_for_checkpoint (sn : SeqNum) : bool :=
    if Nat.eq_dec ((seqnum2nat sn) mod PBFTcheckpoint_period) 0
    then true
    else false.

  Fixpoint clear_log_checkpoint (l : PBFTlog) (sn : SeqNum) : PBFTlog :=
    match l with
    | [] => []
    | entry :: log' =>
      let sn' := entry2seq entry in

        (* we already executed request with SeqNum sn', so we can delete it from the log *)
      if SeqNumLe sn' sn
      then clear_log_checkpoint log' sn
      else entry :: clear_log_checkpoint log' sn

    end.

  Fixpoint trim_checkpoint_log
           (s : SeqNum)
           (l : PBFTcheckpoint_log) : PBFTcheckpoint_log :=
    match l with
    | [] => []
    | entry :: entries =>
      if cp_sn entry <? s then trim_checkpoint_log s entries
      else entry :: trim_checkpoint_log s entries
    end.

  Definition trim_checkpoint_state
             (sn : SeqNum)
             (st : PBFTcheckpointState) : PBFTcheckpointState :=
    match st with
    | Build_CheckpointState stable others =>
      Build_CheckpointState stable (trim_checkpoint_log sn others)
    end.

  Definition trim_checkpoint (s : PBFTstate) (sn : SeqNum) : PBFTstate :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (log               s)
      (trim_checkpoint_state sn (cp_state s))
      (sm_state          s)
      (next_to_execute   s)
      (ready             s)
      (last_reply_state  s)
      (view_change_state s)
      (primary_state     s).

  Definition check_stable
             (slf   : Rep)
             (s     : PBFTstate)
             (entry : PBFTcheckpointEntry) : option PBFTstate :=
    if is_stable_checkpoint_entry entry then

      match checkpoint_entry2stable entry with
      | Some sentry =>

        (* we save the stable entry in checkpoint_state  *)
        let new_state1 := update_log_checkpoint_stable s sentry in

        (* we delete all messages form the log with sequence number lower or equal to sn *)
        let new_log    := clear_log_checkpoint (log new_state1) (cp_sn entry) in
        let new_state2 := update_log new_state1 new_log in

        (* we delete all messages form the cp_log with sequence number lower that sn *)
        let new_state3 := trim_checkpoint new_state2 (cp_sn entry) in

        Some new_state3

      | None => None
      end

    else None.

  Definition on_check_stable
             (i : Rep)
             (s : PBFTstate)
             (e : PBFTcheckpointEntry) : PBFTstate :=
    match check_stable i s e with
    | Some s' => s'
    | None => s
    end.

  Definition check_broadcast_checkpoint
             (slf    : Rep)
             (sn     : SeqNum)
             (vn     : View)
             (keys   : local_key_map)
             (s      : PBFTstate) : PBFTstate * DirectedMsgs :=
    if time_for_checkpoint sn then

      (* Next, we create, log and broadcast the checkpoint message*)
      (* we hash the state *)
      let digest := create_hash_state_last_reply (sm_state s) (last_reply_state s) in
      (* we create an unsingned checkpoint message *)
      let cp     := mk_auth_checkpoint vn sn digest slf keys in

      let lr     := last_reply_state s in
      (* we log the checkpoint message *)
      let (entryop, new_cp_state) := add_new_checkpoint2cp_state (cp_state s) (Some (sm_state s)) (Some lr) cp in
      let new_state := update_checkpoint_state s new_cp_state in

      (new_state, [broadcast2others slf (send_checkpoint cp), send_check_stable slf])

    else (s, []).


  (* We try to execute the requests that are ready

     We return:
       (1) the list of replies computes while executing the requests
       (2) the list of remaining requests that are ready
       (3) the new state
   *)
  Definition execute_requests
           (slf   : Rep)
           (view  : View)
           (keys  : local_key_map)
           (state : PBFTstate)
           (ready : list SeqNum) : DirectedMsgs * list SeqNum * PBFTstate :=
    match ready with
    | [] => ([], [], state)
    | sn :: sns =>
      if SeqNumDeq sn (next_to_execute state) then

        (* We can now execute [sn] (=[next]) *)

        (* we increment the sequence number of the next request to execute *)
        let new_state1 := increment_next_to_execute state in

        match find_entry (log state) sn with
        | Some entry =>

          (* We checked that before sending the check-ready message but it's easier to
             check it locally (event-wise) *)
          if is_committed_entry entry then

            (* we compute the result *)
            let reqs := log_entry2requests entry in

            match reply2requests slf view keys reqs (sm_state new_state1) (last_reply_state new_state1) with
            | (reps1, new_sm_state, new_lastr) =>

              let new_state2 := change_sm_state new_state1 new_sm_state in
              let new_state3 := change_last_reply_state new_state2 new_lastr in

              (* we add the replies to the entry*)
              let new_entry := add_replies2entry entry reps1 in
              (* we change the old entry for the new one to store the replies *)
              let new_state4 := change_log_entry new_state3 new_entry in

              (* if sn is divisible by PBFTcheckpoint_period, we start sending checkpoint messages *)
              let (new_state5, cp1) := check_broadcast_checkpoint slf sn view keys new_state4 in

              (* we send a check-ready message to keep on checking whether there are
                 anymore ready messages to send *)
              let cr := send_check_ready slf in

              let replies := map send_reply (list_option2list reps1) in

              (replies ++ cr :: cp1, sns, new_state5)

            end

          else ([], ready, state)

        | None =>
          ([], ready, state)
        end

      else ([], ready, state)
    end.

  Definition find_and_execute_requests
             (slf   : Rep)
             (view  : View)
             (keys  : local_key_map)
             (state : PBFTstate) : DirectedMsgs * PBFTstate :=
    match execute_requests slf view keys state (ready state) with
    | (outs, still_ready,new_state1) =>
      let new_state2 := update_ready new_state1 still_ready in
      (outs, new_state2)
    end.

  Definition decrement_requests_in_progress_if_primary
             (slf   : Rep)
             (view  : View)
             (state : PBFTstate) : PBFTstate :=
    if is_primary view slf then
      decrement_requests_in_progress state
    else state.

  Definition nat2string1 (n : nat) : String.string :=
    String.String (Ascii.ascii_of_N (N.of_nat n)) String.EmptyString.

  Definition nat2string (n : nat) : String.string :=
    match n with
    | 0 => "0"
    | S 0 => "1"
    | S (S 0) => "2"
    | S (S (S 0)) => "3"
    | S (S (S (S 0))) => "4"
    | S (S (S (S (S 0)))) => "5"
    | S (S (S (S (S (S 0))))) => "6"
    | S (S (S (S (S (S (S 0)))))) => "7"
    | S (S (S (S (S (S (S (S 0))))))) => "8"
    | S (S (S (S (S (S (S (S (S 0)))))))) => "9"
    | _ => "-"
    end.

  Definition sn2string (s : SeqNum) : String.string :=
    match s with
    | seq_num n => String.append "|" (String.append (nat2string n) "|")
    end.

  Fixpoint ready2string (l : list SeqNum) : String.string :=
    match l with
    | [] => ""
    | n :: ns => String.append (sn2string n) (ready2string ns)
    end.

  Definition prepare2rep_toks_of_commit
             (slf  : Rep)
             (keys : local_key_map)
             (p    : Prepare) : RepToks :=
    commit2rep_toks (prepare2commit slf keys p).

  Definition check_broadcast_prepare
             (slf     : Rep)
             (rd      : RequestData)
             (entryop : option GeneratedInfo) : DirectedMsgs :=
    match entryop with
    | Some (MkGeneratedInfo prepst commst entry) =>

      if is_pre_prepared_entry entry then

        match prepst with

        | add_prepare_status_already_in => []

        | add_prepare_status_added prep =>

          [broadcast2others
             slf
             (send_prepare (request_data_and_rep_toks2prepare rd prep))]

        | add_prepare_status_na => []

        end

      else []

    | None => []
    end.

  Definition check_broadcast_commit
             (slf     : Rep)
             (rd      : RequestData)
             (entryop : option GeneratedInfo) : DirectedMsgs :=
    match entryop with
    | Some (MkGeneratedInfo prepst commst entry) =>

      if is_prepared_entry entry then

        match commst with

        | add_commit_status_already_in => []

        | add_commit_status_added comm =>

          [broadcast2others
             slf
             (send_commit (request_data_and_rep_toks2commit rd comm))]

        | add_commit_status_not_prepared => []

        | add_commit_status_na => []

        end

      else []

    | None => []
    end.

  Definition check_send_replies
             (slf     : Rep)
             (view    : View)
             (keys    : local_key_map)
             (entryop : option GeneratedInfo)
             (state   : PBFTstate)
             (sn      : SeqNum) : DirectedMsgs * PBFTstate :=
    match entryop with
    | Some (MkGeneratedInfo prepop commop entry) =>

      if is_committed_entry entry then

        (* then the request corresponding to [sn] is committed and ready to be executed *)

        (* we add the sequence number [sn] to the list of sequence numbers ready to be executed *)
        let ready_state := add_to_ready state sn in

        (* we send a check-ready message to start checking whether there are
           some messages are ready to be sent *)
        let cr := send_check_ready slf in

        ([cr], ready_state)

      else ([], state)

    | None => ([], state)
    end.

  Definition own_prepare_is_already_in_entry_with_different_digest
             (i  : Rep)
             (s  : SeqNum)
             (v  : View)
             (d  : PBFTdigest)
             (e  : PBFTlogEntry) : option Prepare :=
    let rd := log_entry_request_data e in

    if SeqNumDeq (request_data2seq rd) s then

      if ViewDeq (request_data2view rd) v then

        if PBFTdigestdeq (request_data2digest rd) d
        then (* the digests are the same *)

          None

        else

          let preps := log_entry_prepares e in
          match find_rep_toks_in_list i preps with
          | Some rt => Some (request_data_and_rep_toks2prepare rd rt)
          | None => None
          end

      else None
    else None.


  Fixpoint own_prepare_is_already_logged_with_different_digest
           (i  : Rep)
           (s  : SeqNum)
           (v  : View)
           (d  : PBFTdigest)
           (L  : PBFTlog) : option Prepare :=
    match L with
    | [] => None
    | entry :: entries =>
      match own_prepare_is_already_in_entry_with_different_digest i s v d entry with
      | Some prep => Some prep
      | None => own_prepare_is_already_logged_with_different_digest i s v d entries
      end
    end.

  Definition PBFThandle_pre_prepare (slf : Rep) : Update PBFTstate Pre_prepare DirectedMsgs :=
    fun state pp =>
      let keys  := local_keys state in
      let cview := current_view state in
      let lwm   := low_water_mark state in

      let sender := pre_prepare2sender pp in
      let ppsn   := pre_prepare2seq pp in
      let ppview := pre_prepare2view pp in

      if has_new_view (view_change_state state) cview then

        if rep_deq slf sender then
          (* we don't do anything because the message comes from us *)

          (Some state, [])

        else

          if is_primary cview sender then
            (* the pre-prepare message has to come from the primary *)

            if is_primary cview slf then (* the primary ignores pre_prepare messages *)
              (Some state, [])

            else

              (* we check whether the pre-prepare message is signed properly *)
              if verify_pre_prepare slf keys pp then

                (* we check that the view is correct *)
                if ViewDeq ppview cview then

                  (* we check that the sequence number is between the low water mark and the high water mark *)
                  if check_between_water_marks lwm ppsn then

                    let digest := pre_prepare2digest pp in

                    if own_prepare_is_already_logged_with_different_digest slf ppsn ppview digest (log state) then

                      (Some state, [])

                    else

                      (* we create an authenticated prepare message from the pre_prepare message *)
                      let Fp := fun (u : unit) => pre_prepare2rep_toks_of_prepare slf keys pp digest in
                      let Fc := fun (u : unit) => pre_prepare2rep_toks_of_commit  slf keys pp digest in
                      let (entryop, new_log) := add_new_pre_prepare_and_prepare2log slf (log state) pp digest Fp Fc in
                      let new_state := update_log state new_log in

                      let rd := pre_prepare2request_data pp digest in
                      let preps := check_broadcast_prepare slf rd entryop in
                      (* Getting this pre_prepare message might make the 'prepared' predicate
                         turn true, in which case we start sending commit messages *)
                      let comms := check_broadcast_commit slf rd entryop in
                      (* Getting this pre_prepare message might make the 'committed' predicate
                         turn true, in which case we start sending replies *)
                      let (reps, new_state') := check_send_replies slf cview keys entryop new_state ppsn in

                      (* we broadcast the prepare message to all replicas *)
                      (Some new_state', preps ++ comms ++ reps)

                  else (* if the sequence number is not between the water marks, we ignore the message *)
                    (Some state, [])

                else (* if the view is not the current view, we ignore the message *)
                  (Some state, [])

              else (* if we cannot verify the pre-prepare, we just ignore it *)
                (Some state, [])

          else (* the sender is not the primary *)
            (Some state, [])

      else (* we don't have a new-view for the current view *)
        (Some state, []).

  Definition PBFThandle_prepare (slf : Rep) : Update PBFTstate Prepare DirectedMsgs :=
    fun state p =>
      let keys  := local_keys state in
      let cview := current_view state in
      let lwm   := low_water_mark state in

      let sender := prepare2sender p in
      let psn    := prepare2seq p in

      if rep_deq slf sender then
          (* we don't do anything because the message comes from us *)

          (Some state, [])

        else

          if is_primary cview sender then
            (* the prepare message is not supposed to come from the primary *)

            (Some state, [])

          else

            (* we check whether the prepare message is signed properly *)
            if verify_prepare slf keys p then

              (* we check that the view is correct *)
              if ViewDeq (prepare2view p) cview then

                (* we check that the sequence number is between the low water mark and the high water mark *)
                if check_between_water_marks lwm psn then

                  (* we log the prepare message *)
                  let Fc := fun (u : unit) => prepare2rep_toks_of_commit slf keys p in
                  let (entryop, new_log) := add_new_prepare2log slf (log state) p Fc in
                  let new_state := update_log state new_log in

                  let rd := prepare2request_data p in
                  let comms := check_broadcast_commit slf rd entryop in
                  (* Getting this prepare message might make the 'committed' predicate
                     turn true, in which case we start sending replies *)
                  let (reps, new_state') := check_send_replies slf cview keys entryop new_state psn in

                  (Some new_state', comms ++ reps)

                else (* if the sequence number is not between the water marks, we ignore the message *)
                  (Some state, [])

              else (* if the view is not the current view, we ignore the message *)
                (Some state, [])

            else (* if we cannot verify the prepare, we just ignore it *)
              (Some state, []).

  Definition PBFThandle_commit (slf : Rep) : Update PBFTstate Commit DirectedMsgs :=
    fun state c =>
      let keys := local_keys state in
      let view := current_view state in
      let lwm  := low_water_mark state in

      let sender := commit2sender c in
      let csn    := commit2seq c in

      if rep_deq slf sender then
          (* we don't do anything because the message comes from us *)

          (Some state, [])

        else

          (* we check whether the commit message is signed properly *)
          if verify_commit slf keys c then

            (* we check that the view is correct *)
            if ViewDeq (commit2view c) view then

              (* we check that the sequence number is between the low water mark and the high water mark *)
              if check_between_water_marks lwm csn then

                (* we log the commit message *)
                let (entryop, new_log) := add_new_commit2log (log state) c in
                let new_state := update_log state new_log in

                (* Getting this commit message might make the 'committed' predicate
                   turn true, in which case we start sending replies *)
                let (reps, new_state') := check_send_replies slf view keys entryop new_state csn in

                (Some new_state', reps)

              else (* the sequence number is not between the water marks *)
                (Some state, [])

            else (* the view doesn't match *)
              (Some state, [])

          else (* if we cannot verify the pre-prepare, we just ignore it *)
            (Some state, []).


  Fixpoint str_concat (l : list String.string) : String.string :=
    match l with
    | [] => ""
    | s :: ss => String.append s (str_concat ss)
    end.

  (* for now we need only sequence number *)
  Definition print_entry (entry : PBFTlogEntry) : String.string :=
    String.append (sn2string (request_data2seq (log_entry_request_data  entry))) "; ".

  Fixpoint print_log (l : PBFTlog) :String.string :=
    match l with
    | [] => ""
    | entry :: entries =>
      String.append (print_entry entry) (print_log entries)
    end.


  (* printing debugging info regarding checkpointing *)
  Definition debug_checkpoint (slf : Rep) (old_state new_state : PBFTstate) : DirectedMsgs :=
    let str := str_concat
                 ["old seq num of stable chkpoint:",
                  sn2string (low_water_mark old_state),
                  ",",
                  "new seq num of stable chkpoint:",
                  sn2string (low_water_mark new_state),
                  ",",
                  "old log size:",
                  nat2string (length (log old_state)),
                  ",",
                  "new log size:",
                  nat2string (length (log new_state)),
                  ",",
                  "print new log:",
                  print_log (log new_state)
                 ] in
    [send_debug slf str].

  Definition PBFThandle_checkpoint (slf : Rep) : Update PBFTstate Checkpoint DirectedMsgs :=
    fun state c =>
      let keys := local_keys state in
      let lwm  := low_water_mark state in
      let view := current_view state in

      let sender := checkpoint2sender c in
      let csn    := checkpoint2seq c in
      let cvn    := checkpoint2view c in

      if rep_deq slf sender then
        (* we don't do anything because the message comes from us *)

        (Some state, [])

      else

        (* we check whether the checkpoint message is signed properly *)
        if verify_checkpoint slf keys c then

          if check_between_water_marks lwm csn then
            (* then the sequence number of the checkpoint messages is between the water marks *)

            if ViewLe cvn view then
              (* we have to check if the current view number is >= than the one send in checkpoint *)

              (* we log the checkpoint message *)
              let (entryop, new_cp_state) := add_new_checkpoint2cp_state (cp_state state) None None c in
              let new_state := update_checkpoint_state state new_cp_state in

              (Some new_state, [send_check_stable slf] (*debug_checkpoint slf state new_state'*))

            else (* view number in the checkpoint is greater than the current view *)
              (Some state, [])

          else (* the sequence number of the checkpoint message is not between the water marks *)
            (Some state, [])

        else (* if we cannot verify the checkpoint, we just ignore it *)
          (Some state,[]).

  Definition checkpoint_certificate_of_last_stable_checkpoint (state : PBFTstate) : list Checkpoint :=
    scp_checkpoint (chk_state_stable (cp_state state)).

  Definition stable_chkpt_of_last_stable_checkpoint (state : PBFTstate) : StableChkPt :=
    let entry := chk_state_stable (cp_state state) in
    MkStableChkPt (scp_sm_state entry) (scp_last_reply_state entry).

  Definition request_data2pre_prepare
             (rd   : RequestData)
             (reqs : list Request)
             (a    : Tokens) : Pre_prepare :=
    match rd with
    | request_data v s d => pre_prepare (bare_pre_prepare v s reqs) a
    end.

  Definition entry2prepared_info (entry : PBFTlogEntry) : option PreparedInfo :=
    match entry with
    | Build_PBFTlogEntry rd (pp_info_pre_prep a reqs) preps _ =>
      if 2 * F <=? length preps then
        Some (MkPreparedInfo
                (request_data2pre_prepare rd (map fst reqs) a)
                (request_data2digest rd)
                (map (request_data_and_rep_toks2prepare rd) preps))
      else None
    | _ => None
    end.

  Fixpoint gather_prepared_messages (L : PBFTlog) (sn : SeqNum) : list PreparedInfo :=
    match L with
    | [] => []
    | entry :: entries =>
      if sn <? entry2seq entry then

        match entry2prepared_info entry with
        | Some nfo => nfo :: gather_prepared_messages entries sn
        | None => gather_prepared_messages entries sn
        end

      else
        gather_prepared_messages entries sn
    end.

  Fixpoint find_pre_prepare_certificate_in_prepared_infos
           (F :  PreparedInfo -> bool)
           (sn : SeqNum)
           (preps : list PreparedInfo) : option PreparedInfo :=
    match preps with
    | [] => None
    | ppinfo :: preps =>
      if SeqNumDeq sn (prepared_info2seq ppinfo) then
        if F ppinfo then Some ppinfo
        else find_pre_prepare_certificate_in_prepared_infos F sn preps
      else find_pre_prepare_certificate_in_prepared_infos F sn preps
    end.

  (* Boolean is true if the pre-prepare message is not for the null-request *)
  Definition create_new_prepare_message
             (sn    : SeqNum)
             (nview : View)
             (keys  : local_key_map)
             (P     : list PreparedInfo) : bool * (Pre_prepare * PBFTdigest) :=
    let F := valid_prepared_info P in
    match find_pre_prepare_certificate_in_prepared_infos F sn P with
    | Some prepared_info =>

      let reqs   := prepared_info2requests prepared_info in
      let digest := prepared_info2digest prepared_info in
      let pp     := mk_auth_pre_prepare nview sn reqs keys in
      (true, (pp, digest))

    | None =>

      let nreq   := mk_auth_null_req keys in
      let digest := requests2digest [nreq] in
      let pp     := mk_auth_pre_prepare nview sn [nreq] keys in
      (false, (pp, digest))

    end.

  Fixpoint create_new_prepare_messages
           (L     : list SeqNum)
           (nview : View)
           (keys  : local_key_map)
           (P     : list PreparedInfo)
    : list (Pre_prepare * PBFTdigest) * list (Pre_prepare * PBFTdigest) :=
    match L with
    | [] => ([], [])
    | s :: ss =>
      let (b, p) := create_new_prepare_message s nview keys P in
      let (OP, NP) := create_new_prepare_messages ss nview keys P in
      if b then (p :: OP, NP) else (OP, p :: NP)
    end.

  Definition valid_view (vc_view cur_view : View) (*(changing : bool)*) : bool :=
    cur_view <=? vc_view.

  Definition gather_valid_prepared_messages (L : PBFTlog) (sn : SeqNum) : list PreparedInfo :=
    let ps:= gather_prepared_messages L sn in
    filter (valid_prepared_info ps) ps.

  Definition mk_current_view_change (i : Rep) (v : View) (state : PBFTstate) : ViewChange :=
    let keys  := local_keys state in
    let sn    := low_water_mark state in
    let C     := checkpoint_certificate_of_last_stable_checkpoint state in
    let P     := gather_valid_prepared_messages (log state) sn in
    let stchk := stable_chkpt_of_last_stable_checkpoint state in
    mk_auth_view_change v sn stchk C P i keys.

  Definition refresh_view_change (vc : ViewChange) (state : PBFTstate) : ViewChange :=
    let i := view_change2sender vc in
    let v := view_change2view vc in
    mk_current_view_change i v state.

  Definition replace_own_view_change_in_entry (vc : ViewChange) (e : PBFTviewChangeEntry) : PBFTviewChangeEntry :=
    match e with
    | MkViewChangeEntry v _ vcs nv => MkViewChangeEntry v (Some vc) vcs nv
    end.

  Definition view_changed_entry
             (state : PBFTstate)
             (entry : PBFTviewChangeEntry) : option (ViewChange * PBFTviewChangeEntry) :=
    let current_view := current_view state in
    let entry_view := vce_view entry in

    if ViewLe current_view entry_view then

      if ViewLt initial_view entry_view then
        (* someone started to change views for the current view *)

        match vce_view_change entry with
        | Some vc =>
          (* we started changing to this view *)

          if is_some (vce_new_view entry) then
            (* we have already received a new-view message for this view-change,
             which means that we are not changing to this view anymore *)

            None

          else (* we have not yet received a new-view message for this view,
                  therefore we are still changing view *)

            (* we check whether we have enough view-change messages from other replicas *)
            if 2 * F <=? length (vce_view_changes entry) then

              if norepeatsb rep_deq (map view_change2sender (view_change_entry2view_changes entry)) then

                let vc'    := refresh_view_change vc state in
                let entry' := replace_own_view_change_in_entry vc' entry in

                if forallb (correct_view_change entry_view) (view_change_entry2view_changes entry') then

                  Some (vc', entry')

                else (* the view-change messages are not all correct *)
                  None

              else (* the messages are not from different replicas *)
                None

            else (* We don't have enough view-change messages *)
              None

        | None =>
          (* the view of the entry is our current view, but no timer has expired yet,
             therefore we are not yet changing view *)
          None
        end

      else (* the view of the entry is 0 *)
        None

    else (* the view of the entry is strictly less than our current view *)
      None.

  (* What is called "mergeP" in the thesis is called "view_change_cert2prep" here *)
  Definition mergeP (V : ViewChangeCert) : list PreparedInfo :=
    view_change_cert2prep V.

  (* nview is the view of the message that triggered this check *)
  Definition check_broadcast_new_view
             (slf   : Rep)
             (state : PBFTstate )
             (entry : PBFTviewChangeEntry)
    : option (NewView
              * PBFTviewChangeEntry
              * list (Pre_prepare * PBFTdigest)
              * list (Pre_prepare * PBFTdigest)) :=
    let view := vce_view entry in
    let keys := local_keys state in

    if is_primary view slf then
      (* We're the primary of the new view *)

      (* we check if we're changing view, which we do when a trigger expires
         we then have logged our own view-change message, but we have not logged
         yet a new-view message *)
        match view_changed_entry state entry with

        | Some (vc', entry') =>

          (* we now have enough view-change messages to generate a new-view message *)

          let L        := from_min_to_max_of_view_changes entry' in
          let V        := view_change_entry2view_changes entry' in
          let P        := view_change_cert2prep V in
          let nview    := view_change2view vc' in
          let (OP, NP) := create_new_prepare_messages L nview keys P in

          let nv := mk_auth_new_view nview V (map fst OP) (map fst NP) keys in

        Some (nv, entry', OP, NP)

        | None =>
          (* we're not currently changing views *)
          None
        end

    else (* we're not the primary of the view we're changing to *)
      None.

  Fixpoint select {A} (n : nat) (l : list A) : option A :=
    match l with
    | [] => None
    | x :: xs =>
      match n with
      | 0 => Some x
      | S m => select m xs
      end
    end.

  Definition CheckBCastNewView2entry
             (c : CheckBCastNewView)
             (s : PBFTviewChangeState) : option PBFTviewChangeEntry :=
    match c with
    | check_bcast_new_view i => select i s
    end.

  Fixpoint max_O (l : list (Pre_prepare * PBFTdigest)) : SeqNum :=
    match l with
    | [] => seq_num 0
    | (p,d) :: ps => max_seq_num (pre_prepare2seq p) (max_O ps)
    end.

  (* If the checkpoint certificate is correct all the checkpoint messages in there
     have the same sequence number and digest.  We can therefore extract the info
     from any of the checkpoint messages (if any). *)
  Definition extract_seq_and_digest_from_checkpoint_certificate
             (C : CheckpointCert) : option (SeqNum * PBFTdigest) :=
    match C with
    | [] => None
    | c :: _ => Some (checkpoint2seq c, checkpoint2digest c)
    end.

  Fixpoint contains_our_own_checkpoint_message
           (slf : Rep)
           (C   : CheckpointCert) : bool :=
    match C with
    | [] => false
    | c :: cs =>
      if rep_deq (checkpoint2sender c) slf then true
      else contains_our_own_checkpoint_message slf cs
    end.

  Definition log_checkpoint_cert_from_new_view
             (slf   : Rep)
             (state : PBFTstate)
             (v     : View)
             (maxV  : SeqNum)
             (C     : CheckpointCert)
             (s     : StableChkPt)
    (* the [option Checkpoint] is to indicate when we have to send a new checkpoint message *)
    : PBFTstate * option Checkpoint :=
    match extract_seq_and_digest_from_checkpoint_certificate C with
    | Some (sn, digest) =>

      let keys  := local_keys state in

      let smst  := si_state s in
      let lastr := si_lastr s in

      if contains_our_own_checkpoint_message slf C then

        let entry := Build_PBFTstableCheckpointEntry sn digest C smst lastr in
        (update_log_checkpoint_stable state entry, None)

      else (* we have to add our own checkpoint message to the certificate *)

        let digest := create_hash_state_last_reply smst lastr in
        (* we create an authenticated checkpoint message *)
        let cp     := mk_auth_checkpoint v maxV digest slf keys in

        let entry := Build_PBFTstableCheckpointEntry sn digest (cp :: C) smst lastr in
        (update_log_checkpoint_stable state entry, Some cp)

    | None => (state, None)
    end.

  Definition update_checkpoint_from_new_view
             (state : PBFTstate)
             (s     : StableChkPt)
             (maxV  : SeqNum) : PBFTstate :=
    if next_to_execute state <=? maxV then

      let new_state1 := change_last_reply_state state (si_lastr s) in
      let new_state2 := change_sm_state new_state1 (si_state s) in
      let new_state3 := change_next_to_execute new_state2 (next_seq (* NEW *) maxV) in

      new_state3

    else state.

  Definition broadcast_checkpoint_op (slf : Rep) (cop : option Checkpoint) : DirectedMsgs :=
    match cop with
    | Some c => [broadcast2others slf (send_checkpoint c)]
    | None => []
    end.

  Definition update_state_new_view
             (slf   : Rep)
             (state : PBFTstate)
             (nv    : NewView) : PBFTstate * DirectedMsgs :=

    let sn := low_water_mark state in
    let V  := new_view2cert nv in

    match view_change_cert2max_seq_vc V with
    | Some (maxV,vc) =>

      if sn <? maxV then

        (* The checkpoint certificate C has a higher sequence number than our
           current certificate, so we'll replace our current certificate by this one *)
        let C := view_change2cert vc in
        let s := view_change2stable vc in
        let v := view_change2view vc in

        let (new_state1, cpop) := log_checkpoint_cert_from_new_view slf state v maxV C s in

        (* we clear the log *)
        let new_log    := clear_log_checkpoint (log new_state1) maxV in
        let new_state2 := update_log new_state1 new_log in

        (* we clear the checkpoint log *)
        let new_state3 := trim_checkpoint new_state2 maxV in

        let new_state4 := update_checkpoint_from_new_view new_state3 s maxV in

        let out := broadcast_checkpoint_op slf cpop in

        (new_state4, out)

      else (state, [])

    | None => (state, [])
    end.

  Definition PBFThandle_check_bcast_new_view (slf : Rep)
    : Update PBFTstate CheckBCastNewView DirectedMsgs :=
    fun state c =>
      match CheckBCastNewView2entry c (view_change_state state) with
      | Some entry =>

        match check_broadcast_new_view slf state entry with
        | Some (nv, entry', opreps, npreps) =>

          let new_state2 := log_new_view_and_entry_state state nv entry' in
          let new_state3 := log_pre_prepares_of_new_view new_state2 (opreps ++ npreps) in
          let new_state4 := change_sequence_number new_state3 (max_O opreps) in
          let new_state5 := update_view new_state4 (new_view2view nv) in

          let (new_state6, chks) := update_state_new_view slf new_state5 nv in

          let nviews := [broadcast2others slf (send_new_view nv)] in

          (Some new_state6, nviews ++ chks)

        | None => (Some state, [])
        end

      | None => (Some state, [])
      end.

  Definition PBFThandle_expired_timer (slf : Rep) : Update PBFTstate ExpiredTimer DirectedMsgs :=
    fun state t =>
      let view := current_view state in

      if ViewDeq view (expired_timer2view t) then
        (* We only change view if the timer that expired was for the current view *)

        let nview := next_view view in
        let vc := mk_current_view_change slf nview state in

        (* This starts a new view by incrementing the view and starting
           a new view state by recording the generated view-change message *)
        match start_view_change vc (view_change_state state) with
        | (changed_entry, changed_entry_pos, new_vc_state) =>
          let new_state := increment_view (change_view_change_state state new_vc_state) in

          (*  we send a message to ourselves to check whether it's time to checkpoint *)
          let check := send_check_bcast_new_view (check_bcast_new_view changed_entry_pos) [PBFTreplica slf] in
          let vcs   := [broadcast2others slf (send_view_change vc)] in

          (Some new_state, check :: vcs)
        end

      else (* the view we get back from the timer is not the current view *)
        (Some state, []).

  Definition PBFThandle_view_change (slf : Rep) : Update PBFTstate ViewChange DirectedMsgs :=
    fun state vc =>
      let keys     := local_keys state in
      let view     := current_view state in

      let sender  := view_change2sender vc in
      let vc_view := view_change2view vc in

      if rep_deq sender slf then
        (* we ignore the message because it's our own view-change message *)

        (Some state, [])

      else
        (* we check whether the view-change message is signed properly *)
        if verify_view_change slf keys vc then

          if valid_view vc_view view then

            if correct_view_change vc_view vc then

              match add_other_view_change vc (view_change_state state) with
              | Some (modified_entry, modified_entry_pos, new_vc_state) =>
                (* We managed to add the view-change message to our log *)

                let new_state := change_view_change_state state new_vc_state in
                let check := send_check_bcast_new_view (check_bcast_new_view modified_entry_pos) [PBFTreplica slf] in
                (Some new_state, [check])

              | None =>
                (* we didn't manage to add the view-change message to our log *)
                (Some state, [])
              end

            else (* the view-change message is not valid *)
              (Some state, [])

          else (* the view in the view-change message is not valid *)
            (Some state, [])

        else (* the view-change message is not signed properly *)
          (Some state, []).

  Fixpoint find_matching_prepared_info
           (s : SeqNum)
           (d : PBFTdigest)
           (L : list PreparedInfo) : option PreparedInfo :=
    match L with
    | [] => None
    | x :: xs =>
      if SeqNumDeq s (prepared_info2seq x) then
        if PBFTdigestdeq d (prepared_info2digest x) then
          Some x
        else find_matching_prepared_info s d xs
      else find_matching_prepared_info s d xs
    end.

  Definition add_digest (p : Pre_prepare) : Pre_prepare * PBFTdigest :=
    (p, pre_prepare2digest p).

  Definition add_prepare_to_log_from_new_view_pre_prepare
             (slf   : Rep)
             (state : PBFTstate)
             (ppd   : Pre_prepare * PBFTdigest) : PBFTstate * DirectedMsgs :=
    let (pp,digest) := ppd in

    let view := current_view state in
    let keys := local_keys state in
    let sn   := low_water_mark state in

    let sender := pre_prepare2sender pp in
    let ppsn   := pre_prepare2seq pp in
    let ppview := pre_prepare2view pp in

    if sn <? ppsn then

        let Fp := fun (u : unit) => pre_prepare2rep_toks_of_prepare slf keys pp digest in
        let Fc := fun (u : unit) => pre_prepare2rep_toks_of_commit  slf keys pp digest in
        let (entryop, new_log) := add_new_pre_prepare_and_prepare2log slf (log state) pp digest Fp Fc in
        let new_state := update_log state new_log in

        let rd := pre_prepare2request_data pp digest in
        let preps := check_broadcast_prepare slf rd entryop in
        (* Getting this pre_prepare message might make the 'prepared' predicate
           turn true, in which case we start sending commit messages *)
        let comms := check_broadcast_commit slf rd entryop in
        (* Getting this pre_prepare message might make the 'committed' predicate
           turn true, in which case we start sending replies *)
        let (reps, new_state') := check_send_replies slf view keys entryop new_state ppsn in

        (new_state', preps ++ comms ++ reps)

    else

      let prep := pre_prepare2prepare slf keys pp digest in
      (state, [] (*broadcast2others slf (send_prepare prep)*)).

  Fixpoint add_prepares_to_log_from_new_view_pre_prepares
           (slf   : Rep)
           (state : PBFTstate)
           (pps   : list (Pre_prepare * PBFTdigest)) : PBFTstate * DirectedMsgs :=
    match pps with
    | [] => (state, [])
    | ppd :: ppds =>
      let (new_state1, out1) := add_prepare_to_log_from_new_view_pre_prepare slf state ppd in
      let (new_state2, out2) := add_prepares_to_log_from_new_view_pre_prepares slf new_state1 ppds in
      (new_state2, out1 ++ out2)
    end.

  Definition trim_message_with_low_water_mark (lwm : SeqNum) (m : msg) : bool :=
    match m with
    | PBFTprepare p => lwm <? prepare2seq p
    | PBFTcommit c  => lwm <? commit2seq c
    | _ => true
    end.

  Definition trim_output_with_low_water_mark (lwm : SeqNum) (m : DirectedMsg) : bool :=
    trim_message_with_low_water_mark lwm (dmMsg m).

  Definition trim_outputs_with_low_water_mark (msgs : DirectedMsgs) (s : PBFTstate) : DirectedMsgs :=
    filter (trim_output_with_low_water_mark (low_water_mark s)) msgs.

  Definition PBFThandle_new_view (slf : Rep) : Update PBFTstate NewView DirectedMsgs :=
    fun state nv =>
      let keys  := local_keys state in
      let cview := current_view state in

      let nvview := new_view2view nv in
      let sender := new_view2sender nv in
      let V      := new_view2cert nv in
      let OP     := new_view2oprep nv in
      let NP     := new_view2nprep nv in

      if rep_deq sender slf then
        (* we ignore the message because we sent it *)

        (Some state, [])

      else

        (* we check whether the new-view message is signed properly *)
        if verify_new_view slf keys nv then

          if ViewLt initial_view nvview then

            if ViewLe cview nvview then

              if correct_new_view nv then

                if has_new_view (view_change_state state) nvview then
                  (* we have already a new-view message for this view *)

                  (Some state, [])

                else (* we don't yet have a new-view message for this view *)

                  let new_state1 := update_view state nvview in
                  let pre_preps  := map (fun p => add_digest p) (OP ++ NP) in
                  let (new_state2, out) := add_prepares_to_log_from_new_view_pre_prepares slf new_state1 pre_preps in
                  let new_state3 := log_new_view_state new_state2 nv in

                  let (new_state4, chks) := update_state_new_view slf new_state3 nv in

                  let out2 := trim_outputs_with_low_water_mark out new_state4 ++ chks in

                  (Some new_state4, out2)

              else (* the new-view message is not correct *)
                (Some state, [])

            else (* the view of the new-view message is at least our current view *)
              (Some state, [])

          else (* the view in the new-view message is 0 *)
            (Some state, [])

        else
          (* we couldn't verify the message *)
          (Some state, []).

  Definition check_executed_bare_request (state : PBFTstate) (r : Bare_Request) : bool :=
    match bare_request2sender r with
    | Some c =>
      match find_last_reply_entry_corresponding_to_client (last_reply_state state) c with
      | Some e => bare_request2timestamp r <=? lre_timestamp e
      | None => false
      end
    | None => false
    end.

  Definition PBFThandle_start_timer (slf : Rep) : Update PBFTstate StartTimer DirectedMsgs :=
    fun state t =>
      let r := start_timer2req t in
      if check_executed_bare_request state r then
        (Some state, [])
      else
        let t := start_timer2expired_timer t in
        (Some state, [send_expired_timer t slf]).

  (* Replicas don't react to replies *)
  Definition PBFThandle_reply (slf : Rep) : Update PBFTstate Reply DirectedMsgs :=
    fun state r => (Some state, []).

  (* Replicas don't react to debug messages *)
  Definition PBFThandle_debug (slf : Rep) : Update PBFTstate Debug DirectedMsgs :=
    fun state r => (Some state, []).

  Definition PBFThandle_check_ready (slf : Rep) : Update PBFTstate CheckReady DirectedMsgs :=
    fun state c =>
      let keys := local_keys state in
      let view := current_view state in
      let rdy  := ready state in

      match find_and_execute_requests slf view keys state with
      | (outs, new_state) =>

        (* the primary decrements the number of requests in progress because
           this one is now ready to be executed *)
        let decr_state := decrement_requests_in_progress_if_primary slf view new_state in

        (* we send the replies to the corresponding clients *)
        (Some decr_state,  outs)
      end.

  Fixpoint check_one_stable (i : Rep) (s : PBFTstate) (l : PBFTcheckpoint_log) : PBFTstate :=
    match l with
    | [] => s
    | entry :: entries =>
      if low_water_mark s <? cp_sn entry then
        match check_stable i s entry with
        | Some s' => s'
        | None => check_one_stable i s entries
        end
      else check_one_stable i s entries
    end.

  Definition PBFThandle_check_stable (slf : Rep) : Update PBFTstate CheckStableChkPt DirectedMsgs :=
    fun state c =>
      let new_state := check_one_stable slf state (chk_state_others (cp_state state)) in
      (Some new_state, []).

  Definition PBFTreplica_update (slf : Rep) : MUpdate PBFTstate :=
    fun state m =>
      match m with
      | PBFTrequest              r => PBFThandle_request              slf state r
      | PBFTpre_prepare          p => PBFThandle_pre_prepare          slf state p
      | PBFTprepare              p => PBFThandle_prepare              slf state p
      | PBFTcommit               c => PBFThandle_commit               slf state c
      | PBFTcheckpoint           c => PBFThandle_checkpoint           slf state c
      | PBFTreply                r => PBFThandle_reply                slf state r
      | PBFTcheck_ready          c => PBFThandle_check_ready          slf state c
      | PBFTcheck_stable         c => PBFThandle_check_stable         slf state c
      | PBFTcheck_bcast_new_view c => PBFThandle_check_bcast_new_view slf state c
      | PBFTstart_timer          t => PBFThandle_start_timer          slf state t
      | PBFTexpired_timer        t => PBFThandle_expired_timer        slf state t
      | PBFTview_change          v => PBFThandle_view_change          slf state v
      | PBFTnew_view             v => PBFThandle_new_view             slf state v
      | PBFTdebug                d => PBFThandle_debug                slf state d
      end.

  Definition PBFTreplicaSM (slf : Rep) : MStateMachine _ :=
    mkSM
      (PBFTreplica_update slf)
      (initial_state slf).

  Definition PBFTnstate (n : name) :=
    match n with
    | PBFTreplica _ => PBFTstate
    | _ => unit
    end.

  Definition PBFTsys : MUSystem PBFTnstate :=
    fun name =>
      match name return StateMachine (PBFTnstate name) msg DirectedMsgs with
      | PBFTreplica n => PBFTreplicaSM n
      | _ => MhaltedSM tt
      end.

End PBFT.
