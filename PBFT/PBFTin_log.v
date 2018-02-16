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


Require Export PBFT.
Require Export PBFTtactics.


Section PBFTin_log.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition mk_pre_prepare
             (v : View)
             (n : SeqNum)
             (m : list Request)
             (a : Tokens) : Pre_prepare :=
    pre_prepare (bare_pre_prepare v n m) a.

    Definition mk_prepare
             (v : View)
             (n : SeqNum)
             (d : PBFTdigest)
             (i : Rep)
             (a : Tokens) : Prepare :=
      prepare (bare_prepare v n d i) a.

      Definition mk_commit
             (v : View)
             (n : SeqNum)
             (d : PBFTdigest)
             (i : Rep)
             (a : Tokens) : Commit :=
        commit (bare_commit v n d i) a.


  (***********************************************************************************************)

(*  Fixpoint old_prepare_in_log
             (p : Prepare)
             (l : PBFTlog) : bool :=
    match l with
    | [] => false
    | entry :: entries =>
      if is_prepare_in_entry entry p then true
      else old_prepare_in_log p entries
    end.*)

  Lemma RepToksDeq : Deq RepToks.
  Proof.
    introv.
    destruct x as [i1 a1], y as [i2 a2].
    destruct (rep_deq i1 i2); subst;[|right; intro xx; inversion xx; tcsp].
    destruct (Tokens_dec a1 a2); subst; tcsp.
    right; intro xx; inversion xx; tcsp.
  Qed.

  (* this checks whether some [RepToks] we received matches our own [RepToks] *)
  Definition rep_toks_matches_logEntryPrePrepareInfo
             (rt  : RepToks) (* information we received *)
             (i   : Rep)     (* location at which the log entry is stored *)
             (nfo : logEntryPrePrepareInfo) (* information in the log *) : bool :=
    match nfo with
    | pp_info_pre_prep auth reqs =>

      if RepToksDeq rt (MkRepToks i auth) then true else false

    | pp_info_no_pre_prep => false
    end.

  (* this checks whether some [RepToks] we received matches our own [RepToks] *)
  Definition auth_matches_logEntryPrePrepareInfo
             (a   : Tokens)
             (nfo : logEntryPrePrepareInfo) (* information in the log *) : bool :=
    match nfo with
    | pp_info_pre_prep auth reqs =>

      if Tokens_dec a auth then true else false

    | pp_info_no_pre_prep => false
    end.

  Lemma TimestampDeq : Deq Timestamp.
  Proof.
    introv; destruct x as [n1], y as [n2]; prove_dec.
    destruct (eq_nat_dec n1 n2); subst; prove_dec.
  Qed.

  Lemma Bare_RequestDeq : Deq Bare_Request.
  Proof.
    introv; destruct x as [|o1 t1 c1], y as [|o2 t2 c2]; prove_dec.
    destruct (PBFTopdeq o1 o2); subst; prove_dec.
    destruct (TimestampDeq t1 t2); subst; prove_dec.
    destruct (client_deq c1 c2); subst; prove_dec.
  Qed.

  Lemma RequestDeq : Deq Request.
  Proof.
    introv; destruct x as [b1 a1], y as [b2 a2].
    destruct (Bare_RequestDeq b1 b2); subst; prove_dec.
    destruct (Tokens_dec a1 a2); subst; prove_dec.
  Qed.

  Fixpoint matching_requests (reqs1 reqs2 : list Request) : bool :=
    match reqs1, reqs2 with
    | [], [] => true
    | r1 :: rs1, r2 :: rs2 =>
      if RequestDeq r1 r2 then matching_requests rs1 rs2
      else false
    | _, _ => false
    end.

  Definition requests_matches_logEntryPrePrepareInfo
             (reqs : list Request)
             (nfo  : logEntryPrePrepareInfo) : bool :=
    match nfo with
    | pp_info_pre_prep _ reqs' =>

      matching_requests reqs (map fst reqs')

    | pp_info_no_pre_prep => false
    end.

  Definition same_rep_tok (rt rt' : RepToks) : bool :=
    if RepToksDeq rt rt' then true else false.

(*  Fixpoint pre_prepare_in_log
             (p : Pre_prepare)
             (l : PBFTlog) : bool :=
    match l with
    | [] => false
    | entry :: entries =>
      if is_pre_prepared_entry entry then true
      else pre_prepare_in_log p entries
    end.*)

  Fixpoint pre_prepare_in_log
           (pp : Pre_prepare)
           (d  : PBFTdigest)
           (l  : PBFTlog) : bool :=
    match l with
    | [] => false
    | entry :: entries =>
      if similar_entry_and_pre_prepare entry pp d then

        let a    := pre_prepare2auth pp in
        let reqs := pre_prepare2requests pp in
        let nfo  := log_entry_pre_prepare_info entry in

        (auth_matches_logEntryPrePrepareInfo a nfo)
          &&
          (requests_matches_logEntryPrePrepareInfo reqs nfo)

      else pre_prepare_in_log pp d entries
    end.

  Fixpoint prepare_in_log
           (p : Prepare)
           (l : PBFTlog) : bool :=
    match l with
    | [] => false
    | entry :: entries =>
      if is_prepare_for_entry entry p then

        let rt := prepare2rep_toks p in

        existsb
          (same_rep_tok rt)
          (log_entry_prepares entry)

      else prepare_in_log p entries
    end.

  Fixpoint commit_in_log
           (c : Commit)
           (l : PBFTlog) : bool :=
    match l with
    | [] => false
    | entry :: entries =>
      if is_commit_for_entry entry c then

        let rt := commit2rep_toks c in

        existsb
          (same_rep_tok rt)
          (log_entry_commits entry)

      else commit_in_log c entries
    end.


  (* "prepared" certificate true for given request data *)
  Fixpoint prepared_log
           (d : RequestData)
           (l : PBFTlog) : bool :=
    match l with
    | [] => false
    | entry :: entries =>
      if is_request_data_for_entry entry d
      then is_prepared_entry entry
      else prepared_log d entries
    end.

  (* "prepared" predicate is either true or false *)
  Definition prepared
             (d  : RequestData)
             (s  : PBFTstate) : bool :=
    prepared_log d (log s).

End PBFTin_log.
