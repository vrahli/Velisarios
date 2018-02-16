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


Require Export Quorum.
Require Export Process.


Section PBFTheader.

  Local Open Scope eo.
  Local Open Scope proc.


  (* ===============================================================
     Parameters
     =============================================================== *)

  Class PBFTcontext :=
    MkPBFTcontext
      {
        (* maximum number of requests that can be handled at the same time *)
        PBFTmax_in_progress : nat;

        (* This number has to be big enough so that replicas do not stall waiting
         for a checkpoint to become stable *)
        PBFTwater_mark_range : nat; (* this should be SeqNum type *)

        (* usually half of the water-mark range *)
        PBFTcheckpoint_period : nat;

        PBFTdigest : Set;
        PBFTdigestdeq : Deq PBFTdigest;

        PBFTtoken    : Set;
        PBFTtokendeq : Deq PBFTtoken;

        PBFTsending_key   : Set;
        PBFTreceiving_key : Set;

        (* number of faults *)
        F : nat;

        (* ++++++++ Nodes (Replicas & Clients) ++++++++ *)
        num_replicas := (3 * F) + 1;

        (* We have 3F+1 replicas *)
        Rep : Set;
        rep_deq : Deq Rep;
        reps2nat : Rep -> nat_n num_replicas;
        reps_bij : bijective reps2nat;

        num_clients : nat;

        Client : Set;
        client_deq : Deq Client;
        clients2nat : Client -> nat_n num_clients;
        clients_bij : bijective clients2nat;

        (* ++++++++ replicated service ++++++++ *)
        PBFToperation : Set;
        PBFTopdeq : Deq PBFToperation;

        PBFTresult : Set;
        PBFTresdeq : Deq PBFTresult;

        PBFTsm_state : Set;
        PBFTsm_initial_state : PBFTsm_state;
        PBFTsm_update : Client -> PBFTsm_state -> PBFToperation -> PBFTresult * PBFTsm_state;

        PBFTtimer_delay : nat;
      }.

  Context { pbft_context : PBFTcontext }.



  (* ===============================================================
     Nodes
     =============================================================== *)

  Inductive PBFTnode :=
  | PBFTreplica (n : Rep)
  | PBFTclient (n : Client).

  Definition node2rep (n : PBFTnode) : option Rep :=
    match n with
    | PBFTreplica n => Some n
    | _ => None
    end.

  Definition node2client (n : PBFTnode) : option Client :=
    match n with
    |PBFTclient nn => Some nn
    | _ => None
    end.

  Lemma PBFTnodeDeq : Deq PBFTnode.
  Proof.
    introv; destruct x as [r1|c1], y as [r2|c2].
    - destruct (rep_deq r1 r2);[left|right]; subst; auto.
      intro xx; inversion xx; subst; tcsp.
    - right; intro xx; inversion xx; subst; tcsp.
    - right; intro xx; inversion xx; subst; tcsp.
    - destruct (client_deq c1 c2);[left|right]; subst; auto.
      intro xx; inversion xx; subst; tcsp.
  Defined.

  Global Instance PBFT_I_Node : Node := MkNode PBFTnode PBFTnodeDeq.



  (* ===============================================================
     Quorum
     =============================================================== *)

  Lemma PBFTreplica_inj : injective PBFTreplica.
  Proof.
    introv h; ginv; auto.
  Qed.

  Global Instance PBFT_I_Quorum : Quorum_context :=
    MkQuorumContext
      Rep
      num_replicas
      rep_deq
      reps2nat
      reps_bij
      PBFTreplica
      PBFTreplica_inj.

  (* can we have something like this? *)
  Definition rep2node := Rep -> node_type.


  (* ===============================================================
     More about Nodes
     =============================================================== *)

  (* 0 is less than 2*F+1 *)
  Definition nat_n_2Fp1_0 : nat_n num_replicas.
  Proof.
    exists 0.
    apply leb_correct.
    unfold num_replicas.
    omega.
  Defined.

  Definition replica0 : Rep := bij_inv reps_bij nat_n_2Fp1_0.

  (*Eval simpl in (name_dec (PBFTreplica replica0) (PBFTreplica replica0)).*)

  (* We'll return the node as given by our bijection if n < num_nodes,
     otherwise we return a default value (replica0)
   *)
  Definition nat2rep (n : nat) : Rep.
  Proof.
    destruct reps_bij as [f a b].
    destruct (lt_dec n num_replicas) as [d|d].
    - exact (f (mk_nat_n d)). (* here we now that n < num_replicas so we can use our bijection *)
    - exact replica0. (* here num_replicas <= n, so we return a default value: replica0 *)
  Defined.


  Definition reps : list Rep := nodes.
(*    mapin
      (seq 0 num_replicas)
      (fun n i => bij_inv reps_bij (mk_nat_n (seq_0_lt i))).*)

  Definition nreps : list name := map PBFTreplica reps.

  Lemma reps_prop : forall (x : Rep), In x reps.
  Proof.
    exact nodes_prop.
  Qed.

  Definition clients : list Client :=
    mapin
      (seq 0 num_clients)
      (fun n i => bij_inv clients_bij (mk_nat_n (seq_0_lt i))).

  Definition nclients : list name := map PBFTclient clients.

  Lemma clients_prop : forall (x : Client), In x clients.
  Proof.
    introv.
    unfold clients.
    apply in_mapin.

    remember (clients2nat x) as nx.
    destruct nx as [nx condnx].

    pose proof (leb_complete _ _ condnx) as c.

    assert (In nx (seq O num_clients)) as i.
    { apply in_seq; omega. }

    exists nx i; simpl.

    unfold mk_nat_n.
    unfold bij_inv.
    destruct clients_bij.
    pose proof (bij_id1 x) as h.
    rewrite <- Heqnx in h; subst; simpl.

    f_equal; f_equal.
    apply UIP_dec; apply bool_dec.
  Qed.



  (* ===============================================================
     Views
     =============================================================== *)

  Inductive View :=
  | view (n : nat).

  Definition view2nat (v : View) : nat :=
    match v with
    | view n => n
    end.
  Coercion view2nat : View >-> nat.

  Definition next_view (v : View): View := view (S v).

  Definition pred_view (v : View): View := view (pred v).

  Lemma ViewDeq : Deq View.
  Proof.
    introv; destruct x, y; prove_dec.
    destruct (deq_nat n n0); prove_dec.
  Defined.

  Definition initial_view := view 0.


  Definition ViewLe (vn1 vn2 : View) : bool :=
    view2nat vn1 <=? view2nat vn2.

  Definition ViewLt (vn1 vn2 : View) : bool :=
    view2nat vn1 <? view2nat vn2.

  Definition max_view (v1 v2 : View) : View :=
    if ViewLe v1 v2 then v2 else v1.


  (* ===============================================================
     Timestamps
     =============================================================== *)

  Inductive Timestamp :=
  | time_stamp (q : nat).
  Coercion time_stamp : nat >-> Timestamp.

  Definition timestamp2nat (t : Timestamp) : nat :=
    match t with
    | time_stamp n => n
    end.
  Coercion timestamp2nat : Timestamp >-> nat.

  Definition timestamp0 := time_stamp 0.


  (* ===============================================================
     Sequence numbers
     =============================================================== *)

  Inductive SeqNum :=
  | seq_num (n : nat).
  Coercion seq_num : nat >-> SeqNum.

  Definition seqnum2nat (s : SeqNum) : nat :=
    match s with
    | seq_num n => n
    end.
  Coercion seqnum2nat : SeqNum >-> nat.

  Definition SeqNumLe (sn1 sn2 : SeqNum) : bool :=
    seqnum2nat sn1 <=? seqnum2nat sn2.

  Definition SeqNumLt (sn1 sn2 : SeqNum) : bool :=
    seqnum2nat sn1 <? seqnum2nat sn2.

  Definition next_seq (n : SeqNum): SeqNum := seq_num (S n).

  Lemma SeqNumDeq : Deq SeqNum.
  Proof.
    introv; destruct x, y; prove_dec.
    destruct (deq_nat n n0); prove_dec.
  Defined.

  Definition initial_sequence_number : SeqNum := seq_num 0.

  Definition min_seq_num (s1 s2 : SeqNum) : SeqNum :=
    if SeqNumLe s1 s2 then s1 else s2.

  Definition max_seq_num (s1 s2 : SeqNum) : SeqNum :=
    if SeqNumLe s1 s2 then s2 else s1.



  (* ===============================================================
     Primary
     =============================================================== *)

  Definition PBFTprimary_nat (v : View) : nat := v mod num_replicas.

  Definition PBFTprimary (v : View) : Rep := nat2rep (PBFTprimary_nat v).

  Definition is_primary (v : View) (r : Rep) : bool :=
    if rep_deq r (PBFTprimary v) then true else false.



  (* ===============================================================
     Authentication
     =============================================================== *)

  Definition PBFTtokens := list PBFTtoken.

  Global Instance PBFT_I_AuthTok : AuthTok :=
    MkAuthTok
      PBFTtoken
      PBFTtokendeq.



  (* ===============================================================
     Bare messages
     =============================================================== *)

  Inductive Bare_Request : Set :=
  | null_req
  | bare_req
      (o : PBFToperation)
      (t : Timestamp)
      (c : Client).

  Inductive Bare_Reply :=
  | bare_reply
      (v : View)
      (t : Timestamp)
      (c : Client)
      (i : Rep)
      (r : PBFTresult).

  Inductive Bare_Prepare :=
  | bare_prepare
      (v : View)
      (s : SeqNum)
      (d : PBFTdigest)
      (i : Rep).

  Inductive Bare_Commit :=
  | bare_commit
      (v : View)
      (s : SeqNum)
      (d : PBFTdigest)
      (i : Rep).

  Inductive Bare_Checkpoint :=
  | bare_checkpoint
      (v : View) (* see technical report and PhD thesis*)
      (n : SeqNum)
      (d : PBFTdigest)
      (i : Rep).



  (* ===============================================================
     Authenticated messages
     =============================================================== *)

  Inductive Request :=
  | req
      (b : Bare_Request)
      (a : Tokens).  (* [a] authenticate the client *)

  Inductive Reply :=
  | reply
      (b : Bare_Reply)
      (a : Tokens).  (* [a] authenticate the replica *)

  Inductive Prepare :=
  | prepare
      (b : Bare_Prepare)
      (a : Tokens).  (* [a] authenticate the replica (the leader here) *)

  Inductive Commit :=
  | commit
      (b : Bare_Commit)
      (a : Tokens).  (* [a] authenticate the replica *)

  Inductive Checkpoint :=
  | checkpoint
      (b : Bare_Checkpoint)
      (a : Tokens).  (* [a] authenticate the replica *)

  Inductive Debug :=
  | debug
      (r : Rep)
      (s : String.string).

  Inductive CheckReady :=
  | check_ready.

  Inductive CheckStableChkPt :=
  | check_stable_checkpoint.

  Inductive StartTimer :=
  | start_timer
      (r : Bare_Request)
      (v : View).

  Inductive ExpiredTimer :=
  | expired_timer
      (r : Bare_Request)
      (v : View).



  (* ===============================================================
     Messages depending on authenticated messages
     =============================================================== *)

  Inductive Bare_Pre_prepare :=
  | bare_pre_prepare
      (v : View)
      (s : SeqNum)
      (d : list Request). (* this is a list because we buffer requests *)

  Inductive Pre_prepare :=
  | pre_prepare
      (b : Bare_Pre_prepare)
      (a : Tokens).

  Record PreparedInfo :=
    MkPreparedInfo
      {
        prepared_info_pre_prepare : Pre_prepare;
        prepared_info_digest      : PBFTdigest;
        prepared_info_prepares    : list Prepare;
      }.

  Definition CheckpointCert := list Checkpoint.

  Record LastReplyEntry :=
    MkLastReplyEntry
      {
        lre_client    : Client;
        lre_timestamp : Timestamp;    (* initially 0 *)
        lre_reply     : option PBFTresult; (* None is the initial value *)
      }.

  Definition LastReplyState := list LastReplyEntry.

  (* This is meant to be the last stable checkpoint *)
  Record StableChkPt :=
    MkStableChkPt
      {
        si_state : PBFTsm_state;
        si_lastr : LastReplyState;
      }.

  Inductive Bare_ViewChange :=
  | bare_view_change
      (v : View)
      (n : SeqNum)
      (s : StableChkPt)
      (C : CheckpointCert)
      (P : list PreparedInfo)
      (i : Rep).

  Inductive ViewChange :=
  | view_change
      (v : Bare_ViewChange)
      (a : Tokens).

  Definition ViewChangeCert := list ViewChange.

  Inductive Bare_NewView :=
  | bare_new_view
      (v : View)
      (V : ViewChangeCert)
      (* pre-prepare for which we have a request *)
      (OP : list Pre_prepare)
      (* pre-prepare for which we don't have a request *)
      (NP : list Pre_prepare).

  Inductive NewView :=
  | new_view
      (v : Bare_NewView)
      (a : Tokens).

  Record PBFTviewChangeEntry :=
    MkViewChangeEntry
      {
        (* view number of the entry---all the view-change messages in the entry
           are meant to be for this view *)
        vce_view         : View;

        (* view-change message created locally *)
        vce_view_change  : option ViewChange;

        (* list of view change messages received so far *)
        vce_view_changes : list ViewChange;

        (* new-view message sent in response to enough view-change messages *)
        vce_new_view     : option NewView;
      }.

  Inductive CheckBCastNewView :=
  | check_bcast_new_view (i : nat) (* position of the [PBFTviewChangeEntry] to check *).



  (* ===============================================================
     Bare message type
     =============================================================== *)

  Inductive PBFTBare_Msg : Set :=
  | PBFTmsg_bare_request              (r : Bare_Request)
  | PBFTmsg_bare_reply                (r : Bare_Reply)
  | PBFTmsg_bare_pre_prepare          (p : Bare_Pre_prepare)
  | PBFTmsg_bare_prepare              (p : Bare_Prepare)
  | PBFTmsg_bare_commit               (c : Bare_Commit)
  | PBFTmsg_bare_checkpoint           (c : Bare_Checkpoint)

  (* This is to keep on checking whether there are more requests that are
     ready to be executed *)
  | PBFTmsg_bare_check_ready          (t : CheckReady)

  (* This is to check whether it's time to broadcast a new-view message *)
  | PBFTmsg_bare_check_bcast_new_view (e : CheckBCastNewView)

  (* These are sent to the component in charge of handling timers to start a new
     timer in case of a new request *)
  | PBFTmsg_bare_start_timer          (t : StartTimer)

  (* These are received from the component in charge of handling timers when
     timers have expired *)
  | PBFTmsg_bare_expired_timer        (t : ExpiredTimer)

  | PBFTmsg_bare_view_change          (v : Bare_ViewChange)

  | PBFTmsg_bare_new_view             (v : Bare_NewView).



  (* ===============================================================
     Crypto
     =============================================================== *)

  Global Instance PBFT_I_Data : Data := MkData PBFTBare_Msg.

  Global Instance PBFT_I_Key : Key := MkKey PBFTsending_key PBFTreceiving_key.

  Class PBFTauth :=
    MkPBFTauth
      {
        PBFTcreate : data -> sending_keys -> PBFTtokens;
        PBFTverify : data -> name -> receiving_key -> PBFTtoken -> bool
      }.
  Context { pbft_auth : PBFTauth }.

  Global Instance PBFT_I_AuthFun : AuthFun :=
    MkAuthFun
      PBFTcreate
      PBFTverify.

  Class PBFTinitial_keys :=
    MkPBFTinitial_keys {
        initial_keys : key_map;
      }.

  Context { pbft_initial_keys : PBFTinitial_keys }.



  (* ============ extract sender ==============*)

  Definition bare_request2sender (r : Bare_Request) : option Client :=
    match r with
    | null_req => None
    | bare_req o t c => Some c
    end.

  Definition request2sender (r : Request) : option Client :=
    match r with
    | req b _ => bare_request2sender b
    end.

  Definition bare_reply2sender (r : Bare_Reply) :  Rep :=
    match r with
    | bare_reply v t c i r => i
    end.

  Definition reply2sender (r : Reply) :  Rep :=
    match r with
    | reply b _ => bare_reply2sender b
    end.

  Definition bare_pre_prepare2sender (p : Bare_Pre_prepare) : Rep :=
    match p with
    | bare_pre_prepare v n d => PBFTprimary v
    end.

  Definition pre_prepare2sender (p : Pre_prepare) : Rep :=
    match p with
    | pre_prepare b _ => bare_pre_prepare2sender b
    end.

  Definition bare_prepare2sender (p : Bare_Prepare) : Rep :=
    match p with
    | bare_prepare v n d i => i
    end.

  Definition prepare2sender (p : Prepare) : Rep :=
    match p with
    | prepare b _ => bare_prepare2sender b
    end.

  Definition bare_commit2sender (c : Bare_Commit) : Rep :=
    match c with
    | bare_commit v n d i => i
    end.

  Definition commit2sender (c : Commit) : Rep :=
    match c with
    | commit b _ => bare_commit2sender b
    end.

  Definition bare_checkpoint2sender (c : Bare_Checkpoint) : Rep :=
    match c with
    | bare_checkpoint v n d i => i
    end.

  Definition checkpoint2sender (c : Checkpoint) : Rep :=
    match c with
    | checkpoint b _ => bare_checkpoint2sender b
    end.

  Definition debug2sender (d : Debug) :  Rep :=
    match d with
    | debug s _ => s
    end.

  Definition bare_view_change2sender (v : Bare_ViewChange) :  Rep :=
    match v with
    | bare_view_change v n s C P i => i
    end.

  Definition view_change2sender (v : ViewChange) : Rep :=
    match v with
    | view_change bv _ => bare_view_change2sender bv
    end.

  Definition bare_new_view2sender (b : Bare_NewView) : Rep :=
    match b with
    | bare_new_view v V OP NP => PBFTprimary v
    end.

  Definition new_view2sender (v : NewView) : Rep :=
    match v with
    | new_view b _ => bare_new_view2sender b
    end.

  Definition prepared_info2senders (nfo : PreparedInfo) : list Rep :=
    map prepare2sender (prepared_info_prepares nfo).

  Definition prepared_info2pp_sender (nfo : PreparedInfo) : Rep :=
    pre_prepare2sender (prepared_info_pre_prepare nfo).



  (* ============ extract signature ==============*)

  Definition request2sign (r : Request) : Tokens :=
    match r with
    | req _ a => a
    end.

  Definition reply2sign (r : Reply) : Tokens :=
    match r with
    | reply _ a => a
    end.

  Definition pre_prepare2sign (p : Pre_prepare) : Tokens :=
    match p with
    | pre_prepare _ a => a
    end.

  Definition prepare2sign (p : Prepare) : Tokens :=
    match p with
    | prepare _ a => a
    end.

  Definition commit2sign (c : Commit) : Tokens :=
    match c with
    | commit _ a => a
    end.

  Definition checkpoint2sign (c : Checkpoint) : Tokens :=
    match c with
    | checkpoint _ a => a
    end.

  (* ============  extract sequence number ============== *)

  Definition bare_pre_prepare2seq (p : Bare_Pre_prepare) : SeqNum :=
    match p with
    | bare_pre_prepare v n d => n
    end.

  Definition pre_prepare2seq (p : Pre_prepare) : SeqNum :=
    match p with
    | pre_prepare b _ => bare_pre_prepare2seq b
    end.

  Definition bare_prepare2seq (p : Bare_Prepare) : SeqNum :=
    match p with
    | bare_prepare v n d i => n
    end.

  Definition prepare2seq (p : Prepare) : SeqNum :=
    match p with
    | prepare b _ => bare_prepare2seq b
    end.

  Definition bare_commit2seq (c : Bare_Commit) : SeqNum :=
    match c with
    | bare_commit v n d i => n
    end.

  Definition commit2seq (c : Commit) : SeqNum :=
    match c with
    | commit b _ => bare_commit2seq b
    end.

  Definition bare_checkpoint2seq (c : Bare_Checkpoint) : SeqNum :=
    match c with
    | bare_checkpoint v n d i => n
    end.

  Definition checkpoint2seq (c : Checkpoint) : SeqNum :=
    match c with
    | checkpoint b _ => bare_checkpoint2seq b
    end.

  Definition bare_view_change2seq (bvc : Bare_ViewChange) : SeqNum :=
    match bvc with
    | bare_view_change v n s C P i => n
    end.

  Definition view_change2seq (vc : ViewChange) : SeqNum :=
    match vc with
    | view_change bvc _ => bare_view_change2seq bvc
    end.

  Definition prepared_info2seq (p : PreparedInfo) : SeqNum :=
    pre_prepare2seq (prepared_info_pre_prepare p).


  (* =========== extract operation =========== *)

  Definition bare_request2operation (r : Bare_Request) : option PBFToperation :=
    match r with
    | null_req => None
    | bare_req o t c => Some o
    end.

  Definition request2operation (r : Request) : option PBFToperation :=
    match r with
    | req b _ => bare_request2operation b
    end.


  (* =========== extract timestamp =========== *)

  Definition bare_request2timestamp (r : Bare_Request) : Timestamp :=
    match r with
    | null_req => timestamp0
    | bare_req o t c => t
    end.

  Definition request2timestamp (r : Request) : Timestamp :=
    match r with
    | req b _ => bare_request2timestamp b
    end.

  Definition bare_reply2timestamp (r : Bare_Reply) :=
    match r with
    | bare_reply v t c i r => t
    end.

  Definition reply2timestamp (r : Reply) :=
    match r with
    | reply b _ => bare_reply2timestamp b
    end.


  (* =========== extract receiver =========== *)

  Definition bare_reply2client (r : Bare_Reply) : Client :=
    match r with
    | bare_reply v t c i r => c
    end.

  Definition reply2client (r : Reply) : Client :=
    match r with
    | reply b _ => bare_reply2client b
    end.


  (* =========== extract result =========== *)

  Definition bare_reply2result (r : Bare_Reply) :=
    match r with
    | bare_reply v t c i r => r
    end.

  Definition reply2result (r : Reply) :=
    match r with
    | reply b _ => bare_reply2result b
    end.


  (* =========== extracts bare message =========== *)

  Definition reply2bare (r : Reply) :  Bare_Reply :=
    match r with
    | reply b _ => b
    end.

  Definition request2bare (r : Request) :  Bare_Request :=
    match r with
    | req b _ => b
    end.

  Definition pre_prepare2bare (pp : Pre_prepare) : Bare_Pre_prepare :=
    match pp with
    | pre_prepare bp _ => bp
    end.

  Definition bare_pre_prepare2bare_prepare
             (bpp : Bare_Pre_prepare)
             (d   : PBFTdigest)
             (r   : Rep) : Bare_Prepare :=
    match bpp with
    | bare_pre_prepare v s _ => bare_prepare v s d r
    end.

  Definition pre_prepare2bare_prepare
             (p : Pre_prepare)
             (d : PBFTdigest)
             (r : Rep) : Bare_Prepare :=
    match p with
    | pre_prepare b _ => bare_pre_prepare2bare_prepare b d r
    end.

  Definition bare_prepare2bare_commit (slf : Rep) (bp : Bare_Prepare) : Bare_Commit :=
    match bp with
    | bare_prepare v s d i => bare_commit v s d slf
    end.

  Definition prepare2bare_commit (slf : Rep) (p : Prepare) : Bare_Commit :=
    match p with
    | prepare b a => bare_prepare2bare_commit slf b
    end.

  Definition bare_commit2bare_reply
             (bc : Bare_Commit)
             (t : Timestamp)
             (c : Client)
             (r : PBFTresult) : Bare_Reply :=
    match bc with
    | bare_commit v s d i=> bare_reply v t c i r
    end.

  Definition commit2bare_reply
             (c : Commit)
             (t : Timestamp)
             (cl : Client)
             (r : PBFTresult) : Bare_Reply :=
    match c with
    | commit b a => bare_commit2bare_reply b t cl r
    end.

  Definition bare_request2bare_reply
             (br : Bare_Request)
             (v  : View)
             (i  : Rep)
             (r  : PBFTresult) : option Bare_Reply :=
    match br with
    | null_req => None
    | bare_req opr t c => Some (bare_reply v t c i r)
    end.

  Definition request2bare_reply
             (req : Request)
             (v   : View)
             (i   : Rep)
             (r   : PBFTresult) : option Bare_Reply :=
    match req with
    | req b _ => bare_request2bare_reply b v i r
    end.

  Definition bare_request2info (br : Bare_Request) : option (PBFToperation * Timestamp * Client) :=
    match br with
    | null_req => None
    | bare_req opr t c => Some (opr, t, c)
    end.

  Definition request2info (req : Request) : option (PBFToperation * Timestamp * Client) :=
    match req with
    | req b _ => bare_request2info b
    end.

  Definition bare_pre_prepare2bare_commit
             (slf : Rep)
             (b   : Bare_Pre_prepare)
             (d   : PBFTdigest) : Bare_Commit :=
    match b with
    | bare_pre_prepare v s _ => bare_commit v s d slf
    end.

  Definition pre_prepare2bare_commit
             (slf : Rep)
             (pp  : Pre_prepare)
             (d   : PBFTdigest) : Bare_Commit :=
    match pp with
    | pre_prepare b _ => bare_pre_prepare2bare_commit slf b d
    end.

  Definition view_change2bare (vc : ViewChange) : Bare_ViewChange :=
    match vc with
    | view_change v _ => v
    end.



  (* =========== extract view ===============*)

  Definition bare_reply2view (r : Bare_Reply) :=
    match r with
    | bare_reply v t c i r => v
    end.

  Definition reply2view (r : Reply) :=
    match r with
    | reply b _ => bare_reply2view b
    end.

  Definition bare_pre_prepare2view (p : Bare_Pre_prepare) :=
    match p with
    | bare_pre_prepare v n d =>  v
    end.

  Definition pre_prepare2view (p : Pre_prepare) :=
    match p with
    | pre_prepare b _ => bare_pre_prepare2view b
    end.

  Definition bare_prepare2view (p : Bare_Prepare) :=
    match p with
    | bare_prepare v n d i => v
    end.

  Definition prepare2view (p : Prepare) :=
    match p with
    | prepare b _ => bare_prepare2view b
    end.

  Definition bare_commit2view (c : Bare_Commit) :=
    match c with
    | bare_commit v n d i => v
    end.

  Definition commit2view (c : Commit) :=
    match c with
    | commit b _ => bare_commit2view b
    end.

  Definition bare_checkpoint2view (c : Bare_Checkpoint) :=
    match c with
    | bare_checkpoint v n d i => v
    end.

  Definition checkpoint2view (c : Checkpoint) :=
    match c with
    | checkpoint b _ => bare_checkpoint2view b
    end.

  Definition bare_new_view2view (v : Bare_NewView) :=
    match v with
    | bare_new_view v V OP NP => v
    end.

  Definition new_view2view (v : NewView) :=
    match v with
    | new_view b _ => bare_new_view2view b
    end.

  Definition expired_timer2view (e : ExpiredTimer) :=
    match e with
    | expired_timer r v => v
    end.

  Definition bare_view_change2view (bvc : Bare_ViewChange) : View :=
    match bvc with
    | bare_view_change v n s C P i => v
    end.

  Definition view_change2view (vc : ViewChange) : View :=
    bare_view_change2view (view_change2bare vc).

  Definition prepared_info2view (p : PreparedInfo) : View :=
    pre_prepare2view (prepared_info_pre_prepare p).

  Definition start_timer2view (b : StartTimer) : View :=
    match b with
    | start_timer _ v => v
    end.



  (* =========== timer extraction =========== *)

  Definition start_timer2req (b : StartTimer) : Bare_Request :=
    match b with
    | start_timer r _ => r
    end.

  Definition start_timer2expired_timer (b : StartTimer) : ExpiredTimer :=
    match b with
    | start_timer r v => expired_timer r v
    end.



  (* =========== extract prepared info =========== *)

  Definition bare_view_change2prep (bvc : Bare_ViewChange) : list PreparedInfo :=
    match bvc with
    | bare_view_change v n s C P i => P
    end.

  Definition view_change2prep (vc : ViewChange) : list PreparedInfo :=
    bare_view_change2prep (view_change2bare vc).



  (* =========== extract original msg that client send =========== *)

  Definition bare_pre_prepare2requests (p : Bare_Pre_prepare) : list Request :=
    match p with
    | bare_pre_prepare _ _ m => m
    end.

  Definition pre_prepare2requests (p : Pre_prepare) : list Request :=
    match p with
    | pre_prepare bpp _ => bare_pre_prepare2requests bpp
    end.

  Definition prepared_info2requests (p : PreparedInfo) : list Request :=
    pre_prepare2requests (prepared_info_pre_prepare p).


  (* =========== extract digest of msg that client sent ===========*)

  Definition bare_prepare2digest (p : Bare_Prepare) : PBFTdigest  :=
    match p with
    | bare_prepare v n d i => d
    end.

  Definition prepare2digest (p : Prepare) : PBFTdigest  :=
    match p with
    | prepare b _ => bare_prepare2digest b
    end.

  Definition bare_commit2digest (c : Bare_Commit) : PBFTdigest :=
    match c with
    | bare_commit v n d i => d
    end.

  Definition commit2digest (c : Commit) : PBFTdigest :=
    match c with
    | commit b _ => bare_commit2digest b
    end.


  Definition bare_checkpoint2digest (c : Bare_Checkpoint) : PBFTdigest :=
    match c with
    | bare_checkpoint v n d i => d
    end.

  Definition checkpoint2digest (c : Checkpoint) : PBFTdigest :=
    match c with
    | checkpoint b _ => bare_checkpoint2digest b
    end.

  Definition prepared_info2digest (p : PreparedInfo) : PBFTdigest :=
    prepared_info_digest p.


  (* =========== Msg type =========== *)

  Inductive PBFTmsg :=
  | PBFTrequest              (r : Request)
  | PBFTpre_prepare          (p : Pre_prepare)
  | PBFTprepare              (p : Prepare)
  | PBFTcommit               (c : Commit)
  | PBFTreply                (r : Reply)
  | PBFTcheckpoint           (c : Checkpoint)
  | PBFTcheck_ready          (c : CheckReady)
  | PBFTcheck_stable         (c : CheckStableChkPt)
  | PBFTcheck_bcast_new_view (c : CheckBCastNewView)
  | PBFTstart_timer          (c : StartTimer)
  | PBFTexpired_timer        (t : ExpiredTimer)
  | PBFTview_change          (v : ViewChange)
  | PBFTnew_view             (v : NewView)
  | PBFTdebug                (d : Debug).

  Global Instance PBFT_I_Msg : Msg := MkMsg PBFTmsg.

  Definition PBFTmsg2status (m : PBFTmsg) : msg_status :=
    match m with
    | PBFTrequest              _ => MSG_STATUS_EXTERNAL
    | PBFTpre_prepare          _ => MSG_STATUS_PROTOCOL
    | PBFTprepare              _ => MSG_STATUS_PROTOCOL
    | PBFTcommit               _ => MSG_STATUS_PROTOCOL
    | PBFTcheckpoint           _ => MSG_STATUS_PROTOCOL
    | PBFTreply                _ => MSG_STATUS_PROTOCOL
    | PBFTcheck_ready          _ => MSG_STATUS_INTERNAL
    | PBFTcheck_stable         _ => MSG_STATUS_INTERNAL
    | PBFTcheck_bcast_new_view _ => MSG_STATUS_INTERNAL
    | PBFTstart_timer          _ => MSG_STATUS_INTERNAL
    | PBFTexpired_timer        _ => MSG_STATUS_INTERNAL
    | PBFTview_change          _ => MSG_STATUS_PROTOCOL
    | PBFTnew_view             _ => MSG_STATUS_PROTOCOL
    | PBFTdebug                _ => MSG_STATUS_INTERNAL
    end.

  Global Instance PBFT_I_get_msg_status : MsgStatus := MkMsgStatus PBFTmsg2status.



  (* =========== Receive functions and state machines =========== *)

  Definition receive_request (m : PBFTmsg) : option Request :=
    match m with
    | PBFTrequest r => Some r
    | _ => None
    end.

  Definition PBFTreceiveRequest : StateMachine _ PBFTmsg (option Request) :=
    mkSSM (fun state m => (state, receive_request m)) tt.

  Definition receive_pre_prepare (m : PBFTmsg) : option Pre_prepare :=
    match m with
    | PBFTpre_prepare p => Some p
    | _ => None
    end.

  Definition PBFTreceivePre_prepare : StateMachine _ PBFTmsg (option Pre_prepare) :=
    mkSSM (fun state m => (state, receive_pre_prepare m)) tt.

  Definition receive_prepare (m : PBFTmsg) : option Prepare :=
    match m with
    | PBFTprepare p => Some p
    | _ => None
    end.

  Definition PBFTreceivePrepare : StateMachine _ PBFTmsg (option Prepare) :=
    mkSSM (fun state m => (state, receive_prepare m)) tt.

  Definition receive_commit (m : PBFTmsg) : option Commit :=
    match m with
    | PBFTcommit c => Some c
    | _ => None
    end.

  Definition PBFTreceiveCommit : StateMachine _ PBFTmsg (option Commit) :=
    mkSSM (fun state m => (state, receive_commit m)) tt.


  Definition receive_checkpoint (m : PBFTmsg) : option Checkpoint :=
    match m with
    | PBFTcheckpoint c => Some c
    | _ => None
    end.

  Definition PBFTreceiveCheckpoint : StateMachine _ PBFTmsg (option Checkpoint) :=
    mkSSM (fun state m => (state, receive_checkpoint m)) tt.

  Definition receive_reply (m : PBFTmsg) : option Reply :=
    match m with
    | PBFTreply r => Some r
    | _ => None
    end.

  Definition PBFTreceiveReply : StateMachine _ PBFTmsg (option Reply) :=
    mkSSM (fun state m => (state, receive_reply m)) tt.


  (* ===============================================================
     Authenticated Messages
     =============================================================== *)

  Definition option_client2name (cop : option Client) (n : name) : name :=
    match cop with
    | Some c => PBFTclient c
    | None => n
    end.

  (* we are here extracting the sender of the message *)
  Definition PBFTmsg_auth (n : name) (m : msg) : option name :=
    match m with
    | PBFTrequest              r => Some (option_client2name (request2sender r) n)
    | PBFTpre_prepare          p => Some (PBFTreplica (pre_prepare2sender p))
    | PBFTprepare              p => Some (PBFTreplica (prepare2sender p))
    | PBFTcommit               c => Some (PBFTreplica (commit2sender c))
    | PBFTcheckpoint           c => Some (PBFTreplica (checkpoint2sender c))
    | PBFTreply                r => Some (PBFTreplica (reply2sender r))
    | PBFTcheck_ready          c => Some n (* local message *)
    | PBFTcheck_stable         c => Some n (* local message *)
    | PBFTcheck_bcast_new_view c => Some n (* local message *)
    | PBFTstart_timer          t => Some n (* local message *)
    | PBFTexpired_timer        t => Some n (* local message *)
    | PBFTview_change          v => Some (PBFTreplica (view_change2sender v))
    | PBFTnew_view             v => Some (PBFTreplica (new_view2sender v))
    | PBFTdebug                d => Some (PBFTreplica (debug2sender d))
    end.

  Definition PBFTdata_auth (n : name) (m : data) : option name :=
    match m with
    | PBFTmsg_bare_request              r => Some (option_client2name (bare_request2sender r) n)
    | PBFTmsg_bare_pre_prepare          p => Some (PBFTreplica (bare_pre_prepare2sender p))
    | PBFTmsg_bare_prepare              p => Some (PBFTreplica (bare_prepare2sender p))
    | PBFTmsg_bare_commit               c => Some (PBFTreplica (bare_commit2sender c))
    | PBFTmsg_bare_checkpoint           c => Some (PBFTreplica (bare_checkpoint2sender c))
    | PBFTmsg_bare_reply                r => Some (PBFTreplica (bare_reply2sender r))
    | PBFTmsg_bare_check_ready          _ => Some n (* local message *)
    | PBFTmsg_bare_check_bcast_new_view _ => Some n (* local message *)
    | PBFTmsg_bare_start_timer          _ => Some n (* local message *)
    | PBFTmsg_bare_expired_timer        _ => Some n (* local message *)
    | PBFTmsg_bare_view_change          v => Some (PBFTreplica (bare_view_change2sender v))
    | PBFTmsg_bare_new_view             v => Some (PBFTreplica (PBFTprimary ((*pred_view*) (bare_new_view2view v))))
    end.

  Global Instance PBFT_I_DataAuth : DataAuth := MkDataAuth PBFTdata_auth.

  Definition request2auth_data (r : Request) : AuthenticatedData :=
    match r with
    | req b a => MkAuthData (PBFTmsg_bare_request b) a
    end.

  Definition reply2auth_data (r : Reply) : AuthenticatedData :=
    match r with
    | reply b a => MkAuthData (PBFTmsg_bare_reply b) a
    end.

  Definition pre_prepare_data2auth_data_pre (p : Pre_prepare) : AuthenticatedData :=
    match p with
    | pre_prepare b a => MkAuthData (PBFTmsg_bare_pre_prepare b) a
    end.

  Definition pre_prepare2auth_data_req (p : Pre_prepare) : list AuthenticatedData :=
    map request2auth_data (pre_prepare2requests p).

  Definition pre_prepare2auth_data (p : Pre_prepare) : list AuthenticatedData :=
    pre_prepare_data2auth_data_pre p :: pre_prepare2auth_data_req p.

  Definition prepare2auth_data (p : Prepare) : AuthenticatedData :=
    match p with
    | prepare b a => MkAuthData (PBFTmsg_bare_prepare b) a
    end.

  Definition commit2auth_data (c : Commit) : AuthenticatedData :=
    match c with
    | commit b a => MkAuthData (PBFTmsg_bare_commit b) a
    end.

  Definition checkpoint2auth_data (c : Checkpoint) : AuthenticatedData :=
    match c with
    | checkpoint b a => MkAuthData (PBFTmsg_bare_checkpoint b) a
    end.

  Definition prepares2auth_data (l : list Prepare): list AuthenticatedData :=
    map prepare2auth_data l.

  Definition prepared_info2auth_data (p : PreparedInfo) : list AuthenticatedData :=
    (pre_prepare2auth_data (prepared_info_pre_prepare p))
      ++ (prepares2auth_data (prepared_info_prepares p)).

  Definition prepared_infos2auth_data (P : list PreparedInfo) : list AuthenticatedData :=
    flat_map prepared_info2auth_data P.

  Definition checkpoints2auth_data (l : list Checkpoint) : list AuthenticatedData :=
    map checkpoint2auth_data l.

  Definition view_change2auth_data (v : ViewChange) : list AuthenticatedData :=
    match v with
    | view_change (bare_view_change v n s C P i) a =>
      (MkAuthData (PBFTmsg_bare_view_change (bare_view_change v n s C P i)) a)
        :: checkpoints2auth_data C
        ++ prepared_infos2auth_data P
    end.

  Definition view_changes2auth_data (l : list ViewChange) : list AuthenticatedData :=
    flat_map view_change2auth_data l.

  Definition pre_prepares2auth_data (l : list Pre_prepare) : list AuthenticatedData :=
    flat_map pre_prepare2auth_data l.

  Definition new_view2auth_data (v : NewView) : list AuthenticatedData :=
    match v with
    | new_view (bare_new_view v V OP NP) a =>
      (MkAuthData (PBFTmsg_bare_new_view (bare_new_view v V OP NP)) a)
        :: view_changes2auth_data V
        ++ pre_prepares2auth_data OP
        ++ pre_prepares2auth_data NP
    end.

  Definition PBFTget_contained_auth_data (m : msg) : list AuthenticatedData :=
    match m with
    | PBFTrequest              r => [request2auth_data r]
    | PBFTreply                r => [reply2auth_data r]
    | PBFTpre_prepare          p => pre_prepare2auth_data p
    | PBFTprepare              p => [prepare2auth_data p]
    | PBFTcommit               p => [commit2auth_data p]
    | PBFTcheckpoint           p => [checkpoint2auth_data p]
    | PBFTcheck_ready          _ => [] (* internal message *)
    | PBFTcheck_stable         _ => [] (* internal message *)
    | PBFTcheck_bcast_new_view _ => [] (* internal message *)
    | PBFTstart_timer          _ => [] (* internal message *)
    | PBFTexpired_timer        _ => [] (* internal message *)
    | PBFTview_change          v => view_change2auth_data v
    | PBFTnew_view             v => new_view2auth_data v
    | PBFTdebug                _ => [] (* internal message *)
    end.

  Global Instance PBFT_I_ContainedAuthData : ContainedAuthData :=
    MkContainedAuthData PBFTget_contained_auth_data.



  (* ===============================================================
     Sending functions
     =============================================================== *)

  Definition send_request (r : Request) (n : list name) : DirectedMsg :=
    MkDMsg (PBFTrequest r) n 0.

  Definition send_reply (r : Reply) : DirectedMsg :=
    MkDMsg (PBFTreply r) [PBFTclient (reply2client r)] 0.

  Definition send_pre_prepare (p : Pre_prepare) (n : list name) : DirectedMsg :=
    MkDMsg (PBFTpre_prepare p) n 0.

  Definition send_prepare (p : Prepare) (n : list name) : DirectedMsg :=
    MkDMsg (PBFTprepare p) n 0.

  Definition send_commit (c : Commit) (n : list name) : DirectedMsg :=
    MkDMsg (PBFTcommit c) n 0.

  Definition send_checkpoint (c : Checkpoint) (n : list name) : DirectedMsg :=
    MkDMsg (PBFTcheckpoint c) n 0.

  Definition send_debug (n : Rep) (s : String.string) : DirectedMsg :=
    MkDMsg (PBFTdebug (debug n s)) [PBFTreplica n] 0.

  Definition send_view_change (v : ViewChange) (n : list name) : DirectedMsg :=
    MkDMsg (PBFTview_change v) n 0.

  Definition send_new_view (v : NewView) (n : list name) : DirectedMsg :=
    MkDMsg (PBFTnew_view v) n 0.

  Definition send_check_ready (n : Rep) : DirectedMsg :=
    MkDMsg (PBFTcheck_ready check_ready) [PBFTreplica n] 0.

  Definition send_check_stable (n : Rep) : DirectedMsg :=
    MkDMsg (PBFTcheck_stable check_stable_checkpoint) [PBFTreplica n] 0.

  Definition send_check_bcast_new_view (c : CheckBCastNewView) (n : list name) : DirectedMsg :=
    MkDMsg (PBFTcheck_bcast_new_view c) n 0.

  Definition send_start_timer (t : StartTimer) (n : Rep) : DirectedMsg :=
    MkDMsg (PBFTstart_timer t) [PBFTreplica n] PBFTtimer_delay.

  Definition send_expired_timer (t : ExpiredTimer) (n : Rep) : DirectedMsg :=
    MkDMsg (PBFTexpired_timer t) [PBFTreplica n] 0.



  (* ===============================================================
     Verify functions
     =============================================================== *)

  Definition verify_request (slf : Rep) (km : local_key_map) (r : Request) : bool :=
    match r with
    | req b a =>
      verify_authenticated_data
        (PBFTreplica slf)
        (MkAuthData (PBFTmsg_bare_request b) a)
        km
    end.

  Definition verify_requests (slf : Rep) (km : local_key_map) (rs : list Request) : bool :=
    forallb (verify_request slf km) rs.

  Definition verify_pre_prepare (slf : Rep) (km : local_key_map) (p : Pre_prepare) : bool :=
    verify_list_auth_data (PBFTreplica slf) km (pre_prepare2auth_data p).

  Definition verify_prepare (slf : Rep) (km : local_key_map) (p : Prepare) : bool :=
    verify_authenticated_data
      (PBFTreplica slf)
      (prepare2auth_data p)
      km.

  Definition verify_commit (slf : Rep) (km : local_key_map) (c : Commit) : bool :=
    verify_authenticated_data
      (PBFTreplica slf)
      (commit2auth_data c)
      km.

  Definition verify_checkpoint (slf : Rep) (km : local_key_map) (c : Checkpoint) : bool :=
    verify_authenticated_data
      (PBFTreplica slf)
      (checkpoint2auth_data c)
      km.

  Definition verify_view_change (slf : Rep) (km : local_key_map) (vc : ViewChange) : bool :=
    verify_list_auth_data (PBFTreplica slf) km (view_change2auth_data vc).

  Definition verify_new_view (slf : Rep) (km : local_key_map) (nv : NewView) : bool :=
    verify_list_auth_data (PBFTreplica slf) km (new_view2auth_data nv).


  (* ===============================================================
     Creation of authenticated messages
     =============================================================== *)

  Definition mk_auth_pre_prepare
             (v : View)
             (s : SeqNum)
             (d : list Request)
             (keys : local_key_map) : Pre_prepare :=
    let bpp  := bare_pre_prepare v s d in
    (* we authenticate the unsigned pre-prepare message *)
    let toks := authenticate (PBFTmsg_bare_pre_prepare bpp) keys in
    (* we create an authenticated pre-prepare message *)
    pre_prepare bpp toks.

  Definition mk_auth_new_view
             (v : View)
             (V : ViewChangeCert)
             (OP NP : list Pre_prepare)
             (keys : local_key_map) : NewView :=
    let bnv  := bare_new_view v V OP NP in
    let toks := authenticate (PBFTmsg_bare_new_view bnv) keys in
    new_view bnv toks.

  Definition mk_auth_reply
             (v : View)
             (t : Timestamp)
             (c : Client)
             (i : Rep)
             (r : PBFTresult)
             (keys : local_key_map) : Reply :=
    let brep := bare_reply v t c i r in
    (* we authenticate the unsigned reply message *)
    let toks := authenticate (PBFTmsg_bare_reply brep) keys in
    (* we create an authenticated reply message *)
    reply brep toks.

  Definition mk_auth_checkpoint
             (v : View)
             (n : SeqNum)
             (d : PBFTdigest)
             (i : Rep)
             (keys : local_key_map) : Checkpoint :=
    let bcp    := bare_checkpoint v n d i in
    (* we authenticate the unsigned checkpoint message *)
    let toks   := authenticate (PBFTmsg_bare_checkpoint bcp) keys in
    (* we create an authenticated checkpoint message *)
    checkpoint bcp toks.

  Definition mk_auth_view_change
             (v : View)
             (n : SeqNum)
             (s : StableChkPt)
             (C : CheckpointCert)
             (P : list PreparedInfo)
             (i : Rep)
             (keys : local_key_map) : ViewChange :=
    let bvc  := bare_view_change v n s C P i in
    let toks := authenticate (PBFTmsg_bare_view_change bvc) keys in
    view_change bvc toks.

  Definition prepare2commit (slf : Rep) (keys : local_key_map) (p : Prepare) : Commit :=
    (* we create a commit message *)
    let bc   := prepare2bare_commit slf p in
    (* we authenticate the unsigned commit message *)
    let toks := authenticate (PBFTmsg_bare_commit bc) keys in
    (* we create an authenticated prepare message *)
    commit bc toks.

  Definition pre_prepare2prepare
             (n    : Rep)
             (keys : local_key_map)
             (pp   : Pre_prepare)
             (d    : PBFTdigest) : Prepare :=
    let bp := pre_prepare2bare_prepare pp d n in
    let a  := authenticate (PBFTmsg_bare_prepare bp) keys in
    prepare bp a.

  Definition pre_prepare2commit
             (slf  : Rep)
             (keys : local_key_map)
             (pp   : Pre_prepare)
             (d    : PBFTdigest) : Commit :=
    (* we create a commit message *)
    let bc   := pre_prepare2bare_commit slf pp d in
    (* we authenticate the unsigned commit message *)
    let toks := authenticate (PBFTmsg_bare_commit bc) keys in
    (* we create an authenticated prepare message *)
    commit bc toks.

  Definition mk_auth_null_req (keys : local_key_map) : Request :=
    req null_req (authenticate (PBFTmsg_bare_request null_req) keys).



  (* ===============================================================
     Hashing
     =============================================================== *)

  Class PBFThash :=
    MkPBFThash
      {
        create_hash_messages : list PBFTmsg -> PBFTdigest;
        verify_hash_messages : list PBFTmsg -> PBFTdigest -> bool;

        create_hash_state_last_reply  : PBFTsm_state -> LastReplyState -> PBFTdigest;
        verify_hash_state_last_reply  : PBFTsm_state -> LastReplyState -> PBFTdigest -> bool;
      }.

  Context { pbft_hash : PBFThash }.

End PBFTheader.
