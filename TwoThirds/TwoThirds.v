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



Require Export Process.

Require Export Loop.
Require Export PairState.
Require Export Parallel.
Require Export Map.
Require Export Bind.
Require Export Until.
Require Export SendId.


Section TwoThirdConsensus.

  Local Open Scope eo.
  Local Open Scope proc.

  Definition nat_n (n : nat) : Set := {m : nat | m <? n = true}.
  Record bijective {A B} (f : A -> B) :=
    {
      bij_inv : B -> A;
      bij_id1 : forall x : A, bij_inv (f x) = x;
      bij_id2 : forall y : B, f (bij_inv y) = y;
    }.
  Arguments bij_inv [A] [B] [f] _ _.

  Parameter Cmd : Set.
  Parameter cmddeq : Deq Cmd.

  (* number of faults *)
  Parameter F : nat.

  (* We have 3F+1 replicas *)
  Parameter Rep : Set.
  Parameter rep_deq : Deq Rep.
  (* ??? *)
  Parameter reps2nat : Rep -> nat_n ((3 * F) + 1).
  Parameter reps_bij : bijective reps2nat.

  Parameter num_clients : nat.

  Inductive TTCnode :=
  | TTCreplica (n : Rep)
  | TTCclient (n : nat).

  Lemma TTCnodeDeq : Deq TTCnode.
  Proof.
    introv; destruct x, y; prove_dec;
      try (destruct (deq_nat n n0); subst; prove_dec);
      try (destruct (rep_deq n n0); subst; prove_dec).
  Qed.

  Definition node2rep (n : TTCnode) : option Rep :=
    match n with
    | TTCreplica n => Some n
    | _ => None
    end.

  Instance TTC_I_Node : Node := MkNode TTCnode TTCnodeDeq.

  Inductive SlotNum :=
  | snum (n : nat).
  Inductive RoundNum :=
  | rnum (n : nat).
  Inductive Proposal :=
  | prop (sn : SlotNum) (cmd : Cmd).
  Inductive VotingRound :=
  | vround (sn : SlotNum) (rn : RoundNum).
  Inductive Ballot :=
  | ballot (vr : VotingRound) (cmd : Cmd).
  Inductive Vote :=
  | vote (b : Ballot) (sender : Rep).

  Definition snum2nat (s : SlotNum) : nat :=
    match s with
    | snum n => n
    end.
  Coercion snum2nat : SlotNum >-> nat.

  Definition rnum2nat (s : RoundNum) : nat :=
    match s with
    | rnum n => n
    end.
  Coercion rnum2nat : RoundNum >-> nat.

  Definition ballot2votingRound (b : Ballot) : VotingRound :=
    match b with
    | ballot vr _ => vr
    end.

  Definition ballot2proposal (b : Ballot) : Proposal :=
    match b with
    | ballot (vround sn _) cmd => prop sn cmd
    end.

  Definition votingRound2SlotNum (v : VotingRound) : SlotNum :=
    match v with
    | vround sn rn => sn
    end.

  Definition vote2proposal (v : Vote) : Proposal :=
    match v with
    | vote (ballot (vround sn rn) cmd) sender => prop sn cmd
    end.

  Definition vote2ballot (v : Vote) : Ballot :=
    match v with
    | vote b n => b
    end.

  Definition vote2sender (v : Vote) : Rep :=
    match v with
    | vote (ballot (vround sn rn) cmd) sender => sender
    end.

  Definition vote2cmd (v : Vote) : Cmd :=
    match v with
    | vote (ballot (vround sn rn) cmd) sender => cmd
    end.

  Definition proposal2ballot (p : Proposal) (rn : RoundNum) : Ballot :=
    match p with
    | prop sn cmd => ballot (vround sn rn) cmd
    end.

  Definition proposal2slot (p : Proposal) : SlotNum :=
    match p with
    | prop sn cmd => sn
    end.

  Inductive TTCmsg :=
    (* input message to propose to fill a slot with some command *)
  | TTCpropose (p : Proposal)
  (* notification of accepted proposal sent to client *)
  | TTCnotify  (p : Proposal)
  (* internal vote for a proposal *)
  | TTCvote    (v : Vote)
  (* internal message to let the replica know that voting is done for some proposal *)
  | TTCdecided (p : Proposal)
  (* internal message to retry voting for a proposal because not unanimous *)
  | TTCretry   (b : Ballot).

  Instance TTC_I_Msg : Msg := MkMsg TTCmsg.

  Definition TTC_msg_status (m : TTCmsg) : msg_status :=
    match m with
    | TTCpropose p => MSG_STATUS_EXTERNAL
    | TTCnotify _  => MSG_STATUS_PROTOCOL
    | TTCvote v    => MSG_STATUS_PROTOCOL
    | TTCdecided _ => MSG_STATUS_INTERNAL
    | TTCretry _   => MSG_STATUS_INTERNAL
    end.

  Instance TTC_I_MsgStatus : MsgStatus := MkMsgStatus TTC_msg_status.

  Definition received_proposal (m : TTCmsg) : option Proposal :=
    match m with
    | TTCpropose p => Some p
    | TTCnotify _  => None
    | TTCvote v    => Some (vote2proposal v)
    | TTCdecided _ => None
    | TTCretry _   => None
    end.

  Definition TTCreceivedProposal : StateMachine _ TTCmsg (option Proposal) :=
    mkSSM (fun state m => (state, received_proposal m)) tt.

  (* ??? *)
  Definition round_info (m : TTCmsg) : option Ballot :=
    match m with
    | TTCpropose p => None
    | TTCnotify _  => None
    | TTCvote v    => Some (vote2ballot v)
    | TTCdecided _ => None
    | TTCretry b   => Some b
    end.

  Definition TTCroundInfo : StateMachine _ TTCmsg (option Ballot) :=
    mkSSM (fun state m => (state, round_info m)) tt.

  Definition receive_vote (m : TTCmsg) : option Vote :=
    match m with
    | TTCpropose p => None
    | TTCnotify _  => None
    | TTCvote v    => Some v
    | TTCdecided _ => None
    | TTCretry _   => None
    end.

  Definition TTCreceiveVote : StateMachine _ TTCmsg (option Vote) :=
    mkSSM (fun state m => (state, receive_vote m)) tt.

  Class DSet (T : Set) :=
    MkDSeq
      {
        dset_set           : Set;
(*        dset_deq : Deq T;*)
        dset_in            : T -> dset_set -> bool;
        dset_add           : T -> dset_set -> dset_set;
        dset_add_if_not_in : T -> dset_set -> option dset_set;
      }.

  Inductive list_with_missing :=
  | lmiss (max : nat) (missing : list nat).

  Definition valid_list_with_missing (lwm : list_with_missing) : Prop :=
    match lwm with
    | lmiss max missing => forall n, In n missing -> n < max
    end.

  Definition in_list_with_missing (n : nat) (lwm : list_with_missing) : Prop :=
    match lwm with
    | lmiss max missing => n <= max /\ ~ In n missing
    end.

  Definition in_list_with_missing_bool (n : nat) (lwm : list_with_missing) : bool :=
    match lwm with
    | lmiss max missing =>
      if le_dec n max
      then if in_dec deq_nat n missing
           then false
           else true
      else false
    end.

  Definition add_to_list_with_missing (n : nat) (lwm : list_with_missing) : list_with_missing :=
    match lwm with
    | lmiss max missing =>
      if lt_dec max n
      then lmiss n (missing ++ seq (S max) (n - S max))
      else
        if in_dec deq_nat n missing
        then lmiss max (remove_elt deq_nat n missing)
        else lwm
    end.

  Definition add_to_list_with_missing_if_not_in (n : nat) (lwm : list_with_missing) : option list_with_missing :=
    match lwm with
    | lmiss max missing =>
      if lt_dec max n
      then Some (lmiss n (missing ++ seq (S max) (n - S max)))
      else
        if in_dec deq_nat n missing
        then Some (lmiss max (remove_elt deq_nat n missing))
        else None
    end.

  (* returns some if the proposal is new, i.e., not in the state.
     In that case it also returns the new state that includes the new proposal *)
  Definition add_new_proposal (p : Proposal) (lwm : list_with_missing) : option list_with_missing :=
    add_to_list_with_missing_if_not_in (proposal2slot p) lwm.

  Definition add_proposal (p : Proposal) (lwm : list_with_missing) : list_with_missing :=
    add_to_list_with_missing (proposal2slot p) lwm.

  Instance DSet_list_with_missing : DSet nat.
  Proof.
    exists list_with_missing.
(*    - introv; apply deq_nat.*)
    - exact in_list_with_missing_bool.
    - exact add_to_list_with_missing.
    - exact add_to_list_with_missing_if_not_in.
  Qed.

  (*
  (* returns a proposal only when it's new *)
  Definition new_voters_upd_opt : SUpdate list_with_missing TTCmsg (option Proposal) :=
    fun state msg =>
      match state, received_proposal msg with
      | _, None => (state, None)
      | _, Some p =>
        match add_new_proposal p state with
        | Some state' => (state', Some p)
        | None => (state, None)
        end
      end.

  Definition new_voters_upd : SUpdate list_with_missing TTCmsg (list Proposal) :=
    fun state msg =>
      match new_voters_upd_opt state msg with
      | (state, Some p) => (state, [p])
      | (state, None) => (state, [])
      end.

  Definition TTCnewVotersSM : StateMachine _ TTCmsg (list Proposal) :=
    mkSSM new_voters_upd (lmiss 0 []).
   *)

  Definition new_voters_upd : SUpdate list_with_missing (option Proposal) (option Proposal) :=
    fun state pop =>
      match pop with
      | Some p =>
        match add_new_proposal p state with
        | Some state' => (state', Some p)
        | None => (state, None)
        end
      | None => (state, None)
      end.

  Definition TTCnewVotersOpt : StateMachine _ TTCmsg (option Proposal) :=
    simple_state_machineSM
      new_voters_upd
      (lmiss 0 [])
      TTCreceivedProposal.

  Definition TTCnewVoters : StateMachine _ TTCmsg (list Proposal) :=
    mapSM opt2list TTCnewVotersOpt.

  (* QUESTION: Why do we have to repeat that? *)
  Arguments MkSM      [S] [I] [O] _ _ _.
  Arguments sm_state  [S] [I] [O] _.
  Arguments sm_update [S] [I] [O] _ _ _.

  Definition mk_nat_n {x n : nat} (p : x < n) : nat_n n :=
    exist _ x (leb_correct _ _ p).

  Definition reps : list Rep :=
    mapin
      (seq 0 ((3 * F) + 1))
      (fun n i => bij_inv reps_bij (mk_nat_n (seq_0_lt i))).

  Definition nreps : list name := map TTCreplica reps.

  Lemma reps_prop : forall (x : Rep), In x reps.
  Proof.
    introv.
    unfold reps.
    apply in_mapin.

    remember (reps2nat x) as nx.
    destruct nx as [nx condnx].

    pose proof (leb_complete _ _ condnx) as c.

    assert (In nx (seq O (3 * F + 1))) as i.
    { apply in_seq; omega. }

    exists nx i; simpl.

    unfold mk_nat_n.
    unfold bij_inv.
    destruct reps_bij.
    pose proof (bij_id3 x) as h.
    rewrite <- Heqnx in h; subst; simpl.

    f_equal; f_equal.
    apply UIP_dec; apply bool_dec.
  Qed.

  Definition clients : list nat := seq 0 num_clients.

  Definition nclients : list name := map TTCclient clients.

  Definition TTCquorumState : Set := list Cmd * list Rep.

  Lemma SlotNumDeq : Deq SlotNum.
  Proof.
    introv; destruct x, y; prove_dec.
    destruct (deq_nat n n0); prove_dec.
  Qed.

  Lemma RoundNumDeq : Deq RoundNum.
  Proof.
    introv; destruct x, y; prove_dec.
    destruct (deq_nat n n0); prove_dec.
  Qed.

  Lemma VotingRoundDeq : Deq VotingRound.
  Proof.
    introv; destruct x, y; prove_dec.
    destruct (SlotNumDeq sn sn0); subst; prove_dec.
    destruct (RoundNumDeq rn rn0); subst; prove_dec.
  Qed.

  Definition new_vote (v : Vote) (vr : VotingRound) (names : list Rep) : bool :=
    match v with
    | vote (ballot vr' cmd) sender =>
      if VotingRoundDeq vr vr'
      then
        if in_dec rep_deq sender names
        then false (* not a new vote: already received a message from this sender *)
        else true
      else false (* not a new vote: vote for another voting round *)
    end.

  Definition incRoundNum (rn : RoundNum) : RoundNum := rnum (S rn).

  (* increments the round of a VotingRound *)
  Definition incVotingRound (vr : VotingRound) : VotingRound :=
    match vr with
    | vround sn rn => vround sn (incRoundNum rn)
    end.

  Fixpoint poss_maj {T} (dec : Deq T) (l : list T) (x : T) : nat * T :=
    match l with
    | [] => (1, x)
    | t :: ts =>
      let (n,z) := poss_maj dec ts x in
      if dec t z then (S n, z)
      else if deq_nat n 0 then (1, t)
           else (pred n, z)
    end.

  Lemma poss_maj_in :
    forall {T} (dec : Deq T) (l : list T) (x : T),
      In (snd (poss_maj dec l x)) (x :: l).
  Proof.
    induction l; introv; simpl; tcsp.
    dest_cases w.
    dest_cases y.
    dest_cases z; simpl in *.
    pose proof (IHl x) as xx; rewrite <- Heqw in xx; simpl in xx.
    repndors; subst; tcsp.
  Qed.

  Inductive TTCdecision :=
  | TTCdecision_decided (c : Cmd)
  | TTCdecision_retry   (c : Cmd).

  (* We check whether we have consensus.  [c] is a default command *)
  Definition TTCconsensus
             (vr   : VotingRound)
             (cmds : list Cmd)
             (c    : Cmd) : option TTCdecision :=
    if deq_nat (length cmds) (2 * F)
    then
      let (k, c') := poss_maj cmddeq cmds c in
      if deq_nat k ((2 * F) + 1)
      then Some (TTCdecision_decided c')
      else Some (TTCdecision_retry c')
    else None.

  Definition send_decided (n : name) (p : Proposal) : DirectedMsg :=
    MkDMsg (TTCdecided p) [n] 0.

  Definition send_retry (n : name) (b : Ballot) : DirectedMsg :=
    MkDMsg (TTCretry b) [n] 0.

  Definition send_vote (n : name) (v : Vote) : DirectedMsg :=
    MkDMsg (TTCvote v) [n] 0.

  Definition send_notify (n : name) (p : Proposal) : DirectedMsg :=
    MkDMsg (TTCnotify p) [n] 0.

  Definition decision2msgs (slf : name) (vr : VotingRound) (d : TTCdecision) : DirectedMsgs :=
    match vr, d with
    | vround sn rn, TTCdecision_decided c => map (fun r => send_decided r (prop sn c)) nreps
    | vround sn rn, TTCdecision_retry c => [send_retry slf (ballot (incVotingRound vr) c)]
    end.

  (* NOTE: it would be better if the state machine construct would take care of the option *)
  Definition TTCquorum_upd (slf : name) (vr : VotingRound) : Update TTCquorumState (option Vote) DirectedMsgs :=
    fun state vop =>
      match state, vop with
      | (cmds, names), Some v =>
        if new_vote v vr names
        then
          let c      := vote2cmd v in
          let cmds'  := c :: cmds in
          let names' := vote2sender v :: names in
          match TTCconsensus vr cmds c with
          | Some dec => (None, decision2msgs slf vr dec)
          | None => (Some (cmds', names'), [])
          end
        else (Some state, [])
      | _, _ => (Some state, [])
      end.

  (*
  Definition TTCQuorum0 (vr : VotingRound) : NMStateMachine TTCquorumState :=
    fun slf => mkSM (TTCquorum_upd slf vr) ([], []).
*)

  Definition TTCQuorum (vr : VotingRound) : NMStateMachine _ :=
    fun slf =>
      state_machineSM
        (TTCquorum_upd slf vr)
        ([],[])
        TTCreceiveVote.

  Definition TTCround (b : Ballot) : NMStateMachine _ :=
    SendId (fun slf =>
              match slf with
              | TTCreplica n => map (fun r => send_vote r (vote b n)) nreps
              | _ => []
              end)
    [||] TTCQuorum (ballot2votingRound b).

  Definition new_rounds_upd (s : SlotNum) : SUpdate RoundNum (option Ballot) (list Ballot) :=
    fun state bop =>
      match state, s, bop with
      | rnum r, snum n, Some (ballot (vround (snum n') (rnum r')) cmd as b) =>
        if deq_nat n n'
        then
          if lt_dec r r'
          then (rnum r', [b])
          else (state, [])
        else (state, [])
      | _, _, None => (state, [])
      end.

  Definition TTCnewRounds (s : SlotNum) : StateMachine _ TTCmsg (list Ballot) :=
    simple_state_machineSM
      (new_rounds_upd s)
      (rnum 0)
      TTCroundInfo.

  (* ??? *)
  Definition TTCrounds (p : Proposal) : NMStateMachine _ :=
    TTCround (proposal2ballot p (rnum 0))
    [||] ((fun _ => TTCnewRounds (proposal2slot p)) [>>=] TTCround).
  (* why can't I use the coercion up here? *)

  Definition receive_decided (m : TTCmsg) : option Proposal :=
    match m with
    | TTCpropose p => None
    | TTCnotify _  => None
    | TTCvote _    => None
    | TTCdecided p => Some p
    | TTCretry _   => None
    end.

  Definition TTCreceiveDecided : StateMachine _ TTCmsg (option Proposal) :=
    mkSSM (fun state m => (state, receive_decided m)) tt.

  Definition TTCsendNotify : MStateMachine _ :=
    mapSM
      (fun pop =>
         match pop with
         | Some p => map (fun c => send_notify c p) nclients
         | None => []
         end)
      TTCreceiveDecided.

  Definition TTCvoter (p : Proposal) : NMStateMachine _ :=
    TTCrounds p [until-send] TTCsendNotify.

  Definition TTCreplicaSM : NMStateMachine _ :=
    (fun _ => TTCnewVoters) [>>=] TTCvoter.

  (* Got that from [Check TTCreplicaSM] *)
  Definition TTCreplicaState : Set :=
    bindState
      (list_with_missing * unit)
      Proposal
      (pstate
         (pstate
            (pstate unit (TTCquorumState * unit))
            (bindState (RoundNum * unit) Ballot (pstate unit (TTCquorumState * unit))))
         unit).

  Definition TTCstate (n : name) :=
    match n with
    | TTCreplica _ => TTCreplicaState
    | _ => unit
    end.

  Definition TTCsys : MUSystem TTCstate :=
    fun name =>
      match name return StateMachine (TTCstate name) msg DirectedMsgs with
      | TTCreplica n => TTCreplicaSM name
      | _ => MhaltedSM tt
      end.

  Instance TTC_I_Key : Key := MkKey unit unit.

  Instance TTC_I_Data : Data := MkData TTCmsg.

  Instance TTC_I_AuthTok : AuthTok := MkAuthTok unit Deq_unit.

  Instance TTC_I_AuthFun : AuthFun :=
    MkAuthFun
      (fun _ _ => [tt])
      (fun _ _ _ _ => true).

  Definition nat_n_3Fp1_0 : nat_n (3 * F + 1).
  Proof.
    exists 0.
    apply leb_correct.
    omega.
  Defined.

  Definition replica0 : Rep := bij_inv reps_bij nat_n_3Fp1_0.

  Definition TTCdata_auth : name -> msg -> option name :=
    fun n m =>
      match m with (* NOTE: some of these are wrong *)
      | TTCpropose p => None                              (* propose messages come from clients---This is wrong, in the sense that it doesn't necessarily come from client 0 but could be coming from another client *)
      | TTCnotify _  => Some (TTCreplica replica0)        (* notify messages come from replicas---This is wrong! *)
      | TTCvote v    => Some (TTCreplica (vote2sender v)) (* vote come from replicas *)
      | TTCdecided _ => Some n                            (* decided messages are local *)
      | TTCretry _   => Some n                            (* retry messages are local *)
      end.

  Instance TTC_I_DataAuth : DataAuth :=  MkDataAuth TTCdata_auth.

  Instance TTC_I_ContainedAuthData : ContainedAuthData :=
    MkContainedAuthData
      (fun m => [MkAuthData m [tt]]) (* tt here says that the data is authenticated *)
  (*             (fun a => match a with | MkAuthData m _ => m end)*).

  Definition TTChold_keys (eo : EventOrdering) : Prop :=
    forall (e : Event),
      match loc e with
      | TTCreplica n => forall m, has_receiving_key (keys e) (TTCreplica m)
      | _ => True
      end.

  Definition TTCall_not_byz (eo : EventOrdering) :=
    forall (e : Event) r, loc e = TTCreplica r -> ~isByz e.

  Arguments bind_state [SX] [T] [SY] _ _.

  Lemma TTCreceivedProposal_output_iff :
    forall (eo : EventOrdering) (e : Event) p,
      output_sm_on_event TTCreceivedProposal e = Some (Some p)
      <->
      (
        trigger e = TTCpropose p
        \/
        exists v, p = vote2proposal v /\ trigger e = TTCvote v
      ).
  Proof.
    introv; split; intro h.

    - rewrite output_sm_on_event_unroll in h.
      destruct (dec_isFirst e) as [d|d]; simpl in *; ginv.

      + inversion h as [z]; clear h.
        unfold received_proposal in *.
        destruct (trigger e); ginv; auto.
        right.
        eexists; dands; eauto.

      + match goal with
        | [ H : context[option_map _ ?sop] |- _ ] => destruct sop
        end; simpl in *; ginv.
        inversion h as [z]; clear h.
        unfold received_proposal in *.
        destruct (trigger e); ginv; auto.
        right.
        eexists; dands; eauto.

    - rewrite output_sm_on_event_unroll.
      repndors; exrepnd; subst; destruct (dec_isFirst e); allrw; simpl in *; auto;
        match goal with
        | [ |- context[option_map _ ?x] ] => remember x as sop
        end; destruct sop; symmetry in Heqsop; simpl in *; ginv;
          assert False; tcsp; unfold TTCreceivedProposal in Heqsop;
            match goal with
            | [ H : context[state_sm_on_event (mkSSM ?u ?i) ?e] |- _ ] =>
              pose proof (state_sm_on_event_mkSSM e u i) as xx
            end; simpl in xx; apply xx in Heqsop; auto.
  Qed.

  Lemma add_to_list_with_missing_if_not_new_some_implies :
    forall n lwm lwm',
      valid_list_with_missing lwm
      -> add_to_list_with_missing_if_not_in n lwm = Some lwm'
      ->
      (
        ~ in_list_with_missing n lwm
        /\
        in_list_with_missing n lwm'
        /\
        valid_list_with_missing lwm'
      ).
  Proof.
    introv valid a.
    unfold add_to_list_with_missing_if_not_in, in_list_with_missing in *.
    destruct lwm, lwm'; simpl in *.
    repeat (dest_cases w; simpl); ginv; tcsp.

    - dands; tcsp.

      + intro xx; omega.

      + rewrite in_app_iff.
        intro xx; repndors.

        * apply valid in xx; omega.

        * apply in_seq in xx; destruct xx as [yy zz]; simpl in *; omega.

      + introv i.
        apply in_app_iff in i; repndors; tcsp.

        * apply valid in i; omega.

        * apply in_seq in i; destruct i as [yy zz]; simpl in *; omega.

    - dands; tcsp; try omega.

      + intro xx.
        apply in_remove_elt in xx; repnd; omega.

      + introv j.
        apply in_remove_elt in j; repnd.
        apply valid in j0; try omega.
  Qed.

  Lemma add_new_proposal_some_implies :
    forall p lwm lwm',
      valid_list_with_missing lwm
      -> add_new_proposal p lwm = Some lwm'
      ->
      (
        ~ in_list_with_missing (proposal2slot p) lwm
        /\
        in_list_with_missing (proposal2slot p) lwm'
        /\
        valid_list_with_missing lwm'
      ).
  Proof.
    introv valid a.
    unfold add_new_proposal in a.
    apply add_to_list_with_missing_if_not_new_some_implies in a; auto.
  Qed.

  Lemma add_to_list_with_missing_if_not_in_none_implies :
    forall n lwm,
      valid_list_with_missing lwm
      -> add_to_list_with_missing_if_not_in n lwm = None
      -> in_list_with_missing n lwm.
  Proof.
    introv valid a.

    unfold add_to_list_with_missing_if_not_in, in_list_with_missing in *.
    destruct lwm; simpl in *.
    repeat (dest_cases w; simpl); ginv; tcsp.

    dands; auto; try omega.
  Qed.

  Lemma add_new_proposal_none_implies :
    forall p lwm,
      valid_list_with_missing lwm
      -> add_new_proposal p lwm = None
      -> in_list_with_missing (proposal2slot p) lwm.
  Proof.
    introv valid a.

    unfold add_new_proposal in a.
    destruct p, sn; simpl in *.
    apply add_to_list_with_missing_if_not_in_none_implies in a; auto.
  Qed.

  Lemma TTCnewVotersOpt_valid_list_with_missing :
    forall (eo : EventOrdering) (e : Event) lwm,
      SM_state_before_event TTCnewVotersOpt e lwm
      -> valid_list_with_missing lwm.
  Proof.
    intro eo; induction e as [e ind] using HappenedBeforeInd; introv sm.
    unfold SM_state_before_event in *.
    dest_cases sop; symmetry in Heqsop; destruct sop; subst.
    rewrite state_sm_before_event_unroll in Heqsop.
    destruct (dec_isFirst e) as [d|d]; ginv; simpl in *; tcsp.

    remember (@state_sm_before_event
                TTC_I_Node TTC_I_Key TTC_I_Msg
                (prod list_with_missing unit) (option Proposal)
                TTCnewVotersOpt
                eo
                (local_pred e)) as sop'.
    destruct sop'; symmetry in Heqsop'; simpl in *; ginv.
    destruct p; simpl in *.

    pose proof (ind (local_pred e)) as q; clear ind.
    autodimp q hyp; eauto 3 with eo.
    pose proof (q l) as h; clear q.
    rewrite Heqsop' in h; autodimp h hyp.
    unfold new_voters_upd in Heqsop; simpl in *.
    unfold received_proposal in Heqsop.
    remember (trigger (local_pred e)) as tr; destruct tr; simpl in *; ginv.

    - dest_cases w; simpl in *; ginv.
      dest_cases y; ginv; symmetry in Heqy.
      apply add_new_proposal_some_implies in Heqy; tcsp.

    - dest_cases w; simpl in *; ginv.
      dest_cases y; ginv; symmetry in Heqy.
      apply add_new_proposal_some_implies in Heqy; tcsp.
  Qed.


  Lemma add_to_list_with_missing_if_not_not_in_some_implies_add_to_list_with_missing :
    forall n lwm lwm',
      add_to_list_with_missing_if_not_in n lwm = Some lwm'
      -> lwm' = add_to_list_with_missing n lwm.
  Proof.
    introv; destruct lwm; simpl.
    repeat dest_cases w; introv h; ginv; auto.
  Qed.

  Lemma add_new_proposal_some_implies_add_proposal :
    forall p lwm lwm',
      add_new_proposal p lwm = Some lwm'
      -> lwm' = add_proposal p lwm.
  Proof.
    introv.
    unfold add_new_proposal, add_proposal; simpl.
    apply add_to_list_with_missing_if_not_not_in_some_implies_add_to_list_with_missing.
  Qed.

  Lemma add_to_list_with_missing_if_not_not_in_none_implies_add_to_list_with_missing :
    forall n lwm,
      add_to_list_with_missing_if_not_in n lwm = None
      -> lwm = add_to_list_with_missing n lwm.
  Proof.
    introv; destruct lwm; simpl.
    repeat dest_cases w; introv h; ginv; auto.
  Qed.

  Lemma add_new_proposal_none_implies_add_proposal :
    forall p lwm,
      add_new_proposal p lwm = None
      -> lwm = add_proposal p lwm.
  Proof.
    introv.
    unfold add_new_proposal, add_proposal; simpl.
    apply add_to_list_with_missing_if_not_not_in_none_implies_add_to_list_with_missing.
  Qed.

  Lemma SM_state_before_event_implies_TTCnewVotersOpt_not_in_implies :
    forall (eo : EventOrdering) (e : Event) lwm p,
      SM_state_before_event TTCnewVotersOpt e lwm
      -> valid_list_with_missing lwm
      -> output_sm_on_event TTCreceivedProposal e = Some (Some p)
      -> ~ in_list_with_missing (proposal2slot p) lwm
      -> SM_state_on_event TTCnewVotersOpt e (add_proposal p lwm).
  Proof.
    introv sm valid out ni.

    apply TTCreceivedProposal_output_iff in out.

    apply SM_state_before_event_implies_exists in sm; exrepnd.
    unfold SM_state_on_event.
    rewrite state_sm_on_event_unroll.
    destruct (dec_isFirst e) as [d|d]; simpl in *.

    - rewrite state_sm_before_event_unroll in sm0.
      destruct (dec_isFirst e); tcsp; GC; ginv; simpl in *.
      remember (trigger e) as tr; destruct tr; tcsp; simpl in *;
        repndors; exrepnd; ginv; tcsp;
          dest_cases w; simpl in *.

    - rewrite <- state_sm_before_event_as_state_sm_on_event_pred; auto.
      rewrite sm0; simpl.
      unfold new_voters_upd.
      repndors; exrepnd; allrw; simpl.

      + dest_cases w; symmetry in Heqw; simpl in *; ginv; tcsp.
        dest_cases y; symmetry in Heqy; simpl in *; ginv; tcsp.

        * apply add_new_proposal_some_implies_add_proposal in Heqy; auto.

        * apply add_new_proposal_none_implies_add_proposal in Heqy; auto.

      + dest_cases w; symmetry in Heqw; simpl in *; ginv; tcsp.
        dest_cases y; symmetry in Heqy; simpl in *; ginv; tcsp.

        * apply add_new_proposal_some_implies_add_proposal in Heqy; auto.

        * apply add_new_proposal_none_implies_add_proposal in Heqy; auto.
  Qed.

  Lemma TTCnewVoters_output_iff :
    forall (eo : EventOrdering) e (p : Proposal),
      In p (loutput_sm_on_event TTCnewVoters e)
      <->
      exists lwm,
        SM_state_before_event TTCnewVotersOpt e lwm
        /\ valid_list_with_missing lwm
        /\ ~ in_list_with_missing (proposal2slot p) lwm
        /\
        (
          trigger e = TTCpropose p
          \/
          exists v, p = vote2proposal v /\ trigger e = TTCvote v
        ).
  Proof.
    introv; split; intro h.

    - unfold TTCnewVoters in h; simpl in h.
      unfold loutput_sm_on_event in h.

      pose proof (mapSM_output_iff opt2list TTCnewVotersOpt eo e) as q;
        simpl in q; rewrite q in h; clear q.
      apply in_olist2list_option_map_opt2list in h.

      unfold TTCnewVotersOpt in h.
      rewrite simple_state_machineSM_output_iff in h; exrepnd.
      unfold new_voters_upd in h1.
      destruct t; simpl in *; ginv.
      dest_cases w; symmetry in Heqw; ginv; simpl in *.
      fold TTCnewVotersOpt in *.
      applydup TTCnewVotersOpt_valid_list_with_missing in h2.

      apply add_new_proposal_some_implies in Heqw; repnd; auto.

      exists s; dands; auto.
      apply TTCreceivedProposal_output_iff in h0; auto.

    - exrepnd.
      unfold TTCnewVoters.
      unfold loutput_sm_on_event.

      pose proof (mapSM_output_iff opt2list TTCnewVotersOpt eo e) as q;
        simpl in q; rewrite q; clear q.

      apply in_olist2list_option_map_opt2list.
      unfold TTCnewVotersOpt.
      rewrite simple_state_machineSM_output_iff.
      exists (Some p) lwm; dands; auto.

      { apply TTCreceivedProposal_output_iff; auto. }

      { unfold new_voters_upd.
        dest_cases w; symmetry in Heqw; simpl in *.
        apply add_new_proposal_none_implies in Heqw; tcsp. }
  Qed.

  Lemma fold_TTCQuorum :
    forall slf vr,
      state_machineSM
        (TTCquorum_upd slf vr)
        ([], [])
        TTCreceiveVote
      = TTCQuorum vr slf.
  Proof.
    tcsp.
  Qed.

  Lemma output_sm_on_event_TTCreceiveVote_iff :
    forall (eo : EventOrdering) (e : Event) v,
      output_sm_on_event TTCreceiveVote e = Some (Some v)
      <-> trigger e = TTCvote v.
  Proof.
    introv; unfold TTCreceiveVote.
    rewrite output_sm_on_event_unroll.
    destruct (dec_isFirst e) as [d|d]; simpl in *; ginv; split; intro h; ginv.

    - inversion h as [z]; clear h.
      destruct (trigger e); ginv; auto.

    - allrw; simpl; auto.

    - match goal with
      | [ H : context[option_map _ ?sop] |- _ ] => destruct sop
      end; simpl in *; ginv.
      inversion h as [z]; clear h.
      destruct (trigger e); ginv; auto.

    - allrw; simpl.
      match goal with
      | [ |- context[option_map _ ?x] ] => remember x as sop
      end; destruct sop; symmetry in Heqsop; simpl in *; ginv.
      assert False; tcsp.
      match goal with
      | [ H : context[state_sm_on_event (mkSSM ?u ?i) ?e] |- _ ] =>
        pose proof (state_sm_on_event_mkSSM e u i) as xx
      end; simpl in xx; apply xx in Heqsop; auto.
  Qed.

  Lemma output_sm_on_event_TTCreceiveDecided_iff :
    forall (eo : EventOrdering) (e : Event) v,
      output_sm_on_event TTCreceiveDecided e = Some (Some v)
      <-> trigger e = TTCdecided v.
  Proof.
    introv; unfold TTCreceiveDecided.
    rewrite output_sm_on_event_unroll.
    destruct (dec_isFirst e) as [d|d]; simpl in *; ginv; split; intro h; ginv.

    - inversion h as [z]; clear h.
      destruct (trigger e); ginv; auto.

    - allrw; simpl; auto.

    - match goal with
      | [ H : context[option_map _ ?sop] |- _ ] => destruct sop
      end; simpl in *; ginv.
      inversion h as [z]; clear h.
      destruct (trigger e); ginv; auto.

    - allrw; simpl.
      match goal with
      | [ |- context[option_map _ ?x] ] => remember x as sop
      end; destruct sop; symmetry in Heqsop; simpl in *; ginv.
      assert False; tcsp.
      match goal with
      | [ H : context[state_sm_on_event (mkSSM ?u ?i) ?e] |- _ ] =>
        pose proof (state_sm_on_event_mkSSM e u i) as xx
      end; simpl in xx; apply xx in Heqsop; auto.
  Qed.

  Lemma fold_TTCnewRounds :
    forall s,
      simple_state_machineSM (new_rounds_upd s) (rnum 0) TTCroundInfo
      = TTCnewRounds s.
  Proof.
    sp.
  Qed.

  Lemma output_sm_on_event_TTCroundInfo_iff :
    forall (eo : EventOrdering) (e : Event) b,
      output_sm_on_event TTCroundInfo e = Some (Some b)
      <->
      (
        trigger e = TTCretry b
        \/
        exists v, trigger e = TTCvote v /\ b = vote2ballot v
      ).
  Proof.
    introv; unfold TTCroundInfo.
    rewrite output_sm_on_event_unroll.
    destruct (dec_isFirst e) as [d|d]; simpl in *; ginv; split; intro h; ginv;
      repndors; exrepnd; allrw; simpl in *; tcsp.

    - inversion h as [z]; clear h.
      unfold round_info in z.
      destruct (trigger e); ginv; tcsp.
      right; exists v; dands; auto.

    - match goal with
      | [ H : context[option_map _ ?sop] |- _ ] => destruct sop
      end; simpl in *; ginv.
      inversion h as [z]; clear h.
      unfold round_info in *.
      destruct (trigger e); ginv; auto.
      right.
      exists v; dands; auto.

    - match goal with
      | [ |- context[option_map _ ?x] ] => remember x as sop
      end; destruct sop; symmetry in Heqsop; simpl in *; ginv.
      assert False; tcsp.
      match goal with
      | [ H : context[state_sm_on_event (mkSSM ?u ?i) ?e] |- _ ] =>
        pose proof (state_sm_on_event_mkSSM e u i) as xx
      end; simpl in xx; apply xx in Heqsop; auto.

    - match goal with
      | [ |- context[option_map _ ?x] ] => remember x as sop
      end; destruct sop; symmetry in Heqsop; simpl in *; ginv.
      assert False; tcsp.
      match goal with
      | [ H : context[state_sm_on_event (mkSSM ?u ?i) ?e] |- _ ] =>
        pose proof (state_sm_on_event_mkSSM e u i) as xx
      end; simpl in xx; apply xx in Heqsop; auto.
  Qed.

  Lemma subset_singleton_left :
    forall {A} (x : A) l,
      In x l -> subset [x] l.
  Proof.
    introv i j; simpl in *; repndors; subst; tcsp.
  Qed.
  Hint Resolve subset_singleton_left : list.

  Lemma in_singleton :
    forall {A} (x : A), In x [x].
  Proof.
    tcsp.
  Qed.
  Hint Resolve in_singleton : list.

  Lemma TTCsys_output_iff :
    forall (eo : EventOrdering) e m l dl,
      In (MkDMsg m l dl) (output_system_on_event_ldata TTCsys e)
      <->
      (
        (
          exists (n : Rep) (d : name) (e' : Event) (p : e' ⊑ e) (sn : SlotNum) (rn : RoundNum)
                 (cmd cmd0 : Cmd) (lwm : list_with_missing),
            m = TTCvote (vote (proposal2ballot (prop sn cmd) rn) n)
            /\ loc e = TTCreplica n
            /\ SM_state_before_event TTCnewVotersOpt e' lwm
            /\ ~ in_list_with_missing sn lwm
            /\ valid_list_with_missing lwm
            /\ @no_loutput_sm_on_event_prior_to _ _ _ _ _  TTCsendNotify (subEventOrdering e') (mkSubOrderingLe p)
            /\
            (
              trigger e' = TTCpropose (prop sn cmd0)
              \/
              exists rn' sender, trigger e' = TTCvote (vote (ballot (vround sn rn') cmd0) sender)
            )
            /\
            (
              (e' = e /\ rn = rnum 0 /\ cmd0 = cmd)
              \/
              exists (r0 : RoundNum),
                r0 < rn
                /\
                @SM_state_before_event _ _ _ _ _ _ (TTCnewRounds sn) (subEventOrdering e') (mkSubOrderingLe p) r0
                /\
                (
                  trigger e = TTCretry (ballot (vround sn rn) cmd)
                  \/
                  exists v,
                    trigger e = TTCvote v /\
                    ballot (vround sn rn) cmd = vote2ballot v
                )
            )
            /\ l = [d]
            /\ dl = 0
            /\ In d nreps
        )

        \/

        (
          exists (n : Rep) (d : name) (e' : Event) (p : e' ⊑ e) (sn : SlotNum) (rn : RoundNum)
                 (cmd0 : Cmd) (lwm : list_with_missing) (cmd : Cmd) (sender : Rep)
                 (cmds : list Cmd) (names : list Rep) (c : Cmd)
                 (e'' : subEventOrdering_type e') (p' : e'' ⊑ e),
            m = TTCdecided (prop sn c)
            /\ loc e = TTCreplica n
            /\ SM_state_before_event TTCnewVotersOpt e' lwm
            /\ ~ in_list_with_missing sn lwm
            /\ valid_list_with_missing lwm
            /\
            (
              trigger e' = TTCpropose (prop sn cmd0)
              \/
              exists v, prop sn cmd0 = vote2proposal v /\ trigger e' = TTCvote v
            )
            /\ @no_loutput_sm_on_event_prior_to _ _ _ _ _ TTCsendNotify (subEventOrdering e') (mkSubOrderingLe p)
            /\ @SM_state_before_event _ _ _ _ _ _ (TTCQuorum (vround sn rn) (TTCreplica n)) (subEventOrdering e'') (mkSubOrderingLe p') (cmds, names)
            /\ trigger e = TTCvote (vote (ballot (vround sn rn) cmd) sender)
            /\ ~ In sender names
            /\ length cmds = 2 * F
            /\ poss_maj cmddeq cmds cmd = ((2 * F) + 1, c)
            /\ l = [d]
            /\ dl = 0
            /\ In d nreps
            /\
            (
              (rn = rnum 0 /\ sub_eo_event e' e'' = e')
              \/
              exists (rn0 : RoundNum) (cmd0 : Cmd),
                (
                  subEventOrdering_trigger e' e'' = TTCretry (ballot (vround sn rn) cmd0)
                  \/
                  exists v,
                    subEventOrdering_trigger e' e'' = TTCvote v
                    /\ ballot (vround sn rn) cmd0 = vote2ballot v
                )
                /\ rn0 < rn
                /\ @SM_state_before_event _ _ _ _ _ _ (TTCnewRounds sn) (subEventOrdering e') e'' rn0
                /\ trigger e = TTCvote (vote (ballot (vround sn rn) cmd) sender)
            )
        )

        \/

        (
          exists (n : Rep) (e' : Event) (p : e' ⊑ e) (sn : SlotNum) (rn : RoundNum)
                 (cmd0 : Cmd) (lwm : list_with_missing) (cmd : Cmd) (sender : Rep)
                 (cmds : list Cmd) (names : list Rep) (k : nat) (c : Cmd)
                 (e'' : subEventOrdering_type e') (p' : e'' ⊑ e),
            m = TTCretry (ballot (vround sn (rnum (S rn))) c)
            /\ l = [loc e]
            /\ dl = 0
            /\ loc e = TTCreplica n
            /\ SM_state_before_event TTCnewVotersOpt e' lwm
            /\ ~ in_list_with_missing sn lwm
            /\ valid_list_with_missing lwm
            /\
            (
              trigger e' = TTCpropose (prop sn cmd0)
              \/
              exists v, prop sn cmd0 = vote2proposal v /\ trigger e' = TTCvote v
            )
            /\ @no_loutput_sm_on_event_prior_to _ _ _ _ _ TTCsendNotify (subEventOrdering e') (mkSubOrderingLe p)
            /\ @SM_state_before_event _ _ _ _ _ _ (TTCQuorum (vround sn rn) (TTCreplica n)) (subEventOrdering e'') (mkSubOrderingLe p') (cmds, names)
            /\ trigger e = TTCvote (vote (ballot (vround sn rn) cmd) sender)
            /\ ~ In sender names
            /\ length cmds = F + (F + 0)
            /\ poss_maj cmddeq cmds cmd = (k, c)
            /\ k <> (2 * F) + 1
            /\
            (
              (rn = rnum 0 /\ sub_eo_event e' e'' = e')
              \/
              exists (rn0 : RoundNum) (cmd0 : Cmd),
                (
                  subEventOrdering_trigger e' e'' = TTCretry (ballot (vround sn rn) cmd0)
                  \/
                  exists v,
                    subEventOrdering_trigger e' e'' = TTCvote v
                    /\ ballot (vround sn rn) cmd0 = vote2ballot v
                )
                /\ rn0 < rn
                /\ @SM_state_before_event _ _ _ _ _ _ (TTCnewRounds sn) (subEventOrdering e') e'' rn0
                /\ trigger e = TTCvote (vote (ballot (vround sn rn) cmd) sender)
            )
        )

        \/

        (
          exists (n : Rep) (d : name) (e' : Event) (p : e' ⊑ e) (p1 p2 : Proposal)
                 (lwm : list_with_missing),
            m = TTCnotify p2
            /\loc e = TTCreplica n
            /\ SM_state_before_event TTCnewVotersOpt e' lwm
            /\ ~ in_list_with_missing (proposal2slot p1) lwm
            /\ valid_list_with_missing lwm
            /\
            (
              trigger e' = TTCpropose p1
              \/
              exists v, p1 = vote2proposal v /\ trigger e' = TTCvote v
            )
            /\ @no_loutput_sm_on_event_prior_to _ _ _ _ _ TTCsendNotify (subEventOrdering e') (mkSubOrderingLe p)
            /\ trigger e = TTCdecided p2
            /\ @state_sm_before_event_exists _ _ _ _ _ (TTCrounds p1 (TTCreplica n)) (subEventOrdering e') (mkSubOrderingLe p)
            /\ l = [d]
            /\ dl = 0
            /\ In d nclients
        )
      ).
  Proof.
    introv.
    rewrite in_output_system_on_event_ldata.
    split; intro h.

    - unfold TTCsys in h.
      remember (loc e) as n; destruct n; simpl in *;
        unfold MStateMachine in *; ginv.

      + unfold TTCreplicaSM in h; simpl in h.
        unfold nbind in h; simpl in h.

        (* QUESTION: Why doesnt' apply work?? *)
        pose proof (output_bind_iff
                      TTCnewVoters
                      (fun t : Proposal => TTCvoter t (TTCreplica n))
                      eo e
                      (MkDMsg m l dl)) as q; apply q in h; clear q.
        exrepnd.

        apply TTCnewVoters_output_iff in h1; exrepnd.

        unfold TTCvoter in h0.
        unfold nUntilSend in h0.

        apply UntilSend_output_iff in h0.
        repnd.

        destruct h0 as [h0|h0]; repnd;[|].

        * unfold TTCrounds in h0; simpl in *.
          unfold nparallel in h0; simpl in h0.
          rewrite parallel_output_iff in h0.

          destruct h0 as [h0|h0].

          {
            unfold TTCround in h0; simpl in h0.
            unfold nparallel in h0; simpl in h0.
            rewrite parallel_output_iff in h0.

            destruct h0 as [h0|h0]; repnd; [|].

            - apply SendId_list_output_iff in h0; repnd.
              apply in_map_iff in h6; exrepnd; simpl in *.
              unfold send_vote in h6; ginv.

              apply isFirst_mkSubOrderingLe in h0; subst.

              destruct t.
              left.
              exists n x e p sn (rnum 0) cmd cmd lwm; simpl.
              dands; auto; eauto 3 with list.

              repndors; exrepnd; tcsp.
              right.
              destruct v; simpl in *.
              destruct b; simpl in *.
              destruct vr; simpl in *; ginv.
              exists rn sender; auto.

            - unfold TTCQuorum in h0.
              rewrite state_machineSM_list_output_iff in h0; exrepnd.
              allrw fold_TTCQuorum.

              unfold TTCquorum_upd in h0.
              destruct s as [cmds names].
              destruct t0 as [|v]; simpl in *; ginv; tcsp;[].
              unfold new_vote in h0.
              destruct v.
              destruct b.

              apply output_sm_on_event_TTCreceiveVote_iff in h6.

              destruct (VotingRoundDeq (ballot2votingRound (proposal2ballot t (rnum 0))) vr);
                subst; simpl in *; tcsp;[].

              destruct (in_dec rep_deq sender names); simpl in *; tcsp;[].
              destruct t; simpl in *.
              unfold TTCconsensus in h0.
              dest_cases w.
              dest_cases y; symmetry in Heqy.
              dest_cases z; subst; simpl in *; tcsp.

              + apply in_map_iff in h0; exrepnd.
                unfold send_decided in h0; ginv.

                right; left.
                exists n x e' p sn (rnum 0) cmd0 lwm cmd sender.
                exists cmds names y1.
                exists (mkSubOrderingLe (localHappenedBeforeLe_refl e')) p.
                dands; auto; eauto 3 with list.

              + destruct h0 as [h0|h0]; tcsp.
                unfold send_retry in h0; ginv.

                right; right; left.
                exists n e' p sn (rnum 0) cmd0 lwm cmd sender.
                exists cmds names y0 y1.
                exists (mkSubOrderingLe (localHappenedBeforeLe_refl e')) p.
                dands; auto; eauto 3 with list.
          }

          {
            unfold nbind in h0; simpl in h0.
            rewrite output_bind_iff in h0.
            exrepnd.

            unfold TTCnewRounds in h0.
            rewrite simple_state_machineSM_list_output_iff in h0.
            exrepnd.
            allrw fold_TTCnewRounds.

            destruct s; simpl in *.
            destruct t; simpl in *.
            destruct sn; simpl in *.
            destruct t1; simpl in *; ginv; tcsp;[].
            destruct b; simpl in *.
            destruct vr; simpl in *.
            destruct sn; simpl in *.
            destruct rn; simpl in *.
            dest_cases w; subst; simpl in *;[].
            dest_cases w; subst; simpl in *;[].
            destruct h0 as [h0|h0]; tcsp; subst; simpl in *.

            apply output_sm_on_event_TTCroundInfo_iff in h7.

            unfold TTCround in h6; simpl in *.
            unfold nparallel in h6; simpl in *.
            rewrite parallel_output_iff in h6.

            destruct h6 as [h6|h6].

            - apply SendId_list_output_iff in h6; repnd.
              apply in_map_iff in h0; exrepnd; simpl in *.
              unfold send_vote in h0; ginv.

              apply isFirst_mkSubOrderingLe in h6; subst.
              simpl in *.
              clear p0.

              left.
              exists n x e' p (snum n2) (rnum n3) cmd0 cmd lwm.
              dands; auto; eauto 3 with list.

              {
                destruct h2 as [h2|h2]; tcsp.
                exrepnd; right.
                destruct v; simpl in *; ginv.
                destruct b; simpl in *; ginv.
                destruct vr; simpl in *; ginv.
                allrw.
                exists rn sender; auto.
              }

              {
                right.
                exists (rnum n0).
                dands; auto.
              }

            - unfold TTCQuorum in h6.
              rewrite state_machineSM_list_output_iff in h6; exrepnd.
              allrw fold_TTCQuorum.

              unfold TTCquorum_upd in h6.
              destruct s as [cmds names].
              destruct t as [|v]; simpl in *; ginv; tcsp;[].
              unfold new_vote in h4.
              destruct v.
              destruct b.

              apply output_sm_on_event_TTCreceiveVote_iff in h0; simpl in *.

              destruct (VotingRoundDeq (vround (snum n2) (rnum n3)) vr);
                subst; simpl in *; tcsp;[].

              destruct (in_dec rep_deq sender names); simpl in *; tcsp;[].
              unfold TTCconsensus in h6; simpl in *.
              dest_cases w.
              dest_cases y; symmetry in Heqy.
              dest_cases z; subst; simpl in *; tcsp;[|].

              + apply in_map_iff in h6; exrepnd.
                unfold send_decided in h6; ginv; simpl in *.

                assert (e'0 ⊑ e) as q.
                { dup p0 as xx; apply localHappenedBeforeLe_subEventOrdering_implies in xx; simpl in xx; auto. }

                right; left.
                exists n x e' p (snum n2) (rnum n3) cmd lwm cmd1 sender.
                exists cmds names y1.
                exists e'0 q.
                dands; simpl in *; auto; eauto 3 with list;[|].

                {
                  apply SM_state_before_event_sub_sub_so_as_sub_eo in h9.
                  { erewrite sub_sub_event2sub_event_mkSubEventOrderingLe in h9;exact h9. }
                  simpl in *; auto.
                  apply localLe_implies_loc in q; auto.
                }

                {
                  right.
                  exists (rnum n0) cmd0; dands; auto.
                }

              + destruct h6 as [h6|h6]; tcsp.
                unfold send_retry in h6; ginv.

                assert (e'0 ⊑ e) as q.
                { dup p0 as xx; apply localHappenedBeforeLe_subEventOrdering_implies in xx; simpl in xx; auto. }

                right; right; left.
                exists n e' p (snum n2) (rnum n3) cmd lwm cmd1 sender.
                exists cmds names y0 y1.
                exists e'0 q.
                dands; auto; eauto 3 with list;[|].

                {
                  apply SM_state_before_event_sub_sub_so_as_sub_eo in h9.
                  { erewrite sub_sub_event2sub_event_mkSubEventOrderingLe in h9;exact h9. }
                  simpl in *; auto.
                  apply localLe_implies_loc in q; auto.
                }

                {
                  right.
                  exists (rnum n0) cmd0; dands; auto.
                }
          }

        * unfold TTCsendNotify in h6; simpl in h6.
          (* QUESTION: why is that not happening automatically *)
          unfold MStateMachinetoNStateMachine in h6; simpl in h6.
          rewrite mapSM_list_output_iff in h6.
          apply in_olist2list in h6; exrepnd.
          apply option_map_Some in h6; exrepnd; subst.
          destruct a; simpl in *; tcsp;[].
          apply in_map_iff in h7; exrepnd.
          unfold send_notify in h7; ginv.
          apply output_sm_on_event_TTCreceiveDecided_iff in h6.
          autorewrite with eo proc in *.

          right; right; right.
          exists n x e' p t p0 lwm.
          dands; auto; eauto 3 with list.

      + apply MhaltedSM_output in h; tcsp.

    - unfold TTCsys.
      remember (loc e) as n; destruct n; simpl in *;
        unfold MStateMachine in *; ginv;
          [|repndors; exrepnd;
            assert (TTCclient n = TTCreplica n0) as xx by (allrw; auto);
            inversion xx];[].

      unfold TTCreplicaSM; simpl.
      unfold nbind; simpl.

      pose proof (output_bind_iff
                    TTCnewVoters
                    (fun t : Proposal => TTCvoter t (TTCreplica n))
                    eo e
                    (MkDMsg m l dl)) as q; apply q; clear q.

      repndors; exrepnd; ginv.

      + exists e' p (prop sn cmd0).
        rewrite TTCnewVoters_output_iff.
        dands.

        * exists lwm.
          dands; auto.
          destruct h7 as [h7|h7]; tcsp.
          exrepnd; right.
          allrw; simpl.
          eexists;dands;[|eauto]; simpl; auto.

        * unfold TTCvoter; simpl.
          unfold nUntilSend; simpl.
          rewrite UntilSend_output_iff; simpl.

          dands; tcsp.

          left.
          unfold TTCrounds; simpl.
          unfold nparallel; simpl.
          rewrite parallel_output_iff; simpl.

          destruct h8 as [h8|h8];[left|right].

          {
            repnd; subst.
            unfold TTCround; simpl.
            unfold nparallel; simpl.
            rewrite parallel_output_iff; simpl.

            left.
            apply SendId_list_output_iff; simpl.
            dands; eauto with eo.
            apply in_map_iff.
            eexists;dands;[|eauto]; auto.
          }

          {
            exrepnd.
            unfold nbind; simpl.
            rewrite output_bind_iff.

            assert
              (@localHappenedBeforeLe
                 _ _ _
                 (subEventOrdering e')
                 (mkSubOrderingLe (localHappenedBeforeLe_refl e'))
                 (mkSubOrderingLe p)) as q.
            { apply localHappenedBeforeLe_subEventOrdering_iff; simpl; auto. }

            exists
              (mkSubOrderingLe p)
              (@localHappenedBeforeLe_refl _ _ _ (subEventOrdering e') (mkSubOrderingLe p))
              (ballot (vround sn rn) cmd); simpl.
            dands.

            - unfold TTCnewRounds; simpl.
              rewrite simple_state_machineSM_list_output_iff; simpl.
              allrw fold_TTCnewRounds.
              exists (Some (ballot (vround sn rn) cmd)) r0; simpl.
              dands; auto.

              + apply output_sm_on_event_TTCroundInfo_iff; simpl in *; auto.

              + destruct r0; simpl in *.
                destruct sn; simpl in *.
                destruct rn; simpl in *.
                dest_cases w.
                dest_cases w.

            - unfold TTCround; simpl.
              unfold nparallel; simpl.
              rewrite parallel_output_iff; simpl.

              left.
              apply SendId_list_output_iff; simpl.

              dands; auto.

              + apply in_map_iff; eexists; dands;[|eauto]; auto.

              + apply isFirst_mkSubOrderingLe_eq.
          }

      + exists e' p (prop sn cmd0).
        dands; auto.

        * unfold TTCnewVoters; simpl.
          rewrite mapSM_list_output_iff.
          apply in_olist2list.
          exists [prop sn cmd0]; simpl; dands; tcsp.
          apply option_map_Some.
          exists (Some (prop sn cmd0)); simpl; dands; auto.

          unfold TTCnewVotersOpt.
          rewrite simple_state_machineSM_output_iff.
          fold TTCnewVotersOpt.
          exists (Some (prop sn cmd0)) lwm; simpl.
          rewrite TTCreceivedProposal_output_iff.
          dands; auto.

          destruct sn.
          dest_cases w; symmetry in Heqw; simpl.
          apply add_to_list_with_missing_if_not_in_none_implies in Heqw; tcsp.

        * unfold TTCvoter.
          unfold nUntilSend.
          apply UntilSend_output_iff.
          dands; auto.

          left.
          unfold TTCrounds.
          unfold nparallel; simpl.
          rewrite parallel_output_iff; simpl.

          destruct h0 as [h0|h0];[left|right].

          {
            repnd.
            subst rn.
            unfold TTCround.
            unfold nparallel; simpl.
            rewrite parallel_output_iff; simpl.

            right.

            unfold TTCQuorum.
            rewrite state_machineSM_list_output_iff.
            allrw fold_TTCQuorum.

            exists (Some (vote (ballot (vround sn (rnum 0)) cmd) sender)) (cmds, names); simpl.
            rewrite output_sm_on_event_TTCreceiveVote_iff; simpl.
            allrw; dands; auto.

            - revert p' h8; rewrite h0; introv h.
              rewrite <- Heqn.

              assert (mkSubOrderingLe p = mkSubOrderingLe p') as xx;[|rewrite xx;auto];[].
              apply implies_eq_in_sub_eo; simpl; auto.

            - destruct (VotingRoundDeq (vround sn (rnum 0)) (vround sn (rnum 0))); tcsp; GC.
              destruct (in_dec rep_deq sender names); simpl; tcsp.
              unfold TTCconsensus; simpl.
              dest_cases w; simpl.
              allrw.
              dest_cases w; simpl.
              apply in_map_iff.
              eexists;dands;[|eauto]; auto.
          }

          {
            exrepnd.
            unfold nbind; simpl.
            rewrite output_bind_iff; simpl.

            assert (@localHappenedBeforeLe _ _ _ (subEventOrdering e') e'' (mkSubOrderingLe p)) as q.
            { apply localHappenedBeforeLe_subEventOrdering_iff; simpl; auto. }

            exists e'' q (ballot (vround sn rn) cmd1).
            dands.

            - unfold TTCnewRounds; simpl.
              rewrite simple_state_machineSM_list_output_iff; simpl.
              allrw fold_TTCnewRounds.
              exists (Some (ballot (vround sn rn) cmd1)) rn0; simpl.
              dands; auto.

              + apply output_sm_on_event_TTCroundInfo_iff; simpl in *; auto.

              + destruct rn0; simpl in *.
                destruct sn; simpl in *.
                destruct rn; simpl in *.
                dest_cases w.
                dest_cases w.

            - unfold TTCround; simpl.
              unfold nparallel; simpl.
              rewrite parallel_output_iff; simpl.

              right.
              unfold TTCQuorum.
              rewrite state_machineSM_list_output_iff.
              allrw fold_TTCQuorum.

              exists (Some (vote (ballot (vround sn rn) cmd) sender))
                     (cmds, names); simpl.
              rewrite output_sm_on_event_TTCreceiveVote_iff; simpl.
              allrw; dands; auto.

              + rewrite <- Heqn.
                rewrite SM_state_before_event_sub_sub_so_as_sub_eo.
                { erewrite sub_sub_event2sub_event_mkSubEventOrderingLe; exact h8. }
                simpl in *; auto.
                dup p' as xx; apply localLe_implies_loc in xx; simpl in *; auto.

              + destruct (VotingRoundDeq (vround sn rn) (vround sn rn)); tcsp; GC.
                destruct (in_dec rep_deq sender names); simpl; tcsp.
                unfold TTCconsensus; simpl.
                dest_cases w; simpl.
                allrw.
                dest_cases w; simpl.
                apply in_map_iff.
                eexists;dands;[|eauto]; auto.
          }

      + exists e' p (prop sn cmd0).
        dands; auto.

        * unfold TTCnewVoters; simpl.
          rewrite mapSM_list_output_iff.
          apply in_olist2list.
          exists [prop sn cmd0]; simpl; dands; tcsp.
          apply option_map_Some.
          exists (Some (prop sn cmd0)); simpl; dands; auto.

          unfold TTCnewVotersOpt.
          rewrite simple_state_machineSM_output_iff.
          fold TTCnewVotersOpt.
          exists (Some (prop sn cmd0)) lwm; simpl.
          rewrite TTCreceivedProposal_output_iff.
          dands; auto.

          destruct sn.
          dest_cases w; symmetry in Heqw; simpl.
          apply add_to_list_with_missing_if_not_in_none_implies in Heqw; tcsp.

        * unfold TTCvoter.
          unfold nUntilSend.
          apply UntilSend_output_iff.
          dands; auto.

          left.
          unfold TTCrounds.
          unfold nparallel; simpl.
          rewrite parallel_output_iff; simpl.

          destruct h0 as [h0|h0];[left|right].

          {
            repnd.
            subst rn.
            unfold TTCround.
            unfold nparallel; simpl.
            rewrite parallel_output_iff; simpl.

            right.

            unfold TTCQuorum.
            rewrite state_machineSM_list_output_iff.
            allrw fold_TTCQuorum.

            exists (Some (vote (ballot (vround sn (rnum 0)) cmd) sender)) (cmds, names); simpl.
            rewrite output_sm_on_event_TTCreceiveVote_iff; simpl.
            allrw; dands; auto.

            - revert p' h10; rewrite h0; introv h.
              rewrite <- Heqn.

              assert (mkSubOrderingLe p = mkSubOrderingLe p') as xx;[|rewrite xx;auto];[].
              apply implies_eq_in_sub_eo; simpl; auto.

            - destruct (VotingRoundDeq (vround sn (rnum 0)) (vround sn (rnum 0))); tcsp; GC.
              destruct (in_dec rep_deq sender names); simpl; tcsp.
              unfold TTCconsensus; simpl.
              dest_cases w; simpl.
              allrw.
              dest_cases w; simpl.
          }

          {
            exrepnd.
            unfold nbind; simpl.
            rewrite output_bind_iff; simpl.

            assert (@localHappenedBeforeLe _ _ _ (subEventOrdering e') e'' (mkSubOrderingLe p)) as q.
            { apply localHappenedBeforeLe_subEventOrdering_iff; simpl; auto. }

            exists e'' q (ballot (vround sn rn) cmd1).
            dands.

            - unfold TTCnewRounds; simpl.
              rewrite simple_state_machineSM_list_output_iff; simpl.
              allrw fold_TTCnewRounds.
              exists (Some (ballot (vround sn rn) cmd1)) rn0; simpl.
              dands; auto.

              + apply output_sm_on_event_TTCroundInfo_iff; simpl in *; auto.

              + destruct rn0; simpl in *.
                destruct sn; simpl in *.
                destruct rn; simpl in *.
                dest_cases w.
                dest_cases w.

            - unfold TTCround; simpl.
              unfold nparallel; simpl.
              rewrite parallel_output_iff; simpl.

              right.
              unfold TTCQuorum.
              rewrite state_machineSM_list_output_iff.
              allrw fold_TTCQuorum.

              exists (Some (vote (ballot (vround sn rn) cmd) sender))
                     (cmds, names); simpl.
              rewrite output_sm_on_event_TTCreceiveVote_iff; simpl.
              allrw; dands; auto.

              + rewrite <- Heqn.
                rewrite SM_state_before_event_sub_sub_so_as_sub_eo.
                { erewrite sub_sub_event2sub_event_mkSubEventOrderingLe; exact h10. }
                simpl in *; auto.
                dup p' as xx; apply localLe_implies_loc in xx; simpl in *; auto.

              + destruct (VotingRoundDeq (vround sn rn) (vround sn rn)); tcsp; GC.
                destruct (in_dec rep_deq sender names); simpl; tcsp.
                unfold TTCconsensus; simpl.
                dest_cases w; simpl.
                allrw.
                dest_cases w; simpl.
          }

      + exists e' p p1.
        dands; auto.

        * unfold TTCnewVoters; simpl.
          rewrite mapSM_list_output_iff.
          apply in_olist2list.
          exists [p1]; simpl; dands; tcsp.
          apply option_map_Some.
          exists (Some p1); simpl; dands; auto.

          unfold TTCnewVotersOpt.
          rewrite simple_state_machineSM_output_iff.
          fold TTCnewVotersOpt.
          exists (Some p1) lwm; simpl.
          rewrite TTCreceivedProposal_output_iff.
          dands; auto.

          dest_cases w; simpl in *; symmetry in Heqw.
          apply add_new_proposal_none_implies in Heqw; tcsp.

        * unfold TTCvoter.
          unfold nUntilSend.
          apply UntilSend_output_iff.
          dands; auto.

          right.
          dands; auto.

          unfold TTCsendNotify; simpl.
          (* QUESTION: why is that not happening automatically *)
          unfold MStateMachinetoNStateMachine; simpl.
          rewrite mapSM_list_output_iff.
          apply in_olist2list.
          exists (map (fun c : TTCnode => send_notify c p2) nclients); simpl; dands; tcsp;[|].

          {
            apply option_map_Some; simpl.
            exists (Some p2); simpl; dands; tcsp.
            apply output_sm_on_event_TTCreceiveDecided_iff.
            rewrite trigger_mkSubOrderingLe; auto.
          }

          {
            apply in_map_iff; eexists; dands; eauto; tcsp.
          }
  Qed.

  Lemma TTCvote_iff :
    forall (eo : EventOrdering) e l dl v,
      In (MkDMsg (TTCvote v) l dl) (output_system_on_event_ldata TTCsys e)
      <->
      exists (n : Rep) (d : name) (e' : Event) (p : e' ⊑ e) (sn : SlotNum) (rn : RoundNum)
             (cmd cmd0 : Cmd) (lwm : list_with_missing),
        v = vote (proposal2ballot (prop sn cmd) rn) n
        /\ loc e = TTCreplica n
        /\ SM_state_before_event TTCnewVotersOpt e' lwm
        /\ ~ in_list_with_missing sn lwm
        /\ valid_list_with_missing lwm
        /\ @no_loutput_sm_on_event_prior_to _ _ _ _ _ TTCsendNotify (subEventOrdering e') (mkSubOrderingLe p)
        /\
        (
          trigger e' = TTCpropose (prop sn cmd0)
          \/
          (exists rn' sender, trigger e' = TTCvote (vote (ballot (vround sn rn') cmd0) sender))
        )
        /\
        (
          (e' = e /\ rn = rnum 0 /\ cmd0 = cmd)
          \/
          (
            exists (r0 : RoundNum),
              r0 < rn
              /\
              @SM_state_before_event _ _ _ _ _ _ (TTCnewRounds sn) (subEventOrdering e') (mkSubOrderingLe p) r0
              /\
              (
                trigger e = TTCretry (ballot (vround sn rn) cmd)
                \/
                exists v,
                  trigger e = TTCvote v /\
                  ballot (vround sn rn) cmd = vote2ballot v
              )
          )
        )
        /\ l = [d]
        /\ dl = 0
        /\ In d nreps.
  Proof.
    introv; rewrite TTCsys_output_iff; split; intro h.

    - repndors; auto; exrepnd; ginv;[].
      exists n d e' p sn rn cmd cmd0 lwm; dands; auto.

    - left.
      exrepnd; subst.
      exists n d e' p sn rn cmd cmd0 lwm; dands; auto.
  Qed.

  Lemma TTCdecided_iff :
    forall (eo : EventOrdering) e l dl prp,
      In (MkDMsg (TTCdecided prp) l dl) (output_system_on_event_ldata TTCsys e)
      <->
      exists (n : Rep) (d : name) (e' : Event) (p : e' ⊑ e) (sn : SlotNum) (rn : RoundNum)
             (cmd0 : Cmd) (lwm : list_with_missing) (cmd : Cmd) (sender : Rep)
             (cmds : list Cmd) (names : list Rep) (c : Cmd)
             (e'' : subEventOrdering_type e') (p' : e'' ⊑ e),
        prp = prop sn c
        /\ loc e = TTCreplica n
        /\ SM_state_before_event TTCnewVotersOpt e' lwm
        /\ ~ in_list_with_missing sn lwm
        /\ valid_list_with_missing lwm
        /\
        (
          trigger e' = TTCpropose (prop sn cmd0)
          \/
          (exists v, prop sn cmd0 = vote2proposal v /\ trigger e' = TTCvote v)
        )
        /\ @no_loutput_sm_on_event_prior_to _ _ _ _ _ TTCsendNotify (subEventOrdering e') (mkSubOrderingLe p)
        /\ @SM_state_before_event _ _ _ _ _ _ (TTCQuorum (vround sn rn) (TTCreplica n)) (subEventOrdering e'') (mkSubOrderingLe p') (cmds, names)
        /\ trigger e = TTCvote (vote (ballot (vround sn rn) cmd) sender)
        /\ ~ In sender names
        /\ length cmds = 2 * F
        /\ poss_maj cmddeq cmds cmd = ((2 * F) + 1, c)
        /\ l = [d]
        /\ dl = 0
        /\ In d nreps
        /\
        (
          (rn = rnum 0 /\ sub_eo_event e' e'' = e')
          \/
          exists (rn0 : RoundNum) (cmd0 : Cmd),
            (
              subEventOrdering_trigger e' e'' = TTCretry (ballot (vround sn rn) cmd0)
              \/
              (exists v,
                  subEventOrdering_trigger e' e'' = TTCvote v
                  /\ ballot (vround sn rn) cmd0 = vote2ballot v)
            )
            /\ rn0 < rn
            /\ @SM_state_before_event _ _ _ _ _ _ (TTCnewRounds sn) (subEventOrdering e') e'' rn0
            /\ trigger e = TTCvote (vote (ballot (vround sn rn) cmd) sender)
        ).
  Proof.
    introv; rewrite TTCsys_output_iff; split; intro h.

    - repndors; auto; exrepnd; ginv;[].
      exists n d e' p sn rn cmd0 lwm cmd sender cmds names c e'' p'; dands; auto.

    - right; left.
      exrepnd; subst.
      exists n d e' p sn rn cmd0 lwm cmd sender cmds names c e'' p'; dands; auto.
  Qed.

  Lemma TTCretry_iff :
    forall (eo : EventOrdering) e l dl b,
      In (MkDMsg (TTCretry b) l dl) (output_system_on_event_ldata TTCsys e)
      <->
      exists (n : Rep) (e' : Event) (p : e' ⊑ e) (sn : SlotNum) (rn : RoundNum)
             (cmd0 : Cmd) (lwm : list_with_missing) (cmd : Cmd) (sender : Rep)
             (cmds : list Cmd) (names : list Rep) (k : nat) (c : Cmd)
             (e'' : subEventOrdering_type e') (p' : e'' ⊑ e),
        b = ballot (vround sn (rnum (S rn))) c
        /\ l = [loc e]
        /\ dl = 0
        /\ loc e = TTCreplica n
        /\ SM_state_before_event TTCnewVotersOpt e' lwm
        /\ ~ in_list_with_missing sn lwm
        /\ valid_list_with_missing lwm
        /\
        (
          trigger e' = TTCpropose (prop sn cmd0)
          \/
          (exists v, prop sn cmd0 = vote2proposal v /\ trigger e' = TTCvote v)
        )
        /\ @no_loutput_sm_on_event_prior_to _ _ _ _ _ TTCsendNotify (subEventOrdering e') (mkSubOrderingLe p)
        /\ @SM_state_before_event _ _ _ _ _ _ (TTCQuorum (vround sn rn) (TTCreplica n)) (subEventOrdering e'') (mkSubOrderingLe p') (cmds, names)
        /\ trigger e = TTCvote (vote (ballot (vround sn rn) cmd) sender)
        /\ ~ In sender names
        /\ length cmds = F + (F + 0)
        /\ poss_maj cmddeq cmds cmd = (k, c)
        /\ k <> (2 * F) + 1
        /\
        (
          (rn = rnum 0 /\ sub_eo_event e' e'' = e')
          \/
          exists (rn0 : RoundNum) (cmd0 : Cmd),
            (
              subEventOrdering_trigger e' e'' = TTCretry (ballot (vround sn rn) cmd0)
              \/
              (exists v,
                  subEventOrdering_trigger e' e'' = TTCvote v
                  /\ ballot (vround sn rn) cmd0 = vote2ballot v)
            )
            /\ rn0 < rn
            /\ @SM_state_before_event _ _ _ _ _ _ (TTCnewRounds sn) (subEventOrdering e') e'' rn0
            /\ trigger e = TTCvote (vote (ballot (vround sn rn) cmd) sender)
        ).
  Proof.
    introv; rewrite TTCsys_output_iff; split; intro h.

    - repndors; auto; exrepnd; ginv;[].
      exists n e' p sn rn cmd0 lwm cmd sender cmds names k c e'' p'; dands; auto.

    - right; right; left.
      exrepnd; subst.
      exists n e' p sn rn cmd0 lwm cmd sender cmds names k c e'' p'; dands; auto.
  Qed.

  Lemma TTCnotify_iff :
    forall (eo : EventOrdering) e l dl p2,
      In (MkDMsg (TTCnotify p2) l dl) (output_system_on_event_ldata TTCsys e)
      <->
      exists (n : Rep) (d : name) (e' : Event) (p : e' ⊑ e) (p1 : Proposal)
             (lwm : list_with_missing),
        loc e = TTCreplica n
        /\ SM_state_before_event TTCnewVotersOpt e' lwm
        /\ ~ in_list_with_missing (proposal2slot p1) lwm
        /\ valid_list_with_missing lwm
        /\
        (
          trigger e' = TTCpropose p1
          \/
          (exists v, p1 = vote2proposal v /\ trigger e' = TTCvote v)
        )
        /\ @no_loutput_sm_on_event_prior_to _ _ _ _ _ TTCsendNotify (subEventOrdering e') (mkSubOrderingLe p)
        /\ trigger e = TTCdecided p2
        /\ @state_sm_before_event_exists _ _ _ _ _ (TTCrounds p1 (TTCreplica n)) (subEventOrdering e') (mkSubOrderingLe p)
        /\ l = [d]
        /\ dl = 0
        /\ In d nclients.
  Proof.
    introv.
    rewrite TTCsys_output_iff; split; intro h.

    - repndors; auto; exrepnd; ginv;[].
      exists n d e' p p1 lwm; dands; auto.

    - right; right; right.
      exrepnd.
      exists n d e' p p1 p2 lwm; dands; auto.
  Qed.

  Lemma TTCpropose_iff :
    forall (eo : EventOrdering) e l dl p,
      In (MkDMsg (TTCpropose p) l dl) (output_system_on_event_ldata TTCsys e)
      <->
      False.
  Proof.
    introv.
    rewrite TTCsys_output_iff; split; intro h;[|tcsp];[].
    repndors; auto; exrepnd; ginv.
  Qed.

  Lemma TTCkey_replicas :
    forall (eo : EventOrdering) e n m,
      loc e = TTCreplica n
      -> TTChold_keys eo
      -> {k : receiving_key & In k (lookup_receiving_keys (keys e) (TTCreplica m))}.
  Proof.
    introv lp hk.
    pose proof (hk e) as q; clear hk.
    rewrite lp in q.
    pose proof (q m) as h; clear q.
    unfold has_receiving_key in h.
    unfold lookup_receiving_keys.
    remember (lookup_drkeys (keys e) (TTCreplica m)) as lk; destruct lk; simpl; tcsp; GC.
    destruct d as [z k]; simpl in *.
    destruct k.
    exists tt; auto.
  Qed.

  Lemma in_quorum_from_vote :
    forall (eo : EventOrdering) (e : Event) vr slf cmds names cmd,
      SM_state_before_event (TTCQuorum vr slf) e (cmds, names)
      -> In cmd cmds
      -> exists e' sender,
          e' ⊑ e
          /\ trigger e' = TTCvote (vote (ballot vr cmd) sender).
  Proof.
    introv.
    revert cmds names.
    induction e as [e ind] using HappenedBeforeInd; introv sm i.
    unfold SM_state_before_event in sm.
    rewrite state_sm_before_event_unroll in sm.
    destruct (dec_isFirst e) as [d|d]; simpl in *; ginv; simpl in *; tcsp.

    remember (state_sm_before_event (TTCQuorum vr slf) (local_pred e)) as sop.
    symmetry in Heqsop; destruct sop; simpl in *; tcsp.

    destruct p; simpl in *.
    destruct t; simpl in *.
    unfold receive_vote in sm.
    remember (trigger (local_pred e)) as tpred;
      destruct tpred; simpl in *; ginv; tcsp;
        try (complete (pose proof (ind (local_pred e)) as q; autodimp q hyp; eauto with eo; clear ind;
                       pose proof (q cmds names) as h; clear q;
                       repeat (autodimp h hyp);
                       [unfold SM_state_before_event; rewrite Heqsop; auto|];
                       exrepnd; exists e' sender; dands; eauto with eo)).

    destruct v; simpl in *.
    destruct b; simpl in *.
    destruct (VotingRoundDeq vr vr0) as [d1|d1]; subst; simpl in *; ginv.

    {
      destruct (in_dec rep_deq sender l0) as [d2|d2]; subst; simpl in *; ginv.

      - pose proof (ind (local_pred e)) as q; autodimp q hyp; eauto with eo; clear ind.
        pose proof (q cmds names) as h; clear q.
        repeat (autodimp h hyp).
        { unfold SM_state_before_event; rewrite Heqsop; auto. }
        exrepnd; exists e' sender0; dands; eauto with eo.

      - destruct vr0; simpl in *.
        unfold TTCconsensus in sm.
        dest_cases w; simpl in *; ginv.

        + dest_cases y; simpl in *.
          dest_cases z; simpl in *.
          dest_cases u; subst; simpl in *; destruct y0; simpl in *; ginv; tcsp.

        + simpl in *; repndors; subst.

          * exists (local_pred e) sender; dands; eauto with eo.

          * pose proof (ind (local_pred e)) as q; autodimp q hyp; eauto with eo; clear ind.
            pose proof (q l l0) as h; clear q.
            repeat (autodimp h hyp).
            { unfold SM_state_before_event; rewrite Heqsop; auto. }
            exrepnd; exists e' sender0; dands; eauto with eo.
    }

    {
      pose proof (ind (local_pred e)) as q; autodimp q hyp; eauto with eo; clear ind.
      pose proof (q cmds names) as h; clear q.
      repeat (autodimp h hyp).
      { unfold SM_state_before_event; rewrite Heqsop; auto. }
      exrepnd; exists e' sender0; dands; eauto with eo.
    }
  Qed.

  Lemma TTCsent :
    forall (eo : EventOrdering) (e : Event) r1 r2,
      authenticated_messages_were_sent_or_byz_usys eo TTCsys
      -> TTCall_not_byz eo
      -> TTChold_keys eo
      -> TTCdata_auth (loc e) (trigger e) = Some (TTCreplica r1)
      -> loc e = TTCreplica r2
      -> is_protocol_message (trigger e) = true
      -> exists (e' : Event) dst dl,
          e' ≺ e
          /\ In (MkDMsg (trigger e) dst dl) (output_system_on_event_ldata TTCsys e').
  Proof.
    introv sent nbyz hkeys auth loce.

    pose proof (sent e (MkAuthData (trigger e) [tt])) as M1h; simpl in M1h.
    repeat (autodimp M1h hyp);[|].

    {
      unfold verify_authenticated_data; simpl.
      rewrite auth.
      pose proof (TTCkey_replicas eo e r2 r1) as h.
      repeat (autodimp h hyp); exrepnd; eauto 3 with eo; allrw; simpl; auto.
      match goal with
      | [ |- _ _ ?l = _ ] => remember l as w; destruct w; simpl in *; tcsp
      end.
    }

    exrepnd.
    clear M1h2; simpl in *.

    destruct M1h0 as [M1h0|M1h0]; exrepnd.

    { repndors; ginv; tcsp.
      exists e' dst delay; dands; auto. }

    { rewrite auth in M1h5; inversion M1h5 as [z].
      pose proof (nbyz e'' r1) as q; autodimp q hyp; tcsp. }
  Qed.

  Lemma TTCvalidity_aux :
    forall (eo : EventOrdering),
      authenticated_messages_were_sent_or_byz_usys eo TTCsys
      -> TTCall_not_byz eo
      -> TTChold_keys eo
      -> forall (e : Event) (p : Proposal) (c : list name) (m : msg) (dl : nat),
          In (MkDMsg m c dl) (output_system_on_event_ldata TTCsys e)
          ->
          (
            m = TTCpropose p
            \/
            m = TTCnotify p
            \/
            (exists v, m = TTCvote v /\ p = vote2proposal v)
            \/
            m = TTCdecided p
            \/
            (exists b, m = TTCretry b /\ p = ballot2proposal b)
          )
          -> exists e',
            e' ≼ e
            /\ trigger e' = TTCpropose p.
  Proof.
    introv byz nbyz hk.
    induction e as [e ind] using HappenedBeforeInd; introv i eqm.

    repndors; subst.

    - apply TTCpropose_iff in i; tcsp.

    - apply TTCnotify_iff in i; exrepnd.

      pose proof (TTCsent _ e n n) as M1h.
      rewrite i7 in M1h; simpl in M1h; repeat (autodimp M1h hyp); allrw; auto.
      exrepnd.

      apply (ind e'0 M1h1 p) in M1h0; tcsp.
      exrepnd; exists e'1; dands; auto; eauto with eo.

    - exrepnd; subst.
      apply TTCvote_iff in i; exrepnd; subst; simpl in *.

      destruct i8 as [i8|i8]; repnd; subst.

      + destruct i7 as [i7|i7].

        * exists e; dands; auto; eauto with eo.

        * exrepnd.

          pose proof (TTCsent _ e sender n) as M1h.
          rewrite i7 in M1h; simpl in M1h; repeat (autodimp M1h hyp); allrw; auto.
          exrepnd.

          apply (ind e' M1h1 (prop sn cmd)) in M1h0;
            [exrepnd; exists e'0; dands; auto; eauto with eo|].
          right; right; left; eexists;dands;[eauto|];simpl;auto.

      + exrepnd.

        dup p as cloc.

        destruct i1 as [i1|i1].

        {
          pose proof (TTCsent _ e n n) as M1h.
          rewrite i1 in M1h; simpl in M1h; repeat (autodimp M1h hyp); allrw; auto.
          exrepnd.

          apply (ind e'0 M1h1 (prop sn cmd)) in M1h0;
            [exrepnd; exists e'1; dands; eauto with eo|].

          right; right; right; right;eexists;dands;[eauto|];simpl;auto.
        }

        {
          exrepnd.
          destruct v; simpl in *; subst.

          pose proof (TTCsent _ e sender n) as M1h.
          rewrite i1 in M1h; simpl in M1h; repeat (autodimp M1h hyp); allrw; auto.
          exrepnd.

          apply (ind e'0 M1h1 (prop sn cmd)) in M1h0;
            [exrepnd; exists e'1; dands; eauto with eo|].

          right; right; left;eexists;dands;[eauto|];simpl;auto.
        }

    - apply TTCdecided_iff in i; exrepnd; subst.

      pose proof (poss_maj_in cmddeq cmds cmd) as xx; simpl in xx.
      rewrite i12 in xx; simpl in xx.
      destruct xx as [xx|xx]; subst.

      + pose proof (TTCsent _ e sender n) as M1h.
        rewrite i9 in M1h; simpl in M1h; repeat (autodimp M1h hyp); allrw; auto.
        exrepnd.

        apply (ind e'0 M1h1 (prop sn c0)) in M1h0;
          [exrepnd; exists e'1; dands; eauto with eo|].

        right; right; left;eexists;dands;[eauto|];simpl;auto.

      + eapply in_quorum_from_vote in i8;[|exact xx].
        exrepnd.

        rewrite @trigger_in_subEventOrdering in i8.
        dup i1 as eqloc.
        apply localLe_implies_loc in eqloc; simpl in *.
        rewrite subEventOrdering_loc_as_loc in eqloc.

        pose proof (TTCsent eo e'0 sender0 n) as M1h.
        rewrite i8 in M1h; simpl in M1h; repeat (autodimp M1h hyp); allrw; auto.
        exrepnd.

        assert (e'1 ≺ e) as q.
        { apply localHappenedBeforeLe_subEventOrdering_implies in i1; simpl in i1.
          eauto 3 with eo. }

        apply (ind e'1 q (prop sn c0)) in M1h0;
          [exrepnd; exists e'2; dands; eauto with eo|].

        right; right; left;eexists;dands;[eauto|];simpl;auto.

    - exrepnd; subst.
      apply TTCretry_iff in i; exrepnd; subst; simpl in *.

      pose proof (poss_maj_in cmddeq cmds cmd) as xx; simpl in xx.
      rewrite i14 in xx; simpl in xx.
      destruct xx as [xx|xx]; subst.

      + pose proof (TTCsent eo e sender n) as M1h.
        rewrite i11 in M1h; simpl in M1h; repeat (autodimp M1h hyp); allrw; auto.
        exrepnd.

        apply (ind e'0 M1h1 (prop sn c0)) in M1h0;
          [exrepnd; exists e'1; dands; eauto with eo|].

        right; right; left;eexists;dands;[eauto|];simpl;auto.

      + eapply in_quorum_from_vote in i10;[|exact xx].
        exrepnd.

        rewrite @trigger_in_subEventOrdering in i2.
        dup i1 as eqloc.
        apply localLe_implies_loc in eqloc; simpl in *.
        rewrite subEventOrdering_loc_as_loc in eqloc.

        pose proof (TTCsent eo e'0 sender0 n) as M1h.
        rewrite i2 in M1h; simpl in M1h; repeat (autodimp M1h hyp); allrw; auto.
        exrepnd.

        assert (e'1 ≺ e) as q.
        { apply localHappenedBeforeLe_subEventOrdering_implies in i1; simpl in i1.
          eauto 3 with eo. }

        apply (ind e'1 q (prop sn c0)) in M1h0;
          [exrepnd; exists e'2; dands; eauto with eo|].

        right; right; left;eexists;dands;[eauto|];simpl;auto.
  Qed.

  Lemma TTCvalidity :
    forall (eo : EventOrdering),
      authenticated_messages_were_sent_or_byz_usys eo TTCsys
      -> TTCall_not_byz eo
      -> TTChold_keys eo
      -> forall (e : Event) (p : Proposal) (c : list name) (dl : nat),
          In (MkDMsg (TTCnotify p) c dl) (output_system_on_event_ldata TTCsys e)
          ->
          exists e',
            e' ≼ e
            /\ trigger e' = TTCpropose p.
  Proof.
    introv byz nbyz hk i.
    eapply TTCvalidity_aux in i;[exact i| | | |];auto.
  Qed.

  Lemma implies_in_list_with_missing_add_proposal :
    forall p lwm,
      valid_list_with_missing lwm
      -> ~ in_list_with_missing (proposal2slot p) lwm
      -> in_list_with_missing (proposal2slot p) (add_proposal p lwm).
  Proof.
    introv valid ni.
    unfold in_list_with_missing in *.
    unfold valid_list_with_missing in *.
    destruct lwm.
    unfold add_proposal, add_to_list_with_missing.
    destruct p; simpl in *.
    dest_cases w; tcsp.

    - dands; auto.
      intro i.
      apply in_app_iff in i.
      repndors.

      + applydup valid in i; omega.

      + apply in_seq in i; destruct i as [i j]; simpl in *; try omega.

    - dest_cases w.

      + dands; try omega.
        intro j.
        applydup valid in i.
        apply in_remove_elt in j; repnd; try omega.

      + dands; try omega; auto.
  Qed.

  Definition subset_list_with_missing (lwm1 lwm2 : list_with_missing) : Prop :=
    forall n, in_list_with_missing n lwm1 -> in_list_with_missing n lwm2.

  Lemma subset_list_with_missing_refl :
    forall lwm, subset_list_with_missing lwm lwm.
  Proof.
    introv i; auto.
  Qed.
  Hint Resolve subset_list_with_missing_refl : ttc.

  Lemma subset_list_with_missing_trans :
    forall lwm1 lwm2 lwm3,
      subset_list_with_missing lwm1 lwm2
      -> subset_list_with_missing lwm2 lwm3
      -> subset_list_with_missing lwm1 lwm3.
  Proof.
    introv i j k; auto.
  Qed.
  Hint Resolve subset_list_with_missing_trans : ttc.

  Lemma add_to_list_with_missing_if_not_in_some_implies_subset_list_with_missing :
    forall n lwm1 lwm2,
      add_to_list_with_missing_if_not_in n lwm1 = Some lwm2
      -> subset_list_with_missing lwm1 lwm2.
  Proof.
    introv a.
    unfold add_to_list_with_missing_if_not_in in a.
    destruct lwm1.
    dest_cases w; ginv.

    - introv i; simpl in *; repnd; dands; try omega.
      introv j; apply in_app_iff in j; repndors; tcsp.
      apply in_seq in j; simpl in *; omega.

    - dest_cases w; ginv.
      introv j; simpl in *; repnd; dands; try omega.
      intro k; apply in_remove_elt in k; repnd; tcsp.
  Qed.

  Lemma add_new_proposal_some_implies_subset_list_with_missing :
    forall p lwm1 lwm2,
      add_new_proposal p lwm1 = Some lwm2
      -> subset_list_with_missing lwm1 lwm2.
  Proof.
    introv a.
    unfold add_new_proposal in a.
    apply add_to_list_with_missing_if_not_in_some_implies_subset_list_with_missing in a; auto.
  Qed.

  Lemma new_voters_upd_implies_subset_list_with_missing :
    forall lwm1 lwm2 x p,
      new_voters_upd lwm1 p = (lwm2, x)
      -> subset_list_with_missing lwm1 lwm2.
  Proof.
    introv e.
    unfold new_voters_upd in e.
    destruct p; simpl in *; ginv; eauto with ttc.
    dest_cases w; symmetry in Heqw; ginv; eauto with ttc.
    apply add_new_proposal_some_implies_subset_list_with_missing in Heqw; auto.
  Qed.

  Lemma SM_state_on_event_TTCnewVotersOpt_subset :
    forall (eo : EventOrdering) (e1 e2 : Event) lwm1 lwm2,
      e1 ⊏ e2
      -> SM_state_on_event TTCnewVotersOpt e1 lwm1
      -> SM_state_before_event TTCnewVotersOpt e2 lwm2
      -> subset_list_with_missing lwm1 lwm2.
  Proof.
    introv lc sme1 sme2.
    unfold SM_state_on_event in sme1.
    unfold SM_state_before_event in sme2.
    dest_cases sop2; symmetry in Heqsop2; repnd; subst.
    dest_cases sop1; symmetry in Heqsop1; repnd; subst.

    revert lwm2 sop2 lc Heqsop2.
    induction e2 as [e2 ind] using HappenedBeforeInd; introv lc sme2.

    destruct (dec_isFirst e2) as [d|d].

    { apply no_local_predecessor_if_first in lc; tcsp. }

    apply local_implies_pred_or_local in lc; repndors; exrepnd.

    {
      rewrite state_sm_before_event_as_state_sm_on_event_pred in sme2; auto.
      apply pred_implies_local_pred in lc; subst.
      rewrite sme2 in Heqsop1; ginv.
      apply subset_list_with_missing_refl.
    }

    apply pred_implies_local_pred in lc1; subst.

    pose proof (ind (local_pred e2)) as q; clear ind.
    autodimp q hyp; eauto with eo.

    rewrite state_sm_before_event_unroll in sme2.
    destruct (dec_isFirst e2); tcsp; GC.

    remember (@state_sm_before_event
                TTC_I_Node TTC_I_Key TTC_I_Msg
                (prod list_with_missing unit) (option Proposal)
                TTCnewVotersOpt
                eo
                (local_pred e2)) as sop'.
    symmetry in Heqsop'; destruct sop'; repnd; simpl in *; ginv.
    pose proof (q p0 p) as h; clear q.
    repeat (autodimp h hyp).

    eapply subset_list_with_missing_trans;[exact h|clear h].

    dest_cases w; symmetry in Heqw; simpl in *; ginv.
    apply new_voters_upd_implies_subset_list_with_missing in Heqw; auto.
  Qed.

  Lemma SM_state_before_event_TTCnewRounds_update :
    forall (eo : EventOrdering) (e : Event) sn rn rn' cmd,
      SM_state_before_event (TTCnewRounds sn) e rn
      -> output_sm_on_event TTCroundInfo e = Some (Some (ballot (vround sn rn') cmd))
      -> rn < rn'
      -> SM_state_on_event (TTCnewRounds sn) e rn'.
  Proof.
    introv sm out ltrn.

    apply output_sm_on_event_TTCroundInfo_iff in out.

    apply SM_state_before_event_implies_exists in sm; exrepnd.
    unfold SM_state_on_event.
    rewrite state_sm_on_event_unroll.
    destruct (dec_isFirst e) as [d|d]; simpl in *.

    - destruct sn; simpl.
      rewrite state_sm_before_event_unroll in sm0.
      destruct (dec_isFirst e); tcsp; GC; ginv; simpl in *.
      remember (trigger e) as tr; destruct tr; tcsp; simpl in *;
        repndors; exrepnd; ginv; tcsp; simpl in *;
          try (destruct rn'; repeat (dest_cases w)).
      destruct v0; simpl in *; subst; simpl in *; ginv.
      dest_cases w; GC; dest_cases w.

    - rewrite <- state_sm_before_event_as_state_sm_on_event_pred; auto.
      rewrite sm0; simpl.
      unfold new_voters_upd.
      repndors; exrepnd; allrw; simpl.

      + destruct rn, sn, rn'; simpl.
        repeat (dest_cases w; simpl).

      + destruct rn, sn, rn', v; simpl in *; subst; simpl in *.
        repeat (dest_cases s).
  Qed.

  Lemma SM_state_on_event_TTCnewRounds_subset :
    forall (eo : EventOrdering) (e1 e2 : Event) sn rn1 rn2,
      e1 ⊏ e2
      -> SM_state_on_event (TTCnewRounds sn) e1 rn1
      -> SM_state_before_event (TTCnewRounds sn) e2 rn2
      -> rn1 <= rn2.
  Proof.
    introv lc sme1 sme2.
    unfold SM_state_on_event in sme1.
    unfold SM_state_before_event in sme2.
    dest_cases sop2; symmetry in Heqsop2; repnd; subst.
    dest_cases sop1; symmetry in Heqsop1; repnd; subst.

    revert rn2 sop2 lc Heqsop2.
    induction e2 as [e2 ind] using HappenedBeforeInd; introv lc sme2.

    destruct (dec_isFirst e2) as [d|d].

    { apply no_local_predecessor_if_first in lc; tcsp. }

    apply local_implies_pred_or_local in lc; repndors; exrepnd.

    {
      rewrite state_sm_before_event_as_state_sm_on_event_pred in sme2; auto.
      apply pred_implies_local_pred in lc; subst.
      rewrite sme2 in Heqsop1; ginv.
    }

    apply pred_implies_local_pred in lc1; subst.

    pose proof (ind (local_pred e2)) as q; clear ind.
    autodimp q hyp; eauto with eo.

    rewrite state_sm_before_event_unroll in sme2.
    destruct (dec_isFirst e2); tcsp; GC.

    remember (@state_sm_before_event
                TTC_I_Node TTC_I_Key TTC_I_Msg
                (prod RoundNum unit) (list Ballot)
                (TTCnewRounds sn)
                eo
                (local_pred e2)) as sop'.
    symmetry in Heqsop'; destruct sop'; repnd; simpl in *; ginv.
    pose proof (q p0 p) as h; clear q.
    repeat (autodimp h hyp).

    dest_cases w; symmetry in Heqw; simpl in *; ginv.
    unfold new_rounds_upd in Heqw.
    destruct p0, sn, (round_info (trigger (local_pred e2))); ginv.
    destruct b, vr, sn, rn.
    repeat (dest_cases w; subst; ginv; simpl in *); omega.
  Qed.

  Lemma TTCvotes_consistent :
    forall (eo : EventOrdering),
      authenticated_messages_were_sent_or_byz_usys eo TTCsys
      -> TTCall_not_byz eo
      -> TTChold_keys eo
      -> forall (e1 e2 : Event) (vr : VotingRound) (cmd1 cmd2 : Cmd) (sender : Rep) (c1 c2 : list name) (dl1 dl2 : nat),
          In (MkDMsg (TTCvote (vote (ballot vr cmd1) sender)) c1 dl1) (output_system_on_event_ldata TTCsys e1)
          -> In (MkDMsg (TTCvote (vote (ballot vr cmd2) sender)) c2 dl2) (output_system_on_event_ldata TTCsys e2)
          -> cmd1 = cmd2.
  Proof.
    introv byz nbyz hk H1h H2h.

    apply TTCvote_iff in H2h; exrepnd; ginv; simpl in *.
    apply TTCvote_iff in H1h; exrepnd; ginv; simpl in *.

    assert (loc e1 = loc e2) as lee.
    { allrw; auto. }

    pose proof (SM_state_before_event_implies_TTCnewVotersOpt_not_in_implies
                  eo e'0 lwm0 (prop sn0 cmd3)) as smon1.
    repeat (autodimp smon1 hyp).

    { apply TTCreceivedProposal_output_iff; auto.
      destruct H1h7;[left;allrw;tcsp|right].
      exrepnd;eexists;dands;[|eauto]; simpl; auto. }

    pose proof (SM_state_before_event_implies_TTCnewVotersOpt_not_in_implies
                  eo e' lwm (prop sn0 cmd0)) as smon2.
    repeat (autodimp smon2 hyp).

    { apply TTCreceivedProposal_output_iff; auto.
      destruct H2h7;[left;allrw;tcsp|right].
      exrepnd;eexists;dands;[|eauto]; simpl; auto. }

    pose proof (implies_in_list_with_missing_add_proposal (prop sn0 cmd3) lwm0) as i1.
    repeat (autodimp i1 hyp); simpl in *.

    pose proof (implies_in_list_with_missing_add_proposal (prop sn0 cmd0) lwm) as i2.
    repeat (autodimp i2 hyp); simpl in *.

    assert (loc e'0 = loc e') as eqloc.
    { pose proof (localLe_implies_loc e' e2 p) as eql1.
      pose proof (localLe_implies_loc e'0 e1 p0) as eql2.
      allrw; auto. }

    assert (e'0 = e') as xx.

    { pose proof (tri_if_same_loc e'0 e') as tri; autodimp tri hyp.
      destruct tri as [tri|tri];[|destruct tri as [tri|tri] ];auto;[|].

      - pose proof (SM_state_on_event_TTCnewVotersOpt_subset
                      _ e'0 e' (add_proposal (prop sn0 cmd3) lwm0) lwm) as h.
        repeat (autodimp h hyp).
        apply h in i1; tcsp.

      - pose proof (SM_state_on_event_TTCnewVotersOpt_subset
                      _ e' e'0 (add_proposal (prop sn0 cmd0) lwm) lwm0) as h.
        repeat (autodimp h hyp).
        apply h in i2; tcsp. }

    subst.

    assert (cmd0 = cmd3) as eqcmd.
    {
      destruct H2h7 as [H2h7|H2h7].
      - rewrite H2h7 in H1h7.
        destruct H1h7 as [H1h7|H1h7]; exrepnd; ginv.
      - exrepnd; rewrite H2h7 in H1h7.
        destruct H1h7 as [H1h7|H1h7]; exrepnd; ginv.
    }

    subst; GC.

    destruct H1h8 as [H1h8|H1h8]; exrepnd; subst;
      destruct H2h8 as [H2h8|H2h8]; exrepnd; subst;
        auto; simpl in *; try omega;[].

    pose proof (SM_state_before_event_TTCnewRounds_update
                  (subEventOrdering e') (mkSubOrderingLe p)
                  sn0 r1 rn0 cmd) as nr1.
    repeat (autodimp nr1 hyp).
    { apply output_sm_on_event_TTCroundInfo_iff; autorewrite with eo; auto. }

    pose proof (SM_state_before_event_TTCnewRounds_update
                  (subEventOrdering e') (mkSubOrderingLe p0)
                  sn0 r0 rn0 cmd2) as nr2.
    repeat (autodimp nr2 hyp).
    { apply output_sm_on_event_TTCroundInfo_iff; autorewrite with eo; auto. }

    assert (e1 = e2) as eqe.
    { pose proof (tri_if_same_loc e1 e2) as tri; autodimp tri hyp.
      destruct tri as [tri|tri];[|destruct tri as [tri|tri] ];auto;[|].

      - pose proof (SM_state_on_event_TTCnewRounds_subset
                      (subEventOrdering e') (mkSubOrderingLe p0) (mkSubOrderingLe p)
                      sn0 rn0 r1) as h.
        repeat (autodimp h hyp); try omega.

      - pose proof (SM_state_on_event_TTCnewRounds_subset
                      (subEventOrdering e') (mkSubOrderingLe p) (mkSubOrderingLe p0)
                      sn0 rn0 r0) as h.
        repeat (autodimp h hyp); try omega. }

    subst; GC.

    repndors; exrepnd; repndors; exrepnd; ginv; try congruence.
  Qed.

  Lemma poss_maj_implies_has_at_least_n :
    forall {T} (dec : Deq T) (l : list T) x n z,
      poss_maj dec l x = (n, z)
      -> has_at_least_n z (x :: l) n.
  Proof.
    induction l; introv poss; simpl in *; ginv; auto.

    dest_cases w; symmetry in Heqw.
    dest_cases y; subst; ginv.

    + apply IHl in Heqw; exrepnd; subst.
      inversion Heqw as [|? ? h|? ? ? h]; subst; clear Heqw; auto.

    + apply IHl in Heqw.
      dest_cases y; ginv; auto.

      * inversion Heqw as [|? ? h|? ? ? h]; subst; clear Heqw; auto.
        constructor; constructor; eauto with list.

      * inversion Heqw as [|? ? h|? ? ? h]; subst; clear Heqw; auto.
        constructor; constructor.
        eapply has_at_least_le; try (exact h); omega.
  Qed.

  Lemma SM_state_before_event_TTQuorum_has_at_least_n_implies_exists_votes :
    forall (eo : EventOrdering) (e : Event) vr n cmds names cmd k,
      SM_state_before_event (TTCQuorum vr n) e (cmds, names)
      -> has_at_least_n cmd cmds k
      ->
      exists (L : list Rep),
        no_repeats L
        /\ subset L names
        /\ length L = k
        /\
        forall r : Rep,
          In r L
          ->
          exists e',
            e' ⊏ e
            /\
            trigger e' = TTCvote (vote (ballot vr cmd) r).
  Proof.
    intros eo.
    induction e as [e ind] using HappenedBeforeInd; introv sm hasn.
    unfold SM_state_before_event in *.
    rewrite state_sm_before_event_unroll in sm.
    destruct (dec_isFirst e) as [d1|d1]; simpl in *; ginv.

    - inversion hasn; subst; clear hasn.
      exists ([] : list Rep); simpl; dands; tcsp.

    - remember (state_sm_before_event (TTCQuorum vr n) (local_pred e)) as sop.
      symmetry in Heqsop; destruct sop; repnd; simpl in *; ginv; tcsp.

      pose proof (ind (local_pred e)) as q; clear ind.
      autodimp q hyp; eauto 2 with eo.
      destruct p0.

      unfold TTCquorum_upd in sm.
      remember (trigger (local_pred e)) as tr.
      symmetry in Heqtr; destruct tr; simpl in *; ginv;
        try (complete (pose proof (q vr n cmds names cmd k) as h; clear q;
                       rewrite Heqsop in h; repeat (autodimp h hyp); exrepnd;
                       exists L; dands; auto;
                       introv i; apply h0 in i; exrepnd;
                       exists e'; dands; auto; eauto 3 with eo)).

      unfold new_vote in sm.
      destruct v, b.
      dest_cases w; dest_cases y; dest_cases z; simpl in *; ginv; GC; tcsp.

      + destruct vr0.
        unfold TTCconsensus in sm.
        dest_cases w; simpl in *; ginv.

        * dest_cases w.
          dest_cases y.
          dest_cases z; ginv; simpl in *; tcsp.

        * inversion hasn as [|? ? h|? ? ? h]; subst; clear hasn; auto.

          {
            pose proof (q (vround sn rn) n l l0 cmd0 n2) as z; clear q.
            rewrite Heqsop in z; repeat (autodimp z hyp).
            exrepnd.
            exists (sender :: L); simpl; dands; auto; eauto 3 with list.
            introv i; repndors; subst.
            - exists (local_pred e); dands; eauto 2 with eo.
            - apply z0 in i; exrepnd.
              exists e'; dands; eauto 3 with eo.
          }

          {
            pose proof (q (vround sn rn) n l l0 cmd k) as z; clear q.
            rewrite Heqsop in z; repeat (autodimp z hyp).
            exrepnd.
            exists L; simpl; dands; auto; eauto 3 with list.
            introv i; repndors; subst.
            apply z0 in i; exrepnd.
            exists e'; dands; eauto 3 with eo.
          }

      + pose proof (q vr0 n cmds names cmd k) as h; clear q.
        rewrite Heqsop in h; repeat (autodimp h hyp); exrepnd.
        exists L; dands; auto.
        introv j; apply h0 in j; exrepnd.
        exists e'; dands; auto; eauto 3 with eo.

      + pose proof (q vr n cmds names cmd k) as h; clear q.
        rewrite Heqsop in h; repeat (autodimp h hyp); exrepnd.
        exists L; dands; auto.
        introv j; apply h0 in j; exrepnd.
        exists e'; dands; auto; eauto 3 with eo.
  Qed.

  Lemma TTCdecided_property :
    forall (eo : EventOrdering),
      authenticated_messages_were_sent_or_byz_usys eo TTCsys
      -> TTCall_not_byz eo
      -> TTChold_keys eo
      -> forall (e : Event) (sn : SlotNum) (cmd : Cmd) (c : list name) (dl : nat),
          In (MkDMsg (TTCdecided (prop sn cmd)) c dl) (output_system_on_event_ldata TTCsys e)
          ->
          exists (rn : RoundNum) (L : list Rep),
            no_repeats L
            /\ length L = (2 * F) + 1
            /\
            forall r,
              In r L
              ->
              exists e' dst dl',
                e' ≺ e
                /\ In (MkDMsg (TTCvote (vote (ballot (vround sn rn) cmd) r)) dst dl') (output_system_on_event_ldata TTCsys e').
  Proof.
    introv sent nbyz hkeys i.

    apply TTCdecided_iff in i; exrepnd.

    exists rn.

    pose proof (poss_maj_implies_has_at_least_n cmddeq cmds cmd1 ((2 * F) + 1) c0) as hasn.
    autodimp hasn hyp.
    rewrite Nat.add_comm in hasn; simpl in hasn; autorewrite with core in *.
    inversion hasn as [|? ? hn|? ? ? hn]; subst; clear hasn; auto; ginv.

    - pose proof (SM_state_before_event_TTQuorum_has_at_least_n_implies_exists_votes
                    (subEventOrdering e'') (mkSubOrderingLe p')
                    (vround sn0 rn) (TTCreplica n)
                    cmds names cmd1 (2 * F)) as h.
      repeat (autodimp h hyp).
      exrepnd.
      exists (sender :: L).
      rewrite Nat.add_comm; simpl; dands; auto.
      introv i; destruct i as [i|i]; subst; auto.

      + pose proof (TTCsent eo e r n) as M1h.
        rewrite i2 in M1h; simpl in M1h; repeat (autodimp M1h hyp); allrw; auto.
        exrepnd.

        assert (e'0 ≺ e) as q by (eauto 3 with eo).

        exists e'0 dst dl; dands; auto.
        allrw <-; auto.

      + apply h0 in i; exrepnd; simpl in *.
        rewrite subEventOrdering_trigger_sub_eo2 in i1.
        apply localHappenedBefore_subEventOrdering_iff in i13; simpl in *.

        applydup local_implies_loc in i13; allrw; auto.

        pose proof (TTCsent eo (sub_eo_event e'' e'0) r n) as M1h.
        rewrite i14 in M1h; simpl in M1h; repeat (autodimp M1h hyp); allrw; auto.
        exrepnd.

        assert (e'1 ≺ e) as q by (eauto 3 with eo).

        exists e'1 dst dl; dands; auto.
        allrw <-; auto.

    - pose proof (SM_state_before_event_TTQuorum_has_at_least_n_implies_exists_votes
                    (subEventOrdering e'') (mkSubOrderingLe p')
                    (vround sn0 rn) (TTCreplica n)
                    cmds names c0 (S (2 * F))) as h.
      repeat (autodimp h hyp).
      exrepnd.
      exists L.
      rewrite Nat.add_comm; simpl; dands; auto.
      introv i.

      apply h0 in i; exrepnd; simpl in *.
      rewrite subEventOrdering_trigger_sub_eo2 in i1.
      apply localHappenedBefore_subEventOrdering_iff in i13; simpl in *.

      applydup local_implies_loc in i13; allrw; auto.

      pose proof (TTCsent eo (sub_eo_event e'' e'0) r n) as M1h.
      rewrite i14 in M1h; simpl in M1h; repeat (autodimp M1h hyp); allrw; auto.
      exrepnd.

      assert (e'1 ≺ e) as q by (eauto 3 with eo).

      exists e'1 dst dl; dands; auto.
      allrw <-; auto.
  Qed.

  Lemma SM_state_before_event_TTQuorum_from_votes :
    forall (eo : EventOrdering) (e : Event) vr n cmds names cmd,
      SM_state_before_event (TTCQuorum vr n) e (cmds, names)
      -> In cmd cmds
      ->
      exists e' sender,
        e' ⊏ e
        /\ trigger e' = TTCvote (vote (ballot vr cmd) sender).
  Proof.
    intros eo.
    induction e as [e ind] using HappenedBeforeInd; introv sm icmds.
    unfold SM_state_before_event in *.
    rewrite state_sm_before_event_unroll in sm.
    destruct (dec_isFirst e) as [d1|d1]; simpl in *; ginv; simpl in *; tcsp.

    remember (state_sm_before_event (TTCQuorum vr n) (local_pred e)) as sop.
    symmetry in Heqsop; destruct sop; repnd; simpl in *; ginv; tcsp.

    pose proof (ind (local_pred e)) as q; clear ind.
    autodimp q hyp; eauto 2 with eo.
    destruct p0.

    unfold TTCquorum_upd in sm.
    remember (trigger (local_pred e)) as tr.
    symmetry in Heqtr; destruct tr; simpl in *; ginv;
      try (complete (pose proof (q vr n cmds names cmd) as h; clear q;
                     rewrite Heqsop in h; repeat (autodimp h hyp); exrepnd;
                     exists e' sender; dands; eauto 3 with eo)).

    unfold new_vote in sm.
    destruct v, b.
    dest_cases w; dest_cases y; dest_cases z; simpl in *; ginv; GC; tcsp.

    - destruct vr0.
      unfold TTCconsensus in sm.
      dest_cases w; simpl in *; ginv.

      + dest_cases w.
        dest_cases y.
        dest_cases z; ginv; simpl in *; tcsp.

      + simpl in *; destruct icmds as [icmds|icmds]; subst.

        { exists (local_pred e) sender; dands; eauto 3 with eo. }

        {
          pose proof (q (vround sn rn) n l l0 cmd) as z; clear q.
          rewrite Heqsop in z; repeat (autodimp z hyp).
          exrepnd.
          exists e' sender0; dands; eauto 3 with eo.
        }

    - pose proof (q vr0 n cmds names cmd) as h; clear q.
      rewrite Heqsop in h; repeat (autodimp h hyp); exrepnd.
      exists e' sender0; dands; eauto 2 with eo.

    - pose proof (q vr n cmds names cmd) as h; clear q.
      rewrite Heqsop in h; repeat (autodimp h hyp); exrepnd.
      exists e' sender0; dands; eauto 3 with eo.
  Qed.

  Lemma TTCsimple_retry_property :
    forall (eo : EventOrdering),
      authenticated_messages_were_sent_or_byz_usys eo TTCsys
      -> TTCall_not_byz eo
      -> TTChold_keys eo
      -> forall (e : Event) (vr : VotingRound) (cmd : Cmd) (c : list name) (dl : nat),
          In (MkDMsg (TTCretry (ballot vr cmd)) c dl) (output_system_on_event_ldata TTCsys e)
          ->
          exists e' dst vr' r dl',
            vr = incVotingRound vr'
            /\ e' ≺ e
            /\ In (MkDMsg (TTCvote (vote (ballot vr' cmd) r)) dst dl') (output_system_on_event_ldata TTCsys e').
  Proof.
    introv sent nbyz hkeys i.

    apply TTCretry_iff in i; exrepnd.

    pose proof (poss_maj_in cmddeq cmds cmd1) as h.
    rewrite i14 in h; simpl in h.

    destruct h as [h|h]; subst; ginv.

    {
      pose proof (TTCsent _ e sender n) as M1h.
      rewrite i11 in M1h; simpl in M1h; repeat (autodimp M1h hyp); allrw; auto.
      exrepnd.
      exists e'0 dst (vround sn rn) sender dl; simpl; dands; auto.
    }

    eapply SM_state_before_event_TTQuorum_from_votes in i10;[|exact h].
    exrepnd.

    rewrite @trigger_in_subEventOrdering in i2.
    dup i1 as eqloc.
    apply local_implies_loc in eqloc; simpl in *.
    rewrite subEventOrdering_loc_as_loc in eqloc.
    dup i1 as lord.
    apply localHappenedBefore_subEventOrdering_implies in lord; simpl in lord.

    pose proof (TTCsent eo e'0 sender0 n) as M1h.
    rewrite i2 in M1h; simpl in M1h; repeat (autodimp M1h hyp); allrw; auto.
    exrepnd.

    exists e'1 dst (vround sn rn) sender0 dl; simpl; dands; eauto 3 with eo.
  Qed.

  Lemma length_reps : length reps = 3 * F + 1.
  Proof.
    introv; unfold reps; autorewrite with list; auto.
  Qed.

  Lemma exists_list_of_replicas :
    exists (l : list Rep), no_repeats l /\ length l <= 3 * F + 1 /\ forall r, In r l.
  Proof.
    exists (remove_repeats rep_deq reps); dands; eauto 3 with list.
    - eapply le_trans;[apply length_remove_repeats_le|].
      rewrite length_reps; auto.
    - introv.
      apply in_remove_repeats.
      apply reps_prop.
  Qed.

  Lemma rep_list_le :
    forall (l : list Rep),
      no_repeats l
      -> length l <= 3 * F + 1.
  Proof.
    introv norep.
    apply (le_trans _ (length reps));[|rewrite length_reps;auto].

    assert (subset l reps) as ss.
    { introv j; apply reps_prop. }

    pose proof (no_repeats_implies_remove_repeats_eq rep_deq l norep) as e.

    apply (subset_implies_eq_length_remove_repeats rep_deq) in ss.
    rewrite e in ss.
    eapply le_trans;[exact ss|].
    eauto with list.
  Qed.

  Lemma in_intersection_majorities :
    forall (l1 l2 : list Rep),
      no_repeats l1
      -> no_repeats l2
      -> length l1 = 2 * F + 1
      -> length l2 = 2 * F + 1
      -> exists r, In r l1 /\ In r l2.
  Proof.
    introv norep1 norep2 len1 len2.

    assert (existsb (fun r1 => existsb (fun r2 => if rep_deq r1 r2 then true else false ) l2) l1 = true) as h;
      [|apply existsb_exists in h; exrepnd;
        apply existsb_exists in h0; exrepnd;
        dest_cases w; subst; GC;
        exists x0; dands; auto].

    remember (existsb (fun r1 => existsb (fun r2 => if rep_deq r1 r2 then true else false) l2) l1) as e.
    destruct e; auto; symmetry in Heqe.
    assert False; tcsp.

    assert (exists (l : list Rep), length l = 4 * F + 2 /\ no_repeats l) as h.

    {
      exists (l1 ++ l2).
      rewrite app_length.
      rewrite no_repeats_app.
      allrw.
      dands; auto; try omega.

      rewrite existsb_false in Heqe.
      introv i j.
      apply Heqe in i.

      rewrite existsb_false in i.
      apply i in j.
      dest_cases w.
    }

    clear Heqe.
    clear dependent l1.
    clear dependent l2.
    exrepnd.

    pose proof (rep_list_le l h0) as q.
    rewrite h1 in q; try omega.
  Qed.

  Lemma two_quorums :
    forall (l1 l2 : list Rep),
      no_repeats l1
      -> no_repeats l2
      -> length l1 = 2 * F + 1
      -> length l2 = 2 * F + 1
      -> exists l,
          F + 1 <= length l
          /\ no_repeats l
          /\ subset l l1
          /\ subset l l2.
  Proof.
    introv norep1 norep2 len1 len2.

    exists (keep rep_deq l1 l2).
    dands; eauto 3 with list.

    destruct (le_lt_dec (F + 1) (length (keep rep_deq l1 l2))) as [d|d]; auto.
    assert False; tcsp.

    pose proof (rep_list_le (remove_repeats rep_deq (l1 ++ l2))) as q.
    autodimp q hyp; eauto 2 with list;[].
    rewrite remove_repeats_app in q.
    rewrite app_length in q.
    rewrite (no_repeats_implies_remove_repeats_eq _ l2) in q; auto.
    rewrite (no_repeats_implies_remove_repeats_eq _ l1) in q; auto.
    rewrite len2 in q.

    assert (length (remove_list rep_deq l1 l2) <= F) as h by omega; clear q.

    pose proof (split_length_as_keep_remove_list rep_deq l1 l2) as q; omega.
  Qed.

  Definition addRoundNum (rn : RoundNum) (k : nat) : RoundNum := rnum (rnum2nat rn + k).

  Lemma rnum2nat_as_rnum :
    forall (rn : RoundNum) k,
      rnum2nat rn = k <-> rn = rnum k.
  Proof.
    destruct rn; introv; simpl; split; intro h; subst; ginv; auto.
  Qed.

  Lemma addRoundNum0 :
    forall rn, addRoundNum rn 0 = rn.
  Proof.
    destruct rn; unfold addRoundNum; tcsp.
  Qed.
  Hint Rewrite addRoundNum0 : ttc.

  Lemma eq_rnum2nat_iff :
    forall r1 r2, rnum2nat r1 = rnum2nat r2 <-> r1 = r2.
  Proof.
    destruct r1, r2; simpl; split; intro h; subst; ginv; auto.
  Qed.

  Lemma TTCretry_property_local :
    forall (eo    : EventOrdering)
           (e0 e  : Event)
           (p     : e0 ⊑ e)
           (vr    : VotingRound)
           (n     : name)
           (cmds  : list Cmd)
           (names : list Rep)
           (cmd   : Cmd),
      @SM_state_before_event _ _ _ _ _ _ (TTCQuorum vr n) (subEventOrdering e0) (mkSubOrderingLe p) (cmds, names)
      ->
      forall (i : nat),
        i < length cmds
        ->
        exists (e' : Event),
          e' ⊑ e
          /\ trigger e' = TTCvote (vote (ballot vr (nth i cmds cmd)) (nth i names replica0)).
  Proof.
    intros eo.
    induction e as [e ind] using HappenedBeforeInd; introv sm lti.
    unfold SM_state_before_event in *.
    rewrite state_sm_before_event_unroll in sm.
    autorewrite with eo in *.
    destruct (@dec_isFirst _ _ _ (subEventOrdering e0) (mkSubOrderingLe p)) as [d1|d1]; simpl in *; ginv.

    - simpl in *; tcsp.

    - match goal with
      | [ H : context[map_option _ ?x] |- _ ] => remember x as sop
      end.
      symmetry in Heqsop; destruct sop; repnd; simpl in *; ginv; tcsp.

      applydup not_isFirst_mkSubOrderingLe_implies_isFirst in d1.

      pose proof (ind (local_pred e)) as q; clear ind.
      autodimp q hyp; eauto 2 with eo.
      destruct p1, p0.

      assert (e0 ⊑ (local_pred e)) as lee.
      { eapply not_isFirst_implies_le_local_pred; eauto. }

      pose proof (q lee vr n l l0 cmd) as h; clear q.
      rewrite (local_mkSubOrderingLe p lee) in Heqsop.
      rewrite (local_mkSubOrderingLe p lee) in sm.
      rewrite Heqsop in h; autodimp h hyp.
      autorewrite with eo in *.

      unfold TTCquorum_upd in sm; simpl in *.
      remember (trigger (local_pred e)) as tr.
      symmetry in Heqtr; destruct tr; simpl in *; ginv;
        try (complete (pose proof (h i lti) as q; exrepnd;
                       exists e'; dands; eauto 2 with eo)).

      unfold new_vote in sm.
      destruct v, b, vr0.
      dest_cases w; dest_cases y; dest_cases z; simpl in *; ginv; GC; tcsp;
        try (complete (pose proof (h i lti) as q; exrepnd;
                       exists e'; dands; eauto 2 with eo)).

      unfold TTCconsensus in sm.
      dest_cases w; simpl in *; ginv.

      + dest_cases w.
        dest_cases y.
        dest_cases z; ginv; simpl in *; tcsp.

      + simpl in *.
        destruct i.

        { exists (local_pred e); dands; eauto 2 with eo. }

        { apply lt_S_n in lti.
          pose proof (h i lti) as q; exrepnd; exists e'; dands; eauto 2 with eo. }
  Qed.

  Lemma TTCretry_property :
    forall (eo    : EventOrdering)
           (e0 e  : Event)
           (p     : e0 ⊑ e)
           (vr    : VotingRound)
           (n     : Rep)
           (cmds  : list Cmd)
           (names : list Rep)
           (cmd   : Cmd),
      authenticated_messages_were_sent_or_byz_usys eo TTCsys
      -> TTCall_not_byz eo
      -> TTChold_keys eo
      -> loc e = TTCreplica n
      -> @SM_state_before_event _ _ _ _ _ _ (TTCQuorum vr (TTCreplica n)) (subEventOrdering e0) (mkSubOrderingLe p) (cmds, names)
      ->
      forall (i : nat),
        i < length cmds
        ->
        exists (e' : Event) (dst : list name) (dl : nat),
          e' ≺ e
          /\ In (MkDMsg
                   (TTCvote (vote (ballot vr (nth i cmds cmd)) (nth i names replica0)))
                   dst dl)
                (output_system_on_event_ldata TTCsys e').
  Proof.
    introv sent nbyz hkeys eqloc sm j.
    eapply (TTCretry_property_local eo e0 e p vr (TTCreplica n) cmds names cmd) in sm;[|exact j].
    exrepnd.

    applydup localLe_implies_loc in sm1.

    pose proof (TTCsent eo e' (nth i names replica0) n) as M1h.
    rewrite sm0 in M1h; simpl in M1h; repeat (autodimp M1h hyp); allrw; auto;
      try (complete (destruct vr; auto)).
    exrepnd.
    exists e'0 dst dl; dands; eauto 3 with eo.
  Qed.

  Lemma SM_state_before_event_TTQuorum_props :
    forall (eo : EventOrdering) (e : Event) vr n cmds names,
      SM_state_before_event (TTCQuorum vr n) e (cmds, names)
      -> no_repeats names /\ length cmds = length names.
  Proof.
    intros eo.
    induction e as [e ind] using HappenedBeforeInd; introv sm.
    unfold SM_state_before_event in *.
    rewrite state_sm_before_event_unroll in sm.
    destruct (dec_isFirst e) as [d1|d1]; simpl in *; ginv; simpl in *; tcsp.

    remember (state_sm_before_event (TTCQuorum vr n) (local_pred e)) as sop.
    symmetry in Heqsop; destruct sop; repnd; simpl in *; ginv; tcsp.

    pose proof (ind (local_pred e)) as q; clear ind.
    autodimp q hyp; eauto 2 with eo.
    destruct p0.

    unfold TTCquorum_upd in sm.
    remember (trigger (local_pred e)) as tr.
    symmetry in Heqtr; destruct tr; simpl in *; ginv;
      try (complete (pose proof (q vr n cmds names) as h; clear q;
                     rewrite Heqsop in h; repeat (autodimp h hyp); exrepnd;
                     exists e' sender; dands; eauto 3 with eo)).

    unfold new_vote in sm.
    destruct v, b.
    dest_cases w; dest_cases y; dest_cases z; simpl in *; ginv; GC; tcsp;
      try (complete (pose proof (q vr n cmds names) as h; clear q;
                     rewrite Heqsop in h; repeat (autodimp h hyp); exrepnd));
      try (complete (pose proof (q vr0 n cmds names) as h; clear q;
                     rewrite Heqsop in h; repeat (autodimp h hyp); exrepnd)).

    destruct vr0.
    unfold TTCconsensus in sm.
    dest_cases w; simpl in *; ginv.

    - dest_cases w.
      dest_cases y.
      dest_cases z; ginv; simpl in *; tcsp.

    - simpl in *.
      rewrite no_repeats_cons.
      pose proof (q (vround sn rn) n l l0) as z; clear q.
      rewrite Heqsop in z; repeat (autodimp z hyp).
      exrepnd; dands; tcsp.
  Qed.

  Lemma poss_maj_prop :
    forall {T} (deq : Deq T) l x k z,
      poss_maj deq l x = (k, z)
      -> count_in deq (snoc l x) z - count_out deq (snoc l x) z <= k
         /\
         forall y,
           y <> z
           -> count_in deq (snoc l x) y + k <= count_out deq (snoc l x) y.
  Proof.
    induction l; introv poss; simpl in *; ginv.

    - repeat (dest_cases w; simpl in *; tcsp; GC).
      dands; tcsp.
      introv d.
      repeat (dest_cases w; simpl in *; tcsp; GC).

    - dest_cases w; symmetry in Heqw; simpl in *.

      destruct (deq a w1) as [d1|d1]; subst; ginv.

      + destruct (deq z z); tcsp; GC;[]; simpl.

        applydup IHl in Heqw; clear IHl; repnd.

        dands;
          try (complete (remember (count_out deq (snoc l x) z) as xx;
                         destruct xx; dands; try omega)).

        introv d.

        dest_cases w; simpl.
        rewrite <- plus_n_Sm.
        apply le_n_S.
        apply Heqw0; auto.

      + destruct (deq_nat w0 0) as [d2|d2]; ginv.

        * destruct (deq z z); tcsp; GC.

          applydup IHl in Heqw; clear IHl; repnd.

          pose proof (Heqw0 z) as q; autodimp q hyp.

          dands; try omega.

          introv d.

          dest_cases w; simpl.
          rewrite <- plus_n_Sm.
          apply le_n_S.
          destruct (deq y w1) as [d2|d2]; subst; try omega.
          apply Heqw0; auto.

        * dest_cases w; GC.
          applydup IHl in Heqw; repnd; clear IHl.

          dands; try omega.

          introv d.

          dest_cases w; simpl; subst; tcsp; try omega; GC.

          {
            rewrite plus_n_Sm.
            rewrite Nat.succ_pred; auto.
          }

          {
            destruct w0; simpl in *; tcsp.
            apply Heqw0 in d; tcsp; omega.
          }
  Qed.

  Lemma unanimous_implies_consistent_vote :
    forall (eo  : EventOrdering)
           (e   : Event)
           (sn  : SlotNum)
           (rn  : RoundNum)
           (cmd : Cmd)
           (L   : list Rep),
      authenticated_messages_were_sent_or_byz_usys eo TTCsys
      -> TTCall_not_byz eo
      -> TTChold_keys eo
      -> no_repeats L
      -> length L = 2 * F + 1
      -> (forall r : Rep,
             In r L ->
             exists e' dst dl,
               (e') ≺ (e) /\
               In (MkDMsg (TTCvote (vote (ballot (vround sn rn) cmd) r)) dst dl)
                  (output_system_on_event_ldata TTCsys e'))
      -> forall (k      : nat)
                (e'     : Event)
                (dst    : list name)
                (dl     : nat)
                (sender : Rep)
                (c      : Cmd),
          In (MkDMsg (TTCvote (vote (ballot (vround sn (addRoundNum rn (S k))) c) sender)) dst dl)
             (output_system_on_event_ldata TTCsys e')
          -> c = cmd.
  Proof.
    introv sent nbyz hkeys norep len imp.
    induction k as [? indk] using comp_ind.
    induction e' as [e' inde] using HappenedBeforeInd; introv i.

    apply TTCvote_iff in i; exrepnd.

    destruct i8 as [i8|i8]; exrepnd; subst; simpl in *.

    { inversion i1; subst; clear i1.
      allrw Nat.eq_add_0; repnd; subst; try omega. }

    destruct i11 as [i10|i10]; exrepnd; ginv.

    - pose proof (TTCsent _ e' n n) as M1h.
      rewrite i10 in M1h; simpl in M1h.
      repeat (autodimp M1h hyp); allrw; auto.

      exrepnd.

      applydup TTCsimple_retry_property in M1h0 as M3h1; auto.
      exrepnd.
      destruct vr'; simpl in *.

      inversion M3h1; subst; clear M3h1.
      match goal with
      | [ H : _ + _ = _ |- _ ] => rename H into eqp
      end.
      rewrite <- plus_n_Sm in eqp.
      inversion eqp; clear eqp; subst.
      match goal with
      | [ H : _ + _ = _ |- _ ] => rename H into eqp
      end.
      symmetry in eqp; rewrite rnum2nat_as_rnum in eqp; subst.
      fold (addRoundNum rn k) in *.

      destruct k;[|apply indk in M3h0; auto].
      clear indk M3h0.

      (* Now we have to prove that this retry [M1h1] couldn't have happened
         because of the unanimous quorum L *)
      apply TTCretry_iff in M1h0; exrepnd.

      inversion M1h0; subst; clear M1h0.
      match goal with
      | [ H : _ + _ = _ |- _ ] => rename H into eqp
      end.
      rewrite Nat.add_1_r in eqp.
      symmetry in eqp; inversion eqp; clear eqp; subst.
      allrw eq_rnum2nat_iff; subst.

      pose proof (TTCretry_property
                    eo e'' e'1 p'
                    (vround sn0 rn)
                    n0 cmds names cmd3) as q.
      repeat (autodimp q hyp).

      applydup SM_state_before_event_TTQuorum_props in M1h11; repnd.

      pose proof (two_quorums L (sender :: names)) as quor.
      simpl in quor.
      rewrite no_repeats_cons in quor.
      rewrite <- M1h0 in quor; rewrite M1h14 in quor.
      repeat (autodimp quor hyp); try omega;[].
      exrepnd.

      pose proof (TTCsent _ e'1 sender n0) as M4h.
      rewrite M1h12 in M4h; simpl in M4h.
      repeat (autodimp M4h hyp); allrw; auto.
      exrepnd.

      assert (forall i : nat,
                 i < 2 * F + 1
                 -> In (nth i (sender :: names) replica0) l
                 -> nth i (cmd3 :: cmds) cmd3 = cmd) as xx.
      {
        introv z1 z2.
        destruct i; simpl in *.

        - apply quor3 in z2.
          apply imp in z2; exrepnd.
          eapply TTCvotes_consistent in z0; try (exact M4h0); auto.

        - pose proof (q i) as zz; autodimp zz hyp; try omega;[].
          apply quor3 in z2.
          apply imp in z2; exrepnd.
          eapply TTCvotes_consistent in z0; try (exact zz0); auto.
      }

      assert (exists (cs : list Cmd),
                 sublist cs (cmd3 :: cmds)
                 /\ F + 1 <= length cs
                 /\ contains_only cs cmd) as exs.
      {

        exists (map (fun i => nth i (cmd3 :: cmds) cmd3) (find_positions rep_deq (sender :: names) l)).
        autorewrite with list.
        rewrite length_find_positions_if_subset_and_no_repeats; auto;[].
        dands; auto;[|].

        - apply sublist_map_nth_find_positions_if_same_length; simpl; omega.

        - introv i.
          apply in_map_iff in i; exrepnd; subst.
          apply xx; auto.
          { apply in_find_positions_implies_lt in i1; simpl in *; try omega. }
          { eapply in_find_positions_implies_nth_in in i1; exact i1. }
      }

      clear xx.
      exrepnd.
      apply (subset_cons_r_snoc_if_all_same cmd) in exs1; auto;[].

      destruct (cmddeq c cmd); auto.
      assert False;[|tcsp];[].

      pose proof (poss_maj_prop cmddeq cmds cmd3 k c) as zzz.
      autodimp zzz hyp; repnd.
      pose proof (zzz cmd) as yyy; autodimp yyy hyp.
      clear zzz zzz0.

      pose proof (sublist_implies_count_in cmddeq (snoc cmds cmd3) cs cmd) as uuu.
      repeat (autodimp uuu hyp).

      assert (F + 1 <= count_in cmddeq (snoc cmds cmd3) cmd) as vvv by omega.
      clear uuu.

      pose proof (length_count_in_out cmddeq cmd (snoc cmds cmd3)) as uuu.
      rewrite length_snoc in uuu.
      rewrite M1h14 in uuu.
      omega.

    - destruct v; simpl in *; subst.

      pose proof (TTCsent _ e' sender n) as M4h.
      rewrite i10 in M4h; simpl in M4h.
      repeat (autodimp M4h hyp); allrw; auto.
      exrepnd.
      apply inde in M4h0; auto.
  Qed.

  Lemma lt_implies_eq_add :
    forall a b, a < b -> exists k, b = a + S k.
  Proof.
    introv ltab.
    exists (pred (b - a)); omega.
  Qed.

  Lemma lt_round_implies_eq_add :
    forall (a b : RoundNum), a < b -> exists k, b = addRoundNum a (S k).
  Proof.
    introv ltab.
    destruct a, b; simpl in *.
    apply lt_implies_eq_add in ltab; exrepnd.
    exists k; subst; simpl in *; auto.
  Qed.

  Lemma TTCdecided_agreement :
    forall (eo : EventOrdering),
      authenticated_messages_were_sent_or_byz_usys eo TTCsys
      -> TTCall_not_byz eo
      -> TTChold_keys eo
      -> forall (e1 e2 : Event) (sn : SlotNum) (cmd1 cmd2 : Cmd) (c1 c2 : list name) (dl1 dl2 : nat),
          In (MkDMsg (TTCdecided (prop sn cmd1)) c1 dl1) (output_system_on_event_ldata TTCsys e1)
          -> In (MkDMsg (TTCdecided (prop sn cmd2)) c2 dl2) (output_system_on_event_ldata TTCsys e2)
          -> cmd1 = cmd2.
  Proof.
    introv sent nbyz hkeys H1i H2i.

    apply TTCdecided_property in H1i; auto; exrepnd.
    apply TTCdecided_property in H2i; auto; exrepnd.

    assert (exists r, In r L /\ In r L0) as excmd.
    { apply in_intersection_majorities; auto. }

    exrepnd.

    destruct (RoundNumDeq rn0 rn) as [d1|d1].

    - subst.

      pose proof (H1i1 r) as q1; autodimp q1 hyp.
      pose proof (H2i1 r) as q2; autodimp q2 hyp.
      exrepnd.

      eapply TTCvotes_consistent in q0; try (exact q3); auto.

    - assert (rnum2nat rn0 <> rnum2nat rn) as d.
      { introv xx; destruct rn0, rn; subst; tcsp. }
      destruct (le_lt_dec rn rn0) as [lern|ltrn]; simpl in *.

      + assert (rn < rn0) as ltrn by omega; clear lern.
        pose proof (lt_round_implies_eq_add rn rn0) as xx; autodimp xx hyp.
        exrepnd; subst.

        pose proof (H2i1 r) as q2; autodimp q2 hyp; exrepnd.

        pose proof (unanimous_implies_consistent_vote
                      eo e1 sn rn cmd1 L) as h.
        repeat (autodimp h hyp).
        apply h in q0; auto.

      + pose proof (lt_round_implies_eq_add rn0 rn) as xx; autodimp xx hyp.
        exrepnd; subst.

        pose proof (H1i1 r) as q1; autodimp q1 hyp; exrepnd.

        pose proof (unanimous_implies_consistent_vote
                      eo e2 sn rn0 cmd2 L0) as h.
        repeat (autodimp h hyp).
        apply h in q0; auto.
  Qed.

  Lemma TTCagreement :
    forall (eo : EventOrdering),
      authenticated_messages_were_sent_or_byz_usys eo TTCsys
      -> TTCall_not_byz eo
      -> TTChold_keys eo
      -> forall (e1 e2 : Event) (sn : SlotNum) (cmd1 cmd2 : Cmd) (c1 c2 : list name) (dl1 dl2 : nat),
          In (MkDMsg (TTCnotify (prop sn cmd1)) c1 dl1) (output_system_on_event_ldata TTCsys e1)
          -> In (MkDMsg (TTCnotify (prop sn cmd2)) c2 dl2) (output_system_on_event_ldata TTCsys e2)
          -> cmd1 = cmd2.
  Proof.
    introv sent nbyz hkeys i j.

    apply TTCnotify_iff in i.
    apply TTCnotify_iff in j.
    exrepnd.

    pose proof (TTCsent _ e1 n0 n0) as M1h.
    rewrite i7 in M1h; simpl in M1h.
    repeat (autodimp M1h hyp); allrw; auto.
    exrepnd.

    pose proof (TTCsent _ e2 n n) as M2h.
    rewrite j7 in M2h; simpl in M2h.
    repeat (autodimp M2h hyp); allrw; auto.
    exrepnd.

    eapply TTCdecided_agreement in M1h0; try (exact M2h0); auto.
  Qed.


End TwoThirdConsensus.
