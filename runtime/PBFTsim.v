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


Require Export Simulator.
Require Export PBFT.
Require Export PBFTcollision_resistant.
Require Import Ascii String.
(*Require Import SHA256.*)


(*
    We'll define here an instance of PBFT so that we can simulate it.
 *)



(* ================== INSTANCE OF PBFT ================== *)

Section PBFTinstance.

(*  Class NumNodes := MkNumNodes { total_num_faults : nat; total_num_clients : nat }.
  Context { p_num_nodes : NumNodes }.*)


  (* ============================================ *)
  (* total_num_faults *)
  Definition F := 1.

  (* total_num_clients is C+1 *)
  Definition C := 0.

  (* max requests in progress *)
  Definition MIP := 2.

  (* water-mark range *)
  Definition WMR := 100.

  (* checkpoint period *)
  Definition CP := 50.
  (* ============================================ *)


  Definition pbft_digest : Set := list nat.

  Lemma pbft_digest_deq : Deq pbft_digest.
  Proof.
    introv; apply list_eq_dec.
    apply deq_nat.
  Defined.

  Inductive sending_key_stub : Set :=
  | pbft_sending_key_stub.

  Inductive receiving_key_stub : Set :=
  | pbft_receiving_key_stub.

  Definition pbft_sending_key   : Set := sending_key_stub.
  Definition pbft_receiving_key : Set := receiving_key_stub.

  (*Definition F : nat := 1.*)
  Definition nreps (F : nat) : nat := 3 * F + 1.

  Definition replica (F : nat) : Set := nat_n (nreps F).

  Lemma replica_deq (F : nat) : Deq (replica F).
  Proof.
    apply nat_n_deq.
  Defined.

  Definition reps2nat (F : nat) : replica F -> nat_n (nreps F) := fun n => n.

  Lemma bijective_reps2nat (F : nat) : bijective (reps2nat F).
  Proof.
    exists (fun n : nat_n (nreps F) => n); introv; unfold reps2nat; auto.
  Defined.

  Definition nclients (C : nat) : nat := S C.

  Definition client (C : nat) : Set := nat_n (nclients C).

  Definition client0 (C : nat) : client C.
  Proof.
    exists 0.
    apply leb_correct.
    unfold nclients.
    omega.
  Defined.

  Lemma client_deq (C : nat) : Deq (client C).
  Proof.
    apply nat_n_deq.
  Defined.

  Definition clients2nat (C : nat) : client C -> nat_n (nclients C) := fun n => n.

  Lemma bijective_clients2nat (C : nat) : bijective (clients2nat C).
  Proof.
    exists (fun n : nat_n (nclients C) => n); introv; unfold clients2nat; auto.
  Defined.

  Inductive operation :=
  | opr_add (n : nat)
  | opr_sub (n : nat).

  Lemma operation_deq : Deq operation.
  Proof.
    introv; destruct x as [n|n], y as [m|m]; prove_dec;
      destruct (deq_nat n m); subst; prove_dec.
  Defined.

  Definition smState : Set := nat.
  Definition result : Set := nat.

  Definition operation_upd (C : nat) (c : client C) (state : smState) (opr : operation) : result * smState :=
    match opr with
    | opr_add m => let k := state + m in (k,k)
    | opr_sub m => let k := state - m in (k,k)
    end.

  Inductive PBFTtoken_stub : Set :=
  | pbft_token_stub.

  Definition pbft_token : Set := PBFTtoken_stub.

  Lemma pbft_token_deq : Deq pbft_token.
  Proof.
    introv; destruct x, y; simpl; prove_dec.
  Defined.

  Global Instance PBFT_I_context : PBFTcontext :=
    MkPBFTcontext
      (* max in progress *)
      MIP

      (* water mark range *)
      WMR

      (* checkpoint period *)
      CP

      (* digest type *)
      pbft_digest

      (* digest decider *)
      pbft_digest_deq

      (* token type *)
      pbft_token

      (* token decider *)
      pbft_token_deq

      (* sending key type *)
      pbft_sending_key

      (* receiving key type *)
      pbft_receiving_key

      (* number of faults *)
      F

      (* replica type *)
      (replica F)

      (* Replica decider *)
      (replica_deq F)

      (* replica 2 nat *)
      (reps2nat F)

      (* proof that reps2nat is bijective *)
      (bijective_reps2nat F)

      (* number of clients *)
      (nclients C)

      (* client type *)
      (client C)

      (* client decider *)
      (client_deq C)

      (* client 2 nat *)
      (clients2nat C)

      (* proof that clients2nat is bijective *)
      (bijective_clients2nat C)

      (* operation type *)
      operation

      (* operation decider *)
      operation_deq

      (* result type *)
      result

      (* result decider *)
      deq_nat

      (* state type *)
      smState

      (* initial state *)
      0

      (* update function *)
      (operation_upd C)

      (* delay in ms *)
      1000.


  Definition pbft_create_signature
             (m  : PBFTBare_Msg)
             (ks : sending_keys) : PBFTtokens := [pbft_token_stub].

  Definition pbft_verify_signature
             (m : PBFTBare_Msg)
             (n : name)
             (k : receiving_key)
             (a : pbft_token) : bool := true.

  Global Instance PBFT_I_auth : PBFTauth :=
    MkPBFTauth pbft_create_signature pbft_verify_signature.


  Definition pbft_lookup_replica_sending_key   (src : Rep)    : pbft_sending_key   := pbft_sending_key_stub.
  Definition pbft_lookup_replica_receiving_key (dst : Rep)    : pbft_receiving_key := pbft_receiving_key_stub.
  Definition pbft_lookup_client_receiving_key  (c   : Client) : pbft_receiving_key := pbft_receiving_key_stub.

  Definition initial_pbft_local_key_map_replicas (src : name) : local_key_map :=
    match src with
    | PBFTreplica i =>
      MkLocalKeyMap
        [MkDSKey (map PBFTreplica reps) (pbft_lookup_replica_sending_key i)]
        (List.app
           (map (fun c => MkDRKey [PBFTclient  c] (pbft_lookup_client_receiving_key  c)) clients)
           (map (fun m => MkDRKey [PBFTreplica m] (pbft_lookup_replica_receiving_key m)) reps))
    | PBFTclient _ => MkLocalKeyMap [] []
    end.

  Global Instance PBFT_I_keys : PBFTinitial_keys :=
    MkPBFTinitial_keys initial_pbft_local_key_map_replicas.

  Definition pbft_simple_create_hash_messages (msgs : list PBFTmsg) : PBFTdigest := [].
  Definition pbft_simple_verify_hash_messages (msgs : list PBFTmsg) (d : PBFTdigest) := true.
  Definition pbft_simple_create_hash_state_last_reply (smst : PBFTsm_state) (lastr : LastReplyState) : PBFTdigest := [].
  Definition pbft_simple_verify_hash_state_last_reply (smst : PBFTsm_state) (lastr : LastReplyState) (d : PBFTdigest) := true.

  Global Instance PBFT_I_hash : PBFThash :=
    MkPBFThash
      pbft_simple_create_hash_messages
      pbft_simple_verify_hash_messages
      pbft_simple_create_hash_state_last_reply
      pbft_simple_verify_hash_state_last_reply.


  (*Lemma simple_create_hash_messages_collision_resistant :
  forall msgs1 msgs2,
    simple_create_hash_messages msgs1 = simple_create_hash_messages msgs2
    -> msgs1 = msgs2.
Proof.
  introv h.
  unfold simple_create_hash_messages in *.
Admitted.

Lemma simple_create_hash_state_last_reply_collision_resistant :
  forall sm1 sm2 last1 last2,
    simple_create_hash_state_last_reply sm1 last1 = simple_create_hash_state_last_reply sm2 last2
    -> sm1 = sm2 /\ last1 = last2.
Proof.
  introv h.
Admitted.

Global Instance PBFT_I_hash_axioms : PBFThash_axioms.
Proof.
  exact (Build_PBFThash_axioms
           (* create_hash_message is collision resistant *)
           simple_create_hash_messages_collision_resistant

           (* create_hash_state_last_reply is collision resistant *)
           simple_create_hash_state_last_reply_collision_resistant
        ).
Defined.
   *)


  (* ================== TIME ================== *)


  Definition time_I_type : Set := unit.

  Definition time_I_get_time : unit -> time_I_type := fun _ => tt.

  Definition time_I_sub : time_I_type -> time_I_type -> time_I_type := fun _ _ => tt.

  Definition time_I_2string : time_I_type -> string := fun _ => "".

  Global Instance TIME_I : Time.
  Proof.
    exists time_I_type.
    { exact time_I_get_time. }
    { exact time_I_sub. }
    { exact time_I_2string. }
  Defined.



  (* ================== PRETTY PRINTING ================== *)


  (* FIX: to replace when extracting *)
  Definition print_endline : string -> unit := fun _ => tt.
  Definition nat2string (n : nat) : string := "-".

  Definition CR : string := String (ascii_of_nat 13) "".

  (* Fix: to finish *)
  Definition tokens2string (toks : Tokens) : string := "-".

  (* Fix: to finish *)
  Definition digest2string (d : pbft_digest) : string := "-".

  (* Fix: to finish *)
  Definition result2string (r : result) : string := "-".

  (* Fix: there's only one client anyway *)
  Definition client2string (c : client C) : string := "-".

  Definition timestamp2string (ts : Timestamp) : string :=
    match ts with
    | time_stamp n => nat2string n
    end.

  Definition view2string (v : View) : string :=
    match v with
    | view n => nat2string n
    end.

  Definition seq2string (s : SeqNum) : string :=
    match s with
    | seq_num n => nat2string n
    end.

  Definition operation2string (opr : operation) : string :=
    match opr with
    | opr_add n => str_concat ["+", nat2string n]
    | opr_sub n => str_concat ["-", nat2string n]
    end.

  Definition nat_n2string {m} (n : nat_n m) : string := nat2string (proj1_sig n).

  Definition replica2string (r : replica F) : string := nat_n2string r.

  Definition bare_request2string (br : Bare_Request) : string :=
    match br with
    | null_req => str_concat [ "null_req"]
    | bare_req opr ts c => str_concat [operation2string opr, ",", timestamp2string ts, ",", client2string c]
    end.

  Definition request2string (r : Request) : string :=
    match r with
    | req br a => str_concat ["REQUEST(", bare_request2string br, ",", tokens2string a, ")"]
    end.

  Fixpoint requests2string (rs : list Request) : string :=
    match rs with
    | [] => ""
    | [r] => request2string r
    | r :: rs => str_concat [request2string r, ",", requests2string rs]
    end.

  Definition bare_pre_prepare2string (bpp : Bare_Pre_prepare) : string :=
    match bpp with
    | bare_pre_prepare v s reqs => str_concat [view2string v, ",", seq2string s, ",", requests2string reqs]
    end.

  Definition bare_prepare2string (bp : Bare_Prepare) : string :=
    match bp with
    | bare_prepare v s d i => str_concat [view2string v, ",", seq2string s, ",", digest2string d, ",", replica2string i]
    end.

  Definition bare_commit2string (bc : Bare_Commit) : string :=
    match bc with
    | bare_commit v s d i => str_concat [view2string v, ",", seq2string s, ",", digest2string d, ",", replica2string i]
    end.

  Definition bare_reply2string (br : Bare_Reply) : string :=
    match br with
    | bare_reply v ts c i res => str_concat [view2string v, ",", timestamp2string ts, ",", client2string c, ",", replica2string i, ",", result2string res]
    end.

  Definition pre_prepare2string (pp : Pre_prepare) : string :=
    match pp with
    | pre_prepare b a => str_concat ["PRE_PREPARE(",bare_pre_prepare2string b, ",", tokens2string a, ")"]
    end.

  Definition prepare2string (p : Prepare) : string :=
    match p with
    | prepare bp a => str_concat ["PREPARE(", bare_prepare2string bp, ",", tokens2string a, ")"]
    end.

  Definition commit2string (c : Commit) : string :=
    match c with
    | commit bc a => str_concat ["COMMIT(", bare_commit2string bc, ",", tokens2string a, ")"]
    end.

  Definition reply2string (r : Reply) : string :=
    match r with
    | reply br a => str_concat ["REPLY(", bare_reply2string br, ",", tokens2string a, ")"]
    end.

  Definition debug2string (d : Debug) : string :=
    match d with
    | debug r s => str_concat ["DEBUG(", replica2string r, ",", s, ")"]
    end.

  Definition bare_checkpoint2string (bc : Bare_Checkpoint) : string :=
    match bc with
    | bare_checkpoint v n d i => str_concat [view2string v, ",", seq2string n, ",", digest2string d, ",", replica2string i]
    end.

  Definition checkpoint2string (c : Checkpoint) : string :=
    match c with
    | checkpoint bc a => str_concat ["CHECKPOINT(", bare_checkpoint2string bc, ",", tokens2string a, ")"]
    end.

  Definition check_ready2string (c : CheckReady) : string := "CHECK-READY()".

  Definition check_stable2string (c : CheckStableChkPt) : string := "CHECK-STABLE()".

  Definition start_timer2string (t : StartTimer) : string :=
    match t with
    | start_timer r v => str_concat ["START-TIMER(", bare_request2string r, "," , view2string v, ")"]
    end.

  Definition expired_timer2string (t : ExpiredTimer) : string :=
    match t with
    | expired_timer r v => str_concat ["EXPIRED-TIMER(", bare_request2string r, "," , view2string v, ")"]
    end.

  (* FIX *)
  Definition stable_chkpt2string (stable : StableChkPt) : string := "-".

  (* FIX *)
  Definition checkpoint_cert2string (cert : CheckpointCert) : string := "-".

  (* FIX *)
  Definition prepared_infos2string (l : list PreparedInfo) : string := "-".

  Definition bare_view_change2string (bvc : Bare_ViewChange) : string :=
    match bvc with
    | bare_view_change v n stable cert preps i =>
      str_concat
        [view2string v,
         ",",
         seq2string n,
         ",",
         stable_chkpt2string stable,
         ",",
         checkpoint_cert2string cert,
         ",",
         prepared_infos2string preps,
         ",",
         replica2string i
        ]
    end.

  Definition view_change2string (vc : ViewChange) : string :=
    match vc with
    | view_change bvc a => str_concat ["VIEW-CHANGE(", bare_view_change2string bvc, ",", tokens2string a, ")"]
    end.

  (* FIX *)
  Definition view_change_cert2string (V : ViewChangeCert) : string := "-".

  Fixpoint pre_prepares2string (l : list Pre_prepare) : string :=
    match l with
    | [] => ""
    | [r] => pre_prepare2string r
    | r :: rs => str_concat [pre_prepare2string r, ",", pre_prepares2string rs]
    end.

  Definition bare_new_view2string (bnv : Bare_NewView) : string :=
    match bnv with
    | bare_new_view v V OP NP =>
      str_concat
        [
          view2string v,
          ",",
          view_change_cert2string V,
          ",",
          pre_prepares2string OP,
          ",",
          pre_prepares2string NP
        ]
    end.

  Definition new_view2string (nv : NewView) : string :=
    match nv with
    | new_view bnv a => str_concat ["NEW-VIEW(", bare_new_view2string bnv, ",", tokens2string a, ")"]
    end.

  Definition check_bcast_new_view2string (c : CheckBCastNewView) : string :=
    match c with
    | check_bcast_new_view i => str_concat ["CHECK-BCAST-NEW-VIEW(", nat2string i, ")"]
    end.

  Definition msg2string (m : PBFTmsg) : string :=
    match m with
    | PBFTrequest r              => request2string r
    | PBFTpre_prepare pp         => pre_prepare2string pp
    | PBFTprepare p              => prepare2string p
    | PBFTcommit c               => commit2string c
    | PBFTcheckpoint c           => checkpoint2string c
    | PBFTcheck_ready c          => check_ready2string c
    | PBFTcheck_stable c         => check_stable2string c
    | PBFTcheck_bcast_new_view c => check_bcast_new_view2string c
    | PBFTstart_timer t          => start_timer2string t
    | PBFTexpired_timer t        => expired_timer2string t
    | PBFTview_change v          => view_change2string v
    | PBFTnew_view v             => new_view2string v
    | PBFTdebug d                => debug2string d
    | PBFTreply r                => reply2string r
    end.

  Definition name2string (n : name) : string :=
    match n with
    | PBFTreplica r => replica2string r
    | PBFTclient c => client2string c
    end.

  Fixpoint names2string (l : list name) : string :=
    match l with
    | [] => ""
    | [n] => name2string n
    | n :: ns => str_concat [name2string n, ",", names2string ns]
    end.

  Definition delay2string (delay : nat) : string := nat2string delay.

  Definition DirectedMsg2string (dm : DirectedMsg) : string :=
    match dm with
    | MkDMsg msg dst delay =>
      str_concat [msg2string msg, ":", "[", names2string dst, "]", ":", delay2string delay]
    end.

  Fixpoint DirectedMsgs2string (l : DirectedMsgs) : string :=
    match l with
    | [] => ""
    | [dm] => DirectedMsg2string dm
    | dm :: dmsgs => str_concat [DirectedMsg2string dm, CR, DirectedMsgs2string dmsgs]
    end.

  Definition TimedDirectedMsg2string (m : TimedDirectedMsg) : string :=
    match m with
    | MkTimedDMsg dm time => str_concat [DirectedMsg2string dm, ":", time_I_2string time]
    end.

  Fixpoint TimedDirectedMsgs2string (l : TimedDirectedMsgs) : string :=
    match l with
    | [] => ""
    | [dm] => TimedDirectedMsg2string dm
    | dm :: dmsgs => str_concat [TimedDirectedMsg2string dm, CR, TimedDirectedMsgs2string dmsgs]
    end.

  Definition MonoSimulationState2string (s : MonoSimulationState) : string :=
    match s with
    | MkMonoSimState ty sys step out_inflight in_inflight delivered =>
      str_concat
        [CR,
         "====== STEP ======",
         CR,
         nat2string step,
         CR,
         "====== IN FLIGHT (from outside the system) ======",
         CR,
         DirectedMsgs2string out_inflight,
         CR,
         "====== IN FLIGHT (from inside the system) ======",
         CR,
         DirectedMsgs2string in_inflight,
         CR,
         "====== DELIVERED ======",
         CR,
         TimedDirectedMsgs2string delivered,
         CR]
    end.

  Definition pbft_state2string (s : PBFTstate) :=
      str_concat
        ["(checkpoint state size:"
         , nat2string (List.length (chk_state_others (cp_state s)))
         ,")"
         ,"(ready size:"
         , nat2string (List.length (ready s))
         ,")"
         ,"(buffered requests:"
         , nat2string (List.length (request_buffer (primary_state s)))
         ,")"
         ,"(log size:"
         , nat2string (List.length (log s))
         ,")"
        ].

  (* ================== SYSTEM ================== *)


  Definition dummy_initial_state : PBFTstate :=
    Build_State
      (MkLocalKeyMap [] [])
      initial_view
      []
      initial_checkpoint_state
      PBFTsm_initial_state
      initial_next_to_execute
      initial_ready
      initial_last_reply
      initial_view_change_state
      initial_primary_state.

  Definition PBFTdummySM : MStateMachine PBFTstate :=
    MhaltedSM dummy_initial_state.

  Definition PBFTmono_sys : NMStateMachine PBFTstate :=
    fun name =>
      match name with
      | PBFTreplica n => PBFTreplicaSM n
      | _ => MhaltedSM dummy_initial_state
      end.

  Definition mk_request_to (rep : Rep) (ts : nat) (opr : nat) : DirectedMsg :=
    let ts   := time_stamp ts in
    let breq := bare_req (opr_add opr) ts (client0 C) in
    let dst  := PBFTreplica rep in (* the leader *)
    let toks := [ pbft_token_stub ] : Tokens in (* we just send empty lists here to authenticate messages *)
    let req  := req breq toks in
    let msg  := PBFTrequest req in
    MkDMsg msg [dst] 0.

  Definition mk_request (ts : nat) (opr : nat) : DirectedMsg :=
    mk_request_to (PBFTprimary initial_view) ts opr.

  (* n request starting with number start *)
  Fixpoint mk_requests_start (n start opr : nat) : DirectedMsgs :=
    match n with
    | 0 => []
    | S m => List.app (mk_requests_start m start opr) [mk_request (n + start) opr]
    end.

  Definition mk_requests (n opr : nat) : DirectedMsgs :=
    mk_requests_start n 0 opr.

  Record InitRequests :=
    MkInitRequests
      {
        num_requests     : nat;
        starting_seq_num : nat;
        req_operation    : nat;
      }.

  Definition PBFTinit_msgs (msgs : DirectedMsgs) : MonoSimulationState :=
    MkInitMonoSimState PBFTmono_sys msgs.

  Definition PBFTinit (init : InitRequests) : MonoSimulationState :=
    PBFTinit_msgs
      (mk_requests_start
         (num_requests init)
         (starting_seq_num init)
         (req_operation init)).

  Definition PBFTsimul_list (init : InitRequests) (L : list nat) : MonoSimulationState :=
    mono_run_n_steps L (PBFTinit init).

  Definition PBFTsimul_list_msgs (msgs : DirectedMsgs) (L : list nat) : MonoSimulationState :=
    mono_run_n_steps L (PBFTinit_msgs msgs).

  (* [switch] is the list of steps at which we want to switch to sending messages
   coming from the outside (from clients) instead of keeping on sending messages
   coming from the inside (from replicas). *)
  Definition PBFTsimul_n
             (init     : InitRequests) (* This is to generate an initial list of requests *)
             (rounds   : Rounds)
             (switches : Switches) : MonoSimulationState :=
    mono_iterate_n_steps rounds switches (PBFTinit init).

  Definition PBFTsimul_n_msgs
             (msgs     : DirectedMsgs)
             (rounds   : Rounds)
             (switches : Switches) : MonoSimulationState :=
    mono_iterate_n_steps rounds switches (PBFTinit_msgs msgs).

End PBFTinstance.



(* ================== EXTRACTION ================== *)


Extraction Language Ocaml.

(* printing stuff *)
Extract Inlined Constant print_endline => "Prelude.print_coq_endline".
Extract Inlined Constant nat2string    => "Prelude.char_list_of_int".
Extract Inlined Constant CR            => "['\n']".

(* numbers *)
Extract Inlined Constant Nat.modulo    => "(mod)".

(* lists *)
Extract Inlined Constant forallb => "List.for_all".
Extract Inlined Constant existsb => "List.exists".
Extract Inlined Constant length  => "List.length".
Extract Inlined Constant app     => "List.append".
Extract Inlined Constant map     => "List.map".
Extract Inlined Constant filter  => "List.filter".

(* timing stuff *)
Extract Inlined Constant time_I_type     => "float".
Extract Inlined Constant time_I_get_time => "Prelude.Time.get_time".
Extract Inlined Constant time_I_sub      => "Prelude.Time.sub_time".
Extract Inlined Constant time_I_2string  => "Prelude.Time.time2string".


(* == crypto stuff == *)
(* === COMMENT OUT THIS PART IF YOU DON'T WANT TO USE KEYS === *)
Extract Inlined Constant pbft_sending_key   => "Nocrypto.Rsa.priv".
Extract Inlined Constant pbft_receiving_key => "Nocrypto.Rsa.pub".
Extract Inlined Constant pbft_lookup_replica_sending_key   => "RsaKeyFun.lookup_replica_sending_key".
Extract Inlined Constant pbft_lookup_replica_receiving_key => "RsaKeyFun.lookup_replica_receiving_key".
Extract Inlined Constant pbft_lookup_client_receiving_key  => "RsaKeyFun.lookup_client_receiving_key".

Extract Inlined Constant pbft_create_signature => "RsaKeyFun.sign_list".
Extract Inlined Constant pbft_verify_signature => "RsaKeyFun.verify_one".
Extract Inlined Constant pbft_token => "Cstruct.t".
Extract Inlined Constant pbft_token_deq => "(=)".
(* === --- === *)


(* == hashing stuff == *)
Extract Inlined Constant pbft_digest => "Cstruct.t".
Extract Inlined Constant pbft_digest_deq => "(=)".
Extract Inlined Constant pbft_simple_create_hash_messages => "Obj.magic (Hash.create_hash_objects)".
Extract Inlined Constant pbft_simple_verify_hash_messages => "Obj.magic (Hash.verify_hash_objects)".
Extract Inlined Constant pbft_simple_create_hash_state_last_reply => "Obj.magic (Hash.create_hash_pair)".
Extract Inlined Constant pbft_simple_verify_hash_state_last_reply => "Obj.magic (Hash.verify_hash_pair)".
(* === --- === *)


Require Export ExtrOcamlBasic.
Require Export ExtrOcamlNatInt.
Require Export ExtrOcamlString.


Definition local_replica (*(F C : nat)*) :=
  @PBFTreplicaSM
    (@PBFT_I_context (*(MkNumNodes F C)*))
    PBFT_I_auth
    PBFT_I_keys
    PBFT_I_hash.

Extraction "PbftReplica.ml" pbft_state2string lrun_sm MonoSimulationState2string PBFTdummySM local_replica.
