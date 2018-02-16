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


Require Export CorrectTrace.
Require Export EventOrderingLemmas.


Section Process.
  Context { pd  : @Data }.
  Context { pn  : @Node }.
  Context { pk  : @Key }.
  Context { pat : @AuthTok }.
  Context { paf : @AuthFun pn pk pat pd }.
  Context { pm  : @Msg }.
  Context { pda : @DataAuth pd pn }.
  Context { qc  : @Quorum_context pn}.

  Local Open Scope eo.

  (* None is for the halted process *)
  CoInductive Process (I O : Type) : Type :=
  | proc (f : option (I -> (Process I O * O))).
  Arguments proc [I] [O] _.

  (* Process that sends and receives messages *)
  Definition MProcess := Process msg (@DirectedMsgs pn pm).

  (* update function that can halt --- This is the one we're using *)
  Definition Update (S I O : Type) := S -> I -> (option S * O).

  (* update function that sends and receives messages and can halt *)
  Definition MUpdate (S : Type) := Update S msg (@DirectedMsgs pn pm).

  Definition haltedProc {I O} : Process I O := proc None.

  CoFixpoint build_process {S I O}
             (upd : Update S I O)
             (s   : S) : Process I O :=
    proc (Some
            (fun (i : I) =>
               match upd s i with
               | (Some s', out) => (build_process upd s', out)
               | (None, out) => (haltedProc, out)
               end)).

  Definition counter_update : Update nat nat nat :=
    fun s i => (Some (s + i), s + i).

  Definition counter_proc (s : nat) : Process nat nat :=
    build_process counter_update 0.

  (* QUESTION: can we pull the type out? *)
  Record StateMachine S I O : Type :=
    MkSM
      {
        sm_halted : bool; (* true if the state machine has halted *)
        sm_update :> Update S I O;
        sm_state  : S;
      }.
  Arguments MkSM      [S] [I] [O] _(*halted?*) _(*update*) _(*initial state*).
  Arguments sm_halted [S] [I] [O] _.
  Arguments sm_state  [S] [I] [O] _.
  Arguments sm_update [S] [I] [O] _(*type*) _(*state*) _(*input*).

  (* to build a state machine that hasn't halted yet *)
  Definition mkSM {I O S} (upd : Update S I O) (s : S) := MkSM false upd s.


  (* Simple state machines that never halts *)
  Definition SUpdate (S I O : Type) := S -> I -> (S * O).
  Definition MSUpdate (S : Type) := SUpdate S msg (@DirectedMsgs pn pm).
  (* ??? *)
  Definition S2Update {S I O} (upd : SUpdate S I O) : Update S I O :=
    fun s i => let (s',o) := upd s i in (Some s', o).

  (* ??? *)
  Definition mkSSM {I O S} (upd : SUpdate S I O) (s : S) :=
    mkSM (S2Update upd) s.

  (* simple process from simple update function that never halts *)
  CoFixpoint build_sprocess {S I O}
             (upd : SUpdate S I O)
             (s   : S) : Process I O :=
    proc (Some (fun a => let (s', out) := upd s a in (build_sprocess upd s', out))).


  (* Named state machine *)
  Definition NStateMachine S I O := name -> StateMachine S I O.

  Definition MStateMachine S := StateMachine S msg DirectedMsgs.
  Definition NMStateMachine S := name -> MStateMachine S.

  (* a bunch of coercions to named state machines *)
  Definition StateMachinetoNStateMachine {S I O} (s : StateMachine S I O) : NStateMachine S I O :=
    fun _ => s.
  Coercion StateMachinetoNStateMachine : StateMachine >-> NStateMachine.

  Definition MStateMachinetoNMStateMachine {S} (s : MStateMachine S) : NMStateMachine S :=
    fun _ => s.
  Coercion MStateMachinetoNMStateMachine : MStateMachine >-> NMStateMachine.

  Definition MStateMachinetoNStateMachine {S} (s : MStateMachine S) :  NStateMachine S msg DirectedMsgs :=
    fun _ => s.
  Coercion MStateMachinetoNStateMachine : MStateMachine >-> NStateMachine.

  Definition sm2option {S I O} (s : StateMachine S I O) : option (StateMachine S I O) :=
    if sm_halted s then None else Some s.

  Definition haltedSM {S I O} (s : S) (o : O) : StateMachine S I O :=
    MkSM true (fun _ _ => (None, o)) s.

  (* ??? *)
  Definition LhaltedSM {S I O} (s : S) : StateMachine S I (list O) := haltedSM s [].
  Definition MhaltedSM {S} (s : S) : MStateMachine S := LhaltedSM s.

  (* would this be the same as if we would say
   s: sm_state ??? *)
  Definition updState {S I O}
             (c : StateMachine S I O)
             (s : S) : StateMachine S I O :=
    MkSM (sm_halted c) (sm_update c) s.

  Definition halts {S I O} (c : StateMachine S I O) : StateMachine S I O :=
    MkSM true (sm_update c) (sm_state c).

  Definition force_sm {S I O T} (sm : StateMachine S I O) (F : StateMachine S I O -> T) : T :=
    match sm with
    | MkSM h upd st => F (MkSM h upd st)
    end.

  Definition run_sm {S I O}
             (c : StateMachine S I O)
             (i : I) : option (StateMachine S I O * O) :=
    if sm_halted c then None
    else
      match sm_update c (sm_state c) i with
      | (Some s, o) => force_sm (updState c s) (fun sm => Some (sm, o))
      | (None, o) => force_sm (halts c) (fun sm => Some (sm, o))
      end.

  (* similar to run_sm, but instead of returning None, when the state machine
     has halted, we simply return the state machine and the empty list of outputs *)
  Definition lrun_sm {S I O}
             (c : StateMachine S I (list O))
             (i : I) : StateMachine S I (list O) * list O :=
    if sm_halted c then (c, [])
    else
      match sm_update c (sm_state c) i with
      | (Some s, o) => force_sm (updState c s) (fun sm => (sm, o))
      | (None, o) => force_sm (halts c) (fun sm => (sm, o))
      end.

  (* This one returns [a] all the time.  We might want one that returns a only once *)
  Definition ret {I T} (a : T) : StateMachine unit I (list T) :=
    mkSM (fun state msg => (None, [a])) tt.

  Definition nret {I T} (a : T) : NStateMachine unit I (list T) :=
    fun slf => ret a.

  (* BEGIN EXAMPLE: initialization to 0 *)
  Definition counter_sm : StateMachine nat nat nat :=
    mkSM (fun s i => (Some (s + i), s)) 0.

  Eval compute in (sm_state counter_sm).

  Definition counter_sm2 : StateMachine nat nat nat :=
    updState counter_sm 10.

  Eval compute in (sm_state counter_sm2).
  (* END EXAMPLE *)

  Definition USystem (F : name -> Type) I O : Type :=
    forall n : name, StateMachine (F n) I O.

  Definition MUSystem (F : name -> Type) : Type := USystem F msg (@DirectedMsgs pn pm).

  (* first update the current state, and then apply some function f to the result of
     update and return that optput
     e.g. state is counter; increment it, but as output send only digest of counter *)
  Definition OnUpdate {S A B C} (f : B -> C) (upd : Update S A B) : Update S A C :=
    fun s a =>
      match upd s a with
      | (s',b) => (s',f b)
      end.

  (*
  (* ??? *)
  CoFixpoint looping_process (A B : Type) (b : B) : Process A B :=
    proc (Some (fun a => (looping_process A B b,b))).

  Definition MLoop : MProcess := looping_process msg (@DirectedMsgs pn pm) [].
*)

  Definition System := name -> MProcess.

  (* apply process *)
  Definition app_proc {A B} (p : Process A B) (a : A) : option (Process A B * B) :=
    match p with
    | proc o => option_map (fun f => f a) o
    end.

  (* application of a process with a default output value in case the process has halted *)
  Definition app_proc_def {A B} (p : Process A B) (a : option A) (b : B) : Process A B * B :=
    match a with
    | Some a =>
      match p with
      | proc (Some f) => f a
      | _ => (p, b)
      end
    | None => (p,b)
    end.

  Eval compute in (match app_proc (counter_proc 0) 17 with
                   | Some (p, _) =>
                     match app_proc p 3 with
                     | Some (p, _) =>
                       match app_proc p 5 with
                       | Some (p, o) => o
                       | None => 0
                       end
                     | None => 0
                     end
                   | None => 0
                   end).

  Definition oplist (A : Type) := list (option A).

  Fixpoint run_process_on_list {A B} (p : Process A B) (l : oplist A) : Process A B :=
    match l with
    | [] => p
    | Some a :: l =>
      match app_proc p a with
      | Some (p, _) => run_process_on_list p l
      | None => haltedProc
      end
    | None :: _ => haltedProc
    end.

  Fixpoint run_update_on_list {A B S}
           (s   : S)
           (upd : Update S A B)
           (l   : oplist A) : option S :=
    match l with
    | [] => Some s
    | Some a :: l =>
      match upd s a with
      | (Some s', _) => run_update_on_list s' upd l
      | _ => None
      end
    | None :: _ => None
    end.

  Definition build_process_opt {S I O}
             (upd : Update S I O)
             (sop : option S) : Process I O :=
    match sop with
    | Some s => build_process upd s
    | None => haltedProc
    end.

  Lemma run_process_on_list_haltedProc :
    forall {I O} l, @run_process_on_list I O haltedProc l = haltedProc.
  Proof.
    destruct l; simpl; auto.
    destruct o; simpl; auto.
  Qed.
  Hint Rewrite @run_process_on_list_haltedProc : proc.

  Lemma run_process_eq {A B S} :
    forall (upd : Update S A B) (l : oplist A) s,
      build_process_opt upd (run_update_on_list s upd l)
      = run_process_on_list (build_process upd s) l.
  Proof.
    induction l; introv; simpl; auto.
    destruct a; simpl; auto.
    remember (upd s a) as p; destruct p as [sop out]; destruct sop;
      simpl; auto; autorewrite with core proc; auto.
  Qed.

  Definition run_process_on_event
             (p  : MProcess)
             {eo : EventOrdering}
             (e  : Event) : MProcess * DirectedMsgs :=
    app_proc_def
      (run_process_on_list
         p
         (map trigger (@localPreds pn pk pm eo e)))
      (trigger e)
      [].

  Definition output_process_on_event
             (p  : MProcess)
             {eo : EventOrdering}
             (e  : Event) : DirectedMsgs :=
    snd (run_process_on_event p e).

  Definition op_update {S I O}
             (p : Update S I O)
             (s : S)
             (o : option I) : option (option S * O) :=
    match o with
    | Some i => Some (p s i)
    | None => None
    end.

  Definition op_output {S I O}
             (p : Update S I O)
             (s : S)
             (o : option I) : option O :=
    option_map snd (op_update p s o).

  Definition op_state {S I O}
             (p : Update S I O)
             (s : S)
             (o : option I) : option S :=
    map_option fst (op_update p s o).

  Definition run_update_on_event {S O}
             (s  : S)
             (p  : Update S msg O)
             {eo : EventOrdering}
             (e  : Event) : option (option S * O) :=
    map_option
      (fun s' => op_update p s' (trigger e)) (*???*)
      (run_update_on_list s p (map trigger (@localPreds pn pk pm eo e))).

  Definition output_update_on_event {S O}
             (s  : S)
             (p  : Update S msg O)
             {eo : EventOrdering}
             (e  : Event) : option O :=
    option_map snd (run_update_on_event s p e).

  Definition state_sm_before_event {S O}
             (c  : StateMachine S msg O)
             {eo : EventOrdering}
             (e  : Event) : option S :=
    run_update_on_list
      (sm_state c)
      (sm_update c)
      (map trigger (@localPreds pn pk pm eo e)).

  Definition run_sm_on_event_state {S O}
             (c  : StateMachine S msg O)
             {eo : EventOrdering}
             (e  : Event) : option (option S * O) :=
    run_update_on_event
      (sm_state c)
      (sm_update c)
      e.

  Definition state_sm_on_event {S O}
             (sm : StateMachine S msg O)
             {eo : EventOrdering}
             (e  : Event) : option S :=
    map_option fst (run_sm_on_event_state sm e).

  Definition run_sm_on_event {S O}
             (c  : StateMachine S msg O)
             {eo : EventOrdering}
             (e  : Event) : option (StateMachine S msg O * O) :=
    match run_sm_on_event_state c e with
    | Some (Some s, o) => Some (mkSM (sm_update c) s, o)
    | Some (None, o) => Some (halts c, o)
    | None => None
    end.

  Definition output_sm_on_event {S O}
             (c  : StateMachine S msg O)
             {eo : EventOrdering}
             (e  : Event) : option O :=
    option_map snd (run_sm_on_event_state c e).

  Lemma output_sm_on_event_as_run {S O} :
    forall (c  : StateMachine S msg O)
           {eo : EventOrdering}
           (e  : Event),
      output_sm_on_event c e
      = option_map snd (run_sm_on_event c e).
  Proof.
    introv.
    unfold output_sm_on_event, run_sm_on_event.
    remember (run_sm_on_event_state c e) as p.
    destruct p as [p|]; auto.
    destruct p as [sop out]; simpl; auto.
    destruct sop; simpl; auto.
  Qed.

  Definition run_system_on_event_sm {F O}
             (s  : USystem F msg O)
             {eo : EventOrdering}
             (e  : Event) : option (StateMachine (F (loc e)) msg O * O) :=
    run_sm_on_event (s (loc e)) e.

  Definition output_system_on_event {S O}
             (s  : USystem S msg O)
             {eo : EventOrdering}
             (e  : Event) : option O :=
    option_map snd (run_system_on_event_sm s e).

  Definition run_sm_on_list {S I O}
           (c : StateMachine S I O)
           (l : oplist I) : option S :=
    run_update_on_list (sm_state c) (sm_update c) l.

  Definition state_of_sm_at_start_of_event {S O}
             (c  : StateMachine S msg O)
             {eo : EventOrdering}
             (e  : Event) : option S :=
    run_sm_on_list c (map trigger (@localPreds pn pk pm eo e)).

  Lemma output_sm_on_event_eq {S O} :
    forall (c  : StateMachine S msg O)
           {eo : EventOrdering}
           (e  : Event),
      output_sm_on_event c e
      = map_option
          (fun s => op_output c s (trigger e))
          (state_of_sm_at_start_of_event c e).
  Proof.
    introv.
    unfold output_sm_on_event; simpl.
    unfold run_sm_on_event_state; simpl.
    unfold state_of_sm_at_start_of_event; simpl.
    unfold run_update_on_event; simpl.
    unfold run_sm_on_list; simpl.
    remember (run_update_on_list (sm_state c) (sm_update c) (map trigger History( e)%eo)) as sop.
    destruct sop; simpl; auto.
  Qed.

  Lemma run_update_on_list_snoc :
    forall {S I O} L x st (upd : Update S I O),
      run_update_on_list st upd (snoc L x)
      = map_option (fun s => op_state upd s x) (run_update_on_list st upd L).
  Proof.
    induction L; introv; simpl; auto.
    - destruct x; simpl; auto.
      unfold op_state; simpl.
      remember (upd st i) as p; destruct p as [sop o]; destruct sop; simpl; auto.
    - destruct a; simpl; auto.
      remember (upd st i) as p; destruct p as [sop o]; destruct sop; simpl; auto.
  Qed.

  (* ??? *)
  Lemma update_unroll {S I O} :
    forall (eo  : EventOrdering)
           (e   : Event)
           (F   : Event -> option I)
           (upd : Update S I O)
           (st  : S),
      ~ isFirst e
      -> run_update_on_list
           st
           upd
           (map F (localPreds e))
         = map_option
             (fun s => op_state upd s (F (local_pred e)))
             (run_update_on_list
                st
                upd
                (map F (localPreds (local_pred e)))).
  Proof.
    introv ni.
    rewrite (localPreds_unroll e) at 1; auto.
    rewrite map_snoc.
    remember (map F (localPreds (local_pred e))) as L; destruct HeqL.
    apply run_update_on_list_snoc.
  Qed.

  (* ====== observer stuff ====== *)

  Definition process_satisfies_observer
             (n   : name)
             (p   : MProcess)
             (obs : Observer) :=
    forall (eo : EventOrdering) e,
      n = loc e
      -> obs eo e = output_process_on_event p e.

  Definition system_satisfies_observer
             (sys : System)
             (obs : Observer) :=
    forall (eo : EventOrdering) e,
      obs eo e = output_process_on_event (sys (loc e)) e.

  Definition process2observer (n : name) (p : MProcess) : Observer :=
    fun (eo : EventOrdering) (e : Event) =>
      if name_dec n (loc e)
      then output_process_on_event p e
      else [].

  Definition process_satisfies_process2observer :
    forall (p : MProcess) n,
      process_satisfies_observer n p (process2observer n p).
  Proof.
    introv; introv xx.
    unfold process2observer.
    destruct (name_dec n (loc e)); tcsp.
  Qed.

  Context { cad : ContainedAuthData }.
  Context { gms : MsgStatus }.

  (* Similar to [authenticated_messages_were_sent_or_byz],
   * which is defined on observers, but for processes instead here.
   *)
  Definition authenticated_messages_were_sent_or_byz_proc
             (eo : EventOrdering) (p : MProcess) :=
    @authenticated_messages_were_sent_or_byz
      pd
      pn
      pk
      pat
      paf
      pm
      eo
      pda
      cad
      gms
(*      authMsg2Msg*)
      (fun eo e => @output_process_on_event p eo e).

  Definition authenticated_messages_were_sent_non_byz_proc
             (eo : EventOrdering) (p : MProcess) :=
    @authenticated_messages_were_sent_non_byz
      pd
      pn
      pk
      pm
      pat
      paf
      pda
      cad
      gms
      eo
      (fun eo e => @output_process_on_event p eo e).

  Definition authenticated_messages_were_sent_or_byz_sys
             (eo : EventOrdering) (sys : System) :=
    forall n : name, authenticated_messages_were_sent_or_byz_proc eo (sys n).

  Definition authenticated_messages_were_sent_non_byz_sys
             (eo : EventOrdering) (sys : System) :=
    forall n : name, authenticated_messages_were_sent_non_byz_proc eo (sys n).

      (*
    forall e,
    exists e',
      (e' ≺ e) (* event e was triggered by an earlier send event e' *)
      /\
      (
        (* either the message is what was supposed to be sent at e' *)
        (In (MkDData (loc e) (data e)) (output_process_on_event p eo e')
         /\ isRunning e')

        \/

        (* or the message wasn't what was supposed to be sent at e'
           because the node is Byzantine.
           In that case we have to make sure that *)
        (check_auth_data e' e
         /\ isByz e')
      ).*)

(*  Definition DUSystem := USystem Data (@LDirectedData Data n).*)

  (* apply history with last event *)
  Definition output_system_on_event_ldata {S}
             (s  : MUSystem S)
             {eo : EventOrdering}
             (e  : Event) : DirectedMsgs :=
    olist2list (output_system_on_event s e).

  Definition loutput_sm_on_event {S O}
             (c  : StateMachine S msg (list O))
             {eo : EventOrdering}
             (e  : Event) : list O :=
    olist2list (output_sm_on_event c e).

  Definition ooutput_sm_on_event {S O}
             (c  : StateMachine S msg O)
             {eo : EventOrdering}
             (e  : Event) : list O :=
    opt2list (output_sm_on_event c e).

  Definition op_outputs {S I O}
             (p : Update S I (list O))
             (s : S)
             (o : option I) : list O :=
    match option_map snd (op_update p s o) with
    | Some l => l
    | None => []
    end.

  Definition option_compose {A B C} (f : B -> C) (g : A -> option B) (a : A) : option C :=
    match g a with
    | Some b => Some (f b)
    | None => None
    end.

  Lemma option_map_map_option :
    forall {A B C} (f : B -> C) (g : A -> option B) (o : option A),
      option_map f (map_option g o)
      = map_option (option_compose f g) o.
  Proof.
    introv.
    destruct o; simpl; auto.
  Qed.

  Lemma map_option_Some :
    forall {A B} (f : A -> option B) (o : option A) (b : B),
      map_option f o = Some b
      <-> exists a, o = Some a /\ Some b = f a.
  Proof.
    destruct o; simpl in *; introv; split; intro h;
      tcsp; exrepnd; try (inversion h); try (inversion h1); subst; auto.
    eexists; dands; eauto.
  Qed.

  Lemma op_state_Some :
    forall {S I O} (p : Update S I O) s o s',
      op_state p s o = Some s'
      -> exists x, op_update p s o = Some (Some s', x).
  Proof.
    introv h.
    unfold op_state in h.
    remember (op_update p s o) as upd; destruct upd; simpl in *; ginv.
    destruct p0; simpl in *; subst; eexists; eauto.
  Qed.

  Lemma option_compose_snd_op_update_implies :
    forall {S I O} (sm : Update S I (list O)) i a l,
      option_compose snd (fun s' : S => op_update sm s' i) a = Some l
      -> l = op_outputs sm a i.
  Proof.
    introv h.
    unfold option_compose, op_outputs in *; simpl in *.
    remember (op_update sm a i) as x; destruct x; simpl in *; ginv.
  Qed.

  Lemma op_update_Some :
    forall {S I O} (p : Update S I O) s o x,
      op_update p s o = Some x
      -> op_state p s o = fst x.
  Proof.
    introv h.
    unfold op_state; allrw; simpl; auto.
  Qed.

  Lemma op_update_some_iff :
    forall {S I O} (p : Update S I O) s o x,
      op_update p s o = Some x
      <-> exists i, o = Some i /\ x = p s i.
  Proof.
    introv.
    unfold op_update; repnd.
    destruct o; simpl; split; introv h; exrepnd; ginv.
    inversion h; eexists; dands; eauto.
  Qed.

  Lemma op_state_some_iff :
    forall {S I O} (p : Update S I O) s o x,
      op_state p s o = Some x
      <-> exists i, o = Some i /\ fst (p s i) = Some x.
  Proof.
    introv.
    unfold op_state; repnd.
    destruct o; simpl; split; introv h; exrepnd; ginv.
    eexists; dands; eauto.
  Qed.

  Lemma in_op_outputs_iff :
    forall {S I O} (p : Update S I (list O)) s o x,
      In x (op_outputs p s o)
      <-> exists i, o = Some i /\ In x (snd (p s i)).
  Proof.
    introv.
    unfold op_outputs, op_update.
    destruct o; simpl; split; introv h; ginv; tcsp.

    - eexists; dands; eauto.

    - exrepnd; simpl in *; ginv; auto.
  Qed.

  Lemma in_output_sm_on_event :
    forall {S O}
           (sm  : StateMachine S msg (list O))
           {eo  : EventOrdering}
           (e   : Event)
           (out : O),
      In out (loutput_sm_on_event sm e)
      <->
      if dec_isFirst e
      then In out (op_outputs sm (sm_state sm) (trigger e))
      else exists s',
          state_sm_on_event sm (local_pred e) = Some s'
          /\ In out (op_outputs sm s' (trigger e)).
  Proof.
    introv.
    unfold loutput_sm_on_event; simpl.
    unfold output_sm_on_event; simpl.
    unfold state_sm_on_event; simpl.
    unfold run_sm_on_event_state; simpl.
    unfold run_update_on_event; simpl.
    rewrite option_map_map_option.
    split; intro h.

    - dest_cases w;
        [rewrite (isFirst_implies_localPreds_eq e) in h; auto|].
      apply in_olist2list in h; exrepnd.
      apply map_option_Some in h1; exrepnd.
      rewrite (update_unroll eo e trigger) in h1; auto.
      apply map_option_Some in h1; exrepnd.
      fold trigger_info in *.
      rewrite h1; simpl.
      symmetry in h3; apply op_state_Some in h3; exrepnd.
      allrw; simpl.
      eexists; dands; eauto.
      symmetry in h2; apply option_compose_snd_op_update_implies in h2; subst; auto.

    - dest_cases w;
        [rewrite (isFirst_implies_localPreds_eq e); auto|].
      exrepnd.
      apply in_olist2list.
      apply map_option_Some in h1; exrepnd; simpl in *; subst.
      rewrite (update_unroll eo e trigger); auto.
      apply map_option_Some in h1; exrepnd; simpl in *; subst.
      fold trigger_info in *.
      allrw; simpl.
      symmetry in h2.
      apply op_update_Some in h2; simpl in *.
      allrw; simpl.
      unfold option_compose; simpl; auto.
      apply in_op_outputs_iff in h0; exrepnd.
      allrw; simpl.
      eexists; dands; eauto.
  Qed.

  Lemma MhaltedSM_doesnt_output :
    forall {S} m (s : S) {eo : EventOrdering} (e : Event),
      ~ In m (loutput_sm_on_event (MhaltedSM s) e).
  Proof.
    introv i.
    unfold loutput_sm_on_event in i; simpl in i.
    unfold output_sm_on_event in i; simpl in i.
    unfold run_sm_on_event_state in i; simpl in i.
    unfold run_update_on_event in i; simpl in i.
    apply in_olist2list in i; exrepnd.
    apply option_map_Some in i1; exrepnd; simpl in *; subst.
    apply map_option_Some in i1; exrepnd; simpl in *.
    symmetry in i2.
    rewrite op_update_some_iff in i2; exrepnd; ginv.
  Qed.

  Lemma in_output_system_on_event_ldata :
    forall {S}
           (s  : MUSystem S)
           {eo : EventOrdering}
           (e  : Event)
           (m  : DirectedMsg),
      In m (output_system_on_event_ldata s e)
      <->
      In m (loutput_sm_on_event (s (loc e)) e).
  Proof.
    introv.
    unfold output_system_on_event_ldata.
    unfold output_system_on_event.
    unfold run_system_on_event_sm.
    rewrite <- output_sm_on_event_as_run; tcsp.
  Qed.

  Lemma output_system_on_event_ldata_as_loutput :
    forall {S}
           (s  : MUSystem S)
           {eo : EventOrdering}
           (e  : Event),
      output_system_on_event_ldata s e
      = loutput_sm_on_event (s (loc e)) e.
  Proof.
    introv.
    unfold output_system_on_event_ldata.
    unfold output_system_on_event.
    unfold run_system_on_event_sm.
    rewrite <- output_sm_on_event_as_run; tcsp.
  Qed.

  (* Similar to sent_byz_proc, which is defined on processes, but here for
   * a system instead
   *)
  Definition authenticated_messages_were_sent_or_byz_usys
             {S} (eo : EventOrdering) (s : MUSystem S) :=
    @authenticated_messages_were_sent_or_byz
      pd
      pn
      pk
      pat
      paf
      pm
      eo
      pda
      cad
      gms
      (fun eo e => @output_system_on_event_ldata _ s eo e).

  Definition authenticated_messages_were_sent_non_byz_usys
             {S} (eo : EventOrdering) (s : MUSystem S) :=
    @authenticated_messages_were_sent_non_byz
      pd
      pn
      pk
      pm
      pat
      paf
      pda
      cad
      gms
      eo
      (fun eo e => @output_system_on_event_ldata _ s eo e).

  Definition internal_messages_were_sent_usys
             {S} (eo : EventOrdering) (s : MUSystem S) :=
    @internal_messages_were_sent
      pn
      pk
      pm
      eo
      gms
      (fun eo e => @output_system_on_event_ldata _ s eo e).

  Lemma implies_authenticated_messages_were_sent_non_byz_usys :
    forall {S} (eo : EventOrdering) (P : MUSystem S),
      authenticated_messages_were_sent_or_byz_usys eo P
      -> authenticated_messages_were_sent_non_byz_usys eo P.
  Proof.
    introv auth.
    apply implies_authenticated_messages_were_sent_non_byz in auth; auto.
  Qed.
  Hint Resolve implies_authenticated_messages_were_sent_non_byz_usys : proc.

  (*forall e,
    exists e',
      (e' ≺ e) (* event e was triggered by an earlier send event e' *)
      /\
      (
        (* either the message is what was supposed to be sent at e' *)
        (
          In (MkDData (loc e) (data e)) (output_system_on_event_ldata s eo e')
          /\
          isRunning e'
        )

        \/

        (* or the message wasn't what was supposed to be sent at e'
           because the node is Byzantine.
           In that case we have to make sure that loc(e') did not forge the data *)
        (
          check_auth_data e' e
          /\
          isByz e'
        )
      ).*)

  Definition sm_on_list {S I O}
           (sm : StateMachine S I O)
           (l  : oplist I) : StateMachine S I O :=
    match run_sm_on_list sm l with
    | Some s => updState sm s
    | None => halts sm
    end.

  Definition option_compose2 {A B C} (f : B -> option C) (g : A -> option B) (a : A) : option C :=
    match g a with
    | Some b => f b
    | None => None
    end.

  Lemma map_option_map_option :
    forall {A B C} (f : B -> option C) (g : A -> option B) (o : option A),
      map_option f (map_option g o)
      = map_option (option_compose2 f g) o.
  Proof.
    introv.
    destruct o; simpl; auto.
  Qed.

  Lemma equal_map_options :
    forall {A B} (f g : A -> option B) (o : option A),
      (forall a, o = Some a -> f a = g a)
      -> map_option f o = map_option g o.
  Proof.
    introv h.
    destruct o; simpl; auto.
  Qed.

  Lemma state_sm_on_event_unroll {S O} :
    forall (sm : StateMachine S msg O)
           {eo  : EventOrdering}
           (e   : Event),
      state_sm_on_event sm e
      = if dec_isFirst e
        then op_state sm (sm_state sm) (trigger e)
        else map_option
               (fun s => op_state sm s (trigger e))
               (state_sm_on_event sm (local_pred e)).
  Proof.
    introv.
    unfold state_sm_on_event, run_sm_on_event_state, run_update_on_event; simpl.
    destruct (dec_isFirst e) as [d|d].

    { rewrite isFirst_implies_localPreds_eq; auto. }

    rewrite (update_unroll eo e trigger); auto.
    repeat rewrite map_option_map_option.
    unfold option_compose2; simpl.
    apply equal_map_options; introv h.
    unfold op_state.

    remember (op_update sm a (trigger (local_pred e))) as x; destruct x; simpl; auto.
  Qed.

  Definition ite_first {A} {eo : EventOrdering} (e : Event) (a b : A) : A :=
    if dec_isFirst e then a else b.

  Lemma fold_ite_first :
    forall {A} {eo : EventOrdering} (e : Event) (a b : A),
      (if dec_isFirst e then a else b) = ite_first e a b.
  Proof.
    tcsp.
  Qed.

  Lemma output_sm_on_event_unroll {S O} :
    forall (sm : StateMachine S msg O)
           {eo  : EventOrdering}
           (e   : Event),
      output_sm_on_event sm e
      = if dec_isFirst e
        then op_output sm (sm_state sm) (trigger e)
        else map_option
               (fun s => op_output sm s (trigger e))
               (state_sm_on_event sm (local_pred e)).
  Proof.
    introv.
    unfold output_sm_on_event, state_sm_on_event, run_sm_on_event_state, run_update_on_event; simpl.
    destruct (dec_isFirst e) as [d|d].

    { rewrite isFirst_implies_localPreds_eq; auto. }

    rewrite (update_unroll eo e trigger); auto.
    repeat rewrite map_option_map_option.
    rewrite option_map_map_option.
    unfold option_compose, option_compose2; simpl.
    apply equal_map_options; introv h.
    unfold op_state.

    remember (op_update sm a (trigger (local_pred e))) as x; destruct x; simpl; auto.
    repnd; simpl; auto.
    destruct p0; simpl; auto.
  Qed.

  Lemma state_sm_before_event_unroll {S O} :
    forall (sm : StateMachine S msg O)
           {eo  : EventOrdering}
           (e   : Event),
      state_sm_before_event sm e
      = if dec_isFirst e
        then Some (sm_state sm)
        else map_option
               (fun s => op_state sm s (trigger (local_pred e)))
               (state_sm_before_event sm (local_pred e)).
  Proof.
    introv.
    unfold state_sm_before_event; simpl.
    destruct (dec_isFirst e) as [d|d].

    { rewrite isFirst_implies_localPreds_eq; auto. }

    rewrite (localPreds_unroll e) at 1; auto; simpl.
    rewrite map_snoc.
    remember (map trigger (localPreds (local_pred e))) as L; destruct HeqL.
    apply run_update_on_list_snoc.
  Qed.

  Lemma state_sm_before_event_as_state_sm_on_event_pred :
    forall {S O} (X : StateMachine S msg O) {eo : EventOrdering} (e : Event),
      ~ isFirst e
      -> state_sm_before_event X e = state_sm_on_event X (local_pred e).
  Proof.
    intros S O X eo.
    induction e as [e ind] using predHappenedBeforeInd; introv ni; simpl.
    rewrite state_sm_on_event_unroll.
    rewrite state_sm_before_event_unroll.
    destruct (dec_isFirst e) as [d1|d1]; tcsp.
    destruct (dec_isFirst (local_pred e)) as [d2|d2]; tcsp.

    - rewrite state_sm_before_event_unroll.
      destruct (dec_isFirst (local_pred e)); tcsp; GC.

    - rewrite ind; auto.
      apply local_pred_is_direct_pred; auto.
  Qed.

  Lemma ite_first_state_sm_on_event_as_before {S O} :
    forall (sm : StateMachine S msg O)
           {eo : EventOrdering}
           (e  : Event),
      ite_first
        e
        (Some (sm_state sm))
        (state_sm_on_event sm (local_pred e))
      = state_sm_before_event sm e.
  Proof.
    introv; unfold ite_first.
    destruct (dec_isFirst e) as [d|d].

    { rewrite state_sm_before_event_unroll.
      destruct (dec_isFirst e); tcsp. }

    { rewrite state_sm_before_event_as_state_sm_on_event_pred; auto. }
  Qed.

  (*Definition state_sm_on_local_pred_event {S O}
             (sm : StateMachine S msg O)
             (eo : EventOrdering)
             (e  : Event) :=
    ite_first
      e
      (Some (sm_state sm))
      (state_sm_on_event sm eo (local_pred e)).*)

  Lemma state_sm_on_event_unroll2 {S O} :
    forall (sm : StateMachine S msg O)
           {eo : EventOrdering}
           (e  : Event),
      state_sm_on_event sm e
      = map_option
          (fun s => op_state sm s (trigger e))
          (state_sm_before_event sm e).
  Proof.
    introv.
    rewrite <- ite_first_state_sm_on_event_as_before.
    unfold ite_first.
    rewrite state_sm_on_event_unroll.
    destruct (dec_isFirst e); simpl; auto.
  Qed.

  Lemma olist2list_map_option_op_output_as_olist2list_option_map_op_outputs :
    forall {S O} (sm : StateMachine S msg (list O)) i o,
      olist2list (map_option (fun s : S => op_output sm s i) o)
      = olist2list (option_map (fun s : S => op_outputs sm s i) o).
  Proof.
    introv; destruct o; simpl; auto.
  Qed.

  Lemma loutput_sm_on_event_unroll {S O} :
    forall (sm : StateMachine S msg (list O))
           {eo  : EventOrdering}
           (e   : Event),
      loutput_sm_on_event sm e
      = if dec_isFirst e
        then op_outputs sm (sm_state sm) (trigger e)
        else olist2list
               (option_map
                  (fun s => op_outputs sm s (trigger e))
                  (state_sm_on_event sm (local_pred e))).
  Proof.
    introv; unfold loutput_sm_on_event.
    rewrite output_sm_on_event_unroll.
    dest_cases w.
    apply olist2list_map_option_op_output_as_olist2list_option_map_op_outputs.
  Qed.

  Lemma loutput_sm_on_event_unroll2 {S O} :
    forall (sm : StateMachine S msg (list O))
           {eo  : EventOrdering}
           (e   : Event),
      loutput_sm_on_event sm e
      = olist2list
          (map_option
             (fun s => op_output sm s (trigger e))
             (state_sm_before_event sm e)).
  Proof.
    introv.
    rewrite <- ite_first_state_sm_on_event_as_before.
    unfold ite_first.
    rewrite loutput_sm_on_event_unroll.
    destruct (dec_isFirst e); simpl; auto.
    rewrite olist2list_map_option_op_output_as_olist2list_option_map_op_outputs; auto.
  Qed.

(*  Lemma mkSSM_output_iff :
    forall {T} {eo : EventOrdering} (e : Event) (t : T) (init : T) upd,
      In t (loutput_sm_on_event (mkSSM upd init) e)
      <->
      exists s,
        (if dec_isFirst e
         then s = init
         else state_sm_on_event (mkSSM upd init) (local_pred e) = Some s)
        /\ In t (snd (upd s (trigger e))).
  Proof.
    intros T eo.
    induction e as [e ind] using predHappenedBeforeInd;
      introv; split; intro h.

    - rewrite loutput_sm_on_event_unroll in h.
      destruct (dec_isFirst e) as [d|d]; simpl in *; tcsp.

      + unfold S2Update in h; simpl in *.
        dest_cases w; simpl in *; symmetry in Heqw; tcsp.
        exists init; dands; auto.
        allrw; simpl; auto.

      + remember (state_sm_on_event (mkSSM upd init) (local_pred e)) as sop.
        symmetry in Heqsop; destruct sop; simpl in *; ginv; tcsp.

        unfold S2Update in h; simpl in h.
        dest_cases w; symmetry in Heqw; simpl in *.
        eexists; dands;[eauto|].
        allrw; simpl; auto.

    - rewrite loutput_sm_on_event_unroll.
      exrepnd.
      destruct (dec_isFirst e) as [d|d]; simpl in *; tcsp.

      + subst.
        unfold S2Update; simpl.
        dest_cases w; simpl in *; tcsp.

      + allrw; simpl.
        unfold S2Update; dest_cases w; simpl in *; auto.
  Qed.*)

  Definition opt_val {T} (top : option T) (d : T) : T :=
    match top with
    | Some t => t
    | None => d
    end.

(*  Lemma state_sm_before_event_some_implies :
    forall {S O}
           (X   : StateMachine S msg O)
           {eo  : EventOrdering}
           (e   : Event)
           (s   : S),
      state_sm_before_event X e = Some s
      -> state_sm_on_event X e = fst (sm_update X s (trigger e))
         /\ output_sm_on_event X e = Some (snd (sm_update X s (trigger e))).
  Proof.
    intros S O X eo.
    induction e as [e ind] using predHappenedBeforeInd; introv hsx; simpl in *.

    rewrite state_sm_before_event_unroll in hsx.
    destruct (dec_isFirst e) as [d|d]; simpl in *; ginv.

    - rewrite state_sm_on_event_unroll.
      rewrite output_sm_on_event_unroll.
      destruct (dec_isFirst e); tcsp; GC.

    - remember (state_sm_before_event X (local_pred e)) as sbop.
      symmetry in Heqsbop; destruct sbop; simpl in *; ginv.
      rewrite state_sm_on_event_unroll.
      rewrite output_sm_on_event_unroll.
      destruct (dec_isFirst e); tcsp; GC.
      eapply ind in Heqsbop;
        [|apply local_pred_is_direct_pred;auto].
      repnd; simpl in *.
      allrw; simpl; tcsp.
  Qed.*)

  Lemma state_sm_before_event_as_initial :
    forall {S O} (X : StateMachine S msg O) {eo : EventOrdering} (e : Event),
      isFirst e
      -> state_sm_before_event X e = Some (sm_state X).
  Proof.
    introv isf.
    rewrite state_sm_before_event_unroll.
    destruct (dec_isFirst e) as [d1|d1]; tcsp.
  Qed.

  Lemma state_sm_on_event_as_update_initial :
    forall {S O} (X : StateMachine S msg O) {eo : EventOrdering} (e : Event),
      isFirst e
      -> state_sm_on_event X e = op_state X (sm_state X) (trigger e).
  Proof.
    introv isf.
    rewrite state_sm_on_event_unroll.
    destruct (dec_isFirst e) as [d1|d1]; tcsp.
  Qed.

  Lemma implies_eq_fst :
    forall (A B : Type) (x y : A * B), x = y -> fst x = fst y.
  Proof.
    introv h.
    destruct x, y; ginv.
  Qed.

  Lemma implies_eq_snd :
    forall (A B : Type) (x y : A * B), x = y -> snd x = snd y.
  Proof.
    introv h.
    destruct x, y; ginv.
  Qed.

  Definition SM_state_before_event {S SX U}
             (sm : StateMachine (S * SX) msg U)
             {eo : EventOrdering}
             (e  : Event)
             (s  : S) : Prop :=
    match state_sm_before_event sm e with
    | Some (x,_) => x = s
    | None => False
    end.

  Definition SM_state_on_event {S SX U}
             (sm : StateMachine (S * SX) msg U)
             {eo : EventOrdering}
             (e  : Event)
             (s  : S) : Prop :=
    match state_sm_on_event sm e with
    | Some (x,_) => x = s
    | None => False
    end.

  Lemma SM_state_before_event_implies_exists :
    forall {S SX U}
           (sm : StateMachine (S * SX) msg U)
           {eo : EventOrdering}
           (e  : Event)
           (s  : S),
      SM_state_before_event sm e s
      -> exists sx, state_sm_before_event sm e = Some (s, sx).
  Proof.
    introv h.
    unfold SM_state_before_event in h.
    dest_cases w; dest_cases y; subst; simpl in *.
    eexists; eauto.
  Qed.

  Lemma state_sm_on_event_if_before_event_direct_pred :
    forall {S O} {eo : EventOrdering} (e1 e2 : Event) (sm : StateMachine S msg O) st,
      (e1) ⊂ (e2)
      -> state_sm_before_event sm e2 = Some st
      -> state_sm_on_event sm e1 = Some st.
  Proof.
    introv lte eqst.
    applydup pred_implies_local_pred in lte; subst.
    rewrite state_sm_before_event_as_state_sm_on_event_pred in eqst; eauto 2 with eo.
  Qed.
  Hint Resolve state_sm_on_event_if_before_event_direct_pred : proc.

  Lemma output_sm_on_event_none_implies_state_sm_before_event_none :
    forall {S O} (X : StateMachine S msg O) {eo : EventOrdering} (e : Event),
      all_correct eo
      -> output_sm_on_event X e = None
      -> state_sm_before_event X e = None.
  Proof.
    introv allc.
    induction e as [e ind] using predHappenedBeforeInd; introv h; simpl.
    rewrite output_sm_on_event_unroll in h.
    destruct (dec_isFirst e) as [d|d]; simpl in *.

    - rewrite state_sm_before_event_unroll.
      destruct (dec_isFirst e); tcsp; GC.
      pose proof (allc e) as q.
      apply isCorrect_implies_msg in q.
      exrepnd; rewrite q0 in *; simpl in *; ginv.

    - remember (state_sm_on_event X (local_pred e)) as sop.
      symmetry in Heqsop; destruct sop; simpl in *; ginv.

      { pose proof (allc e) as q.
        apply isCorrect_implies_msg in q.
        exrepnd; rewrite q0 in *; simpl in *; ginv. }

      rewrite state_sm_before_event_as_state_sm_on_event_pred; auto.
  Qed.

  Lemma state_sm_on_event_mkSSM :
    forall {S O} {eo : EventOrdering} (e : Event) (upd : SUpdate S msg O) (init : S),
      all_correct eo
      -> ~ (state_sm_on_event (mkSSM upd init) e = None).
  Proof.
    introv allc.
    revert init.
    induction e as [e ind] using predHappenedBeforeInd; introv; simpl.
    rewrite state_sm_on_event_unroll.
    destruct (dec_isFirst e) as [d|d]; simpl in *; tcsp.

    - pose proof (allc e) as q.
      apply isCorrect_implies_msg in q.
      exrepnd; rewrite q0 in *; simpl in *; ginv.
      unfold S2Update, op_state; simpl; dest_cases w; simpl; intro xx; tcsp.

    - remember (state_sm_on_event (mkSSM upd init) (local_pred e)) as sop.
      symmetry in Heqsop; destruct sop; simpl.

      { pose proof (allc e) as q.
        apply isCorrect_implies_msg in q.
        exrepnd; rewrite q0 in *; simpl in *; ginv.
        unfold S2Update, op_state; simpl; dest_cases w; simpl; intro xx; tcsp. }

      apply ind in Heqsop; tcsp.
      apply local_pred_is_direct_pred; auto.
  Qed.

  Lemma state_sm_on_event_none_monotonic :
    forall {S O} (X : StateMachine S msg O) {eo : EventOrdering} (e e' : Event),
      e' ⊑ e
      -> state_sm_on_event X e' = None
      -> state_sm_on_event X e = None.
  Proof.
    intros S O X eo.
    induction e as [e ind] using predHappenedBeforeInd; introv lee eqnone; simpl.
    apply localHappenedBeforeLe_implies_or2 in lee; repndors; subst; auto;[].
    rewrite state_sm_on_event_unroll.

    destruct (dec_isFirst e) as [d|d]; simpl in *;
      [apply no_local_predecessor_if_first in lee; tcsp|];[].

    remember (state_sm_on_event X (local_pred e)) as sop.
    symmetry in Heqsop; destruct sop; simpl in *; auto;[].
    pose proof (ind (local_pred e)) as h; autodimp h hyp; clear ind;
      [apply local_pred_is_direct_pred;auto|];[].

    apply h in eqnone;[rewrite eqnone in Heqsop; ginv|].
    apply localHappenedBefore_implies_le_local_pred; auto.
  Qed.

  Definition no_loutput_sm_on_event_prior_to {S O}
             (X  : StateMachine S msg (list O))
             {eo : EventOrdering}
             (e  : Event) : Prop :=
    forall e' x, e' ⊏ e -> ~ In x (loutput_sm_on_event X e').

  Definition state_sm_before_event_exists {S O}
             (X  : StateMachine S msg (list O))
             {eo : EventOrdering}
             (e  : Event) : Prop :=
    exists s,  state_sm_before_event X e = Some s.

  (* e ---> e' ---> e'' *)
  Lemma state_sm_before_event_sub_sub_so_as_sub_eo :
    forall {S SX O}
           (X   : StateMachine (S * SX) msg O)
           {eo  : EventOrdering}
           (e   : Event)
           (e'  : subEventOrdering_type e)
           (e'' : @subEventOrdering_type pn pk pm (subEventOrdering e) e'),
      loc e' = loc e''
      -> @state_sm_before_event
           _ _ X
           (@subEventOrdering pn pk pm (@subEventOrdering pn pk pm eo e) e')
           e''
         =
         @state_sm_before_event
           _ _ X
           (@subEventOrdering pn pk pm eo e')
           (sub_sub_event2sub_event eo e e' e'').
  Proof.
    intros S SX O X eo e e'.
    induction e'' as [e'' ind] using (@predHappenedBeforeInd _ _ _ (@subEventOrdering _ _ _ (@subEventOrdering _ _ _ eo e) e')); introv eqloc; simpl.

    rewrite (state_sm_before_event_unroll X); symmetry.
    rewrite (state_sm_before_event_unroll X); symmetry.

    destruct (dec_isFirst e'') as [d1|d1]; simpl in *.

    - destruct (@dec_isFirst _ _ _ (subEventOrdering (sub_eo_event e e')) (sub_sub_event2sub_event eo e e' e'')) as [d2|d2];
        simpl in *; auto;[].

      destruct e' as [e' conde']; simpl in *.
      destruct e'' as [e'' conde''1]; simpl in *.
      destruct e'' as [e'' conde''2]; simpl in *.

      clear ind.
      destruct d2.

      apply isFirstSubEvent_iff in d1; simpl in *.
      dest_cases w; ginv.

      inversion d1 as [z]; clear d1; subst.
      apply isFirstSubEvent_iff.
      dest_cases w.

    - destruct (@dec_isFirst _ _ _ (subEventOrdering (sub_eo_event e e')) (sub_sub_event2sub_event eo e e' e'')) as [d2|d2];
        simpl in *; auto.

      + destruct d1.
        clear ind.
        apply isFirstSubEvent_iff in d2; simpl in *.
        destruct e' as [e' conde']; simpl in *.
        destruct e'' as [e'' conde''1]; simpl in *.
        destruct e'' as [e'' conde''2]; simpl in *.
        dest_cases w; simpl in *;[]; subst.

        apply implies_isFirstSubEvent; simpl.
        dest_cases w.
        f_equal; apply UIP_dec; apply bool_dec.

      + rewrite ind; simpl; auto; clear ind.

        * repeat rewrite subEventOrdering_trigger_sub_eo.
          assert (sub_sub_event2sub_event
                    eo e e'
                    (@local_pred
                       _ _ _ (@subEventOrdering
                                _ _ _ (@subEventOrdering
                                         _ _ _ eo e) e') e'')
                  =
                  @local_pred
                    _ _ _
                    (@subEventOrdering _ _ _ eo (@sub_eo_event _ _ _ eo e e'))
                    (sub_sub_event2sub_event eo e e' e'')) as xx;
            [|rewrite xx;auto];[].

          apply implies_eq_in_sub_eo; simpl.
          rewrite sub_eo_event_sub_sub_event2sub_event.

          rewrite sub_eo_local_pred_if_not_first; auto.
          symmetry.
          rewrite sub_eo_local_pred_if_not_first; auto.
          rewrite sub_eo_event_sub_sub_event2sub_event.
          symmetry.
          rewrite sub_eo_local_pred_if_not_first; auto.

          introv q.

          clear eqloc d2.
          apply isFirstSubEvent_iff in q; dest_cases w.

          { destruct d1.
            apply isFirstSubEvent_iff.
            dest_cases w.

            - destruct e' as [e' conde'].
              destruct e'' as [e'' conde''1].
              destruct e'' as [e'' conde''2].
              simpl in *; subst.
              apply implies_eq_in_sub_eo; simpl.
              apply subEventOrdering_cond_bool_iff in conde''1.
              unfold subEventOrdering_cond in conde''1; simpl in*.
              autodimp conde''1 hyp.
              apply happenedBeforeLe_subEventOrdering_implies in conde''1; simpl in *.
              apply subEventOrdering_cond_bool_iff in conde'.
              unfold subEventOrdering_cond in conde'; simpl in*.
              autodimp conde' hyp.
              destruct conde' as [h1|h1]; auto.
              destruct conde''1 as [h2|h2]; auto.
              eapply causal_trans in h1;[|exact h2].
              apply causal_anti_reflexive in h1; tcsp.

            - apply isFirstSubEvent_iff.
              dest_cases w. }

          { destruct d1.
            apply isFirstSubEvent_iff.
            dest_cases w.

            - destruct e' as [e' conde'].
              destruct e'' as [e'' conde''1].
              destruct e'' as [e'' conde''2].
              simpl in *; subst.
              apply implies_eq_in_sub_eo; simpl.
              apply subEventOrdering_cond_bool_iff in conde''1.
              unfold subEventOrdering_cond in conde''1; simpl in*.
              autodimp conde''1 hyp.
              apply happenedBeforeLe_subEventOrdering_implies in conde''1; simpl in *.
              destruct conde''1 as [h2|h2]; auto.
              apply (no_local_predecessor_if_first e'' e') in q.
              destruct q; split; auto.

            - apply isFirstSubEvent_iff.
              dest_cases w. }

        * clear eqloc d2.
          unfold local_pred.
          unfold isFirst in d1.
          remember (@direct_pred _ _ _ (@subEventOrdering _ _ _ (@subEventOrdering _ _ _ eo e) e') e'') as dp.
          destruct dp; tcsp.

        * rewrite sub_eo_local_pred_if_not_first; auto; simpl.
          autorewrite with eo in *; auto.
          clear d1 d2.
          destruct e' as [e' conde'].
          destruct e'' as [e'' conde''1].
          destruct e'' as [e'' conde''2].
          simpl in *; auto.
  Qed.

  (* e ---> e' ---> e'' *)
  Lemma SM_state_before_event_sub_sub_so_as_sub_eo :
    forall {S SX O}
           (X   : StateMachine (S * SX) msg O)
           {eo  : EventOrdering}
           (e   : Event)
           (e'  : subEventOrdering_type e)
           (e'' : @subEventOrdering_type pn pk pm (subEventOrdering e) e')
           (s   : S),
      loc e' = loc e''
      -> @SM_state_before_event
           _ _ _ X
           (@subEventOrdering pn pk pm (@subEventOrdering pn pk pm eo e) e')
           e''
           s
         <->
         @SM_state_before_event
           _ _ _ X
           (@subEventOrdering pn pk pm eo e')
           (sub_sub_event2sub_event eo e e' e'')
           s.
  Proof.
    introv eqloc.
    unfold SM_state_before_event.
    rewrite state_sm_before_event_sub_sub_so_as_sub_eo; tcsp.
  Qed.

  Lemma MhaltedSM_output :
    forall {S} {eo : EventOrdering} (e : Event) (s : S) m,
      ~ In m (loutput_sm_on_event (MhaltedSM s) e).
  Proof.
    introv h.
    rewrite loutput_sm_on_event_unroll in h; simpl in h.
    destruct (dec_isFirst e) as [d|d]; simpl in *; tcsp.

    { apply in_op_outputs_iff in h; exrepnd; ginv. }

    match goal with
    | [ H : context[option_map _ ?x] |- _ ] => remember x as sop
    end.
    destruct sop; simpl in *; auto.
    apply in_op_outputs_iff in h; exrepnd; ginv.
  Qed.

  Lemma Deq_unit : Deq unit.
  Proof.
    introv; destruct x, y; prove_dec.
  Defined.

  Lemma SM_state_on_event_implies_exists :
    forall {S SX U}
           (sm : StateMachine (S * SX) msg U)
           {eo : EventOrdering}
           (e  : Event)
           (s  : S),
      SM_state_on_event sm e s
      -> exists sx, state_sm_on_event sm e = Some (s, sx).
  Proof.
    introv h.
    unfold SM_state_on_event in h.
    dest_cases w; dest_cases y; subst; simpl in *.
    eexists; eauto.
  Qed.

  Lemma state_sm_before_event_if_on_event_direct_pred :
    forall {S O} {eo : EventOrdering} (e1 e2 : Event) (sm : StateMachine S msg O) st,
      (e1) ⊂ (e2)
      -> state_sm_on_event sm e1 = Some st
      -> state_sm_before_event sm e2 = Some st.
  Proof.
    introv lte eqst.
    applydup pred_implies_local_pred in lte; subst.
    rewrite state_sm_before_event_as_state_sm_on_event_pred; eauto 2 with eo.
  Qed.
  Hint Resolve state_sm_before_event_if_on_event_direct_pred : proc.

  Lemma state_sm_before_event_some_between :
    forall {S O} {eo : EventOrdering} (e1 e2 : Event) (sm : StateMachine S msg O) s,
      e1 ⊑ e2
      -> ~ isFirst e1
      -> state_sm_before_event sm e2 = Some s
      -> exists s', state_sm_before_event sm e1 = Some s'.
  Proof.
    intros S O eo e1 e2.
    induction e2 as [e2 ind] using predHappenedBeforeInd; introv lee nfirst eqst.

    applydup @localHappenedBeforeLe_implies_or in lee; repndors; subst; tcsp.

    { eexists; eauto. }

    rewrite state_sm_before_event_unroll in eqst.
    destruct (dec_isFirst e2) as [d|d]; ginv.

    { apply isFirst_localHappenedBeforeLe_implies_eq in lee; auto; subst; tcsp. }

    remember (state_sm_before_event sm (local_pred e2)) as q; symmetry in Heqq.
    destruct q; simpl in *; ginv.
    apply ind in Heqq; auto; eauto 4 with eo.
  Qed.

  Lemma state_sm_on_event_some_between :
    forall {S O} {eo : EventOrdering} (e1 e2 : Event) (sm : StateMachine S msg O) s,
      e1 ⊑ e2
      -> ~ isFirst e1
      -> state_sm_on_event sm e2 = Some s
      -> exists s', state_sm_on_event sm e1 = Some s'.
  Proof.
    intros S O eo e1 e2.
    induction e2 as [e2 ind] using predHappenedBeforeInd; introv lee nfirst eqst.

    applydup @localHappenedBeforeLe_implies_or in lee; repndors; subst; tcsp.

    { eexists; eauto. }

    rewrite state_sm_on_event_unroll in eqst.
    destruct (dec_isFirst e2) as [d|d]; ginv.

    { apply isFirst_localHappenedBeforeLe_implies_eq in lee; auto; subst; tcsp. }

    remember (state_sm_on_event sm (local_pred e2)) as q; symmetry in Heqq.
    destruct q; simpl in *; ginv.
    apply ind in Heqq; auto; eauto 4 with eo.
  Qed.

  Lemma state_sm_on_event_some_between2 :
    forall {S O} {eo : EventOrdering} (e1 e2 : Event) (sm : StateMachine S msg O) s,
      e1 ⊑ e2
      -> state_sm_on_event sm e2 = Some s
      -> exists s', state_sm_on_event sm e1 = Some s'.
  Proof.
    intros S O eo e1 e2.
    induction e2 as [e2 ind] using predHappenedBeforeInd; introv lee eqst.

    applydup @localHappenedBeforeLe_implies_or in lee; repndors; subst; tcsp.

    { eexists; eauto. }

    rewrite state_sm_on_event_unroll in eqst.
    destruct (dec_isFirst e2) as [d|d]; ginv.

    { apply isFirst_localHappenedBeforeLe_implies_eq in lee; auto; subst; tcsp.
      apply op_state_some_iff in eqst; exrepnd; simpl in *.
      rewrite state_sm_on_event_as_update_initial; auto.
      exists s.
      rewrite op_state_some_iff.
      exists i; dands; auto. }

    remember (state_sm_on_event sm (local_pred e2)) as q; symmetry in Heqq.
    destruct q; simpl in *; ginv.
    apply ind in Heqq; auto; eauto 4 with eo.
  Qed.

  Lemma state_sm_before_event_some_between2 :
    forall {S O} {eo : EventOrdering} (e1 e2 : Event) (sm : StateMachine S msg O) s,
      e1 ⊑ e2
      -> state_sm_before_event sm e2 = Some s
      -> exists s', state_sm_before_event sm e1 = Some s'.
  Proof.
    introv lee eqst.
    destruct (dec_isFirst e1) as [d|d]; ginv.

    { rewrite state_sm_before_event_as_initial; auto.
      eexists; eauto. }

    eapply state_sm_before_event_some_between; eauto.
  Qed.

  Lemma state_sm_before_event_some_between3 :
    forall {S O} {eo : EventOrdering} (e1 e2 : Event) (sm : StateMachine S msg O) s,
      e1 ⊑ e2
      -> state_sm_on_event sm e2 = Some s
      -> exists s', state_sm_before_event sm e1 = Some s'.
  Proof.
    introv lee eqst.
    destruct (dec_isFirst e1) as [d|d]; ginv.

    { rewrite state_sm_before_event_as_initial; auto.
      eexists; eauto. }

    rewrite state_sm_on_event_unroll2 in eqst.
    remember (state_sm_before_event sm e2) as s'.
    destruct s'; simpl in *; ginv;[].
    symmetry in Heqs'.

    eapply state_sm_before_event_some_between; eauto.
  Qed.

  Lemma output_system_on_event_ldata_implies_state_sm_on_event :
    forall {S} (s : MUSystem S) {eo : EventOrdering} (e  : Event) m,
      In m (output_system_on_event_ldata s e)
      -> (forall x i, exists s', fst (sm_update (s (loc e)) x i) = Some s')
      -> exists st, state_sm_on_event (s (loc e)) e = Some st.
  Proof.
    introv i imp.
    unfold output_system_on_event_ldata in i.
    unfold state_sm_on_event.
    unfold output_system_on_event in i.
    unfold run_system_on_event_sm in i.
    unfold run_sm_on_event in i.
    remember (run_sm_on_event_state (s (loc e)) e) as r; symmetry in Heqr.
    destruct r; simpl in *; tcsp;[].
    repnd; simpl in *.
    destruct p0; simpl in *; tcsp.
    { eexists; eauto. }

    unfold run_sm_on_event_state in Heqr.
    unfold run_update_on_event in Heqr; simpl in *.

    match goal with
    | [ H : map_option _ ?w = _ |- _ ] => remember w as z
    end.
    destruct z; simpl in *; ginv.
    apply op_update_some_iff in Heqr; exrepnd.
    pose proof (imp s0 i0) as q; exrepnd.
    rewrite <- Heqr0 in *; simpl in *; ginv.
  Qed.

  Lemma state_sm_on_event_some_implies_has_correct_trace_before :
    forall {S O} (sm : StateMachine S msg O) (eo : EventOrdering) (e : Event) i s,
      loc e = i
      -> state_sm_on_event sm e = Some s
      -> has_correct_trace_before e i.
  Proof.
    intros S O sm eo e.
    induction e as [? IND] using HappenedBeforeInd;[].
    introv eqloci eqst.

    rewrite state_sm_on_event_unroll in eqst.
    destruct (dec_isFirst e) as [d|d]; simpl in *.

    - introv lee1 eqloc lee2.

      assert (e' ⊑ e) as lee3 by (split; allrw; auto).

      pose proof (isFirst_localHappenedBeforeLe_implies_eq lee3 d) as q; subst; GC.
      clear lee3 lee1.

      pose proof (isFirst_localHappenedBeforeLe_implies_eq lee2 d) as q; subst; GC.

      remember (trigger e) as trig; symmetry in Heqtrig; destruct trig; simpl in *; eauto 3 with eo.
      unfold op_state in *; simpl in *; ginv.

    - remember (state_sm_on_event sm (local_pred e)) as s'.
      symmetry in Heqs'.
      destruct s'; simpl in *; ginv.
      pose proof (IND (local_pred e)) as h; autodimp h hyp; eauto 3 with eo.
      pose proof (h i s0) as h; autorewrite with eo in *.
      repeat (autodimp h hyp).

      remember (trigger e) as trig; symmetry in Heqtrig; destruct trig; simpl in *;
        unfold op_state in *; simpl in *; ginv; eauto 3 with eo.
  Qed.
  Hint Resolve state_sm_on_event_some_implies_has_correct_trace_before : eo proc.

  Lemma isCorrect_first_implies_has_correct_trace_before :
    forall (eo : EventOrdering) (e : Event),
      isCorrect e
      -> isFirst e
      -> has_correct_trace_before e (loc e).
  Proof.
    introv cor isf.
    introv lee1 eqloc2 lee2.
    assert (e' ⊑ e) as lee3 by (split; allrw; auto).

    pose proof (isFirst_localHappenedBeforeLe_implies_eq lee3 isf) as q; subst; GC.
    clear lee3 lee1.

    pose proof (isFirst_localHappenedBeforeLe_implies_eq lee2 isf) as q; subst; GC.

    remember (trigger e) as trig; symmetry in Heqtrig; destruct trig; simpl in *; eauto 3 with eo.
  Qed.
  Hint Resolve isCorrect_first_implies_has_correct_trace_before : eo proc.

  Lemma state_sm_before_event_some_implies_has_correct_trace_before :
    forall {S O} (sm : StateMachine S msg O) (eo : EventOrdering) (e : Event) s,
      isCorrect e
      -> state_sm_before_event sm e = Some s
      -> has_correct_trace_before e (loc e).
  Proof.
    introv iscor eqst.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in eqst.
    destruct (dec_isFirst e) as [d|d]; ginv; eauto 3 with proc eo.
    apply has_correct_trace_before_local_pred_implies; auto.
    eapply state_sm_on_event_some_implies_has_correct_trace_before; autorewrite with eo; eauto.
  Qed.
  Hint Resolve state_sm_before_event_some_implies_has_correct_trace_before : eo proc.

  Lemma state_sm_on_event_some_implies_node_has_correct_trace_before :
    forall {S O} (sm : StateMachine S msg O) (eo : EventOrdering) (e : Event) i s,
      loc e = node2name i
      -> state_sm_on_event sm e = Some s
      -> node_has_correct_trace_before e i.
  Proof.
    introv eqloc eqst.
    try (unfold node_has_correct_trace_before; eauto 3 with eo);
      try (eapply state_sm_on_event_some_implies_has_correct_trace_before; eauto).
  Qed.
  Hint Resolve state_sm_on_event_some_implies_node_has_correct_trace_before : eo proc.

  Lemma isCorrect_first_implies_node_has_correct_trace_before :
    forall (eo : EventOrdering) (e : Event) i,
      loc e = node2name i
      -> isCorrect e
      -> isFirst e
      -> node_has_correct_trace_before e i.
  Proof.
    introv eqloc cor isf.
    pose proof (isCorrect_first_implies_has_correct_trace_before eo e cor isf) as q.
    rewrite eqloc in q; auto.
  Qed.
  Hint Resolve isCorrect_first_implies_node_has_correct_trace_before : eo proc.

  Lemma state_sm_before_event_some_implies_node_has_correct_trace_before :
    forall {S O} (sm : StateMachine S msg O) (eo : EventOrdering) (e : Event) i s,
      loc e = node2name i
      -> isCorrect e
      -> state_sm_before_event sm e = Some s
      -> node_has_correct_trace_before e i.
  Proof.
    introv eqloc iscor eqst.
    pose proof (state_sm_before_event_some_implies_has_correct_trace_before sm eo e s iscor eqst) as q.
    rewrite eqloc in q; auto.
  Qed.
  Hint Resolve state_sm_before_event_some_implies_node_has_correct_trace_before : eo proc.

End Process.


Hint Rewrite @run_process_on_list_haltedProc : proc.


Hint Resolve state_sm_on_event_if_before_event_direct_pred : proc.
Hint Resolve implies_authenticated_messages_were_sent_non_byz_usys : proc.
Hint Resolve state_sm_on_event_some_implies_has_correct_trace_before : eo proc.
Hint Resolve isCorrect_first_implies_has_correct_trace_before : eo proc.
Hint Resolve state_sm_before_event_some_implies_has_correct_trace_before : eo proc.

Hint Resolve state_sm_on_event_some_implies_node_has_correct_trace_before : eo proc.
Hint Resolve isCorrect_first_implies_node_has_correct_trace_before : eo proc.
Hint Resolve state_sm_before_event_some_implies_node_has_correct_trace_before : eo proc.


Delimit Scope proc with proc.

Arguments MkSM      [S] [I] [O] _(*halted?*) _(*update*) _(*initial state*).
Arguments sm_halted [S] [I] [O] _.
Arguments sm_state  [S] [I] [O] _.
Arguments sm_update [S] [I] [O] _(*type*) _(*state*) _(*input*).
