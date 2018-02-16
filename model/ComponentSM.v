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


Section ComponentSM.
  Context { pd  : @Data }.
  Context { pn  : @Node }.
  Context { pk  : @Key }.
  Context { pat : @AuthTok }.
  Context { paf : @AuthFun pn pk pat pd }.
  Context { pm  : @Msg }.
  Context { pda : @DataAuth pd pn }.

  Definition CompName := String.string.

  (* component *)
  Definition p_nproc (p : CompName -> Type) := { cn : CompName & p cn }%type.
  (* list of components *)
  Definition p_procs (p : CompName -> Type) := list (p_nproc p).

  (* monad of the component *)
  Definition M_p (p : CompName -> Type) (PO : Type) :=
    p_procs p -> (p_procs p * PO)%type.

  (* monad update function of the component that can halt *)
  Definition MP_Update (p : CompName -> Type) (I O S : Type) :=
    S -> I -> M_p p (option S * O).

  (* component interface *)
  Record ComponentIO :=
    MkComponentIO
      {
        cio_I : Type;
        cio_O : Type;
        cio_default_O : cio_O;
      }.

  (* component that works with DirectedMsgs *)
  Definition CIOmsg : ComponentIO :=
    MkComponentIO msg DirectedMsgs [].

  (* A default CIO *)
  Definition CIOdef : ComponentIO :=
    MkComponentIO unit unit tt.

  (* interface of the single component *)
  Class baseFunIO :=
    MkBaseFunIO
      {
        bfio : CompName -> ComponentIO;
      }.

  Context { base_fun_io : baseFunIO }.

  (* interface of the single component *)
  Class funIO :=
    MkFunIO
      {
        fio : CompName -> ComponentIO;
      }.

  Definition msg_comp_name : CompName := "MSG".

  (* We constrain here that components with named [msg_comp_name] have to be
     message components, i.e., taking in messages and returning directed messages *)
  Global Instance funIOd_msg : funIO :=
    MkFunIO (fun nm =>
               if String.string_dec nm msg_comp_name then CIOmsg
               else bfio nm).

  (* state machine as monad -- one level state machine*)
  Record MP_StateMachine (p : CompName -> Type) (cn : CompName) : Type :=
    MkMPSM
      {
        sm_S      : Type;
        sm_halted : bool;
        sm_update :> MP_Update p (cio_I (fio cn)) (cio_O (fio cn)) sm_S;
        sm_state  : sm_S;
      }.
  Arguments MkMPSM    [p] [cn] _ _ _ _.
  Arguments sm_S      [p] [cn] _.
  Arguments sm_halted [p] [cn] _.
  Arguments sm_update [p] [cn] _ _ _ _.
  Arguments sm_state  [p] [cn] _.

  Definition NFalse (cn : CompName) : Type := False.

  (* state machine that can have several levels as monad *)
  Fixpoint M_StateMachine (n : nat) (cn : CompName) : Type :=
    match n with
    | 0 => False (*MP_StateMachine NFalse cn*)
    | S n => MP_StateMachine (M_StateMachine n) cn [+] M_StateMachine n cn
    end.

  (* list of state machines; each state machine can have several levels *)
  Definition n_proc := M_StateMachine.
  Definition n_nproc (n : nat) := {cn : CompName & n_proc n cn }.
  Definition n_procs (n : nat) := list (n_nproc n).

  (* monad of the list of state machines; each state machine can have several levels *)
  Definition M_n (n : nat) (PO : Type) := n_procs n -> (n_procs n * PO)%type.

  (* monad update function that can halt *)
  Definition M_Update (n : nat) (nm : CompName) (S : Type) :=
    S -> cio_I (fio nm) -> M_n n (option S * cio_O (fio nm)).

  (* return state and outpu ? *)
  Definition ret {A} (n : nat) (a : A) : M_n n A := fun s => (s, a).

  (* enables combining multiple state machine monads *)
  Definition bind {A B} {n:nat} (m : M_n n A) (f : A -> M_n n B) : M_n n B :=
    fun s =>
      let (s1,a) := m s in
      let (s2,b) := f a s1 in
      (s2,b).

  Notation "a >>= f" := (bind a f) (at level 100).

  (* in a list of monad processes, find the one that has a Component Name nm *)
  Fixpoint find_name {n:nat} (nm : CompName) (l : n_procs n) : option (n_proc n nm) :=
    match l with
    | [] => None
    | existT _ m pr :: rest =>
      match String.string_dec m nm with
      | left q => Some (eq_rect _ _ pr _ q)
      | right _ => find_name nm rest
      end
    end.

  Fixpoint replace_name {n:nat} {nm : CompName} (pr : n_proc n nm) (l : n_procs n) : n_procs n :=
    match l with
    | [] => []
    | existT _ m q :: rest =>
      if String.string_dec m nm then existT _ nm pr :: rest
      else existT _ m q :: replace_name pr rest
    end.

  (* halted state machine as monad -- one level state machine*)
  Definition MP_haltedSM {S}
             (n  : nat)
             (nm : CompName)
             (d  : S) : MP_StateMachine (n_proc n) nm :=
    MkMPSM
      S
      true
      (fun s i p => (p, (None, cio_default_O (fio nm))))
      d.

  (* halted state machine as monad -- state machine can have multiple levels*)
  Definition M_haltedSM {S}
             (nm : CompName)
             (n : nat)
             (d  : S) : M_StateMachine 1 nm :=
    inl (MkMPSM
           S
           true
           (fun s i p => (p, (None, cio_default_O (fio nm))))
           d).

  (* incr of one level state machine monad *)
  Definition incr_n_proc {n} {nm} (p : n_proc n nm) : n_proc (S n) nm := inr p.

  (* incr of state machine monad -each state machine can have multiple levels *)
  Definition incr_n_nproc {n} (p : n_nproc n) : n_nproc (S n) :=
    match p with
    | existT _ m q =>
      existT _ m (incr_n_proc q)
    end.

  (* incr list of state machine monads -- each state machine can have multiple levels *)
  Definition incr_n_procs {n} (ps : n_procs n) : n_procs (S n) :=
    map incr_n_nproc ps.

(*  (* halted monad of the state machine -- each state machine that can have several levels*)
  Fixpoint M_haltedSM_n {S}
           (n  : nat)
           (nm : CompName)
           (d  : S) : M_StateMachine n nm :=
    match n with
    | 0 => M_haltedSM nm d
    | S m => incr_n_proc (M_haltedSM_n m nm d)
    end.*)

  Definition decr_n_proc {n} {nm} : n_proc n nm -> option (n_proc (Init.Nat.pred n) nm) :=
    match n with
    | 0 => fun p => Some p
    | S m => fun p =>
               match p with
               | inl _ => None
               | inr q => Some q
               end
    end.

  Definition decr_n_nproc {n} (np : n_nproc n) : option (n_nproc (Init.Nat.pred n)) :=
    match np with
    | existT _ m p =>
      match decr_n_proc p with
      | Some q => Some (existT _ m q)
      | None => None
      end
    end.

  Definition decr_n_procs {n} (ps : n_procs n) : n_procs (Init.Nat.pred n) :=
    mapOption decr_n_nproc ps.

  Definition incr_pred_n_proc {n} {nm} : n_proc (pred n) nm -> n_proc n nm :=
    match n with
    | 0 => fun p => p
    | S m => inr
    end.

  Definition incr_pred_n_nproc {n} (p : n_nproc (pred n)) : n_nproc n :=
    match p with
    | existT _ m q =>
      existT _ m (incr_pred_n_proc q)
    end.

  Definition incr_pred_n_procs {n} (ps : n_procs (pred n)) : n_procs n :=
    map incr_pred_n_nproc ps.

  Definition lift_M {m} {nm} {O}
             (x : M_p (n_proc m) (MP_StateMachine (n_proc m) nm * O))
    : M_n m (M_StateMachine (S m) nm * O) :=
    fun ps =>
      let (k, qo) := x ps in
      let (q, o) := qo in
      (k, (injL(q), o)).

  Definition lift_M2 {n} {nm} {O} (m : M_n (pred n) (M_StateMachine n nm * O))
    : M_n (pred (S n)) (M_StateMachine (S n) nm * O) :=
    fun (ps : n_procs n) =>
      match m (decr_n_procs ps) with
      | (ps',(p',o)) => (incr_pred_n_procs ps', (incr_n_proc p',o))
      end.

  Definition update_state {p} {cn} (sm : MP_StateMachine p cn) (s : sm_S sm) : MP_StateMachine p cn :=
    MkMPSM
      (sm_S      sm)
      (sm_halted sm)
      (sm_update sm)
      s.

  Definition halt_machine {p} {cn} (sm : MP_StateMachine p cn) : MP_StateMachine p cn :=
    MkMPSM
      (sm_S      sm)
      true
      (sm_update sm)
      (sm_state  sm).

  Definition sm_s_to_sm {n} {nm}
             (sm : MP_StateMachine (n_proc n) nm)
             (x : M_n n (option (sm_S sm) * cio_O (fio nm)))
    : M_n n (MP_StateMachine (n_proc n) nm * cio_O (fio nm)) :=
    x >>= fun so =>
            let (ops,o) := so in
            match ops with
            | Some s => ret _ (update_state sm s,o)
            | None => ret _ (halt_machine sm, o)
            end.

  Fixpoint app_m_proc {n} {nm}
    : M_StateMachine n nm
      -> cio_I (fio nm)
      -> option (M_n (pred n) (M_StateMachine n nm * cio_O (fio nm))) :=
    match n return M_StateMachine n nm -> cio_I (fio nm) -> option (M_n (pred n) (M_StateMachine n nm * cio_O (fio nm))) with
    | 0 =>
      fun pr i =>
        (*Some (lift_M (sm_s_to_sm pr (sm_update pr (sm_state pr) i)))*)
        None
    | S m =>
      fun pr =>
        match pr with
        | inl sm => fun i => Some (lift_M (sm_s_to_sm sm (sm_update sm (sm_state sm) i)))
        | inr pr' => fun i => option_map lift_M2 (app_m_proc pr' i)
        end
    end.

  (* replace subprocess *)
  Fixpoint replace_sub {n} {nm}
           (ps : n_procs n)
           (p  : n_proc (pred n) nm) : n_procs n :=
    match ps with
    | [] => []
    | existT _ m q :: rest =>
      if String.string_dec nm m then existT _ nm (incr_pred_n_proc p) :: rest
      else existT _ m q :: replace_sub rest p
    end.

  (* replace subprocesses in a list*)
  Fixpoint replace_subs {n} (ps : n_procs n) (l : n_procs (pred n)) : n_procs n :=
    match l with
    | [] => ps
    | p :: rest =>
      match p with
      | existT _ nm q => replace_subs (replace_sub ps q) rest
      end
    end.

  Definition call_proc {n:nat} (nm : CompName) (i : cio_I (fio nm)) : M_n n (cio_O (fio nm)) :=
    fun (l : n_procs n) =>
      match find_name nm l with
      | Some pr =>
        match app_m_proc pr i with
        | Some f =>
          match f (decr_n_procs l) with
          | (l',(pr',o)) => (replace_subs (replace_name pr' l) l',o)
          end
        | None => (l,cio_default_O (fio nm))
        end
      | None => (l,cio_default_O (fio nm))
      end.

  (* We had to break the abstraction because Coq didn't like [build_m_process]. *)
  Definition build_mp_sm {n}
             {S}
             {nm  : CompName}
             (upd : M_Update n nm S)
             (s   : S) : MP_StateMachine (n_proc n) nm :=
    MkMPSM S false upd s.

  Definition build_m_sm {n}
             {St}
             {nm  : CompName}
             (upd : M_Update n nm St)
             (s   : St) : M_StateMachine (S n) nm :=
    inl (build_mp_sm upd s).

  Fixpoint run_n_proc {n} {nm} (p : n_proc n nm) (l : list (cio_I (fio nm)))
    : M_n (pred n) (list (cio_O (fio nm)) * n_proc n nm) :=
    match l with
    | [] => ret _ ([], p)
    | i :: rest =>
      match app_m_proc p i with
      | Some f =>
        f >>= fun x =>
        let (p',o) := x in
        (run_n_proc p' rest) >>= fun y =>
        let (outs,p'') := y in
        ret _ (o :: outs, p'')
      | None => ret _ ([], p)
      end
    end.

  Record LocalSystem :=
    MkLocalSystem
      {
        ls_level : nat;
        ls_main  :> n_nproc (S ls_level);
        ls_subs  : n_procs ls_level;
      }.

  Record message_local_system_constraint (s : LocalSystem) :=
    MkMessageLocalSystemConstratin
      {
        mlsc_I : cio_I (fio (projT1 (ls_main s))) = msg;
        mlsc_O : cio_O (fio (projT1 (ls_main s))) = DirectedMsgs;
      }.

  Definition run_local_system (s : LocalSystem) (l : list (cio_I (fio (projT1 (ls_main s))))) :=
    run_n_proc (projT2 (ls_main s)) l (ls_subs s).

  (*Definition M_NStateMachine (nm : CompName) (n : nat) := name -> M_StateMachine n nm.*)

  Definition M_USystem := name -> LocalSystem.

  Definition message_system_constraint (s : M_USystem) :=
    forall n, message_local_system_constraint (s n).

  (* This is a system with a constraint that the main component takes in messages
     and outputs directed messages *)
  Record M_MUSystem :=
    MkMMUSystem
      {
        msys_sys  :> M_USystem;
        msys_cond : message_system_constraint msys_sys;
      }.

  Definition M_op_update {S} {n} {nm}
             (upd : M_Update n nm S)
             (s   : S)
             (o   : option (cio_I (fio nm)))
    : M_n n (option (option S * cio_O (fio nm))) :=
    match o with
    | Some i => (upd s i) >>= fun so => ret _ (Some so)
    | None => ret _ None
    end.

  Definition M_op_op_update {S} {n} {nm}
             (upd : M_Update n nm S)
             (s   : S)
             (o   : option (cio_I (fio nm)))
    : option (M_n n (option S * cio_O (fio nm))) :=
    match o with
    | Some i => Some (upd s i)
    | None => None
    end.

  Definition M_op_sm_update {n} {nm}
             (sm  : M_StateMachine n nm)
             (iop : option (cio_I (fio nm)))
    : M_n (pred n) (option (M_StateMachine n nm * cio_O (fio nm))) :=
    match iop with
    | Some i => match app_m_proc sm i with
                | Some x => x >>= fun x => ret _ (Some x)
                | None => ret _ None
                end
    | None => ret _ None
    end.

  Fixpoint M_run_update_on_list {S} {n} {nm}
           (s   : S)
           (upd : M_Update n nm S)
           (l   : oplist (cio_I (fio nm))) : M_n n (option S) :=
    match l with
    | [] => ret _ (Some s)
    | Some a :: l =>
      (upd s a) >>= fun so =>
                      match so with
                      | (Some s', _) => M_run_update_on_list s' upd l
                      | _ => ret _ None
                      end
    | None :: _ => ret _ None
    end.

  (* extracts the type of states by going down a state machine until an MP machine *)
  Fixpoint sm2S {n} {nm} : n_proc n nm -> Type :=
    match n return n_proc n nm -> Type with
    | 0 => fun p => match p with end
    | S m => fun p =>
               match p with
               | inl q => sm_S q
               | inr q => sm2S q
               end
    end.

  Fixpoint sm2state {n} {nm} : forall (sm : n_proc n nm), sm2S sm :=
    match n return forall (sm : n_proc n nm), sm2S sm with
    | 0 => fun p => match p with end
    | S m => fun p =>
               match p with
               | inl q => sm_state q
               | inr q => sm2state q
               end
    end.

  Fixpoint sm2level {n} {nm} : n_proc n nm -> nat :=
    match n return n_proc n nm -> nat with
    | 0 => fun p => match p with end
    | S m => fun p =>
               match p with
               | inl q => m
               | inr q => sm2level q
               end
    end.

(*  Definition sm2update {n} {cn} : forall (sm : n_proc n cn), MP_Update (n_proc (sm2level sm)) (cio_I (fio cn)) (cio_O (fio cn)) (sm2S sm).
  Proof.
    induction n; introv; simpl in *.

    - destruct sm.

    - destruct sm; simpl in *.

      + exact (sm_update m).

      + apply IHn.
  Qed.*)

  Fixpoint sm2update {n} {cn}
    : forall (sm : n_proc n cn), M_Update (sm2level sm) cn (sm2S sm) :=
    match n with
    | 0 => fun sm => match sm with end
    | S m => fun sm =>
               match sm with
               | inl q => sm_update q
               | inr q => sm2update q
               end
    end.

  Fixpoint M_run_sm_on_list {n} {nm}
           (sm : M_StateMachine n nm)
           (l  : oplist (cio_I (fio nm))) : M_n (sm2level sm) (option (sm2S sm)) :=
   M_run_update_on_list (sm2state sm) (sm2update sm) l.

 (*Fixpoint M_run_sm_on_list {n} {nm}
           (sm : M_StateMachine n nm)
           (l  : oplist (cio_I (fio nm))) : M_n (pred n) (option (M_StateMachine n nm)) :=
    match l with
    | [] => ret _ (Some sm)
    | Some a :: l =>
      match app_m_proc sm a with
      | Some f => f >>= fun so => let (sm',_) := so in M_run_sm_on_list sm' l
      | None => ret _ None
      end
    | None :: _ => ret _ None
    end.*)

  Definition lift_M3 {n} {O} (m : M_n (pred n) O)
    : M_n (pred (S n)) O :=
    fun (ps : n_procs n) =>
      match m (decr_n_procs ps) with
      | (ps',o) => (incr_pred_n_procs ps', o)
      end.

  Fixpoint app_m_proc_state {n} {nm}
    : forall (sm : M_StateMachine n nm),
      cio_I (fio nm)
      -> option (M_n (pred n) (option (sm2S sm) * cio_O (fio nm))) :=
    match n return forall (sm : M_StateMachine n nm), cio_I (fio nm) -> option (M_n (pred n) (option (sm2S sm) * cio_O (fio nm))) with
    | 0 =>
      fun pr i =>
        (*Some (lift_M (sm_s_to_sm pr (sm_update pr (sm_state pr) i)))*)
        None
    | S m =>
      fun pr =>
        match pr with
        | inl sm => fun i => Some (sm_update sm (sm_state sm) i)
        | inr pr' => fun i => option_map lift_M3 (app_m_proc_state pr' i)
        end
    end.

  (*Fixpoint M_run_sm_on_list_state {n} {nm}
           (sm : M_StateMachine n nm)
           (l  : oplist (cio_I (fio nm))) : M_n (pred n) (option (sm2S sm)) :=
    match l with
    | [] => ret _ (Some (sm2state sm))
    | Some a :: l =>
      match app_m_proc_state sm a with
      | Some f => f >>= fun so => let (sm',_) := so in M_run_sm_on_list_state sm' l
      | None => ret _ None
      end
    | None :: _ => ret _ None
    end.*)

  Definition M_run_update_on_event {S} {n}
             (s    : S)
             (upd  : M_Update n msg_comp_name S)
             {eo   : EventOrdering}
             (e    : Event) : M_n n (option (option S * DirectedMsgs)) :=
    (M_run_update_on_list s upd (map trigger (@localPreds pn pk pm eo e)))
      >>= fun sop =>
            match sop with
            | Some s => M_op_update upd s (trigger e)
            | None => ret _ None
            end.

  Definition M_run_sm_on_event {n}
             (sm : M_StateMachine n msg_comp_name)
             {eo : EventOrdering}
             (e  : Event) : M_n (sm2level sm) (option (option (sm2S sm) * DirectedMsgs)) :=
    M_run_update_on_event (sm2state sm) (sm2update sm) e.

  Definition M_state_sm_on_event {n}
             (sm : M_StateMachine n msg_comp_name)
             {eo : EventOrdering}
             (e  : Event) : M_n (sm2level sm) (option (sm2S sm)) :=
  (M_run_sm_on_event sm e)
    >>= fun x =>
          match x with
          | Some (sm',msgs) => ret _ (Some (sm2state sm))
          | None => ret _ None
          end.

  Definition M_state_sm_before_event {n}
             (sm : M_StateMachine n msg_comp_name)
             {eo : EventOrdering}
             (e  : Event) : M_n (sm2level sm) (option (sm2S sm)) :=
    M_run_sm_on_list sm (map trigger (@localPreds pn pk pm eo e)).

End ComponentSM.

Notation "a >>= f" := (bind a f) (at level 100).
