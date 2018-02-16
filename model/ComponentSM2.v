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

  Definition CompName := String.string.

  Definition p_nproc (p : CompName -> Type) := { cn : CompName & p cn }%type.
  Definition p_procs (p : CompName -> Type) := list (p_nproc p).

  Definition M_p (p : CompName -> Type) (PO : Type) := p_procs p -> (p_procs p * PO)%type.

  Definition MP_Update (p : CompName -> Type) (I O S : Type) := S -> I -> M_p p (option S * O).

  Record ComponentIO :=
    MkComponentIO
      {
        cio_I : Type;
        cio_O : Type;
        cio_default_O : cio_O;
      }.

  Class funIO :=
    MkFunIO
      {
        fio : CompName -> ComponentIO
      }.

  Context { fun_io : funIO }.

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

  Fixpoint M_StateMachine (n : nat) (cn : CompName) : Type :=
    match n with
    | 0 => MP_StateMachine (fun cn => False) cn
    | S n => MP_StateMachine (M_StateMachine n) cn [+] M_StateMachine n cn
    end.

  Definition n_proc := M_StateMachine.
  Definition n_nproc (n : nat) := {cn : CompName & n_proc n cn }.
  Definition n_procs (n : nat) := list (n_nproc n).

  Definition M_n (n : nat) (PO : Type) := n_procs n -> (n_procs n * PO)%type.

  Definition M_Update (n : nat) (nm : CompName) (S : Type) :=
    S -> cio_I (fio nm) -> M_n n (option S * cio_O (fio nm)).

  Definition ret {A} (n : nat) (a : A) : M_n n A := fun s => (s, a).

  Definition bind {A B} {n:nat} (m : M_n n A) (f : A -> M_n n B) : M_n n B :=
    fun s =>
      let (s1,a) := m s in
      let (s2,b) := f a s1 in
      (s2,b).

  Notation "a >>= f" := (bind a f) (at level 100).

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

  Definition MP_haltedSM {S}
             (n  : nat)
             (nm : CompName)
             (d  : S) : MP_StateMachine (n_proc n) nm :=
    MkMPSM
      S
      true
      (fun s i p => (p, (None, cio_default_O (fio nm))))
      d.

  Definition M_haltedSM {S}
             (nm : CompName)
             (d  : S) : M_StateMachine 0 nm :=
    MkMPSM
      S
      true
      (fun s i p => (p, (None, cio_default_O (fio nm))))
      d.

  Definition incr_n_proc {n} {nm} (p : n_proc n nm) : n_proc (S n) nm := inr p.

  Definition incr_n_nproc {n} (p : n_nproc n) : n_nproc (S n) :=
    match p with
    | existT _ m q =>
      existT _ m (incr_n_proc q)
    end.

  Definition incr_n_procs {n} (ps : n_procs n) : n_procs (S n) :=
    map incr_n_nproc ps.

  Fixpoint M_haltedSM_n {S}
           (n  : nat)
           (nm : CompName)
           (d  : S) : M_StateMachine n nm :=
    match n with
    | 0 => M_haltedSM nm d
    | S m => incr_n_proc (M_haltedSM_n m nm d)
    end.

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

  Definition sm_s_to_sm {m} {nm}
             (sm : MP_StateMachine (n_proc m) nm)
             (x : M_p (n_proc m) (option (sm_S sm) * cio_O (fio nm)))
    : M_p (n_proc m) (MP_StateMachine (n_proc m) nm * cio_O (fio nm)) :=
    fun ps =>
      let (ps', so) := x ps in
      let (ops,o) := so in
      match ops with
      | Some s =>
        (ps',
         (MkMPSM
            (sm_S      sm)
            (sm_halted sm)
            (sm_update sm)
            s,o))
      | None =>
        (ps',
         (MkMPSM
            (sm_S      sm)
            true
            (sm_update sm)
            (sm_state  sm),
          o))
      end.

  Fixpoint app_m_proc {n} {nm}
    : M_StateMachine n nm -> cio_I (fio nm) -> option (M_n (pred n) (M_StateMachine n nm * cio_O (fio nm))) :=
    match n return M_StateMachine n nm -> cio_I (fio nm) -> option (M_n (pred n) (M_StateMachine n nm * cio_O (fio nm))) with
    | 0 => fun pr i => None
    | S m =>
      fun pr =>
        match pr with
        | inl sm => fun i => Some (lift_M (sm_s_to_sm sm (sm_update sm (sm_state sm) i)))
        | inr pr' => fun i => option_map lift_M2 (app_m_proc pr' i)
        end
    end.

  Fixpoint replace_sub {n} {nm}
           (ps : n_procs n)
           (p  : n_proc (pred n) nm) : n_procs n :=
    match ps with
    | [] => []
    | existT _ m q :: rest =>
      if String.string_dec nm m then existT _ nm (incr_pred_n_proc p) :: rest
      else existT _ m q :: replace_sub rest p
    end.

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

  Fixpoint run_n_proc {n} {nm} (p : n_proc n nm) (l : list (cio_I (fio nm))) (ps : n_procs (pred n))
    : list (cio_O (fio nm)) * n_proc n nm * n_procs (pred n) :=
    match l with
    | [] => ([], p, ps)
    | i :: rest =>
      match app_m_proc p i with
      | Some f =>
        match f ps with
        | (ps',(p',o)) =>
          match run_n_proc p' rest ps' with
          | (outs,p'',ps'') => (o :: outs, p'', ps'')
          end
        end
      | None => ([], p, ps)
      end
    end.

End ComponentSM.


Notation "a >>= f" := (bind a f) (at level 100).
