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


  Class ComponentIO :=
    BuildComponentIO
      {
        cio_I         : Type;
        cio_O         : Type;
        cio_default_O : cio_O;
      }.
  Context { cio : ComponentIO }.


  Definition CompName := String.string.

  Definition p_nproc (p : Type) := (CompName * p)%type.
  Definition p_procs (p : Type) := list (p_nproc p).

  Definition M_p (p : Type) (PO : Type) := p_procs p -> (p_procs p * PO)%type.

  Definition MP_Update (p : Type) (S : Type) := S -> cio_I -> M_p p (option S * cio_O).

  Record MP_StateMachine (p : Type) : Type :=
    MkMPSM
      {
        sm_type   : Type;
        sm_halted : bool;
        sm_update :> MP_Update p sm_type;
        sm_state  : sm_type;
      }.
  Arguments MkMPSM [p] _ _ _ _.
  Arguments sm_type   [p] _.
  Arguments sm_halted [p] _.
  Arguments sm_update [p] _ _ _ _.
  Arguments sm_state  [p] _.

  Fixpoint M_StateMachine (n : nat) : Type :=
    match n with
    | 0 => MP_StateMachine False
    | S n =>
      MP_StateMachine (M_StateMachine n) [+] M_StateMachine n
    end.

  Definition n_proc  (n : nat) := M_StateMachine n.
  Definition n_nproc (n : nat) := (CompName * n_proc n)%type.
  Definition n_procs (n : nat) := list (n_nproc n).

  Definition M_n (n : nat) (PO : Type) := n_procs n -> (n_procs n * PO)%type.

  Definition M_Update (n : nat) (S : Type) := S -> cio_I -> M_n n (option S * cio_O).

  Definition ret {A} (n : nat) (a : A) : M_n n (A) := fun s => (s, a).

  Definition bind {A B} {n:nat} (m : M_n n A) (f : A -> M_n n B) : M_n n B :=
    fun s =>
      let (s1,a) := m s in
      let (s2,b) := f a s1 in
      (s2,b).

  Notation "a >>= f" := (bind a f) (at level 100).

  Fixpoint find_name {n:nat} (nm : CompName) (l : n_procs n) : option (n_proc n) :=
    match l with
    | [] => None
    | (m,pr) :: rest =>
      if String.string_dec nm m then Some pr
      else find_name nm rest
    end.

  Fixpoint replace_name {n:nat} (nm : CompName) (pr : n_proc n) (l : n_procs n) : n_procs n :=
    match l with
    | [] => []
    | (m,q) :: rest =>
      if String.string_dec nm m then (m,pr) :: rest
      else (m,q) :: replace_name nm pr rest
    end.

  Definition MP_haltedSM {S} (n : nat) (d : S) : MP_StateMachine (M_StateMachine n) :=
    MkMPSM
      S
      true
      (fun s i => ret _ (None, cio_default_O))
      d.

  Definition M_haltedSM {S} (d : S) : M_StateMachine 0 :=
    MkMPSM
      S
      true
      (fun s i p => (p, (None, cio_default_O)))
      d.

  Definition incr_n_proc {n} (p : n_proc n) : n_proc (S n) := inr p.

  Definition incr_n_nproc {n} (p : n_nproc n) : n_nproc (S n) :=
    let (m,q) := p in
    (m, incr_n_proc q).

  Definition incr_n_procs {n} (ps : n_procs n) : n_procs (S n) :=
    map incr_n_nproc ps.

  Fixpoint M_haltedSM_n {S} (n : nat) (d : S) : M_StateMachine n :=
    match n with
    | 0 => M_haltedSM d
    | S m => incr_n_proc (M_haltedSM_n m d)
    end.

  Definition decr_n_proc {n} : n_proc n -> option (n_proc (Init.Nat.pred n)) :=
    match n with
    | 0 => fun p => Some p
    | S m => fun p =>
               match p with
               | inl _ => None
               | inr q => Some q
               end
    end.

  Definition decr_n_nproc {n} (np : n_nproc n) : option (n_nproc (Init.Nat.pred n)) :=
    let (m,p) := np in
    match decr_n_proc p with
    | Some q => Some (m,q)
    | None => None
    end.

  Definition decr_n_procs {n} (ps : n_procs n) : n_procs (Init.Nat.pred n) :=
    mapOption decr_n_nproc ps.

  Definition incr_pred_n_proc {n} : n_proc (pred n) -> n_proc n :=
    match n with
    | 0 => fun p => p
    | S m => inr
    end.

  Definition incr_pred_n_nproc {n} (p : n_nproc (pred n)) : n_nproc n :=
    let (m,q) := p in
    (m, incr_pred_n_proc q).

  Definition incr_pred_n_procs {n} (ps : n_procs (pred n)) : n_procs n :=
    map incr_pred_n_nproc ps.

  Definition lift_M {m}
             (x : M_p (M_StateMachine m) (MP_StateMachine (M_StateMachine m) * cio_O))
    : M_n m (M_StateMachine (S m) * cio_O) :=
    fun ps =>
      let (k, qo) := x ps in
      let (q, o) := qo in
      (k, (injL(q), o)).

  Definition lift_M2 {n} (m : M_n (pred n) (M_StateMachine n * cio_O))
    : M_n (pred (S n)) (M_StateMachine (S n) * cio_O) :=
    fun (ps : n_procs n) =>
      match m (decr_n_procs ps) with
      | (ps',(p',o)) => (incr_pred_n_procs ps', (incr_n_proc p',o))
      end.

  Definition sm_s_to_sm {m}
             (sm : MP_StateMachine (M_StateMachine m))
             (x : M_p (M_StateMachine m) (option (sm_type sm) * cio_O))
    : M_p (M_StateMachine m) (MP_StateMachine (M_StateMachine m) * cio_O) :=
    fun ps =>
      let (ps', so) := x ps in
      let (ops,o) := so in
      match ops with
      | Some s =>
        (ps',
         (MkMPSM
            (sm_type   sm)
            (sm_halted sm)
            (sm_update sm)
            s,o))
      | None =>
        (ps',
         (MkMPSM
            (sm_type   sm)
            true
            (sm_update sm)
            (sm_state  sm),
          o))
      end.

  Fixpoint app_m_proc {n:nat}
    : M_StateMachine n -> cio_I -> option (M_n (pred n) (M_StateMachine n * cio_O)) :=
    match n return M_StateMachine n -> cio_I -> option (M_n (pred n) (M_StateMachine n * cio_O)) with
    | 0 => fun pr i => None
    | S m =>
      fun pr i =>
        match pr with
        | inl sm => Some (lift_M (sm_s_to_sm sm (sm_update sm (sm_state sm) i)))
        | inr pr' => option_map lift_M2 (app_m_proc pr' i)
        end
    end.

  Fixpoint replace_sub {n} (ps : n_procs n) (nm : CompName) (p : n_proc (pred n)) : n_procs n :=
    match ps with
    | [] => []
    | (m,q) :: rest =>
      if String.string_dec nm m then (m,incr_pred_n_proc p) :: rest
      else (m,q) :: replace_sub rest nm p
    end.

  Fixpoint replace_subs {n} (ps : n_procs n) (l : n_procs (pred n)) : n_procs n :=
    match l with
    | [] => ps
    | p :: rest =>
      let (nm,q) := p in
      replace_subs (replace_sub ps nm q) rest
    end.

  Definition call_proc {n:nat} (nm : CompName) (i : cio_I) : M_n n cio_O :=
    fun (l : n_procs n) =>
      match find_name nm l with
      | Some pr =>
        match app_m_proc pr i with
        | Some f =>
          match f (decr_n_procs l) with
          | (l',(pr',o)) => (replace_subs (replace_name nm pr' l) l',o)
          end
        | None => (l,cio_default_O)
        end
      | None => (l,cio_default_O)
      end.

  (* We had to break the abstraction because Coq didn't like [build_m_process]. *)
  Definition build_mp_sm {n}
             {S}
             (upd : M_Update n S)
             (s   : S) : MP_StateMachine (M_StateMachine n) :=
    MkMPSM S false upd s.

  Definition build_m_sm {n}
             {St}
             (upd : M_Update n St)
             (s   : St) : M_StateMachine (S n) :=
    inl (build_mp_sm upd s).

  Fixpoint run_n_proc {n} (p : n_proc n) (l : list cio_I) (ps : n_procs (pred n))
    : list cio_O * n_proc n * n_procs (pred n) :=
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
