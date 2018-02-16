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


Section Component.

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

  Definition M_p (p : Type) (A : Type) := p_procs p -> (p_procs p * A)%type.

  CoInductive MP_Process (p : Type) : Type :=
  | m_proc (f : option (cio_I -> M_p p (MP_Process p * cio_O))).
  Arguments m_proc [p] _.

  Fixpoint M_Process (n : nat) : Type :=
    match n with
    | 0 => MP_Process False
    | S n =>
      MP_Process (M_Process n) [+] M_Process n
    end.

  Definition n_proc  (n : nat) := M_Process n.
  Definition n_nproc (n : nat) := (CompName * n_proc n)%type.
  Definition n_procs (n : nat) := list (n_nproc n).

  Definition M_n (n : nat) (A : Type) := n_procs n -> (n_procs n * A)%type.

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

  Definition lift_M {m}
             (x : M_p (M_Process m) (MP_Process (M_Process m) * cio_O))
    : M_n m (M_Process (S m) * cio_O) :=
    fun ps =>
      let (k, qo) := x ps in
      let (q, o) := qo in
      (k, (injL(q), o)).

  Definition MP_haltedProc (n : nat) : MP_Process (M_Process n) := m_proc None.

  Definition M_haltedProc : M_Process 0 := m_proc None.

  Definition incr_n_proc {n} (p : n_proc n) : n_proc (S n) := inr p.

  Definition incr_n_nproc {n} (p : n_nproc n) : n_nproc (S n) :=
    let (m,q) := p in
    (m, incr_n_proc q).

  Definition incr_n_procs {n} (ps : n_procs n) : n_procs (S n) :=
    map incr_n_nproc ps.

  Fixpoint M_haltedProc_n (n : nat) : M_Process n :=
    match n with
    | 0 => M_haltedProc
    | S m => incr_n_proc (M_haltedProc_n m)
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

  (*Fixpoint lift0_n_proc n (p : n_proc 0) : n_proc n :=
  match n with
  | 0 => p
  | S m => incr_n_proc (lift0_n_proc m p)
  end.*)

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

  Definition lift_M2 {n} (m : M_n (pred n) (M_Process n * cio_O))
    : M_n (pred (S n)) (M_Process (S n) * cio_O) :=
    fun (ps : n_procs n) =>
      match m (decr_n_procs ps) with
      | (ps',(p',o)) => (incr_pred_n_procs ps', (incr_n_proc p',o))
      end.

  Fixpoint app_m_proc {n:nat}
    : M_Process n -> cio_I -> option (M_n (pred n) (M_Process n * cio_O)) :=
    match n return M_Process n -> cio_I -> option (M_n (pred n) (M_Process n * cio_O)) with
    | 0 => fun pr i => None
    | S m =>
      fun pr i =>
        match pr with
        | inl (m_proc o) => option_map (fun f => lift_M (f i)) o
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

  (*Definition B_update (i : nat) : M_Update unit nat nat :=
  fun s n =>
    fun procs =>
      let (ps,out) :=
          match find_name "A" procs with
          | Some p =>
            match app_proc p n with
            | Some (q,out) => ([("A",q)],out)
            | None => ([],0)
            end
          | None => ([],0)
          end in
      (ps, (Some s, out)).*)

  (*CoFixpoint build_m_process {S cio_I O}
           (upd : M_Update S cio_I O)
           (s   : S) : M_Process cio_I O :=
  m_proc (Some
            (fun a =>
               (upd s a)
                 >>= (fun x =>
                        match x with
                        | (Some s', out) => ret (build_m_process upd s', out)
                        | (None, out) => ret (M_haltedProc, out)
                        end))).*)

  (* We had to break the abstraction because Coq didn't like [build_m_process]. *)
  CoFixpoint build_mp_process {n} {ST}
             (upd : M_Update n ST)
             (s   : ST) : MP_Process (M_Process n) :=
    m_proc (Some
              (fun a (l : n_procs n) =>
                 let (k,x) := upd s a l in
                 match x with
                 | (Some s', out) => (k, (build_mp_process upd s', out))
                 | (None, out) => (k, (MP_haltedProc n, out))
                 end)).

  Definition build_m_process {n} {ST}
             (upd : M_Update n ST)
             (s   : ST) : M_Process (S n) :=
    inl (build_mp_process upd s).

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

End Component.


Notation "a >>= f" := (bind a f) (at level 100).
