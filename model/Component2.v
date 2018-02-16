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

Definition I := nat.
Definition O := nat.
Definition S := nat.

Definition name := String.string.

Definition proc  := Process I O.
Definition nproc := (name * proc)%type.
Definition procs := list nproc.

Definition M (A : Type) := procs -> (procs * A)%type.

CoInductive M_Process (I O : Type) : Type :=
| m_proc (f : option (I -> M (M_Process I O * O))).
Arguments m_proc [I] [O] _.

Definition M_Update (S I O : Type) := S -> I -> M (option S * O).

Definition ret {A} (a : A) : M(A) := fun s => (s, a).

Definition bind {A B} (m : M(A)) (f : A -> M(B)) : M(B) :=
  fun s =>
    let (s1,a) := m s in
    let (s2,b) := f a s1 in
    (s2,b).

Notation "a >>= f" := (bind a f) (at level 100).

Fixpoint find_name (n : name) (l : procs) : option proc :=
  match l with
  | [] => None
  | (m,pr) :: rest =>
    if String.string_dec n m then Some pr
    else find_name n rest
  end.

Fixpoint replace_name (n : name) (pr : proc) (l : procs) : procs :=
  match l with
  | [] => []
  | (m,q) :: rest =>
    if String.string_dec n m then (m,pr) :: rest
    else (m,q) :: replace_name n pr rest
  end.

Definition call_proc (n : name) (i : I) : M O :=
  fun l =>
    match find_name n l with
    | Some pr =>
      match app_proc pr i with
      | Some (q,o) => (replace_name n q l,o)
      | None => (l,0)
      end
    | None => (l,0)
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

Definition M_haltedProc {I O} : M_Process I O := m_proc None.

(*CoFixpoint build_m_process {S I O}
           (upd : M_Update S I O)
           (s   : S) : M_Process I O :=
  m_proc (Some
            (fun a =>
               (upd s a)
                 >>= (fun x =>
                        match x with
                        | (Some s', out) => ret (build_m_process upd s', out)
                        | (None, out) => ret (M_haltedProc, out)
                        end))).*)

(* We had to break the abstraction because Coq didn't like [build_m_process]. *)
CoFixpoint build_m_process {S I O}
           (upd : M_Update S I O)
           (s   : S) : M_Process I O :=
  m_proc (Some
            (fun a l =>
               let (k,x) := upd s a l in
               match x with
               | (Some s', out) => (k, (build_m_process upd s', out))
               | (None, out) => (k, (M_haltedProc, out))
               end)).

Definition m_counter_update : M_Update S I O :=
  fun s i => ret (Some (s + i), s + i).

Definition A : M_Process I O :=
  build_m_process m_counter_update 0.

Definition B_update : M_Update unit nat nat :=
  fun s n =>
    (call_proc "A" n)
      >>= (fun out => ret (Some s, out)).

Definition B : M_Process I O :=
  build_m_process B_update tt.

(*Definition prog : procs := [("A",A),("B",B)].*)
