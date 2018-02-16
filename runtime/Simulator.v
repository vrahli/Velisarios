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

Require Import Program.
Require Import Coq.Init.Wf.


Section Simulator.

  Context { pd     : @Data }.
  Context { pn     : @Node }.
  Context { pk     : @Key }.
(*  Context { auth   : @Auth pd pk }. *)
  Context { pm     : @Msg }.
  Context { pda    : @DataAuth pd pn }.

  Class Time :=
    {
      Time_type     : Type;
      Time_get_time : unit -> Time_type;
      Time_sub      : Time_type -> Time_type -> Time_type;
      Time_2string  : Time_type -> String.string;
    }.

  Context { time : Time }.

  (* time needed to run state machine sm *)
  Definition run_with_time {S} (sm : MStateMachine S) (m : msg) :
    MStateMachine S * DirectedMsgs * Time_type :=
    let t1 := Time_get_time tt in
    let (sm', outs) := lrun_sm sm m in
    let t2 := Time_get_time tt in
    (sm', outs, Time_sub t2 t1).

  (* DirectedMsg with timestamps *)
  Record TimedDirectedMsg :=
    MkTimedDMsg
    {
      tdm_dmsg : DirectedMsg;
      tdm_time : Time_type;
    }.

  Definition TimedDirectedMsgs := list TimedDirectedMsg.

  (* decompose a list [l] into Some(iseg,elt,fseg) such that
       l = iseg ++ elt :: fseg
     and elt is l's nth element *)
  Fixpoint decomp_nth {T} (l : list T) (n : nat) : option (list T * T * list T) :=
    match l, n with
    | [], _ => None
    | x :: xs, 0 => Some ([], x, xs)
    | x :: xs, S n =>
      match decomp_nth xs n with
      | None => None
      | Some (iseg, elt, fseg) => Some (x :: iseg, elt, fseg)
      end
    end.

(*  Record SimulationState :=
    MkSimState
      {
        (* system *)
        sim_state_type      : name -> Type;
        sim_state_sys       : MUSystem sim_state_type;

        (* the number indicated how many messages have been sent so far *)
        sim_state_step      : nat;

        (* messages in flight *)
        sim_state_inflight  : DirectedMsgs;

        (* log of messages delivered so far *)
        sim_state_delivered : TimedDirectedMsgs;
      }.

  Definition MkInitSimState
             {F : name -> Type}
             (s : MUSystem F)
             (msgs : DirectedMsgs) : SimulationState :=
    MkSimState F s 0 msgs [].

  (* We apply the state machine to the first inflight message and return
       (1) the number of messages sent (either 0 or 1)
       (2) the messages that are produced and
       (3) the new system

     The eq_rect down there is problematic because it doesn't compute.
   *)
  Definition run_simulator (s : SimulationState) : SimulationState :=
    match sim_state_inflight s with
    | [] => s
    | dmsg :: dmsgs =>
      let sm := sim_state_sys s (dmDst dmsg) in
      match run_with_time sm (dmMsg dmsg) with
      | (sm', outs, time) =>
        MkSimState
          (sim_state_type s)
          (fun name =>
             match name_dec (dmDst dmsg) name return StateMachine (sim_state_type s name) msg DirectedMsgs with
             | left  p => eq_rect
                            (dmDst dmsg)
                            (fun n => MStateMachine (sim_state_type s n))
                            sm'
                            name
                            p
             | right p => sim_state_sys s name
             end)
          (S (sim_state_step s))
          (dmsgs ++ outs)
          (MkTimedDMsg dmsg time :: sim_state_delivered s)
      end
    end.

  (* Similar to [run_simulator] but in addition takes the position of the message
     we want to send
   *)
  Definition run_simulator_at (s : SimulationState) (n : nat) : SimulationState :=
    match decomp_nth (sim_state_inflight s) n with
    | None => s
    | Some (iseg, dmsg, fseg) =>
      let sm := sim_state_sys s (dmDst dmsg) in
      match run_with_time sm (dmMsg dmsg) with
      | (sm', outs, time) =>
        MkSimState
          (sim_state_type s)
          (fun name =>
             match name_dec (dmDst dmsg) name return StateMachine (sim_state_type s name) msg DirectedMsgs with
             | left  p => eq_rect
                            (dmDst dmsg)
                            (fun n => MStateMachine (sim_state_type s n))
                            sm'
                            name
                            p
           | right p => sim_state_sys s name
             end)
          (S (sim_state_step s))
          (iseg ++ outs ++ fseg)
          (MkTimedDMsg dmsg time :: sim_state_delivered s)
      end
    end.

  Fixpoint iterate_n_steps
           (s : SimulationState)
           (n : nat) : SimulationState :=
    match n with
    | 0 => s
    | S n =>
      let s1 := run_simulator s in
      iterate_n_steps s1 n
    end.

  Fixpoint run_n_steps
           (s : SimulationState)
           (l : list nat) : SimulationState :=
    match l with
    | [] => s
    | n :: ns =>
      let s1 := run_simulator_at s n in
      run_n_steps s1 ns
    end.*)


  (* ========= This is for a system where all state machines have the same kind of states ========= *)

  Record MonoSimulationState :=
    MkMonoSimState
      {
        (* system *)
        mono_sim_state_type          : Type;
        mono_sim_state_sys           : NMStateMachine mono_sim_state_type;

        (* the number indicated how many messages have been sent so far *)
        mono_sim_state_step          : nat;

        (* messages in flight from the outside (clients) *)
        mono_sim_state_out_inflight  : DirectedMsgs;

        (* messages in flight from the inside (replicas) *)
        mono_sim_state_in_inflight   : DirectedMsgs;

        (* log of messages delivered so far *)
        mono_sim_state_delivered     : TimedDirectedMsgs;
      }.

  Definition MkInitMonoSimState
             {S : Type}
             (s : NMStateMachine S)
             (msgs : DirectedMsgs) : MonoSimulationState :=
    MkMonoSimState S s 0 msgs [] [].

(*  Definition run_mono_simulator_out (s : MonoSimulationState) : MonoSimulationState :=
    match mono_sim_state_out_inflight s with
    | [] => s
    | dmsg :: dmsgs =>
      let sm := mono_sim_state_sys s (dmDst dmsg) in
      match run_with_time sm (dmMsg dmsg) with
      | (sm', outs, time) =>
        MkMonoSimState
          (mono_sim_state_type s)
          (fun name =>
             match name_dec (dmDst dmsg) name with
             | left  p => sm'
             | right p => mono_sim_state_sys s name
             end)
          (S (mono_sim_state_step s))
          (* outside system: *)
          dmsgs
          (* inside system: *)
          (outs ++ mono_sim_state_in_inflight s)
          (MkTimedDMsg dmsg time :: mono_sim_state_delivered s)
      end
    end.

  (* We apply the state machine to the first inflight message and return
       (1) the number of messages sent (either 0 or 1)
       (2) the messages that are produced and
       (3) the new system
   *)
  Definition run_mono_simulator (s : MonoSimulationState) : MonoSimulationState :=
    match mono_sim_state_in_inflight s with
    | [] =>
      (* if we don't have any more "internal" messages to send we send an external one *)
      run_mono_simulator_out s

    | dmsg :: dmsgs =>
      let sm := mono_sim_state_sys s (dmDst dmsg) in
      match run_with_time sm (dmMsg dmsg) with
      | (sm', outs, time) =>
        MkMonoSimState
          (mono_sim_state_type s)
          (fun name =>
             match name_dec (dmDst dmsg) name with
             | left  p => sm'
             | right p => mono_sim_state_sys s name
             end)
          (S (mono_sim_state_step s))
          (* outside system: *)
          (mono_sim_state_out_inflight s)
          (* inside system: *)
          (dmsgs ++ outs)
          (MkTimedDMsg dmsg time :: mono_sim_state_delivered s)
      end
    end.
 *)

  Locate dmDst.

  (* run MonoSimulationState on the in flight messages that came from the client *)
  Definition run_mono_simulator_out_at (s : MonoSimulationState) (n : nat) : MonoSimulationState :=
    match decomp_nth (mono_sim_state_out_inflight s) n with
    | None => s
    | Some (iseg, dmsg, fseg) =>
      (* dmDst is list of destination msgs (defined in model/Msg.v) *)
      match dmDst dmsg with
      | [] =>
        MkMonoSimState
          (mono_sim_state_type s)
          (mono_sim_state_sys s)
          (mono_sim_state_step s)
          (iseg ++ fseg)
          (mono_sim_state_in_inflight s)
          (mono_sim_state_delivered s)
(* ??? *)
      | dst :: dsts =>
        let sm := mono_sim_state_sys s dst in
        match run_with_time sm (dmMsg dmsg) with
        | (sm', outs, time) =>
          MkMonoSimState
            (mono_sim_state_type s)
            (fun name =>
               match name_dec dst name with
               | left  p => sm'
               | right p => mono_sim_state_sys s name
               end)
            (S (mono_sim_state_step s))
            (* outside system: *)
            (iseg ++ MkDMsg (dmMsg dmsg) dsts 0 :: fseg)
            (* inside system: *)
            (outs ++ mono_sim_state_in_inflight s)
            (MkTimedDMsg dmsg time :: mono_sim_state_delivered s)
        end
      end
    end.


  (* We apply the state machine to the nth inflight message and return
       (1) the number of messages sent (either 0 or 1)
       (2) the messages that are produced and
       (3) the new system

     The boolean is true if we want to prepend the outputs in case of an
     in-system inflight message.
   *)
  Definition run_mono_simulator_at (s : MonoSimulationState) (n : nat) (b : bool) : MonoSimulationState :=
    match decomp_nth (mono_sim_state_in_inflight s) n with
    | None =>

      run_mono_simulator_out_at s n

    | Some (iseg, dmsg, fseg) =>
      match dmDst dmsg with
      | [] =>
        MkMonoSimState
          (mono_sim_state_type s)
          (mono_sim_state_sys s)
          (mono_sim_state_step s)
          (iseg ++ fseg)
          (mono_sim_state_in_inflight s)
          (mono_sim_state_delivered s)

      | dst :: dsts =>
        let sm := mono_sim_state_sys s dst in
        match run_with_time sm (dmMsg dmsg) with
        | (sm', outs, time) =>
          MkMonoSimState
            (mono_sim_state_type s)
            (fun name =>
               match name_dec dst name with
               | left  p => sm'
               | right p => mono_sim_state_sys s name
               end)
            (S (mono_sim_state_step s))
            (* outside system: *)
            (mono_sim_state_out_inflight s)
            (* inside system: *)
            (if b
             then iseg ++ outs ++ MkDMsg (dmMsg dmsg) dsts 0 :: fseg
             else iseg ++ MkDMsg (dmMsg dmsg) dsts 0 :: fseg ++ outs)
            (MkTimedDMsg dmsg time :: mono_sim_state_delivered s)
        end
      end
    end.

  Definition run_mono_simulator_out (s : MonoSimulationState) : MonoSimulationState :=
    run_mono_simulator_out_at s 0.

  Definition run_mono_simulator (s : MonoSimulationState) : MonoSimulationState :=
    run_mono_simulator_at s 0 false (* false means append outputs *).

  Record Round :=
    MkRound
      {
        round_pos : nat; (* the position of the message we want to send *)
        round_num : nat; (* the number of times we want to send a message at this position *)
      }.

  Definition Rounds := list Round.

  Record Switch :=
    MkSwitch
      {
        switch_step : nat; (* the step at which we want to switch *)
        switch_pos  : nat; (* the position of the message we want to switch *)
      }.

  Definition Switches := list Switch.

  Fixpoint find_switch (step : nat) (L : Switches) : option nat :=
    match L with
    | [] => None
    | MkSwitch s p :: L => if eq_nat_dec step s then Some p else find_switch step L
    end.


  Fixpoint rounds_size (l : Rounds) : nat :=
    match l with
    | [] => 0
    | MkRound pos n :: rounds => S n + rounds_size rounds
    end.

  Lemma rounds_lt1 :
    forall pos rounds,
      rounds_size rounds < rounds_size (MkRound pos 0 :: rounds).
  Proof.
    introv; simpl; omega.
  Qed.

  Lemma rounds_lt2 :
    forall pos m rounds,
      rounds_size (MkRound pos m :: rounds) < rounds_size (MkRound pos (S m) :: rounds).
  Proof.
    introv; simpl; omega.
  Qed.

  Definition mono_iterate_n_steps
             (rounds : Rounds)
             (switch : Switches)
             (s : MonoSimulationState) : MonoSimulationState :=
    @Fix
      Rounds
      (fun a b => lt (rounds_size a) (rounds_size b))
      (measure_wf lt_wf rounds_size)
      (fun rounds => list Switch -> MonoSimulationState -> MonoSimulationState)
      (fun rounds =>
         match rounds with
         | [] => fun F switch s => s
         | MkRound pos 0 :: rounds =>
           fun F switch s =>
             F rounds (rounds_lt1 pos rounds) switch s
         | MkRound pos (S m) :: rounds =>
           fun F switch s =>
             match find_switch (mono_sim_state_step s) switch with
             | Some p =>

               let s1 := run_mono_simulator_out_at s p in
               F (MkRound pos m :: rounds) (rounds_lt2 pos m rounds) switch s1

             | None =>

               let s1 := run_mono_simulator_at s pos false in
               F (MkRound pos m :: rounds) (rounds_lt2 pos m rounds) switch s1

             end
         end) rounds switch s.

  Definition mono_run_n_steps
             (l : list nat)
             (s : MonoSimulationState) : MonoSimulationState :=
    mono_iterate_n_steps (map (fun p => MkRound p 1) l) [] s.

(*    match l with
    | [] => s
    | n :: ns =>
      let s1 := run_mono_simulator_at s n in
      mono_run_n_steps s1 ns
    end.*)

End Simulator.
