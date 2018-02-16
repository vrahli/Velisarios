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


Section PrimaryBackup.

  (* QUESTION: Should we distinguish nodes that participate in the protocol from
       the other nodes, such as clients? *)
  Inductive PBnode :=
  | PBprimary
  | PBbackup
  | PBc.

  Inductive PBmsg :=
  | PBinput   (n : nat)
  | PBforward (n : nat)
  | PBackn    (n : nat)
  | PBreply   (n : nat).

  (* when primary receives request from client, it state si locked,
     until backup sends ack *)
  Inductive PBprimary_status :=
  | PBlocked
  | PBfree.

  Inductive PBprimary_state :=
  | PBpst (status : PBprimary_status) (counter : nat).

  Lemma Deq_PBnode : Deq PBnode.
  Proof.
    introv; destruct x, y; prove_dec.
  Qed.

  Instance PB_I_Node : Node := MkNode PBnode Deq_PBnode.

  Instance PB_I_Msg : Msg := MkMsg PBmsg.

  Definition PB_msg_status (m : PBmsg) : msg_status :=
    match m with
    | PBinput _   => MSG_STATUS_EXTERNAL
    | PBforward _ => MSG_STATUS_INTERNAL
    | PBackn _    => MSG_STATUS_INTERNAL
    | PBreply _   => MSG_STATUS_INTERNAL
    end.

  Instance PB_I_MsgStatus : MsgStatus := MkMsgStatus PB_msg_status.

  Definition primary_upd : MSUpdate PBprimary_state :=
    fun state input =>
      match state, input with
      (* if locked, then we're waiting for an acknowledgment *)
      | PBpst PBlocked counter, PBackn n =>
        (PBpst PBfree (counter + n), [MkDMsg (PBreply n) [PBc] 0])

      (* if the message is not an acknowledgment, we ignore it *)
      | PBpst PBlocked _, _ => (state, [])

      (* if free and message is an input then forward it to backup *)
      | PBpst PBfree counter, PBinput n => (state, [MkDMsg (PBforward n) [PBbackup] 0])

      (* otherwise ignore message *)
      | _, _ => (state, [])
      end.

  Inductive PBbackup_state :=
  | PBbst (counter : nat).

  Definition backup_upd : MSUpdate PBbackup_state :=
    fun state input =>
      match state, input with
        (* if we get a forward message then we store the value and send back and acknowledgment *)
      | PBbst counter, PBforward n =>
        (PBbst (counter + n), [MkDMsg (PBackn n) [PBprimary] 0])

      (* otherwise ignore message *)
      | _, _ => (state, [])
      end.

  (* QUESTION: Why do we have to repeat that? *)
  Arguments MkSM      [S] [I] [O] _ _ _.
  Arguments sm_halted [S] [I] [O] _.
  Arguments sm_state  [S] [I] [O] _.
  Arguments sm_update [S] [I] [O] _ _ _.

  Definition PBprimarySM : MStateMachine PBprimary_state :=
    mkSSM primary_upd (PBpst PBfree 0).

  Definition PBbackupSM : MStateMachine PBbackup_state :=
    mkSSM backup_upd (PBbst 0).

  Definition PBstate (n : name) :=
    match n with
    | PBprimary => PBprimary_state
    | PBbackup => PBbackup_state
    | _ => unit
    end.

  Definition PBusys : MUSystem PBstate :=
    fun name =>
      match name return StateMachine (PBstate name) msg DirectedMsgs with
      | PBprimary => PBprimarySM
      | PBbackup => PBbackupSM
      | _ => MhaltedSM tt
      end.

  Definition PBsys : System :=
    fun name =>
      match name with
      | PBprimary => build_sprocess primary_upd (PBpst PBfree 0)
      | PBbackup => build_sprocess backup_upd (PBbst 0)
      | _ => haltedProc
      end.

  Instance PB_I_Key : Key := MkKey unit unit.

  Instance PB_I_Data : Data := MkData PBmsg.

  Instance PB_I_AuthTok : AuthTok := MkAuthTok unit Deq_unit.

  Instance PB_I_AuthFun : AuthFun :=
    MkAuthFun
      (fun _ _ => [tt])
      (fun _ _ _ _ => true).

  Definition PBdata_auth : name -> PBmsg -> option name :=
    fun n m => (* n is not used because no message sent to itself *)
      match m with
      | PBinput   _ => Some PBc
      | PBforward _ => Some PBprimary
      | PBackn    _ => Some PBbackup
      | PBreply   _ => Some PBprimary
      end.

  Instance PB_I_DataAuth : DataAuth := MkDataAuth PBdata_auth.

  Instance PB_I_ContainedAuthData : ContainedAuthData :=
    MkContainedAuthData
      (fun m => [MkAuthData m [tt]]) (* tt here says that the data is authenticated *)
  (*(fun a => match a with | MkAuthData m _ => m end)*).

  (* QUESTION: Can we avoid repeating this? *)
  Hint Rewrite @map_option_option_map : option.
  Hint Rewrite @option_map_option_map : option.

  (* QUESTION: Can we export this automatically *)
  Hint Resolve if_not_first_if_first : eo.

  Ltac in_op_outs m :=
    match goal with
    | [ H : In _ (op_outputs _ _ _) |- _ ] =>
      apply in_op_outputs_iff in H;
      destruct H as [m H]; repnd;
      destruct m; simpl in *; ginv; tcsp;
      repndors; tcsp; ginv
    end.

  Lemma PBoutput_iff :
    forall (eo : EventOrdering) e m l d,
      In (MkDMsg m l d) (output_system_on_event_ldata PBusys e)
      <->
      (
        (
          exists n,
            m = PBforward n
            /\ l = [PBbackup]
            /\ d = 0
            /\ loc e = PBprimary
            /\ if_not_first
                 e
                 (exists counter,
                     state_sm_on_event PBprimarySM (local_pred e)
                     = Some (PBpst PBfree counter))
            /\ event_triggered_by_message e (PBinput n)
        )

        \/
        (
          exists n counter,
            m = PBreply n
            /\ l = [PBc]
            /\ d = 0
            /\ loc e = PBprimary
            /\ ~ isFirst e
            /\ state_sm_on_event PBprimarySM (local_pred e)
               = Some (PBpst PBlocked counter)
            /\ event_triggered_by_message e (PBackn n)
        )

        \/
        (
          exists n,
            m = PBackn n
            /\ l = [PBprimary]
            /\ d = 0
            /\ loc e = PBbackup
            /\ if_not_first
                 e
                 (exists counter,
                     state_sm_on_event PBbackupSM (local_pred e)
                     = Some (PBbst counter))
            /\ event_triggered_by_message e (PBforward n)
        )
      ).
  Proof.
    introv.
    rewrite in_output_system_on_event_ldata.
    split; intro h.

    - unfold PBusys in h.
      remember (loc e) as n; destruct n; simpl in *;
        unfold MStateMachine in *; ginv.

      + apply in_output_sm_on_event in h; simpl in *.
        dest_cases w; clear Heqw.

        * in_op_outs te.
          left.
          exists n; dands; auto; eauto with eo.

        * exrepnd; simpl in *.
          unfold primary_upd, S2Update in h0; simpl in h0.
          fold DirectedMsgs in h0.
          destruct s'.
          destruct status.

          {
            in_op_outs te.
            right; left.
            exists n0 counter; dands; auto.
          }

          {
            in_op_outs te.
            left.
            exists n0; dands; auto.
            intro xx; exists counter; dands; auto.
          }

      + apply in_output_sm_on_event in h; simpl in *.
        dest_cases w; clear Heqw.

        * in_op_outs te.
          right; right.
          exists n; dands; auto; eauto with eo.

        * exrepnd.
          unfold backup_upd, S2Update in h0; simpl in h0.
          fold DirectedMsgs in h0.
          destruct s'.

          in_op_outs te.
          right; right.
          exists n0; dands; auto.
          intro xx; exists counter; dands; auto.

      + apply MhaltedSM_doesnt_output in h; tcsp.

    - repndors; exrepnd; subst;
        try match goal with
            | [ H : if_not_first _ _ |- _ ] => apply if_not_first_implies_or in H
            end; repndors; exrepnd; subst;
          try (complete (unfold PBusys; allrw; simpl;
                         apply in_output_sm_on_event;
                         dest_cases w; simpl;
                         fold DirectedMsgs in *;
                         try (eexists; dands;[eauto|]);
                         allrw; simpl; auto)).
  Qed.

  (* hold keys to receive messages to the other one *)
  Definition PBhold_keys (eo : EventOrdering) :=
    forall (e : Event),
      match loc e with
      | PBprimary => has_receiving_key (keys e) PBbackup
      | PBbackup  => has_receiving_key (keys e) PBprimary
      | _ => True
      end.

  Definition PBall_correct (eo : EventOrdering) :=
    forall (e : Event), (loc e = PBprimary \/ loc e = PBbackup) -> isCorrect e.

  Lemma PBkey_primary :
    forall (eo : EventOrdering) e,
      loc e = PBprimary
      -> PBhold_keys eo
      -> {k : receiving_key & In k (lookup_receiving_keys (keys e) PBbackup)}.
  Proof.
    introv lp hk.
    pose proof (hk e) as q; clear hk.
    rewrite lp in q.
    unfold has_receiving_key in q.
    unfold lookup_receiving_keys.
    remember (lookup_drkeys (keys e) PBbackup) as lk; destruct lk; simpl; tcsp.
    destruct d as [n k]; simpl in *.
    destruct k.
    exists tt; auto.
  Qed.

  Lemma PBkey_backup :
    forall (eo : EventOrdering) e,
      loc e = PBbackup
      -> PBhold_keys eo
      -> {k : receiving_key & In k (lookup_receiving_keys (keys e) PBprimary)}.
  Proof.
    introv lp hk.
    pose proof (hk e) as q; clear hk.
    rewrite lp in q.
    unfold has_receiving_key in q.
    unfold lookup_receiving_keys.
    remember (lookup_drkeys (keys e) PBprimary) as lk; destruct lk; simpl; tcsp.
    destruct d as [n k]; simpl in *.
    destruct k.
    exists tt; auto.
  Qed.

  Local Open Scope eo.

 (* if the system sends a reply, then it received an input *)
  Lemma PBvalidity :
    forall (eo : EventOrdering),
      authenticated_messages_were_sent_or_byz_usys eo PBusys
      -> PBhold_keys eo
      -> PBall_correct eo
      -> forall (e : Event) (n : nat) (dst : list name) (d : nat),
        In (MkDMsg (PBreply n) dst d) (output_system_on_event_ldata PBusys e)
        -> exists e',
          e' ≺ e
          /\ event_triggered_by_message e' (PBinput n).
  Proof.
    introv byz hk cor i.

    apply PBoutput_iff in i; repndors; exrepnd; subst; ginv;[].

    (* receipt of an acknowledgment at e *)
    pose proof (byz e (MkAuthData (PBackn n0) [tt])) as M1h.
    rewrite in_bind_op_list_as_auth_data_in_trigger in M1h.
    simpl in M1h.
    repeat (autodimp M1h hyp);
      [eapply event_triggered_by_message_implies_auth_data_in_trigger;eauto;simpl;tcsp
      | |];[|].

    {
      unfold verify_authenticated_data; simpl.
      pose proof (PBkey_primary eo e) as h; repeat (autodimp h hyp); exrepnd.
      match goal with
      | [ |- _ _ ?l = _ ] => remember l as w; destruct w; simpl in *; tcsp
      end.
    }

    exrepnd; repndors; exrepnd.

    {
      (* the acknowledgment was sent by the backup *)
      apply PBoutput_iff in M1h4; repndors; exrepnd; subst; ginv; tcsp.
      injection M1h3; clear M1h3; intro eqloc.

      (* receipt of a forward message at e' *)
      pose proof (byz e' (MkAuthData (PBforward n0) [tt])) as M2h.
      rewrite in_bind_op_list_as_auth_data_in_trigger in M2h.
      simpl in M2h.
      repeat (autodimp M2h hyp);
        [eapply event_triggered_by_message_implies_auth_data_in_trigger;eauto;simpl;tcsp
        | |];[|].

      { unfold verify_authenticated_data; simpl.
        pose proof (PBkey_backup eo e') as h; repeat (autodimp h hyp); exrepnd.
        match goal with
        | [ |- _ _ ?l = _ ] => remember l as w; destruct w; simpl in *; tcsp
        end. }

      exrepnd; repndors; exrepnd; ginv.

      {
        (* forward was sent by the primary *)
        apply PBoutput_iff in M2h4; repndors; exrepnd; subst; ginv; tcsp.

        (* receipt of an input message at e'0 *)
        exists e'0; dands; auto.
        eapply causal_trans;eauto.
      }

      {
        injection M2h6; clear M2h6; intro eqloc2.
        pose proof (cor e'') as q; autodimp q hyp.
        apply correct_is_not_byzantine in q; tcsp.
      }
    }

    {
      injection M1h6; clear M1h6; intro eqloc2.
      pose proof (cor e'') as q; autodimp q hyp.
      apply correct_is_not_byzantine in q; tcsp.
    }
  Qed.

End PrimaryBackup.
