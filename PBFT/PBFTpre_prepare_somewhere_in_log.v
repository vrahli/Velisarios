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


Require Export PBFTwell_formed_log.
Require Export PBFTordering.
Require Export PBFTprops3.


Section PBFT_pre_prepare_somewhere_in_log.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Definition pre_prepare_matches_info
             (pp  : Pre_prepare)
             (nfo : logEntryPrePrepareInfo) :=
    match nfo with
    | pp_info_pre_prep a l =>
      a = pre_prepare2auth pp
      /\
      matching_requests (pre_prepare2requests pp) (map fst l) = true
    | pp_info_no_pre_prep => False
    end.

  Definition pre_prepare_matches_entry
             (pp : Pre_prepare)
             (d  : PBFTdigest)
             (e  : PBFTlogEntry) :=
    pre_prepare2request_data pp d = log_entry_request_data e
    /\
    pre_prepare_matches_info pp (log_entry_pre_prepare_info e).

  Fixpoint pre_prepare_somewhere_in_log
           (pp : Pre_prepare)
           (d  : PBFTdigest)
           (l  : PBFTlog) :=
    match l with
    | [] => False
    | entry :: entries =>
      pre_prepare_matches_entry pp d entry
      \/
      pre_prepare_somewhere_in_log pp d entries
    end.

  Lemma pre_prepare_somewhere_in_log_prop :
    forall pp d l,
      pre_prepare_somewhere_in_log pp d l
      <-> exists entry, In entry l /\ pre_prepare_matches_entry pp d entry.
  Proof.
    induction l; introv; split; intro h; simpl in *; repndors; tcsp.

    - exists a; dands; auto.

    - apply IHl in h; exrepnd; exists entry; dands; auto.

    - exrepnd; repndors; subst; tcsp.
      right; apply IHl; exists entry; auto.
  Qed.

  Lemma entry_of_pre_prepare_somewhere_in_log :
    forall d p L,
      pre_prepare_somewhere_in_log p d L
      -> exists entry,
        In entry L
        /\ log_entry_request_data entry = pre_prepare2request_data p d.
  Proof.
    introv h; rewrite pre_prepare_somewhere_in_log_prop in h; exrepnd; exists entry.
    dands; auto.
    unfold pre_prepare_matches_entry in *; tcsp.
  Qed.
  Hint Rewrite entry_of_pre_prepare_somewhere_in_log : pbft.

  Lemma check_send_replies_preserves_pre_prepare_somewhere_in_log :
    forall d prep slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> pre_prepare_somewhere_in_log d prep (log state')
      -> pre_prepare_somewhere_in_log d prep (log state).
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_pre_prepare_somewhere_in_log : pbft.

  Lemma check_send_replies_update_log_preserves_pre_prepare_somewhere_in_log :
    forall prep d slf view keys entryop state L sn msgs state',
      check_send_replies slf view keys entryop (update_log state L) sn = (msgs, state')
      -> pre_prepare_somewhere_in_log d prep (log state')
      -> pre_prepare_somewhere_in_log d prep L.
  Proof.
    introv chk pil.
    eapply check_send_replies_preserves_pre_prepare_somewhere_in_log in chk;[|eauto].
    simpl in *. auto.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_pre_prepare_somewhere_in_log : pbft.


  Lemma add_new_commit2log_preserves_pre_prepare_somewhere_in_log :
    forall d p c L1 L2 i,
      add_new_commit2log L1 c = (i, L2)
      -> pre_prepare_somewhere_in_log p d L2
         <-> pre_prepare_somewhere_in_log p d L1.
  Proof.
    induction L1; introv h; simpl in *; ginv; simpl in *; smash_pbft; tcsp.

    {
      simpl.
      unfold pre_prepare_matches_entry; simpl.
      split; intro h; repndors; repnd; tcsp.
    }

    {
      f_equal.
      match goal with
      | [H : add_commit2entry _ _ = _ |- _ ] =>
        applydup add_commit2entry_preserves_log_entry_request_data in H
      end.
      allrw.

      match goal with
      | [H : add_commit2entry _ _ = _ |- _ ] =>
        apply add_commit2entry_preserves_log_entry_pre_prepare_info in H
      end.
      unfold pre_prepare_matches_entry; allrw; tcsp.
    }

    {
      rewrite IHL1;[|reflexivity]; tcsp.
    }
  Qed.

  Lemma clear_log_checkpoint_preserves_pre_prepare_somewhere_in_log :
    forall d p L sn,
      well_formed_log L
      -> pre_prepare_somewhere_in_log p d (clear_log_checkpoint L sn)
      -> pre_prepare_somewhere_in_log p d L.
  Proof.
    induction L; simpl in *; introv wf h; tcsp.
    pbft_dest_all x.

    - inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.

    - repndors;[tcsp |].

      inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.
  Qed.
  Hint Rewrite clear_log_checkpoint_preserves_pre_prepare_somewhere_in_log : pbft.

  Lemma check_stable_preserves_pre_prepare_somewhere_in_log :
    forall d slf state entryop state' p,
      well_formed_log (log state)
      -> check_stable slf state entryop = Some state'
      -> pre_prepare_somewhere_in_log p d (log state')
      -> pre_prepare_somewhere_in_log p d (log state).
  Proof.
    introv wf h q.
    unfold check_stable in h.
    pbft_dest_all x;[].
    apply clear_log_checkpoint_preserves_pre_prepare_somewhere_in_log in q; auto.
  Qed.
  Hint Rewrite check_stable_preserves_pre_prepare_somewhere_in_log : pbft.

  Lemma find_entry_implies_in :
    forall l n e,
      find_entry l n = Some e
      -> In e l.
  Proof.
    induction l; introv find; simpl in *; smash_pbft.
  Qed.
  Hint Resolve find_entry_implies_in : pbft.

  Lemma pre_prepare_matches_entry_add_replies2entry :
    forall p d entry reps,
      pre_prepare_matches_entry d p (add_replies2entry entry reps)
      <-> pre_prepare_matches_entry d p entry.
  Proof.
    induction entry; introv; simpl in *.
    unfold pre_prepare_matches_entry. simpl in *.
    induction log_entry_pre_prepare_info; simpl in *; tcsp.

    rewrite matching_requests_map_fst_combine_replies.
    tcsp.
  Qed.
  Hint Rewrite pre_prepare_matches_entry_add_replies2entry : pbft.


  Lemma change_entry_add_replies2entry_preserves_pre_prepare_somewhere_in_log :
    forall d p sn entry  reps L,
      pre_prepare_somewhere_in_log d p (change_entry L (add_replies2entry entry reps))
      -> find_entry L sn = Some entry
      -> pre_prepare_somewhere_in_log d p L.
  Proof.
    introv prep find.
    allrw pre_prepare_somewhere_in_log_prop.
    exrepnd.

    apply in_change_entry_implies in prep1; repndors; subst; tcsp.

    - exists entry0; auto.

    - exists entry; dands; eauto 2 with pbft.
      eapply pre_prepare_matches_entry_add_replies2entry; eauto.
  Qed.

  Lemma change_log_entry_add_replies2entry_preserves_pre_prepare_somewhere_in_log :
    forall d prep sn entry state reps,
      pre_prepare_somewhere_in_log
        d
        prep
        (log
           (change_log_entry
              state
              (add_replies2entry entry reps)))
      -> find_entry (log state) sn = Some entry
      -> pre_prepare_somewhere_in_log d prep (log state).
  Proof.
    introv h fe.
    destruct state; simpl in *. smash_pbft.
    eapply change_entry_add_replies2entry_preserves_pre_prepare_somewhere_in_log in h;[|eauto].
    auto.
  Qed.
  Hint Rewrite change_log_entry_add_replies2entry_preserves_pre_prepare_somewhere_in_log : pbft.

  Lemma find_and_execute_requests_preserves_pre_prepare_somewhere_in_log :
    forall d msg i prep st p,
      find_and_execute_requests i (current_view p) (local_keys p) p = (msg, st)
      -> pre_prepare_somewhere_in_log d prep (log st)
      -> pre_prepare_somewhere_in_log d prep (log p).
  Proof.
    introv H1 H2.

    unfold find_and_execute_requests in *.
    pbft_dest_all x;[].
    rename x1 into st.
    unfold execute_requests in *.
    destruct (ready p); simpl in *;[ inversion Heqx; allrw; tcsp |].

    pbft_dest_all y.

    match goal with
    | [ H : context[reply2requests] |- _ ] => hide_hyp H
    end.

    match goal with
    | [ H : check_broadcast_checkpoint _ _ _ _ _ = _ |- _ ] =>
      apply check_broadcast_checkpoint_preserves_log in H
    end.

    match goal with
    | [ H1 : pre_prepare_somewhere_in_log _ _ (log ?s) , H2 : _ = log ?s |- _ ] =>
      rewrite <- H2 in H1; clear H2
    end.

    pose proof (change_log_entry_add_replies2entry_preserves_pre_prepare_somewhere_in_log
                  d prep (next_to_execute p) y p y3) as xx.
    apply xx in H2; auto.
  Qed.
  (* If I uncomment this code runs forever and block my laptop
Hint Rewrite add_new_commit2log_preserves_pre_prepare_somewhere_in_log : pbft. *)

  (* can we prove stronger one than these. Do we really need it??? *)
  Lemma pre_prepare_somewhere_in_log_add_new_prepare2log :
    forall pp d npp nd L,
      pre_prepare_somewhere_in_log pp d (add_new_pre_prepare2log npp nd L)
      -> pre_prepare_somewhere_in_log pp d L
         \/
         pre_prepare2request_data pp d = pre_prepare2request_data npp nd.
  Proof.
    induction L; introv h; simpl in *; ginv; simpl in *; smash_pbft; tcsp; [ | ].

    {
      repndors; tcsp.
      unfold pre_prepare_matches_entry in *.
      exrepnd.

      unfold log_entry_request_data in *. smash_pbft.
    }

    {
      repndors; [|].

      {
        allrw similar_entry_and_pre_prepare_true_iff.
        unfold change_pre_prepare_info_of_entry in *. destruct a. simpl in *.
        unfold pre_prepare_matches_entry in *. simpl in *.
        exrepnd.
        unfold change_pre_prepare_info in *.
        destruct log_entry_pre_prepare_info; simpl in *; tcsp.
        destruct log_entry_request_data. ginv.
      }

      {
        allrw similar_entry_and_pre_prepare_true_iff.
        left. tcsp.
      }
    }
Qed.

  Lemma add_new_prepare2log_preserves_pre_prepare_somewhere_in_log :
    forall i d gi Fc pp new_prep L new_log,
      add_new_prepare2log i L new_prep Fc = (gi, new_log)
      -> pre_prepare_somewhere_in_log pp d new_log
      -> pre_prepare_somewhere_in_log pp d L.
  Proof.
    induction L; introv IH1 IH2; simpl in *; ginv; simpl in *; smash_pbft; tcsp.

    {
      simpl in *.
      unfold pre_prepare_matches_entry in *.
      repndors; repnd; tcsp.
    }

    {
      repndors;[| tcsp].
      exrepnd.
      unfold add_prepare2entry in *.
      destruct a. smash_pbft.
    }

    {
      repndors;[tcsp |].
      exrepnd.
      unfold add_prepare2entry in *.
      destruct a. smash_pbft.
    }
  Qed.

  (* can we prove stronger one than these. Do we really need it??? *)
  Lemma add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_somewhere_in_log :
    forall i L pp d Fp Fc giop K prep d',
      add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> pre_prepare_somewhere_in_log prep d' K
      -> pre_prepare_somewhere_in_log prep d' L
         \/
         pre_prepare2request_data prep d' = pre_prepare2request_data pp d.
  Proof.
    induction L; introv h q; simpl in *; ginv; simpl in *; smash_pbft; tcsp.

    {
      simpl in *.
      unfold pre_prepare_matches_entry in *. simpl in *.
      unfold pre_prepare_matches_info in *. simpl in *.
      repndors; repnd; tcsp.
    }

    {
      repndors; repnd; tcsp.
      exrepnd.
      destruct x; simpl in *.
      unfold fill_out_pp_info_with_prepare in *.
      destruct a; simpl in *.
      destruct log_entry_pre_prepare_info; simpl in *; ginv; simpl in *; tcsp.
      smash_pbft;[].

      unfold pre_prepare_matches_entry in *. simpl in *.
      repnd; subst; smash_pbft.
    }

    {
      repndors; tcsp.
      allrw similar_entry_and_pre_prepare_false_iff.
      eapply IHL in q; eauto. tcsp.
    }
  Qed.

  (*  can we prove stronger one than these. Do we really need it??? *)
  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_somewhere_in_log :
    forall d' slf prep pp d state state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state (pp,d) = (state', msgs)
      -> pre_prepare_somewhere_in_log  prep d' (log state')
      -> pre_prepare_somewhere_in_log prep d' (log state)
         \/
         pre_prepare2request_data prep d' = pre_prepare2request_data pp d.
  Proof.

    introv h q.
    unfold add_prepare_to_log_from_new_view_pre_prepare in h; smash_pbft.

    match goal with
    | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
      apply check_send_replies_preserves_log in H; simpl in *; subst
    end.

    match goal with
    | [ H : add_new_pre_prepare_and_prepare2log _ _ _ _ _ _ = _ |- _ ] =>
      eapply add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_somewhere_in_log in H;[|eauto]
    end.

    auto.
  Qed.
  Hint Rewrite add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_somewhere_in_log : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_pre_prepare_somewhere_in_log :
    forall d' slf prep pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> pre_prepare_somewhere_in_log prep d' (log state')
      -> pre_prepare_somewhere_in_log prep d' (log state)
         \/
         exists pp d,
           In (pp,d) pps
           /\
           pre_prepare2request_data prep d' = pre_prepare2request_data pp d.
  Proof.
    induction pps; introv h q; simpl in *; smash_pbft; repnd.

    match goal with
    | [ H : add_prepares_to_log_from_new_view_pre_prepares _ _ _ = _ |- _ ] =>
      applydup IHpps in H;auto;[]
    end.
    repndors; tcsp;[|].

    {
      match goal with
      | [ H : add_prepare_to_log_from_new_view_pre_prepare _ _ _ = _ |- _ ] =>
        eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_somewhere_in_log in H;[|eauto]
      end.

      repndors; repnd; tcsp; subst.
      right.
      exists a0 d'; dands; auto; [|].

      {
        left.
        destruct prep, b. simpl in *.
        destruct a0, b. simpl in *. ginv.
      }
      {
        destruct prep, b. simpl in *.
        destruct a0, b. simpl in *. ginv.
      }
    }

    {
      exrepnd; repnd; subst; tcsp.
      right.
      exists pp d'; dands; auto;[ | ].

      {
        right.
        match goal with
        | [ H : pre_prepare2request_data _ _ = pre_prepare2request_data _ _ |- _] =>
          applydup eq_pre_prepare2request_data_implies_eq_digest in H as dd;
            rewrite dd; auto
        end.
      }
      {
         match goal with
        | [ H : pre_prepare2request_data _ _ = pre_prepare2request_data _ _ |- _] =>
          applydup eq_pre_prepare2request_data_implies_eq_digest in H as dd;
            rewrite dd in H; rewrite dd; tcsp
         end.
      }
    }
  Qed.

  Lemma pre_prepare_somewhere_in_log_log_pre_prepares_somewhere_implies :
    forall pp d P L lwm,
      pre_prepare_somewhere_in_log pp d (log_pre_prepares L lwm P)
      -> pre_prepare_somewhere_in_log pp d L
         \/
         exists prep d',
           In (prep,d') P
           /\ lwm < pre_prepare2seq prep
           /\ pre_prepare2request_data prep d' = pre_prepare2request_data pp d.
  Proof.
    induction P; introv h; simpl in *; ginv; simpl in *; smash_pbft; tcsp.

    {
      apply IHP in h; repndors; repnd; tcsp;[|].

      {
        apply pre_prepare_somewhere_in_log_add_new_prepare2log in h; repndors; tcsp.
        repnd; subst; tcsp.
        right.
        exists x0 x1. dands; auto.
      }

      {
        exrepnd.
        right.
        exists prep d'. dands; auto.
      }
    }

    {
      apply IHP in h; repndors; repnd; tcsp.
      exrepnd.
      right.
      exists prep d'. dands; auto.
    }
  Qed.

 Lemma gather_prepared_messages_implies_pre_prepare_somewhere_in_log :
    forall x p,
      In x (gather_prepared_messages (log p) (low_water_mark p))
      -> valid_prepared_info (gather_prepared_messages (log p) (low_water_mark p)) x = true
      -> pre_prepare_somewhere_in_log (prepared_info_pre_prepare x) (prepared_info_digest x) (log p).
  Proof.
    introv; induction (log p); introv inH vH; simpl in *; ginv; simpl in *; smash_pbft; tcsp.

    repndors;[|].

    {
      allrw <- .

      unfold entry2prepared_info in *.
      destruct a; simpl in *; ginv; simpl in *; smash_pbft; tcsp.
      destruct log_entry_pre_prepare_info; simpl in *; ginv; simpl in *; smash_pbft; tcsp.

      unfold pre_prepare_matches_entry. simpl.
      unfold request_data2pre_prepare.
      destruct log_entry_request_data. simpl.
      dands; auto.
      allrw matching_requests_true_iff. auto.
    }
    {
      right.
      apply IHp0; eauto.
      unfold valid_prepared_info in *.
      allrw andb_true; repnd; dands; auto;[]; smash_pbft.
    }
  Qed.
  Hint Rewrite gather_prepared_messages_implies_pre_prepare_somewhere_in_log : pbft.


End PBFT_pre_prepare_somewhere_in_log.


Hint Rewrite @entry_of_pre_prepare_somewhere_in_log : pbft.
Hint Rewrite @clear_log_checkpoint_preserves_pre_prepare_somewhere_in_log : pbft.
Hint Rewrite @check_stable_preserves_pre_prepare_somewhere_in_log : pbft.
Hint Rewrite @pre_prepare_matches_entry_add_replies2entry : pbft.
Hint Rewrite @change_log_entry_add_replies2entry_preserves_pre_prepare_somewhere_in_log : pbft.
Hint Rewrite @add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_somewhere_in_log : pbft.
Hint Rewrite @gather_prepared_messages_implies_pre_prepare_somewhere_in_log : pbft.

Hint Resolve check_send_replies_preserves_pre_prepare_somewhere_in_log : pbft.
Hint Resolve check_send_replies_update_log_preserves_pre_prepare_somewhere_in_log : pbft.
Hint Resolve find_entry_implies_in : pbft.
