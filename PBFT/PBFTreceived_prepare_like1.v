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


Require Export PBFTin_log.
Require Export PBFTquorum.
Require Export PBFTwell_formed_log.
Require Export PBFTwf_view_change_state.
Require Export PBFTpre_prepare_in_log_preserves.
Require Export PBFTin_iseg.
Require Export PBFT_A_1_2_1_somewhere.
Require Export PBFT_A_1_2_2_somewhere.
Require Export PBFT_A_1_2_3.
Require Export PBFTview_change_in_log.
Require Export PBFTcheck_broadcast_new_view.
Require Export PBFTwf_view_change_state_no_repeats.


Section PBFTreceived_prepare_like1.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma prepared_log_implies :
    forall rd L,
      prepared_log rd L = true
      ->
      exists entry,
        In entry L
        /\ rd = log_entry_request_data entry
        /\ is_prepared_entry entry = true.
  Proof.
    induction L; introv h; simpl in *; tcsp; smash_pbft.

    - unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
      exists a; dands; tcsp.

    - apply IHL in h; exrepnd.
      exists entry; dands; auto.
  Qed.

  Lemma is_prepared_entry_implies :
    forall entry,
      is_prepared_entry entry = true
      ->
      exists a reqs,
        2 * F <= length (log_entry_prepares entry)
        /\ log_entry_pre_prepare_info entry = pp_info_pre_prep a reqs.
  Proof.
    introv i.
    destruct entry; simpl in *.
    allrw andb_true; repnd.
    destruct log_entry_pre_prepare_info; simpl in *; ginv.
    allrw Nat.eqb_eq.
    exists auth reqs; tcsp; dands; auto; smash_pbft.
  Qed.

  Definition entry2prepares (e : PBFTlogEntry) : list Prepare :=
    map (request_data_and_rep_toks2prepare (log_entry_request_data e))
        (log_entry_prepares e).

  Definition entry2prepares_like (e : PBFTlogEntry) : list Prepare_like :=
    match entry2pre_prepare e with
    | Some pp => prepare_like_pre_prepare pp :: map prepare_like_prepare (entry2prepares e)
    | None => map prepare_like_prepare (entry2prepares e)
    end.

  Lemma map_prepare_like2sender_prepare_like_prepare_request_data_and_rep_toks2prepare :
    forall rd l,
      map (fun x =>
             prepare_like2sender
               (prepare_like_prepare (request_data_and_rep_toks2prepare rd x))) l
      = map rt_rep l.
  Proof.
    introv; apply map_ext; introv; simpl.
    destruct rd, a; simpl; auto.
  Qed.
  Hint Rewrite map_prepare_like2sender_prepare_like_prepare_request_data_and_rep_toks2prepare : pbft.

  Lemma is_prepared_entry_implies_prepares_like :
    forall entry,
      well_formed_log_entry entry
      -> is_prepared_entry entry = true
      -> (2 * F) + 1 <= length (entry2prepares_like entry)
         /\ no_repeats (map prepare_like2sender (entry2prepares_like entry)).
  Proof.
    introv wf i.
    destruct entry; simpl in *.
    allrw andb_true; repnd.
    allrw Nat.eqb_eq.

    destruct wf as [norep_preps norep_comms niprim cord nfo].

    destruct log_entry_pre_prepare_info; simpl in *; ginv.
    unfold entry2prepares_like; simpl.
    destruct log_entry_request_data; simpl.
    unfold entry2prepares; simpl.
    autorewrite with list pbft.
    pbft_simplifier.
    dands; try omega.

    constructor; auto.
  Qed.

  Definition prepare_like2message (p : Prepare_like) : PBFTmsg :=
    match p with
    | prepare_like_pre_prepare pp => PBFTpre_prepare pp
    | prepare_like_prepare p => PBFTprepare p
    end.

  Definition prepare_like2dmessage (p : Prepare_like) : DirectedMsg :=
    match p with
    | prepare_like_pre_prepare pp => MkDMsg (PBFTpre_prepare pp) [PBFTreplica (pre_prepare2sender pp)] 0
    | prepare_like_prepare p => MkDMsg (PBFTprepare p) [PBFTreplica (prepare2sender p)] 0
    end.

  Fixpoint prepare_like_in_log (p : Prepare_like) (st : PBFTlog) :=
    match st with
    | [] => False
    | entry :: entries =>
      In p (entry2prepares_like entry)
      \/ prepare_like_in_log p entries
    end.

  Lemma prepare_like_in_log_implies_or :
    forall p L,
      prepare_like_in_log p L
      ->
      (exists prep, p = prepare_like_prepare prep /\ prepare_somewhere_in_log prep L = true)
      \/
      (exists pp d, p = prepare_like_pre_prepare pp /\ pre_prepare_somewhere_in_log pp d L = true).
  Proof.
    induction L; introv h; simpl in *; tcsp; repndors; tcsp.

    - destruct p;[right|left]; simpl in *.

      + destruct a; simpl in *.
        unfold entry2prepares_like in *; simpl in *.
        destruct log_entry_request_data; simpl in *.
        unfold pre_prepare_in_entry; simpl.
        destruct log_entry_pre_prepare_info; simpl in *; repndors; ginv.

        * unfold pre_prepare_in_entry; simpl.
          exists (pre_prepare (bare_pre_prepare v s (map fst reqs)) auth).
          simpl; smash_pbft.
          exists d; dands; auto; smash_pbft.
          allrw matching_requests_true_iff; tcsp.

        * unfold entry2prepares in *; simpl in *.
          allrw map_map.
          allrw in_map_iff; exrepnd; ginv.

        * unfold entry2prepares in *; simpl in *.
          allrw map_map.
          allrw in_map_iff; exrepnd; ginv.

      + exists p; dands; auto.
        smash_pbft.
        left.
        unfold entry2prepares_like in *.
        destruct a; simpl in *.
        destruct log_entry_request_data.
        unfold prepare_in_entry; simpl.
        unfold entry2prepares in *; simpl in *.
        unfold is_prepare_for_entry; simpl.
        destruct log_entry_pre_prepare_info; simpl in *; smash_pbft; repndors; tcsp; ginv.

        * allrw map_map; allrw in_map_iff; exrepnd; ginv.
          destruct x; simpl in *.
          unfold eq_request_data; smash_pbft; dands; auto.
          apply existsb_exists.
          eexists; dands; eauto.
          unfold same_rep_tok; smash_pbft.

        * allrw map_map; allrw in_map_iff; exrepnd; ginv.
          destruct x; simpl in *.
          unfold eq_request_data; smash_pbft; dands; auto.
          apply existsb_exists.
          eexists; dands; eauto.
          unfold same_rep_tok; smash_pbft.

    - autodimp IHL hyp.
      repndors; [left|right]; tcsp; exrepnd; subst; tcsp.

      + exists prep; dands; auto; smash_pbft.

      + exists pp d; dands; auto; smash_pbft.
  Qed.

  Definition verify_prepare_like (i : Rep) keys (p : Prepare_like) : bool :=
    match p with
    | prepare_like_pre_prepare pp => verify_pre_prepare i keys pp
    | prepare_like_prepare p => verify_prepare i keys p
    end.

  Lemma check_send_replies_preserves_prepare_like_in_log :
    forall i v keys giop st1 n x2 st2 p,
      check_send_replies i v keys giop st1 n = (x2, st2)
      -> prepare_like_in_log p (log st2)
      -> prepare_like_in_log p (log st1).
  Proof.
    introv check ilog.
    unfold check_send_replies in check; smash_pbft.
    destruct x; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_prepare_like_in_log : pbft.

  Lemma prepare_like_in_log_log_update_log :
    forall p st L,
      prepare_like_in_log p (log (update_log st L))
      = prepare_like_in_log p L.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite prepare_like_in_log_log_update_log : pbft.

  Lemma implies_prepare_like_in_log_log_update_log :
    forall p st L,
      prepare_like_in_log p L
      -> prepare_like_in_log p (log (update_log st L)).
  Proof.
    tcsp.
  Qed.
  Hint Resolve implies_prepare_like_in_log_log_update_log : pbft.

  Hint Rewrite map_id : list.

  Lemma entry2prepares_like_pre_prepare2entry :
    forall pp d,
      entry2prepares_like (pre_prepare2entry pp d)
      = [prepare_like_pre_prepare pp].
  Proof.
    introv; destruct pp, b; simpl.
    unfold entry2prepares_like; simpl.
    autorewrite with list; simpl; auto.
  Qed.
  Hint Rewrite entry2prepares_like_pre_prepare2entry : pbft.

  Lemma in_entry2prepares_like_change_pre_prepare_info_of_entry :
    forall p pp d e,
      similar_entry_and_pre_prepare e pp d = true
      -> In p (entry2prepares_like (change_pre_prepare_info_of_entry pp e))
      -> In p (entry2prepares_like e)
         \/ p = prepare_like_pre_prepare pp.
  Proof.
    introv sim i.
    destruct pp, b, e, log_entry_request_data, log_entry_pre_prepare_info; simpl in *; tcsp.
    unfold eq_request_data in *; simpl in *; smash_pbft.
    autorewrite with pbft list in *.
    unfold entry2prepares_like in *; simpl.
    unfold entry2prepares in *; simpl.
    autorewrite with list in *; simpl.
    repndors; ginv; tcsp.
  Qed.

  Lemma prepare_like_in_log_add_new_pre_prepare2log :
    forall p pp d L,
      prepare_like_in_log p (add_new_pre_prepare2log pp d L)
      -> prepare_like_in_log p L
         \/
         (p = prepare_like_pre_prepare pp /\ pre_prepare_in_log pp d L = false).
  Proof.
    induction L; introv h; simpl in *; smash_pbft; simpl in *; repndors; tcsp.

    destruct pp, b, a; simpl in *.
    unfold entry2prepares_like in *; simpl in *.
    destruct log_entry_request_data; simpl in *.
    destruct log_entry_pre_prepare_info; simpl in *; tcsp.
    unfold entry2prepares in *; simpl in *.
    repndors; subst; simpl in *; tcsp.
    unfold eq_request_data in *; smash_pbft.

    autorewrite with list pbft; ginv; tcsp.
  Qed.

  Lemma prepare2request_data_request_data_and_rep_toks2prepare :
    forall rd rt,
      prepare2request_data (request_data_and_rep_toks2prepare rd rt) = rd.
  Proof.
    introv; destruct rd, rt; simpl; auto.
  Qed.
  Hint Rewrite prepare2request_data_request_data_and_rep_toks2prepare : pbft.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_prepare_like_in_log :
    forall i L pp d Fp Fc giop K p,
      i = rt_rep (Fp tt)
      -> add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> prepare_like_in_log p K
      -> prepare_like_in_log p L
         \/
         (
           p = prepare_like_pre_prepare pp
           /\ pre_prepare_in_log pp d L = false
         )
         \/
         (
           p = prepare_like_prepare (request_data_and_rep_toks2prepare (pre_prepare2request_data pp d) (Fp tt))
           /\ prepare_in_log (request_data_and_rep_toks2prepare (pre_prepare2request_data pp d) (Fp tt)) L = false
         ).
  Proof.
    induction L; introv eqi h q; simpl in *; smash_pbft; repndors; tcsp.

    - simpl in *; smash_pbft; repndors; tcsp.
      destruct pp, b; simpl in *.
      repndors; subst; tcsp.
      autorewrite with list; tcsp.

    - destruct x; simpl in *.
      unfold fill_out_pp_info_with_prepare in *.
      destruct a; simpl in *.
      destruct log_entry_pre_prepare_info; smash_pbft.

      unfold entry2prepares_like in *; simpl in *.
      destruct log_entry_request_data.
      destruct pp, b; simpl in *.
      unfold eq_request_data in *; smash_pbft.
      unfold entry2prepares in *; simpl in *.
      autorewrite with list pbft in *.

      unfold add_prepare_if_not_enough in *; repndors; smash_pbft; repndors; ginv; tcsp;[].

      right; right.
      subst.
      dands; auto.
      apply in_list_rep_toks_false_implies_existsb_same_rep_toks_false.
      autorewrite with pbft.

      remember (Fp tt) as q; destruct q; simpl in *; auto.

    - allrw is_prepare_for_entry_false_iff.
      autorewrite with pbft in *.
      allrw similar_entry_and_pre_prepare_true_iff; tcsp.

    - allrw is_prepare_for_entry_true_iff.
      autorewrite with pbft in *.
      allrw similar_entry_and_pre_prepare_false_iff; tcsp.

    - match goal with
      | [ H : context[add_new_pre_prepare_and_prepare2log] |- _ ] =>
        eapply IHL in H;[|auto|eauto]
      end.
      repndors; tcsp.
  Qed.

  Lemma prepare_like2sender_prepare_like_pre_prepare :
    forall p,
      prepare_like2sender (prepare_like_pre_prepare p) = pre_prepare2sender p.
  Proof.
    introv; tcsp.
  Qed.
  Hint Rewrite prepare_like2sender_prepare_like_pre_prepare : pbft.

  Lemma prepare_like2sender_prepare_like_prepare :
    forall p,
      prepare_like2sender (prepare_like_prepare p) = prepare2sender p.
  Proof.
    introv; tcsp.
  Qed.
  Hint Rewrite prepare_like2sender_prepare_like_prepare : pbft.

  Lemma prepare2sender_pre_prepare2prepare :
    forall i keys p d,
      prepare2sender (pre_prepare2prepare i keys p d) = i.
  Proof.
    introv; destruct p, b; simpl; auto.
  Qed.
  Hint Rewrite prepare2sender_pre_prepare2prepare : pbft.

  Lemma add_new_prepare2log_preserves_prepare_like_in_log :
    forall i L prep Fc giop K p,
      add_new_prepare2log i L prep Fc = (giop, K)
      -> prepare_like_in_log p K
      -> prepare_like_in_log p L
         \/ p = prepare_like_prepare prep.
  Proof.
    induction L; introv h q; simpl in *; smash_pbft; repndors; tcsp.

    - simpl in *; smash_pbft; repndors; tcsp.
      destruct prep, b; simpl in *.
      repndors; subst; tcsp.

    - unfold add_prepare2entry in *.
      destruct a; simpl in *; smash_pbft.
      unfold entry2prepares_like in *; simpl in *.
      destruct log_entry_request_data.
      destruct log_entry_pre_prepare_info; simpl in *; tcsp.

      + unfold entry2prepares in *; simpl in *.
        repndors; subst; simpl in *; tcsp.
        autorewrite with list pbft in *.
        unfold add_prepare_if_not_enough in *; smash_pbft.
        destruct prep, b; simpl in *.
        repndors; subst; simpl in *; tcsp.
        autorewrite with pbft.
        unfold is_prepare_for_entry, eq_request_data in *; simpl in *.
        smash_pbft; ginv.

      + unfold entry2prepares in *; simpl in *.
        autorewrite with list pbft in *.
        unfold add_prepare_if_not_enough in *; smash_pbft.
        destruct prep, b; simpl in *.
        repndors; subst; simpl in *; tcsp.
        autorewrite with pbft.
        unfold is_prepare_for_entry, eq_request_data in *; simpl in *.
        smash_pbft; ginv.

    - match goal with
      | [ H : context[add_new_prepare2log] |- _ ] => eapply IHL in H;[|eauto]
      end.
      repndors; tcsp.
  Qed.

  Lemma add_new_commit2log_preserves_prepare_like_in_log :
    forall L c giop K p,
      add_new_commit2log L c = (giop, K)
      -> prepare_like_in_log p K
      -> prepare_like_in_log p L.
  Proof.
    induction L; introv h q; simpl in *; smash_pbft; repndors; tcsp;
      simpl in *; repndors; tcsp.

    - unfold MkNewLogEntryFromCommit in *; simpl in *.
      unfold entry2prepares_like in *; simpl in *.
      destruct c, b; simpl in *; tcsp.

    - unfold add_commit2entry in *.
      destruct a; simpl in *; smash_pbft.

    - right; eapply IHL; eauto.
  Qed.
  Hint Resolve add_new_commit2log_preserves_prepare_like_in_log : pbft.

  Lemma clear_log_checkpoint_preserves_prepare_like_in_log :
    forall p L sn,
      prepare_like_in_log p (clear_log_checkpoint L sn)
      -> prepare_like_in_log p L.
  Proof.
    induction L; simpl in *; introv h; tcsp; smash_pbft.
    repndors; tcsp.
    right; eapply IHL; eauto.
  Qed.
  Hint Resolve clear_log_checkpoint_preserves_prepare_like_in_log : pbft.

  Lemma check_stable_preserves_prepare_like_in_log :
    forall slf state entryop state' p,
      check_stable slf state entryop = Some state'
      -> prepare_like_in_log p (log state')
      -> prepare_like_in_log p (log state).
  Proof.
    introv h q.
    unfold check_stable in h.
    pbft_dest_all x;[].
    apply clear_log_checkpoint_preserves_prepare_like_in_log in q; auto.
  Qed.
  Hint Resolve check_stable_preserves_prepare_like_in_log : pbft.

  Lemma map_fst_combine_replies :
    forall reqs reps,
      map fst (combine_replies reqs reps) = map fst reqs.
  Proof.
    induction reqs; introv; simpl; destruct reps; tcsp.
    repnd; simpl; allrw; auto.
  Qed.
  Hint Rewrite map_fst_combine_replies : pbft.

  Lemma entry2prepares_like_add_replies2entry :
    forall entry reps,
      entry2prepares_like (add_replies2entry entry reps) = entry2prepares_like entry.
  Proof.
    destruct entry; introv; simpl.
    unfold entry2prepares_like; simpl.
    destruct log_entry_request_data; simpl;[].
    destruct log_entry_pre_prepare_info; simpl; tcsp.
    autorewrite with list pbft.
    unfold entry2prepares; simpl; tcsp.
  Qed.
  Hint Rewrite entry2prepares_like_add_replies2entry : pbft.

  Lemma change_entry_add_replies2entry_preserves_prepare_like_in_log :
    forall prep sn entry L reps,
      prepare_like_in_log prep (change_entry L (add_replies2entry entry reps))
      -> find_entry L sn = Some entry
      -> prepare_like_in_log prep L.
  Proof.
    induction L; introv h fe; simpl in *; tcsp.
    smash_pbft; repndors; tcsp;
      try (complete (applydup entry2seq_if_find_entry in fe as eqsn;
                     match goal with
                     | [ H : similar_entry _ _ = _ |- _ ] => apply entry2seq_if_similar_entry in H
                     end;
                     match goal with
                     | [ H : _ <> _ |- _ ] => destruct H; allrw; auto
                     end));[].

    right.
    eapply IHL; eauto.
  Qed.
  Hint Resolve change_entry_add_replies2entry_preserves_prepare_like_in_log : pbft.

  Lemma find_and_execute_requests_preserves_prepare_like_in_log :
    forall msg i prep st p,
      find_and_execute_requests i (current_view p) (local_keys p) p = (msg, st)
      -> prepare_like_in_log prep (log st)
      -> prepare_like_in_log prep (log p).
  Proof.
    introv find ilog.

    unfold find_and_execute_requests in *; smash_pbft.
    unfold execute_requests in *.
    destruct (ready p); simpl in *; smash_pbft.

    match goal with
    | [ H : check_broadcast_checkpoint _ _ _ _ _ = _ |- _ ] =>
      apply check_broadcast_checkpoint_preserves_log in H
    end.
    simpl in *.

    match goal with
    | [ H1 : prepare_like_in_log _ (log ?s), H2 : _ = log ?s |- _ ] =>
      rewrite <- H2 in H1; clear H2
    end.
    eapply change_entry_add_replies2entry_preserves_prepare_like_in_log in ilog; eauto.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_prepare_like_in_log : pbft.

  Lemma prepare_like_in_log_log_pre_prepares_implies :
    forall p P L lwm,
      prepare_like_in_log p (log_pre_prepares L lwm P)
      -> prepare_like_in_log p L
         \/
         exists pp d,
           p = prepare_like_pre_prepare pp
           /\ In (pp,d) P
           /\ pre_prepare_in_log pp d L = false.
  Proof.
    induction P; introv h; simpl in *; tcsp.
    repnd; simpl in *; smash_pbft; apply IHP in h; repndors; repnd; tcsp;[| |].

    {
      apply prepare_like_in_log_add_new_pre_prepare2log in h; repndors; repnd; subst; tcsp.
      right.
      exists a0 a; dands; tcsp.
    }

    {
      exrepnd; subst; simpl in *.
      apply pre_prepare_in_log_add_new_pre_prepare2log_false_implies in h1; tcsp.
      right.
      exists pp d; dands; tcsp.
    }

    {
      exrepnd; subst; simpl in *; tcsp.
      right.
      exists pp d; dands; tcsp.
    }
  Qed.

  Lemma update_state_new_view_preserves_prepare_like_in_log :
    forall i st nv st' msgs p,
      update_state_new_view i st nv = (st', msgs)
      -> prepare_like_in_log p (log st')
      -> prepare_like_in_log p (log st).
  Proof.
    introv u prep.
    unfold update_state_new_view in *; smash_pbft.
    unfold log_checkpoint_cert_from_new_view in *; smash_pbft.
  Qed.
  Hint Resolve update_state_new_view_preserves_prepare_like_in_log : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_like_in_log :
    forall slf p pp d state state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state (pp,d) = (state', msgs)
      -> prepare_like_in_log p (log state')
      -> prepare_like_in_log p (log state)
         \/
         (
           p = prepare_like_pre_prepare pp
           /\ pre_prepare_in_log pp d (log state) = false
         )
         \/
         (
           p = prepare_like_prepare (pre_prepare2prepare slf (local_keys state) pp d)
           /\ prepare_in_log (pre_prepare2prepare slf (local_keys state) pp d) (log state) = false
         ).
  Proof.
    introv h q.
    unfold add_prepare_to_log_from_new_view_pre_prepare in h; smash_pbft.

    match goal with
    | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
      apply check_send_replies_preserves_log in H; simpl in *; subst
    end.

    match goal with
    | [ H : add_new_pre_prepare_and_prepare2log _ _ _ _ _ _ = _ |- _ ] =>
      eapply add_new_pre_prepare_and_prepare2log_preserves_prepare_like_in_log in H;
        [| |eauto]; autorewrite with pbft; auto
    end.

    autorewrite with pbft in *.
    repndors; repnd; subst; tcsp.
  Qed.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_pre_prepare_in_log_forward :
    forall i L pp Fp Fc giop d K prep d',
      add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> pre_prepare_in_log prep d' L = true
      -> pre_prepare_in_log prep d' K = true.
  Proof.
    induction L; introv add ilog; simpl in *; smash_pbft.

    - allrw auth_matches_logEntryPrePrepareInfo_true_iff.
      exrepnd.
      destruct a; simpl in *.
      destruct log_entry_pre_prepare_info; simpl in *; ginv.

    - allrw auth_matches_logEntryPrePrepareInfo_true_iff.
      exrepnd.
      allrw similar_entry_and_pre_prepare_false_iff.

      match goal with
      | [ H : context[fill_out_pp_info_with_prepare] |- _ ] => rename H into fill
      end.
      apply gi_entry_of_fill_out_pp_info_with_prepare_some in fill.
      allrw similar_entry_and_pre_prepare_true_iff.
      match goal with
      | [ H1 : ?x = _, H2 : ?x <> _ |- _ ] => rewrite H1 in H2
      end.
      tcsp.

    - allrw auth_matches_logEntryPrePrepareInfo_true_iff.
      exrepnd.
      allrw similar_entry_and_pre_prepare_false_iff.

      match goal with
      | [ H : context[fill_out_pp_info_with_prepare] |- _ ] => rename H into fill
      end.
      apply gi_entry_of_fill_out_pp_info_with_prepare_some in fill.
      allrw similar_entry_and_pre_prepare_true_iff.
      match goal with
      | [ H1 : ?x = _, H2 : ?x <> _ |- _ ] => rewrite H1 in H2
      end.
      repeat match goal with
             | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2
             end.
      tcsp.
  Qed.

  Lemma check_send_replies_preserves_pre_prepare_in_log_forward :
    forall d prep slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> pre_prepare_in_log d prep (log state) = true
      -> pre_prepare_in_log d prep (log state') = true.
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_pre_prepare_in_log_forward : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_in_log_forward :
    forall i state pp d pp' d' state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare i state (pp, d) = (state', msgs)
      -> pre_prepare_in_log pp' d' (log state) = true
      -> pre_prepare_in_log pp' d' (log state') = true.
  Proof.
    introv add ilog.
    unfold add_prepare_to_log_from_new_view_pre_prepare in *; smash_pbft.
  Qed.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_like_in_log :
    forall slf p pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> prepare_like_in_log p (log state')
      -> prepare_like_in_log p (log state)
         \/
         exists pp d,
           In (pp,d) pps
           /\
           (
             (
               p = prepare_like_pre_prepare pp
               /\ pre_prepare_in_log pp d (log state) = false
             )
             \/
             (
               p = prepare_like_prepare (pre_prepare2prepare slf (local_keys state) pp d)
               /\ prepare_in_log (pre_prepare2prepare slf (local_keys state) pp d) (log state) = false
             )
           ).
  Proof.
    induction pps; introv h q; simpl in *; smash_pbft; repnd.

    match goal with
    | [ H : add_prepares_to_log_from_new_view_pre_prepares _ _ _ = _ |- _ ] =>
      applydup IHpps in H;auto;[]
    end.
    clear IHpps.
    repndors; tcsp;[|].

    {
      match goal with
      | [ H : add_prepare_to_log_from_new_view_pre_prepare _ _ _ = _ |- _ ] =>
        eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_like_in_log in H;[|eauto]
      end.

      repndors; repnd; subst; tcsp.

      - right.
        eexists; eexists; dands; eauto.

      - right.
        eexists; eexists; dands; eauto.
    }

    {
      exrepnd; repndors; repnd; subst; tcsp.

      - right.
        eexists; eexists; dands; eauto.
        left; dands; auto.

        match goal with
        | [ |- ?a = _ ] => remember a as b
        end.
        symmetry in Heqb; destruct b; tcsp.

        match goal with
        | [ H : context[add_prepare_to_log_from_new_view_pre_prepare] |- _ ] => rename H into add
        end.
        eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_pre_prepare_in_log_forward in add; tcsp;[|eauto]; tcsp.

      - right.
        eexists; eexists; dands; eauto.

        match goal with
        | [ H : context[add_prepare_to_log_from_new_view_pre_prepare] |- _ ] => rename H into add
        end.

        applydup add_prepare_to_log_from_new_view_pre_prepare_preserves_local_keys in add.
        allrw.
        right; dands; auto.

        match goal with
        | [ |- ?a = _ ] => remember a as b
        end.
        symmetry in Heqb; destruct b; tcsp.

        eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_in_log_forward in add;[|eauto].
        rewrite <- add0 in add; tcsp.
    }
  Qed.

  Lemma verify_list_auth_data_app :
    forall i keys l1 l2,
      verify_list_auth_data i keys (l1 ++ l2)
      = verify_list_auth_data i keys l1 && verify_list_auth_data i keys l2.
  Proof.
    induction l1; introv; simpl; auto.
    rewrite IHl1.
    rewrite andb_assoc; auto.
  Qed.

  Lemma implies_verify_pre_prepare :
    forall i keys pp,
      verify_one_auth_data (PBFTreplica i) keys (pre_prepare_data2auth_data_pre pp) = true
      -> verify_list_auth_data (PBFTreplica i) keys (pre_prepare2auth_data_req pp) = true
      -> verify_pre_prepare i keys pp = true.
  Proof.
    introv v1 v2.
    unfold verify_pre_prepare; simpl; smash_pbft.
  Qed.
  Hint Resolve implies_verify_pre_prepare : pbft.

  Lemma verify_pre_prepares_implies_verify_pre_prepare :
    forall pp l i keys,
      In pp l
      -> verify_list_auth_data (PBFTreplica i) keys (pre_prepares2auth_data l) = true
      -> verify_pre_prepare i keys pp = true.
  Proof.
    induction l; introv j verif; simpl in *; tcsp.
    allrw verify_list_auth_data_app; smash_pbft.
    repndors; subst; tcsp; eauto 3 with pbft.
  Qed.
  Hint Resolve verify_pre_prepares_implies_verify_pre_prepare : pbft.

  Lemma verify_new_view_implies_verify_pre_prepare :
    forall pp v i keys,
      In pp (new_view2oprep v ++ new_view2nprep v)
      -> verify_new_view i keys v = true
      -> verify_pre_prepare i keys pp = true.
  Proof.
    introv j verif.
    destruct v, v; simpl in *.
    allrw in_app_iff.
    unfold verify_new_view in *; simpl in *.
    repeat (rewrite verify_list_auth_data_app in verif).
    allrw andb_true; repnd.
    repndors; eauto 2 with pbft.
  Qed.
  Hint Resolve verify_new_view_implies_verify_pre_prepare : pbft.

  Lemma pre_prepare2auth_data_in_pre_prepares2auth_data :
    forall pp l,
      In pp l
      -> subset (pre_prepare2auth_data pp) (pre_prepares2auth_data l).
  Proof.
    induction l; introv i; simpl in *; tcsp.
    repndors; subst; tcsp;
      try (complete (unfold pre_prepare2auth_data;
                     apply implies_subset_cons_lr_same;
                     apply implies_subset_app_r; tcsp));
      try (complete (apply implies_subset_cons_r_weak;
                     apply implies_subset_app_r; tcsp)).
  Qed.
  Hint Resolve pre_prepare2auth_data_in_pre_prepares2auth_data : pbft.

  Lemma pre_prepare2auth_data_in_new_view2auth_data :
    forall pp v,
      In pp (new_view2oprep v ++ new_view2nprep v)
      -> subset (pre_prepare2auth_data pp) (new_view2auth_data v).
  Proof.
    introv i.
    destruct v, v; simpl in *.
    apply implies_subset_cons_r_weak.
    apply implies_subset_app_r; right.
    apply implies_subset_app_r.
    allrw in_app_iff; repndors;[left|right]; eauto 2 with pbft.
  Qed.
  Hint Resolve pre_prepare2auth_data_in_new_view2auth_data : pbft.

  Lemma pre_prepare_data2auth_data_pre_in_pre_prepares2auth_data :
    forall pp l,
      In pp l
      -> In (pre_prepare_data2auth_data_pre pp) (pre_prepares2auth_data l).
  Proof.
    induction l; introv i; simpl in *; tcsp.
    repndors; subst; tcsp;
      try (complete (unfold pre_prepare2auth_data;
                     apply implies_subset_cons_lr_same;
                     apply implies_subset_app_r; tcsp));
      try (complete (apply implies_subset_cons_r_weak;
                     apply implies_subset_app_r; tcsp));
      try (complete (allrw in_app_iff; tcsp)).
  Qed.
  Hint Resolve pre_prepare_data2auth_data_pre_in_pre_prepares2auth_data : pbft.

  Lemma pre_prepare_data2auth_data_pre_in_new_view2auth_data :
    forall pp v,
      In pp (new_view2oprep v ++ new_view2nprep v)
      -> In (pre_prepare_data2auth_data_pre pp) (new_view2auth_data v).
  Proof.
    introv i.
    destruct v, v; simpl in *.
    allrw in_app_iff.
    right; right.
    repndors;[left|right]; eauto 2 with pbft.
  Qed.
  Hint Resolve pre_prepare_data2auth_data_pre_in_new_view2auth_data : pbft.

  Lemma bare_prepare2sender_pre_prepare2bare_prepare :
    forall pp d i,
      bare_prepare2sender (pre_prepare2bare_prepare pp d i) = i.
  Proof.
    introv; destruct pp, b; simpl; auto.
  Qed.
  Hint Rewrite bare_prepare2sender_pre_prepare2bare_prepare : pbft.

  Lemma implies_prepare_like_in_log :
    forall pl entry L,
      In pl (entry2prepares_like entry)
      -> In entry L
      -> prepare_like_in_log pl L.
  Proof.
    induction L; introv i j; simpl in *; tcsp; repndors; subst; tcsp.
  Qed.
  Hint Resolve implies_prepare_like_in_log : pbft.

  Lemma prepared_log_implies_first :
    forall rd L,
      prepared_log rd L = true
      ->
      exists entry l,
        In_iseg l entry L
        /\ (forall e, In e l -> is_request_data_for_entry e rd = false)
        /\ rd = log_entry_request_data entry
        /\ is_prepared_entry entry = true.
  Proof.
    induction L; introv h; simpl in *; tcsp; smash_pbft.

    - unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
      exists a ([] : list PBFTlogEntry); simpl; dands; tcsp.

    - apply IHL in h; exrepnd.
      exists entry (a :: l); simpl; dands; auto.
      introv xx; repndors; subst; tcsp.
  Qed.

  Lemma prepare_like_prepare_in_entry2prepares_like_implies :
    forall p entry v n d,
      In (prepare_like_prepare p) (entry2prepares_like entry)
      -> request_data v n d = log_entry_request_data entry
      -> exists a i, p = mk_prepare v n d i a /\ In (MkRepToks i a) (log_entry_prepares entry).
  Proof.
    introv ie erd.
    destruct entry; simpl in *.
    destruct log_entry_request_data; ginv.
    destruct p, b.
    unfold entry2prepares_like in ie; simpl in ie.
    destruct log_entry_pre_prepare_info; simpl in *; repndors; ginv; simpl in *.

    - unfold entry2prepares in ie; simpl in *.
      allrw map_map; unfold compose in *.
      allrw in_map_iff; exrepnd.
      destruct x; ginv.
      unfold mk_prepare.
      eexists; eexists; eauto.

    - unfold entry2prepares in ie; simpl in *.
      allrw map_map; unfold compose in *.
      allrw in_map_iff; exrepnd.
      destruct x; ginv.
      unfold mk_prepare.
      eexists; eexists; eauto.
  Qed.

  Lemma prepare_like_pre_prepare_in_entry2prepares_like_implies :
    forall p entry v n d,
      well_formed_log_entry entry
      -> In (prepare_like_pre_prepare p) (entry2prepares_like entry)
      -> request_data v n d = log_entry_request_data entry
      -> exists a reqs, p = mk_pre_prepare v n reqs a /\ d = create_hash_messages (map PBFTrequest reqs).
  Proof.
    introv wf ie erd.
    pose proof (well_formed_log_entry_correct_digest entry) as wfe.
    autodimp wfe hyp; clear wf.
    destruct entry; simpl in *.
    unfold pp_info_has_correct_digest in wfe.
    destruct log_entry_request_data; ginv.
    destruct p, b.
    unfold entry2prepares_like in ie; simpl in ie.
    unfold mk_pre_prepare.
    destruct log_entry_pre_prepare_info; simpl in *; repndors; ginv; simpl in *.

    - unfold same_digests in *; smash_pbft.
      eexists; eexists; dands; eauto.
      allrw map_map; unfold compose; auto.

    - unfold entry2prepares in ie; simpl in *.
      allrw map_map; unfold compose in *.
      allrw in_map_iff; exrepnd; ginv.

    - unfold entry2prepares in ie; simpl in *.
      allrw map_map; unfold compose in *.
      allrw in_map_iff; exrepnd; ginv.
  Qed.

  Lemma request_data_eq_log_entry_request_data_implies_view :
    forall v n d e,
      request_data v n d = log_entry_request_data e
      -> entry2view e = v.
  Proof.
    introv h; destruct e, log_entry_request_data; simpl in *; ginv; auto.
  Qed.

  Lemma well_formed_log_implies_correct_digest :
    forall v n r a d L,
      well_formed_log L
      -> pre_prepare_in_log (mk_pre_prepare v n r a) d L = true
      -> d = create_hash_messages (map PBFTrequest r).
  Proof.
    induction L; introv wf prep; simpl in *; ginv.
    inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
    smash_pbft;[].
    clear IHL.

    pose proof (well_formed_log_entry_correct_digest a0 wf1) as wfd.
    clear wf1 wf2.

    destruct a0; simpl in *.
    unfold pp_info_has_correct_digest in *.
    destruct log_entry_pre_prepare_info in *; ginv;[].
    unfold same_digests in *; smash_pbft.
    destruct log_entry_request_data; simpl in *; subst.
    unfold eq_request_data in *; smash_pbft; ginv;[].
    allrw matching_requests_true_iff; subst.
    allrw map_map; auto.
  Qed.

  Definition prepare_like2auth_data (p : Prepare_like) : list AuthenticatedData :=
    match p with
    | prepare_like_pre_prepare pp => pre_prepare2auth_data pp
    | prepare_like_prepare p => [prepare2auth_data p]
    end.

  Definition prepare_like2main_auth_data (p : Prepare_like) : AuthenticatedData :=
    match p with
    | prepare_like_pre_prepare pp => pre_prepare_data2auth_data_pre pp
    | prepare_like_prepare p => prepare2auth_data p
    end.

  Lemma verify_prepare_like_implies_verify_authenticated_data :
    forall i pl keys,
      verify_prepare_like i keys pl = true
      -> verify_list_auth_data (PBFTreplica i) keys (prepare_like2auth_data pl) = true.
  Proof.
    introv verif.
    destruct pl; simpl in *; tcsp; smash_pbft.
  Qed.
  Hint Resolve verify_prepare_like_implies_verify_authenticated_data : pbft.

  Lemma verify_pre_prepare_implies_verify_authenticated_data_pre_prepare_data2auth_data_pre :
    forall i keys pp,
      verify_pre_prepare i keys pp = true
      -> verify_authenticated_data (PBFTreplica i) (pre_prepare_data2auth_data_pre pp) keys = true.
  Proof.
    introv verify; unfold verify_pre_prepare in verify; simpl in *; smash_pbft.
  Qed.
  Hint Resolve verify_pre_prepare_implies_verify_authenticated_data_pre_prepare_data2auth_data_pre : pbft.

  Lemma verify_prepare_like_implies_verify_main_authenticated_data :
    forall i pl keys,
      verify_prepare_like i keys pl = true
      -> verify_authenticated_data (PBFTreplica i) (prepare_like2main_auth_data pl) keys = true.
  Proof.
    introv verif.
    destruct pl; simpl in *; tcsp; smash_pbft.
  Qed.
  Hint Resolve verify_prepare_like_implies_verify_main_authenticated_data : pbft.

  Lemma PBFTdata_auth_prepare_like2main_auth_data_some_implies :
    forall i k pl,
      PBFTdata_auth (PBFTreplica i) (prepare_like2main_auth_data pl) = Some k
      -> k = PBFTreplica (prepare_like2sender pl).
  Proof.
    introv h.
    destruct pl; simpl in *.

    - destruct pp; simpl in *; ginv; auto.

    - destruct p; simpl in *; ginv; auto.
  Qed.

  Lemma pre_prepare_not_in_checkpoints2auth_data :
    forall pp a C,
      ~ In (MkAuthData (PBFTmsg_bare_pre_prepare pp) a) (checkpoints2auth_data C).
  Proof.
    induction C; introv i; simpl in *; tcsp.
    repndors; tcsp.
    destruct a0; simpl in *; ginv.
  Qed.

  Lemma prepare_like2main_auth_data_in_get_contained_auth_data_implies :
    forall pl m,
      In (prepare_like2main_auth_data pl) (PBFTget_contained_auth_data m)
      -> (exists p, m = PBFTprepare p)
         \/ (exists pp, m = PBFTpre_prepare pp)
         \/ (exists vc, m = PBFTview_change vc)
         \/ (exists nv, m = PBFTnew_view nv).
  Proof.
    introv i.
    destruct m, pl as [x|x]; simpl in *; repndors; tcsp;
      try (complete (destruct r, x; simpl in *; ginv));
      try (complete (destruct c, x; simpl in *; ginv));
      try (complete (left; eexists; auto));
      try (complete (right; left; eexists; auto));
      try (complete (right; right; left; eexists; eauto));
      try (complete (right; right; right; eexists; eauto)).
  Qed.

  Lemma prepare2auth_data_equal_prepare_like2main_auth_data_implies :
    forall p pl,
      prepare2auth_data p = prepare_like2main_auth_data pl
      -> pl = prepare_like_prepare p.
  Proof.
    introv h.
    destruct p, pl as [x|x], x; simpl in *; ginv; auto.
  Qed.

  Lemma in_check_broadcast_commit_implies :
    forall x i rd entryop,
      In x (check_broadcast_commit i rd entryop)
      -> exists c dst, x = send_commit c dst.
  Proof.
    introv j.
    destruct entryop; simpl in *; tcsp.
    destruct g; smash_pbft.
    destruct gi_commit; simpl in *; tcsp; smash_pbft.
  Qed.

  Lemma in_check_broadcast_prepare_implies :
    forall x i rd entryop,
      In x (check_broadcast_prepare i rd entryop)
      ->
      exists p comm entry,
        entryop = Some (MkGeneratedInfo (add_prepare_status_added p) comm entry)
        /\ is_pre_prepared_entry entry = true
        /\ x = send_prepare (request_data_and_rep_toks2prepare rd p) (other_names i).
  Proof.
    introv j.
    destruct entryop; simpl in *; tcsp;[].
    destruct g; simpl in *; ginv; [].
    smash_pbft.
    destruct gi_prepare; simpl in *; tcsp.
    repndors; subst; tcsp.
    eexists; eexists; eexists; dands; eauto.
  Qed.

  Lemma prepare2rep_toks_request_data_and_rep_toks2prepare :
    forall rd rt,
      prepare2rep_toks (request_data_and_rep_toks2prepare rd rt) = rt.
  Proof.
    introv; destruct rd, rt; simpl; auto.
  Qed.
  Hint Rewrite prepare2rep_toks_request_data_and_rep_toks2prepare : pbft.

  Lemma add_new_pre_prepare_and_prepare2log_add_prepare_status_added_implies_prepare_in_log :
    forall i L pp d Fp Fc rt comm entry K,
      add_new_pre_prepare_and_prepare2log i L pp d Fp Fc
      = (Some (MkGeneratedInfo (add_prepare_status_added rt) comm entry), K)
      -> prepare_in_log (request_data_and_rep_toks2prepare (pre_prepare2request_data pp d) rt) K = true.
  Proof.
    induction L; introv add; simpl in *; pbft_simplifier; simpl in *; smash_pbft.

    - unfold same_rep_tok; smash_pbft.

    - unfold is_prepare_for_entry, eq_request_data in *; simpl in *; smash_pbft.

    - unfold is_prepare_for_entry, eq_request_data in *; simpl in *; smash_pbft.
      destruct a, log_entry_pre_prepare_info; simpl in *; ginv.
      smash_pbft;[].
      subst; simpl in *.
      unfold add_prepare_if_not_enough in *; smash_pbft;[].
      unfold same_rep_tok; smash_pbft.

    - unfold is_prepare_for_entry, eq_request_data in *; simpl in *; smash_pbft.
      destruct a, log_entry_pre_prepare_info; simpl in *; ginv.
      smash_pbft.

    - unfold is_prepare_for_entry, eq_request_data in *; smash_pbft.
      allrw similar_entry_and_pre_prepare_false_iff; tcsp.
  Qed.
  Hint Resolve add_new_pre_prepare_and_prepare2log_add_prepare_status_added_implies_prepare_in_log : pbft.

  Lemma message_in_check_send_replies_implies :
    forall i v keys entryop s1 n msgs s2 x,
      check_send_replies i v keys entryop s1 n = (msgs, s2)
      -> In x msgs
      -> x = send_check_ready i.
  Proof.
    introv check j.
    unfold check_send_replies in check; smash_pbft.
    destruct x0; smash_pbft.
  Qed.
  Hint Resolve message_in_check_send_replies_implies : pbft.

  Lemma message_in_check_broadcast_checkpoint_implies :
    forall i n v keys s1 s2 msgs x,
      check_broadcast_checkpoint i n v keys s1 = (s2, msgs)
      -> In x msgs
      -> (exists c o, x = send_checkpoint c o)
         \/ x = send_check_stable i.
  Proof.
    introv check j.
    unfold check_broadcast_checkpoint in check; smash_pbft.
    repndors; subst; smash_pbft.
    left.
    unfold broadcast2others; simpl; eexists; eexists; eauto.
  Qed.

  Lemma message_in_find_and_execute_requests_implies :
    forall i v keys s1 msgs s2 x,
      find_and_execute_requests i v keys s1 = (msgs, s2)
      -> In x msgs
      -> x = send_check_ready i
         \/ (exists r, x = send_reply r)
         \/ (exists c o, x = send_checkpoint c o)
         \/ x = send_check_stable i.
  Proof.
    introv check j.
    unfold find_and_execute_requests in check; smash_pbft;[].
    unfold execute_requests in *.
    destruct (ready s1); pbft_simplifier; simpl in *; tcsp;[].
    smash_pbft.
    allrw in_app_iff.
    allrw in_map_iff.
    simpl in *.
    repndors; exrepnd; subst; tcsp;[right; left; eexists; eauto|];[].

    rename_hyp_with check_broadcast_checkpoint check.
    eapply message_in_check_broadcast_checkpoint_implies in check;[|eauto].
    repndors; tcsp.
    right; right; auto.
  Qed.

  Lemma message_in_update_state_new_view_implies :
    forall i s1 nv s2 msgs x,
      update_state_new_view i s1 nv = (s2, msgs)
      -> In x msgs
      -> exists c o, x = send_checkpoint c o.
  Proof.
    introv upd j.
    unfold update_state_new_view in upd; smash_pbft;[].
    unfold broadcast_checkpoint_op in j; smash_pbft;[].
    unfold broadcast2others; eexists; eexists; eauto.
  Qed.

  Lemma prepare_in_add_prepare_to_log_from_new_view_pre_prepare_is_in_log :
    forall p dst i s1 a s2 msgs,
      add_prepare_to_log_from_new_view_pre_prepare i s1 a = (s2, msgs)
      -> In (send_prepare p dst) msgs
      -> prepare_in_log p (log s2) = true.
  Proof.
    introv add j.
    unfold add_prepare_to_log_from_new_view_pre_prepare in add; smash_pbft;
      allrw in_app_iff; repndors; try conflicting_sends;
        try (rename_hyp_with add_new_pre_prepare_and_prepare2log add);
        try (rename_hyp_with check_send_replies check);[| |].

    - eapply check_send_replies_preserves_prepare_in_log_forward;[eauto|].
      simpl.
      clear check.

      destruct x2; simpl in *; smash_pbft;[].
      destruct g; smash_pbft;[].
      destruct gi_prepare; smash_pbft;[].
      unfold broadcast2others in *; exrepnd; ginv.
      eauto 3 with pbft.

    - eapply check_send_replies_preserves_prepare_in_log_forward;[eauto|].
      simpl.
      clear check.

      destruct x2; simpl in *; smash_pbft;[].
      destruct g; smash_pbft;[].
      destruct gi_commit; smash_pbft.

    - eapply check_send_replies_preserves_prepare_in_log_forward;[eauto|].
      simpl.
      eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
  Qed.
  Hint Resolve prepare_in_add_prepare_to_log_from_new_view_pre_prepare_is_in_log : pbft.

  Lemma prepare_in_add_prepares_to_log_from_new_view_pre_prepares_is_in_log :
    forall p dst i L s1 s2 msgs,
      In (send_prepare p dst) msgs
      -> add_prepares_to_log_from_new_view_pre_prepares i s1 L = (s2, msgs)
      -> prepare_in_log p (log s2) = true.
  Proof.
    induction L; introv j add; simpl in *; pbft_simplifier; simpl in *; tcsp.
    smash_pbft;[].
    allrw in_app_iff;repndors;[|eapply IHL;eauto];[].

    rename_hyp_with add_prepare_to_log_from_new_view_pre_prepare add.
    rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares adds.
    eauto 3 with pbft.
  Qed.
  Hint Resolve prepare_in_add_prepares_to_log_from_new_view_pre_prepares_is_in_log : pbft.

  Lemma send_prepare_in_trim_outputs_with_low_water_mark :
    forall p dst msgs st,
      In (send_prepare p dst) (trim_outputs_with_low_water_mark msgs st)
      -> In (send_prepare p dst) msgs
         /\ low_water_mark st < prepare2seq p.
  Proof.
    introv i.
    unfold trim_outputs_with_low_water_mark in i.
    apply filter_In in i; repnd.
    unfold trim_output_with_low_water_mark in i; simpl in i; smash_pbft.
  Qed.

  Lemma update_state_new_view_preserves_prepare_in_log_true_forward :
    forall p i s1 nv s2 msgs,
      correct_new_view nv = true
      -> update_state_new_view i s1 nv = (s2, msgs)
      -> low_water_mark s2 < prepare2seq p
      -> prepare_in_log p (log s1) = true
      -> prepare_in_log p (log s2) = true.
  Proof.
    introv cor upd h prep.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    eapply update_state_new_view_preserves_prepare_in_log_false_forward in upd; eauto.
  Qed.
  Hint Resolve update_state_new_view_preserves_prepare_in_log_true_forward : pbft.

  Lemma pre_prepare2auth_data_equal_prepare_like2auth_data_implies :
    forall p pl,
      pre_prepare2auth_data p = prepare_like2auth_data pl
      -> pl = prepare_like_pre_prepare p.
  Proof.
    introv h.
    destruct p, pl as [x|x], x; simpl in *; ginv; auto.
  Qed.

  Lemma pre_prepare_data2auth_data_pre_equal_prepare_like2main_auth_data_implies :
    forall p pl,
      pre_prepare_data2auth_data_pre p = prepare_like2main_auth_data pl
      -> pl = prepare_like_pre_prepare p.
  Proof.
    introv h.
    destruct p, pl as [x|x], x; simpl in *; ginv; auto.
  Qed.

  Lemma check_new_request_preserves_sequence_number :
    forall i l st r st' o,
      check_new_request i l st r = (st', o)
      -> sequence_number st' = sequence_number st.
  Proof.
    introv check.
    unfold check_new_request in check; smash_pbft.
  Qed.
  Hint Resolve check_new_request_preserves_sequence_number : pbft.

  Lemma pre_prepare2request_data_request_data2pre_prepare :
    forall rd reqs a d,
      d = request_data2digest rd
      -> pre_prepare2request_data (request_data2pre_prepare rd reqs a) d = rd.
  Proof.
    introv h; subst; destruct rd; simpl; auto.
  Qed.

  Lemma request_data2digest_pre_prepare2request_data :
    forall p d, request_data2digest (pre_prepare2request_data p d) = d.
  Proof.
    introv; destruct p, b; simpl; auto.
  Qed.
  Hint Rewrite request_data2digest_pre_prepare2request_data : pbft.

  Lemma pre_prepare2auth_request_data2pre_prepare :
    forall rd reqs a,
      pre_prepare2auth (request_data2pre_prepare rd reqs a) = a.
  Proof.
    introv; destruct rd; simpl; auto.
  Qed.
  Hint Rewrite pre_prepare2auth_request_data2pre_prepare : pbft.

  Lemma pre_prepare2seq_request_data2pre_prepare :
    forall rd reqs a,
      pre_prepare2seq (request_data2pre_prepare rd reqs a) = request_data2seq rd.
  Proof.
    introv; destruct rd; simpl; auto.
  Qed.
  Hint Rewrite pre_prepare2seq_request_data2pre_prepare : pbft.

  Lemma pre_prepare2requests_request_data2pre_prepare :
    forall rd reqs a,
      pre_prepare2requests (request_data2pre_prepare rd reqs a) = reqs.
  Proof.
    introv; destruct rd; simpl; auto.
  Qed.
  Hint Rewrite pre_prepare2requests_request_data2pre_prepare : pbft.

  Lemma implies_same_pre_prepare_in_add_new_pre_prepare2log :
    forall p d L,
      (forall p' d',
          pre_prepare_in_log p' d' L = true
          -> pre_prepare2request_data p d <> pre_prepare2request_data p' d')
      -> pre_prepare_in_log p d (add_new_pre_prepare2log p d L) = true.
  Proof.
    induction L; introv imp; simpl in *; tcsp; repeat smash_pbft; GC;
      [| | |].

    - clear imp.
      destruct p, b; simpl.
      rewrite matching_requests_true_iff; allrw map_map; simpl.
      rewrite map_id; smash_pbft.

    - clear IHL.
      destruct a; simpl in *.
      unfold eq_request_data in *; smash_pbft.
      destruct log_entry_pre_prepare_info; simpl in *; tcsp; GC.

      pose proof (imp (request_data2pre_prepare
                         (pre_prepare2request_data p d)
                         (map fst reqs)
                         auth) d) as q.
      clear imp.
      rewrite pre_prepare2request_data_request_data2pre_prepare in q;
        autorewrite with pbft in *; auto;[].
      smash_pbft; allrw matching_requests_true_iff; autodimp q hyp; tcsp.

    - clear imp IHL.
      destruct p, b; simpl.
      rewrite matching_requests_true_iff; allrw map_map; simpl.
      rewrite map_id; smash_pbft.

    - apply IHL; introv h; clear IHL.

      destruct a; simpl in *.
      unfold eq_request_data in *; smash_pbft.
      destruct log_entry_pre_prepare_info; simpl in *; tcsp;
        [|pose proof (imp p' d') as q; clear imp; smash_pbft].

      intro xx.
      rewrite xx in *.
      pose proof (imp p' d') as q; clear imp; smash_pbft.
      autodimp q hyp; tcsp.
  Qed.

  Lemma in_add_prepare_to_log_from_new_view_pre_prepare_implies :
    forall x i s1 a s2 msgs,
      add_prepare_to_log_from_new_view_pre_prepare i s1 a = (s2, msgs)
      -> In x msgs
      -> (exists p dst, x = send_prepare p dst)
         \/ (exists c dst, x = send_commit c dst)
         \/ x = send_check_ready i.
  Proof.
    introv add j; unfold add_prepare_to_log_from_new_view_pre_prepare in add; smash_pbft.
    allrw in_app_iff; repndors.
    - apply in_check_broadcast_prepare_implies in j; exrepnd; subst.
      left; eexists; eexists; eauto.
    - apply in_check_broadcast_commit_implies in j; exrepnd; subst.
      right; left; eexists; eexists; eauto.
    - eapply message_in_check_send_replies_implies in j;[|eauto]; subst.
      right; right; eexists; eexists; eauto.
  Qed.

  Lemma in_add_prepares_to_log_from_new_view_pre_prepares_implies :
    forall x i L s1 s2 msgs,
      add_prepares_to_log_from_new_view_pre_prepares i s1 L = (s2, msgs)
      -> In x msgs
      -> (exists p dst, x = send_prepare p dst)
         \/ (exists c dst, x = send_commit c dst)
         \/ x = send_check_ready i.
  Proof.
    induction L; introv add j; simpl in *; pbft_simplifier; simpl in *; tcsp.
    smash_pbft;[].
    allrw in_app_iff;repndors;[|eapply IHL;eauto];[].
    eapply in_add_prepare_to_log_from_new_view_pre_prepare_implies; eauto.
  Qed.

  Definition digest_matches_pre_prepare (d : PBFTdigest) (p : Pre_prepare) : bool :=
    same_digests d (pre_prepare2digest p).

  Lemma send_pre_prepare_in_trim_outputs_with_low_water_mark :
    forall p dst msgs st,
      In (send_pre_prepare p dst) (trim_outputs_with_low_water_mark msgs st)
      -> In (send_pre_prepare p dst) msgs.
  Proof.
    introv i.
    unfold trim_outputs_with_low_water_mark in i.
    apply filter_In in i; repnd.
    unfold trim_output_with_low_water_mark in i; simpl in i; smash_pbft.
  Qed.
  Hint Resolve send_pre_prepare_in_trim_outputs_with_low_water_mark : pbft.

  Lemma prepare_like2main_auth_data_not_in_pre_prepare2auth_data_req :
    forall pl pp,
      ~ In (prepare_like2main_auth_data pl) (pre_prepare2auth_data_req pp).
  Proof.
    introv i; destruct pl as [p|p], pp, b, p, b; simpl in *;
      unfold pre_prepare2auth_data_req in *; simpl in *;
        allrw in_map_iff; exrepnd; destruct x, b; simpl in *; ginv.
  Qed.

  Lemma prepare_like2main_auth_data_in_view_change2auth_data_implies :
    forall vc pl,
      In (prepare_like2main_auth_data pl) (view_change2auth_data vc)
      ->
      exists pi,
        In pi (view_change2prep vc)
        /\ prepare_like_in_prepared_info pl pi.
  Proof.
    introv i.
    destruct vc, v; simpl in *.
    repndors;[destruct pl as [p|p]; destruct p, b; simpl in *; ginv|];[].
    allrw in_app_iff.
    repndors.

    - induction C; simpl in *; tcsp;[].
      repndors; tcsp;[].
      destruct a0, pl as [p|p], p; simpl in *; ginv.

    - unfold view_change2prep; simpl.
      induction P; simpl in *; tcsp;[].
      repndors; tcsp;[|].

      + clear IHP.
        destruct a0; simpl in *.
        eexists; dands;[eauto|].
        destruct pl as [p|p], p, b; simpl in *;
          destruct prepared_info_pre_prepare; simpl in *; ginv; auto.

      + allrw in_app_iff; repndors; tcsp;[| |].

        * apply prepare_like2main_auth_data_not_in_pre_prepare2auth_data_req in i; tcsp.

        * clear IHP.
          destruct a0; simpl in *.
          eexists; dands;[eauto|].
          destruct pl as [p|p]; simpl in *;[|].

          { destruct p; simpl in *.
            induction prepared_info_prepares; simpl in *; tcsp.
            repndors; tcsp.
            destruct a1; simpl in *; ginv. }

          { destruct p; simpl in *.
            induction prepared_info_prepares; simpl in *; tcsp.
            repndors; tcsp.
            destruct a1; simpl in *; ginv; auto. }

        * autodimp IHP hyp; exrepnd.
          eexists; dands; eauto.
  Qed.

  Lemma entry2prepared_info_implies_in_entry2prepares_like :
    forall a pl pi,
      entry2prepared_info a = Some pi
      -> prepare_like_in_prepared_info pl pi
      -> In pl (entry2prepares_like a).
  Proof.
    introv h prep.
    destruct a; simpl in *.
    smash_pbft.
    destruct log_entry_pre_prepare_info; simpl in *; ginv.
    destruct log_entry_request_data; simpl.
    destruct pl as [p|p]; simpl in *; subst; tcsp.
    allrw in_map_iff; exrepnd; subst; simpl in *; tcsp.
    destruct x; simpl in *.
    right.
    eexists; dands; eauto.
    unfold entry2prepares; simpl.
    allrw in_map_iff; simpl.
    eexists; dands; eauto.
    simpl; auto.
  Qed.
  Hint Resolve entry2prepared_info_implies_in_entry2prepares_like : pbft.

  Lemma in_gather_prepared_messages_implies_prepare_like_in_log :
    forall pi pl L m,
      In pi (gather_prepared_messages L m)
      -> prepare_like_in_prepared_info pl pi
      -> prepare_like_in_log pl L.
  Proof.
    induction L; introv j prep; simpl in *; tcsp; smash_pbft;[].
    repndors; subst; tcsp; eauto 3 with pbft.
  Qed.
  Hint Resolve in_gather_prepared_messages_implies_prepare_like_in_log : pbft.

  Lemma in_gather_valid_prepared_messages_implies_prepare_like_in_log :
    forall pi pl L m,
      In pi (gather_valid_prepared_messages L m)
      -> prepare_like_in_prepared_info pl pi
      -> prepare_like_in_log pl L.
  Proof.
    introv j prep.
    unfold gather_valid_prepared_messages in j.
    apply filter_In in j; repnd; eauto 3 with pbft.
  Qed.
  Hint Resolve in_gather_valid_prepared_messages_implies_prepare_like_in_log : pbft.

  Lemma send_view_change_in_trim_outputs_with_low_water_mark :
    forall p dst msgs st,
      In (send_view_change p dst) (trim_outputs_with_low_water_mark msgs st)
      -> In (send_view_change p dst) msgs.
  Proof.
    introv i.
    unfold trim_outputs_with_low_water_mark in i.
    apply filter_In in i; repnd.
    unfold trim_output_with_low_water_mark in i; simpl in i; smash_pbft.
  Qed.
  Hint Resolve send_view_change_in_trim_outputs_with_low_water_mark : pbft.

  Lemma prepare_like2main_auth_data_in_new_view2auth_data_implies :
    forall nv pl,
      In (prepare_like2main_auth_data pl) (new_view2auth_data nv)
      ->
      (exists vc pi,
          In vc (new_view2cert nv)
          /\ In pi (view_change2prep vc)
          /\ prepare_like_in_prepared_info pl pi)
      \/ (exists p,
             In p (new_view2oprep nv)
             /\ pl = prepare_like_pre_prepare p)
      \/ (exists p,
             In p (new_view2nprep nv)
             /\ pl = prepare_like_pre_prepare p).
  Proof.
    introv i.
    destruct nv, v; simpl in *.
    repndors;[destruct pl as [p|p]; destruct p, b; simpl in *; ginv|];[].
    allrw in_app_iff.
    repndors;[| |].

    - left.
      induction V; simpl in *; tcsp.
      allrw in_app_iff; repndors; tcsp;[|].

      + clear IHV.
        apply prepare_like2main_auth_data_in_view_change2auth_data_implies in i.
        exrepnd.
        eexists; eexists; dands; eauto.

      + autodimp IHV hyp; exrepnd.
        eexists; eexists; dands; eauto.

    - right; left.
      induction OP; simpl in *; tcsp;[].
      repndors; tcsp;[|].

      + clear IHOP.
        destruct a0, pl as [p|p], p; simpl in *; ginv.
        eexists; dands; eauto.

      + allrw in_app_iff; repndors;
          try (complete (apply prepare_like2main_auth_data_not_in_pre_prepare2auth_data_req in i; tcsp));[].
        autodimp IHOP hyp; exrepnd.
        eexists; eexists; dands; eauto.

    - right; right.
      induction NP; simpl in *; tcsp;[].
      repndors; tcsp.

      + clear IHNP.
        destruct a0, pl as [p|p], p; simpl in *; ginv.
        eexists; dands; eauto.

      + allrw in_app_iff; repndors;
          try (complete (apply prepare_like2main_auth_data_not_in_pre_prepare2auth_data_req in i; tcsp));[].
        autodimp IHNP hyp; exrepnd.
        eexists; eexists; dands; eauto.
  Qed.

  Lemma implies_prepare_like_in_log_prepare_like_prepare :
    forall p L,
      well_formed_log L
      -> prepare_in_log p L = true
      -> prepare_like_in_log (prepare_like_prepare p) L.
  Proof.
    induction L; introv wf prep; simpl in *; tcsp; smash_pbft;
      try (inversion wf as [|? ? imp wf1 wf2]; clear wf; subst); tcsp;[].

    left.
    clear IHL.
    unfold is_prepare_for_entry, eq_request_data in *; smash_pbft.
    allrw existsb_exists; exrepnd.
    unfold same_rep_tok in *; smash_pbft.
    destruct p, b, a, log_entry_request_data, log_entry_pre_prepare_info;
      simpl in *; ginv; simpl in *.

    - right.
      unfold entry2prepares; simpl.
      allrw map_map.
      apply in_map_iff; simpl.
      eexists; dands; eauto.
      simpl; auto.

    - unfold entry2prepares_like; simpl.
      unfold entry2prepares; simpl.
      allrw map_map; simpl.
      apply in_map_iff.
      eexists; dands; eauto.
      simpl; auto.
  Qed.
  Hint Resolve implies_prepare_like_in_log_prepare_like_prepare : pbft.

  Lemma implies_prepare_like_in_log_prepare_like_pre_prepare :
    forall p d L,
      well_formed_log L
      -> pre_prepare_in_log p d L = true
      -> prepare_like_in_log (prepare_like_pre_prepare p) L.
  Proof.
    induction L; introv wf prep; simpl in *; tcsp; smash_pbft;
      try (inversion wf as [|? ? imp wf1 wf2]; clear wf; subst); tcsp;[].

    left.
    clear IHL.
    destruct a; simpl in *.
    unfold eq_request_data in *; smash_pbft;[].
    allrw auth_matches_logEntryPrePrepareInfo_true_iff; exrepnd; subst.
    allrw requests_matches_logEntryPrePrepareInfo_true_iff; repnd.
    simpl in *; GC.
    destruct p, b; simpl in *; subst; tcsp.
  Qed.
  Hint Resolve implies_prepare_like_in_log_prepare_like_pre_prepare : pbft.

  Lemma implies_view_change_in_log_new_view :
    forall vc nv S,
      view_change_in_log vc S
      -> view_change_in_log vc (log_new_view S nv).
  Proof.
    induction S; introv i; simpl in *; tcsp; smash_pbft.
  Qed.
  Hint Resolve implies_view_change_in_log_new_view : pbft.

  Fixpoint view_change_somewhere_in_log
           (vc : ViewChange)
           (S  : PBFTviewChangeState) : Prop :=
    match S with
    | [] => False
    | entry :: entries =>
      In vc (view_change_entry2view_changes entry)
      \/ view_change_somewhere_in_log vc entries
    end.

  Lemma implies_in_view_change_entry2view_changes_add_new_view_to_entry :
    forall vc e nv,
      In vc (view_change_entry2view_changes e)
      -> In vc (view_change_entry2view_changes (add_new_view_to_entry e nv)).
  Proof.
    destruct e; unfold view_change_entry2view_changes; introv h; simpl in *.
    destruct vce_new_view; simpl in *; tcsp.
  Qed.
  Hint Resolve implies_in_view_change_entry2view_changes_add_new_view_to_entry : pbft.

  Lemma implies_view_change_somewhere_in_log_new_view :
    forall vc nv S,
      view_change_somewhere_in_log vc S
      -> view_change_somewhere_in_log vc (log_new_view S nv).
  Proof.
    induction S; introv i; simpl in *; tcsp; smash_pbft;
      repndors; smash_pbft.
  Qed.
  Hint Resolve implies_view_change_somewhere_in_log_new_view : pbft.

  Lemma implies_view_change_somewhere_in_log :
    forall S e vc,
      In e S
      -> In vc (view_change_entry2view_changes e)
      -> view_change_somewhere_in_log vc S.
  Proof.
    induction S; introv i j; simpl in *; tcsp.
    repndors; subst; tcsp; smash_pbft.
  Qed.
  Hint Resolve implies_view_change_somewhere_in_log : pbft.

  Lemma view_change2prep_refresh_view_change :
    forall vc s,
      view_change2prep (refresh_view_change vc s)
      = gather_valid_prepared_messages (log s) (low_water_mark s).
  Proof.
    tcsp.
  Qed.

  Definition prepare_like2seq (p : Prepare_like) : SeqNum :=
    match p with
    | prepare_like_pre_prepare pp => pre_prepare2seq pp
    | prepare_like_prepare p => prepare2seq p
    end.

  Lemma prepare2seq_request_data_and_rep_toks2prepare :
    forall rd rt,
      prepare2seq (request_data_and_rep_toks2prepare rd rt)
      = request_data2seq rd.
  Proof.
    introv; destruct rd, rt; simpl; auto.
  Qed.
  Hint Rewrite prepare2seq_request_data_and_rep_toks2prepare : pbft.

  Lemma prepare_like2seq_equal_if_wf :
    forall a pl pi,
      well_formed_log_entry a
      -> prepare_like_in_prepared_info pl pi
      -> entry2prepared_info a = Some pi
      -> prepare_like2seq pl = entry2seq a.
  Proof.
    introv wf prep i.
    destruct a; simpl in *; smash_pbft;[].
    destruct log_entry_pre_prepare_info; simpl in *; ginv;[].
    destruct pl; simpl in *; subst; autorewrite with pbft; auto;[].
    allrw in_map_iff; exrepnd; subst.
    autorewrite with pbft in *; auto.
  Qed.
  Hint Resolve prepare_like2seq_equal_if_wf : pbft.

  Lemma in_gather_prepared_messages_implies_prepare_like_in_log2 :
    forall pi pl L m,
      well_formed_log L
      -> In pi (gather_prepared_messages L m)
      -> prepare_like_in_prepared_info pl pi
      -> prepare_like_in_log pl L /\ m < prepare_like2seq pl.
  Proof.
    induction L; introv wf j prep; simpl in *; tcsp; smash_pbft;
      repndors; subst; tcsp; eauto 3 with pbft;[| | |];
        inversion wf as [|? ? imp wf1 wf2]; subst; clear wf;
          dands; eauto 3 with pbft;
            try (complete (apply IHL; auto)).
    eapply prepare_like2seq_equal_if_wf in prep; eauto; try rewrite prep; auto.
  Qed.
  Hint Resolve in_gather_prepared_messages_implies_prepare_like_in_log2 : pbft.

  Lemma in_gather_valid_prepared_messages_implies_prepare_like_in_log2 :
    forall pi pl L m,
      well_formed_log L
      -> In pi (gather_valid_prepared_messages L m)
      -> prepare_like_in_prepared_info pl pi
      -> prepare_like_in_log pl L /\ m < prepare_like2seq pl.
  Proof.
    introv wf j prep.
    unfold gather_valid_prepared_messages in j.
    apply filter_In in j; repnd; eauto 3 with pbft.
  Qed.
  Hint Resolve in_gather_valid_prepared_messages_implies_prepare_like_in_log2 : pbft.

  Lemma view_change_entry2view_changes_add_new_view_to_entry :
    forall e nv,
      view_change_entry2view_changes (add_new_view_to_entry e nv)
      = view_change_entry2view_changes e.
  Proof.
    destruct e, vce_new_view; introv; simpl; tcsp.
  Qed.
  Hint Rewrite view_change_entry2view_changes_add_new_view_to_entry : pbft.

  Lemma implies_view_change_somewhere_in_log_log_new_view_and_entry :
    forall s nv vc e,
      In vc (view_change_entry2view_changes e)
      -> view_change_somewhere_in_log vc (log_new_view_and_entry s nv e).
  Proof.
    induction s; introv i; simpl in *; autorewrite with pbft in *; smash_pbft.
  Qed.
  Hint Resolve implies_view_change_somewhere_in_log_log_new_view_and_entry : pbft.

  Lemma update_state_new_view_preserves_log :
    forall i s1 nv s2 msgs maxV,
      view_change_cert2max_seq (new_view2cert nv) = Some maxV
      -> update_state_new_view i s1 nv = (s2, msgs)
      -> if low_water_mark s1 <? maxV
         then log s2 = clear_log_checkpoint (log s1) maxV
         else log s2 = log s1.
  Proof.
    introv h upd.
    unfold update_state_new_view in upd; smash_pbft; try omega;
      rename_hyp_with view_change_cert2max_seq_vc mseq;
      unfold view_change_cert2max_seq in *;
      rewrite mseq in *; ginv; try omega;[].

    rename_hyp_with log_checkpoint_cert_from_new_view lcert.
    apply log_checkpoint_cert_from_new_view_preserves_log in lcert.
    allrw; auto.
  Qed.

  Lemma equal_views_implies_equal_nats :
    forall (v1 v2 : View), v1 = v2 -> view2nat v1 = view2nat v2.
  Proof.
    introv h; destruct v1, v2; simpl in *; auto.
    inversion h; subst; auto.
  Qed.

  Lemma implies_has_new_view_false :
    forall s e,
      wf_view_change_state (view_change_state s)
      -> In e (view_change_state s)
      -> initial_view < vce_view e
      -> vce_new_view e = None
      -> has_new_view (view_change_state s) (vce_view e) = false.
  Proof.
    introv wf i ltv nnv.
    unfold has_new_view; smash_pbft;
      try match goal with
          | [ H : @eq View _ _ |- _ ] =>
            apply equal_views_implies_equal_nats in H; simpl in *; try omega
          end.
    unfold has_new_view1.
    rewrite existsb_false.
    introv j; smash_pbft.
    eapply wf_view_change_state_implies_same_entries_if_same_views in i;
      try exact j; auto; subst; pbft_simplifier.
  Qed.
  Hint Resolve implies_has_new_view_false : pbft.

  Lemma log_pre_prepares_preserves_pre_prepare_in_log_true :
    forall P pp d L m,
      pre_prepare_in_log pp d L = true
      -> pre_prepare_in_log pp d (log_pre_prepares L m P) = true.
  Proof.
    introv h.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    apply PBFTpre_prepare_in_log_preserves.pre_prepare_in_log_log_pre_prepares_false in Heqb.
    rewrite h in Heqb; ginv.
  Qed.
  Hint Resolve log_pre_prepares_preserves_pre_prepare_in_log_true : pbft.

  Lemma implies_pre_prepare_in_log_log_pre_prepares :
    forall P pp d L (m : SeqNum),
      no_repeats (map (fun p => pre_prepare2seq (fst p)) P)
      -> (forall pp' d',
             pre_prepare_in_log pp' d' L = true
             -> pre_prepare2seq pp' = pre_prepare2seq pp
             -> pre_prepare2view pp' <> pre_prepare2view pp)
      -> In (pp,d) P
      -> m < pre_prepare2seq pp
      -> pre_prepare_in_log pp d (log_pre_prepares L m P) = true.
  Proof.
    induction P; introv norep imp i h; simpl in *; tcsp;[].
    repnd; repndors; ginv; smash_pbft; try omega;[| |].

    - apply log_pre_prepares_preserves_pre_prepare_in_log_true.
      apply implies_same_pre_prepare_in_add_new_pre_prepare2log.
      introv w z.
      apply imp in w; destruct pp, p', b, b0; simpl in *; ginv.

    - inversion norep as [|? ? ni nrep]; clear norep; subst.
      apply IHP; auto.
      introv w z.
      apply pre_prepare_in_log_add_new_prepare2log in w.
      repndors;[|].

      + apply imp in w; tcsp.

      + repnd; subst.
        destruct ni.
        apply in_map_iff.
        eexists; dands; eauto; simpl; auto.

    - inversion norep as [|? ? ni nrep]; clear norep; subst.
      apply IHP; auto.
  Qed.

  Lemma clear_log_checkpoint_preserves_pre_prepare_in_log_true :
    forall (n : SeqNum) pp d L,
      n < pre_prepare2seq pp
      -> pre_prepare_in_log pp d L = true
      -> pre_prepare_in_log pp d (clear_log_checkpoint L n) = true.
  Proof.
    introv h w.
    match goal with
    | [ |- ?x = _ ] => remember x as b; symmetry in Heqb; destruct b; auto
    end.
    apply pre_prepare_in_log_clear_log_checkpoint_false_implies in Heqb; auto; pbft_simplifier.
  Qed.

  Lemma send_new_view_in_trim_outputs_with_low_water_mark :
    forall p dst msgs st,
      In (send_new_view p dst) (trim_outputs_with_low_water_mark msgs st)
      -> In (send_new_view p dst) msgs.
  Proof.
    introv i.
    unfold trim_outputs_with_low_water_mark in i.
    apply filter_In in i; repnd.
    unfold trim_output_with_low_water_mark in i; simpl in i; smash_pbft.
  Qed.
  Hint Resolve send_new_view_in_trim_outputs_with_low_water_mark : pbft.

  Lemma view_change_somewhere_in_log_new_view_iff :
    forall vc S nv,
      view_change_somewhere_in_log vc (log_new_view S nv)
      <-> view_change_somewhere_in_log vc S.
  Proof.
    induction S; introv; simpl; split; introv h; tcsp; smash_pbft; repndors; tcsp.

    - apply IHS in h; tcsp.

    - rewrite IHS; tcsp.
  Qed.
  Hint Rewrite view_change_somewhere_in_log_new_view_iff : pbft.

  Lemma view_change_somewhere_in_log_log_new_view_and_entry_implies :
    forall vc s nv e,
      view_change_somewhere_in_log vc (log_new_view_and_entry s nv e)
      -> view_change_somewhere_in_log vc s
         \/ In vc (view_change_entry2view_changes e).
  Proof.
    induction s; introv i; simpl in *; tcsp; repeat (repndors; smash_pbft).
    apply IHs in i; tcsp.
  Qed.

  Lemma in_vce_view_changes_implies_in_view_change_somewhere_in_log :
    forall vc e s,
      In e s
      -> In vc (vce_view_changes e)
      -> view_change_somewhere_in_log vc s.
  Proof.
    induction s; introv i j; simpl in *; tcsp.
    repndors; subst; tcsp.
    left; clear IHs.
    destruct e, vce_view_change; simpl in *; tcsp.
  Qed.
  Hint Resolve in_vce_view_changes_implies_in_view_change_somewhere_in_log : pbft.

  Lemma start_view_change_preserves_view_change_somewhere_in_log :
    forall vc s1 e n s2 x,
      start_view_change vc s1 = (e, n, s2)
      -> view_change_somewhere_in_log x s2
      -> view_change_somewhere_in_log x s1 \/ x = vc.
  Proof.
    introv start vcinlog.
    unfold start_view_change in start.
    revert e n s2 start vcinlog.

    induction s1; introv add vcinlog; repeat (simpl in *; repndors; smash_pbft).

    - destruct a, vce_view_change; simpl in *; repndors; subst; tcsp.

    - pose proof (IHs1 e x4 x2) as q; clear IHs1; repeat (autodimp q hyp); tcsp.
  Qed.

  Lemma view_change2prep_mk_current_view_change :
    forall i v s,
      view_change2prep (mk_current_view_change i v s)
      = gather_valid_prepared_messages (log s) (low_water_mark s).
  Proof.
    tcsp.
  Qed.

  Lemma add_other_view_change_preserves_view_change_somewhere_in_log :
    forall x s1 e n s2 vc,
      add_other_view_change x s1 = Some (e, n, s2)
      -> view_change_somewhere_in_log vc s2
      -> view_change_somewhere_in_log vc s1 \/ x = vc.
  Proof.
    induction s1; introv add vcinlog; repeat (simpl in *; repndors; smash_pbft).

    - destruct a; simpl in *; smash_pbft; repndors; subst; tcsp;
        rename_hyp_with add_view_change2view_changes add;
        eapply add_view_change2view_changes_preserves_in in add; eauto; tcsp.

    - pose proof (IHs1 e n x3 vc) as q; clear IHs1; repeat (autodimp q hyp); tcsp.
  Qed.
  Hint Resolve add_other_view_change_preserves_view_change_somewhere_in_log : pbft.

  Lemma implies_prepare_like2main_auth_data_in_prepared_info2auth_data :
    forall pi pl P,
      In pi P
      -> prepare_like_in_prepared_info pl pi
      -> In (prepare_like2main_auth_data pl) (prepared_infos2auth_data P).
  Proof.
    induction P; introv i prep; simpl in *; tcsp; repndors; subst; tcsp;
      allrw in_app_iff; tcsp;[].

    clear IHP.
    destruct pl; simpl in *; subst; tcsp;[].
    right; left.
    destruct pi; simpl in *.
    induction prepared_info_prepares; simpl in *; tcsp; repndors; subst; tcsp.
  Qed.
  Hint Resolve implies_prepare_like2main_auth_data_in_prepared_info2auth_data : pbft.

  Lemma in_view_change2prep_implies_prepare_like2main_auth_data_in_view_change2auth_data :
    forall pi pl vc,
      In pi (view_change2prep vc)
      -> prepare_like_in_prepared_info pl pi
      -> In (prepare_like2main_auth_data pl) (view_change2auth_data vc).
  Proof.
    introv h q.
    destruct vc, v; simpl in *.
    unfold view_change2prep in *; simpl in *.
    allrw in_app_iff.
    right; eauto 3 with pbft.
  Qed.
  Hint Resolve in_view_change2prep_implies_prepare_like2main_auth_data_in_view_change2auth_data : pbft.

  Lemma verify_view_change_implies_verify_prepare_like :
    forall pi pl vc i keys,
      In pi (view_change2prep vc)
      -> prepare_like_in_prepared_info pl pi
      -> verify_view_change i keys vc = true
      -> verify_prepare_like i keys pl = true.
  Proof.
    introv k prep verif.
    destruct vc, v; simpl in *.
    unfold view_change2prep in *; simpl in *.
    unfold verify_view_change in verif; simpl in *; smash_pbft.
    clear verif.
    rewrite verify_list_auth_data_app in *; smash_pbft.
    clear verif0.
    induction P; simpl in *; repndors; subst; tcsp; smash_pbft;
      rewrite verify_list_auth_data_app in *; smash_pbft;[].

    rewrite verify_list_auth_data_app in *; smash_pbft.

    destruct pl; simpl in *; subst; simpl in *; tcsp;
      try (complete (unfold verify_pre_prepare; simpl; smash_pbft));[].

    destruct pi; simpl in *.
    clear IHP verif1 verif2.
    induction prepared_info_prepares; simpl in *; tcsp; repndors; subst; tcsp; smash_pbft.
  Qed.
  Hint Resolve verify_view_change_implies_verify_prepare_like : pbft.

  Lemma non_first_if_prepare_like_in_log :
    forall (eo : EventOrdering) (e : Event) i st pl,
      state_sm_before_event (PBFTreplicaSM i) e = Some st
      -> prepare_like_in_log pl (log st)
      -> ~ isFirst e.
  Proof.
    introv eqst prep.
    pose proof (ite_first_state_sm_on_event_as_before (PBFTreplicaSM i) e) as q.
    rewrite eqst in q.
    unfold ite_first in q.
    destruct (dec_isFirst e) as [d|d]; ginv.
  Qed.
  Hint Resolve non_first_if_prepare_like_in_log : pbft.

  Lemma PBFTdata_auth_prepare_like2auth_data_some_implies :
    forall i pl,
      PBFTdata_auth (PBFTreplica i) (prepare_like2main_auth_data pl)
      = Some (PBFTreplica (prepare_like2sender pl)).
  Proof.
    introv.
    destruct pl as [p|p], p; simpl in *; auto.
  Qed.
  Hint Resolve PBFTdata_auth_prepare_like2auth_data_some_implies : pbft.
  Hint Rewrite PBFTdata_auth_prepare_like2auth_data_some_implies : pbft.

  Definition verify_main_prepare_like i km (p : Prepare_like) : bool :=
    verify_one_auth_data (PBFTreplica i) km (prepare_like2main_auth_data p).

  Lemma verify_prepare_like_implies_verify_main_prepare_like :
    forall i km p,
      verify_prepare_like i km p = true
      -> verify_main_prepare_like i km p = true.
  Proof.
    introv verif.
    unfold verify_prepare_like, verify_pre_prepare, verify_prepare, verify_main_prepare_like in *.
    destruct p; simpl in *; smash_pbft.
  Qed.
  Hint Resolve verify_prepare_like_implies_verify_main_prepare_like : pbft.

  Lemma verify_view_change_implies_verify_main_prepare_like :
    forall pi pl vc i keys,
      In pi (view_change2prep vc)
      -> prepare_like_in_prepared_info pl pi
      -> verify_view_change i keys vc = true
      -> verify_main_prepare_like i keys pl = true.
  Proof.
    eauto 3 with pbft.
  Qed.
  Hint Resolve verify_view_change_implies_verify_main_prepare_like : pbft.

  Lemma check_one_stable_preserves_prepare_like_in_log :
    forall p i s l,
      prepare_like_in_log p (log (check_one_stable i s l))
      -> prepare_like_in_log p (log s).
  Proof.
    induction l; introv prep; simpl in *; smash_pbft.
  Qed.
  Hint Resolve check_one_stable_preserves_prepare_like_in_log : pbft.

  Lemma verify_authenticated_data_iff_verify_main_prepare_like :
    forall i pl keys,
      verify_authenticated_data (PBFTreplica i) (prepare_like2main_auth_data pl) keys = true
      <-> verify_main_prepare_like i keys pl = true.
  Proof.
    introv; unfold verify_main_prepare_like, verify_one_auth_data; simpl; tcsp.
  Qed.

  Lemma send_message_in_trim_outputs_with_low_water_mark :
  forall m msgs st,
    In m (trim_outputs_with_low_water_mark msgs st)
    -> In m msgs.
  Proof.
    introv i; unfold trim_outputs_with_low_water_mark in i.
    apply filter_In in i; tcsp.
  Qed.

  Lemma trigger_implies_auth_data_in_trigger_pre_prepare_data2auth_data_pre :
    forall (eo : EventOrdering) (e : Event) p,
      trigger e = Some (PBFTpre_prepare p)
      -> auth_data_in_trigger (pre_prepare_data2auth_data_pre p) e.
  Proof.
    introv trig.
    unfold auth_data_in_trigger; allrw; simpl; tcsp.
  Qed.
  Hint Resolve trigger_implies_auth_data_in_trigger_pre_prepare_data2auth_data_pre : pbft.

End PBFTreceived_prepare_like1.


Hint Rewrite @map_prepare_like2sender_prepare_like_prepare_request_data_and_rep_toks2prepare : pbft.
Hint Rewrite @prepare_like_in_log_log_update_log : pbft.
Hint Rewrite @entry2prepares_like_pre_prepare2entry : pbft.
Hint Rewrite @prepare2request_data_request_data_and_rep_toks2prepare : pbft.
Hint Rewrite @prepare_like2sender_prepare_like_pre_prepare : pbft.
Hint Rewrite @prepare_like2sender_prepare_like_prepare : pbft.
Hint Rewrite @prepare2sender_pre_prepare2prepare : pbft.
Hint Rewrite @map_fst_combine_replies : pbft.
Hint Rewrite @entry2prepares_like_add_replies2entry : pbft.
Hint Rewrite @bare_prepare2sender_pre_prepare2bare_prepare : pbft.
Hint Rewrite @prepare2rep_toks_request_data_and_rep_toks2prepare : pbft.
Hint Rewrite @request_data2digest_pre_prepare2request_data : pbft.
Hint Rewrite @pre_prepare2auth_request_data2pre_prepare : pbft.
Hint Rewrite @pre_prepare2seq_request_data2pre_prepare : pbft.
Hint Rewrite @pre_prepare2requests_request_data2pre_prepare : pbft.
Hint Rewrite @prepare2seq_request_data_and_rep_toks2prepare : pbft.
Hint Rewrite @view_change_entry2view_changes_add_new_view_to_entry : pbft.
Hint Rewrite @view_change_somewhere_in_log_new_view_iff : pbft.
Hint Rewrite @PBFTdata_auth_prepare_like2auth_data_some_implies : pbft.


Hint Rewrite @map_id : list.


Hint Resolve check_send_replies_preserves_prepare_like_in_log : pbft.
Hint Resolve implies_prepare_like_in_log_log_update_log : pbft.
Hint Resolve add_new_commit2log_preserves_prepare_like_in_log : pbft.
Hint Resolve clear_log_checkpoint_preserves_prepare_like_in_log : pbft.
Hint Resolve check_stable_preserves_prepare_like_in_log : pbft.
Hint Resolve change_entry_add_replies2entry_preserves_prepare_like_in_log : pbft.
Hint Resolve find_and_execute_requests_preserves_prepare_like_in_log : pbft.
Hint Resolve update_state_new_view_preserves_prepare_like_in_log : pbft.
Hint Resolve check_send_replies_preserves_pre_prepare_in_log_forward : pbft.
Hint Resolve verify_pre_prepares_implies_verify_pre_prepare : pbft.
Hint Resolve verify_new_view_implies_verify_pre_prepare : pbft.
Hint Resolve pre_prepare2auth_data_in_pre_prepares2auth_data : pbft.
Hint Resolve pre_prepare2auth_data_in_new_view2auth_data : pbft.
Hint Resolve implies_prepare_like_in_log : pbft.
Hint Resolve verify_prepare_like_implies_verify_authenticated_data : pbft.
Hint Resolve add_new_pre_prepare_and_prepare2log_add_prepare_status_added_implies_prepare_in_log : pbft.
Hint Resolve prepare_in_add_prepare_to_log_from_new_view_pre_prepare_is_in_log : pbft.
Hint Resolve prepare_in_add_prepares_to_log_from_new_view_pre_prepares_is_in_log : pbft.
Hint Resolve check_new_request_preserves_sequence_number : pbft.
Hint Resolve entry2prepared_info_implies_in_entry2prepares_like : pbft.
Hint Resolve in_gather_prepared_messages_implies_prepare_like_in_log : pbft.
Hint Resolve in_gather_valid_prepared_messages_implies_prepare_like_in_log : pbft.
Hint Resolve implies_prepare_like_in_log_prepare_like_prepare : pbft.
Hint Resolve implies_prepare_like_in_log_prepare_like_pre_prepare : pbft.
Hint Resolve implies_view_change_in_log_new_view : pbft.
Hint Resolve implies_in_view_change_entry2view_changes_add_new_view_to_entry : pbft.
Hint Resolve implies_view_change_somewhere_in_log_new_view : pbft.
Hint Resolve implies_view_change_somewhere_in_log : pbft.
Hint Resolve prepare_like2seq_equal_if_wf : pbft.
Hint Resolve in_gather_prepared_messages_implies_prepare_like_in_log2 : pbft.
Hint Resolve in_gather_valid_prepared_messages_implies_prepare_like_in_log2 : pbft.
Hint Resolve implies_view_change_somewhere_in_log_log_new_view_and_entry : pbft.
Hint Resolve implies_has_new_view_false : pbft.
Hint Resolve log_pre_prepares_preserves_pre_prepare_in_log_true : pbft.
Hint Resolve in_vce_view_changes_implies_in_view_change_somewhere_in_log : pbft.
Hint Resolve add_other_view_change_preserves_view_change_somewhere_in_log : pbft.
Hint Resolve implies_prepare_like2main_auth_data_in_prepared_info2auth_data : pbft.
Hint Resolve in_view_change2prep_implies_prepare_like2main_auth_data_in_view_change2auth_data : pbft.
Hint Resolve verify_view_change_implies_verify_prepare_like : pbft.
Hint Resolve non_first_if_prepare_like_in_log : pbft.
Hint Resolve update_state_new_view_preserves_prepare_in_log_true_forward : pbft.
Hint Resolve send_pre_prepare_in_trim_outputs_with_low_water_mark : pbft.
Hint Resolve send_view_change_in_trim_outputs_with_low_water_mark : pbft.
Hint Resolve send_new_view_in_trim_outputs_with_low_water_mark : pbft.
Hint Resolve implies_verify_pre_prepare : pbft.
Hint Resolve verify_pre_prepare_implies_verify_authenticated_data_pre_prepare_data2auth_data_pre : pbft.
Hint Resolve pre_prepare_data2auth_data_pre_in_pre_prepares2auth_data : pbft.
Hint Resolve pre_prepare_data2auth_data_pre_in_new_view2auth_data : pbft.
Hint Resolve verify_prepare_like_implies_verify_main_authenticated_data : pbft.
Hint Resolve PBFTdata_auth_prepare_like2auth_data_some_implies : pbft.
Hint Resolve verify_view_change_implies_verify_main_prepare_like : pbft.
Hint Resolve verify_prepare_like_implies_verify_main_prepare_like : pbft.
Hint Resolve check_one_stable_preserves_prepare_like_in_log : pbft.
Hint Resolve message_in_check_send_replies_implies : pbft.
Hint Resolve trigger_implies_auth_data_in_trigger_pre_prepare_data2auth_data_pre : pbft.
