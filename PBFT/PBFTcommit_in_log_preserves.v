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


Require Export PBFTprops2.
Require Export PBFTwell_formed_log.


Section PBFTcommit_in_log_preserves.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.

  Lemma check_send_replies_preserves_commit_in_log :
    forall com slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> commit_in_log com (log state') = true
      -> commit_in_log com (log state) = true.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve check_send_replies_preserves_commit_in_log: pbft.

  Lemma commit_in_log_add_new_pre_prepare2log_log_entry_commits :
    forall com pp d entry L,
      commit_in_log com (add_new_pre_prepare2log pp d L) = commit_in_log com L
      -> similar_entry_and_pre_prepare entry pp d = true
      -> log_entry_commits (change_pre_prepare_info_of_entry pp entry)
         = log_entry_commits entry.
  Proof.
    pbft_brute_force.
  Qed.
  (*Hint Rewrite commit_in_log_add_new_pre_prepare2log_log_entry_commits : pbft.*)

  (* MOVE *)
(*  DO WE NEED THESE??? We have stronger ones below.
  Lemma is_commit_for_entry_true_implies :
    forall entry c,
      is_commit_for_entry entry c = true
      -> log_entry_request_data entry = commit2request_data c.
  Proof.
    introv h.
    unfold is_commit_for_entry, eq_request_data in h.
    dest_cases w.
  Qed.

  Lemma is_commit_for_entry_false_implies :
    forall entry c,
      is_commit_for_entry entry c = false
      -> log_entry_request_data entry <> commit2request_data c.
  Proof.
    introv h.
    unfold is_commit_for_entry, eq_request_data in h.
    dest_cases w.
  Qed.
*)

  Lemma is_commit_for_entry_true_iff :
    forall entry c,
      is_commit_for_entry entry c = true
      <-> log_entry_request_data entry = commit2request_data c.
  Proof.
    introv.
    unfold is_commit_for_entry, eq_request_data;
      destruct entry; simpl in *; pbft_dest_all x; split; tcsp.
  Qed.
  Hint Rewrite is_commit_for_entry_true_iff : pbft.

  Lemma is_commit_for_entry_false_iff :
    forall entry c,
      is_commit_for_entry entry c = false
      <-> log_entry_request_data entry <> commit2request_data c.
  Proof.
    introv.
    unfold is_commit_for_entry, eq_request_data;
      destruct entry; simpl in *; pbft_dest_all x; split; tcsp.
  Qed.
  Hint Rewrite is_commit_for_entry_false_iff : pbft.

  Lemma add_new_pre_prepare2log_preserves_commit_in_log :
    forall com pp s L,
      commit_in_log com (add_new_pre_prepare2log pp s L) =
      commit_in_log com L.
  Proof.
    induction L; simpl in *; smash_pbft.

    {
      pose proof (commit_in_log_add_new_pre_prepare2log_log_entry_commits com pp s a L) as xx.
      apply xx in IHL; [| auto]. clear xx.
      rewrite IHL in *. auto.
    }

(*    {
      allrw is_commit_for_entry_true_iff.
      allrw is_commit_for_entry_false_iff.

      allrw similar_entry_and_pre_prepare_true_iff.

      unfold change_pre_prepare_info_of_entry in *.
      destruct a; simpl in *.
      tcsp.
    }

    {
      allrw is_commit_for_entry_true_iff.
      allrw is_commit_for_entry_false_iff.

      allrw similar_entry_and_pre_prepare_true_iff.

      unfold change_pre_prepare_info_of_entry in *.
      destruct a; simpl in *.
      tcsp.
    }*)
  Qed.
  Hint Rewrite  add_new_pre_prepare2log_preserves_commit_in_log : pbft.

  Lemma decomp_commit :
    forall com,
      request_data_and_rep_toks2commit
        (commit2request_data com)
        (commit2rep_toks com)
      = com.
  Proof.
    destruct com; simpl.
    destruct b; simpl; auto.
  Qed.
  Hint Rewrite decomp_commit : pbft.

  (* MOVE *)
  Lemma rt_rep_commit2rep_toks_as_commit2sender :
    forall com,
      rt_rep (commit2rep_toks com)
      = commit2sender com.
  Proof.
    introv; destruct com, b; simpl; auto.
  Qed.
  Hint Rewrite rt_rep_commit2rep_toks_as_commit2sender: pbft.

  Lemma split_commit :
    forall com,
      com = request_data_and_rep_toks2commit (commit2request_data com) (commit2rep_toks com).
  Proof.
    introv; destruct com, b; simpl; tcsp.
  Qed.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_commit_in_log :
    forall L K pp d Fp Fc giop slf com,
      slf = rt_rep (Fc tt)
      -> add_new_pre_prepare_and_prepare2log slf L pp d Fp Fc = (giop, K)
      -> commit_in_log com K = true
      -> commit_in_log com L = true
         \/
         (
           com = request_data_and_rep_toks2commit (pre_prepare2request_data pp d) (Fc tt)
           /\
           commit_in_log com L = false
           /\
           prepared_log (pre_prepare2request_data pp d) K = true
         ).
  Proof.
    induction L; introv irt h q; repeat (progress (simpl in *; smash_pbft));
      try (complete (unfold is_request_data_for_entry, eq_request_data in *; smash_pbft;
                     allrw similar_entry_and_pre_prepare_true_iff;
                     allrw similar_entry_and_pre_prepare_false_iff;
                     try (rename_hyp_with fill_out_pp_info_with_prepare fill);
                     try (apply fill_out_pp_info_with_prepare_preserves_request_data in fill);
                     congruence)).

    allrw similar_entry_and_pre_prepare_true_iff.
    unfold fill_out_pp_info_with_prepare in *.
    destruct a; simpl in *;[].
    destruct log_entry_pre_prepare_info; ginv; smash_pbft.
    unfold add_commit_if_prepared in *; smash_pbft.

    repndors; tcsp;[].

    match goal with
    | [ |- context[?x = true] ] => remember x as b; destruct b; tcsp; clear Heqb
    end.
    right.

    unfold is_request_data_for_entry in *; simpl in *.
    unfold same_rep_tok in *; smash_pbft.

    rewrite (split_commit com).
    allrw.
    dands; tcsp.
  Qed.
  (*Hint Rewrite add_new_pre_prepare_and_prepare2log_preserves_commit_in_log : pbft.*)

  Lemma add_new_prepare2log_preserves_commit_in_log :
    forall i com new_prep L K gi Fc,
      add_new_prepare2log i L new_prep Fc = (gi, K)
      -> commit_in_log com K = true
      -> commit_in_log com L = true
         \/
         (
           com = request_data_and_rep_toks2commit (prepare2request_data new_prep) (Fc tt)
           /\
           commit_in_log com L = false
           /\
           prepared_log (prepare2request_data new_prep) K = true
         ).
  Proof.
    induction L; introv h q; simpl in *; smash_pbft; tcsp;
      try (simpl in *; smash_pbft);
      try (allrw is_commit_for_entry_false_iff; allrw is_commit_for_entry_true_iff;
           match goal with
           | [ H : add_prepare2entry _ _ _ _ = _, H' : _ <> _ |- _ ] =>
             apply add_prepare2entry_some_implies_log_entry_request_data in H;
             destruct H'; allrw <-; auto
           end).

   {
     hide_hyp IHL.

     allrw is_prepare_for_entry_true_iff.
     unfold is_request_data_for_entry in *.
     unfold eq_request_data in *. smash_pbft.

     unfold add_prepare2entry in *.
     destruct a;[]; simpl in *; ginv; simpl in *; smash_pbft; tcsp.
     unfold add_commit_if_prepared in *.
     smash_pbft.

     allrw same_rep_tok_true_iff.

     repndors; tcsp;[].

     remember (existsb (same_rep_tok (commit2rep_toks com)) log_entry_commits) as b.
     symmetry in Heqb; destruct b; tcsp.
     pose proof (decomp_commit com) as q1. rewrite <- q1. clear q1.
     allrw; dands; auto.
   }

   {
     unfold is_request_data_for_entry in *.
     unfold eq_request_data in *. smash_pbft.
     allrw is_prepare_for_entry_true_iff.

     match goal with
       [H1 :  _ = commit2request_data com , H2 : _ = commit2request_data com |-_ ] =>
       rewrite <- H2 in H1
     end.
     match goal with
       [H1 : log_entry_request_data a = prepare2request_data new_prep , H2 : log_entry_request_data (gi_entry x) = _ |-_ ] =>
       rewrite H1 in H2
     end.
    tcsp.

   }

   {
     allrw is_prepare_for_entry_false_iff.
     unfold is_request_data_for_entry in *.
     unfold eq_request_data in *; smash_pbft.
   }
  Qed.
  (*Hint Rewrite add_new_prepare2log_preserves_commit_in_log : pbft.*)


  Lemma add_commit2entry_some_implies_log_entry_commits_gi_entry_or :
    forall  entry com entry' ,
      add_commit2entry entry com = Some entry'
      -> if in_list_rep_toks (commit2sender com) (log_entry_commits entry)
         then log_entry_commits entry' = log_entry_commits entry
         else log_entry_commits entry' = commit2rep_toks com :: log_entry_commits entry.
  Proof.
    introv h.
    unfold add_commit2entry in h.
    destruct entry; simpl in *.
    smash_pbft.
  Qed.
  Hint Resolve add_commit2entry_some_implies_log_entry_commits_gi_entry_or: pbft.

  Lemma commit2sender_eq_if_request_data_and_rep_toks_equal :
    forall com new_com,
      commit2request_data new_com = commit2request_data com
      -> commit2rep_toks com = commit2rep_toks new_com
      -> commit2sender new_com = commit2sender com.
  Proof.
    introv H1 H2.
    pose proof (decomp_commit com) as q1; rewrite <- q1; clear q1.
    pose proof (decomp_commit new_com) as q2; rewrite <- q2; clear q2.
    allrw. auto.
  Qed.
  Hint Resolve commit2sender_eq_if_request_data_and_rep_toks_equal : pbft.

  Lemma add_new_commit2log_preserves_commit_in_log :
    forall com new_com L gi K,
      add_new_commit2log L new_com = (gi, K)
      -> commit_in_log com K = true
      -> commit_in_log com L = true
         \/
         (
           new_com = com
           /\
           commit_in_log com L = false
(*           /\
           prepared_log (commit2request_data new_com) K = true*)
         ).
  Proof.
    induction L; introv IH1 IH2; repeat (simpl in *; ginv; smash_pbft; tcsp).

    {
      repndors;[|ginv].
      pose proof (decomp_commit com) as q1; rewrite <- q1; clear q1.
      pose proof (decomp_commit new_com) as q2; rewrite <- q2; clear q2.
      allrw same_rep_tok_true_iff.
      allrw; simpl; tcsp.
    }

    {
      match goal with
      | [ H : add_commit2entry _ _ = _ |- _ ] =>
        apply add_commit2entry_some_implies_log_entry_commits_gi_entry_or in H
      end.
      smash_pbft; GC; ginv;[].

      match goal with
      | [ H1 : ?x = _, H2 : existsb _ ?x = _ |- _ ] =>
        rewrite H1 in H2; simpl in H2; pbft_simplifier; repndors; auto;[]
      end.

      match goal with
      | [ H1 : log_entry_request_data ?x = _, H2 : log_entry_request_data _ = _ |- _ ] =>
        rewrite H1 in H2
      end.

      allrw same_rep_tok_true_iff.

      right; dands; tcsp;[|].

      {
        pose proof (decomp_commit com) as q1; rewrite <- q1; clear q1.
        pose proof (decomp_commit new_com) as q2; rewrite <- q2; clear q2.
        allrw; simpl; autorewrite with pbft; tcsp.
      }

      {
        apply in_list_rep_toks_false_implies_existsb_same_rep_toks_false.
        autorewrite with pbft.
        pose proof (commit2sender_eq_if_request_data_and_rep_toks_equal com new_com) as xx.
        autodimp xx hyp.
        autodimp xx hyp.
        rewrite <- xx. auto.
      }
    }

    {
      apply gi_entry_of_add_commit2entry_some in Heqx1.
      allrw is_commit_for_entry_true_iff.
      allrw is_commit_for_entry_false_iff.
      rewrite Heqx1 in Heqx2. tcsp.
    }

    {
      allrw is_commit_for_entry_true_iff.
      allrw is_commit_for_entry_false_iff.

      destruct x;[]; simpl in *.
      unfold add_commit2entry in *.
      destruct a;[]; simpl in *.
      smash_pbft.
    }
  Qed.
  (*Hint Rewrite add_new_commit2log_preserves_commit_in_log : pbft.*)

  Lemma entry_of_commit_in_log :
    forall com L,
      commit_in_log com L = true
      -> exists entry,
        In entry L
        /\ log_entry_request_data entry = commit2request_data com.
  Proof.
    induction L; introv h; simpl in *; tcsp.
    pbft_dest_all x.

    - exists a; dands; tcsp.
      allrw is_commit_for_entry_true_iff; auto.

    - apply IHL in h; exrepnd; exists entry; auto.
  Qed.
  (*Hint Rewrite entry_of_commit_in_log : pbft.*)

  Lemma clear_log_checkpoint_preserves_commit_in_log2 :
    forall com L sn,
      well_formed_log L
      -> commit_in_log com (clear_log_checkpoint L sn) = true
      -> commit_in_log com L = true /\ sn < commit2seq com.
  Proof.
    induction L; simpl in *; introv wf h; tcsp; smash_pbft.

    - inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
      apply IHL in h; repnd; dands; auto.

      match goal with
      | [ H : commit_in_log _ _ = _ |- _ ] => apply entry_of_commit_in_log in H
      end.
      exrepnd.
      discover.
      unfold entries_have_different_request_data in *; congruence.

    - inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
      apply IHL in h; auto.

    - inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
      dands; auto.
      destruct com, b, a; simpl in *; subst; simpl in *; auto.

    - inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.
      apply IHL in h; auto.
  Qed.

  Lemma clear_log_checkpoint_preserves_commit_in_log :
    forall com L sn,
      well_formed_log L
      -> commit_in_log com (clear_log_checkpoint L sn) = true
      -> commit_in_log com L = true.
  Proof.
    introv wf c.
    apply clear_log_checkpoint_preserves_commit_in_log2 in c; tcsp.
  Qed.
  Hint Resolve clear_log_checkpoint_preserves_commit_in_log : pbft.

  Lemma check_stable_preserves_commit_in_log :
    forall slf state entryop state' com,
      well_formed_log (log state)
      -> check_stable slf state entryop = Some state'
      -> commit_in_log com (log state') = true
      -> commit_in_log com (log state) = true.
  Proof.
    introv wf h q.
    unfold check_stable in h.
    pbft_dest_all x;[].
    apply clear_log_checkpoint_preserves_commit_in_log in q; auto.
  Qed.
  Hint Resolve check_stable_preserves_commit_in_log : pbft.

  Lemma add_replies2entry_preserves_log_entry_commits :
    forall entry reps,
      log_entry_commits (add_replies2entry entry reps) = (log_entry_commits entry).
  Proof.
    induction entry; simpl in *; ginv; simpl in *; tcsp.
  Qed.
  Hint Rewrite add_replies2entry_preserves_log_entry_commits : pbft.

  Lemma add_replies2entry_preserves_log_entry_request_data :
    forall entry reps,
      log_entry_request_data (add_replies2entry entry reps) = (log_entry_request_data entry).
  Proof.
    induction entry; simpl in *; ginv; simpl in *; tcsp.
  Qed.
  Hint Rewrite add_replies2entry_preserves_log_entry_request_data : pbft.

  Lemma change_entry_add_replies2entry_preserves_commit_in_log :
    forall com sn entry reps L,
      commit_in_log
        com
        (change_entry L (add_replies2entry entry reps)) = true
      -> find_entry L sn = Some entry
      -> commit_in_log com L = true.
  Proof.
    induction L; introv h fe; simpl in *; tcsp.
    smash_pbft;
      try (complete (applydup entry2seq_if_find_entry in fe as eqsn;
                     match goal with
                     | [ H : similar_entry _ _ = _ |- _ ] =>
                       apply entry2seq_if_similar_entry in H
                     end;
                     match goal with
                     | [ H : _ <> _ |- _ ] => destruct H; allrw; auto
                     end)).

    {
      match goal with
      | [ H : similar_entry _ _ = _ |- _ ] =>
        apply entry2seq_if_similar_entry in H
      end.
      match goal with
      | [ H : find_entry _ _ = _ |- _ ] =>
        apply entry2seq_if_find_entry in H; rewrite H in *; clear H
      end.
      smash_pbft.
    }
  Qed.
  Hint Resolve change_entry_add_replies2entry_preserves_commit_in_log : pbft.

  Lemma change_log_entry_add_replies2entry_preserves_commit_in_log :
    forall com sn entry state reps,
      commit_in_log
        com
        (log
           (change_log_entry
              state
              (add_replies2entry entry reps))) = true
      -> find_entry (log state) sn = Some entry
      -> commit_in_log com (log state) = true.
  Proof.
    introv h fe.
    destruct state; simpl in *.
    eapply change_entry_add_replies2entry_preserves_commit_in_log in h;[|eauto].
    auto.
  Qed.
  Hint Resolve change_log_entry_add_replies2entry_preserves_commit_in_log : pbft.

  Lemma find_and_execute_requests_preserves_commit_in_log :
    forall msg i com st p,
      find_and_execute_requests i (current_view p) (local_keys p) p = (msg, st)
      -> commit_in_log com (log st) = true
      -> commit_in_log com (log p) = true.
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
    | [ H1 : commit_in_log _ (log ?s) = _, H2 : _ = log ?s |- _ ] =>
      rewrite <- H2 in H1; clear H2
    end.

    pose proof (change_log_entry_add_replies2entry_preserves_commit_in_log
                  com (next_to_execute p) y p y3) as xx.
    apply xx in H2; auto.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_commit_in_log : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_commit_in_log :
    forall slf com pp d state state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state (pp,d) = (state', msgs)
      -> commit_in_log com (log state') = true
      -> commit_in_log com (log state) = true
         \/
         (
           com
           = request_data_and_rep_toks2commit
               (pre_prepare2request_data pp d)
               (pre_prepare2rep_toks_of_commit slf (local_keys state) pp d)
           /\ low_water_mark state < pre_prepare2seq pp
           /\ prepared_log (pre_prepare2request_data pp d) (log state') = true
           /\ commit_in_log com (log state) = false).
  Proof.
    introv h q.
    unfold add_prepare_to_log_from_new_view_pre_prepare in h; smash_pbft.

    match goal with
    | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
      apply check_send_replies_preserves_log in H; simpl in *; subst
    end.

    match goal with
    | [ H : add_new_pre_prepare_and_prepare2log _ _ _ _ _ _ = _ |- _ ] =>
      eapply add_new_pre_prepare_and_prepare2log_preserves_commit_in_log in H;[ | | eauto]
    end.

    - repndors; auto.
      exrepnd; tcsp.

    - unfold pre_prepare2rep_toks_of_commit.
      autorewrite with pbft.
      destruct pp, b. simpl in *. auto.
  Qed.


  Lemma fill_out_pp_info_with_prepare_preserves_existsb_rep_tok_commit :
    forall i entry pp Fp Fc gi rt,
      fill_out_pp_info_with_prepare i entry pp Fp Fc = Some gi
      -> existsb (same_rep_tok rt) (log_entry_commits entry) = true
      -> existsb (same_rep_tok rt) (log_entry_commits (gi_entry gi)) = true.
  Proof.
    introv h q; unfold fill_out_pp_info_with_prepare in h.
    destruct entry; simpl in *.
    destruct log_entry_pre_prepare_info; ginv.
    smash_pbft.
    unfold add_commit_if_prepared in *. smash_pbft.
  Qed.
  Hint Resolve fill_out_pp_info_with_prepare_preserves_existsb_rep_tok_commit : pbft.


  Lemma add_new_pre_prepare_and_prepare2log_preserves_commit_in_log_forward :
    forall i L pp d Fp Fc giop K com,
      add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> commit_in_log com L = true
      -> commit_in_log com K = true.
  Proof.
    induction L; introv h q; simpl in *; smash_pbft.

    - allrw is_commit_for_entry_true_iff.
      allrw is_commit_for_entry_false_iff.

      match goal with
      | [ H : fill_out_pp_info_with_prepare _ _ _ _ _ = _ |- _ ] =>
        eapply fill_out_pp_info_with_prepare_preserves_request_data in H
      end.

      rewrite Heqx in Heqx1. tcsp.

    - allrw is_commit_for_entry_true_iff.
      allrw is_commit_for_entry_false_iff.

      match goal with
      | [ H : fill_out_pp_info_with_prepare _ _ _ _ _ = _ |- _ ] =>
        apply fill_out_pp_info_with_prepare_preserves_request_data in H
      end.

      match goal with
      | [ H1 : ?x = ?y, H2 : ?x = ?z |- _ ] => rewrite H2 in H1; tcsp
      end.
  Qed.
  Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_commit_in_log_forward : pbft.

  Lemma check_send_replies_preserves_commit_in_log_forward :
    forall i v keys giop state n msgs state' com,
      check_send_replies i v keys giop state n = (msgs, state')
      -> commit_in_log com (log state) = true
      -> commit_in_log com (log state') = true.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve check_send_replies_preserves_commit_in_log_forward : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_commit_in_log_forward :
    forall slf com state pp d state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state (pp, d) = (state', msgs)
      -> commit_in_log com (log state) = true
      -> commit_in_log com (log state') = true.
  Proof.
    introv h q.
    unfold add_prepare_to_log_from_new_view_pre_prepare in h.
    smash_pbft.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_commit_in_log_forward : pbft.


  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log_forward :
    forall slf com pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> commit_in_log com (log state) = true
      -> commit_in_log com (log state') = true.
  Proof.
    induction pps; introv h q; simpl in *; smash_pbft; repnd.
    eapply IHpps; eauto with pbft.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log_forward : pbft.


  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_commit_in_log_backward :
    forall slf com state pp d state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state (pp, d) = (state', msgs)
      -> commit_in_log com (log state') = false
      -> commit_in_log com (log state) = false.
  Proof.
    introv h q.
    match goal with
    | [ |- ?a = ?b ] => remember a as pb; symmetry in Heqpb; destruct pb; auto
    end.
    eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_commit_in_log_forward in h;[|eauto].
    rewrite h in q; ginv.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_commit_in_log_backward : pbft.


  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log_backward :
    forall slf com pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> commit_in_log com (log state') = false
      -> commit_in_log com (log state) = false.
  Proof.
    introv h q.
    match goal with
    | [ |- ?a = ?b ] => remember a as pb; symmetry in Heqpb; destruct pb; auto
    end.
    eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log_forward in h;[|eauto].
    rewrite h in q; ginv.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log_backward : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log :
    forall slf com pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> commit_in_log com (log state') = true
      -> commit_in_log com (log state) = true
         \/
         (
           exists pp d,
             In (pp,d) pps
             /\ com
                = request_data_and_rep_toks2commit
                    (pre_prepare2request_data pp d)
                    (pre_prepare2rep_toks_of_commit slf (local_keys state) pp d)
             /\ low_water_mark state < pre_prepare2seq pp
             /\ commit_in_log com (log state) = false).
  Proof.
    induction pps; introv h q; simpl in *; smash_pbft; repnd.

    match goal with
    | [ H : add_prepares_to_log_from_new_view_pre_prepares _ _ _ = _ |- _ ] =>
      apply IHpps in H;auto;[]
    end.
    repndors; tcsp.

    {
      match goal with
      | [ H : add_prepare_to_log_from_new_view_pre_prepare _ _ _ = _ |- _ ] =>
        eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_commit_in_log in H;[|eauto]
      end.

      repndors; tcsp; subst.

      exrepnd.
      right.
      exists a0 a; dands; auto.
    }

    {
      exrepnd; subst.
      right.

      rename_hyp_with add_prepare_to_log_from_new_view_pre_prepare add.
      applydup add_prepare_to_log_from_new_view_pre_prepare_preserves_cp_state in add.
      apply eq_low_water_marks_if_eq_cp_states in add0.
      rewrite <- add0.

      exists pp d; dands; tcsp; eauto 3 with pbft.

      match goal with
      | [ H : add_prepare_to_log_from_new_view_pre_prepare _ _ _ = _ |- _ ] =>
        apply add_prepare_to_log_from_new_view_pre_prepare_preserves_local_keys in H
      end.
      allrw; auto.
    }
  Qed.
  (*Hint Rewrite add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log : pbft.*)

  Lemma log_pre_prepares_preserves_commit_in_log :
    forall com P L lwm,
      commit_in_log com (log_pre_prepares L lwm P)
      = commit_in_log com L.
  Proof.
    induction P; introv; simpl in *; tcsp; repnd; smash_pbft.
    rewrite IHP.
    apply add_new_pre_prepare2log_preserves_commit_in_log.
  Qed.
  Hint Rewrite log_pre_prepares_preserves_commit_in_log : pbft.

  Lemma update_state_new_view_preserves_commit_in_log2 :
    forall i st nv st' msgs com,
      well_formed_log (log st)
      -> correct_new_view nv = true
      -> update_state_new_view i st nv = (st', msgs)
      -> commit_in_log com (log st') = true
      -> commit_in_log com (log st) = true
         /\ (low_water_mark st < low_water_mark st' -> low_water_mark st' < commit2seq com).
  Proof.
    introv wf cor upd h.
    unfold update_state_new_view in *; smash_pbft;
      try (complete (dands; auto; introv q; try omega));[].

    apply clear_log_checkpoint_preserves_commit_in_log2 in h; eauto 3 with pbft;[].
    repnd.
    unfold log_checkpoint_cert_from_new_view in *; smash_pbft.

    + unfold low_water_mark; simpl; dands; auto.

      rename_hyp_with view_change_cert2max_seq_vc maxs.
      applydup view_change_cert2_max_seq_vc_some_in in maxs.
      applydup sn_of_view_change_cert2max_seq_vc in maxs.
      subst.

      rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft; [].
      subst; auto.

    + rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_none_implies in ext.
      rewrite ext in *.
      simpl in *; ginv.

    + rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft;[].
      subst.
      unfold low_water_mark; simpl in *.
      dands; auto.

      rename_hyp_with view_change_cert2max_seq_vc maxs.
      applydup view_change_cert2_max_seq_vc_some_in in maxs.
      applydup sn_of_view_change_cert2max_seq_vc in maxs.
      subst; auto.

    + rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      apply extract_seq_and_digest_from_checkpoint_certificate_none_implies in ext.
      dands; auto.

      rename_hyp_with view_change_cert2max_seq_vc maxs.
      applydup view_change_cert2_max_seq_vc_some_in in maxs.
      applydup sn_of_view_change_cert2max_seq_vc in maxs.
      subst; auto.

      assert (correct_view_change (new_view2view nv) x2 = true) as cvc by eauto 3 with pbft;[].
      unfold correct_view_change in cvc; smash_pbft.
      rewrite ext in *.
      simpl in *; ginv; try omega.
  Qed.

  Lemma update_state_new_view_preserves_commit_in_log :
    forall i st nv st' msgs com,
      well_formed_log (log st)
      -> update_state_new_view i st nv = (st', msgs)
      -> commit_in_log com (log st') = true
      -> commit_in_log com (log st) = true.
  Proof.
    introv wf upd h.
    unfold update_state_new_view in *; smash_pbft.
    apply clear_log_checkpoint_preserves_commit_in_log in h; eauto 3 with pbft;[].
    unfold log_checkpoint_cert_from_new_view in *; smash_pbft.
  Qed.
  Hint Resolve update_state_new_view_preserves_commit_in_log : pbft.

  Lemma commit_in_log_clear_log_checkpoint_false_implies :
    forall (n : SeqNum) c L,
      n < commit2seq c
      -> commit_in_log c (clear_log_checkpoint L n) = false
      -> commit_in_log c L = false.
  Proof.
    induction L; introv h prep; simpl in *; smash_pbft.
    repeat (autodimp IHL hyp).
    allrw SeqNumLe_true.
    destruct a, c, b, log_entry_request_data; simpl in *; ginv; omega.
  Qed.
  Hint Resolve commit_in_log_clear_log_checkpoint_false_implies : pbft.

  Lemma update_state_new_view_preserves_commit_in_log_false_forward :
    forall c i s1 v s2 msgs,
      correct_new_view v = true
      -> update_state_new_view i s1 v = (s2, msgs)
      -> low_water_mark s2 < commit2seq c
      -> commit_in_log c (log s2) = false
      -> commit_in_log c (log s1) = false.
  Proof.
    introv cor upd h com.

    unfold update_state_new_view in upd; smash_pbft.
    unfold log_checkpoint_cert_from_new_view in *; smash_pbft.

    - unfold update_log_checkpoint_stable, low_water_mark in *; simpl in *.
      apply commit_in_log_clear_log_checkpoint_false_implies in com; eauto 3 with pbft.

      rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      apply sn_of_view_change_cert2max_seq_vc in mseq; subst.

      rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft;[].
      subst; auto.

    - rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      apply sn_of_view_change_cert2max_seq_vc in mseq; subst.

      rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      apply extract_seq_and_digest_from_checkpoint_certificate_none_implies in ext.
      rewrite ext in *.
      simpl in *; ginv.

    - unfold update_log_checkpoint_stable, low_water_mark in *; simpl in *.
      apply commit_in_log_clear_log_checkpoint_false_implies in com; eauto 3 with pbft.

      rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      apply sn_of_view_change_cert2max_seq_vc in mseq; subst.

      rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      eapply extract_seq_and_digest_from_checkpoint_certificate_implies_eq_view_change2seq in ext; eauto 3 with pbft;[].
      subst; auto.

    - rename_hyp_with view_change_cert2max_seq_vc mseq.
      applydup view_change_cert2_max_seq_vc_some_in in mseq.
      apply sn_of_view_change_cert2max_seq_vc in mseq; subst.

      rename_hyp_with extract_seq_and_digest_from_checkpoint_certificate ext.
      apply extract_seq_and_digest_from_checkpoint_certificate_none_implies in ext.
      rewrite ext in *.
      simpl in *; ginv.

      apply correct_new_view_implies_correct_view_change in mseq0; auto.
      unfold correct_view_change, correct_view_change_cert in *; smash_pbft.
      rewrite ext in *; simpl in *; omega.
  Qed.
  Hint Resolve update_state_new_view_preserves_commit_in_log_false_forward : pbft.

End PBFTcommit_in_log_preserves.


Hint Resolve check_send_replies_preserves_commit_in_log: pbft.
Hint Resolve commit2sender_eq_if_request_data_and_rep_toks_equal : pbft.
Hint Resolve fill_out_pp_info_with_prepare_preserves_existsb_rep_tok_commit : pbft.
Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_commit_in_log_forward : pbft.
Hint Resolve check_send_replies_preserves_commit_in_log_forward : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_commit_in_log_forward : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log_forward : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_commit_in_log_backward : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log_backward : pbft.
Hint Resolve commit_in_log_clear_log_checkpoint_false_implies : pbft.
Hint Resolve update_state_new_view_preserves_commit_in_log_false_forward : pbft.
Hint Resolve clear_log_checkpoint_preserves_commit_in_log : pbft.
Hint Resolve update_state_new_view_preserves_commit_in_log : pbft.
Hint Resolve check_stable_preserves_commit_in_log : pbft.
Hint Resolve change_entry_add_replies2entry_preserves_commit_in_log : pbft.
Hint Resolve change_log_entry_add_replies2entry_preserves_commit_in_log : pbft.
Hint Resolve find_and_execute_requests_preserves_commit_in_log : pbft.


Hint Rewrite @is_commit_for_entry_true_iff : pbft.
Hint Rewrite @is_commit_for_entry_false_iff : pbft.
Hint Rewrite @add_new_pre_prepare2log_preserves_commit_in_log : pbft.
Hint Rewrite @decomp_commit : pbft.
Hint Rewrite @rt_rep_commit2rep_toks_as_commit2sender: pbft.
Hint Rewrite @add_replies2entry_preserves_log_entry_request_data : pbft.
Hint Rewrite @log_pre_prepares_preserves_commit_in_log : pbft.
Hint Rewrite @add_replies2entry_preserves_log_entry_commits : pbft.
(*Hint Rewrite @commit_in_log_add_new_pre_prepare2log_log_entry_commits : pbft.*)
(*Hint Rewrite @add_new_pre_prepare_and_prepare2log_preserves_commit_in_log : pbft.*)
(*Hint Rewrite @add_new_prepare2log_preserves_commit_in_log : pbft.*)
(*Hint Resolve @add_commit2entry_some_implies_log_entry_commits_gi_entry_or: pbft.*)
(*Hint Rewrite @add_new_commit2log_preserves_commit_in_log : pbft.*)
(*Hint Rewrite @entry_of_commit_in_log : pbft.*)
(*Hint Rewrite @add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log : pbft.*)
