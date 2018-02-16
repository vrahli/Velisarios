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


Section PBFTprepare_in_log_preserves.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma add_new_commit2log_preserves_prepare_in_log :
    forall p c L1 L2 i,
      add_new_commit2log L1 c = (i, L2)
      -> prepare_in_log p L2 = prepare_in_log p L1.
  Proof.
    induction L1; introv h; simpl in *; tcsp.

    { pbft_simplifier; simpl in *; pbft_dest_all w. }

    pbft_dest_all w.

    - applydup add_commit2entry_preserves_log_entry_prepares in Heqw1 as e.
      rewrite <- e; auto.

    - apply (add_commit2entry_preserves_is_prepare_for_entry p) in Heqw1.
      match goal with
      | [ H1 : ?a = ?b, H2 : ?a = false, H3 : ?b = true |- _ ] =>
        rewrite H1 in H2; rewrite H2 in H3; ginv
      end.

    - apply (add_commit2entry_preserves_is_prepare_for_entry p) in Heqw1.
      match goal with
      | [ H1 : ?a = ?b, H2 : ?a = true, H3 : ?b = false |- _ ] =>
        rewrite H1 in H2; rewrite H2 in H3; ginv
      end.

    - eapply IHL1; eauto.
  Qed.

  Lemma decrement_requests_in_progress_preserves_prepare_in_log :
    forall i prep p st,
      prepare_in_log prep (log (decrement_requests_in_progress_if_primary i (current_view p) st))
      = prepare_in_log prep (log st).
  Proof.
    introv.
    unfold decrement_requests_in_progress_if_primary.
    pbft_dest_all x.
  Qed.
  Hint Rewrite decrement_requests_in_progress_preserves_prepare_in_log : pbft.

  Lemma entry_of_prepare_in_log :
    forall p L,
      prepare_in_log p L = true
      -> exists entry,
        In entry L
        /\ log_entry_request_data entry = prepare2request_data p.
  Proof.
    induction L; introv h; simpl in *; tcsp.
    pbft_dest_all x.

    - exists a; dands; tcsp.
      apply is_prepare_for_entry_true_implies; auto.

    - apply IHL in h; exrepnd; exists entry; auto.
  Qed.

  Lemma change_entry_add_replies2entry_preserves_prepare_in_log :
    forall prep sn entry L reps,
      prepare_in_log
        prep
        (change_entry L (add_replies2entry entry reps)) = true
      -> find_entry L sn = Some entry
      -> prepare_in_log prep L = true.
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
  Qed.

  Lemma change_log_entry_add_replies2entry_preserves_prepare_in_log :
    forall prep sn entry state reps,
      prepare_in_log
        prep
        (log
           (change_log_entry
              state
              (add_replies2entry entry reps))) = true
      -> find_entry (log state) sn = Some entry
      -> prepare_in_log prep (log state) = true.
  Proof.
    introv h fe.
    destruct state; simpl in *.
    eapply change_entry_add_replies2entry_preserves_prepare_in_log in h;[|eauto].
    auto.
  Qed.

  Lemma find_and_execute_requests_preserves_prepare_in_log :
    forall msg i prep st p,
      find_and_execute_requests i (current_view p) (local_keys p) p = (msg, st)
      -> prepare_in_log prep (log st) = true
      -> prepare_in_log prep (log p) = true.
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
    | [ H1 : prepare_in_log _ (log ?s) = _, H2 : _ = log ?s |- _ ] =>
      rewrite <- H2 in H1; clear H2
    end.

    pose proof (change_log_entry_add_replies2entry_preserves_prepare_in_log
                  prep (next_to_execute p) y p y3) as xx.
    apply xx in H2; auto.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_prepare_in_log : pbft.

  Lemma log_pre_prepares_preserves_prepare_in_log :
    forall prep P L lwm,
      prepare_in_log prep (log_pre_prepares L lwm P)
      = prepare_in_log prep L.
  Proof.
    induction P; introv; simpl in *; tcsp; repnd; smash_pbft.
    rewrite IHP.
    autorewrite with pbft; auto.
  Qed.
  Hint Rewrite log_pre_prepares_preserves_prepare_in_log : pbft.

  Lemma check_send_replies_preserves_prepare_in_log :
    forall prep slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> prepare_in_log prep (log state') = true
      -> prepare_in_log prep (log state) = true.
  Proof.
    introv chk pil.
    unfold check_send_replies in chk.
    destruct entryop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_prepare_in_log : pbft.

  Lemma prepare2re_toks_request_data_and_rep_toks2prepare :
    forall rd rt,
      prepare2rep_toks (request_data_and_rep_toks2prepare rd rt) = rt.
  Proof.
    introv; destruct rd, rt; simpl; auto.
  Qed.
  Hint Rewrite prepare2re_toks_request_data_and_rep_toks2prepare : pbft.

  Lemma add_new_prepare2log_preserves_prepare_in_log :
    forall slf gi Fc prep new_prep L new_log,
      add_new_prepare2log slf L new_prep Fc = (gi, new_log)
      -> prepare_in_log prep new_log = true
      -> prepare_in_log prep L = true
         \/
         (
           new_prep = prep
           /\
           prepare_in_log prep L = false
         ).
  Proof.
    induction L; introv IH1 IH2; simpl in *; pbft_simplifier;
      simpl in *; smash_pbft; repndors; tcsp;
        allrw is_prepare_for_entry_true_iff;
        allrw same_rep_tok_true_iff; simpl in *.

    {
      pose proof (decomp_propose prep) as q1; rewrite <- q1; clear q1.
      pose proof (decomp_propose new_prep) as q2; rewrite <- q2; clear q2.
      allrw; simpl; tcsp.
    }

    {
      match goal with
      | [ H : add_prepare2entry _ _ _ _ = _ |- _ ] =>
        apply add_prepare2entry_some_implies_log_entry_prepares_gi_entry_or in H
      end.
      smash_pbft; GC; ginv.

      match goal with
      | [ H1 : ?x = _, H2 : existsb _ ?x = _ |- _ ] =>
        rewrite H1 in H2; simpl in H2; pbft_simplifier; repndors; auto;[]
      end.

      match goal with
      | [ H1 : log_entry_request_data ?x = _, H2 : log_entry_request_data _ = _ |- _ ] =>
        rewrite H1 in H2
      end.

      allrw same_rep_tok_true_iff.
      pose proof (decomp_propose prep) as q1; rewrite <- q1; clear q1.
      pose proof (decomp_propose new_prep) as q2; rewrite <- q2; clear q2.
      allrw; simpl; autorewrite with pbft; tcsp.
      right; dands; tcsp.

      apply in_list_rep_toks_false_implies_existsb_same_rep_toks_false.
      autorewrite with pbft; auto.
    }

    {
      apply gi_entry_of_add_prepare2entry_some in Heqx1.
      allrw is_prepare_for_entry_true_iff.
      allrw is_prepare_for_entry_false_iff.
      rewrite Heqx1 in Heqx2. tcsp.
    }

    {
      allrw is_prepare_for_entry_true_iff.
      allrw is_prepare_for_entry_false_iff.

      destruct x;[]; simpl in *.
      unfold add_prepare2entry in *.
      destruct a;[]; simpl in *.
      smash_pbft.
    }
  Qed.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_in_log :
    forall slf prep pp d state state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state (pp,d) = (state', msgs)
      -> prepare_in_log prep (log state') = true
      -> prepare_in_log prep (log state) = true
         \/
         (
           prep
           = request_data_and_rep_toks2prepare
               (pre_prepare2request_data pp d)
               (pre_prepare2rep_toks_of_prepare slf (local_keys state) pp d)
           /\ low_water_mark state < pre_prepare2seq pp
           /\ prepare_in_log prep (log state) = false
           (*/\ own_prepare_is_already_logged_with_different_digest
                slf (pre_prepare2seq pp) (pre_prepare2view pp) d (log state) = None*)
  (*         /\ (forall entry : PBFTlogEntry,
                  find_entry_with_request_data (log state) (pre_prepare2request_data pp d) = Some entry
                  -> length (log_entry_prepares entry) < 2 * F
                     /\ in_list_rep_toks slf (log_entry_prepares entry) = false)*)
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
      eapply add_new_pre_prepare_and_prepare2log_preserves_prepare_in_log in H;[| |eauto];
        autorewrite with pbft;auto
    end.
    repndors; repnd; tcsp.
  Qed.

  Lemma add_prepare_if_not_enough_preserves_existsb_rep_tok :
    forall i preps Fp rtop preps' rt,
      add_prepare_if_not_enough i preps Fp = (rtop, preps')
      -> existsb (same_rep_tok rt) preps = true
      -> existsb (same_rep_tok rt) preps' = true.
  Proof.
    introv h q; unfold add_prepare_if_not_enough in h.
    smash_pbft.
  Qed.
  Hint Resolve add_prepare_if_not_enough_preserves_existsb_rep_tok : pbft.

  Lemma fill_out_pp_info_with_prepare_preserves_existsb_rep_tok :
    forall i entry pp Fp Fc gi rt,
      fill_out_pp_info_with_prepare i entry pp Fp Fc = Some gi
      -> existsb (same_rep_tok rt) (log_entry_prepares entry) = true
      -> existsb (same_rep_tok rt) (log_entry_prepares (gi_entry gi)) = true.
  Proof.
    introv h q; unfold fill_out_pp_info_with_prepare in h.
    destruct entry; simpl in *.
    destruct log_entry_pre_prepare_info; ginv.
    smash_pbft.
  Qed.
  Hint Resolve fill_out_pp_info_with_prepare_preserves_existsb_rep_tok : pbft.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_prepare_in_log_forward :
    forall i L pp d Fp Fc giop K prep,
      add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> prepare_in_log prep L = true
      -> prepare_in_log prep K = true.
  Proof.
    induction L; introv h q; simpl in *; smash_pbft.

    - allrw is_prepare_for_entry_true_iff.
      allrw is_prepare_for_entry_false_iff.

      match goal with
      | [ H : fill_out_pp_info_with_prepare _ _ _ _ _ = _ |- _ ] =>
        apply fill_out_pp_info_with_prepare_preserves_request_data in H
      end.

      match goal with
      | [ H1 : ?x = ?y, H2 : ?y = ?z |- _ ] => rewrite H2 in H1; tcsp
      end.

    - allrw is_prepare_for_entry_true_iff.
      allrw is_prepare_for_entry_false_iff.

      match goal with
      | [ H : fill_out_pp_info_with_prepare _ _ _ _ _ = _ |- _ ] =>
        apply fill_out_pp_info_with_prepare_preserves_request_data in H
      end.

      match goal with
      | [ H1 : ?x = ?y, H2 : ?x = ?z |- _ ] => rewrite H2 in H1; tcsp
      end.
  Qed.
  Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_prepare_in_log_forward : pbft.

  Lemma check_send_replies_preserves_prepare_in_log_forward :
    forall i v keys giop state n msgs state' prep,
      check_send_replies i v keys giop state n = (msgs, state')
      -> prepare_in_log prep (log state) = true
      -> prepare_in_log prep (log state') = true.
  Proof.
    introv h q.
    unfold check_send_replies in h.
    destruct giop; smash_pbft.
    destruct g; smash_pbft.
  Qed.
  Hint Resolve check_send_replies_preserves_prepare_in_log_forward : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_in_log_forward :
    forall slf prep state pp d state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state (pp, d) = (state', msgs)
      -> prepare_in_log prep (log state) = true
      -> prepare_in_log prep (log state') = true.
  Proof.
    introv h q.
    unfold add_prepare_to_log_from_new_view_pre_prepare in h.
    smash_pbft.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_in_log_forward : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_in_log_backward :
    forall slf prep state pp d state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state (pp, d) = (state', msgs)
      -> prepare_in_log prep (log state') = false
      -> prepare_in_log prep (log state) = false.
  Proof.
    introv h q.
    match goal with
    | [ |- ?a = ?b ] => remember a as pb; symmetry in Heqpb; destruct pb; auto
    end.
    eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_in_log_forward in h;[|eauto].
    rewrite h in q; ginv.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_in_log_backward : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log_forward :
    forall slf prep pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> prepare_in_log prep (log state) = true
      -> prepare_in_log prep (log state') = true.
  Proof.
    induction pps; introv h q; simpl in *; smash_pbft; repnd.
    eapply IHpps; eauto with pbft.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log_forward : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log_backward :
    forall slf prep pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> prepare_in_log prep (log state') = false
      -> prepare_in_log prep (log state) = false.
  Proof.
    introv h q.
    match goal with
    | [ |- ?a = ?b ] => remember a as pb; symmetry in Heqpb; destruct pb; auto
    end.
    eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log_forward in h;[|eauto].
    rewrite h in q; ginv.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log_backward : pbft.

  Lemma fill_out_pp_info_with_prepare_preserves_own_prepare_is_already_logged_with_different_digest_false :
    forall i e p Fp Fc gi s v d,
      fill_out_pp_info_with_prepare i e p Fp Fc = Some gi
      -> own_prepare_is_already_in_entry_with_different_digest i s v d (gi_entry gi) = None
      -> own_prepare_is_already_in_entry_with_different_digest i s v d e = None.
  Proof.
    introv f o.
    unfold fill_out_pp_info_with_prepare in f; destruct e; simpl in *.
    destruct log_entry_pre_prepare_info; ginv.
    unfold own_prepare_is_already_in_entry_with_different_digest in *; simpl in *.
    smash_pbft.

    unfold add_prepare_if_not_enough in *; smash_pbft.
  Qed.
  Hint Resolve fill_out_pp_info_with_prepare_preserves_own_prepare_is_already_logged_with_different_digest_false : pbft.

  Lemma add_new_pre_prepare_and_prepare2log_preserves_own_prepare_is_already_logged_with_different_digest_false :
    forall i L1 p p0 Fp Fc giop L2 s v d,
      add_new_pre_prepare_and_prepare2log i L1 p p0 Fp Fc = (giop, L2)
      -> own_prepare_is_already_logged_with_different_digest i s v d L2 = None
      -> own_prepare_is_already_logged_with_different_digest i s v d L1 = None.
  Proof.
    induction L1; introv xx o; simpl in *; smash_pbft.
    match goal with
    | [ H : own_prepare_is_already_in_entry_with_different_digest _ _ _ _ _ = Some _ |- _ ] => rename H into own
    end.
    erewrite fill_out_pp_info_with_prepare_preserves_own_prepare_is_already_logged_with_different_digest_false in own;[|eauto|];auto.
  Qed.
  Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_own_prepare_is_already_logged_with_different_digest_false : pbft.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_own_prepare_is_already_logged_with_different_digest_false :
    forall i st1 ppd st2 msgs s v d,
      add_prepare_to_log_from_new_view_pre_prepare i st1 ppd = (st2, msgs)
      -> own_prepare_is_already_logged_with_different_digest i s v d (log st2) = None
      -> own_prepare_is_already_logged_with_different_digest i s v d (log st1) = None.
  Proof.
    introv h o.
    unfold add_prepare_to_log_from_new_view_pre_prepare in h; destruct ppd; smash_pbft.

    match goal with
    | [ H : check_send_replies _ _ _ _ _ _ = _ |- _ ] =>
      apply check_send_replies_preserves_log in H
    end; simpl in *; subst.
    eauto 3 with pbft.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_own_prepare_is_already_logged_with_different_digest_false : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log :
    forall slf prep pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> prepare_in_log prep (log state') = true
      -> prepare_in_log prep (log state) = true
         \/
         exists pp d,
           In (pp,d) pps
           /\ prep
              = request_data_and_rep_toks2prepare
                  (pre_prepare2request_data pp d)
                  (pre_prepare2rep_toks_of_prepare slf (local_keys state) pp d)
           /\ low_water_mark state < pre_prepare2seq pp
           /\ prepare_in_log prep (log state) = false
           (*/\ own_prepare_is_already_logged_with_different_digest
                slf (pre_prepare2seq pp) (pre_prepare2view pp) d (log state) = None*).
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
        eapply add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_in_log in H;[|eauto]
      end.

      repndors; repnd; tcsp; subst.
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

(*  Lemma update_state_new_view_preserves_prepare_in_log :
    forall i st nv st' msgs p,
      update_state_new_view i st nv = (st', msgs)
      -> prepare_in_log p (log st) = true
      -> prepare_in_log p (log st') = true.
  Proof.
    introv u prep.
    apply update_state_new_view_preserves_log in u; allrw <-; auto.
  Qed.
  Hint Resolve update_state_new_view_preserves_prepare_in_log : pbft.*)

  Lemma clear_log_checkpoint_preserves_prepare_in_log :
    forall p L sn,
      well_formed_log L
      -> prepare_in_log p (clear_log_checkpoint L sn) = true
      -> prepare_in_log p L = true.
  Proof.
    induction L; simpl in *; introv wf h; tcsp.
    pbft_dest_all x.

    - assert False; tcsp.

      inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.

      match goal with
      | [ H : is_prepare_for_entry _ _ = true |- _ ] =>
        apply is_prepare_for_entry_true_implies in H
      end.

      match goal with
      | [ H : prepare_in_log _ _ = _ |- _ ] => apply entry_of_prepare_in_log in H
      end.
      exrepnd.
      pose proof (imp entry) as q; autodimp q hyp; apply q; auto.
      allrw; auto.

    - inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.

    - inversion wf as [|? ? imp wfL]; subst; clear wf.
      apply IHL in h; auto.
  Qed.

  Lemma check_stable_preserves_prepare_in_log :
    forall slf state entryop state' p,
      well_formed_log (log state)
      -> check_stable slf state entryop = Some state'
      -> prepare_in_log p (log state') = true
      -> prepare_in_log p (log state) = true.
  Proof.
    introv wf h q.
    unfold check_stable in h.
    pbft_dest_all x;[].
    apply clear_log_checkpoint_preserves_prepare_in_log in q; auto.
  Qed.

  Lemma update_state_new_view_preserves_prepare_in_log :
    forall p i s1 v s2 msgs,
      well_formed_log (log s1)
      -> update_state_new_view i s1 v = (s2, msgs)
      -> prepare_in_log p (log s2) = true
      -> prepare_in_log p (log s1) = true.
  Proof.
    introv wf upd prep.
    unfold update_state_new_view in upd; smash_pbft.
    rename_hyp_with log_checkpoint_cert_from_new_view chk.
    apply log_checkpoint_cert_from_new_view_preserves_log in chk; allrw.
    eapply clear_log_checkpoint_preserves_prepare_in_log; eauto.
    allrw <- ; auto.
  Qed.
  Hint Resolve update_state_new_view_preserves_prepare_in_log : pbft.

  Lemma prepare_in_log_clear_log_checkpoint_false_implies :
    forall (n : SeqNum) p L,
      n < prepare2seq p
      -> prepare_in_log p (clear_log_checkpoint L n) = false
      -> prepare_in_log p L = false.
  Proof.
    induction L; introv h prep; simpl in *; smash_pbft.
    repeat (autodimp IHL hyp).
    allrw SeqNumLe_true.
    unfold is_prepare_for_entry, eq_request_data in *; smash_pbft.
    destruct a, p, b, log_entry_request_data; simpl in *; ginv; omega.
  Qed.
  Hint Resolve prepare_in_log_clear_log_checkpoint_false_implies : pbft.

  Lemma update_state_new_view_preserves_prepare_in_log_false_forward :
    forall p i s1 v s2 msgs,
      correct_new_view v = true
      -> update_state_new_view i s1 v = (s2, msgs)
      -> low_water_mark s2 < prepare2seq p
      -> prepare_in_log p (log s2) = false
      -> prepare_in_log p (log s1) = false.
  Proof.
    introv cor upd h prep.

    unfold update_state_new_view in upd; smash_pbft.
    unfold log_checkpoint_cert_from_new_view in *; smash_pbft.

    - unfold update_log_checkpoint_stable, low_water_mark in *; simpl in *.
      apply prepare_in_log_clear_log_checkpoint_false_implies in prep; eauto 3 with pbft.

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
      apply prepare_in_log_clear_log_checkpoint_false_implies in prep; eauto 3 with pbft.

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
      rewrite ext in *; simpl in *; try omega.
  Qed.
  Hint Resolve update_state_new_view_preserves_prepare_in_log_false_forward : pbft.

End PBFTprepare_in_log_preserves.


Hint Rewrite @decrement_requests_in_progress_preserves_prepare_in_log : pbft.
Hint Rewrite @log_pre_prepares_preserves_prepare_in_log : pbft.
Hint Rewrite @rt_rep_pre_prepare2rep_toks_of_prepare : pbft.


Hint Resolve check_send_replies_preserves_prepare_in_log : pbft.
Hint Resolve add_prepare_if_not_enough_preserves_existsb_rep_tok : pbft.
Hint Resolve fill_out_pp_info_with_prepare_preserves_existsb_rep_tok : pbft.
Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_prepare_in_log_forward : pbft.
Hint Resolve check_send_replies_preserves_prepare_in_log_forward : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_in_log_forward : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_prepare_in_log_backward : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log_forward : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_prepare_in_log_backward : pbft.
Hint Resolve find_and_execute_requests_preserves_prepare_in_log : pbft.
(*Hint Resolve update_state_new_view_preserves_prepare_in_log : pbft.*)
Hint Resolve fill_out_pp_info_with_prepare_preserves_own_prepare_is_already_logged_with_different_digest_false : pbft.
Hint Resolve add_new_pre_prepare_and_prepare2log_preserves_own_prepare_is_already_logged_with_different_digest_false : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_own_prepare_is_already_logged_with_different_digest_false : pbft.
Hint Resolve update_state_new_view_preserves_prepare_in_log : pbft.
Hint Resolve prepare_in_log_clear_log_checkpoint_false_implies : pbft.
Hint Resolve update_state_new_view_preserves_prepare_in_log_false_forward : pbft.
