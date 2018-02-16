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


Require Export PBFTwell_formed_log_def.
Require Export PBFTtactics3.


Section PBFTwell_formed_log.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.

  Lemma eq_request_data_true :
    forall rd1 rd2, eq_request_data rd1 rd2 = true <-> rd1 = rd2.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Rewrite eq_request_data_true : pbft.

  Lemma digest_for_pre_prepare_mk_auth_pre_prepare :
    forall rs v n keys,
      digest_for_pre_prepare
        (requests2digest rs)
        (mk_auth_pre_prepare v n rs keys) = true.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Rewrite digest_for_pre_prepare_mk_auth_pre_prepare : pbft.
  Hint Resolve digest_for_pre_prepare_mk_auth_pre_prepare : pbft.

  Lemma digest_for_pre_prepare_trivial :
    forall pp,
      digest_for_pre_prepare
        (pre_prepare2digest pp)
        pp = true.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Rewrite digest_for_pre_prepare_trivial : pbft.
  Hint Resolve digest_for_pre_prepare_trivial : pbft.

  Lemma find_pre_prepare_certificate_in_prepared_infos_implies_in :
    forall F n C e,
      find_pre_prepare_certificate_in_prepared_infos F n C = Some e
      -> In e C.
  Proof.
    induction C; introv find; simpl in *; smash_pbft.
  Qed.

  Lemma create_new_prepare_message_implies_well_formed_pre_prepare_and_digest :
    forall n v keys C b pp d,
      create_new_prepare_message n v keys C = (b, (pp,d))
      -> wf_prepared_infos C = true
      -> digest_for_pre_prepare d pp = true.
  Proof.
    introv create wf; unfold create_new_prepare_message in create; smash_pbft;[].

    match goal with
    | [ H : context[find_pre_prepare_certificate_in_prepared_infos] |- _ ] =>
      apply find_pre_prepare_certificate_in_prepared_infos_implies_in in H;
        apply wf_prepared_info_if_in in H;auto
    end.
  Qed.
  Hint Resolve create_new_prepare_message_implies_well_formed_pre_prepare_and_digest : pbft.

  Lemma digest_for_pre_prepare_and_similar_entry_and_pre_prepare_implies_same_digests :
    forall e pp d,
      digest_for_pre_prepare d pp = true
      -> similar_entry_and_pre_prepare e pp d = true
      -> entry_and_pre_prepare_have_same_digests e pp.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve digest_for_pre_prepare_and_similar_entry_and_pre_prepare_implies_same_digests : pbft.

  Lemma requests_and_replies_map_none_as :
    forall d,
      requests_and_replies2digest (map (fun r => (r, None)) d)
      = requests2digest d.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Rewrite requests_and_replies_map_none_as : pbft.

  Lemma change_pre_prepare_info_of_entry_preserves_well_formed_log_entry :
    forall e pp,
      entry_and_pre_prepare_have_same_digests e pp
      -> well_formed_log_entry e
      -> well_formed_log_entry (change_pre_prepare_info_of_entry pp e).
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve change_pre_prepare_info_of_entry_preserves_well_formed_log_entry : pbft.

  Lemma pp_info_is_pre_prep_pre_prepare2pp_info :
    forall pp, pp_info_is_pre_prep (pre_prepare2pp_info pp) = true.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Rewrite pp_info_is_pre_prep_pre_prepare2pp_info : pbft.

  Lemma implies_well_formed_log_entry :
    forall pp d,
      digest_for_pre_prepare d pp = true
      -> well_formed_log_entry (pre_prepare2entry pp d).
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve implies_well_formed_log_entry : pbft.

  Lemma well_formed_log_add_new_pre_prepare2log :
    forall pp d L,
      digest_for_pre_prepare d pp = true
      -> well_formed_log L
      -> well_formed_log (add_new_pre_prepare2log pp d L).
  Proof.
    induction L; introv cord wf; simpl in *; tcsp.

    { constructor; simpl; tcsp; eauto 2 with pbft. }

    inversion wf as [|? ? imp wfentry wfL]; subst; clear wf.
    autodimp IHL hyp.
    pbft_dest_all x; auto; constructor; eauto 3 with pbft.

    { introv i j; apply imp in i; autorewrite with pbft in *.
      apply i in j; auto. }

    { introv i j.
      apply entry_in_add_new_pre_prepare2log_implies in i; repndors.
      - apply imp in i; apply i in j; tcsp.
      - allrw similar_entry_and_pre_prepare_true_iff.
        allrw similar_entry_and_pre_prepare_false_iff.
        match goal with
        | [ H : _ <> _ |- _ ] => destruct H; allrw; auto
        end. }
  Qed.
  Hint Resolve well_formed_log_add_new_pre_prepare2log : pbft.

  Lemma check_send_replies_preserves_wf :
    forall slf view keys entryop state sn msgs state',
      check_send_replies slf view keys entryop state sn = (msgs, state')
      -> well_formed_log (log state)
      -> well_formed_log (log state').
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve check_send_replies_preserves_wf : pbft.

  Lemma request_data2view_pre_prepare2request_data :
    forall pp d,
      request_data2view (pre_prepare2request_data pp d)
      = pre_prepare2view pp.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Rewrite request_data2view_pre_prepare2request_data : pbft.

  Lemma request_data2view_prepare2request_data :
    forall p,
      request_data2view (prepare2request_data p)
      = prepare2view p.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Rewrite request_data2view_prepare2request_data : pbft.

  Lemma request_data2digest_pre_prepare2request_data :
    forall pp d,
      request_data2digest (pre_prepare2request_data pp d)
      = d.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Rewrite request_data2digest_pre_prepare2request_data : pbft.

  Lemma digest_for_pre_prepare_pp_info_has_correct_digest :
    forall d pp,
      digest_for_pre_prepare d pp = true
      <-> pp_info_has_correct_digest (pre_prepare2pp_info pp) d = true.
  Proof.
    pbft_brute_force.
  Qed.

  Lemma digest_for_pre_prepare_implies_pp_info_has_correct_digest :
    forall d pp,
      digest_for_pre_prepare d pp = true
      -> pp_info_has_correct_digest (pre_prepare2pp_info pp) d = true.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve digest_for_pre_prepare_implies_pp_info_has_correct_digest : pbft.

  Lemma add_prepare_if_not_enough_preserves_no_repeats :
    forall i preps Fp status preps',
      rt_rep (Fp tt) = i
      -> add_prepare_if_not_enough i preps Fp = (status, preps')
      -> no_repeats (map rt_rep preps)
      -> no_repeats (map rt_rep preps').
  Proof.
    pbft_brute_force.
    constructor; auto.
    allrw in_list_rep_toks_false_iff.
    introv j.
    apply in_map_iff in j; exrepnd.
    discover; tcsp.
  Qed.

  Lemma add_commit_if_prepared_preserves_no_repeats :
    forall i nfo L comms Fc status comms',
      rt_rep (Fc tt) = i
      -> add_commit_if_prepared i nfo L comms Fc = (status, comms')
      -> no_repeats (map rt_rep comms)
      -> no_repeats (map rt_rep comms').
  Proof.
    pbft_brute_force.
    constructor; auto.
    allrw in_list_rep_toks_false_iff.
    introv j.
    apply in_map_iff in j; exrepnd.
    discover; tcsp.
  Qed.

  Lemma in_add_prepare_if_not_enough_implies :
    forall i preps Fp status preps' x,
      add_prepare_if_not_enough i preps Fp = (status, preps')
      -> In x preps'
      -> In x preps \/ x = Fp tt.
  Proof.
    pbft_brute_force.
  Qed.

  Lemma in_commit_if_prepared_implies :
    forall i nfo L comms Fc status comms' x,
      add_commit_if_prepared i nfo L comms Fc = (status, comms')
      -> In x comms'
      -> In x comms \/ x = Fc tt.
  Proof.
    pbft_brute_force.
  Qed.

  Lemma fill_out_pp_info_with_prepare_preserves_well_formed_log :
    forall i e pp Fp Fc x d,
      rt_rep (Fp tt) = i
      -> rt_rep (Fc tt) = i
      -> i <> PBFTprimary (pre_prepare2view pp)
      -> digest_for_pre_prepare d pp = true
      -> similar_entry_and_pre_prepare e pp d = true
      -> fill_out_pp_info_with_prepare i e pp Fp Fc = Some x
      -> well_formed_log_entry e
      -> well_formed_log_entry (gi_entry x).
  Proof.
    introv eqpi eqci di dfp sim fill wf.
    unfold fill_out_pp_info_with_prepare in fill.
    destruct e; simpl in *.
    destruct log_entry_pre_prepare_info; ginv.
    smash_pbft.

    destruct wf as [nrepp nrepc nip cord nfo]; simpl in *; GC.

    split; simpl; autorewrite with pbft; tcsp.

    - eapply add_prepare_if_not_enough_preserves_no_repeats;[|eauto|]; auto.

    - eapply add_commit_if_prepared_preserves_no_repeats;[|eauto|]; auto.

    - introv j; apply in_map_iff in j; exrepnd.
      eapply in_add_prepare_if_not_enough_implies in j0;[|eauto].
      destruct nip; apply in_map_iff.
      destruct j0 as [j0|j0]; tcsp;[exists x; tcsp|].
      subst; smash_pbft.

    - subst; smash_pbft.
  Qed.

  Lemma add_new_pre_prepare_and_prepare2log_preserve_wf :
    forall i L pp d Fp Fc giop K,
      rt_rep (Fp tt) = i
      -> rt_rep (Fc tt) = i
      -> i <> PBFTprimary (pre_prepare2view pp)
      -> digest_for_pre_prepare d pp = true
      -> add_new_pre_prepare_and_prepare2log i L pp d Fp Fc = (giop, K)
      -> well_formed_log L
      -> well_formed_log K.
  Proof.
    induction L; introv eqpi eqci nprim dfp h q; simpl in *; tcsp.

    {
      pbft_simplifier.
      constructor; simpl; tcsp.
      unfold MkNewLogEntryWithPrepare.
      constructor; simpl; tcsp; autorewrite with pbft in *; eauto 2 with pbft.
      allrw; tcsp.
    }

    pbft_dest_all x.

    {
      inversion q as [|? ? imp wfe wfL]; subst; clear q.
      constructor; auto.

      { introv k; apply imp in k.
        destruct a; simpl in *; pbft_dest_all x. }

      match goal with
      | [ H : context[fill_out_pp_info_with_prepare] |- _ ] => rename H into fill
      end.
      eapply fill_out_pp_info_with_prepare_preserves_well_formed_log;
        try (exact fill); try (exact dfp); auto.
    }

    {
      inversion q as [|? ? imp wfe wfL]; subst; clear q.
      match goal with
      | [ H : add_new_pre_prepare_and_prepare2log _ _ _ _ _ _ = _ |- _ ] =>
        applydup IHL in H; auto
      end.
      constructor; auto.
      introv k.

      match goal with
      | [ H : add_new_pre_prepare_and_prepare2log _ _ _ _ _ _ = _ |- _ ] =>
        eapply add_new_pre_prepare_and_prepare2log_preserves_request_data in H
      end;[|eauto].
      repndors; exrepnd.

      - match goal with
        | [ H : In _ L |- _ ] => apply imp in H
        end.
        introv j; apply Heqx0; allrw; auto.

      - introv j.
        allrw similar_entry_and_pre_prepare_true_iff.
        allrw similar_entry_and_pre_prepare_false_iff.
        destruct Heqx; allrw; auto.
    }
  Qed.
  Hint Resolve add_new_pre_prepare_and_prepare2log_preserve_wf : pbft.

  Lemma rt_rep_prepare2rep_toks :
    forall p, rt_rep (prepare2rep_toks p) = prepare2sender p.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Rewrite rt_rep_prepare2rep_toks : pbft.

  Lemma add_prepare_if_not_enough_preserves_not_null :
    forall i preps Fc status preps',
      add_prepare_if_not_enough i preps Fc = (status, preps')
      -> ~null preps
      -> ~null preps'.
  Proof.
    pbft_brute_force.
  Qed.

  Lemma add_commit_if_prepared_preserves_not_null :
    forall i nfo L comms Fc status comms',
      add_commit_if_prepared i nfo L comms Fc = (status, comms')
      -> ~null comms
      -> ~null comms'.
  Proof.
    pbft_brute_force.
  Qed.

  Lemma add_prepare2entry_preserves_well_formed_log_entry :
    forall i e p Fc x,
      rt_rep (Fc tt) = i
      -> is_prepare_for_entry e p = true
      -> prepare2sender p <> PBFTprimary (prepare2view p)
      -> add_prepare2entry i e p Fc = Some x
      -> well_formed_log_entry e
      -> well_formed_log_entry (gi_entry x).
  Proof.
    introv eqci isp nprim add wf.
    unfold add_prepare2entry in add.
    destruct e; smash_pbft.

    destruct wf as [nrepp nrepc nip cord nfo]; simpl in *; GC.

    split; simpl; autorewrite with pbft; tcsp.

    - eapply add_prepare_if_not_enough_preserves_no_repeats;[|eauto|]; auto.
      simpl; autorewrite with pbft; auto.

    - eapply add_commit_if_prepared_preserves_no_repeats;[|eauto|]; auto.

    - introv j; apply in_map_iff in j; exrepnd.
      eapply in_add_prepare_if_not_enough_implies in j0;[|eauto].
      destruct nip; apply in_map_iff.
      destruct j0 as [j0|j0]; tcsp;[exists x; tcsp|].
      subst.
      unfold is_prepare_for_entry in *; simpl in *.
      unfold eq_request_data in *; smash_pbft; tcsp.

    - repndors; tcsp.

      + right; left; eapply add_prepare_if_not_enough_preserves_not_null;[eauto|]; auto.

      + right; right; eapply add_commit_if_prepared_preserves_not_null;[eauto|]; auto.
  Qed.

  Lemma add_new_prepare2log_preserve_wf :
    forall i L p Fc giop K,
      rt_rep (Fc tt) = i
      -> prepare2sender p <> PBFTprimary (prepare2view p)
      -> add_new_prepare2log i L p Fc = (giop, K)
      -> well_formed_log L
      -> well_formed_log K.
  Proof.
    induction L; introv eqci nprim h q; simpl in *; tcsp.

    {
      pbft_simplifier.
      constructor; simpl; tcsp.
      unfold MkNewLogEntryFromPrepare.
      constructor; simpl; tcsp; autorewrite with pbft in *; eauto 2 with pbft.
      { introv xx; repndors; tcsp. }
      { right; left; unfold null; introv xx; inversion xx. }
    }

    pbft_dest_all x.

    {
      inversion q as [|? ? imp wfe wfL]; subst; clear q.
      constructor; auto.

      { introv i; apply imp in i.
        destruct a; simpl in *; pbft_dest_all x. }

      match goal with
      | [ H : context[add_prepare2entry] |- _ ] => rename H into add
      end.
      eapply add_prepare2entry_preserves_well_formed_log_entry;
        try (exact add); tcsp.
    }

    { inversion q as [|? ? imp wfe wfL]; subst; clear q.
      match goal with
      | [ H : add_new_prepare2log _ _ _ _ = _ |- _ ] =>
        applydup IHL in H; auto
      end.
      constructor; auto.
      introv i.

      match goal with
      | [ H : add_new_prepare2log _ _ _ _ = _ |- _ ] =>
        eapply add_new_prepare2log_preserves_request_data in H
      end;[|eauto].
      repndors; exrepnd.

      - match goal with
        | [ H : In _ L |- _ ] => apply imp in H
        end.
        introv j; apply Heqx0; allrw; auto.

      - introv j.
        allrw is_prepare_for_entry_true_iff.
        allrw is_prepare_for_entry_false_iff.
        destruct Heqx; allrw; auto. }
  Qed.
  Hint Resolve add_new_prepare2log_preserve_wf : pbft.

  Lemma rt_rep_commit2rep_toks :
    forall c, rt_rep (commit2rep_toks c) = commit2sender c.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Rewrite rt_rep_commit2rep_toks : pbft.

  Lemma add_commit2entry_preserves_well_formed_log :
    forall a x c,
      is_commit_for_entry a c = true
      -> add_commit2entry a c = Some x
      -> well_formed_log_entry a
      -> well_formed_log_entry x.
  Proof.
    introv isc add wf.
    unfold add_commit2entry in add.
    destruct a; smash_pbft.
    unfold is_commit_for_entry, eq_request_data in isc; simpl in *.
    smash_pbft.

    destruct wf as [nrepp nrepc nip cord nfo]; simpl in *; GC.

    split; simpl; autorewrite with pbft; tcsp.

    - constructor; auto.
      allrw in_list_rep_toks_false_iff.
      introv j.
      apply in_map_iff in j; exrepnd.
      discover; tcsp.

    - right; right; intro xx.
      inversion xx.
  Qed.
  Hint Resolve add_commit2entry_preserves_well_formed_log : pbft.

  Lemma add_new_commit2log_preserve_wf :
    forall L c giop K,
      add_new_commit2log L c = (giop, K)
      -> well_formed_log L
      -> well_formed_log K.
  Proof.
    induction L; introv h q; simpl in *; tcsp.

    {
      pbft_simplifier.
      constructor; simpl; tcsp.
      unfold MkNewLogEntryFromCommit.
      constructor; simpl; tcsp; autorewrite with pbft in *; eauto 2 with pbft.
      right; right; intro n; inversion n.
    }

    pbft_dest_all x.

    {
      inversion q as [|? ? imp wfe wfL]; subst; clear q.
      constructor; auto; eauto 2 with pbft.

      introv i; apply imp in i.
      destruct a; simpl in *; pbft_dest_all x.
    }

    { inversion q as [|? ? imp wfe wfL]; subst; clear q.
      match goal with
      | [ H : add_new_commit2log _ _ = _ |- _ ] =>
        applydup IHL in H; auto
      end.
      constructor; auto.
      introv i.

      match goal with
      | [ H : add_new_commit2log _ _ = _ |- _ ] =>
        eapply add_new_commit2log_preserves_request_data in H
      end;[|eauto].
      repndors; exrepnd.

      - match goal with
        | [ H : In _ L |- _ ] => apply imp in H
        end.
        introv j; apply Heqx0; allrw; auto.

      - introv j.
        allrw is_commit_for_entry_true_iff.
        allrw is_commit_for_entry_false_iff.
        destruct Heqx; allrw; auto. }
  Qed.
  Hint Resolve add_new_commit2log_preserve_wf : pbft.

  Lemma implies_well_formed_log_clear_log_checkpoint :
    forall L sn,
      well_formed_log L
      -> well_formed_log (clear_log_checkpoint L sn).
  Proof.
    induction L; introv wf; simpl in *; auto.
    inversion wf as [|? ? imp wfL]; subst; clear wf.
    pbft_dest_all x; constructor; tcsp.
    introv i.
    apply in_clear_log_checkpoint_implies in i.
    apply imp in i; auto.
  Qed.
  Hint Resolve implies_well_formed_log_clear_log_checkpoint : pbft.

  Lemma check_stable_preserves_wf :
    forall slf state entryop state',
      check_stable slf state entryop = Some state'
      -> well_formed_log (log state)
      -> well_formed_log (log state').
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve check_stable_preserves_wf : pbft.

  Lemma check_broadcast_checkpoint_preserves_wf :
    forall slf sn vn keys state state' msgs,
      check_broadcast_checkpoint slf sn vn keys state = (state', msgs)
      -> well_formed_log (log state)
      -> well_formed_log (log state').
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve check_broadcast_checkpoint_preserves_wf : pbft.

  Lemma change_entry_preserves_wf :
    forall L entry,
      well_formed_log_entry entry
      -> well_formed_log L
      -> well_formed_log (change_entry L entry).
  Proof.
    induction L; introv wfe wf; simpl in *; auto.
    inversion wf as [|? ? imp wfa wfL]; subst; clear wf.
    pbft_dest_all x; auto; constructor; auto; try (introv i).

    - apply imp in i.
      allrw similar_entry_true_iff.
      introv xx; destruct i; allrw; auto.

    - allrw similar_entry_false_iff.
      apply in_change_entry_implies in i; repndors; subst; tcsp.
  Qed.
  Hint Resolve change_entry_preserves_wf : pbft.

  Lemma change_log_entry_preserves_wf :
    forall state entry,
      well_formed_log_entry entry
      -> well_formed_log (log state)
      -> well_formed_log (log (change_log_entry state entry)).
  Proof.
    introv; apply change_entry_preserves_wf.
  Qed.
  Hint Resolve change_log_entry_preserves_wf : pbft.

  Lemma requests_and_replies2digest_combine_replies :
    forall reqs R,
      requests_and_replies2digest (combine_replies reqs R)
      = requests_and_replies2digest reqs.
  Proof.
    introv.
    unfold requests_and_replies2digest.
    f_equal.
    revert R.

    induction reqs; introv; simpl; repnd; auto; destruct R; tcsp; simpl.
    allrw; auto.
  Qed.
  Hint Rewrite requests_and_replies2digest_combine_replies : pbft.

  Lemma implies_well_formed_log_entry_add_replies2entry :
    forall e R,
      well_formed_log_entry e
      -> well_formed_log_entry (add_replies2entry e R).
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve implies_well_formed_log_entry_add_replies2entry : pbft.

  Lemma find_entry_implies_in :
    forall L n e,
      find_entry L n = Some e
      -> In e L.
  Proof.
    induction L; introv h; simpl in *; ginv.
    smash_pbft.
  Qed.
  Hint Resolve find_entry_implies_in : pbft.

  Lemma well_formed_log_entry_if_in :
    forall e L,
      In e L
      -> well_formed_log L
      -> well_formed_log_entry e.
  Proof.
    induction L; introv i wf; simpl in *; tcsp.
    inversion wf as [|? ? imp wfa wfL]; subst; clear wf.
    repndors; subst; tcsp.
  Qed.
  Hint Resolve well_formed_log_entry_if_in : pbft.

  Lemma execute_requests_preserves_wf :
    forall i v keys rdy state msgs rdy' state',
      execute_requests i v keys state rdy = (msgs, rdy', state')
      -> well_formed_log (log state)
      -> well_formed_log (log state').
  Proof.
    induction rdy; introv h wf; simpl in *.

    { inversion h; subst; clear h; auto. }

    fold DirectedMsgs in *.
    pbft_dest_all x.

    match goal with
    | [ H : check_broadcast_checkpoint _ _ _ _ _ = _ |- _ ] =>
      apply check_broadcast_checkpoint_preserves_wf in H
    end; auto.

    apply change_log_entry_preserves_wf; autorewrite with pbft; eauto 4 with pbft.
  Qed.
  Hint Resolve execute_requests_preserves_wf : pbft.

  Lemma find_and_execute_requests_preserves_wf :
    forall i v keys state msgs state',
      find_and_execute_requests i v keys state = (msgs, state')
      -> well_formed_log (log state)
      -> well_formed_log (log state').
  Proof.
    introv h wf.
    unfold find_and_execute_requests in h.
    pbft_dest_all x.
    apply execute_requests_preserves_wf in Heqx; auto.
  Qed.
  Hint Resolve find_and_execute_requests_preserves_wf : pbft.

  Definition well_formed_pre_prepare_and_digest (x : Pre_prepare * PBFTdigest) :=
    digest_for_pre_prepare (snd x) (fst x).

  Definition well_formed_pre_prepares (P : list (Pre_prepare * PBFTdigest)) :=
    forallb well_formed_pre_prepare_and_digest P.

  Lemma log_pre_prepares_preserves_wf :
    forall P lwm L,
      well_formed_pre_prepares P = true
      -> well_formed_log L
      -> well_formed_log (log_pre_prepares L lwm P).
  Proof.
    induction P; introv wfp wf; simpl in *; auto.
    allrw andb_true; repnd.
    smash_pbft.
  Qed.
  Hint Resolve log_pre_prepares_preserves_wf : pbft.

  Lemma rt_rep_pre_prepare2rep_toks :
    forall i keys pp d,
      rt_rep (pre_prepare2rep_toks_of_commit i keys pp d) = i.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Rewrite rt_rep_pre_prepare2rep_toks : pbft.

  Definition pre_prepare_and_digest_not_from_primary
             (i : Rep)
             (x : Pre_prepare * PBFTdigest) :=
    if rep_deq i (PBFTprimary (pre_prepare2view (fst x))) then false
    else true.

  Definition pre_prepares_and_digests_not_from_primary
             (i : Rep)
             (P : list (Pre_prepare * PBFTdigest)) :=
    forallb (pre_prepare_and_digest_not_from_primary i) P.

  Lemma add_prepare_to_log_from_new_view_pre_prepare_preserves_wf :
    forall slf state ppd state' msgs,
      add_prepare_to_log_from_new_view_pre_prepare slf state ppd = (state', msgs)
      -> well_formed_pre_prepare_and_digest ppd = true
      -> pre_prepare_and_digest_not_from_primary slf ppd = true
      -> well_formed_log (log state)
      -> well_formed_log (log state').
  Proof.
    introv h wfppd nprim wf; unfold add_prepare_to_log_from_new_view_pre_prepare in h.
    smash_pbft.
    eapply check_send_replies_preserves_wf;[eauto|].
    simpl.
    eapply add_new_pre_prepare_and_prepare2log_preserve_wf;
      [| | | |eauto|]; simpl; auto; autorewrite with pbft; auto.
    unfold pre_prepare_and_digest_not_from_primary in nprim; simpl in *; smash_pbft.
  Qed.
  Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_wf : pbft.

  Lemma add_prepares_to_log_from_new_view_pre_prepares_preserves_wf :
    forall slf pps state state' msgs,
      add_prepares_to_log_from_new_view_pre_prepares slf state pps = (state', msgs)
      -> well_formed_pre_prepares pps = true
      -> pre_prepares_and_digests_not_from_primary slf pps = true
      -> well_formed_log (log state)
      -> well_formed_log (log state').
  Proof.
    induction pps; introv h wfps nprim wf; simpl in *; pbft_simplifier; auto.
    pbft_dest_all x.
    eapply IHpps; eauto 3 with pbft.
  Qed.
  Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_wf : pbft.

  Lemma log_new_view_state_preserves_wf :
    forall state nv,
      well_formed_log (log state)
      -> well_formed_log (log (log_new_view_state state nv)).
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve log_new_view_state_preserves_wf : pbft.

  Lemma log_pre_prepares_of_new_view_preserves_wf :
    forall state P,
      well_formed_pre_prepares P = true
      -> well_formed_log (log state)
      -> well_formed_log (log (log_pre_prepares_of_new_view state P)).
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve log_pre_prepares_of_new_view_preserves_wf : pbft.

  Lemma is_primary_false_iff_diff_primary :
    forall v i, is_primary v i = false <-> i <> PBFTprimary v.
  Proof.
    introv; unfold is_primary; smash_pbft; split; intro h; tcsp.
  Qed.

  Lemma is_primary_false_implies_diff_primary :
    forall v i, is_primary v i = false -> i <> PBFTprimary v.
  Proof.
    introv h; apply is_primary_false_iff_diff_primary in h; auto.
  Qed.
  Hint Resolve is_primary_false_implies_diff_primary : pbft.

  Lemma rt_rep_prepare2rep_toks_of_commit :
    forall i k p,
      rt_rep (prepare2rep_toks_of_commit i k p) = i.
  Proof.
    pbft_brute_force.
  Qed.
  Hint Rewrite rt_rep_prepare2rep_toks_of_commit : pbft.

  Lemma create_new_prepare_messages_implies_well_formed_pre_prepare_and_digest :
    forall L v keys C OP NP pp d,
      wf_prepared_infos C = true
      -> create_new_prepare_messages L v keys C = (OP, NP)
      -> In (pp,d) (OP ++ NP)
      -> digest_for_pre_prepare d pp = true.
  Proof.
    induction L; introv wf create i; simpl in *; pbft_simplifier; simpl in *; tcsp.
    smash_pbft; repndors; subst; tcsp; eauto 2 with pbft.
    apply in_app_cons_implies_in_cons_app in i; repndors; subst; eauto 2 with pbft.
  Qed.
  Hint Resolve create_new_prepare_messages_implies_well_formed_pre_prepare_and_digest : pbft.

  Lemma check_broadcast_new_view_implies_well_formed_pre_prepares :
    forall i state entry nv entry' OP NP,
      check_broadcast_new_view i state entry = Some (nv, entry', OP, NP)
      -> well_formed_pre_prepares (OP ++ NP) = true.
  Proof.
    introv check.
    unfold check_broadcast_new_view in check; smash_pbft.
    unfold well_formed_pre_prepares.
    rewrite forallb_forall.
    introv i.
    repnd.
    unfold well_formed_pre_prepare_and_digest; simpl.
    unfold view_changed_entry in *; smash_pbft.
    eapply create_new_prepare_messages_implies_well_formed_pre_prepare_and_digest;
      eauto; eauto 2 with pbft.
  Qed.
  Hint Resolve check_broadcast_new_view_implies_well_formed_pre_prepares : pbft.

  Lemma well_formed_pre_prepares_of_new_view :
    forall nv,
      well_formed_pre_prepares
        (map add_digest (new_view2oprep nv ++ new_view2nprep nv)) = true.
  Proof.
    introv.
    unfold well_formed_pre_prepares.
    rewrite forallb_forall; introv i.
    allrw in_map_iff; exrepnd.
    unfold add_digest in *; ginv.
    unfold well_formed_pre_prepare_and_digest; simpl.
    eauto 2 with pbft.
  Qed.
  Hint Resolve well_formed_pre_prepares_of_new_view : pbft.

  Lemma correct_new_view_implies_pre_prepare2view_eq_new_view2view :
    forall nv pp,
      correct_new_view nv = true
      -> In pp (new_view2oprep nv ++ new_view2nprep nv)
      -> pre_prepare2view pp = new_view2view nv.
  Proof.
    introv cor i.
    unfold correct_new_view in cor; smash_pbft.
    allrw forallb_forall.
    allrw in_app_iff; repndors; discover.

    - unfold correct_new_view_opre_prepare_op in *.
      smash_pbft.
      unfold correct_new_view_opre_prepare in *; smash_pbft.

    - unfold correct_new_view_npre_prepare_op in *.
      smash_pbft.
      unfold correct_new_view_npre_prepare in *; smash_pbft.
  Qed.

  Lemma correct_new_view_implies_from_primary :
    forall nv,
      correct_new_view nv = true
      -> new_view2sender nv = PBFTprimary (new_view2view nv).
  Proof.
    pbft_brute_force.
  Qed.

  Lemma log_checkpoint_cert_from_new_view_preserves_well_formed_log :
    forall i s1 v n C S s2 cop,
      log_checkpoint_cert_from_new_view i s1 v n C S = (s2, cop)
      -> well_formed_log (log s1)
      -> well_formed_log (log s2).
  Proof.
    introv h wf.
    apply log_checkpoint_cert_from_new_view_preserves_log in h.
    allrw <- ; auto.
  Qed.
  Hint Resolve log_checkpoint_cert_from_new_view_preserves_well_formed_log : pbft.

  Lemma correct_new_view_implies_pre_prepares_and_digests_not_from_primary :
    forall i v,
      new_view2sender v <> i
      -> correct_new_view v = true
      -> pre_prepares_and_digests_not_from_primary
           i (map add_digest (new_view2oprep v ++ new_view2nprep v)) = true.
  Proof.
    introv d cor.
    unfold pre_prepares_and_digests_not_from_primary.
    rewrite forallb_forall.
    introv j.
    allrw in_map_iff; exrepnd.
    unfold add_digest in j1; ginv.
    unfold pre_prepare_and_digest_not_from_primary; simpl.

    dup cor as cor'.
    eapply correct_new_view_implies_pre_prepare2view_eq_new_view2view in cor';[|eauto].
    applydup correct_new_view_implies_from_primary in cor.
    allrw.
    smash_pbft.
  Qed.
  Hint Resolve correct_new_view_implies_pre_prepares_and_digests_not_from_primary : pbft.

  Lemma update_state_new_view_preserves_well_formed_log :
    forall i s1 nv s2 msgs,
      update_state_new_view i s1 nv = (s2, msgs)
      -> well_formed_log (log s1)
      -> well_formed_log (log s2).
  Proof.
    pbft_brute_force.
  Qed.
  Hint Resolve update_state_new_view_preserves_well_formed_log : pbft.

  Lemma check_send_replies_update_log_preserves_wf :
    forall slf view keys entryop state L sn msgs state',
      check_send_replies slf view keys entryop (update_log state L) sn = (msgs, state')
      -> well_formed_log L
      -> well_formed_log (log state').
  Proof.
    introv check wf.
    eapply check_send_replies_preserves_wf;[eauto|].
    simpl; auto.
  Qed.
  Hint Resolve check_send_replies_update_log_preserves_wf : pbft.

  Lemma add_new_pre_prepare_and_prepare2log_preserve_wf2 :
    forall i keys L pp d giop K,
      i <> PBFTprimary (pre_prepare2view pp)
      -> digest_for_pre_prepare d pp = true
      -> add_new_pre_prepare_and_prepare2log
           i L pp d
           (fun _ => pre_prepare2rep_toks_of_prepare i keys pp (pre_prepare2digest pp))
           (fun _ => pre_prepare2rep_toks_of_commit i keys pp (pre_prepare2digest pp))
         = (giop, K)
      -> well_formed_log L
      -> well_formed_log K.
  Proof.
    introv diff digest add wf.
    eapply add_new_pre_prepare_and_prepare2log_preserve_wf in add;
      autorewrite with pbft; auto.
  Qed.
  Hint Resolve add_new_pre_prepare_and_prepare2log_preserve_wf2 : pbft.

  Lemma implies_diff_primary :
    forall i j v w,
      i <> j
      -> j = PBFTprimary w
      -> v = w
      -> i <> PBFTprimary v.
  Proof.
    introv h q z; subst; auto.
  Qed.
  Hint Resolve implies_diff_primary : pbft.

  Lemma add_new_prepare2log_preserve_wf2 :
    forall i keys L p giop K,
      prepare2sender p <> PBFTprimary (prepare2view p)
      -> add_new_prepare2log i L p (fun _ => prepare2rep_toks_of_commit i keys p) = (giop, K)
      -> well_formed_log L
      -> well_formed_log K.
  Proof.
    introv diff add wf.
    eapply add_new_prepare2log_preserve_wf; try exact add;
      simpl; autorewrite with pbft; auto.
  Qed.
  Hint Resolve add_new_prepare2log_preserve_wf2 : pbft.

  Lemma well_formed_log_log_update_view :
    forall s v,
      well_formed_log (log s)
      -> well_formed_log (log (update_view s v)).
  Proof.
    tcsp.
  Qed.
  Hint Resolve well_formed_log_log_update_view : pbft.

  Lemma well_formed_log_log_change_sequence_number :
    forall s n,
      well_formed_log (log s)
      -> well_formed_log (log (change_sequence_number s n)).
  Proof.
    tcsp.
  Qed.
  Hint Resolve well_formed_log_log_change_sequence_number : pbft.

  Lemma check_stable_update_checkpoint_state_preserves_wf :
    forall slf state cs entryop state',
      check_stable slf (update_checkpoint_state state cs) entryop = Some state'
      -> well_formed_log (log state)
      -> well_formed_log (log state').
  Proof.
    introv h wf.
    eapply check_stable_preserves_wf;[eauto|].
    simpl; eauto 2 with pbft.
  Qed.
  Hint Resolve check_stable_update_checkpoint_state_preserves_wf : pbft.

  Lemma implies_well_formed_log_log_log_pre_prepares_of_new_view :
    forall s P,
      well_formed_log (log_pre_prepares (log s) (low_water_mark s) P)
      -> well_formed_log (log (log_pre_prepares_of_new_view s P)).
  Proof.
    tcsp.
  Qed.
  Hint Resolve implies_well_formed_log_log_log_pre_prepares_of_new_view : pbft.

  Lemma implies_well_formed_log_log_log_new_view_and_entry_state :
    forall s a b P,
      well_formed_log
        (log_pre_prepares
           (log s)
           (low_water_mark (log_new_view_and_entry_state s a b))
           P)
      -> well_formed_log
           (log_pre_prepares
              (log (log_new_view_and_entry_state s a b))
              (low_water_mark (log_new_view_and_entry_state s a b))
              P).
  Proof.
    tcsp.
  Qed.
  Hint Resolve implies_well_formed_log_log_log_new_view_and_entry_state : pbft.

  Lemma well_formed_log_pre_prepare2entry :
    forall v n r k,
      well_formed_log
        [pre_prepare2entry (mk_auth_pre_prepare v n r k)
                           (requests2digest r)].
  Proof.
    introv.
    constructor; simpl; tcsp.
    constructor; simpl; tcsp.
    unfold requests_and_replies2digest; allrw map_map.
    unfold same_digests; smash_pbft.
  Qed.
  Hint Resolve well_formed_log_pre_prepare2entry : pbft.

  Lemma well_formed_log_MkNewLogEntryWithPrepare :
    forall p i keys,
      is_primary (pre_prepare2view p) i = false
      -> well_formed_log
           [MkNewLogEntryWithPrepare
              p
              (pre_prepare2digest p)
              (pre_prepare2rep_toks_of_prepare i keys p (pre_prepare2digest p))].
  Proof.
    introv nisprim.
    constructor; simpl; tcsp.
    constructor; simpl; tcsp;
      try (complete (right; left; eauto 3 with list));
      try (complete (destruct p, b; simpl;
                     unfold requests_and_replies2digest; allrw map_map;
                     unfold same_digests; smash_pbft)).
    autorewrite with pbft.
    unfold is_primary in nisprim; smash_pbft.
    introv xx; repndors; tcsp.
  Qed.
  Hint Resolve well_formed_log_MkNewLogEntryWithPrepare : pbft.

  Lemma well_formed_log_MkNewLogEntryFromPrepare :
    forall p,
      is_primary (prepare2view p) (prepare2sender p) = false
      -> well_formed_log
           [MkNewLogEntryFromPrepare p].
  Proof.
    introv nisprim.
    constructor; simpl; tcsp.
    constructor; simpl; tcsp;
      try (complete (right; left; eauto 3 with list));
      try (complete (destruct p, b; simpl;
                     unfold requests_and_replies2digest; allrw map_map;
                     unfold same_digests; smash_pbft)).
    autorewrite with pbft.
    unfold is_primary in nisprim; smash_pbft.
    introv xx; repndors; tcsp.
  Qed.
  Hint Resolve well_formed_log_MkNewLogEntryFromPrepare : pbft.

  Lemma well_formed_log_MkNewLogEntryFromCommit :
    forall c, well_formed_log [MkNewLogEntryFromCommit c].
  Proof.
    introv.
    constructor; simpl; tcsp.
    constructor; simpl; tcsp;
      try (complete (right; right; eauto 3 with list)).
  Qed.
  Hint Resolve well_formed_log_MkNewLogEntryFromCommit : pbft.

  Lemma CheckBCastNewView2entry_initial :
    forall c, CheckBCastNewView2entry c initial_view_change_state = None.
  Proof.
    introv.
    unfold CheckBCastNewView2entry; destruct c; simpl.
    unfold initial_view_change_state.
    destruct i; simpl; auto.
  Qed.
  Hint Rewrite CheckBCastNewView2entry_initial : pbft.

  Lemma update_state_new_view_log_new_view_state_preserves_well_formed_log :
    forall i s1 nv s2 msgs,
      update_state_new_view i (log_new_view_state s1 nv) nv = (s2, msgs)
      -> well_formed_log (log s1)
      -> well_formed_log (log s2).
  Proof.
    introv upd wf; eauto 3 with pbft.
  Qed.
  Hint Resolve update_state_new_view_log_new_view_state_preserves_well_formed_log : pbft.

  Lemma well_formed_log_log_initial_state :
    forall i, well_formed_log (log (initial_state i)).
  Proof.
    tcsp.
  Qed.
  Hint Resolve well_formed_log_log_initial_state : pbft.

  Lemma well_formed_log_log_check_one_stable :
    forall i s l,
      well_formed_log (log s)
      -> well_formed_log (log (check_one_stable i s l)).
  Proof.
    induction l; introv wf; simpl in *; smash_pbft.
  Qed.
  Hint Resolve well_formed_log_log_check_one_stable : pbft.

  Lemma log_is_well_formed_on_event :
    forall i (eo : EventOrdering) e st,
      state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> well_formed_log (log st).
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers4 smash_pbft_ind6_6.
  Qed.
  Hint Resolve log_is_well_formed_on_event : pbft.

  Lemma log_is_well_formed :
    forall i (eo : EventOrdering) e st,
      state_sm_before_event (PBFTreplicaSM i) e = Some st
      -> well_formed_log (log st).
  Proof.
    introv eqst.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d|d]; ginv; subst; simpl in *; eauto 3 with pbft.
  Qed.
  Hint Resolve log_is_well_formed : pbft.

End PBFTwell_formed_log.


Hint Resolve well_formed_log_add_new_pre_prepare2log : pbft.
Hint Resolve check_send_replies_preserves_wf : pbft.
Hint Resolve add_new_pre_prepare_and_prepare2log_preserve_wf : pbft.
Hint Resolve add_new_prepare2log_preserve_wf : pbft.
Hint Resolve add_new_commit2log_preserve_wf : pbft.
Hint Resolve implies_well_formed_log_clear_log_checkpoint : pbft.
Hint Resolve check_stable_preserves_wf : pbft.
Hint Resolve check_broadcast_checkpoint_preserves_wf : pbft.
Hint Resolve change_entry_preserves_wf : pbft.
Hint Resolve change_log_entry_preserves_wf : pbft.
Hint Resolve execute_requests_preserves_wf : pbft.
Hint Resolve find_and_execute_requests_preserves_wf : pbft.
Hint Resolve log_pre_prepares_preserves_wf : pbft.
Hint Resolve add_prepare_to_log_from_new_view_pre_prepare_preserves_wf : pbft.
Hint Resolve add_prepares_to_log_from_new_view_pre_prepares_preserves_wf : pbft.
Hint Resolve log_new_view_state_preserves_wf : pbft.
Hint Resolve log_pre_prepares_of_new_view_preserves_wf : pbft.
Hint Resolve check_stable_update_checkpoint_state_preserves_wf : pbft.
Hint Resolve CheckBCastNewView2entry_some_implies : pbft.
Hint Resolve log_checkpoint_cert_from_new_view_preserves_well_formed_log : pbft.
Hint Resolve implies_well_formed_log_clear_log_checkpoint : pbft.
Hint Resolve correct_new_view_implies_pre_prepares_and_digests_not_from_primary : pbft.
Hint Resolve well_formed_pre_prepares_of_new_view : pbft.
Hint Resolve update_state_new_view_preserves_well_formed_log : pbft.
Hint Resolve check_broadcast_new_view_implies_well_formed_pre_prepares : pbft.
Hint Resolve check_send_replies_update_log_preserves_wf : pbft.
Hint Resolve add_new_pre_prepare_and_prepare2log_preserve_wf2 : pbft.
Hint Resolve implies_diff_primary : pbft.
Hint Resolve add_new_prepare2log_preserve_wf2 : pbft.
Hint Resolve well_formed_log_log_update_view : pbft.
Hint Resolve well_formed_log_log_change_sequence_number : pbft.
Hint Resolve implies_well_formed_log_log_log_pre_prepares_of_new_view : pbft.
Hint Resolve implies_well_formed_log_log_log_new_view_and_entry_state : pbft.
Hint Resolve well_formed_log_pre_prepare2entry : pbft.
Hint Resolve well_formed_log_MkNewLogEntryWithPrepare : pbft.
Hint Resolve well_formed_log_MkNewLogEntryFromPrepare : pbft.
Hint Resolve well_formed_log_MkNewLogEntryFromCommit : pbft.
Hint Resolve update_state_new_view_log_new_view_state_preserves_well_formed_log : pbft.
Hint Resolve log_is_well_formed : pbft.
Hint Resolve log_is_well_formed_on_event : pbft.
Hint Resolve well_formed_log_log_initial_state : pbft.
Hint Resolve well_formed_log_log_check_one_stable : pbft.


Hint Resolve select_some_implies_in : list.


Hint Rewrite @rt_rep_pre_prepare2rep_toks : pbft.
Hint Rewrite @CheckBCastNewView2entry_initial : pbft.
Hint Rewrite @requests_and_replies_map_none_as : pbft.
Hint Rewrite @eq_request_data_true : pbft.
