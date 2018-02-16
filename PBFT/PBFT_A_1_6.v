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


Require Export PBFTin_log.
Require Export PBFTcommit_in_log_preserves.
Require Export PBFTprepared_is_preserved.
Require Export PBFTprops4.
Require Export PBFTordering.
Require Export PBFTgarbage_collect.


Section PBFT_A_1_6.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma prepared_log_new_view_state :
    forall rd s nv,
      prepared rd (log_new_view_state s nv) = prepared rd s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite prepared_log_new_view_state : pbft.

  Lemma check_one_stable_preserves_commit_in_log :
    forall com i s l,
      well_formed_log (log s)
      -> commit_in_log com (log (check_one_stable i s l)) = true
      -> commit_in_log com (log s) = true.
  Proof.
    induction l; introv wf comm; simpl in *; smash_pbft.
  Qed.
  Hint Resolve check_one_stable_preserves_commit_in_log : pbft.

  Lemma matching_requests_same :
    forall l, matching_requests l l = true.
  Proof.
    induction l; simpl; smash_pbft.
  Qed.
  Hint Rewrite matching_requests_same : pbft.

  Lemma prepared_log_implies_pre_prepare_in_log :
    forall rd L,
      well_formed_log L
      -> prepared_log rd L = true
      ->
      exists pp d,
        pre_prepare_in_log pp d L = true
        /\ pre_prepare2request_data pp d = rd.
  Proof.
    induction L; introv wf prep; simpl in *; smash_pbft;
      inversion wf as [|? ? imp wf1 wf2]; subst; clear wf.

    - unfold is_request_data_for_entry, eq_request_data in *; smash_pbft.
      destruct a; simpl in *; smash_pbft.
      destruct log_entry_pre_prepare_info in *; simpl in *; ginv;[].
      exists (request_data2pre_prepare log_entry_request_data (map fst reqs) auth)
             (request_data2digest log_entry_request_data); simpl.
      destruct log_entry_request_data; simpl in *; smash_pbft.

    - repeat (autodimp IHL hyp);[].
      exrepnd.
      exists pp d; dands; smash_pbft.
      destruct a; simpl in *.
      unfold is_request_data_for_entry, eq_request_data in *; simpl in *; smash_pbft.
  Qed.

  Lemma prepared_higher_than_low_water_mark :
    forall (eo : EventOrdering) e i rd s,
      state_sm_on_event (PBFTreplicaSM i) e = Some s
      -> well_formed_log (log s)
      -> prepared rd s = true
      -> low_water_mark s < request_data2seq rd.
  Proof.
    introv eqst wf prep.
    apply prepared_log_implies_pre_prepare_in_log in prep; auto;[].
    exrepnd; subst; simpl in *.
    eapply pre_prepares_are_between_water_marks_if_in_log in prep0;[|eauto].
    unfold check_between_water_marks in *; smash_pbft.
  Qed.
  Hint Resolve prepared_higher_than_low_water_mark : pbft.

  Lemma prepared_higher_than_low_water_mark_before :
    forall (eo : EventOrdering) e i rd s,
      state_sm_before_event (PBFTreplicaSM i) e = Some s
      -> well_formed_log (log s)
      -> prepared rd s = true
      -> low_water_mark s < request_data2seq rd.
  Proof.
    introv eqst wf prep.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d|d]; ginv; subst; simpl in *; tcsp; eauto 3 with pbft.
  Qed.
  Hint Resolve prepared_higher_than_low_water_mark_before : pbft.

  Lemma implies_prepared_check_one_stable_if_commit :
    forall rd c i s l,
      well_formed_log (log s)
      -> prepared rd s = true
      -> commit_in_log c (log (check_one_stable i s l)) = true
      -> commit2seq c = request_data2seq rd
      -> prepared rd (check_one_stable i s l) = true.
  Proof.
    induction l; introv wf prep com eqseq; simpl in *; smash_pbft.
    unfold check_stable in *; simpl in *; smash_pbft.
    unfold prepared in *; simpl in *.
    apply clear_log_checkpoint_preserves_commit_in_log2 in com; auto; repnd.
    apply clear_log_checkpoint_preserves_prepared_log_reverse; auto.
    rewrite <- eqseq; auto.
  Qed.
  Hint Resolve implies_prepared_check_one_stable_if_commit : pbft.

  (* Invariant 1.6 pg 149 *)
  Lemma PBFT_A_1_6 :
    forall (eo  : EventOrdering)
           (e   : Event)
           (slf : Rep)
           (n   : SeqNum)
           (v   : View)
           (a   : Tokens)
           (d   : PBFTdigest)
           (st  : PBFTstate),
      state_sm_on_event (PBFTreplicaSM slf) e = Some st
      -> commit_in_log (mk_commit v n d slf a) (log st) = true
      -> prepared (request_data v n d) st = true.
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers3 smash_pbft_ind3.

    { (* handle request *)

      assert (prepared (request_data v n d) p = true) as prep' by (smash_pbft_ind ind).
      clear ind.
      unfold prepared in *; simpl in *; eauto 3 with pbft.
    }

    { (* handle pre-prepare *)

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_pre_prepare_and_prepare2log add.

      dup check as check1.
      eapply check_send_replies_preserves_commit_in_log in check1;[|eauto]; simpl in *.

      dup add as add1.
      eapply add_new_pre_prepare_and_prepare2log_preserves_commit_in_log in add1;
        [| |eauto]; autorewrite with pbft; auto.

      repndors;[|].

      {
        eapply check_send_replies_preserves_prepared_reverse;[eauto|].
        assert (prepared (request_data v n d) p = true) as prep' by (smash_pbft_ind ind).
        clear ind.
        unfold prepared in *; simpl in *; eauto 2 with pbft.
      }

      {
        clear ind.
        exrepnd;[].

        destruct p0 as [b' a']; simpl in *.
        destruct b' as [v' s' reqs]; simpl in *.
        unfold mk_commit in *; ginv.

        eapply check_send_replies_preserves_prepared_reverse in check;eauto.
      }
    }

    { (* handle prepare *)

      hide_hyp ind.

      rename_hyp_with check_send_replies check.
      rename_hyp_with add_new_prepare2log add.

      dup check as check1.
      eapply check_send_replies_preserves_commit_in_log in check;[|eauto].
      autorewrite with pbft in *.

      dup add as add1.
      eapply add_new_prepare2log_preserves_commit_in_log in add1;[|eauto];[].

      repndors;[|].

      {
        eapply check_send_replies_preserves_prepared_reverse;[eauto|].
        assert (prepared (request_data v n d) p = true) as prep' by (smash_pbft_ind ind).
        clear ind.
        unfold prepared in *; simpl in *; eauto 2 with pbft.
      }

      {
        clear ind.
        exrepnd;[].

        destruct p0 as [b' a']; simpl in *.
        destruct b' as [v' s' d' i']; simpl in *.
        unfold mk_commit in *; ginv.

        eapply check_send_replies_preserves_prepared_reverse in check1;eauto.
      }
    }

    { (* handle commit *)

      hide_hyp ind.

      rename_hyp_with check_send_replies check.

      applydup check_send_replies_preserves_log in check as eqlogs; simpl in *; subst; simpl in *.

      applydup check_send_replies_preserves_keys in check as eqkeys; simpl in *; subst; simpl in *; try (rewrite eqkeys).

      rename_hyp_with add_new_commit2log add.
      dup add as add1.
      eapply add_new_commit2log_preserves_commit_in_log in add1; [| eauto].

      repndors;[|].

      {
        show_hyp ind.

        eapply check_send_replies_preserves_prepared_reverse;[eauto|].
        assert (prepared (request_data v n d) p = true) as prep' by (smash_pbft_ind ind).
        clear ind.
        unfold prepared in *; simpl in *; eauto 2 with pbft.
      }

      {
        clear ind.
        exrepnd;[].
        subst.

        unfold mk_commit in *; ginv.
      }
    }

    { (* handle check_ready *)

      rename_hyp_with find_and_execute_requests fexec.

      dup fexec as find.
      eapply find_and_execute_requests_preserves_commit_in_log in find;[|eauto].

      assert (prepared (request_data v n d) p = true) as prep' by (smash_pbft_ind ind).
      clear ind.

      unfold prepared; simpl; autorewrite with pbft.
      eapply find_and_execute_requests_preserves_prepared in fexec; [|eauto|]; eauto 3 with pbft.
    }

    { (* handle check-bcast-new-view *)

      rename_hyp_with commit_in_log prep.

      eapply update_state_new_view_preserves_commit_in_log2 in prep;[| | |eauto];
        simpl in *; auto; eauto 2 with pbft;[|eauto 4 with pbft].

      repnd.
      autorewrite with pbft in *.

      assert (prepared (request_data v n d) p = true) as prep' by (smash_pbft_ind ind).
      clear ind.
      unfold prepared in *; simpl in *; eauto 3 with pbft.

      rename_hyp_with update_state_new_view upd.
      apply (update_state_new_view_preserves_prepared_reverse
               _ _ _ _ _ (request_data v n d)) in upd;
        unfold prepared; simpl in *; autorewrite with pbft in *; eauto 2 with pbft;
          [|eauto 4 with pbft];[].
      repndors; repnd; tcsp;[].
      simpl in *.
      autodimp prep hyp; omega.
    }

    { (* handle new_view *)

      hide_hyp ind.

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.
      rename_hyp_with commit_in_log prep.

      applydup add_prepares_to_log_from_new_view_pre_prepares_preserves_wf in add;
        simpl; autorewrite with pbft; eauto 3 with pbft;[].
      applydup update_state_new_view_preserves_wf in upd; simpl; eauto 3 with pbft;[].

      eapply update_state_new_view_preserves_commit_in_log2 in prep;[| | |eauto];
        simpl in *; auto;[].
      repnd.
      autorewrite with pbft in *.

      eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_commit_in_log2 in prep0;
        [|eauto]; simpl in *; autorewrite with pbft in *.

      repndors;[|].

      {
        assert (prepared (request_data v n d) p = true) as prep' by (smash_pbft_ind ind).
        clear ind.

        unfold prepared; simpl; autorewrite with pbft.

        eapply add_prepares_to_log_from_new_view_pre_prepares_preserves_prepared_log_forward in add; eauto.

        eapply update_state_new_view_preserves_prepared_reverse in upd; simpl; auto;
          [|autorewrite with pbft;eauto].
        simpl in *; autorewrite with pbft in *.
        repndors; repnd; tcsp;[].
        autodimp prep hyp; try omega.
      }

      {
        exrepnd.
        destruct pp as [ [v' s' reqs] a']; simpl in *.
        unfold mk_commit in *; ginv.
        eapply update_state_new_view_preserves_prepared_reverse in upd;
          simpl in *; auto;[|autorewrite with pbft;eauto].
        simpl in *; autorewrite with pbft in *.
        repndors; repnd; auto;[].
        autodimp prep hyp; try omega.
      }
    }
  Qed.
  Hint Resolve PBFT_A_1_6 : pbft.

End PBFT_A_1_6.


Hint Resolve check_one_stable_preserves_commit_in_log : pbft.
Hint Resolve prepared_higher_than_low_water_mark : pbft.
Hint Resolve prepared_higher_than_low_water_mark_before : pbft.
Hint Resolve implies_prepared_check_one_stable_if_commit : pbft.
Hint Resolve PBFT_A_1_6 : pbft.


Hint Rewrite @prepared_log_new_view_state : pbft.
Hint Rewrite @matching_requests_same : pbft.
