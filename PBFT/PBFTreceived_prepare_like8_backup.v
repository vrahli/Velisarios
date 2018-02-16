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


Require Export PBFTreceived_prepare_like3.
Require Export PBFTreceived_prepare_like4.
Require Export PBFTreceived_prepare_like5.
Require Export PBFTreceived_prepare_like6.
Require Export PBFTreceived_prepare_like7.


Section PBFTreceived_prepare_like8.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma prepare_like_received_from_good_replica_was_in_log :
    forall (eo : EventOrdering) (e : Event) good pl i,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> (forall e', e' ≼ e -> loc e' = PBFTreplica good -> replica_has_correct_trace_before eo e')
      -> prepare_like2sender pl = good
      -> verify_prepare_like i (keys e) pl = true
      -> In (prepare_like2auth_data pl) (get_contained_authenticated_data (trigger e))
      ->
      exists e' st,
        e' ≺ e
        /\ loc e' = PBFTreplica good
        /\ state_sm_on_event (PBFTreplicaSM good) eo e' = Some st
        /\ prepare_like_in_log pl (log st).
  Proof.
    introv sendbyz ckeys.
    revert e good pl i.
    induction e as [? ind] using CausalOrderInd;[].
    introv eqloc cortrace goodprep verif iauth.

    applydup sendbyz in iauth as sb.
    exrepnd.
    rewrite eqloc in sb0.

    autodimp sb0 hyp; eauto 2 with pbft;[].
    repnd; simpl in *.

    (* the right branch amount to saying that [good] is Byz, which is false *)
    repndors; exrepnd; rename_hyp_with PBFTdata_auth dauth.
    Focus 2.
    applydup PBFTdata_auth_prepare_like2auth_data_some_implies in dauth.
XXXX

    clear dauth.
    clear sb2.
    clear iauth.
    clear verif.

    applydup prepare_like2auth_data_in_get_contained_auth_data_implies in sb3.

    repndors; exrepnd; subst m; simpl in *; autodimp sb4 hyp; repndors; tcsp;[| | |].

    - (* prepare *)

      apply prepare2auth_data_equal_prepare_like2auth_data_implies in sb3.
      subst pl.
      simpl in *.

      pose proof (PBFTnever_stops_on_event eo e' good) as q.
      exrepnd.

      rename_hyp_with @output_system_on_event_ldata sendprep.
      eapply send_prepares_are_in_log in sendprep;[| |eauto]; auto;[].

      exists e' st.
      dands; auto; eauto 3 with pbft.

    - (* pre-prepare *)

      apply pre_prepare2auth_data_equal_prepare_like2auth_data_implies in sb3.
      subst pl.
      simpl in *.

      pose proof (PBFTnever_stops_on_event eo e' good) as q.
      exrepnd.

      rename_hyp_with @output_system_on_event_ldata sendprep.
      eapply send_pre_prepares_are_in_log in sendprep;[| |eauto]; auto;[].

      exists e' st.
      dands; auto; eauto 3 with pbft.

    - (* view-change *)

      apply prepare_like2auth_data_in_view_change2auth_data_implies in sb3.
      destruct sb3 as [pi pip]; repnd.

      pose proof (PBFTnever_stops_on_event eo e' good) as q.
      exrepnd.

      rename_hyp_with @output_system_on_event_ldata sendvc.
      eapply prepare_like_of_send_view_change_are_in_log in sendvc;
        [| |eauto|eauto|eauto];auto;[].

      exists e' st; dands; auto.

    - (* new_view *)

      pose proof (PBFTnever_stops_on_event eo e' good) as q.
      exrepnd.

      rename_hyp_with @output_system_on_event_ldata sendprep.

      eapply prepare_like_of_send_new_view_are_in_log in sendprep;
        [| | |]; eauto.
      repndors;[exists e' st; dands; auto|];[].
      exrepnd.

      rename_hyp_with view_change_somewhere_in_log vcinlog.
      dup vcinlog as vcinlog_backup.
      eapply view_changes_are_received_or_created in vcinlog;[|eauto].
      exrepnd.

      applydup localLe_implies_loc in vcinlog0.

      (* either the view-change message was received or it was created *)
      repndors; exrepnd;[|].

      + (* the view-change messages was received *)

        pose proof (ind e'0) as q; clear ind; autodimp q hyp; eauto 3 with eo;[].
        pose proof (q good pl good) as h; clear q.
        repeat (autodimp h hyp); eauto 3 with pbft eo;
          [allrw;auto|introv w z;apply cortrace; eauto 5 with eo| | |];
          [|allrw;simpl;eauto 2 with pbft|];
          [|exrepnd; exists e'1 st0; dands; eauto 4 with eo];[].

        pose proof (ckeys e'0 good st') as eqkeys; autodimp eqkeys hyp.
        rewrite eqkeys; clear eqkeys; eauto 2 with pbft.

      + (* the view-change messages was create *)

        pose proof (vcinlog1 pl pi) as prep; repeat (autodimp prep hyp).
        rewrite state_sm_before_event_as_state_sm_on_event_pred in vcinlog2;[|eauto 2 with pbft];[].
        exists (local_pred e'0) st'; dands; eauto 4 with eo pbft.
        rewrite loc_local_pred; allrw;auto.
  Qed.

End PBFTreceived_prepare_like8.
