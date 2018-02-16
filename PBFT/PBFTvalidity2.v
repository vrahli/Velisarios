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


Require Export PBFTilf.


Section PBFTvalidity2.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  (* ==== Hints from PBFTilf.v ==== *)
  Hint Rewrite is_primary_PBFTprimary                                    : pbft.
  Hint Rewrite ready_decrement_requests_in_progress_if_primary           : pbft.
  Hint Rewrite next_to_execute_decrement_requests_in_progress_if_primary : pbft.
  Hint Rewrite sm_state_decrement_requests_in_progress_if_primary        : pbft.
  Hint Rewrite low_water_mark_decrement_requests_in_progress_if_primary  : pbft.
  Hint Rewrite current_view_decrement_requests_in_progress_if_primary    : pbft.
  Hint Rewrite log_decrement_requests_in_progress_if_primary             : pbft.
  Hint Rewrite local_keys_decrement_requests_in_progress_if_primary      : pbft.
  Hint Rewrite bare_reply2result_request2bare_reply                      : pbft.
  Hint Rewrite entry2pre_prepare_MkNewLogEntryWithPrepare                : pbft.
  Hint Rewrite entry2pre_prepare_add_prepare2entry                       : pbft.
  Hint Rewrite entry2pre_prepare_add_commit2entry                        : pbft.
  Hint Rewrite map_fst_combine_replies                                   : pbft.
  Hint Rewrite entry2pre_prepare_add_replies2entry                       : pbft.
  Hint Rewrite seqnum2nat_seq_num                                        : pbft.
  Hint Rewrite update_primary_state_primary_state_same                   : pbft.
  Hint Rewrite update_log_same_log                                       : pbft.
  Hint Rewrite log_update_ready                                          : pbft.
  Hint Rewrite request_buffer_decrement_requests_in_progress_if_primary  : pbft.

  Hint Resolve In_iseg_implies_In : list.
  (* ==== End ==== *)


  (* For Vincent *)
  Lemma PBFTvalidity2 :
    forall (eo : EventOrdering),
      sent_byz_usys eo PBFTsys
      -> PBFT_hold_keys_client eo
      -> PBFTkeys_from_state eo
      ->
      forall (e : Event)
             (v : View)
             (t : Timestamp)
             (c : Client)
             (i : Rep)
             (r : PBFTresult)
             (a : Tokens)
             (n : Rep)
             (l : name),
        (* FIX: we have to assume
             (1) that the replica sending the reply (n) is not faulty
             (2) that we have at most f faulty replicas *)
        PBFT_at_most_f_byz2 eo e
        (* A reply was sent at [e] *)
        -> In (MkDMsg l (PBFTreply (reply (bare_reply v t c i r) a)))
              (output_system_on_event_ldata PBFTsys eo e)
        -> loc e = PBFTreplica n
        ->
        exists opr e' a',
          e' ≼ e
          /\ trigger e' = PBFTrequest (req (bare_req opr t c) a').
  Proof.
    introv sendbyz holdkeys keysst faults send eqloc.

    (* The reply was triggered by a commit message *)
    apply PBFT_reply_output_iff in send.
    exrepnd; subst.

    assert (n0 = n) as eqn.
    { match goal with
      | [ H1 : loc _ = _ , H2 : loc _ = _ |- _ ] => rewrite H1 in H2; ginv
      end. }
    subst n0; GC.

    match goal with
    | [ H : In _ replies |- _ ] => rename H into inreps
    end.
    (* We will now get the request corresponding to the reply mentioned in [inreps] *)

    match goal with
    | [ H : execute_requests _ _ _ _ _ = _ |- _ ] => rename H into exec
    end.
    (* We can get this request from the log via [rep2req] *)

    eapply reply_from_execute_requests in exec;[|eauto].
    exrepnd; simpl in *.
    destruct req as [breq auth]; simpl in *.
    destruct breq as [opr ts cl]; simpl in *; ginv.

    eapply entry_in_add_new_commit2log_implies_exists_same_pre_prepare in exec1;[|eauto].
    exrepnd.

    eapply change_in_fst_log_entry_requests in exec1;[|eauto].

    clear inreps exec2.

    match goal with
    | [ H : In _ (log _) |- _ ] => rename H into inlog
    end.

    match goal with
    | [ H : In _ (map fst _) |- _ ] => rename H into inentry
    end.

    match goal with
    | [ H : state_sm_before_event _ _ _ = _ |- _ ] => rename H into ssb
    end.

    match goal with
    | [ H : state_correspondence_on_commit _ _ _ _ |- _ ] => rename H into corr
    end.
    (* We now reason by local induction to get to the point in time when we got the
       request that's in our state: see [iiseg] where the state is defined in [ssb] *)

    pose proof (received_pre_prepare_in_entry eo e n st1 entry') as q.
    repeat (autodimp q hyp).
    exrepnd.

    assert (loc e' = PBFTreplica n) as eqloc1 by (allrw <-; eauto 3 with eo).
    assert (loc e' = loc e) as eqloc2 by (eauto 3 with eo).

    (* either we're the primary and the request comes directly from a client
       or we're a backup and the request comes from a pre_prepare *)
    dest_cases w; symmetry in Heqw; exrepnd; subst; simpl in *;[|].

    {
      (* either the request is [r] or it was in our list of buffered requests *)
      destruct entry'; simpl in *; ginv.

      pose proof (fst_in_PBFTcheck_new_requests_implies
                    log_entry_requests
                    (req (bare_req opr ts cl) auth)
                    r
                    (primary_state st'0)) as q.
      repeat (autodimp q hyp).
      repndors; subst.

      (* This is the easy case where the reply is the one we just received *)
      { eexists; eexists; eexists;dands;[|eauto]; eauto 3 with eo. }

      (* Now we know that the request is one that we've buffered
         and we have to go by induction again *)
      pose proof (in_request_buffer_from_request eo e' n st'0 (req (bare_req opr ts cl) auth)) as ir.
      repeat (autodimp ir hyp); try (complete (allrw; auto)).
      exrepnd.
      exists opr e'0 auth; dands; eauto 4 with eo.
    }

    {
      pose proof (sendbyz
                    e'
                    (request2auth_data (req (bare_req opr ts cl) auth)))
        as q; simpl in q.
      autodimp q hyp.

      {
        allrw; simpl; right.
        destruct entry'; simpl in *.
        rw map_map; simpl.
        allrw in_map_iff; exrepnd; simpl in *; subst; simpl in *.
        eexists; dands;[|eauto]; simpl; auto.
      }

      exrepnd.

      autodimp q4 hyp.

      {
        unfold verify_pre_prepare in q1.
        remember (entry2pre_prepare entry') as pp.
        destruct pp; simpl in *.
        allrw andb_true_iff; repnd.
        destruct entry'; simpl in *; ginv.
        eapply verify_request_if_verify_requests in q1;[|eauto].
        simpl in q1.
        pose proof (keysst e' n st'0) as k; autodimp k hyp; allrw; auto.
      }

      repnd.

      repndors;[|].
      (* first subgoal is if everything went fine and
         the second if the byzantine case *)

      {
        exrepnd.
        match goal with
        | [ H : Some _ = Some _ |- _ ] => inversion H as [clloc]; clear H
        end.

        pose proof (authenticated_request_from_request_or_pre_prepare
                      m (req (bare_req opr ts cl) auth)) as h;
          simpl in h; autodimp h hyp.

        (* because of the second case here we should go by induction *)

        repndors;[|].

        {
          subst m; simpl in *.
          repndors; tcsp;[]; GC.
          unfold is_internal_message in *; simpl in *.

  Abort.

End PBFTvalidity2.
