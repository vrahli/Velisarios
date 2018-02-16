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


Require Export PBFTreceived_prepare_like2.
Require Export PBFTreceived_prepare_like8.
Require Export PBFTreplica_has_correct_trace.
Require Export PBFTprepare_like2request_data.


(* based on PBFTreplica_prepare_like9 *)

Section PBFTlearns_or_knows.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma correct_in_intersection :
    forall (eo : EventOrdering) (l1 l2 : list Rep) (E : list Event),
      no_repeats l1
      -> no_repeats l2
      -> 2 * F + 1 <= length l1
      -> 2 * F + 1 <= length l2
      -> PBFT_at_most_f_byz2 eo E
      -> exists good,
          In good l1
          /\ In good l2
          /\ forall e, In e E -> replica_has_correct_trace_before eo e good.
  Proof.
    introv nrep1 nrep2 len1 len2 atmost.
    pose proof (two_quorums l1 l2) as quor; repeat (autodimp quor hyp).
    exrepnd.
    pose proof (there_is_one_good_guy_before eo l E) as gg.
    repeat (autodimp gg hyp).
    exrepnd.
    exists good; dands; auto.
  Qed.

  Inductive pbft_data :=
  | pbft_data_pl (pl : Prepare_like).

  Definition pbft_data_knows (d : pbft_data) (s : PBFTstate) : Prop :=
    match d with
    | pbft_data_pl pl => prepare_like_in_log pl (log s)
    end.

  Definition pbft_data2main_auth_data (d : pbft_data) : AuthenticatedData :=
    match d with
    | pbft_data_pl pl => prepare_like2main_auth_data pl
    end.

  Definition verify_pbft_data (i : Rep) (keys : local_key_map) (d : pbft_data) : bool :=
    match d with
    | pbft_data_pl pl => verify_prepare_like i keys pl
    end.

  Definition pbft_data2loc (d : pbft_data) : name :=
    match d with
    | pbft_data_pl pl => PBFTreplica (prepare_like2sender pl)
    end.

  Definition pbft_knows {eo : EventOrdering} (e : Event) (d : pbft_data) :=
    exists st i,
      loc e = PBFTreplica i
      /\ pbft_data_knows d st
      /\ state_sm_on_event (PBFTreplicaSM i) eo e = Some st.

  Definition pbft_learns {eo : EventOrdering} (e : Event) (d : pbft_data) :=
    exists i,
      loc e = PBFTreplica i
      /\ In (pbft_data2main_auth_data d) (get_contained_authenticated_data (trigger e))
      /\ verify_pbft_data i (keys e) d = true.

  Definition pbft_learns_or_knows (d : pbft_data) : Prop :=
    forall {eo : EventOrdering} (e : Event),
      pbft_knows e d
      ->
      (exists e', e' ⊑ e /\ pbft_learns e' d)
      \/ pbft_data2loc d = loc e.

  Definition pbft_learns_if_knows (d : pbft_data) :=
    forall {eo : EventOrdering} (e : Event),
      pbft_learns e d
      ->
      exists e',
        e' ≺ e
        /\ loc e' = pbft_data2loc d
        /\ pbft_knows e' d.

  Lemma knows_propagates :
    forall (eo : EventOrdering) (e : Event) pl,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> replica_has_correct_trace_before eo e (prepare_like2sender pl)
      -> pbft_learns_or_knows (pbft_data_pl pl)
      -> pbft_learns_if_knows (pbft_data_pl pl)
      -> pbft_knows e (pbft_data_pl pl)
      ->
      exists e',
        e' ≼ e
        /\ loc e' = PBFTreplica (prepare_like2sender pl)
        /\ pbft_knows e' (pbft_data_pl pl).
  Proof.
    introv auth ckeys ctrace lok lik knows.
    pose proof (lok _ e knows) as sent.
    repndors; repnd;[|exists e; dands; eauto 2 with eo];[].

    exrepnd.

    pose proof (lik _ e' sent0) as h.
    exrepnd.
    exists e'0; dands; auto; eauto 4 with eo.
  Qed.

End PBFTlearns_or_knows.
