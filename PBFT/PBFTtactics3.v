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

Lemma same_iff_true :
  forall {A} (a : A), (a = a) <-> True.
Proof.
  introv; split; auto.
Qed.
Hint Rewrite @same_iff_true : prop.

Lemma true_equal_false_as_false :
  (true = false) <-> False.
Proof.
  introv; split; tcsp.
Qed.
Hint Rewrite @true_equal_false_as_false : prop.

Lemma false_equal_true_as_false :
  (false = true) <-> False.
Proof.
  introv; split; tcsp.
Qed.
Hint Rewrite @false_equal_true_as_false : prop.

Lemma false_iff_as_not :
  forall P, (False <-> P) <-> ~P.
Proof.
  introv; split; intro h; tcsp.
  - intro q; apply h; auto.
  - split; intro q; tcsp.
Qed.
Hint Rewrite @false_iff_as_not : prop.

Ltac simple_unfold :=
  match goal with
  | [ |- ?x ] => unfold x
  | [ |- ?x = _ ] => unfold x
  | [ |- ?x _ = _ ] => unfold x
  | [ |- ?x _ _ = _ ] => unfold x
  | [ |- ?x _ _ _ = _ ] => unfold x
  | [ |- ?x _ _ _ _ = _ ] => unfold x
  | [ |- ?x _ _ _ _ _ = _ ] => unfold x
  | [ |- ?x _ _ _ _ _ _ = _ ] => unfold x
  | [ |- ?x _ _ _ _ _ _ _ = _ ] => unfold x
  end.

Ltac unf_smash_pbft :=
  intros; repeat simple_unfold; simpl; smash_pbft.

Ltac pbft_destruct_one :=
  match goal with
  | [ H : PBFTlogEntry            |- _ ] => destruct H
  | [ H : Pre_prepare             |- _ ] => destruct H
  | [ H : Bare_Pre_prepare        |- _ ] => destruct H
  | [ H : Prepare                 |- _ ] => destruct H
  | [ H : Bare_Prepare            |- _ ] => destruct H
  | [ H : Commit                  |- _ ] => destruct H
  | [ H : Bare_Commit             |- _ ] => destruct H
  | [ H : logEntryPrePrepareInfo  |- _ ] => destruct H
  | [ H : well_formed_log_entry _ |- _ ] => destruct H
  | [ H : RequestData             |- _ ] => destruct H
  | [ H : GeneratedInfo           |- _ ] => destruct H

  | [ |- well_formed_log_entry _ ] => constructor
  end.

Ltac pbft_destruct_all :=
  repeat pbft_destruct_one; simpl in *; auto.

Ltac pbft_unfold_all :=
  unfold
    digest_for_pre_prepare,
  entry_and_pre_prepare_have_same_digests,
  similar_entry_and_pre_prepare,
  eq_request_data,
  pre_prepare2digest,
  requests_and_replies2digest,
  requests2digest,
  add_prepare_if_not_enough,
  add_commit_if_prepared,
  check_send_replies,
  check_stable,
  check_broadcast_checkpoint,
  execute_requests,
  find_and_execute_requests,
  check_broadcast_new_view,
  correct_new_view,
  update_state_new_view,
  same_digests in *;
  simpl in *.

Ltac pbft_brute_force_step :=
  first
    [complete tcsp
    |progress GC
    |progress autorewrite with pbft list prop in *
    |progress pbft_destruct_all
    |progress pbft_unfold_all
    |progress ginv
    |progress smash_pbft
    ].

Ltac pbft_brute_force :=
  intros;
  repeat pbft_brute_force_step.
