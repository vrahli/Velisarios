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


Require Export PBFTprops.
Require Export generic_tactics.


Ltac conflicting_sends :=
  match goal with
  | [ H : send_request _ _ = send_reply _                  |- _ ] => inversion H;fail
  | [ H : send_request _ _ = send_pre_prepare _ _          |- _ ] => inversion H;fail
  | [ H : send_request _ _ = send_prepare _ _              |- _ ] => inversion H;fail
  | [ H : send_request _ _ = send_commit _ _               |- _ ] => inversion H;fail
  | [ H : send_request _ _ = send_checkpoint _ _           |- _ ] => inversion H;fail
  | [ H : send_request _ _ = send_debug _ _                |- _ ] => inversion H;fail
  | [ H : send_request _ _ = send_view_change _ _          |- _ ] => inversion H;fail
  | [ H : send_request _ _ = send_new_view _ _             |- _ ] => inversion H;fail
  | [ H : send_request _ _ = send_check_ready _            |- _ ] => inversion H;fail
  | [ H : send_request _ _ = send_check_stable _           |- _ ] => inversion H;fail
  | [ H : send_request _ _ = send_check_bcast_new_view _ _ |- _ ] => inversion H;fail
  | [ H : send_request _ _ = send_start_timer _ _          |- _ ] => inversion H;fail
  | [ H : send_request _ _ = send_expired_timer _ _        |- _ ] => inversion H;fail

  | [ H : send_reply _ = send_request _ _              |- _ ] => inversion H;fail
  | [ H : send_reply _ = send_pre_prepare _ _          |- _ ] => inversion H;fail
  | [ H : send_reply _ = send_prepare _ _              |- _ ] => inversion H;fail
  | [ H : send_reply _ = send_commit _ _               |- _ ] => inversion H;fail
  | [ H : send_reply _ = send_checkpoint _ _           |- _ ] => inversion H;fail
  | [ H : send_reply _ = send_debug _ _                |- _ ] => inversion H;fail
  | [ H : send_reply _ = send_view_change _ _          |- _ ] => inversion H;fail
  | [ H : send_reply _ = send_new_view _ _             |- _ ] => inversion H;fail
  | [ H : send_reply _ = send_check_ready _            |- _ ] => inversion H;fail
  | [ H : send_reply _ = send_check_stable _           |- _ ] => inversion H;fail
  | [ H : send_reply _ = send_check_bcast_new_view _ _ |- _ ] => inversion H;fail
  | [ H : send_reply _ = send_start_timer _ _          |- _ ] => inversion H;fail
  | [ H : send_reply _ = send_expired_timer _ _        |- _ ] => inversion H;fail

  | [ H : send_pre_prepare _ _ = send_request _ _              |- _ ] => inversion H;fail
  | [ H : send_pre_prepare _ _ = send_reply _                  |- _ ] => inversion H;fail
  | [ H : send_pre_prepare _ _ = send_prepare _ _              |- _ ] => inversion H;fail
  | [ H : send_pre_prepare _ _ = send_commit _ _               |- _ ] => inversion H;fail
  | [ H : send_pre_prepare _ _ = send_checkpoint _ _           |- _ ] => inversion H;fail
  | [ H : send_pre_prepare _ _ = send_debug _ _                |- _ ] => inversion H;fail
  | [ H : send_pre_prepare _ _ = send_view_change _ _          |- _ ] => inversion H;fail
  | [ H : send_pre_prepare _ _ = send_new_view _ _             |- _ ] => inversion H;fail
  | [ H : send_pre_prepare _ _ = send_check_ready _            |- _ ] => inversion H;fail
  | [ H : send_pre_prepare _ _ = send_check_stable _           |- _ ] => inversion H;fail
  | [ H : send_pre_prepare _ _ = send_check_bcast_new_view _ _ |- _ ] => inversion H;fail
  | [ H : send_pre_prepare _ _ = send_start_timer _ _          |- _ ] => inversion H;fail
  | [ H : send_pre_prepare _ _ = send_expired_timer _ _        |- _ ] => inversion H;fail

  | [ H : send_prepare _ _ = send_request _ _              |- _ ] => inversion H;fail
  | [ H : send_prepare _ _ = send_reply _                  |- _ ] => inversion H;fail
  | [ H : send_prepare _ _ = send_pre_prepare _ _          |- _ ] => inversion H;fail
  | [ H : send_prepare _ _ = send_commit _ _               |- _ ] => inversion H;fail
  | [ H : send_prepare _ _ = send_checkpoint _ _           |- _ ] => inversion H;fail
  | [ H : send_prepare _ _ = send_debug _ _                |- _ ] => inversion H;fail
  | [ H : send_prepare _ _ = send_view_change _ _          |- _ ] => inversion H;fail
  | [ H : send_prepare _ _ = send_new_view _ _             |- _ ] => inversion H;fail
  | [ H : send_prepare _ _ = send_check_ready _            |- _ ] => inversion H;fail
  | [ H : send_prepare _ _ = send_check_stable _           |- _ ] => inversion H;fail
  | [ H : send_prepare _ _ = send_check_bcast_new_view _ _ |- _ ] => inversion H;fail
  | [ H : send_prepare _ _ = send_start_timer _ _          |- _ ] => inversion H;fail
  | [ H : send_prepare _ _ = send_expired_timer _ _        |- _ ] => inversion H;fail

  | [ H : send_commit _ _ = send_request _ _              |- _ ] => inversion H;fail
  | [ H : send_commit _ _ = send_reply _                  |- _ ] => inversion H;fail
  | [ H : send_commit _ _ = send_pre_prepare _ _          |- _ ] => inversion H;fail
  | [ H : send_commit _ _ = send_prepare _ _              |- _ ] => inversion H;fail
  | [ H : send_commit _ _ = send_checkpoint _ _           |- _ ] => inversion H;fail
  | [ H : send_commit _ _ = send_debug _ _                |- _ ] => inversion H;fail
  | [ H : send_commit _ _ = send_view_change _ _          |- _ ] => inversion H;fail
  | [ H : send_commit _ _ = send_new_view _ _             |- _ ] => inversion H;fail
  | [ H : send_commit _ _ = send_check_ready _            |- _ ] => inversion H;fail
  | [ H : send_commit _ _ = send_check_stable _           |- _ ] => inversion H;fail
  | [ H : send_commit _ _ = send_check_bcast_new_view _ _ |- _ ] => inversion H;fail
  | [ H : send_commit _ _ = send_start_timer _ _          |- _ ] => inversion H;fail
  | [ H : send_commit _ _ = send_expired_timer _ _        |- _ ] => inversion H;fail

  | [ H : send_checkpoint _ _ = send_request _ _              |- _ ] => inversion H;fail
  | [ H : send_checkpoint _ _ = send_reply _                  |- _ ] => inversion H;fail
  | [ H : send_checkpoint _ _ = send_pre_prepare _ _          |- _ ] => inversion H;fail
  | [ H : send_checkpoint _ _ = send_prepare _ _              |- _ ] => inversion H;fail
  | [ H : send_checkpoint _ _ = send_commit _ _               |- _ ] => inversion H;fail
  | [ H : send_checkpoint _ _ = send_debug _ _                |- _ ] => inversion H;fail
  | [ H : send_checkpoint _ _ = send_view_change _ _          |- _ ] => inversion H;fail
  | [ H : send_checkpoint _ _ = send_new_view _ _             |- _ ] => inversion H;fail
  | [ H : send_checkpoint _ _ = send_check_ready _            |- _ ] => inversion H;fail
  | [ H : send_checkpoint _ _ = send_check_stable _           |- _ ] => inversion H;fail
  | [ H : send_checkpoint _ _ = send_check_bcast_new_view _ _ |- _ ] => inversion H;fail
  | [ H : send_checkpoint _ _ = send_start_timer _ _          |- _ ] => inversion H;fail
  | [ H : send_checkpoint _ _ = send_expired_timer _ _        |- _ ] => inversion H;fail

  | [ H : send_debug _ _ = send_request _ _              |- _ ] => inversion H;fail
  | [ H : send_debug _ _ = send_reply _                  |- _ ] => inversion H;fail
  | [ H : send_debug _ _ = send_pre_prepare _ _          |- _ ] => inversion H;fail
  | [ H : send_debug _ _ = send_prepare _ _              |- _ ] => inversion H;fail
  | [ H : send_debug _ _ = send_commit _ _               |- _ ] => inversion H;fail
  | [ H : send_debug _ _ = send_checkpoint _ _           |- _ ] => inversion H;fail
  | [ H : send_debug _ _ = send_view_change _ _          |- _ ] => inversion H;fail
  | [ H : send_debug _ _ = send_new_view _ _             |- _ ] => inversion H;fail
  | [ H : send_debug _ _ = send_check_ready _            |- _ ] => inversion H;fail
  | [ H : send_debug _ _ = send_check_stable _           |- _ ] => inversion H;fail
  | [ H : send_debug _ _ = send_check_bcast_new_view _ _ |- _ ] => inversion H;fail
  | [ H : send_debug _ _ = send_start_timer _ _          |- _ ] => inversion H;fail
  | [ H : send_debug _ _ = send_expired_timer _ _        |- _ ] => inversion H;fail

  | [ H : send_view_change _ _ = send_request _ _              |- _ ] => inversion H;fail
  | [ H : send_view_change _ _ = send_reply _                  |- _ ] => inversion H;fail
  | [ H : send_view_change _ _ = send_pre_prepare _ _          |- _ ] => inversion H;fail
  | [ H : send_view_change _ _ = send_prepare _ _              |- _ ] => inversion H;fail
  | [ H : send_view_change _ _ = send_commit _ _               |- _ ] => inversion H;fail
  | [ H : send_view_change _ _ = send_checkpoint _ _           |- _ ] => inversion H;fail
  | [ H : send_view_change _ _ = send_debug _ _                |- _ ] => inversion H;fail
  | [ H : send_view_change _ _ = send_new_view _ _             |- _ ] => inversion H;fail
  | [ H : send_view_change _ _ = send_check_ready _            |- _ ] => inversion H;fail
  | [ H : send_view_change _ _ = send_check_stable _           |- _ ] => inversion H;fail
  | [ H : send_view_change _ _ = send_check_bcast_new_view _ _ |- _ ] => inversion H;fail
  | [ H : send_view_change _ _ = send_start_timer _ _          |- _ ] => inversion H;fail
  | [ H : send_view_change _ _ = send_expired_timer _ _        |- _ ] => inversion H;fail

  | [ H : send_new_view _ _ = send_request _ _              |- _ ] => inversion H;fail
  | [ H : send_new_view _ _ = send_reply _                  |- _ ] => inversion H;fail
  | [ H : send_new_view _ _ = send_pre_prepare _ _          |- _ ] => inversion H;fail
  | [ H : send_new_view _ _ = send_prepare _ _              |- _ ] => inversion H;fail
  | [ H : send_new_view _ _ = send_commit _ _               |- _ ] => inversion H;fail
  | [ H : send_new_view _ _ = send_checkpoint _ _           |- _ ] => inversion H;fail
  | [ H : send_new_view _ _ = send_debug _ _                |- _ ] => inversion H;fail
  | [ H : send_new_view _ _ = send_view_change _ _          |- _ ] => inversion H;fail
  | [ H : send_new_view _ _ = send_check_ready _            |- _ ] => inversion H;fail
  | [ H : send_new_view _ _ = send_check_stable _           |- _ ] => inversion H;fail
  | [ H : send_new_view _ _ = send_check_bcast_new_view _ _ |- _ ] => inversion H;fail
  | [ H : send_new_view _ _ = send_start_timer _ _          |- _ ] => inversion H;fail
  | [ H : send_new_view _ _ = send_expired_timer _ _        |- _ ] => inversion H;fail

  | [ H : send_check_ready _ = send_request _ _              |- _ ] => inversion H;fail
  | [ H : send_check_ready _ = send_reply _                  |- _ ] => inversion H;fail
  | [ H : send_check_ready _ = send_pre_prepare _ _          |- _ ] => inversion H;fail
  | [ H : send_check_ready _ = send_prepare _ _              |- _ ] => inversion H;fail
  | [ H : send_check_ready _ = send_commit _ _               |- _ ] => inversion H;fail
  | [ H : send_check_ready _ = send_checkpoint _ _           |- _ ] => inversion H;fail
  | [ H : send_check_ready _ = send_debug _ _                |- _ ] => inversion H;fail
  | [ H : send_check_ready _ = send_view_change _ _          |- _ ] => inversion H;fail
  | [ H : send_check_ready _ = send_new_view _ _             |- _ ] => inversion H;fail
  | [ H : send_check_ready _ = send_check_bcast_new_view _ _ |- _ ] => inversion H;fail
  | [ H : send_check_ready _ = send_start_timer _ _          |- _ ] => inversion H;fail
  | [ H : send_check_ready _ = send_expired_timer _ _        |- _ ] => inversion H;fail
  | [ H : send_check_ready _ = send_check_stable _           |- _ ] => inversion H;fail

  | [ H : send_check_stable _ = send_request _ _              |- _ ] => inversion H;fail
  | [ H : send_check_stable _ = send_reply _                  |- _ ] => inversion H;fail
  | [ H : send_check_stable _ = send_pre_prepare _ _          |- _ ] => inversion H;fail
  | [ H : send_check_stable _ = send_prepare _ _              |- _ ] => inversion H;fail
  | [ H : send_check_stable _ = send_commit _ _               |- _ ] => inversion H;fail
  | [ H : send_check_stable _ = send_checkpoint _ _           |- _ ] => inversion H;fail
  | [ H : send_check_stable _ = send_debug _ _                |- _ ] => inversion H;fail
  | [ H : send_check_stable _ = send_view_change _ _          |- _ ] => inversion H;fail
  | [ H : send_check_stable _ = send_new_view _ _             |- _ ] => inversion H;fail
  | [ H : send_check_stable _ = send_check_bcast_new_view _ _ |- _ ] => inversion H;fail
  | [ H : send_check_stable _ = send_start_timer _ _          |- _ ] => inversion H;fail
  | [ H : send_check_stable _ = send_expired_timer _ _        |- _ ] => inversion H;fail
  | [ H : send_check_stable _ = send_check_ready _            |- _ ] => inversion H;fail

  | [ H : send_check_bcast_new_view _ _ = send_request _ _              |- _ ] => inversion H;fail
  | [ H : send_check_bcast_new_view _ _ = send_reply _                  |- _ ] => inversion H;fail
  | [ H : send_check_bcast_new_view _ _ = send_pre_prepare _ _          |- _ ] => inversion H;fail
  | [ H : send_check_bcast_new_view _ _ = send_prepare _ _              |- _ ] => inversion H;fail
  | [ H : send_check_bcast_new_view _ _ = send_commit _ _               |- _ ] => inversion H;fail
  | [ H : send_check_bcast_new_view _ _ = send_checkpoint _ _           |- _ ] => inversion H;fail
  | [ H : send_check_bcast_new_view _ _ = send_debug _ _                |- _ ] => inversion H;fail
  | [ H : send_check_bcast_new_view _ _ = send_view_change _ _          |- _ ] => inversion H;fail
  | [ H : send_check_bcast_new_view _ _ = send_new_view _ _             |- _ ] => inversion H;fail
  | [ H : send_check_bcast_new_view _ _ = send_check_ready _            |- _ ] => inversion H;fail
  | [ H : send_check_bcast_new_view _ _ = send_check_stable _           |- _ ] => inversion H;fail
  | [ H : send_check_bcast_new_view _ _ = send_start_timer _ _          |- _ ] => inversion H;fail
  | [ H : send_check_bcast_new_view _ _ = send_expired_timer _ _        |- _ ] => inversion H;fail

  | [ H : send_start_timer _ _ = send_request _ _              |- _ ] => inversion H;fail
  | [ H : send_start_timer _ _ = send_reply _                  |- _ ] => inversion H;fail
  | [ H : send_start_timer _ _ = send_pre_prepare _ _          |- _ ] => inversion H;fail
  | [ H : send_start_timer _ _ = send_prepare _ _              |- _ ] => inversion H;fail
  | [ H : send_start_timer _ _ = send_commit _ _               |- _ ] => inversion H;fail
  | [ H : send_start_timer _ _ = send_checkpoint _ _           |- _ ] => inversion H;fail
  | [ H : send_start_timer _ _ = send_debug _ _                |- _ ] => inversion H;fail
  | [ H : send_start_timer _ _ = send_view_change _ _          |- _ ] => inversion H;fail
  | [ H : send_start_timer _ _ = send_new_view _ _             |- _ ] => inversion H;fail
  | [ H : send_start_timer _ _ = send_check_ready _            |- _ ] => inversion H;fail
  | [ H : send_start_timer _ _ = send_check_stable _           |- _ ] => inversion H;fail
  | [ H : send_start_timer _ _ = send_check_bcast_new_view _ _ |- _ ] => inversion H;fail
  | [ H : send_start_timer _ _ = send_expired_timer _ _        |- _ ] => inversion H;fail

  | [ H : send_expired_timer _ _ = send_request _ _              |- _ ] => inversion H;fail
  | [ H : send_expired_timer _ _ = send_reply _                  |- _ ] => inversion H;fail
  | [ H : send_expired_timer _ _ = send_pre_prepare _ _          |- _ ] => inversion H;fail
  | [ H : send_expired_timer _ _ = send_prepare _ _              |- _ ] => inversion H;fail
  | [ H : send_expired_timer _ _ = send_commit _ _               |- _ ] => inversion H;fail
  | [ H : send_expired_timer _ _ = send_checkpoint _ _           |- _ ] => inversion H;fail
  | [ H : send_expired_timer _ _ = send_debug _ _                |- _ ] => inversion H;fail
  | [ H : send_expired_timer _ _ = send_view_change _ _          |- _ ] => inversion H;fail
  | [ H : send_expired_timer _ _ = send_new_view _ _             |- _ ] => inversion H;fail
  | [ H : send_expired_timer _ _ = send_check_ready _            |- _ ] => inversion H;fail
  | [ H : send_expired_timer _ _ = send_check_stable _           |- _ ] => inversion H;fail
  | [ H : send_expired_timer _ _ = send_check_bcast_new_view _ _ |- _ ] => inversion H;fail
  | [ H : send_expired_timer _ _ = send_start_timer _ _          |- _ ] => inversion H;fail
  end.

Ltac pbft_simplifier_step :=
  match goal with
  | [ H : context[SeqNumLe _ _ = true]  |- _ ] => rewrite SeqNumLe_true  in H
  | [ H : context[SeqNumLe _ _ = false] |- _ ] => rewrite SeqNumLe_false in H
  | [ H : context[SeqNumLt _ _ = true]  |- _ ] => rewrite SeqNumLt_true  in H
  | [ H : context[SeqNumLt _ _ = false] |- _ ] => rewrite SeqNumLt_false in H

  | [ |- context[SeqNumLe _ _ = true]  ] => rewrite SeqNumLe_true
  | [ |- context[SeqNumLe _ _ = false] ] => rewrite SeqNumLe_false
  | [ |- context[SeqNumLt _ _ = true]  ] => rewrite SeqNumLt_true
  | [ |- context[SeqNumLt _ _ = false] ] => rewrite SeqNumLt_false

  | [ H : is_primary _ _ = true |- _ ] => apply is_primary_true in H

  | [ H : broadcast2others _ _ = _ |- _ ] =>
    complete (unfold broadcast2others in H; (*ginv*) conflicting_sends)
  end.

Ltac unfold_handler :=
  match goal with
  | [ H : context[PBFThandle_request              _ _ _] |- _ ] => unfold PBFThandle_request              in H
  | [ H : context[PBFThandle_pre_prepare          _ _ _] |- _ ] => unfold PBFThandle_pre_prepare          in H
  | [ H : context[PBFThandle_prepare              _ _ _] |- _ ] => unfold PBFThandle_prepare              in H
  | [ H : context[PBFThandle_commit               _ _ _] |- _ ] => unfold PBFThandle_commit               in H
  | [ H : context[PBFThandle_checkpoint           _ _ _] |- _ ] => unfold PBFThandle_checkpoint           in H
  | [ H : context[PBFThandle_reply                _ _ _] |- _ ] => unfold PBFThandle_reply                in H
  | [ H : context[PBFThandle_check_ready          _ _ _] |- _ ] => unfold PBFThandle_check_ready          in H
  | [ H : context[PBFThandle_check_bcast_new_view _ _ _] |- _ ] => unfold PBFThandle_check_bcast_new_view in H
  | [ H : context[PBFThandle_start_timer          _ _ _] |- _ ] => unfold PBFThandle_start_timer          in H
  | [ H : context[PBFThandle_expired_timer        _ _ _] |- _ ] => unfold PBFThandle_expired_timer        in H
  | [ H : context[PBFThandle_view_change          _ _ _] |- _ ] => unfold PBFThandle_view_change          in H
  | [ H : context[PBFThandle_new_view             _ _ _] |- _ ] => unfold PBFThandle_new_view             in H
  | [ H : context[PBFThandle_debug                _ _ _] |- _ ] => unfold PBFThandle_debug                in H
  end.

Ltac unfold_handler_concl :=
  match goal with
  | [ |- context[PBFThandle_request              _ _ _] ] => unfold PBFThandle_request
  | [ |- context[PBFThandle_pre_prepare          _ _ _] ] => unfold PBFThandle_pre_prepare
  | [ |- context[PBFThandle_prepare              _ _ _] ] => unfold PBFThandle_prepare
  | [ |- context[PBFThandle_commit               _ _ _] ] => unfold PBFThandle_commit
  | [ |- context[PBFThandle_checkpoint           _ _ _] ] => unfold PBFThandle_checkpoint
  | [ |- context[PBFThandle_reply                _ _ _] ] => unfold PBFThandle_reply
  | [ |- context[PBFThandle_check_ready          _ _ _] ] => unfold PBFThandle_check_ready
  | [ |- context[PBFThandle_check_bcast_new_view _ _ _] ] => unfold PBFThandle_check_bcast_new_view
  | [ |- context[PBFThandle_start_timer          _ _ _] ] => unfold PBFThandle_start_timer
  | [ |- context[PBFThandle_expired_timer        _ _ _] ] => unfold PBFThandle_expired_timer
  | [ |- context[PBFThandle_view_change          _ _ _] ] => unfold PBFThandle_view_change
  | [ |- context[PBFThandle_new_view             _ _ _] ] => unfold PBFThandle_new_view
  | [ |- context[PBFThandle_debug                _ _ _] ] => unfold PBFThandle_debug
  end.

Ltac pbft_simplifier :=
  let stac := (fun _ => pbft_simplifier_step) in
  simplifier stac.

Ltac pbft_dest_all name :=
  let stac := fun _ => pbft_simplifier_step in
  let ftac := fun _ => try (fold DirectedMsgs in * ) in
  dest_all
    name
    stac
    ftac.

Ltac smash_pbft_tac tac :=
  let stac := fun _ => pbft_simplifier_step in
  let ftac := fun _ => try (fold DirectedMsgs in * ) in
  let atac := fun _ => (autorewrite with pbft in * ) in
  smash_byzeml_tac
    tac
    stac
    ftac
    atac.

Ltac smash_pbft1  := let tac := fun _ => (eauto 1 with pbft) in smash_pbft_tac tac.
Ltac smash_pbft2  := let tac := fun _ => (eauto 2 with pbft) in smash_pbft_tac tac.
Ltac smash_pbft3  := let tac := fun _ => (eauto 3 with pbft) in smash_pbft_tac tac.
Ltac smash_pbft4  := let tac := fun _ => (eauto 4 with pbft) in smash_pbft_tac tac.
Ltac smash_pbft5  := let tac := fun _ => (eauto 5 with pbft) in smash_pbft_tac tac.
Ltac smash_pbft6  := let tac := fun _ => (eauto 6 with pbft) in smash_pbft_tac tac.
Ltac smash_pbft7  := let tac := fun _ => (eauto 7  with pbft) in smash_pbft_tac tac.
Ltac smash_pbft8  := let tac := fun _ => (eauto 8  with pbft) in smash_pbft_tac tac.
Ltac smash_pbft9  := let tac := fun _ => (eauto 9  with pbft) in smash_pbft_tac tac.
Ltac smash_pbft10 := let tac := fun _ => (eauto 10 with pbft) in smash_pbft_tac tac.

Ltac smash_pbft := smash_pbft3.

Ltac unfold_handlers := repeat unfold_handler.

Ltac smash_handlers1  := unfold_handlers; smash_pbft1.
Ltac smash_handlers2  := unfold_handlers; smash_pbft2.
Ltac smash_handlers3  := unfold_handlers; smash_pbft3.
Ltac smash_handlers4  := unfold_handlers; smash_pbft4.
Ltac smash_handlers5  := unfold_handlers; smash_pbft5.
Ltac smash_handlers6  := unfold_handlers; smash_pbft6.
Ltac smash_handlers7  := unfold_handlers; smash_pbft7.
Ltac smash_handlers8  := unfold_handlers; smash_pbft8.
Ltac smash_handlers9  := unfold_handlers; smash_pbft9.
Ltac smash_handlers10 := unfold_handlers; smash_pbft10.

Ltac smash_handlers := smash_handlers3.

Ltac unfold_handlers_concl := repeat unfold_handler_concl.

Ltac smash_handlers_concl1  := unfold_handlers_concl; smash_pbft1.
Ltac smash_handlers_concl2  := unfold_handlers_concl; smash_pbft2.
Ltac smash_handlers_concl3  := unfold_handlers_concl; smash_pbft3.
Ltac smash_handlers_concl4  := unfold_handlers_concl; smash_pbft4.
Ltac smash_handlers_concl5  := unfold_handlers_concl; smash_pbft5.
Ltac smash_handlers_concl6  := unfold_handlers_concl; smash_pbft6.
Ltac smash_handlers_concl7  := unfold_handlers_concl; smash_pbft7.
Ltac smash_handlers_concl8  := unfold_handlers_concl; smash_pbft8.
Ltac smash_handlers_concl9  := unfold_handlers_concl; smash_pbft9.
Ltac smash_handlers_concl10 := unfold_handlers_concl; smash_pbft10.

Ltac smash_handlers_concl := smash_handlers_concl3.

Ltac hide_concl := apply ltac_something_show.
Ltac show_concl := apply ltac_something_hide.

Ltac clear_current_view :=
  let cv := fresh "cv" in
  match goal with
  | [ H : context[current_view ?x] |- _ ] => remember (current_view x) as cv
  end;
  match goal with
  | [ H : cv = current_view _ |- _ ] => clear H
  end.

Ltac hide_current_view :=
  let cv := fresh "cv" in
  match goal with
  | [ H : context[current_view ?x] |- _ ] => remember (current_view x) as cv
  end;
  match goal with
  | [ H : cv = current_view _ |- _ ] => hide_hyp H
  end.

Ltac pbft_gen_inv :=
  let stac := (fun _ => pbft_simplifier_step) in
  gen_inv stac.

Ltac pbftLR :=
  first [complete auto
        |complete (left;  eauto 2 with eo pbft; pbftLR)
        |complete (right; eauto 2 with eo pbft; pbftLR)].

Ltac eproves :=
  repeat eexists; eauto; simpl; try eassumption; autorewrite with eo; auto.

Ltac smash_pbft_ind_tac ind base_tac ind_tac :=
  let d   := fresh "d" in
  let hyp := fresh "hyp" in
  match goal with
  | [ H : state_sm_before_event ?sm ?e = Some ?s |- _ ] =>
    let K := fresh H in
    rewrite <- ite_first_state_sm_on_event_as_before in H;
    unfold ite_first in H;
    destruct (dec_isFirst e) as [d|d]; pbft_gen_inv;
    try (complete (try clear_current_view; simpl in *; subst; simpl in *;
                   pbft_simplifier; base_tac ();
                   simpl in *; try iffalse;
                   try congruence; try omega));
    first[fail
         |idtac;[];
          repeat (autodimp ind hyp);
          first[fail
               |idtac;[];
                dup H as K;
                try (complete eproves);
                try (eapply ind in K; eauto; clear ind);
                ind_tac ();
                exrepnd;
                repeat (eexists;[]);
                dands; eauto; eauto 3 with eo pbft;
                complete (repndors; tcsp; try pbftLR; try congruence; try omega)
               ]
         ]
  end.

Ltac smash_pbft_ind ind :=
  let base_tac := (fun _ => smash_pbft) in
  let ind_tac  := (fun _ => eauto 2 with pbft) in
  smash_pbft_ind_tac ind base_tac ind_tac.

Ltac prove_left := eauto 2 with pbft; repndors; tcsp; []; left.

Ltac smash_pbft_ind2 ind :=
  let base_tac := (fun _ => smash_pbft) in
  let ind_tac  := (fun _ => prove_left) in
  smash_pbft_ind_tac ind base_tac ind_tac.

Ltac smash_pbft_ind3 ind :=
  let base_tac := (fun _ => smash_pbft) in
  let ind_tac  := (fun _ => eauto 3 with pbft) in
  smash_pbft_ind_tac ind base_tac ind_tac.

Ltac smash_pbft_ind4 ind :=
  let base_tac := (fun _ => smash_pbft) in
  let ind_tac  := (fun _ => eauto 4 with pbft) in
  smash_pbft_ind_tac ind base_tac ind_tac.

Ltac smash_pbft_ind5 ind :=
  let base_tac := (fun _ => smash_pbft) in
  let ind_tac  := (fun _ => eauto 5 with pbft) in
  smash_pbft_ind_tac ind base_tac ind_tac.

Ltac smash_pbft_ind6 ind :=
  let base_tac := (fun _ => smash_pbft) in
  let ind_tac  := (fun _ => eauto 6 with pbft) in
  smash_pbft_ind_tac ind base_tac ind_tac.

Ltac smash_pbft_ind6_6 ind :=
  let base_tac := (fun _ => smash_pbft6) in
  let ind_tac  := (fun _ => eauto 6 with pbft) in
  smash_pbft_ind_tac ind base_tac ind_tac.

Ltac smash_pbft_ind6_7 ind :=
  let base_tac := (fun _ => smash_pbft6) in
  let ind_tac  := (fun _ => eauto 7 with pbft) in
  smash_pbft_ind_tac ind base_tac ind_tac.

Ltac smash_pbft_ind6_8 ind :=
  let base_tac := (fun _ => smash_pbft6) in
  let ind_tac  := (fun _ => eauto 8 with pbft) in
  smash_pbft_ind_tac ind base_tac ind_tac.

Ltac smash_pbft_ind6_9 ind :=
  let base_tac := (fun _ => smash_pbft6) in
  let ind_tac  := (fun _ => eauto 9 with pbft) in
  smash_pbft_ind_tac ind base_tac ind_tac.

Ltac smash_pbft_ind6_10 ind :=
  let base_tac := (fun _ => smash_pbft6) in
  let ind_tac  := (fun _ => eauto 10 with pbft) in
  smash_pbft_ind_tac ind base_tac ind_tac.

Ltac rename_hyp_with oldname newname :=
  match goal with
  | [ H : context[oldname] |- _ ] => rename H into newname
  end.
