(** * proof_finishing_tactics.v
Authors: 
    - Cosmin Manea (1298542)

Creation date: 06 June 2021

Tactics for finishing a proof.
--------------------------------------------------------------------------------

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Option.

Add LoadPath "C:/Users/cosmi/Desktop/SEP - CM forward reasoning/waterproof/coq_tactics/new_wplib/tactics/" as wplib.
Load it_holds_that.

(** * reflexivity_and_trivial
    Tries to finish a proof by using the [reflexivity] and [trivial] tactics.

    Arguments:
        - no arguments.

    Does:
        - tries to apply [reflexivity] first, then [trivial].
*)
Local Ltac2 reflexivity_and_trivial () :=
    try reflexivity; try trivial.


Ltac2 Notation "This" "follows" "by" "reflexivity" :=
    reflexivity.

Ltac2 Notation "This" "concludes" "the" "proof" :=
    reflexivity_and_trivial ().

Ltac2 Notation "This" "follows" "by" "assumption" :=
    assumption.

Ltac2 Notation "Then" s(ident) ":" conclusion(constr) "holds" "by" "assumption" :=
    assert_and_prove_sublemma s conclusion None.