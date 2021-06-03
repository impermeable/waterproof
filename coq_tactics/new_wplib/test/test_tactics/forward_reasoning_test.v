(** * Testcases for [forward_reasoning.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 3 June 2021


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
From Ltac2 Require Option.
From Ltac2 Require Import Message.
Add LoadPath "./coq_tactics/new_wplib/" as wplib.
Load test_auxiliary.
Load forward_reasoning.

Ltac2 Eval first [waterprove_with_hint constr:(0 < 1) constr:(0 < 1) 
                  | print_failure () ].

(* -------------------------------------------------------------------------- *)
(** * Testcases for [By ... it holds that ... : ...] *)

(** * Test 1
    Base case: intoduce a sublemma with a lemma that proves it
    immediately.
*)
Lemma test1: 0 = 0.
Proof.
    By zero_lt_one it holds that this_lemma:(0 < 1).
    assert_hyp_has_type @this_lemma constr:(0 < 1).
Abort.


(** * Test 2
    Corner case: try a sublemma that cannot be solved,
    at least not with the default lemmas and the provided lemma.
*)
Lemma test2: 0 = 0.
Proof.
    let result () := 
        By zero_lt_one it holds that this_lemma:(1 > 2)
    in
    assert_raises_error result.
Abort.


(* -------------------------------------------------------------------------- *)
(** * Testcases for [It holds that ... : ...] *)

(** * Test 1
    Base case: intoduce a sublemma that can be proven immediately.
*)
Lemma test1: 0 = 0.
Proof.
    It holds that this_lemma:(True).
    assert_hyp_has_type @this_lemma constr:(True).
Abort.


(** * Test 2
    Corner case: try a sublemma that cannot be solved,
    at least not with the default lemmas [waterprove] uses.
*)
Lemma test2: 0 = 0.
Proof.
    let result () := 
        It holds that this_lemma:(1 > 2)
    in
    assert_raises_error result.
Abort.




