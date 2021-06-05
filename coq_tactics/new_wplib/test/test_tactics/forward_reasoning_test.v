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

(* lra only works in the [R_scope] *)
Local Open Scope R_scope.
Lemma zero_lt_one: 0 < 1.
Proof.
    ltac1:(lra).
Qed.

(* This axiom does not make sense, 
    but therefore we can be sure that [waterprove]
    does not know it without *explicitly* being told to use it.*)
    Axiom zero_is_ten: 0 = 10.


(* -------------------------------------------------------------------------- *)
(** * Testcases for [By ... it holds that ... : ...] *)
Ltac2 Eval (print (of_string "

Testcases for [By ... it holds that ... : ...]:" )).

(** * Test 1
    Base case: intoduce a sublemma with a lemma that proves it
    immediately.

    NOTE: [waterprove] can apparently also find
    [zero_lt_one] by itself.
*)
Lemma test_by_it_holds_1: 0 = 0.
Proof.
    By zero_lt_one it holds that this_lemma:(0 < 1).
    assert_hyp_has_type @this_lemma constr:(0 < 1).
Abort.

(** * Test 2
    Base case: intoduce a sublemma with a lemma that proves it
    immediately. 
    The sublemma cannot be proven without the given lemma!

*)
Lemma test_by_it_holds_2: True.
Proof.
    (* This is just to test if the extra lemma is really needed: *)
    let failure () := It holds that ten_is_zero:(10 = 0) in
    assert_raises_error failure.
    
    By zero_is_ten it holds that ten_is_zero:(10 = 0).
Abort.

(** * Test 3
    Corner case: try a sublemma that cannot be solved,
    at least not with the default lemmas and the provided lemma.
*)
Lemma test_by_it_holds_3: 0 = 0.
Proof.
    let result () := 
        By zero_lt_one it holds that this_lemma:(1 > 2)
    in
    assert_raises_error result.
Abort.


(* -------------------------------------------------------------------------- *)
(** * Testcases for [It holds that ... : ...] *)
Ltac2 Eval (print (of_string "

Testcases for [It holds that ... : ...]:" )).


(** * Test 1
    Base case: intoduce a sublemma that can be proven immediately.
*)
Lemma test_it_holds_1: 0 = 0.
Proof.
    It holds that this_lemma:(True).
    assert_hyp_has_type @this_lemma constr:(True).
Abort.


(** * Test 2
    Corner case: try a sublemma that cannot be solved,
    at least not with the default lemmas [waterprove] uses.
*)
Lemma test_it_holds_2: 0 = 0.
Proof.
    let result () := 
        It holds that this_lemma:(1 > 2)
    in
    assert_raises_error result.
Abort.

(** * Example for the SUM.
    Somewhat more realistic context.
*)

Open Scope nat_scope.
Inductive even : nat -> Prop :=
    even0 : even 0
  | evenS : forall x:nat, even x -> even (S (S x)).

Lemma it_holds_example: forall x:nat, x > 1 /\ x < 3 -> even x.
Proof.
    intros x h.
    It holds that x_is_two: (x = 2).
    rewrite x_is_two. (* Change the goal to "even 2"*)
    apply evenS. (* Change the goal to "even 0"*)
    apply even0.
Qed.

Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [We conclude that ... ] *)
Ltac2 Eval (print (of_string "

Testcases for [We conclude that ...]:" )).

(** * Test 1
    Base case: should easily be possible to finish the goal.
*)
Lemma test_we_conclude_1: True.
Proof.
    We conclude that True.
Qed.

(** * Test 2
    Error case: wrong goal provided.
*)
Lemma test_we_conclude_2: True.
Proof.
    let result () := We conclude that False in
    assert_raises_error result.
Abort.

(** * Test 3
    Warning case: provided goal is equivalent, 
        but uses an alternative notation.
*)
Lemma test_we_conclude_3: 2 = 2.
Proof.
    Ltac2 Eval (print (of_string "Should raise warning:")).
    We conclude that (1+1 = 2).
Qed.

(** * Test 4
    Base case, like test 1 but more complex goal.
*)
Lemma test_we_conclude_4: forall A: Prop, (A \/ ~A  -> True).
Proof.
    intros A h.
    We conclude that (True).
Qed.

(** * Test 5
    Error case: Waterprove cannot find proof
    (because the statement is false!).
*)
Lemma test_we_conclude_5: 0 = 1.
Proof.
    let result () := We conclude that (0 = 1) in
    assert_raises_error result.
Abort.


(* -------------------------------------------------------------------------- *)
(** * Testcases for [By ... we conclude that ... ] *)
Ltac2 Eval (print (of_string "

Testcases for [By ... we conclude that ...]:" )).

(** * Test 1
    Base case: should easily be possible to finish the goal,
    even with the provided lemma.

    NOTE: this test would also pass if we just
    write 
    [We conclude that (2 = 1).]
    Applarently, waterprove is powerful enough to apply symmetry to hypotheses.
*)
Lemma test_by_we_conclude_1: (1 = 2) -> (2 = 1).
Proof.
    intros h.
    apply eq_sym in h. (* Rewrite h as (2 = 1) using symmetry of "="*)
    By h we conclude that (2 = 1).
Qed.


(** * Test 2
    Base case: should easily be possible to finish the goal,
    but only with the given lemma.
*)
Lemma test_by_we_conclude_2: 0 + 0 = 20.
Proof.
    
    assert (zero_plus_zero_is_twenty: 0+0 = 20).
    rewrite zero_is_ten. (* Get goal: [10 + 10 = 20]*)
    ltac1:(lra).

    (* This is just to test if the extra lemma is really needed: *)
    let failure () := We conclude that (0 + 0 = 10) in
    assert_raises_error failure.
    
    By zero_plus_zero_is_twenty we conclude that (0 + 0 = 20).
Qed.

(** * Test 3
    Warning case: provided goal is equivalent, 
        but uses an alternative notation.
*)
Lemma test_by_we_conclude_3: 2 = 1 + 1.
Proof.
    Ltac2 Eval (print (of_string "Should raise warning:")).
    By zero_lt_one we conclude that (2 = 2).
Qed.

(** * Test 4
    Error case: Waterprove cannot find proof
    (because the statement is false,
    even with the given lemma).
*)
Lemma test_by_we_conclude_4: 0 = 1.
Proof.
    let result () := By zero_is_ten we conclude that (0 = 1) in
    assert_raises_error result.
Abort.

(** * Test 5
    Shows that [waterprove]
    can solve [(1 < 2)]
    without explcitly being given 
    the lemma that states [0 < 1].
*)
Lemma test_it_holds_5: 1 < 2.
Proof.
    assert (useless: 1 = 1).
    reflexivity.

    By useless we conclude that (1 < 2).
Qed.
