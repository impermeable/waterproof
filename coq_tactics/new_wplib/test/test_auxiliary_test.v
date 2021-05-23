(*
Author: Lulof Pirée (1363638)
Creation date: 20 May 2021

Testcases for the functions used to build testcases.
It is assumes that "assert_raises_error" is correct,
and using this assumption it is tested that the other
functions in "test_auxiliary.v" are correct.

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

(*
--------------------------------------------------------------------------------
    Testcases for "assert_list_equal"
*)
Ltac2 Eval assert_list_equal (constr:(1)::constr:(2)::constr:(3)::[])
                             (constr:(1)::constr:(2)::constr:(3)::[]).

Ltac2 Eval assert_list_equal [] [].                             

Ltac2 Eval assert_raises_error (fun () =>
assert_list_equal (constr:(1)::constr:(3)::[]) (constr:(2)::constr:(3)::[]) ).

(*
--------------------------------------------------------------------------------
    Testcases for "assert_hyp_exists"
*)
Goal forall n, n = 1.
    intros n.
    assert_hyp_exists @n.
    assert_raises_error (fun () => assert_hyp_exists @x).
Abort.


(*
--------------------------------------------------------------------------------
    Testcases for "assert_constr_is_true"
*)
Ltac2 Eval assert_constr_is_true constr:(true).
Ltac2 Eval assert_raises_error 
    (fun () => assert_constr_is_true constr:(false)).
    Ltac2 Eval assert_raises_error 
    (fun () => assert_constr_is_true constr:(1)).

(*
--------------------------------------------------------------------------------
    Testcases for "assert_is_true" and "assert_is_false".
*)
Ltac2 Eval assert_is_true (true).
Ltac2 Eval assert_raises_error 
    (fun () => assert_is_true false).

Ltac2 Eval assert_is_false (false).
Ltac2 Eval assert_raises_error 
    (fun () => assert_is_false true).

(*
--------------------------------------------------------------------------------
    Testcases for "string_equal".
*)
Ltac2 Eval assert_is_true (string_equal "hello" "hello").
Ltac2 Eval assert_is_false (string_equal "hello" "Hello").
Ltac2 Eval assert_is_false (string_equal "hello" "hell").