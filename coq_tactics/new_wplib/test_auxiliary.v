(*
Author: Lulof Pirée (1363638)
Creation date: 16 May 2021

Auxiliary functions for testing.

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
Load auxiliary.

Ltac2 Type exn ::= [ TestFailedError(string) ].

Local Ltac2 fail_test (s:string) := 
    Control.zero (TestFailedError s).

(*
    Check if the function "f" raises an error when evaluated.

    Arguments:
        * f, function without arguments.
    
    Raises Exceptions:
        * TestFailedError, if the execution of "f"
            does NOT raise a catchable exception.
*)
Ltac2 assert_raises_error f :=
    match Control.case f with
    | Val _ => fail_test "Should raise an error"
    | Err exn => print (concat 
        (of_string "Test passed, got error:") 
        (of_exn exn))
    end.

(*
    Check if two lists (of type "constr list") are equal. 
    Raise an error if they have different lengths,
    or that there exists an index such that their value at that index
    differs.

    Arguments:
        * x, y: (constr list), lists of constr's to be compared.

    Raises Exceptions:
        * TestFailedError, if x and y have a different length.
        * TestFailedError, if there exists an i such that x[i] ≠ y[i].
*)
Ltac2 rec assert_list_equal (x:constr list) (y: constr list) :=
    match x with
    | x_head::x_tail =>
        match y with
        | y_head::y_tail =>
            match (check_constr_equal x_head y_head) with
            | true => assert_list_equal x_tail y_tail
            | false => print(concat (of_string "Unequal elements:") 
                                    (concat (of_constr x_head) 
                                            (of_constr y_head)
                                    )
                            ); fail_test "List have different element"
            end
        | [] => fail_test "First list has more elements"
        end
    | [] => 
        match y with
            | [] => print (of_string "Test passed: lists indeed equal")
            | y_head::y_tai => fail_test "Second list has more elements"
        end
    end.