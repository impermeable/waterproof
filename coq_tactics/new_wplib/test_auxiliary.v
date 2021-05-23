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
            match (Constr.equal x_head y_head) with
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

(*
    Assert that the hypothesis of the given ident
    exists in the current environment.

    Arguments:
        * x, y: (constr list), lists of constr's to be compared.

    Raises Exceptions:
        * TestFailedError, if x and y have a different length.
        * TestFailedError, if there exists an i such that x[i] ≠ y[i].
*)
Ltac2 assert_hyp_exists (h: ident) :=
    match Control.case (fun () => Control.hyp h) with
    | Val _ => print(concat (of_string "Indeed hyp exists:") (of_ident h))
    | Err exn => print (of_exn exn); fail_test "Hyp not found"
    end.


(*
    Assert that the constr-variable describes 
    a Gallina bool with value "true".

    Arguments:
        * b: bool, should equal "true"

    Raises Exceptions:
        * TestFailedError, if b is not a bool.
        * TestFailedError, if b is false.
*)
Ltac2 assert_constr_is_true (b:constr) :=
    match Constr.equal b constr:(true) with
    | true => print (of_string "Test passed: received constr:(true)")
    | false => fail_test "Did not get a constr equal to a bool with value true"
    end.

(*
    Assert that the Ltac2-variable is a bool with value "true".

    Arguments:
        * b: bool, should equal "true"

    Raises Exceptions:
        * TestFailedError, if b is not a bool.
        * TestFailedError, if b is false.
*)
Ltac2 assert_is_true (b:bool) :=
    match b with
    | true => print (of_string "Test passed: received true")
    | false => fail_test "Expected Ltac2 true, got Ltac2 bool 'false'"
    end.

(*
    Assert that the Ltac2-variable is a bool with value "false".

    Arguments:
        * b: bool, should equal "false"

    Raises Exceptions:
        * TestFailedError, if b is not a bool.
        * TestFailedError, if b is TRUE.
*)
Ltac2 assert_is_false (b:bool) :=
    match b with
    | false => print (of_string "Test passed: received false")
    |  true => fail_test "Expected Ltac2 FALSE, got Ltac2 bool 'true'"
    end.