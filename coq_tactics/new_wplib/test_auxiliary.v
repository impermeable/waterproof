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

(*  Same function as [type_of] in [auxiliary.v].
        Repeated here to avoid double imports
        in modules that import both 
        [auxiliary.v] AND [test_auxiliary.v]. *)
Definition type_of_test_aux {T : Type} (x : T) := T.

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

(** * assert_hyp_exists
    Assert that the hypothesis of the given ident
    exists in the current environment.

    Arguments:
        - [h : ident], identifier of target hypothesis

    Raises Exceptions:
        - [TestFailedError], if there is no hypothesis with the identifier
            stored in [h] in the current context.
*)
Ltac2 assert_hyp_exists (h: ident) :=
    match Control.case (fun () => Control.hyp h) with
    | Val _ => print(concat (of_string "Indeed hyp exists:") (of_ident h))
    | Err exn => print (of_exn exn); fail_test "Hyp not found"
    end.

(** * assert_hyp_has_type
    Assert that the hypothesis of the given ident
    exists in the current environment, AND has the indicated type.

    Arguments:
        - [h : ident], identifier of target hypothesis.
        - [t : constr], expected type of the hypothesis identified
            by the value of [h].

    Raises Exceptions:
        - [TestFailedError], if there is no hypothesis with the identifier
            stored in [h] in the current context.
        - [TestFailedError], if the hypothesis identified by [h] has a 
            different type than [t]. Types are normalized before comparison.
*)
Ltac2 assert_hyp_has_type (h: ident) (t: constr) :=
    assert_hyp_exists h;
    let h_val := Control.hyp h in
    let h_normalized :=  (eval cbv in (type_of_test_aux $h_val)) in
    let t_normalized :=  (eval cbv in $t) in
    match Constr.equal h_normalized t_normalized with
    | true => print (concat (concat (of_string "Hypothesis ") (of_ident h))
                            (concat (of_string " indeed has type ") 
                                    (of_constr t))
                    )
    | false => print (
            concat  (concat  (of_string "Expected type: ") 
                            (of_constr t))
                    (concat (of_string ", actual type: ") 
                            (of_constr 
                            (eval cbv in (type_of_test_aux $h_val))))
            );
        fail_test "Hyp has wrong type"
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


Local Ltac2 rec string_equal_rec (idx) (s1:string) (s2:string) :=
    (* If the strings are of unequal length, 
        then they are never equal*)
    let len1 := (String.length s1) in
    let len2 := (String.length s2) in
    match Int.equal len1 len2 with
    | false => false
    | true => 
        (* If we are past the last index of the strings,
        then stop and return "true".
        Otherwise, compare the integer representation
        of the characters of the current index and recurse.*)
        match (Int.equal idx len1) with
        | true => true
        | false =>
            let ascii_int_1 := Char.to_int (String.get s1 idx) in
            let ascii_int_2 := Char.to_int (String.get s2 idx) in
            match Int.equal ascii_int_1 ascii_int_2 with
            | true => string_equal_rec (Int.add idx 1) s1 s2
            | false => false
            end
        end
    end.

(*
    Compare two Ltac2 strings for equality.

    Arguments:
        * s1, s2: string, strings to compare.

    Returns:
        * bool
            - true, if "s1" and "s2" have 
                the same length and the same characters.
            - false otherwise.
*)
Ltac2 string_equal (s1:string) (s2:string) := string_equal_rec 0 s1 s2.

(*
    Assert two Ltac2 strings are equal.

    Arguments:
        * s1, s2: string, strings to compare.

    Raises Exceptions:
        * TestFailedError, if s1 has different characters or a different
            length as s2.
*)
Ltac2 assert_string_equal (s1:string) (s2:string) :=
    match string_equal s1 s2 with
    | true => print (of_string "Test passed: strings are equal")
    | false => fail_test "Strings not equal"
    end.