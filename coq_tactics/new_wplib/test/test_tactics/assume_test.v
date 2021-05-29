(*
Authors: 
    * Lulof Pirée (1363638)
Creation date: 20 May 2021

Testcases for "assume.v".
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
Load assume.

(*
--------------------------------------------------------------------------------
*)
(** * Testcases for [intro_hyp_from_list]
    (These require some auxiliary functions which are defined first)
*)

(** Subroutine of map_to_second_elem *)
Local Ltac2 rec map_to_second_elem_recursion (x : (ident*constr) list)
                                             (result: (constr list)) :=
    match x with
    | head::tail =>
        match head with
        | (s, t) => map_to_second_elem_recursion tail (List.append result [t])
        | _ => Control.zero (CannotHappenError "x malformed")
        end
    | [] => result
    end.

(** * map_to_second_elem
    Map a list of tuples [(s1, t1), (s2, t2), (s3, t3) ...]
    to a list of the second elements [t1, t2, t3, ...].

    Arguments:
        - [x: (ident * constr) list]
    
    Returns:
        - [constr list], second elements of each tuple in [x].
*)
Ltac2 map_to_second_elem (x : (ident*constr) list) :=
    map_to_second_elem_recursion x [].


(** * assert_second_elems_equal
    Given two [(ident*constr) list], 
    check if they have the same length,
    and if at every index, the second element of the tuple at that index
    is the same for both lists.

    Raises exceptions:
        - [TestFailedError], if [x] and [y] have a different length.
        - [TestFailedError], if there exists an [i] 
                             such that [x[i][1] ≠ y[i][1]].

*)
Ltac2 assert_second_elems_equal (x : (ident*constr) list) 
                                (y : (ident*constr) list) :=
    assert_list_equal (map_to_second_elem x) (map_to_second_elem y).

    
    

(** 
    * Test 1
    Assert the input hypothesis gets renamed 
    to the ident given in the matching tuple of the input list. 
*)
Goal 0=0 -> 1=1.
    intros h.
    intro_hyp_from_list ((@a, constr:(2=2))::(@b, constr:(3=3))::(@c, constr:(0=0))::[]) @h.
    assert_hyp_exists @c.
Abort.

(**
    * Test 2
    Assert the matching tuple is removed from the output list.
    Case: matching tuple is last.
*)
Goal 0=0 -> 1=1.
    intros h.
    let result :=
        intro_hyp_from_list ((@b, constr:(3=3))::(@c, constr:(0=0))::[]) @h
    in
    assert_second_elems_equal (result_t2 ()) ((@b, constr:(3=3))::[]).
Abort.

(**
    * Test 3
    Assert the matching tuple is removed from the output list.
    Case: matching tuple is first.
*)
Goal 0=0 -> 1=1.
    intros h.
    let result :=
        intro_hyp_from_list ((@b, constr:(0=0))::(@c, constr:(9=9))::[]) @h
    in
    assert_second_elems_equal result ((@c, constr:(9=9))::[]).
Abort.

(**
    * Test 4
    It is also allowed to use a different name than [h].
*)
Goal 0=0 -> 1=1.
    intros m.
    intro_hyp_from_list ((@b, constr:(0=0))::(@c, constr:(9=9))::[]) @m.
Abort.

(**
    * Test 5
    Only 1 item in the list.
*)
Goal 0=0 -> 1=1.
    intros m.
    let result := intro_hyp_from_list ((@b, constr:(0=0))::[]) @m in
    assert_second_elems_equal result [].
Abort.

(*
--------------------------------------------------------------------------------
*) 
(** * Testcases for [hyp_is_in_list]
*)

(** * Test 1
    The item is in the list, should resolve to true.
*)
Goal 0=0 -> 1=1.
    intros h.
        
    assert_is_true (
        hyp_is_in_list ((@a, constr:(2=2))::(@b, constr:(3=3))
                        ::(@c, constr:(0=0))::[]) @h).
Abort.

(** * Test 2
    The item is NOT in the list, 
    should resolve to false.
*)
Goal 0=0 -> 1=1.
    intros h.
        
    assert_is_false (
        hyp_is_in_list ((@a, constr:(2=2))::(@b, constr:(3=3))
                        ::(@c, constr:(1=1))::[]) @h).
Abort.

(** * Test 3
    Corner case: only one item in the list.
*)
Goal 0=0 -> 1=1.
    intros h.
        
    assert_is_true (
        hyp_is_in_list ((@c, constr:(0=0))::[]) @h).
Abort.

(* ---------------------------------------------------------------------------*)
(**
    * Testcases for [assume_premise_with_breakdown].
*)
Ltac2 Eval print(of_string "Testcases for [assume_premise_with_breakdown]").

Goal forall n, n = 1 /\ n = 2 -> False.
    intros n.
    let inp_list := ((@h0, constr:(n = 1))::(@h1, constr:(n = 2))::[]) in
    assume_premise_with_breakdown inp_list.
Abort.

