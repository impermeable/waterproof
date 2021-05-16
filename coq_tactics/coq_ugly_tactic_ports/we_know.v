(* 
Author: Lulof Pirée (1363638)
    & Cosmin Manea
Creation date: 16 May 2021

Tactic that can be used to check if an hypothesis
exists under a given name.

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
Require Import Arith.
Add LoadPath "./coq_tactics/new_wplib/" as new_wplib.
Load auxiliary.
Load test_auxiliary.



Ltac2 Type exn ::= [ WeKnowError(string) ].

Ltac2 raise_we_know_error (s:string) := 
    Control.zero (WeKnowError s).


Ltac2 check_hypothesis (s:ident) (t:constr) :=
    let h := (Control.hyp s) in
    match Constr.equal (eval cbv in (type_of $h)) (eval cbv in $t) with 
    | true => ()
    | false => raise_we_know_error("This hypothesis does not exist.")
    end. 

Ltac2 Notation "We" "know" s(ident) ":" t(constr) := check_hypothesis s t.

(* Test 1: basic functionality of "We know H:..."*)
Goal forall x: nat, x = 3 -> x < 4.
    intros.
    We know H : (x = 3).
    assert (four_is_S_three: 4 = S x).
        rewrite H.
        reflexivity.
    assert (x_smaller_than_succ: x < S x).
        apply gt_Sn_n.
    rewrite <- four_is_S_three in x_smaller_than_succ.
    exact x_smaller_than_succ.
Qed.

(* Test 2: "We know Z:T" should fail in case "Z" is undefined,
    or the type "T" does not match 
    the type of the variable "Z" in the context *)
Goal forall x: nat, x = 3 -> x < 4.
    intros.
    assert_raises_error (fun () => We know H: (x = 999)).
    assert_raises_error (fun () => We know Z: (x = 4)).
Abort.


Definition double := fun (x: nat) => 2*x.

(* Test 3: this test shows why we need "(eval cbv in $t)".
    Without "eval cbv in", "t" would contain "double x",
    while this gets replaced by its definition in 
    "(eval cbv in (type_of $h))".*)
Goal forall x: nat, double x = 4 -> x = 2.
    intros.
    We know H : (double x = 4).
Abort.
