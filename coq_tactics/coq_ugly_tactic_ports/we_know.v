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


Ltac2 hypothesis_checking (s:ident) (t:constr) :=
    let h := (Control.hyp s) in
    match Constr.equal (eval cbv in (type_of $h)) t with 
    | true => ()
    | false => raise_we_know_error("This hypothesis does not exist.")
    end. 

Ltac2 Notation "We" "know" s(ident) ":" t(constr) := hypothesis_checking s t.

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

Goal forall x: nat, x = 3 -> x < 4.
    intros.
    assert_raises_error (fun () => We know H: (x = 999)).
    assert_raises_error (fun () => We know Z: (x = 4)).
Abort.
