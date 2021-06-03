(*
Authors: 
    * Cosmin Manea (1298542)
Creation date: 30 May 2021

Testcases for the "Choose ... such that ..." tactic.
Tests pass if they can be run without unhandled errors.
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
Add LoadPath "C:/Users/cosmi/Desktop/SEP/waterproof/coq_tactics/new_wplib/tactics/" as wplib.
Load choose_such_that.


Lemma reflexivity_of_nat: forall n : nat, exists m : nat, (n = m).
Proof.
    intro n.
    pose (m := n).
    exists m.
    reflexivity.
Defined. 

(** Test 0: This should work fine *)
Goal forall n : nat, exists m : nat, (n + 1 = m + 1).
    intro n.
    Choose m such that n_eq_m according to (reflexivity of nat n m).
Abort.


(** Test 1: This should work fine *)
Goal forall n : nat, ( ( (n = n) /\ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro H.
    Because H both n_eq_n : nat and n_plus_1_eq_n_plus_1 : nat.
Abort.


(** Test 2: This should work fine *)
Goal forall n : nat, ( ( (n = n) \/ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro H.
    Because H either n_eq_n or n_plus_1_eq_n_plus_1.
Abort.