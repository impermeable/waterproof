(*
Authors: 
    - Cosmin Manea (1298542)

Creation date: 30 May 2021

Testcases for the two [Choose] tactics.
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
Add LoadPath "C:/Users/cosmi/Desktop/SEP/waterproof/coq_tactics/new_wplib" as wplib2.
Load Choose.
Load test_auxiliary.


(** Test 0: This should work fine *)
Goal forall n : nat, exists m : nat, n = m.
Proof.
  intros.
  Choose m := n.
  reflexivity.
Abort.


(** Test 1: This should work fine *)
Goal forall n : nat, exists m : nat, n = m.
    intro n.
    Choose (n).
    reflexivity.
Abort.


(** Test 2: This should work fine *)
Goal forall n : nat, ( ( (n = n) \/ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    assert_raises_error (fun() => Choose (n)).
Abort.


(** Test 3: This should work fine *)
Goal forall n : nat, ( ( (n = n) \/ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    assert_raises_error (fun() => Choose m := n).
Abort.