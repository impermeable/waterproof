(** * test_by_we_know.v
Authors: 
    - Cosmin Manea (1298542)

Creation date: 23 May 2021

Testcases for the [By ... we know ...] tactic.
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
Load by_we_know.


(** Test 0: This should work and assert that (n + 1 = n + 1) if (n = n) *)
Goal forall n : nat, ((n = n) <-> (n + 1 = n + 1)).
Proof.
    intro n.
    split.
    By (n = n) we know (n + 1 = n + 1).
    reflexivity.
    reflexivity.
    reflexivity.
Qed.


(** Test 0: This should work and assert that (n + 1 = m + 1) if (n = m) *)
Goal forall n m : nat, (n = m) <-> (n + 1 = m + 1).
Proof.
    intros.
    split.
    intros.
    By (n = m) we know (n + 1 = m + 1).
    exact H.
    auto with *.
Abort.