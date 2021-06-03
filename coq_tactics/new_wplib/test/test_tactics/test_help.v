(*
Authors: 
    * Cosmin Manea (1298542)
Creation date: 28 May 2021

Testcases for the "Help" tactic.
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
Load help.

(** Test 0: This should work fine *)
Goal forall n : nat, n = n.
    Help.
Abort.

(** Test 1: This should work fine *)
Goal exists n : nat, n = n.
    Help.
Abort.

(** Test 2: This should work fine *)
Goal forall n : nat, n = n.
    intro n.
    Help.
Abort.

(* Test 3: For some reason, this does not work fine *)
Goal forall n : nat, (n = n) -> (n = n).
    intro n.
    Help.
Abort.