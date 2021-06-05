(*
Authors: 
    - Cosmin Manea (1298542)
Creation date: 28 May 2021

Version of the [Help] tactic.
This tactic gives hints to what should be done to advance the proof state,
depending on the goal.
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
From Ltac2 Require Import Message.



(** * help
    Gives hints on what should be done to advance the proof state, depending
    on the goal.

    Arguments:
        - no arguments.

    Does:
        - Prints hints on what should be done to advance the proof state, depending
          on the goal.
*)
Ltac2 help () :=
    lazy_match! goal with
        | [ |- forall _ : ?u, _ ] => 
              print (concat (concat (of_string "Try to define a variable of type ")
              (of_constr u)) (of_string ", or assume a hypothesis.") )
        | [ |- _ -> _ ] => print (of_string "Try to define a variable, or assume a hypothesis.")
        | [ |- exists _ : ?v, _] => 
              print (concat (concat (of_string "Choose a specific value of type ") (of_constr v)) 
              (of_string "." ))
        | [ |- _ ] => print (of_string "Waterproof currently cannot provide help for this goal.")
    end.

Ltac2 Notation "Help" :=
    help ().