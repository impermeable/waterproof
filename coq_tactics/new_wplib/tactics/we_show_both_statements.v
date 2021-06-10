(** * we_show_both_statements.v
Authors: 
    - Cosmin Manea (1298542)
Creation date: 22 May 2021

Version of [We show/prove both statements] tactic.
[We show/prove both statements] can be used to split the proof of a conjunction.

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



Ltac2 Type exn ::= [ BothStatementsError(string) ].

Ltac2 raise_both_statements_error (s:string) := 
    Control.zero (BothStatementsError s).


(** * both_directions_and
    Split the proof of a conjuctions statement into both of its parts.

    Arguments:
        - no arguments

    Does:
        - splits the conjunction statement into its both parts.

    Raises Exceptions:
        - [BothStatementsError], if the [goal] is not a conjunction of statments.
*)
Ltac2 both_directions_and () :=
    lazy_match! goal with 
        | [ |- _ /\ _] => split
        | [ |- _ ] => raise_both_statements_error("This is not an 'and' statement, so try another tactic.")
    end.

Ltac2 Notation "We" show(opt("show")) prove(opt("prove")) "both" "statements" := 
    both_directions_and ().