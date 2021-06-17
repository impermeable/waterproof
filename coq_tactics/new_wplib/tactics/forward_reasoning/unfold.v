(** * unfold.v
Authors: 
    - Cosmin Manea (1298542)

Creation date: 06 June 2021

Version of [Unfold] tactic. This unfolds a definition.
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
From Ltac2 Require Import Option.

(** * unfolding
    Unfolds the definition of a statement, possibly inside another statement.

    Arguments:
        - [t: constr], the statement to unfold the definition for.
        - [s: constr option], a possible additional statement, where [t] can be unfolded in.

    Does:
        - unfolds [t] in the current [goal], or in [s].
*)
Local Ltac2 unfolding (t: constr) (s: constr option) :=
    match s with 
        | None => unfold &t
        | Some y => unfold &t in y
    end.


Ltac2 Notation "Unfold" t(constr) inn(opt("in")) s(opt(constr)):=
    unfolding t s.