(*
Authors: 
    * Cosmin Manea (1298542)

Creation date: 23 May 2021

Version of the "Because ... both/either ..." tactic.
This tactic uses an already existing result to prove that more results hold.
It is a form of forward reasoning.

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



(*
    Destruct an AND hypothesis into its respective two parts.

    Arguments:
        * s: constr, the AND hypothesis.
        * u: ident, the name of the first part of s.
        * v: ident, the name of the second part of s.

    Does:
        * destruct s into its two respective parts.
*)
Ltac2 and_hypothesis_destruct s u v :=
    destruct $s as [u v].



(*
    Destruct an OR hypothesis into its respective two parts.

    Arguments:
        * s: constr, the OR hypothesis.
        * u: ident, the name of the first part of s.
        * v: ident, the name of the second part of s.

    Does:
        * destruct s into its two respective parts.
*)
Ltac2 or_hypothesis_destruct s u v :=
    destruct $s as [u | v].



Ltac2 Notation "Because" s(constr) "both" u(ident) "and" v(ident) :=
    and_hypothesis_destruct s u v.

Ltac2 Notation "Because" s(constr) "both" u(ident) ":" t_u(constr) "and" v(ident) ":" t_v(constr) :=
    and_hypothesis_destruct s u v.

Ltac2 Notation "Because" s(constr) "either" u(ident) "or" v(ident) :=
    or_hypothesis_destruct s u v.