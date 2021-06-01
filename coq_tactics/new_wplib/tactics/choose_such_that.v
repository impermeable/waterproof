(*
Author: Cosmin Manea (1298542)
Creation date: 30 May 2021

Various tactics for instantiating a variable according to a specific rule given from a:
previously known result.
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



(** * choose_destrct_without_extra_hypothesis
    Choose a variable such that two additional hypotheses are satisfied.

    Arguments:
        * [s: ident], one of the two hypotheses.
        * [v: constr], the requirted constr that needs to be instantiated.
        * [u: ident], the other hypothesis.

    Does:
        * instantiates the constr v under the hypotheses s and u.

    Raises Exceptions:
        * ExistsError, if the goal is not an exists goal.
*)
Ltac2 choose_destruct_without_extra_hypothesis s u v :=
   destruct $v as [s u].



(** * choose_destruct_with_extra_hypothesis
    Choose a variable such that three additional hypotheses are satisfied.

    Arguments:
        * [s: ident], the first hypothesis.
        * [v: constr], the requirted constr that needs to be instantiated.
        * [u: ident], the second hypothesis.
        * [t: constr], the last hypothesis.

    Does:
        * instantiates the constr v under the hypotheses s, u and .

    Raises Exceptions:
        * ExistsError, if the goal is not an exists goal.
*)
Ltac2 choose_destruct_with_extra_hypothesis s u v t :=
    destruct $v with $t as [s u].



Ltac2 Notation "Choose" s(ident) "such" "that" u(ident) "according" "to" v(constr) withh(opt("with")) t(opt(constr)) :=
    match t with 
        | None => choose_destruct_without_extra_hypothesis s u v
        | Some y => choose_destruct_with_extra_hypothesis s u v t
    end.
