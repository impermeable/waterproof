(*
Author: Cosmin Manea (1298542)
Creation date: 20 May 2021

Two tactics for instantiating a variable according to a specific rule:
choose a specific value or when the hypothesis reads ``∃ n : N``, one can define such an `n`.
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


Ltac2 Type exn ::= [ ChooseError(string) ].

Local Ltac2 raise_take_error (s:string) := 
    Control.zero (ChooseError s).



(** *choose_varible_in_exists_goal_with_renaming
    Instantiate a variable in an exists goal, according to a given constructor, and also rename the constructor.

    Arguments:
        * [s: ident], an ident for naming an indefined constr/variable.
        * [t: constr], the requirted constr that needs to be instantiated.

    Does:
        * instantiates the constr t under the name s.

    Raises Exceptions:
        * ChooseError, if the goal is not an exists goal.
*)
Ltac2 choose_variable_in_exists_goal_with_renaming s t :=
    lazy_match! goal with
        | [ |- exists _ : _, _] => pose (s := $t); exists &s
        | [ |- _ ] => raise_take_error("'Choose' can only be applied to 'exists' goals")
    end.



(** *choose_variable_in_exists_no_renaming
    Instantiate a variable in an exists goal, according to a given constructor, without renaming the constructor.

    Arguments:
        * t: constr, the requirted constr that needs to be instantiated.

    Does:
        * instantiates the constr t under the same name.

    Raises Exceptions:
        * ChooseError, if the goal is not an exists goal.
*)
Ltac2 choose_variable_in_exists_no_renaming t :=
    lazy_match! goal with
        | [ |- exists _ : _, _] => exists $t
        | [ |- _ ] => raise_take_error("'Choose' can only be applied to 'exists' goals")
    end.


Ltac2 Notation "Choose" t(constr) :=
    choose_variable_in_exists_no_renaming t.

Ltac2 Notation "Choose" s(ident) ":=" t(constr) :=
    choose_variable_in_exists_goal_with_renaming s t.