(*
Author: Cosmin Manea (1298542)
Creation date: 20 May 2021

Generic auxiliary functions.

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



(*
    Ltac2 function that instantiates a variable
    in an exists goal.

    Arguments:
        * x: a generic constr.
    Returns:
        * instantiated x in an exists goal.

*)

Ltac2 chooseExistsNoIntro x :=
    exists $x.


Ltac2 chooseExistsWithIntro s t :=
    pose (s := $t); exists $s.

Ltac2 chooseDestructThreeArguments s u v :=
    destruct $v as [s u].

Ltac2 chooseDestructFourArguments s u v t :=
    destruct $v with $t as [s u].


Ltac2 Notation "Choose" s(constr) :=
    chooseExistsNoIntro s.

Ltac2 Notation "Choose" s(ident) ":=" t(constr) :=
    chooseExistsWithIntro s t.





(*

Ltac2 Notation "Choose" s(opt(constr)) ofType(opt(":=")) t(constr) :=
    lazy_match! goal with
        | [ |- exists _, _] =>
            match s with
                | None => chooseExistsNoIntro t
                | Some y => chooseExistsWithIntro s t
            end
        | [ |- _ ] => print(of_string "Error")
    end.


*)




Goal forall n: nat, exists  m: nat, (n = m). 
    intro n.
    Choose m := n.
    auto.
Abort.