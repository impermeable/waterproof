(*
Author: Lulof Pirée (1363638)
Creation date: 14 May 2021

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

(* Defensive programming error *)
Ltac2 Type exn ::= [ CannotHappenError(string) ].


(*
    Gallina function mapping a term of a type
    to the type itself.

    Arguments:
        * x: a term of a generic type T.
    Returns:
        * T: the type of x.
*)
Definition type_of {T : Type} (x : T) := T.

(*  
    Ltac2 function: constr -> constr -> bool.
    Check if the normalized TYPE OF "a" is syntactically 
    equal to the normalized TYPE OF "b".

    Arguments:
        * a, b: constr, any constr
    Returns:
        * bool:
            - true if the TYPES OF a and b are syntactically equal
                (i.e. are of the same type after normalization)
            - false otherwise.
*)  
Ltac2 check_constr_type_equal (a: constr) (b: constr) :=
    Constr.equal (eval cbv in (type_of $a)) (eval cbv in (type_of $b)).

(*  
    Ltac2 function: constr -> constr -> bool.
    Check if the normalized form of "a" is syntactically 
    equal to the normalized form of "b".

    Arguments:
        * a, b: constr, any constr
    Returns:
        * bool:
            - true if a and b are syntactically equal
                (i.e. are of the same type after normalization)
            - false otherwise.
*)  
Ltac2 check_constr_equal (a: constr) (b: constr) :=
    Constr.equal (eval cbv in $a) (eval cbv in $b).