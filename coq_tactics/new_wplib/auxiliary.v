(*
Author: Lulof Pirée (1363638)
Creation date: 14 May 2021

Generic auxiliary functions.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.


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

    Arguments:
        * a, b: any constr
    Returns:
        * a bool:
            - true if a and b are judgementally equal
                (i.e. are of the same type after normalization)
            - false otherwise.
*)  
Ltac2 check_constr_type_equal (a: constr) (b: constr) :=
    Constr.equal (eval cbv in (type_of $a)) (eval cbv in (type_of $b)).
