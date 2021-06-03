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

Module Aux.

(* Defensive programming error *)
Ltac2 Type exn ::= [ CannotHappenError(string) ].



(** * type_of
    Gallina function mapping a term of a type
    to the type itself.

    Arguments:
        - [T:type], any type
        - [x:T], a term of a generic type T.
    Returns:
        - [T], the type of x.
*)
Definition type_of {T : Type} (x : T) := T.

(** * check_constr_type_equal  
    Ltac2 function: [constr -> constr -> bool].
    Check if the normalized TYPE OF [a] is syntactically 
    equal to the normalized TYPE OF [b].

    Arguments:
        - [a, b: constr], any [constr]
    Returns:
        - [bool]:
            - [true] if the TYPES OF [a] and [b] are syntactically equal
                (i.e. are of the same type after normalization)
            - [false] otherwise.
*)  
Ltac2 check_constr_type_equal (a: constr) (b: constr) :=
    Constr.equal (eval cbv in (type_of $a)) (eval cbv in (type_of $b)).

(** * check_constr_equal
    Ltac2 function: [constr -> constr -> bool]
    Check if the normalized form of [a] is syntactically 
    equal to the normalized form of [b].

    Arguments:
        - [a, b: constr], any [constr]
    Returns:
        - [bool]:
            - [true] if a and b are syntactically equal
                (i.e. are of the same type after normalization)
            - [false] otherwise.
*)  
Ltac2 check_constr_equal (a: constr) (b: constr) :=
    Constr.equal (eval cbv in $a) (eval cbv in $b).


(** Subroutine of [print_all_hyps]*)
Local Ltac2 rec print_all_hyps_rec (x : (ident * constr option * constr) list) :=
    match x with
    | head::tail =>
        match head with
        | (name, dunno, type) => Message.print
            (Message.concat 
                (Message.concat (Message.of_ident name) 
                                (Message.of_string " : "))
                (Message.of_constr type)
            );
            print_all_hyps_rec tail
        | _ => Control.zero (CannotHappenError "Cannot happen")
        end
    | [] => ()
    end.

(** * print_all_hyps
    Print all hypotheses of the current context as [ident : type] pairs,
    each on a separate line.
*)
Ltac2 print_all_hyps () := print_all_hyps_rec (Control.hyps ()).


(** * print_bool
    Prints the value of an Ltac2 [bool] to the output.

    Arguments:
        - [b: bool], any Ltac2 [bool] term.
    
    Does:
        - print "true" if [b] is [true], print "false" otherwise.
*)
Ltac2 print_bool (b: bool) :=
    match b with
    | true => Message.print (Message.of_string "true")
    | false => Message.print (Message.of_string "false")
    end.

(** * ltac2_assert
    Introduce *and prove* a new sublemma.
    Wrapper for the build-in Gallina [assert] statement
    that can accept Ltac2 variables as arguments.
    Includes a 'by' clause as used in
    [assert (... : ...) by ...].

    Arguments:
        - [id: ident], name of the new sublemma to prove.
        - [lemma_content: constr], new proposition to prove.
        - [by_arg: unit -> unit], 
            function that tries the prove the new sublemma.
*)
Ltac2 ltac2_assert_with_by (id: ident) (lemma_constent: constr)
                           (by_arg: unit -> unit) :=
    (** [Std.assert] expects an [AssertType] as argument.
        An [AssrtType] consist of three parts:
        - an [intropatterns opt]. 
            The whole [(Some (Std.IntroNaming (Std.IntroIdentifier id)))] 
            thing just wraps an [ident] into an optional [intropatterns].
        - A [constr], the actual propositions to assert.
        - Optionally, the method to prove the proposition 
            (e.g. manually done with "by [something]"). 
            This is an optional [unit -> unit]. 
            It is a series of tactic executions used to prove the [constr].
    *)
    Std.assert (Std.AssertType 
        (Some (Std.IntroNaming (Std.IntroIdentifier id))) 
        lemma_constent (Some by_arg)).

(** * ltac2_assert
    Introduce a new sublemma.
    Wrapper for the build-in Gallina [assert] statement
    that can accept Ltac2 variables as arguments.

    Arguments:
        - [id: ident], name of the new sublemma to prove.
        - [lemma_content: constr], new proposition to prove.
*)
Ltac2 ltac2_assert (id: ident) (lemma_content: constr) :=
    Std.assert (Std.AssertType 
        (Some (Std.IntroNaming (Std.IntroIdentifier id))) 
        lemma_content None).

End Aux.