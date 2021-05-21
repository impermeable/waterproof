(*
Authors: 
    * Lulof Pirée (1363638)
Creation date: 20 May 2021

"Assume" can be used to introduce the premise of an implication (⇒)
as an hypothesis. 
There are two version: 
    * one which expectes a type annotation and performs type-checking,
    * one which only requires identifiers, and does not perform type checking.
        It will raise a warning that type annotation is recommended.

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
Add LoadPath "./coq_tactics/new_wplib/" as wplib.
Load auxiliary.


Ltac2 Type exn ::= [ AssumeError(string) ].

Ltac2 raise_assume_error (s:string) := 
    Control.zero (AssumeError s).


Ltac2 rec assume_breakdown (x: (ident*constr) list) :=
    lazy_match! goal with
    | [h:?a/\?b |- _] => ()
    | [|-_] => ()
    end.

(* 
Ltac2 assume_premise_with_breakdown (x: (ident*constr) list) :=
    lazy_match! goal with
    | [ |- ?premise->?conclusion] => Std.intros false premise; assume_breakdown x
    | [|- _] => raise_assume_error "Cannot assume premise: 
                                    goal is not an implication"
    end. *)

(*
--------------------------------------------------------------------------------
    "intro_hyp_from_list" plus subroutines
*)



(* Subroutine of intro_hyp_from_list:
    performs iteration over the list "x",
    in a recursive way.
    "prev" are the previously seen items of "x",
    and "x" will be the remaining items. *)
Local Ltac2 rec intro_hyp_from_list_recursion
    (x: (ident*constr) list) (h: ident) (prev: (ident*constr) list) :=
    match x with
    | tuple::remainder => 
        match tuple with
        | (s, t) =>
            let h' := (eval cbv in (type_of &h)) in
            match (Constr.equal h' t ) with
                | true => Std.rename ((h, s)::[]);
                    (* The type of remainder may be the empty list,
                        so we cannot simply return "remainder::prev"*)
                    match remainder with
                        | head::tail => List.append remainder prev
                        | [] => prev
                    end
                | false => 
                    intro_hyp_from_list_recursion remainder @h ((s, t)::prev)
            end
        (* x is a nonempty list of (ident*constr) tuples. 
            Hence case can never happen! But Ltac2 requires it.*)
        | _ => Control.throw (CannotHappenError "x malformed" )
        end
    | [] => raise_assume_error("Premise not present in given hypotheses")
    end.
(*
    Given a list of (ident, constr) tuples and a hypothesis h,
    searches the list if it contains an entry (s, t)
    such that t judgementally equals the type of h.
    As soon as such a tuple is found, h is renamed to s,
    and a copy of the list with with matching (s, t) tuple removed
    is be returned.

    Arguments:
        * x: a list of (ident, constr) tuples. 
            This are pairs of name:type hypotheses.
        * h: the ident of a hypothesis in the current context.
            (Control.hyp h) should exist.

    Returns:
        * a copy x' of x, such (s, t) ∉ x', 
            where (s, t) ∈ x the first entry in x such that
            t is judgementally equal to (Control.hyp h).

    Raises Exceptions:
        * AssumeError, if there exists no (s, t) ∈ x such that
            t is judgementally equal to (Control.hyp h).
*)
Ltac2 intro_hyp_from_list (x: (ident*constr) list) (h: ident) :=
    intro_hyp_from_list_recursion x h [].
    