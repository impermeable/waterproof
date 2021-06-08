(*
Authors: 
    - Cosmin Manea (1298542)
    - Lulof Pirée (1363638)
Creation date: 06 June 2021

Various versions of [Rewrite using ...] tactic. 
This tactic is used to rewrite the goal or hypotheses.
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
Load forward_reasoning_aux.

Ltac2 Type exn ::= [ RewriteError(string) ].

Local Ltac2 fail_goal_rewrite () := 
        Control.zero (RewriteError 
            "Could not rewrite goal with this expression").

Local Ltac2 fail_verify_lemma () :=
    Control.zero (AutomationFailure 
        "Could not verify that the replacement expression holds.
You may need to prove this lemma first before rewriting others with it.").

Local Ltac2 print_rewrote_goal_success (lemma: constr) :=
    print(concat 
        (concat
            (of_string "Successfully rewrote goal using '")
            (of_constr lemma)
        )
        (of_string "'.")
    ).

(** * rewrite_attempt
    Try to rewrite the goal using [lemma].
    Throw a custom error in case of failure,
    print a success message otherwise.

    Arguments:
        - [lemma:constr], the lemma (or theorem) used for the rewrite.
            This should be an equality proposition.
        - [target: ident option], optional name of hypothesis to rewrite.
            In case [None] is given, the goal will be rewritten.
        - [to_left: bool], direction in which the lemma should be used.
            - [true], the RHS of [lemma] will be interpreted as the current
                goal/hypothesis, and the goal will be rewritten toward the
                LHS. Equivalent to [rewrite <- ...].
            - [false], vice-versa, so using the normal [rewrite] without [<-].

    Raises exceptions:
        - [RewriteError], in case the goal/hypothesis could not be
            rewritten by [lemma] in the indicated direction.
*)
Local Ltac2 rewrite_attempt (lemma: constr)
                            (target : ident option)
                            (to_left: bool):=
    let f () :=
        match target with
        | None => 
            match to_left with
            | true => (rewrite <- $lemma)
            | false => (rewrite $lemma)
            end
        | Some id => 
            match to_left with
            | true => (rewrite <- $lemma in $id)
            | false => (rewrite $lemma in $id)
            end
        end
    in
    match Control.case f with
    | Val _ => print_rewrote_goal_success lemma
    | Err exn => fail_goal_rewrite ()
    end.

(* TODO: ask Jim if this is needed, if not remove it *)
(* Ltac2 rewrite_with_lemma_check (lemma: constr) :=
    let u := Fresh.in_goal @u in
    let by_arg () := waterprove_with_hint lemma constr:(dummy_lemma)
    in
    let verify_lemma () := Aux.ltac2_assert_with_by u lemma by_arg
    in
    match Control.case verify_lemma with
    | Val _ => clear u; rewrite_attempt lemma
    | Err exn => clear u; fail_verify_lemma ()
    end. *)


(** * Rewrite using ...
    Try to rewrite the goal using [lemma].
    Throw a custom error in case of failure,
    print a success message otherwise.
    Matches the LHS of [lemma] to the goal,
    and tries to change part of expression towards the RHS.

    Arguments:
        - [lemma:constr], the lemma (or theorem) used for the rewrite.
            This should be an equality proposition. 

    Raises exceptions:
        - [RewriteError], in case the goal/hypothesis could not be
            rewritten by [lemma] in the right-to-left direction.
*)
Ltac2 Notation "Rewrite" "using" t(constr) :=
    rewrite_attempt t None false.

(** * Rewrite using ... in ...
    Try to rewrite a hypothesis using [lemma].
    Throw a custom error in case of failure,
    print a success message otherwise.
    Matches the LHS of [lemma] to the goal,
    and tries to change part of expression towards the RHS.

    Arguments:
        - [lemma:constr], the lemma (or theorem) used for the rewrite.
            This should be an equality proposition. 
        - [target: ident], name of hypothesis to rewrite.

    Raises exceptions:
        - [RewriteError], in case the goal/hypothesis could not be
            rewritten by [lemma] in the right-to-left direction.
*)
Ltac2 Notation "Rewrite" "using" t(constr) "in" target(ident):=
    rewrite_attempt t (Some target) false.

(** * Rewrite <- using ...
    Try to rewrite the goal using [lemma].
    Throw a custom error in case of failure,
    print a success message otherwise.
    Matches the RHS of [lemma] to the goal,
    and tries to change part of expression towards the LHS.

    Arguments:
        - [lemma:constr], the lemma (or theorem) used for the rewrite.
            This should be an equality proposition. 

    Raises exceptions:
        - [RewriteError], in case the goal/hypothesis could not be
            rewritten by [lemma] in the left-to-right direction.
*)
Ltac2 Notation "Rewrite" "<-" "using" t(constr) :=
    rewrite_attempt t None true.

(** * Rewrite <- using ... in ...
    Try to rewrite a hypothesis using [lemma].
    Throw a custom error in case of failure,
    print a success message otherwise.
    Matches the RHS of [lemma] to the goal,
    and tries to change part of expression towards the LHS.

    Arguments:
        - [lemma:constr], the lemma (or theorem) used for the rewrite.
            This should be an equality proposition. 
        - [target: ident], name of hypothesis to rewrite.

    Raises exceptions:
        - [RewriteError], in case the goal/hypothesis could not be
            rewritten by [lemma] in the left-to-right direction.
*)
Ltac2 Notation "Rewrite" "<-" "using" t(constr) "in" target(ident):=
    rewrite_attempt t (Some target) true.