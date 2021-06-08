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

Local Ltac2 fail_verify_statement () :=
    Control.zero (AutomationFailure 
        "Could not verify that the replacement expression holds.
You may need to prove this statement first before rewriting others with it.").

Local Ltac2 print_rewrote_goal_success (statement: constr) :=
    print(concat 
        (concat
            (of_string "Successfully rewrite goal using '")
            (of_constr statement)
        )
        (of_string "'.")
    ).

(** * rewrite_attempt
    Try to rewrite the goal using [statement].
    Throw a custom error in case of failure,
    print a success message otherwise.

    Arguments:
        - [statement:constr], 
*)
Local Ltac2 rewrite_attempt (statement: constr)
                            (target : ident option)
                            (to_left: bool):=
    let f () :=
        match target with
        | None => 
            match to_left with
            | true => (rewrite <- $statement)
            | false => (rewrite $statement)
            end
        | Some id => 
            match to_left with
            | true => (rewrite <- $statement in $id)
            | false => (rewrite $statement in $id)
            end
        end
    in
    match Control.case f with
    | Val _ => print_rewrote_goal_success statement
    | Err exn => fail_goal_rewrite ()
    end.

(* Ltac2 rewrite_with_statement_check (statement: constr) :=
    let u := Fresh.in_goal @u in
    let by_arg () := waterprove_with_hint statement constr:(dummy_lemma)
    in
    let verify_statement () := Aux.ltac2_assert_with_by u statement by_arg
    in
    match Control.case verify_statement with
    | Val _ => clear u; rewrite_attempt statement
    | Err exn => clear u; fail_verify_statement ()
    end. *)

Ltac2 Notation "Rewrite" "using" t(constr) :=
    rewrite_attempt t None false.

Ltac2 Notation "Rewrite" "using" t(constr) "in" target(ident):=
    rewrite_attempt t (Some target) false.

Ltac2 Notation "Rewrite" "<-" "using" t(constr) :=
    rewrite_attempt t None true.
    
Ltac2 Notation "Rewrite" "<-" "using" t(constr) "in" target(ident):=
    rewrite_attempt t (Some target) true.

Goal forall n : Q, exists m : Q, (n + 1 = m + 1).
Proof.
    intro.
    assert (n = n) as X.
    {
        auto.
    }
    pose (m := n).
    exists m.
    change m with n.
    reflexivity.
Qed.