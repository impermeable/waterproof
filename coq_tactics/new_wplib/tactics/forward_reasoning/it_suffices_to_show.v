(** * [it_suffices_to_show.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 6 June 2021

Tactic [It suffices to show that ...].
Used to assert that a certain statement would be able to prove the goal.
After that, one still needs to prove this statement, but not the original goal.
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

Local Ltac2 fail_suffice_to_show () :=
    Control.zero (AutomationFailure 
"Waterproof could not verify that this statement is enough to prove the goal.").

Local Ltac2 try_enough_expression (f: unit -> unit) 
                           (statement: constr):=
    match Control.case f with
    | Val _ => 
    print (
        concat
            (of_string "It indeed suffices to show that '")
            (concat 
                (of_constr statement)
                (of_string "'.")
            )
    )
    | Err exn => fail_suffice_to_show ()
    end.


Ltac2 apply_enough_with_waterprove (statement:constr) :=
    let g := Control.goal () in
    let hyp_name := Fresh.in_goal @h in
    let f () := enough ($hyp_name : $statement) 
                by (waterprove_with_hint g constr:(dummy_lemma))
    in
    try_enough_expression f statement.

Ltac2 Notation "It" "suffices" "to" "show" "that" 
    statement(constr) := 
    apply_enough_with_waterprove statement.

Ltac2 apply_enough_with_tactic (statement:constr) (tac:unit -> unit) :=
    let hyp_name := Fresh.in_goal @h in
    let f () := enough ($hyp_name : $statement) by (tac ())
    in
    try_enough_expression f statement.


Ltac2 Notation "It" "suffices" "to" "show" "that" 
    statement(constr) "by" tac(thunk(tactic)) := 
    apply_enough_with_tactic statement tac.