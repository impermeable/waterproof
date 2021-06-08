(** * write_using.v
Authors: 
    - Lulof Pirée (1363638)
Creation date: 08 June 2021

Contains tactics [Write goal using ...] and [Write ... using ...].
Used to rewrite and finish the goal/hypothesis with a certain equality,
which is then set as a new goal.
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
Load rewrite_using.
Load test_auxiliary.

Ltac2 rewrite_using (lemma: constr)
                    (target_hyp : ident option) 
                    (expected_result: constr) :=
    let f () :=
        match target_hyp with
        | None => rewrite $lemma; apply_enough_with_waterprove expected_result 
        | Some id => Rewrite using $lemma in $id
        end
    in
    f ().

Ltac2 Notation "Write" id(ident) "using" lemma(constr) "as" result(constr) :=
    rewrite_attempt lemma (Some id) false; 
    let assert_expected_result () := (assert_hyp_has_type id result) in
    match Control.zero assert_expected_result with
    | Val _ => ()
    | Err exn => Control.zero (RewriteError 
    "Rewriting the hypothesis with this equality is possible,
but did produce the expected result")
    end.

