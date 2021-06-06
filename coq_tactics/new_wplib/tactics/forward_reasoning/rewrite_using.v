(*
Authors: 
    - Cosmin Manea (1298542)
Creation date: 06 June 2021

Various versions of [Rewrite] tactic. This allows the user to rewrite the goal.
The tactics allow for multiple rewrites simultaneously, using keywords such as `as, in` etc.
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

Add LoadPath "C:/Users/cosmi/Desktop/SEP - CM forward reasoning/waterproof/coq_tactics/new_wplib/tactics/" as wplib.
Load forward_reasoning_aux.

(** * rewriting
    Rewrites the goal, according to the [waterprove] automation tactic, using an additional statement.

    Arguments:
        - [statement: constr], the additional statement.

    Does:
        - rewrites [goal] using [statement], according to the [waterprove] automation tactic.
*)
Ltac2 rewriting (statement: constr) :=
    let used_lemma := unwrap_optional_lemma None in
    let u := Fresh.in_goal @u in
    let u_val := (Control.hyp u) in
    let by_arg () := waterprove_with_hint statement used_lemma in
    Aux.ltac2_assert_with_by u statement by_arg; rewrite $u_val; clear u.


Ltac2 Notation "Rewrite" "using" t(constr) :=
    rewriting t.


Goal forall n : Q, exists m : Q, (n + 1 = m + 1).
Proof.
    intro.
    assert (n = n) as X.
    {
        auto.
    }
    pose (m := n).
    exists m.
    Rewrite using (n = n).