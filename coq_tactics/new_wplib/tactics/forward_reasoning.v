(** * forward_reasoning.v
Authors: 
    - Lulof Pirée (1363638)
Creation date: 3 June 2021

Tactics that rely on [auto] (usually indirectly via [waterprove]).


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

Require Import Rbase.
Require Import Qreals.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Omega.
Require Import Max.

Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.

Add LoadPath "./coq_tactics/new_wplib/" as wplib.
Load waterprove.
Load goal_to_hint.
Load auxiliary.

(* lra only works in the [R_scope] *)
Local Open Scope R_scope.
Lemma zero_lt_one: 0 < 1.
Proof.
    ltac1:(lra).
Qed.

Lemma dummy_lemma: 0 = 0.
Proof.
    reflexivity.
Qed.

(** * get_search_depth
    Placeholder for the function that retrieves the maximum
    search-depth to pass as an argument to [waterprove].
*)
Local Ltac2 get_search_depth () := 
    print (of_string "Warning: seach depth still hardcoded to '2'.");
    2.

(** * waterprove_with_hint
    First print an hint for reaching the target goal,
    try to prove the goal immediately afterward.

    Arguments:
        - [target_goal: constr], the goal to prove. 
        - [lemmas: constr], lemmas to pass to [waterprove] for automatically
            proving the [target_goal].
*)
Local Ltac2 waterprove_with_hint (target_goal:constr) (lemmas:constr) :=
    print_goal_hint (Some target_goal);
    waterprove target_goal lemmas (get_search_depth ()).

Ltac2 Type exn ::= [ AutomationFailure(string) ].

Local Ltac2 fail_automation () := 
        Control.zero (AutomationFailure 
        "Waterproof could not find a proof. 
If you believe the statement should hold, 
try making a smaller step.").

Local Ltac2 print_failure () :=
    print (of_string "Waterproof could not find a proof. 
If you believe the statement should hold, 
try making a smaller step.").

(** * By ... it holds that ... : ...
    Introduce a new sublemma and try to prove it immediately,
    optionally using a given lemma.

    Arguments:
        - [id: ident], name for the new sublemma.
            If the proof succeeds, 
            it will become a hypotheses bearing [id] as name.
        - [conclusion: constr], the actual content 
            of the new sublemma to prove.
        - [proving_lemma: constr], optional reference to a lemma 
            used to prove the new sublemma (via [waterprove)]).
*)
Ltac2 assert_and_prove_sublemma (id: ident) (conclusion: constr) 
                                (proving_lemma: constr option) :=
    let help_lemma := 
        match proving_lemma with
        | None => constr:(dummy_lemma)
        | Some lemma => lemma
        end
    in
    let by_arg () := first [waterprove_with_hint conclusion help_lemma 
                            | fail_automation () ]
    in
    let proof_attempt () := Aux.ltac2_assert_with_by id conclusion by_arg
    in
    match Control.case proof_attempt with
    | Val _ => print (of_string ("New sublemma successfully added."))
    | Err exn => fail_automation()
    end.

(** * By ... it holds that ... : ...
    Introduce a new sublemma and try to prove it immediately
    using a given lemma.

    Arguments:
        - [lemma: constr], reference to a lemma 
            used to prove the new sublemma (via [waterprove)]).
        - [id: ident], name for the new sublemma.
            If the proof succeeds, 
            it will become a hypotheses bearing [id] as name.
        - [conclusion: constr], the actual content 
            of the new sublemma to prove.
*)
Ltac2 Notation "By" lemma(constr) 
               "it" "holds" "that" id(ident) ":" conclusion(constr) := 
    assert_and_prove_sublemma id conclusion (Some lemma).
    
    
(** * It holds that ... : ...
    Introduce a new sublemma and try to prove it immediately.
    Same as [By ... it holds that ... : ...],
    but without using a specified lemma.

    Arguments:
        - [id: ident], name for the new sublemma.
            If the proof succeeds, 
            it will become a hypotheses bearing [id] as name.
        - [conclusion: constr], the actual content 
            of the new sublemma to prove.
*)
Ltac2 Notation "It" "holds" "that" id(ident) ":" conclusion(constr) :=
    assert_and_prove_sublemma id conclusion None.


(* Below is copied stuff for easy reference. Just as a personal note, should eventually be removed.*)
(* Ltac new_hyp_verified_pose_proof s t u:=
    assert (u : t) by (first [ wp_power t s
                            | idtac "Waterproof could not find a proof. If you believe the statement should hold, try making a smaller step"]).
    Ltac new_hyp_verified_pose_proof_no_name s t:=
    ( wp_power t s || fail "Waterproof could not find a proof. If you believe the statement should hold, try making a smaller step").
    Tactic Notation "By" constr(s)
    "it" "holds" "that" constr(t) "("ident(u)")"
    := new_hyp_verified_pose_proof s t u.
    Tactic Notation "It" "holds" "that"
    constr(t) "(" ident(u) ")" :=
    assert (u : t) by first [ wp_power t dum
                            | idtac "Waterproof could not find a proof. If you believe the statement should hold, try making a smaller step"].
    Ltac conclude_proof t s :=
    match goal with
    | [|-t] => idtac
    | _ => (idtac "Warning: The statement you provided does not exactly correspond to what you need to show. This can make your proof less readable.";
        change t || fail "The statement you provided is not what you needed to show. If you are trying to prove an intermediate step, add a name to your hypothesis between brackets at the end of the sentence.")
    end; wp_power t s || fail "Waterproof could not find a proof. Try making a smaller step.".
    Tactic Notation "It" "holds" "that" constr(t) :=
    conclude_proof t dum.
    Tactic Notation "By" constr(s)
    "it" "holds" "that" constr(t)
    := conclude_proof t s.
    Tactic Notation "It" "follows" "that" constr(t) :=
    conclude_proof t dum. *)


