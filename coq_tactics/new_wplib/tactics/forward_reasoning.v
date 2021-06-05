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

Local Ltac2 print_failure () :=
    print (of_string "Waterproof could not find a proof. 
If you believe the statement should hold, 
try making a smaller step.").

(** * unwrap_optional_lemma
    Given an optional lemma, either returns the lemma itself,
    or case the argument is [None], returns a dummy lemma.

    Arguments:
        - [lemma: constr option], one of the following:
            - a [constr] referring to a lemma, wrapped in [Some].
            - the value [None]
    
    Returns:
        - [constr]: the provided lemma, or [dummy_lemma] in case
            the input was [None]. [dummy_lemma] simply states that [0=0].
*)
Local Ltac2 unwrap_optional_lemma (lemma: constr option) :=
    match lemma with
    | None => constr:(dummy_lemma)
    | Some y => y
    end.

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
    let help_lemma := unwrap_optional_lemma proving_lemma
    in
    let by_arg () := waterprove_with_hint conclusion help_lemma
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



(* -------------------------------------------------------------------------- *)
(** * Tactics to finish a goal
    They automate the last final steps. *)


Ltac2 warn_equivalent_goal_given () :=
    print (of_string "Warning: 
The statement you provided does not exactly correspond to what you need to show. 
This can make your proof less readable.
Waterproof will try to rewrite the goal...").

Ltac2 warn_wrong_goal_given (wrong_target: constr) :=
    print (concat
            (concat
                (concat
                    (of_string "The actual goal (")
                    (of_constr (Control.goal ()))
                )
                (concat 
                    (of_string ") is not equivalent to the goal you gave (")
                    (of_constr wrong_target)
                )
            )
            (of_string "). ")
    ).

Ltac2 target_equals_goal_judgementally (target:constr) :=
    let target := eval cbv in $target in
    let real_goal := Control.goal () in
    let real_goal := eval cbv in $real_goal in
    Constr.equal target real_goal.
    

Ltac2 solve_remainder_proof (target_goal:constr) (lemmas:constr option) :=
    let lemmas := unwrap_optional_lemma lemmas
    in
    (* First check if the given target equals the goal directly,
        without applying any rewrite. *)
    match Constr.equal target_goal (Control.goal ()) with
    | false => 
        match target_equals_goal_judgementally target_goal with
        | false => 
            warn_wrong_goal_given (target_goal); 
            Control.zero (AutomationFailure 
        "Given goal not equivalent to actual goal.")
        | true => 
            (* User provided an equivalent goal, 
            but written differently. 
            Try to rewrite the real goal to match user input.*)
            warn_equivalent_goal_given ();
            let g := Control.goal () in
            change $target_goal;
            waterprove_with_hint target_goal lemmas
        end
    | true =>  waterprove_with_hint target_goal lemmas
    end.

Ltac2 Notation "We" "conclude" "that" target_goal(constr) := 
    solve_remainder_proof target_goal None.



Ltac2 Notation "By" lemma(constr) "we" "conclude" "that" target_goal(constr) := 
    solve_remainder_proof target_goal (Some lemma).


(* Below is copied stuff for easy reference. Just as a personal note, should eventually be removed.*)
(* 
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


