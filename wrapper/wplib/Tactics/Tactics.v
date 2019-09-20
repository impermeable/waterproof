(** * Syntax extensions for Computer programs for analysis

      This document contains some very preliminary experiments with 
      notations, ltac definitions and tactic notations to make it possible 
      to stay closer to mathematical language when writing proofs in Coq. *)

(** This file is supposed to be put in a folder 
    WaterProof/Tactics/ and intended to be compiled, 
    with 
    sertop --mode=vo 
           -R "WaterProof","WaterProof"
           "WaterProof/Tactics/Tactics.v"*)

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Omega.
Require Import Max.
(* Require Import Unicode.Utf8. *)

(** * Custom notations
    
    Notations are variations on the ones in Unicode.Utf8 *)

(** Guarantee indentation and introduce custom notation for forall *)
Notation "'for' 'all' x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' for  all  x .. y ']' , '//'  P ']'") : type_scope.

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : type_scope.

Notation "'there' 'exists' x .. y , P " := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' there  exists  x .. y  ']' , '//'  P ']'") : type_scope.

Notation "∃ x .. y , P " := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : type_scope.

Notation "'fun' x .. y '↦' t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' 'fun' x .. y ']' '↦' '/' t ']'").

Notation "x ∨ y" := (x \/ y) (at level 85, right associativity) : type_scope.
Notation "x ∧ y" := (x /\ y) (at level 80, right associativity) : type_scope.
Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity,
   only parsing): type_scope.
Notation "x ⇒ y" := (x -> y)
  (at level 99, y at level 200, right associativity,
   only parsing): type_scope.
(* the notation below is fun, but is no good for functions *)
(* need to see if this can be adapted so it only uses 
   this notation for propositions *)
(*Notation "'if' x 'then' y" := (x -> y)
  (at level 99, y at level 200, right associativity): prop_scope.*)
Notation "x ⇨ y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.

Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "x ⇔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.

Notation "x ≤ y" := (le x y) (at level 70, no associativity) : nat_scope.
Notation "x ≥ y" := (ge x y) (at level 70, no associativity) : nat_scope.

Notation "x ≤ y" := (x <= y)%R (at level 70, no associativity) : R_scope.
Notation "x ≥ y" := (x >= y)%R (at level 70, no associativity) : R_scope.

Open Scope R_scope.

(* TODO: the below definition doesn't work very nicely *)
Notation "x ↦ y" := (fun x => y) (at level 0).

Notation "'ℕ'" := (nat).
Notation "'ℝ'" := (R).

(** Add field and lra to tactics to try automatically *)

Hint Extern 3 ( _ = _ ) => field : real.
Hint Extern 3 ( _ <= _ ) => lra : real.
Hint Extern 3 ( _ >= _ ) => lra : real.
Hint Extern 3 ( _ < _ ) => lra : real.
Hint Extern 3 ( _ > _ ) => lra : real.

(** * Custom tactics *)

(** ** A powertool *)

(* TODO: in some cases, eauto has left some existentials.
   this may be undesired, but eauto can be very powerful...
   one option is to let waterproof check whether 
   existentials are created and block this behavior. *)

Ltac wp_power :=
  first [ progress info_auto with *
(*        | omega
        | field 
        | lra *)
        | progress info_eauto with *].

(** ** Intro-based tactics *)

(** A strict version of intro with pattern matching *)
Ltac intro_strict s t :=
  match goal with
    | [ |- forall _ : t, _ ] => intro s
  end.

(** Envisioned use of intro_strict tactic. 
    The user should for instance be able to write:
      Take eps : R.
    With respect to the usual intro tactic, the system now also 
    checks the type of the variable to be introduced. *)
Tactic Notation "Take" ident(s) ":" constr(t):=
  intro_strict s t.

(** Practically the same tactic as above, 
    except the envisioned use is when you want to write "Assume ..."
    and actually specify in Coq code what you need to assume *)
Ltac assume_strict s t :=
  match goal with
    | [ |- t -> _ ] => intro s
  end.

Tactic Notation "Assume" ident(s) :=
  intro s.

Tactic Notation "Assume" ident(s) "of" "type" constr(t) :=
  assume_strict s t.

Tactic Notation "Assume" ident(s) ":" constr(t) :=
  assume_strict s t.

Ltac test_tac t :=
  match type of t with 
    |  ?T  => idtac T
  end.

(** ** Checking the context
       The following tactics let the user record in the proof script various
       aspects of the current context *)

(** The tactic call (goal_check t) checks if the current goal 
    can equivalently be written as t, otherwise it fails. *)
(** TODO May be much better to change the goal to the new formulation *)
Ltac goal_check t :=
  tryif (change t) 
    then (idtac "We indeed need to show that" t)
    else fail "This is not the current goal".

(** Make it possible to verify the goal t by writing
    "We need to show that t". *)
Tactic Notation "We" "need" "to" "show" "that" constr(t) :=
  goal_check t.

(** Make it possible to verify the goal t by writing
    "To show : t". *)
Tactic Notation "To" "show" ":" constr(t) :=
  goal_check t.

(** The tactic (hypo_check s t) checks if t is one of the 
    current hypothesis, and if so, it renames it into s *)
Ltac hypo_check s t:=
match goal with 
| [H : t |- _] => rename H into s
| _ => fail
end.

(** Apply with goal check
    The next tactics verify whether certain steps have the desired effect. *)
Ltac new_goal_verified_apply s t :=
  apply s;
  match goal with 
  | [|- t] => idtac "Expected goal was produced"
  | _ => fail "Lemma did not produce expected outcome"
  end.

(*Tactic Notation "By" constr(s) 
  "it" "suffices" "to" "show" "that"
  constr(t) :=
  new_goal_verified_apply s t.*)

(** A powerful forward reasoning tactic. 
    The sequential trying of auto and eauto 
    is there because eauto can be much slower. 
    TODO: is this what we want? *)
Ltac new_hyp_verified_pose_proof s t u:=
  assert (u : t) by first [ progress info_auto using s with *
                          | progress info_eauto using s with *
                          | fail "Could not find a proof."].
  (*;
  match goal with
  | [u : t |- _] => idtac "Outcome matched"
  | _ => fail "Unexpected outcome obtained"
  end.*)

Tactic Notation "By" constr(s)
  "it" "holds" "that" constr(t) "("ident(u)")"
  := new_hyp_verified_pose_proof s t u.

(*Tactic Notation "By" constr(s0) "," constr(s1)
  "it" "holds" "that" constr(t) "("ident(u)")"
  :=*) 

(** ** Instantiating variables that exist *)

Tactic Notation "Choose" constr(t):=
  exists t.

Tactic Notation "Choose" ident(s) ":=" constr(t) :=
  exists t.

Tactic Notation "Choose" ident(s) 
                "such" "that" ident(u)
                "according" "to" constr(v) (*":" constr(t)*):=
  destruct v as [s u].

(*Tactic Notation "Choose" ident(s)
                "such" "that" ident(u)
                "according" "to" ident(v)
                "with" constr(t) :=
  destruct v with t as [s u]. *)

Tactic Notation "Choose" ident(s)
                "such" "that" ident(u)
                "according" "to" constr(v)
                "with" constr(t) :=
  destruct v with t as [s u].

(** ** Forward reasoning *)

Tactic Notation "Because" ident(s) 
  "both" ident(u) "and" ident(v) :=
  destruct s as [u v].

Tactic Notation "Because" ident(s) 
  "both" ident(u) ":" constr(t_u)
  "and"  ident(v) ":" constr(t_v):=
  destruct s as [u v].

(* TODO: align syntax with "By ... it holds that" *)
Tactic Notation "It" "holds" "that"
  constr(t) "(" ident(u) ")" :=
  assert (u : t) by first [ progress info_auto with *
                          | progress info_eauto with *
                          | fail "Failed to find a proof"].



Tactic Notation "This" "follows" "immediately" :=
  wp_power.

Tactic Notation "follows" "immediately" := 
  wp_power.

Tactic Notation "This" "follows" "by" "assumption" := 
  assumption.

(*Tactic Notation "It" "holds" "that"
  constr(t) "(" ident(u) ")" :=
  assert (u : t) by (auto with real).

Tactic Notation "It" "holds" "that"
  constr(t) :=
  assert (t) by (auto with real).*)

(** ** Claims *)

Tactic Notation "We" "claim" "that" 
  constr(t) "(" ident(u) ")" :=
  assert (u : t).

(*Tactic Notation "It" "holds" "that"
  ident(u) ":" constr(t) :=
  assert (u : t) by (info_auto with real).*)

(** ** Rewriting 
    TODO: add rewrite with at
    TODO: add support for rewriting in 
          and at multiple places at once 
    TODO: clear the proved equality? *)

Tactic Notation "Rewrite" "using" constr(t) :=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u.

Tactic Notation "rewrite" "using" constr(t) :=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u.

Tactic Notation "Rewrite" "using" constr(t) "in" ident(s):=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u in s.

Tactic Notation "rewrite" "using" constr(t) "in" ident(s):=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u in s.

Tactic Notation "Rewrite" "<-" "using" constr(t) :=
  let u := fresh in 
    assert (u : t) by (info_auto with *);
  rewrite<-u.

(** A different notation for apply. It is important to note that 
    when using constr(t) instead of uconstr(t), the use of wildcards 
    is no longer possible. *)
Tactic Notation "Apply" uconstr(t) :=
  apply t.

(** TODO: write an equivalent for using apply with *)

(** A different notation for the unfold tactic.

    TODO: find ways to add further options 
    with these tactics.
   *)
Tactic Notation "Unfold" constr(t) :=
  unfold t.

Tactic Notation "Unfold" constr(t) "in" ident(s):=
  unfold t in s.

Tactic Notation "Expand" "the" "definition" "of" constr(t) :=
  unfold t.

Tactic Notation "Expand" "the" "definition" "of" 
  constr(t) "in" ident(s) :=
  unfold t in s.

(** ** Strings of (in)equalities.
  
  The following tactics should help in situations 
  where in a pen-and-paper proof we would write a 
  string of equalities and inequalities.
    *)

(** The tactic trans_ineq eq_or_ineq reduces 
    the inequality in the goal to a new one by using
    eq_or_ineq. *)
Ltac trans_ineq eq_or_ineq := 
  match goal with 
  | [|-?x <= ?z] => 
    match (type of eq_or_ineq) with 
    | (x <= ?y) => apply (Rle_trans x y z eq_or_ineq)
    | _ => idtac "not a less-than-or-equal-to inequality"
    end
  | _ => idtac "Goal is not a less-than-or-equal-to inequality."
  end.

(** ** Defining new variables *)

Tactic Notation "Define" ident(u) ":=" constr(t) :=
  set (u := t).

(** ** Reflexivity *)

Tactic Notation "This" "follows" "by" "reflexivity" :=
  reflexivity.

(** ** Simplification *)

(** TODO: The following tactic notation may need 
    to be improved. *)
Tactic Notation "Simplify" "what" "we" "need" "to" "show" :=
  simpl.

Lemma test : (1 + 1 = 2)%nat.
Proof.
We claim that (1 + 1 = 2)%nat (H1).
simpl. reflexivity. rewrite using ((1+1)%nat = 2%nat).
reflexivity.
Qed.


