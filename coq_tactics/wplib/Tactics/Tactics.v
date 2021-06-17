(** # Tactics for Waterproof

This file contains tactics that are better suited for readable mathematical proofs.*)
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

Require Import wplib.Notations.Notations.
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.

Require Import wplib.Tactics.AdditionalLemmas.
Require Import wplib.Tactics.Waterprove.
Ltac help :=
  match goal with
  | [ |- forall _ : ?A, _ ] => idtac "Try to define a variable of type " A " , or assume a hypothesis"
  | [ |- _ -> _ ] =>  idtac "Try to define a variable, or assume a hypothesis"
  | [ |- exists _ : ?A, _ ] => idtac "Choose a specific value of type " A
  end.
(** *)
(** ## **Introducing variables and hypotheses.**

The following tactics are variations on the `intro` tactic.
We distinguish on introducing variables (`Take`) and listing assumptions (`Assume`).
Currently supports introduction of one and two terms simultaneously.

**TODO**:
- Variable arity of tactics
- More variation on choice of specific words (e.g. `Let` instead of `Take`)
- Consider assumptions as sequence of conjunctions
- Consider more fluent introduction of $\varepsilon > 0$, $n \geq N$, etc.
- Add more feedback.*)
(** #### **Strict introduction**
Match introduced variable / assumption exactly with its type.*)
Ltac intro_strict s t :=
  match goal with
    | [ |- forall _ : ?u, _ ] => 
      match u with
      | t => intro s
      | (subsets_R_to_elements _) => intro s
      end
  end.
Ltac assume_strict s t :=
  match goal with    
    | [ |- ?u -> _ ] =>
      match u with
      | (_ /\ _) => (change u with t; intro s; destruct s)
      | _ => (change u with t; intro s)
      end
  end.
(** *)
(** #### **Introducing variables**
Enforce a strict introduction.
The first tactic enables introduction of single variable.*)
Tactic Notation "Take" ident(s) ":" constr(t):= 
  intro_strict s t.
(** Next, we consider the introduction of two variables.*)
Tactic Notation "Take" ident(s1) "," ident(s2) ":" constr(t):=
  intro_strict s1 t; intro_strict s2 t.
Tactic Notation "Take" ident(s1) "and" ident(s2) ":" constr(t):=
  intro_strict s1 t; intro_strict s2 t.
Tactic Notation "Take" ident(s1) ":" constr(t1) "," ident(s2) ":" constr(t2):=
  intro_strict s1 t1; intro_strict s2 t2.
Tactic Notation "Take" ident(s1) ":" constr(t1) "and" ident(s2) ":" constr(t2):=
  intro_strict s1 t1; intro_strict s2 t2.
(** Similarly, the following tactics allow for introduction of three variables.*)
Tactic Notation "Take" ident(s1) "," ident(s2) "," ident(s3) ":" constr(t) :=
  intro_strict s1 t; intro_strict s2 t; intro_strict s3 t.
Tactic Notation "Take" ident(s1) "," ident(s2) "and" ident(s3) ":" constr(t) :=
  intro_strict s1 t; intro_strict s2 t; intro_strict s3 t.
Tactic Notation "Take" ident(s1) "," ident(s2) ":" constr(t1) "," ident(s3) ":" constr(t2) :=
  intro_strict s1 t1; intro_strict s2 t1; intro_strict s3 t2.
Tactic Notation "Take" ident(s1) "," ident(s2) ":" constr(t1) "and" ident(s3) ":" constr(t2) :=
  intro_strict s1 t1; intro_strict s2 t1; intro_strict s3 t2.
Tactic Notation "Take" ident(s1) ":" constr(t1) "," ident(s2) "," ident(s3) ":" constr(t2) :=
  intro_strict s1 t1; intro_strict s2 t2; intro_strict s3 t2.
Tactic Notation "Take" ident(s1) ":" constr(t1) "and" ident(s2) "," ident(s3) ":" constr(t2) :=
  intro_strict s1 t1; intro_strict s2 t2; intro_strict s3 t2.
Tactic Notation "Take" ident(s1) ":" constr(t1) "," ident(s2) ":" constr(t2) "," ident(s3) ":" constr(t3) :=
  intro_strict s1 t1; intro_strict s2 t2; intro_strict s3 t3.
Tactic Notation "Take" ident(s1) ":" constr(t1) "," ident(s2) ":" constr(t2) "and" ident(s3) ":" constr(t3) :=
  intro_strict s1 t1; intro_strict s2 t2; intro_strict s3 t3.
(** *)
(** *)
(** #### **Assuming hypotheses**
Both strict and non-strict introduction.
If the goal contains a conjunction of hypothesis, split them into two separate hypotheses.*)
Tactic Notation "Assume" ident(s) :=
  intro s.
Tactic Notation "Assume" ident(s1) "and" ident(s2) :=
  match goal with
  | [ |- _ -> _ -> _ ] => intros s1 s2
  | [ |- _ /\ _ -> _ ] => intro s1; destruct s1 as [s1 s2]
  end.
Tactic Notation "Assume" ident(s) ":" constr(t) :=
  assume_strict s t.
Tactic Notation "Assume" ident(s1) ":" constr(t1) "and" ident(s2) ":" constr(t2) :=
  match goal with
  | [ |- _ -> _ -> _ ] => assume_strict s1 t1; assume_strict s2 t2
  | [ |- _ /\ _ -> _ ] => idtac "Not yet supported"
  end.
(** #### **Introducing variable with assumption**
Take care of introducing a variable with an assumption, e.g. let $\varepsilon \in \mathbb{R}$ such that $ε > 0$.\
**TODO**:
- Note that it is possible to use a newly introduced variable right of the tactical `;`, so perhaps the best option is to interpret keywords (like `such`) as `;`.
This should most likely be done one the Waterproof side.*)
Tactic Notation "such" "that" ident(s1) ":" constr(t1) :=
  assume_strict s1 t1.
(** ## **If and only if**
If we have to prove two directions, we first have to say that we show both directions.*)
Ltac iff :=
  match goal with
  | [|- _ <-> _ ] => split
  | _ => fail "This is not an if and only if, so try another tactic."
  end.
Ltac and :=
  match goal with
  | [|- _ /\ _ ] => split
  | [|- _ <-> _ ] => split
  | _ => fail "You can not split this into two different goals."
  end;
  idtac "Recommendation: For clarity of your proof, it is helpful to remind the reader of what you need to show when you start to show each of the statements.".
Tactic Notation "We" "show" "both" "directions" :=
  iff.
Tactic Notation "We" "prove" "both" "directions" := iff.
Tactic Notation "We" "show" "both" "statements" := and.
Tactic Notation "We" "prove" "both" "statements" := and.
(** Another version is the following, requiring the user to explicitly mention the two cases:*)
Tactic Notation "We" "show" "both" constr(s) "and" constr(t) :=
  try auto with nocore unfolds;
  match goal with
  | [|- s ∧ t] => split
  | [|- t ∧ s] => split
  | [|- ?x ∧ t] => fail "You need to show " x " instead of" s
  | [|- t ∧ ?x] => fail "You need to show " x " instead of" s
  | [|- s ∧ ?x] => fail "You need to show " x " instead of" t
  | [|- ?x ∧ s] => fail "You need to show " x " instead of" t
  end.
(** ## **Checking the context**

The following tactics let the user record in the proof script various aspects of the current context.
In particular, users can state or manipulate the exact goal, and rename or add existing hypotheses.\
**TODO**
- More precisely specify how much rephrasing is possible.
- Add more feedback for when a tactic fails.*)
(** #### **Checking the goal**

Make it possible to verify the goal t by writing: `We need to show that t` or `To show: t`.*)
Ltac goal_check t :=
  tryif (change t) 
    then (idtac "We indeed need to show that" t)
    else fail "This is not the current goal".
Tactic Notation "We" "need" "to" "show" "that" constr(t) :=
  goal_check t.
Tactic Notation "To" "show" ":" constr(t) :=
  goal_check t.
(** #### **Checking hypotheses**
These tactics allow for renaming existing hypotheses.
Moreover, it is now possible to add existing lemmas to the context.*)
Ltac hypo_check s t:=
match goal with 
| [H : t |- _] => rename H into s
| _ => fail
end.
Tactic Notation "We" "know" ident(s) ":" constr(t) :=
  hypo_check s t.
Tactic Notation "By" constr(t) "we" "know" ident(s) :=
  pose proof t as s.
(** *)
(** ## **Choosing variables that exist**

The following tactics are variations on two tactics that act on existential quantifiers; `exists` and `destruct`.
With the former, we want to express a specific choice, whereas the latter is often used when a hypothesis contains an $\exists$.\
**TODO**
- How flexible do we want these tactics?
- Add a hypothesis check to ensure the hypothesis has the form `∃ _ : _, _`.*)
(** #### **Exists in goal**

Choose a specific value.
(Should the order in the second tactic not be reversed?)*)
Tactic Notation "Choose" constr(t):=
  exists t.
Tactic Notation "Choose" ident(s) ":=" constr(t) :=
  pose (s := t);
  exists s.
(** #### **Exists in hypothesis**

E.g. when the hypothesis reads ``∃ n : ℕ``, we can 'introduce' such an `n`.*)
(** *)
Tactic Notation "Choose" ident(s) 
                "such" "that" ident(u)
                "according" "to" constr(v) (*":" constr(t)*):=
  destruct v as [s u].
Tactic Notation "Choose" ident(s)
                "such" "that" ident(u)
                "according" "to" constr(v)
                "with" constr(t) :=
  destruct v with t as [s u].
(** *)
(** ## **Forward reasoning**

These tactics try to use forward reasoning to deduce more useful hypothesis. *)
Tactic Notation "Because" ident(s) 
  "both" ident(u) "and" ident(v) :=
  destruct s as [u v].
Tactic Notation "Because" ident(s) 
  "both" ident(u) ":" constr(t_u)
  "and"  ident(v) ":" constr(t_v):=
  destruct s as [u v].
Tactic Notation "Because" ident(s)
  "either" ident(u) "or" ident(v) :=
  destruct s as [u | v].
(** #### **Decidability**
There are a number of tactics that deal with decidability. They are of the form ``{r1 s1 r2} + {r1 s2 r2}``, and can be useful in case evaluation.
To implement this, we create a new database ``decidiability``, and a tactic that uses this database (only).
We first add existing lemmas to the new database.

**TODO**:
- Add options to split hypotheses ``{r1 <= r2}`` into ``Either {r1 < r2} or {r1 = r2}``.*)
Create HintDb decidability.
Hint Resolve Req_EM_T : decidability.
Hint Resolve Rlt_dec Rle_dec Rgt_dec Rge_dec : decidability.
Hint Resolve Rlt_le_dec Rle_lt_dec Rgt_ge_dec Rge_gt_dec : decidability.
(** The following lemmas are necessary to write e.g. `{r1 ≤ r2} + {r2 < r1}`.*)
Lemma Rlt_ge_dec : forall r1 r2, {r1 < r2} + {r1 >= r2}.
Proof.
  intros.
  destruct (total_order_T r1 r2). destruct s. 
    apply (left r).
    apply (right (Req_ge r1 r2 e)). 
    apply (right (Rle_ge r2 r1 (Rlt_le r2 r1 r))).
Qed.
Lemma Rgt_le_dec : forall r1 r2, {r1 > r2} + {r1 <= r2}.
Proof.
  intros.
  destruct (total_order_T r1 r2). destruct s. 
    apply (right (Rlt_le r1 r2 r)).
    apply (right (Req_le r1 r2 e)). 
    apply (left r).
Qed.

Hint Resolve Rlt_ge_dec Rgt_le_dec : decidability.
(** Finally, we add four more lemmas to write e.g. `{r1 ≤ r2} + {~r2 ≥ r1}`.*)
Lemma Rlt_gt_dec : forall r1 r2, {r1 < r2} + {~ r2 > r1}.
Proof.
  intros.
  destruct (total_order_T r1 r2). destruct s.
    apply (left r).
    apply (right (Rge_not_gt r2 r1 (Req_ge r1 r2 e))).
    apply (right (Rgt_asym r1 r2 r)).
Qed.
Lemma Rgt_lt_dec : forall r1 r2, {r1 > r2} + {~ r2 < r1}.
Proof.
  intros.
  destruct (total_order_T r1 r2). destruct s.
    apply (right (Rlt_asym r1 r2 r)).
    apply (right (Rle_not_gt r1 r2 (Req_le r1 r2 e))).
    apply (left r).
Qed.
Lemma Rle_ge_dec : forall r1 r2, {r1 <= r2} + {~ r2 >= r1}.
Proof.
  intros.
  destruct (total_order_T r1 r2). destruct s.
    apply (left (Rlt_le r1 r2 r)).
    apply (left (Req_le r1 r2 e)).
    apply (right (Rlt_not_ge r2 r1 r)).
Qed.
Lemma Rge_le_dec : forall r1 r2, {r1 >= r2} + {~ r2 <= r1}.
Proof.
  intros.
  destruct (total_order_T r1 r2). destruct s.
    apply (right (Rlt_not_le r2 r1 r)).
    apply (left (Req_ge r1 r2 e)).
    apply (left (Rgt_ge r1 r2 r)).
Qed.

Hint Resolve Rlt_gt_dec Rgt_lt_dec Rle_ge_dec Rge_le_dec : decidability.
(** Using the database `decidability`, we can then make a new tactic to destruct lemmas of the type `{r1 s1 r2} + {r1 s2 r2}`.*)
Tactic Notation "Either" constr(t1) "or" constr(t2) :=
  idtac "Recommendation: Please use comments to indicate the case you are in after writing this line. This helps to keep the proof readable.";
  first [
    assert (u : {t1} + {t2}) by auto with decidability nocore;
      destruct u |
    assert (u : {t2} + {t1}) by auto with decidability nocore;
      destruct u
    ].
(** ## **Forward reasoning by automation**
The following tactics try to automatically reduce the goal by doing trivial substeps.\
**TODO**
- Formalise the amount of automation
- Uniform notation*)
(** Apply with goal check
    The next tactics verify whether certain steps have the desired effect. *)
Ltac new_goal_verified_apply s t :=
  apply s;
  match goal with 
  | [|- t] => idtac "Expected goal was produced"
  | _ => fail "Lemma did not produce expected outcome"
  end.
(** ** Wrapping the waterprove automation tactic

The following tactic is very powerful, and will be used to solve (trivial) arithmetic steps. Note that the exact behaviour of this tactic is not known. Also, it may be too powerful in some cases.*)
Lemma dum : 0 < 1.
lra.
Qed.
Ltac check_status t :=
match t with
| ( forall _ : ?A, _ ) => idtac "You may need to introduce an arbitrary variable (Take ... : ...) or make an assumption (Assume ... : ...)."
| ( exists _ : ?A, _ ) => idtac "You may need to choose a specific value of type " A
| _ => idtac
end.
Ltac wp_power t s :=
  check_status t;
  waterprove t s.
(** ** Automation for forward reasoning

A powerful forward reasoning tactic. 
    The sequential trying of auto and eauto 
    is there because eauto can be much slower. 
    TODO: is this what we want? *)
Ltac new_hyp_verified_pose_proof s t u:=
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
  conclude_proof t dum.
(** *)
(** TODO: preferably deprecate this notation.*)
Tactic Notation "This" "follows" "immediately" :=
  match goal with
  | [ |- ?t ] =>   wp_power t dum
  end.
Tactic Notation "follows" "immediately" := 
  match goal with
  | [ |- ?t ] =>   wp_power t dum
  end.
Tactic Notation "It" "suffices" "to" "show" "that"
  constr(t) :=
  match goal with 
  | [ |- ?u ] => enough t by ( wp_power u dum || fail "Waterproof could not confirm that proving the statement would be enough.")
  end.
Tactic Notation "It" "suffices" "to" "show" "that"
  constr(t) "by" tactic(tac) :=
  enough t by tac.
Tactic Notation "Write" "goal" "using" constr(t) "as" 
  constr(s) :=
  let u := fresh in
    assert (u : t) by wp_power t dum;
  rewrite u;
  match goal with
  | [ |- ?v ] => enough s by wp_power v dum
  end;
  clear u.
Tactic Notation "Write" ident(H) "using" constr(t) "as"
  constr(s) :=
  let u := fresh in
    assert (u : t) by wp_power t dum;
  rewrite u in H;
  clear u.
(** *)
(** *)
(** ## **Claims**
The following tactics are variants of the ``assert`` tactic.
Enables the user to prove a 'sublemma' in a proof.\
**TODO**
- Is this a suitable notation?
- Consider tactic ``We claim by _ that _``
- (Automatically) naming the claim*)
Tactic Notation "We" "claim" "that" constr(t) "(" ident(u) ")" :=
  assert (u : t).
(** ## **Rewriting**

The following tactics are variants on the ``rewrite`` tactic.\
**TODO**
- Allow for multiple rewrites simultaneously using keywords such as `as, in, with ..`*)
(** *)
Tactic Notation "Rewrite" "using" constr(t) :=
  let u := fresh in
    assert (u : t) by wp_power t dum;
  rewrite u;
  clear u.
Tactic Notation "rewrite" "using" constr(t) :=
  let u := fresh in
    assert (u : t) by wp_power t dum;
  rewrite u;
  clear u.
Tactic Notation "Rewrite" "using" constr(t) "in" ident(s):=
  let u := fresh in
    assert (u : t) by wp_power t dum;
  rewrite u in s;
  clear u.
Tactic Notation "rewrite" "using" constr(t) "in" ident(s):=
  let u := fresh in
    assert (u : t) by wp_power t dum;
  rewrite u in s;
  clear u.
Tactic Notation "Rewrite" "<-" "using" constr(t) :=
  let u := fresh in 
    assert (u : t) by wp_power t dum;
  rewrite<-u;
  clear u.
(** *)
Tactic Notation "replacing" constr(s) "with" constr(t) :=
  replace s with t by wp_power (s=t) dum.
(** ## **Applying lemmas and theorems**

The following tactics are variants of the ``apply`` tactic.
Note: when using `constr(t)` instead of `uconstr(t)`, the use of wildcards is no longer possible.\
**TODO**
- Add option `apply with`.
- More variation on choice of specific words (e.g. `Use` or `By ...`.*)
Tactic Notation "Apply" uconstr(t) :=
  apply t.
(** *)
(** ## **Expanding definitions**
The following tactics are variants of the `` unfold`` tactic.

**TODO:**
- Ideally, replace this with a more 'natural' tactic.
- Allow use of keywords (`in`, `as`, etc.)*)
Tactic Notation "Unfold" constr(t) :=
  unfold t.
Tactic Notation "Unfold" constr(t) "in" ident(s):=
  unfold t in s.
Tactic Notation "Expand" "the" "definition" "of" reference(t) :=
  match goal with
  | [|- ?u] =>
  unfold t;
  idtac "Recommendation: please remind the reader of what you need to show now that you expanded the definition of "
        t
        ". You can do so by writing 'We need to show that "
        u
        "'"
  end.
Tactic Notation "Expand" "the" "definition" "of" 
  reference(t) "in" ident(s) :=
  unfold t in s;
  idtac "Recommendation: please tell the reader the current form of " s " after expanding the definition of " t 
    ". You can do so by writing 'Write " s " as ...".
Tactic Notation "Write" ident(s) "as" constr(t) :=
  change t in s.
(** *)
(** ## **Strings of (in)equalities**

The following tactics should help in situations where in a pen-and-paper proof we would write a string equalities and inequalites.

**Note:** As of now, forward reasoning by "it holds that" seems to be a better option.

**TODO**:
- Define type s.t. we can use arbitrary number of (in)equalities in a string, or
- Define lots of tactic notations, each for a specific order of (in)equalities.
- Incorporate rewriting tactics, reducing trivial or small steps automatically
- Improve 'proving the step'*)
(** #### **Proving the step**
First, we define auxiliary tactics that help with proving the transitive 'step'.
Currently, try to solve with auto and to prove by (rewriting) assumptions.*)
Ltac extended_reflexivity :=
  try reflexivity;
  try apply Rle_refl;
  try apply Rge_refl.
Ltac extended_assumption :=
  try assumption;
  try (apply Rlt_le; assumption);
  try (apply Rgt_ge; assumption).
Ltac rewrite_all_tac :=
  match goal with
  |[ H : _ = _  |- _] => try rewrite H; extended_reflexivity
  end.
Ltac prove_step step :=
  try auto with *;
  try rewrite_all_tac;
  try extended_assumption.
(** #### **Transitive step**
Here, try to convert the goal by using transitivity.\
**Note:** do not add Rlt_trans and Rgt_trans. They can lead to an inprovable statement.*)
Ltac trans_ineq x y z step symbol :=
  match symbol with
  | Rlt => 
      first [apply (Rlt_le_trans x y z step) |
            apply (Rle_lt_trans x y z step)|
            idtac "'<' does not work here."]
  | Rle => 
      first [apply (Rle_trans x y z step) |
            apply (Rle_trans x y z (Rlt_le x y step))|
            idtac "'≤' does not work here."]
  | Rgt =>
      first [apply (Rge_gt_trans x y z step) |
            apply (Rgt_ge_trans x y z step)|
            idtac "'>' does not work here."]
  | Rge =>
      first [apply (Rge_trans x y z step) |
            apply (Rle_trans x y z (Rgt_ge x y step))|
            idtac "'≥' does not work here."]
  | eq =>
      first [rewrite step|
            idtac "'=' does not work here."]
  | ?a => idtac a "is not allowed here. Try using =, <, >, ≤ or ≥"
  end.
(** #### **String of (in)equalities**
Here, the actual tactic is implemented.
Currently works as follows on call ``Rewrite (a ≤ b) (b ≤ c)``:
- Two subcalls to ``string_of_ineqs``, once with ``(a ≤ b)``, once with ``(b ≤ c)``.
- In subcall, first prove that step ``a ≤ b`` actually holds.
- If the goal is the same as the step, we finish the proof.
- If the goal is of the form `a ≤ c`, use transitivity to change the goal to `b ≤ c`. *)
(** *)
Ltac string_of_ineqs step_form := 
  let step := fresh in
    assert (step : step_form);
      [> prove_step step; fail "Could not find proof for" step_form"." | ];
  match goal with
  | [|- ?symbol ?x ?z ] => 
    match (type of step) with
    | (symbol x z) => exact step
    | (?symbol2 x ?y) => trans_ineq x y z step symbol2
    | _ => fail "Rewrite only works if the first statement is " x
    end
  end;
  try extended_reflexivity.
Tactic Notation "Rewrite" constr(t) 
  := string_of_ineqs t.
Tactic Notation "Rewrite" constr(t1) constr(t2)
  := string_of_ineqs t1; string_of_ineqs t2.
Tactic Notation "Rewrite" constr(t1) constr(t2) constr(t3) 
  := string_of_ineqs t1; string_of_ineqs t2; string_of_ineqs t3.
Tactic Notation "Rewrite" constr(t1) "<" constr(t2)
  := string_of_ineqs (t1 < t2).
Tactic Notation "Rewrite" constr(t1) ">" constr(t2)
  := string_of_ineqs (t1 > t2).
Tactic Notation "Rewrite" constr(t1) "≤" constr(t2)
  := string_of_ineqs (t1 <= t2).
Tactic Notation "Rewrite" constr(t1) "≥" constr(t2)
  := string_of_ineqs (t1 >= t2).
Tactic Notation "Rewrite" constr(t1) "=" constr(t2)
  := string_of_ineqs (t1 = t2).
Tactic Notation "Rewrite" constr(t1) "<" constr(t2) "<" constr(t3)
  := string_of_ineqs (t1 < t2); string_of_ineqs (t2 < t3).
Tactic Notation "Rewrite" constr(t1) "<" constr(t2) "≤" constr(t3)
  := string_of_ineqs (t1 < t2); string_of_ineqs (t2 <= t3).
Tactic Notation "Rewrite" constr(t1) "<" constr(t2) "=" constr(t3)
  := string_of_ineqs (t1 < t2); string_of_ineqs (t2 = t3).
Tactic Notation "Rewrite" constr(t1) ">" constr(t2) ">" constr(t3)
  := string_of_ineqs (t1 > t2); string_of_ineqs (t2 > t3).
Tactic Notation "Rewrite" constr(t1) ">" constr(t2) "≥" constr(t3)
  := string_of_ineqs (t1 > t2); string_of_ineqs (t2 >= t3).
Tactic Notation "Rewrite" constr(t1) ">" constr(t2) "=" constr(t3)
  := string_of_ineqs (t1 > t2); string_of_ineqs (t2 = t3).
Tactic Notation "Rewrite" constr(t1) "≤" constr(t2) "<" constr(t3)
  := string_of_ineqs (t1 <= t2); string_of_ineqs (t2 < t3).
Tactic Notation "Rewrite" constr(t1) "≤" constr(t2) "≤" constr(t3)
  := string_of_ineqs (t1 <= t2); string_of_ineqs (t2 <= t3).
Tactic Notation "Rewrite" constr(t1) "≤" constr(t2) "=" constr(t3)
  := string_of_ineqs (t1 <= t2); string_of_ineqs (t2 = t3).
Tactic Notation "Rewrite" constr(t1) "≥" constr(t2) ">" constr(t3)
  := string_of_ineqs (t1 >= t2); string_of_ineqs (t2 > t3).
Tactic Notation "Rewrite" constr(t1) "≥" constr(t2) "≥" constr(t3)
  := string_of_ineqs (t1 >= t2); string_of_ineqs (t2 >= t3).
Tactic Notation "Rewrite" constr(t1) "≥" constr(t2) "=" constr(t3)
  := string_of_ineqs (t1 >= t2); string_of_ineqs (t2 = t3).
Tactic Notation "Rewrite" constr(t1) "=" constr(t2) "<" constr(t3)
  := string_of_ineqs (t1 = t2); string_of_ineqs (t2 < t3).
Tactic Notation "Rewrite" constr(t1) "=" constr(t2) ">" constr(t3)
  := string_of_ineqs (t1 = t2); string_of_ineqs (t2 > t3).
Tactic Notation "Rewrite" constr(t1) "=" constr(t2) "≤" constr(t3)
  := string_of_ineqs (t1 = t2); string_of_ineqs (t2 <= t3).
Tactic Notation "Rewrite" constr(t1) "=" constr(t2) "≥" constr(t3)
  := string_of_ineqs (t1 = t2); string_of_ineqs (t2 >= t3).
Tactic Notation "Rewrite" constr(t1) "=" constr(t2) "=" constr(t3)
  := string_of_ineqs (t1 = t2); string_of_ineqs (t2 = t3).
(** *)
(** ## **Defining new variables**
The following tactics are used to define new variables (e.g. `Define k := a / b`).*)
Tactic Notation "Define" ident(u) ":=" constr(t) :=
  set (u := t).
(** *)
(** ## **Finishing a proof**
The following tactics can be used to finish a proof.\
**TODO**:
- Add more variants of this
- Perhaps add more automation to these steps
- Perhaps add a check that it indeed follows by the assumption.*)
Tactic Notation "This" "follows" "by" "reflexivity" :=
  reflexivity.
Tactic Notation "This" "concludes" "the" "proof" :=
  try reflexivity; try trivial.
Tactic Notation "This" "follows" "by" "assumption" :=
  assumption.
Tactic Notation "Then" constr(t) "holds" "by" "assumption" :=
  conclude_proof t dum.
(** ## **Simplification**
Deprecate(?)*)
Tactic Notation "Simplify" "what" "we" "need" "to" "show" :=
  simpl.
(** ## Proving by induction

Very basic notation, room for improvement. Also not the nicest formulation, but `Proof` is already used. *)
Tactic Notation "We" "prove" "by" "induction" "on" ident(x) "," "calling" "the" "induction" "hypothesis" ident(y) := 
  induction x.
(** ## A tool for set equalities and inclusions*)
(** TODO This tool works well in separate lemmas, but not always in larger contexts. Also, no error message is built in yet.*)
Ltac set_power :=
  timeout 1 (first [ solve [auto with sets]
        | solve [eauto with sets]
        | solve [firstorder (auto with sets)]
        | solve [firstorder (eauto with sets)]]).
Ltac destruct_sets :=
  match goal with 
    | [H : In _ (Intersection _ _ _) _ |- _] => destruct H
    | [H : In _ (Union _ _ _) _  |- _] => destruct H; try set_power
  end.
Ltac trivial_set_inclusion := 
  try intro x;
  try intro H;
  try destruct_sets;
  try contradiction;
  try set_power.
Ltac trivial_set_equality := 
  try intros A;
  try intros B;
  try apply Extensionality_Ensembles;
  try unfold Same_set;
  try unfold Included;
  split;
  trivial_set_inclusion;
  trivial_set_inclusion.
Tactic Notation "This" "equality" "is" "trivial" := 
   trivial_set_equality.
(** ### Tactics for new set definitions*)
Tactic Notation "lift_element" constr(A) ident(x) :=
  let u := fresh in
    assert (u : A) by wp_power;
  rewrite u in x;
  clear u.
(** 
*)
(** *)
(** 

## Hints*)
Hint Resolve Rmult_gt_0_compat : real.
Hint Resolve Rmult_lt_0_compat : real.
Hint Resolve R_dist_eq : real.
Hint Constructors Union Intersection Disjoint Full_set : sets. 

(*Would like to add the following hint, but this undesirably interferes with workings of e.g. wp_power. Also, what weight to use?
Hint Extern 5 (_ = _) => try trivial_set_equality : sets. 
*)
(** *)
