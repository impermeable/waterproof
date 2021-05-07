(** # **Databases**
In this file, we construct so-called Hint Databases.
These databases can be used in combination with the tactics `auto` and `eauto`.
When using such a tactic, the hints in th database are recursively called until a certain search depth (standard is 5).
We choose to split the interesting hints among a number of different databases, so that the recursive search  size and the corresponding search time remain relatively small.

## **Equality**
We first look at databases that can be used for solving equalities, like $x + y = y + x$ and $|(\left|\log(e^x)|)\right| = |x|$.
The most important operation in each of the databases is the `reflexivity` tactic, since with that tactic, we want to solve the step.
We distinguish a number of operations and characteristics, and initialise these databases by adding a reflexivity hint.*)
Require Import Reals.
Local Open Scope R_scope.
Hint Extern 0 => reflexivity : 
  eq_general
  eq_opp eq_zero eq_one
  eq_abs eq_sqr eq_exp eq_other 
  eq_plus eq_minus eq_mult.

(** Next, we will categorise existing lemmas of the form `forall _ : R, _ = _`, and use the rewrite tactic to change the goal.
These are ideal for solving equalities, since they do not require any assumptions.

Note that we add all lemmas to a general database `eq_general`.*)
(** ### **Plus, minus and multiplication rewriters**
In this database, we will add commutative, associative and distributative properties of numbers in combination with the $+$ operator.
We let $x, y ∈ \mathbb{R}$.

#### Commutativity:
We have the following commutative properties:*)
Hint Extern 1 => (rewrite Rplus_comm) : eq_general eq_plus. (* x + y = y + x *)
Hint Extern 1 => (rewrite Rmult_comm) : eq_general eq_mult. (* x * y = y * x *)
(** #### Associativity
We have the following associative properties:*)
Hint Extern 1 => (rewrite Rplus_assoc) : eq_general eq_plus. (* x + y + z = x + (y + z) *)
Hint Extern 1 => (rewrite Rmult_assoc) : eq_general eq_mult. (* x * y * z = x * (y * z) *)
(** #### Distributivity
We have the following distributive properties:*)
Hint Extern 1 => (rewrite Rdiv_plus_distr) : eq_general eq_plus. 
  (* (x + y) / z = x / z + y / z *)
Hint Extern 1 => (rewrite Rdiv_minus_distr) : eq_general eq_minus. 
  (* (x - y) / z = x / z - y / z *)
Hint Extern 1 => (rewrite Rmult_plus_distr_l) : eq_general eq_mult eq_plus. 
  (* x * (y+z) = x * y + x * z *)
Hint Extern 1 => (rewrite Rmult_plus_distr_r) : eq_general eq_mult eq_plus. 
  (* (x+y) * z = x * z + y * z *)
(** #### Other
We have some other properties:
*)
Hint Extern 1 => (unfold Rminus) : eq_minus.
(** ### **Opposite rewriters**
In this database, we will add properties with the additive inverse.*)
(** #### Distributitivity
We have the following distributive properties containing additive inverses:*)
Hint Extern 1 => (rewrite Ropp_minus_distr) : eq_general eq_opp. 
  (* - (x - y) = y - x *)
Hint Extern 1 => (rewrite Ropp_minus_distr') : eq_general eq_opp. 
  (* - (y - x) = x - y *)
Hint Extern 1 => (rewrite Ropp_mult_distr_l) : eq_general eq_opp. 
  (* - (x * y) = - x * y *)
Hint Extern 1 => (rewrite Ropp_mult_distr_r) : eq_general eq_opp.
  (* - (x * y) = x * - y *)
Hint Extern 1 => (rewrite Ropp_mult_distr_l_reverse) : eq_general eq_opp. 
  (* - x * y = - (x * y) *)
Hint Extern 1 => (rewrite Ropp_mult_distr_r_reverse) : eq_general eq_opp. 
  (* x * - y = - (x * y) *)
Hint Extern 1 => (rewrite Ropp_plus_distr) : eq_general eq_opp. 
  (* - (x + y) = - x + - y. *)
(** #### Other 
We have some other properties:*)
Hint Extern 1 => (rewrite Ropp_involutive) : eq_general eq_opp. (* --a = a *)
Hint Extern 1 => (rewrite Rmult_opp_opp) : eq_general eq_opp. (* -a * -b = a * b *)
Hint Extern 1 => (rewrite Ropp_div) : eq_general eq_opp. (* - a / b = - (a / b) *)
Hint Extern 1 => (rewrite Rplus_opp_l) : eq_general eq_opp. (* -a  + a = 0 *)
Hint Extern 1 => (rewrite Rplus_opp_r) : eq_general eq_opp. (* a  + -a = 0 *)
(** ### **Simple number arithmetic**
Addition with 0 and multiplication with 0 or 1 is a trivial task, so we use two databases to resolve such simple steps.

#### Arithmetic with 0's
We have the following properties for equations with 0:*)
Hint Extern 1 => (rewrite Rplus_0_l) : eq_general eq_zero. (* 0 + x = x *)
Hint Extern 1 => (rewrite Rplus_0_r) : eq_general eq_zero. (* x + 0 = x *)
Hint Extern 1 => (rewrite Rminus_0_l) : eq_general eq_zero. (* 0 - x = - x *)
Hint Extern 1 => (rewrite Rminus_0_r) : eq_general eq_zero. (* x - 0 = x *)
Hint Extern 1 => (rewrite Rmult_0_l) : eq_general eq_zero. (* 0 * x = 0 *)
Hint Extern 1 => (rewrite Rmult_0_r) : eq_general eq_zero. (* x * 0 = 0 *)
Hint Extern 1 => (rewrite pow_O) : eq_general eq_zero. (* x ^ 0 = 1 *)
(** #### Arithmetic with 1's
We have the following properties for equations with 1:*)
Hint Extern 1 => (rewrite Rmult_1_l) : eq_general eq_one. (* 1 * x = x *)
Hint Extern 1 => (rewrite Rmult_1_r) : eq_general eq_one. (* x * 1 = x *)
Hint Extern 1 => (rewrite Rinv_1) : eq_general eq_one. (* x / 1 = x *)
Hint Extern 1 => (rewrite pow_1) : eq_general eq_one. (* x ^ 1 = x *)
(** ### **Distances and absolute values**
There are a number of trivial steps regarding distances, or absolute values.

#### Distance (R_dist)
We have the following properties:*)
Hint Extern 1 => (rewrite R_dist_eq) : eq_general eq_abs. 
  (* ||a - a|| = 0 *)
Hint Extern 1 => (rewrite R_dist_mult_l) : eq_general eq_abs. 
  (* ||a * b - a * c|| = ||a|| * ||b - c|| *)
Hint Extern 1 => (rewrite R_dist_sym) : eq_general eq_abs. 
  (*||a - b|| = ||b - a||*)
(** #### Absolute value (Rabs)
We have the following properties:*)
Hint Extern 1 => (rewrite Rabs_minus_sym) : eq_general eq_abs. 
  (* |a - b| = |b - a|, using Rabs *)
Hint Extern 1 => (rewrite Rabs_Rabsolu) : eq_general eq_abs. 
  (* | |a| | = |a| *)
Hint Extern 1 => (rewrite Rabs_Ropp) : eq_general eq_abs. 
  (* |-a| = |a| *)
Hint Extern 1 => (rewrite Rabs_mult) : eq_general eq_abs. 
  (* |a * b| = |a| * |b| *)
Hint Extern 1 => (rewrite Rsqr_abs) : eq_general eq_abs. 
  (* a^2 = |a|^2 *)
Hint Extern 1 => (rewrite sqrt_Rsqr_abs) : eq_general eq_abs. 
  (* sqrt(a^2) = |a| *)
Hint Extern 1 => (rewrite pow2_abs) : eq_general eq_abs. 
  (* | a |^2 = a^2*)
(** ### **Squares**
There are a number of trivial steps regarding squares.
We have the following properties:*)
Hint Extern 1 => (rewrite Rsqr_pow2) : eq_general eq_sqr. (* a² = a ^ 2 *)
Hint Extern 1 => (rewrite Rsqr_plus) : eq_general eq_sqr. (* (a-b)² = a² + b² + 2*a*b *)
Hint Extern 1 => (rewrite Rsqr_plus_minus) : eq_general eq_sqr. (* (a+b)*(a-b) = a² - b² *)
Hint Extern 1 => (rewrite Rsqr_minus) : eq_general eq_sqr. (* (a-b)² = a² + b² - 2*a*b *)
Hint Extern 1 => (rewrite Rsqr_minus_plus) : eq_general eq_sqr. (* (a-b)*(a+b) = a² - b² *)
Hint Extern 1 => (rewrite Rsqr_neg) : eq_general eq_sqr. (* a² = (-a)² *)
Hint Extern 1 => (rewrite Rsqr_neg_minus) : eq_general eq_sqr. (* (a-b)² = (b-a)² *)
Hint Extern 1 => (rewrite Rsqr_mult) : eq_general eq_sqr. (* (a*b)² = a² * b² *)
(** ### **Exponentials**
There are a number of trivial steps regarding exponentials. We have the following properties:*)
Hint Extern 1 => (rewrite ln_exp) : eq_general eq_exp. (* ln (exp a)) = a *)
Hint Extern 1 => (rewrite exp_Ropp) : eq_general eq_exp. (* exp (-a) = / exp a*)
Hint Extern 1 => (rewrite exp_plus) : eq_general eq_exp. (* exp(a+b) = exp(a) * exp(b) *)
Hint Extern 1 => (rewrite ln_exp) : eq_general eq_exp. (* ln (exp a)) = a *)

