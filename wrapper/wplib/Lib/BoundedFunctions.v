(** * A module for bounded functions
 *)
Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Omega.
Require Import Max.

(** When current working directory is that of BoundedFunctions.v, then 
    adding the folder two levels up in the load path may be necessary *)
Add LoadPath "..\..\".

(** This library is written with the custom 
    notations and tactics developed especially for the 
    waterproof project. *)
(** The current library is intended to be 
    compiled from WaterProof base directory 
    running:
    sercomp -R "WaterProof","WaterProof" --mode=vo ".\WaterProof\Tactics\Tactics.v" *)
(** Moreover, one way to make the next line work is to 
    start coqide from the same directory with
    coqide -R "WaterProof" "WaterProof" ".\WaterProof\Lib\BoundedFunctions.v".*)
Require Import WaterProof.Tactics.Tactics.

Open Scope R_scope.

(** TODO: See if we should wrap the contents of the file in a section. *)

(** We will consider functions defined on a domain D *)
Variable D : Set.

(** We assume that there is an element in D. *)
Variable element : D.


(** TODO: Should we deal with bounded functions as 
    elements of a Coq subsets, making them essentially 
    pairs of a function evidence that it is bounded? 
    Or, for instance, define norm_inf as a function 
    that takes in functions AND evidence that the 
    function is bounded? *)

(** Given a function f : D -> R, the expression is_bdd f 
    encodes that f is bounded. *)
Definition is_bdd := 
  fun (f : D -> R)
    => exists (M : R), forall x : D, Rabs (f x) <= M.

(** Define the set of bounded functions. *)
Definition bdd_func := {f | is_bdd f}.

(** Define (pointwise) addition of two functions *)
Definition f_plus :=
  fun (f g : D -> R) => (fun x : D => f x + g x).

(** Define multiplication of a function with a scalar *)
Definition f_scal_mult :=
  fun (a : R) (f : D -> R) => (fun x : D => a * (f x)).

(** Custom notation for sum of two functions.
    TODO: May need to be optimized. *)
Notation "f + g" := (f_plus f g) : bdd_func_scope.
Open Scope bdd_func_scope.

(** The sum of two bounded functions is bounded. *)
Lemma sum_bdd_func_bdd :
  forall (f g: D -> R) (f_bdd : is_bdd f) (g_bdd : is_bdd g),
    is_bdd (f + g).
Proof.
Take f : (D -> R). Take g : (D -> R). 
Assume f_bdd. Assume g_bdd.
Expand the definition of is_bdd in f_bdd.
Expand the definition of is_bdd in g_bdd. 
Expand the definition of is_bdd.
Choose M_f such that f_le_M_f according to f_bdd : 
    (exists M_f : ℝ , for all x : D,
            Rabs (f x) <= M_f).
Choose M_g such that g_le_M_g
  according to g_bdd : 
    (exists M_g : ℝ , for all x : D,
            Rabs (f x) <= M_g).
We need to show that
  (there exists M : ℝ ,
    for all x : D,
      Rabs (f_plus f g x) <= M).
Choose M := (M_f + M_g)%R.
Take x : D.
Expand the definition of f_plus.
We claim that (Rabs(f x + g x)<= Rabs(f x) + Rabs(g x))
  (H1).
Apply Rabs_triang.
(* TODO: there should be a better way of dealing with this *)
trans_ineq H1.
We need to show that (Rabs (f x) + Rabs (g x) <= M_f + M_g).
This follows immediately.
Qed.

(** Definition of addition of two bounded functions *)
Definition bdd_func_plus :
  bdd_func -> bdd_func -> bdd_func 
  := 
    fun (f_w_ev : bdd_func) (g_w_ev : bdd_func) =>
    (exist (is_bdd))
       (f_plus (proj1_sig f_w_ev) (proj1_sig g_w_ev))
       (sum_bdd_func_bdd
         (proj1_sig f_w_ev)
         (proj1_sig g_w_ev)
         (proj2_sig f_w_ev)
         (proj2_sig g_w_ev)).

(** Definition of the range of a function, 
    in the form of a predicate *)
Definition func_range :=
  fun (f : D -> R) => 
    (fun (y : R) => exists x : D, y = f x).

(** Definition of the function range of the 
    absolute value of a function *)
Definition func_range_abs :=
  fun (f : D -> R) => func_range (fun y => Rabs (f y)).

(** If a function is bounded, the range of the absolute value 
    of the function is bounded from above. *)
Lemma func_bdd_implies_bdd_range :
  forall (f : D -> R),
    is_bdd f -> bound (func_range_abs f).
Proof.
  Take f : (D -> R).
  Assume f_bdd.
  Expand the definition of is_bdd in f_bdd.
  Choose M such that Rabs_f_le_M according to 
    f_bdd : (there exists M : ℝ ,
          for all x : D,
            Rabs (f x) <= M).
  Expand the definition of bound.
  We need to show that 
    (there exists m : R ,
      is_upper_bound (func_range_abs f) m).
  Choose m := M.
  Expand the definition of is_upper_bound.
  We need to show that
    (for all y : R,
      (func_range_abs f) y -> y <= M).
  Take y : R.
  Expand the definition of func_range_abs.
  Expand the definition of func_range.
  Assume original_exists.
  Choose x such that f_x_is_y 
    according to original_exists :
      (there exists x : D,
                    Rabs (f x) = y).
  rewrite f_x_is_y.
  Apply Rabs_f_le_M.
Qed.

(** By assuming the existence of an element in D, 
    we can show that there is an element in the range. *)
Lemma exists_element_in_range_abs :
  forall (f : D -> R),
    exists z, (func_range_abs f) z.
Proof.
Take f : (D -> R).
Choose z := (Rabs (f element)).
Expand the definition of func_range_abs.
Choose x := element.
reflexivity.
Qed.

Definition norm_inf_with_evidence :=
  fun (f : bdd_func) =>
   (completeness (func_range_abs (proj1_sig f))
                   (func_bdd_implies_bdd_range (proj1_sig f) (proj2_sig f))
                   (exists_element_in_range_abs (proj1_sig f))).

(** Define the infinity norm on the set of bounded functions *)
Definition norm_inf :=
  fun (f : bdd_func) => proj1_sig (norm_inf_with_evidence f).

Lemma norm_inf_spec :
  forall (f_w_ev : bdd_func),
    is_lub (func_range_abs (proj1_sig f_w_ev)) (norm_inf f_w_ev).
Proof.
Take f_w_ev : bdd_func.
Apply (proj2_sig (norm_inf_with_evidence f_w_ev)).
Qed.

(** This lemma expresses that the absolute value 
    of the function values of f are bounded by norm_inf f. 
    There is a subtle detail, that in fact, norm_inf 
    works on the type of bounded functions, which 
    are actually dependent pairs of a function and evidence 
    that the function is bounded. *)
Lemma func_val_bdd_by_norm_inf :
  forall (f : D->R) (H : is_bdd f),
    forall (x : D),
      Rabs (f x) <= norm_inf (exist is_bdd f H).
Proof.
Take f : (D -> R).
Assume H : (is_bdd f).
Take x : D.
Define f_w_ev := (exist is_bdd f H).
By (norm_inf_spec) it holds that 
  H1 : (is_lub (func_range_abs (proj1_sig f_w_ev)) (norm_inf f_w_ev)).
Expand the definition of is_lub in H1.
Because H1 both
  H2 and H3.
Expand the definition of is_upper_bound in H2.
Apply H2.
Expand the definition of func_range_abs.
Expand the definition of func_range.
Choose x0 := x.
We need to show that 
  (Rabs(f x) = Rabs(f x)).
This follows by reflexivity.
Qed.


(** The following lemma states that every bound for 
    f is larger than or equal to the norm_inf of f. 

    TODO: improve and use wrapper for rewrite tactic.
    TODO: improve hypothesis naming below.*)
Lemma norm_inf_le_upp_bound :
  forall (f: D ->R) (H : is_bdd f),
    forall L : R,
      (forall x : D, Rabs (f x) <= L)
         -> norm_inf (exist is_bdd f H) <= L.
Proof.
Take f : (D -> R).
Assume H : (is_bdd f).
Take L : R.
Assume L_bd : (for all x : D, Rabs(f x) <= L).
Define f_w_ev := (exist is_bdd f H).
By (norm_inf_spec) it holds that 
  H1 : (is_lub (func_range_abs (proj1_sig f_w_ev)) (norm_inf f_w_ev)).
Expand the definition of is_lub in H1.
Because H1 both H2 and H3.
Expand the definition of is_upper_bound in H3.
Apply H3.
Take z : R.
Expand the definition of func_range_abs.
Expand the definition of func_range.
Assume exists_original : (there exists x : D, z = Rabs( proj1_sig f_w_ev x)).
Choose x such that Rabs_f_x_is_z
  according to exists_original :
    (there exists x : D ,
                    z = Rabs (proj1_sig f_w_ev x)).
rewrite Rabs_f_x_is_z.
Apply L_bd.
Qed.

(** The lemma proj_exist_id is a convenience lemma 
    that states an element in bdd_func can be constructed 
    back from its projections to the function itself and 
    the evidence that it is bounded. *)
Lemma proj_exist_id :
  forall f_w_ev : bdd_func,
    f_w_ev = exist is_bdd (proj1_sig f_w_ev) (proj2_sig f_w_ev).
Proof.
Take f_w_ev : bdd_func.
destruct f_w_ev.
simpl.
reflexivity.
Qed.

(** The lemma norm_inf_triang contains the triangle 
    inequality for norm_inf. *)
Lemma norm_inf_triang:
  forall (f_w_ev : bdd_func) (g_w_ev : bdd_func),
    norm_inf (bdd_func_plus f_w_ev g_w_ev)
      <= norm_inf f_w_ev + norm_inf g_w_ev.
Proof.
Take f_w_ev : bdd_func.
Take g_w_ev : bdd_func.
Define f := (proj1_sig f_w_ev).
Define g := (proj1_sig g_w_ev).
Define f_bdd := (proj2_sig f_w_ev).
Define g_bdd := (proj2_sig g_w_ev).
We claim that (for all x : D,
  Rabs((f_plus f g) x)
  <= norm_inf f_w_ev + norm_inf g_w_ev ) (H_triang).
Take x : D.
Expand the definition of f_plus.
By Rabs_triang it holds that H1 :
  (Rabs (f x + g x) <= Rabs(f x) + Rabs(g x)).
trans_ineq H1.
By (func_val_bdd_by_norm_inf f f_bdd) it holds that H2 :
  (Rabs (f x) <= norm_inf f_w_ev).
By (func_val_bdd_by_norm_inf g g_bdd) it holds that H3 :
  (Rabs (g x) <= norm_inf g_w_ev).
This follows immediately.
Apply norm_inf_le_upp_bound.
Apply H_triang.
Qed.
