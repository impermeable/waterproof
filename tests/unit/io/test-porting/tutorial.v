(** * Tutorial: Getting used to Waterproof

This tutorial explains how to get started with Waterproof. The aim of Waterproof is to help learning how to prove mathematical statements.

This tutorial is in the form of an #<strong>#exercise sheet#</strong># (sometimes we will call it a #<strong>#notebook#</strong>#). It is a mix of explanations and exercises in which you can try proving mathematical statements yourself. 

The exercise sheet contains #<strong>#text cells#</strong># (white background) and #<strong>#code cells#</strong># (gray background). So far, we have been writing text, in text cells. But now we will introduce the first code cell.
 *)
Require Import Rbase.
Require Import Rfunctions.

Require Import Waterproof.AllTactics.
Require Import Waterproof.notations.notations.
Require Import Waterproof.load_database.RealsAndIntegers.

Open Scope R_scope.

Set Default Goal Selector "!".
Set Default Timeout 5.
(** The code consists of several _sentences_. Every sentence finishes with a period. These sentences above are necessary to make the rest of the notebook work. *)
(** 
We recommend that while you read this notebook, you execute the code sentence-by-sentence by pressing #<strong>#Alt + ↓#</strong># (on MacOS: #<strong>#Option + ↓#</strong># or #<strong>#⌥ + ↓#</strong>#). (Alternatively, you can use the buttons on the left, but it is typically much faster to work with keyboard shortcuts.) *)
(** * 1. Prove a lemma

In the following code cell, we introduce a #<strong>#lemma#</strong>#. We called the lemma #<strong>#example_reflexivity#</strong>#. *)
Lemma example_reflexivity :
  0 = 0.
(** 
We will now prove the lemma. We start the proof by writing the sentence ["Proof."] in a code cell. *)

Proof.
(** 
Execute the code sentence after sentence (press #<strong>#Alt + ↓#</strong># or #<strong>#Option + ↓#</strong>#), until a blue checkmark appears in place of the period after [Proof.]. The checkmark means that Waterproof has checked every sentence before the checkmark. Note how in the part of the screen under #<strong>#Proof progress#</strong># (either on the right of the screen, or down below) appeared what we need to show, namely [(0=0)]. We will often refer to this as the current #<strong>#goal#</strong>#. *)
(** 
Next, we tell Waterproof what to do to prove the lemma. For such a simple statement, we can just write and execute the sentence ["We conclude that (0=0)."] and Waterproof will check automatically that this holds. We will often refer to executing such a sentence as #<strong>#applying a tactic.#</strong># *)

We conclude that (0 = 0).
(** 
Execute the above sentence, with #<strong>#Alt + ↓#</strong>#, until the checkmark appears after the sentence. Note how under proof progress it says [Done.]. The lemma is proved! We close the proof by writing [Qed.]. *)

Qed.
(** 
#<strong>#HINT:#</strong># When writing [We conclude that (...)], it is important that at the place of the dots you write the current goal (which you can see under #<strong>#Proof progress#</strong>#), and not another statement.

#<strong>#HINT:#</strong># If you click on the hammer symbol on the top right, a list of tactics will open. You can click on one of the icons next to the tactics, and the tactic will be either be copied to the clipboard or inserted in the text at the place of the cursor, usually with some placeholders that you need to fill in. *)
(** ** Try it yourself: prove a lemma

You can now try this for yourself. We prepared a lemma below, that we named #<strong>#exercise_reflexivity#</strong>#. *)
Lemma exercise_reflexivity :
  3 = 3.
Proof.
(** The blue brackets below delineate an input area. You can freely work there. Move the mouse just below the first blue bracket until a blue, horizontal line appears and click on it. Then, you can add a code cell by pressing #<strong>#Alt + c#</strong># (On MacOS: #<strong>#Ctrl + c#</strong>#), and add a text cell by pressing #<strong>#Alt + t#</strong># (On MacOS: #<strong>#Ctrl + t#</strong>#).

You can also change the text that is already there between the blue brackets by clicking on it.

Below we already added one code cell, which says [Admitted.]. Executing that code cell (#<strong>#Alt + ↓#</strong>#), will also make the proof progress turn to [Done.] #<strong>#However,#</strong># in that case it is not proven but assumed as an axiom. We do this so you can continue executing the notebook even if you cannot solve the exercise.

After you have found a proof, replace the [Admitted.] by [Qed.] (click on the code cell and change the sentence). *)
(** INPUT-START *)
(** Write your solution here, then change the [Admitted.] below to [Qed.]. *)

Admitted.
(** INPUT-END *)
(** * 2. Show *for-all* statements: take arbitrary values

Let us consider the following lemma. *)
Lemma every_x_equal_to_itself :
  for all x : ℝ,
    x = x.
(** > #<strong>#NOTE:#</strong># the notation $x : ℝ$ means $x$ is in $\mathbb{R}$ (or more accurately, $x$ is of type $\mathbb{R}$) may be unfamiliar to you, and you may be more familiar with the notation $x ∈ \reals$. This difference is due to the fact that Waterproof is built on #<strong>#type theory#</strong># and not on set theory. 

#<strong>#HINT:#</strong># You can insert characters such as ℝ either from the symbol menu that opens when clicking on 'Σ' in the top right corner, or you can write '\reals' until a menu pops up and press enter. Make sure that the code reads 'ℝ' and not '\reals' itself. For many other unicode characters you can use a backslash command as well. *)

Proof.
(** 
To show a statement like "for all $x : \mathbb{R}$, ...", you first need to take an arbitrary $x : \mathbb{R}$, and then continue showing ... . We do this by writing and executing the following sentence, i.e. by applying the following #<strong>#tactic#</strong>#. *)

Take x : ℝ.
(** 
When showing $∀ x : ℝ, ...$, after taking $x : \mathbb{R}$ we need to continue showing whatever statement is at the place of the dots $...$. In our case, we need to show that $x = x$. So we are back in a situation we are by now familiar with. We finish the proof as before. *)

We conclude that (x = x).
Qed.
(** ** Try it yourself: show *for-all* statements

Try to complete the proof of the following lemma. *)
Lemma exercise :
  for all x : ℝ,
    x + 3 = 3 + x.
Proof.
(** 
#<strong>#HINT:#</strong># If you would like to get a hint on what you need to do, you can write and execute the sentence [Help.] *)

Help.
(** 

#<strong>#HINT:#</strong># We recommend that always after you write down a sentence, you immediately execute it (#<strong>#Alt + ↓#</strong>#). *)
(** INPUT-START *)
(** Write your solution here. After you have found a proof, remember to change the [Admitted.] below to [Qed.]. *)

Admitted.
(** INPUT-END *)
(** * 3. Show *there-exists* statements: choose values

If you want to show that *there exists* $y : \mathbb{R}$ such that $(\dots)$, you need to #<strong>#choose#</strong># a candidate for $y$, and continue showing $(\dots)$ with your choice. *)
Lemma example_choosing : 
  there exists y : ℝ,
    y < 3.
(***)

Proof.
(** 
We first choose $y:=2$ by using the tactic [Choose y := ((* value *)).]. *)

Choose y := (2).
(** 
(In this particular case we could also have written [Choose y := 2], but in general the brackets are important.)

We now need to show that (y<3) (see #<strong>#Proof progress#</strong># after executing the previous sentence). We can record this for our own convenience. *)

We need to show that (y < 3).
(** 
In other words, we need to show that ($2 < 3$). We can also use the [We need to show that] tactic to slightly reformulate the goal. *)

We need to show that (2 < 3).
(***)

We conclude that (2 < 3).
Qed.
(** *** Try it yourself: show *there-exists* statements *)
Lemma exercise_choosing :
  there exists z : ℝ,
    10 < z.
Proof.
(** INPUT-START *)
(** Write your solution here... *)

Admitted.
(** INPUT-END *)
(** * 4. Combine *for-all* and *there-exists* statements

Often the statement you need to prove consists of many quantifiers. To deal with such a statement, it is useful to deal with this one quantifier at a time, using the techniques that you have just learnt. Here is an example. *)
Lemma example_combine_quantifiers :
  ∀ a : ℝ,
    ∀ b : ℝ,
      ∃ c : ℝ,
        c > b - a.
(***)

Proof.
(** We first deal with (∀ a : ℝ, ... ) by taking an arbitrary $a$ in $ℝ$. *)

Take a : ℝ.
(** 
Next, we need to deal with the quantified statement (∀ b : ℝ, ...). We take an arbitrary $b$ in $ℝ$. *)

Take b : ℝ.
(** 
Now we need to deal with (∃ c : ℝ, ...). We need to make a choice for $c$. *)

Choose c := (b - a + 1).
(** 
Now we can finish the proof. *)

We need to show that (c > b - a).
We need to show that (b - a + 1 > b - a).
We conclude that (b - a + 1 > b - a).
Qed.
(** ** Try it yourself: combine *for-all* and *there-exists* statements.

Can you prove the following lemma by dealing with one quantifier at a time? *)
Lemma exercise_combine_quantifiers :
  ∀ x : ℝ,
    ∀ y : ℝ,
      ∃ z : ℝ,
        x < z - y.
        
Proof.
(** INPUT-START *)
(** Write your solution here... *)

Admitted.
(** INPUT-END *)
(** * 5. Make an assumption

The following lemma expresses that for all $a : \mathbb{R}$, if $a < 0$ then ($-a > 0$). *)

Lemma example_assumptions :
  ∀ a : ℝ, a < 0 ⇒ - a > 0.
(** Corresponding to what we explained above, if we want to show this statement, we first need to take an arbitrary $a : ℝ$. Afterwards, we need to show that $(a < 0) ⇒ (- a > 0)$. 

To show such an implication, we should first assume whatever is on the left hand side of the implication arrow, and then continue showing the right-hand side. In Waterproof, this works as follows. *)

Proof.
(** 
Because we need to show a for-all statement, we know how to start the proof. *)

Take a : ℝ.
(** 
If you now execute the code up to previous sentence, you can see in the #<strong>#Proof progress#</strong># that we need to show [a < 0 ⇒ -a > 0.] Remembering the rules for brackets, this means: *)
We need to show that 
  ((a < 0) ⇒ (-a > 0)).
(** 
In words, if $a < 0$ then ($- a > 0$). To show this we need to assume that $a < 0$, and then continue proving that $(-a > 0)$. We can make such an assumption with the following sentence. *)

Assume a_lt_0 : (a < 0).
(** 
The #<strong>#name#</strong># of this assumption is in this case #<strong>#a_lt_0#</strong>#. What you are actually assuming is written after the colon, namely #<strong>#a < 0#</strong>#. Note how after executing the sentence, the assumption $a < 0$ is added under #<strong>#Proof progress#</strong># with the name #<strong>#a_lt_0#</strong>#.

We finish the proof. *)
We need to show that (-a > 0).
We conclude that (-a > 0).
Qed.
(** ** Try it yourself: make an assumption

You can practice making assumptions by proving the lemma below. We have added brackets in the statement to help in reading it, but we didn't have to: the lemma would have exactly the same meaning if we would have left out the brackets. *)
Lemma exercise_assumptions :
  ∀ a : ℝ, (∀ b : ℝ, ( a > 0 ⇒ (b > 0 ⇒ a + b > -1))).
  
Proof.
(** INPUT-START *)
(** Write your solution here... *)

Admitted.
(** INPUT-END *)
(** * 6. Chains of (in)equalities

As a last step of a proof in Analysis, we often have a chain of (in)equalities. Consider for instance a case in which we would like to show that for all $ε : \mathbb{R}$, if $ε > 0$ then $\min(\epsilon, 1) ≤ 2$. 

Here are the statement and a possible proof in Waterproof. Note that we need to write [Rmin x y] for the minimum of two real numbers $x$ and $y$. *)

Lemma example_inequalities :
  ∀ ε : ℝ, ε > 0 ⇒ Rmin ε 1 < 2.
(***)
Proof.
Take ε : ℝ.
Assume ε_gt_0 : (ε > 0).
We conclude that
  (&  Rmin ε 1 &≤ 1
               &< 2).
Qed.
(** 
Note how we used special notation for the chain of inequalities

``
(&   Rmin ε 1 &≤ 1
              &< 2).
``

We think of this statement that #<strong>#and#</strong># [Rmin ε 1 ≤ 1] #<strong>#and#</strong># [1 < 2]. 


#<strong>#IMPORTANT#</strong>#: Here are a few issues to pay attention to:
- After opening the first parenthesis, you need to write a '&' sign.
- Directly in front of every comparison operator (such as '≤'), you also need to put the '&' sign.
- Chains of inequalities go from smaller to larger. So only $=$, $≤$ and $<$ are supported. *)
(** ** Try it yourself: chains of (in)equalities *)
Lemma exercise_inequalities :
  ∀ ε : ℝ, ε > 0 ⇒ Rmin (ε / 2) 1 < ε.
  
Proof.
(** Click to open hint.
<hint>
At the end of your proof, use the following chain of inequalities 

[[
Rmin (ε / 2) 1 ≤ ε / 2 < ε
]]

but pay attention to the issues mentioned above: in particular use the '&' sign at the appropriate places. *)
(** INPUT-START *)
(** Write your solution here... *)

Admitted.
(** INPUT-END *)
(** * 7. Backward reasoning in smaller steps

Sometimes, what you need to show can be derived from another statement. In that case, you can tell Waterproof that it suffices to show the second statement. It will then try to verify that indeed the first statement can be derived from the second, and all that's left to do for you is show the second statement. Here is an example. *)
Lemma example_backwards :
  ∀ ε : ℝ,
    ε > 0 ⇒
      3 + Rmax ε 2 ≥ 3.
(***)
Proof.
Take ε : ℝ.
Assume ε_gt_0 : (ε > 0).
(** 
We now tell Waterproof that it suffices to show that ($\max(  ε, 2)≥ 0$). It will automatically try to verify that this is indeed enough. *)

It suffices to show that (Rmax ε 2 ≥ 0).
(** 
We can finish the proof. *)

Rewrite inequality (Rmax ε 2) "≥" (2) "≥" 0.
Qed.
(** ** Try it yourself: backward reasoning in smaller steps

 *)
Lemma exercise_backwards :
  ∀ ε : ℝ, ε > 0 ⇒ 5 - Rmax ε 3 ≤ 5.
(** INPUT-START *)
(** Write your solution here... *)

Admitted.
(** INPUT-END *)
(** * 8. Forward reasoning in smaller steps

Sometimes, the step to what you need to show is too big for Waterproof to find a proof. In that case, the tactic [We conclude that (...).] will not find a proof. Then it often helps to make smaller steps.

Here is an example. *)
Lemma example_smaller_steps :
  ∀ ε : ℝ, ε > 0 ⇒
    4 - Rmax ε 1 ≤ 3.
(***)
Proof.
Take ε : ℝ.
Assume ε_gt_0 : (ε > 0).

(** 
We now make an intermediate step. We let Waterproof automatically show that [(Rmax ε 1 ≥ 1)], and we call that statement [Rmax_gt_1]. *)

It holds that Rmax_gt_1 : (Rmax ε 1 ≥ 1).
(** 
Now Waterproof can finish the proof. *)

We conclude that (4 - Rmax ε 1 ≤ 3).
Qed.
(** 
Sometimes, you also need to tell Waterproof what lemma to use in proving the intermediate step. The following line would tell Waterproof to use the lemma called [Rmax_r].

[[
By Rmax_r it holds that
  Rmax_gt_1 : (Rmax ε 1 ≥ 1). 
]]

For very difficult statements, it may happen that Waterproof cannot find a proof even when providing the name of a lemma. In that case you can first make an intermediate claim.

[[
We claim that Rmax_gt_1 : (Rmax ε 1 ≥ 1).
{
  (* proof of claim *)
}
]] *)
(** ** Try it yourself: forward reasoning in smaller steps *)

Lemma exercise_smallers_steps :
  ∀ ε : ℝ, ε > 0 ⇒
    3 + Rmax 2 ε ≥ 5. 
    
Proof.
(** INPUT-START *)
(** Write your solution here... *)

Admitted.
(** INPUT-END *)
(** * 9. Use a _for-all_ statement

A special case of the above is when you would like to _use_ a for-all statement, as in the example below. *)
Lemma example_use_for_all :
  ∀ x : ℝ, ∀ y : ℝ,
    (∀ δ : ℝ, δ > 0 ⇒ x < δ) ⇒
      (∀ ε : ℝ, ε > 0 ⇒ y < ε) ⇒
        x + y < 1.
(***)
Proof.
Take x : ℝ. Take y : ℝ.
Assume del_cond : (∀ δ : ℝ, δ > 0 ⇒ x < δ).
Assume eps_cond : (∀ ε : ℝ, ε > 0 ⇒ y < ε).

(** We can now #<strong>#use#</strong># the statement that we called [del_cond] with $δ = 1/2$. We can do this by substituting $\delta = 1/2$ as follows. *)

By del_cond it holds that x_lt_half : (x < 1/2).
(** Similarly, we can use the statement that we called [eps_cond]. We can also indicate explicitly that we choose $ε = 1/2$ in the statement by writing [By (eps_cond (1/2)) ...] as in *)

By (eps_cond (1/2)) it holds that y_lt_half : (y < 1/2).

We conclude that (x + y < 1).
Qed.
(** ** Try it yourself: Use a for-all statement *)
Lemma exercise_use_for_all:
  ∀ x : ℝ,
    (∀ ε : ℝ, ε > 0 ⇒ x < ε) ⇒
      10 * x < 1.
      
Proof.
(** INPUT-START *)
(** Write your solution here... *)

Admitted.
(** INPUT-END *)
(** * 10. Use a _there-exists_ statement

In this example we show how to #<strong>#use#</strong># a there-exists statement (when you know it holds). *)

Lemma example_use_there_exists :
  ∀ x : ℝ,
    (∃ y : ℝ, 10 < y ∧ y < x) ⇒
      10 < x.
(***)
Proof.
Take x : ℝ.
Assume exists_y_with_prop : (∃ y : ℝ, 10 < y ∧ y < x).

(** We now would like to use that there exists a $y$ in $\mathbb{R}$ such that $y>10$ and $x > y$. In other words, we would like to obtain such a $y$. We do this as follows. *)

Choose y such that 
  y_gt_10_and_x_gt_y according to exists_y_with_prop.

(***)
We conclude that
  (&  10 &< y
         &< x).
Qed.
(** ** Try it yourself: use a _there-exists_ statement *)
Lemma exercise_use_there_exists :
  ∀ z : ℝ,
    (∃ x : ℝ, (x < -5) ∧ (z > x^2)) ⇒
      25 < z.
      
Proof.
(** INPUT-START *)
(** Write your solution here... *)

Admitted.
(** INPUT-END *)
(** * 11. Argue by contradiction

Sometimes a direct proof is not easy to find, or maybe even impossible, and you need to use a contradiction argument. The following example illustrates how you can do this in Waterproof. *)
Lemma example_contradiction :
  ∀ x : ℝ,
   (∀ ε : ℝ, ε > 0 ⇒ x < ε) ⇒
     x ≤ 0.
(***)
Proof. 
Take x : ℝ.
Assume eps_cond : (∀ ε : ℝ, ε > 0 ⇒ x < ε).
We need to show that (x ≤ 0).
(** We will now argue by contradiction. *)

We argue by contradiction.
(** 
Note how we need to show that $¬ (¬ (x ≤ 0))$. To do so, we first need to assume that $¬ (x ≤ 0)$ and try to arrive at a contradiction. *)

Assume not_x_le_0 : (¬ (x ≤ 0)).
It holds that x_gt_0 : (x > 0).
By eps_cond it holds that x_lt_x_div_2 : (x < x/2).
It holds that x_le_0 : (x ≤ 0).
(** Now we have derived that both $(x ≤ 0)$ and $¬ (x ≤ 0)$. In general, in a contradiction proof in Waterproof you need to make sure that you get a statement $P$ and the statement $¬ P$ in your list of hypotheses. Then you can finish the proof as follows. *)

Contradiction.
Qed.
(** 
Instead of writing [Contradiction.] you can also write [↯.]. You can get the symbol [↯] with the backslash-command [\contradiction]. *)
(** ** Try it yourself: argue by contradiction *)
Lemma exercise_contradiction :
  ∀ x : ℝ,
    (∀ ε : ℝ, ε > 0 ⇒ x > 1 - ε) ⇒
      x ≥ 1.
      
Proof.
(** INPUT-START *)
(** 
Write your solution here... *)

Admitted.
(** INPUT-END *)
(** * 12. Split into cases.

At times, you need to make a case distinction in your proof, as in the following example. *)
Lemma example_cases : 
  ∀ x : ℝ, ∀ y : ℝ,
    Rmax x y = x ∨ Rmax x y = y.
(***)
Proof. 
Take x : ℝ. Take y : ℝ.
(** We now make a case distinction. *)

Either (x < y) or (x ≥ y).
- Case (x < y).
  It suffices to show that (Rmax x y = y).
  By Rmax_right we conclude that (Rmax x y = y).
- Case (x ≥ y).
  It suffices to show that (Rmax x y = x).
  By Rmax_left we conclude that (Rmax x y = x).
Qed.
(** ** Try it yourself: split into cases

See if you can find a proof of the following exercise using a case distinction. *)
Lemma exercises_cases :
  ∀ x : ℝ, ∀ y : ℝ,
    Rmin x y = x ∨ Rmin x y = y.
    
Proof.
(** Click to open hint.
<hint>
Distinguish between cases [x < y] and [x ≥ y]. *)
(** INPUT-START *)
(** 
Write your solution here... *)

Admitted.
(** INPUT-END *)
(** * 13. Prove two statements: A ∧ B

The next example shows how you could prove a statement of the form $A ∧ B$. *)
Lemma example_both_statements:
  ∀ x : ℝ, x^2 ≥ 0 ∧ | x | ≥ 0.
(***)
Proof.
Take x : ℝ.
(** We now need to show $(x^2 ≥ 0) ∧ (|x| ≥ 0)$. *)

We show both statements.
(** 
Now the proof splits into two parts, one for each statement. We need to indicate these two parts using bullet points. They can be indicated by any of [-], [+], [*], [--] etc.. You can use a bulleted list inside of a bulleted list. *)

- We need to show that (x^2 ≥ 0).
  We conclude that (x^2 ≥ 0).
- We need to show that (| x | ≥ 0).
  We conclude that (| x | ≥ 0).
Qed.
(** ** Try it yourself: show both statements

The following exercise gives some practice in showing two statements. *)
Lemma exercise_both_statements:
  ∀ x : ℝ, 0 * x = 0 ∧ x + 1 > x.
  
Proof.
(** INPUT-START *)
(** Write your solution here... Don't forget to use bullet points... *)

Admitted.
(** INPUT-END *)
(** ** 14. Show both directions

If you need to show a statement of the form $A ⇔ B$, then you need to show both directions separately, namely $A ⇒ B$ and $B ⇒ A$. Here is an example. *)
Lemma example_both_directions:
  ∀ x : ℝ, ∀ y : ℝ,
    x < y ⇔ y > x.
(***)
Proof.
Take x : ℝ. Take y : ℝ.

(** We need to indicate that we show both directions. *)

We show both directions.
(** 
Again we need to make use of bullet points to indicate the two directions. *)

- We need to show that (x < y ⇒ y > x ).
  Assume x_lt_y : (x < y).
  We conclude that (y > x).
- We need to show that (y > x ⇒ x < y ).
  Assume y_gt_x : (y > x).
  We need to show that (x < y).
  We conclude that (x < y).
Qed.
(** ** Try it yourself: show both directions

See if you can prove both directions in the following statement. *)
Lemma exercise_both_directions:
  ∀ x : ℝ, x > 1 ⇔ x - 1 > 0.
  
Proof.
(** INPUT-START *)
(** Write your solution here... Don't forget to use bullet points... *)

Admitted.
(** INPUT-END *)
(** * 15. Proof by induction

The following example shows how one could use mathematical induction to show a statement of the form

 $$∀ k : ℕ, ... $$

Note that Waterproof will usually interpret any statement such as an inequality [n(k +1 ) > n k] as a statement comparing real numbers, while in this exercise we need statements that compare natural numbers. To indicate this, we have to write [(n (k+1) > n k)%nat] instead. *)
Lemma example_induction :
  ∀ n : ℕ → ℕ, (∀ k : ℕ, (n k < n (k + 1))%nat) ⇒
    ∀ k : ℕ, (k ≤ n k)%nat.
(***)
Proof.
Take n : (ℕ → ℕ).
Assume n_increasing : (∀ k : ℕ, (n k < n (k + 1))%nat).
(** We can now perform the induction argument. *)

We use induction on k.
- We first show the base case, namely ( (0 ≤ n 0)%nat ).
  We conclude that (0 ≤ n 0)%nat.
- We now show the induction step.
  Assume IH : (k ≤ n k)%nat.
  It holds that n_k_lt_n_k_plus_1 : (n k < n (k + 1))%nat.
  We conclude that (k + 1 ≤ n (k + 1))%nat.
Qed.
(** ** Try it yourself: a proof by induction

Can you prove the following statement using mathematical induction? *)
Lemma exercise_induction :
  ∀ f : ℕ → ℕ, (∀ k : ℕ, (f (k + 1) = f k)%nat) ⇒
    ∀ k : ℕ, (f k = f 0)%nat.
    
Proof.
(** INPUT-START *)
(** write your solution here... *)

Admitted.
(** INPUT-END *)
(** * 16. Expand definitions

It happens that you need to use a definition of some object in Waterproof, for instance the definition of a function. Here is the definition of a function called [square]. *)

Definition square (x : ℝ) := x^2.
(** 
We now aim to prove the following lemma. *)
Lemma example_expand :
  ∀ x : ℝ, square x ≥ 0.
(***)
Proof.
Take x : ℝ.
(** At this stage, Waterproof does not know how to continue. We could immediately reformulate the goal by writing [We need to show that (x^2 ≥ 0).], or we could write 

[[
We conclude that
  (& square x &= x^2
              &≥ 0). 
]]
However these options aren't available if you do not know the definition of [square]. In that case you could write *)

Expand the definition of square.
(** 
Now Waterproof has expanded the definition of [square] in the goal. It is always important to keep the proof readable, so that's why Waterproof asks you now to also reformulate the goal. *)

That is, write the goal as (x^2 ≥ 0).
We conclude that (x^2 ≥ 0).
Qed.
(** You can also expand the definition in a hypothesis. For instance,
[[
Expand the definition of square in H.
]]
would expand the definition of [square] in the hypothesis with the name [H]. *)
(** ** Try it yourself: expand a definition *)
Lemma exercise_expand :
  ∀ x : ℝ, - (square x) ≤ 0.
  
Proof.
(** INPUT-START *)
(** Write your solution here... *)

Admitted.
(** INPUT-END *)