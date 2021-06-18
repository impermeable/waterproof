Require Import Bool.
Require Import Arith.
Add LoadPath "/home/nifrec/documents/bachelor_3/sep_2IPE0/coq_practice/datatypes/" as working_dir.
Load example_bin_tree.


(* The left child of a Node can never be itself. *)
Lemma not_subterm_self_left : forall x y, ~ x = Node x y.
Proof.
induction x.

(* Base case: x is a Leaf.
   Goal: "forall y : bin_tree, Leaf <> Node Leaf y".
   Well that is obvious as a Leaf never is a Node!*)
discriminate.

(* Inductive case: x = N x1 x2.
  IHx1 : forall y : bin_tree, x1 <> Node x1 y
  IHx2 : forall y : bin_tree, x2 <> Node x2 y

  Goal:
  forall y : bin_tree, Node x1 x2 <> Node (Node x1 x2) y *)
(* Proceed by a proof by contradiction. 
  Take any y and assume "Node x1 x2 = Node (Node x1 x2) y"
  "abs" is this assumtion.*)
intros y abs.
(* Very well, if "abs" then "x1 = (Node x1 x2)" and "x2 = y". *)
injection abs.
(* Now need to show this leads to a contradiction. 
  So "x1 = (Node x1 x2)" AND "x2 = y"  == false. *)
intros h2 h1.
(* Ok now we got:
  "IHx1 : forall y : bin_tree, x1 <> Node x1 y"
  "h2: x1 = Node x1 x2"
  Clearly they contradict! *)
apply IHx1 with (y := x2).
exact h1. (* h1 confirms the contradicting fact *)
Qed.



