Require Import Bool.
Require Import Arith.

Inductive bin_tree : Type :=
    Leaf : bin_tree
  | Node (child1 child2: bin_tree).

Definition not_has_2_leaves (t: bin_tree) : bool :=
  match t with
    Node Leaf Leaf => false
  | _ => true
  end.

Compute not_has_2_leaves Leaf.
Compute not_has_2_leaves (Node Leaf (Node Leaf Leaf)).
Compute not_has_2_leaves (Node Leaf Leaf).

Fixpoint size (t: bin_tree) : nat :=
  match t with
    Leaf => 1
  | Node child1 child2 => 1 + size child1 + size child2
  end.

Compute size Leaf.
Compute size (Node Leaf (Node Leaf Leaf)).
Compute size (Node Leaf Leaf).

Lemma size_correct: forall t, not_has_2_leaves t = false -> size t = 3.
Proof.
intros.
(* Case distinction: either t is a leaf, or t is a (semi-)internal node. *)
destruct t.
(* In case t is a leaf, then the premise is already false. *)
discriminate.

(* In case t is a node, need to do case analysis on its children. *)
destruct t1.
destruct t2.
simpl.
(* Both t1 and t2 a leaf *)
reflexivity.
(* t1 is a leaf, t2 a node. Premise does not hold. *)
discriminate.
(* t1 is a node, t2 is a leaf. Premise does again not hold. *)
discriminate.
Qed.





(* INDUCTIVE PROOFS ON CUSTOM DATATYPE's STRUCTURAL RECURSIVE FUNCTIONS *)

Fixpoint flatten_aux (t1 t2: bin_tree) : bin_tree :=
  match t1 with
    Leaf => Node t2 Leaf
  | Node child1 child2 => flatten_aux child1 (flatten_aux child2 t2)
  end.


Lemma flatten_aux_size:
  forall t1 t2, size (flatten_aux t1 t2) = size t1 + size t2 + 1.
Proof.
induction t1.
(* Now we first get the first case of the "size" definition,
  i.e. t1 = Leaf, which acts as a base case. *)
simpl.
reflexivity.
(* Inductive step. Assume it holds for the children of t1 (t1_1 and t1_2).
  (The children are the fields of the same datatype in the type definition).
  Then replace t1 with (N t1_1 t1_2) and show that the lemma still holds. 

  IHt1_1 : forall t2 : bin_tree,
         size (flatten_aux t1_1 t2) = size t1_1 + size t2 + 1
  IHt1_2 : forall t2 : bin_tree,
         size (flatten_aux t1_2 t2) = size t1_2 + size t2 + 1
*)
intros t2.
simpl.
rewrite IHt1_1.
rewrite IHt1_2.
ring.
Qed.
