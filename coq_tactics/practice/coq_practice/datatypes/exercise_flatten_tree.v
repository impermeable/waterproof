(* Exercise: when rewriting a tree such that every node
  has at most one non-leaf child, the size of the tree remains
  constant. Proof this ofc. *)

Require Import Bool.
Require Import Arith.
Add LoadPath "/home/nifrec/documents/bachelor_3/sep_2IPE0/coq_practice/datatypes/" as working_dir.
Load example_bin_tree.

Fixpoint flatten (t: bin_tree): bin_tree :=
  match t with
    Leaf => Leaf
  | Node child1 child2 => flatten_aux child1 (flatten child2)
  end.

Lemma flatten_size: forall t, size (flatten t) = size t.
Proof.
induction t.

(* Base case: t is a Leaf. *)
simpl. (* flatten simply return 1 for a leaf. *)
reflexivity. (* 1=1 *)

(* Inductive step. t = N t1 t2.
  IHt1 : size (flatten t1) = size t1
  IHt2 : size (flatten t2) = size t2.
  Goal: size (flatten (Node t1 t2)) = size (Node t1 t2) *)

(* Replace "flatten (Node t1 t2)" -> "flatten_aux t1 (flatten t2)" 
  And "size(Node t1 t2) -> S (size t1 + size t2)" *)
simpl.
(* Use lemma form the example: 
  forall t1 t2, size (flatten_aux t1 t2) = size t1 + size t2 + 1.
  Now we change in the goal "flatten_aux t1 (flatten t2)"
  with "size t1 + size (flatten t2) + 1". *)
rewrite flatten_aux_size.
rewrite IHt2.
ring.
Qed.


