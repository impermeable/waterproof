(** * Definitions for sets*)
Require Import Reals.
Open Scope R_scope.
(** The following line automatically generates induction schemes for Records.*)
Set Nonrecursive Elimination Schemes.
Record elements_R_satisfying (pred : R -> Prop)
  := mk_element_R {
  element :> R;
  witness : pred element;
}.
Record subsets_R :=
  mk_subset_R {
  is_in : R -> Prop;
  elements := elements_R_satisfying is_in;
}.
Coercion subsets_R_to_elements :=
  (fun A : subsets_R => elements A).



