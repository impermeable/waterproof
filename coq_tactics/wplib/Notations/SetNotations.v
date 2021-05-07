(** # Set notations
For Coq's Ensembles library*)
Require Import Sets.Ensembles. 
Require Import wplib.Tactics.Tactics.
Require Import wplib.Notations.Notations.
Notation "'subset' U" := 
  (Ensemble U) (at level 50). 

Notation "'set_of_subsets' U" := 
  (Ensemble (Ensemble U)) (at level 50). 

Definition empty {U} := Empty_set U.
Definition full {U} := Full_set U.
Notation "∅" := 
  (empty). 

Notation "'Ω'" := 
  (full) (at level 0). 

Notation "A ∩ B" := 
  (Intersection _ A B) (at level 45). 

Notation "A ∪ B" := 
  (Union _ A B) (at level 45). 

Notation "A \ B" := 
  (Setminus _ A B) (at level 45). 

Notation "x ∈ A" := 
  (In _ A x) (at level 50) : ensemble_scope. 

Notation "x ∉ A" :=  
  (~ In _ A x) (at level 50). 

Notation "A ⊂ B" := 
  (Included _ A B) (at level 45). 
  
Notation "A 'and' B 'are' 'disjoint'" := 
  (Disjoint _ A B) (at level 50).   
  
Notation "｛ x : T | P ｝" := 
  (fun (x : T) ↦ P) (x at level 99).
(*these brackets are not the same as {}, and are not yet included in shortcuts! *)

Tactic Notation "We" "prove" "equality" "by" "proving" "two" "inclusions" :=
   apply Extensionality_Ensembles; 
   unfold Same_set; 
   unfold Included;
   split.
  
Open Scope ensemble_scope.
