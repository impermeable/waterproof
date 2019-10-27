(*# Notations for Waterproof*) Require Import Reals.

Require Import wplib.Tactics.Tactics. (*## Suprema and infima*) Notation is_sup := is_lub. (*## Sets*) Definition is_in {D : Set} := fun (A : (D → Prop)) ↦ (fun (x : D) ↦ A x).
Notation "x ∈ A" := (@is_in _ A x) (at level 50). 