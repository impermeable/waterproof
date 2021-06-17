(** * Syntax extensions for Computer programs for analysis

      This document contains some very preliminary experiments with 
      notations, ltac definitions and tactic notations to make it possible 
      to stay closer to mathematical language when writing proofs in Coq. *)

(** This file is supposed to be put in a folder 
    wplib/Tactics/ and intended to be compiled, 
    with 
    sercomp --mode=vo 
           -R "wplib","wplib"
           "wplib/Tactics/TacticsContra.v"*)

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Omega.
Require Import Max.
Require Import Classical.
(* Require Import Unicode.Utf8. *)

(** * Classical tactics *)
    
(** TODO: problem with current implementation is that 
    the assumption is not explicitly named. *)
Ltac contra :=
  match goal with
  | [|- ?X] => destruct (classic X); try assumption
  | _ => idtac "failure of tactic"
  end.

Tactic Notation "We" "argue" "by" "contradiction" :=
  contra.
  
Tactic Notation "Contradiction" := contradiction.
Hint Resolve not_all_not_ex : contra_hints.
Hint Resolve not_all_ex_not : contra_hints.
Hint Resolve not_ex_all_not : contra_hints.
Hint Resolve ex_not_not_all : contra_hints.
Hint Resolve all_not_not_ex : contra_hints.
