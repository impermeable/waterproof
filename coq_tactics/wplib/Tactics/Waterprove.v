(** * Waterprove: Tactic automation for Waterproof*)
Require Import Reals.
Ltac waterprove t s :=
  timeout 60 (first [ solve [auto using s with *]
        | solve [eauto using s with *]
        | solve [intuition (auto using s with * )]
        | solve [intuition (eauto using s with * )]
        | idtac "Waterproof could not find a proof of " t]).
