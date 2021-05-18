Require Import Arith.

Fixpoint evenb (n: nat) : bool :=
  match n with
    0 => true
  | 1 => false
  | S (S p) => evenb p
  end.

(* Every even number n can be written as 2*x for some x *)
Lemma evenb_p : forall n, evenb n = true -> exists x, n = 2*x.
Proof.
assert (Main: forall n,
      (evenb n = true -> exists x, n = 2*x)
   /\ (evenb (S n) = true -> exists x, S n  = 2*x)).
induction n.
(* Need show base cases:
     (evenb 0 = true -> exists x : nat, 0 = 2 * x)
  /\ (evenb 1 = true -> exists x : nat, 1 = 2 * x)
  Let's do them one by one. *)
split.
(* Assume "evenb 0 = true". Show  ∃[x: 0 = 2*x] follows. *)
exists 0.
(* 0 = 2*0. Hmm that is hard to prove, isn't it? *)
ring.
(* Makes no sence to assume "evenb 1 = true". 
  Show evenb 1 evaluates to false. *)
simpl.
(* false = true -> ... 
  Everything follows from nonsense. *)
intros H.
(* Now we assumed "false = true". Great. *)
discriminate.

(* Now for the recursive case:
     (evenb (S n) = true -> exists x : nat, S n = 2 * x)
  /\ (evenb (S (S n)) = true -> exists x : nat, S (S n) = 2 * x)

  Using the IH:
  IHn:   (evenb n = true -> exists x : nat, n = 2 * x)
      /\ (evenb (S n) = true -> exists x : nat, S n = 2 * x)
*)
split.
(* Ok so first part of goal equals the second part of the IH.
  That is easy! *)
destruct IHn as [_ IHn_2].
exact IHn_2.
(* Second part: (S (S n)) = true -> ∃[x, S(S(n)) = 2 * x].
  From definition of evenb: can replace S(S(n)) by n.*)
simpl evenb.
(* Assume H: "evenb n = true" *)
intros.
(* Separate "(evenb n = true -> exists x : nat, n = 2 * x)" from IH *)
destruct IHn as [IHn_1 _].
assert (exists_x_st_n_is_2x: exists x, n = 2*x).
(* Apply implication of IHn_1 on goal of this assertion *)
apply IHn_1.
exact H.
(* ∃-elim: pick an x with... *)
destruct exists_x_st_n_is_2x as [x n_is_2x].
(* If n = 2*x, then (n+2) = 2*x + 2 = 2*(x + 1) *)
exists (x+1).
(* subst n with 2*x in the goal. 
  Get S(S(2*x)) = 2*(x+1).
  Rest is just arithmetric. *)
rewrite n_is_2x.
ring.

(* WE HAVE PROVEN Main.
  "firstorder" could have solved the rest, but that is too lazy ;) *)
intros n n_is_even.
(* Trick: use the theorem Main as a function.
  The "forall" maps to its conclusion. *)
destruct (Main n) as [n_is_2x _].
apply n_is_2x.
exact n_is_even.
Qed.