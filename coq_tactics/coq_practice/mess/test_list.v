Require Import List.
Require Import Bool.

Check 1::2::3::999::nil.

Compute map (fun x => x + 3) (1::3::2::nil).

(* Okay, can we also make a function to map instead of only applying it? *)
Definition add_three := fun x: list nat => map (fun y => y + 3) (x).

Print add_three.
Compute add_three (1::3::2::nil).

(* Lists can be appended to each other: *)
Locate "++".
Print app.

(* Returns:  1 :: 2 :: 3 :: 4 :: 5 :: 6 :: nil : list nat *)
Compute let my_list := (1::2::3::nil) in my_list ++ add_three my_list.

(* "Exercise on lists, map, and app Define a function that takes as input a number n and
returns a list with n elements, from 0 to n − 1" *)
Check nil.

Fixpoint recurse_range_list (n: nat) (list_so_far: list nat) : list nat
  :=
  match n with
    0 => list_so_far
  | S p => recurse_range_list p (p::list_so_far)
  end.

Definition range_list := fun n: nat => recurse_range_list n nil.

Compute range_list 10.

Fixpoint sum_list (some_list: list nat): nat :=
  match some_list with
    nil => 0
  | n::tail => n + (sum_list tail)
  end.

Compute sum_list (1::10::3::nil).
