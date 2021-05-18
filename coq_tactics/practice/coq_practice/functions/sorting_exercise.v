(*
  Exercise on sorting 
  Define a function that takes a list as input and returns true when
  it has less than 2 elements or when the first element is smaller than or equal to
  the second one. 

  Then define a function that takes a list as input and returns true
  exactly when this list is sorted (Hint: when the list has at least two elements, the
  first element must be smaller than the second element and the tail must be sorted,
  use the first function to write the second one).
*)

Require Import List.
Require Import Bool.
Require Import Arith.

(* this does the same as 'andb' *)
Definition both_true := fun (b1: bool) (b2: bool) =>
  if b1
  then
    if b2
    then true
    else false
  else false.

(* Function that takes a list and returns true 
  if the list has less than two elements, 
  or the first is smaller/equal than the second.
  Returns false in all other cases. *)
Definition first_smaller_eq_second := fun (li : list nat) =>
  match li with
    nil => true
  | a::nil => true
  | a::b::tail => (a <=? b)
  end.

Compute first_smaller_eq_second (1::2::3::5::nil).
Compute first_smaller_eq_second (5::3::5::nil).
Compute first_smaller_eq_second (5::nil).
Compute first_smaller_eq_second (nil).

Fixpoint check_is_sorted (li: list nat) : bool :=
  match li with
    nil => true
  | a::tail => andb (first_smaller_eq_second li) (check_is_sorted tail)
  end.

Compute check_is_sorted (1::2::3::5::nil).
Compute check_is_sorted (5::3::5::nil).
Compute check_is_sorted (5::nil).
Compute check_is_sorted (999::1010::3030::nil).