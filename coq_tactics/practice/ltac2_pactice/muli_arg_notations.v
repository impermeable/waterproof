(*
Author: Lulof Pirée (1363638)
Creation date: 11 May 2021
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.

Ltac2 rec print_my_list x :=
    match x with
    | head :: remainder => print (of_constr head); print_my_list remainder
    | [] => ()
end.

Ltac2 Notation "print_list" x(list1(constr, ",")) := print_my_list x.

Goal True.
    print_list 1, 2, true, 0.
Abort.

Ltac2 rec print_nested_list x :=
    match x with
    | a::remainder => 
        match a with
        | b::nested_remainder => print_my_list (b::nested_remainder); 
                                 print_nested_list remainder
        | [] => ()
        end
    | [] => ()
    end.

Ltac2 Notation "print_nested_list" x(list1(list1(constr, ":"), ",")) := 
    print_nested_list x.  

Goal True.
    print_nested_list 1 : nat, 2 : bool, true : nat, 0 : 10.
Abort.



