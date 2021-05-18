(*
Author: Lulof Pirée (1363638)
Creation date: 14 May 2021

Ltac2 implementation of a function that takes a list
and an arbitrary constr, and returns the list without that
constr. 
*)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.

Ltac2 rec remove_from_list (l_seen: constr list) 
    (l_unseen: constr list) (x: constr)  :=
    match l_unseen with
    | n::remainder =>
        match Constr.equal n x with
        | true => List.append l_seen remainder
        | false => remove_from_list (List.append l_seen [n]) remainder x
        end
    | [] => l_seen
    end.

Ltac2 Eval remove_from_list [] (constr:(1)::constr:(2)::constr:(2)::[]) constr:(2).   

Ltac2 Eval List.remove (Constr.equal) (constr:(2)) (constr:(1)::constr:(2)::constr:(3)::[]).   

(* Does almost the same, but filters out ALL occurences where
    the boolean function evaluates to true.*)
Ltac2 Eval List.filter_out (fun (x:constr) => Constr.equal x constr:(2))(constr:(1)::constr:(2)::constr:(3)::[]).   
Ltac2 Eval List.filter_out (fun (x:constr) => Constr.equal x constr:(2))(constr:(1)::constr:(2)::constr:(2)::[]).   