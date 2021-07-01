From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.

Ltac2 replace_with_18 (s:string) := String.set s 1 (Char.of_int 18).
Ltac2 Eval let s := (replace_with_18 "hello") in s.

Ltac2 Eval Message.print( Message.of_string (String.make 13 (Char.of_int 100))).


Ltac2 replace_with_18_2 (s:string) := (String.set s 1 (Char.of_int 18); s).

Ltac2 Eval Message.print( Message.of_string (replace_with_18_2 "hello")).

(* let h1 := Ident.of_string(String.set((String.length h + 1) "1")) in
            let h2 := Ident.of_string(String.set((String.length h + 1) "2")) in *)


Ltac2 replace_at_pos (s:string) (pos: int) (c:char) :=
    let s' := s in
    (String.set s' pos c; s').

Ltac2 Eval replace_at_pos "Hollo" 1 (Char.of_int 101).

Ltac2 Eval Char.to_int (String.get "hello" 1). 

Ltac2 rec copy_to_target (source_idx: int) (target_idx:int) (source_end:int)
                         (source: string) (target: string):=
    match Int.equal source_idx source_end with
    | true => target
    | false => let t' := replace_at_pos target target_idx (String.get source source_idx) in
        copy_to_target (Int.add source_idx 1) (Int.add target_idx 1) source_end source t'
    end.

Ltac2 copy_suffix_to_target (source_idx: int) (target_idx:int) 
                         (source: string) (target: string):=
    let i := String.length(source) in
    copy_to_target source_idx target_idx i source target.

Ltac2 underscore := fun () => Char.of_int 95.

Ltac2 Eval copy_suffix_to_target 12 1 "Hello world Unicorns!" "~_________~". 

Ltac2 concat_strings (s1:string) (s2: string) :=
    let tot_len := Int.add (String.length s1) (String.length s2) in
    let empty_result := String.make tot_len (underscore ()) in
    let half_result := copy_suffix_to_target 0 0 s1 empty_result in
        copy_suffix_to_target 0 (String.length s1) s2 half_result.

Ltac2 Eval concat_strings "hello " "world".
    
