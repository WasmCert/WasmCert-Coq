(* TODO: more tests *)
Require Import leb128.
Require Import Ascii Coq.Init.Byte.
From parseque Require Import Running Induction.
Require Import check_toks.

Definition plop n :=
  List.map (fun x => byte_of_ascii x) (encode_unsigned n).

(* test from Wikipedia article: https://en.wikipedia.org/wiki/LEB128#Unsigned_LEB128 *)
Definition test_wikipedia : list byte :=
  xe5 :: x8e :: x26 :: nil.

Definition encode_unsigned_check (n : nat) :=
  Singleton (plop n).

Eval vm_compute in encode_unsigned_check 624485.

Eval vm_compute in test_wikipedia.

(* TODO: this is way too slow :-( *)

(* Disabled because it takes a while to compute.
Definition test_wikipedia_encode :
  encode_unsigned_check 624485 := MkSingleton test_wikipedia.
*)

(* Disabled because it raises a stack overflow.
Definition test_wikipedia_decode : check_toks test_wikipedia unsigned_ := MkSingleton 624485.
*)





