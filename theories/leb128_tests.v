From Wasm Require Import leb128 check_toks.
From Coq Require Import Init.Byte ZArith.
From parseque Require Import Running Induction.

(** Example from Wikipedia article: https://en.wikipedia.org/wiki/LEB128#Unsigned_LEB128
   This is the representation of the number [624485]. **)
Definition test_wikipedia : list Byte.byte :=
  xe5 :: x8e :: x26 :: nil.

Definition encode_unsigned_check (k : N) :=
  Singleton (encode_unsigned k).

Lemma test_wikipedia_encode :
  encode_unsigned_check 624485%N = Singleton test_wikipedia.
Proof.
  vm_compute. reflexivity.
Qed.

Definition test_wikipedia_decode :
  check_toks test_wikipedia parse_unsigned = Singleton 624485%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition test_wikipedia_signed: list Byte.byte :=
  xc0 :: xbb :: x78 :: nil.

Definition encode_signed_check (k : Z) :=
  Singleton (encode_signed k).

Lemma test_wikipedia_signed_encode:
  encode_signed_check (-123456)%Z = Singleton test_wikipedia_signed.
Proof.
  vm_compute. reflexivity.
Qed.
