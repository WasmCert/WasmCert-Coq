From Wasm Require Import leb128 check_toks.
From Coq Require Import Init.Byte ZArith List.
From parseque Require Import Running Induction.
Import ListNotations.

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

(* https://github.com/WasmCert/WasmCert-Coq/issues/83 *)
Lemma encode_signed_minus65 :
  encode_signed (-65)%Z = (xbf :: x7f :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma encode_signed_plus63 :
  encode_signed 63%Z = (x3f :: nil).
Proof. vm_compute. reflexivity. Qed.

(** Injectivity at boundary *)
Lemma encode_signed_collision :
  encode_signed (-65)%Z <> encode_signed 63%Z.
Proof. vm_compute. intros Heq; inversion Heq. Qed.

Lemma encode_signed_minus8193 :
  encode_signed (-8193)%Z <> encode_signed 8191%Z.
Proof. vm_compute. intros Heq; inversion Heq. Qed.

(** Boundary value -64 still encodes to canonical instead of c0 7f ---- *)
Lemma encode_signed_minus64 :
  encode_signed (-64)%Z = (x40 :: nil).
Proof. vm_compute. reflexivity. Qed.
