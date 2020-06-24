From Flocq Require Import Bits.
Require Import Ascii Byte.
Require Import BinNums ZArith.BinInt.

(* TODO: this to circumvent Flocq's "binary" representation of floats *)

Definition Z_of_ascii (a : ascii) : Z :=
  match a with
  | Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
    let inj (b : bool) := if b then Z.one else Z.zero in
    Zplus (inj b1) (Z.mul 256 (
    Zplus (inj b1) (Z.mul 256 (
    Zplus (inj b3) (Z.mul 256 (
    Zplus (inj b4) (Z.mul 256 (
    Zplus (inj b5) (Z.mul 256 (
    Zplus (inj b6) (Z.mul 256 (
    Zplus (inj b7) (Z.mul 256 (
    (inj b8)))))))))))))))
  end.

(* little endian *)
Fixpoint Z_of_asciis_aux (acc : Z) (factor : Z) (bs : list ascii) :=
  match bs with
  | nil => acc
  | cons b bs' => Z_of_asciis_aux (Z.add acc (Z.mul factor (Z_of_ascii b))) (Zplus 256 factor) bs'
  end.

Definition Z_of_asciis (bs : list ascii) :=
  Z_of_asciis_aux Z.zero Z.one bs.