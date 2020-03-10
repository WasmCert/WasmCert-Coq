(* LEB128 integer format *)
(* TODO: size bound *)
(* TODO: signed integers *)
(* TODO: write a relational spec, and prove they correspond *)
Require Import bytes.
Require Import Numbers.BinNums.
Require Import NArith.BinNat.
From compcert Require Import Integers.
Require Import Parseque.

Fixpoint binary_of_aux (acc : list bool) (n : positive) : list bool :=
  match n with
  | xH => acc
  | xI n' => binary_of_aux (cons true acc) n'
  | xO n' => binary_of_aux (cons false acc) n'
  end.

Definition byte_two := Integers.Byte.add Integers.Byte.one Integers.Byte.one.
Definition byte_4 := Integers.Byte.mul byte_two byte_two.
Definition byte_8 := Integers.Byte.mul byte_4 byte_two.
Definition byte_16 := Integers.Byte.mul byte_4 byte_4.
Definition byte_128 := Integers.Byte.mul byte_16 byte_8.

Fixpoint byte_of_bits_aux (acc : Integers.Byte.int) (bs : list bool) : Integers.Byte.int :=
  match bs with
  | nil => acc
  | cons false bs' => byte_of_bits_aux (Integers.Byte.mul byte_two acc) bs'
  | cons true bs' => byte_of_bits_aux (Integers.Byte.add (Integers.Byte.mul byte_two acc) Integers.Byte.one) bs'
  end.

(** expects 7 bits, with MSB at head *)
Definition byte_of_bits (bs : list bool) : Integers.Byte.int :=
  byte_of_bits_aux Integers.Byte.zero bs.

Definition rebalance acc1 acc2 b :=
  if Nat.eqb (List.length acc2) 6 then (cons (byte_of_bits (cons b acc2)) acc1, nil)
  else (acc1, cons b acc2).

Fixpoint binary_of_aux2 (acc1 : list Integers.Byte.int) (acc2 : list bool (* MSB at head *)) (n : positive) : list Integers.Byte.int :=
  match n with
  | xH =>
    let (acc1', acc2') := rebalance acc1 acc2 true in
    let acc2'' := (* List.repeat false (7 - List.length acc2') *) acc2' in
    cons (byte_of_bits acc2'') acc1'
  | xI n' =>
    let (acc1', acc2') := rebalance acc1 acc2 true in
    binary_of_aux2 acc1' acc2' n'
  | xO n' =>
    let (acc1', acc2') := rebalance acc1 acc2 false in
    binary_of_aux2 acc1' acc2' n'
  end.

Definition decorate_msb b :=
  Integers.Byte.add byte_128 b.

Fixpoint decorate_msbs bs :=
  match bs with
  | nil => nil
  | cons b bs' => cons (decorate_msb b) (decorate_msbs bs')
  end.

Definition decorate_msb_of_non_first_byte bs :=
  match bs with
  | nil => nil
  | cons b bs' => cons b (decorate_msbs bs')
  end.

(** LSB at head of list *)
Definition binary_of (n : N) : list Integers.Byte.int :=
  match n with
  | N0 => cons #00 nil
  | Npos n' => decorate_msb_of_non_first_byte (binary_of_aux2 nil nil n')
  end.

Definition encode_unsigned (n : nat) : list Integers.Byte.int :=
  List.rev (binary_of (N.of_nat n)).

  Section Language.

  Context
    {Toks : nat -> Type} `{Sized Toks Integers.Byte.int}
    {M : Type -> Type} `{RawMonad M} `{RawAlternative M}.
  
  Definition w_parser A n := Parser Toks Integers.Byte.int M A n.

  Definition byte_as_nat {n} : w_parser nat n :=
  (fun x => BinIntDef.Z.to_nat (Integers.Byte.intval x)) <$> anyTok.

Definition unsigned_end_ {n} : w_parser nat n :=
  guardM (fun n => if Nat.leb 128 n then None else Some n) byte_as_nat.

Definition unsigned_ctd_ {n} : w_parser nat n :=
  guardM (fun n => if Nat.leb 128 n then Some (n - 128) else None) byte_as_nat.

  Section Unsigned_sec.

  Record Unsigned (n : nat) : Type := MkUnsigned
  { _unsigned : w_parser nat n;
  }.
  
  Arguments MkUnsigned {_}.
  
  Context
    {Tok : Type} {A B : Type} {n : nat}.
  
  Definition unsigned_aux : [ Unsigned ] := Fix Unsigned (fun _ rec =>
    let aux := Induction.map _unsigned _ rec in
    let unsigned_ :=
      unsigned_end_ <|>
      (((fun lsb rest => lsb + 128 * rest) <$> unsigned_ctd_) <*> aux) in
    MkUnsigned unsigned_).
  
  Definition unsigned_ : [ w_parser nat ] := fun n => _unsigned n (unsigned_aux n).

  End Unsigned_sec.

End Language.

(* TODO: signed *)
