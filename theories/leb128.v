Require Import bytes.
Require Import Numbers.BinNums.
Require Import NArith.BinNat.
Require Import Running.

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

(** expects 7 bits, with MSB??? at head *)
Definition byte_of_bits (bs : list bool) : Integers.Byte.int :=
  byte_of_bits_aux Integers.Byte.zero bs.

Definition byte_of_bits_check (bs : list bool) :=
  Singleton (byte_of_bits bs).

Definition test0 : byte_of_bits_check nil := MkSingleton #00.
Definition test1 : byte_of_bits_check (true :: nil) := MkSingleton #01.
Definition test2 : byte_of_bits_check (true :: false :: nil) := MkSingleton #02.
Definition test3 : byte_of_bits_check (true :: true :: nil) := MkSingleton #03.
Definition testB : byte_of_bits_check (true :: false :: true :: true :: nil) := MkSingleton #0B.
Definition testDB : byte_of_bits_check (true :: true :: false :: true :: true :: false :: true :: true :: nil) := MkSingleton #DB.
Definition testE5 : byte_of_bits_check (true :: true :: true :: false :: false :: true :: false :: true :: nil) := MkSingleton #E5.
Definition testF : byte_of_bits_check (List.repeat true 8) := MkSingleton #FF.

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

Definition encode_unsigned_check (n : nat) :=
  Singleton (encode_unsigned n).

Definition test2_0 : encode_unsigned_check 0 := MkSingleton (cons #00 nil).
Definition test2_1 : encode_unsigned_check 1 := MkSingleton (cons #01 nil).

Definition plop n :=
  List.map (fun x => BinIntDef.Z.to_nat (Integers.Byte.intval x)) (encode_unsigned n).

Compute plop 255.

Compute plop 624485.

(* test from Wikipedia article *)
Definition testX :
  encode_unsigned_check 624485 := MkSingleton (cons ( #E5 ) (cons ( #8E ) (cons ( #26 ) nil) ) ).

(* TODO: signed *)
