Require Import leb128.
Require Import bytes.
Require Import Running.

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

Definition encode_unsigned_check (n : nat) :=
  Singleton (encode_unsigned n).

Definition test2_0 : encode_unsigned_check 0 := MkSingleton (cons #00 nil).
Definition test2_1 : encode_unsigned_check 1 := MkSingleton (cons #01 nil).

Definition plop n :=
  List.map (fun x => BinIntDef.Z.to_nat (Integers.Byte.intval x)) (encode_unsigned n).

(* test from Wikipedia article *)
Definition testX :
  encode_unsigned_check 624485 := MkSingleton (cons ( #E5 ) (cons ( #8E ) (cons ( #26 ) nil) ) ).