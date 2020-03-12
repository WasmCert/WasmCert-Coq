(* LEB128 integer format *)
(* TODO: size bound *)
(* TODO: write a relational spec, and prove they correspond *)
Require Import Numbers.BinNums.
Require Import NArith.BinNat.
Require Import Ascii.
Require Import Coq.Init.Byte.
From parseque Require Import Parseque.

(** expects 7 bits, with MSB at head *)
Definition byte_of_7_bits (bs : list bool) : ascii :=
  match bs with
  | cons b1 (cons b2 (cons b3 (cons b4 (cons b5 (cons b6 (cons b7 nil)))))) =>
    Ascii b7 b6 b5 b4 b3 b2 b1 false
  | _ => Ascii false false false false false false false false
  end.

Definition rebalance acc1 acc2 b :=
  if Nat.eqb (List.length acc2) 6 then (cons (byte_of_7_bits (cons b acc2)) acc1, nil)
  else (acc1, cons b acc2).

Fixpoint binary_of_aux2 (acc1 : list ascii) (acc2 : list bool (* MSB at head *)) (n : positive) : list ascii :=
  match n with
  | xH =>
    let (acc1', acc2') := rebalance acc1 acc2 true in
    let acc2'' := List.app (List.repeat false (7 - List.length acc2')) acc2' in
    cons (byte_of_7_bits acc2'') acc1'
  | xI n' =>
    let (acc1', acc2') := rebalance acc1 acc2 true in
    binary_of_aux2 acc1' acc2' n'
  | xO n' =>
    let (acc1', acc2') := rebalance acc1 acc2 false in
    binary_of_aux2 acc1' acc2' n'
  end.

Definition make_msb_one '(Ascii b1 b2 b3 b4 b5 b6 b7 _ : ascii) : ascii :=
  Ascii b1 b2 b3 b4 b5 b6 b7 true.

Definition make_msb_of_non_first_byte_one bs :=
  match bs with
  | nil => nil
  | cons b bs' => cons b (List.map make_msb_one bs')
  end.

(** LSB at head of list *)
Definition binary_of (n : N) : list ascii :=
  match n with
  | N0 => cons (ascii_of_byte x00) nil
  | Npos n' => make_msb_of_non_first_byte_one (binary_of_aux2 nil nil n')
  end.

Definition encode_unsigned (n : N) : list ascii :=
  List.rev (binary_of n).

Section Language.

  Context
    {Toks : nat -> Type} `{Sized Toks ascii}
    {M : Type -> Type} `{RawMonad M} `{RawAlternative M}.
  
  Definition w_parser A n := Parser Toks ascii M A n.

  Definition byte_as_N {n} : w_parser N n :=
  (fun x => N_of_ascii x) <$> anyTok.

  Definition unsigned_end_ {n} : w_parser N n :=
    guardM (fun k => match k with
        | Ascii _ _ _ _ _ _ _ msb => if msb then None else Some (N_of_ascii k) end) anyTok.

  Definition unsigned_ctd_ {n} : w_parser N n :=
    guardM (fun k => match k with
      | Ascii b1 b2 b3 b4 b5 b6 b7 msb =>
        if msb then Some (N_of_ascii (Ascii b1 b2 b3 b4 b5 b6 b7 false))
        else None
        end) anyTok.

  Section Unsigned_sec.

    Record Unsigned (n : nat) : Type := MkUnsigned
    { _unsigned : w_parser N n;
    }.
    
    Arguments MkUnsigned {_}.
    
    Context
      {Tok : Type} {A B : Type} {n : nat}.

      SearchAbout (N -> N -> N).
    
    Definition unsigned_aux : [ Unsigned ] := Fix Unsigned (fun _ rec =>
      let aux := Induction.map _unsigned _ rec in
      let unsigned_ :=
        unsigned_end_ <|>
        (((fun lsb rest => BinNatDef.N.add lsb (BinNatDef.N.mul 128 rest)) <$> unsigned_ctd_) <*> aux) in
      MkUnsigned unsigned_).
    
    Definition unsigned_ : [ w_parser N ] := fun n => _unsigned n (unsigned_aux n).

  End Unsigned_sec.

Definition sub_2_7 (k : N) :=
  BinIntDef.Z.sub (BinInt.Z_of_N k) (BinIntDef.Z.pow (BinInt.Z.of_nat 2) (BinInt.Z.of_nat 7)).

  Definition signed_end_ {n} : w_parser Z n :=
  guardM
    (fun k =>
      match k with
      | Ascii _ _ _ _ _ _ _ true => None
      | Ascii _ _ _ _ _ _ true false => Some (sub_2_7 (N_of_ascii k))
      | Ascii _ _ _ _ _ _ false false => Some (ZArith.BinInt.Z_of_N (N_of_ascii k))
      end)
    anyTok.

Definition signed_ctd_ {n} : w_parser Z n :=
  guardM
    (fun k =>
      match k with
      | Ascii _ _ _ _ _ _ _  true =>
        Some (sub_2_7 (N_of_ascii k))
      | Ascii _ _ _ _ _ _ _ false => None
      end)
    anyTok.

  Section Signed_sec.

    Record Signed (n : nat) : Type := MkSigned
    { _signed : w_parser BinNums.Z n;
    }.
    
    Arguments MkUnsigned {_}.
    
    Context
      {Tok : Type} {A B : Type} {n : nat}.
    
    Definition signed_aux : [ Signed ] := Fix Signed (fun _ rec =>
      let aux := Induction.map _signed _ rec in
      let signed_ :=
        signed_end_ <|>
        (((fun lsb rest => ZArith.BinInt.Zplus lsb (ZArith.BinInt.Zmult (ZArith.BinInt.Z_of_nat 128) rest)) <$> signed_ctd_) <*> aux) in
      MkSigned _ signed_).
    
    Definition signed_ : [ w_parser Z ] := fun n => _signed n (signed_aux n).

  End Signed_sec.

End Language.

(* TODO: signed encoding *)
