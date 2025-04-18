(* LEB128 integer format *)
(* https://en.wikipedia.org/wiki/LEB128 *)
(* TODO: size bound *)
Require Import Numbers.BinNums.
Require Import BinNat BinInt.
Require Import Coq.Init.Byte.
From parseque Require Import Parseque.

(** expects 7 bits, with MSB at head *)
Definition byte_of_7_bits (bs : list bool) : byte :=
  (* using lists is very inefficient *)
  match bs with
  | cons b1 (cons b2 (cons b3 (cons b4 (cons b5 (cons b6 (cons b7 nil)))))) =>
    Byte.of_bits (b7, (b6, (b5, (b4, (b3, (b2, (b1, false)))))))
  | _ => (* should never happen *) x00
  end.

Definition rebalance (bytes_produced : list byte) (bits_produced : list bool) (the_bit : bool) :
  ((list byte) * (list bool)) :=
  if Nat.eqb (List.length bits_produced) 6 then (cons (byte_of_7_bits (cons the_bit bits_produced)) bytes_produced, nil)
  else (bytes_produced, cons the_bit bits_produced).

Fixpoint binary_of_aux2 (acc1 : list byte) (acc2 : list bool (* MSB at head *)) (n : positive) : list byte :=
  (* using lists is very inefficient *)
  match n with
  | xH =>
    let (acc1', acc2') := rebalance acc1 acc2 true in
    let acc2'' := List.app (List.repeat false (6 - List.length acc2)) acc2' in
    cons (byte_of_7_bits acc2'') acc1'
  | xI n' =>
    let (acc1', acc2') := rebalance acc1 acc2 true in
    binary_of_aux2 acc1' acc2' n'
  | xO n' =>
    let (acc1', acc2') := rebalance acc1 acc2 false in
    binary_of_aux2 acc1' acc2' n'
  end.

Definition incr_mod (len: nat) (pad: nat) : nat :=
  if Nat.eqb (S len) pad then 0 else (S len).

(* Convert pos to bits, MSB at head *)
Fixpoint bits_of_pos_pad (acc: list bool) (len: nat) (pad: nat) (n: positive) : list bool :=
  match n with
  | xH =>
    List.app (List.repeat false (pad - 1 - len)) (cons true acc)
  | xI n' =>
    bits_of_pos_pad (cons true acc) (incr_mod len pad) pad n'
  | xO n' =>
    bits_of_pos_pad (cons false acc) (incr_mod len pad) pad n'
  end.

(* Evaluate two's complement LEB128 encoding. Need LSB at head *)
Fixpoint complement_of_one_two_aux (zeros: nat) (bs: list bool) : list bool :=
  match bs with
  | nil => List.repeat false zeros
  | cons true bs' => List.app (List.repeat false zeros) (cons true (List.map negb bs'))
  | cons false bs' => complement_of_one_two_aux (S zeros) bs'
  end.

(* MSB at head *)
Definition complement_of_one_two (bs: list bool) : list bool :=
  List.rev (complement_of_one_two_aux 0 (List.rev bs)).

Fixpoint bytes_of_bits (bs: list bool): list byte :=
  match bs with
  | cons b1 (cons b2 (cons b3 (cons b4 (cons b5 (cons b6 (cons b7 bs')))))) =>
    cons (Byte.of_bits (b7, (b6, (b5, (b4, (b3, (b2, (b1, false)))))))) (bytes_of_bits bs')
  | _ => (* should never happen *) nil
  end.

Definition make_msb_one (b : byte) : byte :=
  let '(b1, (b2, (b3, (b4, (b5, (b6, (b7, _))))))) := Byte.to_bits b in
  Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, true))))))).

Definition make_msb_zero (b : byte) : byte :=
  let '(b1, (b2, (b3, (b4, (b5, (b6, (b7, _))))))) := Byte.to_bits b in
  Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, false))))))).

Definition make_msb_of_non_first_byte_one (bs : list byte) : list byte :=
  match bs with
  | nil => nil
  | cons b bs' => cons b (List.map make_msb_one bs')
  end.

(** LSB at head of list *)
Definition encode_unsigned_aux (n : N) : list byte :=
  match n with
  | N0 => cons x00 nil
  | Npos n' => make_msb_of_non_first_byte_one (binary_of_aux2 nil nil n')
  end.

Definition encode_unsigned (n : N) : list byte :=
  List.rev (encode_unsigned_aux n).

Definition encode_signed_aux (z : Z) : list byte :=
  match z with
  | Z0 => cons x00 nil
  | Zpos n' => make_msb_of_non_first_byte_one (binary_of_aux2 nil nil n')
  | Zneg n' => make_msb_of_non_first_byte_one
                (bytes_of_bits
                   (complement_of_one_two
                      (bits_of_pos_pad nil 0 7 n')))
  end.

Definition encode_signed (z : Z) : list byte :=
  List.rev (encode_signed_aux z).

Section Language.

  Context
    {Toks : nat -> Type} `{Sized Toks byte}
    {M : Type -> Type} `{RawMonad M} `{RawAlternative M}.
  
  Definition byte_parser A n := Parser Toks byte M A n.

  Definition byte_as_N {n} : byte_parser N n :=
    Coq.Strings.Byte.to_N <$> anyTok.

  (* parse a final byte *)
  Definition parse_unsigned_end {n} : byte_parser (N * nat) n :=
    guardM
      (fun b =>
        let '(_, (_, (_, (_, (_, (_, (_, msb))))))) := Byte.to_bits b in
        if msb then None else Some ((Coq.Strings.Byte.to_N b), 1))
      anyTok.

  (* parse a non-final byte *)
  Definition parse_unsigned_ctd {n} : byte_parser N n :=
    guardM
      (fun b =>
       let '(b1, (b2, (b3, (b4, (b5, (b6, (b7, msb))))))) := Byte.to_bits b in
       if msb then Some (Coq.Strings.Byte.to_N (make_msb_zero b))
       else None)
      anyTok.

  Section Unsigned_sec.

    Record Unsigned (n : nat) : Type := MkUnsigned
    { _unsigned : byte_parser (N * nat) n;
    }.
    
    Arguments MkUnsigned {_}.
    
    Context
      {Tok : Type} {A B : Type} {n : nat}.

    Definition parse_unsigned_aux : [ Unsigned ] := Fix Unsigned (fun _ rec =>
      let aux := Induction.map _unsigned _ rec in
      let unsigned_ :=
        parse_unsigned_end <|>
        (((fun lsb '(rest, curlen) => (BinNatDef.N.add lsb (BinNatDef.N.mul 128%N rest), curlen + 1)) <$> parse_unsigned_ctd) <*> aux) in
      MkUnsigned unsigned_).
    
    Definition parse_unsigned_len : [ byte_parser (N * nat) ] :=
      fun n => _unsigned n (parse_unsigned_aux n).
    
    (** top-level function *)
    Definition parse_unsigned (len_bound: nat) {n} : byte_parser N n :=
      guardM
        (fun '(ret, len) =>
           if Nat.leb len len_bound then Some ret
           else None
        )
        (extract parse_unsigned_len n).

  End Unsigned_sec.

Definition sub_2_7 (k : N) :=
  BinIntDef.Z.sub (BinInt.Z_of_N k) (BinIntDef.Z.pow (BinInt.Z.of_nat 2) (BinInt.Z.of_nat 7)).

(* parse a non-final byte *)
Definition parse_signed_end {n} : byte_parser (Z * nat) n :=
guardM
  (fun b =>
    let '(_, (_, (_, (_, (_, (_, (b7, b8))))))) := Byte.to_bits b in
    if b8 then None
    else if b7 then  Some ((sub_2_7 (Coq.Strings.Byte.to_N b)), 1)
    else Some ((ZArith.BinInt.Z_of_N (Coq.Strings.Byte.to_N b)), 1))
  anyTok.

(* parse a final byte *)
Definition parse_signed_ctd {n} : byte_parser Z n :=
  guardM
    (fun b =>
      let '(_, (_, (_, (_, (_, (_, (_, msb))))))) := Byte.to_bits b in
      if msb then Some (sub_2_7 (Coq.Strings.Byte.to_N b))
      else None)
    anyTok.

Section Signed_sec.

  Record Signed (n : nat) : Type := MkSigned
  { _signed : byte_parser (Z * nat) n;
  }.
    
  Arguments MkUnsigned {_}.
    
  Context
    {Tok : Type} {A B : Type} {n : nat}.
    
    Definition signed_aux : [ Signed ] := Fix Signed (fun _ rec =>
      let aux := Induction.map _signed _ rec in
      let signed_ :=
        parse_signed_end <|>
        (((fun lsb '(rest, curlen) => (ZArith.BinInt.Zplus lsb (ZArith.BinInt.Zmult 128%Z rest), curlen+1)) <$> parse_signed_ctd) <*> aux) in
      MkSigned _ signed_).
    
    Definition parse_signed_len : [ byte_parser (Z * nat) ] := fun n => _signed n (signed_aux n).
    
    Definition parse_signed (len_bound: nat) {n} : byte_parser Z n :=
      guardM
        (fun '(ret, len) =>
           if Nat.leb len len_bound then Some ret
           else None
        )
        (extract parse_signed_len n).

  End Signed_sec.

End Language.
