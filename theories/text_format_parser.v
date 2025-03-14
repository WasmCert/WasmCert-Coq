(** Parser for the Wasm text format. **)
(* (C) J. Pichon - see LICENSE.txt *)

From Wasm Require Import datatypes_properties typing.
From compcert Require Import Integers.
From parseque Require Import Parseque.
Require Import Strings.Byte.
Require Import ZArith BinInt.

Open Scope Z.

Notation "p $> b" := (cmap b p) (at level 59, right associativity).

Section Language.

Context
  {Toks : nat -> Type} `{Sized Toks byte}
  {M : Type -> Type} `{RawMonad M} `{RawAlternative M}.

Definition byte_parser A n := Parser Toks byte M A n.
Definition be_parser n := byte_parser basic_instruction n.

Definition exact_byte (b : byte) {n} : byte_parser byte n :=
  guardM
    (fun b' =>
      if byte_eqb b' b then Some b'
      else None)
    anyTok.

Inductive value_sign : Set :=
| sgn_plus
| sgn_minus
.

Definition parse_sign {n} : byte_parser value_sign n :=
  exact_byte x2b $> sgn_plus <|>
  exact_byte x2d $> sgn_minus.

Definition parse_underscore_forget {n} : byte_parser unit n :=
  exact_byte x5f $> tt.

Definition parse_digit {n} : byte_parser Z n :=
  exact_byte x30 $> 0 <|>
  exact_byte x31 $> 1 <|>
  exact_byte x32 $> 2 <|>
  exact_byte x33 $> 3 <|>
  exact_byte x34 $> 4 <|>
  exact_byte x35 $> 5 <|>
  exact_byte x36 $> 6 <|>
  exact_byte x37 $> 7 <|>
  exact_byte x38 $> 8 <|>
  exact_byte x39 $> 9.

Definition parse_hexdigit {n} : byte_parser Z n :=
  parse_digit <|>
  ((exact_byte x41 <|> exact_byte x61) $> 10) <|>
  ((exact_byte x42 <|> exact_byte x62) $> 11) <|>
  ((exact_byte x43 <|> exact_byte x63) $> 12) <|>
  ((exact_byte x44 <|> exact_byte x64) $> 13) <|>
  ((exact_byte x45 <|> exact_byte x65) $> 14) <|>
  ((exact_byte x46 <|> exact_byte x66) $> 15).

Definition parse_num_aux {n} : byte_parser (Z -> Z) n :=
  (fun n d => 10*n+d) <$> parse_underscore_forget &> parse_digit.

Definition parse_num_after {n} (f: byte_parser Z n) : byte_parser Z n :=
  @iteratel _ _ _ _ _ _ _ _ _ _ n f parse_num_aux.

Definition parse_num {n} : byte_parser Z n :=
  parse_num_after parse_digit.

Definition parse_hexnum_aux {n} : byte_parser (Z -> Z) n :=
  (fun n h => 16*n+h) <$> parse_underscore_forget &> parse_hexdigit.

Definition parse_hexnum_after {n} (f: byte_parser Z n) : byte_parser Z n :=
  @iteratel _ _ _ _ _ _ _ _ _ _ n f parse_hexnum_aux.

Definition parse_hexnum {n} : byte_parser Z n :=
  parse_hexnum_after parse_hexdigit.

End Language.

Record Language (n : nat) : Type := MkLanguage {
  _be : byte_parser basic_instruction n;
  _bes_end_with_x0b : byte_parser (list basic_instruction) n;
  _bes_end_with_x05 : byte_parser (list basic_instruction) n;
  _bes_end_with_x0b_or_x05_ctd : byte_parser (list basic_instruction * list basic_instruction) n;
}.

Arguments MkLanguage {_}.

Context
  {Tok : Type} {A B : Type} {n : nat}.

Definition language : [ Language ] := Fix Language (fun k rec =>
  let be_aux := Induction.map _be _ rec in
  let bes_end_with_x0b_aux := Induction.map _bes_end_with_x0b _ rec in
  let bes_end_with_x05_aux := Induction.map _bes_end_with_x05 _ rec in
  let bes_end_with_x0b_or_x05_ctd_aux := Induction.map _bes_end_with_x0b_or_x05_ctd _ rec in
  let parse_block :=
    exact_byte x02 &> ((BI_block <$> parse_block_type) <*> bes_end_with_x0b_aux) in
  let parse_loop :=
    exact_byte x03 &> ((BI_loop <$> parse_block_type) <*> bes_end_with_x0b_aux) in
  let parse_if_body :=
    (((fun x y => (x, y)) <$> parse_block_type) <*> bes_end_with_x0b_or_x05_ctd_aux) in
  let parse_if :=
    (fun '(x, (y, z)) => BI_if x y z) <$> (exact_byte x04 &> parse_if_body) in
  let parse_be :=
    parse_unreachable <|>
    parse_nop <|>
    parse_block <|>
    parse_loop <|>
    parse_if <|>
    parse_br <|>
    parse_br_if <|>
    parse_br_table <|>
    parse_return <|>
    parse_call <|>
    parse_call_indirect <|>
    parse_reference_instruction <|>
    parse_parametric_instruction <|>
    parse_variable_instruction <|>
    parse_table_instruction <|>
    parse_memory_instruction <|>
    parse_numeric_instruction in
  let parse_bes_end_with_x0b :=
    (exact_byte x0b $> nil) <|>
    ((cons <$> parse_be) <*> bes_end_with_x0b_aux) in
  let parse_bes_end_with_x05 :=
    (exact_byte x05 $> nil) <|>
    ((cons <$> parse_be) <*> bes_end_with_x05_aux) in
  let parse_bes_end_with_x0b_or_x05_ctd :=
    ((nil, nil) <$ exact_byte x0b) <|>
    (((fun x => (nil, x)) <$ exact_byte x05) <*> parse_bes_end_with_x0b) <|>
    (((fun x '(y, z) => (cons x y, z)) <$> parse_be) <*> bes_end_with_x0b_or_x05_ctd_aux) in
  MkLanguage parse_be parse_bes_end_with_x0b parse_bes_end_with_x05 parse_bes_end_with_x0b_or_x05_ctd).

Definition parse_be : [ byte_parser basic_instruction ] := fun n => _be n (language n).

Inductive Singleton (A : Type) : A -> Type :=
  MkSingleton : forall a, Singleton A a.

Arguments Singleton {_}.
Arguments MkSingleton {_}.

Class Tokenizer (A : Type) : Type :=
  MkTokenizer { _tokenize : list byte -> list A }.

Definition tokenize {A : Type} `{Tokenizer A} : list byte -> list A := _tokenize.

Arguments MkTokenizer {_}.

Definition fromText {A : Type} `{Tokenizer A} (s : list byte) : list A :=
  tokenize s.

#[export]
Instance tokBytes : Tokenizer byte := MkTokenizer (fun x => x).

Section Run.

Context
  {M : Type -> Type} `{RawMonad M} `{RawAlternative M} `{RawMonadRun M}
  {Tok : Type} `{Tokenizer Tok}
  {A : Type}.

Definition run : list byte -> [ Parser (SizedList Tok) Tok M A ] -> option A := fun s p =>
  let tokens := (fromText s : list Tok) in
  let n      := List.length tokens in
  let input  := mkSizedList tokens in
  let result := runParser (p n) (Nat.le_refl n) input in
  let valid  := fun s => match Success.size s with | O => Some (Success.value s) | _ => None end in
  match mapM valid (runMonad result) with
    | Some (cons hd _) => Some hd
    | _                => None
  end.

End Run.

Definition run_parse_num (bs : list byte) : option Z :=
  run bs parse_num.
