(** Parser for the Wasm text format. **)
(* (C) J. Pichon - see LICENSE.txt *)

From Wasm Require Import datatypes_properties typing numerics.
From compcert Require Import Integers.
From parseque Require Import Parseque.
Require Import Strings.Byte.
Require Import ZArith.

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
  exact_byte "0" $> 0 <|>
  exact_byte "1" $> 1 <|>
  exact_byte "2" $> 2 <|>
  exact_byte "3" $> 3 <|>
  exact_byte "4" $> 4 <|>
  exact_byte "5" $> 5 <|>
  exact_byte "6" $> 6 <|>
  exact_byte "7" $> 7 <|>
  exact_byte "8" $> 8 <|>
  exact_byte "9" $> 9.

Definition parse_num_aux {n} : byte_parser (Z -> Z) n :=
  (fun d n => 10*n+d) <$>
  ((fun res =>
     match res with
     | (_, d) => d
     end
  ) <$>
  (parse_underscore_forget <?&> parse_digit)).

Definition parse_num_after {n} (f: byte_parser Z n) : byte_parser Z n :=
  @iteratel _ _ _ _ _ _ _ _ _ _ n f parse_num_aux.

Definition parse_num {n} : byte_parser Z n :=
  parse_num_after parse_digit.

Definition parse_hexdigit {n} : byte_parser Z n :=
  parse_digit <|>
  ((exact_byte "A" <|> exact_byte "a") $> 10) <|>
  ((exact_byte "B" <|> exact_byte "b") $> 11) <|>
  ((exact_byte "C" <|> exact_byte "c") $> 12) <|>
  ((exact_byte "D" <|> exact_byte "d") $> 13) <|>
  ((exact_byte "E" <|> exact_byte "e") $> 14) <|>
  ((exact_byte "F" <|> exact_byte "f") $> 15).

Definition parse_hexnum_aux {n} : byte_parser (Z -> Z) n :=
  (fun h n => 16*n+h) <$>
  ((fun res =>
     match res with
     | (_, h) => h
     end
  ) <$>
  (parse_underscore_forget <?&> parse_hexdigit)).

Definition parse_hexnum_after {n} (f: byte_parser Z n) : byte_parser Z n :=
  @iteratel _ _ _ _ _ _ _ _ _ _ n f parse_hexnum_aux.

Definition parse_hexnum {n} : byte_parser Z n :=
  parse_hexnum_after parse_hexdigit.

(* Hex needs to be first *)
Definition parse_unsigned_int {n} : byte_parser Z n :=
  (exact_byte "0" &> exact_byte "x" &> parse_hexnum) <|>
  parse_num.

Definition parse_signed_int {n} : byte_parser Z n :=
  (fun sgn_z =>
     match sgn_z with
     | (sgn_plus, z) => z
     | (sgn_minus, z) => -z
     end
  ) <$>
    (parse_sign <&> ((exact_byte "0" &> exact_byte "x" &> parse_hexnum)
                       <|> parse_num)).

Definition parse_uninterpreted_int {n} : byte_parser Z n :=
  parse_unsigned_int <|>
  parse_signed_int.

Definition parse_i32_sym {n}: byte_parser number_type n :=
  exact_byte "i" &> exact_byte "3" &> exact_byte "2" $> T_i32.

Definition parse_i64_sym {n}: byte_parser number_type n :=
  exact_byte "i" &> exact_byte "6" &> exact_byte "4" $> T_i64.

Definition parse_f32_sym {n}: byte_parser number_type n :=
  exact_byte "f" &> exact_byte "3" &> exact_byte "2" $> T_f32.

Definition parse_f64_sym {n}: byte_parser number_type n :=
  exact_byte "f" &> exact_byte "6" &> exact_byte "4" $> T_f64.

Definition parse_dotconst {n} : byte_parser unit n :=
  exact_byte "." &> exact_byte "c" &> exact_byte "o" &> exact_byte "n" &>
             exact_byte "s" &> exact_byte "t" $> tt.

Definition parse_arg {n} : byte_parser datatypes.value n :=
  parse_i32_sym &> parse_dotconst &> exact_byte " " &> ((fun z => VAL_num (VAL_int32 (Wasm_int.Int32.repr z))) <$> parse_uninterpreted_int) <|>
  parse_i64_sym &> parse_dotconst &> exact_byte " " &> ((fun z => VAL_num (VAL_int64 (Wasm_int.Int64.repr z))) <$> parse_uninterpreted_int).

Record Language (n : nat) : Type := MkLanguage {
  _parse_arg: byte_parser datatypes.value n;
}.

Arguments MkLanguage {_}.

Context
  {Tok : Type} {A B : Type} {n : nat}.

Definition language : [ Language ] := (fun k => MkLanguage parse_arg).

End Language.

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

Definition run_parse_arg (bs : list byte) : option datatypes.value :=
  run bs (fun n => parse_arg).
