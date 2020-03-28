From compcert Require Import Integers.
From parseque Require Import Parseque Running.
Require Import Coq.Arith.Le.

Section Check.

Context
  {Toks : nat -> Type} `{Sized Toks Byte.byte}
  {M : Type -> Type} `{RawMonad M} `{RawAlternative M} `{RawMonadRun M}
  {Tok : Type} `{Tokenizer Tok}
  {A : Type}.

Definition check_toks : list Byte.byte -> [ Parser (SizedList Byte.byte) Byte.byte M A ] -> Type := fun s p =>
  let tokens := s in
  let n      := List.length tokens in
  let input  := mkSizedList tokens in
  let result := runParser (p n) (le_refl n) input in
  let valid  := fun s => match Success.size s with | O => Some (Success.value s) | _ => None end in
  match mapM valid (runMonad result) with
    | Some (cons hd _) => @Singleton A hd
    | _                => False
  end.

  Definition run : list Byte.byte -> [ Parser (SizedList Ascii.ascii) Ascii.ascii M A ] -> option A := fun s p =>
  let tokens := List.map Ascii.ascii_of_byte s in
  let n      := List.length tokens in
  let input  := mkSizedList tokens in
  let result := runParser (p n) (le_refl n) input in
  let valid  := fun s => match Success.size s with | O => Some (Success.value s) | _ => None end in
  match mapM valid (runMonad result) with
    | Some (cons hd _) => Some hd
    | _                => None
  end.

End Check.
