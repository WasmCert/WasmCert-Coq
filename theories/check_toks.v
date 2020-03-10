From compcert Require Import Integers.
From parseque Require Import Parseque Running.
Require Import Coq.Arith.Le.

Section Check.

Context
  {Toks : nat -> Type} `{Sized Toks Integers.Byte.int}
  {M : Type -> Type} `{RawMonad M} `{RawAlternative M} `{RawMonadRun M}
  {Tok : Type} `{Tokenizer Tok}
  {A : Type}.

Definition check_toks : list Tok -> [ Parser (SizedList Tok) Tok M A ] -> Type := fun s p =>
  let tokens := s in
  let n      := List.length tokens in
  let input  := mkSizedList tokens in
  let result := runParser (p n) (le_refl n) input in
  let valid  := fun s => match Success.size s with | O => Some (Success.value s) | _ => None end in
  match mapM valid (runMonad result) with
    | Some (cons hd _) => @Singleton A hd
    | _                => False
  end.

End Check.