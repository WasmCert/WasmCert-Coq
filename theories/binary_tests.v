Require Import binary.
Require Import bytes.
Require Import wasm.
Require Import Parseque.
Require Import Coq.Arith.Le.

Section Check.

Context
  {Toks : nat -> Type} `{Sized Toks Integers.Byte.int}
  {M : Type -> Type} `{RawMonad M} `{RawAlternative M} `{RawMonadRun M}
  {Tok : Type} `{Tokenizer Tok}
  {A : Type}.

  (*
Context
  {Tok : Type} `{Tokenizer Tok}
  {M : Type -> Type} `
  {A : Type}.
  *)

Definition check : list Integers.Byte.int -> [ Parser (SizedList Tok) Tok M A ] -> Type := fun s p =>
  let tokens := (fromText s : list Tok) in
  let n      := List.length tokens in
  let input  := mkSizedList tokens in
  let result := runParser (p n) (le_refl n) input in
  let valid  := fun s => match Success.size s with | O => Some (Success.value s) | _ => None end in
  match mapM valid (runMonad result) with
    | Some (cons hd _) => @Singleton A hd
    | _                => False
  end.

End Check.

Definition test1 : check (cons #00 nil) be := MkSingleton
  (Unreachable).