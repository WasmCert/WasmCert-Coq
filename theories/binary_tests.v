Require Import binary.
Require Import bytes.
Require Import wasm.

Compute run (cons #00 nil) be.

Definition test1 : check (cons #00 nil) be := MkSingleton
  (Unreachable).