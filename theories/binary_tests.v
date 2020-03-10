Require Import binary.
Require Import bytes.
Require Import wasm.
Require Import bytes.
Require Import Parseque.
Require Import Running.
Require Import check_toks.

Definition test_unreachable : check_toks (cons #00 nil) be := MkSingleton Unreachable.
Definition test_nop : check_toks (cons #01 nil) be := MkSingleton Nop.