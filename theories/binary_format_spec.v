From Wasm Require Import datatypes_properties.
From compcert Require Import Integers.
From parseque Require Import Parseque.
Require Import Ascii Byte.
Require Import leb128.
Require Import Coq.Arith.Le.

Inductive repr_unsigned : list ascii -> module -> Prop :=
.

Inductive repr_module : list ascii -> module -> Prop :=
.

(* TODO: we have ast->binary->ast = id
   but not binary->ast->binary /= id, because of non-unique representation  *)