From Wasm Require Import datatypes_properties binary_parser_types.
From Wasm Require Import binary_format_parser binary_format_printer.
From compcert Require Import Integers.
From parseque Require Import Parseque.
Require Import Byte.
Require Import leb128.
Require Import Coq.Arith.Le.

Inductive repr_unsigned : list byte -> module -> Prop :=
.

Inductive repr_module : list byte -> module -> Prop :=
.

(* TODO: we should have ast->binary->ast = id
   but not binary->ast->binary /= id, because of non-unique representation  *)

Lemma encode_decode_is_identity : forall m,
(* TODO: probably need some well-formedness condition, for example of block types *)
  run_parse_module (binary_of_module m) = Some m.
(* TODO *)
Admitted.

