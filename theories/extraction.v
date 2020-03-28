(** Extraction to OCaml. **)
(* (C) M. Bodin - see LICENSE.txt *)

From Wasm Require Import binary_format_parser type_checker interpreter.

Extraction Language OCaml.

Extraction "extract" run_parse_be_from_asciis cl_type_check run_v.

