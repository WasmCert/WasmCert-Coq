(** Extraction to OCaml. **)
(* (C) M. Bodin - see LICENSE.txt *)

From Wasm Require Import binary_parser type_checker interpreter.

Extraction Language OCaml.

Extraction "extract" parse_wasm cl_type_check_single run_v.

