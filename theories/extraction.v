(** Extraction to OCaml. **)
(* (C) M. Bodin - see LICENSE.txt *)

From Wasm Require Import binary type_checker interpreter.

Extraction Language OCaml.

Extraction "extract" parse_wasm cl_type_check run_v.

