(* the Wasm type checker reflects typing (soundness and completeness) *)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp
Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import operations typing type_checker.

Lemma wasm_type_checker_reflects_typing:
  forall C es,
    reflect (cl_typing_self C es) (cl_type_check C es).
Admitted. (* TODO *)

