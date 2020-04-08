(** The Wasm type checker reflects typing (soundness and completeness) **)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp
Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import operations typing type_checker.


Section Host.

Variable host_function : eqType.

Lemma wasm_type_checker_reflects_typing:
  forall C (es : function_closure host_function),
    reflect (cl_typing_self C es) (cl_type_check C es).
Admitted. (* TODO *)

End Host.

