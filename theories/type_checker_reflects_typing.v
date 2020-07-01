(** The Wasm type checker reflects typing (soundness and completeness) **)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Wasm Require Import common operations typing type_checker.


Section Host.

Variable host_function : eqType.

Lemma result_typingP : forall r ts,
  reflect (result_typing r ts) (result_types_agree ts r).
Proof.
  move=> + ts. case.
  - move=> l /=. apply: iffP.
    + rewrite all2_swap. by apply: all2_mapP.
    + move=> ?. subst. by constructor.
    + move=> T. by inversion_clear T.
  - apply: Bool.ReflectT. by constructor.
Qed.


Lemma wasm_type_checker_reflects_typing:
  forall C (es : function_closure host_function),
    reflect (cl_typing_self C es) (cl_type_check C es).
Admitted. (* TODO *)

End Host.

