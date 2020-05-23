(** The Wasm type checker reflects typing (soundness and completeness) **)
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
Proof.
  move => C es. destruct (cl_type_check C es) eqn:tc_bool.
  - apply ReflectT. move: tc_bool.
    unfold cl_type_check.
    destruct es.
    + destruct f.
      admit.
    + move => _. by apply cl_typing_host.
  - apply ReflectF. move => tc_prop.
    inversion tc_prop; subst => //=.
    + 
    
Admitted. (* TODO *)

