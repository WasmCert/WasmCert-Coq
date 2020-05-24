(** The Wasm type checker reflects typing (soundness and completeness) **)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp
Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import operations typing type_checker.

Lemma ct_suffix_empty: forall l,
    ct_suffix [::] l.
Proof.
  move => l. unfold ct_suffix => /=.
  rewrite subn0. apply/eqP. by apply drop_size.
Qed.

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
    assert (cl_type_check C es = true) as HTest; last by rewrite tc_bool in HTest.
    clear tc_bool.
    unfold cl_typing_self in tc_prop.
    inversion tc_prop; subst => //=.
    unfold c_types_agree.
    clear H5.
    (* This is important as otherwise Coq will fail to remember this information
         and the proof cannot be done otherwise. It's in SF but this is also a 
         good reference:
https://stackoverflow.com/questions/4519692/keeping-information-when-using-induction
    *)
    remember (Tf [::] t2s) as tf.
    clear tc_prop.
    induction H2; subst => //.
    + inversion Heqtf. by apply/eqP.
    + simpl. by rewrite ct_suffix_empty.
    + inversion Heqtf. by apply/eqP.
    + simpl.

    
Admitted. (* TODO *)

