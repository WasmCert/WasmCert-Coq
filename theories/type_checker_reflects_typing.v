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

Print upd_local_label_return.

Lemma upd_label_overwrite: forall C loc lab ret lab',
  upd_label (upd_local_label_return C loc lab ret) lab'
  = upd_local_label_return C loc lab' ret.
Proof.
  move => C loc lab ret lab'.
  unfold upd_label.
  unfold upd_local_label_return. by auto.
Qed.

(*???*)
Ltac bool_to_prop_and:=
  repeat match goal with
         | H: _ && _ = true |- _ =>
           move/andP in H; destruct H
         | H: _ && _ |- _ =>
           move/andP in H; destruct H
end.

(*
  Let's first state this lemma which naturally sounds correct.
*)

Lemma inst_typeP:
  forall s i C,
    reflect (inst_type_check s i = C) (inst_typing s i C).
Proof.
  move => s i C. destruct (inst_typing s i C) eqn:itc_bool => //=.
  - apply ReflectT. unfold inst_typing in itc_bool.
    destruct i. destruct C. destruct tc_local => //=. destruct tc_label => //=.
    destruct tc_return => //=.
    unfold inst_type_check => /=.
    bool_to_prop_and.
    (**TODO**)
    move/andP in H. destruct H as [H H1].
    move/andP in H. destruct H as [H H2].
    move/andP in H. destruct H as [H H3].
    move/eqP in H. rewrite H. clear H.
    (**---**)
    admit.
  - admit.
Admitted.

(* 
  This seems really non-trivial. The structrue might also change after we fix
    the duplication in the definition of be_type_check. How about we leave this
    as admitted for now and explore other things first?
*)

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
    clear tc_bool. move:tc_prop. move:es.
    
    unfold cl_typing_self.
    move => es tc_prop.
    inversion tc_prop; subst => //=.
    clear H5.
    (* This is important as otherwise Coq will fail to remember this information
         and the proof cannot be done otherwise. It's in SF but this is also a 
         good reference:
https://stackoverflow.com/questions/4519692/keeping-information-when-using-induction
    *)
    remember (Tf [::] t2s) as tf.
    unfold cl_type in tc_prop.
    induction H2; subst => //.
    + inversion Heqtf. by apply/eqP.
    + simpl. unfold type_update => /=. rewrite ct_suffix_empty => /=.
      by rewrite ct_suffix_empty.
    + inversion Heqtf; subst. admit.
    + simpl. admit.

    
Admitted. (* TODO *)

