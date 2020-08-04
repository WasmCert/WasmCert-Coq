(** The Wasm type checker reflects typing (soundness and completeness) **)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Require Import Coq.Program.Equality.

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

(* 
  This seems really non-trivial. The structure might also change after we fix
    the duplication in the definition of be_type_check. How about we leave this
    as admitted for now and explore other things first?
*)

Lemma wasm_type_checker_reflects_typing:
  forall C cl,
    reflect (cl_typing_self C cl) (cl_type_check C cl).
Proof.
  move => C cl. destruct (cl_type_check C cl) eqn:tc_bool.
  - apply ReflectT. move: tc_bool.
    unfold cl_type_check.
    destruct cl.
    + destruct f.
      unfold b_e_type_checker.
      unfold c_types_agree.
      move: l l0 l1 l2.
      induction l0 => //=.
      -- move => l1 l2 H.
         move/eqP in H; subst.
         unfold cl_typing_self.
         eapply cl_typing_native => //=.
         ++ apply/inst_typeP. by eauto.
         ++ apply bet_empty.
      -- move => l1 l2.
         match goal with
         | |- context C [match ?exp with
                         | CT_top_type _ => _
                         | CT_type _ => _
                         | CT_bot => _ end]
           => destruct exp eqn:HDestruct
                                 end.
      
         admit.
      -- admit.
      -- by [].
    + move => _. by apply cl_typing_host.
  - apply ReflectF. move => tc_prop.
    assert (cl_type_check C cl = true) as HTest; last by rewrite tc_bool in HTest.
    clear tc_bool. 
    
    unfold cl_typing_self in tc_prop.
    inversion tc_prop; subst => //.
    clear H5.
    Print be_typing_ind.
    clear tc_prop.
    
    dependent induction H2; try (inversion Heqtf; subst; clear Heqtf) => //.
    + by apply/eqP.
    + simpl. by rewrite ct_suffix_empty.
    + simpl. by apply/eqP.
    + rewrite upd_label_overwrite in H2. simpl in H2.
      rewrite upd_label_overwrite in IHbe_typing. simpl in IHbe_typing.
      simpl. rewrite upd_label_overwrite.
      
      
      

    
Admitted. (* TODO *)

*)

