(** The Wasm type checker reflects typing (soundness and completeness) **)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp
     Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Require Import Coq.Program.Equality.

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

Lemma be_typing_empty: forall C t1s t2s,
  be_typing C [::] (Tf t1s t2s) -> t1s = t2s.
Proof.
  move => C t1s t2s H.
  (*
  (* This is extremely stupid... just why do I have to do this??? *)
  remember [::] as es.

  remember (Tf t1s t2s) as tf.  
  induction H; try by [].
  - by inversion Heqtf.
  - by destruct es => //=.
  - inversion Heqtf. subst. apply IHbe_typing => //=. (* ??? *) admit. *)

  (* dependent induction seems to be much more clever than induction! *)
  (* TODO: check out what dependent induction actually does. Currently I only
     know it as a 'better induction'. *)
  dependent induction H => //=.
  - by destruct es => //=.
  - f_equal. by apply IHbe_typing => //=.
Qed.

(* 
  This seems really non-trivial. The structrue might also change after we fix
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

