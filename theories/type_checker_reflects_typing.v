(** The Wasm type checker reflects typing (soundness and completeness) **)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Require Import Coq.Program.Equality.

Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Wasm Require Import common operations typing type_checker properties.

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
  rewrite subn0. apply/eqP.
  by rewrite drop_size.
Qed.

Lemma ct_suffix_split: forall s l,
  ct_suffix s l = true ->
  l = take (size l - size s) l ++ s.
Proof.
  induction s => //=.
  - intros.
    rewrite subn0.
    rewrite take_size.
    by rewrite cats0.
  - intros.
    unfold ct_suffix in H; simpl in H.
    move/andP in H. destruct H as [H1 H2].
    move/eqP in H2.
    rewrite - H2.
    by rewrite cat_take_drop.
Qed.
    
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

Ltac simplify_hypothesis Hb :=
  repeat match type of Hb with
  | is_true (es_is_trap _) => move/es_is_trapP: Hb => Hb
  | ?b = true => fold (is_true b) in Hb
  | (_ == _) = false => move/eqP in Hb
  | context C [size (rev _)] => rewrite size_rev in Hb
  | context C [take _ (rev _)] => rewrite take_rev in Hb
  | context C [rev (rev _)] => rewrite revK in Hb
  | context C [true && _] => rewrite Bool.andb_true_l in Hb
  | context C [_ && true] => rewrite Bool.andb_true_r in Hb
  | context C [false || _] => rewrite Bool.orb_false_l in Hb
  | context C [_ || false] => rewrite Bool.orb_false_r in Hb
  | context C [type_update _ _] => unfold type_update in Hb; simpl in Hb
  | context C [ct_suffix [::] _] => rewrite ct_suffix_empty in Hb; simpl in Hb
(*  | context C [ct_suffix ?l1 ?l2] => let Hsuffix := fresh "Hsuffix" in
                                     destruct (ct_suffix l1 l2) eqn:Hsuffix; try (apply ct_suffix_split in Hsuffix; simpl in Hsuffix)*)
  | context C [?x - 0] => rewrite subn0 in Hb; simpl in Hb
  | context C [take (size ?x) ?x] => rewrite take_size in Hb; simpl in Hb
  | context C [produce _ _] => unfold produce in Hb; simpl in Hb
  | exists _, _ /\ _ => let tx := fresh "tx" in
                        let Hsuffix := fresh "Hsuffix" in
                        let Hbet := fresh "Hbet" in
                        destruct Hb as [tx [Hsuffix Hbet]]
  | is_true true => clear Hb
  | is_true false => exfalso; apply: notF; apply: Hb
  | is_true (_ == _) => move/eqP in Hb
  | ?x = ?x => clear Hb
  | _ = _ => rewrite Hb in *
         end.

Ltac simplify_goal :=
  repeat match goal with H: _ |- _ => progress simplify_hypothesis H end.

Lemma CT_top_empty_consume: forall tf,
  consume (CT_top_type [::]) tf = CT_top_type [::].
Proof.
  move => tf. unfold consume.
  destruct tf => //=.
  by rewrite ct_suffix_empty.
Qed.

Fixpoint populate_ct_aux (l: list checker_type_aux): list value_type :=
  match l with
  | [::] => [::]
  | t :: l' =>
    match t with
    | CTA_any => T_i32
    | CTA_some vt => vt
    end
      :: populate_ct_aux l'
  end.

Definition populate_ct (ct: checker_type) : list value_type :=
  match ct with
  | CT_type tn => tn
  | CT_top_type tn => populate_ct_aux tn
  | CT_bot => [::]
  end.

Lemma populate_ct_aux_suffix: forall l,
  ct_suffix l (to_ct_list (populate_ct_aux l)).
Proof.
Admitted.
  
Lemma populate_ct_agree: forall l,
  c_types_agree l (populate_ct l).
Proof.
Admitted.

Ltac resolve_bet:=
  repeat match goal with
         | |- be_typing _ [::] (Tf ?tx ?tx) =>
           apply bet_weakening_empty_both; apply bet_empty => //
         | H: be_typing ?C ?bes (Tf ?tn ?tm) |- be_typing ?C (_ :: ?bes) (Tf _ ?tm) =>
           eapply bet_composition_front; last by apply H
         end.

Lemma tc_to_bet_generalized: forall C bes tm ct,
  (match List.fold_left (check_single C) bes ct with
        | CT_top_type ts => ct_suffix ts (to_ct_list tm)
        | CT_type ts => ts == tm
        | CT_bot => false end) = true -> 
  match ct with 
  | CT_type tn => be_typing C bes (Tf tn tm)
  | CT_top_type tn => exists tn', c_types_agree (CT_top_type tn) tn' /\ be_typing C bes (Tf tn' tm)
  | CT_bot => true
  end.
Proof.
  move => C bes. move: C.
  elim: bes => //=.
  - move => C tm ct.
    destruct ct => //=.
    + move => Hsuffix.
      exists tm.
      split => //=.
      by resolve_bet.
    + move => Heq.
      move/eqP in Heq. subst.
      by resolve_bet.
  - move => be bes IH C tm ct Htc.
    apply IH in Htc.
    destruct ct, be => //=; simpl in Htc; simplify_hypothesis Htc.
    (* 56 cases *)
    + exists (populate_ct_aux l).
      split; first by apply populate_ct_aux_suffix.
      resolve_bet.
      by apply bet_unreachable.
    + exists tx.
      split => //.
      resolve_bet.
      apply bet_weakening_empty_both.
      by apply bet_nop.
    + 
      * exists (tx ++ [::T_i32]).
        split; first by apply ct_suffix_empty.
        resolve_bet.
        apply bet_weakening_empty_2.
        by apply bet_drop.
Admitted.
  
Lemma b_e_type_checker_reflects_typing:
  forall C bes tf,
    reflect (be_typing C bes tf) (b_e_type_checker C bes tf).
Proof.
  move => C bes tf.
  destruct tf as [tn tm].
  destruct (b_e_type_checker C bes (Tf tn tm)) eqn: Htc_bool.
  - apply ReflectT.
    unfold b_e_type_checker, c_types_agree in Htc_bool.
    by apply tc_to_bet_generalized in Htc_bool.
  - admit.  
Admitted.
    
(*
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
    clear tc_prop.
    
    dependent induction H2; try (inversion Heqtf; subst; clear Heqtf) => //.
    + by apply/eqP.
    + simpl. by rewrite ct_suffix_empty.
    + simpl. by apply/eqP.
    + rewrite upd_label_overwrite in H2. simpl in H2.
      rewrite upd_label_overwrite in IHbe_typing. simpl in IHbe_typing.
      simpl. rewrite upd_label_overwrite.
      
      
      

    
Admitted.
*)
End Host.

