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

Lemma ct_suffix_any_1: forall l,
  size l > 0 ->
  ct_suffix [::CTA_any] l.
Proof.
  move => l H.
  destruct l => //=.
  unfold ct_suffix, ct_list_compat => /=.
  destruct (_ -1) eqn: Hsize => //.
  - destruct l => //=. apply/andP.
    split => //. by destruct c.
  - assert (size (drop n l) = 1).
    { rewrite size_drop. by lias. }
    remember (drop n l) as l'.
    do 2 destruct l' => //=.
    by destruct c0.
Qed.

Lemma ct_list_compat_self: forall l,
  ct_list_compat l l.
Proof.
  induction l => //.
  unfold all2.
  apply/andP; split => //.
  by destruct a => //=.
Qed.

Lemma ct_suffix_self: forall l,
  ct_suffix l l.
Proof.
  move => l.
  unfold ct_suffix => /=.
  apply/andP; split => //.
  rewrite subnn.
  rewrite drop0.
  by apply ct_list_compat_self.
Qed.

Lemma ct_suffix_suffix: forall l1 l2,
  ct_suffix (to_ct_list l2) (to_ct_list (l1 ++ l2)).
Proof.
  move => l1 l2.
  unfold ct_suffix.
  apply/andP; split => //; repeat rewrite size_map; rewrite size_cat => //.
  - by lias.
  - unfold to_ct_list. rewrite map_cat.
    replace (size l1 + size l2 - size l2) with (size l1); last by lias.
    rewrite drop_size_cat; last by rewrite size_map.
    by apply ct_list_compat_self.
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
  | context C [ct_suffix [::CTA_any] (_::_)] => rewrite ct_suffix_any_1 in Hb => //; simpl in Hb
  | context C [ct_suffix ?l ?l] => rewrite ct_suffix_self in Hb => //; simpl in Hb
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

Definition populate_ct_aux_single (cta: checker_type_aux): value_type :=
  match cta with
  | CTA_any => T_i32
  | CTA_some vt => vt
  end.

Definition populate_ct_aux (l: list checker_type_aux): list value_type :=
  map populate_ct_aux_single l.

Definition populate_ct (ct: checker_type) : list value_type :=
  match ct with
  | CT_type tn => tn
  | CT_top_type tn => populate_ct_aux tn
  | CT_bot => [::]
  end.

Ltac resolve_bet:=
  repeat match goal with
         | |- be_typing _ [::] (Tf ?tx ?tx) =>
           apply bet_weakening_empty_both; apply bet_empty => //
         | H: be_typing ?C ?bes (Tf ?tn ?tm) |- be_typing ?C (_ :: ?bes) (Tf _ ?tm) =>
           eapply bet_composition_front; last by apply H
         | H: is_true ?expr |- context C [ if ?expr then _ else _ ] =>
           idtac H; rewrite H => //=
         end.

Ltac auto_rewrite_cond:=
  repeat match goal with
         | H: is_true ?expr |- context C [ ?expr ] =>
           rewrite H => //=
         | H: ?x <> ?y |- context C [?x != ?y ] =>
           move/eqP in H; rewrite H => //=
         | H: is_true (Nat.eqb ?x ?y) |- _ =>
           move/eqP in H; rewrite H => //=
         | H: is_true (b_e_type_checker _ _ _) |- _ => simpl in H => //=
         | |- context C [ ?x == ?x ] =>
           rewrite eq_refl => //=
         | |- context C [ true && true ] =>
           unfold andb => //=
         | |- context C [ct_suffix [::] _] => rewrite ct_suffix_empty => //=
         | |- context C [ct_suffix [::CTA_any] (_::_)] => rewrite ct_suffix_any_1 => //=
         | |- context C [ct_suffix ?l ?l] => rewrite ct_suffix_self => //=
         | |- context C [ct_suffix ?l (?l)%list] => rewrite ct_suffix_self => //=
         | |- context C [size (to_ct_list _)] => unfold to_ct_list; rewrite size_map => //=
         | |- context C [?x - ?x] => rewrite subnn => //=
         | |- context C [take 0 _] => rewrite take0 => //=
         | |- context C [drop 0 _] => rewrite drop0 => //=
         | |- context C [_ :: (tc_label _)] => rewrite - cat1s => //=
         | |- context C [size (_ ++ _)] => rewrite size_cat => //=
         | |- context C [size (_ ++ _)%list] => rewrite size_cat => //=
         | |- context C [?x + ?n - ?n] => replace (x + n - n) with x; last by lias => //=
         | H: is_true (plop2 _ _ _) |- _ => unfold plop2 in H => //=
         | H: is_true (List.nth_error _ _ == _) |- _ => move/eqP in H; rewrite H => //=
         | H: _ = _ |- _ => rewrite H => //=
         | _ => (try rewrite ct_suffix_suffix => //=); (try rewrite ct_suffix_self => //=)
         end.

Lemma populate_ct_aux_suffix: forall l,
  ct_suffix l (to_ct_list (populate_ct_aux l)).
Proof.
  induction l => //=.
  unfold ct_suffix => /=.
  apply/andP; split.
  - repeat rewrite size_map. by lias.
  - unfold ct_list_compat.
    unfold ct_suffix, ct_list_compat in IHl.
    auto_rewrite_cond.
    repeat rewrite size_map in IHl.
    repeat rewrite size_map.
    rewrite subnn in IHl.
    rewrite subnn.
    simpl.
    move/andP in IHl.
    destruct IHl as [_ H].
    rewrite drop0 in H.
    rewrite H.
    destruct a => //=.
    by apply/andP.
Qed.

Lemma populate_ct_agree: forall l,
  l <> CT_bot ->
  c_types_agree l (populate_ct l).
Proof.
  intros.
  destruct l => //=.
  by apply populate_ct_aux_suffix.
Qed.

Lemma same_lab_h_condition: forall C i ts l,
  i \in l ->
  all (fun i: nat => (i < length (tc_label C)) && plop2 C i ts) l ->
  same_lab l (tc_label C) = Some ts.
Proof.
Admitted.

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
    + destruct l => //=; simpl in Htc; simplify_hypothesis Htc.
      * exists (tx ++ [::T_i32]).
        split; first by apply ct_suffix_empty.
        resolve_bet.
        apply bet_weakening_empty_2.
        by apply bet_drop.
      * exists (tx ++ populate_ct_aux [:: c]).
        split => //.
        2: { resolve_bet. apply bet_weakening_empty_2. by apply bet_drop. }
        unfold to_ct_list. rewrite map_cat => /=.
        destruct l => //=.
Admitted.
  
Lemma b_e_type_checker_reflects_typing:
  forall C bes tf,
    reflect (be_typing C bes tf) (b_e_type_checker C bes tf).
Proof with auto_rewrite_cond.
  move => C bes tf.
  destruct tf as [tn tm].
  destruct (b_e_type_checker C bes (Tf tn tm)) eqn: Htc_bool.
  - apply ReflectT.
    unfold b_e_type_checker, c_types_agree in Htc_bool.
    by apply tc_to_bet_generalized in Htc_bool.
  - apply ReflectF.
    move => Hbet.
    assert (b_e_type_checker C bes (Tf tn tm)) as H; (try by rewrite H in Htc_bool); clear Htc_bool.
    induction Hbet; subst => //=; unfold type_update => //=; simplify_goal; (try rewrite ct_suffix_self => //=)...
    + unfold convert_cond...
    + erewrite same_lab_h_condition; last by apply H.
      2: { instantiate (1 := i). rewrite mem_cat. apply/orP. right. by rewrite mem_head. }
      rewrite ct_suffix_suffix...
    + destruct tf as [t1 t2] => //=...
      unfold type_update => //=...
    + apply List.nth_error_
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

