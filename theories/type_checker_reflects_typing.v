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

Lemma ct_suffix_extend: forall l1 l2 l3,
  ct_suffix l1 l2 ->
  ct_suffix l1 (l3 ++ l2).
Proof.
  unfold ct_suffix.
  move => l1 l2 l3 H.
  move/andP in H; destruct H as [H1 H2].
  apply/andP; split; first by rewrite size_cat; lias.
  rewrite size_cat.
  rewrite drop_cat.
  replace (size l3 + size l2 - size l1 < size l3) with false; last by lias.
  replace (size l3 + size l2 - size l1 - size l3) with (size l2 - size l1); last by lias.
  assumption.
Qed.

Lemma ct_suffix_size: forall ct1 ct2,
  ct_suffix ct1 ct2 ->
  size ct1 <= size ct2.
Proof.
  move => ct1 ct2.
  unfold ct_suffix.
  move => H.
  move/andP in H; destruct H as [H _].
  by repeat rewrite size_map in H.
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

Lemma consume_empty: forall l,
  consume l [::] = l.
Proof.
  move => l.
  by destruct l => //=; rewrite ct_suffix_empty; rewrite subn0; rewrite take_size.
Qed.

Lemma produce_empty: forall l,
  produce l (CT_type [::]) = l.
Proof.
  move => l.
  unfold produce.
  by destruct l => //=; rewrite cats0.
Qed.

Lemma type_update_empty_cons: forall l ct,
  type_update l [::] ct = produce l ct.
Proof.
  move => l.
  unfold type_update. by rewrite consume_empty.
Qed.

Lemma type_update_empty_prod: forall l ts,
  type_update l ts (CT_type [::]) = consume l ts.
Proof.
  move => l ts.
  unfold type_update. by rewrite produce_empty.
Qed.
  

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
  (* It looks really like a bad idea to unfold type_update in general. *)
(*  | context C [type_update _ _] => unfold type_update in Hb; try simpl in Hb*)
  | context C [ct_suffix [::] _] => rewrite ct_suffix_empty in Hb; try simpl in Hb
  | context C [ct_suffix [::CTA_any] (_::_)] => rewrite ct_suffix_any_1 in Hb => //; try simpl in Hb
  | context C [ct_suffix ?l ?l] => rewrite ct_suffix_self in Hb => //; try simpl in Hb
  | context C [?x - 0] => rewrite subn0 in Hb; simpl in Hb
  | context C [take (size ?x) ?x] => rewrite take_size in Hb; simpl in Hb
  | context C [produce _ _] => unfold produce in Hb; simpl in Hb
  | context C [ if ?expr then _ else _ ] => let if_expr := fresh "if_expr" in destruct expr eqn:if_expr => //=; simpl in Hb => //=
  | exists _, _ /\ _ => let tx := fresh "tx" in
                        let Hsuffix := fresh "Hsuffix" in
                        let Hbet := fresh "Hbet" in
                        destruct Hb as [tx [Hsuffix Hbet]]
  | is_true true => clear Hb
  | is_true false => exfalso; apply: notF; apply: Hb
  | is_true (_ == _) => move/eqP in Hb
  | ?x = ?x => clear Hb
  | _ = _ => rewrite Hb in *; subst => //=
  | _ => simpl in Hb => /=
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
         | |- context C [?x - 0] => rewrite subn0 => //=
         | |- context C [take 0 _] => rewrite take0 => //=
         | |- context C [take (size ?x) ?x] => rewrite take_size => //=
         | |- context C [drop 0 _] => rewrite drop0 => //=
         | |- context C [take (drop ?x) ?x] => rewrite drop_size => //=
         | |- context C [_ :: (tc_label _)] => rewrite - cat1s => //=
         | |- context C [_ ++ [::]] => rewrite cats0 => //=
         | |- context C [size (_ ++ _)] => rewrite size_cat => //=
         | |- context C [size (_ ++ _)%list] => rewrite size_cat => //=
         | |- context C [?x + ?n - ?n] => replace (x + n - n) with x; last by lias => //=
(*         | |- context C [type_update _ _] => unfold type_update => //=*)
         | H: match ?expr with | _ => _ end = CT_type _ |- _ => let Hexpr := fresh "Hexpr" in destruct expr eqn: Hexpr => //=
         | H: option_map _ _ = _ |- _ => unfold option_map in H
         | H: Some _ = Some _ |- _ => inversion H; subst; clear H => //=
         | H: CT_type _ = CT_type _ |- _ => inversion H; subst; clear H => //=
         | H: is_true (plop2 _ _ _) |- _ => unfold plop2 in H => //=
         | H: is_true (List.nth_error _ _ == _) |- _ => move/eqP in H; rewrite H => //=
         | H: is_true (_ == _) |- _ => move/eqP in H
         | H: ?x = ?x |- _ => clear H
         | H: _ = _ |- _=> progress (rewrite H; subst => //=)
         | _ => simplify_goal => //=; (try rewrite ct_suffix_suffix => //=); (try rewrite ct_suffix_self => //=); (try subst => //=)
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

Lemma type_update_prefix: forall l1 l2 l3 cons prod,
  type_update (CT_type l1) cons prod = CT_type l2 ->
  type_update (CT_type (l3 ++ l1)) cons prod = CT_type (l3 ++ l2).
Proof.
  unfold type_update, produce, consume.
  move => l1 l2 l3 cons prod H.
  auto_rewrite_cond.
  unfold to_ct_list.
  rewrite map_cat.
  rewrite ct_suffix_extend => //.
  rewrite take_cat.
  assert (size cons <= size l1); first by apply ct_suffix_size in Hexpr1; rewrite size_map in Hexpr1.
  replace (_ < _) with false; last by lias.
  replace (_ + _ - _ - _) with (size l1 - size cons); last by lias.
  by rewrite catA.
Qed.
  
Lemma check_rcons: forall es e C ts,
  check C (es ++ [::e]) ts = check_single C (check C es ts) e.
Proof.
  by induction es => //=.
Qed.
    
Lemma check_single_notop: forall C ct ts e,
  check_single C ct e = CT_type ts ->
  exists ts', ct = CT_type ts'.
Proof with auto_rewrite_cond.
  move => C ct ts e.
  move : C ct ts.
  induction e; move => C ct ts Htc; destruct ct; auto_rewrite_cond; try (unfold type_update in Htc); try by eexists...
Qed.
  
Lemma check_single_bot: forall C e,
  check_single C CT_bot e = CT_bot.
Proof.
  move => C e.
  by destruct e => //=.
Qed.
  
Lemma check_single_weaken: forall C e ts ts2 ts0,
  check_single C (CT_type ts) e = CT_type ts0 ->
  check_single C (CT_type (ts2 ++ ts)) e = CT_type (ts2 ++ ts0).
Proof with auto_rewrite_cond.
  move => C e.
  move : C.
  induction e; move => C ts ts2 ts0 Htc; simpl in Htc => //=; simplify_goal; auto_rewrite_cond; simplify_goal; subst => //=; try by apply type_update_prefix...
  - move/andP in if_expr; destruct if_expr as [H H2].
    move/eqP in H2.
    do 3 destruct ts => //=; clear H.
    (* Numerical disaster *)
    rewrite length_is_size; rewrite size_cat.
    replace (_ < _) with true => /=; last by lias.
    repeat (rewrite List.nth_error_app2; last by rewrite length_is_size; lias).
    repeat rewrite length_is_size.
    replace (_ + _ - 2 - _) with (size ts + 1); last by lias.
    replace (_ + _ - 3 - _) with (size ts); last by lias.
    replace (_ - 2) with (length ts + 1) in H2; last by lias.
    replace (_ - 3) with (length ts) in H2; last by lias.
    rewrite length_is_size in H2.
    rewrite H2.
    rewrite eq_refl.
    unfold to_ct_list.
    rewrite map_cat.
    rewrite ct_suffix_extend => //.
    rewrite take_cat.
    replace (_ < _) with false; last by lias.
    replace (_ + _ - _ - _) with (size ts + 1); last by lias.
    repeat f_equal => //=.
    replace (size ts + 1) with (1 + size ts); last by lias.
    simpl.
    by f_equal.
  - destruct f => //=.
    simplify_goal.
    by apply type_update_prefix.
Qed.
    
Lemma check_single_weaken_top: forall C e ts ts2 ts0,
  check_single C (CT_type ts) e = CT_top_type ts0 ->
  check_single C (CT_type (ts2 ++ ts)) e = CT_top_type ts0.
Admitted.

Lemma check_weaken: forall C es ts ts2 ts0,
  check C es (CT_type ts) = CT_type ts0 ->
  check C es (CT_type (ts2 ++ ts)) = CT_type (ts2 ++ ts0).
Proof.
  move => C es.
  move: C.
  (* It's much easier to do induction from the right side due to how check works. *)
  induction es using List.rev_ind => //=; move => C ts ts2 ts0 Htc; first by inversion Htc.
  rewrite check_rcons in Htc.
  rewrite check_rcons.
  assert (exists ts', (check C es (CT_type ts)) = CT_type ts') as [ts3 Htc2]; first by eapply check_single_notop; eauto.
  rewrite Htc2 in Htc.
  erewrite IHes; eauto.
  by apply check_single_weaken.
Qed.
  
Lemma check_weaken_top: forall C es ts ts2 ts0,
  check C es (CT_type ts) = CT_top_type ts0 ->
  check C es (CT_type (ts2 ++ ts)) = CT_top_type ts0.
Proof.
  move => C es.
  move: C.
  induction es using List.rev_ind => //=; move => C ts ts2 ts0 Htc.
  rewrite check_rcons in Htc.
  rewrite check_rcons.
  destruct (check C es (CT_type ts)) eqn:Htc2; simpl in Htc => //=.
  - by erewrite IHes; eauto.
  - erewrite check_weaken; eauto.
    by erewrite check_single_weaken_top; eauto.
  - by rewrite check_single_bot in Htc.
Qed.
    
Lemma same_lab_h_condition: forall C ts l,
  all (fun i: nat => (i < length (tc_label C)) && plop2 C i ts) l ->
  same_lab_h l (tc_label C) ts = Some ts.
Proof.
  move => C ts l.
  move: C ts.
  induction l => //=.
  move => C ts H.
  move/andP in H; destruct H as [H1 H2].
  move/andP in H1; destruct H1 as [H1 H3].
  replace (length (tc_label C) <= a) with false; last by lias.
  move/ltP in H1.
  unfold plop2 in H3.
  move/eqP in H3.
  rewrite H3.
  rewrite eq_refl.
  by apply IHl.
Qed.

Lemma same_lab_h_rec: forall x l C ts,
  same_lab_h (x :: l) (tc_label C) ts = Some ts ->
  same_lab_h l (tc_label C) ts = Some ts.
Proof.
  move => x l C ts H.
  simpl in H.
  destruct (length (tc_label C) <= x) => //=.
  destruct (List.nth_error (tc_label C) x) => //=.
  destruct (l0 == ts) eqn:Heq => //=.
  move/eqP in Heq. by subst.
Qed.

(*Lemma type_update_agree_suffix: forall C ts e l,
  ct_suffix l (to_ct_list ts) ->
  
*)

Lemma c_types_agree_suffix_single: forall l C ts ts2 e,
  c_types_agree (check_single C (CT_type ts) e) ts2 ->
  ct_suffix l (to_ct_list ts) ->
  c_types_agree (check_single C (CT_top_type l) e) ts2.
Proof with auto_rewrite_cond.
  move => l C ts ts2 e.
  move: l C ts ts2.
  Print check_single.
  induction e; move => topt C ts ts2 H Hsuffix => //=; unfold c_types_agree, check_single in H => //=...
  
  Print check_single.
Admitted.

Lemma c_types_agree_weakening: forall C es ts ts' ts2,
  c_types_agree (check C es (CT_type ts)) ts2 ->
  c_types_agree (check C es (CT_type (ts' ++ ts))) (ts' ++ ts2).
Proof.
  unfold c_types_agree.
  move => C es ts ts' ts2.
  destruct (check C es (CT_type ts)) eqn:Htc => //=; move => H.
  - erewrite check_weaken_top; eauto.
    unfold to_ct_list.
    rewrite map_cat.
    by rewrite ct_suffix_extend.
  - move/eqP in H. subst.
    erewrite check_weaken; by eauto.
Qed.
    
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
    induction Hbet; subst => //=; unfold type_update => //=...
    + unfold convert_cond...
    + unfold same_lab => //=.
      remember (ins ++ [::i]) as l.
      rewrite - Heql.
      destruct l => //=; first by destruct ins.
      remember H as H2; clear HeqH2.
      move/allP in H2.
      assert (n \in (ins ++ [::i])) as Hn; first by rewrite - Heql; rewrite mem_head.
      apply H2 in Hn.
      move/andP in Hn; destruct Hn as [H3 H4].
      unfold plop2 in H4.
      replace (length (tc_label C) <= n) with false; last by lias.
      move/eqP in H4.
      rewrite H4.
      apply same_lab_h_condition in H.
      replace (ins ++ [::i])%list with (ins ++ [::i]) in H; last by lias.
      rewrite - Heql in H.
      apply same_lab_h_rec in H.
      rewrite H.
      rewrite ct_suffix_suffix...
    + destruct tf as [t1 t2] => //=...
    + destruct (List.nth_error (tc_global C) i) => //=...
    + rewrite List.fold_left_app => //=.
      unfold c_types_agree in IHHbet1.
      destruct (List.fold_left _ es _) eqn:Htc => //=.
      * by eapply c_types_agree_suffix_single; eauto.
      * move/eqP in IHHbet1. by subst.
    + by apply c_types_agree_weakening.
Qed.
      
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

