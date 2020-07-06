Require Import common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Program.Equality.

Require Import operations typing type_checker datatypes_properties typing opsem properties.

Definition t_be_value (bes: seq basic_instruction) : Prop :=
  const_list (to_e_list bes).

Print tc_global.

Print value.

Print value_type.

Print instance.

Ltac b_to_a_revert :=
  repeat lazymatch goal with
         | H:  to_e_list ?bes = _ |- _ =>
           apply b_e_elim in H; destruct H
         end.

Lemma upd_label_overwrite: forall C l1 l2,
    upd_label (upd_label C l1) l2 = upd_label C l2.
Proof.
  by [].
Qed.

(* Maybe there are better/standard tactics for dealing with these, but I didn't find
     anything helpful *)
Lemma concat_cancel_last: forall {X:Type} (l1 l2: seq X) (e1 e2:X),
    l1 ++ [::e1] = l2 ++ [::e2] ->
    l1 = l2 /\ e1 = e2.
Proof.
  move => X l1 l2 e1 e2 H.
  assert (rev (l1 ++ [::e1]) = rev (l2 ++ [::e2])); first by rewrite H.
  repeat rewrite rev_cat in H0. inversion H0.
  rewrite - (revK l1). rewrite H3. split => //. by apply revK.
Qed.

Local Lemma concat_cancel_last_n: forall (l1 l2 l3 l4: seq value_type),
    l1 ++ l2 = l3 ++ l4 ->
    size l2 = size l4 ->
    (l1 == l3) && (l2 == l4).
Proof.
  move => l1 l2 l3 l4 HCat HSize.
  
  rewrite -eqseq_cat; first by apply/eqP.
  assert (size (l1 ++ l2) = size (l3 ++ l4)); first by rewrite HCat.
  repeat rewrite size_cat in H. unfold vs_to_vts in H.
  rewrite HSize in H. by lias.
Qed.  

Local Lemma extract_list1 : forall {X:Type} (es: seq X) (e1 e2:X),
    es ++ [::e1] = [::e2] ->
    es = [::] /\ e1 = e2.
Proof.
  move => X es e1 e2 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Local Lemma extract_list2 : forall {X:Type} (es: seq X) (e1 e2 e3:X),
    es ++ [::e1] = [::e2; e3] ->
    es = [::e2] /\ e1 = e3.
Proof.
  move => X es e1 e2 e3 H.
  apply concat_cancel_last.
  by apply H.
Qed.    

Local Lemma extract_list3 : forall {X:Type} (es: seq X) (e1 e2 e3 e4:X),
    es ++ [::e1] = [::e2; e3; e4] ->
    es = [::e2; e3] /\ e1 = e4.
Proof.
  move => X es e1 e2 e3 e4 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Local Lemma extract_list4 : forall {X:Type} (es: seq X) (e1 e2 e3 e4 e5:X),
    es ++ [::e1] = [::e2; e3; e4; e5] ->
    es = [::e2; e3; e4] /\ e1 = e5.
Proof.
  move => X es e1 e2 e3 e4 e5 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Ltac extract_listn :=
  repeat lazymatch goal with
  | H: (?es ++ [::?e])%list = [::_] |- _ =>
    apply extract_list1 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _] |- _ =>
    apply extract_list2 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _; _] |- _ =>
    apply extract_list3 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _; _; _] |- _ =>
    apply extract_list4 in H; destruct H; subst
  end.

Ltac extract_listn' :=
  repeat lazymatch goal with
  | H: (?es ++ [::?e]) = [::_] |- _ =>
    apply extract_list1 in H; destruct H; subst
  | H: (?es ++ [::?e]) = [::_; _] |- _ =>
    apply extract_list2 in H; destruct H; subst
  | H: (?es ++ [::?e]) = [::_; _; _] |- _ =>
    apply extract_list3 in H; destruct H; subst
  | H: (?es ++ [::?e]) = [::_; _; _; _] |- _ =>
    apply extract_list4 in H; destruct H; subst
end.

Lemma list_nth_error_in: forall {l:list nat} i c,
    List.nth_error l i = Some c ->
    c \in l.
Proof.
  move => l i c HLookup.
  generalize dependent i.
  induction l => //=; move => i HLookup.
  - by destruct i => //=.
  - destruct i => //=.
    + simpl in HLookup. inversion HLookup => //=.
      by apply mem_head.
    + simpl in HLookup.
      assert (c \in l).
      eapply IHl => //=.
      apply HLookup.
      rewrite in_cons.
      apply/orP. by right.
Qed.

Lemma list_nth_prefix: forall {X:Type} (l1 l2: seq X) x,
    List.nth_error (l1 ++ [::x] ++ l2) (length l1) = Some x.
Proof.
  move => X. induction l1 => //=.
Qed.

(* 
  This is actually very non-trivial to prove, unlike I first thought.
  The main difficulty arises due to the two rules bet_composition and bet_weakening,
    which will apply for EVERY hypothesis of be_typing when doing inversion/induction.
  Moreover, bet_weakening has a reversed inductive structure, so the proof in fact
    required induction (where one would hardly expect an induction here!).
*)
Lemma empty_typing: forall C t1s t2s,
    be_typing C [::] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by destruct es => //=.
  - f_equal.
    by apply IHHType => //=.
Qed.

(* Some quality of life lemmas *)
Lemma bet_weakening_empty_1: forall C es ts t2s,
    be_typing C es (Tf [::] t2s) ->
    be_typing C es (Tf ts (ts ++ t2s)).
Proof.
  move => C es ts t2s HType.
  assert (be_typing C es (Tf (ts ++ [::]) (ts ++ t2s))); first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma et_weakening_empty_1: forall s C es ts t2s,
    e_typing s C es (Tf [::] t2s) ->
    e_typing s C es (Tf ts (ts ++ t2s)).
Proof.
  move => s C es ts t2s HType.
  assert (e_typing s C es (Tf (ts ++ [::]) (ts ++ t2s))); first by apply ety_weakening.
  by rewrite cats0 in H.
Qed.

Lemma bet_weakening_empty_2: forall C es ts t1s,
    be_typing C es (Tf t1s [::]) ->
    be_typing C es (Tf (ts ++ t1s) ts).
Proof.
  move => C es ts t1s HType.
  assert (be_typing C es (Tf (ts ++ t1s) (ts ++ [::]))); first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma bet_weakening_empty_both: forall C es ts,
    be_typing C es (Tf [::] [::]) ->
    be_typing C es (Tf ts ts).
Proof.
  move => C es ts HType.
  assert (be_typing C es (Tf (ts ++ [::]) (ts ++ [::]))); first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

(*
  These proofs are largely similar.
  A sensible thing to do is to make tactics for all of them.
  However, some of the proofs depend on the previous ones...
*)

Lemma EConst_typing: forall C econst t1s t2s,
    be_typing C [::EConst econst] (Tf t1s t2s) ->
    t2s = t1s ++ [::typeof econst].
Proof.
  move => C econst t1s t2s HType.
  (* The name generated by dependent induction is a bit weird. *)
  dependent induction HType; subst => //=.
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by apply IHHType2 => //=.
  - rewrite - catA. f_equal.
    + move => _ _ H. by subst.
    + by apply IHHType => //=.
Qed.

Lemma EConst2_typing: forall C econst1 econst2 t1s t2s,
    be_typing C [::EConst econst1; EConst econst2] (Tf t1s t2s) ->
    t2s = t1s ++ [::typeof econst1; typeof econst2].
Proof.
  move => C econst1 econst2 t1s t2s HType.
  dependent induction HType; subst => //=.
  - apply extract_list2 in x; destruct x; subst.
    apply EConst_typing in HType1; subst.
    apply EConst_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + move => _ _ H. by subst.
    + by apply IHHType => //=.
Qed.

Lemma EConst3_typing: forall C econst1 econst2 econst3 t1s t2s,
    be_typing C [::EConst econst1; EConst econst2; EConst econst3] (Tf t1s t2s) ->
    t2s = t1s ++ [::typeof econst1; typeof econst2; typeof econst3].
Proof.
  move => C econst1 econst2 econst3 t1s t2s HType.
  dependent induction HType; subst => //=.
  - apply extract_list3 in x; destruct x; subst.
    apply EConst2_typing in HType1; subst.
    apply EConst_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + move => _ _ H. by subst.
    + by apply IHHType => //=.
Qed.

Lemma Const_list_typing_empty: forall C vs,
    be_typing C (to_b_list (v_to_e_list vs)) (Tf [::] (vs_to_vts vs)).
Proof.
  move => C vs.
  remember (rev vs) as vs'.
  assert (vs = rev vs'). rewrite Heqvs'. symmetry. by apply revK.
  rewrite H.

  generalize dependent vs.
  
  induction vs' => //=; move => vs HRev1 HRev2.
  - by apply bet_empty.
  - rewrite rev_cons. rewrite -cats1.
    rewrite -v_to_e_cat.
    rewrite to_b_list_concat.
    eapply bet_composition.
    + eapply IHvs' => //.
      symmetry. by apply revK.
    + simpl.
      rewrite vs_to_vts_cat.      
      apply bet_weakening_empty_1.
      by apply bet_const.
Qed.

Lemma Unop_i_typing: forall C t op t1s t2s,
    be_typing C [::Unop_i t op] (Tf t1s t2s) ->
    t1s = t2s /\ exists ts, t1s = ts ++ [::t].
Proof.
  move => C t op t1s t2s HType.
  dependent induction HType; subst => //=.
  - split => //=. by exists [::].
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    split => //=.
    destruct H0 as [ts' H].
    exists (ts ++ ts').
    rewrite - catA.
    by rewrite H.
Qed.

Lemma Binop_i_typing: forall C t op t1s t2s,
    be_typing C [::Binop_i t op] (Tf t1s t2s) ->
    t1s = t2s ++ [::t] /\ exists ts, t2s = ts ++ [::t].
Proof.
  move => C t op t1s t2s HType.
  dependent induction HType; subst => //=.
  - split => //=. by exists [::].
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    split => //=.
    + destruct H0 as [ts' H].
      by rewrite - catA.
    + destruct H0 as [ts' H].
      exists (ts ++ ts').
      subst.
      by rewrite - catA.  
Qed.

Lemma Binop_f_typing: forall C t op t1s t2s,
    be_typing C [::Binop_f t op] (Tf t1s t2s) ->
    t1s = t2s ++ [::t] /\ exists ts, t2s = ts ++ [::t].
Proof.
  move => C t op t1s t2s HType.
  dependent induction HType; subst => //=.
  - split => //=. by exists [::].
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    split => //=.
    + destruct H0 as [ts' H].
      by rewrite - catA.
    + destruct H0 as [ts' H].
      exists (ts ++ ts').
      subst.
      by rewrite - catA.  
Qed.

Lemma Unop_f_typing: forall C t op t1s t2s,
    be_typing C [::Unop_f t op] (Tf t1s t2s) ->
    t1s = t2s /\ exists ts, t1s = ts ++ [::t].
Proof.
  move => C t op t1s t2s HType.
  dependent induction HType; subst => //=.
  - split => //=. by exists [::].
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    split => //=.
    destruct H0 as [ts' H].
    exists (ts ++ ts').
    rewrite - catA.
    by rewrite H.
Qed.  

Lemma Testop_typing: forall C t op t1s t2s,
    be_typing C [::Testop t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t] /\ t2s = ts ++ [::T_i32].
Proof.
  move => C t op t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::]. 
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Relop_i_typing: forall C t op t1s t2s,
    be_typing C [::Relop_i t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t; t] /\ t2s = ts ++ [::T_i32].
Proof.
  move => C t op t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::]. 
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Relop_f_typing: forall C t op t1s t2s,
    be_typing C [::Relop_f t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t; t] /\ t2s = ts ++ [::T_i32].
Proof.
  move => C t op t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::]. 
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Cvtop_typing: forall C t1 t2 op sx t1s t2s,
    be_typing C [::Cvtop t2 op t1 sx] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t1] /\ t2s = ts ++ [::t2].
Proof.
  move => C t1 t2 op sx t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::]. 
  - by exists [::]. 
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Nop_typing: forall C t1s t2s,
    be_typing C [::Nop] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by apply IHHType2 => //=.
  - f_equal. by apply IHHType => //=.
Qed.

Lemma Drop_typing: forall C t1s t2s,
    be_typing C [::Drop] (Tf t1s t2s) ->
    exists t, t1s = t2s ++ [::t].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by eauto.
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    exists x. repeat rewrite -catA. by f_equal.
Qed.

Lemma Select_typing: forall C t1s t2s,
    be_typing C [::Select] (Tf t1s t2s) ->
    exists ts t, t1s = ts ++ [::t; t; T_i32] /\ t2s = ts ++ [::t].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::], t.
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    edestruct H => //=; destruct H as [x1 [H1 H2]]; subst.
    exists (ts ++ x), x1. split => //=; by repeat rewrite -catA.
Qed.

Lemma If_typing: forall C t1s t2s e1s e2s ts ts',
    be_typing C [::If (Tf t1s t2s) e1s e2s] (Tf ts ts') ->
    exists ts0, ts = ts0 ++ t1s ++ [::T_i32] /\ ts' = ts0 ++ t2s /\
                be_typing (upd_label C ([:: t2s] ++ tc_label C)) e1s (Tf t1s t2s) /\
                be_typing (upd_label C ([:: t2s] ++ tc_label C)) e2s (Tf t1s t2s).
Proof.
  move => C t1s t2s e1s e2s ts ts' HType.
  dependent induction HType; subst => //=.
  - by exists [::].
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1. subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    destruct H as [H1 [H2 [H3 H4]]]. subst.
    exists (ts0 ++ x).
    repeat rewrite -catA.
    repeat split => //=.
Qed.

Lemma Br_if_typing: forall C ts1 ts2 i,
    be_typing C [::Br_if i] (Tf ts1 ts2) ->
    exists ts ts', ts2 = ts ++ ts' /\ ts1 = ts2 ++ [::T_i32] /\ i < length (tc_label C) /\ plop2 C i ts'.
Proof.
  move => C ts1 ts2 i HType.
  dependent induction HType; subst => //=.
  - unfold plop2 in H0.
    by exists [::], ts2 => //=.
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - rewrite -catA. f_equal => //=.
    edestruct IHHType => //=.
    destruct H as [ts' [H1 [H2 [H3 H4]]]].
    exists (ts ++ x), ts'. subst.
    split.
    + repeat rewrite -catA. by f_equal => //=.
    + split => //=.
Qed.

Lemma Br_table_typing: forall C ts1 ts2 ids i0,
    be_typing C [::Br_table ids i0] (Tf ts1 ts2) ->
    exists ts1' ts, ts1 = ts1' ++ ts ++ [::T_i32] /\
                         all (fun i => (i < length (tc_label C)) && (plop2 C i ts)) (ids ++ [::i0]).
Proof.
  move => C ts1 ts2 ids i0 HType.
  dependent induction HType; subst => //=.
  - by exists t1s, ts => //=.
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [ts' [H1 H2]].
    exists (ts ++ x), ts'. subst.
    split => //=.
    + repeat rewrite -catA. by f_equal => //=.
Qed.

Lemma Tee_local_typing: forall C i ts1 ts2,
    be_typing C [::Tee_local i] (Tf ts1 ts2) ->
    exists ts t, ts1 = ts2 /\ ts1 = ts ++ [::t] /\ i < length (tc_local C) /\
                 List.nth_error (tc_local C) i = Some t.
Proof.
  move => C i ts1 ts2 HType.
  dependent induction HType; subst => //=.
  - by exists [::], t.
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [t [H1 [H2 [H3 H4]]]]. subst.
    exists (ts ++ x), t. subst.
    repeat (try split => //=).
    by rewrite -catA.
Qed.
      
Ltac basic_inversion :=
   repeat lazymatch goal with
         | H: True |- _ =>
           clear H
         | H: es_is_basic (_ ++ _) |- _ =>
           apply basic_concat in H; destruct H
         | H: es_is_basic [::] |- _ =>
           clear H
         | H: es_is_basic [::_] |- _ =>
           let H1 := fresh "H1" in
           let H2 := fresh "H2" in
           try by (unfold es_is_basic in H; destruct H as [H1 H2]; inversion H1)
         | H: e_is_basic _ |- _ =>
           inversion H; try by []
         end.

(* A convenient lemma to invert e_typing back to be_typing. *)
Lemma et_to_bet: forall s C es ts,
    es_is_basic es ->
    e_typing s C es ts ->
    be_typing C (to_b_list es) ts.
Proof.
  move => s C es ts HBasic HType. subst.
  dependent induction HType; subst => //=; basic_inversion.
  + replace (to_b_list (to_e_list bes)) with bes => //.
    by apply b_e_elim.
  + rewrite to_b_list_concat.
    eapply bet_composition.
    apply IHHType1 => //.
    apply IHHType2 => //.
  + apply bet_weakening. by apply IHHType.
Qed.

(* A reformulation of ety_a that is easier to be used. *)
Lemma ety_a': forall s C es ts,
    es_is_basic es ->
    be_typing C (to_b_list es) ts ->
    e_typing s C es ts.
Proof.
  move => s C es ts HBasic HType.
  replace es with (to_e_list (to_b_list es)).
  - by apply ety_a.
  - symmetry. by apply e_b_elim.
Qed.

Section composition_typing_proofs.

Hint Constructors be_typing.

Ltac auto_prove_bet:=
  repeat lazymatch goal with
  | H: _ |- exists ts t1s t2s t3s, ?tn = ts ++ t1s /\ ?tm = ts ++ t2s /\
                                   be_typing _ [::] (Tf _ _) /\ _ =>
    try exists [::], tn, tm, tn; try eauto
  | H: _ |- _ /\ _ =>
    split => //=; try eauto
  | H: _ |- be_typing _ [::] (Tf ?es ?es) =>
    apply bet_weakening_empty_both; try by []
  end.

Lemma composition_typing_single: forall C es1 e t1s t2s,
    be_typing C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             be_typing C es1 (Tf t1s' t3s) /\
                             be_typing C [::e] (Tf t3s t2s').
Proof with auto_prove_bet.
  move => C es1 e t1s t2s HType.
  dependent induction HType; subst => //=; try (symmetry in x; extract_listn')...
  + by apply bet_block.
  + by destruct es1 => //=.
  + apply concat_cancel_last in x. destruct x. subst.
    by exists [::], t1s, t2s, t2s0.
  + edestruct IHHType; eauto.
    destruct H as [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]. subst.
    exists (ts ++ x), t1s', t2s', t3s'.
    repeat split => //=; by rewrite -catA.
Qed.

Lemma composition_typing: forall C es1 es2 t1s t2s,
    be_typing C (es1 ++ es2) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             be_typing C es1 (Tf t1s' t3s) /\
                             be_typing C es2 (Tf t3s t2s').
Proof.
  move => C es1 es2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1.
  clear Heqes2'. subst.
  induction es2' => //=; move => es1 t1s t2s HType.
  - unfold rev in HType; simpl in HType. subst.
    rewrite cats0 in HType.
    exists [::], t1s, t2s, t2s.
    repeat split => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite rev_cons in HType.
    rewrite -cats1 in HType. subst.
    rewrite catA in HType.
    apply composition_typing_single in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]]. subst.
    apply IHes2' in H3.
    destruct H3 as [ts2 [t1s2 [t2s2 [t3s2 [H5 [H6 [H7 H8]]]]]]]. subst.
    exists ts', (ts2 ++ t1s2), t2s', (ts2 ++ t3s2).
    repeat split => //.
    + by apply bet_weakening.
    + rewrite rev_cons. rewrite -cats1.
      by eapply bet_composition; eauto.
Qed.

Lemma e_composition_typing_single: forall s C es1 e t1s t2s,
    e_typing s C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             e_typing s C es1 (Tf t1s' t3s) /\
                             e_typing s C [::e] (Tf t3s t2s').
Proof.
  move => s C es1 es2 t1s t2s HType.
  dependent induction HType; subst => //=.
  - (* basic *)
    apply b_e_elim in x. destruct x. subst.
    rewrite to_b_list_concat in H.
    apply composition_typing in H.
    apply basic_concat in H1. destruct H1.
    destruct H as [ts' [t1s' [t2s' [t3s' [H2 [H3 [H4 H5]]]]]]]. subst.
    exists ts', t1s', t2s', t3s'.
    repeat split => //=; by apply ety_a' => //=.
  - (* composition *)
    apply concat_cancel_last in x. destruct x. subst.
    by exists [::], t1s, t2s, t2s0.
  - (* weakening *)
    edestruct IHHType; eauto.
    destruct H as [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]. subst.
    exists (ts ++ x), t1s', t2s', t3s'.
    repeat split => //; by rewrite catA.
  - (* Trap *)
    symmetry in x. apply extract_list1 in x. destruct x. subst.
    exists [::], t1s, t2s, t1s.
    repeat split => //=.
    + apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
    + by apply ety_trap.
  - (* Local *)
    symmetry in x. apply extract_list1 in x. destruct x. subst.
    exists [::], [::], t2s, [::]. repeat split => //=.
    + by apply ety_a' => //.
    + by apply ety_local.
  - (* Invoke *)    
    symmetry in x. apply extract_list1 in x. destruct x. subst.
    exists [::], t1s, t2s, t1s. repeat split => //=.
    + apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
    + by apply ety_invoke.
  - (* Label *)
    symmetry in x. apply extract_list1 in x. destruct x. subst.
    exists [::], [::], t2s, [::]. repeat split => //=.
    + by apply ety_a' => //.
    + by eapply ety_label; eauto.
Qed.
      
Lemma e_composition_typing: forall s C es1 es2 t1s t2s,
    e_typing s C (es1 ++ es2) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             e_typing s C es1 (Tf t1s' t3s) /\
                             e_typing s C es2 (Tf t3s t2s').
Proof.
  move => s C es1 es2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1.
  clear Heqes2'. subst.
  induction es2' => //=; move => es1 t1s t2s HType.
  - unfold rev in HType; simpl in HType. subst.
    rewrite cats0 in HType.
    exists [::], t1s, t2s, t2s.
    repeat split => //=.
    apply ety_a' => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite rev_cons in HType.
    rewrite -cats1 in HType. subst.
    rewrite catA in HType.
    apply e_composition_typing_single in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]]. subst.
    apply IHes2' in H3.
    destruct H3 as [ts2 [t1s2 [t2s2 [t3s2 [H5 [H6 [H7 H8]]]]]]]. subst.
    exists ts', (ts2 ++ t1s2), t2s', (ts2 ++ t3s2).
    repeat split => //.
    + by apply ety_weakening.
    + rewrite rev_cons. rewrite -cats1.
      eapply ety_composition; eauto.
      by apply ety_weakening.
Qed.

Lemma bet_composition': forall C es1 es2 t1s t2s t3s,
    be_typing C es1 (Tf t1s t2s) ->
    be_typing C es2 (Tf t2s t3s) ->
    be_typing C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => C es1 es2 t1s t2s t3s HType1 HType2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1. generalize dependent es2.
  generalize dependent t1s. generalize dependent t2s.
  generalize dependent t3s.
  induction es2' => //=.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1. destruct es2 => //=. rewrite cats0.
    apply empty_typing in HType2. by subst.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1.
    rewrite rev_cons in H2. rewrite -cats1 in H2.
    rewrite H2 in HType2.
    apply composition_typing in HType2.
    destruct HType2 as [ts [t1s' [t2s' [t3s' [H3 [H4 [H5 H6]]]]]]]. subst.
    rewrite catA. eapply bet_composition => //=.
    instantiate (1 := (ts ++ t3s')).
    eapply IHes2' => //.
    instantiate (1 := (ts ++ t1s')); first by apply bet_weakening.
    symmetry. by apply revK.
    by apply HType1.
    by apply bet_weakening.  
Qed.    
    
Lemma et_composition': forall s C es1 es2 t1s t2s t3s,
    e_typing s C es1 (Tf t1s t2s) ->
    e_typing s C es2 (Tf t2s t3s) ->
    e_typing s C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => s C es1 es2 t1s t2s t3s HType1 HType2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1. generalize dependent es2.
  generalize dependent t1s. generalize dependent t2s.
  generalize dependent t3s.
  induction es2' => //=.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1. destruct es2 => //=. rewrite cats0.
    apply et_to_bet in HType2. apply empty_typing in HType2. by subst.
  - by [].
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1.
    rewrite rev_cons in H2. rewrite -cats1 in H2.
    rewrite H2 in HType2.
    apply e_composition_typing in HType2.
    destruct HType2 as [ts [t1s' [t2s' [t3s' [H3 [H4 [H5 H6]]]]]]]. subst.
    rewrite catA. eapply ety_composition => //=.
    instantiate (1 := (ts ++ t3s')).
    eapply IHes2' => //.
    instantiate (1 := (ts ++ t1s')); first by apply ety_weakening.
    symmetry. by apply revK.
    by apply HType1.
    by apply ety_weakening.
Qed.

End composition_typing_proofs.

Lemma Const_list_typing: forall C vs t1s t2s,
    be_typing C (to_b_list (v_to_e_list vs)) (Tf t1s t2s) ->
    t2s = t1s ++ (map typeof vs).
Proof.
  move => C vs.
  remember (rev vs) as vs'.
  generalize dependent vs.
  induction vs'.
  - move => vs H t1s t2s HType. destruct vs => //=.
    + simpl in HType.
      apply empty_typing in HType. subst. by rewrite cats0.
    + rewrite rev_cons in H. rewrite -cats1 in H.
      by destruct (rev vs) => //=.
  - move => vs H t1s t2s HType.
    assert (vs = rev (a::vs')).
    { rewrite H. symmetry. by apply revK. }
    rewrite rev_cons in H0. rewrite -cats1 in H0.
    rewrite H0 in HType.
    rewrite -v_to_e_cat in HType.
    rewrite to_b_list_concat in HType.
    apply composition_typing in HType.
    destruct HType as [ts [ts1' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]].
    apply IHvs' in H3; last by (symmetry; apply revK). subst.
    simpl in H4.
    apply EConst_typing in H4. subst. 
    repeat rewrite -catA. repeat f_equal.
    by rewrite map_cat.
Qed.
(*
  Unlike the above proofs which have a linear dependent structure therefore hard
    to factorize into a tactic, the following proofs are independent of each other
    and should therefore be easily refactorable.
*)

Ltac invert_be_typing:=
  repeat lazymatch goal with
  | H: (?es ++ [::?e])%list = [::_] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _; _] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _; _; _] |- _ =>
    extract_listn
  | H: be_typing _ [::] _ |- _ =>
    apply empty_typing in H; subst
  | H: be_typing _ [:: EConst _] _ |- _ =>
    apply EConst_typing in H; subst
  | H: be_typing _ [:: EConst _; EConst _] _ |- _ =>
    apply EConst2_typing in H; subst
  | H: be_typing _ [:: EConst _; EConst _; EConst _] _ |- _ =>
    apply EConst3_typing in H; subst
  | H: be_typing _ [::Unop_i _ _] _ |- _ =>
    apply Unop_i_typing in H; destruct H; subst
  | H: be_typing _ [::Unop_f _ _] _ |- _ =>
    apply Unop_f_typing in H; destruct H; subst
  | H: be_typing _ [::Binop_i _ _] _ |- _ =>
    apply Binop_i_typing in H; destruct H; subst
  | H: be_typing _ [::Binop_f _ _] _ |- _ =>
    apply Binop_f_typing in H; destruct H; subst
  | H: be_typing _ [::Testop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Testop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::Relop_i _ _] _ |- _ =>
    apply Relop_i_typing in H; destruct H; subst
  | H: be_typing _ [::Relop_f _ _] _ |- _ =>
    apply Relop_f_typing in H; destruct H; subst
  | H: be_typing _ [::Cvtop _ _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Cvtop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::Drop] _ |- _ =>
    apply Drop_typing in H; destruct H; subst
  | H: be_typing _ [::Select] _ |- _ =>
    let ts := fresh "ts" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Select_typing in H; destruct H as [ts [t [H1 H2]]]; subst
  | H: be_typing _ [::If _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply If_typing in H; destruct H as [ts [H1 [H2 [H3 H4]]]]; subst
  | H: be_typing _ [::Br_if _] _ |- _ =>
    let ts := fresh "ts" in
    let ts' := fresh "ts'" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Br_if_typing in H; destruct H as [ts [ts' [H1 [H2 [H3 H4]]]]]; subst
  | H: be_typing _ [::Br_table _ _] _ |- _ =>
    let ts := fresh "ts" in
    let ts' := fresh "ts'" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Br_table_typing in H; destruct H as [ts [ts' [H1 H2]]]; subst
  | H: be_typing _ [::Tee_local _] _ |- _ =>
    let ts := fresh "ts" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Tee_local_typing in H; destruct H as [ts [t [H1 [H2 [H3 H4]]]]]; subst
  | H: _ ++ [::_] = _ ++ [::_] |- _ =>
    apply concat_cancel_last in H; destruct H; subst
  end.

(* Both 32bit and 64bit *)
Lemma t_Unop_i_preserve: forall C v iop be tf,
    be_typing C [:: EConst v; Unop_i (typeof v) iop] tf ->
    reduce_simple (to_e_list [::EConst v; Unop_i (typeof v) iop]) (to_e_list [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v iop be tf HType HReduce.
  inversion HReduce; b_to_a_revert; subst.
  (* This is actually very troublesome: we have to use induction just because of
       bet_weakening every time...... *)
  - (* ConstInt32 *)
    dependent induction HType; subst.
    + (* Composition -- the right one *)
    invert_be_typing.
    (* Due to the existence of bet_composition and bet_weakening, a direct
         inversion of those be_typing rules won't work. 
       As a result we have to prove them as separate lemmas.
       Is there a way to avoid this? *)
    apply bet_weakening_empty_1.
    replace (typeof (ConstInt32 c)) with (typeof (ConstInt32 (app_unop_i iop c))).
    by apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
      by apply IHHType. 
  - (* ConstInt64 *)
    dependent induction HType; subst.
    + (* Composition -- the right one *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    replace (typeof (ConstInt64 c)) with (typeof (ConstInt64 (app_unop_i iop c)));
      first by apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
      by apply IHHType.
Qed.

(* Both 32bit and 64bit *)
Lemma t_Unop_f_preserve: forall C v fop be tf,
    be_typing C [:: EConst v; Unop_f (typeof v) fop] tf ->
    reduce_simple (to_e_list [::EConst v; Unop_f (typeof v) fop]) (to_e_list [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v fop be tf HType HReduce.
  inversion HReduce; b_to_a_revert; subst.
  - (* ConstFloat32 *)
    dependent induction HType; subst.
    + (* Composition -- the right one *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    replace (typeof (ConstFloat32 c)) with (typeof (ConstFloat32 (app_unop_f fop c))).
    by apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
      by apply IHHType. 
  - (* ConstFloat64 *)
    dependent induction HType; subst.
    + (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    replace (typeof (ConstFloat64 c)) with (typeof (ConstFloat64 (app_unop_f fop c))).
    by apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
      by apply IHHType. 
Qed.

Lemma t_Binop_i_preserve_success: forall C v1 v2 iop be tf,
    be_typing C [:: EConst v1; EConst v2; Binop_i (typeof v1) iop] tf ->
    reduce_simple (to_e_list[::EConst v1; EConst v2; Binop_i (typeof v2) iop]) (to_e_list [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 iop be tf HType HReduce.
  inversion HReduce; b_to_a_revert; subst.
  - (* ConstInt32 *)
    dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H.
      replace t3s with (t1s ++ [::T_i32]).
      -- apply bet_weakening_empty_1.
         by apply bet_const.
      -- (* replace *)
         replace [::T_i32; T_i32] with ([::T_i32] ++ [::T_i32]) in H => //=.
         rewrite catA in H.
         by apply concat_cancel_last in H; destruct H.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
  - (* ConstInt64 *)
    dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H.
      replace t3s with (t1s ++ [::T_i64]).
      -- apply bet_weakening_empty_1.
         by apply bet_const.
      -- (* replace *)
         replace [::T_i64; T_i64] with ([::T_i64] ++ [::T_i64]) in H => //=.
         rewrite catA in H.
         by apply concat_cancel_last in H; destruct H.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
Qed.


Lemma t_Binop_f_preserve_success: forall C v1 v2 fop be tf,
    be_typing C [:: EConst v1; EConst v2; Binop_f (typeof v1) fop] tf ->
    reduce_simple (to_e_list[::EConst v1; EConst v2; Binop_f (typeof v2) fop]) (to_e_list [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 iop be tf HType HReduce.
  inversion HReduce; b_to_a_revert; subst.
  - (* ConstInt32 *)
    dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H.
      replace t3s with (t1s ++ [::T_f32]).
      -- apply bet_weakening_empty_1.
         by apply bet_const.
      -- (* replace *)
         replace [::T_f32; T_f32] with ([::T_f32] ++ [::T_f32]) in H => //=.
         rewrite catA in H.
         by apply concat_cancel_last in H; destruct H.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
  - (* ConstInt64 *)
    dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H.
      replace t3s with (t1s ++ [::T_f64]).
      -- apply bet_weakening_empty_1.
         by apply bet_const.
      -- (* replace *)
         replace [::T_f64; T_f64] with ([::T_f64] ++ [::T_f64]) in H => //=.
         rewrite catA in H.
         by apply concat_cancel_last in H; destruct H.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
Qed.

(* It seems very hard to refactor the i32 and i64 cases into one because of
     the polymorphism of app_testop_i. *)
Lemma t_Testop_i32_preserve: forall C c testop tf,
    be_typing C [::EConst (ConstInt32 c); Testop T_i32 testop] tf ->
    be_typing C [::EConst (ConstInt32 (wasm_bool (app_testop_i testop c)))] tf.
Proof.
  move => C c testop tf HType.
  dependent induction HType; subst.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1. simpl.
    apply bet_const.
  - (* Weakening *)
    apply bet_weakening.
    by apply IHHType.
Qed.

Lemma t_Testop_i64_preserve: forall C c testop tf,
    be_typing C [::EConst (ConstInt64 c); Testop T_i64 testop] tf ->
    be_typing C [::EConst (ConstInt32 (wasm_bool (app_testop_i testop c)))] tf.
Proof.
  move => C c testop tf HType.
  dependent induction HType; subst.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1. simpl.
    by apply bet_const.
  - (* Weakening *)
    apply bet_weakening.
    by apply IHHType.
Qed.


Lemma t_Relop_i_preserve: forall C v1 v2 be iop tf,
    be_typing C [::EConst v1; EConst v2; Relop_i (typeof v1) iop] tf ->
    reduce_simple [:: Basic (EConst v1); Basic (EConst v2); Basic (Relop_i (typeof v1) iop)] [::Basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 be iop tf HType HReduce.
  inversion HReduce; subst.
  (* i32 *)
  - dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H. destruct H. subst.
      replace [:: T_i32; T_i32] with ([::T_i32] ++ [::T_i32]) in H => //=.
      repeat rewrite catA in H.
      repeat (apply concat_cancel_last in H; destruct H; subst).
      apply bet_weakening_empty_1.
      apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
      by apply IHHType.
  (* i64 *)
  - dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H. destruct H. subst.
      replace [:: T_i64; T_i64] with ([::T_i64] ++ [::T_i64]) in H => //=.
      repeat rewrite catA in H.
      repeat (apply concat_cancel_last in H; destruct H; subst).
      apply bet_weakening_empty_1.
      apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
        by apply IHHType.
Qed.
        
Lemma t_Relop_f_preserve: forall C v1 v2 be fop tf,
    be_typing C [::EConst v1; EConst v2; Relop_f (typeof v1) fop] tf ->
    reduce_simple [:: Basic (EConst v1); Basic (EConst v2); Basic (Relop_f (typeof v1) fop)] [::Basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 be fop tf HType HReduce.
  inversion HReduce; subst.
  (* f32 *)
  - dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H. destruct H. subst.
      replace [:: T_f32; T_f32] with ([::T_f32] ++ [::T_f32]) in H => //=.
      repeat rewrite catA in H.
      repeat (apply concat_cancel_last in H; destruct H; subst).
      apply bet_weakening_empty_1.
      apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
      by apply IHHType.
  (* f64 *)
  - dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H. destruct H. subst.
      replace [:: T_f64; T_f64] with ([::T_f64] ++ [::T_f64]) in H => //=.
      repeat rewrite catA in H.
      repeat (apply concat_cancel_last in H; destruct H; subst).
      apply bet_weakening_empty_1.
      apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
        by apply IHHType.
Qed.

(* deserialise is yet defined -- I think it's counted as an host operation.
   see Line 70 in operations.v. *)
Axiom typeof_deserialise: forall v t,
    typeof (wasm_deserialise v t) = t.

Axiom host_apply_typing: forall s vs1 vs2 ts f s',
    host_apply s (Tf (vs_to_vts vs1) ts) f vs1 = Some (s', vs2) ->
    map typeof vs2 = ts.

(* While the above two are reasonable assumptions, this one is definitely too strong.
   This is stated in the current form for the proof to the case of host functions.
   Since there is going to be a huge update on host, I don't think it's currently
     worth it to put a lot of time into finding a sensible hypothesis here. *)
Axiom host_apply_store: forall s vs1 vs2 ts1 ts2 f s',
    host_apply s (Tf ts1 ts2) f vs1 = Some (s', vs2) ->
    s = s'.  

Lemma be_typing_const_deserialise: forall C v t,
    be_typing C [:: EConst (wasm_deserialise (bits v) t)] (Tf [::] [:: t]).
Proof.
  move => C v t.
  assert (be_typing C [:: EConst (wasm_deserialise (bits v) t)] (Tf [::] [:: typeof (wasm_deserialise (bits v) t)])); first by apply bet_const.
  by rewrite typeof_deserialise in H.
Qed.

Lemma t_Convert_preserve: forall C v t1 t2 sx be tf,
    be_typing C [::EConst v; Cvtop t2 Convert t1 sx] tf ->
    reduce_simple [::Basic (EConst v); Basic (Cvtop t2 Convert t1 sx)] [::Basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v t1 t2 sx be tf HType HReduce.
  inversion HReduce; subst.
  dependent induction HType; subst.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    unfold cvt in H5.
    destruct t2; unfold option_map in H5.
    (* TODO: maybe refactor this destruct *)
    + destruct (cvt_i32 sx v) eqn:HDestruct => //=. inversion H5. by apply bet_const.
    + destruct (cvt_i64 sx v) eqn:HDestruct => //=. inversion H5. by apply bet_const.
    + destruct (cvt_f32 sx v) eqn:HDestruct => //=. inversion H5. by apply bet_const.
    + destruct (cvt_f64 sx v) eqn:HDestruct => //=. inversion H5. by apply bet_const.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType.
Qed.  
      
Lemma t_Reinterpret_preserve: forall C v t1 t2 be tf,
    be_typing C [::EConst v; Cvtop t2 Reinterpret t1 None] tf ->
    reduce_simple [::Basic (EConst v); Basic (Cvtop t2 Reinterpret t1 None)] [::Basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v t1 t2 be tf HType HReduce.
  inversion HReduce; subst.
  dependent induction HType; subst.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    apply be_typing_const_deserialise.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType.
Qed.

Lemma t_Drop_preserve: forall C v tf,
    be_typing C [::EConst v; Drop] tf ->
    be_typing C [::] tf.
Proof.
  move => C v tf HType.
  dependent induction HType; subst.
  - invert_be_typing.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - apply bet_weakening. by eapply IHHType.  
Qed.

Lemma t_Select_preserve: forall C v1 v2 n tf be,
    be_typing C [::EConst v1; EConst v2; EConst (ConstInt32 n); Select] tf ->
    reduce_simple [::Basic (EConst v1); Basic (EConst v2); Basic (EConst (ConstInt32 n)); Basic Select] [::Basic be]->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 n tf be HType HReduce.
  inversion HReduce; subst.
  - (* n = 0 : Select second *)
    dependent induction HType; subst => //=.
    + (* Composition *)
      invert_be_typing.
      replace [::t; t; T_i32] with ([::t] ++ [::t] ++ [::T_i32]) in H1 => //=.
      replace [::typeof v1; typeof v2; typeof (ConstInt32 (Wasm_int.int_zero i32m))] with
          ([::typeof v1] ++ [::typeof v2] ++ [::typeof (ConstInt32 (Wasm_int.int_zero i32m))]) in H1 => //=.
      repeat rewrite catA in H1.
      repeat (apply concat_cancel_last in H1; let H2 := fresh "H2" in destruct H1 as [H1 H2]). subst.
      apply bet_weakening_empty_1.
      rewrite -H0. by apply bet_const.
    + apply bet_weakening. by eapply IHHType => //=.
  - (* n = 1 : Select first *)
    dependent induction HType; subst => //=.
    + (* Composition *)
      invert_be_typing.
      replace [::t; t; T_i32] with ([::t] ++ [::t] ++ [::T_i32]) in H1 => //=.
      replace [::typeof v1; typeof v2; typeof (ConstInt32 n)] with
          ([::typeof v1] ++ [::typeof v2] ++ [::typeof (ConstInt32 n)]) in H1 => //=.
      repeat rewrite catA in H1.
      repeat (apply concat_cancel_last in H1; let H2 := fresh "H2" in destruct H1 as [H1 H2]). subst.
      apply bet_weakening_empty_1.
      by apply bet_const.
    + apply bet_weakening. by eapply IHHType => //=.
Qed.

(*
(* Try phrasing in e_typing? There's actually not much difference.
   We might want to only prove for be_typing for these separate lemmas since I believe
     in the end when we want results on e_typing, we can just simply use the 
     et_to_bet lemma to change e_typing to be_typing (and use ety_a for the other
     direction).
 *)
Lemma t_If_e_preserve: forall s C c tf0 es1 es2 tf be,
  e_typing s C (to_e_list [::EConst (ConstInt32 c); If tf0 es1 es2]) tf ->
  reduce_simple (to_e_list [::EConst (ConstInt32 c); If tf0 es1 es2]) [::Basic be] ->
  e_typing s C [::Basic be] tf.
Proof.
  move => s C c tf0 es1 es2 tf be HType HReduce. destruct tf. destruct tf0.
  inversion HReduce; subst.
  - (* if_0 *)
    eapply et_to_bet in HType.
    dependent induction HType; subst => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H1. apply concat_cancel_last in H1. destruct H1. subst.
      apply ety_weakening.
      replace [::Basic (Block (Tf l1 l2) es2)] with (to_e_list [::Block (Tf l1 l2) es2]) => //.
      apply ety_a.
      by apply bet_block.
    + (* Weakening *)
      apply ety_weakening.
      by eapply IHHType => //=.
  - (* if_n0 *)
    apply et_to_bet in HType.
    dependent induction HType; subst => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H1. apply concat_cancel_last in H1. destruct H1. subst.
      apply ety_weakening.
      replace [::Basic (Block (Tf l1 l2) es1)] with (to_e_list [::Block (Tf l1 l2) es1]) => //.
      apply ety_a.
      by apply bet_block.
    + (* Weakening *)
      apply ety_weakening.
      by eapply IHHType => //=.
Qed.*)
      
Lemma t_If_be_preserve: forall C c tf0 es1 es2 tf be,
  be_typing C ([::EConst (ConstInt32 c); If tf0 es1 es2]) tf ->
  reduce_simple (to_e_list [::EConst (ConstInt32 c); If tf0 es1 es2]) [::Basic be] ->
  be_typing C [::be] tf.
Proof.
  move => C c tf0 es1 es2 tf be HType HReduce. destruct tf. destruct tf0.
  inversion HReduce; subst.
  - (* if_0 *)
    dependent induction HType; subst => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H1. apply concat_cancel_last in H1. destruct H1. subst.
      apply bet_weakening.
      by apply bet_block.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
  - (* if_n0 *)
    dependent induction HType; subst => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H1. apply concat_cancel_last in H1. destruct H1. subst.
      apply bet_weakening.
      by apply bet_block.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
Qed.

Lemma t_Br_if_true_preserve: forall C c i tf be,
    be_typing C ([::EConst (ConstInt32 c); Br_if i]) tf ->
    reduce_simple (to_e_list [::EConst (ConstInt32 c); Br_if i]) [::Basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C c i tf be HType HReduce.
  inversion HReduce; subst.
  dependent induction HType; subst => //=.
  - (* Composition *)
    invert_be_typing.
    by apply bet_br => //=. (* Surprisingly convenient! *)
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType => //=.
Qed.

Lemma t_Br_if_false_preserve: forall C c i tf,
    be_typing C ([::EConst (ConstInt32 c); Br_if i]) tf ->
    reduce_simple (to_e_list [::EConst (ConstInt32 c); Br_if i]) [::] ->
    be_typing C [::] tf.
Proof.
  move => C c i tf HType HReduce.
  inversion HReduce; subst.
  dependent induction HType; subst => //=.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType => //=.
Qed.
    
Lemma t_Br_table_preserve: forall C c ids i0 tf be,
    be_typing C ([::EConst (ConstInt32 c); Br_table ids i0]) tf ->
    reduce_simple (to_e_list [::EConst (ConstInt32 c); Br_table ids i0]) [::Basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C c ids i0 tf be HType HReduce.
  inversion HReduce; subst.
  (* in range *)
  - dependent induction HType; subst => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H0. apply concat_cancel_last in H0. destruct H0. subst.
      move/allP in H2.
      assert ((j < length (tc_label C)) && plop2 C j ts').
      -- apply H2. rewrite mem_cat. apply/orP. left.
         eapply list_nth_error_in. by eauto.
      move/andP in H. destruct H.
      by apply bet_br => //.         
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
  (* out of range *)
  - dependent induction HType; subst => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H1. apply concat_cancel_last in H1. destruct H1. subst.
      move/allP in H2.
      assert ((i0 < length (tc_label C)) && plop2 C i0 ts').
      -- apply H2. rewrite mem_cat. apply/orP. right. by rewrite mem_seq1. 
      move/andP in H. destruct H.
      by apply bet_br => //.         
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
Qed.

Lemma t_Tee_local_preserve: forall C v i tf,
    be_typing C ([::EConst v; Tee_local i]) tf ->
    be_typing C [::EConst v; EConst v; Set_local i] tf.
Proof.
  move => C v i tf HType.
  dependent induction HType; subst.
  - (* Composition *)
    invert_be_typing.
    replace ([::EConst v; EConst v; Set_local i]) with ([::EConst v] ++ [::EConst v] ++ [::Set_local i]) => //.
    repeat (try rewrite catA; eapply bet_composition) => //.
    + instantiate (1 := (ts ++ [::typeof v])).
      apply bet_weakening_empty_1. by apply bet_const.
    + instantiate (1 := (ts ++ [::typeof v] ++ [::typeof v])).
      apply bet_weakening. apply bet_weakening_empty_1. by apply bet_const.
    + apply bet_weakening. apply bet_weakening_empty_2. by apply bet_set_local.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType => //=.
Qed.
 (*   
Ltac invert_non_be:=
  repeat lazymatch goal with
  | H: exists e, _ = Basic e |- _ =>
    try by destruct H
  end.
*)
(*
  Preservation for all be_typeable simple reductions.
*)

Theorem t_be_simple_preservation: forall bes bes' es es' C tf,
    be_typing C bes tf ->
    reduce_simple es es' ->
    es_is_basic es ->
    es_is_basic es' ->
    to_e_list bes = es ->
    to_e_list bes' = es' ->
    be_typing C bes' tf.
Proof.
  move => bes bes' es es' C tf HType HReduce HBasic1 HBasic2 HBES1 HBES2.
  destruct tf.
  inversion HReduce; b_to_a_revert; subst; simpl in HType => //; basic_inversion.
(* The proof itself should be refactorable further into tactics as well. *)
  - (* Unop_i32 *)
    eapply t_Unop_i_preserve => //=.
    + replace T_i32 with (typeof (ConstInt32 c)) in HType => //=.
      by apply HType.
    + by apply rs_unop_i32.
  - (* Unop_i64 *)
    eapply t_Unop_i_preserve => //=.
    + replace T_i64 with (typeof (ConstInt64 c)) in HType => //=.
      by apply HType.
    + by apply rs_unop_i64.
  - (* Unop_f32 *)
    eapply t_Unop_f_preserve => //=.
    + replace T_f32 with (typeof (ConstFloat32 c)) in HType => //=.
      by apply HType.
    + by apply rs_unop_f32.
  - (* Unop_f64 *)
    eapply t_Unop_f_preserve => //=.
    + replace T_f64 with (typeof (ConstFloat64 c)) in HType => //=.
      by apply HType.
    + by apply rs_unop_f64.
  - (* Binop_i32_success *)
    eapply t_Binop_i_preserve_success => //=.
    + replace T_i32 with (typeof (ConstInt32 c1)) in HType => //=.
      by apply HType.
    + by apply rs_binop_i32_success.
  - (* Binop_i64_success *)
    eapply t_Binop_i_preserve_success => //=.
    + replace T_i64 with (typeof (ConstInt64 c1)) in HType => //=.
      by apply HType.
    + by apply rs_binop_i64_success.
  - (* Binop_f32_success *)
    eapply t_Binop_f_preserve_success => //=.
    + replace T_f32 with (typeof (ConstFloat32 c1)) in HType => //=.
      by apply HType.
    + by apply rs_binop_f32_success.
  - (* Binop_f64_success *)
    eapply t_Binop_f_preserve_success => //=.
    + replace T_f64 with (typeof (ConstFloat64 c1)) in HType => //=.
      by apply HType.
    + by apply rs_binop_f64_success.
  - (* testop_i T_i32 *)
    apply t_Testop_i32_preserve => //.
  - (* testop_i T_i64 *)
    apply t_Testop_i64_preserve => //.
  - (* relop T_i32 *)
    eapply t_Relop_i_preserve => //=.
    + replace T_i32 with (typeof (ConstInt32 c1)) in HType => //=.
      by apply HType.
    + by apply rs_relop_i32.
  - (* relop T_i64 *)
    eapply t_Relop_i_preserve => //=.
    + replace T_i64 with (typeof (ConstInt64 c1)) in HType => //=.
      by apply HType.
    + by apply rs_relop_i64.
  - (* relop T_f32 *)
    eapply t_Relop_f_preserve => //=.
    + replace T_f32 with (typeof (ConstFloat32 c1)) in HType => //=.
      by apply HType.
    + by apply rs_relop_f32.
  - (* relop T_f64 *)
    eapply t_Relop_f_preserve => //=.
    + replace T_f64 with (typeof (ConstFloat64 c1)) in HType => //=.
      by apply HType.
    + by apply rs_relop_f64.
  - (* Cvtop Convert success *)
    eapply t_Convert_preserve => //=.
    apply HType.
    by apply rs_convert_success => //=.
  - (* Cvtop Reinterpret *)
    eapply t_Reinterpret_preserve => //=.
    apply HType.
    by apply rs_reinterpret => //=.
  - (* Nop *)
    apply Nop_typing in HType; subst => /=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Drop *)
    eapply t_Drop_preserve => //=.
    by apply HType.
  - (* Select_false *)
    eapply t_Select_preserve => //=.
    + by apply HType.
    + by apply rs_select_false.
  - (* Select_true *)
    eapply t_Select_preserve => //=.
    + by apply HType.
    + by apply rs_select_true.
  - (* If_0 *)
    eapply t_If_be_preserve => //=.
    + by apply HType.
    + by apply rs_if_false.
  - (* If_n0 *)
    eapply t_If_be_preserve => //=.
    + by apply HType.
    + by apply rs_if_true.
  - (* br_if_0 *)
    eapply t_Br_if_false_preserve => //=.
    + by apply HType.
    + by apply rs_br_if_false.
  - (* br_if_n0 *)
    eapply t_Br_if_true_preserve => //=.
    + by apply HType.
    + by apply rs_br_if_true.
  - (* br_table -- in range *)
    eapply t_Br_table_preserve => //=.
    + by apply HType.
    + by apply rs_br_table.
  - (* br_table -- out of range default *)
    eapply t_Br_table_preserve => //=.
    + by apply HType.
    + by apply rs_br_table_length.
  - (* tee_local *)
    unfold is_const in H.
    destruct v => //. destruct b => //.
    eapply t_Tee_local_preserve => //=.
Qed.
  
Ltac auto_basic :=
  repeat lazymatch goal with
  | |- es_is_basic [::Basic _; Basic _; Basic _; Basic _] =>
    simpl; repeat split
  | |- es_is_basic [::Basic _; Basic _; Basic _] =>
    simpl; repeat split
  | |- es_is_basic [::Basic _; Basic _] =>
    simpl; repeat split
  | |- es_is_basic [::Basic _] =>
    simpl; repeat split
  | |- e_is_basic (Basic ?e) =>
    unfold e_is_basic; by exists e
  end.
    
Lemma t_const_ignores_context: forall s s' C C' es tf,
    const_list es ->
    e_typing s C es tf ->
    e_typing s' C' es tf.
Proof.
  move => s s' C C' es tf HConst HType.
  apply et_to_bet in HType => //; last by apply const_list_is_basic.
  apply ety_a'; first by apply const_list_is_basic.

  (* A trick on doing induction from tail since composition needs that... *)
  remember (rev es) as es'.
  assert (es = rev es'). rewrite Heqes'. symmetry. by apply revK.
  rewrite H.

  generalize dependent tf. generalize dependent es.
  
  induction es' => //=; move => es HConst HRev1 HRev2 tf HType; destruct tf.
  - subst. simpl in HType. apply empty_typing in HType; subst.
    apply bet_weakening_empty_both. by apply bet_empty.
  - subst.
    rewrite -to_b_list_rev.
    simpl. rewrite rev_cons. rewrite -cats1.
    rewrite -to_b_list_rev in HType.
    simpl in HType. rewrite rev_cons in HType. rewrite -cats1 in HType.
    apply composition_typing in HType.
    destruct HType as [ts [t1s' [t2s' [t3s H]]]].
    destruct H as [H1 [H2 [H3 H4]]].
    subst.
    apply bet_weakening.
    rewrite rev_cons in HConst. rewrite -cats1 in HConst.
    apply const_list_split in HConst. destruct HConst.
    eapply bet_composition.
    + rewrite to_b_list_rev.
      eapply IHes' => //.
      -- by apply H.
      -- by rewrite revK.
      -- rewrite to_b_list_rev in H3. by apply H3.
    + (* The main reason that this holds *)
      simpl in H0. move/andP in H0. destruct H0.
      destruct a => //=.
      destruct b => //=.
      simpl in H4. apply EConst_typing in H4. subst.
      apply bet_weakening_empty_1.
      by apply bet_const.
Qed.


Lemma Block_typing: forall C t1s t2s es tn tm,
    be_typing C [::Block (Tf t1s t2s) es] (Tf tn tm) ->
    exists ts, tn = ts ++ t1s /\ tm = ts ++ t2s /\
               be_typing (upd_label C ([::t2s] ++ (tc_label C))) es (Tf t1s t2s).
Proof.
  move => C t1s t2s es tn tm HType.
  dependent induction HType => //=.
  - by exists [::].
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists (ts ++ x).
    repeat rewrite -catA.
    by repeat split => //=.
Qed.
    
Lemma Loop_typing: forall C t1s t2s es tn tm,
    be_typing C [::Loop (Tf t1s t2s) es] (Tf tn tm) ->
    exists ts, tn = ts ++ t1s /\ tm = ts ++ t2s /\
               be_typing (upd_label C ([::t1s] ++ (tc_label C))) es (Tf t1s t2s).
Proof.
  move => C t1s t2s es tn tm HType.
  dependent induction HType => //=.
  - by exists [::].
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists (ts ++ x).
    repeat rewrite -catA.
    by repeat split => //=.
Qed.

Lemma Break_typing: forall n C t1s t2s,
    be_typing C [::Br n] (Tf t1s t2s) ->
    exists ts ts0, n < size (tc_label C) /\
               plop2 C n ts /\
               t1s = ts0 ++ ts.
Proof.
  move => n C t1s t2s HType.
  dependent induction HType => //=.
  - by exists ts, t1s0.
  - invert_be_typing.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [ts0 [H1 [H2 H3]]]. subst.
    exists x, (ts ++ ts0).
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Label_typing: forall s C n es0 es ts1 ts2,
    e_typing s C [::Label n es0 es] (Tf ts1 ts2) ->
    exists ts ts2', ts2 = ts1 ++ ts2' /\
                    e_typing s C es0 (Tf ts ts2') /\
                    e_typing s (upd_label C ([::ts] ++ (tc_label C))) es (Tf [::] ts2') /\
                    length ts = n.
Proof.
  move => s C n es0 es ts1 ts2 HType.
  dependent induction HType.
  - (* ety_a *)
    assert (es_is_basic (to_e_list bes)); first by apply to_e_list_basic.
    rewrite x in H0. by basic_inversion.
  - (* ety_composition *)
    apply extract_list1 in x. destruct x. subst.
    apply et_to_bet in HType1 => //.
    simpl in HType1. apply empty_typing in HType1. subst.
    by eapply IHHType2 => //.
  - (* ety_weakening *)
    edestruct IHHType => //=.
    destruct H as [ts2' [H1 [H2 [H3 H4]]]].
    exists x, ts2'.
    repeat split => //=. subst. by rewrite catA.
  - (* ety_label *)
    by exists ts, ts2.
Qed.

(*
  Looking at what we want to prove in the Lfilled_break case, it might be tempting to
    prove the following:

Lemma Lfilled_break_typing: forall n lh vs LI ts s C t2s,
    e_typing s (upd_label C ([::ts] ++ tc_label C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::Basic (Br n)]) LI ->
    e_typing s C vs (Tf [::] ts).

  The lemma itself is definitely correct, and an apparent approach is to do induction
    on n (or induction on the lfilled hypothesis).

  However, this will *NOT* work: the culprit is that there is no inductive relationship
    that changes the instruction (Br n+1) into (Br n), and we will get a useless 
    induction hypothesis that can never be applied.

  We need to somehow avoid getting the parameter of Br into induction. By the lfilled
    hypothesis, we know LI is a nested Label which, at the innermost level, has (Br n) 
    as its first non-constant instruction, and vs at the top of the value stack.

  Recall that (Br n) looks at the nth entry in the label of the typing context and
    needs to consume that type. Since we can only induct on the depth of lfilled
    (but not the n in the instruction), they have to be two separate numbers, say
    n and m. Now if n is 0, the instruction will basically look at the mth entry;
    what if n is not 0? In that case if we trace the expansion of LI and simulate
    how the typing is evaluated, we realize that there will be n entries prepended
    to the label of the typing context, after which we'll then find the mth element
    of it due to the (Br m).

  So a more sensible lemma to prove is the following, which the original lemma we 
    wanted is a special case of:
*)

Lemma Lfilled_break_typing: forall n m k lh vs LI ts s C t2s tss,
    e_typing s (upd_label C (tss ++ [::ts] ++ tc_label C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::Basic (Br m)]) LI ->
    length tss = k ->
    n + k = m ->
    e_typing s C vs (Tf [::] ts).
Proof.
  move => n m k lh vs LI ts s C ts2 tss HType HConst HLength HLF HTSSLength HSum.
  apply const_es_exists in HConst. destruct HConst. subst.
  move/lfilledP in HLF.
  generalize dependent ts.
  generalize dependent ts2.
  generalize dependent LI.
  generalize dependent tss.
  generalize dependent lh.
  induction n.
  - move => lh tss LI HLF ts2 ts HType HTSSLength.
    rewrite add0n in HLF.
    repeat rewrite catA in HType.
    inversion HLF.
    apply const_es_exists in H. destruct H. subst.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    subst. clear H1.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H5 [H6 [H7 H8]]]]]]].
    subst.
    apply e_composition_typing in H7.
    destruct H7 as [ts0'' [t1s'' [t2s'' [t3s'' [H9 [H10 [H11 H12]]]]]]].
    subst.
    apply et_to_bet in H12; last by auto_basic.
    apply Break_typing in H12.
    destruct H12 as [ts0 [ts1 [H13 [H14 H15]]]]. clear H13.
    unfold plop2 in H14. simpl in H14. move/eqP in H14. inversion H14. subst.
    clear H14.
    apply et_to_bet in H11; last by (apply const_list_is_basic; apply v_to_e_is_const_list).
    apply Const_list_typing in H11.
    repeat rewrite length_is_size in HTSSLength.
    rewrite -catA in H0. rewrite list_nth_prefix in H0. inversion H0. subst. clear H0.
    assert ((ts1 == t1s'') && (ts0 == vs_to_vts x)).
    + apply concat_cancel_last_n => //=. rewrite size_map.
      by rewrite v_to_e_size in HTSSLength.
    + move/andP in H. destruct H.
      move/eqP in H0. subst.
      apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
      by apply Const_list_typing_empty.    
  - move => lh tss LI HLF ts2 ts HType HTSSLength.
    inversion HLF. subst.
    repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    clear H2. clear H3.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H6 [H7 [H8 H9]]]]]]].
    destruct ts0' => //=.
    destruct t1s' => //=.
    clear H6. clear H7.
    apply Label_typing in H9.
    destruct H9 as [ts0'' [t2s'' [H10 [H11 [H12 H13]]]]]. subst.
    simpl in H12.
    rewrite upd_label_overwrite in H12.
    rewrite -cat1s in H12. repeat rewrite catA in H12.
    remember ([::ts0''] ++ tss) as tss'. rewrite -catA in H12.
    replace (n.+1+length tss) with (n + length tss') in H1.
    eapply IHn => //=.
    + by apply H1.
    + by apply H12.
    (* replace *)
    assert (length tss' = length tss + 1).
    { rewrite Heqtss'. rewrite cat1s. simpl. by lias. }
    by lias.
Qed.

(*
  And yes, the above observation was obviously the result of some futile attempt
    to prove the unprovable version of the lemma.

Lemma Lfilled_break_typing: forall n lh vs LI ts s C t2s,
    e_typing s (upd_label C ([::ts] ++ tc_label C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::Basic (Br n)]) LI ->
    e_typing s C vs (Tf [::] ts).
Proof.
  move => n lh vs LI ts s C ts2 HType HConst HLength HLF.
  apply const_es_exists in HConst. destruct HConst. subst.
  move/lfilledP in HLF.
  generalize dependent ts2. 
  generalize dependent LI.
  induction n.
  - move => LI HLF ts2 HType.
    repeat rewrite catA in HType.
    inversion HLF.
    apply const_es_exists in H. destruct H. subst.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    subst. clear H1.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H5 [H6 [H7 H8]]]]]]].
    subst.
    apply e_composition_typing in H7.
    destruct H7 as [ts0'' [t1s'' [t2s'' [t3s'' [H9 [H10 [H11 H12]]]]]]].
    subst.
    apply et_to_bet in H12; last by auto_basic.
    apply Break_typing in H12.
    destruct H12 as [ts0 [ts1 [H13 [H14 H15]]]]. clear H13.
    unfold plop2 in H14. simpl in H14. move/eqP in H14. inversion H14. subst.
    clear H14.
    apply et_to_bet in H11; last by (apply const_list_is_basic; apply v_to_e_is_const_list).
    apply Const_list_typing in H11.
    repeat rewrite length_is_size in HLength.
    assert ((ts1 == t1s'') && (ts0 == vs_to_vts x)).
    + apply concat_cancel_last_n => //=. rewrite size_map.
      by rewrite v_to_e_size in HLength.
    + move/andP in H. destruct H.
      move/eqP in H0. subst.
      apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
      by apply Const_list_typing_empty.    
  - move => LI HLF ts2 HType.
    inversion HLF. subst.
    repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    clear H2. clear H3.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H6 [H7 [H8 H9]]]]]]].
    destruct ts0' => //=.
    destruct t1s' => //=.
    clear H6. clear H7.
    apply Label_typing in H9.
    destruct H9 as [ts0'' [t2s'' [H10 [H11 [H12 H13]]]]]. subst.
    simpl in H12. 
            
Admitted.
 *)

Lemma Local_typing: forall s C n i vs es t1s t2s,
    e_typing s C [::Local n i vs es] (Tf t1s t2s) ->
    exists ts, t2s = t1s ++ ts /\
               s_typing s (Some ts) i vs es ts /\
               length ts = n.
Proof.
  move => s C n i vs es t1s t2s HType.
  dependent induction HType; subst.
  - (* ety_a *)
    assert (es_is_basic (to_e_list bes)); first by apply to_e_list_basic.
    rewrite x in H0. by basic_inversion.
  - (* ety_composition *)
    apply extract_list1 in x. destruct x. subst.
    apply et_to_bet in HType1 => //.
    simpl in HType1. apply empty_typing in HType1. subst.
    by eapply IHHType2 => //.
  - (* ety_weakening *)
    edestruct IHHType => //=.
    edestruct H as [H1 [H2 H3]]. subst. clear H.
    exists x.
    repeat split => //=.
    by rewrite catA.
  - (* ety_local *)
    by exists t2s.
Qed.

Lemma Return_typing: forall C t1s t2s,
    be_typing C [::Return] (Tf t1s t2s) ->
    exists ts ts', t1s = ts' ++ ts /\
                   tc_return C = Some ts.
Proof.
  move => C t1s t2s HType.
  dependent induction HType => //=.
  - by exists ts, t1s0.
  - invert_be_typing.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [ts' [H1 H2]]. subst.
    exists x, (ts ++ ts').
    split => //=.
    by rewrite -catA.
Qed.

(* 
  Similarly, Local does not involve in induction either. So what we want to prove
    is also slightly different from what we desire. However, this one is easier
    to observe.

  The only thing that got me stuck for a while is to observe that label of the
    typing context plays no role in typing for this case; this is required since
    we'll get an extra label update from inverting the Label instruction.
 *)

Lemma Lfilled_return_typing: forall n lh vs LI ts s C lab t2s,
    e_typing s (upd_label C lab) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::Basic Return]) LI ->
    Some ts = tc_return C ->
    e_typing s C vs (Tf [::] ts).
Proof.
  induction n; move => lh vs LI ts s C lab t2s HType HConst HLength HLF HReturn; move/lfilledP in HLF; inversion HLF; subst => //=.
  - repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H1 [H2 [H3 H4]]]]]]].
    destruct ts0 => //=.
    destruct t1s0 => //=.
    subst. clear H1.
    apply e_composition_typing in H3.
    destruct H3 as [ts1 [t1s1 [t2s1 [t3s1 [H5 [H6 [H7 H8]]]]]]].
    destruct ts1 => //=.
    destruct t1s1 => //=.
    subst. clear H5. 
    apply e_composition_typing in H7.
    destruct H7 as [ts2 [t1s2 [t2s2 [t3s2 [H9 [H10 [H11 H12]]]]]]].
    destruct ts2 => //=.
    destruct t1s2 => //=.
    subst. clear H9. simpl in H8. simpl in H4.
    apply et_to_bet in H8; auto_basic. apply Return_typing in H8.
    destruct H8 as [ts1 [ts2 [H13 H14]]]. subst.
    apply et_to_bet in H12; last by apply const_list_is_basic.
    apply const_es_exists in HConst. destruct HConst. subst.
    apply Const_list_typing in H12.
    rewrite -HReturn in H14. inversion H14. subst. clear H14.
    assert ((ts2 == t3s2) && (ts1 == vs_to_vts x)).
    + apply concat_cancel_last_n => //=.
      repeat rewrite length_is_size in HLength.
      rewrite v_to_e_size in HLength.
      by rewrite size_map.
    + move/andP in H0. destruct H0.
      move/eqP in H1. subst.
      apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
      by apply Const_list_typing_empty.
  - repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s0 => //=.
    subst. clear H2.
    apply e_composition_typing in H4.
    destruct H4 as [ts1 [t1s1 [t2s1 [t3s1 [H6 [H7 [H8 H9]]]]]]].
    destruct ts1 => //=.
    destruct t1s1 => //=.
    subst. clear H6.
    apply Label_typing in H9.
    destruct H9 as [ts' [ts2' [H10 [H11 [H12 H13]]]]].
    subst. simpl in H5.
    eapply IHn => //.
    simpl in H12.
    apply H12.
    apply/lfilledP.
    by apply H1.
Qed.
  
Lemma Local_return_typing: forall s C vs i vls LI tf n lh,
    e_typing s C [:: Local (length vs) i vls LI] tf ->
    const_list vs ->
    lfilled n lh (vs ++ [::Basic Return]) LI ->
    e_typing s C vs tf.
Proof.
  move => s C vs i vls LI tf n lh HType HConst HLF.
  destruct tf as [t1s t2s].
  apply Local_typing in HType.
  destruct HType as [ts [H1 [H2 H3]]]. subst.
  inversion H2. subst. clear H4. clear H2.
  apply et_weakening_empty_1.
  assert (e_typing s (upd_local_return C1 (tc_local C1 ++ tvs) (Some ts)) vs (Tf [::] ts)).
  { eapply Lfilled_return_typing; eauto. }
  apply et_to_bet in H0; last by apply const_list_is_basic.
  apply const_es_exists in HConst. destruct HConst.
  rewrite H2 in H0.
  apply Const_list_typing in H0.
  rewrite H0. simpl. subst.
  - apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
    by apply Const_list_typing_empty.
Qed.

Theorem t_simple_preservation: forall s i es es' C loc lab ret tf,
    inst_typing s i C ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es tf ->
    reduce_simple es es' ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es' tf.
Proof.
  move => s i es es' C loc lab ret tf HInstType HType HReduce.
  inversion HReduce; subst; try (by (apply et_to_bet in HType => //; auto_basic; apply ety_a' => //; auto_basic; eapply t_be_simple_preservation; try by eauto; auto_basic)); try by apply ety_trap.
  (* Though only a few cases, these cases are expected to be much more difficult. *)
  - (* Block *)
    destruct tf.
    apply et_to_bet in HType.
    2: {
      apply basic_split => //=.
      + by apply const_list_is_basic.
      + split => //=. unfold e_is_basic. by eauto.
      }
    rewrite to_b_list_concat in HType. simpl in HType.
    apply composition_typing in HType.
    destruct HType as [ts [t1s' [t2s' [t3s [H2 [H3 [H4 H5]]]]]]]. subst.
    apply const_es_exists in H. destruct H. subst.
    apply Const_list_typing in H4. subst.
    apply Block_typing in H5.
    destruct H5 as [t3s [H6 [H7 H8]]].
    subst.
    repeat rewrite length_is_size in H1. rewrite v_to_e_size in H1.
    assert ((t1s' == t3s) && ((vs_to_vts x) == t1s)) => //=.
    + apply concat_cancel_last_n => //=. by rewrite size_map.
    + move/andP in H. destruct H.
      move/eqP in H. move/eqP in H0. subst. clear H6. clear H1.
      rewrite catA. apply et_weakening_empty_1.
      eapply ety_label.
      -- apply ety_a' => //=.
         instantiate (1:= t2s).
         apply bet_weakening_empty_both.
         by apply bet_empty.
      -- apply ety_a' => //=.
         ++ apply basic_split.
            * apply const_list_is_basic. by apply v_to_e_is_const_list.
            * by apply to_e_list_basic.
         ++ rewrite to_b_list_concat. simpl in H8.
            eapply bet_composition'; first by apply Const_list_typing_empty.
            remember (to_e_list es0) as es'.
            symmetry in Heqes'.
            apply b_e_elim in Heqes'.
            destruct Heqes'. by subst.
      -- by [].
  - (* Loop *)
    destruct tf.
    apply et_to_bet in HType.
    2: {
      apply basic_split => //=.
      + by apply const_list_is_basic.
      + split => //=. unfold e_is_basic. by eauto.
    }
    rewrite to_b_list_concat in HType. simpl in HType.
    apply composition_typing in HType.
    destruct HType as [ts [t1s' [t2s' [t3s [H2 [H3 [H4 H5]]]]]]]. subst.
    apply const_es_exists in H. destruct H. subst.
    apply Const_list_typing in H4. subst.
    apply Loop_typing in H5.
    destruct H5 as [t3s [H6 [H7 H8]]]. subst.
    repeat rewrite length_is_size in H1. rewrite v_to_e_size in H1.
    assert ((t1s' == t3s) && ((vs_to_vts x) == t1s)) => //=.
    + apply concat_cancel_last_n => //=. by rewrite size_map.
    + move/andP in H. destruct H.
      move/eqP in H. move/eqP in H0. subst. clear H6. clear H1.
      rewrite catA. apply et_weakening_empty_1.
      eapply ety_label.
      -- apply ety_a' => //=.
         ++ split => //=. unfold e_is_basic. by eauto.
         ++ by apply bet_loop.
      -- apply ety_a' => //=.
         ++ apply basic_split.
            * apply const_list_is_basic. by apply v_to_e_is_const_list.
            * by apply to_e_list_basic.
         ++ rewrite to_b_list_concat. simpl in H8.
            eapply bet_composition'; first by apply Const_list_typing_empty.
            remember (to_e_list es0) as es'.
            symmetry in Heqes'.
            apply b_e_elim in Heqes'.
            destruct Heqes'. subst.
      -- by [].
      -- repeat rewrite length_is_size.
         unfold vs_to_vts. rewrite size_map.
         by rewrite v_to_e_size.
  - (* Label_const *)
    dependent induction HType; subst.
    + (* ety_a *)
      assert (es_is_basic (to_e_list bes)); first by apply to_e_list_basic.
      rewrite x in H1. by basic_inversion.
    + (* ety_composition *)
      apply extract_list1 in x. destruct x. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_typing in HType1. subst.
      by eapply IHHType2 => //.
    + (* ety_weakening *)
      apply ety_weakening.
      by eapply IHHType => //.
    + (* ety_label *)
      eapply t_const_ignores_context; try by eauto.
  - (* Label_lfilled_Break *)
    dependent induction HType; subst.
    + (* ety_a *)
      assert (es_is_basic (to_e_list bes)); first by apply to_e_list_basic.
      rewrite x in H2. by basic_inversion.
    + (* ety_composition *)
      apply extract_list1 in x. destruct x. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_typing in HType1. subst.
      eapply IHHType2 => //=.
      -- by apply HReduce.
      -- by apply H1.
    + (* ety_weakening *)
      apply ety_weakening.
      eapply IHHType => //.
      -- by apply HReduce.
      -- by apply H1.
    + (* ety_label *)
      eapply et_composition' => //=.
      -- eapply Lfilled_break_typing => //=.
         ++ instantiate (4 := [::]). rewrite cat0s.
            by apply HType2.
         ++ by [].
         ++ simpl. rewrite addn0. by apply H1.
      -- by apply HType1.
  - (* Local_const *)
    dependent induction HType; subst.
    + (* ety_a *)
      assert (es_is_basic (to_e_list bes)); first by apply to_e_list_basic.
      rewrite x in H1. by basic_inversion.
    + (* ety_composition *)
      apply extract_list1 in x. destruct x. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_typing in HType1. subst.
      by eapply IHHType2 => //.
    + (* ety_weakening *)
      apply ety_weakening.
      by eapply IHHType => //.
    + (* ety_local *)
      inversion H. subst.
      eapply t_const_ignores_context; try by eauto.
  - (* Local_lfilled_Return *)
    eapply Local_return_typing; by eauto.
  - (* Tee_local -- actually a simple reduction *)
    destruct v => //.
    destruct b => //.
    apply et_to_bet in HType => //; auto_basic.
    apply ety_a' => //; auto_basic.
    eapply t_be_simple_preservation; try by eauto; by auto_basic.
Qed.

  (*
Theorem t_e_preservation: forall s vs es i s' vs' es' bes bes' C C' tf,
    inst_typing s i C ->
    inst_typing s' i C' ->
    be_typing (upd_local C (map typeof vs)) bes tf ->
    reduce s vs es i s' vs' es' ->
    es_is_basic es ->
    es_is_basic es' ->
    to_e_list bes = es ->
    to_e_list bes' = es' ->
    be_typing (upd_local C (map typeof vs')) bes' tf.
Proof.
  move => s vs es i s' vs' es' bes bes' C C' tf HInstT1 HInstT2 HType HReduce HBasic1 HBasic2 HBES1 HBES2.
  inversion HReduce; b_to_a_revert; subst; simpl in HType => //; try (unfold es_is_basic in HBasic1; unfold e_is_basic in HBasic1; inversion HBasic1 => //); try (unfold es_is_basic in HBasic2; unfold e_is_basic in HBasic2; inversion HBasic2 => //); invert_non_be; destruct tf.
  - (* reduce_simple *)
    eapply t_be_simple_preservation.
    + by apply HType.
    + by apply H.
    + by [].
    + by [].
    + symmetry. by apply e_b_elim.
    + symmetry. by apply e_b_elim.
  - (* Invoke -- not be typeable *)
    + apply basic_concat in H15. destruct H15.
      inversion H0. inversion H1. discriminate H5.
  - (* Get_local *)
    
Admitted.
   *)
(*
Lemma func_agree_self: forall s_funcs i_funcs,
    all2 (functions_agree s_funcs) i_funcs
         (collect_at_inds [seq cl_type i | i <- s_funcs] i_funcs).
Proof.
  move => s_funcs i_funcs.
  generalize dependent s_funcs.
  induction i_funcs; move => s_funcs => //=.
  destruct (List.nth_error [seq cl_type i | i <- s_funcs] a) eqn:Hnth => //=.
  - apply/andP. split => //.
    unfold functions_agree.
    apply/andP. split.
    + replace (length s_funcs) with (length ([seq cl_type i | i <- s_funcs])).
      apply/ltP. rewrite - List.nth_error_Some. by rewrite Hnth.
      (* replace *)
      repeat rewrite length_is_size.
      clear Hnth.
      induction s_funcs => //=.
      by f_equal.
    + unfold option_map.
      *)


Lemma Call_typing: forall j C t1s t2s,
    be_typing C [::Call j] (Tf t1s t2s) ->
    exists ts t1s' t2s', j < length (tc_func_t C) /\ 
    List.nth_error (tc_func_t C) j = Some (Tf t1s' t2s') /\
                         t1s = ts ++ t1s' /\
                         t2s = ts ++ t2s'.
Proof.
  move => j C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::], t1s, t2s.
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [t1s' [t2s' [H1 [H2 [H3 H4]]]]].
    subst.
    exists (ts ++ x), t1s', t2s'.
    repeat rewrite -catA.
    by repeat (split => //=).
Qed.

Lemma Call_indirect_typing: forall i C t1s t2s,
    be_typing C [::Call_indirect i] (Tf t1s t2s) ->
    exists tn tm ts, tc_table C <> None /\
    i < length (tc_types_t C) /\
    List.nth_error (tc_types_t C) i = Some (Tf tn tm) /\
    t1s = ts ++ tn ++ [::T_i32] /\ t2s = ts ++ tm.
Proof.
  move => i C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t1s0, t2s, [::].
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [tm [ts' [H1 [H2 [H3 [H4 H5]]]]]]. subst.
    exists x, tm, (ts ++ ts').
    by repeat rewrite -catA.
Qed.

Ltac remove_messes:=
  repeat lazymatch goal with
  | H: is_true (_ && _ ) |- _ =>
    move/andP in H; destruct H
  | H: (_ && _) = true |- _ =>
    move/andP in H; destruct H                                    
  | H: is_true (_ == _) |- _ =>
    move/eqP in H
  | H: is_true (_ || _) |- _=>
    move/orP in H; destruct H
  | H: Some _ = Some _ |- _ =>
    inversion H; subst; clear H
  | H: option_map _ _ = _ |- _ =>
    unfold option_map in H
  | H: match ?exp with
       | Some _ => _
       | None => _
       end = _
    |- _ =>
    let Hoption := fresh "Hoption" in
    destruct exp eqn:Hoption; try by []
  | H: is_true match ?exp with
       | Some _ => _
       | None => _
       end
    |- _ =>
    let Hoption := fresh "Hoption" in
    destruct exp eqn:Hoption; try by []
  end.


Lemma all_projection: forall {X:Type} f (l:seq X) n x,
    all f l ->
    List.nth_error l n = Some x ->
    f x.
Proof.
  move => X f l n x.
  generalize dependent l.
  induction n => //; destruct l => //=; move => HF HS; remove_messes => //.
  eapply IHn; by eauto.
Qed.

Lemma all2_projection: forall {X Y:Type} f (l1:seq X) (l2:seq Y) n x1 x2,
    all2 f l1 l2 ->
    List.nth_error l1 n = Some x1 ->
    List.nth_error l2 n = Some x2 ->
    f x1 x2.
Proof.
  move => X Y f l1 l2 n.
  generalize dependent l1.
  generalize dependent l2.
  induction n => //=; move => l2 l1 x1 x2 HALL HN1 HN2.
  - destruct l1 => //=. destruct l2 => //=.
    inversion HN1. inversion HN2. subst. clear HN1. clear HN2.
    simpl in HALL. move/andP in HALL. by destruct HALL.
  - destruct l1 => //=. destruct l2 => //=.
    simpl in HALL. move/andP in HALL. destruct HALL.
    eapply IHn; by eauto.
Qed.

Definition function {X Y:Type} (f: X -> Y -> Prop) : Prop :=
  forall x y1 y2, ((f x y1 /\ f x y2) -> y1 = y2).

Lemma all2_function_unique: forall {X Y:Type} f (l1:seq X) (l2 l3:seq Y),
    all2 f l1 l2 ->
    all2 f l1 l3 ->
    function f ->
    l2 = l3.
Proof.
  move => X Y f l1.
  induction l1 => //=; move => l2 l3 HA1 HA2 HF.
  - destruct l2 => //. by destruct l3 => //.
  - destruct l2 => //=; destruct l3 => //=.
    simpl in HA1. simpl in HA2.
    move/andP in HA1. move/andP in HA2.
    destruct HA1. destruct HA2.
    unfold function in HF.
    assert (y = y0); first by eapply HF; eauto.
    rewrite H3. f_equal.
    by apply IHl1.
Qed.

Lemma globs_agree_function: forall s,
    function (globals_agree (s_globs s)).
Proof.
  move => s. unfold function. move => x y1 y2 [H1 H2].
  unfold globals_agree in H1. unfold globals_agree in H2.
  remove_messes.
  unfold global_agree in H3. unfold global_agree in H4.
  remove_messes.
  destruct y1; destruct y2 => //.
  simpl in H0. simpl in H2. simpl in H3. simpl in H4. by subst.
Qed.
  
Lemma functions_agree_function: forall s,
    function (functions_agree (s_funcs s)).
Proof.
  move => s. unfold function. move => x y1 y2 [H1 H2].
  unfold functions_agree in H1. unfold functions_agree in H2.
  by remove_messes.
Qed.

Lemma inst_typing_unique: forall s i C C',
    inst_typing s i C ->
    inst_typing s i C' ->
    C = C'.
Proof.
  move => s i C C' HIT1 HIT2.
  unfold inst_typing in HIT1. unfold inst_typing in HIT2.
  destruct i => //.
  destruct C => //.
  destruct tc_local => //=.
  destruct tc_label => //=.
  destruct tc_return => //=.
  move/andP in HIT1. destruct HIT1.
  repeat (move/andP in H; destruct H).
  destruct C' => //.
  destruct tc_local => //=.
  destruct tc_label => //=.
  destruct tc_return => //=.
  move/andP in HIT2. destruct HIT2.
  repeat (move/andP in H4; destruct H4).
  assert (tc_global = tc_global0); first by eapply all2_function_unique; eauto; apply globs_agree_function.
  assert (tc_func_t = tc_func_t0); first by eapply all2_function_unique; eauto; apply functions_agree_function.
  move/eqP in H4.
  move/eqP in H. subst.
  unfold memi_agree in H0.
  unfold memi_agree in H5.
  by remove_messes.
Qed.  

Lemma tc_func_reference1: forall j k i s f C tf,
  List.nth_error (i_funcs i) j = Some k ->
  List.nth_error (s_funcs s) k = Some f ->
  inst_typing s i C ->
  List.nth_error (tc_func_t C) j = Some tf ->
  tf = cl_type f.
Proof.
  move => j k i s f C tf HN1 HN2 HInstType HN3.
  unfold inst_typing in HInstType.
  destruct i => //=.
  destruct C => //=.
  destruct tc_local => //=.
  destruct tc_label => //=.
  destruct tc_return => //=.
  move/andP in HInstType. destruct HInstType.
  repeat (move/andP in H; destruct H).
  simpl in HN1. simpl in HN3.
  eapply all2_projection in H3; eauto.
  unfold functions_agree in H3. move/andP in H3. destruct H3.
  unfold option_map in H4.
  rewrite HN2 in H4. move/eqP in H4.
  by inversion H4.
Qed.

Lemma tc_func_reference2: forall s C i j cl tf,
  List.nth_error (i_types i) j = Some (cl_type cl) ->
  inst_typing s i C ->
  List.nth_error (tc_types_t C) j = Some tf ->
  tf = cl_type cl.
Proof.
  move => s C i j cl tf HN1 HIT HN2.
  unfold inst_typing in HIT.
  destruct i => //=.
  destruct C => //=.
  destruct tc_local => //=.
  destruct tc_label => //=.
  destruct tc_return => //=.
  move/andP in HIT. destruct HIT.
  repeat (move/andP in H; destruct H).
  simpl in HN1. simpl in HN2.
  move/eqP in H. subst.
  rewrite HN1 in HN2.
  by inversion HN2.
Qed.  

Lemma Invoke_func_native_typing: forall s i C tn tm ts es t1s t2s,
    e_typing s C [::Invoke (Func_native i (Tf tn tm) ts es)] (Tf t1s t2s) ->
    exists ts' C', t1s = ts' ++ tn /\ t2s = ts' ++ tm /\
                inst_typing s i C' /\
               be_typing (upd_local_label_return C' (tc_local C' ++ tn ++ ts) ([::tm] ++ tc_label C') (Some tm)) es (Tf [::] tm).
Proof.
  move => s i C tn tm ts es t1s t2s HType.
  dependent induction HType; subst.
  - by destruct bes => //=.
  - apply extract_list1 in x. destruct x. subst.
    apply et_to_bet in HType1 => //=.
    apply empty_typing in HType1. subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [C' [H1 [H2 [H3 H4]]]]. subst.
    exists (ts0 ++ x), C'.
    repeat split => //; by rewrite catA.
  - inversion H. subst. inversion H8. subst.
    exists [::], C0.
    repeat split => //.
Qed.

Lemma Invoke_func_host_typing: forall s C h tn tm t1s t2s,
    e_typing s C [::Invoke (Func_host (Tf tn tm) h)] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ tn /\ t2s = ts ++ tm.
Proof.
  move => s C h tn tm t1s t2s HType.
  dependent induction HType; subst.
  - by destruct bes => //=.
  - apply extract_list1 in x. destruct x. subst.
    apply et_to_bet in HType1 => //=.
    apply empty_typing in HType1. subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    exists (ts ++ x). destruct H. subst.
    by split; repeat rewrite catA.
  - inversion H. subst. by exists [::].
Qed.

Lemma Get_local_typing: forall C i t1s t2s,
    be_typing C [::Get_local i] (Tf t1s t2s) ->
    exists t, List.nth_error (tc_local C) i = Some t /\
    t2s = t1s ++ [::t] /\
    i < length (tc_local C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Set_local_typing: forall C i t1s t2s,
    be_typing C [::Set_local i] (Tf t1s t2s) ->
    exists t, List.nth_error (tc_local C) i = Some t /\
    t1s = t2s ++ [::t] /\
    i < length (tc_local C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Get_global_typing: forall C i t1s t2s,
    be_typing C [::Get_global i] (Tf t1s t2s) ->
    exists t, option_map tg_t (List.nth_error (tc_global C) i) = Some t /\
    t2s = t1s ++ [::t] /\
    i < length (tc_global C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Set_global_typing: forall C i t1s t2s,
    be_typing C [::Set_global i] (Tf t1s t2s) ->
    exists t, option_map tg_t (List.nth_error (tc_global C) i) = Some t /\
    t1s = t2s ++ [::t] /\
    i < length (tc_global C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Load_typing: forall C t a off tp_sx t1s t2s,
    be_typing C [::Load t tp_sx a off] (Tf t1s t2s) ->
    exists ts n, t1s = ts ++ [::T_i32] /\ t2s = ts ++ [::t] /\
                    tc_memory C = Some n /\
                    load_store_t_bounds a (option_projl tp_sx) t.
Proof.
  move => C t a off tp_sx t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::], n.
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [n [H1 [H2 [H3 H4]]]]. subst.
    exists (ts ++ x), n.
    by repeat rewrite -catA.
Qed.

Lemma Store_typing: forall C t a off tp t1s t2s,
    be_typing C [::Store t tp a off] (Tf t1s t2s) ->
    exists n, t1s = t2s ++ [::T_i32; t] /\
                    tc_memory C = Some n /\
                    load_store_t_bounds a tp t.
Proof.
  move => C t a off tp t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists n.
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x.
    by repeat rewrite -catA.
Qed.

Lemma Current_memory_typing: forall C t1s t2s,
    be_typing C [::Current_memory] (Tf t1s t2s) ->
    exists n, tc_memory C = Some n /\ t2s = t1s ++ [::T_i32].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists n.
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H. subst.
    exists x.
    by repeat rewrite -catA.
Qed.

Lemma Grow_memory_typing: forall C t1s t2s,
    be_typing C [::Grow_memory] (Tf t1s t2s) ->
    exists ts n, tc_memory C = Some n /\ t2s = t1s /\ t1s = ts ++ [::T_i32].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::], n.
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [n [H1 [H2 H3]]]. subst.    
    exists (ts ++ x), n.
    by repeat rewrite -catA.
Qed.

Lemma store_typed_cl_typed: forall s n f,
    List.nth_error (s_funcs s) n = Some f ->
    store_typing s ->
    cl_typing s f (cl_type f).
Proof.
  move => s n f HN HST.
  unfold store_typing in HST.
  destruct s => //=.
  remove_messes.
  simpl in HN.
  destruct HST.
  (* arrow actually required to avoid ssreflect hijacking the rewrite tactic! *)
  rewrite -> List.Forall_forall in H.
  apply List.nth_error_In in HN.
  apply H in HN. unfold cl_type_check_single in HN. destruct HN.
  by inversion H1; subst.
Qed.
  
Lemma inst_t_context_local_empty: forall s i C,
    inst_typing s i C ->
    tc_local C = [::].
Proof.
  move => s i C HInstType.
  unfold inst_typing in HInstType.
  destruct i => //=.
  destruct C => //=.
  by destruct tc_local.
Qed.

Lemma inst_t_context_label_empty: forall s i C,
    inst_typing s i C ->
    tc_label C = [::].
Proof.
  move => s i C HInstType.
  unfold inst_typing in HInstType.
  destruct i => //=.
  destruct C => //=.
  destruct tc_local; by destruct tc_label.  
Qed.

Lemma global_type_reference: forall s i j C v t,
    inst_typing s i C ->
    sglob_val s i j = Some v ->
    option_map tg_t (List.nth_error (tc_global C) j) = Some t ->
    typeof v = t.
Proof.
  move => s i j C v t HInstType Hvref Htref.
  unfold sglob_val in Hvref. unfold option_map in Hvref.
  unfold sglob in Hvref. unfold option_bind in Hvref.
  unfold sglob_ind in Hvref.
  destruct (List.nth_error (i_globs i) j) eqn:Hi => //=.
  destruct (List.nth_error (s_globs s) i0) eqn:Hv => //=.
  unfold option_map in Htref.
  destruct (List.nth_error (tc_global C) j) eqn:Ht => //=.
  inversion Hvref. inversion Htref. subst. clear Hvref. clear Htref.
  unfold inst_typing in HInstType.
  destruct i => //=. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  move/andP in HInstType. destruct HInstType.
  repeat (move/andP in H; destruct H).
  eapply all2_projection in H2; eauto.
  unfold globals_agree in H2. move/andP in H2. destruct H2.
  unfold option_map in H4.
  destruct (List.nth_error (s_globs s) i0) eqn:H5 => //=.
  simpl in Hi. simpl in Ht. inversion Hv. subst. clear Hv.
  move/eqP in H4. inversion H4.
  unfold global_agree in H7.
  move/andP in H7. destruct H7.
  by move/eqP in H7.
Qed.  
  
Lemma upd_label_unchanged: forall C lab,
    tc_label C = lab ->
    upd_label C lab = C.
Proof.
  move => C lab HLab.
  rewrite -HLab. unfold upd_label. by destruct C.
Qed.

Lemma upd_label_upd_local_return_combine: forall C loc lab ret,
    upd_label (upd_local_return C loc ret) lab =
    upd_local_label_return C loc lab ret.
Proof.
  by [].
Qed.  

Lemma set_nth_same_unchanged: forall {X:Type} (l:seq X) e i vd,
    List.nth_error l i = Some e ->
    set_nth vd l i e = l.
Proof.
  move => X l e i.
  generalize dependent l. generalize dependent e.
  induction i; move => e l vd HNth => //=.
  - destruct l => //=.
    simpl in HNth. by inversion HNth.
  - destruct l => //=.
    f_equal. apply IHi.
    by simpl in HNth.
Qed.

Lemma set_nth_map: forall {X Y:Type} (l:seq X) e i vd {f: X -> Y},
    i < size l ->
    map f (set_nth vd l i e) = set_nth (f vd) (map f l) i (f e).
Proof.
  move => X Y l e i.
  generalize dependent l. generalize dependent e.
  induction i; move => e l vd f HSize => //=.
  - by destruct l => //=.
  - destruct l => //=.
    f_equal.
    apply IHi.
    by simpl in HSize.
Qed.

Lemma n_zeros_typing: forall ts,
    map typeof (n_zeros ts) = ts.
Proof.
  induction ts => //=.
  by destruct a => //=; f_equal.
Qed.
  
Lemma inst_typing_reduce_exists: forall s vs es i s' vs' es' C,
    reduce s vs es i s' vs' es' ->
    inst_typing s i C ->
    exists C', inst_typing s' i C'.
Proof.
Admitted.

Lemma store_typing_reduce: forall s vs es i s' vs' es',
    reduce s vs es i s' vs' es' ->
    store_typing s ->
    store_typing s'.
Proof.
Admitted.

(* This is the only questionable lemma that I'm not >99% sure of it's correctness.
   But it seems to be absolutely required. Maybe I'm 98% sure. *)
Lemma store_reduce_same_es_typing: forall s vs es i s' vs' es' es0 C C' loc lab ret tf,
    reduce s vs es i s' vs' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s i C ->
    inst_typing s' i C' ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es0 tf ->
    e_typing s' (upd_label (upd_local_return C' loc ret) lab) es0 tf.
Proof.
Admitted.

Ltac convert_et_to_bet:=
  lazymatch goal with
  | H: e_typing _ _ _ _ |- _ =>
    apply et_to_bet in H; try auto_basic; simpl in H
  end.

Ltac split_et_composition:=
  lazymatch goal with
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let t3s := fresh "t3s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply e_composition_typing in H;
    destruct H as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]; subst
  end.

Ltac invert_e_typing:=
  repeat lazymatch goal with
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    split_et_composition
  | H: e_typing _ _ [::Label _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Label_typing in H;
    destruct H as [ts [t1s [H1 [H2 [H3 H4]]]]]; subst
  end.

Lemma lfilled_es_type_exists: forall k lh es les s C tf,
    lfilled k lh es les ->
    e_typing s C les tf ->
    exists lab t1s t2s, e_typing s (upd_label C lab) es (Tf t1s t2s).
Proof.
  move => k lh es les s C tf HLF.
  generalize dependent tf.
  generalize dependent C.
  move/lfilledP in HLF.
  induction HLF; move => C tf HType; destruct tf.
  - invert_e_typing.
    exists (tc_label C), t1s0, t3s0 => //=.
    by rewrite upd_label_unchanged.
  - invert_e_typing.
    edestruct IHHLF; first by apply H4.
    destruct H0 as [t1s' t2s'].
    by eauto.
Qed.    

Lemma t_preservation_vs_type: forall s vs es i s' vs' es' C C' lab ret t1s t2s,
    reduce s vs es i s' vs' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s i C ->
    inst_typing s' i C' ->
    e_typing s (upd_label (upd_local_return C (tc_local C ++ map typeof vs) ret) lab) es (Tf t1s t2s) ->
    map typeof vs = map typeof vs'.
Proof.
  move => s vs es i s' vs' es' C C' lab ret t1s t2s HReduce HST1 HST2 HIT1 HIT2 HType.
  generalize dependent t2s. generalize dependent t1s.
  generalize dependent lab.
  dependent induction HReduce => //; move => lab t1s t2s HType.
  - convert_et_to_bet.
    replace [::EConst v; Set_local j] with ([::EConst v] ++ [::Set_local j]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Set_local_typing in H10.
    destruct H10 as [t [H4 [H5 H6]]]. subst.
    apply concat_cancel_last in H5. destruct H5. subst.
    assert (tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.  
    rewrite H0 in H4. simpl in H4.
    rewrite H0 in H6. simpl in H6.
    rewrite length_is_size in H6. rewrite size_map in H6.
    rewrite set_nth_map => //.
    by rewrite set_nth_same_unchanged.
  - assert (exists lab' t1s' t2s', e_typing s (upd_label (upd_label (upd_local_return C (tc_local C ++ map typeof vs) ret) lab) lab') es (Tf t1s' t2s')); first eapply lfilled_es_type_exists; eauto.
    destruct H1 as [lab' [t1s' [t2s' H1]]].
    rewrite upd_label_overwrite in H1.
    by eapply IHHReduce; eauto.
Qed.

Lemma t_preservation_e: forall s vs es i s' vs' es' C C' t1s t2s lab ret,
    reduce s vs es i s' vs' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s i C ->
    inst_typing s' i C' ->
    e_typing s (upd_label (upd_local_return C (tc_local C ++ map typeof vs) ret) lab) es (Tf t1s t2s) ->
    e_typing s' (upd_label (upd_local_return C' (tc_local C' ++ map typeof vs') ret) lab) es' (Tf t1s t2s).
Proof.
  move => s vs es i s' vs' es' C C' t1s t2s lab ret HReduce HST1 HST2.
  generalize dependent t2s. generalize dependent t1s. 
  generalize dependent lab. generalize dependent ret.
  generalize dependent C'. generalize dependent C.
  dependent induction HReduce; move => C C' ret lab tx ty HIT1 HIT2 HType; subst; try eauto; try by apply ety_trap.
  - (* reduce_simple *)
    eapply t_simple_preservation; eauto.
    replace C' with C; last by eapply inst_typing_unique; eauto. clear HIT2.
    by apply HType.
  - (* Call *)
    replace C' with C; last by eapply inst_typing_unique; eauto. clear HIT2.
    convert_et_to_bet.
    apply Call_typing in HType.
    destruct HType as [ts [t1s' [t2s' [H1 [H2 [H3 H4]]]]]].
    subst. simpl in H1. simpl in H2.
    unfold sfunc in H.
    unfold option_bind in H.
    destruct (sfunc_ind s i j) eqn:HSF => //=.
    unfold sfunc_ind in HSF.
    apply ety_weakening.
    apply ety_invoke.
    assert ((Tf t1s' t2s') = cl_type f) as HFType; first by eapply tc_func_reference1; eauto.
    rewrite HFType.
    eapply store_typed_cl_typed; by eauto.
  - (* Call_indirect *)
    replace C' with C; last by eapply inst_typing_unique; eauto. clear HIT2.
    convert_et_to_bet.
    replace [::EConst (ConstInt32 c); Call_indirect j] with ([::EConst (ConstInt32 c)] ++ [::Call_indirect j]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]].
    subst.
    invert_be_typing.
    apply Call_indirect_typing in H4.
    destruct H4 as [tn [tm [ts [H5 [H6 [H7 [H8 H9]]]]]]].
    rewrite catA in H8. apply concat_cancel_last in H8. destruct H8. subst. clear H2.
    simpl in H5. simpl in H6. simpl in H7.
    repeat apply ety_weakening.
    apply ety_invoke.
    unfold stypes in H0.
    assert ((Tf tn tm) = cl_type cl) as HFType; first by eapply tc_func_reference2; eauto.
    rewrite HFType.
    unfold stab in H.
    destruct (i_tab i) eqn:HiTab => //.
    destruct (stab_s s i0 (Wasm_int.nat_of_uint i32m c)) eqn:Hstab => //.
    inversion H. subst. clear H.
    unfold stab_s in Hstab.
    unfold option_bind in Hstab.
    destruct (stab_index s i0 (Wasm_int.nat_of_uint i32m c)) eqn:Hstabi => //.
    unfold stab_index in Hstabi.
    unfold option_bind in Hstabi.
    destruct (List.nth_error (s_tab s) i0) eqn:HN1 => //.
    destruct (List.nth_error (table_data t) (Wasm_int.nat_of_uint i32m c)) eqn:HN2 => //.
    subst.
    eapply store_typed_cl_typed; by eauto.
  - (* Invoke native *)
    apply e_composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H5 [H6 [H7 H8]]]]]]].
    subst. 
    apply Invoke_func_native_typing in H8.
    destruct H8 as [ts2 [C2 [H9 [H10 [H11 H12]]]]]. subst.
    apply et_to_bet in H7; last by apply const_list_is_basic; apply v_to_e_is_const_list.
    apply Const_list_typing in H7.
    apply concat_cancel_last_n in H7; last by (repeat rewrite length_is_size in H2; rewrite size_map).
    move/andP in H7. destruct H7.
    move/eqP in H. move/eqP in H0. subst.
    simpl in H12.
    replace C' with C; last by eapply inst_typing_unique; eauto. clear HIT2.
    apply ety_weakening. apply et_weakening_empty_1.
    assert (tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
    rewrite H. simpl.
    apply ety_local => //.
    eapply mk_s_typing; eauto; last by apply/orP; left.
    apply ety_a'; auto_basic => //=.
    assert (tc_label C2 = [::]); first by eapply inst_t_context_label_empty; eauto.
    rewrite H0 in H12.
    apply bet_block. simpl.
    rewrite H0.
    rewrite upd_label_upd_local_return_combine.
    rewrite map_cat => //=.
    by rewrite n_zeros_typing.
  - (* Invoke host *)
    apply e_composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H5 [H6 [H7 H8]]]]]]].
    subst. 
    apply Invoke_func_host_typing in H8.
    destruct H8 as [ts [H8 H9]]. subst.
    apply et_to_bet in H7; last by apply const_list_is_basic; apply v_to_e_is_const_list.
    apply Const_list_typing in H7.
    apply concat_cancel_last_n in H7; last by (repeat rewrite length_is_size in H2; rewrite size_map).
    move/andP in H7. destruct H7.
    move/eqP in H. move/eqP in H0. subst.
    (* We require more knowledge of the host at this point. *)
    (* UPD: made it an axiom. *)
    assert (map typeof vcs' = t2s); first by eapply host_apply_typing; eauto.
    rewrite catA. apply et_weakening_empty_1.
    apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
    rewrite -H.
    by apply Const_list_typing_empty.
  - (* Get_local *)
    replace C' with C; last by eapply inst_typing_unique; eauto. clear HIT2.
    convert_et_to_bet.
    apply Get_local_typing in HType.
    destruct HType as [t [H1 [H2 H3]]]. subst.
    apply ety_a'; auto_basic => //=.
    assert (tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.  
    rewrite H in H1. rewrite H in H3. rewrite H.
    simpl in H1. simpl in H3. simpl.
    repeat rewrite map_cat in H1.
    simpl in H1. rewrite -cat1s in H1.
    replace (length vi) with (length (map typeof vi)) in H1; last by rewrite length_is_size; rewrite size_map.
    rewrite list_nth_prefix in H1. inversion H1. subst.
    apply bet_weakening_empty_1.
    by apply bet_const.
  - (* Set_local *)
    replace C' with C; last by eapply inst_typing_unique; eauto. clear HIT2.
    convert_et_to_bet.
    replace [::EConst v; Set_local j] with ([::EConst v] ++ [::Set_local j]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Set_local_typing in H10.
    destruct H10 as [t [H4 [H5 H6]]]. subst.
    apply ety_a'; auto_basic => //=.
    assert (tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.  
    rewrite H0 in H6. rewrite H0 in H4. rewrite H0.
    simpl in H6. simpl in H5. simpl in H4. simpl.
    apply concat_cancel_last in H5. destruct H5. subst.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Get_global *)
    replace C' with C; last by eapply inst_typing_unique; eauto. clear HIT2.
    convert_et_to_bet.
    apply Get_global_typing in HType.
    destruct HType as [t [H4 [H5 H6]]]. subst.
    apply ety_a'; auto_basic => //=.
    assert (tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.  
    rewrite H0 in H6. rewrite H0 in H4. rewrite H0.
    simpl in H6. simpl in H4. simpl.
    assert (typeof v = t); first by eapply global_type_reference; eauto.
    rewrite -H1.
    apply bet_weakening_empty_1.
    by apply bet_const.
  - (* Set_Global *)
    convert_et_to_bet.
    replace [::EConst v; Set_global j] with ([::EConst v] ++ [::Set_global j]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Set_global_typing in H10.
    destruct H10 as [t [H4 [H5 H6]]]. subst.
    apply ety_a'; auto_basic => //=.
    simpl in H6. simpl in H5. simpl in H4. simpl.
    apply concat_cancel_last in H5. destruct H5. subst.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Load None *)
    replace C' with C; last by eapply inst_typing_unique; eauto. clear HIT2.
    convert_et_to_bet.
    replace [::EConst (ConstInt32 k); Load t None a off] with ([::EConst (ConstInt32 k)] ++ [::Load t None a off]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Load_typing in H10.
    destruct H10 as [ts [n [H11 [H12 [H13 H14]]]]].
    apply concat_cancel_last in H11. destruct H11. subst.
    eapply t_const_ignores_context => //=.
    instantiate (2 := s).
    apply ety_a'; auto_basic.
    simpl.
    assert (be_typing C [::EConst (wasm_deserialise bs t)] (Tf [::] [:: typeof (wasm_deserialise bs t)])); first by apply bet_const.
    rewrite catA.
    apply bet_weakening_empty_1.
    rewrite typeof_deserialise in H2. by apply H2.
  - (* Load Some *)
    replace C' with C; last by eapply inst_typing_unique; eauto. clear HIT2.
    convert_et_to_bet.
    replace [::EConst (ConstInt32 k); Load t (Some (tp, sx)) a off] with ([::EConst (ConstInt32 k)] ++ [::Load t (Some (tp, sx)) a off]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Load_typing in H10.
    destruct H10 as [ts [n [H11 [H12 [H13 H14]]]]].
    apply concat_cancel_last in H11. destruct H11. subst.
    eapply t_const_ignores_context => //=.
    instantiate (2 := s).
    apply ety_a'; auto_basic.
    simpl.
    assert (be_typing C [::EConst (wasm_deserialise bs t)] (Tf [::] [:: typeof (wasm_deserialise bs t)])); first by apply bet_const.
    rewrite catA. apply bet_weakening_empty_1.
    rewrite typeof_deserialise in H2. by apply H2.
  - (* Store None *)
    + convert_et_to_bet.
      simpl in HType.
      replace [::EConst (ConstInt32 k); EConst v; Store t None a off] with ([::EConst (ConstInt32 k); EConst v] ++ [::Store t None a off]) in HType => //=.
      apply composition_typing in HType.
      destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
      invert_be_typing.
      apply Store_typing in H10.
      destruct H10 as [n [H11 [H12 H13]]].
      apply concat_cancel_last_n in H11 => //.
      move/andP in H11. destruct H11. move/eqP in H3. subst.
      apply ety_a'; auto_basic => //=.
      apply bet_weakening_empty_both.
      by apply bet_empty.
  - (* Store Some *)
    + convert_et_to_bet.
      simpl in HType.
      replace [::EConst (ConstInt32 k); EConst v; Store t (Some tp) a off] with ([::EConst (ConstInt32 k); EConst v] ++ [::Store t (Some tp) a off]) in HType => //=.
      apply composition_typing in HType.
      destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
      invert_be_typing.
      apply Store_typing in H10.
      destruct H10 as [n [H11 [H12 H13]]].
      apply concat_cancel_last_n in H11 => //.
      move/andP in H11. destruct H11. move/eqP in H3. subst.
      apply ety_a'; auto_basic => //.
      apply bet_weakening_empty_both.
      by apply bet_empty.
  - (* Current_memory *)
    convert_et_to_bet.
    apply Current_memory_typing in HType.
    destruct HType as [n [H5 H6]]. subst.
    simpl.
    apply ety_a'; auto_basic.
    apply bet_weakening_empty_1.
    by apply bet_const.
  - (* Grow_memory success *)
    convert_et_to_bet.
    replace [::EConst (ConstInt32 c); Grow_memory] with ([::EConst (ConstInt32 c)] ++ [::Grow_memory]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Grow_memory_typing in H10.
    destruct H10 as [ts [n [H11 [H12 H13]]]]. subst.
    simpl.
    apply ety_a'; auto_basic.
    rewrite catA.
    apply bet_weakening_empty_1.
    by apply bet_const.
  - (* Grow_memory fail *)
    convert_et_to_bet.
    replace [::EConst (ConstInt32 c); Grow_memory] with ([::EConst (ConstInt32 c)] ++ [::Grow_memory]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Grow_memory_typing in H10.
    destruct H10 as [ts [n [H11 [H12 H13]]]]. subst.
    simpl.
    apply ety_a'; auto_basic.
    rewrite catA.
    apply bet_weakening_empty_1.
    by apply bet_const.
  (* From the structure, it seems that some form of induction is required to prove these
   2 cases. *)
  - (* r_label *)
    generalize dependent lh. generalize dependent les. generalize dependent les'.
    generalize dependent ty. generalize dependent tx. generalize dependent lab.
    induction k; move => lab tx ty les' les HType lh HLF1 HLF2; move/lfilledP in HLF1; move/lfilledP in HLF2.
    + inversion HLF1. inversion HLF2. subst. clear HLF1. clear HLF2.
      inversion H5. subst. clear H5. clear H0.
      apply e_composition_typing in HType.
      destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]]. subst.
      apply e_composition_typing in H5.
      destruct H5 as [ts1 [t1s1 [t2s1 [t3s1 [H6 [H7 [H8 H9]]]]]]]. subst.
      eapply et_composition'.
      -- instantiate (1 := ts0 ++ ts1 ++ t1s1).
         apply ety_weakening.
         by eapply t_const_ignores_context; eauto.
      -- eapply et_composition'; eauto.
         ++ instantiate (1 := ts0 ++ ts1 ++ t3s1).
            repeat apply ety_weakening.
            by eapply IHHReduce; eauto => //.
         ++ repeat apply ety_weakening.
            eapply store_reduce_same_es_typing; eauto.
            assert (tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto. 
            assert (tc_local C' = [::]); first by eapply inst_t_context_local_empty; eauto. 
            rewrite H0 in H9. rewrite H1.
            replace (map typeof vs') with (map typeof vs) => //.
            by eapply t_preservation_vs_type; eauto.
    + inversion HLF1. inversion HLF2. subst.
      inversion H8. subst. clear H8.
      move/lfilledP in H1. move/lfilledP in H7.
      apply e_composition_typing in HType.
      destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]]. subst.
      apply e_composition_typing in H5.
      destruct H5 as [ts1 [t1s1 [t2s1 [t3s1 [H8 [H9 [H10 H11]]]]]]]. subst.
      apply Label_typing in H10.
      destruct H10 as [ts2 [t2s2 [H12 [H13 [H14 H15]]]]]. subst.
      eapply et_composition'.
      -- instantiate (1 := ts0 ++ ts1 ++ t1s1).
         apply ety_weakening.
         by eapply t_const_ignores_context; eauto.
      -- eapply et_composition'; eauto.
         ++ instantiate (1 := ts0 ++ ts1 ++ t1s1 ++ t2s2).
            repeat apply ety_weakening.
            apply et_weakening_empty_1.
            eapply ety_label; eauto.
            * eapply store_reduce_same_es_typing; eauto.
              assert (tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto. 
              assert (tc_local C' = [::]); first by eapply inst_t_context_local_empty; eauto. 
              rewrite H in H13. rewrite H2.
              simpl in H14. rewrite upd_label_overwrite in H14.
              eapply lfilled_es_type_exists in H14; eauto.
              destruct H14 as [lab' [t1s' [t2s' H14]]].
              rewrite upd_label_overwrite in H14.
              replace (map typeof vs') with (map typeof vs) => //.
              by eapply t_preservation_vs_type; eauto.
            * simpl.
              simpl in H14.
              by eapply IHk; eauto.
         ++ repeat apply ety_weakening.
            eapply store_reduce_same_es_typing; eauto.
            assert (tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto. 
            assert (tc_local C' = [::]); first by eapply inst_t_context_local_empty; eauto. 
            rewrite H in H11. rewrite H2.
            simpl in H14. rewrite upd_label_overwrite in H14.
            eapply lfilled_es_type_exists in H14; eauto.
            destruct H14 as [lab' [t1s' [t2s' H14]]].
            rewrite upd_label_overwrite in H14.
            replace (map typeof vs') with (map typeof vs) => //.
            by eapply t_preservation_vs_type; eauto. 
  - (* r_local *)
    apply Local_typing in HType.
    destruct HType as [ts [H1 [H2 H3]]]. subst.
    apply et_weakening_empty_1.
    eapply ety_local => //.
    inversion H2. subst.
    assert (exists C1', inst_typing s' i C1'); first by eapply inst_typing_reduce_exists; eauto. destruct H0 as [C1' H0].
    eapply mk_s_typing; eauto.
    assert (e_typing s' (upd_label (upd_local_return C1' (tc_local C1' ++ map typeof vs') (Some ts)) [::]) es' (Tf [::] ts)).
    eapply IHHReduce; eauto.
    assert (tc_label C1 = [::]); first by eapply inst_t_context_label_empty; eauto.
    assert (tc_label (upd_local_return C1 (tc_local C1 ++ map typeof vs) (Some ts)) = [::]) => //.
    rewrite upd_label_unchanged => //=.
    rewrite upd_label_unchanged in H4 => //=.
    by eapply inst_t_context_label_empty; eauto.
Qed.
    
Lemma t_preservation: forall s vs es i s' vs' es' ts,
    reduce s vs es i s' vs' es' ->
    config_typing i s vs es ts ->
    config_typing i s' vs' es' ts.
Proof.
  move => s vs es i s' vs' es' ts HReduce HType.
  inversion HType. inversion H0. subst.
  assert (store_typing s'); first by eapply store_typing_reduce; eauto.
  assert (exists C', inst_typing s' i C'); first by eapply inst_typing_reduce_exists; eauto. destruct H2.
  apply mk_config_typing; eauto.
  eapply mk_s_typing; eauto.
  eapply t_preservation_e; eauto.
  assert (tc_label C0 = [::]); first by eapply inst_t_context_label_empty; eauto.
  assert (tc_label (upd_local_return C0 (tc_local C0 ++ map typeof vs) (Some ts)) = [::]) => //.
  assert (tc_label x = [::]); first by eapply inst_t_context_label_empty; eauto.
  rewrite upd_label_unchanged => //=.
  by rewrite H3.
Qed.
  
