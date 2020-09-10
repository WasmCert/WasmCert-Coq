Require Import common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Program.Equality.

Require Import NArith.

Require Import Omega.

Require Import operations typing type_checker datatypes_properties typing opsem properties.

Section Host.

Variable host_function : eqType.

Let store_record := store_record host_function.
Let function_closure := function_closure host_function.
Let administrative_instruction := administrative_instruction host_function.

Let to_e_list : seq basic_instruction -> seq administrative_instruction := @to_e_list _.
Let to_b_list : seq administrative_instruction -> seq basic_instruction := @to_b_list _.
Let e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
  @e_typing _.
Let reduce_simple : seq administrative_instruction -> seq administrative_instruction -> Prop :=
  @reduce_simple _.
Let const_list : seq administrative_instruction -> bool := @const_list _.
Let lholed := lholed host_function.
Let lfilled : depth -> lholed -> seq administrative_instruction -> seq administrative_instruction -> bool :=
  @lfilled _.
Let sfunc : store_record -> instance -> nat -> option function_closure := @sfunc _.
Let sglob : store_record -> instance -> nat -> option global := @sglob _.
Let smem_ind : store_record -> instance -> option nat := @smem_ind _.

Let host := host host_function.

Variable host_instance : host.

Let host_state := host_state host_instance.

Let reduce : host_state -> store_record -> seq value -> seq administrative_instruction -> instance ->
             host_state -> store_record -> seq value -> seq administrative_instruction -> Prop
  := @reduce _ _.


Definition t_be_value bes : Prop :=
  const_list (to_e_list bes).

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
  repeat rewrite size_cat in H.
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

Lemma list_nth_prefix: forall {X:Type} (l1 l2: seq X) x,
    List.nth_error (l1 ++ [::x] ++ l2) (length l1) = Some x.
Proof.
  move => X. induction l1 => //=.
Qed.

Lemma inP: forall {X:eqType} (x:X) l,
    reflect (List.In x l) (x \in l).
Proof.
  move => X x l.
  induction l => //=.
  - rewrite in_nil. by apply ReflectF.
  - rewrite in_cons. destruct IHl.
    + rewrite orbT. apply ReflectT. by right.
    + rewrite orbF. eapply iffP; first by apply eqP.
      * by left.
      * by inversion 1.
Defined.

(** Perform an induction over [be_typing], generalising its parameter.
  The reason for this tactic is that [dependent induction] is far too aggressive
  in its generalisation, and prevents the use of some lemmas. **)
Ltac be_typing_ind H :=
  let rec try_generalize t :=
    lazymatch t with
    | ?f ?x => try_generalize f; try_generalize x
    | ?x => is_variable x ltac:(generalize x) ltac:(idtac)
    end in
  lazymatch type of H with
  | be_typing ?C ?l ?t =>
    move: H;
    let C' := fresh "C" in
    let l' := fresh "l" in
    let t' := fresh "t" in
    set_eq C' C;
    move=> + H;
    try_generalize C;
    move: H;
    set_eq l' l;
    move=> + H;
    try_generalize l;
    move: H;
    set_eq t' t;
    move=> + H;
    try_generalize t;
    induction H;
    repeat lazymatch goal with
    | |- _ = _ -> _ => inversion 1
    | |- _ -> _ => intro
    end
  end.

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
  be_typing_ind HType; subst => //=.
  - by destruct es.
  - f_equal. by eapply IHHType.
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
  be_typing_ind HType; subst => //=.
  - apply extract_list1 in H2; inversion H2; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.

Lemma EConst2_typing: forall C econst1 econst2 t1s t2s,
    be_typing C [::EConst econst1; EConst econst2] (Tf t1s t2s) ->
    t2s = t1s ++ [::typeof econst1; typeof econst2].
Proof.
  move => C econst1 econst2 t1s t2s HType.
  be_typing_ind HType; subst => //=.
  - apply extract_list2 in H2; inversion H2; subst.
    apply EConst_typing in HType1; subst.
    apply EConst_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.

Lemma EConst3_typing: forall C econst1 econst2 econst3 t1s t2s,
    be_typing C [::EConst econst1; EConst econst2; EConst econst3] (Tf t1s t2s) ->
    t2s = t1s ++ [::typeof econst1; typeof econst2; typeof econst3].
Proof.
  move => C econst1 econst2 econst3 t1s t2s HType.
  be_typing_ind HType; subst => //=.
  - apply extract_list3 in H2; inversion H2; subst.
    apply EConst2_typing in HType1; subst.
    apply EConst_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
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
    rewrite -v_to_e_cat /to_b_list.
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
    exists (ts ++ x), x1. by split => //=; repeat rewrite -catA.
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
  + replace (to_b_list (operations.to_e_list bes)) with bes => //.
    by apply b_e_elim.
  + rewrite /to_b_list to_b_list_concat.
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

Hint Constructors be_typing : core.

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
    by repeat split => //=; rewrite -catA.
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
      eapply bet_composition; eauto.
      by apply bet_weakening.
Qed.

(* FIXME: [Variable p should be bound to a term but is bound to a ident] error.
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
    by repeat split => //=; apply ety_a' => //=.
  - (* composition *)
    apply concat_cancel_last in x. destruct x. subst.
    by exists [::], t1s, t2s, t2s0.
  - (* weakening *)
    edestruct IHHType; eauto.
    destruct H as [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]. subst.
    exists (ts ++ x), t1s', t2s', t3s'.
    by repeat split => //; rewrite catA.
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
*)

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
    rewrite /to_b_list to_b_list_concat in HType.
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
    reduce_simple (to_e_list [::EConst v1; EConst v2; Binop_i (typeof v2) iop]) (to_e_list [::be]) ->
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
    reduce_simple (to_e_list [::EConst v1; EConst v2; Binop_f (typeof v2) fop]) (to_e_list [::be]) ->
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

Lemma typeof_deserialise: forall v t,
  typeof (wasm_deserialise v t) = t.
Proof.
  move=> v. by case.
Qed.

(* FIXME: This axiom no longer makes sense in this branch.
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
  inversion HReduce; subst. rename H5 into E.
  dependent induction HType; subst.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    by destruct t2; simpl in E;
      match type of E with
        option_map _ ?e = _ => destruct e eqn:HDestruct => //=
      end; inversion E; apply bet_const.
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
      -- apply H2. rewrite mem_cat. apply/orP. left. apply/inP.
         eapply List.nth_error_In. by eauto.
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
    by unfold e_is_basic; exists e
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
    { rewrite Heqtss'. rewrite cat1s. simpl. by rewrite addn1. }
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
    by eapply Local_return_typing; eauto.
  - (* Tee_local -- actually a simple reduction *)
    destruct v => //.
    destruct b => //.
    apply et_to_bet in HType => //; auto_basic.
    apply ety_a' => //; auto_basic.
    by eapply t_be_simple_preservation; try by eauto; auto_basic.
Qed.

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
    exists tn tm ts, tc_table C <> nil /\
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

Lemma globs_agree_function: forall s,
    function (globals_agree (s_globals s)).
Proof.
  move => s. unfold function. move => x y1 y2 [H1 H2].
  unfold globals_agree in H1. unfold globals_agree in H2.
  remove_bools_options.
  unfold global_agree in H3. unfold global_agree in H4.
  remove_bools_options.
  destruct y1; destruct y2 => //.
  simpl in H0. simpl in H2. simpl in H3. simpl in H4. by subst.
Qed.

Lemma functions_agree_function: forall s,
    function (functions_agree (s_funcs s)).
Proof.
  move => s. unfold function. move => x y1 y2 [H1 H2].
  unfold functions_agree in H1. unfold functions_agree in H2.
  by remove_bools_options.
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
    by repeat split => //; rewrite catA.
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
    exists g t, List.nth_error (tc_global C) i = Some g /\
    tg_t g = t /\
    is_mut g /\
    t1s = t2s ++ [::t] /\
    i < length (tc_global C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists g, (tg_t g).
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [t [H1 [H2 [H3 [H4 H5]]]]]. subst.
    exists x, (tg_t x).
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Load_typing: forall C t a off tp_sx t1s t2s,
    be_typing C [::Load t tp_sx a off] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_i32] /\ t2s = ts ++ [::t] /\
                    tc_memory C <> nil /\
                    load_store_t_bounds a (option_projl tp_sx) t.
Proof.
  move => C t a off tp_sx t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::].
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 [H3 H4]]]. subst.
    exists (ts ++ x).
    by repeat rewrite -catA.
Qed.

Lemma Store_typing: forall C t a off tp t1s t2s,
    be_typing C [::Store t tp a off] (Tf t1s t2s) ->
    t1s = t2s ++ [::T_i32; t] /\
    tc_memory C <> nil /\
    load_store_t_bounds a tp t.
Proof.
  move => C t a off tp t1s t2s HType.
  dependent induction HType; subst => //=.
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=. subst.
    by repeat rewrite -catA.
Qed.

Lemma Current_memory_typing: forall C t1s t2s,
    be_typing C [::Current_memory] (Tf t1s t2s) ->
    tc_memory C <> nil /\ t2s = t1s ++ [::T_i32].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=. subst.
    by repeat rewrite -catA.
Qed.

Lemma Grow_memory_typing: forall C t1s t2s,
    be_typing C [::Grow_memory] (Tf t1s t2s) ->
    exists ts, tc_memory C <> nil /\ t2s = t1s /\ t1s = ts ++ [::T_i32].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::].
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists (ts ++ x).
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
  remove_bools_options.
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
  by destruct tc_local; destruct tc_label.
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
  destruct (List.nth_error (s_globals s) g) eqn:Hv => //=.
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
  destruct (List.nth_error (s_globals s) g) eqn:H5 => //=.
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

Lemma upd_label_unchanged_typing: forall s C es tf,
    e_typing s C es tf ->
    e_typing s (upd_label C (tc_label C)) es tf.
Proof.
  move => s C es tf HType.
  by rewrite upd_label_unchanged.
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

Lemma global_agree_extension: forall g0 g1 g,
    global_agree g0 g ->
    glob_extension g0 g1 ->
    global_agree g1 g.
Proof.
  move => g0 g1 g H1 H2.
  unfold global_agree.
  unfold global_agree in H1. unfold glob_extension in H2.
  destruct g => //=.
  destruct g0 => //=.
  destruct g1 => //=.
  simpl in H2. simpl in H1.
  by destruct g_mut => //=; remove_bools_options; apply/andP => //=; subst; split => //=; destruct g_mut0 => //=; destruct g_val => //=; destruct g_val0 => //=.
Qed.

Lemma glob_extension_C: forall sg sg' ig tcg,
    all2 (globals_agree sg) ig tcg ->
    all2 glob_extension sg sg' ->
    all2 (globals_agree sg') ig tcg.
Proof.
  move => sg sg' ig.
  generalize dependent sg; generalize dependent sg'.
  induction ig; move => sg' sg tcg HA Hext => //=; destruct tcg => //=.
  - simpl in HA. remove_bools_options.
    edestruct IHig; eauto.
    unfold globals_agree in H. remove_bools_options.
    assert (size sg = size sg'); first by eapply all2_size; eauto.
    assert (a < length sg')%coq_nat.
    {
        rewrite length_is_size in H. rewrite length_is_size.
        rewrite -H1. by lias.
    }
    remember H2 as H5. clear HeqH5.
    rewrite <- List.nth_error_Some in H2.
    destruct (List.nth_error sg' a) eqn:HGlob => //=; eauto. clear H2.
    remember Hext as Hext1. clear HeqHext1.
    eapply all2_projection in Hext1; eauto.
    apply/andP. split => //=.
    + unfold globals_agree. apply/andP; split => //=; first by lias.
      unfold option_map. rewrite HGlob.
      apply/eqP. f_equal.
      by eapply global_agree_extension; eauto.
    + by eapply IHig; eauto.
Qed.

(* NOTE: weird behaviour in this lemma *)

Lemma memi_agree_extension: forall m0 m1 n m,
    memi_agree m0 n m ->
    all2 mem_extension m0 m1 ->
    memi_agree m1 n m.
Proof.
  move => m0 m1 n m H1 H2.
  assert (size m0 = size m1) as HSize; first by eapply all2_size; eauto.
  unfold memi_agree.
  unfold memi_agree in H1. unfold mem_extension in H2.
  destruct m => //=.
  remove_bools_options.
  rewrite length_is_size in H.
  apply/andP; split => //=; first by rewrite HSize in H.
  rewrite HSize in H.
  rewrite -length_is_size in H.
  move/ltP in H.
  rewrite <- List.nth_error_Some in H.
  destruct (List.nth_error m1 n) eqn:HN => //=.
  unfold mem_typing. simpl.
  (* eauto is unbearably slow for some reason. *)
  eapply all2_projection in H2; [| by apply Hoption | by apply HN ].
  unfold mem_typing in H0. simpl in H0.
  remove_bools_options.
  apply/andP; split.
  (* even auto takes incredibly long... lias takes shorter somehow *)
  - by lias.
  (* it seems that any automatic tactic takes very long *)
  - rewrite H3 in H2. rewrite H2. by apply/eqP.
Qed.

Lemma mem_extension_C: forall sm sm' im tcm,
    all2 (memi_agree sm) im tcm ->
    all2 mem_extension sm sm' ->
    all2 (memi_agree sm') im tcm.
Proof.
  move => sm sm' im.
  generalize dependent sm; generalize dependent sm'.
  induction im; move => sm' sm tcm HA Hext => //=; destruct tcm => //=.
  simpl in HA. remove_bools_options.
  apply/andP; split => //=; last by eapply IHim; eauto.
  by eapply memi_agree_extension; eauto.
Qed.

Lemma tabi_agree_extension: forall t0 t1 n t,
    tabi_agree t0 n t ->
    all2 tab_extension t0 t1 ->
    tabi_agree t1 n t.
Proof.
  move => t0 t1 n t H1 H2.
  assert (size t0 = size t1) as HSize; first by eapply all2_size; eauto.
  unfold tabi_agree.
  unfold tabi_agree in H1. unfold tab_extension in H2.
  unfold tab_size in H2.
  destruct t => //=.
  destruct t0 => //=.
  destruct t1 => //=.
  simpl in H2. simpl in H1.
  remove_bools_options.
  unfold tab_typing in H3.
  remove_bools_options.
  simpl in H3. simpl in H4.
  unfold tab_typing. simpl.
  simpl in HSize. inversion HSize. subst. clear HSize.
  apply/andP; split => //=.
  - rewrite length_is_size in H1. rewrite length_is_size. by rewrite H6 in H1.
  - assert (List.nth_error (t1 :: t2) n <> None).
    { apply List.nth_error_Some. rewrite length_is_size. simpl. rewrite -H6.
      by lias. }
    destruct (List.nth_error (t1 :: t2) n) eqn:HN => //=.
    destruct n => //=.
    + simpl in HN. simpl in Hoption. inversion HN. inversion Hoption. subst.
      apply/andP; split => //=; last by rewrite -H2.
      unfold tab_size. unfold tab_size in H3. by lias.
    + simpl in HN. simpl in Hoption.
      eapply all2_projection in H0; eauto.
      remove_bools_options.
      apply/andP; split => //=; last by rewrite -H7.
      unfold tab_size. unfold tab_size in H3. by lias.
Qed.

Lemma tab_extension_C: forall st st' it tct,
    all2 (tabi_agree st) it tct ->
    all2 tab_extension st st' ->
    all2 (tabi_agree st') it tct.
Proof.
  move => st st' it.
  generalize dependent st; generalize dependent st'.
  induction it; move => st' st tct HA Hext => //=; destruct tct => //=.
  simpl in HA. remove_bools_options.
  apply/andP; split => //=; last by eapply IHit; eauto.
  by eapply tabi_agree_extension; eauto.
Qed.

Lemma inst_typing_extension: forall s s' i C,
    store_extension s s' ->
    inst_typing s i C ->
    inst_typing s' i C.
Proof.
  move => s s' i C HST HIT.
  unfold store_extension in HST. unfold inst_typing in HIT.
  unfold inst_typing.
  destruct i => //=.
  destruct C => //=.
  destruct tc_local => //. destruct tc_label => //. destruct tc_return => //.
  remove_bools_options; rewrite -H4.
  repeat (apply/andP; split => //=; subst => //=).
  - by eapply glob_extension_C; eauto.
  - by eapply tab_extension_C; eauto.
  - by eapply mem_extension_C; eauto.
Qed.

Lemma reflexive_all2_same: forall {X:Type} f (l: seq X),
    reflexive f ->
    all2 f l l.
Proof.
  move => X f l.
  induction l; move => H; unfold reflexive in H => //=.
  apply/andP. split => //=.
  by apply IHl.
Qed.

Lemma all2_tab_extension_same: forall t,
    all2 tab_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. move => x. unfold tab_extension.
  by apply/andP.
Qed.

Lemma all2_mem_extension_same: forall t,
    all2 mem_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. move => x. unfold mem_extension.
  by apply/andP.
Qed.

Lemma all2_glob_extension_same: forall t,
    all2 glob_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. move => x. unfold glob_extension.
  destruct (g_mut x) => //=.
  by destruct (g_val x).
Qed.

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

Lemma store_extension_same: forall s,
    store_extension s s.
Proof.
  move => s. unfold store_extension.
  repeat (apply/andP; split).
  + by apply/eqP.
  + by apply all2_tab_extension_same.
  + by apply all2_mem_extension_same.
  + by apply all2_glob_extension_same.
Qed.

(* This is the only questionable lemma that I'm not >99% sure of it's correctness.
   But it seems to be absolutely required. Maybe I'm 98% sure. *)
(*
   UPD: oops, this is in fact completely nonsense and in no way required --
          I overlooked another possibility here. This is now abandoned and
          replaced by a correct version.

Lemma store_reduce_same_es_typing: forall s vs es i s' vs' es' es0 C C' loc lab ret tf,
    reduce s vs es i s' vs' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s i C ->
    inst_typing s' i C' ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es0 tf ->
    e_typing s' (upd_label (upd_local_return C' loc ret) lab) es0 tf.
Proof.
 *)

Lemma store_extension_cl_typing: forall s s' cl tf,
    store_extension s s' ->
    cl_typing s cl tf ->
    cl_typing s' cl tf.
Proof.
  move => s s' cl tf Hext HType.
  inversion HType; subst.
  - eapply cl_typing_native; eauto.
    by eapply inst_typing_extension; eauto.
  - by eapply cl_typing_host; eauto.
Qed.

(*
  The correct version. We need a mutual induction on e_typing and s_typing
    since they were defined with a mutual induction.
 *)

Lemma store_extension_e_typing: forall s s' C es tf,
    store_typing s ->
    store_typing s' ->
    store_extension s s' ->
    e_typing s C es tf -> e_typing s' C es tf.
Proof.
  move=> s s' C es tf HST1 HST2 Hext HType. move: s' HST1 HST2 Hext.
  apply e_typing_ind' with (e := HType)
    (P := fun s C es tf (_ : e_typing s C es tf) => forall s',
            store_typing s ->
            store_typing s' ->
            store_extension s s' ->
            e_typing s' C es tf)
    (P0 := fun s rs i vs es ts (_ : s_typing s rs i vs es ts) => forall s',
             store_typing s ->
             store_typing s' ->
             store_extension s s' ->
             s_typing s' rs i vs es ts); clear.
  - move=> s C bes tf HType s' HST1 HST2 Hext.
    apply ety_a'; first by apply to_e_list_basic.
    replace (to_b_list (to_e_list bes)) with bes => //.
    by apply b_e_elim.
  - move=> s C bes tf r1 r2 r3 HType1 IHHType1 IH2 IHHType2 s' HST1 HST2 Hext.
    eapply ety_composition.
    + by apply IHHType1.
    + by apply IHHType2.
  - move=> s C es tf t1s t2s HType IHHType s' HST1 HST2 Hext.
    eapply ety_weakening. by apply IHHType.
  - move=> s C tf s' HST1 HST2 Hext.
    by apply ety_trap.
  - move=> s C es tf vs es' vts HType IHHType E s' HST1 HST2 Hext.
    apply ety_local => //.
    by eapply IHHType; try apply HST1 => //.
  - move=> s C cl tf Cl s' HST1 HST2 Hext.
    apply ety_invoke => //.
    by eapply store_extension_cl_typing; eauto.
  - move=> s C es es' t1s t2s n HType1 IHHType1 HType2 IHHType2 E s' HST1 HST2 Hext.
    by eapply ety_label => //; eauto.
  - move=> s i vs es rs ts C C' tvs Inst E HType IHHType E' s' HST1 HST2 Hext.
    eapply mk_s_typing; eauto.
    by eapply inst_typing_extension; eauto.
Defined.

Lemma glob_extension_update_nth: forall sglobs n g g',
  List.nth_error sglobs n = Some g ->
  glob_extension g g' ->
  all2 glob_extension sglobs (update_list_at sglobs n g').
Proof.
  move => sglobs n.
  generalize dependent sglobs.
  induction n; move => sglobs g g' HN Hext => //=; destruct sglobs => //.
  - simpl in HN. inversion HN. subst.
    apply/andP; split => //=.
    by apply all2_glob_extension_same.
  - assert ((n.+1 < length (g0 :: sglobs))%coq_nat); first by rewrite -List.nth_error_Some; rewrite HN.
    rewrite -update_list_at_is_set_nth; last by lias.
    simpl.
    apply/andP. split.
    + unfold glob_extension. destruct (g_mut g0) => //=. by destruct (g_val g0).
    + rewrite update_list_at_is_set_nth.
      * by eapply IHn; eauto.
      * simpl in H. rewrite length_is_size in H. by lias.
Qed.

Lemma tc_reference_glob_type: forall s i C n m gt g,
    inst_typing s i C ->
    List.nth_error (i_globs i) n = Some m ->
    List.nth_error (s_globals s) m = Some g ->
    List.nth_error (tc_global C) n = Some gt ->
    global_agree g gt.
Proof.
  move => s i C n m gt g HIT HN1 HN2 HN3.
  unfold inst_typing in HIT.
  destruct i => //=.
  destruct C => //=.
  destruct tc_local => //=.
  destruct tc_label => //=.
  destruct tc_return => //=.
  remove_bools_options.
  eapply all2_projection in H2; eauto.
  unfold globals_agree in H2.
  by remove_bools_options.
Qed.

(* same here *)

Lemma mem_extension_update_nth: forall smems n m m',
  List.nth_error smems n = Some m ->
  mem_extension m m' ->
  all2 mem_extension smems (update_list_at smems n m').
Proof.
  move => smems n.
  generalize dependent smems.
  induction n; move => smems m m' HN Hext => //=; destruct smems => //.
  - simpl in HN. inversion HN. subst.
    apply/andP. split; first apply Hext.
   by apply all2_mem_extension_same.
  - assert ((n.+1 < length (m0 :: smems))%coq_nat); first by rewrite -List.nth_error_Some; rewrite HN.
    rewrite -update_list_at_is_set_nth; last by lias.
    (* it seems that simpl is the culprit? *)
    simpl.
    apply/andP. split.
    + unfold mem_extension. by lias.
    + rewrite update_list_at_is_set_nth.
      * by eapply IHn; eauto.
      * simpl in H. rewrite length_is_size in H. by lias.
Qed.

Lemma bytes_takefill_size: forall c l vs,
    size (bytes_takefill c l vs) = l.
Proof.
  move => c l. induction l => //=.
  by destruct vs => //=; f_equal.
Qed.

Lemma bytes_replicate_size: forall n b,
    size (bytes_replicate n b) = n.
Proof.
  induction n => //=.
  by move => b; f_equal.
Qed.


Lemma div_le: forall a b, b > 0 -> a/b <= a.
Proof.
  move => a b H.
  destruct b => //.
  destruct b => //; first by rewrite Nat.div_1_r; lias.
  destruct a => //.
  assert (a.+1/b.+2 < a.+1)%coq_nat.
  { apply Nat.div_lt; omega. (* lias doesn't solve this. *) }
  by lias.
Qed.

Lemma mem_extension_store: forall m k off v tlen mem,
    store m k off (bits v) tlen = Some mem ->
    mem_extension m mem.
Proof.
  move => m k off v tlen mem HStore.
  unfold mem_extension.
  unfold store in HStore.
  destruct ((k + off + N.of_nat tlen <=? mem_length m)%N) eqn:HMemSize => //.
  inversion HStore; clear HStore.
  by apply/andP; split => //=.
Qed.

Lemma mem_extension_grow_memory: forall m c mem,
    mem_grow m c = (Some mem) ->
    mem_extension m mem.
Proof.
  move => m c mem HMGrow.
  unfold mem_extension.
  unfold mem_grow in HMGrow.
  destruct (lim_max (mem_limit m)) eqn:HLimMax => //=.
  - destruct ((mem_size m + c <=? n)%N) eqn:HLT => //.
    inversion HMGrow; subst; clear HMGrow.
    apply/andP; split => //.
    by apply/eqP.
  - inversion HMGrow; subst; clear HMGrow.
    apply/andP; split => //.
    by apply/eqP.
Qed.

Lemma store_global_extension_store_typed: forall s s',
    store_typing s ->
    store_extension s s' ->
    (s_funcs s = s_funcs s') ->
    (s_tables s = s_tables s') ->
    (s_mems s = s_mems s') ->
    store_typing s'.
Proof.
  move => s s' HST Hext HF HT.
  remember HST as HST'. clear HeqHST'.
  unfold store_typing in HST.
  unfold store_typing.
  destruct s => //=.
  destruct s' => //=.
  destruct HST.
  rewrite -> List.Forall_forall in H.
  rewrite -> List.Forall_forall in H0.
  split => //; remove_bools_options; simpl in HF; simpl in HT; subst.
  - rewrite -> List.Forall_forall. move => x HIN.
    apply H in HIN. unfold cl_type_check_single in HIN.
    destruct HIN.
    unfold cl_type_check_single.
    exists x0. by eapply store_extension_cl_typing; eauto.
  - split => //.
    + rewrite -> List.Forall_forall. move => x HIN.
      apply H0 in HIN. unfold tab_agree in HIN.
      destruct HIN.
      rewrite -> List.Forall_forall in H1.
      unfold tab_agree.
      rewrite -> List.Forall_forall.
      split => //=.
      move => x' HIN'.
      apply H1 in HIN'.
      unfold tabcl_agree in HIN'.
      unfold tabcl_agree.
      destruct x' => //=.
      simpl in HIN'. destruct (List.nth_error s_funcs0 n) => //=.
      unfold cl_type_check_single in HIN'.
      destruct HIN'.
      unfold cl_type_check_single.
      exists x0. by eapply store_extension_cl_typing; eauto.
    + unfold store_extension in Hext. simpl in Hext.
      remove_bools_options.
      rewrite List.Forall_forall.
      move => x HIN.
      destruct HST' as [_ [_ H8]].
      rewrite -> List.Forall_forall in H8.
      apply List.In_nth_error in HIN.
      destruct HIN as [n HN].
      apply H8. by eapply List.nth_error_In; eauto.
Qed.

Lemma store_memory_extension_store_typed: forall s s',
    store_typing s ->
    store_extension s s' ->
    (s_funcs s = s_funcs s') ->
    (s_tables s = s_tables s') ->
    List.Forall mem_agree (s_mems s') ->
    store_typing s'.
Proof.
  move => s s' HST Hext HF HT HMem.
  remember HST as HST'. clear HeqHST'.
  unfold store_typing in HST.
  unfold store_typing.
  destruct s => //=.
  destruct s' => //=.
  destruct HST.
  rewrite -> List.Forall_forall in H.
  rewrite -> List.Forall_forall in H0.
  split => //; remove_bools_options; simpl in HF; simpl in HT; subst.
  - rewrite -> List.Forall_forall. move => x HIN.
    apply H in HIN. unfold cl_type_check_single in HIN.
    destruct HIN.
    unfold cl_type_check_single.
    exists x0. by eapply store_extension_cl_typing; eauto.
  - split => //.
    rewrite -> List.Forall_forall. move => x HIN.
    apply H0 in HIN. unfold tab_agree in HIN.
    destruct HIN.
    rewrite -> List.Forall_forall in H1.
    unfold tab_agree.
    rewrite -> List.Forall_forall.
    split => //=.
    move => x' HIN'.
    apply H1 in HIN'.
    unfold tabcl_agree in HIN'.
    unfold tabcl_agree.
    destruct x' => //=.
    simpl in HIN'. destruct (List.nth_error s_funcs0 n) => //=.
    unfold cl_type_check_single in HIN'.
    destruct HIN'.
    unfold cl_type_check_single.
    exists x0. by eapply store_extension_cl_typing; eauto.
Qed.

Lemma nth_error_update_list_hit: forall {X:Type} l n {x:X},
    n < length l ->
    List.nth_error (update_list_at l n x) n = Some x.
Proof.
  move => X l n. generalize dependent l.
  induction n => //=; destruct l => //=.
  - move => x' HLength.
    simpl. rewrite -cat1s.
    assert (n < length l); first by lias.
    assert (length (take n l) = n).
    { rewrite length_is_size. rewrite length_is_size in H.
      rewrite size_take. by rewrite H. }
    assert (List.nth_error (take n l ++ [:: x'] ++ List.skipn (n+1)%Nrec l) (length (take n l)) = Some x'); first by apply list_nth_prefix.
    by rewrite H0 in H1.
Qed.

Lemma nth_error_update_list_others: forall {X:Type} l n m {x:X},
    n <> m ->
    n < length l ->
    List.nth_error (update_list_at l n x) m = List.nth_error l m.
Proof.
  move => X l n. generalize dependent l.
  induction n => //=; move => l m x Hne HLength.
  - destruct m => //=.
    by destruct l => //=.
  - destruct m => //=.
    + by destruct l => //=.
    + destruct l => //=.
      simpl in HLength.
      by apply IHn; lias.
Qed.

Lemma Forall_update: forall {X:Type} f l n {x:X},
    List.Forall f l ->
    f x ->
    n < length l ->
    List.Forall f (update_list_at l n x).
Proof.
  move => X f l n x HA Hf HLength.
  rewrite -> List.Forall_forall in HA.
  rewrite List.Forall_forall.
  move => x0 HIN.
  apply List.In_nth_error in HIN.
  destruct HIN as [n' HN].
  assert (n' < length (update_list_at l n x))%coq_nat.
  { rewrite <- List.nth_error_Some. by rewrite HN. }
  move/ltP in H.
  destruct (n == n') eqn:H1 => //=.
  - move/eqP in H1. subst.
    rewrite nth_error_update_list_hit in HN => //=. by inversion HN; subst.
  - move/eqP in H1.
    rewrite nth_error_update_list_others in HN => //=.
    apply HA.
    by eapply List.nth_error_In; eauto.
Qed.

Lemma store_typed_mem_agree: forall s n m,
    store_typing s ->
    List.nth_error (s_mems s) n = Some m ->
    mem_agree m.
Proof.
  move => s n m HST HN.
  unfold store_typing in HST.
  destruct s => //=.
  destruct HST as [_ [_ H]].
  rewrite -> List.Forall_forall in H.
  simpl in HN.
  apply H. by eapply List.nth_error_In; eauto.
Qed.

Lemma store_mem_agree: forall s n m k off vs tl mem,
    store_typing s ->
    List.nth_error (s_mems s) n = Some m ->
    store m k off vs tl = Some mem ->
    tl > 0 ->
    mem_agree mem.
Proof.
  move => s n m k off vs tl mem HST HN HStore HTL.
  unfold store in HStore.
  destruct ((k+off+N.of_nat tl <=? mem_length m)%N) eqn:H => //=.
  inversion HStore. subst. clear HStore.
  unfold mem_agree => //=.
  destruct (lim_max (mem_limit m)) eqn:HLimMax => //=.
  unfold mem_size. unfold mem_length => /=.
  assert (mem_agree m); first by eapply store_typed_mem_agree; eauto.
  unfold mem_agree in H0. by rewrite HLimMax in H0.
Qed.

Lemma mem_grow_mem_agree: forall s n m c mem,
    store_typing s ->
    List.nth_error (s_mems s) n = Some m ->
    mem_grow m c = Some mem ->
    mem_agree mem.
Proof.
  move => s n m c mem HST HN HGrow.
  assert (mem_agree m); first by eapply store_typed_mem_agree; eauto.
  unfold mem_grow in HGrow.
  unfold mem_agree. simpl.
  unfold mem_agree in H.
  destruct (lim_max (mem_limit m)) eqn:HLimMax => //=.
  - destruct ((mem_size m + c <=? n0)%N) eqn:H1 => //.
    inversion HGrow; subst; clear HGrow.
    by rewrite HLimMax.
  - inversion HGrow; subst; clear HGrow.
    by rewrite HLimMax.
Qed.

Lemma store_extension_reduce: forall s vs es i s' vs' es' C tf loc lab ret,
    reduce s vs es i s' vs' es' ->
    inst_typing s i C ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es tf ->
    store_typing s ->
    store_extension s s' /\ store_typing s'.
Proof.
  move => s vs es i s' vs' es' C tf loc lab ret HReduce.
  generalize dependent C. generalize dependent tf.
  generalize dependent loc. generalize dependent lab. generalize dependent ret.
  induction HReduce => //; try move => ret lab loc tf C HIT HType HST; try intros; destruct tf; try by (split => //; apply store_extension_same).
  - (* update glob *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::EConst v; Set_global j] with ([::EConst v] ++ [::Set_global j]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]. subst.
    invert_be_typing.
    apply Set_global_typing in H4.
    destruct H4 as [g [t [H5 [H6 [H7 [H8 H9]]]]]].
    apply concat_cancel_last in H8. destruct H8. subst.
    unfold supdate_glob in H.
    unfold option_bind in H.
    unfold supdate_glob_s in H.
    unfold option_map in H.
    assert (store_extension s s') as Hext.
    remove_bools_options.
    unfold sglob_ind in Hoption. simpl in H5.
    eapply tc_reference_glob_type in H5; eauto.
    destruct g => //.
    destruct g0 => //.
    simpl in H1. unfold global_agree in H5. simpl in H5.
    unfold is_mut in H7. simpl in H7. remove_bools_options. subst.
    + simpl. unfold store_extension => //=.
      repeat (apply/andP; split) => //=.
      -- by apply all2_tab_extension_same.
      -- by apply all2_mem_extension_same.
      -- eapply glob_extension_update_nth; eauto => //=.
         unfold glob_extension => //=.
         by destruct v => //=; destruct g_val => //=.
    split => //.
    by eapply store_global_extension_store_typed; eauto;
      destruct s => //=; destruct s' => //=; remove_bools_options.
  - (* update memory : store none *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::EConst (ConstInt32 k); EConst v; Store t None a off] with ([::EConst (ConstInt32 k); EConst v] ++ [::Store t None a off]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    apply Store_typing in H6.
    destruct H6 as [H7 [H8 H9]]. subst.
    apply concat_cancel_last_n in H7 => //.
    remove_bools_options.
    inversion H4. subst. clear H4.
    assert (store_extension s (upd_s_mem s (update_list_at (s_mems s) j mem'))) as Hext.
    + unfold store_extension => //=.
      repeat (apply/andP; split) => //=.
      * by apply all2_tab_extension_same.
        eapply mem_extension_update_nth; eauto => //=.
      * by eapply mem_extension_store; eauto.
      * by apply all2_glob_extension_same.
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as [_ [_ H11]].
    simpl in H1.
    assert (j < length s_mems)%coq_nat.
    { apply List.nth_error_Some. by rewrite H1. }
    inversion H0; subst. clear H0.
    apply Forall_update => //=.
    eapply store_mem_agree; eauto.
    * by destruct v => //=.
    * by move/ltP in H3.
  - (* another update memory : store some *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::EConst (ConstInt32 k); EConst v; Store t (Some tp) a off] with ([::EConst (ConstInt32 k); EConst v] ++ [::Store t (Some tp) a off]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    apply Store_typing in H6.
    destruct H6 as [H7 [H8 H9]]. subst.
    apply concat_cancel_last_n in H7 => //.
    remove_bools_options.
    inversion H4. subst. clear H4.
    assert (store_extension s (upd_s_mem s (update_list_at (s_mems s) j mem'))) as Hext.
    + unfold store_extension => //=.
      repeat (apply/andP; split) => //=.
      * by apply all2_tab_extension_same.
      * eapply mem_extension_update_nth; eauto => //=.
        by eapply mem_extension_store; eauto.
      * by apply all2_glob_extension_same.
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as [_ [_ H11]].
    simpl in H1.
    assert (j < length s_mems)%coq_nat.
    { apply List.nth_error_Some. by rewrite H1. }
    apply Forall_update => //=.
    eapply store_mem_agree; eauto.
    * by destruct tp => //=.
    * by move/ltP in H3.
  - (* again update memory : grow_memory *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::EConst (ConstInt32 c); Grow_memory] with ([::EConst (ConstInt32 c)] ++ [::Grow_memory]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    apply Grow_memory_typing in H6.
    destruct H6 as [ts' [H7 [H8 H9]]]. subst.
    apply concat_cancel_last in H9 => //. destruct H9. subst.
    assert (store_extension s (upd_s_mem s (update_list_at (s_mems s) j mem'))) as Hext.
    + unfold store_extension => //=.
      repeat (apply/andP; split) => //=.
      * by apply all2_tab_extension_same.
      * eapply mem_extension_update_nth; eauto => //=.
        by eapply mem_extension_grow_memory; eauto.
      * by apply all2_glob_extension_same.
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as [_ [_ H11]].
    simpl in H0.
    assert (j < length s_mems)%coq_nat.
    { apply List.nth_error_Some. by rewrite H0. }
    apply Forall_update => //=.
    eapply mem_grow_mem_agree; eauto. by move/ltP in H1.
  - (* r_label *)
    eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab' [t1s [t2s HType]]].
    eapply IHHReduce; eauto.
    rewrite upd_label_overwrite in HType. by apply HType.
  - (* r_local *)
    apply Local_typing in HType.
    destruct HType as [ts [H1 [H2 H3]]]. subst.
    inversion H2. subst.
    eapply IHHReduce; eauto.
    by apply H1.
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

Lemma t_preservation_e: forall s vs es i s' vs' es' C t1s t2s lab ret,
    reduce s vs es i s' vs' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s i C ->
    inst_typing s' i C ->
    e_typing s (upd_label (upd_local_return C (tc_local C ++ map typeof vs) ret) lab) es (Tf t1s t2s) ->
    e_typing s' (upd_label (upd_local_return C (tc_local C ++ map typeof vs') ret) lab) es' (Tf t1s t2s).
Proof.
  move => s vs es i s' vs' es' C t1s t2s lab ret HReduce HST1 HST2.
  generalize dependent t2s. generalize dependent t1s.
  generalize dependent lab. generalize dependent ret.
  generalize dependent C.
  dependent induction HReduce; move => C ret lab tx ty HIT1 HIT2 HType; subst; try eauto; try by apply ety_trap.
  - (* reduce_simple *)
    by eapply t_simple_preservation; eauto.
  - (* Call *)
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
    by eapply store_typed_cl_typed; eauto.
  - (* Call_indirect *)
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
    destruct (stab_s s t (Wasm_int.nat_of_uint i32m c)) eqn:Hstab => //.
    inversion H. subst. clear H.
    unfold stab_s in Hstab.
    unfold option_bind in Hstab.
    destruct (stab_index s t (Wasm_int.nat_of_uint i32m c)) eqn:Hstabi => //.
    unfold stab_index in Hstabi.
    unfold option_bind in Hstabi.
    destruct (List.nth_error (s_tables s) t) eqn:HN1 => //.
    destruct (List.nth_error (table_data t0) (Wasm_int.nat_of_uint i32m c)) eqn:HN2 => //.
    subst.
    by eapply store_typed_cl_typed; eauto.
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
    destruct H10 as [g [t [H4 [H5 [H6 [H7 H8]]]]]]. subst.
    apply ety_a'; auto_basic => //=.
    simpl in H8. simpl in H4. simpl.
    apply concat_cancel_last in H7. destruct H7. subst.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Load None *)
    convert_et_to_bet.
    replace [::EConst (ConstInt32 k); Load t None a off] with ([::EConst (ConstInt32 k)] ++ [::Load t None a off]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Load_typing in H10.
    destruct H10 as [ts  [H11 [H12 [H13 H14]]]].
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
    convert_et_to_bet.
    replace [::EConst (ConstInt32 k); Load t (Some (tp, sx)) a off] with ([::EConst (ConstInt32 k)] ++ [::Load t (Some (tp, sx)) a off]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Load_typing in H10.
    destruct H10 as [ts [H11 [H12 [H13 H14]]]].
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
      destruct H10 as [H11 [H12 H13]].
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
      destruct H10 as [H11 [H12 H13]].
      apply concat_cancel_last_n in H11 => //.
      move/andP in H11. destruct H11. move/eqP in H3. subst.
      apply ety_a'; auto_basic => //.
      apply bet_weakening_empty_both.
      by apply bet_empty.
  - (* Current_memory *)
    convert_et_to_bet.
    apply Current_memory_typing in HType.
    destruct HType as [H5 H6]. subst.
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
    destruct H10 as [ts [H11 [H12 H13]]]. subst.
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
    destruct H10 as [ts [H11 [H12 H13]]]. subst.
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
            assert (tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
            rewrite H0 in H9. rewrite H0.
            replace (map typeof vs') with (map typeof vs) => //.
            eapply store_extension_e_typing; try apply HST1 => //; try by [].
            eapply store_extension_reduce; eauto.
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
            * assert (tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
              rewrite H in H13. rewrite H.
              simpl in H14. rewrite upd_label_overwrite in H14.
              eapply lfilled_es_type_exists in H14; eauto.
              destruct H14 as [lab' [t1s' [t2s' H14]]].
              rewrite upd_label_overwrite in H14.
              replace (map typeof vs') with (map typeof vs) => //.
              eapply store_extension_e_typing; try apply HST1 => //; try by [].
              eapply store_extension_reduce; eauto.
              by eapply t_preservation_vs_type; eauto.
            * simpl.
              simpl in H14.
              by eapply IHk; eauto.
         ++ repeat apply ety_weakening.
            assert (tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
            rewrite H in H11. rewrite H.
            simpl in H14. rewrite upd_label_overwrite in H14.
            eapply lfilled_es_type_exists in H14; eauto.
            destruct H14 as [lab' [t1s' [t2s' H14]]].
            rewrite upd_label_overwrite in H14.
            replace (map typeof vs') with (map typeof vs) => //.
            eapply store_extension_e_typing; try apply HST1 => //; try by [].
            eapply store_extension_reduce; eauto.
            by eapply t_preservation_vs_type; eauto.
  - (* r_local *)
    apply Local_typing in HType.
    destruct HType as [ts [H1 [H2 H3]]]. subst.
    apply et_weakening_empty_1.
    eapply ety_local => //.
    inversion H2. subst.
    apply upd_label_unchanged_typing in H1.
    eapply mk_s_typing; eauto.
    + eapply inst_typing_extension; eauto.
      eapply store_extension_reduce; eauto.
    + eapply IHHReduce; eauto.
      eapply inst_typing_extension; eauto.
      eapply store_extension_reduce; eauto.
Qed.

Theorem t_preservation: forall s vs es i s' vs' es' ts,
    reduce s vs es i s' vs' es' ->
    config_typing i s vs es ts ->
    config_typing i s' vs' es' ts.
Proof.
  move => s vs es i s' vs' es' ts HReduce HType.
  inversion HType. inversion H0. subst.
  assert (store_extension s s' /\ store_typing s').
  { apply upd_label_unchanged_typing in H8.
    by eapply store_extension_reduce; eauto. }
  destruct H1.
  assert (inst_typing s' i C0); first by eapply inst_typing_extension; eauto.
  apply mk_config_typing; eauto.
  eapply mk_s_typing; eauto.
  by eapply t_preservation_e; eauto.
Qed.

*)

Definition terminal_form (es: seq administrative_instruction) :=
  const_list es \/ es = [::Trap].

Lemma reduce_trap_left: forall vs,
    const_list vs ->
    vs <> [::] ->
    reduce_simple (vs ++ [::Trap]) [::Trap].
Proof.
  move => vs HConst H.
  destruct vs => //=; eapply rs_trap; try by destruct vs => //=.
  assert (lfilledInd 0 (LBase (a::vs) [::]) [::Trap] (a::vs++[::Trap])); first by apply LfilledBase.
  apply/lfilledP.
  by apply H0.
Qed.

Lemma v_e_trap: forall vs es,
    const_list vs ->
    vs ++ es = [::Trap] ->
    vs = [::] /\ es = [::Trap].
Proof.
  move => vs es HConst H.
  destruct vs => //=.
  destruct vs => //=. destruct es => //=.
  simpl in H. inversion H. by subst.
Qed.

Lemma cat_split: forall {X:Type} (l l1 l2: seq X),
    l = l1 ++ l2 ->
    l1 = take (size l1) l /\
    l2 = drop (size l1) l.
Proof.
  move => X l l1.
  generalize dependent l.
  induction l1 => //=; move => l l2 HCat; subst => //=.
  - split. by rewrite take0. by rewrite drop0.
  - edestruct IHl1.
    instantiate (1 := l2). eauto.
    split => //.
    by f_equal.
Qed.

Lemma reduce_composition: forall s cs vs es es0 i s' vs' es' hs hs',
    const_list cs ->
    reduce hs s vs es i hs' s' vs' es' ->
    reduce hs s vs (cs ++ es ++ es0) i hs' s' vs' (cs ++ es' ++ es0).
Proof.
  move => s cs vs es es0 i s' vs' es' hs hs' HConst HReduce.
  eapply r_label; eauto; apply/lfilledP.
  - instantiate (1 := (LBase cs es0)). instantiate (1 := 0).
    by apply LfilledBase.
  - by apply LfilledBase.
Qed.

Lemma reduce_composition_right: forall s vs es es0 i s' vs' es' hs hs',
    reduce hs s vs es i hs' s' vs' es' ->
    reduce hs s vs (es ++ es0) i hs' s' vs' (es' ++ es0).
Proof.
  move => s vs es es0 i s' vs' es' hs hs' HReduce.
  eapply reduce_composition in HReduce.
  instantiate (1 := es0) in HReduce.
  instantiate (1 := [::]) in HReduce.
  by simpl in HReduce.
  by [].
Qed.

Lemma reduce_composition_left: forall s cs vs es i s' vs' es' hs hs',
    const_list cs ->
    reduce hs s vs es i hs' s' vs' es' ->
    reduce hs s vs (cs ++ es) i hs' s' vs' (cs ++ es').
Proof.
  move => s vs es es0 i s' vs' es' hs hs' HConst HReduce.
  eapply reduce_composition in HReduce; eauto.
  instantiate (1 := [::]) in HReduce.
  by repeat rewrite cats0 in HReduce.
Qed.

Lemma lfilled0_empty: forall es,
    lfilled 0 (LBase [::] [::]) es es.
Proof.
  move => es.
  apply/lfilledP.
  assert (lfilledInd 0 (LBase [::] [::]) es ([::] ++ es ++ [::])); first by apply LfilledBase.
  by rewrite cats0 in H.
Qed.

Lemma label_lfilled1: forall n es es0,
    lfilled 1 (LRec [::] n es0 (LBase [::] [::]) [::]) es [::Label n es0 es].
Proof.
  move => n es es0.
  apply/lfilledP.
  replace [:: Label n es0 es] with ([::] ++ [::Label n es0 es] ++ [::]) => //.
  apply LfilledRec => //.
  assert (lfilledInd 0 (LBase [::] [::]) es ([::] ++ es ++ [::])); first by apply LfilledBase.
  simpl in H. by rewrite cats0 in H.
Qed.

Lemma terminal_form_v_e: forall vs es,
    const_list vs ->
    terminal_form (vs ++ es) ->
    terminal_form es.
Proof.
  move => vs es HConst HTerm.
  unfold terminal_form in HTerm.
  destruct HTerm.
  - unfold terminal_form. left.
    apply const_list_split in H. by destruct H.
  - destruct vs => //=.
    + simpl in H. subst. unfold terminal_form. by right.
    + destruct vs => //=. destruct es => //=.
      simpl in H. inversion H. by subst.
Qed.

Lemma terminal_trap: terminal_form [::Trap].
Proof.
  unfold terminal_form. by right.
Qed.

Lemma e_b_inverse: forall es,
    es_is_basic es ->
    to_e_list (to_b_list es) = es.
Proof.
  move => es HBasic.
  by erewrite e_b_elim; eauto.
Qed.

Lemma typeof_append: forall ts t vs,
    map typeof vs = ts ++ [::t] ->
    exists v,
      vs = take (size ts) vs ++ [::v] /\
      map typeof (take (size ts) vs) = ts /\
      typeof v = t.
Proof.
  move => ts t vs HMapType.
  apply cat_split in HMapType.
  destruct HMapType.
  rewrite -map_take in H.
  rewrite -map_drop in H0.
  destruct (drop (size ts) vs) eqn:HDrop => //=.
  destruct l => //=.
  inversion H0. subst.
  exists v.
  split => //.
  rewrite -HDrop. by rewrite cat_take_drop.
Qed.

Hint Unfold reduce_simple : core.
Hint Constructors opsem.reduce_simple : core.

Ltac invert_typeof_vcs :=
  lazymatch goal with
  | H: map typeof ?vcs = [::_; _; _] |- _ =>
    destruct vcs => //=; destruct vcs => //=; destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map typeof ?vcs = [::_; _] |- _ =>
    destruct vcs => //=; destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map typeof ?vcs = [::_] |- _ =>
    destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map typeof ?vcs = [::] |- _ =>
    destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  end.
(*
Ltac invert_inst_typing :=
  lazymatch goal with
  | H: inst_typing _ ?i ?C |- _ =>
    unfold inst_typing in H;
    destruct i => //=;
    destruct C => //=;
    destruct tc_local => //=;
    destruct tc_label => //=;
    destruct tc_return => //=
  end.
*)

Lemma nth_error_map: forall {X Y:Type} (l: seq X) n f {fx: Y},
    List.nth_error (map f l) n = Some fx ->
    exists x, List.nth_error l n = Some x /\
    f x = fx.
Proof.
  move => X Y l n.
  generalize dependent l.
  induction n => //; move => l f fx HN.
  - destruct l => //=.
    simpl in HN. inversion HN. subst. by eauto.
  - destruct l => //=.
    simpl in HN. by apply IHn.
Qed.

Lemma func_context_store: forall s i C j x,
    inst_typing s i C ->
    j < length (tc_func_t C) ->
    List.nth_error (tc_func_t C) j = Some x ->
    sfunc s i j <> None.
Proof.
  move => s i C j x HIT HLength HN.
  unfold sfunc. unfold operations.sfunc. unfold option_bind.
  unfold sfunc_ind.
  unfold inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  remove_bools_options.
  remember H3 as H4. clear HeqH4.
  apply all2_size in H3.
  repeat rewrite -length_is_size in H3.
  simpl in HLength.
  rewrite -H3 in HLength.
  move/ltP in HLength.
  apply List.nth_error_Some in HLength.
  destruct (List.nth_error i_funcs j) eqn:HN1 => //=.
  apply List.nth_error_Some.
  unfold functions_agree in H4.
  eapply all2_projection in H4; eauto.
  remove_bools_options.
  by move/ltP in H4.
Qed.

Lemma glob_context_store: forall s i C j g,
    inst_typing s i C ->
    j < length (tc_global C) ->
    List.nth_error (tc_global C) j = Some g ->
    sglob s i j <> None.
Proof.
  move => s i C j g HIT HLength HN.
  unfold sglob. unfold operations.sglob. unfold option_bind.
  unfold sglob_ind.
  unfold inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  remove_bools_options.
  remember H2 as H4. clear HeqH4.
  apply all2_size in H2.
  repeat rewrite -length_is_size in H2.
  simpl in HLength.
  rewrite -H2 in HLength.
  move/ltP in HLength.
  apply List.nth_error_Some in HLength.
  destruct (List.nth_error i_globs j) eqn:HN1 => //=.
  apply List.nth_error_Some.
  unfold globals_agree in H4.
  eapply all2_projection in H4; eauto.
  remove_bools_options.
  by move/ltP in H4.
Qed.

Lemma mem_context_store: forall s i C,
    inst_typing s i C ->
    tc_memory C <> [::] ->
    exists n, smem_ind s i = Some n /\
              List.nth_error (s_mems s) n <> None.
Proof.
  move => s i C HIT HMemory.
  unfold inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  remove_bools_options.
  simpl in HMemory. unfold smem_ind. simpl.
  remember H0 as H4. clear HeqH4.
  apply all2_size in H0.
  destruct i_memory => //=; first by destruct tc_memory.
  exists m. split => //.
  destruct tc_memory => //.
  simpl in H4.
  unfold memi_agree in H4.
  by remove_bools_options.
Qed.

(*
  Except [::Br i] or [::Return], every other basic instruction can be
    prepended by several consts to be reduceable to something else.

  Although we only actually need bes to be not Return or Br, we have to state an
    entire lfilled proposition as a condition due to composition.
 *)

Definition not_lf_br (es: seq administrative_instruction) (n: nat) :=
  forall k lh, ~ lfilled n lh [::Basic (Br k)] es.

Definition not_lf_return (es: seq administrative_instruction) (n: nat) :=
  forall lh, ~ lfilled n lh [::Basic Return] es.

Lemma lf_composition: forall es es2 e0 lh n,
    lfilled n lh e0 es ->
    exists lh', lfilled n lh' e0 (es ++ es2).
Proof.
  move => es es2 e0 lh n HLF.
  move/lfilledP in HLF.
  inversion HLF; subst.
  - exists (LBase vs (es' ++ es2)).
    apply/lfilledP.
    repeat rewrite -catA.
    by apply LfilledBase.
  - exists (LRec vs n0 es' lh' (es'' ++ es2)).
    apply/lfilledP.
    repeat rewrite -catA.
    by apply LfilledRec.
Qed.

Lemma lf_composition_left: forall cs es e0 lh n,
    const_list cs ->
    lfilled n lh e0 es ->
    exists lh', lfilled n lh' e0 (cs ++ es).
Proof.
  move => cs es e0 lh n HConst HLF.
  move/lfilledP in HLF.
  inversion HLF; subst.
  - exists (LBase (cs ++ vs) es').
    apply/lfilledP.
    rewrite (catA cs vs).
    apply LfilledBase.
    by apply const_list_concat.
  - exists (LRec (cs ++ vs) n0 es' lh' es'').
    apply/lfilledP.
    rewrite (catA cs vs).
    apply LfilledRec => //.
    by apply const_list_concat.
Qed.

Lemma nlfbr_right: forall es n es',
    not_lf_br (es ++ es') n ->
    not_lf_br es n.
Proof.
  unfold not_lf_br.
  move => es n es' HNLF k lh HContra.
  eapply lf_composition in HContra.
  instantiate (1 := es') in HContra.
  destruct HContra.
  by eapply HNLF; eauto.
Qed.

Lemma nlfret_right: forall es n es',
    not_lf_return (es ++ es') n ->
    not_lf_return es n.
Proof.
  unfold not_lf_return.
  move => es n es' HNLF lh HContra.
  eapply lf_composition in HContra.
  instantiate (1 := es') in HContra.
  destruct HContra.
  by eapply HNLF; eauto.
Qed.

Lemma nlfbr_left: forall es n cs,
    const_list cs ->
    not_lf_br (cs ++ es) n ->
    not_lf_br es n.
Proof.
  unfold not_lf_return.
  move => es n cs HConst HNLF k lh HContra.
  eapply lf_composition_left in HContra => //.
  {
    instantiate (1 := cs) in HContra.
    destruct HContra.
    by eapply HNLF; eauto.
  }
  by [].
Qed.

Lemma nlfret_left: forall es n cs,
    const_list cs ->
    not_lf_return (cs ++ es) n ->
    not_lf_return es n.
Proof.
  unfold not_lf_return.
  move => es n cs HConst HNLF lh HContra.
  eapply lf_composition_left in HContra => //.
  {
    instantiate (1 := cs) in HContra.
    destruct HContra.
    by eapply HNLF; eauto.
  }
  by [].
Qed.

Lemma t_progress_be: forall C bes ts1 ts2 vcs lab ret s vs i hs hs',
    store_typing s ->
    inst_typing s i C ->
    be_typing (upd_label (upd_local_return C (map typeof vs) ret) lab) bes (Tf ts1 ts2) ->
    map typeof vcs = ts1 ->
    not_lf_br (to_e_list bes) 0 ->
    not_lf_return (to_e_list bes) 0 ->
    const_list (to_e_list bes) \/
    exists s' vs' es', reduce hs s vs (v_to_e_list vcs ++ to_e_list bes) i hs' s' vs' es'.
Proof.
  move => C bes ts1 ts2 vcs lab ret s vs i hs hs' HST HIT HType HConstType HNBr HNRet.
  generalize dependent vcs.
  dependent induction HType; (try by left); move => vcs HConstType.
  - (* Unop_i *)
    right. invert_typeof_vcs.
    by destruct v => //=; repeat eexists; apply r_simple.
  - (* Unop_f *)
    right. invert_typeof_vcs.
    by destruct v => //=; repeat eexists; apply r_simple.
  - (* binop_i *)
    right. invert_typeof_vcs.
    destruct v => //=; destruct v0 => //=.
    + destruct (@app_binop_i i32t op s0 s1) eqn:HBinary;
        by repeat eexists; apply r_simple; eauto.
    + destruct (@app_binop_i i64t op s0 s1) eqn:HBinary;
        by repeat eexists; apply r_simple; eauto.
  - (* binop_f *)
    right. invert_typeof_vcs.
    destruct v => //=; destruct v0 => //=.
    + destruct (@app_binop_f f32t op s0 s1) eqn:HBinary;
        by repeat eexists; apply r_simple; eauto.
    + destruct (@app_binop_f f64t op s0 s1) eqn:HBinary;
        by repeat eexists; apply r_simple; eauto.
  - (* testop *)
    right. invert_typeof_vcs.
    by destruct v => //=; repeat eexists; apply r_simple.
  - (* relop_i *)
    right. invert_typeof_vcs.
    by destruct v => //=; destruct v0 => //=; repeat eexists; apply r_simple.
  - (* relop_f *)
    right. invert_typeof_vcs.
    by destruct v => //=; destruct v0 => //=; repeat eexists; apply r_simple.
  - (* cvtop *)
    right. invert_typeof_vcs.
    destruct (cvt t1 sx v) eqn:HConvert; repeat eexists; apply r_simple; destruct v => //=; eauto.
  - (* reinterpret *)
    right. invert_typeof_vcs.
    by destruct v => //=; repeat eexists; apply r_simple; apply rs_reinterpret.
  - (* Unreachable *)
    right.
    exists s, vs, (v_to_e_list vcs ++ [::Trap]).
    apply reduce_composition_left; first by apply v_to_e_is_const_list.
    by apply r_simple.
  - (* Nop *)
    right.
    exists s, vs, (v_to_e_list vcs ++ [::]).
    apply reduce_composition_left; first by apply v_to_e_is_const_list.
    by apply r_simple.
  - (* Drop *)
    right. invert_typeof_vcs.
    by repeat eexists; apply r_simple.
  - (* Select *)
    right. invert_typeof_vcs.
    destruct v1 => //=.
    by destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0;
      repeat eexists; apply r_simple; eauto.
  - (* Block *)
    right.
    exists s, vs, [::Label (length ts2) [::] (v_to_e_list vcs ++ to_e_list es)].
    apply r_simple. eapply rs_block; eauto.
    + by apply v_to_e_is_const_list.
    + repeat rewrite length_is_size.
      rewrite v_to_e_size.
      rewrite -HConstType.
      by rewrite size_map.
  - (* Loop *)
    right.
    exists s, vs, [::Label (length vcs) [::Basic (Loop (Tf ts1 ts2) es)] (v_to_e_list vcs ++ to_e_list es)].
    apply r_simple. eapply rs_loop; eauto; repeat rewrite length_is_size.
    + by apply v_to_e_is_const_list.
    + by rewrite v_to_e_size.
    + rewrite -HConstType. by rewrite size_map.
  - (* if *)
    right.
    apply typeof_append in HConstType.
    destruct HConstType as [v [H1 [H2 H3]]].
    rewrite H1. rewrite -v_to_e_cat.
    rewrite -catA.
    destruct v => //=.
    destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
    + exists s, vs, (v_to_e_list (take (size tn) vcs) ++ [::Basic (Block (Tf tn ts2) es2)]).
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.
    + exists s, vs, (v_to_e_list (take (size tn) vcs) ++ [::Basic (Block (Tf tn ts2) es1)]).
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.
  - (* Br *)
    exfalso.
    unfold not_lf_br in HNBr.
    apply (HNBr i0 (LBase [::] [::])).
    by apply lfilled0_empty.
  - (* Br_if *)
    right.
    apply typeof_append in HConstType.
    destruct HConstType as [v [H1 [H2 H3]]].
    rewrite H1. rewrite -v_to_e_cat.
    rewrite -catA.
    destruct v => //=.
    destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
    + exists s, vs, (v_to_e_list (take (size ts2) vcs) ++ [::]).
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.
    + exists s, vs, (v_to_e_list (take (size ts2) vcs) ++ [::Basic (Br i0)]).
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.
  - (* Br_table *)
    right.
    apply cat_split in HConstType. destruct HConstType.
    assert (vcs = take (size t1s) vcs ++ drop (size t1s) vcs); first by rewrite cat_take_drop.
    rewrite H2.
    symmetry in H1. rewrite -map_drop in H1. apply typeof_append in H1.
    destruct H1 as [v [H3 [H4 H5]]].
    destruct v => //=.
    rewrite H3.
    repeat rewrite -v_to_e_cat.
    repeat rewrite -catA. rewrite catA.
    destruct (length ins > Wasm_int.nat_of_uint i32m s0) eqn:HLength; move/ltP in HLength.
    + remember HLength as H6. clear HeqH6.
      apply List.nth_error_Some in H6.
      destruct (List.nth_error ins (Wasm_int.nat_of_uint i32m s0)) eqn:HN => //=.
      exists s, vs, ((v_to_e_list (take (size t1s) vcs) ++ v_to_e_list (take (size ts) (drop (size t1s) vcs))) ++ [::Basic (Br n)]).
      apply reduce_composition_left.
      { by apply const_list_concat; apply v_to_e_is_const_list. }
      apply r_simple. apply rs_br_table => //.
      by lias.
    + assert (length ins <= Wasm_int.nat_of_uint i32m s0); first by lias.
      move/leP in H1.
      remember H1 as H6. clear HeqH6.
      apply List.nth_error_None in H6.
      exists s, vs, ((v_to_e_list (take (size t1s) vcs) ++ v_to_e_list (take (size ts) (drop (size t1s) vcs))) ++ [::Basic (Br i0)]).
      apply reduce_composition_left.
      { by apply const_list_concat; apply v_to_e_is_const_list. }
      apply r_simple. apply rs_br_table_length => //.
      by lias.
  - (* Return *)
    exfalso.
    unfold not_lf_return in HNRet.
    apply (HNRet (LBase [::] [::])).
    by apply lfilled0_empty.
  - (* Call *)
    right.
    simpl in H. simpl in H0.
    eapply func_context_store in H; eauto.
    destruct (sfunc s i i0) eqn:HCL => //.
    exists s, vs, (v_to_e_list vcs ++ [:: (Invoke f)]).
    apply reduce_composition_left; first by apply v_to_e_is_const_list.
    apply r_call => //.
  - (* Call_indirect *)
    right.
    simpl in H.
    simpl in H0.
    simpl in H1.
    apply typeof_append in HConstType. destruct HConstType as [v [H2 [H3 H4]]].
    destruct v => //=.
    rewrite H2. rewrite -v_to_e_cat. rewrite -catA.
    exists s, vs.
    destruct (stab s i (Wasm_int.nat_of_uint i32m s0)) eqn:Hstab.
    + (* Some cl *)
      destruct (stypes s i i0 == Some (cl_type f)) eqn:Hclt; move/eqP in Hclt.
      * exists (v_to_e_list (take (size t1s) vcs) ++ [::Invoke f]).
        apply reduce_composition_left; first by apply v_to_e_is_const_list.
        simpl.
        eapply r_call_indirect_success; eauto.
      * exists (v_to_e_list (take (size t1s) vcs) ++ [::Trap]).
        apply reduce_composition_left; first by apply v_to_e_is_const_list.
        by eapply r_call_indirect_failure1; eauto.
    + (* None *)
      exists (v_to_e_list (take (size t1s) vcs) ++ [::Trap]).
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_call_indirect_failure2.

  - (* Get_local *)
    right. invert_typeof_vcs.
    simpl in H. simpl in H0.
    apply nth_error_map in H0.
    destruct H0 as [x [HN HType]].
    rewrite length_is_size in H.
    rewrite size_map in H.
    apply split3 in HN => //.
    exists s, vs, [::Basic (EConst x)].
    rewrite HN.
    apply r_get_local.
    rewrite length_is_size.
    rewrite size_take. by rewrite H.

  - (* Set_local *)
    right. invert_typeof_vcs.
    simpl in H.
    rewrite length_is_size in H. rewrite size_map in H. rewrite -length_is_size in H.
    exists s, (set_nth v vs i0 v), [::].
    by apply r_set_local.

  - (* Tee_local *)
    right. invert_typeof_vcs.
    exists s, vs, [::Basic (EConst v); Basic (EConst v); Basic (Set_local i0)].
    by apply r_simple; eauto.

  - (* Get_global *)
    right. invert_typeof_vcs.
    simpl in H. simpl in H0.
    unfold option_map in H0.
    destruct (List.nth_error (tc_global C) i0) eqn:HN => //=.
    eapply glob_context_store in HN; eauto.
    assert (sglob_val s i i0 <> None).
    unfold sglob_val. unfold option_map. by destruct (sglob s i i0).
    destruct (sglob_val s i i0) eqn:Hglobval => //=.
    exists s, vs, [::Basic (EConst v)].
    by apply r_get_global.

  - (* Set_global *)
    right. invert_typeof_vcs.
    destruct (supdate_glob s i i0 v) eqn:Hs.
    + exists s0, vs, [::].
      by apply r_set_global.
    + unfold supdate_glob in Hs. unfold option_bind in Hs.
      simpl in H. simpl in H0.
      eapply glob_context_store in H0; eauto.
      unfold sglob in H0. unfold option_bind in H0.
      destruct (sglob_ind s i i0) eqn:Hglob => //.
      unfold supdate_glob_s in Hs. unfold option_map in Hs.
      by destruct (List.nth_error (s_globals s) n).

  - (* Load *)
    right.
    simpl in H.
    exists s, vs.
    invert_typeof_vcs. destruct v => //=.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMenInd HMem]].
    destruct (List.nth_error (s_mems s) n) eqn:HN => //=.
    destruct tp_sx.
    + (* Load Some *)
      destruct p as [tp sx].
      simpl in H0. remove_bools_options.
      destruct (load_packed sx m (Wasm_int.N_of_uint i32m s0) off (tp_length tp) (t_length t)) eqn:HLoadResult.
      * exists [::Basic (EConst (wasm_deserialise b t))].
        by eapply r_load_packed_success; eauto.
      * exists [::Trap].
        by eapply r_load_packed_failure; eauto.
    + (* Load None *)
      simpl in H0.
      destruct (load m (Wasm_int.N_of_uint i32m s0) off (t_length t)) eqn:HLoadResult.
      * exists [::Basic (EConst (wasm_deserialise b t))].
        by eapply r_load_success; eauto.
      * exists [::Trap].
        by eapply r_load_failure; eauto.

  - (* Store *)
    right.
    simpl in H.
    invert_typeof_vcs. destruct v => //=.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMenInd HMem]].
    destruct (List.nth_error (s_mems s) n) eqn:HN => //=.
    destruct tp as [tp |].
    + (* Store Some *)
      simpl in H0. remove_bools_options.
      destruct (store_packed m (Wasm_int.N_of_uint i32m s0) off (bits v0) (tp_length tp)) eqn:HStoreResult.
      * exists (upd_s_mem s (update_list_at s.(s_mems) n m0)), vs, [::].
        eapply r_store_packed_success; eauto.
        by unfold types_agree; apply/eqP.
      * exists s, vs, [::Trap].
        eapply r_store_packed_failure; eauto.
        by unfold types_agree; apply/eqP.
    + (* Store None *)
      simpl in H0.
      destruct (store m (Wasm_int.N_of_uint i32m s0) off (bits v0) (t_length (typeof v0))) eqn:HStoreResult.
      * exists (upd_s_mem s (update_list_at s.(s_mems) n m0)), vs, [::].
        eapply r_store_success; eauto.
        by unfold types_agree; apply/eqP.
      * exists s, vs, [::Trap].
        eapply r_store_failure; eauto.
        by unfold types_agree; apply/eqP.

  - (* Current_memory *)
    right. invert_typeof_vcs.
    simpl in H.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMemInd HMem]].
    destruct (List.nth_error (s_mems s) n) eqn:HN => //=.
    exists s, vs, [::Basic (EConst (ConstInt32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size m)))))].
    by eapply r_current_memory; eauto.

  - (* Grow_memory *)
    right. invert_typeof_vcs.
    simpl in H.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMemInd HMem]].
    destruct (List.nth_error (s_mems s) n) eqn:HN => //=.
    destruct v => //=.
    (* Similarly, for this proof we can just use trap and use the failure case. *)
    exists s, vs, [::Basic (EConst (ConstInt32 int32_minus_one))].
    by eapply r_grow_memory_failure; eauto.

  - (* Composition *)
    rewrite to_e_list_cat in HNBr.
    rewrite to_e_list_cat in HNRet.
    edestruct IHHType1; eauto.
    { by eapply nlfbr_right; eauto. }
    { by eapply nlfret_right; eauto. }
    + (* Const *)
      apply const_es_exists in H. destruct H as [cs HConst].
      apply b_e_elim in HConst. destruct HConst. subst.
      rewrite e_b_inverse in HNRet; last by apply const_list_is_basic; apply v_to_e_is_const_list.
      rewrite e_b_inverse in HNBr; last by apply const_list_is_basic; apply v_to_e_is_const_list.
      apply Const_list_typing in HType1. subst.
      edestruct IHHType2; eauto.
      { by eapply nlfbr_left; try apply v_to_e_is_const_list; eauto. }
      { by eapply nlfret_left; try apply v_to_e_is_const_list; eauto. }
      { by rewrite -map_cat. }
      * left. rewrite to_e_list_cat. apply const_list_concat => //.
        by rewrite e_b_inverse => //; apply v_to_e_is_const_list.
      * destruct H as [es' HReduce].
        right.
        rewrite to_e_list_cat.
        rewrite e_b_inverse; last by apply const_list_is_basic; apply v_to_e_is_const_list.
        exists es'.
        rewrite catA.
        by rewrite v_to_e_cat.
    + (* reduce *)
      destruct H as [s' [vs' [es' HReduce]]].
      right.
      rewrite to_e_list_cat.
      exists s', vs', (es' ++ to_e_list [::e]).
      rewrite catA.
      by apply reduce_composition_right.

  - (* Weakening *)
    apply cat_split in HConstType.
    destruct HConstType.
    rewrite -map_take in H. rewrite -map_drop in H0.
    edestruct IHHType; eauto.
    destruct H1 as [s' [vs' [es' HReduce]]].
    right.
    replace vcs with (take (size ts) vcs ++ drop (size ts) vcs); last by apply cat_take_drop.
    rewrite -v_to_e_cat. rewrite -catA.
    exists s', vs', (v_to_e_list (take (size ts) vcs) ++ es').
    by apply reduce_composition_left => //; apply v_to_e_is_const_list.
Qed.

(*
Traceback:
  WTP: config_typing i s vs es ts <=
       s_typing s None i vs es ts && (store_typing s) <=
       e_typing s (C [local = map typeof vs, label = [::], return = None]) es (Tf [::] ts) && ...

  So we only need the part of e_typing with label and return being empty.

  However, it's insufficient to state the e_typing lemma as above, since non-empty label and
    return are required for the Local and Label cases respectively.

  Note that for Br i to be typeable, the length of label must be at least i+1 due to the
    requirement List.nth_error (tc_label C) i = Some ts. This means that there must be
    at least k+1 labels below the current Br i instruction. So say if the current instruction
    list satisfies lfilled n ..., then we have i<n.

  In particular, since in the be_typing case we have no labels (as label is not a basic
    instruction, we have i<0, i.e. we don't need to deal with Br there!

  Similarly, for Return to be typeable, tc_return C must be not None; but that is the case
    only if there's already a Local outside the Return instruction. So we don't have to deal
    with Return in be_typing either.
 *)

Definition br_reduce (es: seq administrative_instruction) :=
  exists n lh, lfilled n lh [::Basic (Br n)] es.

Definition return_reduce (es: seq administrative_instruction) :=
  exists n lh, lfilled n lh [::Basic Return] es.

(** [br_reduce] is decidable. **)
Lemma br_reduce_decidable : forall es, decidable (br_reduce es).
Proof.
  move=> es. apply: pickable_decidable. apply: pickable2_weaken.
  apply lfilled_pickable_rec_gen => es' lh n.
  by apply: lfilled_decidable_base.
Defined.

(** [return_reduce] is decidable. **)
Lemma return_reduce_decidable : forall es, decidable (return_reduce es).
Proof.
  move=> es. apply: pickable_decidable. apply: pickable2_weaken.
  apply lfilled_pickable_rec => es'.
  by apply: lfilled_decidable_base.
Defined.


Local Lemma cat_abcd_a_bc_d: forall {X:Type} (a b c d: seq X),
    a ++ b ++ c ++ d = a ++ (b ++ c) ++ d.
Proof.
  move => X a b c d.
  f_equal. by rewrite catA.
Qed.

Lemma br_reduce_label_length: forall n k lh es s C ts2,
    lfilled n lh [::Basic (Br (n + k))] es ->
    e_typing s C es (Tf [::] ts2) ->
    length (tc_label C) > k.
Proof.
  move => n k lh es s C ts2 HLF.
  generalize dependent ts2. generalize dependent C.
  generalize dependent s.
  move/lfilledP in HLF.
  dependent induction HLF; move => s C ts2 HType.
  - invert_e_typing.
    destruct ts => //=; destruct t1s => //=; clear H1.
    rewrite add0n in H5.
    apply et_to_bet in H5; auto_basic.
    simpl in H5. apply Break_typing in H5.
    destruct H5 as [ts [ts2 [H7 [H8 H9]]]].
    unfold plop2 in H8. move/eqP in H8.
    apply/ltP.
    apply List.nth_error_Some. by rewrite H8.
  - invert_e_typing.
    destruct ts => //=; destruct t1s => //=; clear H1.
    assert (k+1 < length (tc_label (upd_label C ([::ts1] ++ tc_label C)))).
    { eapply IHHLF; eauto.
      repeat (f_equal; try by lias). }
    simpl in H0. by lias.
Qed.

Lemma return_reduce_return_some: forall n lh es s C ts2,
    lfilled n lh [::Basic Return] es ->
    e_typing s C es (Tf [::] ts2) ->
    tc_return C <> None.
Proof.
  move => n lh es s C ts2 HLF.
  generalize dependent s. generalize dependent C. generalize dependent ts2.
  move/lfilledP in HLF.
  dependent induction HLF; subst; move => ts2 C s HType.
  - invert_e_typing.
    destruct ts; destruct t1s => //=; clear H1.
    apply et_to_bet in H5; auto_basic.
    simpl in H5. apply Return_typing in H5.
    destruct H5 as [ts [ts' [H7 H8]]]. subst.
    by rewrite H8.
  - invert_e_typing.
    destruct ts; destruct t1s => //=; clear H1.
    assert (tc_return (upd_label C ([::ts1] ++ tc_label C)) <> None); first by eapply IHHLF; eauto.
    by simpl in H0.
Qed.

Lemma br_reduce_extract_vs: forall n k lh es s C ts ts2,
    lfilled n lh [::Basic (Br (n + k))] es ->
    e_typing s C es (Tf [::] ts2) ->
    List.nth_error (tc_label C) k = Some ts ->
    exists vs lh', const_list vs /\
      lfilled n lh' (vs ++ [::Basic (Br (n + k))]) es /\
      length vs = length ts.
Proof.
  move => n k lh es s C ts ts2 HLF.
  move/lfilledP in HLF.
  generalize dependent ts. generalize dependent ts2.
  generalize dependent C. generalize dependent s.
  dependent induction HLF; subst; move => s C ts2 ts HType HN.
  - invert_e_typing.
    destruct ts0; destruct t1s => //; clear H1.
    rewrite add0n in H5.
    apply et_to_bet in H5; auto_basic.
    simpl in H5.
    apply Break_typing in H5.
    destruct H5 as [ts3 [ts3' [H7 [H8 H9]]]]. subst.
    unfold plop2 in H8. move/eqP in H8.
    rewrite HN in H8. inversion H8. subst.
    apply et_to_bet in H3; last by apply const_list_is_basic.
    apply const_es_exists in H.
    destruct H as [vs' H]. subst.
    apply Const_list_typing in H3. simpl in H3.
    rewrite catA in H3. symmetry in H3.
    apply cat_split in H3. destruct H3.
    replace vs' with (take (size (ts1 ++ ts3')) vs' ++ drop (size (ts1 ++ ts3')) vs'); last by apply cat_take_drop.
    exists (v_to_e_list (drop (size (ts1 ++ ts3')) vs')), (LBase (v_to_e_list (take (size (ts1 ++ ts3')) vs')) es').
    repeat split.
    + by apply v_to_e_is_const_list.
    + apply/lfilledP.
      rewrite -v_to_e_cat. rewrite -catA.
      rewrite cat_abcd_a_bc_d.
      by apply LfilledBase; apply v_to_e_is_const_list.
    + rewrite H0.
      repeat rewrite length_is_size.
      rewrite v_to_e_size. rewrite -map_drop.
      by rewrite size_map.
  - invert_e_typing.
    destruct ts0; destruct t1s => //; clear H1.
    edestruct IHHLF; eauto.
    { instantiate (1 := k.+1).
      repeat (f_equal; try by lias). }
    {  simpl. by eauto. }
    destruct H0 as [lh2 [HConst [HLF2 HLength]]].
    replace (k0.+1+k) with (k0+k.+1); last by lias.
    repeat eexists. repeat split => //; eauto.
    move/lfilledP in HLF2. apply/lfilledP.
    instantiate (1 := (LRec vs (length ts2) es' lh2 es'')).
    apply LfilledRec => //.
    by apply HLength.
Qed.

Lemma return_reduce_extract_vs: forall n lh es s C ts ts2,
    lfilled n lh [::Basic Return] es ->
    e_typing s C es (Tf [::] ts2) ->
    tc_return C = Some ts ->
    exists vs lh', const_list vs /\
      lfilled n lh' (vs ++ [::Basic Return]) es /\
      length vs = length ts.
Proof.
  move => n lh es s C ts ts2 HLF.
  move/lfilledP in HLF.
  generalize dependent ts. generalize dependent ts2.
  generalize dependent C. generalize dependent s.
  dependent induction HLF; subst; move => s C ts2 ts HType HN.
  - invert_e_typing.
    destruct ts0; destruct t1s => //; clear H1.
    apply et_to_bet in H5; auto_basic.
    simpl in H5.
    apply Return_typing in H5.
    destruct H5 as [ts2 [ts2' [H7 H8]]]. subst.
    rewrite HN in H8. inversion H8. subst.
    apply et_to_bet in H3; last by apply const_list_is_basic.
    apply const_es_exists in H.
    destruct H as [vs' H]. subst.
    apply Const_list_typing in H3. simpl in H3.
    rewrite catA in H3. symmetry in H3.
    apply cat_split in H3. destruct H3.
    replace vs' with (take (size (ts1 ++ ts2')) vs' ++ drop (size (ts1 ++ ts2')) vs'); last by apply cat_take_drop.
    exists (v_to_e_list (drop (size (ts1 ++ ts2')) vs')), (LBase (v_to_e_list (take (size (ts1 ++ ts2')) vs')) es').
    repeat split.
    + by apply v_to_e_is_const_list.
    + apply/lfilledP.
      rewrite -v_to_e_cat. rewrite -catA.
      rewrite cat_abcd_a_bc_d.
      by apply LfilledBase; apply v_to_e_is_const_list.
    + rewrite H0.
      repeat rewrite length_is_size.
      rewrite v_to_e_size. rewrite -map_drop.
      by rewrite size_map.
  - invert_e_typing.
    destruct ts0; destruct t1s => //; clear H1.
    edestruct IHHLF; eauto.
    destruct H0 as [lh2 [HConst [HLF2 HLength]]].
    repeat eexists. repeat split => //; eauto.
    move/lfilledP in HLF2. apply/lfilledP.
    instantiate (1 := (LRec vs (length ts2) es' lh2 es'')).
    apply LfilledRec => //.
    by apply HLength.
Qed.

Lemma le_add: forall n m,
    n <= m ->
    exists k, m = n+k.
Proof.
  move => n m. generalize dependent n.
  induction m => //=; move => n H.
  - destruct n => //=. by exists 0.
  - destruct n => //=.
    + by exists (m.+1).
    + apply IHm in H. destruct H as [k H].
      exists k. by lias.
Qed.

(*
  These two guarantees that the extra conditions we put in progress_e are true -- the second
    being true only if the function doesn't return anything (so we are not in the middle of some
    Local functions).
*)
Lemma s_typing_lf_br: forall s rs i vs es ts,
    s_typing s rs i vs es ts ->
    (forall n lh k, lfilled n lh [::Basic (Br k)] es -> k < n).
Proof.
  move => s rs i vs es ts HType n lh k HLF.
  inversion HType; subst.
  destruct (k<n) eqn: H3 => //=.
  move/ltP in H3.
  assert (n <= k); first by lias.
  apply le_add in H0.
  destruct H0 as [j H0]. subst.
  clear H3.
  eapply br_reduce_label_length in H1; eauto.
  simpl in H1.
  assert (tc_label C0 = [::]); first by eapply inst_t_context_label_empty; eauto.
  by rewrite H0 in H1.
Qed.

Lemma s_typing_lf_return: forall s i vs es ts,
    s_typing s None i vs es ts ->
    (forall n, not_lf_return es n).
Proof.
  unfold not_lf_return.
  move => s i vs es ts HType n lh HContra.
  inversion HType; subst.
  by eapply return_reduce_return_some in H1; eauto.
Qed.

Lemma t_progress_e: forall s i C C' vs vcs es tf ts1 ts2 lab ret,
    e_typing s C es tf ->
    tf = Tf ts1 ts2 ->
    C = (upd_label (upd_local_return C' (map typeof vs) ret) lab) ->
    inst_typing s i C' ->
    map typeof vcs = ts1 ->
    store_typing s ->
    (forall n lh k, lfilled n lh [::Basic (Br k)] es -> k < n) ->
    (forall n, not_lf_return es n) ->
    terminal_form (v_to_e_list vcs ++ es) \/
    exists s' vs' es', reduce s vs (v_to_e_list vcs ++ es) i s' vs' es'.
Proof.
  (* e_typing *)
  move => s i C C' vs vcs es tf ts1 ts2 lab ret HType.
  move: i C' vs vcs ts1 ts2 lab ret.
  (* Initially I had the wrong order of lab and ret --
       The error message here is extremely misleading *)
  apply e_typing_ind' with (e := HType)
    (P := fun s C es tf (_ : e_typing s C es tf) => forall i C' vs vcs ts1 ts2 lab ret,
              tf = Tf ts1 ts2 ->
              C = (upd_label (upd_local_return C' (map typeof vs) ret) lab) ->
              inst_typing s i C' ->
              map typeof vcs = ts1 ->
              store_typing s ->
              (forall n lh k, lfilled n lh [::Basic (Br k)] es -> k < n) ->
              (forall n, not_lf_return es n) ->
              terminal_form (v_to_e_list vcs ++ es) \/
              exists s' vs' es', reduce s vs (v_to_e_list vcs ++ es) i s' vs' es')
    (P0 := fun s rs i vs es ts (_ : s_typing s rs i vs es ts) =>
              store_typing s ->
              (forall n lh k, lfilled n lh [::Basic (Br k)] es -> k < n) ->
              (forall n, not_lf_return es n) ->
              (const_list es /\ length es = length ts) \/
              es = [::Trap] \/
              exists s' vs' es', reduce s vs es i s' vs' es'); clear.
  (* The previous variables s/C/es/tf still lingers here so we need to clear *)
(*  generalize dependent vcs.
  dependent induction HType; subst; move => vcs HIT HConstType HST HBrDepth HNRet. *)
  - (* Basic *)
    move => s C bes tf HType.
    move => i C' vs vcs ts1 ts2 lab ret HTF HContext HInst HConstType HST HBrDepth HNRet.
    subst.
    eapply t_progress_be in HType; try instantiate (1 := vs) in HType; try by eauto.
    destruct HType as [HType | [s' [vs' [es' HType]]]].
    + left.
      unfold terminal_form; left.
      apply const_list_concat => //. by apply v_to_e_is_const_list.
    + right.
      repeat eexists. by apply HType.
    + unfold not_lf_br. move => k lh HContra.
      by apply HBrDepth in HContra.
  - (* Composition *)
    move => s C es e t1s t2s t3s HType1 IHHType1 HType2 IHHType2.
    move => i C' vs vcs ts1 ts2 lab ret HTF HContext HInst HConstType HST HBrDepth HNRet.
    inversion HTF; subst.
    edestruct IHHType1; eauto.
    { move => n lh k HLF.
      eapply lf_composition in HLF.
      destruct HLF as [lh' HLF].
      instantiate (1 := [::e]) in HLF.
      eapply HBrDepth.
      by apply HLF. }
    { move => n.
      eapply nlfret_right. by apply HNRet. }
    + (* Terminal *)
      unfold terminal_form in H. destruct H.
      * (* Const *)
        apply const_list_split in H. destruct H as [HC1 HC2].
        apply et_to_bet in HType1; last by apply const_list_is_basic.
        apply const_es_exists in HC2.
        destruct HC2 as [esv HC2]. subst.
        apply Const_list_typing in HType1. subst.
        edestruct IHHType2; eauto.
        { by apply map_cat. }
        { move => n lh k HLF.
          eapply lf_composition_left in HLF.
          instantiate (1 := v_to_e_list esv) in HLF.
          destruct HLF as [lh' HLF].
          eapply HBrDepth; eauto.
          by apply v_to_e_is_const_list. }
        { move => n.
          eapply nlfret_left.
          instantiate (1 := v_to_e_list esv); first by apply v_to_e_is_const_list.
          by apply HNRet. }
        -- (* Terminal *)
          unfold terminal_form in H. destruct H.
          ++ left. unfold terminal_form. left.
             rewrite -v_to_e_cat in H.
             by rewrite catA.
          ++ apply extract_list1 in H. destruct H.
             rewrite -v_to_e_cat in H.
             destruct vcs => //=.
             destruct esv => //=.
             left. subst. by apply terminal_trap.
        -- (* reduce *)
          rewrite -v_to_e_cat in H.
          rewrite -catA in H.
          by right.
      * (* Trap *)
        destruct vcs => //=; destruct es => //=; destruct es => //=.
        simpl in H. inversion H. subst.
        right.
        exists s, vs, [::Trap].
        apply r_simple.
        eapply rs_trap => //.
        instantiate (1 := (LBase [::] [::e])).
        apply/lfilledP.
        by apply LfilledBase => //=; apply v_to_e_is_const_list.
    + (* reduce *)
      destruct H as [s' [vs' [es' HReduce]]].
      right.
      exists s', vs', (es' ++ [::e]).
      eapply r_label; eauto; try apply/lfilledP.
      * assert (lfilledInd 0 (LBase [::] [::e]) (v_to_e_list vcs ++ es) ([::] ++ (v_to_e_list vcs ++ es) ++ [::e])); first by apply LfilledBase.
        simpl in H. rewrite -catA in H. by apply H.
      * by apply LfilledBase.
  - (* Weakening *)
    (* This is interetingly easy. Think more carefully: the only part that is
       relevant in the reduction is ts1, but ts1 is only required for typing the
       const list. So we just separate the new const list into 2 parts and add
       the first part to the result correspondingly! *)
    move => s C es ts t1s t2s HType IHHType.
    move => i C' vs vcs ts1 ts2 lab ret HTF HContext HInst HConstType HST HBrDepth HNRet.
    inversion HTF; subst.
    symmetry in H0. apply cat_split in H0. destruct H0 as [HCT1 HCT2].
    rewrite - map_take in HCT1.
    rewrite - map_drop in HCT2.
    assert (vcs = take (size ts) vcs ++ drop (size ts) vcs); first by symmetry; apply cat_take_drop.
    rewrite H. rewrite - v_to_e_cat.
    edestruct IHHType; eauto.
    + (* Terminal *)
      unfold terminal_form in H0.
      destruct H0 => //=.
      * (* Const *)
        left. unfold terminal_form. left.
        rewrite -catA. apply const_list_concat => //.
        by apply v_to_e_is_const_list.
      * (* Trap *)
        apply v_e_trap in H0; last by apply v_to_e_is_const_list.
        destruct H0. subst.
        rewrite H0.
        destruct (drop (size ts) vcs) eqn:HDrop => //=.
        clear H0. rewrite cats0 in H. rewrite -H.
        rewrite cats0.
        destruct vcs => //.
        -- left. by apply terminal_trap.
        -- right.
           exists s, vs, [::Trap].
           apply r_simple.
           apply reduce_trap_left => //.
           by apply v_to_e_is_const_list.
    + (* reduce *)
      destruct H0 as [s' [vs' [es' HReduce]]].
      right.
      exists s', vs', (v_to_e_list (take (size ts) vcs) ++ es').
      rewrite -catA.
      by apply reduce_composition_left => //; apply v_to_e_is_const_list.
  - (* Trap *)
    destruct vcs => //; first by left; apply terminal_trap.
    right.
    exists s, vs, [::Trap].
    apply r_simple.
    apply reduce_trap_left => //.
    by apply v_to_e_is_const_list.
  - (* Local *)
    move => s C n j vs0 es ts HType IHHType HLength.
    move => i C' vs vcs ts1 ts2 lab ret HTF HContext HInst HConstType HST HBrDepth HNRet.
    inversion HTF; subst; clear HTF.
    symmetry in H0.
    invert_typeof_vcs.
    right.
    destruct (return_reduce_decidable es) as [HEMT | HEMF].
    { inversion HType; subst.
      unfold return_reduce in HEMT.
      destruct HEMT as [n [lh HLF]].
      (* HEMT is almost what we need to prove the rs_return reduction, but we also need to prove
           that there are some consts of suitable length before the [::Basic Return] as well.
         Done as a separate lemma. *)
      eapply return_reduce_extract_vs in HLF; eauto.
      instantiate (1 := ts2) in HLF.
      destruct HLF as [cs [lh' [HConst [HLF2 HLength]]]].
      repeat eexists.
      apply r_simple.
      eapply rs_return; eauto.
      by [].
    }
    edestruct IHHType as [ | [ | ]]; eauto.
    {
      move => n lh k HLF.
      by eapply s_typing_lf_br in HLF; eauto.
    }
    { unfold return_reduce in HEMF. unfold not_lf_return.
      move => n lh HContra.
      apply HEMF. by eauto.
    }
    + (* Const *)
      destruct H.
      exists s, vs, es.
      apply r_simple.
      by apply rs_local_const.
    + (* Trap *)
      subst.
      exists s, vs, [::Trap].
      apply r_simple.
      by apply rs_local_trap.
    + (* reduce *)
      destruct H as [s' [vs' [es' HReduce]]].
      exists s', vs, [::Local (length ts2) j vs' es'].
      by apply r_local; apply HReduce.
  - (* Invoke *)
    move => s C cl tf HType.
    move => i C' vs vcs ts1 ts2 lab ret HTF HContext HInst HConstType HST HBrDepth HNRet.
    inversion HType; subst.
    inversion H5; subst; clear H5.
    + (* Native *)
      (* Very weirdly, this case requires almost nothing.
         Take some time and look at this again later. *)
      right.
      exists s, vs, [:: Local (length ts2) i0 (vcs ++ n_zeros ts) [::Basic (Block (Tf [::] ts2) es)]].
      eapply r_invoke_native; eauto.
      repeat rewrite length_is_size. by rewrite size_map.
    + (* Host *)
      right.
      (* There are two possible reduction paths dependning on whether the host
         call was successful. However for the proof here we just have to show that
         on exists -- so just use the easier failure case. *)
      exists s, vs, [::Trap].
      eapply r_invoke_host_failure; eauto.
      repeat rewrite length_is_size.
      by rewrite size_map.
  - (* Label *)
    move => s C e0s es ts t2s n HType1 IHHType1 HType2 IHHType2 HLength.
    move => i C' vs vcs ts1 ts2 lab ret HTF HContext HInst HConstType HST HBrDepth HNRet.
    inversion HTF; subst.
    symmetry in H0. invert_typeof_vcs.
    rewrite upd_label_overwrite in HType2. simpl in HType2.
    destruct (br_reduce_decidable es) as [HEMT | HEMF].
    { unfold br_reduce in HEMT.
      destruct HEMT as [n [lh HLF]].
      right. 
      assert (lfilled n lh [::Basic (Br (n+0))] es); first by rewrite addn0.
      eapply br_reduce_extract_vs in H => //; eauto.
      instantiate (1 := ts) in H.
      destruct H as [cs [lh' [HConst [HLF2 HLength]]]].
      rewrite addn0 in HLF2.
      repeat eexists.
      apply r_simple.
      eapply rs_br; eauto.
      by [].
    }
    edestruct IHHType2; eauto.
    { rewrite upd_label_overwrite. simpl. eauto. }
    { unfold br_reduce in HEMF.
      move => n lh k HLF.
      assert (k < n.+1).
      eapply HBrDepth.
      move/lfilledP in HLF.
      apply/lfilledP.
      assert (lfilledInd (n.+1) (LRec [::] (length ts) e0s lh [::]) [::Basic (Br k)] ([::] ++ [::Label (length ts) e0s es] ++ [::])); first by apply LfilledRec.
      rewrite cats0 in H. simpl in H.
      apply H.
      rewrite ltnS in H.
      rewrite leq_eqVlt in H.
      remove_bools_options => //.
      subst.
      exfalso.
      apply HEMF. repeat eexists. by apply HLF.
    }
    { unfold not_lf_return.
      move => n lh HContra.
      unfold not_lf_return in HNRet.
      eapply HNRet.
      move/lfilledP in HContra.
      apply/lfilledP.
      assert (lfilledInd (n.+1) (LRec [::] (length ts) e0s lh [::]) [::Basic Return] ([::] ++ [::Label (length ts) e0s es] ++ [::])); first by apply LfilledRec.
      by apply H.
    }
    + (* Terminal *)
      apply terminal_form_v_e in H.
      unfold terminal_form in H. destruct H.
      * (* Const *)
        right.
        exists s, vs, es.
        apply r_simple.
        by apply rs_label_const.
      * (* Trap *)
        right. subst.
        exists s, vs, [::Trap].
        apply r_simple.
        by apply rs_label_trap.
        by apply v_to_e_is_const_list.
    + (* reduce *)
      (* This is also surprisingly easy... *)
      destruct H as [s' [vs' [es' HReduce]]].
      right.
      simpl in HReduce.
      exists s', vs', [::Label (length ts) e0s es'].
      by eapply r_label; eauto; apply label_lfilled1.
  - (* s_typing *)
    move => s j vs0 es rs ts C C0 tvs HIT HContext HType IHHType HRetType HST HBrDepth HNRet.
    subst.
    edestruct IHHType; eauto.
    { (* Context *)
      assert (tc_local C0  = [::]); first by eapply inst_t_context_local_empty; eauto.
      rewrite H. simpl.
      replace (upd_local_return C0 tvs rs) with
          (upd_label (upd_local_return C0 tvs rs) [::]); first by eauto.
      (* replace *)
      assert (tc_label (upd_local_return C0 tvs rs) = [::]).
      { simpl. by eapply inst_t_context_label_empty; eauto. }
      rewrite -H0.
      by apply upd_label_unchanged. }
    { by instantiate (1 := [::]). }
    + unfold terminal_form in H. destruct H.
      * (* Const *)
        left. split => //.
        apply et_to_bet in HType; last by apply const_list_is_basic.
        simpl in H.
        apply const_es_exists in H. destruct H as [es' H]. subst.
        apply Const_list_typing in HType. subst.
        repeat rewrite length_is_size. simpl.
        rewrite v_to_e_size. by rewrite size_map.
      * (* Trap *)
        right. by left.
    + (* reduce *)
       simpl in H. right. by right.
Qed.

Theorem t_progress: forall s vs es i ts,
    config_typing i s vs es ts ->
    terminal_form es \/
    exists s' vs' es', reduce s vs es i s' vs' es'.
Proof.
  move => s vs es i ts HType.
  inversion HType. subst.
  inversion H0. subst.
  eapply t_progress_e with (vcs := [::]) (ret := None) (lab := [::]) in H3; eauto.
  - assert (tc_local C0 = [::]); first by eapply inst_t_context_local_empty; eauto.
    rewrite H2. simpl.
    replace (upd_local_return C0 tvs None) with
        (upd_label (upd_local_return C0 tvs None) [::]); first by eauto.
    (* replace *)
    assert (tc_label (upd_local_return C0 tvs None) = [::]).
    { simpl. by eapply inst_t_context_label_empty; eauto. }
    rewrite -H5.
    by apply upd_label_unchanged. 
  - by eapply s_typing_lf_br; eauto.
  - by eapply s_typing_lf_return; eauto.
Qed.

End Host.

