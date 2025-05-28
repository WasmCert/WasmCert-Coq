(** Soundness and correctness of the type checker **)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program Wf_nat BinNums NArith.
From Wasm Require Import type_checker typing_inversion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Context {hfc: host_function_class}.

Definition ct_subtyping (ct1 ct2: checker_type) :=
  c_types_agree ct1 ct2.(CT_type) &&
    ((ct1.(CT_unr) == true) || (ct2.(CT_unr) == false)).

Notation "ct1 <ct: ct2" := (ct_subtyping ct1 ct2) (at level 5).

Lemma expand_t_context_reverse: forall C tb tf,
    expand_t C tb = Some tf ->
    expand_t (context_reverse C) tb = Some (rev_tf tf).
Proof.
  intros.
  unfold expand_t in *; destruct tb => //=; first by rewrite lookup_N_map H.
  by remove_bools_options.
Qed.

Lemma rev_tfK:
  involutive rev_tf.
Proof.
  move => [tx ty] => /=.
  by repeat rewrite revK.
Qed.
  
Lemma context_reverseK:
    involutive context_reverse.
Proof.
  move => C.
  destruct C; unfold context_reverse => /=; f_equal; try rewrite mapK => //; try (by apply rev_tfK); try by apply revK.
  destruct tc_return => //=; by rewrite revK.
Qed.

Lemma upd_label_context_reverse: forall C labs,
    upd_label (context_reverse C) labs = context_reverse (upd_label C (map rev labs)).
Proof.
  move => C labs.
  unfold upd_label, upd_local_label_return, context_reverse => /=; f_equal.
  rewrite mapK => //.
  by apply revK.
Qed.
  
Lemma consume_nil: forall ct,
    consume ct nil = Some ct.
Proof.
  by destruct ct => //.
Qed.

Lemma consume_self: forall ts unr,
    consume <<ts, unr>> ts = Some <<nil, unr>>.
Proof.
  induction ts => //=; by resolve_subtyping.
Qed.

Lemma consume_prefix: forall ts1 ts2 unr,
    consume << ts1 ++ ts2, unr>> ts1 = Some <<ts2, unr>>.
Proof.
  induction ts1; destruct ts2 => //=; by resolve_subtyping.
Qed.

Lemma combine_rev {T: Type}: forall (l1 l2: list T),
    length l1 = length l2 ->
    List.combine l1 l2 = rev (List.combine (rev l1) (rev l2)).
Proof.
  induction l1; destruct l2 => //=; move => Hlen.
  do 2 rewrite rev_cons.
  do 2 rewrite - cats1.
  rewrite combine_app; last by do 2 rewrite rev_length; injection Hlen.
  rewrite cats1 rev_rcons.
  f_equal; apply IHl1; by injection Hlen.
Qed.

Lemma common_lab_h_spec_acc: forall iss lab_c tx ts,
    common_lab_h iss lab_c tx = Some ts ->
    ts <ts: tx.
Proof.
  induction iss; move => lab_c tx ts /= Hcommon => //=.
  - by injection Hcommon as <-; resolve_subtyping.
  - remove_bools_options.
    apply IHiss in Hcommon.
    rewrite ts_inf_comm in Hoption0.
    apply ts_inf_sub in Hoption0.
    by resolve_subtyping.
Qed.
    
Lemma common_lab_h_spec: forall iss lab_c tx ts i labid,
    common_lab_h iss lab_c tx = Some ts ->
    List.nth_error iss i = Some labid ->
    exists tcs, List.nth_error lab_c (N.to_nat labid) = Some tcs /\
    ts <ts: tcs.
Proof.
  induction iss; move => lab_c tx ts [ | i] labid /= Hcommon Hnthi => //=; remove_bools_options.
  - unfold lookup_N in Hoption.
    exists l.
    rewrite Hoption; split => //.
    apply common_lab_h_spec_acc in Hcommon.
    apply ts_inf_sub in Hoption0.
    by resolve_subtyping.
  - by eapply IHiss; eauto.
Qed.
    
Lemma common_lab_spec: forall iss lab_c ts i labid,
    common_lab iss lab_c = Some ts ->
    List.nth_error iss i = Some labid ->
    exists tcs, List.nth_error lab_c (N.to_nat labid) = Some tcs /\
    ts <ts: tcs.
Proof.
  move => iss lab_c ts i labid Hcommon Hnthi.
  unfold common_lab in Hcommon.
  destruct iss => //; remove_bools_options.
  destruct i; simpl in *.
  - injection Hnthi as ->.
    apply common_lab_h_spec_acc in Hcommon.
    unfold lookup_N in Hoption.
    by exists l.
  - by eapply common_lab_h_spec in Hcommon; eauto.
Qed.

Lemma common_lab_h_cond: forall iss lab_c tx ts,
    List.Forall
      (fun i : N =>
         exists ts' : result_type,
           lookup_N lab_c i = Some ts' /\ tx <ts: ts')
      iss ->
    tx <ts: ts ->
    exists ty, common_lab_h iss lab_c ts = Some ty /\
            tx <ts: ty.
Proof.
  induction iss; move => lab_c tx ts Hforall Hsub => //=; remove_bools_options.
  - by exists ts.
  - inversion Hforall as [ | ?? Hlookup Hrest]; subst; clear Hforall.
    destruct Hlookup as [ts' [Hlablookup Hsubts']].
    rewrite Hlablookup.
    specialize (ts_inf_exists Hsubts' Hsub) as [tsinf Hinfeq].
    rewrite Hinfeq.
    apply IHiss => //.
    by apply (ts_inf_strict Hsubts' Hsub).
Qed.
    
Lemma common_lab_cond: forall iss lab_c tx,
    iss <> nil ->
    List.Forall
      (fun i : N =>
         exists ts' : result_type,
           lookup_N lab_c i = Some ts' /\ tx <ts: ts')
      iss ->
    exists ty, common_lab iss lab_c = Some ty /\
            tx <ts: ty.
Proof.
  move => iss lab_c ts Hnotnil Hforall.
  unfold common_lab; destruct iss => //.
  inversion Hforall as [ | ?? Hlookup Hrest]; subst; clear Hforall.
  destruct Hlookup as [ts' [Hlablookup Hsubts']].
  rewrite Hlablookup.
  by eapply common_lab_h_cond in Hrest; eauto.
Qed.
  
Lemma common_lab_h_rev: forall iss lab_c tx ts,
    common_lab_h iss lab_c tx = Some ts ->
    common_lab_h iss (map rev lab_c) (rev tx) = Some (rev ts).
Proof.
  induction iss => //; move => lab_c tx ts /= Hcommon.
  - by injection Hcommon as <-.
  - remove_bools_options.
    rewrite lookup_N_map Hoption => /=.
    unfold ts_inf in *; repeat rewrite rev_length.
    remove_bools_options.
    apply IHiss in Hcommon.
    rewrite <- Hcommon.
    f_equal.
    rewrite combine_rev; last by repeat rewrite rev_length; move/eqP in Hif.
    repeat rewrite revK.
    by rewrite map_rev.
Qed.
  
Lemma common_lab_rev: forall iss lab_c ts,
    common_lab iss lab_c = Some ts ->
    common_lab iss (map rev lab_c) = Some (rev ts).
Proof.
  unfold common_lab.
  move => iss lab_c ts Hlab.
  destruct iss => //; remove_bools_options.
  rewrite lookup_N_map Hoption => /=.
  by apply common_lab_h_rev.
Qed.

Lemma c_types_agree_extend: forall ts1 ts2 ts,
    c_types_agree <<ts1, false>> ts2 ->
    c_types_agree <<ts1 ++ ts, false>> (ts2 ++ ts).
Proof.
  move => ts1 ts2 ts Hagree.
  by unfold c_types_agree in *; simpl in *; resolve_subtyping.
Qed.

Lemma c_types_agree_extend_top: forall ts1 ts2 ts unr,
    c_types_agree <<ts1, unr>> ts2 ->
    c_types_agree <<ts1, true>> (ts2 ++ ts).
Proof.
  move => ts1 ts2 ts unr Hagree.
  unfold c_types_agree in *; simpl in *; resolve_subtyping.
  destruct unr.
  - rewrite takel_cat => //.
    apply values_subtyping_size in Hagree; rewrite size_take_min in Hagree.
    by symmetry in Hagree; move/minn_idPl in Hagree.
  - replace (size ts1) with (size ts2); last by apply values_subtyping_size in Hagree.
    by rewrite take_size_cat.
Qed.
             
Ltac simplify_tc_goal := 
  repeat match goal with
  | H: context C [take 0 _] |- _ =>
      rewrite take0 in H
  | H: context C [drop 0 _] |- _ =>
      rewrite drop0 in H
  | H: ?expr = _ |-
    context [match ?expr with | _ => _ end] =>
      rewrite H
  | H: Some _ = Some _ |- _ =>
    injection H as H; try subst H
  | H: is_true ?expr |-
    context [if ?expr then _ else _] =>
      rewrite H
  | H: ?expr = _ |-
    context [?expr] =>
      rewrite H
(*  | H: unop_type_agree ?t ?op = true |- _ =>
      destruct t, op; inversion H; subst; clear H
  | H: binop_type_agree ?t ?op = true |- _ =>
      destruct t, op; inversion H; subst; clear H
  | H: relop_type_agree ?t ?op = true |- _ =>
      destruct t, op; inversion H; subst; clear H*)
  | H: lookup_N ?l ?n = ?x
    |- context [lookup_N (map _ ?l) ?n] =>
    rewrite lookup_N_map H
  | H: expand_t ?C ?tb = ?tf
    |- context [expand_t (context_reverse ?C) ?tb] =>
      rewrite (expand_t_context_reverse H)
  | H: context C [ match ?u with | Unop_i _ => _ | Unop_f _ | _ => _ end ] |- _ => destruct u => //=
  | H: context C [ match ?b with | Binop_i _ => _ | Binop_f _ => _ end ] |- _ => destruct b => //=
    | H: context C [ match ?r with | Relop_i _ => _ | Relop_f _ => _ end ] |- _ => destruct r => //=
(*                                                                                 | H: context C [ lookup_N_safe _ _ ] |- _ => setoid_rewrite lookup_N_safe_spec in H
                                                                                 | |- context [ lookup_N_safe _ _ ] => setoid_rewrite lookup_N_safe_spec*)
  | |- context [ consume _ nil ] => rewrite consume_nil
  | |- context [ consume <<?ts, _>> ?ts ] => rewrite consume_self
  | |- context [ consume <<(?ts ++ _), _>> ?ts ] => rewrite consume_prefix
  | |- context [ take 0 _ ] => rewrite take0
  | |- context [ _ ++ nil ] => rewrite cats0
  | |- context [ rev (_ ++ _) ] => rewrite rev_cat
  | |- context [ rev [::?x] ] => replace (rev [::x]) with [::x]; last by lias
  | |- context [ _ = _ ] => rewrite eq_refl
  | |- context [ _ == _ ] => rewrite eq_refl
  | _ => simpl in *; subst; remove_bools_options; resolve_subtyping => //
  end.

Ltac fold_remember_check :=
  repeat match goal with
         | H: context C [List.fold_left (check_single ?C) ?l ?ct] |- _ =>
              fold (check C l ct) in H; let res_check := fresh "res_check" in remember (check C l ct) as res_check
         end.

(* Measure for induction on basic_instruction *)
Fixpoint be_size_single (be: basic_instruction): nat :=
  match be with
  | BI_block _ l => 1 + (List.fold_left addn (map be_size_single l)) 1 + size l
  | BI_loop _ l => 1 + (List.fold_left addn (map be_size_single l)) 1 + size l
  | BI_if _ l1 l2 => 1 + ((List.fold_left addn (map be_size_single l1) 1) + size l1) + ((List.fold_left addn (map be_size_single l2) 1) + size l2)
  | _ => 1
  end.

Definition be_size_list (bes: list basic_instruction) :=
  (List.fold_left addn (map be_size_single bes) 1) + size bes.

Lemma fold_left_rcons {A B: Type} (f: A -> B -> A) (l: list B) (x: B) (acc: A):
  List.fold_left f (rcons l x) acc = f (List.fold_left f l acc) x.
Proof.
  move: f l x acc.
  by induction l => //=.
Qed.
  
Lemma be_size_list_rcons bes e:
  be_size_list (rcons bes e) = be_size_single e + (be_size_list bes) + 1.
Proof.
  unfold be_size_list.
  rewrite map_rcons size_rcons.
  rewrite fold_left_rcons.
  by lias.
Qed.

Lemma check_rcons: forall es e C ts,
  check C (es ++ [::e]) ts = check_single C (check C es ts) e.
Proof.
  by induction es => //=.
Qed.

Lemma consume_reachable: forall ct ts cons,
  consume ct cons = Some <<ts, false>> ->
  ct.(CT_unr) = false.
Proof.
  move => [c_ts unr].
  induction c_ts; destruct cons => //=; move => H; remove_bools_options => //.
  by apply IHc_ts in H.
Qed.
  
Lemma type_update_reachable: forall ct ts cons prod,
  type_update ct cons prod = Some <<ts, false>> ->
  ct.(CT_unr) = false.
Proof.
  unfold type_update.
  move => ct ts cons prod H; remove_bools_options; destruct c; simpl in *; subst.
  by apply consume_reachable in Hoption.
Qed.

Lemma consume_preserve_unr: forall ct1 ct2 l,
    consume ct1 l = Some ct2 ->
    ct1.(CT_unr) = ct2.(CT_unr).
Proof.
  move => ct1 ct2 l.
  move : ct1 ct2.
  induction l => //=; move => ct1 ct2 Hconsume; first by injection Hconsume as <-.
  destruct ct1 as [ts1 u1]; destruct ct2 as [ts2 u2]; simpl in *.
  destruct ts1; remove_bools_options => //; try by inversion Hconsume.
  by apply IHl in Hconsume.
Qed.

Lemma consume_extend: forall l l1 l2 l3 unr,
  consume <<l1, unr>> l = Some <<l3, false>> ->
  consume <<l1 ++ l2, unr>> l = Some <<l3 ++ l2, false>>.
Proof.
  induction l => //=; first by move => ???? H; inversion H.
  destruct l1 => //=; move => l2 ? unr Hconsume; remove_bools_options.
  by apply IHl.
Qed.

Lemma type_update_preserve_unr: forall ct1 ct2 cons prod,
    type_update ct1 cons prod = Some ct2 ->
    ct1.(CT_unr) = ct2.(CT_unr).
Proof.
  move => ct1 ct2 cons prod Hupdate.
  unfold type_update in Hupdate; remove_bools_options.
  by apply consume_preserve_unr in Hoption.
Qed.

Lemma type_update_extend: forall l1 l2 l3 cons prod unr,
  type_update (<<l1, unr>>) cons prod = Some <<l3, false>> ->
  type_update (<<l1 ++ l2, unr>>) cons prod = Some <<l3 ++ l2, false>>.
Proof.
  unfold type_update.
  move => l1 l2 l3 cons prod unr Hupdate.
  specialize (type_update_preserve_unr Hupdate) => /= ?; subst.
  simplify_tc_goal.
  destruct c as [ts [|]]; first by apply consume_preserve_unr in Hoption.
  erewrite consume_extend; eauto.
  unfold produce => //=.
  by rewrite catA.
Qed.

Lemma type_update_top_extend: forall l1 l2 l3 cons prod,
  type_update_top (<<l1, false>>) cons prod = Some <<l3, true>> ->
  type_update_top (<<l1 ++ l2, false>>) cons prod = Some <<l3, true>>.
Proof.
  unfold type_update_top.
  move => l1 l2 l3 cons prod H.
  simplify_tc_goal.
  destruct c as [ts [|]]; first by apply consume_preserve_unr in Hoption.
  by erewrite consume_extend; eauto.
Qed.

Lemma c_types_agree_cons: forall cts unr t t' ts,
    c_types_agree <<t :: cts, unr>> (t' :: ts) <->
    t <t: t' /\ c_types_agree <<cts, unr>> ts.
Proof.
  split.
  - by unfold c_types_agree; move => ?; destruct unr; simplify_tc_goal.
  - by unfold c_types_agree => /=; move => [??]; destruct unr; simplify_tc_goal.
Qed.

Lemma c_types_agree_cons_split: forall cts unr t ts,
    c_types_agree <<t :: cts, unr>> ts ->
    exists t' ts', ts = t' :: ts' /\ t <t: t' /\ c_types_agree <<cts, unr>> ts'.
Proof.
  move => cts unr t [ | t' ts'] Hagree; simplify_tc_goal; try by destruct unr.
  apply c_types_agree_cons in Hagree.
  by eexists; eauto.
Qed.

Lemma c_types_agree_cat_split: forall cts unr ts0 ts,
    c_types_agree <<ts0 ++ cts, unr>> ts ->
    exists ts1 ts2, ts = ts1 ++ ts2 /\ ts0 <ts: ts1 /\ c_types_agree <<cts, unr>> ts2.
Proof.
  move => cts unr ts0.
  move : cts unr.
  induction ts0; move => cts unr ts Hagree; simpl in *.
  - by exists nil, ts.
  - apply c_types_agree_cons_split in Hagree as [t' [ts' [-> [Hsub Hagree]]]].
    apply IHts0 in Hagree as [ts1' [ts2' [-> [Hsub' Hagree']]]].
    exists (t' :: ts1'), ts2'; repeat split => //.
    by lias.
Qed.

Lemma c_types_agree_size_sub: forall cts unr ts,
    size cts = size ts ->
    c_types_agree <<cts, unr>> ts ->
    cts <ts: ts.
Proof.
  move => cts unr ts Hsize Hagree; unfold c_types_agree in Hagree; simplify_tc_goal.
  destruct unr => //.
  by rewrite Hsize take_size in Hagree.
Qed.
  
Lemma c_types_agree_sub_cat: forall cts1 cts2 unr ts1 ts2,
    cts1 <ts: ts1 ->
    c_types_agree <<cts2, unr>> ts2 ->
    c_types_agree <<cts1 ++ cts2, unr>> (ts1 ++ ts2).
Proof.
  induction cts1; move => cts2 unr ts1 ts2 Hsub Hagree; destruct ts1 => //; simplify_tc_goal.
  apply c_types_agree_cons; split => //.
  by apply IHcts1.
Qed.

Lemma c_types_agree_take_cat: forall cts1 cts2 unr ts1 ts2,
    c_types_agree <<cts1, unr>> ts1 ->
    c_types_agree <<cts2, unr>> ts2 ->
    c_types_agree <<cts1 ++ cts2, unr>> (take (size cts1) ts1 ++ ts2).
Proof.
  induction cts1; move => cts2 unr ts1 ts2 Hagree1 Hagree2; destruct ts1 => //; simplify_tc_goal; first by unfold c_types_agree in *; destruct unr; simplify_tc_goal.
  apply c_types_agree_cons_split in Hagree1 as [t' [ts' [Heq [Hsub Hagree]]]]; inversion Heq; subst; clear Heq.
  apply c_types_agree_cons; split => //.
  by apply IHcts1.
Qed.
  
Lemma c_types_agree_size_cat: forall cts1 cts2 unr ts1 ts2,
    size cts1 = size ts1 ->
    c_types_agree <<cts1, unr>> ts1 ->
    c_types_agree <<cts2, unr>> ts2 ->
    c_types_agree <<cts1 ++ cts2, unr>> (ts1 ++ ts2).
Proof.
  intros.
  eapply c_types_agree_take_cat in H1; try by apply H0; eauto.
  by rewrite H take_size in H1.
Qed.
  
Lemma consume_Some_impl: forall ct l ct',
    consume ct l = Some ct' ->
    c_types_agree <<take (size l) ct.(CT_type), ct.(CT_unr)>> l /\
    ct' = << drop (size l) ct.(CT_type), ct.(CT_unr) >>.
Proof.
  move => ct l.
  move: ct.
  induction l => //=; unfold c_types_agree; simplify_tc_goal; move => ct ct' Hconsume.
  - injection Hconsume as <-.
    by destruct ct as [? [|]] => //=; rewrite take0 drop0.
  - destruct ct as [cts [|]]; simpl in *; destruct cts as [ | t cts] => //; simplify_tc_goal; by apply IHl in Hconsume.
Qed.

Lemma consume_Some_spec: forall ct l ct',
    c_types_agree <<take (size l) ct.(CT_type), ct.(CT_unr)>> l ->
    ct' = << drop (size l) ct.(CT_type), ct.(CT_unr) >> ->
    consume ct l = Some ct'.
Proof.
  move => ct l.
  move: ct.
  induction l => //=; move => ct ct' Hagree ->.
  - by rewrite drop0; destruct ct.
  - destruct ct as [[ | t cts] [|]]; simplify_tc_goal; apply c_types_agree_cons in Hagree as [-> Hagree]; by apply IHl.
Qed.

Lemma type_update_Some_impl: forall ct ct' cons prod,
    type_update ct cons prod = Some ct' ->
    (c_types_agree << take (size cons) ct.(CT_type), ct.(CT_unr) >> cons) /\
      ct' = <<prod ++ drop (size cons) ct.(CT_type), ct.(CT_unr)>>.
Proof.
  move => ct ct' cons prod Hupdate.
  unfold type_update, produce in Hupdate; simplify_tc_goal.
  by apply consume_Some_impl in Hoption as [? ->].
Qed.
  
Lemma ct_subtyping_refl:
    reflexive ct_subtyping.
Proof.
  move => [? [|]]; unfold ct_subtyping, c_types_agree; by rewrite take_size; resolve_subtyping.
Qed.

Lemma ct_subtyping_trans:
    transitive ct_subtyping.
Proof.
  move => [cts1 [|]] [cts2 [|]] [cts3 ?]; unfold ct_subtyping, c_types_agree; move => Hsub1 Hsub2; simplify_tc_goal.
  eapply values_subtyping_trans; eauto.
  assert (minn (size cts2) (size cts1) = size cts2) as Hsize.
  { apply values_subtyping_size in H1.
    by rewrite size_take_min in H1.
  }
  apply values_subtyping_take with (n := size cts2) in H.
  by rewrite - take_min Hsize in H.
Qed.

Lemma ct_subtyping_take: forall ct1 ct2 n,
    ct1 <ct: ct2 ->
    ((<<take n ct1.(CT_type), ct1.(CT_unr)>>) <ct: (<<take n ct2.(CT_type), ct2.(CT_unr)>>)).
Proof.
  unfold ct_subtyping, c_types_agree; move => [cts1 [|]] [cts2 unr] n Hsub; simpl in *; simplify_tc_goal.
  repeat rewrite size_take_min; repeat rewrite - take_min; apply values_subtyping_take with (n := n) in H; rewrite - take_min in H; by rewrite minnC minnA minnn.
Qed.
  
Lemma ct_subtyping_drop: forall ct1 ct2 n,
    ct1 <ct: ct2 ->
    ((<<drop n ct1.(CT_type), ct1.(CT_unr)>>) <ct: (<<drop n ct2.(CT_type), ct2.(CT_unr)>>)).
Proof.
  unfold ct_subtyping, c_types_agree; move => [cts1 [|]] [cts2 unr] n Hsub; simpl in *; simplify_tc_goal.
  apply values_subtyping_drop with (n := n) in H.
  rewrite take_drop.
  replace (drop n (take _ _)) with (drop n (take (size cts1) cts2)) => //.
  rewrite size_drop.
  destruct (n <= size cts1) eqn:Hsize; first by rewrite subnK.
  repeat rewrite drop_oversize => //.
  { rewrite size_take_min.
    replace (size cts1 - n) with 0; last by lias.
    rewrite add0n.
    by apply geq_minl.
  }
  {
    rewrite size_take_min.
    assert (size cts1 <= n); first by lias.
    specialize (geq_minl (size cts1) (size cts2)) as ?.
    by lias.
  }
Qed.

Lemma ct_subtyping_prefix: forall cts1 cts2 unr1 unr2 ts1 ts2,
    (<<cts1, unr1>>) <ct: (<<cts2, unr2>>) ->
    ts1 <ts: ts2 ->
    ((<<ts1 ++ cts1, unr1>>) <ct: (<<ts2 ++ cts2, unr2>>)).
Proof.
  unfold ct_subtyping, c_types_agree; move => cts1 cts2 [|] unr2 ts1 ts2 Hsub1 Hsub2; simpl in *; simplify_tc_goal.
  rewrite size_cat.
  replace (size ts1) with (size ts2); last by apply values_subtyping_size in Hsub2.
  rewrite take_size1_cat.
  by resolve_subtyping.
Qed.
  
Lemma c_types_agree_subtyping: forall ct1 ct2 ts1 ts2,
    c_types_agree ct1 ts1 ->
    ct2 <ct: ct1 ->
    ts1 <ts: ts2 ->
    c_types_agree ct2 ts2.
Proof.
  move => [cts1 [|]] [cts2 [|]] ts1 ts2 Hagree Hsub1 Hsub2; unfold ct_subtyping, c_types_agree in *; simpl in *; simplify_tc_goal.
  - assert (size cts2 <= size cts1) as Hsize.
    { apply values_subtyping_size in H.
      rewrite size_take_min in H; symmetry in H.
      by move/minn_idPl in H.
    }
    apply values_subtyping_take with (n := size cts2) in Hsub2.
    apply values_subtyping_take with (n := size cts2) in Hagree.
    do 2 (eapply values_subtyping_trans; eauto).
    by rewrite take_takel => //.
  - apply values_subtyping_take with (n := size cts2) in Hsub2.
    apply values_subtyping_take with (n := size cts2) in Hagree.
    by resolve_subtyping.
Qed.

Lemma consume_subtyping: forall ct1 ct1' ct2 ts,
    consume ct1 ts = Some ct2 ->
    ct1' <ct: ct1 ->  
    exists ct2', consume ct1' ts = Some ct2' /\
            ct2' <ct: ct2.
Proof.
  move => ct1 ct1' ct2 ts Hconsume Hsub.
  apply consume_Some_impl in Hconsume as [Hagree ->].
  exists << drop (size ts) ct1'.(CT_type), ct1'.(CT_unr) >>; split.
  - apply consume_Some_spec => //.
    apply ct_subtyping_take with (n := (size ts)) in Hsub.
    by eapply c_types_agree_subtyping; eauto; resolve_subtyping.
  - by apply ct_subtyping_drop.
Qed.

Lemma type_update_subtyping: forall ct1 ct1' ct2 cons prod,
    type_update ct1 cons prod = Some ct2 ->
    ct1' <ct: ct1 ->  
    exists ct2', type_update ct1' cons prod = Some ct2' /\
            ct2' <ct: ct2.
Proof.
  move => ct1 ct1' ct2 cons prod Hupdate Hsub.
  unfold type_update in *; simplify_tc_goal.
  eapply consume_subtyping in Hoption as [ct2' [Hconsume Hsub']]; eauto.
  rewrite Hconsume.
  unfold produce.
  eexists; split; eauto.
  apply ct_subtyping_prefix; eauto.
  by resolve_subtyping.
Qed.

Lemma type_update_subtyping_top: forall ct1 ct1' ct2 cons prod,
  type_update_top ct1 cons prod = Some ct2 ->
  ct1' <ct: ct1 ->  
  type_update_top ct1' cons prod = Some ct2.
Proof.
  move => ct1 ct1' ct2 cons prod Hupdate Hsub.
  unfold type_update_top in *; simplify_tc_goal.
  eapply consume_subtyping in Hoption as [ct2' [Hconsume Hsub']]; eauto.
  by rewrite Hconsume.
Qed.
  
Lemma check_single_reachable: forall C ct ts e,
  check_single C (Some ct) e = Some <<ts, false>> ->
  ct.(CT_unr) = false.
Proof.
  move => C ct ts e.
  move : C ct ts.
  induction e => /=; move => C ct ts Htc; simplify_tc_goal; (try destruct i; simplify_tc_goal); (try by eapply type_update_reachable; eauto); (try by unfold type_update_top in Htc; simplify_tc_goal).
  (* ref_is_null *)
  - unfold type_update_ref_is_null in Htc.
    destruct ct as [c_ts unr]; simpl in *.
    destruct c_ts, unr => //; by simplify_tc_goal.
  (* drop *)
  - unfold type_update_drop in Htc.
    destruct ct as [c_ts unr]; simpl in *.
    destruct c_ts, unr => //; by simplify_tc_goal.
  (* select *)
  - unfold type_update_select in Htc; simplify_tc_goal.
    + do 2 destruct l => //.
      by eapply type_update_reachable; eauto.
    + destruct ct as [c_ts unr]; simpl in *.
      destruct unr; do 3 (try destruct c_ts as [ | ? c_ts] => //); try by eapply type_update_reachable in Htc.
      * simplify_tc_goal.
        unfold type_update, produce in Htc; simpl in *.
        by simplify_tc_goal.
      * simplify_tc_goal; by eapply type_update_reachable in Htc.
  (* call *)
  - destruct f0; by eapply type_update_reachable; eauto.
  (* call_indirect *)
  - destruct f; by eapply type_update_reachable; eauto.
  (* return_call *)
  - destruct f0; simpl in *.
    by unfold type_update_top in Htc; simplify_tc_goal.
  (* return_call_indirect *)
  - destruct f.
    by unfold type_update_top in Htc; simplify_tc_goal.
Qed.
  
Lemma check_single_None: forall C e,
  check_single C None e = None.
Proof.
  move => C e.
  by destruct e => //=.
Qed.

Lemma check_None: forall C es,
  check C es None = None.
Proof.
  move => C es.
  induction es => //=.
  by rewrite check_single_None.
Qed.

Lemma check_single_extend: forall C e ts ts2 ts0,
  check_single C (Some <<ts, false>>) e = Some <<ts0, false>> ->
  check_single C (Some <<ts ++ ts2, false>>) e = Some <<ts0 ++ ts2, false>>.
Proof.
  move => C e.
  move : C.
  induction e; move => C ts ts2 ts0 Htc; simpl in Htc => //=; simplify_tc_goal; (try destruct i); (try destruct f); (try destruct f0); simplify_tc_goal; (try by apply type_update_extend with (l2 := ts2) in Htc; simplify_tc_goal); (try by unfold type_update_top in *; simplify_tc_goal).
  - by unfold type_update_ref_is_null in *; destruct ts; simplify_tc_goal.
  - by unfold type_update_drop in *; destruct ts; simplify_tc_goal.
  - unfold type_update_select in *.
    destruct o => //.
    + do 2 destruct l => //. by apply type_update_extend with (l2 := ts2) in Htc.
    + simpl in *.
      do 3 (try destruct ts => //; simpl in * ); simplify_tc_goal.
      by apply type_update_extend with (l2 := ts2) in Htc.
Qed.

Lemma check_single_extend_top: forall C e ts ts2 ts0,
  check_single C (Some <<ts, false>>) e = Some <<ts0, true>> ->
  check_single C (Some <<ts ++ ts2, false>>) e = Some <<ts0, true>>.
Proof.
  move => C e.
  move : C.
  induction e; move => C ts ts2 ts0 Htc; simpl in Htc => //=; simplify_tc_goal; (try destruct i); (try destruct f); (try destruct f0); simplify_tc_goal; (try by apply type_update_preserve_unr in Htc); (try by apply type_update_top_extend).
  - by unfold type_update_ref_is_null in *; destruct ts; simplify_tc_goal.
  - by unfold type_update_drop in *; destruct ts; simplify_tc_goal.
  - unfold type_update_select in *.
    destruct o => //.
    + do 2 destruct l => //. by apply type_update_preserve_unr in Htc.
    + simpl in *.
      do 3 (try destruct ts => //; simpl in * ); simplify_tc_goal.
      by apply type_update_preserve_unr in Htc.
Qed.

Lemma value_type_select_subtyping: forall v1 v2 v3 v4 v,
    value_type_select v1 v2 = Some v ->
    v3 <t: v1 ->
    v4 <t: v2 ->
    exists v', value_type_select v3 v4 = Some v' /\ v' <t: v.
Proof.
  unfold value_type_select.
  move => v1 v2 v3 v4 v Hvtselect Hsub1 Hsub2; simplify_tc_goal; move/eqP in Hif; subst.
  - destruct v3, v4 => //; resolve_subtyping; by eexists; eauto; split => //; resolve_subtyping.
  - move/eqP in Hif0; subst.
    destruct v3, v4 => //; resolve_subtyping; by eexists; eauto; split => //; resolve_subtyping.
  - move/eqP in Hif0.
    move/eqP in Hif1; subst.
    destruct v3, v4 => //; resolve_subtyping; (try rewrite eq_refl); by eexists; eauto; split => //; resolve_subtyping.
Qed.
    
Lemma c_types_agree_trans: forall ts ct ts',
  c_types_agree ct ts ->
  c_types_agree <<ts, false>> ts' ->
  c_types_agree ct ts'.
Proof.
  unfold c_types_agree.
  move => ts [c_ts [|]] ts' Hagree1 Hagree2 => /=; by simplify_tc_goal.
Qed.

Lemma c_types_agree_refl: forall ts ct ,
  ts = ct.(CT_type) ->
  c_types_agree ct ts.
Proof.
  unfold c_types_agree.
  move => ts [c_ts [|]] -> => /=; simplify_tc_goal.
  by rewrite take_size; resolve_subtyping.
Qed.

Lemma check_single_subtyping: forall C e ct1 ct1' ct2,
    check_single C (Some ct1) e = Some ct2 ->
    ct1' <ct: ct1 ->  
    exists ct2', check_single C (Some ct1') e = Some ct2' /\
            ct2' <ct: ct2.
Proof.
  move => C e.
  move: C.
  induction e; move => C ct1 ct1' ct2 Hcheck Hsub; simplify_tc_goal; (try destruct i); (try destruct f0); (try destruct f); simplify_tc_goal; (try by eapply type_update_subtyping in Hcheck; eauto); (try by eapply type_update_subtyping_top in Hcheck; eauto; eexists; split; eauto; apply ct_subtyping_refl); (try by eexists; split; eauto).
  - unfold type_update_ref_is_null in *; simpl in *.
    destruct ct1 as [[| t1 ct1] unr]; destruct ct1' as [[|t1' ct1'] [|]]; unfold ct_subtyping, c_types_agree in *; simpl in *; simplify_tc_goal; try by (eexists; split; eauto => //=; try rewrite take0 => //).
    + replace (is_ref_t t1') with true; last by destruct t1, t1'.
      by eexists; split; eauto => /=; resolve_subtyping.
    + replace (is_ref_t t1') with true; last by destruct t1, t1'.
      by eexists; split; eauto => /=; resolve_subtyping.
  - unfold type_update_drop in *; simpl in *.
    destruct ct1 as [[| t1 ct1] unr]; destruct ct1' as [[|t1' ct1'] [|]]; unfold ct_subtyping, c_types_agree in *; simpl in *; simplify_tc_goal; try by (eexists; split; eauto => //=; try rewrite take0 => //; resolve_subtyping).
  - unfold type_update_select in *.
    destruct o => //; simpl in *.
    + do 2 (try destruct l => //).
      by eapply type_update_subtyping in Hcheck; eauto.
    + destruct ct1 as [ts1 unr1]; destruct ct1' as [ts2 unr2]; simpl in *.
      destruct ts1 as [| ? ts1] => //.
      { unfold ct_subtyping, c_types_agree, type_update, produce in *; simplify_tc_goal.
        by eexists; split; eauto.
      }
      destruct ts1 as [| ? ts1] => //.
      { unfold ct_subtyping, c_types_agree, type_update, produce in *; simplify_tc_goal.
        destruct ts2 as [| ? ts2] => //=; first by eexists; split; eauto.
        simplify_tc_goal.
        replace (v0 <t: T_num T_i32) with true; last by symmetry; eapply value_subtyping_trans; eauto.
        by eexists; split; eauto.
      }
      destruct ts1 as [| ? ts1] => //.
      { unfold ct_subtyping, c_types_agree, type_update, produce in *; simplify_tc_goal.
        destruct ts2 as [| ? ts2] => //=; simplify_tc_goal.
        { eexists; split; eauto => /=; resolve_subtyping.
          by destruct v0.
        }
        destruct ts2 as [| ? ts2] => //=; simplify_tc_goal.
        {
          replace (v1 <t: T_num T_i32) with true; last by symmetry; eapply value_subtyping_trans; eauto.
          eexists; split; eauto => /=.
          by destruct v0.
        }
        {
          replace (is_numeric_type v2) with true; last by destruct v0, v2.
          replace (v1 <t: T_num T_i32) with true; last by symmetry; eapply value_subtyping_trans; eauto.
          eexists; split; eauto => /=.
          by rewrite H0.
        }
      }
      { destruct ts2 as [| ? ts2] => //=; simplify_tc_goal.
        { destruct unr2; last by unfold ct_subtyping, c_types_agree in Hsub.
          eapply type_update_subtyping in Hcheck as [ct2' [Hupdate Hagree]]; eauto.
          unfold type_update, produce in *; simplify_tc_goal.
          eexists; split; eauto.
          unfold ct_subtyping, c_types_agree in *; simplify_tc_goal.
          by destruct v3.
        }
        destruct ts2 as [| ? ts2] => //=; simplify_tc_goal.
        { destruct unr2; last by unfold ct_subtyping, c_types_agree in Hsub; simplify_tc_goal.
          eapply type_update_subtyping in Hcheck as [ct2' [Hupdate Hagree]]; eauto.
          unfold type_update, produce in *; simplify_tc_goal.
          eexists; split; eauto.
          unfold ct_subtyping, c_types_agree in *; simplify_tc_goal.
          by destruct v4.
        }
        destruct ts2 as [| ? ts2] => //=; simplify_tc_goal.
        { destruct unr2; last by unfold ct_subtyping, c_types_agree in Hsub; simplify_tc_goal.
          eapply type_update_subtyping in Hcheck as [ct2' [Hupdate Hagree]]; eauto.
          unfold type_update, produce in *; simplify_tc_goal.
          unfold ct_subtyping, c_types_agree in *; simplify_tc_goal.
          replace (is_numeric_type v4) with true => /=; last by destruct v0, v4.
          eexists; split => //=; eauto.
          rewrite Hcons.
          resolve_subtyping.
          do 2 (eapply value_subtyping_trans; eauto).
          unfold value_type_select in Hoption.
          simplify_tc_goal; by destruct v0, v3.
        }
        { assert (exists t, value_type_select v4 v5 = Some t /\ t <t: v3) as [t [Hvtselect Hsubvt]].
          { by unfold type_update, produce, ct_subtyping, c_types_agree in *; destruct unr2; simplify_tc_goal; eapply value_type_select_subtyping; eauto. }
          rewrite Hvtselect.
          eapply type_update_subtyping in Hcheck as [ct2' [Hupdate Hagree]]; eauto.
          unfold type_update, produce in *; simplify_tc_goal.
          eexists; split; eauto.
          rewrite <- cat1s in *.
          eapply ct_subtyping_trans; eauto.
          apply ct_subtyping_prefix => /=; first by apply ct_subtyping_refl.
          by resolve_subtyping.
        }
      }
Qed.

Lemma check_subtyping: forall C es ct1 ct1' ct2,
    check C es (Some ct1) = Some ct2 ->
    ct1' <ct: ct1 ->  
    exists ct2', check C es (Some ct1') = Some ct2' /\
            ct2' <ct: ct2.
Proof.
  move => C es; move : C.
  induction es using last_ind; move => C ct1 ct1' ct2 Hcheck Hsub.
  - injection Hcheck as <- => /=; subst.
    by exists ct1'.
  - rewrite -cats1 check_rcons in Hcheck.
    rewrite -cats1 check_rcons.
    destruct (check C es (Some ct1)) as [cts |] eqn:Hcheck' => //; last by rewrite check_single_None in Hcheck.
    eapply IHes in Hcheck' as [ts2' [Hcheck' Hsub']]; eauto.
    rewrite Hcheck'.
    by eapply check_single_subtyping; eauto.
Qed.

Lemma type_update_preserve_top: forall cts1 cons prod cts2 unr,
    type_update <<cts1, true>> cons prod = Some <<cts2, unr>> ->
    unr = true.
Proof.
  intros.
  unfold type_update, produce in *; simplify_tc_goal.
  by apply consume_preserve_unr in Hoption.
Qed.
  
Lemma check_single_preserve_top: forall C e cts1 cts2 unr,
    check_single C (Some <<cts1, true>>) e = Some <<cts2, unr>> ->
    unr = true.
Proof.
  move => C e; move :C.
  induction e; move => C cts1 cts2 unr Hcheck; simplify_tc_goal; (try destruct i); (try destruct f0); (try destruct f); simplify_tc_goal; (try by apply type_update_preserve_top in Hcheck); (try by unfold type_update_top in Hcheck; simplify_tc_goal).
  - unfold type_update_ref_is_null in Hcheck; simpl in *.
    by destruct cts1 => //; simplify_tc_goal.
  - unfold type_update_drop in Hcheck; simpl in *.
    by destruct cts1 => //; simplify_tc_goal.
  - unfold type_update_select in Hcheck; simpl in *.
    destruct o => //; simplify_tc_goal.
    + do 2 (try destruct l => //).
      by apply type_update_preserve_top in Hcheck.
    + do 3 (try destruct cts1 => //); simplify_tc_goal; by apply type_update_preserve_top in Hcheck.
Qed.

Lemma check_preserve_top: forall C es cts1 cts2 unr,
    check C es (Some <<cts1, true>>) = Some <<cts2, unr>> ->
    unr = true.
Proof.
  move => C es; move : C.
  induction es => //=; move => C cts1 cts2 unr Hcheck; first by inversion Hcheck.
  destruct (check_single C _ a) eqn: Hcheck'; last by rewrite check_None in Hcheck.
  destruct c as [? [|]]; first by apply IHes in Hcheck.
  by apply check_single_preserve_top in Hcheck'.
Qed.
  
(* Needs to perform induction from head instead of tail, as the first conversion to a
   top stack needs special proofs *)
Lemma check_extend: forall C cts es ts ts2,
  check C es (Some <<ts, false>>) = Some <<cts, false>> ->
  check C es (Some <<ts ++ ts2, false>>) = Some <<cts ++ ts2, false>>.
Proof.
  move => C ct es.
  move: ct.
  induction es as [| e es'] => //=; move => cts ts ts2 Hcheck.
  - by injection Hcheck as <-.
  - destruct (check_single C (Some <<ts, false>>) e) as [[c_ts [|]] | ] eqn:Hcheck'; last by rewrite check_None in Hcheck.
    + by apply check_preserve_top in Hcheck.
    + apply check_single_extend with (ts2 := ts2) in Hcheck'.
      rewrite Hcheck'.
      by eapply IHes' in Hcheck; eauto.
Qed.

(* Once the result becomes a top stack, the original stack type doesn't really matter. *)
Lemma check_extend_top: forall C cts es ts ts2,
  check C es (Some <<ts, false>>) = Some <<cts, true>> ->
  check C es (Some <<ts ++ ts2, false>>) = Some <<cts, true>>.
Proof.
  move => C ct es.
  move: ct.
  induction es as [| e es'] => //=; move => cts ts ts2 Hcheck.
  destruct (check_single C (Some <<ts, false>>) e) as [[c_ts [|]] | ] eqn:Hcheck'; last by rewrite check_None in Hcheck.
  - apply check_single_extend_top with (ts2 := ts2) in Hcheck'.
    by rewrite Hcheck'.
  - apply check_single_extend with (ts2 := ts2) in Hcheck'.
    rewrite Hcheck'.
    by eapply IHes' in Hcheck; eauto.
Qed.

Lemma value_type_select_refl: forall t,
    is_numeric_type t ->
    value_type_select t t = Some t.
Proof.
  unfold value_type_select.
  move => t -> => /=.
  destruct t => /=; try by rewrite eq_refl.
  reflexivity.
Qed.
  
Ltac invert_update_agree :=
  repeat match goal with
    | H: type_update _ [::] _ = Some _ |- _ =>
         let Hagree := fresh "Hagree" in
         apply type_update_Some_impl in H as [Hagree ->]
    | H: type_update _ [::?t1] _ = Some _ |- _ =>
         let Hagree := fresh "Hagree" in
         apply type_update_Some_impl in H as [Hagree ->]
    | H: type_update _ [::?t1; ?t2] _ = Some _ |- _ =>
         let Hagree := fresh "Hagree" in
         apply type_update_Some_impl in H as [Hagree ->]
    | H: type_update _ [::?t1; ?t2; ?t3] _ = Some _ |- _ =>
         let Hagree := fresh "Hagree" in
         apply type_update_Some_impl in H as [Hagree ->]
    | H: is_true (c_types_agree << _ :: _, _ >> _) |- _ =>
        let t := fresh "t" in
        let ts := fresh "ts" in
        let Hsub := fresh "Hsub" in
        let Hagree := fresh "Hagree" in
        apply c_types_agree_cons_split in H as [t [ts [-> [Hsub Hagree]]]]
    | H: is_true (c_types_agree << _ ++ _, _ >> _) |- _ =>
        let tx := fresh "tx" in
        let ty := fresh "ty" in
        let Hsub := fresh "Hsub" in
        let Hagree := fresh "Hagree" in
        apply c_types_agree_cat_split in H as [tx [ty [-> [Hsub Hagree]]]]
    end.

Lemma resolve_type_update_agree_aux1: forall cts t1 ts,
  c_types_agree << take 1 (CT_type cts), CT_unr cts >> [::t1] ->
  c_types_agree << drop 1 (CT_type cts), CT_unr cts >> ts ->
  c_types_agree cts ([::t1] ++ ts).
Proof.
  move => cts t1 ts Hagree1 Hagree2.
  destruct cts as [[ | t cts] unr] => //.
  apply c_types_agree_size_sub in Hagree1; last by rewrite size_takel => /=.
  simplify_tc_goal.
  by apply c_types_agree_cons.
Qed.

Lemma resolve_type_update_agree_aux2: forall cts t1 t2 ts,
  c_types_agree << take 2 (CT_type cts), CT_unr cts >> [::t1; t2] ->
  c_types_agree << drop 2 (CT_type cts), CT_unr cts >> ts ->
  c_types_agree cts ([::t1; t2] ++ ts).
Proof.
  move => cts t1 t2 ts Hagree1 Hagree2.
  destruct cts as [[ | t cts] unr] => //.
  destruct cts as [ | t' cts] => //.
  apply c_types_agree_size_sub in Hagree1; last by rewrite size_takel => /=.
  simplify_tc_goal.
  by repeat (apply c_types_agree_cons; split => //).
Qed.

Lemma resolve_type_update_agree_aux3: forall cts t1 t2 t3 ts,
  c_types_agree << take 3 (CT_type cts), CT_unr cts >> [::t1; t2; t3] ->
  c_types_agree << drop 3 (CT_type cts), CT_unr cts >> ts ->
  c_types_agree cts ([::t1; t2; t3] ++ ts).
Proof.
  move => cts t1 t2 t3 ts Hagree1 Hagree2.
  destruct cts as [[ | t cts] unr] => //.
  destruct cts as [ | t' cts] => //.
  destruct cts as [ | t'' cts] => //.
  apply c_types_agree_size_sub in Hagree1; last by rewrite size_takel => /=.
  simplify_tc_goal.
  by repeat (apply c_types_agree_cons; split => //).
Qed.

Ltac resolve_check_agree :=
  match goal with
  | H: is_true (c_types_agree << CT_type ?cts, CT_unr ?cts >> ?ts) |-
      exists tx, is_true (c_types_agree ?cts tx) /\ _ =>
      exists ts; split; first done
  | H1: is_true (c_types_agree << take 1 (CT_type ?cts), CT_unr ?cts >> [::?t1]),
    H2: is_true (c_types_agree << drop 1 (CT_type ?cts), CT_unr ?cts >> ?ts) |-
      exists tx, is_true (c_types_agree ?cts tx) /\ _ =>
      exists ([::t1] ++ ts); split; first by apply resolve_type_update_agree_aux1
  | H1: is_true (c_types_agree << take 2 (CT_type ?cts), CT_unr ?cts >> [::?t1; ?t2]),
    H2: is_true (c_types_agree << drop 2 (CT_type ?cts), CT_unr ?cts >> ?ts) |-
      exists tx, is_true (c_types_agree ?cts tx) /\ _ =>
      exists ([::t1; t2] ++ ts); split; first by apply resolve_type_update_agree_aux2
  | H1: is_true (c_types_agree << take 3 (CT_type ?cts), CT_unr ?cts >> [::?t1; ?t2; ?t3]),
    H2: is_true (c_types_agree << drop 3 (CT_type ?cts), CT_unr ?cts >> ?ts) |-
      exists tx, is_true (c_types_agree ?cts tx) /\ _ =>
      exists ([::t1; t2; t3] ++ ts); split; first by apply resolve_type_update_agree_aux3
  end.

Ltac resolve_tc_be_typing :=
  (try rewrite rev_cat); (try apply bet_weakening); (try apply bet_weakening_empty_1); try by (econstructor; eauto; resolve_subtyping); ((try unfold rev => /=); eapply bet_subtyping; first (by econstructor; eauto; resolve_subtyping); by resolve_subtyping).

Lemma type_update_ref_is_null_bet: forall C cts cts' tm,
  type_update_ref_is_null cts = Some cts' ->
  c_types_agree cts' tm ->
  exists tn, c_types_agree cts tn /\ be_typing C [::BI_ref_is_null] (Tf (rev tn) (rev tm)).
Proof.
  move => C cts cts' tm Hupdate Hct.
  unfold type_update_ref_is_null in Hupdate.
  destruct cts as [[ | t ts] unr]; simplify_tc_goal.
  - apply c_types_agree_cons_split in Hct as [t' [ts' [-> [Hsub Hagree]]]].
    exists ([::T_bot] ++ ts'); split => //.
    rewrite rev_cons -cats1 rev_cat rev_cons -cats1.
    apply bet_weakening => /=.
    eapply bet_subtyping; first by apply bet_ref_is_null with (t := T_funcref).
    resolve_subtyping.
    apply instr_subtyping_weaken1 with (tx1 := [::T_bot]); by resolve_subtyping.
  - apply c_types_agree_cons_split in Hct as [t' [ts' [-> [Hsub Hagree]]]].
    exists ([::t] ++ ts'); split => //.
    { by simpl; apply c_types_agree_cons; split; resolve_subtyping. }
    rewrite rev_cons -cats1 rev_cat rev_cons -cats1.
    apply bet_weakening => /=.
    destruct t => //.
    + eapply bet_subtyping; first by apply bet_ref_is_null with (t := r).
      by resolve_subtyping.
    + eapply bet_subtyping; first by apply bet_ref_is_null with (t := T_funcref).
      resolve_subtyping.
      apply instr_subtyping_weaken1 with (tx1 := [::T_bot]); by resolve_subtyping.
Qed.
      
Lemma type_update_drop_bet: forall C cts cts' tm,
  type_update_drop cts = Some cts' ->
  c_types_agree cts' tm ->
  exists tn, c_types_agree cts tn /\ be_typing C [::BI_drop] (Tf (rev tn) (rev tm)).
Proof.
  move => C cts cts' tm Hupdate Hct.
  unfold type_update_drop in Hupdate.
  destruct cts as [[ | t ts] unr]; simplify_tc_goal.
  - exists ([::T_bot] ++ tm); split => //.
    rewrite rev_cat rev_cons -cats1.
    apply bet_weakening_empty_2 => /=.
    by apply bet_drop.
  - exists ([::t] ++ tm); split => //.
    { by simpl; apply c_types_agree_cons; split; resolve_subtyping. }
    rewrite rev_cat rev_cons -cats1.
    apply bet_weakening_empty_2 => /=.
    by apply bet_drop.
Qed.

Lemma type_update_select_bet: forall C cts cts' tm ots,
  type_update_select cts ots = Some cts' ->
  c_types_agree cts' tm ->
  exists tn, c_types_agree cts tn /\ be_typing C [::BI_select ots] (Tf (rev tn) (rev tm)).
Proof.
  move => C cts cts' tm ots Hupdate Hct.
  unfold type_update_select in Hupdate.
  destruct ots as [ts |].
  - do 3 (try destruct ts => //).
    invert_update_agree; simplify_tc_goal.
    resolve_check_agree.
    rewrite rev_cat.
    apply bet_weakening; unfold rev => /=.
    eapply bet_subtyping; first by apply bet_select_Some.
    by resolve_subtyping.
  - destruct cts as [ts unr]; simplify_tc_goal.
    destruct ts as [ | t1 ts]; simplify_tc_goal; invert_update_agree; simplify_tc_goal.
    { exists ([::T_num T_i32; T_bot; T_bot] ++ ty); split => //.
      rewrite rev_cat.
      apply bet_weakening.
      unfold rev => /=.
      apply bet_subtyping with (t1s := [::T_bot; T_bot; T_num T_i32]) (t2s := [::T_bot]); first by apply bet_select_None.
      by resolve_subtyping.
    }
    destruct ts as [ | t2 ts]; simplify_tc_goal; invert_update_agree; simplify_tc_goal.
    { exists ([::T_num T_i32; T_bot; T_bot] ++ ty); split => //.
      rewrite rev_cat.
      apply bet_weakening.
      unfold rev => /=.
      apply bet_subtyping with (t1s := [::T_bot; T_bot; T_num T_i32]) (t2s := [::T_bot]); first by apply bet_select_None.
      by resolve_subtyping.
    }
    destruct ts as [ | t3 ts]; simplify_tc_goal; invert_update_agree; simplify_tc_goal.
    { exists ([::T_num T_i32; t2; T_bot] ++ ty); split => //.
      { by unfold c_types_agree in *; destruct unr; simplify_tc_goal. }
      repeat rewrite rev_cat.
      unfold rev => /=.
      apply bet_weakening.
      apply bet_subtyping with (t1s := [::t2; t2; T_num T_i32]) (t2s := [::t2]); first by apply bet_select_None.
      resolve_subtyping.
      apply instr_subtyping_weaken1 with (tx1 := [::T_bot; t2; T_num T_i32]); first by resolve_subtyping.
      simpl; resolve_subtyping; by destruct t2.
    }
    {
      exists ([::T_num T_i32; t2; t3] ++ ty); split => //.
      { by unfold c_types_agree in *; destruct unr; simplify_tc_goal. }
      rewrite rev_cat.
      apply bet_weakening.
      unfold rev => /=.
      assert (t1 <t: T_num T_i32) as Hsub.
      { by unfold c_types_agree in * => /=; destruct unr; simplify_tc_goal. }
      clear Hagree Hagree0.
      unfold value_type_select in Hoption; simplify_tc_goal; move/eqP in Hif; try move/eqP in Hif0; try move/eqP in Hif1; subst.
      { apply bet_subtyping with (t1s := [:: v; v; T_num T_i32]) (t2s := [::v]); first by apply bet_select_None => //.
        resolve_subtyping.
        apply instr_subtyping_weaken1 with (tx1 := [::v; T_bot; T_num T_i32]); resolve_subtyping => /=.
        by resolve_subtyping; destruct v.
      }
      { apply bet_subtyping with (t1s := [:: v; v; T_num T_i32]) (t2s := [::v]); first by apply bet_select_None => //.
        resolve_subtyping.
        apply instr_subtyping_weaken1 with (tx1 := [::T_bot; v; T_num T_i32]); resolve_subtyping => /=.
        by resolve_subtyping; destruct v.
      }
      { apply bet_subtyping with (t1s := [:: t3; t3; T_num T_i32]) (t2s := [::t3]); first by apply bet_select_None => //.
        by resolve_subtyping.
      }
    }
Qed.

Lemma instr_subtyping_rev_spec: forall ts1 ts2 ts3 ts4,
  (exists ts ts' ts1_sub ts2_sub,
     ts3 = ts1_sub ++ ts /\
     ts4 = ts2_sub ++ ts' /\
     ts <ts: ts' /\
     ts1_sub <ts: ts1 /\
     ts2 <ts: ts2_sub) ->
  (Tf (rev ts1) (rev ts2) <ti: Tf (rev ts3) (rev ts4)).
Proof.
  move => ts1 ts2 ts3 ts4 [ts [ts' [ts1_sub [ts2_sub [-> [-> [Hsub1 [Hsub2 Hsub3]]]]]]]].
  apply values_subtyping_rev in Hsub1, Hsub2, Hsub3.
  repeat rewrite rev_cat.
  by exists (rev ts), (rev ts'), (rev ts1_sub), (rev ts2_sub).
Qed.

Lemma c_types_agree_take_drop: forall cts unr ts1 ts2,
    c_types_agree <<take (size ts1) cts, unr>> ts1 ->
    c_types_agree <<drop (size ts1) cts, unr>> ts2 ->
    c_types_agree <<cts, unr>> (take (size cts) ts1 ++ ts2).
Proof.
  move => cts unr ts1 ts2 Hagree1 Hagree2.
  rewrite <-(cat_take_drop (size ts1) cts) at 1.
  eapply c_types_agree_take_cat in Hagree2; try by apply Hagree1.
  by rewrite size_take_min minnC take_min take_size in Hagree2.
Qed.
  
Opaque instr_subtyping.

Lemma type_update_agree_subtyping: forall cts ts_cons ts_prod cts' tx,
  type_update cts ts_cons ts_prod = Some cts' ->
  c_types_agree cts' tx ->
  exists tn, c_types_agree cts tn /\ (Tf (rev ts_cons) (rev ts_prod) <ti: Tf (rev tn) (rev tx)).
Proof.
  move => [ts unr] ts_cons ts_prod cts' tx Hupdate Hagree.
  unfold type_update, produce in *; simplify_tc_goal.
  apply consume_Some_impl in Hoption as [Hagree' ->]; simpl in *.
  apply c_types_agree_cat_split in Hagree as [ts1 [ts2 [-> [Hsub Hagree]]]].
  destruct (size ts <= size ts_cons) eqn:Hoversize.
  { rewrite take_oversize in Hagree' => //.
    rewrite drop_oversize in Hagree => //.
    exists (ts_cons ++ ts2); split.
    { unfold c_types_agree in *; destruct unr; simplify_tc_goal.
      by rewrite takel_cat.
    }
    apply instr_subtyping_rev_spec.
    exists ts2, ts2, ts_cons, ts1; repeat split => //; by resolve_subtyping.
  }
  { specialize (c_types_agree_take_drop Hagree' Hagree) as Hagree0.
    exists (take (size ts) ts_cons ++ ts2); split => //.
    apply instr_subtyping_rev_spec.
    exists ts2, ts2, (take (size ts) ts_cons), ts1; repeat split; resolve_subtyping.
    rewrite take_oversize; last by lias.
    by resolve_subtyping.
  }
Qed.
  
Lemma type_update_top_agree_subtyping: forall cts ts_cons cts' tx,
  type_update_top cts ts_cons nil = Some cts' ->
  c_types_agree cts' tx ->
  exists tn ts1 ts2, c_types_agree cts tn /\ (Tf (ts1 ++ rev ts_cons) ts2 <ti: Tf (rev tn) (rev tx)).
Proof.
  move => [ts unr] ts_cons cts' tx Hupdate Hagree.
  unfold type_update_top in *; simplify_tc_goal.
  apply consume_Some_impl in Hoption as [Hagree' ->]; simpl in *.
  destruct (size ts <= size ts_cons) eqn:Hoversize.
  { rewrite take_oversize in Hagree' => //.
    destruct unr.
    { exists (ts_cons ++ tx), (rev tx), (rev tx); split.
      { by eapply c_types_agree_extend_top; eauto. }
      by rewrite rev_cat; reflexivity.
    }
    unfold c_types_agree in Hagree'; simplify_tc_goal.
    exists ts_cons, nil, (rev tx) => /=; split => //.
    reflexivity.
  }
  {
    destruct unr.
    { unfold c_types_agree in *; simplify_tc_goal.
      rewrite size_take_min minnC take_min take_size in Hagree'.
      rewrite (@take_oversize _ (size ts) ts_cons) in Hagree'; last by lias.
      exists (ts_cons ++ drop (size ts_cons) ts), (rev (drop (size ts_cons) ts)), (rev tx) => /=; split; last by rewrite rev_cat; reflexivity.
      replace (size ts) with (size (ts_cons ++ drop (size ts_cons) ts)).
      { rewrite take_size.
        rewrite <- (cat_take_drop (size ts_cons) ts) at 1.
        by resolve_subtyping.
      }
      { rewrite size_cat size_drop.
        by lias.
      }
    }
    { unfold c_types_agree in *; simplify_tc_goal.
      exists (ts_cons ++ drop (size ts_cons) ts), (rev (drop (size ts_cons) ts)), (rev tx); split => /=.
      - by rewrite <- (cat_take_drop (size ts_cons) ts) at 1; resolve_subtyping.
      - rewrite rev_cat; reflexivity.
    }
  }
Qed.

Transparent instr_subtyping.
  
Lemma c_types_agree_impl_subtyping: forall cts unr ts,
    c_types_agree <<cts, unr>> ts ->
    cts <ts: take (size cts) ts.
Proof.
  move => cts unr ts Hagree; unfold c_types_agree in Hagree; destruct unr; simplify_tc_goal.
  replace (size cts) with (size ts); last by apply values_subtyping_size in Hagree.
  by rewrite take_size.
Qed.
  
(*
  The first part of the conjunction is what is required, but we need to prove it by simultaneous
  induction on the following two lemmas.
  Coq is reluctant to accept that the mutual recursive proof actually terminates, so we use the
  meausre we defined above for that purpose.
*)
Lemma tc_to_bet_conj d:
  ( forall C cts bes tm cts',
  be_size_list bes <= d ->
  check (context_reverse C) bes (Some cts) = Some cts' ->
  c_types_agree cts' tm ->
  exists tn, c_types_agree cts tn /\ be_typing C bes (Tf (rev tn) (rev tm))) /\
  ( forall C cts tm e cts',
  be_size_single e <= d ->
  check_single (context_reverse C) (Some cts) e = (Some cts') ->
  c_types_agree cts' tm ->
  exists tn, c_types_agree cts tn /\ be_typing C ([:: e]) (Tf (rev tn) (rev tm))).
Proof.
  induction (lt_wf d) as [d _ H] => //=.
  split.
  (* List *) 
  - move => c cts bes.
    move: c cts.
    induction bes as [| bes e] using last_ind => //=; move => C cts tm cts' Hs Hct1 Hbetc.
    + exists tm.
      split => //; first by injection Hct1 as ->.
      by apply bet_weakening_empty_both, bet_empty.
    + rewrite be_size_list_rcons in Hs.
      rewrite -cats1 in Hct1.
      rewrite check_rcons in Hct1.
      remember (check (context_reverse C) bes (Some cts)) as obesct.
      destruct obesct as [besct | ]; last by destruct e.
      symmetry in Heqobesct.
      assert (be_size_single e < d)%coq_nat as Hmeasure; first by lias.
      assert (be_size_list bes < d)%coq_nat as Hmeasure2; first by lias.
      apply H in Hmeasure as [_ Hmeasure].
      eapply Hmeasure in Hbetc as [ts1 [Hagree1 Hbet1]]; eauto.
      eapply IHbes in Heqobesct as [ts2 [Hagree2 Hbet2]]; eauto; last by lias.
      apply H in Hmeasure2 as [_ Hmeasure2].
      exists ts2.
      rewrite -cats1.
      split => //.
      by eapply bet_composition; eauto.
  (* Single *)
  - destruct e => //=; (try destruct i as [tn' tm']); simplify_tc_goal;
                 move => cts' Hs Hupdate Hagree => //; simplify_tc_goal;
                 invert_update_agree; simplify_tc_goal;
                 try resolve_check_agree; try rewrite rev_cat.
    (* It is true that many cases can be automatically resolved. However,
       we avoid doing so -- so that this proof is easier to be fixed when
       there's a major update in the future. *)
    (* Const_num *)
    + by resolve_tc_be_typing.
    (* Unop *)
    + apply bet_weakening, bet_unop.
      destruct n, u => //; by constructor.
    (* Binop *)
    + apply bet_weakening, bet_binop.
      destruct n, b => //; by constructor.
    (* Testop *)
    + by resolve_tc_be_typing.
    (* Relop *)
    + apply bet_weakening, bet_relop.
      destruct n, r => //; by constructor.
    (* Cvtop *)
    + apply bet_weakening, bet_cvtop.
      destruct n, n0 => //; by constructor.
    (* Const_vec *)
    + by resolve_tc_be_typing.
    (* Unop_vec *)
    + by resolve_tc_be_typing.
    (* Binop_vec *)
    + by resolve_tc_be_typing.
    (* Ternop_vec *)
    + by resolve_tc_be_typing.
    (* Test_vec *)
    + by resolve_tc_be_typing.
    (* Shift_vec *)
    + by resolve_tc_be_typing.
    (* Splat_vec *)
    + by resolve_tc_be_typing.
    (* Extract_vec *)
    + by resolve_tc_be_typing.
    (* Replace_vec *)
    + by resolve_tc_be_typing.
    (* Ref_null *)
    + by resolve_tc_be_typing.
    (* Ref_is_null *)
    + by apply type_update_ref_is_null_bet with (cts' := cts').
    (* Ref_func *)
    + move/inP in Hif.
      apply bet_weakening_empty_1, bet_ref_func with (t := (rev_tf f0)) => //.
      apply nth_error_map in Hoption as [ft [? <-]].
      by destruct ft; unfold rev_tf; repeat rewrite revK.
    (* Drop *)
    + by apply type_update_drop_bet with (cts' := cts').
    (* Select *)
    + by apply type_update_select_bet with (cts' := cts').
    (* Local_get *)
    + apply bet_weakening_empty_1.
      eapply bet_subtyping; first (by econstructor; eauto; resolve_subtyping);
      by resolve_subtyping.
    (* Local_set *)
    + by resolve_tc_be_typing.
    (* Local_tee *)
    + apply bet_weakening.
      unfold rev => /=.
      eapply bet_subtyping; first (by econstructor; eauto; resolve_subtyping).
      by resolve_subtyping.
    (* Global_set *)
    + apply bet_weakening_empty_1.
      eapply bet_subtyping; first by econstructor; eauto.
      by resolve_subtyping.
    (* Global_get *)
    + by resolve_tc_be_typing.
    (* Table_get *)
    + by resolve_tc_be_typing.
    (* Table_set *)
    + by resolve_tc_be_typing.
    (* Table_size *)
    + by resolve_tc_be_typing.
    (* Table_grow *)
    + by resolve_tc_be_typing.
    (* Table_fill *)
    + by resolve_tc_be_typing.
    (* Table_copy *)
    + move/eqP in Hif.
      by resolve_tc_be_typing.
    (* Table_init *)
    + move/eqP in Hif.
      by resolve_tc_be_typing.
    (* Elem_drop *)
    + exists tm; split => //.
      by apply bet_weakening_empty_both; econstructor; eauto.
    (* Load *)
    + by resolve_tc_be_typing.
    (* Load_vec *)
    + by resolve_tc_be_typing.
    (* Load_vec_lane *)
    + by resolve_tc_be_typing.
    (* Store *)
    + by resolve_tc_be_typing.
    (* Store_vec_lane *)
    + by resolve_tc_be_typing.
    (* Memory_size *)
    + by resolve_tc_be_typing.
    (* Memory_grow *)
    + by resolve_tc_be_typing.
    (* Memory_fill *)
    + by resolve_tc_be_typing.
    (* Memory_copy *)
    + by resolve_tc_be_typing.
    (* Memory_init *)
    + by resolve_tc_be_typing.
    (* Data_drop *)
    + exists tm; split => //.
      by apply bet_weakening_empty_both; econstructor; eauto.
    (* Nop *)
    + exists tm; split => //.
      by apply bet_weakening_empty_both; econstructor; eauto.
    (* Unreachable *)
    + exists (CT_type cts); split => //; first by apply c_types_agree_refl.
      by apply bet_unreachable.
    (* Block *)
    + destruct i.
      rewrite upd_label_context_reverse in Hupdate.
      simpl in Hupdate.
      rewrite mapK in Hupdate; last by apply revK.
      apply expand_t_context_reverse in Hoption; simpl in Hoption.
      rewrite context_reverseK in Hoption.
      fold_remember_check.
      assert (be_size_list l < d)%coq_nat as Hmeasure; first by unfold be_size_list; lias.
      apply H in Hmeasure; destruct Hmeasure as [IH _]; clear H.
      simplify_tc_goal.
      eapply IH in Hoption0 => //; last (by erewrite Hif); clear IH Hs.
      destruct Hoption0 as [tn [Hct Hbet]].
      unfold c_types_agree in Hct; simplify_tc_goal.
      (* It is really difficult to work out what the consumed type should be, so it is slightly easier to construct towards the target typing judgement from the premises instead of inverting backwards. *)
      apply values_subtyping_rev in Hct.
      eapply bet_subtyping with (t1s' := rev r) (t2s' := rev r0) in Hbet; last by resolve_subtyping.
      eapply bet_block in Hbet; last by eauto.
      specialize (type_update_agree_subtyping Hupdate Hagree) as [tx [Hagree0 Hsub]].
      eapply bet_subtyping in Hbet; last by apply Hsub.
      by exists tx.
    (* Loop *)
    + destruct i.
      rewrite upd_label_context_reverse in Hupdate.
      simpl in Hupdate.
      rewrite mapK in Hupdate; last by apply revK.
      apply expand_t_context_reverse in Hoption; simpl in Hoption.
      rewrite context_reverseK in Hoption.
      fold_remember_check.
      assert (be_size_list l < d)%coq_nat as Hmeasure; first by unfold be_size_list; lias.
      apply H in Hmeasure; destruct Hmeasure as [IH _]; clear H.
      simplify_tc_goal.
      eapply IH in Hoption0 => //; last (by erewrite Hif); clear IH Hs.
      destruct Hoption0 as [tn [Hct Hbet]].
      unfold c_types_agree in Hct; simplify_tc_goal.
      apply values_subtyping_rev in Hct.
      eapply bet_subtyping with (t1s' := rev r) (t2s' := rev r0) in Hbet; last by resolve_subtyping.
      eapply bet_loop in Hbet; last by eauto.
      specialize (type_update_agree_subtyping Hupdate Hagree) as [tx [Hagree0 Hsub]].
      eapply bet_subtyping in Hbet; last by apply Hsub.
      by exists tx.
    (* If *)
    + destruct i.
      rewrite upd_label_context_reverse in Hupdate.
      simpl in Hupdate.
      rewrite mapK in Hupdate; last by apply revK.
      apply expand_t_context_reverse in Hoption; simpl in Hoption.
      rewrite context_reverseK in Hoption.
      fold_remember_check.
      fold (be_size_list l) in Hs.
      fold (be_size_list l0) in Hs.
      assert (be_size_list l < d)%coq_nat as Hmeasure1; first by lias.
      assert (be_size_list l0 < d)%coq_nat as Hmeasure2; first by lias.
      apply H in Hmeasure1; destruct Hmeasure1 as [IH1 _].
      apply H in Hmeasure2; destruct Hmeasure2 as [IH2 _].
      clear H; simplify_tc_goal.
      eapply IH1 in Hoption1 => //; last by apply H; clear IH1.
      eapply IH2 in Hoption0 => //; last by apply H0; clear IH2.
      destruct Hoption0 as [tn1 [Hct1 Hbet1]].
      destruct Hoption1 as [tn2 [Hct2 Hbet2]].
      unfold c_types_agree in Hct1; unfold c_types_agree in Hct2; simplify_tc_goal.
      apply values_subtyping_rev in Hct1.
      apply values_subtyping_rev in Hct2.
      eapply bet_subtyping with (t1s' := rev r) (t2s' := rev r0) in Hbet1; last by resolve_subtyping.
      eapply bet_subtyping with (t1s' := rev r) (t2s' := rev r0) in Hbet2; last by resolve_subtyping.
      eapply bet_if_wasm in Hbet1; (try by apply Hbet2); try by eauto.
      specialize (type_update_agree_subtyping Hupdate Hagree) as [tx [Hagree0 Hsub]].
      rewrite rev_cons -cats1 in Hsub.
      eapply bet_subtyping in Hbet1; last by apply Hsub.
      by exists tx.
    (* Br *)
    + apply nth_error_map in Hoption as [ts [Hnth <-]].
      eapply type_update_top_agree_subtyping in Hupdate; eauto.
      destruct Hupdate as [tn [ts1 [ts2 [Hagree' Hsub]]]].
      rewrite revK in Hsub.
      exists tn; split => //.
      eapply bet_subtyping; first by apply bet_br with (ts := ts) => //.
      by apply Hsub.
    (* Br_if *)
    + apply nth_error_map in Hoption as [ts [Hnth <-]].
      eapply type_update_agree_subtyping in Hupdate; eauto.
      destruct Hupdate as [tn [Hagree' Hsub]].
      rewrite rev_cons -cats1 revK in Hsub.
      exists tn; split => //.
      eapply bet_subtyping; first by apply bet_br_if with (ts := ts) => //.
      by apply Hsub.
    (* Br_table *)
    + apply common_lab_rev in Hoption.
      rewrite mapK in Hoption; last by apply revK.
      eapply type_update_top_agree_subtyping in Hupdate; eauto.
      destruct Hupdate as [tn [ts1 [ts2 [Hagree' Hsub]]]].
      rewrite rev_cons -cats1 in Hsub.
      exists tn; split => //.
      eapply bet_subtyping.
      { eapply bet_br_table with (ts := rev l1).
        apply Forall_spec.
        move => n x Hnth.
        by eapply common_lab_spec; eauto.
      }
      by apply Hsub.
    (* Return *)
      eapply type_update_top_agree_subtyping in Hupdate; eauto.
      destruct Hupdate as [tn [ts1 [ts2 [Hagree' Hsub]]]].
      rewrite revK in Hsub.
      exists tn; split => //.
      eapply bet_subtyping; first by apply bet_return with (ts := r) => //.
      by apply Hsub.
    (* Call *)
    + apply nth_error_map in Hoption as [ts [Hnth <-]].
      destruct ts; simpl in Hupdate.
      eapply type_update_agree_subtyping in Hupdate; eauto.
      destruct Hupdate as [tn [Hagree' Hsub]].
      do 2 rewrite revK in Hsub.
      exists tn; split => //.
      by resolve_tc_be_typing.
    (* Call_indirect *)
    + destruct f.
      move/eqP in Hif.
      apply nth_error_map in Hoption0 as [ts [Hnth Hmap]].
      destruct ts; simpl in Hmap; inversion Hmap; subst; clear Hmap.
      eapply type_update_agree_subtyping in Hupdate; eauto.
      destruct Hupdate as [tn [Hagree' Hsub]].
      rewrite rev_cons revK -cats1 revK in Hsub.
      exists tn; split => //.
      by resolve_tc_be_typing.
    (* Return_call *)
    + destruct f0 as [tn0 tm0].
      remove_bools_options.
      move/eqP in Hif; subst.
      eapply type_update_top_agree_subtyping in Hupdate; eauto.
      destruct Hupdate as [tn [ts1 [ts2 [Hagree' Hsub]]]].
      apply nth_error_map in Hoption0 as [ts [Hnth Heq]].
      destruct ts; simpl in Heq.
      injection Heq as <- Hrevr.
      apply (f_equal rev) in Hrevr; repeat rewrite revK in Hrevr; subst.
      rewrite revK in Hsub.
      exists tn; split => //.
      eapply bet_subtyping; first by apply bet_return_call with (t1s := r0) (t2s := r).
      by eauto.
    (* Return_call_indirect *)      
    + destruct f as [tn0 tm0].
      move/eqP in Hif.
      remove_bools_options.
      move/eqP in Hif0; subst.
      eapply type_update_top_agree_subtyping in Hupdate; eauto.
      destruct Hupdate as [tn [ts1 [ts2 [Hagree' Hsub]]]].
      apply nth_error_map in Hoption as [ts [Hnth Heq]].
      destruct ts; simpl in Heq.
      injection Heq as <- Hrevr.
      apply (f_equal rev) in Hrevr; repeat rewrite revK in Hrevr; subst.
      rewrite rev_cons revK -cats1 in Hsub.
      exists tn; split => //.
      eapply bet_subtyping; first by eapply bet_return_call_indirect with (t1s := r0) (t2s := r); eauto.
      by eauto.
Qed.
      
Lemma tc_to_bet_list: forall C cts bes tm cts',
  check (context_reverse C) bes (Some cts) = Some cts' ->
  c_types_agree cts' tm ->
  exists tn, c_types_agree cts tn /\ be_typing C bes (Tf (rev tn) (rev tm)).
Proof.
  intros.
  specialize tc_to_bet_conj with (be_size_list bes).
  move => [H1 _].
  by eapply H1; eauto.
Qed.

Lemma b_e_type_checker_reflects_typing:
  forall C bes tf,
    reflect (be_typing C bes tf) (b_e_type_checker C bes tf).
Proof.
  move => C bes tf.
  destruct tf as [tn tm].
  destruct (b_e_type_checker C bes (Tf tn tm)) eqn: Htc_bool.
  - apply ReflectT.
    unfold b_e_type_checker, b_e_type_checker_aux in Htc_bool.
    fold (check (context_reverse C) bes (Some <<(rev tn), false>>)) in Htc_bool.
    remove_bools_options.
    eapply tc_to_bet_list in Htc_bool; eauto.
    destruct Htc_bool as [ts [Hagree Hbet]].
    unfold c_types_agree in Hagree; simpl in *.
    apply values_subtyping_rev in Hagree.
    rewrite -> revK in *.
    eapply bet_subtyping; eauto.
    eapply instr_subtyping_weaken1; first reflexivity; by resolve_subtyping.
  - apply ReflectF.
    move => Hbet.
    assert (b_e_type_checker C bes (Tf tn tm)) as H; (try by rewrite H in Htc_bool); clear Htc_bool.
    induction Hbet; subst => //=; (try rewrite H); unfold type_update, type_update_top, produce; simplify_tc_goal; (try by unfold c_types_agree in *; simplify_tc_goal).
    (* Ref_func *)
    + move/inP in H0.
      by rewrite H0.
    + rewrite value_type_select_refl => //.
      unfold c_types_agree.
      by simplify_tc_goal.
    (* Br_table *)
    + apply common_lab_cond in H as [ty [Hcommon Hsub]]; last by destruct ins.
      apply common_lab_rev in Hcommon.
      rewrite Hcommon.
      apply values_subtyping_rev in Hsub.
      specialize consume_subtyping with (ct1 := << rev ty ++ rev t1s, false >>) (ct1' := << rev ts ++ rev t1s, false >>) (ct2 := << rev t1s, false >>) (ts := rev ty) as Hconsume.
      destruct Hconsume as [ct2' [Hconsume' Hctsub]].
      { by apply consume_prefix. }
      { apply ct_subtyping_prefix => //.
        by apply ct_subtyping_refl.
      }
      { rewrite Hconsume'.
        by unfold c_types_agree; simplify_tc_goal.
      }
    (* Call *)
    + destruct tf as [t1 t2] => /=.
      by unfold c_types_agree, type_update; simplify_tc_goal.
    (* Composition *)
    + rewrite List.fold_left_app => //=.
      rewrite Hoption0.
      destruct (List.fold_left _ es _) as [ct_res | ] eqn:Htc => //=.
      injection Hoption0 as <-.
      assert (ct_res <ct: (<<rev t2s, false>>)) as Hctsub.
      { unfold ct_subtyping; rewrite IHHbet1 => /=; by rewrite eq_refl; lias. }
      eapply check_single_subtyping in Hoption as [ct2' [Hcheck Hagree]]; eauto.
      rewrite Hcheck.
      by eapply c_types_agree_subtyping; eauto; resolve_subtyping.
    (* Subtyping *)
    + simplify_subtyping.
      apply values_subtyping_rev in Hconjl2.
      apply values_subtyping_rev in Hconjr0.
      apply values_subtyping_rev in Hconjl1.
      simplify_tc_goal.
      destruct c as [cts [|]].
      { eapply check_extend_top with (ts2 := rev extr0) in Hoption; eauto.
        eapply check_subtyping with (ct1' := <<rev extr1 ++ rev extr, false>>) in Hoption as [ct' [Hcheck Hagree]]; eauto; last by unfold ct_subtyping, c_types_agree => /=; resolve_subtyping => //.
        fold (check (context_reverse C) es (Some <<rev extr1 ++ rev extr, false>>)).
        rewrite Hcheck.
        apply c_types_agree_extend_top with (ts := rev extr0) in IHHbet.
        eapply c_types_agree_subtyping; eauto.
        by resolve_subtyping.
      }
      { eapply check_extend with (ts2 := rev extr0) in Hoption; eauto.
        eapply check_subtyping with (ct1' := <<rev extr1 ++ rev extr, false>>) in Hoption as [ct' [Hcheck Hagree]]; eauto; last by unfold ct_subtyping, c_types_agree => /=; resolve_subtyping => //.
        fold (check (context_reverse C) es (Some <<rev extr1 ++ rev extr, false>>)).
        rewrite Hcheck.
        unfold ct_subtyping, c_types_agree in *; destruct ct' as [cts' [|]]; simplify_tc_goal => //.
        - eapply values_subtyping_trans; eauto.
          apply values_subtyping_take.
          rewrite values_subtyping_cat; last by apply values_subtyping_size in IHHbet; apply values_subtyping_size in Hconjr0; lias.
          by resolve_subtyping.
        - eapply values_subtyping_trans; eauto.
          rewrite values_subtyping_cat; last by apply values_subtyping_size in IHHbet; apply values_subtyping_size in Hconjr0; lias.
          by resolve_subtyping.
      }
Qed.
      
End Host.
