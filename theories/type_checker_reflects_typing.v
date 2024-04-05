(** Soundness and correctness of the type checker **)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

From Coq Require Import Program Wf_nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Wasm Require Import type_checker typing_inversion.

Section Host.

Context {hfc: host_function_class}.

Definition ct_subtyping (ct1 ct2: checker_type) :=
  c_types_agree ct1 ct2.(CT_type) &&
    ((ct1.(CT_unr) == true) || (ct2.(CT_unr) == false)).

Notation "ct1 <ct: ct2" := (ct_subtyping ct1 ct2) (at level 5).

Lemma lookup_N_map {T1 T2: Type}: forall (f: T1 -> T2) (l: list T1) n,
    lookup_N (map f l) n = option_map f (lookup_N l n).
Proof.
  move => f l n.
  by apply nth_error_map'.
Qed.

Lemma expand_t_context_reverse: forall C tb tf,
    expand_t C tb = Some tf ->
    expand_t (context_reverse C) tb = Some (rev_tf tf).
Proof.
  intros.
  unfold expand_t in *; destruct tb => //=; first by rewrite lookup_N_map H.
  by remove_bools_options.
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

Lemma same_lab_h_condition: forall labs ts l,
  List.Forall (fun i => lookup_N labs i = Some ts) l ->
  same_lab_h l labs ts = Some ts.
Proof.
  move => C ts l.
  move: C ts.
  induction l => //=.
  move => C ts H.
  inversion H; subst; clear H.
  rewrite H2 eq_refl.
  by apply IHl.
Qed.

Lemma same_lab_h_all: forall labs ts l,
  same_lab_h l labs ts = Some ts ->
  List.Forall (fun i => lookup_N labs i = Some ts) l.
Proof.
  move => C ts l.
  move: C ts.
  induction l => //=.
  move => C ts H.
  remove_bools_options.
  move/eqP in Hif; subst.
  constructor => //.
  by apply IHl.
Qed.
  
Lemma same_lab_h_rec: forall x l labs ts,
  same_lab_h (x :: l) labs ts = Some ts ->
  same_lab_h l labs ts = Some ts.
Proof.
  move => x l C ts H.
  simpl in H.
  remove_bools_options.
  by move/eqP in Hif; subst.
Qed.

Lemma same_lab_h_consistent: forall l lab ts ts',
  same_lab_h l lab ts' = Some ts ->
  ts = ts'.
Proof.
  induction l => //=; intros; first by inversion H.
  remove_bools_options.
  move/eqP in Hif; subst.
  by apply IHl in H.
Qed.

Lemma same_lab_same_lab_h: forall l lab ts,
  same_lab l lab = Some ts ->
  same_lab_h l lab ts = Some ts.
Proof.
  move => l lab ts H.
  unfold same_lab in H.
  destruct l => //=; remove_bools_options.
  rewrite H.
  replace l0 with ts => //=; first by rewrite eq_refl.
  by apply same_lab_h_consistent in H.
Qed.

Lemma same_lab_h_same_lab: forall l lab ts,
  same_lab_h l lab ts = Some ts ->
  l <> nil ->  
  same_lab l lab = Some ts.
Proof.
  move => l lab ts H Hnil.
  unfold same_lab_h in H.
  by destruct l => //=; remove_bools_options.
Qed.

Lemma same_lab_rev: forall iss lab_c ts,
    same_lab iss lab_c = Some ts ->
    same_lab iss (map rev lab_c) = Some (rev ts).
Proof.
  move => iss lab_c ts Hlab.
  destruct iss => //.
  apply same_lab_h_same_lab => //.
  apply same_lab_h_condition.
  apply same_lab_same_lab_h, same_lab_h_all in Hlab.
  apply Forall_spec.
  move => n x Hnth.
  eapply Forall_lookup in Hlab; eauto.
  by rewrite lookup_N_map Hlab.
Qed.

(*
Lemma type_update_agree_weaken: forall ts cons prod ts2 ts' unr,
  c_types_agree (type_update (CT_type ts false) cons prod) ts2 ->
  ((unr && (ts' <ts: take (size ts') ts)) || ((negb unr) && (ts' <ts: ts))) ->
  c_types_agree (type_update (CT_type ts' unr) cons prod) ts2.
Proof.
Admitted.
  
Lemma c_types_agree_weaken: forall C ts ts' ts2 e unr,
  c_types_agree (check_single C (CT_type ts false) e) ts2 ->
  ((unr && (ts' <ts: take (size ts') ts)) || ((negb unr) && (ts' <ts: ts))) ->
  c_types_agree (check_single C (CT_type ts' unr) e) ts2.
Proof.
  move => C ts ts' ts2 e.
  move: C ts ts' ts2.
  Opaque type_update.
  induction e; move => C ts ts' ts2 unr Hagree; unfold c_types_agree in *; simpl in * => //=; simplify_tc_goal; (try by eapply type_update_agree_weaken; eauto) => //=.
  (* Ref_is_null *)
  - specialize (type_update_agree_suffix H Hsuffix) as Hsuffix'.
    destruct topt => //=.
    + unfold type_update in H...
      replace (_.+1 - 1) with (length topt); last by lias.
      destruct (List.nth_error (c :: topt) (length topt)) eqn:Hnth; last first.
      { apply List.nth_error_None in Hnth; simpl in Hnth; by lias. }
      { destruct c0...
        replace (length topt) with (length (c :: topt) - 1) in Hnth; last by lias.
        assert (ct_compat (CTA_some v0) (CTA_some v)) as Hcompat.
        { eapply ct_suffix_compat_index; try apply Hnth; eauto.
          apply nth_to_ct_list.
          uapply match_expr.
          do 2 f_equal.
          unfold to_ct_list.
          repeat rewrite length_is_size; by rewrite size_map.
        }
        by auto_rewrite_cond.
      }
  - by eapply type_update_select_agree; eauto.
  - simplify_goal.
    by eapply type_update_agree_suffix; eauto.
Qed.
 *)

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
  | H: unop_type_agree ?t ?op |- _ =>
      destruct t, op; inversion H; subst; clear H
  | H: binop_type_agree ?t ?op |- _ =>
      destruct t, op; inversion H; subst; clear H
  | H: relop_type_agree ?t ?op |- _ =>
      destruct t, op; inversion H; subst; clear H
  | H: lookup_N ?l ?n = ?x
    |- context [lookup_N (map _ ?l) ?n] =>
    rewrite lookup_N_map H
  | H: expand_t ?C ?tb = ?tf
    |- context [expand_t (context_reverse ?C) ?tb] =>
      rewrite (expand_t_context_reverse H)
  | H: context C [ match ?u with | Unop_i _ => _ | Unop_f _ | _ => _ end ] |- _ => destruct u => //=
  | H: context C [ match ?b with | Binop_i _ => _ | Binop_f _ => _ end ] |- _ => destruct b => //=
  | H: context C [ match ?r with | Relop_i _ => _ | Relop_f _ => _ end ] |- _ => destruct r => //=
  | |- context [ consume _ nil ] => rewrite consume_nil
  | |- context [ consume <<?ts, _>> ?ts ] => rewrite consume_self
  | |- context [ consume <<(?ts ++ _), _>> ?ts ] => rewrite consume_prefix
  | |- context [ take 0 _ ] => rewrite take0
  | |- context [ _ ++ nil ] => rewrite cats0
  | |- context [ rev (_ ++ _) ] => rewrite rev_cat
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
    c_types_agree <<t :: cts, unr>> (t' :: ts) ->
    t <t: t' /\ c_types_agree <<cts, unr>> ts.
Proof.
  by unfold c_types_agree; move => ? [|] ????; simplify_tc_goal.
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
(*
Lemma consume_subtyping_top: forall ts ts' l res,
    consume <<ts, false>> l = Some <<res, false>> ->
    ts' <ts: take (size ts') ts ->  
    exists res', consume <<ts', true>> l = Some <<res', true>> /\
            res' <ts: take (size res') res.
Proof.
  move => ts ts' l res Hconsume Hsub.
  apply consume_Some_impl in Hconsume as [Hsub' Hsuffix]; subst.
  exists (drop (size l) ts'); split.
  - apply consume_Some_spec_top => //.
    move : ts l Hsub' Hsub.
    induction ts'; destruct ts, l => //=.
    move => Hsub1 Hsub2; simplify_tc_goal.
    by eapply IHts'; eauto.
  - move : ts l Hsub' Hsub.
    induction ts'; destruct ts, l => //=; move => Hsub1 Hsub2; simplify_tc_goal.
    by eapply IHts'; eauto.
Qed.
*)
  
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
  - destruct f0; by eapply type_update_reachable; eauto.
  - destruct f; by eapply type_update_reachable; eauto.
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

(*
Lemma check_single_subtyping_top: forall C e ts1 ts1' ts2 unr1 unr2,
  check_single C (Some <<ts1, false>>) e = Some <<ts2, unr2>> ->
  ts1' <ts: take (size ts1') ts1 ->
  exists ts2', check_single C (Some <<ts1', true>>) e = Some <<ts2', unr2>> /\
          ts2' <ts: ts2.
Proof.
  move => C e.
  move: C.
  induction e; move => C ts1 ts1' ts2 unr1 unr2 Hcheck Hsub; simplify_tc_goal; (try destruct i); (try destruct f0); (try destruct f); simplify_tc_goal; (try by eapply type_update_subtyping in Hcheck; eauto); (try by eapply type_update_subtyping_top in Hcheck; eauto); (try by eexists; split; eauto).
  - unfold type_update_ref_is_null in *; simpl in *.
    destruct ts1, ts1'; simpl in *; simplify_tc_goal; try by eexists.
    replace (is_ref_t v0) with true; last by destruct v, v0.
    by eexists.
  - unfold type_update_drop in *; simpl in *.
    destruct ts1, ts1'; simpl in *; simplify_tc_goal; by eexists.
  - unfold type_update_select in *.
    destruct o => //; simpl in *.
    + do 2 (try destruct l => //).
      by eapply type_update_subtyping in Hcheck; eauto.
    + do 3 (try destruct ts1, ts1' => //); simplify_tc_goal.
      * by eexists; split; eauto => //; resolve_subtyping.
      * by eapply type_update_subtyping in Hcheck; eauto => /=; resolve_subtyping.
      * replace (is_numeric_type v2) with true; last by destruct v1, v2.
        by eexists; split; eauto => //=; resolve_subtyping.
      * eapply value_type_select_subtyping in Hoption as [v' [Hvtselect Hsub]]; eauto.
        rewrite Hvtselect.
        unfold type_update in *; simplify_tc_goal.
        replace (v0 <t: T_num T_i32) with true; last by erewrite value_subtyping_trans; eauto.
        unfold produce => /=.
        exists (v' :: ts1'); split => //=.
        by resolve_subtyping.
Qed.
*)
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
  - destruct e => //=; (try destruct i as [tn' tm']); simplify_tc_goal; move => cts' Hs Hct Hct2 => //.
    (*
    (* Const_num *)
    + by resolve_no_consume cts [::T_num (typeof_num v)] tm.
    (* Unop_i *)
    + by destruct n; resolve_update_agree.
    (* Unop_f *)
    + by destruct n; resolve_update_agree.
    (* Unop_extend *)
    + by destruct n; resolve_update_agree.
    (* Binop_i *)
    + by destruct n; resolve_update_agree.
    (* Binop_f *)
    + by destruct n; resolve_update_agree.
    (* Testop *)
    + by resolve_update_agree.
    (* Relop_i *)
    + by destruct n; resolve_update_agree.
    (* Relop_f *)
    + by destruct n; resolve_update_agree.
    (* Cvtop *)
    + by resolve_update_agree.
    (* Const_vec *)
    + by resolve_no_consume cts [::T_vec (typeof_vec v)] tm.
    (* Const_vec *)
    + by resolve_no_consume cts [::T_ref r] tm.
    (* Ref_is_null *)
    + by apply type_update_ref_is_null_bet.
    (* Ref_func *)
    + resolve_no_consume cts [::T_ref T_funcref] tm.
      econstructor; eauto.
      by move/inP in if_expr0.
    (* Drop *)
    + destruct cts => //=; clear if_expr.
      * move: Hct2. case/lastP : l => [| l x] => //=; move => Hsuf.
        { exists (tm ++ [::T_num T_i32]); split; first by apply ct_suffix_empty.
          apply bet_weakening_empty_2.
          by apply bet_drop.
        }
        { exists (tm ++ [::populate_ct_aux_single x]).
          split; last by apply bet_weakening_empty_2; apply bet_drop.
          rewrite cats1.
          unfold to_ct_list.
          rewrite map_rcons.
          apply ct_suffix_rcons.
          split; first by destruct x => //=.
          rewrite ct_suffix_any_1 in Hsuf; last by rewrite size_rcons.
          rewrite - cats1 in Hsuf.
          simpl in Hsuf.
          rewrite size_cat take_cat in Hsuf.
          simpl in Hsuf.
          replace (size l + 1 - 1) with (size l) in Hsuf; last by lias.
          rewrite subnn take_size cats0 in Hsuf.
          by destruct (size l < size l) => //=.
        }
      * simpl in Hct2...
        exists l; split => //.
        move: if_expr. case/lastP: l => [|l x] => //=; move => _.
        rewrite - cats1.
        rewrite size_cat take_cat => /=.
        replace (size l + 1 - 1) with (size l); last by lias.
        rewrite take_size subnn cats0.
        replace (size l < size l) with false; last by clear H; lias.
        apply bet_weakening_empty_2.
        by apply bet_drop.
    (* Select *)
    + by apply type_update_select_agree_bet.
      (* Local_get *)
    + by resolve_update_agree.
      (* Local_set *)
    + by resolve_update_agree.
      (* Local_tee *)
    + by resolve_update_agree.
      (* Global_set *)
    + by resolve_update_agree.
      (* Global_get *)
    + by resolve_update_agree.
      (* Table_get *)
    + by resolve_update_agree.
      (* Table_set *)
    + by resolve_update_agree.
      (* Table_size *)
    + by resolve_no_consume cts [::T_num T_i32] tm.
      (* Table_grow *)
    + by resolve_update_agree.
      (* Table_fill *)
    + by resolve_update_agree.
      (* Table_copy *)
    + fold_type_update Hct2.
      by resolve_update_agree.
      (* Table_init *)
    + fold_type_update Hct2.
      by resolve_update_agree.
      (* Elem_drop *)
    + exists tm; split => //.
      by apply bet_weakening_empty_both; econstructor; eauto.
      (* Load *)
    + by resolve_update_agree.
      (* Store *)
    + fold_type_update Hct2.
      by resolve_update_agree.
      (* Memory_size *)
    + by resolve_no_consume cts [::T_num T_i32] tm.
      (* Memory_grow *)
    + by resolve_update_agree.
      (* Memory_fill *)
    + fold_type_update Hct2.
      by resolve_update_agree.
      (* Memory_copy *)
    + fold_type_update Hct2.
      by resolve_update_agree.
      (* Memory_init *)
    + fold_type_update Hct2.
      by resolve_update_agree.
      (* Data_drop *)
    + exists tm; split => //.
      by apply bet_weakening_empty_both; econstructor; eauto.
      (* Nop *)
    + exists tm; split => //.
      by apply bet_weakening_empty_both; econstructor; eauto.
      (* Unreachable *)
    + exists (populate_ct cts); split; by [apply populate_ct_agree | apply bet_unreachable].
      (* Block *)
    + destruct i.
      fold_remember_check.
      assert (be_size_list l < d)%coq_nat as Hmeasure; first by unfold be_size_list; lias.
      apply H in Hmeasure.
      destruct Hmeasure as [IH _].
      auto_rewrite_cond.
      eapply IH in if_expr0 => //; eauto.
      destruct if_expr0 as [tn'' [Hct1 Hbet]].
      simpl in Hct1.
      move/eqP in Hct1; subst.
      apply type_update_type_agree in Hct2.
      destruct Hct2 as [lp [Hct1 Heq]]; subst.
      exists (lp ++ tn''); split => //.
      by apply bet_weakening; econstructor; eauto.
      (* Loop *)
    + destruct i.
      fold_remember_check.
      assert (be_size_list l < d)%coq_nat as Hmeasure; first by unfold be_size_list; lias.
      apply H in Hmeasure.
      destruct Hmeasure as [IH _].
      auto_rewrite_cond.
      eapply IH in if_expr0 => //.
      destruct if_expr0 as [tn'' [Hct1 Hbet]].
      simpl in Hct1.
      move/eqP in Hct1; subst.
      apply type_update_type_agree in Hct2.
      destruct Hct2 as [lp [Hct1 Heq]]; subst.
      exists (lp ++ tn''); split => //.
      by apply bet_weakening; econstructor; eauto.
      (* If *)
    + destruct i.
      fold_remember_check.
      fold (be_size_list l) in Hs.
      fold (be_size_list l0) in Hs.
      assert (be_size_list l < d)%coq_nat as Hmeasure1; first by lias.
      assert (be_size_list l0 < d)%coq_nat as Hmeasure2; first by lias.
      apply H in Hmeasure1.
      destruct Hmeasure1 as [IH1 _].
      apply H in Hmeasure2.
      destruct Hmeasure2 as [IH2 _].
      auto_rewrite_cond.
      eapply IH1 in H0 => //.
      eapply IH2 in H1 => //.
      destruct H0 as [tn1'' [Hctif1 Hbet1]].
      destruct H1 as [tn2'' [Hctif2 Hbet2]].
      simpl in *.
      move/eqP in Hctif1; subst.
      move/eqP in Hctif2; subst.
      apply type_update_type_agree in Hct2.
      destruct Hct2 as [lp [Hct1 Heq]]; subst.
      exists (lp ++ tn2'' ++ [::T_num T_i32]); split => //.
      by apply bet_weakening; econstructor; eauto.
      (* Br *)
    + unfold type_update in Hct2.
      assert (consume cts (to_ct_list r) <> CT_error) as Hconsume; first by destruct (consume _ _).
      apply tc_to_bet_br in Hconsume.
      destruct Hconsume as [tn Hcts].
      exists (tn ++ r); split => //.
      by constructor.
      (* Br_if *)
    + apply type_update_type_agree in Hct2.
      destruct Hct2 as [tn' [Hctif Hbet]]. subst.
      exists (tn' ++ r ++ [::T_num T_i32]); split => //.
      apply bet_weakening.
      by constructor.
      (* Br_table *)
    + unfold type_update in Hct2.
      assert (consume cts (to_ct_list (l1 ++ [::T_num T_i32])) <> CT_error) as Hconsume; first by destruct (consume _ _).
      apply tc_to_bet_br in Hconsume as [tn Hcts].
      exists (tn ++ l1 ++ [::T_num T_i32]); split => //.
      econstructor.
      apply same_lab_same_lab_h in match_expr.
      by apply same_lab_h_all.
      (* Return *)
    + unfold type_update in Hct2.
      assert (consume cts (to_ct_list r) <> CT_error) as Hconsume; first by destruct (consume _ _).
      apply tc_to_bet_br in Hconsume as [tn Hcts].
      exists (tn ++ r); split => //.
      by apply bet_return.
    + destruct f0...
      apply type_update_type_agree in Hct2.
      destruct Hct2 as [tn' [Hct Hbet]]; subst.
      exists (tn' ++ r); split => //=.
      apply bet_weakening.
      by apply bet_call.
    + destruct f...
      apply type_update_type_agree in Hct2.
      destruct Hct2 as [tn' [Hct Hbet]]; subst.
      exists (tn' ++ r ++ [::T_num T_i32]); split => //=.
      apply bet_weakening.
      by eapply bet_call_indirect; eauto => //=.
Qed.
     *)
    Admitted.
      
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

Lemma value_type_select_refl: forall t,
    is_numeric_type t ->
    value_type_select t t = Some t.
Proof.
  unfold value_type_select.
  move => t -> => /=.
  destruct t => /=; try by rewrite eq_refl.
  reflexivity.
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
    + (* inP is slightly stupid *)
      move/(@inP u32_eqType) in H0.
      by rewrite H0.
    + rewrite value_type_select_refl => //.
      unfold c_types_agree.
      by simplify_tc_goal.
    (* Br_table *)
    + apply same_lab_h_condition in H.
      apply same_lab_h_same_lab in H; last by destruct ins.
      apply same_lab_rev in H.
      by unfold c_types_agree; simplify_tc_goal.
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
      
(*
Lemma size_ct_list: forall l,
  size (to_ct_list l) = size l.
Proof.
  unfold to_ct_list. by apply size_map.
Qed.
  
Lemma ssr_nth_error: forall {T: Type} (l: list T) n (x x0:T),
  nth x0 l n = x ->
  n < size l ->
  List.nth_error l n = Some x.
Proof.
  induction l; destruct n => //=; intros; subst => //=.
  eapply IHl; eauto; by lias.
Qed.

(* Old weakening rule *)
Lemma bet_weakening: forall C es ts ts1 ts2,
    be_typing C es (Tf ts1 ts2) ->
    be_typing C es (Tf (ts ++ ts1) (ts ++ ts2)).
Proof.
  intros ????? Hbet.
  eapply bet_subtyping; eauto.
  by resolve_subtyping.
Qed.

Lemma ct_compat_symmetry: forall c1 c2,
  ct_compat c1 c2 ->
  ct_compat c2 c1.
Proof.
  intros.
  destruct c1, c2 => //=.
  simpl in H.
  move/eqP in H.
  subst.
  by apply/eqP.
Qed.

Lemma ct_list_compat_rcons_bool: forall l1 l2 x1 x2,
  ct_list_compat (rcons l1 x1) (rcons l2 x2) =
  ct_compat x1 x2 && ct_list_compat l1 l2.
Proof.
  induction l1; intros; destruct l2 => //=.
  - destruct l2 => //=; by lias.
  - destruct l1 => //=; by lias.
  - rewrite IHl1. by lias.
Qed.
    
Lemma ct_list_compat_rcons: forall l1 l2 x1 x2,
  ct_list_compat (rcons l1 x1) (rcons l2 x2) <->
  ct_compat x1 x2 /\ ct_list_compat l1 l2.
Proof.
  split; intros.
  - rewrite ct_list_compat_rcons_bool in H.
    by move/andP in H.
  - move/andP in H.
    by rewrite ct_list_compat_rcons_bool.
Qed.

Lemma ct_suffix_rcons: forall l1 l2 x1 x2,
  ct_suffix (rcons l1 x1) (rcons l2 x2) <->
  ct_compat x1 x2 /\ ct_suffix l1 l2.
Proof.
  unfold ct_suffix.
  intros.
  split; move => H.
  - move/andP in H; destruct H.
    repeat rewrite size_rcons in H.
    rewrite drop_rcons in H0; last by repeat rewrite size_rcons; lias.
    apply ct_list_compat_rcons in H0.
    destruct H0.
    split => //; first by apply ct_compat_symmetry.
    apply/andP; split; first by lias.
    repeat rewrite size_rcons in H1.
    by replace (_-_) with (size l2 - size l1) in H1; last by lias.
  - destruct H.
    move/andP in H0; destruct H0.
    repeat rewrite size_rcons.
    apply/andP; split; first by lias.
    rewrite drop_rcons; last by lias.
    replace (_-_) with (size l2 - size l1); last by lias.
    apply ct_list_compat_rcons.
    split => //.
    by apply ct_compat_symmetry.
Qed.
    
Lemma ct_suffix_empty: forall l,
  ct_suffix [::] l.
Proof.
  move => l. unfold ct_suffix => /=.
  rewrite subn0. apply/eqP.
  by rewrite drop_size.
Qed.

Lemma ct_suffix_any_grow: forall l1 l2,
  ct_suffix l1 l2 ->
  size l1 < size l2 ->
  ct_suffix [::CTA_any & l1] l2.
Proof.
  unfold ct_suffix => /=.
  move => l1 l2 Hsuf Hsize.
  move/andP in Hsuf; destruct Hsuf as [_ Hcompat].
  apply/andP; split => //=.
  move: l1 l2 Hsize Hcompat.
  induction l1 using last_ind => //=; move => l2; case/lastP: l2 => [|l2 x']; intros => //.
  - rewrite -> size_rcons in *.
    replace (_-_) with (size l2); last by lias.
    remember (drop (size l2) _) as tail.
    assert (size tail = 1).
    { subst. rewrite size_drop size_rcons. by lias. }
    do 2 destruct tail => //=.
    by destruct c.
  - repeat rewrite size_rcons in Hsize.
    rewrite drop_rcons in Hcompat; last by repeat rewrite size_rcons; lias.
    rewrite drop_rcons; last by repeat rewrite size_rcons; lias.
    apply ct_list_compat_rcons in Hcompat.
    destruct Hcompat.
    repeat rewrite size_rcons in H0.
    replace (_-_) with (size l2 - size l1) in H0; last by lias.
    apply IHl1 in H0; eauto.
    repeat rewrite size_rcons.
    rewrite - rcons_cons.
    by apply ct_list_compat_rcons.
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
    simpl. remember (drop n l) as l'.
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

Lemma ct_suffix_prefix: forall l1 l2 l3,
  ct_suffix (l1 ++ l2) l3 ->
  ct_suffix l2 l3.
Proof.
  unfold ct_suffix; intros.
  move/andP in H; rewrite size_cat in H; destruct H.
  apply/andP; split; first by lias.
  unfold ct_list_compat in *.
  move : l2 l3 H H0.
  induction l1 => //; intros.
  destruct l3 => //.
  simpl in H.
  apply IHl1; first by lias.
  rewrite -> drop_nth with (x0 := a) in H0; last by lias.
  simpl in H0.
  move/andP in H0; destruct H0.
  replace (_-_) with (size l3 - (size l1 + size l2)) in H1; last by lias.
  simpl.
  by replace (_-_) with ((size l3 - (size l1 + size l2)).+1); last by lias.
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

Lemma produce_empty_top: forall l,
  l <> CT_error ->
  produce l (CT_top_type [::]) = CT_top_type [::].
Proof.
  move => l.
  unfold produce.
  by destruct l.
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
  | context C [size (map _ _)] => rewrite size_map in Hb
  | context C [size (_ ++ _)] => rewrite size_cat in Hb
  | context C [size (to_ct_list _)] => rewrite size_ct_list in Hb
  | context C [?x - 0] => rewrite subn0 in Hb; simpl in Hb
  | context C [?x - ?x] => rewrite subnn in Hb; simpl in Hb
  | context C [take (size ?x) ?x] => rewrite take_size in Hb; simpl in Hb
  | context C [drop (size ?x) ?x] => rewrite drop_size in Hb; simpl in Hb
  | context C [take 0 ?x] => rewrite take0 in Hb; simpl in Hb
  | context C [drop 0 ?x] => rewrite drop0 in Hb; simpl in Hb
  | context C [produce _ _] => unfold produce in Hb; simpl in Hb
  | context C [ match ?u with | Unop_i _ => _ | Unop_f _ | _ => _ end ] => destruct u => //=
  | context C [ match ?b with | Binop_i _ => _ | Binop_f _ => _ end ] => destruct b => //=
  | context C [ match ?r with | Relop_i _ => _ | Relop_f _ => _ end ] => destruct r => //=
  | context C [ match ?c with | CVO_convert => _ | _ => _ end ] => destruct c => //=
  | context C [ if ?expr then _ else _ ] => let if_expr := fresh "if_expr" in destruct expr eqn:if_expr => //=; simpl in Hb => //=
  | context C [ match ?expr with | Some _ => _ | None => _ end ] => let match_expr := fresh "match_expr" in destruct expr eqn:match_expr => //=; simpl in Hb => //=
  | exists _, _ /\ _ => let tx := fresh "tx" in
                        let Hsuffix := fresh "Hsuffix" in
                        let Hbet := fresh "Hbet" in
                        destruct Hb as [tx [Hsuffix Hbet]]
  | is_true true => clear Hb
  | is_true false => exfalso; apply: notF; apply: Hb
  | is_true (_ == _) => move/eqP in Hb
  | is_true (_ && _) => move/andP in Hb; destruct Hb
  | is_true (_ || _) => move/orP in Hb; destruct Hb
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
  | CTA_any => T_num T_i32
  | CTA_some vt => vt
  end.

Definition populate_ct_aux (l: list checker_type_aux): list value_type :=
  map populate_ct_aux_single l.

Definition populate_ct (ct: checker_type) : list value_type :=
  match ct with
  | CT_type tn => tn
  | CT_top_type tn => populate_ct_aux tn
  | CT_error => [::]
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
         | |- context C [size (to_ct_list _)] => rewrite size_ct_list => //=
         | |- context C [?x - ?x] => rewrite subnn => //=
         | |- context C [?x - 0] => rewrite subn0 => //=
         | |- context C [take 0 _] => rewrite take0 => //=
         | |- context C [take (size ?x) ?x] => rewrite take_size => //=
         | |- context C [drop 0 _] => rewrite drop0 => //=
         | |- context C [take (drop ?x) ?x] => rewrite drop_size => //=
         | |- context C [_ :: (tc_labels _)] => rewrite - cat1s => //=
         | |- context C [_ ++ [::]] => rewrite cats0 => //=
         | |- context C [size (_ ++ _)] => rewrite size_cat => //=
         | |- context C [size (_ ++ _)%list] => rewrite size_cat => //=
         | |- context C [?x + ?n - ?n] => replace (x + n - n) with x; last by lias => //=
         | |- context C [match ?f with | (Tf _ _) => _ end ] => destruct f => //=
(*         | |- context C [type_update _ _] => unfold type_update => //=*)
         | H: match ?expr with | _ => _ end = CT_type _ |- _ => let Hexpr := fresh "Hexpr" in destruct expr eqn: Hexpr => //=
         | H: match ?expr with | _ => _ end = CT_top_type _ |- _ => let Hexpr := fresh "Hexpr" in destruct expr eqn: Hexpr => //=
         | H: option_map _ _ = _ |- _ => unfold option_map in H
         | H: Some _ = Some _ |- _ => inversion H; subst; clear H => //=
         | H: CT_type _ = CT_type _ |- _ => inversion H; subst; clear H => //=
         | H: is_true (List.nth_error _ _ == _) |- _ => move/eqP in H; rewrite H => //=
         | H: is_true (_ == _) |- _ => move/eqP in H
         | H: ?x = ?x |- _ => clear H
         | H: _ = _ |- _=> progress (rewrite H; subst => //=)
         | _ => simplify_goal => //=; (try rewrite ct_suffix_suffix => //=); (try rewrite ct_suffix_self => //=); (try subst => //=)
         end.

Lemma populate_ct_aux_suffix: forall l,
  ct_suffix l (to_ct_list (populate_ct_aux l)).
Proof with auto_rewrite_cond.
  induction l => //=.
  unfold ct_suffix => /=.
  apply/andP; split.
  - repeat rewrite size_map. by lias.
  - unfold ct_list_compat.
    unfold ct_suffix, ct_list_compat, to_ct_list, populate_ct_aux in IHl...
    repeat rewrite size_map.
    rewrite subnn.
    simpl.
    destruct a => //=.
    by apply/andP.
Qed.

Lemma populate_ct_agree: forall l,
  l <> CT_error ->
  c_types_agree l (populate_ct l).
Proof.
  intros.
  destruct l => //=.
  by apply populate_ct_aux_suffix.
Qed.

Lemma type_update_select_prefix: forall l1 l2 l3 ots,
  type_update_select (CT_type l1) ots = CT_type l2 ->
  type_update_select (CT_type (l3 ++ l1)) ots = CT_type (l3 ++ l2).
Proof.
  unfold type_update_select.
  move => l1 l2 l3 ots.
  destruct ots.
  - do 2 destruct l => //.
    move => H.
    by apply type_update_prefix.
  - do 3 destruct l1 => //=.
    repeat rewrite length_is_size.
    rewrite size_cat => //=.
    replace (2 < _) with true; last by lias.
    repeat (rewrite List.nth_error_app2; try by repeat rewrite length_is_size; lias).
    repeat rewrite length_is_size.
    replace (_ + _ - 2 - _) with ((size l1).+1); last by lias.
    replace (_ + _ - 3 - _) with (size l1); last by lias.
    replace ((size l1).+3 - 3) with (size l1); last by lias.
    move => Htc.
    auto_rewrite_cond.
    unfold to_ct_list. rewrite map_cat.
    auto_rewrite_cond.
    rewrite ct_suffix_extend => //.
    rewrite take_cat.
    replace (_ < _) with false => /=; last by lias.
    replace (_ + _ - _ - _) with ((size l1).+1); last by lias.
    by repeat f_equal => //=.
Qed.
    
Lemma type_update_prefix_top: forall l1 l2 l3 cons prod,
  type_update (CT_type l1) cons prod = CT_top_type l2 ->
  type_update (CT_type (l3 ++ l1)) cons prod = CT_top_type l2.
Proof.
  unfold type_update, produce, consume.
  move => l1 l2 l3 cons prod H.
  auto_rewrite_cond.
  unfold to_ct_list.
  rewrite map_cat.
  by rewrite ct_suffix_extend => //.
Qed.

Lemma type_update_select_prefix_top: forall l1 l2 l3 ots,
  type_update_select (CT_type l1) ots = CT_top_type l2 ->
  type_update_select (CT_type (l3 ++ l1)) ots = CT_top_type l2.
Proof.
  unfold type_update_select.
  move => l1 l2 l3 ots.
  destruct ots as [ts |].
  - do 2 destruct ts => //.
    by apply type_update_prefix_top.
  - auto_rewrite_cond.
    unfold to_ct_list.
    rewrite map_cat.
    do 3 destruct l1 => //=.
    repeat rewrite length_is_size.
    rewrite size_cat => //=.
    replace (2 < _) with true; last by lias.
    repeat (rewrite List.nth_error_app2; try by repeat rewrite length_is_size; lias).
    repeat rewrite length_is_size.
    replace (_ + _ - 2 - _) with ((size l1).+1); last by lias.
    replace (_ + _ - 3 - _) with (size l1); last by lias.
    replace ((size l1).+3 - 3) with (size l1); last by lias.
    move => ?.
    by auto_rewrite_cond.
Qed.

Lemma check_single_weaken_top: forall C e ts ts2 ts0,
  check_single C (CT_type ts) e = CT_top_type ts0 ->
  check_single C (CT_type (ts2 ++ ts)) e = CT_top_type ts0.
Proof with auto_rewrite_cond.
  move => C e.
  move : C.
  induction e; move => C ts ts2 ts0 Htc; simpl in Htc => //=; simplify_goal; auto_rewrite_cond => //=; try (destruct i); simplify_goal; try by erewrite type_update_prefix_top; eauto...
  - erewrite type_update_prefix_top; eauto.
    destruct ts => //...
    repeat rewrite List.app_length.
    replace (_ < _) with true; last by lias.
    rewrite List.nth_error_app2; last by lias.
    replace (_ - 1 - length ts2) with (length ts); last by lias.
    replace ((length ts).+1 - 1) with (length ts) in match_expr; last by lias.
    by auto_rewrite_cond.
  - by apply type_update_select_prefix_top.
Qed.
    
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

Lemma ct_list_compat_trans: forall ts1 ts2 ts,
  ct_list_compat (to_ct_list ts) ts1 ->
  ct_list_compat (to_ct_list ts) ts2 ->
  ct_list_compat ts1 ts2.
Proof.
  move => ts1.
  induction ts1; move => ts2 ts H1 H2; destruct ts2, ts => //=.
  simpl in *.
  move/andP in H1; destruct H1.
  move/andP in H2; destruct H2.
  apply/andP; split.
  - destruct c, a => //=.
    move/eqP in H; move/eqP in H1.
    subst.
    by apply/eqP.
  by eapply IHts1; eauto.
Qed.

Lemma ct_suffix_take: forall l1 l2 n,
  ct_suffix l1 l2 ->
  n <= size l1 ->
  ct_suffix (take (size l1 - n) l1) (take (size l2 - n) l2).
Proof with auto_rewrite_cond.
  induction l1 using last_ind; case/lastP => [|l2' x'] => //=; intros.
  - by apply ct_suffix_empty.
  - by destruct l1 => //=.
  - rewrite size_rcons in H0.
    destruct n => //=.
    + repeat rewrite subn0.
      by repeat rewrite take_size.
    + repeat rewrite size_rcons.
      repeat rewrite subSS.
      apply ct_suffix_rcons in H; destruct H.
      repeat rewrite - cats1.
      repeat rewrite take_cat.
      destruct n => //=...
      * by destruct (size l1 < size l1), (size l2' < size l2') => //=.
      * assert (size l1 - n.+1 < size l1); first by lias...
        assert (size l1 <= size l2'); first by unfold ct_suffix in H1; move/andP in H1; destruct H1.
        assert (size l2' - n.+1 < size l2'); first by lias...
        by apply IHl1.
Qed.

Lemma ct_list_compat_cat: forall l1 l2 l3 l4,
  ct_list_compat l1 l2 ->
  ct_list_compat l3 l4 ->
  ct_list_compat (l1 ++ l3) (l2 ++ l4).
Proof.
  move => l1.
  induction l1 => //=; move => l2 l3 l4 Hct1 Hct2; destruct l2 => //=.
  move/andP in Hct1; destruct Hct1 as [H ?].
  rewrite H => /=.
  by apply IHl1.
Qed.
          
Lemma ct_list_compat_extend: forall l1 l2 l3,
  ct_list_compat l1 l2 ->
  ct_list_compat (l1 ++ l3) (l2 ++ l3).
Proof.
  intros.
  apply ct_list_compat_cat => //.
  by apply ct_list_compat_self.
Qed.

Lemma ct_list_compat_take: forall l1 l2 n,
  ct_list_compat l1 l2 ->
  ct_list_compat (take n l1) (take n l2).
Proof.
  move => l1.
  induction l1 => //=; move => l2 n H; destruct l2 => //=.
  move/andP in H; destruct H as [H1 H2].
  destruct n => //=.
  apply/andP; split => //.
  by apply IHl1.
Qed.

Lemma ct_list_compat_drop: forall l1 l2 n,
  ct_list_compat l1 l2 ->
  ct_list_compat (drop n l1) (drop n l2).
Proof.
  move => l1.
  induction l1 => //=; move => l2 n H; destruct l2 => //=.
  move/andP in H; destruct H as [H1 H2].
  destruct n => //=.
  apply/andP; split => //.
  by apply IHl1.
Qed.

Lemma ct_list_compat_drop_shift: forall l1 l2 n a b c1 c2,
  ct_list_compat (drop n l1) l2 ->
  a < size l1 ->
  b < size l2 ->
  a = b + n ->
  ct_compat (nth c1 l1 a) (nth c2 l2 b).
Proof.
  induction l1 as [| x l1'] => //=; move => l2 n a b c1 c2 Hcompat Hs1 Hs2 Hsum; destruct l2, a, b => //=.
  - destruct n => //. simpl in Hcompat.
    move/andP in Hcompat. by destruct Hcompat.
  - rewrite add0n in Hsum.
    subst.
    replace c with (nth c1 (c :: l2) 0) => //.
    by eapply IHl1'; eauto.
  - eapply IHl1'; eauto.
    destruct n => //=.
    + simpl in Hcompat.
      move/andP in Hcompat.
      destruct Hcompat.
      by rewrite drop0.
    + rewrite -> drop_nth with (x0 := CTA_any) in Hcompat; last by lias.
      simpl in Hcompat.
      move/andP in Hcompat.
      by destruct Hcompat.
Qed.

Lemma ct_list_nth_type: forall l c n,
  n < size l ->
  exists t, nth c (to_ct_list l) n = CTA_some t.
Proof.
  induction l; destruct n => //=; move => Hsize.
  - by eexists.
  - by eapply IHl; eauto.
Qed.

(*
  We need the mutual ct type to be from ct_list, since CTA_any destroys transitivity. 
*)
Lemma ct_compat_mutual: forall ts1 ts2 ts_mutual ts,
  ts_mutual = to_ct_list ts ->
  size ts1 <= size ts_mutual ->
  size ts2 <= size ts_mutual ->
  ct_list_compat (drop (size ts_mutual - size ts1) ts_mutual) ts1 ->
  ct_list_compat (drop (size ts_mutual - size ts2) ts_mutual) ts2 ->
  size ts1 <= size ts2 ->
  ct_list_compat (drop (size ts2 - size ts1) ts2) ts1.
Proof.
  move => ts1.
  induction ts1; move => ts2 ts_mutual ts Hnany Hs1 Hs2 Hct1 Hct2 Hsize => //=.
  - rewrite subn0. by rewrite drop_size.
  - destruct ts2 => //=.
    destruct ts_mutual, ts => //=.
    simpl in *.
    inversion Hnany; subst; clear Hnany.
    destruct (size ts2 == size ts1) eqn: Heq1 => //=; move/eqP in Heq1.
    + rewrite Heq1.
      rewrite Heq1 in Hct2.
      rewrite subnn.
      destruct (size (to_ct_list ts) == size ts1) eqn: Heq2 => //=; move/eqP in Heq2.
      * rewrite Heq2 in Hct1, Hct2.
        rewrite subnn in Hct1, Hct2.
        replace (CTA_some v :: to_ct_list ts) with (to_ct_list (v :: ts)) in * => //=.
        rewrite drop0 in Hct1, Hct2.
        eapply ct_list_compat_trans in Hct1; eauto.
        by simpl in Hct1.
      * destruct (_-_) eqn:Hsub.
        -- assert ((size (to_ct_list ts)).+1 <= (size ts1).+1); first by lias.
           simpl in *. by lias.
        -- unfold to_ct_list in Hct1, Hct2.
           simpl in Hct1, Hct2.
           rewrite - map_drop in Hct1, Hct2.
           eapply ct_list_compat_trans in Hct1; eauto.
           by simpl in Hct1.
    + destruct ((size ts2).+1-(size ts1).+1) eqn:Hsub.
      * assert ((size ts2).+1 <= (size ts1).+1); first by lias.
        simpl in *. by lias.
      * assert (size ts1 < size (to_ct_list ts)); first by lias.
        destruct (_ - _) eqn:Hsub2; first by lias.
        destruct (size (to_ct_list ts) == size ts2) eqn: Heq3 => //=; move/eqP in Heq3.
        -- rewrite Heq3 in Hct2.
           rewrite subnn in Hct2.
           rewrite Heq3 in Hsub2.
           assert (n0 = n); first by lias.
           subst.
           simpl in Hct2.
           move/andP in Hct2; destruct Hct2 as [_ Hct2].
           eapply ct_list_compat_drop in Hct2.
           unfold to_ct_list in Hct1, Hct2.
           simpl in Hct1, Hct2.
           rewrite - map_drop in Hct1.
           rewrite - map_drop in Hct2.
           by eapply ct_list_compat_trans in Hct1; eauto.
        -- destruct ((size (to_ct_list ts)).+1 - (size ts2).+1) eqn:Hsub4.
           ++ assert ((size (to_ct_list ts)).+1 <= (size ts2).+1); first by lias.
              simpl in *. by lias.
           ++ assert (n < size ts2); first by lias.
              assert (n0 < size (to_ct_list ts)); first by lias.
              assert (n1 < size (to_ct_list ts)); first by lias.
              eapply drop_nth with (x0 := CTA_any) in H0.
              eapply drop_nth with (x0 := CTA_any) in H1.
              eapply drop_nth with (x0 := CTA_any) in H2.
              rewrite - Hsub in H0.
              rewrite - Hsub2 in H1.
              rewrite - Hsub4 in H2.
              rewrite H0.
              simpl in Hct1.
              rewrite H1 in Hct1.
              simpl in Hct2.
              rewrite H2 in Hct2.
              simpl in *.
              rewrite -> subSS in *.
              move/andP in Hct1; destruct Hct1 as [Hcs1 Hct1].
              move/andP in Hct2; destruct Hct2 as [Hcs2 Hct2].
              apply/andP; split.
              ** assert (ct_compat (nth CTA_any (to_ct_list ts) n0) (nth CTA_any ts2 n)) as Hcs3.
                 eapply ct_list_compat_drop_shift; eauto; by lias.
                 destruct (nth CTA_any ts2 n), a => //=.
                 assert (exists v, nth CTA_any (to_ct_list ts) n0 = CTA_some v) as Hv; first eapply ct_list_nth_type; eauto; first by unfold to_ct_list in Hsub2; rewrite size_map in Hsub2; lias.
                 destruct Hv as [vt Hv].
                 rewrite -> Hv in *.
                 simpl in *.
                 move/eqP in Hcs1.
                 move/eqP in Hcs3.
                 subst.
                 by apply/eqP.
              (* Finally the IH applies here... *)
              ** eapply IHts1; by eauto.
Qed.

Lemma ct_suffix_mutual_compat: forall ts1 ts2 ts_mutual ts,
  ts_mutual = to_ct_list ts ->
  ct_suffix ts1 ts_mutual ->
  ct_suffix ts2 ts_mutual ->
  size ts1 <= size ts2 ->
  ct_list_compat (drop (size ts2 - size ts1) ts2) ts1.
Proof with auto_rewrite_cond.
  move => ts1 ts2 ts_mutual ts Hnany Hsuffix1 Hsuffix2 Hsize.
  subst.
  unfold ct_suffix in *...
  by eapply ct_compat_mutual; auto_rewrite_cond; eauto.
Qed.

Lemma ct_suffix_mutual_suffix: forall ts1 ts2 ts_mutual ts,
  ts_mutual = to_ct_list ts ->
  ct_suffix ts1 ts_mutual ->
  ct_suffix ts2 ts_mutual ->
  size ts1 <= size ts2 ->
  ct_suffix ts1 ts2.
Proof with auto_rewrite_cond.
  move => ts1 ts2 ts_mutual ts Hnany Hsuffix1 Hsuffix2 Hsize.
  subst.
  unfold ct_suffix in *...
  by eapply ct_compat_mutual; auto_rewrite_cond; eauto.
Qed.

Lemma le_neq_lt: forall a b,
    a <= b ->
    a <> b ->
    a < b.
Proof.
  by lias.
Qed.

Lemma sub_if: forall a b,
  (if a-b < a then a-b else a) = a-b.
Proof.
  move => a b.
  destruct (a-b<a) eqn:H; by lias.
Qed.
  
Lemma type_update_agree_suffix: forall ts cons prod ts2 topt,
  c_types_agree (type_update (CT_type ts) cons prod) ts2 ->
  ct_suffix topt (to_ct_list ts) ->
  c_types_agree (type_update (CT_top_type topt) cons prod) ts2.
Proof with auto_rewrite_cond.
  move => ts cons prod ts2 topt Hct Hsuffix.
  unfold type_update, c_types_agree, produce, consume, ct_suffix, to_ct_list in * => /=...
  destruct (size cons <= size topt) eqn:Hsize => //=.
  - remember Hsize as Hsize_ct; clear HeqHsize_ct.
    apply ct_compat_mutual with (ts := ts) (ts_mutual := to_ct_list ts) in Hsize; eauto...
    rewrite size_map.
    destruct prod => //=...
    apply/andP; split.
    + repeat rewrite size_take.
      rewrite size_map.
      repeat rewrite sub_if.
      by lias.
    + repeat rewrite size_take.
      repeat rewrite size_map.
      repeat rewrite sub_if.
      rewrite - map_drop.
      rewrite drop_cat.
      rewrite size_take.
      rewrite sub_if.
      replace (_ - _ + _ - _) with (size ts - size topt); last by lias.
      move/leP in Hsize_ct.
      destruct (size ts - size topt == size ts - size cons) eqn:Heq.
      * replace (_ - _ < _ - _) with false => //=; last by lias.
        replace (_ - _ - _) with 0; last by lias.
        rewrite drop0.
        assert (size topt = size cons); first by lias.
        rewrite -> H3 in *.
        rewrite subnn.
        rewrite take0 => //=.
        by apply ct_list_compat_self.
      * assert (size ts - size topt <= size ts - size cons); first by lias.
        move/eqP in Heq.
        apply le_neq_lt in H3 => //.
        rewrite H3.
        rewrite map_cat.
        apply ct_list_compat_extend.
        replace (size ts - size cons) with ((size topt - size cons) + (size ts - size topt)); last by lias.
        rewrite - take_drop.
        rewrite map_take.
        apply ct_list_compat_take.
        by rewrite map_drop.
  - assert (size topt <= size cons) as Hsize2; first by lias.
    rewrite Hsize2.
    apply ct_compat_mutual with (ts := ts) (ts_mutual := to_ct_list ts) in Hsize2 => //...
    rewrite size_map.
    destruct prod => //=...
    repeat rewrite size_map.
    rewrite size_take.
    rewrite sub_if.
    apply/andP; split; first by lias.
    rewrite map_cat map_take.
    replace (_ - _ + _ - _) with (size ts - size cons); last by lias.
    rewrite drop_cat.
    rewrite size_take size_map.
    rewrite sub_if => /=.
    replace (_ < _) with false; last by lias.
    rewrite subnn drop0.
    by apply ct_list_compat_self.
Qed.

Lemma ct_suffix_any_take_2: forall ts,
  2 < size ts ->
  ct_suffix [::CTA_any] (to_ct_list (take (size ts - 2) ts)).
Proof.
  move => ts H.
  apply ct_suffix_any_1.
  rewrite size_ct_list size_take sub_if.
  by lias.
Qed.

Lemma ct_suffix_compat_index: forall l1 l2 n t1 t2,
  ct_suffix l1 l2 ->
  n >= 1 ->
  n <= size l1 ->
  List.nth_error l1 (length l1 - n) = Some t1 ->
  List.nth_error l2 (length l2 - n) = Some t2 ->
  ct_compat t1 t2.
Proof.
  move => l1 l2 n t1 t2 Hsuf Hn Hsize Hn1 Hn2.
  unfold ct_suffix in Hsuf.
  move/andP in Hsuf; destruct Hsuf as [Hsize2 Hcompat].
  rewrite length_is_size in Hn1.
  rewrite length_is_size in Hn2.
  apply nth_error_nth' with (x0 := t1) in Hn1.
  apply nth_error_nth' with (x0 := t2) in Hn2.
  apply ct_list_compat_drop_shift with (a := size l2 - n) (b := size l1 - n) (c1 := t2) (c2 := t1) in Hcompat; by [rewrite Hn1 Hn2 in Hcompat; apply ct_compat_symmetry | lias | lias | lias].
Qed.

Lemma ct_suffix_append_compat: forall l1 l2 l3 l4,
  ct_suffix l1 l2 ->
  ct_list_compat l3 l4 ->
  ct_suffix (l1 ++ l3) (l2 ++ l4).
Proof with auto_rewrite_cond.
  move => l1 l2 l3.
  move : l1 l2.
  induction l3 using last_ind; move => l1 l2 l4; case/lastP : l4 => [|l4 x'] => //=; move => Hsuf H...
  - by destruct l4 => //=.
  - by destruct l3 => //=.
  - apply ct_list_compat_rcons in H.
    destruct H.
    repeat rewrite - rcons_cat.
    apply ct_suffix_rcons; split => //.
    by apply IHl3.
Qed.
  
Lemma nth_to_ct_list: forall ts n x,
  List.nth_error ts n = Some x ->
  List.nth_error (to_ct_list ts) n = Some (CTA_some x).
Proof.
  intros ts n x H.
  assert (n < length ts)%coq_nat as Hsize; first by rewrite - List.nth_error_Some; rewrite H.
  eapply nth_error_nth' with (x0 := x) in H.
  assert (nth (CTA_some x) (to_ct_list ts) n = CTA_some x) as Hssr.
  { unfold to_ct_list. rewrite -> nth_map with (x1 := x); last by lias. by rewrite H. }
  by apply ssr_nth_error in Hssr; last by unfold to_ct_list; rewrite size_map; lias.
Qed.

Lemma select_return_top_suffix: forall c2 c3 ts topt topts,
  select_return_top topt c2 c3 = CT_top_type topts ->
  ct_suffix topt (to_ct_list ts) ->  
  List.nth_error topt (length topt - 2) = Some c2 ->
  List.nth_error topt (length topt - 3) = Some c3 ->
  List.nth_error ts (length ts - 2) = List.nth_error ts (length ts - 3) ->
  2 < length topt ->
  2 < size ts ->
  ct_suffix topts (to_ct_list (take (size ts - 2) ts)).
Proof with auto_rewrite_cond.
  move => c2 c3 ts topt topts Hselect Hsuffix Hn2 Hn3 Hts3 Hsize1 Hsize2.
  unfold select_return_top in Hselect.
  destruct (List.nth_error ts (length ts-2)) eqn:Hts2; last by apply List.nth_error_None in Hts2; rewrite length_is_size in Hts2; lias.
  symmetry in Hts3.
  remember Hts3 as Hts3'; clear HeqHts3'.
  apply nth_error_nth' with (x0 := v) in Hts3'.
  apply nth_to_ct_list in Hts2.
  apply nth_to_ct_list in Hts3.
  replace (length ts) with (length (to_ct_list ts)) in Hts2; last by repeat rewrite length_is_size; unfold to_ct_list; rewrite size_map.
  replace (length ts) with (length (to_ct_list ts)) in Hts3; last by repeat rewrite length_is_size; unfold to_ct_list; rewrite size_map.
  eapply ct_suffix_compat_index in Hts2; eauto.
  eapply ct_suffix_compat_index in Hts3; eauto.
  assert (ct_suffix (take (size topt - 3) topt) (take (size (to_ct_list ts) - 3) (to_ct_list ts)))as Hsuffixm3; first by apply ct_suffix_take.
  replace (size ts - 2) with ((size ts - 3).+1); last by lias.
  rewrite -> take_nth with (x0 := v); last by lias.
  replace (size (to_ct_list ts)) with (size ts) in Hsuffixm3; last by unfold to_ct_list; rewrite size_map.
  destruct c2, c3 => //=; auto_rewrite_cond; inversion Hselect; subst; clear Hselect; repeat rewrite length_is_size; unfold to_ct_list; rewrite map_rcons; rewrite cats1; rewrite ct_suffix_rcons; rewrite map_take; split => //; by unfold ct_compat.
Qed.

(*
  This is a rather tedious single case.
 *)
Lemma type_update_select_agree: forall topt ts ot ts2,
  c_types_agree (type_update_select (CT_type ts) ot) ts2 ->
  ct_suffix topt (to_ct_list ts) ->
  c_types_agree (type_update_select (CT_top_type topt) ot) ts2.
Proof with auto_rewrite_cond.
  move => topt ts ot ts2 Htype Hsuffix.
  unfold type_update_select in *.
  (* The case where the selected type is specified can be solved by a lemma. *)
  auto_rewrite_cond; try (by do 2 destruct l => //; by eapply type_update_agree_suffix; eauto).
  (* The Wasm 1.0 select -- unspecified type *)
  rewrite length_is_size in if_expr.
  destruct topt => //=; first by apply ct_suffix_any_take_2...
  destruct topt => //=...
  - (* 1 *)
    eapply ct_suffix_mutual_compat with (ts1 := [::c]) in if_expr0...
    destruct c => //=; auto_rewrite_cond; by apply ct_suffix_any_take_2...
  - destruct topt => //=...
    + (* 2 *)
      eapply ct_suffix_mutual_compat with (ts1 := [::c; c0]) in if_expr0...
      assert (ct_suffix [::CTA_some (T_num T_i32)] [::c; c0] = true) as Hsuffix2; first destruct c0 => //=...
      destruct c => //; auto_rewrite_cond; first apply ct_suffix_any_1.
      { rewrite size_map size_takel; by lias. }

      assert (ct_compat (CTA_some v) (CTA_some v0)) as Heq.
      { eapply ct_suffix_compat_index with (n := 2); try apply Hsuffix => //; try by lias.
        apply nth_to_ct_list.
        uapply match_expr0.
        do 2 f_equal.
        by repeat rewrite length_is_size; rewrite size_map.
      }
      simpl in Heq; move/eqP in Heq; subst v0.
      rewrite H; auto_rewrite_cond.
      unfold ct_suffix.
      
      assert (ts = take (size ts - 3) ts ++ drop (size ts - 3) ts) as Heq; first by rewrite cat_take_drop.
      remember (drop (size ts-3) ts) as tail.
      assert (size tail = 3) as Hsizetail.
      { subst. rewrite size_drop. by lias. }
      repeat destruct tail as [|? tail] => //=. clear Hsizetail.
      apply/andP; split => //=.
      * unfold to_ct_list.
        rewrite size_map size_take sub_if.
        by lias.
      * rewrite -> Heq in *.
        unfold to_ct_list.
        rewrite size_map size_take sub_if size_cat size_take sub_if => //=.
        rewrite map_take.
        replace (size ts - 3 + 3 - 2 - 1) with (size ts - 3); last by lias.
        replace (size ts - 3 + 3 - 2) with (1 + (size ts - 3)); last by lias.
        rewrite - take_drop.
        rewrite map_cat.
        assert (size ts - 3 = size (to_ct_list (take (size ts - 3) ts))) as Hsize2.
        { unfold to_ct_list. by rewrite size_map size_take sub_if. }
        rewrite drop_size_cat => //.
        simpl.
        apply/andP; split => //.
        repeat rewrite length_is_size size_cat size_take sub_if in match_expr1.
        simpl in *.
        repeat (rewrite List.nth_error_app2 in match_expr1; last by (rewrite length_is_size size_take sub_if; lias)).
        repeat rewrite length_is_size size_take sub_if in match_expr1.
        replace (size ts - 3 + 3 - 3 - (size ts - 3))%coq_nat with 0 in match_expr1; last by lias.
        simpl in *.
        injection match_expr1 as <-.
        by rewrite eq_refl.
    + (* 3 *)
      replace ((length topt).+3-3) with (length topt); last by lias.
      destruct (List.nth_error [::c0, c1 & topt] (length topt)) eqn: Hl2; last by apply List.nth_error_None in Hl2; simpl in Hl2; lias.
      destruct (List.nth_error [::c, c0, c1 & topt] (length topt)) eqn: Hl3; last by apply List.nth_error_None in Hl3; simpl in Hl3; lias.
      assert (exists topts, select_return_top [::c, c0, c1 & topt] c2 c3 = CT_top_type topts) as Htopts.
      { unfold select_return_top.
        destruct c2, c3 => //=; try by eexists.
        
        replace (length topt) with (length [::c, c0, c1 & topt] - 3) in Hl3; last by lias.
        apply nth_error_nth' with (x0 := v1) in match_expr1.
        repeat rewrite length_is_size in match_expr1.
        assert (nth (CTA_some v1) (to_ct_list ts) (size ts - 3) = CTA_some v0) as Hts3ssr.
        { unfold to_ct_list. rewrite -> nth_map with (x1 := v1); last by lias. by rewrite match_expr1. }
        apply ssr_nth_error in Hts3ssr; last by unfold to_ct_list; rewrite size_map; lias.
        eapply ct_suffix_compat_index with (l2 := to_ct_list ts) in Hl3; eauto; last by rewrite length_is_size; unfold to_ct_list; rewrite size_map; apply Hts3ssr.

        replace (length topt) with (length [::c0, c1 & topt] - 2) in Hl2; last by lias.
        apply nth_error_nth' with (x0 := v1) in match_expr0.
        repeat rewrite length_is_size in match_expr0.
        assert (nth (CTA_some v1) (to_ct_list ts) (size ts - 2) = CTA_some v0) as Hts2ssr.
        { unfold to_ct_list. rewrite -> nth_map with (x1 := v1); last by lias. by rewrite match_expr0. }
        apply ssr_nth_error in Hts2ssr; last by unfold to_ct_list; rewrite size_map; lias.
        eapply ct_suffix_compat_index with (l2 := to_ct_list ts) in Hl2; eauto.
        2: { by apply ct_suffix_prefix with (l1 := [::c]). }
        2: { rewrite length_is_size; unfold to_ct_list; rewrite size_map; apply Hts2ssr. }
        simpl in *.
        move/eqP in Hl3; move/eqP in Hl2.
        subst v; subst v1.
        rewrite H eq_refl => /=.
        by eexists.
        }
      destruct Htopts as [topts Htopts].
      rewrite Htopts.
      unfold type_update, produce...
      replace (ct_suffix _ _) with true...
      * eapply select_return_top_suffix; eauto; last by rewrite match_expr0 match_expr1.
        simpl.
        by replace (_-_) with (length topt); last by lias.
      * rewrite ct_suffix_any_grow => //.
        by eapply ct_suffix_mutual_suffix; eauto.
Qed.

Lemma c_types_agree_suffix_single: forall l C ts ts2 e,
  c_types_agree (check_single C (CT_type ts) e) ts2 ->
  ct_suffix l (to_ct_list ts) ->
  c_types_agree (check_single C (CT_top_type l) e) ts2.
Proof with auto_rewrite_cond.
  move => l C ts ts2 e.
  move: l C ts ts2.
  induction e; move => topt C ts ts2 H Hsuffix; simpl in H => //=; auto_rewrite_cond; simplify_goal; (try destruct i); (try destruct c); (try by eapply type_update_agree_suffix; eauto) => //=...
  (* Ref_is_null *)
  - specialize (type_update_agree_suffix H Hsuffix) as Hsuffix'.
    destruct topt => //=.
    + unfold type_update in H...
      replace (_.+1 - 1) with (length topt); last by lias.
      destruct (List.nth_error (c :: topt) (length topt)) eqn:Hnth; last first.
      { apply List.nth_error_None in Hnth; simpl in Hnth; by lias. }
      { destruct c0...
        replace (length topt) with (length (c :: topt) - 1) in Hnth; last by lias.
        assert (ct_compat (CTA_some v0) (CTA_some v)) as Hcompat.
        { eapply ct_suffix_compat_index; try apply Hnth; eauto.
          apply nth_to_ct_list.
          uapply match_expr.
          do 2 f_equal.
          unfold to_ct_list.
          repeat rewrite length_is_size; by rewrite size_map.
        }
        by auto_rewrite_cond.
      }
  - by eapply type_update_select_agree; eauto.
  - simplify_goal.
    by eapply type_update_agree_suffix; eauto.
Qed.

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

Lemma c_types_agree_subtyping: forall C es ts1 ts1' ts2 ts2',
  c_types_agree (check C es (CT_type ts1)) ts2 ->
  ts1' <ts: ts1 ->
  ts2 <ts: ts2' ->
  c_types_agree (check C es (CT_type ts1')) ts2'.
(*
Proof.
  unfold c_types_agree.
  move => C es ts ts' ts2.
  destruct (check C es (CT_type ts)) eqn:Htc => //=; move => H.
  - 
Qed.
 *)
Admitted.

Lemma ct_list_compat_to_ct: forall tn tm,
  ct_list_compat (to_ct_list tn) (to_ct_list tm) ->
  tn = tm.
Proof with auto_rewrite_cond.
  induction tn; destruct tm; move => H => //=...
  f_equal. by apply IHtn.
Qed.

Lemma ct_list_compat_symmetry: forall l1 l2,
  ct_list_compat l1 l2 ->
  ct_list_compat l2 l1.
Proof with auto_rewrite_cond.
  induction l1; destruct l2; move => H => //=...
  apply ct_compat_symmetry in H.
  rewrite H => /=.
  by apply IHl1.
Qed.
  

Lemma ct_list_compat_cat1: forall l1 l2 l3,
  ct_list_compat (l2 ++ l3) l1 <->
  ct_list_compat l2 (take (size l2) l1) /\ ct_list_compat l3 (drop (size l2) l1).
Proof with auto_rewrite_cond.
  move => l1 l2.
  move : l1.
  induction l2 => //=; move => l1 l3.
  - rewrite take0 drop0.
    split => //=.
    by move => [_ ?].
  - destruct l1 => //=; first by split => //=; move => [? _].
    split; move => Hct...
    + by apply IHl2.
    + destruct Hct...
      by apply IHl2.
Qed.

Lemma ct_list_compat_cat2: forall l1 l2 l3,
  ct_list_compat l1 (l2 ++ l3) <->
  ct_list_compat (take (size l2) l1) l2 /\ ct_list_compat (drop (size l2) l1) l3.
Proof.
  move => l1 l2 l3.
  split; move => Hct.
  - apply ct_list_compat_symmetry in Hct.
    apply ct_list_compat_cat1 in Hct; destruct Hct.
    apply ct_list_compat_symmetry in H.
    apply ct_list_compat_symmetry in H0.
    by split.
  - destruct Hct.
    apply ct_list_compat_symmetry in H.
    apply ct_list_compat_symmetry in H0.
    apply ct_list_compat_symmetry.
    by apply ct_list_compat_cat1.
Qed.

Lemma consume_top_not_bot: forall cts tn,
  size cts >= size tn ->
  consume (CT_top_type cts) tn <> CT_error ->
  ct_list_compat (drop (size cts - size tn) cts) tn.
Proof with auto_rewrite_cond.
  move => cts tn Hsize H.
  unfold consume in H...
  - unfold ct_suffix in *...
  - unfold ct_suffix in *...
    assert (size tn = size cts) as Hsizeeq; first by lias.
    rewrite -> Hsizeeq, subnn, drop0 in *.
    by apply ct_list_compat_symmetry.
Qed.

Lemma consume_top_not_bot_short: forall cts tn,
  size cts <= size tn ->
  consume (CT_top_type cts) tn <> CT_error ->
  ct_list_compat cts (drop (size tn - size cts) tn).
Proof with auto_rewrite_cond. 
  move => cts tn Hsize H.
  unfold consume in H...
  - unfold ct_suffix in *...
    assert (size tn = size cts) as Hsizeeq; first by lias.
    by rewrite -> Hsizeeq, subnn, drop0 in *.
  - unfold ct_suffix in *...
    by apply ct_list_compat_symmetry.
Qed.

Lemma consume_type_not_bot: forall cts tn,
  consume (CT_type cts) tn <> CT_error ->
  ct_list_compat (drop (size cts - size tn) (to_ct_list cts)) tn.
Proof with auto_rewrite_cond.
  move => cts tn H.
  unfold consume in H...
  unfold ct_suffix in *...
Qed.

Lemma type_update_type_agree: forall tm tn' tm' cts,
  c_types_agree (type_update cts (to_ct_list tn') (CT_type tm')) tm ->
  exists lp, c_types_agree cts (lp ++ tn') /\ tm = lp ++ tm'.
Proof with auto_rewrite_cond.
  move => tm tn' tm' cts H.
  exists (take (size tm - size tm') tm).
  destruct cts as [ctst | cts | ] => //=...
  - unfold type_update in *; auto_rewrite_cond; unfold ct_suffix in * => //=...
    + rewrite -> size_take, sub_if in *.
      remember (size tm - size tm') as x.
      remember (size ctst - size tn') as y.
      apply ct_list_compat_cat2 in H0.
      rewrite size_take Heqy sub_if in H0.
      rewrite -Heqy in H0.
     destruct H0 as [Hct1 Hct2].
      unfold to_ct_list in Hct2.
      repeat rewrite - map_drop in Hct2.
      apply ct_list_compat_to_ct in Hct2.
      rewrite drop_drop in Hct2.
      replace (_+(_-_)) with x in Hct2; last by lias.
      split; last by rewrite - Hct2; rewrite cat_take_drop.
      apply/andP; split; first by lias.
      unfold to_ct_list.
      rewrite map_cat.
      rewrite drop_cat size_map size_take Heqx sub_if.
      rewrite - Heqx.
      destruct y. (* if it's non-zero, then we have x + size tn' - size csts < x *)
      * assert (size ctst = size tn') as Hsize; first by lias.
        rewrite -> Hsize in *; simpl in *.
        replace (_ < _) with false; last by lias.
        repeat rewrite take0 in Hct1.
        replace (x + size tn' - size tn' - x) with 0; last by lias.
        rewrite -> drop0 in *.
        by apply ct_list_compat_symmetry.
      * replace (_ < _) with true; last by lias.
        apply ct_list_compat_symmetry in H2.
        apply ct_list_compat_cat1.
        rewrite size_drop size_map size_take Heqx sub_if.
        rewrite - Heqx.
        replace (x - (x + size tn' - size ctst)) with (y.+1); last by lias.
        split => //.
        unfold to_ct_list in Hct1.
        rewrite take_drop in Hct1.
        replace (_ + (_ - (_ + _))) with x in Hct1; last by lias.
        rewrite map_take.
        replace (x + size tn' - size ctst) with (size tm - (y.+1 + size tm')) => //.
        by lias.
    + unfold to_ct_list in H0; rewrite - map_drop in H0.
      apply ct_list_compat_to_ct in H0.
      remember (size tm - size tm') as x.
      split; last by rewrite - H0; rewrite cat_take_drop.
      rewrite Heqx.
      rewrite size_take sub_if.
      apply/andP; split; first by lias.
      remember (size tn' - size ctst) as y.
      rewrite - Heqx.
      replace (x + size tn' - size ctst) with (x+y); last by lias.
      unfold to_ct_list in *.
      rewrite - map_drop in H2.
      rewrite - map_drop.
      rewrite drop_cat size_take Heqx sub_if.
      replace (_<_) with false; last by lias.
      by replace (size tm - _ + _ - _) with y; last by lias.
  - unfold type_update in *...
    unfold ct_suffix in *...
    unfold to_ct_list in H0; rewrite - map_drop in H0.
    apply ct_list_compat_to_ct in H0.
    remember (size cts - size tn') as x.
    rewrite size_take Heqx sub_if.
    split.
    + rewrite take_cat size_take sub_if.
      replace (_ < _) with false; last by lias.
      rewrite subnn take0 cats0.
      rewrite - Heqx -H0; by rewrite cat_take_drop.
    + rewrite take_cat size_take sub_if.
      replace (_ < _) with false; last by lias.
      by rewrite subnn take0 cats0.
Qed.

Lemma consume_type_agree: forall tm tn' cts,
  c_types_agree (consume cts (to_ct_list tn')) tm ->
  c_types_agree cts (tm ++ tn').
Proof.
  move => tm tn' cts Hct.
  rewrite - type_update_empty_prod in Hct.
  apply type_update_type_agree in Hct; destruct Hct as [tn [H1 H2]].
  by rewrite cats0 in H2; subst.
Qed.
        
Ltac simplify_type_update :=
  (try rewrite -> type_update_empty_cons in * );
  (try rewrite -> type_update_empty_prod in * );
  (try rewrite -> consume_empty in * );
  (try rewrite -> produce_empty in * );
  (try rewrite -> produce_empty_top in * ).

Lemma check_single_top_top: forall C cts e,
  check_single C (CT_top_type cts) e <> CT_error ->
  exists cts', check_single C (CT_top_type cts) e = CT_top_type cts'.
Proof with auto_rewrite_cond.
  move => C cts e H.
  remember (check_single C (CT_top_type cts) e) as cts'.
  destruct cts' => //; first by eexists.
  symmetry in Heqcts'.
  apply check_single_notop in Heqcts'.
  by destruct Heqcts'.
Qed.

Lemma ct_suffix_1_impl: forall tm,
  ct_suffix [::CTA_any] (to_ct_list tm) ->
  exists v tm', tm = tm' ++ [::v].
Proof.
  move => tm.
  case/lastP: tm => [|tm x] => //=.
  move => H.
  exists x, tm.
  by rewrite cats1.
Qed.

Ltac resolve_no_consume cts rt tm :=
  let Hct3 := fresh "Hct3" in
  assert (c_types_agree (type_update cts (to_ct_list [::]) (CT_type rt)) tm) as Hct3; first (by simplify_type_update; unfold produce => //=);
  apply type_update_type_agree in Hct3;
  destruct Hct3 as [tn' [Hct bet]]; subst;
  rewrite cats0 in Hct;
  exists tn'; split => //;
  apply bet_weakening_empty_1;
  try by econstructor; eauto.

Ltac fold_type_update H :=
  match type of H with
  | context [ consume ?cts ?ts ] =>
    let Hct3 := fresh "Hct3" in
    assert (consume cts ts = type_update cts ts (CT_type nil)) as Hct3; first (unfold type_update; rewrite produce_empty; reflexivity); rewrite Hct3 in H
  end.

(* Resolving update agree when the types being consumed are non-polymorphic, which is true for most of the instructions. *)
Ltac resolve_update_agree :=
  match goal with
  | Hct2: is_true (c_types_agree (type_update ?cts nil (CT_type _)) ?tm) |- _ =>
    let tn' := fresh "tn'" in
    let Hct := fresh "Hct" in
    let bet := fresh "bet" in
    replace nil with (to_ct_list nil) in Hct2 => //=;
    apply type_update_type_agree in Hct2 as [tn' [Hct bet]]; subst;
    rewrite -> cats0 in *;
    exists tn'; split => //;
    try apply bet_weakening; try apply bet_weakening_empty_1;
    (try by econstructor; eauto);
    (try by do 2 econstructor; eauto)
  | Hct2: is_true (c_types_agree (type_update ?cts [::CTA_some ?t1] (CT_type _)) ?tm) |- _ =>
    let tn' := fresh "tn'" in
    let Hct := fresh "Hct" in
    let bet := fresh "bet" in
    replace ([::CTA_some t1]) with (to_ct_list [:: t1]) in Hct2 => //=;
    apply type_update_type_agree in Hct2 as [tn' [Hct bet]]; subst;
    exists (tn' ++ [::t1]); split => //;
    try apply bet_weakening; try apply bet_weakening_empty_1;
    (try by econstructor; eauto);
    (try by do 2 econstructor; eauto)
  | Hct2: is_true (c_types_agree (type_update ?cts [::CTA_some ?t1; CTA_some ?t2] (CT_type _)) ?tm) |- _ =>
    let tn' := fresh "tn'" in
    let Hct := fresh "Hct" in
    let bet := fresh "bet" in
    replace ([::CTA_some t1; CTA_some t2]) with (to_ct_list [:: t1; t2]) in Hct2 => //=;
    apply type_update_type_agree in Hct2 as [tn' [Hct bet]]; subst;
    exists (tn' ++ [::t1; t2]); split => //;
    try apply bet_weakening; try apply bet_weakening_empty_1;
    (try by econstructor; eauto);
    (try by do 2 econstructor; eauto)
  | Hct2: is_true (c_types_agree (type_update ?cts [::CTA_some ?t1; CTA_some ?t2; CTA_some ?t3] (CT_type _)) ?tm) |- _ =>
    let tn' := fresh "tn'" in
    let Hct := fresh "Hct" in
    let bet := fresh "bet" in
    replace ([::CTA_some t1; CTA_some t2; CTA_some t3]) with (to_ct_list [:: t1; t2; t3]) in Hct2 => //=;
    apply type_update_type_agree in Hct2 as [tn' [Hct bet]]; subst;
    exists (tn' ++ [::t1; t2; t3]); split => //;
    try apply bet_weakening; try apply bet_weakening_empty_1;
    (try by econstructor; eauto);
    (try by do 2 econstructor; eauto)
  end.

Lemma type_update_ref_is_null_bet: forall C cts tm,
  c_types_agree (type_update_ref_is_null cts) tm ->
  exists tn, c_types_agree cts tn /\ be_typing C [::BI_ref_is_null] (Tf tn tm).
(*
Proof.
  move => C cts tm Hct.
  unfold type_update_ref_is_null in Hct.
  destruct cts as [ts | ts | ].
  - destruct ts => //.
    unfold ct_suffix in Hct; auto_rewrite_cond.
    exists ((take (size tm - 1) tm) ++ [::T_ref T_funcref]); split; first by apply ct_suffix_empty.
    rewrite <- (cat_take_drop (size tm - 1) tm) at 3.
    apply bet_weakening_empty_1.
    unfold to_ct_list in H0; rewrite - map_drop in H0.
    fold (to_ct_list (drop (size tm - 1) tm)) in H0.
    replace ([::CTA_some (T_num T_i32)]) with (to_ct_list [::T_num T_i32]) in H0 => //.
    apply ct_list_compat_to_ct in H0.
    rewrite H0.
    apply bet_ref_is_null.
    unfold ct_list_compat in H0.
    + move => Hct.
      apply ct_suffix_1_impl in Hct as [t [ts ->]].
      exists (ts ++ [::T_ref T_funcref]); split; first by apply ct_suffix_empty.
      apply bet_weakening.
      eapply bet_subtyping; first by constructor.
      resolve_subtyping.
*)
Admitted.


Lemma type_update_select_agree_bet: forall C cts ots tm,
  c_types_agree (type_update_select cts ots) tm ->
  exists tn, c_types_agree cts tn /\ be_typing C [::BI_select ots] (Tf tn tm).
Admitted.
(*
Proof with auto_rewrite_cond.
  move => C cts ots tm Hct.
  unfold type_update_select in Hct; auto_rewrite_cond; first by do 2 destruct l => //; resolve_update_agree.
  destruct cts as [ts | ts | ] => //.
  - move:Hct.
    rewrite length_is_size.
    case/lastP : ts => [|ts x1] => //=.
    + move => Hct.
      apply ct_suffix_1_impl in Hct.
      destruct Hct as [v [tm' ?]]; subst.
      exists (tm' ++ [::T_bot; T_bot; T_num T_i32]); split; first by apply ct_suffix_empty.
      apply bet_weakening.
      apply bet_select_None.
    + rewrite size_rcons.
      case/lastP : ts => [|ts x2] => //=.
      * move => Hct.
        unfold type_update, produce, consume in Hct.
        destruct x1; simpl in Hct.
        {
          apply ct_suffix_1_impl in Hct.
          destruct Hct as [v [tm' ?]]; subst.
          exists (tm' ++ [::v; v; T_i32]); split; first by apply ct_suffix_any_1; rewrite size_ct_list size_cat; lias.
          apply bet_weakening.
          by apply bet_select.
        }
        { destruct v => //=.
          simpl in Hct.
          apply ct_suffix_1_impl in Hct.
          destruct Hct as [v [tm' ?]]; subst.
          exists (tm' ++ [::v; v; T_i32]); split.
          - unfold ct_suffix...
            apply/andP; split; first by lias.
            unfold to_ct_list.
            rewrite map_cat drop_cat size_map.
            replace (_<_) with false; last by lias.
            by replace (_+_-_-_) with 2; last by lias.
          - apply bet_weakening.
            by apply bet_select.
        }
      * rewrite size_rcons.
        case/lastP : l => [|l x3] => //=.
        {
          move => H...
          unfold ct_suffix in *...
          clear H1.
          move : H H0.
          case/lastP : tm => [|tm x'] => //=.
          rewrite size_rcons.
          rewrite - cats1.
          move => _ Hct.
          replace (_-_) with (size tm) in Hct; last by lias.
          unfold to_ct_list in Hct.
          rewrite map_cat drop_cat size_map subnn drop0 in Hct.
          replace (_<_) with false in Hct; last by lias.
          simpl in Hct.
          exists (tm ++ [::x'; x'; T_i32]).
          rewrite size_ct_list size_cat.
          split.
          - apply/andP; split => /=; first by simpl; lias.
            unfold to_ct_list.
            rewrite map_cat drop_cat size_map.
            replace (_<_) with false; last by lias.
            replace (_+_-_-_) with 1; last by lias.
            simpl.
            destruct x2, x1 => //=...
          - apply bet_weakening.
            by apply bet_select.
        }
        {
          rewrite size_rcons.
          repeat rewrite -cats1.
          repeat rewrite -catA.
          intros...
          assert (List.nth_error (l ++ [::x3;x2;x1]) (1+size l) = Some c) as Hnth => //.
          clear match_expr.
          apply nth_error_nth' with (x0 := c) in Hnth.
          apply nth_error_nth' with (x0 := c) in match_expr0.
          replace (_-_) with (size l) in match_expr0; last by lias.
          rewrite nth_cat subnn in match_expr0.
          replace (_<_) with false in match_expr0; last by lias.
          simpl in match_expr0; subst.
          rewrite nth_cat in Hnth.
          replace (_<_) with false in Hnth; last by lias.
          replace (_-_) with 1 in Hnth; last by lias.
          simpl in Hnth; subst.
          unfold select_return_top, type_update in Hct...
          - repeat rewrite length_is_size size_cat in Hct.
            replace (size l + size _ - 3) with (size l) in Hct; last by simpl; lias.
            rewrite take_cat subnn take0 cats0 take_size in Hct.
            replace (_<_) with false in Hct; last by lias.
            unfold ct_suffix in if_expr...
            replace (size l + 3 - 3) with (size l) in H0; last by lias.
            rewrite drop_cat subnn drop0 in H0.
            replace (_<_) with false in H0; last by lias.
            auto_rewrite_cond.
            move : Hct.
            case/lastP: tm => [|tm x] => //=; move => Hct.
            + destruct c, c0; unfold c_types_agree, ct_suffix; auto_rewrite_cond; by destruct l => //=.
            + replace (_+_-_) with (size l) in Hct; last by lias.
              rewrite take_cat subnn take0 cats0 in Hct.
              replace (_<_) with false in Hct; last by lias.
              exists (tm ++ [::x; x; T_i32]).
              repeat rewrite cats1 in Hct.
              split; last by rewrite - cats1; apply bet_weakening; apply bet_select.
              destruct c , c0 => //=; auto_rewrite_cond; unfold to_ct_list in Hct; rewrite map_rcons in Hct; (try rewrite cats1 in Hct); apply ct_suffix_rcons in Hct; destruct Hct; unfold to_ct_list; rewrite map_cat; apply ct_suffix_append_compat => //=...
          - unfold ct_suffix in *; destruct l; auto_rewrite_cond; last by lias.
            replace (ct_compat c0 CTA_any) with true in if_expr; last by destruct c0.
            replace (ct_compat c CTA_any) with true in if_expr; last by destruct c.
            simpl in if_expr.
            destruct x1 => //=...
        }
  - move: Hct.
    case/lastP : l => [|l x1] => //=.
    case/lastP : l => [|l x2] => //=.
    case/lastP : l => [|l x3] => //=.
    move => Hct...
    repeat rewrite length_is_size in H0.
    repeat rewrite length_is_size in H.
    repeat rewrite size_rcons in H0.
    repeat rewrite size_rcons in H.
    destruct (List.nth_error _ ((size l).+3 - 2)) eqn:Hnth => //=; last by apply List.nth_error_None in Hnth; rewrite length_is_size in Hnth; repeat rewrite size_rcons in Hnth; lias.
    symmetry in H0.
    apply nth_error_nth' with (x0 := v) in Hnth.
    apply nth_error_nth' with (x0 := v) in H0.
    repeat rewrite nth_rcons in Hnth.
    repeat rewrite size_rcons in Hnth.
    replace ((size l).+3 - 2 < (size l).+2) with true in Hnth; last by lias.
    replace ((size l).+3 - 2 < (size l).+1) with false in Hnth; last by lias.
    replace (_ == _) with true in Hnth; last by lias.
    subst.
    repeat rewrite - cats1.
    repeat rewrite -catA. simpl.
    exists (l ++ [::x3; v; x1]).
    split => //.
    rewrite take_cat size_cat.
    replace (_ < size l) with false; last by simpl; lias.
    apply bet_weakening.
    replace (_ + _ - _ - _) with 1; last by simpl; lias.
    simpl.
    repeat rewrite nth_rcons in H0.
    repeat rewrite size_rcons in H0.
    replace ((size l).+3 - 3 < (size l).+2) with true in H0; last by lias.
    replace ((size l).+3 - 3 < (size l).+1) with true in H0; last by lias.
    replace ((size l).+3 - 3 < (size l)) with false in H0; last by lias.
    replace ((size l).+3 - 3 == (size l)) with true in H0; last by lias.
    subst.
    repeat rewrite - cats1 in if_expr0.
    repeat rewrite - catA in if_expr0.
    simpl in if_expr0.
    unfold ct_suffix in if_expr0...
    unfold to_ct_list in H1.
    rewrite map_cat in H1...
    rewrite drop_cat size_map in H1.
    replace (_<_) with false in H1; last by lias.
    replace (_+_-_-_) with 1 in H1; last by lias.
    simpl in H1...
    apply bet_select.
Qed.
*)
    
Lemma tc_to_bet_br: forall cts l,
  consume cts (to_ct_list l) <> CT_error ->
  exists tn, c_types_agree cts (tn ++ l).
Proof with auto_rewrite_cond.
  move => cts l Hconsume.
  destruct cts as [ctst | cts | ]=> //.
  - destruct (size ctst <= size l) eqn:Hsize.
    + apply consume_top_not_bot_short in Hconsume; last by rewrite size_ct_list.
      rewrite size_ct_list in Hconsume.
      exists [::] => //=.
      unfold ct_suffix...
      by apply ct_list_compat_symmetry.
    + apply consume_top_not_bot in Hconsume; last by rewrite size_ct_list; lias.
      rewrite size_ct_list in Hconsume.
      exists (populate_ct_aux (take (size ctst - size l) ctst))...
      unfold ct_suffix...
      unfold populate_ct_aux; rewrite size_map size_take sub_if.
      apply/andP; split; first by lias.
      replace (_ - _ + _ - _) with 0; last by lias.
      rewrite drop0.
      unfold to_ct_list.
      rewrite map_cat.
      rewrite - map_comp.
      remember (take _ ctst) as cl.
      rewrite - (cat_take_drop (size ctst - size l) ctst).
      subst.
      apply ct_list_compat_cat; last by apply ct_list_compat_symmetry.
      apply ct_list_compat_symmetry.
      remember (take _ _) as cl.
      clear.
      induction cl => //=; destruct a...
    + apply consume_type_not_bot in Hconsume.
      rewrite size_ct_list in Hconsume.
      exists (take (size cts - size l) cts)...
      unfold to_ct_list in Hconsume.
      rewrite - map_drop in Hconsume.
      apply ct_list_compat_to_ct in Hconsume...
      remember (size cts - size l) as x.
      rewrite - Hconsume.
      by rewrite cat_take_drop.
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
  check C bes cts = cts' ->
  c_types_agree cts' tm ->
  exists tn, c_types_agree cts tn /\ be_typing C bes (Tf tn tm)) /\
  ( forall C cts tm e cts',
  be_size_single e <= d ->
  check_single C cts e = cts' ->
  c_types_agree cts' tm ->
  exists tn, c_types_agree cts tn /\ be_typing C ([:: e]) (Tf tn tm)).
Proof with auto_rewrite_cond.
  induction (lt_wf d) as [d _ H] => //=.
  split.
  (* List *) 
  - move => c cts bes.
    move: c cts.
    induction bes as [| bes e] using last_ind => //=; move => C cts tm cts' Hs Hct1 Hbetc.
    + exists tm.
      split => //...
      by resolve_bet.
    + rewrite be_size_list_rcons in Hs.
      rewrite <- Hct1 in *.
      rewrite - cats1 in Hbetc.
      rewrite - cats1.
      rewrite check_rcons in Hbetc.
      remember (check C bes cts) as besct.
      remember (check_single C besct e) as ect.
      symmetry in Heqect.
      symmetry in Heqbesct.
      assert (be_size_single e < d)%coq_nat as Hmeasure; first by lias.
      assert (be_size_list bes < d)%coq_nat as Hmeasure2; first by lias.
      specialize H with (be_size_single e) as Hs1.
      apply Hs1 in Hmeasure.
      destruct Hmeasure as [_ Hmeasure].
      eapply Hmeasure in Heqect => //; last by apply Hbetc.
      destruct Heqect as [tn' [Hct Hbet]].
      eapply IHbes in Heqbesct => //; (try apply Hct); last by apply/leP; lias.
      destruct Heqbesct as [tn'' [Hcts Hbets]].
      exists tn''; split => //.
      eapply bet_composition; last by apply Hbet.
      by apply Hbets.
  (* Single *)
  - destruct e => //=; (try destruct i as [tn' tm']); auto_rewrite_cond; move => ? Hs Hct Hct2; simplify_type_update => //...
    (* Const_num *)
    + by resolve_no_consume cts [::T_num (typeof_num v)] tm.
    (* Unop_i *)
    + by destruct n; resolve_update_agree.
    (* Unop_f *)
    + by destruct n; resolve_update_agree.
    (* Unop_extend *)
    + by destruct n; resolve_update_agree.
    (* Binop_i *)
    + by destruct n; resolve_update_agree.
    (* Binop_f *)
    + by destruct n; resolve_update_agree.
    (* Testop *)
    + by resolve_update_agree.
    (* Relop_i *)
    + by destruct n; resolve_update_agree.
    (* Relop_f *)
    + by destruct n; resolve_update_agree.
    (* Cvtop *)
    + by resolve_update_agree.
    (* Const_vec *)
    + by resolve_no_consume cts [::T_vec (typeof_vec v)] tm.
    (* Const_vec *)
    + by resolve_no_consume cts [::T_ref r] tm.
    (* Ref_is_null *)
    + by apply type_update_ref_is_null_bet.
    (* Ref_func *)
    + resolve_no_consume cts [::T_ref T_funcref] tm.
      econstructor; eauto.
      by move/inP in if_expr0.
    (* Drop *)
    + destruct cts => //=; clear if_expr.
      * move: Hct2. case/lastP : l => [| l x] => //=; move => Hsuf.
        { exists (tm ++ [::T_num T_i32]); split; first by apply ct_suffix_empty.
          apply bet_weakening_empty_2.
          by apply bet_drop.
        }
        { exists (tm ++ [::populate_ct_aux_single x]).
          split; last by apply bet_weakening_empty_2; apply bet_drop.
          rewrite cats1.
          unfold to_ct_list.
          rewrite map_rcons.
          apply ct_suffix_rcons.
          split; first by destruct x => //=.
          rewrite ct_suffix_any_1 in Hsuf; last by rewrite size_rcons.
          rewrite - cats1 in Hsuf.
          simpl in Hsuf.
          rewrite size_cat take_cat in Hsuf.
          simpl in Hsuf.
          replace (size l + 1 - 1) with (size l) in Hsuf; last by lias.
          rewrite subnn take_size cats0 in Hsuf.
          by destruct (size l < size l) => //=.
        }
      * simpl in Hct2...
        exists l; split => //.
        move: if_expr. case/lastP: l => [|l x] => //=; move => _.
        rewrite - cats1.
        rewrite size_cat take_cat => /=.
        replace (size l + 1 - 1) with (size l); last by lias.
        rewrite take_size subnn cats0.
        replace (size l < size l) with false; last by clear H; lias.
        apply bet_weakening_empty_2.
        by apply bet_drop.
    (* Select *)
    + by apply type_update_select_agree_bet.
      (* Local_get *)
    + by resolve_update_agree.
      (* Local_set *)
    + by resolve_update_agree.
      (* Local_tee *)
    + by resolve_update_agree.
      (* Global_set *)
    + by resolve_update_agree.
      (* Global_get *)
    + by resolve_update_agree.
      (* Table_get *)
    + by resolve_update_agree.
      (* Table_set *)
    + by resolve_update_agree.
      (* Table_size *)
    + by resolve_no_consume cts [::T_num T_i32] tm.
      (* Table_grow *)
    + by resolve_update_agree.
      (* Table_fill *)
    + by resolve_update_agree.
      (* Table_copy *)
    + fold_type_update Hct2.
      by resolve_update_agree.
      (* Table_init *)
    + fold_type_update Hct2.
      by resolve_update_agree.
      (* Elem_drop *)
    + exists tm; split => //.
      by apply bet_weakening_empty_both; econstructor; eauto.
      (* Load *)
    + by resolve_update_agree.
      (* Store *)
    + fold_type_update Hct2.
      by resolve_update_agree.
      (* Memory_size *)
    + by resolve_no_consume cts [::T_num T_i32] tm.
      (* Memory_grow *)
    + by resolve_update_agree.
      (* Memory_fill *)
    + fold_type_update Hct2.
      by resolve_update_agree.
      (* Memory_copy *)
    + fold_type_update Hct2.
      by resolve_update_agree.
      (* Memory_init *)
    + fold_type_update Hct2.
      by resolve_update_agree.
      (* Data_drop *)
    + exists tm; split => //.
      by apply bet_weakening_empty_both; econstructor; eauto.
      (* Nop *)
    + exists tm; split => //.
      by apply bet_weakening_empty_both; econstructor; eauto.
      (* Unreachable *)
    + exists (populate_ct cts); split; by [apply populate_ct_agree | apply bet_unreachable].
      (* Block *)
    + destruct i.
      fold_remember_check.
      assert (be_size_list l < d)%coq_nat as Hmeasure; first by unfold be_size_list; lias.
      apply H in Hmeasure.
      destruct Hmeasure as [IH _].
      auto_rewrite_cond.
      eapply IH in if_expr0 => //; eauto.
      destruct if_expr0 as [tn'' [Hct1 Hbet]].
      simpl in Hct1.
      move/eqP in Hct1; subst.
      apply type_update_type_agree in Hct2.
      destruct Hct2 as [lp [Hct1 Heq]]; subst.
      exists (lp ++ tn''); split => //.
      by apply bet_weakening; econstructor; eauto.
      (* Loop *)
    + destruct i.
      fold_remember_check.
      assert (be_size_list l < d)%coq_nat as Hmeasure; first by unfold be_size_list; lias.
      apply H in Hmeasure.
      destruct Hmeasure as [IH _].
      auto_rewrite_cond.
      eapply IH in if_expr0 => //.
      destruct if_expr0 as [tn'' [Hct1 Hbet]].
      simpl in Hct1.
      move/eqP in Hct1; subst.
      apply type_update_type_agree in Hct2.
      destruct Hct2 as [lp [Hct1 Heq]]; subst.
      exists (lp ++ tn''); split => //.
      by apply bet_weakening; econstructor; eauto.
      (* If *)
    + destruct i.
      fold_remember_check.
      fold (be_size_list l) in Hs.
      fold (be_size_list l0) in Hs.
      assert (be_size_list l < d)%coq_nat as Hmeasure1; first by lias.
      assert (be_size_list l0 < d)%coq_nat as Hmeasure2; first by lias.
      apply H in Hmeasure1.
      destruct Hmeasure1 as [IH1 _].
      apply H in Hmeasure2.
      destruct Hmeasure2 as [IH2 _].
      auto_rewrite_cond.
      eapply IH1 in H0 => //.
      eapply IH2 in H1 => //.
      destruct H0 as [tn1'' [Hctif1 Hbet1]].
      destruct H1 as [tn2'' [Hctif2 Hbet2]].
      simpl in *.
      move/eqP in Hctif1; subst.
      move/eqP in Hctif2; subst.
      apply type_update_type_agree in Hct2.
      destruct Hct2 as [lp [Hct1 Heq]]; subst.
      exists (lp ++ tn2'' ++ [::T_num T_i32]); split => //.
      by apply bet_weakening; econstructor; eauto.
      (* Br *)
    + unfold type_update in Hct2.
      assert (consume cts (to_ct_list r) <> CT_error) as Hconsume; first by destruct (consume _ _).
      apply tc_to_bet_br in Hconsume.
      destruct Hconsume as [tn Hcts].
      exists (tn ++ r); split => //.
      by constructor.
      (* Br_if *)
    + apply type_update_type_agree in Hct2.
      destruct Hct2 as [tn' [Hctif Hbet]]. subst.
      exists (tn' ++ r ++ [::T_num T_i32]); split => //.
      apply bet_weakening.
      by constructor.
      (* Br_table *)
    + unfold type_update in Hct2.
      assert (consume cts (to_ct_list (l1 ++ [::T_num T_i32])) <> CT_error) as Hconsume; first by destruct (consume _ _).
      apply tc_to_bet_br in Hconsume as [tn Hcts].
      exists (tn ++ l1 ++ [::T_num T_i32]); split => //.
      econstructor.
      apply same_lab_same_lab_h in match_expr.
      by apply same_lab_h_all.
      (* Return *)
    + unfold type_update in Hct2.
      assert (consume cts (to_ct_list r) <> CT_error) as Hconsume; first by destruct (consume _ _).
      apply tc_to_bet_br in Hconsume as [tn Hcts].
      exists (tn ++ r); split => //.
      by apply bet_return.
    + destruct f0...
      apply type_update_type_agree in Hct2.
      destruct Hct2 as [tn' [Hct Hbet]]; subst.
      exists (tn' ++ r); split => //=.
      apply bet_weakening.
      by apply bet_call.
    + destruct f...
      apply type_update_type_agree in Hct2.
      destruct Hct2 as [tn' [Hct Hbet]]; subst.
      exists (tn' ++ r ++ [::T_num T_i32]); split => //=.
      apply bet_weakening.
      by eapply bet_call_indirect; eauto => //=.
Qed.
      
Lemma tc_to_bet_list: forall C cts bes tm cts',
  check C bes cts = cts' ->
  c_types_agree cts' tm ->
  exists tn, c_types_agree cts tn /\ be_typing C bes (Tf tn tm).
Proof.
  intros.
  specialize tc_to_bet_conj with (be_size_list bes).
  move => [H1 _].
  by eapply H1; eauto.
Qed.
 *)
End Host.
