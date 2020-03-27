(* soundness of the Wasm interpreter *)
(* (C) J. Pichon, M. Bodin, Rao Xiaojia - see LICENSE.txt *)

Require Import common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From StrongInduction Require Import StrongInduction Inductions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import operations opsem interpreter wasm_properties_aux.


Section Host.

(* TODO: The host should be defined as a mixin. *)
Variable mem_grow_impl : mem -> nat -> option mem.
Hypothesis mem_grow_impl_correct :
  forall m n m',
    mem_grow_impl m n = Some m' ->
    mem_grow m n = m'.

Variable host_apply_impl : store_record -> function_type -> datatypes.host -> list value -> option (store_record * list value).
Hypothesis host_apply_impl_correct :
  forall s tf h vs m',
    host_apply_impl s tf h vs = Some m' ->
    exists hs, host_apply s tf h vs hs = Some m'.

Let run_one_step := run_one_step mem_grow_impl host_apply_impl.
Let run_step := run_step mem_grow_impl host_apply_impl.

Hint Constructors reduce_simple : core.
Hint Constructors reduce : core.

(** The lemmas [r_eliml] and [r_elimr] are the fundamental framing lemmas.
  They enable to focus on parts of the stack, ignoring the context. **)

Lemma r_eliml: forall s vs es s' vs' es' lconst i,
    const_list lconst ->
    reduce s vs es i s' vs' es' ->
    reduce s vs (lconst ++ es) i s' vs' (lconst ++ es').
Proof.
  move => s vs es s' vs' es' lconst i HConst H.
  apply: r_label; try apply/lfilledP.
  - by apply: H.
  - replace (lconst++es) with (lconst++es++[::]); first by apply: LfilledBase.
    f_equal. by apply: cats0.
  - replace (lconst++es') with (lconst++es'++[::]); first by apply: LfilledBase.
    f_equal. by apply: cats0.
Qed.

Lemma r_elimr: forall s vs es s' vs' es' i les,
    reduce s vs es i s' vs' es' ->
    reduce s vs (es ++ les) i s' vs' (es' ++ les).
Proof.
  move => s vs es s' vs' es' i les H.
  apply: r_label; try apply/lfilledP.
  - apply: H.
  - replace (es++les) with ([::]++es++les) => //. by apply: LfilledBase.
  - replace (es'++les) with ([::]++es'++les) => //. by apply: LfilledBase.
Qed.

(** [r_eliml_empty] and [r_elimr_empty] are useful instantiations on empty stacks. **)

Lemma r_eliml_empty: forall s vs es s' vs' lconst i,
    const_list lconst ->
    reduce s vs es i s' vs' [::] ->
    reduce s vs (lconst ++ es) i s' vs' lconst.
Proof.
  move => s vs es s' vs' lconst i HConst H.
  assert (reduce s vs (lconst++es) i s' vs' (lconst++[::])); first by apply: r_eliml.
  by rewrite cats0 in H0.
Qed.

Lemma r_elimr_empty: forall s vs es s' vs' i les,
    reduce s vs es i s' vs' [::] ->
    reduce s vs (es ++ les) i s' vs' les.
Proof.
  move => s vs es s' vs' i les H.
  assert (reduce s vs (es++les) i s' vs' ([::] ++les)); first by apply: r_elimr.
  by rewrite cat0s in H0.
Qed.

Lemma run_step_fuel_not_zero : forall tt,
  run_step_fuel tt <> 0.
Proof.
  move=> [[st vs] es]. rewrite/run_step_fuel. by lias.
Qed.


Lemma const_list_cons : forall a l,
  const_list (a :: l) = is_const a && const_list l.
Proof. by []. Qed.

(** This lemma is useful when an instruction consumes some expressions on the stack:
  we usually have to split a list of expressions by the expressions effectively
  consumed by the instructions and the one left. **)
Lemma v_to_e_take_drop_split: forall l n,
  v_to_e_list l = v_to_e_list (take n l) ++ v_to_e_list (drop n l).
Proof.
  move => l n. rewrite v_to_e_cat. by rewrite cat_take_drop.
Qed.

Lemma v_to_e_take: forall l n,
  v_to_e_list (take n l) = take n (v_to_e_list l).
Proof.
  move => + n. induction n => //.
  - move => l. by repeat rewrite take0.
  - move => l. destruct l => //. simpl. f_equal. by apply IHn.
Qed.

Lemma v_to_e_drop: forall l n,
  v_to_e_list (drop n l) = drop n (v_to_e_list l).
Proof.
  move => + n. induction n => //.
  - move => l. by repeat rewrite drop0.
  - move => l. destruct l => //. simpl. f_equal. by apply IHn.
Qed.

Lemma v_to_e_rev: forall l,
  v_to_e_list (rev l) = rev (v_to_e_list l).
Proof.
  elim => //=.
  move => a l IH. rewrite rev_cons. rewrite -cats1. rewrite -v_to_e_cat.
  rewrite rev_cons. rewrite -cats1. by rewrite -IH.
Qed.

Lemma v_to_e_list0 : v_to_e_list [::] = [::].
Proof. reflexivity. Qed.

Lemma v_to_e_list1 : forall v, v_to_e_list [:: v] = [:: Basic (EConst v)].
Proof. reflexivity. Qed.

Local Lemma ves_projection: forall vs e es vs' e' es',
  const_list vs ->
  const_list vs' ->
  ~ is_const e ->
  ~ is_const e' ->
  vs ++ e :: es = vs' ++ e' :: es' ->
  e = e'.
Proof.
  move => vs. induction vs => //=.
  - move => e es vs' e' es' _ HConstList HNConst HNConst'.
    destruct vs' => //=.
    + move => H. by inversion H.
    + simpl in HConstList. move => H. inversion H. subst.
      move/andP in HConstList. destruct HConstList as [Ha _].
      rewrite Ha in HNConst. exfalso. by apply HNConst.
  - move => e es vs' e' es' HConstList HConstList' HNConst HNConst'.
    destruct vs' => //=.
    + move => H. inversion H. subst.
      move/andP in HConstList. destruct HConstList as [He' _].
      exfalso. by apply HNConst'.
    + simpl in HConstList'. move => H. inversion H. subst.
      move/andP in HConstList. move/andP in HConstList'.
      destruct HConstList as [Ha Hvs]. destruct HConstList' as [Ha' Hvs'].
      eapply IHvs => //=.
      * by apply Hvs'.
      * by apply H2.
Qed.

Lemma lfilled0: forall es,
  lfilledInd 0 (LBase [::] [::]) es es.
Proof.
  move => es.
  assert (lfilledInd 0 (LBase [::] [::]) es ([::]++es++[::])) as H; first by apply LfilledBase.
  simpl in H. by rewrite cats0 in H.
Qed.

Lemma lfilled0_frame_l: forall vs es es' LI vs',
  lfilledInd 0 (LBase vs es') es LI ->
  const_list vs' ->
  lfilledInd 0 (LBase (vs' ++ vs) es') es (vs' ++ LI).
Proof.
  move => vs es es' LI vs' HLF HConst. inversion HLF; subst; clear HLF.
  rewrite catA.
  apply LfilledBase. by rewrite const_list_concat.
Qed.

Lemma lfilled0_frame_l_empty: forall es es' LI vs',
  lfilledInd 0 (LBase [::] es') es LI ->
  const_list vs' ->
  lfilledInd 0 (LBase vs' es') es (vs' ++ LI).
Proof.
  move => es es' LI vs' HLF HConst. inversion HLF; subst; clear HLF.
  rewrite catA.
  rewrite cats0.
  by apply LfilledBase.
Qed.

Lemma lfilled0_frame_r: forall vs es es' LI es'',
  lfilledInd 0 (LBase vs es') es LI ->
  lfilledInd 0 (LBase vs (es' ++ es'')) es (LI ++ es'').
Proof.
  move => vs es es' LI es'' HLF. inversion HLF; subst; clear HLF.
  repeat rewrite -catA.
  by apply LfilledBase.
Qed.
      
Lemma lfilled0_frame_r_empty: forall vs es LI es'',
  lfilledInd 0 (LBase vs [::]) es LI ->
  lfilledInd 0 (LBase vs es'') es (LI ++ es'').
Proof.
  move => vs es LI es'' HLF. inversion HLF; subst; clear HLF.
  repeat rewrite -catA.
  by apply LfilledBase.
Qed.

Lemma lfilled0_take_drop: forall vs es n es',
  const_list vs ->
  n <= size vs ->
  lfilledInd 0 (LBase (take n vs) es') (drop n vs ++ es) (vs ++ es ++ es').
Proof.
  move => vs es n es' HConst HSize.
  replace (vs++es++es') with (take n vs ++ (drop n vs ++ es) ++ es').
  apply LfilledBase. by apply const_list_take.
  { repeat rewrite catA. by rewrite cat_take_drop. }
Qed.

(** The following tactics are meant to help the proof of [run_step_soundness] below. **)

(** Simplify an hypothesis, possibly rewriting it everywhere. **)
Ltac simplify_hypothesis Hb :=
  repeat rewrite length_is_size in Hb;
  repeat match type of Hb with
  | is_true (es_is_trap _) => move/es_is_trapP: Hb => Hb
  | is_true (const_list (_ :: _)) => rewrite const_list_cons in Hb
  | host_apply_impl _ _ _ _ = Some _ =>
    apply host_apply_impl_correct in Hb;
    let hs := fresh "hs" in
    destruct Hb as [hs Hb]
  | ?b = true => fold (is_true b) in Hb
  | context C [size (rev _)] => rewrite size_rev in Hb
  | context C [take _ (rev _)] => rewrite take_rev in Hb
  | context C [rev (rev _)] => rewrite revK in Hb
  | context C [true && _] => rewrite Bool.andb_true_l in Hb
  | context C [_ && true] => rewrite Bool.andb_true_r in Hb
  | context C [false || _] => rewrite Bool.orb_false_l in Hb
  | context C [_ || false] => rewrite Bool.orb_false_r in Hb
  | is_true true => clear Hb
  | is_true false => exfalso; apply: notF; apply: Hb
  | is_true (_ == _) => move/eqP in Hb
  | ?x = ?x => clear Hb
  | _ = _ => rewrite Hb in *
  end.

(** Apply [simplify_hypothesis] to all hypotheses. **)
Ltac simplify_goal :=
  repeat match goal with H: _ |- _ => progress simplify_hypothesis H end.

(** A common pattern in the proof: using an hypothesis on the form [rev l = l'] to rewrite [l]. **)
Ltac subst_rev_const_list :=
 repeat lazymatch goal with
 | HRevConst: rev ?lconst = ?h :: ?t |- _ =>
   apply rev_move in HRevConst; rewrite HRevConst; rewrite -cat1s; rewrite rev_cat;
   rewrite -v_to_e_cat; rewrite -catA
 end.

(** Simplify the lists in the goal. **)
Ltac simplify_lists :=
  (** Common rewriting rules. **)
  repeat first [
      rewrite drop_rev
    | rewrite take_rev
    | rewrite revK
    | rewrite length_is_size
    | rewrite size_take
    | rewrite size_drop
    | rewrite size_rev
    | rewrite v_to_e_size
    | rewrite rev_cat
    | rewrite rev_cons -cats1
    | rewrite -v_to_e_cat
    | rewrite -v_to_e_rev
    | rewrite -v_to_e_take
    | rewrite -v_to_e_drop];
  (** Putting all the lists into a normal form, as concatenations of as many things.
    Because [cat1s] conflicts with [cats0], replacing any occurence of [[X]] to
    [[X] ++ [::]], it has to be done separately.
    Rewrite with the associated [math goal with] is avoid to deal with existential
    vairables. **)
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite -(cat1s x l) end
  end;
  repeat lazymatch goal with
  | |- context C [[::] ++ _] => rewrite cat0s
  | |- context C [_ ++ [::]] => rewrite cats0
  | |- context C [rcons _ _] => rewrite -cats1
  | |- context C [(_ ++ _) ++ _] => rewrite -catA
  | |- context C [rev [::]] => rewrite rev0
  | |- context C [v_to_e_list [::]] => rewrite v_to_e_list0
  | |- context C [v_to_e_list [:: _]] => rewrite v_to_e_list1
  end;
  try subst_rev_const_list.

(** Explode a tuple into all its components. **)
Ltac explode_value v :=
  lazymatch type of v with
  | (_ * _)%type =>
    let v1 := fresh "v1" in
    let v2 := fresh "v2" in
    destruct v as [v1 v2];
    explode_value v1;
    explode_value v2
  | _ => idtac
  end.

(** Try to find which variable to pattern match on, destruct it,
  then simplify the destructing equality. **)
Ltac explode_and_simplify :=
  repeat lazymatch goal with
  | |- ?T = _ -> _ =>
    lazymatch T with
    | context C [split_n ?l ?n] => rewrite (split_n_is_take_drop l n)
    | context C [vs_to_es ?l] => rewrite/vs_to_es
    | context C [match ?b with true => ?v1 | false => ?v2 end] =>
      let Hb := fresh "if_expr" in
      destruct b eqn:Hb;
      simplify_hypothesis Hb;
      try by [|apply: Hb]
    | context C [match rev ?lconst with
                 | _ :: _ => _
                 | _ => _
                 end] =>
      let HRevConst := fresh "HRevConst" in
      destruct (rev lconst) eqn:HRevConst;
      simplify_hypothesis HRevConst;
      try by [|apply: HRevConst]
    | context C [match ?v with
                 | ConstInt32 _ => _
                 | _ => _
                 end] =>
      let Hb := fresh "Ev" in
      destruct v eqn:Hb;
      simplify_hypothesis Hb;
      try by []
    | context C [match ?v with
                 | Some _ => _
                 | _ => _
                 end] =>
      let Hv := fresh "option_expr" in
      let v' := fresh "v" in
      destruct v as [v'|] eqn:Hv; [ explode_value v' |];
      simplify_hypothesis Hv;
      try by [|apply: Hv]
    | context C [match ?v with
                 | T_i32 => _
                 | T_i64 => _
                 | T_f32 => _
                 | T_f64 => _
                 end] =>
      let Hv := fresh "Ev" in
      destruct v eqn:Hv;
      simplify_hypothesis Hv;
      try by []
    | context C [match ?v with
                 | Convert => _
                 | Reinterpret => _
                 end] =>
      let Hv := fresh "Ecvtop" in
      destruct v eqn:Hv;
      simplify_hypothesis Hv;
      try by []
    | context C [match ?v with
                 | Tf _ _ => _
                 end] =>
      let vs1 := fresh "vs" in
      let vs2 := fresh "vs" in
      let Hv := fresh "Eft" in
      destruct v as [vs1 vs2] eqn:Hv;
      simplify_hypothesis Hv;
      try by []
    | context C [expect ?X ?f ?err] =>
       let HExpect := fresh "HExpect" in
       destruct X eqn:HExpect;
       simplify_hypothesis HExpect;
       simpl;
       try by [|apply: HExpect]
    | context C [match ?l with
                 | _ :: _ => _
                 | _ => _
                 end] =>
      destruct l;
      try by []
    end
  end;
  simplify_lists.

(** If the goal is on the form [c1 = c2 -> property] where [c1] and [c2] are two configurations,
  then invert it. **)
Ltac pattern_match :=
  let go _ :=
    lazymatch goal with
    | |- (_, _, _) = (_, _, _) -> _ =>
      let H := fresh in
      move=> H; inversion H; subst; clear H
    end in
  go tt || (simpl; go tt).

(** Eliminate the stack frame, by applying [r_elimr] and [r_eliml] according to some heuristics. **)
Ltac stack_frame :=
  repeat lazymatch goal with
  | |- reduce _ _ (_ :: ?l) _ _ _ _ =>
    rewrite -cat1s
  | |- reduce _ _ (?l1 ++ ?l2 :: ?l3) _ _ _ ((?l5 ++ ?l4) ++ ?l3) =>
    rewrite -cat1s; rewrite catA;
    apply: r_elimr; try apply: r_eliml; try apply: v_to_e_is_const_list
  | |- reduce _ _ (?l1 ++ ?l2 :: ?l3) _ _ _ (?l5 ++ ?l3) =>
    rewrite -cat1s; rewrite catA;
    apply: r_elimr; try apply: r_eliml_empty; try apply: v_to_e_is_const_list
  | |- reduce _ _ (v_to_e_list ?l1 ++ _) _ _ _ (v_to_e_list (take ?n ?l1) ++ _) =>
    rewrite (v_to_e_take_drop_split l1 n); rewrite -catA;
    apply: r_eliml; try apply: v_to_e_is_const_list
  end.

(** Try to solve a goal of the form [const_list _]. **)
Ltac solve_const_list :=
  repeat rewrite const_list_concat;
  repeat rewrite const_list_cons;
  by [| apply: v_to_e_is_const_list ].

(** Try to solve a goal of the form [l1 = l2] where [l1] and [l2] are two lists. **)
Ltac show_list_equality :=
  simplify_lists; simplify_goal;
  by [| repeat f_equal
      | repeat rewrite catA; repeat f_equal
      | repeat rewrite -catA; repeat f_equal
      | eauto
      | erewrite cats0; eauto
      | erewrite cat0s; eauto
      | repeat (repeat rewrite catA; f_equal; repeat rewrite -catA; f_equal)
      | repeat (repeat rewrite -catA; f_equal; repeat rewrite catA; f_equal) ].

(** Given a left and a right frame, rewrite the goal to move these frames out. **)
Ltac frame_out l r :=
  lazymatch goal with
  | |- reduce _ _ ?st1 _ _ _ ?st2 =>
    let sta := fresh "st1" in
    evar (sta : seq administrative_instruction);
    let stb := fresh "st2" in
    evar (stb : seq administrative_instruction);
    let Est1 := fresh "E_before" in
    assert (Est1: st1 = (l ++ sta) ++ r); [
        rewrite/sta {sta stb}; try show_list_equality
      | let Est2 := fresh "E_after" in
        assert (Est2: st2 = (l ++ stb) ++ r); [
            rewrite/stb {Est1 sta stb}; try show_list_equality
          | rewrite Est1 Est2;
            apply r_elimr with (les := r);
            apply r_eliml with (lconst := l); first try solve_const_list;
            rewrite /sta /stb {Est1 Est2 sta stb};
            try by repeat constructor ] ]
  end.

(** Same as [frame_out], by the frames are inferred (syntactically). **)
Ltac auto_frame :=
  simplify_lists;
  let empty := constr:([::] : list administrative_instruction) in
  let left _ :=
    repeat rewrite -catA;
    repeat lazymatch goal with
    | |- reduce _ _ (?l ++ _) _ _ _ (?l ++ _) =>
      frame_out l empty
    | |- reduce _ _ (?l ++ _) _ _ _ ?l =>
      frame_out l empty
    | |- reduce _ _ ?l _ _ _ (?l ++ _) =>
      frame_out l empty
    end in
  let right _ :=
    repeat rewrite catA;
    repeat lazymatch goal with
    | |- reduce _ _ (_ ++ ?r) _ _ _ (_ ++ ?r) =>
      frame_out empty r
    | |- reduce _ _ (_ ++ ?r) _ _ _ ?r =>
      frame_out empty r
    | |- reduce _ _ ?r _ _ _ (_ ++ ?r) =>
      frame_out empty r
    end;
    (** Renormalising back. **)
    repeat (rewrite -catA) in
  repeat first [ progress left tt | progress right tt ].

(** Same as [frame_out], by the frames are existential variables. **)
Ltac eframe :=
  let l := fresh "l" in
  evar (l : seq administrative_instruction);
  let r := fresh "r" in
  evar (r : seq administrative_instruction);
  frame_out l r.

Local Lemma run_step_fuel_increase_aux : forall d i es s vs s' vs' r' fuel fuel',
  fuel <= fuel' ->
  TProp.Forall (fun e => forall d i tt s vs r fuel fuel',
     fuel <= fuel' ->
     run_one_step fuel d i tt e = (s, vs, r) ->
     r = RS_crash C_exhaustion \/ run_one_step fuel' d i tt e = (s, vs, r)) es ->
  run_step_with_fuel mem_grow_impl host_apply_impl fuel d i (s, vs, es) = (s', vs', r') ->
  r' = RS_crash C_exhaustion
  \/ run_step_with_fuel mem_grow_impl host_apply_impl fuel' d i (s, vs, es) = (s', vs', r').
Proof.
  move=> d i es s vs s' vs' r' fuel fuel' I F. destruct fuel as [|fuel].
  - pattern_match. by left.
  - destruct fuel' as [|fuel'] => /=.
    + inversion I.
    + destruct (split_vals_e es) as [lconst les] eqn:HSplitVals.
      apply split_vals_e_v_to_e_duality in HSplitVals.
      destruct les as [|e les'] eqn:Hles.
      * pattern_match. by right.
      * explode_and_simplify; try by pattern_match; right.
        apply TProp.Forall_forall with (e := e) in F.
        -- destruct interpreter.run_one_step as [[s'' vs''] r''] eqn:E.
           eapply F in E; [|by apply I|..]. destruct E as [E|E].
           ++ subst. pattern_match. by left.
           ++ unfold run_one_step in E. rewrite E. by right.
        -- rewrite HSplitVals. apply Coqlib.in_app. right. by left.
Qed.

Lemma run_one_step_fuel_increase : forall d i tt e s vs r fuel fuel',
  fuel <= fuel' ->
  run_one_step fuel d i tt e = (s, vs, r) ->
  r = RS_crash C_exhaustion \/ run_one_step fuel' d i tt e = (s, vs, r).
Proof.
  move=> + + + e. induction e using administrative_instruction_ind';
    move=> d j [[tt_s tt_vs] tt_es] s' vs' r;
    (case; first by move=> ? ?; pattern_match; left) => fuel;
    (case; first by []) => fuel' I /=.
  - by destruct b; explode_and_simplify; try pattern_match; right.
  - pattern_match. by right.
  - by destruct f; explode_and_simplify; pattern_match; right.
  - explode_and_simplify; try by pattern_match; right.
    destruct run_step_with_fuel as [[s'' vs''] r''] eqn: E.
    eapply run_step_fuel_increase_aux in E; [|by apply I|..] => //. destruct E as [E|E].
    + subst. pattern_match. by left.
    + rewrite E. by right.
  - explode_and_simplify; try by pattern_match; right.
    destruct run_step_with_fuel as [[s'' vs''] r''] eqn: E.
    eapply run_step_fuel_increase_aux in E; [|by apply I|..] => //. destruct E as [E|E].
    + subst. pattern_match. by left.
    + rewrite E. by right.
Qed.

Lemma run_step_fuel_increase : forall d i tt s vs r fuel fuel',
  fuel <= fuel' ->
  run_step_with_fuel mem_grow_impl host_apply_impl fuel d i tt = (s, vs, r) ->
  r = RS_crash C_exhaustion
  \/ run_step_with_fuel mem_grow_impl host_apply_impl fuel' d i tt = (s, vs, r).
Proof.
  move=> d i [[s vs] es] s' vs' r' fuel fuel' I. apply: run_step_fuel_increase_aux => //.
  apply: TProp.forall_Forall => e Ie.
  move=> > I' E'. apply: run_one_step_fuel_increase.
  + by apply: I'.
  + by apply: E'.
Qed.

Local Lemma max_fold_left_run_step_fuel : forall es,
  List.fold_left Init.Nat.max (List.map run_one_step_fuel es) 0
  <= TProp.max
       ((fix rect_list (es : seq administrative_instruction) : TProp.Forall (fun=> nat) es :=
          match es as es' return (TProp.Forall (fun=> nat) es') with
          | [::] => TProp.Forall_nil (fun=> nat)
          | e :: l => TProp.Forall_cons (run_one_step_fuel e) (rect_list l)
          end) es).
Proof.
  move=> es. match goal with |- is_true (_ <= TProp.max ?F) => set Fm := F end.
  rewrite -(Max.max_0_l (TProp.max Fm)). move: 0. induction es => n /=.
  - by lias.
  - rewrite Max.max_assoc. by apply: IHes.
Qed.

Local Lemma run_step_fuel_enough_aux : forall d i s vs es s' vs' r',
  TProp.Forall (fun e => forall d i tt s vs r,
    run_one_step (run_one_step_fuel e) d i tt e = (s, vs, r) ->
    r <> RS_crash C_exhaustion) es ->
  run_step d i (s, vs, es) = (s', vs', r') ->
  r' <> RS_crash C_exhaustion.
Proof.
  move=> d i s vs es s' vs' r' F. rewrite/run_step/interpreter.run_step.
  destruct run_step_fuel eqn: E => //=.
  destruct (split_vals_e es) as [lconst les] eqn:HSplitVals.
  apply split_vals_e_v_to_e_duality in HSplitVals.
  destruct les as [|e les'] eqn:Hles.
  - by pattern_match.
  - explode_and_simplify; try by pattern_match.
    apply TProp.Forall_forall with (e := e) in F.
    + destruct (run_one_step (run_one_step_fuel e) d i (s, vs, rev lconst) e)
        as [[s'' vs''] r''] eqn:E1.
      move: (E1) => E2. apply F in E2.
      apply run_one_step_fuel_increase with (fuel' := n) in E1.
      * destruct E1 as [E1|E1] => //.
        rewrite/run_one_step in E1. rewrite E1.
        by destruct r'' as [|[|]| |] => //; pattern_match.
      * move: E. rewrite /run_step_fuel HSplitVals.
        rewrite List.map_app List.fold_left_app => /=.
        move=> E. have: (exists v, n = Nat.max (run_one_step_fuel e) v).
        {
          move: E. clear. move: (List.fold_left _ _ 0). induction les' => /=.
          - move=> v E. exists v. by lias.
          - move=> v E. apply: IHles'.
            rewrite Max.max_comm in E. rewrite Max.max_assoc in E. by apply: E.
        }
        move=> [v E']. by lias.
    + rewrite HSplitVals. apply Coqlib.in_app. right. by left.
Qed.

(** [run_one_step_fuel] is indeed enough fuel to run [run_one_step]. **)
Lemma run_one_step_fuel_enough : forall d i tt e s vs r,
  run_one_step (run_one_step_fuel e) d i tt e = (s, vs, r) ->
  r <> RS_crash C_exhaustion.
Proof.
  move=> + + + e. induction e using administrative_instruction_ind';
    move=> d j [[tt_s tt_vs] tt_es] s' vs' r /=.
  - by destruct b; explode_and_simplify; pattern_match.
  - by pattern_match.
  - by destruct f; explode_and_simplify; pattern_match.
  - match goal with |- context [ run_step_with_fuel _ _ ?fuel _ _ _ ] => set f := fuel end.
    assert (run_step_fuel (tt_s, tt_vs, es2) <= f).
    {
      apply/leP. rewrite/f /=.
      move: (max_fold_left_run_step_fuel es2). clear. by lias.
    }
    explode_and_simplify; try by pattern_match.
    destruct (run_step d j (tt_s, tt_vs, es2)) as [[s'' vs''] r''] eqn:E1.
    move: (E1) => E2. unfold run_step, interpreter.run_step in E2.
    apply run_step_fuel_increase with (fuel' := f) in E2.
    move: (E1) => D. apply run_step_fuel_enough_aux in D => //.
    + destruct E2 as [E2|E2] => //. rewrite E2.
      by destruct r'' as [|[|]| |] => //; explode_and_simplify; pattern_match.
    + by [].
  - (* LATER: This proof might be factorised somehow. *)
    match goal with |- context [ run_step_with_fuel _ _ ?fuel _ _ _ ] => set f := fuel end.
    assert (run_step_fuel (tt_s, vs, es) <= f).
    {
      apply/leP. rewrite/f /=.
      move: (max_fold_left_run_step_fuel es). clear. by lias.
    }
    explode_and_simplify; try by pattern_match.
    destruct (run_step d i (tt_s, vs, es)) as [[s'' vs''] r''] eqn:E1.
    move: (E1) => D. apply run_step_fuel_enough_aux in D => //.
    move: (E1) => E2. apply run_step_fuel_increase with (fuel' := f) in E2.
    + destruct E2 as [E2|E2] => //. rewrite E2.
      by destruct r'' as [|[|]| |] => //; explode_and_simplify; pattern_match.
    + by [].
Qed.

(** [run_step_fuel] is indeed enough fuel to run [run_step]. **)
Lemma run_step_fuel_enough : forall d i tt s vs r,
  run_step d i tt = (s, vs, r) ->
  r <> RS_crash C_exhaustion.
Proof.
  move=> d i [[s vs] r] s' vs' r'. apply: run_step_fuel_enough_aux.
  apply: TProp.forall_Forall => e Ie.
  move=> >. by apply: run_one_step_fuel_enough.
Qed.

(** If the result of the interpreter is a [RS_break], then we were executing
  either a [Br] or a [Label] instruction, which itself returned a [RS_break]. **)
Local Lemma rs_break_trace_bool: forall fuel d i s vs es s' vs' n es',
  run_step_with_fuel mem_grow_impl host_apply_impl fuel.+2 d i (s, vs, es)
  = (s', vs', RS_break n es') -> 
  let: (ves, es'') := split_vals_e es in
  exists e es2 ln les es3, (es'' == e :: es2) &&
   ((e == Basic (Br n)) && ((s', vs', es') == (s, vs, rev ves)) ||
    (e == Label ln les es3) &&
     ((run_step_with_fuel mem_grow_impl host_apply_impl fuel d i (s, vs, es3))
      == (s', vs', RS_break n.+1 es'))).
Proof.
  move => fuel d i s vs es s' vs' n es' /= H.
  destruct (split_vals_e es) as [vs2 es2] eqn:HSplit.
  apply split_vals_e_v_to_e_duality in HSplit.
  destruct es2 as [|e es2']=> //.
  destruct e as [b| | |n0 l l0|n0 l l0]=> //; unfold e_is_trap in H.
  - destruct b => //; move:H; try explode_and_simplify.
    + (* Basic (Br i0) *)
      pattern_match.
      exists (Basic (Br n)). exists es2'.
      (* unused ones *) exists 0. exists [::]. exists [::].
      move=> /=. apply/andP. split => //=. apply/orP. left. apply/andP. by split => //=.
  - move:H. by explode_and_simplify.
  - move:H. destruct f; destruct f; by explode_and_simplify.
  - (* Label *) exists (Label n0 l l0). exists es2'. exists n0. exists l. exists l0.
    apply/andP. split => //.
    apply/andP. split => //.
    apply/eqP.
    move:H. explode_and_simplify.
    destruct run_step_with_fuel as [[s'' vs''] r''] eqn:HDestruct.
    destruct r'' as [ |n' rvs'| |]=> //. destruct n'; last by pattern_match.
    by destruct (n0 <= length rvs').
  - (* Local *)
    move:H. explode_and_simplify.
    destruct run_step_with_fuel as [[s'' vs''] r''] eqn:HDestruct.
    destruct r'' as [ | |rvs'|]=> //. by destruct (n0 <= length rvs').
Qed.

(** Similar to [rs_break_trace_bool], but in [Prop]. **)
Lemma rs_break_trace: forall fuel d i s vs es s' vs' n es',
  run_step_with_fuel mem_grow_impl host_apply_impl fuel.+2 d i (s, vs, es)
  = (s', vs', RS_break n es') -> 
  let: (ves, es'') := split_vals_e es in
  exists e es2 ln les es3, (es'' = e :: es2) /\
   ((e = Basic (Br n)) /\ ((s, vs, es') = (s', vs', rev ves)) \/
    (e = Label ln les es3) /\
    ((run_step_with_fuel mem_grow_impl host_apply_impl fuel d i (s, vs, es3))
     = (s', vs', RS_break n.+1 es'))).
Proof.
  move => fuel d i s vs es s' vs' n es' H.
  apply rs_break_trace_bool in H.
  destruct (split_vals_e es) as [lconst les'] eqn:HSplitVals.
  destruct H as [e [es2 [ln [les [es3 EH]]]]].
  exists e. exists es2. exists ln. exists les. exists es3.
  move/andP in EH. destruct EH as [HES EH2]. split; first by move/eqP in HES.
  move/orP in EH2. destruct EH2 as [HBasic|HLabel].
  - left. move/andP in HBasic. destruct HBasic as [HBasicE HBasicR].
    move/eqP in HBasicE. move/eqP in HBasicR. split => //. by inversion HBasicR.
  - right. move/andP in HLabel. destruct HLabel as [HLabelE HLabelR].
    move/eqP in HLabelE. move/eqP in HLabelR. by split => //.
Qed.

(** If the result of the interpreter is a [RS_return], then we were executing
  either a [Basic Return] or [Label] instruction, which itself returned a [RS_return]. **)
Lemma rs_return_trace: forall fuel d i s vs es s' vs' rvs,
  run_step_with_fuel mem_grow_impl host_apply_impl fuel.+2 d i (s, vs, es)
  = (s', vs', RS_return rvs) ->
  let: (ves, es') := split_vals_e es in
  exists e es'' ln les es2,
    (es' = e :: es'') /\
    (e = Basic Return /\ (s, vs, rvs) = (s', vs', rev ves) \/
     (e = Label ln les es2 /\
      run_step_with_fuel mem_grow_impl host_apply_impl fuel d i (s, vs, es2)
      = (s', vs', RS_return rvs))).
Proof.
  move => fuel d i s vs es s' vs' rvs /= H.
  destruct (split_vals_e es) as [vs2 es2] eqn:HSplit.
  apply split_vals_e_v_to_e_duality in HSplit.
  destruct es2 as [|e es2']=> //.
  destruct e as [b| | | |]=> //; unfold e_is_trap in H.
  - destruct b => //; move:H; try explode_and_simplify.
    + (* Basic Return *)
      exists (Basic Return). exists es2'.
      exists 0. exists [::]. exists [::].
      split => //. left. split => //. by inversion H.
  - move:H. by explode_and_simplify.
  - move:H. repeat destruct f; by explode_and_simplify.
  - (* Label *)
    exists (Label n l l0). exists es2'. exists n. exists l. exists l0.
    split => //. right. split => //.
    move:H. explode_and_simplify.
    destruct run_step_with_fuel as [[s'' vs''] r''] eqn:HDestruct => //.
    destruct r'' as [ |n' rvs'| |]=> //; try pattern_match.
    destruct n' => //.
    by destruct (n <= length rvs').
  - (* Local *)
    move:H. explode_and_simplify.
    destruct run_step_with_fuel as [[s'' vs''] r''] eqn:HDestruct => //.
    destruct r'' as [ | |rvs'| ]=> //; try pattern_match.
    by destruct (n <= length rvs').
Qed.

(** Variants relating the result with [lfilledInd] (no longer used). **)

Lemma rs_break_lfilled: forall fuel d i s vs es s' vs' n es',
  run_step_with_fuel mem_grow_impl host_apply_impl fuel.+2 d i (s, vs, es)
  = (s', vs', RS_break n es') -> 
  let: (ves, es'') := split_vals_e es in
  exists e es2 ln les es3, es'' = e :: es2 /\
    ((e = Basic (Br n) /\ (s, vs, es') = (s', vs', rev ves) /\
      lfilledInd 0 (LBase (v_to_e_list ves) es2) [::Basic (Br n)] es /\
      es' = rev ves
    ) \/
    (e = Label ln les es3 /\ 
     (forall k lh les', lfilledInd k lh les' es3 ->
         lfilledInd k.+1 (LRec (v_to_e_list ves) ln les lh es2) les' es) /\
     run_step_with_fuel mem_grow_impl host_apply_impl fuel d i (s, vs, es3)
     = (s', vs', RS_break n.+1 es')
   )).
Proof.
  move => fuel d i s vs es s' vs' n es' H.
  apply rs_break_trace in H.
  destruct (split_vals_e es) as [vs1 es1] eqn:HSplit.
  apply split_vals_e_v_to_e_duality in HSplit.
  destruct H as [e [es2 [ln [les [es3 EH]]]]].
  destruct EH as [HES [[HBasicE HBasicR] | [HLabelE HLabelR]]].
  - exists e. exists es2. inversion HBasicR. subst.
    exists 0. exists [::]. exists [::].
    split => //. left. repeat split => //.
    simplify_lists. apply LfilledBase; by apply v_to_e_is_const_list.
  - exists e. exists es2. exists ln. exists les. exists es3. 
    subst. split => //. right.
    split => //. split => //.
    move => k lh les' HLF.
    apply LfilledRec => //; by apply v_to_e_is_const_list. 
Qed.

Lemma rs_return_lfilled: forall fuel d i s vs es s' vs' rvs,
  run_step_with_fuel mem_grow_impl host_apply_impl fuel.+2 d i (s, vs, es)
  = (s', vs', RS_return rvs) -> 
  let: (ves, es'') := split_vals_e es in
  exists e es2 ln les es3, (es'' = e :: es2) /\
    ((e = Basic Return /\ (s, vs, rvs) = (s', vs', rev ves) /\
      (lfilledInd 0 (LBase (v_to_e_list ves) es2) [::Basic Return] es) /\
      rvs = rev ves
    ) \/
    (e = Label ln les es3 /\ 
     (forall k lh les', lfilledInd k lh les' es3 ->
        lfilledInd k.+1 (LRec (v_to_e_list ves) ln les lh es2) les' es)) /\
     run_step_with_fuel mem_grow_impl host_apply_impl fuel d i (s, vs, es3)
     = (s', vs', RS_return rvs)
   ).
Proof.
  move => fuel d i s vs es s' vs' rvs H.
  apply rs_return_trace in H.
  destruct (split_vals_e es) as [vs1 es1] eqn:HSplit.
  apply split_vals_e_v_to_e_duality in HSplit.
  destruct H as [e [es2 [ln [les [es3 EH]]]]].
  destruct EH as [HES [[HBasicE HBasicR] | [HLabelE HLabelR]]].
  - exists e. exists es2. inversion HBasicR. subst.
    exists 0. exists [::]. exists [::].
    split => //. left. repeat split => //.
    simplify_lists. apply LfilledBase; by apply v_to_e_is_const_list.
  - exists e. exists es2. exists ln. exists les. exists es3. 
    subst. split => //. right.
    split => //. split => //.
    move => k lh les' HLF.
    apply LfilledRec => //; by apply v_to_e_is_const_list. 
Qed.
  
Lemma rs_break_takes_2_fuel: forall fuel d i s vs es s' vs' n es',
  run_step_with_fuel mem_grow_impl host_apply_impl fuel d i (s, vs, es)
  = (s', vs', RS_break n es') ->
  exists fuel', fuel = fuel'.+2 .
Proof.
  destruct fuel; first by [].
  move => d i s vs es s' vs' n es'.
  unfold run_step_with_fuel.
  destruct (split_vals_e es) as [vs2 es2] eqn:HSplit.
  apply split_vals_e_v_to_e_duality in HSplit.
  destruct es2 as [|e es2'] => //.
  destruct e as [b| | | |] => //=; try (destruct fuel => //; by exists fuel).
  by explode_and_simplify.
Qed.                   

Lemma rs_return_takes_2_fuel: forall fuel d i s vs es s' vs' rvs,
  run_step_with_fuel mem_grow_impl host_apply_impl fuel d i (s, vs, es)
  = (s', vs', RS_return rvs) ->
  exists fuel', fuel = fuel'.+2 .
Proof.
  destruct fuel; first by [].
  move => d i s vs es s' vs' rvs.
  unfold run_step_with_fuel.
  destruct (split_vals_e es) as [vs2 es2] eqn:HSplit.
  apply split_vals_e_v_to_e_duality in HSplit.
  destruct es2 as [|e es2'] => //.
  destruct e as [b| | | |] => //=; try (destruct fuel => //; by exists fuel).
  by explode_and_simplify.
Qed.

(** A sequence of labels with a break/return inside the inner most level. This 
  characterises the stack when the interpreter ends execution with an
  [RS_break] or [RS_return]. **)
Inductive Label_sequence: nat -> seq administrative_instruction -> administrative_instruction -> seq administrative_instruction -> Prop :=
  | LS_Break: forall n vs es,
           const_list vs ->
           Label_sequence 0 vs (Basic (Br n)) (vs ++ [::Basic (Br n)] ++ es)
  | LS_Return: forall vs es,
           const_list vs ->
           Label_sequence 0 vs (Basic Return) (vs ++ [::Basic Return] ++ es)
  | LS_Label: forall k m vs0 e0 vs es bs es',
           const_list vs ->
           Label_sequence k vs0 e0 bs ->
           Label_sequence (k.+1) vs0 e0 (vs ++ [::Label m es' bs] ++ es).

(** [Label_sequence] is in fact very similar to lfilled. **)
Lemma Label_sequence_lfilled_exists: forall k vs e bs,
  Label_sequence k vs e bs ->
  exists lh es, lfilledInd k lh es bs.
Proof.
  move => k. induction k.
  - move => vs0 e0 bs H. inversion H; subst.
    + exists (LBase vs0 es). exists [::Basic (Br n)]. apply LfilledBase => //.
    + exists (LBase vs0 es). exists [::Basic Return]. apply LfilledBase => //.
  - subst. move => vs0 e0 bs H. inversion H. subst.
    apply IHk in H2. destruct H2 as [lh [es2 HLF]].
    exists (LRec vs m es' lh es). exists es2.
    apply LfilledRec => //.
Qed.

Lemma Label_sequence_lfilledk: forall k vs e bs m,
  Label_sequence k vs e bs ->
  m <= size vs ->
  exists lh, lfilledInd k lh (drop m vs ++ [::e]) bs.
Proof.
  move => k. induction k.
  - move => vs e bs m HLS HSize.
    inversion HLS; subst; exists (LBase (take m vs) es); by apply lfilled0_take_drop.
  - move => vs e bs m HLS HSize. inversion HLS. subst.
    eapply IHk in H1. destruct H1 as [lh EH].
    eexists. apply LfilledRec => //.
    apply EH.
    assumption.
Qed.

(** If the interpreter successfully finishes execution given stack [es] and [ends]
  up with [RS_break n es'], then [es] is well-founded, i.e. the recursive case
  [Label _ _ _] cannot take place infinitely often. In fact we even know exactly 
  how many times the recursive case takes place. **)
Lemma rs_break_wellfounded: forall fuel d i s vs es s' vs' n es',
  run_step_with_fuel mem_grow_impl host_apply_impl fuel d i (s, vs, es)
  = (s', vs', RS_break n es') ->
  s = s' /\ vs = vs' /\ (exists k m vs0, k+n=m /\ Label_sequence k vs0 (Basic (Br m)) es /\
  v_to_e_list es' = rev vs0). 
Proof.
  induction fuel using induction2 => //.
  - (* fuel = 1 *)
    move => d i s vs es s' vs' n es' H.
    apply rs_break_takes_2_fuel in H. by inversion H.
  - (* fuel >= 2 *)    
    move => d i s vs es s' vs' n es' H.
    eapply rs_break_trace in H.
    destruct (split_vals_e es) as [vs2 es2] eqn:HSplit.
    apply split_vals_e_v_to_e_duality in HSplit.
    destruct H as [e [es3 [ln [les [es4 EH]]]]].
    destruct EH as [HES [[HBasicE HBasicR] | [HLabelE HLabelR]]].
    + inversion HBasicR. subst. repeat split => //.
      exists 0. exists n. exists (v_to_e_list vs2). repeat split => //.
      * apply LS_Break. by apply v_to_e_is_const_list.
      * by apply v_to_e_rev.
    + apply IHfuel in HLabelR.
      destruct HLabelR as [Hs [Hvs [k [m [vs0 [HSum [HLS HES']]]]]]]. subst.
      repeat split => //.
      exists (k.+1). exists (k.+1+n). exists vs0. repeat split => //.
      apply LS_Label => //. by apply v_to_e_is_const_list.
      replace (k.+1+n) with (k+n.+1) => //.
      by lias.
Qed.

Lemma rs_return_wellfounded: forall fuel d i s vs es s' vs' es',
  run_step_with_fuel mem_grow_impl host_apply_impl fuel d i (s, vs, es)
  = (s', vs', RS_return es') ->
  s = s' /\ vs = vs' /\ (exists k vs0, Label_sequence k vs0 (Basic Return) es /\
  v_to_e_list es' = rev vs0). 
Proof.
  induction fuel using induction2 => //.
  - (* fuel = 1 *)
    move => d i s vs es s' vs' es' H.
    apply rs_return_takes_2_fuel in H. by inversion H.
  - (* fuel >= 2 *)    
    move => d i s vs es s' vs' es' H.
    eapply rs_return_trace in H.
    destruct (split_vals_e es) as [vs2 es2] eqn:HSplit.
    apply split_vals_e_v_to_e_duality in HSplit.
    destruct H as [e [es3 [ln [les [es4 EH]]]]].
    destruct EH as [HES [[HBasicE HBasicR] | [HLabelE HLabelR]]].
    + inversion HBasicR. subst. repeat split => //.
      exists 0. exists (v_to_e_list vs2). repeat split => //.
      * apply LS_Return. by apply v_to_e_is_const_list.
      * by apply v_to_e_rev.
    + apply IHfuel in HLabelR.
      destruct HLabelR as [Hs [Hvs [k [vs0 [HLS HES']]]]]. subst.
      repeat split => //.
      exists (k.+1). exists vs0. repeat split => //.
      apply LS_Label => //. by apply v_to_e_is_const_list.
Qed.

(** Main proof for the [RS_break] case. **)
Lemma reduce_label_break: forall fuel d i s vs es es' s' vs' es'' n,
  run_step_with_fuel mem_grow_impl host_apply_impl fuel d i (s, vs, es') =
  (s', vs', RS_break 0 es'') ->
  n <= size es'' ->
  reduce s vs ([:: Label n es es']) i s' vs'
   (v_to_e_list (rev (take n es'')) ++ es).
Proof.
  move => fuel d i s vs es es' s' vs' es'' n H HSize.
  apply rs_break_wellfounded in H.
  destruct H as [Hs [Hvs [k [m [vs0 [HSum [HLS HES']]]]]]]. subst.
  destruct k.
  - inversion HLS. subst. apply r_simple. eapply rs_br; first by apply v_to_e_is_const_list.
    + simplify_lists. 
      rewrite leq_eqVlt in HSize. move/orP in HSize. destruct HSize.
      * move/eqP in H. subst. apply /eqP. by rewrite ltnn.
      * by rewrite H.
    + apply/lfilledP.
      symmetry in HES'. apply rev_move in HES'. rewrite HES'.
      simplify_lists.
      replace (rev es'') with (rev (drop n es'') ++ rev (take n es'')).
      simplify_lists.
      repeat rewrite -catA. apply lfilled0_frame_l_empty; last by apply v_to_e_is_const_list.
      repeat rewrite catA. apply lfilled0_frame_r_empty.
      apply lfilled0.
      { rewrite -rev_cat. by rewrite cat_take_drop. }
  - eapply Label_sequence_lfilledk in HLS.
    destruct HLS as [lh EH].
    apply r_simple. eapply rs_br; first by apply v_to_e_is_const_list.
    + simplify_lists. 
      rewrite leq_eqVlt in HSize. move/orP in HSize. destruct HSize.
      * move/eqP in H. subst. apply /eqP. by rewrite ltnn.
      * by rewrite H.
    + apply/lfilledP.
      replace (v_to_e_list (rev (take n es''))) with (drop (size vs0 - n) vs0).
      replace (k.+1+0) with (k.+1) in EH.
      apply EH.
      { by lias. }
      {
        symmetry in HES'. apply rev_move in HES'. rewrite HES'.
        simplify_lists.
        by rewrite subKn.
      }
      { by lias. }
Qed.
      
Lemma reduce_label_return: forall fuel d i s vs ess s' vs' vs'' vs2 n j,
  run_step_with_fuel mem_grow_impl host_apply_impl fuel d j (s, vs, ess) =
  (s', vs', RS_return vs'') ->
  n <= size vs'' ->
  reduce s vs2 ([:: Local n j vs ess]) i s' vs2
   (v_to_e_list (rev (take n vs''))).
Proof.
  move => fuel d i s vs ess s' vs' vs'' vs2 n j H HSize.
  apply rs_return_wellfounded in H.
  destruct H as [Hs [Hvs [k [vs0 [HLS HES']]]]]. subst.
  destruct k.
  - inversion HLS. subst. auto_frame. apply r_simple. eapply rs_return; first by apply v_to_e_is_const_list.
    + simplify_lists.
      rewrite leq_eqVlt in HSize. move/orP in HSize. destruct HSize.
      * move/eqP in H0. subst. apply /eqP. by rewrite ltnn.
      * by rewrite H0.
    + apply/lfilledP.
      symmetry in HES'. apply rev_move in HES'. rewrite HES'.
      rewrite -v_to_e_rev. replace (rev vs'') with (rev (drop n vs'') ++ rev (take n vs'')).
      rewrite -v_to_e_cat. repeat rewrite v_to_e_rev.
      repeat rewrite -catA. apply lfilled0_frame_l_empty.
      repeat rewrite catA. apply lfilled0_frame_r_empty.
      simplify_lists. apply lfilled0.
      { rewrite -v_to_e_rev.  apply v_to_e_is_const_list. }
      { rewrite -rev_cat. by rewrite cat_take_drop. }
  - subst.
    eapply Label_sequence_lfilledk in HLS.
    destruct HLS as [lh EH].
    auto_frame. apply r_simple. eapply rs_return; first by apply v_to_e_is_const_list.
    + simplify_lists. 
      rewrite leq_eqVlt in HSize. move/orP in HSize. destruct HSize.
      * move/eqP in H. subst. apply /eqP. by rewrite ltnn.
      * by rewrite H.
    + apply/lfilledP.
      replace (v_to_e_list (rev (take n vs''))) with (drop (size vs0 - n) vs0).
      replace (k.+1+0) with (k.+1) in EH.
      apply EH.
      * by lias.
      * symmetry in HES'.
        apply rev_move in HES'. rewrite HES'.
        simplify_lists.
        by rewrite subKn.
      * by lias.
Qed.

Local Lemma run_step_soundness_aux : forall fuel d i s vs es s' vs' es',
  run_step_with_fuel mem_grow_impl host_apply_impl fuel d i (s, vs, es)
  = (s', vs', RS_normal es') ->
  reduce s vs es i s' vs' es'.
Proof.
  strong induction fuel.
  move=> d i s vs es s' vs' es' /=. destruct fuel as [|fuel] => //=.
  destruct (split_vals_e es) as [lconst les] eqn:HSplitVals.
  apply split_vals_e_v_to_e_duality in HSplitVals. rewrite {} HSplitVals.
  destruct les as [|e les'] eqn:Hles => //.
  explode_and_simplify.
  {
    pattern_match. destruct e => //. apply: r_simple.
    apply rs_trap with (lh := LBase (v_to_e_list lconst) les').
    - move/orP in if_expr0. inversion if_expr0 => //=.
      + move/eqP in H0. destruct lconst => //=. by destruct les'.
      + move/eqP in H0. by destruct lconst.
    - rewrite/lfilled/lfill. rewrite v_to_e_is_const_list. show_list_equality.
  }
  destruct fuel as [|fuel] => //=. destruct e as [b| |f|n es1 es2|n j vls ess] => /=.
    { (** [Basic b] **) (* TODO: Separate this case as a lemma. *)
      destruct b.
      - (** [Basic Unreachable] **)
        by explode_and_simplify; pattern_match; auto_frame.

      - (** [Basic Nop] **)
        by explode_and_simplify; pattern_match; auto_frame.

      - (** [Basic Drop] **)
        by explode_and_simplify; pattern_match; auto_frame.

      - (** [Basic Select] **)
        explode_and_simplify; pattern_match; stack_frame; subst_rev_const_list.
        + (** [Select_true] **)
          by auto_frame.
        + (** [Select_false] **)
          frame_out (v_to_e_list (rev l)) les'.
          simpl. apply: r_simple. apply: rs_select_false.
          move/eqP in if_expr0. by apply/eqP.

      - (** [Basic Block] **)
        explode_and_simplify. pattern_match. auto_frame. stack_frame.
        apply: r_simple. apply: rs_block; first by apply: v_to_e_is_const_list.
        + by eauto.
        + repeat rewrite length_is_size.
          rewrite v_to_e_drop_exchange. rewrite size_drop. rewrite v_to_e_size.
          by rewrite subKn.
        + by [].

      - (** [Basic loop] **)
        explode_and_simplify. pattern_match. auto_frame. stack_frame.
        apply: r_simple. apply: rs_loop => //=.
        +(*1*) by apply: v_to_e_is_const_list.
        +(*2*) repeat rewrite length_is_size.
          rewrite v_to_e_drop_exchange. rewrite size_drop. rewrite v_to_e_size.
          by rewrite subKn.

      - (** [Basic If] **)
        explode_and_simplify; pattern_match; stack_frame; subst_rev_const_list.
        + auto_frame.
        + auto_frame. apply: r_simple. apply: rs_if_true.
          apply/eqP. by move/eqP in if_expr0.

      - (** [Basic (Br i0)] **)
        by pattern_match.

      - (** [Basic Br_if] **)
        explode_and_simplify; pattern_match; auto_frame.
        simpl. apply: r_simple. apply: rs_br_if_true.
        apply/eqP. by move/eqP in if_expr0.

      - (** [Basic Br_table] **)
        explode_and_simplify; pattern_match; auto_frame.
        + apply: r_simple. apply: rs_br_table.
          * by rewrite length_is_size.
          * by apply/eqP.
        + apply: r_simple. apply: rs_br_table_length.
          rewrite length_is_size. move/ltP in if_expr0.
          apply/leP => /=. by lias.

      - (** [Basic Return] **)
        by pattern_match.

      - (** [Basic (Call i0)] **)
        explode_and_simplify. pattern_match. auto_frame.
        apply: r_call. by apply/eqP.

      - (** [Basic (Call_indirect i0)] **)
        explode_and_simplify; pattern_match; auto_frame.
        + apply: r_call_indirect_success.
          * simpl. by apply/eqP.
          * apply/eqP. by eauto.
          * by [].
        + apply: r_call_indirect_failure1.
          * simpl. apply/eqP. by eauto.
          * move/eqP in if_expr0. by apply/eqP.
        + apply: r_call_indirect_failure2. simpl. by apply/eqP.

      - (** [Basic (Get_local i0)] **)
        explode_and_simplify. pattern_match. auto_frame.
        rewrite (split3 if_expr0 HExpect).
        apply: r_get_local. rewrite length_is_size. rewrite size_take.
        by rewrite if_expr0.

      - (** [Basic (Set_local i0)] **)
        explode_and_simplify. pattern_match.
        rewrite -update_list_at_is_set_nth => //=.
        by auto_frame.

      - (** [Basic (Tee_local i0)] **)
        explode_and_simplify. pattern_match.
        by frame_out (v_to_e_list (rev l)) les'.

      - (** [Basic (Get_global i0)] **)
        explode_and_simplify. pattern_match. auto_frame. stack_frame.
        apply: r_get_global. by apply/eqP.

      - (** [Basic (Set_global i0)] **)
        explode_and_simplify. pattern_match. by auto_frame.

      - (** [Basic (Load v o a0 s0)] **)
        explode_and_simplify; try (pattern_match; auto_frame).
        + apply: r_load_packed_success; try eassumption. by apply/eqP.
        + apply: r_load_packed_failure; try eassumption. by apply/eqP.
        + simpl. by apply: r_load_success; try eassumption; try apply/eqP; eauto.
        + apply: r_load_failure; try eassumption. by apply/eqP.

      - (** [Basic (Store v o a0 s0)] **)
        explode_and_simplify; pattern_match; auto_frame.
        + by apply: r_store_packed_success => //=; try eassumption; try apply/eqP; eauto.
        + by apply: r_store_packed_failure => //=; eauto.
        + by apply: r_store_success => //=; eauto.
        + apply: r_store_failure => //=; try eassumption. by apply/eqP.

      - (** [Basic Current_memory] **)
        explode_and_simplify. pattern_match. auto_frame.
        apply: r_current_memory => //=.
        + by eauto.
        + by [].

      - (** [Basic Grow_memory] **)
        explode_and_simplify. pattern_match. auto_frame.
        apply: r_grow_memory_success => //=.
        + by [].
        + by apply: mem_grow_impl_correct.

      - (** [Basic (Econst _)] **)
        by pattern_match.

      - (** [Basic Unop_i v u] **)
        by explode_and_simplify;  pattern_match; auto_frame.

      - (** [Basic Unop_f v u] **)
        by explode_and_simplify;  pattern_match; auto_frame.

      - (** [Basic Binop_i v b] **)
        by explode_and_simplify; pattern_match; auto_frame.

      - (** [Basic Binop_f v b] **)
        by explode_and_simplify; pattern_match; auto_frame.

      - (** [Basic (Testop v t)] **)
        by explode_and_simplify; pattern_match; auto_frame.

      - (** [Basic (Relop_i v r)] **)
        by explode_and_simplify; pattern_match; auto_frame.

      - (** [Basic (relop_f v r)] **)
        by explode_and_simplify; pattern_match; auto_frame.

      - (** [Basic (Cvtop v c v0 o)] **)
        explode_and_simplify; pattern_match; auto_frame.
        + apply: r_simple. apply: rs_convert_failure => //. by apply/eqP.
        + apply: r_simple. apply: rs_convert_failure => //. by apply/eqP.
    }
    { (** [Trap] **)
      by pattern_match.
    }
    { (** [Callcl] **)
      destruct f => //=.
      - (** [Func_native] **)
        explode_and_simplify. pattern_match. stack_frame. auto_frame.
        apply: r_callcl_native => //=.
        simplify_lists. by rewrite subKn.
      - (** [Func_host] **)
        explode_and_simplify; pattern_match; stack_frame; auto_frame.
        + apply: r_callcl_host_success => //=.
          * simplify_lists. by rewrite subKn.
          * apply/eqP. by eauto.
        + apply: r_callcl_host_failure => //=.
          explode_and_simplify. by rewrite subKn.
    }
    { (** [Label] **)
      explode_and_simplify; try (pattern_match; auto_frame).
      + apply: r_simple. by apply: rs_label_trap.
      + destruct run_step_with_fuel as [[s'' vs''] r] eqn: EH.
        destruct r as [|nd es''| |es''] => //.
        * (** [RS_break] **)
          destruct nd => //. explode_and_simplify. pattern_match. auto_frame.
          eapply reduce_label_break => //; by eauto.
             
        * (** [RS_normal] **)
          pattern_match.
          (* We actually want to keep the frame here for later use in lfilled.*)
          apply H in EH; last by lias.
          eapply r_label.
          - by eauto.
          - apply/lfilledP.
            eapply LfilledRec; first by apply v_to_e_is_const_list.
            by apply lfilled0.
          - apply/lfilledP.
            rewrite -catA.
            apply LfilledRec; first by apply v_to_e_is_const_list.
            by apply lfilled0.
    }
    { (** [Local] **)
      explode_and_simplify; try (pattern_match; auto_frame).
      + apply: r_simple. by apply: rs_local_trap.
      + destruct run_step_with_fuel as [[s'' vs''] r] eqn: EH.
        destruct r as [| |vs'''|es''] => //.
        * (** [RS_return] **)
          explode_and_simplify. pattern_match. auto_frame.
          eapply reduce_label_return => //; by eauto. 
        * (** [RS_normal] **)
          pattern_match. auto_frame. apply H in EH; last by lias.
          by apply r_local.
    }
Qed.

Theorem run_step_soundness : forall d i s vs es s' vs' es',
  run_step d i (s, vs, es) = (s', vs', RS_normal es') ->
  reduce s vs es i s' vs' es'.
Proof.
  move=> d i s vs es s' vs' es'. by apply: run_step_soundness_aux.
Qed.

End Host.
