(* soundness of the Wasm interpreter *)
(* (C) J. Pichon, M. Bodin, Rao Xiaojia - see LICENSE.txt *)

Require Import common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Require Import Omega.
From StrongInduction Require Import StrongInduction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import wasm opsem interpreter wasm_properties_aux.


Section Host.

(* TODO: The host should be defined as a mixin. *)
Variable mem_grow_impl : mem -> nat -> option mem.
Hypothesis mem_grow_impl_correct :
  forall m n m',
    mem_grow_impl m n = Some m' ->
    mem_grow m n = m'.

Variable host_apply_impl : store_record -> function_type -> wasm.host -> list value -> option (store_record * list value).
Hypothesis host_apply_impl_correct :
  forall s tf h vs m',
    host_apply_impl s tf h vs = Some m' ->
    exists hs, wasm.host_apply s tf h vs hs = Some m'.

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
  apply: r_label; try apply lfilled_Ind_Equivalent.
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
  apply: r_label; try apply lfilled_Ind_Equivalent.
  - apply: H.
  - replace (es++les) with ([::]++es++les) => //. by apply: LfilledBase.
  - replace (es'++les) with ([::]++es'++les) => //. by apply: LfilledBase.
Qed.

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

Lemma split3: forall {X:Type} (l:seq X) n v,
    n < size l ->
    List.nth_error l n = Some v ->
    l = (take n l) ++ [::v] ++ (drop (n+1) l).
Proof.
  move => X.
  elim => //= a l IH n v.
  elim: n => [_ [H]|n IH2 Ha Hb].
  - by rewrite /= H drop0.
  - by rewrite /= -(IH _ _ Ha Hb).
Qed.

Lemma run_step_fuel_not_zero : forall tt,
  run_step_fuel tt <> 0.
Proof.
  move=> [[st vs] es]. rewrite/run_step_fuel. by lias.
Qed.


Lemma rev_move: forall {X:Type} (l1 l2:seq X),
  rev l1 = l2 -> l1 = rev l2.
Proof.
  move => X l1 l2 HRev. rewrite -HRev. symmetry. by apply: revK.
Qed.

Lemma const_list_cons : forall a l,
  const_list (a :: l) = is_const a && const_list l.
Proof.
  by [].
Qed.

Lemma v_to_e_take_drop_split: forall l n,
  v_to_e_list l = v_to_e_list (take n l) ++ v_to_e_list (drop n l).
Proof.
  move => l n. rewrite v_to_e_cat. by rewrite cat_take_drop.
Qed.

Lemma v_to_e_rev: forall l,
  v_to_e_list (rev l) = rev (v_to_e_list l).
Proof.
  elim => //=.
  move => a l IH. rewrite rev_cons. rewrite -cats1. rewrite -v_to_e_cat.
  rewrite rev_cons. rewrite -cats1. by rewrite -IH.
Qed.

Lemma rev0 : forall A, rev [::] = ([::] : seq A).
Proof. reflexivity. Qed.

Lemma v_to_e_list0 : v_to_e_list [::] = [::].
Proof. reflexivity. Qed.

Lemma v_to_e_list1 : forall v, v_to_e_list [:: v] = [:: Basic (EConst v)].
Proof. reflexivity. Qed.

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
    | rewrite size_drop
    | rewrite rev_cat
    | rewrite rev_cons -cats1
    | rewrite -v_to_e_cat ];
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
  - by destruct f as [? f ? ?|f ?] => //=; destruct f; explode_and_simplify; pattern_match; right.
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
  move=> > I' E'.
  apply: run_one_step_fuel_increase.
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
  rewrite -(Nat.max_0_l (TProp.max Fm)). move: 0. induction es => n /=.
  - lias.
  - rewrite Nat.max_assoc. by apply: IHes.
Qed.

Local Lemma run_step_fuel_enough_aux : forall d i s vs es s' vs' r',
  TProp.Forall (fun e => forall d i tt s vs r,
     run_one_step (run_one_step_fuel e) d i tt e = (s, vs, r) -> r <> RS_crash C_exhaustion) es ->
  run_step d i (s, vs, es) = (s', vs', r') ->
  r' <> RS_crash C_exhaustion.
Admitted (* TODO *).

(** [run_one_step_fuel] is indeed enough fuel to run [run_one_step]. **)
Lemma run_one_step_fuel_enough : forall d i tt e s vs r,
  run_one_step (run_one_step_fuel e) d i tt e = (s, vs, r) ->
  r <> RS_crash C_exhaustion.
Proof.
  move=> + + + e. induction e using administrative_instruction_ind';
    move=> d j [[tt_s tt_vs] tt_es] s' vs' r /=.
  - by destruct b; explode_and_simplify; pattern_match.
  - by pattern_match.
  - by destruct f as [? f ? ?|f ?] => //=; destruct f; explode_and_simplify; pattern_match.
  - match goal with |- run_one_step ?fuel _ _ _ _ = _ -> _ => set f := fuel end.
    assert (f >= 1 + run_step_fuel (tt_s, tt_vs, es2)).
    {
      apply/leP. rewrite/f /=.
      move: (max_fold_left_run_step_fuel es2). clear. lias.
    }
    destruct f as [|f'] eqn:Ef => //. simpl.
    explode_and_simplify; try by pattern_match.
    destruct (run_step d j (tt_s, tt_vs, es2)) as [[s'' vs''] r''] eqn:E1.
    move: (E1) => D. apply run_step_fuel_enough_aux in D => //.
    move: (E1) => E2. apply run_step_fuel_increase with (fuel' := f') in E2.
    + destruct E2 as [E2|E2] => //. rewrite E2.
      by destruct r'' as [|[|]| |] => //; explode_and_simplify; pattern_match.
    + apply/leP. move: H. move/leP. by lias.
  - match goal with |- run_one_step ?fuel _ _ _ _ = _ -> _ => set f := fuel end.
    assert (f >= 1 + run_step_fuel (tt_s, vs, es)).
    {
      apply/leP. rewrite/f /=.
      move: (max_fold_left_run_step_fuel es). clear. lias.
    }
    destruct f as [|f'] eqn:Ef => //. simpl.
    explode_and_simplify; try by pattern_match.
    destruct (run_step d i (tt_s, vs, es)) as [[s'' vs''] r''] eqn:E1.
    move: (E1) => D. apply run_step_fuel_enough_aux in D => //.
    move: (E1) => E2. apply run_step_fuel_increase with (fuel' := f') in E2.
    + destruct E2 as [E2|E2] => //. rewrite E2.
      by destruct r'' as [|[|]| |] => //; explode_and_simplify; pattern_match.
    + apply/leP. move: H. move/leP. by lias.
Qed.

(** [run_step_fuel] is indeed enough fuel to run [run_step]. **)
Lemma run_step_fuel_enough : forall d i tt s vs r,
  run_step d i tt = (s, vs, r) ->
  r <> RS_crash C_exhaustion.
Proof.
Admitted. (* TODO *)

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
    - admit. (* TODO *)
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
        destruct f as [t1s t2s].
        explode_and_simplify. pattern_match. auto_frame. stack_frame.
        apply: r_simple. apply: rs_block; first by apply: v_to_e_is_const_list.
        + by eauto.
        + repeat rewrite length_is_size.
          rewrite v_to_e_drop_exchange. rewrite size_drop. rewrite v_to_e_size.
          by rewrite subKn.
        + by [].

      - (** [Basic loop] **)
        destruct f as [t1s t2s].
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
          apply/leP => /=. omega.

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
        by explode_and_simplify; destruct v => //=; pattern_match; auto_frame.

      - (** [Basic Unop_f v u] **)
        by explode_and_simplify; destruct v => //=; pattern_match; auto_frame.

      - (** [Basic Binop_i v b] **)
        by explode_and_simplify; destruct v => //; pattern_match; auto_frame.

      - (** [Basic Binop_f v b] **)
        by explode_and_simplify; destruct v => //; pattern_match; auto_frame.

      - (** [Basic (Testop v t)] **)
        by explode_and_simplify; destruct v => //; pattern_match; auto_frame.

      - (** [Basic (Relop_i v r)] **)
        by explode_and_simplify; destruct v => //; pattern_match; auto_frame.

      - (** [Basic (relop_f v r)] **)
        by explode_and_simplify; destruct v => //; pattern_match; auto_frame.

      - (** [Basic (Cvtop v c v0 o)] **)
        explode_and_simplify; destruct c => //; pattern_match; auto_frame.
        + apply: r_simple. apply: rs_convert_failure => //. by apply/eqP.
        + apply: r_simple. apply: rs_convert_failure => //. by apply/eqP.
    }
    { (** [Trap] **)
      explode_and_simplify. pattern_match.
    }
    { (** [Callcl] **)
      destruct f as [? f ? ?|f ?] => //=; destruct f.
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
          destruct nd => //. explode_and_simplify. pattern_match.
          admit. (* TODO *)
        * (** [RS_normal] **)
          pattern_match. auto_frame. apply H in EH; last by lias.
          admit. (* TODO *)
    }
    { (** [Local] **)
      explode_and_simplify; try (pattern_match; auto_frame).
      + apply: r_simple. by apply: rs_local_trap.
      + destruct run_step_with_fuel as [[s'' vs''] r] eqn: EH.
        destruct r as [| |vs'''|es''] => //.
        * (** [RS_return] **)
          explode_and_simplify. pattern_match.
          admit. (* TODO *)
        * (** [RS_normal] **)
          pattern_match. auto_frame. apply H in EH; last by lias.
          admit. (* TODO *)
    }
Admitted. (* TODO *)

Theorem run_step_soundness : forall d i s vs es s' vs' es',
  run_step d i (s, vs, es) = (s', vs', RS_normal es') ->
  reduce s vs es i s' vs' es'.
Proof.
  move=> d i s vs es s' vs' es'. apply run_step_soundness_aux.
Qed.

End Host.
