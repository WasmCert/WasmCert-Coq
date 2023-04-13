(** Wasm interpreter **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Wasm Require Import common opsem properties tactic type_preservation type_progress.
From Coq Require Import ZArith.BinInt.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export operations host type_checker.
Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

Inductive res_crash : Type :=
| C_error : res_crash
| C_exhaustion : res_crash.

Scheme Equality for res_crash.
Definition res_crash_eqb c1 c2 := is_left (res_crash_eq_dec c1 c2).
Definition eqres_crashP : Equality.axiom res_crash_eqb :=
  eq_dec_Equality_axiom res_crash_eq_dec.

Canonical Structure res_crash_eqMixin := EqMixin eqres_crashP.
Canonical Structure res_crash_eqType := Eval hnf in EqType res_crash res_crash_eqMixin.

Inductive res : Type :=
| R_crash : res_crash -> res
| R_trap : res
| R_value : list value -> res.

Definition res_eq_dec : forall r1 r2 : res, {r1 = r2} + {r1 <> r2}.
Proof. decidable_equality. Defined.

Definition res_eqb (r1 r2 : res) : bool := res_eq_dec r1 r2.
Definition eqresP : Equality.axiom res_eqb :=
  eq_dec_Equality_axiom res_eq_dec.

Canonical Structure res_eqMixin := EqMixin eqresP.
Canonical Structure res_eqType := Eval hnf in EqType res res_eqMixin.

Section Host_func.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record := store_record host_function.
(*Let administrative_instruction := administrative_instruction host_function.*)
Let host_state := host_state host_instance.

(*Let vs_to_es : seq value -> seq administrative_instruction := @vs_to_es _.*)

Let e_typing := @e_typing host_function.
Let inst_typing := @inst_typing host_function.

Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                       (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).

Inductive res_step : Type :=
| RS_crash : res_crash -> res_step
| RS_break : nat -> list value -> res_step
| RS_return : list value -> res_step
| RS_normal : list administrative_instruction -> res_step.

(* TODO: the break/return cases also need some proofs to go with them,
 * see interpreter_func_sound. *)
Inductive res_step'
  (hs : host_state) (s : store_record) (f : frame)
  (es : list administrative_instruction) : Type :=
| RS'_exhaustion : res_step' hs s f es
| RS'_error : (~ exists C t, e_typing s C es t) -> res_step' hs s f es
| RS'_break : host_state -> store_record -> frame -> nat -> list value -> res_step' hs s f es (* TODO needs some reduce proof *)
| RS'_return : host_state -> store_record -> frame -> list value -> res_step' hs s f es (* TODO needs some reduce proof *)
| RS'_normal hs' s' f' es': reduce hs s f es hs' s' f' es' -> res_step' hs s f es.

Inductive res_step'_separate_e
  (hs : host_state) (s : store_record) (f : frame)
  (ves : list value) (e : administrative_instruction) : Type :=
| RS''_exhaustion : res_step'_separate_e hs s f ves e
| RS''_error (inst : instance) :
    (~ exists C ts1 ts2 ts1',
      map typeof ves = ts1' ++ ts1 /\
      inst_typing s inst C /\
      e_typing s C ((vs_to_es ves) ++ [::e]) (Tf ts1 ts2)) ->
    res_step'_separate_e hs s f ves e
(* | RS''_break *)
(* | RS''_return *)
| RS''_normal hs' s' f' es' :
    reduce hs s f ((vs_to_es ves) ++ [::e]) hs' s' f' es' ->
    res_step'_separate_e hs s f ves e.

(* Notation for RS'_normal. This forces hs', s', f' es' to be explicitly
 * stated. Their values could be inferred from the type of H instead but we
 * want to make those values clear. *)
Notation "<< hs' , s' , f' , es' >>[ H ]" := (@RS'_normal _ _ _ _ hs' s' f' es' H).

(* Using this as a TODO placeholder *)
Axiom admitted_TODO : forall P : Prop, P.

Definition res_step_eq_dec : forall r1 r2 : res_step, {r1 = r2} + {r1 <> r2}.
Proof. decidable_equality. Defined.

Definition res_step_eqb (r1 r2 : res_step) : bool := res_step_eq_dec r1 r2.
Definition eqres_stepP : Equality.axiom res_step_eqb :=
  eq_dec_Equality_axiom res_step_eq_dec.

Canonical Structure res_step_eqMixin := EqMixin eqres_stepP.
Canonical Structure res_step_eqType := Eval hnf in EqType res_step res_step_eqMixin.

Definition crash_error := RS_crash C_error.

Definition depth := nat.

Definition fuel := nat.

Definition config_tuple := ((host_state * store_record * frame * list administrative_instruction)%type).

Definition config_one_tuple_without_e := (host_state * store_record * frame * list value)%type.

Check config_typing.

Definition config_tuple_typing (cfg : config_tuple) (t : seq value_type) : Prop :=
  match cfg with
  | (_, s, f, es) => config_typing s f es t
  end.

Definition config_tuple_separate_e_typing (cfg : config_one_tuple_without_e) (e : administrative_instruction) (t : seq value_type) : Prop :=
  match cfg with
  | (_, s, f, vs) => config_typing s f ((vs_to_es vs) ++ [::e]) t
  end.

Definition res_tuple := (host_state * store_record * frame * res_step)%type.

(* TODO *)
Axiom coerce_res : forall hs s f es1 es2 (r : res_step' hs s f es1), res_step' hs s f es2.

(* TODO auto instantiate lh, k? *)
(* TODO better name *)
Ltac solve_lfilled_0 :=
  unfold lfilled, lfill, vs_to_es;
  try rewrite v_to_e_is_const_list; apply/eqP; simplify_lists => //.

Lemma reduce_unop : forall (hs : host_state) s f t op v ves' es0,
  es0 = vs_to_es (v :: ves') ++ [:: AI_basic (BI_unop t op)] ->
  reduce hs s f es0 hs s f (vs_to_es (app_unop op v :: ves')).
Proof.
  intros hs s f t op v ves' es0 ?. subst es0.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::])).
  - apply r_simple. by apply rs_unop.
  - by solve_lfilled_0.
  - by solve_lfilled_0.
Qed.

(* NOTE unused, simpler version of unop_error *)
Lemma unop_error_be : forall s inst ves t op,
  ves = [::] ->
  (~ exists C t1s t2s t1s',
    map typeof ves = t1s' ++ t1s /\
    inst_typing s inst C /\
    be_typing C ((map BI_const ves) ++ [:: BI_unop t op]) (Tf t1s t2s)).
Proof.
  intros s inst ves t op Heqves [C [t1s [t2s [t1s' [Ht1s [Hitype Hbtype]]]]]].
  subst ves.
  assert (t1s = [::]). { by destruct t1s' => //. } subst t1s.
  apply Unop_typing in Hbtype as [? [ts ?]].
  by destruct ts => //.
Qed.

(* NOTE seems like this wasn't needed, proved unop_error directly instead *)
Lemma unop_error_helper : forall s t op C ts,
  ~ e_typing s C [:: AI_basic (BI_unop t op)] (Tf [::] ts).
Proof.
  intros s t op C ts Hetype.
  gen_ind_subst Hetype.
  - assert (bes = [:: BI_unop t op]). { give_up. (* by H3 *) } subst bes.
    apply Unop_typing in H as [? [ts' ?]].
    by destruct ts' => //.
  - assert (e = AI_basic (BI_unop t op)). { give_up. (* by H2 *) } subst e.
    assert (es = [::]). { give_up. (* by H2 *) } subst es.
    assert (t2s = [::]). { give_up. (* by Hetype1 *) } subst t2s.
    by eapply IHHetype2 => //.
  - assert (t1s = [::]). { apply cat0_inv in H3 as [??]. by assumption. } subst t1s.
    by eapply IHHetype => //.
Admitted.

(* XXX could move C t1s t2s t1s' into the forall without changing semantics *)
Lemma unop_error : forall s inst ves t op,
  ves = [::] ->
  (~ exists C t1s t2s t1s',
    map typeof ves = t1s' ++ t1s /\
    inst_typing s inst C /\
    e_typing s C ((vs_to_es ves) ++ [:: AI_basic (BI_unop t op)]) (Tf t1s t2s)).
Proof.
  intros s inst ves t op Heqves [C [t1s [t2s [t1s' [Ht1s [Hitype Hetype]]]]]].
  subst ves.
  gen_ind_subst Hetype.
  - symmetry in H4. apply cat0_inv in H4 as [??]. subst t1s t1s'.
    assert (bes = [:: BI_unop t op]).
    { repeat destruct bes => //. simpl in H3. by inversion H3. } subst bes.
    apply Unop_typing in H as [? [ts ?]]. by destruct ts => //.
  - assert (es = [::]).
    { destruct es => //. apply extract_list1 in H2 as [H?]. discriminate H. }
    subst es.
    assert (e = AI_basic (BI_unop t op)). { simpl in H2. by inversion H2. } subst e.
    symmetry in H3. apply cat0_inv in H3 as [??]. subst t1s' t1s0.
    assert (t2s = [::]). { by apply empty_e_typing in Hetype1. } subst t2s.
    eapply IHHetype2 => //. by assumption.
    (* alt: by apply (unop_error_helper Hetype2). *)
  - symmetry in H3. repeat apply cat0_inv in H3 as [? H3]. subst t1s t1s'.
    eapply IHHetype => //. by assumption.
Qed.

Lemma reduce_binop : forall (hs : host_state) s f t op v1 v2 v ves' es0,
  es0 = vs_to_es [:: v2, v1 & ves'] ++ [:: AI_basic (BI_binop t op)] ->
  app_binop op v1 v2 = Some v ->
  reduce hs s f es0 hs s f (vs_to_es (v :: ves')).
Proof.
  intros hs s f t op v1 v2 v ves' es0 ? Heqapp. subst es0.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::])).
  - apply r_simple.
    apply rs_binop_success.
    by apply Heqapp.
  - by solve_lfilled_0.
  - by solve_lfilled_0.
Qed.

(* TODO should probably use Binop_typing from ./type_preservation.v? *)
(* TODO use be_typing instead of config_typing? *)
Lemma binop_typing_inversion : forall (hs : host_state) s f t1 t2 op v1 v2 ves',
  config_tuple_typing (hs, s, f, ((vs_to_es (v2 :: v1 :: ves')) ++ [::AI_basic (BI_binop t2 op)])) t1 ->
  (* XXX would be easier to start with
   * be_typing [::v1; v2; AI_basic (BI_binop t2 op)] *)
  exists v, app_binop op v1 v2 = Some v.
Proof.
  intros hs s f t1 t2 op v1 v2 ves' Hctype.
  destruct (app_binop op v1 v2) eqn:Heqapp.
  (* TODO need to show typeof v1 = typeof v2 = t1 = t2 *)
  (* by htype inversion *)
  - exists v. reflexivity.
  - destruct t1, t2 => //.
Admitted.
  (*
  induction ves'.
  - simpl in Hctype.
    inversion Hctype as [????? Hstype].
    inversion Hstype as [????????? Hetype].
    inversion Hetype; subst.
    * assert (Hbes : bes = [:: BI_const v1; BI_const v2; BI_binop t2 op]).
      { give_up. (* by H12 *) }
      subst bes. destruct H12.
      inversion H15.
    Check Binop_typing.
    *)
  (*
  intros hs s f t1 t2 op v1 v2 ves' Hctype.
  inversion Hctype as [????? Hstype].
  inversion Hstype as [????????? Hetype].
  inversion Hetype; subst.
  - give_up.
  - repeat rewrite cats1 in H12.
    assert (Heqe : e = AI_basic (BI_binop t2 op)). { (* by H12 *) give_up. }
    subst e.
    inversion H18.
    * give_up.
   *)

Fixpoint run_step_with_fuel' hs s f es (fuel : fuel) (d : depth) : res_step' hs s f es :=
  match fuel with
  | 0 => RS'_exhaustion hs s f es
  | fuel.+1 =>
    let: (ves, es') := split_vals_e es in (** Framing out constants. **)
    match es' with
    | [::] => RS'_error _ _ (admitted_TODO (~ exists C t, e_typing s C es t))
    | e :: es'' =>
      if e_is_trap e
      then
        if (es'' != [::]) || (ves != [::])
        then RS'_normal (admitted_TODO (reduce hs s f es hs s f [::AI_trap]))
        else RS'_error hs f (admitted_TODO (~ exists C t, e_typing s C es t))      else
        let: cfg'             := (hs, s, f, (rev ves)) in
        (* TODO: this will need some proof of (es = (rev ves) ++ [::e] ++ es'')
         * or similar, not sure how that will work*)
        let: r := run_one_step' hs s f ves e fuel d in
        if r is RS'_normal hs' s' f' es' _ (* TODO *)
        then RS'_normal (admitted_TODO (reduce hs s f es hs' s' f' (es' ++ es'')))
        else coerce_res _ r (* TODO *)
    end
  end

with run_one_step' hs s f ves e (fuel : fuel) (d : depth) : res_step' hs s f ((vs_to_es ves) ++ [::e]) :=
  let: es0 := (vs_to_es ves) ++ [::e] in (* initial es, useful as an arg for reduce *)
  match fuel with
  | 0 => RS'_exhaustion _ _ _ _
  | fuel.+1 =>
    match e with
    (* unop *)
    | AI_basic (BI_unop t op) =>
      if ves is v :: ves'
      then <<hs, s, f, vs_to_es (app_unop op v :: ves')>>[ admitted_TODO _ ]
      else RS'_error _ _ (admitted_TODO _)
    (* binop *)
    | AI_basic (BI_binop t op) =>
      if ves is v2 :: v1 :: ves' then
        let vo := app_binop op v1 v2 in
        match vo with
        | Some v => <<hs, s, f, vs_to_es (v :: ves')>>[ admitted_TODO _ ]
        | None => RS'_error _ _ (admitted_TODO _)
        end
      else RS'_error _ _ (admitted_TODO _)
    (* testops *)
    | AI_basic (BI_testop T_i32 testop) =>
      if ves is (VAL_int32 c) :: ves' then
        RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ((VAL_int32 (wasm_bool (@app_testop_i i32t testop c))) :: ves'))))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_testop T_i64 testop) =>
      if ves is (VAL_int64 c) :: ves' then
        RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ((VAL_int32 (wasm_bool (@app_testop_i i64t testop c))) :: ves'))))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_testop _ _) => RS'_error _ _ (admitted_TODO _)
    (* relops *)
    | AI_basic (BI_relop t op) =>
      if ves is v2 :: v1 :: ves' then
        RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es (VAL_int32 (wasm_bool (app_relop op v1 v2)) :: ves'))))
      else RS'_error _ _ (admitted_TODO _)
    (* convert & reinterpret *)
    | AI_basic (BI_cvtop t2 CVO_convert t1 sx) =>
      if ves is v :: ves' then
        if types_agree t1 v
        then
          expect (cvt t2 sx v) (fun v' =>
               RS'_normal (admitted_TODO
               (reduce hs s f es0 hs s f (vs_to_es (v' :: ves')))))
               (RS'_normal (admitted_TODO
               (reduce hs s f es0 hs s f ((vs_to_es ves') ++ [::AI_trap]))))
        else RS'_error _ _ (admitted_TODO _)
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_cvtop t2 CVO_reinterpret t1 sx) =>
      if ves is v :: ves' then
        if types_agree t1 v && (sx == None)
        then RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es (wasm_deserialise (bits v) t2 :: ves'))))
        else RS'_error _ _ (admitted_TODO _)
      else RS'_error _ _ (admitted_TODO _)
    (**)
    | AI_basic BI_unreachable => RS'_normal
        (admitted_TODO (reduce hs s f es0 hs s f ((vs_to_es ves) ++ [::AI_trap])))
    | AI_basic BI_nop => RS'_normal
        (admitted_TODO (reduce hs s f es0 hs s f (vs_to_es ves)))
    | AI_basic BI_drop =>
      if ves is v :: ves' then
        RS'_normal (admitted_TODO (reduce hs s f es0 hs s f (vs_to_es ves')))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic BI_select =>
      if ves is (VAL_int32 c) :: v2 :: v1 :: ves' then
        if c == Wasm_int.int_zero i32m
        then RS'_normal (admitted_TODO
          (reduce hs s f es0 hs s f (vs_to_es (v2 :: ves'))))
        else RS'_normal (admitted_TODO
          (reduce hs s f es0 hs s f (vs_to_es (v1 :: ves'))))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_block (Tf t1s t2s) es) =>
      if length ves >= length t1s
      then
        let: (ves', ves'')  := split_n ves (length t1s) in
        RS'_normal (admitted_TODO
          (reduce hs s f es0 hs s f
            (vs_to_es ves'' ++ [::AI_label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)])
        ))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_loop (Tf t1s t2s) es) =>
      if length ves >= length t1s
      then
        let: (ves', ves'') := split_n ves (length t1s) in
        RS'_normal (admitted_TODO
          (reduce hs s f es0 hs s f
            (vs_to_es ves''
                    ++ [::AI_label (length t1s) [::AI_basic (BI_loop (Tf t1s t2s) es)]
                            (vs_to_es ves' ++ to_e_list es)])
        ))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_if tf es1 es2) =>
      if ves is VAL_int32 c :: ves' then
        if c == Wasm_int.int_zero i32m
        then RS'_normal (admitted_TODO
        (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_basic (BI_block tf es2)])))
        else RS'_normal (admitted_TODO 
        (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_basic (BI_block tf es1)])))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_br j) => RS'_break _ _ _ _ hs s f j ves
    | AI_basic (BI_br_if j) =>
      if ves is VAL_int32 c :: ves' then
        if c == Wasm_int.int_zero i32m
        then RS'_normal (admitted_TODO
        (reduce hs s f es0 hs s f (vs_to_es ves')))
        else RS'_normal (admitted_TODO
        (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_basic (BI_br j)])))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_br_table js j) =>
      if ves is VAL_int32 c :: ves' then
        let: k := Wasm_int.nat_of_uint i32m c in
        if k < length js
        then
          expect (List.nth_error js k) (fun js_at_k =>
              RS'_normal (admitted_TODO
                (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_basic (BI_br js_at_k)]))))
            (RS'_error _ _ (admitted_TODO _))
        else RS'_normal (admitted_TODO
               (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_basic (BI_br j)])))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_call j) =>
      if List.nth_error f.(f_inst).(inst_funcs) j is Some a then
        RS'_normal (admitted_TODO
          (reduce hs s f es0 hs s f (vs_to_es ves ++ [::AI_invoke a])))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_call_indirect j) =>
      if ves is VAL_int32 c :: ves' then
        match stab_addr s f (Wasm_int.nat_of_uint i32m c) with
        | Some a =>
          match List.nth_error s.(s_funcs) a with
          | Some cl =>
            if stypes s f.(f_inst) j == Some (cl_type cl)
            then RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_invoke a])))
            else RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_trap])))
          | None => RS'_error _ _ (admitted_TODO _)
          end
        | None => RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_trap])))
        end
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic BI_return => RS'_return _ _ _ _ hs s f ves
    | AI_basic (BI_get_local j) =>
      if j < length f.(f_locs)
      then
        expect (List.nth_error f.(f_locs) j) (fun vs_at_j =>
            RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es (vs_at_j :: ves)))))
          (RS'_error _ _ (admitted_TODO _))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_set_local j) =>
      if ves is v :: ves' then
        if j < length f.(f_locs)
        then
          let f' := Build_frame (update_list_at f.(f_locs) j v) f.(f_inst) in
          RS'_normal (admitted_TODO
            (reduce hs s f es0 hs s f' (vs_to_es ves')))
        else RS'_error _ _ (admitted_TODO _)
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_tee_local j) =>
      if ves is v :: ves' then
        RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es (v :: ves) ++ [::AI_basic (BI_set_local j)])))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_get_global j) =>
      if sglob_val s f.(f_inst) j is Some xx
      then RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es (xx :: ves))))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_set_global j) =>
      if ves is v :: ves' then
        if supdate_glob s f.(f_inst) j v is Some xx
        then RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves')))
        else RS'_error _ _ (admitted_TODO _)
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_load t None a off) =>
      if ves is VAL_int32 k :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load (mem_s_j) (Wasm_int.N_of_uint i32m k) off (t_length t))
                 (fun bs => RS'_normal (admitted_TODO (reduce hs s f es0 hs s f (vs_to_es (wasm_deserialise bs t :: ves')))))
                 (RS'_normal (admitted_TODO (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_trap]))))
             else RS'_error _ _ (admitted_TODO _))
          (RS'_error _ _ (admitted_TODO _))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_load t (Some (tp, sx)) a off) =>
      if ves is VAL_int32 k :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load_packed sx (mem_s_j) (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t))
                 (fun bs => RS'_normal (admitted_TODO (reduce hs s f es0 hs s f (vs_to_es (wasm_deserialise bs t :: ves')))))
                 (RS'_normal (admitted_TODO (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_trap]))))
             else RS'_error _ _ (admitted_TODO _))
          (RS'_error _ _ (admitted_TODO _))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_store t None a off) =>
      if ves is v :: VAL_int32 k :: ves' then
        if types_agree t v
        then
          expect
            (smem_ind s f.(f_inst))
            (fun j =>
               if List.nth_error s.(s_mems) j is Some mem_s_j then
                 expect
                   (store mem_s_j (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t))
                   (fun mem' =>
                      let s' := upd_s_mem s (update_list_at s.(s_mems) j mem') in
                      (RS'_normal (admitted_TODO (reduce hs s f es0 hs s f (vs_to_es ves')))))
                   (RS'_normal (admitted_TODO (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_trap]))))
               else RS'_error _ _ (admitted_TODO _))
            (RS'_error _ _ (admitted_TODO _))
        else RS'_error _ _ (admitted_TODO _)
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_store t (Some tp) a off) =>
      if ves is v :: VAL_int32 k :: ves' then
        if types_agree t v
        then
          expect
            (smem_ind s f.(f_inst))
            (fun j =>
               if List.nth_error s.(s_mems) j is Some mem_s_j then
                 expect
                   (store_packed mem_s_j (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp))
                   (fun mem' =>
                      let s' := upd_s_mem s (update_list_at s.(s_mems) j mem') in
                      (RS'_normal (admitted_TODO (reduce hs s f es0 hs s' f (vs_to_es ves')))))
                   (RS'_normal (admitted_TODO (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_trap]))))
               else RS'_error _ _ (admitted_TODO _))
            (RS'_error _ _ (admitted_TODO _))
        else RS'_error _ _ (admitted_TODO _)
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic BI_current_memory =>
      expect
        (smem_ind s f.(f_inst))
        (fun j =>
           if List.nth_error s.(s_mems) j is Some s_mem_s_j then
             RS'_normal
             (admitted_TODO (reduce hs s f es0 hs s f (vs_to_es (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j))) :: ves))))
           else RS'_error _ _ (admitted_TODO _))
        (RS'_error _ _ (admitted_TODO _))
    | AI_basic BI_grow_memory =>
      if ves is VAL_int32 c :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
            if List.nth_error s.(s_mems) j is Some s_mem_s_j then
              let: l := mem_size s_mem_s_j in
              let: mem' := mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m c) in
              if mem' is Some mem'' then
                let s' := upd_s_mem s (update_list_at s.(s_mems) j mem'') in
                RS'_normal (admitted_TODO
                 (reduce hs s f es0 hs s' f (vs_to_es (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat l)) :: ves'))))
              else RS'_error _ _ (admitted_TODO _)
            else RS'_error _ _ (admitted_TODO _))
          (RS'_error _ _ (admitted_TODO _))
      else RS'_error _ _ (admitted_TODO _)
    | AI_basic (BI_const _) => RS'_error _ _ (admitted_TODO _)
    | AI_invoke a =>
      match List.nth_error s.(s_funcs) a with
      | Some cl => 
        match cl with
        | FC_func_native i (Tf t1s t2s) ts es =>
            let: n := length t1s in
            let: m := length t2s in
            if length ves >= n
            then
            let: (ves', ves'') := split_n ves n in
            let: zs := n_zeros ts in
            RS'_normal (admitted_TODO (reduce hs s f es0 hs s f
              (vs_to_es ves'' ++ [::AI_local m (Build_frame (rev ves' ++ zs) i) [::AI_basic (BI_block (Tf [::] t2s) es)]])))
            else RS'_error _ _ (admitted_TODO _)
        | FC_func_host (Tf t1s t2s) cl' =>
            let: n := length t1s in
            let: m := length t2s in
            if length ves >= n
            then
            let: (ves', ves'') := split_n ves n in
            match host_application_impl hs s (Tf t1s t2s) cl' (rev ves') with
            | (hs', Some (s', rves)) =>
                RS'_normal (admitted_TODO
                  (reduce hs s f es0 hs' s' f (vs_to_es ves'' ++ (result_to_stack rves))))
            | (hs', None) => RS'_normal (admitted_TODO
                (reduce hs s f es0 hs' s f (vs_to_es ves ++ [::AI_invoke a])))
            end
            else RS'_error _ _ (admitted_TODO _)
        end
      | None => RS'_error _ _ (admitted_TODO _)
      end
    | AI_label ln les es =>
      if es_is_trap es
      then RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves ++ [::AI_trap])))
      else
        if const_list es
        then RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves ++ es)))
        else
          match run_step_with_fuel' hs s f es fuel d with
          | RS'_break hs' s' f' 0 bvs =>
            if length bvs >= ln
            then RS'_normal (admitted_TODO
              (reduce hs s f es0 hs' s' f' ((vs_to_es ((take ln bvs) ++ ves)) ++ les)))
            else RS'_error _ _ (admitted_TODO _)
          | RS'_break hs' s' f' (n.+1) bvs => RS'_break _ _ _ _ hs' s' f' n bvs
          | RS'_return hs' s' f' rvs => RS'_return _ _ _ _ hs' s' f' rvs
          | RS'_normal hs' s' f' es' _ =>
            RS'_normal (admitted_TODO
              (reduce hs s f es0 hs' s' f' (vs_to_es ves ++ [::AI_label ln les es'])))
          | RS'_error _ => RS'_error _ _ (admitted_TODO _)
          | RS'_exhaustion => RS'_exhaustion _ _ _ _
          end
    | AI_local ln lf es =>
      if es_is_trap es
      then RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves ++ [::AI_trap])))
      else
        if const_list es
        then
          if length es == ln
          then RS'_normal (admitted_TODO
                 (reduce hs s f es0 hs s f (vs_to_es ves ++ es)))
          else RS'_error _ _ (admitted_TODO _)
        else
          match run_step_with_fuel' hs s f es fuel d with
          | RS'_return hs' s' f' rvs =>
            if length rvs >= ln
            then RS'_normal (admitted_TODO
              (reduce hs s f es0 hs' s' f (vs_to_es (take ln rvs ++ ves))))
            else RS'_error _ _ (admitted_TODO _)
          | RS'_normal hs' s' f' es' _ =>
            RS'_normal (admitted_TODO
              (reduce hs s f es0 hs' s' f (vs_to_es ves ++ [::AI_local ln f' es'])))
          | RS'_error _ => RS'_error _ _ (admitted_TODO _)
          | RS'_exhaustion => RS'_exhaustion _ _ _ _
          | RS'_break _ _ _ _ _ => RS'_error _ _ (admitted_TODO _)
          end
    | AI_trap => RS'_error _ _ (admitted_TODO _)
    end
  end.

Theorem run_step_with_fuel'' hs s f es (fuel : fuel) (d : depth) : res_step' hs s f es
with run_one_step'' hs s f ves e (fuel : fuel) (d : depth) : res_step' hs s f ((vs_to_es ves) ++ [::e]).
(* TODO should use res_step'_separate_e *)
Proof.
  (* NOTE: not indenting the two main subgoals *)
  (* run_step_with_fuel'' *)
  destruct fuel as [|fuel].
  - (* 0 *)
    apply (RS'_exhaustion hs s f es).
  - (* fuel.+1 *)
    (** Framing out constants. **)
    destruct (split_vals_e es) as [ves es'] eqn:Heqes.
    destruct es' as [|e es''] eqn:Heqes'.
    * (* es' = [::] *)
      apply (RS'_error _ _ (admitted_TODO (~ exists C t, e_typing s C es t))).
    * (* es' = e :: es'' *)
      destruct (e_is_trap e).
      + destruct ((es'' != [::]) || (ves != [::])).
        -- apply <<hs, s, f, [::AI_trap]>>[admitted_TODO _].
        -- apply (RS'_error _ _ (admitted_TODO (~ exists C t, e_typing s C es t))).
      + remember (run_one_step'' hs s f (rev ves) e fuel d) as r.
        apply (if r is RS'_normal hs' s' f' es' _
          then <<hs', s', f', (es' ++ es'')>>[admitted_TODO _]
          else coerce_res _ r).

  (* run_one_step'' *)
  (* initial es, useful as an arg for reduce *)
  remember ((vs_to_es ves) ++ [::e]) as es0 eqn:Heqes0.
  destruct fuel as [|fuel].
  - (* 0 *)
    apply RS'_exhaustion.
  - (* fuel.+1 *)
    destruct e as [
      (* AI_basic *) [
      (* BI_unreachable *) |
      (* BI_nop *) |
      (* BI_drop *) |
      (* BI_select *) |
      (* BI_block (Tf t1s t2s) es *) [t1s t2s] es |
      (* BI_loop (Tf t1s t2s) es *) [t1s t2s] es |
      (* BI_if tf es1 es2 *) tf es1 es2 |
      (* BI_br j *) j |
      (* BI_br_if j *) j |
      (* BI_br_table js j *) js j |
      (* BI_return *) |
      (* BI_call j *) j |
      (* BI_call_indirect j *) j |
      (* BI_get_local j *) j |
      (* BI_set_local j *) j |
      (* BI_tee_local j *) j |
      (* BI_get_global j *) j |
      (* BI_set_global j *) j |
      (* BI_load t [Some (tp, sx)|None] a off *) t [[tp sx]|] a off |
      (* BI_store t [Some tp|None] a off *) t [tp|] a off |
      (* BI_current_memory *) |
      (* BI_grow_memory *) |
      (* BI_const _ *) |
      (* BI_unop t op *) t op |
      (* BI_binop t op *) t op |
      (* BI_testop _ testop *) ? testop |
      (* BI_relop t op *) t op |
      (* BI_cvtop t2 _ t1 sx *) t2 ? t1 sx ] |
      (* AI_trap *) |
      (* AI_invoke a *) a |
      (* AI_label ln les es *) ln les es |
      (* AI_local ln lf es *) ln lf es ].

    * (* AI_basic BI_unreachable *)
      give_up.
    * (* AI_basic BI_nop *)
      give_up.
    * (* AI_basic BI_drop *)
      give_up.
    * (* AI_basic BI_select *)
      give_up.
    * (* AI_basic (BI_block (Tf t1s t2s) es) *)
      give_up.
    * (* AI_basic (BI_loop (Tf t1s t2s) es) *)
      give_up.
    * (* AI_basic (BI_if tf es1 t2) *)
      give_up.
    * (* AI_basic (BI_br j) *)
      give_up.
    * (* AI_basic (BI_br_if j) *)
      give_up.
    * (* AI_basic (BI_br_table js j) *)
      give_up.
    * (* AI_basic BI_return *)
      give_up.
    * (* AI_basic (BI_call j) *)
      give_up.
    * (* AI_basic (BI_call_indirect j) *)
      give_up.
    * (* AI_basic (BI_get_local j) *)
      give_up.
    * (* AI_basic (BI_set_local j) *)
      give_up.
    * (* AI_basic (BI_tee_local j) *)
      give_up.
    * (* AI_basic (BI_get_global j) *)
      give_up.
    * (* AI_basic (BI_set_global j) *)
      give_up.
    * (* AI_basic (BI_load t (Some (tp, sx)) a off) *)
      give_up.
    * (* AI_basic (BI_load t None a off) *)
      give_up.
    * (* AI_basic (BI_store t (Some tp) a off) *)
      give_up.
    * (* AI_basic (BI_store t None a off) *)
      give_up.
    * (* AI_basic BI_current_memory *)
      give_up.
    * (* AI_basic BI_grow_memory *)
      give_up.
    * (* AI_basic (BI_const _) *)
      give_up.
    * (* AI_basic (BI_unop t op) *)
      destruct ves as [|v ves'] eqn:Heqves.
      + (* [::] *)
        assert (inst : instance). { give_up. (* TODO need an instance *) }
        (* TODO need to change return type to be able to apply RS''_error *)
        Check (@RS''_error hs s f ves _ inst (unop_error Heqves)).
        give_up.
      + (* v :: ves' *)
          Check reduce_unop.
        apply <<hs, s, f, vs_to_es (app_unop op v :: ves')>>[
          reduce_unop _ _ _ Heqes0
        ].
    * (* AI_basic (BI_binop t op) *)
      destruct ves as [|v2 [|v1 ves']] eqn:foobar.
      + (* [::] *)
        apply (RS'_error _ _ (admitted_TODO _)).
      + (* [:: v2] *)
        apply (RS'_error _ _ (admitted_TODO _)).
      + (* [:: v2, v1 & ves'] *)
        destruct (app_binop op v1 v2) as [v|] eqn:Heqapp.
        -- (* Some v *)
           apply <<hs, s, f, vs_to_es (v :: ves')>>[
             reduce_binop _ _ _ Heqes0 Heqapp
           ].
        -- (* None *)
           apply (RS'_error _ _ (admitted_TODO _)).
    * (* AI_basic (BI_testop _ testop) *) (* TODO match further *)
      give_up.
    * (* AI_basic (BI_relop t op) *)
      give_up.
    * (* AI_basic (BI_cvtop t2 _ t1 sx) *) (* TODO match further *)
      give_up.
    * (* AI_trap *)
      give_up.
    * (* AI_invoke a *)
      give_up.
    * (* AI_label ln les es *)
      give_up.
    * (* AI_local ln lf es *)
      give_up.
Admitted.

(***************************************)

Fixpoint run_step_with_fuel (fuel : fuel) (d : depth) (cfg : config_tuple) : res_tuple :=
  let: (hs, s, f, es) := cfg in
  match fuel with
  | 0 => (hs, s, f, RS_crash C_exhaustion)
  | fuel.+1 =>
    let: (ves, es') := split_vals_e es in (** Framing out constants. **)
    match es' with
    | [::] => (hs, s, f, crash_error)
    | e :: es'' =>
      if e_is_trap e
      then
        if (es'' != [::]) || (ves != [::])
        then (hs, s, f, RS_normal [::AI_trap])
        else (hs, s, f, crash_error)
      else
        let: (hs', s', f', r) := run_one_step fuel d (hs, s, f, (rev ves)) e in
        if r is RS_normal res
        then (hs', s', f', RS_normal (res ++ es''))
        else (hs', s', f', r)
    end
  end

with run_one_step (fuel : fuel) (d : depth) (cfg : config_one_tuple_without_e) (e : administrative_instruction) : res_tuple :=
  let: (hs, s, f, ves) := cfg in
  match fuel with
  | 0 => (hs, s, f, RS_crash C_exhaustion)
  | fuel.+1 =>
    match e with
    (* unop *)
    | AI_basic (BI_unop t op) =>
      if ves is v :: ves' then
        (hs, s, f, RS_normal (vs_to_es (app_unop op v :: ves')))
      else (hs, s, f, crash_error)
    (* binop *)
    | AI_basic (BI_binop t op) =>
      if ves is v2 :: v1 :: ves' then
        expect (app_binop op v1 v2)
               (fun v => (hs, s, f, RS_normal (vs_to_es (v :: ves'))))
               (hs, s, f, RS_normal ((vs_to_es ves') ++ [::AI_trap]))
      else (hs, s, f, crash_error)
    (* testops *)
    | AI_basic (BI_testop T_i32 testop) =>
      if ves is (VAL_int32 c) :: ves' then
        (hs, s, f, RS_normal (vs_to_es ((VAL_int32 (wasm_bool (@app_testop_i i32t testop c))) :: ves')))
      else (hs, s, f, crash_error)
    | AI_basic (BI_testop T_i64 testop) =>
      if ves is (VAL_int64 c) :: ves' then
        (hs, s, f, RS_normal (vs_to_es ((VAL_int32 (wasm_bool (@app_testop_i i64t testop c))) :: ves')))
      else (hs, s, f, crash_error)
    | AI_basic (BI_testop _ _) => (hs, s, f, crash_error)
    (* relops *)
    | AI_basic (BI_relop t op) =>
      if ves is v2 :: v1 :: ves' then
        (hs, s, f, RS_normal (vs_to_es (VAL_int32 (wasm_bool (app_relop op v1 v2)) :: ves')))
      else (hs, s, f, crash_error)
    (* convert & reinterpret *)
    | AI_basic (BI_cvtop t2 CVO_convert t1 sx) =>
      if ves is v :: ves' then
        if types_agree t1 v
        then
          expect (cvt t2 sx v) (fun v' =>
               (hs, s, f, RS_normal (vs_to_es (v' :: ves'))))
            (hs, s, f, RS_normal ((vs_to_es ves') ++ [::AI_trap]))
        else (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_cvtop t2 CVO_reinterpret t1 sx) =>
      if ves is v :: ves' then
        if types_agree t1 v && (sx == None)
        then (hs, s, f, RS_normal (vs_to_es (wasm_deserialise (bits v) t2 :: ves')))
        else (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    (**)
    | AI_basic BI_unreachable => (hs, s, f, RS_normal ((vs_to_es ves) ++ [::AI_trap]))
    | AI_basic BI_nop => (hs, s, f, RS_normal (vs_to_es ves))
    | AI_basic BI_drop =>
      if ves is v :: ves' then
        (hs, s, f, RS_normal (vs_to_es ves'))
      else (hs, s, f, crash_error)
    | AI_basic BI_select =>
      if ves is (VAL_int32 c) :: v2 :: v1 :: ves' then
        if c == Wasm_int.int_zero i32m
        then (hs, s, f, RS_normal (vs_to_es (v2 :: ves')))
        else (hs, s, f, RS_normal (vs_to_es (v1 :: ves')))
      else (hs, s, f, crash_error)
    | AI_basic (BI_block (Tf t1s t2s) es) =>
      if length ves >= length t1s
      then
        let: (ves', ves'')  := split_n ves (length t1s) in
        (hs, s, f, RS_normal (vs_to_es ves''
                ++ [::AI_label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)]))
      else (hs, s, f, crash_error)
    | AI_basic (BI_loop (Tf t1s t2s) es) =>
      if length ves >= length t1s
      then
        let: (ves', ves'') := split_n ves (length t1s) in
        (hs, s, f, RS_normal (vs_to_es ves''
                ++ [::AI_label (length t1s) [::AI_basic (BI_loop (Tf t1s t2s) es)]
                        (vs_to_es ves' ++ to_e_list es)]))
      else (hs, s, f, crash_error)
    | AI_basic (BI_if tf es1 es2) =>
      if ves is VAL_int32 c :: ves' then
        if c == Wasm_int.int_zero i32m
        then (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_block tf es2)]))
        else (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_block tf es1)]))
      else (hs, s, f, crash_error)
    | AI_basic (BI_br j) => (hs, s, f, RS_break j ves)
    | AI_basic (BI_br_if j) =>
      if ves is VAL_int32 c :: ves' then
        if c == Wasm_int.int_zero i32m
        then (hs, s, f, RS_normal (vs_to_es ves'))
        else (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br j)]))
      else (hs, s, f, crash_error)
    | AI_basic (BI_br_table js j) =>
      if ves is VAL_int32 c :: ves' then
        let: k := Wasm_int.nat_of_uint i32m c in
        if k < length js
        then
          expect (List.nth_error js k) (fun js_at_k =>
              (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br js_at_k)])))
            (hs, s, f, crash_error)
        else (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br j)]))
      else (hs, s, f, crash_error)
    | AI_basic (BI_call j) =>
      if List.nth_error f.(f_inst).(inst_funcs) j is Some a then
        (hs, s, f, RS_normal (vs_to_es ves ++ [::AI_invoke a]))
      else (hs, s, f, crash_error)
    | AI_basic (BI_call_indirect j) =>
      if ves is VAL_int32 c :: ves' then
        match stab_addr s f (Wasm_int.nat_of_uint i32m c) with
        | Some a =>
          match List.nth_error s.(s_funcs) a with
          | Some cl =>
            if stypes s f.(f_inst) j == Some (cl_type cl)
            then (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_invoke a]))
            else (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))        
          | None => (hs, s, f, crash_error)
          end
        | None => (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
        end
      else (hs, s, f, crash_error)
    | AI_basic BI_return => (hs, s, f, RS_return ves)
    | AI_basic (BI_get_local j) =>
      if j < length f.(f_locs)
      then
        expect (List.nth_error f.(f_locs) j) (fun vs_at_j =>
            (hs, s, f, RS_normal (vs_to_es (vs_at_j :: ves))))
          (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_set_local j) =>
      if ves is v :: ves' then
        if j < length f.(f_locs)
        then (hs, s, Build_frame (update_list_at f.(f_locs) j v) f.(f_inst), RS_normal (vs_to_es ves'))
        else (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_tee_local j) =>
      if ves is v :: ves' then
        (hs, s, f, RS_normal (vs_to_es (v :: ves) ++ [::AI_basic (BI_set_local j)]))
      else (hs, s, f, crash_error)
    | AI_basic (BI_get_global j) =>
      if sglob_val s f.(f_inst) j is Some xx
      then (hs, s, f, RS_normal (vs_to_es (xx :: ves)))
      else (hs, s, f, crash_error)
    | AI_basic (BI_set_global j) =>
      if ves is v :: ves' then
        if supdate_glob s f.(f_inst) j v is Some xx
        then (hs, xx, f, RS_normal (vs_to_es ves'))
        else (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_load t None a off) =>
      if ves is VAL_int32 k :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load (mem_s_j) (Wasm_int.N_of_uint i32m k) off (t_length t))
                 (fun bs => (hs, s, f, RS_normal (vs_to_es (wasm_deserialise bs t :: ves'))))
                 (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
             else (hs, s, f, crash_error))
          (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_load t (Some (tp, sx)) a off) =>
      if ves is VAL_int32 k :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load_packed sx (mem_s_j) (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t))
                 (fun bs => (hs, s, f, RS_normal (vs_to_es (wasm_deserialise bs t :: ves'))))
                 (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
             else (hs, s, f, crash_error))
          (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_store t None a off) =>
      if ves is v :: VAL_int32 k :: ves' then
        if types_agree t v
        then
          expect
            (smem_ind s f.(f_inst))
            (fun j =>
               if List.nth_error s.(s_mems) j is Some mem_s_j then
                 expect
                   (store mem_s_j (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t))
                   (fun mem' =>
                      (hs, upd_s_mem s (update_list_at s.(s_mems) j mem'), f, RS_normal (vs_to_es ves')))
                   (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
               else (hs, s, f, crash_error))
            (hs, s, f, crash_error)
        else (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_store t (Some tp) a off) =>
      if ves is v :: VAL_int32 k :: ves' then
        if types_agree t v
        then
          expect
            (smem_ind s f.(f_inst))
            (fun j =>
               if List.nth_error s.(s_mems) j is Some mem_s_j then
                 expect
                   (store_packed mem_s_j (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp))
                   (fun mem' =>
                      (hs, upd_s_mem s (update_list_at s.(s_mems) j mem'), f, RS_normal (vs_to_es ves')))
                   (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
               else (hs, s, f, crash_error))
            (hs, s, f, crash_error)
        else (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic BI_current_memory =>
      expect
        (smem_ind s f.(f_inst))
        (fun j =>
           if List.nth_error s.(s_mems) j is Some s_mem_s_j then
             (hs, s, f, RS_normal (vs_to_es (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j))) :: ves)))
           else (hs, s, f, crash_error))
        (hs, s, f, crash_error)
    | AI_basic BI_grow_memory =>
      if ves is VAL_int32 c :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
            if List.nth_error s.(s_mems) j is Some s_mem_s_j then
              let: l := mem_size s_mem_s_j in
              let: mem' := mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m c) in
              if mem' is Some mem'' then
                (hs, upd_s_mem s (update_list_at s.(s_mems) j mem''), f,
                 RS_normal (vs_to_es (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat l)) :: ves')))
              else (hs, s, f, crash_error)
            else (hs, s, f, crash_error))
          (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_const _) => (hs, s, f, crash_error)
    | AI_invoke a =>
      match List.nth_error s.(s_funcs) a with
      | Some cl => 
        match cl with
        | FC_func_native i (Tf t1s t2s) ts es =>
            let: n := length t1s in
            let: m := length t2s in
            if length ves >= n
            then
            let: (ves', ves'') := split_n ves n in
            let: zs := n_zeros ts in
            (hs, s, f, RS_normal (vs_to_es ves''
                    ++ [::AI_local m (Build_frame (rev ves' ++ zs) i) [::AI_basic (BI_block (Tf [::] t2s) es)]]))
            else (hs, s, f, crash_error)
        | FC_func_host (Tf t1s t2s) cl' =>
            let: n := length t1s in
            let: m := length t2s in
            if length ves >= n
            then
            let: (ves', ves'') := split_n ves n in
            match host_application_impl hs s (Tf t1s t2s) cl' (rev ves') with
            | (hs', Some (s', rves)) =>
                (hs', s', f, RS_normal (vs_to_es ves'' ++ (result_to_stack rves)))
            | (hs', None) => (hs', s, f, RS_normal (vs_to_es ves ++ [::AI_invoke a]))
            end
            else (hs, s, f, crash_error)
        end
      | None => (hs, s, f, crash_error)
      end
    | AI_label ln les es =>
      if es_is_trap es
      then (hs, s, f, RS_normal (vs_to_es ves ++ [::AI_trap]))
      else
        if const_list es
        then (hs, s, f, RS_normal (vs_to_es ves ++ es))
        else
          let: (hs', s', f', res) := run_step_with_fuel fuel d (hs, s, f, es) in
          match res with
          | RS_break 0 bvs =>
            if length bvs >= ln
            then (hs', s', f', RS_normal ((vs_to_es ((take ln bvs) ++ ves)) ++ les))
            else (hs', s', f', crash_error)
          | RS_break (n.+1) bvs => (hs', s', f', RS_break n bvs)
          | RS_return rvs => (hs', s', f', RS_return rvs)
          | RS_normal es' =>
            (hs', s', f', RS_normal (vs_to_es ves ++ [::AI_label ln les es']))
          | RS_crash error => (hs', s', f', RS_crash error)
          end
    | AI_local ln lf es =>
      if es_is_trap es
      then (hs, s, f, RS_normal (vs_to_es ves ++ [::AI_trap]))
      else
        if const_list es
        then
          if length es == ln
          then (hs, s, f, RS_normal (vs_to_es ves ++ es))
          else (hs, s, f, crash_error)
        else
          let: (hs', s', f', res) := run_step_with_fuel fuel d (hs, s, lf, es) in
          match res with
          | RS_return rvs =>
            if length rvs >= ln
            then (hs', s', f, RS_normal (vs_to_es (take ln rvs ++ ves)))
            else (hs', s', f, crash_error)
          | RS_normal es' =>
            (hs', s', f, RS_normal (vs_to_es ves ++ [::AI_local ln f' es']))
          | RS_crash error => (hs', s', f, RS_crash error)
          | RS_break _ _ => (hs', s', f, crash_error)
          end
    | AI_trap => (hs, s, f, crash_error)
    end
  end.

(** Enough fuel so that [run_one_step] does not run out of exhaustion. **)
Definition run_one_step_fuel : administrative_instruction -> nat.
Proof.
  move=> es. induction es using administrative_instruction_rect';
    let rec aux v :=
      lazymatch goal with
      | F : TProp.Forall _ _ |- _ =>
        apply TProp.max in F;
        move: F;
        let n := fresh "n" in
        move=> n;
        aux (n + v)
      | |- _ => exact (v.+1)
      end in
    aux (1 : nat).
Defined.

(** Enough fuel so that [run_step] does not run out of exhaustion. **)
Definition run_step_fuel (cfg : config_tuple) : nat :=
  let: (hs, s, f, es) := cfg in
  1 + List.fold_left max (List.map run_one_step_fuel es) 0.

Definition run_step (d : depth) (cfg : config_tuple) : res_tuple :=
  run_step_with_fuel (run_step_fuel cfg) d cfg.

Fixpoint run_v (fuel : fuel) (d : depth) (cfg : config_tuple) : ((host_state * store_record * res)%type) :=
  let: (hs, s, f, es) := cfg in
  match fuel with
  | 0 => (hs, s, R_crash C_exhaustion)
  | fuel.+1 =>
    if es_is_trap es
    then (hs, s, R_trap)
    else
      if const_list es
      then (hs, s, R_value (fst (split_vals_e es)))
      else
        let: (hs', s', f', res) := run_step d (hs, s, f, es) in
        match res with
        | RS_normal es' => run_v fuel d (hs', s', f', es')
        | RS_crash error => (hs', s', R_crash error)
        | _ => (hs', s', R_crash C_error)
        end
  end.

End Host_func.
