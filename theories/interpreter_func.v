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
 * see interpreter_func_sound. Should RS'_crash carry a proof of False? *)
Inductive res_step' : Type :=
| RS'_crash : res_crash -> res_step'
| RS'_break : nat -> list value -> res_step'
| RS'_return : list value -> res_step'
| RS'_normal
    (hs : host_state) (s : store_record) (f : frame)
    (es : list administrative_instruction)
    (hs' : host_state) (s' : store_record) (f' : frame)
    (es' : list administrative_instruction)
    : reduce hs s f es hs' s' f' es' -> res_step'.
(* No need to use a sigma type? *)

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
Definition crash_error' := RS'_crash C_error.

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

(* TODO there is some redundancy here,
 * hs,s,f are stored both in the tuple and in res_step' *)
Definition res_tuple' := (host_state * store_record * frame * res_step')%type.

(* TODO use that once res_step' finalised *)
(* Notation "<< hs' , s' , f' , es' >>[ H ]" := (hs', s', f', RS'_normal _ _ _ _ hs' s' f' es' H). *)

(* TODO auto instantiate lh, k? *)
(* TODO better name *)
Ltac solve_lfilled_0 :=
  unfold lfilled, lfill, vs_to_es;
  try rewrite v_to_e_is_const_list; apply/eqP; simplify_lists => //.

(* NOTE: could've added something like `ves = v :: ves'` (similarly for es0),
 * but having to supply a proof of that in non-proof mode would be annoying *)
Lemma reduce_unop : forall (hs : host_state) s f t op v ves',
  reduce hs s f ((vs_to_es (v :: ves')) ++ [::AI_basic (BI_unop t op)]) hs s f (vs_to_es (app_unop op v :: ves')).
Proof.
  intros hs s f t op v ves'.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::])).
  - apply r_simple. by apply rs_unop.
  - by solve_lfilled_0.
  - by solve_lfilled_0.
Qed.

Lemma reduce_binop : forall (hs : host_state) s f t op v1 v2 v ves',
  app_binop op v1 v2 = Some v ->
  reduce hs s f ((vs_to_es (v2 :: v1 :: ves')) ++ [::AI_basic (BI_binop t op)]) hs s f (vs_to_es (v :: ves')).
Proof.
  intros hs s f t op v1 v2 v ves' Hv.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::])).
  - apply r_simple.
    apply rs_binop_success.
    by apply Hv.
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

Lemma reduce_binop' : forall (hs : host_state) s f t2 op v1 v2 ves',
  (exists t1, config_tuple_typing (hs, s, f, ((vs_to_es (v2 :: v1 :: ves')) ++ [::AI_basic (BI_binop t2 op)])) t1) ->
  exists v, reduce hs s f ((vs_to_es (v2 :: v1 :: ves')) ++ [::AI_basic (BI_binop t2 op)]) hs s f (vs_to_es (v :: ves')).
Proof.
  intros ???????? [t1 Htype].
  apply binop_typing_inversion in Htype as [v Hv].
  exists v. apply reduce_binop. by apply Hv.
Qed.

(* XXX be_typing instead? *)
Fixpoint run_step_with_fuel' (fuel : fuel) (d : depth) (cfg : config_tuple) (Htype : exists t, config_tuple_typing cfg t) : res_tuple' :=
  let: (hs, s, f, es) := cfg in
  match fuel with
  | 0 => (hs, s, f, RS'_crash C_exhaustion)
  | fuel.+1 =>
    let: (ves, es') := split_vals_e es in (** Framing out constants. **)
    match es' with
    | [::] => (hs, s, f, crash_error')
    | e :: es'' =>
      if e_is_trap e
      then
        if (es'' != [::]) || (ves != [::])
        then (hs, s, f, RS'_normal (admitted_TODO (reduce hs s f es hs s f [::AI_trap])))
        else (hs, s, f, crash_error')
      else
        let: cfg'             := (hs, s, f, (rev ves)) in
        (* TODO: this will need some proof of (es = (rev ves) ++ [::e] ++ es'')
         * or similar, not sure how that will work*)
        let: Htype'           := admitted_TODO (exists t, config_tuple_separate_e_typing cfg' e t) in
        let: (hs', s', f', r) := run_one_step' fuel d Htype'
                                   in
        if r is RS'_normal _ _ _ _ _ _ _ res _ (* TODO *)
        then (hs', s', f', RS'_normal (admitted_TODO (reduce hs s f es hs' s' f' (res ++ es''))))
        else (hs', s', f', r)
    end
  end

with run_one_step' (fuel : fuel) (d : depth) (cfg : config_one_tuple_without_e) (e : administrative_instruction) (Htype : exists t, config_tuple_separate_e_typing cfg e t) : res_tuple' :=
  let: (hs, s, f, ves) := cfg in
  let: es0 := (vs_to_es ves) ++ [::e] in (* initial es, useful as an arg for reduce *)
  match fuel with
  | 0 => (hs, s, f, RS'_crash C_exhaustion)
  | fuel.+1 =>
    match e with
    (* unop *)
    | AI_basic (BI_unop t op) =>
      if ves is v :: ves' then
        (hs, s, f, RS'_normal (reduce_unop hs s f t op v ves'))
      else (hs, s, f, crash_error')
    (* binop *)
    | AI_basic (BI_binop t op) =>
      if ves is v2 :: v1 :: ves' then
        let vo := app_binop op v1 v2 in
        match vo as vo0 return (vo = vo0) -> res_tuple' with
        | Some v =>
               fun eq_vo => (hs, s, f, RS'_normal (reduce_binop hs s f t ves' eq_vo))
        | None =>
               (* TODO to get proof of False here:
                * get proof of `app_binop op v1 v2 = None` from the match
                * get proof of `app_binop op v1 v2 = Some v` from typing inversion *)
            (*
               lemma :
               config_typing es t ->
               app_binop op ... = None ->
               False
               app_binop op ... = None ->
               config_typing es t ->
               False
             *)
               fun _ => (False_rect res_tuple' (admitted_TODO False))
        end (Logic.eq_refl vo)
      else (hs, s, f, crash_error')
    (* testops *)
    | AI_basic (BI_testop T_i32 testop) =>
      if ves is (VAL_int32 c) :: ves' then
        (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ((VAL_int32 (wasm_bool (@app_testop_i i32t testop c))) :: ves')))))
      else (hs, s, f, crash_error')
    | AI_basic (BI_testop T_i64 testop) =>
      if ves is (VAL_int64 c) :: ves' then
        (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ((VAL_int32 (wasm_bool (@app_testop_i i64t testop c))) :: ves')))))
      else (hs, s, f, crash_error')
    | AI_basic (BI_testop _ _) => (hs, s, f, crash_error')
    (* relops *)
    | AI_basic (BI_relop t op) =>
      if ves is v2 :: v1 :: ves' then
        (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es (VAL_int32 (wasm_bool (app_relop op v1 v2)) :: ves')))))
      else (hs, s, f, crash_error')
    (* convert & reinterpret *)
    | AI_basic (BI_cvtop t2 CVO_convert t1 sx) =>
      if ves is v :: ves' then
        if types_agree t1 v
        then
          expect (cvt t2 sx v) (fun v' =>
               (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es (v' :: ves'))))))
            (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f ((vs_to_es ves') ++ [::AI_trap]))))
        else (hs, s, f, crash_error')
      else (hs, s, f, crash_error')
    | AI_basic (BI_cvtop t2 CVO_reinterpret t1 sx) =>
      if ves is v :: ves' then
        if types_agree t1 v && (sx == None)
        then (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es (wasm_deserialise (bits v) t2 :: ves')))))
        else (hs, s, f, crash_error')
      else (hs, s, f, crash_error')
    (**)
    | AI_basic BI_unreachable => (hs, s, f, RS'_normal (admitted_TODO
        (reduce hs s f es0 hs s f ((vs_to_es ves) ++ [::AI_trap]))))
    | AI_basic BI_nop => (hs, s, f, RS'_normal (admitted_TODO
        (reduce hs s f es0 hs s f (vs_to_es ves))))
    | AI_basic BI_drop =>
      if ves is v :: ves' then
        (hs, s, f, RS'_normal (admitted_TODO
        (reduce hs s f es0 hs s f (vs_to_es ves'))))
      else (hs, s, f, crash_error')
    | AI_basic BI_select =>
      if ves is (VAL_int32 c) :: v2 :: v1 :: ves' then
        if c == Wasm_int.int_zero i32m
        then (hs, s, f, RS'_normal (admitted_TODO
          (reduce hs s f es0 hs s f (vs_to_es (v2 :: ves')))))
        else (hs, s, f, RS'_normal (admitted_TODO
          (reduce hs s f es0 hs s f (vs_to_es (v1 :: ves')))))
      else (hs, s, f, crash_error')
    | AI_basic (BI_block (Tf t1s t2s) es) =>
      if length ves >= length t1s
      then
        let: (ves', ves'')  := split_n ves (length t1s) in
        (hs, s, f, RS'_normal (admitted_TODO
          (reduce hs s f es0 hs s f
            (vs_to_es ves'' ++ [::AI_label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)])
        )))
      else (hs, s, f, crash_error')
    | AI_basic (BI_loop (Tf t1s t2s) es) =>
      if length ves >= length t1s
      then
        let: (ves', ves'') := split_n ves (length t1s) in
        (hs, s, f, RS'_normal (admitted_TODO
          (reduce hs s f es0 hs s f
            (vs_to_es ves''
                    ++ [::AI_label (length t1s) [::AI_basic (BI_loop (Tf t1s t2s) es)]
                            (vs_to_es ves' ++ to_e_list es)])
        )))
      else (hs, s, f, crash_error')
    | AI_basic (BI_if tf es1 es2) =>
      if ves is VAL_int32 c :: ves' then
        if c == Wasm_int.int_zero i32m
        then (hs, s, f, RS'_normal (admitted_TODO
        (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_basic (BI_block tf es2)]))))
        else (hs, s, f, RS'_normal (admitted_TODO 
        (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_basic (BI_block tf es1)]))))
      else (hs, s, f, crash_error')
    | AI_basic (BI_br j) => (hs, s, f, RS'_break j ves)
    | AI_basic (BI_br_if j) =>
      if ves is VAL_int32 c :: ves' then
        if c == Wasm_int.int_zero i32m
        then (hs, s, f, RS'_normal (admitted_TODO
        (reduce hs s f es0 hs s f (vs_to_es ves'))))
        else (hs, s, f, RS'_normal (admitted_TODO
        (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_basic (BI_br j)]))))
      else (hs, s, f, crash_error')
    | AI_basic (BI_br_table js j) =>
      if ves is VAL_int32 c :: ves' then
        let: k := Wasm_int.nat_of_uint i32m c in
        if k < length js
        then
          expect (List.nth_error js k) (fun js_at_k =>
              (hs, s, f, RS'_normal (admitted_TODO
                (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_basic (BI_br js_at_k)])))))
            (hs, s, f, crash_error')
        else (hs, s, f, RS'_normal (admitted_TODO
               (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_basic (BI_br j)]))))
      else (hs, s, f, crash_error')
    | AI_basic (BI_call j) =>
      if List.nth_error f.(f_inst).(inst_funcs) j is Some a then
        (hs, s, f, RS'_normal (admitted_TODO
          (reduce hs s f es0 hs s f (vs_to_es ves ++ [::AI_invoke a]))))
      else (hs, s, f, crash_error')
    | AI_basic (BI_call_indirect j) =>
      if ves is VAL_int32 c :: ves' then
        match stab_addr s f (Wasm_int.nat_of_uint i32m c) with
        | Some a =>
          match List.nth_error s.(s_funcs) a with
          | Some cl =>
            if stypes s f.(f_inst) j == Some (cl_type cl)
            then (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_invoke a]))))
            else (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_trap]))))
          | None => (hs, s, f, crash_error')
          end
        | None => (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_trap]))))
        end
      else (hs, s, f, crash_error')
    | AI_basic BI_return => (hs, s, f, RS'_return ves)
    | AI_basic (BI_get_local j) =>
      if j < length f.(f_locs)
      then
        expect (List.nth_error f.(f_locs) j) (fun vs_at_j =>
            (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es (vs_at_j :: ves))))))
          (hs, s, f, crash_error')
      else (hs, s, f, crash_error')
    | AI_basic (BI_set_local j) =>
      if ves is v :: ves' then
        if j < length f.(f_locs)
        then
          let f' := Build_frame (update_list_at f.(f_locs) j v) f.(f_inst) in
          (hs, s, f', RS'_normal (admitted_TODO
            (reduce hs s f es0 hs s f' (vs_to_es ves'))))
        else (hs, s, f, crash_error')
      else (hs, s, f, crash_error')
    | AI_basic (BI_tee_local j) =>
      if ves is v :: ves' then
        (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es (v :: ves) ++ [::AI_basic (BI_set_local j)]))))
      else (hs, s, f, crash_error')
    | AI_basic (BI_get_global j) =>
      if sglob_val s f.(f_inst) j is Some xx
      then (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es (xx :: ves)))))
      else (hs, s, f, crash_error')
    | AI_basic (BI_set_global j) =>
      if ves is v :: ves' then
        if supdate_glob s f.(f_inst) j v is Some xx
        then (hs, xx, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves'))))
        else (hs, s, f, crash_error')
      else (hs, s, f, crash_error')
    | AI_basic (BI_load t None a off) =>
      if ves is VAL_int32 k :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load (mem_s_j) (Wasm_int.N_of_uint i32m k) off (t_length t))
                 (fun bs => (hs, s, f, RS'_normal (admitted_TODO
                   (reduce hs s f es0 hs s f (vs_to_es (wasm_deserialise bs t :: ves'))))))
                 (hs, s, f, RS'_normal (admitted_TODO
                   (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_trap]))))
             else (hs, s, f, crash_error'))
          (hs, s, f, crash_error')
      else (hs, s, f, crash_error')
    | AI_basic (BI_load t (Some (tp, sx)) a off) =>
      if ves is VAL_int32 k :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load_packed sx (mem_s_j) (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t))
                 (fun bs => (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es (wasm_deserialise bs t :: ves'))))))
                 (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_trap]))))
             else (hs, s, f, crash_error'))
          (hs, s, f, crash_error')
      else (hs, s, f, crash_error')
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
                      (hs, s', f, RS'_normal (admitted_TODO
                        (reduce hs s f es0 hs s f (vs_to_es ves')))))
                   (hs, s, f, RS'_normal (admitted_TODO
                     (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_trap]))))
               else (hs, s, f, crash_error'))
            (hs, s, f, crash_error')
        else (hs, s, f, crash_error')
      else (hs, s, f, crash_error')
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
                      (hs, s', f, RS'_normal (admitted_TODO
                         (reduce hs s f es0 hs s' f (vs_to_es ves')))))
                   (hs, s, f, RS'_normal (admitted_TODO
                      (reduce hs s f es0 hs s f (vs_to_es ves' ++ [::AI_trap]))))
               else (hs, s, f, crash_error'))
            (hs, s, f, crash_error')
        else (hs, s, f, crash_error')
      else (hs, s, f, crash_error')
    | AI_basic BI_current_memory =>
      expect
        (smem_ind s f.(f_inst))
        (fun j =>
           if List.nth_error s.(s_mems) j is Some s_mem_s_j then
             (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j))) :: ves)))))
           else (hs, s, f, crash_error'))
        (hs, s, f, crash_error')
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
                (hs, s', f,
                 RS'_normal (admitted_TODO
                 (reduce hs s f es0 hs s' f (vs_to_es (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat l)) :: ves')))))
              else (hs, s, f, crash_error')
            else (hs, s, f, crash_error'))
          (hs, s, f, crash_error')
      else (hs, s, f, crash_error')
    | AI_basic (BI_const _) => (hs, s, f, crash_error')
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
            (hs, s, f, RS'_normal (admitted_TODO (reduce hs s f es0 hs s f
              (vs_to_es ves'' ++ [::AI_local m (Build_frame (rev ves' ++ zs) i) [::AI_basic (BI_block (Tf [::] t2s) es)]]))))
            else (hs, s, f, crash_error')
        | FC_func_host (Tf t1s t2s) cl' =>
            let: n := length t1s in
            let: m := length t2s in
            if length ves >= n
            then
            let: (ves', ves'') := split_n ves n in
            match host_application_impl hs s (Tf t1s t2s) cl' (rev ves') with
            | (hs', Some (s', rves)) =>
                (hs', s', f, RS'_normal (admitted_TODO
                  (reduce hs s f es0 hs' s' f (vs_to_es ves'' ++ (result_to_stack rves)))))
            | (hs', None) => (hs', s, f, RS'_normal (admitted_TODO
                (reduce hs s f es0 hs' s f (vs_to_es ves ++ [::AI_invoke a]))))
            end
            else (hs, s, f, crash_error')
        end
      | None => (hs, s, f, crash_error')
      end
    | AI_label ln les es =>
      if es_is_trap es
      then (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves ++ [::AI_trap]))))
      else
        if const_list es
        then (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves ++ es))))
        else
          let: (hs', s', f', res) := run_step_with_fuel' fuel d (admitted_TODO (exists t, config_tuple_typing (hs, s, f, es) t)) in
          match res with
          | RS'_break 0 bvs =>
            if length bvs >= ln
            then (hs', s', f', RS'_normal (admitted_TODO
              (reduce hs s f es0 hs' s' f' ((vs_to_es ((take ln bvs) ++ ves)) ++ les))))
            else (hs', s', f', crash_error')
          | RS'_break (n.+1) bvs => (hs', s', f', RS'_break n bvs)
          | RS'_return rvs => (hs', s', f', RS'_return rvs)
          | RS'_normal _ _ _ _ _ _ _ es' _ =>
            (hs', s', f', RS'_normal (admitted_TODO
              (reduce hs s f es0 hs' s' f' (vs_to_es ves ++ [::AI_label ln les es']))))
          | RS'_crash error => (hs', s', f', RS'_crash error)
          end
    | AI_local ln lf es =>
      if es_is_trap es
      then (hs, s, f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs s f (vs_to_es ves ++ [::AI_trap]))))
      else
        if const_list es
        then
          if length es == ln
          then (hs, s, f, RS'_normal (admitted_TODO
                 (reduce hs s f es0 hs s f (vs_to_es ves ++ es))))
          else (hs, s, f, crash_error')
        else
          let: (hs', s', f', res) := run_step_with_fuel' fuel d (admitted_TODO (exists t, config_tuple_typing (hs, s, lf, es) t)) in
          match res with
          | RS'_return rvs =>
            if length rvs >= ln
            then (hs', s', f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs' s' f (vs_to_es (take ln rvs ++ ves)))))
            else (hs', s', f, crash_error')
          | RS'_normal _ _ _ _ _ _ _ es' _ =>
            (hs', s', f, RS'_normal (admitted_TODO
              (reduce hs s f es0 hs' s' f (vs_to_es ves ++ [::AI_local ln f' es']))))
          | RS'_crash error => (hs', s', f, RS'_crash error)
          | RS'_break _ _ => (hs', s', f, crash_error')
          end
    | AI_trap => (hs, s, f, crash_error')
    end
  end.

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
