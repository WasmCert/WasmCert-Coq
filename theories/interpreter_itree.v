(** Wasm interpreter using Itree **)
(* File currently not in use for extraction *)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Wasm Require Import common.
From Coq Require Import ZArith.BinInt.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From ExtLib Require Import Structures.Monad.
From ITree Require Import ITree ITreeFacts.
From Wasm Require Export operations host.

Import Monads.
Import MonadNotation.

Open Scope monad_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

Definition depth : Type := nat.

Section Host.

Variable host_function : eqType.
  
Let config_tuple := config_tuple host_function.
Let store_record := store_record host_function.

Let executable_host := executable_host host_function.
Variable executable_host_instance : executable_host.
Let host_event := host_event executable_host_instance.

Let host_monad : Monad host_event := host_monad executable_host_instance.
Let host_apply : store_record -> function_type -> host_function -> seq value ->
                 host_event (option (store_record * result)) :=
  @host_apply _ executable_host_instance.


Section ITreeExtract.
(** Some helper functions to extract an interactive tree to a simple-to-interact-with function,
  in order to reduce the shim. **)

Definition option_of_itree_void {A} (t : itree void1 A) : option A :=
  match observe t with
  | RetF r => Some r (** We got a return. **)
  | TauF i => None (** Exhaustion. **)
  | VisF _ a _ => match a with end (** Void, by definition. **)
  end.

Context {R : Type}.
(** We assume an interpreter, as defined by the end of this file. **)
Variable run : forall (eff : Type -> Type),
  host_event -< eff -> depth -> instance -> config_tuple -> itree eff R.

Variable M : Type -> Type.
Hypothesis FM : Functor.Functor M.
Hypothesis MM : Monad M.
Hypothesis IM : MonadIter M.
Variable convert : host_event ~> M.

Definition from_event_monad : itree host_event ~> M :=
  interp convert.

(** This function instantiates the interpreter [run] to a function that does not
  manipulate interaction trees, making it easier to link it to the OCaml shim. **)
Definition run_extraction d i cfg : M R :=
  from_event_monad (run _ d i cfg).

End ITreeExtract.

(** Some types used in the interpreter. **)
Definition config_one_tuple_without_e : Type := store_record * frame * list value.

Inductive res_crash : Type :=
  | C_error : res_crash
  .

Inductive res_step : Type :=
  | RS_crash : res_crash -> res_step
  | RS_break : nat -> seq value -> res_step
  | RS_return : seq value -> res_step
  | RS_normal : seq administrative_instruction -> res_step
  .

Definition res_tuple : Type := store_record * frame * res_step.

Scheme Equality for res_crash.
Definition res_crash_eqb c1 c2 := is_left (res_crash_eq_dec c1 c2).
Definition eqres_crashP : Equality.axiom res_crash_eqb :=
  eq_dec_Equality_axiom res_crash_eq_dec.

Canonical Structure res_crash_eqMixin := EqMixin eqres_crashP.
Canonical Structure res_crash_eqType := Eval hnf in EqType res_crash res_crash_eqMixin.

Definition res_step_eq_dec : forall r1 r2 : res_step, {r1 = r2} + {r1 <> r2}.
Proof.
  (decidable_equality_step;
    last by apply: (eq_comparable (_ : seq administrative_instruction)));
    decidable_equality.
Defined.

Definition res_step_eqb (r1 r2 : res_step) : bool := res_step_eq_dec r1 r2.
Definition eqres_stepP : Equality.axiom res_step_eqb :=
  eq_dec_Equality_axiom res_step_eq_dec.

Canonical Structure res_step_eqMixin := EqMixin eqres_stepP.
Canonical Structure res_step_eqType := Eval hnf in EqType res_step res_step_eqMixin.


(** * Types used by the interpreter **)

Inductive res : Type :=
  | R_crash : res_crash -> res
  | R_trap : res
  | R_value : seq value -> res
  .

Definition res_eq_dec : forall r1 r2 : res, {r1 = r2} + {r1 <> r2}.
Proof. decidable_equality. Defined.

Definition res_eqb (r1 r2 : res) : bool := res_eq_dec r1 r2.
Definition eqresP : Equality.axiom res_eqb :=
  eq_dec_Equality_axiom res_eq_dec.

Canonical Structure res_eqMixin := EqMixin eqresP.
Canonical Structure res_eqType := Eval hnf in EqType res res_eqMixin.

Definition crash_error : res_step := RS_crash C_error.


(** * The interpreter itself. **)

(** An inductive for the [mrec] fixed-point combinator, expressing the signature of the
   functions [run_step_base] and [run_one_step]. **)
Inductive run_stepE : Type -> Type :=
  | call_run_step_base :
    depth -> config_tuple ->
    run_stepE res_tuple
  | call_run_one_step :
    depth -> config_one_tuple_without_e -> administrative_instruction ->
    run_stepE res_tuple
  .

Section RunStep.

(** See ITree/tutorial/Imp.v: these commands are used to enable other events to be mangled in. **)
Context {eff : Type -> Type}.
Context {eff_has_host_event : host_event -< eff}.

Definition run_step_base (call : run_stepE ~> itree (run_stepE +' eff))
    (d : depth) (cgf : config_tuple)
  : itree (run_stepE +' eff) res_tuple :=
  let: (s, f, es) := cgf in
  let: (ves, es') := split_vals_e es in (** Framing out constants. **)
  match es' with
  | [::] => ret (s, f, crash_error)
  | e :: es'' =>
    if e_is_trap e
    then
      if (es'' != [::]) || (ves != [::])
      then ret (s, f, RS_normal [::AI_trap])
      else ret (s, f, crash_error)
    else
      '(s', f', r) <- call _ (call_run_one_step d (s, f, (rev ves)) e) ;;
      if r is RS_normal res
      then ret (s', f', RS_normal (res ++ es''))
      else ret (s', f', r)
  end.

Definition run_one_step (call : run_stepE ~> itree (run_stepE +' eff))
      (d : depth) (cgf : config_one_tuple_without_e) (e : administrative_instruction)
    : itree (run_stepE +' eff) res_tuple :=
  let: (s, f, ves) := cgf in
  match e with

  (** unop **)
  | AI_basic (BI_unop t op) =>
    if ves is v :: ves' then
      ret (s, f, RS_normal (vs_to_es ((app_unop op v) :: ves')))
    else ret (s, f, crash_error)
             
  (** binop **)
  | AI_basic (BI_binop t op) =>
    if ves is v2 :: v1 :: ves' then
      expect (app_binop op v1 v2)
             (fun v => ret (s, f, RS_normal (vs_to_es (v :: ves'))))
             (ret (s, f, RS_normal ((vs_to_es ves') ++ [::AI_trap])))
    else ret (s, f, crash_error)
          
  (** testops **)
  | AI_basic (BI_testop T_i32 testop) =>
    if ves is (VAL_int32 c) :: ves' then
      ret (s, f, RS_normal (vs_to_es ((VAL_int32 (wasm_bool (@app_testop_i i32t testop c))) :: ves')))
    else ret (s, f, crash_error)
  | AI_basic (BI_testop T_i64 testop) =>
    if ves is (VAL_int64 c) :: ves' then
      ret (s, f, RS_normal (vs_to_es ((VAL_int32 (wasm_bool (@app_testop_i i64t testop c))) :: ves')))
    else ret (s, f, crash_error)
  | AI_basic (BI_testop _ _) => ret (s, f, crash_error)

  (** relops **)
  | AI_basic (BI_relop t op) =>
    if ves is v2 :: v1 :: ves' then
      ret (s, f, RS_normal (vs_to_es (VAL_int32 (wasm_bool (app_relop op v1 v2)) :: ves')))
    else ret (s, f, crash_error)
             
  (** convert and reinterpret **)
  | AI_basic (BI_cvtop t2 CVO_convert t1 sx) =>
    if ves is v :: ves' then
      if types_agree t1 v
      then
        expect (cvt t2 sx v) (fun v' =>
             ret (s, f, RS_normal (vs_to_es (v' :: ves'))))
          (ret (s, f, RS_normal ((vs_to_es ves') ++ [::AI_trap])))
      else ret (s, f, crash_error)
    else ret (s, f, crash_error)
  | AI_basic (BI_cvtop t2 CVO_reinterpret t1 sx) =>
    if ves is v :: ves' then
      if types_agree t1 v && (sx == None)
      then ret (s, f, RS_normal (vs_to_es (wasm_deserialise (bits v) t2 :: ves')))
      else ret (s, f, crash_error)
    else ret (s, f, crash_error)

  (** control-flow instructions **)
  | AI_basic BI_unreachable => ret (s, f, RS_normal ((vs_to_es ves) ++ [::AI_trap]))
  | AI_basic BI_nop => ret (s, f, RS_normal (vs_to_es ves))
  | AI_basic BI_drop =>
    if ves is v :: ves' then
      ret (s, f, RS_normal (vs_to_es ves'))
    else ret (s, f, crash_error)

  | AI_basic BI_select =>
    if ves is (VAL_int32 c) :: v2 :: v1 :: ves' then
      if c == Wasm_int.int_zero i32m
      then ret (s, f, RS_normal (vs_to_es (v2 :: ves')))
      else ret (s, f, RS_normal (vs_to_es (v1 :: ves')))
    else ret (s, f, crash_error)

  | AI_basic (BI_block (Tf t1s t2s) es) =>
    if length ves >= length t1s
    then
      let: (ves', ves'')  := split_n ves (length t1s) in
      ret (s, f, RS_normal (vs_to_es ves''
                            ++ [::AI_label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)]))
    else ret (s, f, crash_error)

  | AI_basic (BI_loop (Tf t1s t2s) es) =>
    if length ves >= length t1s
    then
      let: (ves', ves'') := split_n ves (length t1s) in
      ret (s, f, RS_normal (vs_to_es ves''
                            ++ [::AI_label (length t1s) [::AI_basic (BI_loop (Tf t1s t2s) es)]
                                    (vs_to_es ves' ++ to_e_list es)]))
    else ret (s, f, crash_error)

  | AI_basic (BI_if tf es1 es2) =>
    if ves is VAL_int32 c :: ves' then
      if c == Wasm_int.int_zero i32m
      then ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_block tf es2)]))
      else ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_block tf es1)]))
    else ret (s, f, crash_error)

  | AI_basic (BI_br j) => ret (s, f, RS_break j ves)
  | AI_basic (BI_br_if j) =>
    if ves is VAL_int32 c :: ves' then
      if c == Wasm_int.int_zero i32m
      then ret (s, f, RS_normal (vs_to_es ves'))
      else ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br j)]))
    else ret (s, f, crash_error)
  | AI_basic (BI_br_table js j) =>
    if ves is VAL_int32 c :: ves' then
      let: k := Wasm_int.nat_of_uint i32m c in
      if k < length js
      then
        expect (List.nth_error js k) (fun js_at_k =>
            ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br js_at_k)])))
          (ret (s, f, crash_error))
      else ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br j)]))
    else ret (s, f, crash_error)

  | AI_basic (BI_call j) =>
    (*    if sfunc s f.(f_inst) j is Some sfunc_i_j then*)
    if List.nth_error f.(f_inst).(inst_funcs) j is Some a then
      ret (s, f, RS_normal (vs_to_es ves ++ [::AI_invoke a]))
    else ret (s, f, crash_error)

  | AI_basic (BI_call_indirect j) =>
    if ves is VAL_int32 c :: ves' then
(*      match stab s f.(f_inst) (Wasm_int.nat_of_uint i32m c) with
      | Some cl =>*)
      match stab_addr s f (Wasm_int.nat_of_uint i32m c) with
      | Some a =>
        match List.nth_error s.(s_funcs) a with
        | Some cl =>
          if stypes s f.(f_inst) j == Some (cl_type cl)
          then ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_invoke a]))
          else ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
     (* Not Trap because this is not supposed to happen after validation *)
        | None => ret (s, f, crash_error)
        end
      | None => ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
      end
    else ret (s, f, crash_error)

  | AI_basic (BI_return_call j) =>
    (*    if sfunc s f.(f_inst) j is Some sfunc_i_j then*)
    if List.nth_error f.(f_inst).(inst_funcs) j is Some a then
      ret (s, f, RS_normal (vs_to_es ves ++ [::AI_return_invoke a]))
    else ret (s, f, crash_error)

  | AI_basic (BI_return_call_indirect j) =>
    if ves is VAL_int32 c :: ves' then
(*      match stab s f.(f_inst) (Wasm_int.nat_of_uint i32m c) with
      | Some cl =>*)
      match stab_addr s f (Wasm_int.nat_of_uint i32m c) with
      | Some a =>
        match List.nth_error s.(s_funcs) a with
        | Some cl =>
          if stypes s f.(f_inst) j == Some (cl_type cl)
          then ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_return_invoke a]))
          else ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
     (* Not Trap because this is not supposed to happen after validation *)
        | None => ret (s, f, crash_error)
        end
      | None => ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
      end
    else ret (s, f, crash_error)

  | AI_basic BI_return => ret (s, f, RS_return ves)

  | AI_basic (BI_get_local j) =>
    if j < length f.(f_locs)
    then
      expect (List.nth_error f.(f_locs) j) (fun vs_at_j =>
          ret (s, f, RS_normal (vs_to_es (vs_at_j :: ves))))
        (ret (s, f, crash_error))
    else ret (s, f, crash_error)

  | AI_basic (BI_set_local j) =>
    if ves is v :: ves' then
      if j < length f.(f_locs)
      then ret (s, Build_frame (set_nth v f.(f_locs) j v) f.(f_inst), RS_normal (vs_to_es ves'))
      else ret (s, f, crash_error)
    else ret (s, f, crash_error)

  | AI_basic (BI_tee_local j) =>
    if ves is v :: ves' then
      ret (s, f, RS_normal (vs_to_es (v :: ves) ++ [::AI_basic (BI_set_local j)]))
    else ret (s, f, crash_error)

  | AI_basic (BI_get_global j) =>
    if sglob_val s f.(f_inst) j is Some xx
    then ret (s, f, RS_normal (vs_to_es (xx :: ves)))
    else ret (s, f, crash_error)

  | AI_basic (BI_set_global j) =>
    if ves is v :: ves' then
      if supdate_glob s f.(f_inst) j v is Some xx
      then ret (xx, f, RS_normal (vs_to_es ves'))
      else ret (s, f, crash_error)
    else ret (s, f, crash_error)

    | AI_basic (BI_load t None a off) =>
      if ves is VAL_int32 k :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load (mem_s_j) (Wasm_int.N_of_uint i32m k) off (t_length t))
                 (fun bs => ret (s, f, RS_normal (vs_to_es (wasm_deserialise bs t :: ves'))))
                 (ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
             else ret (s, f, crash_error))
          (ret (s, f, crash_error))
      else ret (s, f, crash_error)

    | AI_basic (BI_load t (Some (tp, sx)) a off) =>
      if ves is VAL_int32 k :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load_packed sx (mem_s_j) (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t))
                 (fun bs => ret (s, f, RS_normal (vs_to_es (wasm_deserialise bs t :: ves'))))
                 (ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
             else ret (s, f, crash_error))
          (ret (s, f, crash_error))
      else ret (s, f, crash_error)

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
                      (ret (upd_s_mem s (set_nth mem' s.(s_mems) j mem'), f, RS_normal (vs_to_es ves'))))
                   (ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
               else ret (s, f, crash_error))
            (ret (s, f, crash_error))
        else ret (s, f, crash_error)
      else ret (s, f, crash_error)

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
                      (ret (upd_s_mem s (set_nth mem' s.(s_mems) j mem'), f, RS_normal (vs_to_es ves'))))
                   (ret (s, f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
               else ret (s, f, crash_error))
            (ret (s, f, crash_error))
        else ret (s, f, crash_error)
      else ret (s, f, crash_error)

    | AI_basic BI_current_memory =>
      expect
        (smem_ind s f.(f_inst))
        (fun j =>
           if List.nth_error s.(s_mems) j is Some s_mem_s_j then
             (ret (s, f, RS_normal (vs_to_es (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j))) :: ves))))
           else ret (s, f, crash_error))
        (ret (s, f, crash_error))

    | AI_basic BI_grow_memory =>
      if ves is VAL_int32 c :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
            if List.nth_error s.(s_mems) j is Some s_mem_s_j then
              let: l := mem_size s_mem_s_j in
              let: mem' := mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m c) in
              if mem' is Some mem'' then
                ret (upd_s_mem s (set_nth mem'' s.(s_mems) j mem''), f,
                     RS_normal (vs_to_es (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat l)) :: ves')))
              else ret (s, f, crash_error)
            else ret (s, f, crash_error))
          (ret (s, f, crash_error))
      else ret (s, f, crash_error)

    | AI_basic (BI_const _) => ret (s, f, crash_error)

    | AI_invoke i =>
      match List.nth_error s.(s_funcs) i with
        | Some cl =>
            match cl with
            | FC_func_native i (Tf t1s t2s) ts es =>
                let: n := length t1s in
                let: m := length t2s in
                if length ves >= n
                then
                let: (ves', ves'') := split_n ves n in
                let: zs := n_zeros ts in
                ret (s, f, RS_normal (vs_to_es ves''
                                ++ [::AI_local m (Build_frame (rev ves' ++ zs) i) [::AI_basic (BI_block (Tf [::] t2s) es)]]))
                else ret (s, f, crash_error)
            | FC_func_host (Tf t1s t2s) h =>
                let: n := length t1s in
                let: m := length t2s in
                if length ves >= n
                then
                let: (ves', ves'') := split_n ves n in
                r <- trigger (host_apply s (Tf t1s t2s) h (rev ves')) ;;
                match r with
                | Some (s', r) =>
                    if result_types_agree t2s r
                    then
                    let: rves := result_to_stack r in
                    ret (s', f, RS_normal (vs_to_es ves'' ++ rves))
                    else ret (s (* FIXME: Why not [s']? *), f, crash_error)
                | None => ret (s, f, RS_normal (vs_to_es ves'' ++ [::AI_trap]))
                end
                else ret (s, f, crash_error)
            end
        | None => ret (s, f, crash_error)
      end

  (* FIXME: reduce to standard invoke for now *)
  | AI_return_invoke i => ret (s, f, RS_normal [::AI_invoke i])

  | AI_label ln les es =>
    if es_is_trap es
    then ret (s, f, RS_normal (vs_to_es ves ++ [::AI_trap]))
    else
      if const_list es
      then ret (s, f, RS_normal (vs_to_es ves ++ es))
      else         
      '(s', f', res) <- call _ (call_run_step_base d (s, f, es)) ;;
      match res with
      | RS_break 0 bvs =>
        if length bvs >= ln
        then ret (s', f', RS_normal ((vs_to_es ((take ln bvs) ++ ves)) ++ les))
        else ret (s', f', crash_error)
      | RS_break (n.+1) bvs => ret (s', f', RS_break n bvs)
      | RS_return rvs => ret (s', f', RS_return rvs)
      | RS_normal es' =>
        ret (s', f', RS_normal (vs_to_es ves ++ [::AI_label ln les es']))
      | RS_crash error => ret (s', f', RS_crash error)
      end

  | AI_local ln f es =>
    if es_is_trap es
    then ret (s, f, RS_normal (vs_to_es ves ++ [::AI_trap]))
    else
      if const_list es
      then
        if length es == ln
        then ret (s, f, RS_normal (vs_to_es ves ++ es))
        else ret (s, f, crash_error)
      else
        '(s', f', res) <- call _ (call_run_step_base d (s, f, es)) ;;
        match res return itree (run_stepE +' eff) res_tuple with
        | RS_return rvs =>
          if length rvs >= ln
          then ret (s', f, RS_normal (vs_to_es (take ln rvs ++ ves)))
          else ret (s', f, crash_error)
        | RS_normal es' =>
          ret (s', f, RS_normal (vs_to_es ves ++ [::AI_local ln f' es']))
        | RS_crash error => ret (s', f, RS_crash error)
        | RS_break _ _ => ret (s', f, crash_error)
        end

  | AI_trap => ret (s, f, crash_error)
  end.

Definition run_step_call : run_stepE ~> itree eff :=
  mrec (fun T (f : run_stepE T) =>
    let call _ f := trigger f in
    match f with
    | call_run_step_base d cgf =>
      run_step_base call d cgf
    | call_run_one_step d cgf e =>
      run_one_step call d cgf e
    end).

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
  let: (s, vs, es) := cfg in
  1 + List.fold_left max (List.map run_one_step_fuel es) 0.

(** [run_step] is defined by calling [run_step_base], whilst burning enough fuel
   for it to be fully computed. **)
Definition run_step (d : depth) (inst : instance) (cfg : config_tuple) : itree eff res_tuple :=
  burn (run_step_fuel cfg) (run_step_call (call_run_step_base d cfg)).

End RunStep.

(** Extraction **)
  
Section Run.

Context {eff : Type -> Type}.
Context {eff_has_host_event : host_event -< eff}.

Definition run_v : depth -> instance -> config_tuple -> itree eff (store_record * res) :=
  let run_v :=
    rec-fix run_v (d, i, (s, vs, es)) :=
      if es_is_trap es
      then ret (s, R_trap)
      else
      if const_list es
      then ret (s, R_value (fst (split_vals_e es)))
        else
          '(s', vs', r) <- run_step d i (s, vs, es) ;;
          match r with
          | RS_normal es' => run_v (d, i, (s', vs', es'))
          | RS_crash error => ret (s, R_crash error)
          | _ => ret (s, R_crash C_error)
          end in
  fun d i cfg => run_v (d, i, cfg).

End Run.

Definition run_step_extraction_eqType := run_extraction (@run_step).
Definition run_v_extraction_eqType := run_extraction (@run_v).

End Host.

(* Our current assumptions consist of the classical axiom [Classical_Prop.classic],
  as well as Flocq's axioms.
  The classical axiom comes from our definitions of [f32] and [f64] in numerics.v,
  that use functions (like [Binary.binary_normalize]) based on this axiom.
[[
Print Assumptions run_step.
]]
*)


(** The following module is designed to fit OCaml’s types, and thus to better extract. **)

(** First, due to universe inconsistencies, we are not allowed to extract directly to
  the same monad [host_event].
  We thus assume another monad with the right assumption.
  Again, this module type is designed to extract nicely to OCaml. **)
Module Type TargetMonad (EH : Executable_Host).

Parameter monad : Type -> Type.
Parameter monad_ret : forall t : Type, t -> monad t.
Parameter monad_bind : forall t u : Type, monad t -> (t -> monad u) -> monad u.
Parameter monad_iter : forall R I : Type, (I -> monad (I + R)%type) -> I -> monad R.

Parameter convert : EH.host_event ~> monad.

End TargetMonad.

(** The following module converts the module type above into a proper Coq monad. **)
Module convert_target_monad (EH : Executable_Host) (M : TargetMonad EH).

Export M.

Definition monad_monad : Monad monad := {|
    ret := monad_ret ;
    bind := monad_bind
  |}.

Definition monad_Iter : MonadIter monad := monad_iter.

Definition monad_functor := Functor_Monad (M := monad_monad).

End convert_target_monad.

Module Interpreter_itree_extract (EH : Executable_Host) (TM : TargetMonad EH).

Module Exec := convert_to_executable_host EH.
Import Exec.

Module Target := convert_target_monad EH TM.
Import Target.

Local Definition res_tuple := res_tuple host_function.

Definition run_step
  : depth -> instance -> config_tuple -> monad res_tuple :=
  @run_step_extraction_eqType host_function executable_host_instance
    monad monad_functor monad_monad monad_Iter convert.
Definition run_v
  : depth -> instance -> config_tuple -> monad (store_record * res) :=
  @run_v_extraction_eqType host_function executable_host_instance
    monad monad_functor monad_monad monad_Iter convert.

(** State whether a list of administrative instruction is a final value. **)
Definition is_const_list : list administrative_instruction -> option (list value) :=
  @e_to_v_list_opt.

(** A useful definition for converting [itree] to [option] without executing anything,
  assuming a way to remove events.
  Warning: this breaks the semantics of [itree]s by mapping any event to [None].
  The function [tr] has an unusual type [forall T A, E T -> A] instead of [E ~> void1],
  otherwise it is simply and brutally removed in the extraction process. **)
Definition itree_to_option (E : Type -> Type) (tr : forall T A, E T -> A) :
    forall R, itree E R -> option R :=
  fun _ tree => option_of_itree_void (translate (fun T => tr T _) tree).

End Interpreter_itree_extract.
