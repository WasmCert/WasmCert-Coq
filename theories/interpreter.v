(* Wasm interpreter *)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Export wasm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Inductive res_crash : Type :=
| C_error : res_crash
| C_exhaustion : res_crash.

Inductive res : Type :=
| R_crash : res_crash -> res
| R_trap : res
| R_value : list value -> res.

Inductive res_step : Type :=
| RS_crash : res_crash -> res_step
| RS_break : nat -> list value -> res_step
| RS_return : list value -> res_step
| RS_normal : list administrative_instruction -> res_step.

Definition crash_error := RS_crash C_error.

Definition depth := nat.

Definition fuel := nat.

Definition config_tuple := ((store_record * list value * list administrative_instruction) % type).

Definition config_one_tuple_without_e := (store_record * list value * list value) % type.

Definition res_tuple := (store_record * list value * res_step) % type.

Fixpoint split_vals (es : list basic_instruction) : ((list value) * (list basic_instruction)) % type :=
  match es with
  | (EConst v) :: es' =>
    let (vs', es'') := split_vals es' in
    (v :: vs', es'')
  | _ => ([::], es)
  end.

Fixpoint split_vals_e (es : list administrative_instruction) : ((list value) * (list administrative_instruction)) % type :=
  match es with
  | (Basic (EConst v)) :: es' =>
    let (vs', es'') := split_vals_e es' in
    (v :: vs', es'')
  | _ => ([::], es)
  end.

Fixpoint split_n (es : list value) (n : nat) : ((list value) * (list value)) % type :=
  match (es, n) with
  | ([::], _) => ([::], [::])
  | (_, 0) => ([::], es)
  | (e :: esX, n.+1) =>
    let (es', es'') := split_n esX n in
    (e :: es', es'')
  end.

Definition expect {A B : Type} (ao : option A) (f : A -> B) (b : B) : B :=
  match ao with
  | Some a => f a
  | None => b
  end.

Definition vs_to_es (vs : list value) : list administrative_instruction :=
  v_to_e_list (rev vs).

Definition e_is_trap (e : administrative_instruction) : bool :=
  match e with
  | Trap => true
  | _ => false
  end.

Lemma foo : forall e, reflect (e = Trap) (e_is_trap e).
Proof.
  case => /=; intros; by [ apply: ReflectF | apply: ReflectT ].
Qed.

Definition es_is_trap (es : list administrative_instruction) : bool :=
  match es with
  | e :: _ => e_is_trap e
  | [::] => false
  end.

Section Host.

Variable mem_grow_impl : mem -> nat -> option mem.

Variable host_apply_impl : store_record -> function_type -> wasm.host -> list value -> option (store_record * list value).

Definition run_step_param run_one_step (d : depth) (i : instance) (tt : config_tuple) : res_tuple :=
  let: (s, vs, es) := tt in
  let: (ves, es') := split_vals_e es in
  match es' with
  | [::] => (s, vs, crash_error)
  | e :: es'' =>
    if e_is_trap e
    then
      if (es'' != [::]) || (ves != [::])
      then (s, vs, RS_normal [::Trap])
      else (s, vs, crash_error)
    else
      let '(s', vs', r) := run_one_step d i (s, vs, (rev ves)) e in
      if r is RS_normal res
      then (s', vs', RS_normal (res ++ es''))
      else (s', vs', r)
  end.

Fixpoint run_one_step (d : depth) (i : instance) (tt : config_one_tuple_without_e) (e : administrative_instruction) : res_tuple :=
  let run_step := run_step_param run_one_step in
  let: (s, vs, ves) := tt in
  match e with
  (* unop *)
  | Basic (Unop_i T_i32 iop) =>
    if ves is ConstInt32 c :: ves' then
      (s, vs, RS_normal (vs_to_es ((ConstInt32 (@app_unop_i i32t iop c)) :: ves')))
    else (s, vs, crash_error)
  | Basic (Unop_i T_i64 iop) =>
    if ves is (ConstInt64 c) :: ves' then
      (s, vs, RS_normal (vs_to_es ((ConstInt64 (@app_unop_i i64t iop c)) :: ves')))
    else (s, vs, crash_error)
  | Basic (Unop_i _ _) => (s, vs, crash_error)
  | Basic (Unop_f T_f32 iop) =>
    if ves is (ConstFloat32 c) :: ves' then
      (s, vs, RS_normal (vs_to_es ((ConstFloat32 (@app_unop_f f32t iop c)) :: ves')))
    else (s, vs, crash_error)
  | Basic (Unop_f T_f64 iop) =>
    if ves is (ConstFloat64 c) :: ves' then
      (s, vs, RS_normal (vs_to_es ((ConstFloat64 (@app_unop_f f64t iop c)) :: ves')))
    else (s, vs, crash_error)
  | Basic (Unop_f _ _) => (s, vs, crash_error)
  (* binop *)
  | Basic (Binop_i T_i32 iop) =>
    if ves is (ConstInt32 c2) :: (ConstInt32 c1) :: ves' then
      expect (@app_binop_i i32t iop c1 c2) (fun c => (s, vs, RS_normal (vs_to_es ((ConstInt32 c) :: ves')))) (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
    else (s, vs, crash_error)
  | Basic (Binop_i T_i64 iop) =>
    if ves is (ConstInt64 c2) :: (ConstInt64 c1) :: ves' then
      expect (@app_binop_i i64t iop c1 c2) (fun c => (s, vs, RS_normal (vs_to_es ((ConstInt64 c) :: ves')))) (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
    else (s, vs, crash_error)
  | Basic (Binop_i _ _) => (s, vs, crash_error)
  | Basic (Binop_f T_i32 iop) =>
    if ves is (ConstFloat32 c2) :: (ConstFloat32 c1) :: ves' then
      expect (@app_binop_f f32t iop c1 c2) (fun c => (s, vs, RS_normal (vs_to_es ((ConstFloat32 c) :: ves')))) (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
    else (s, vs, crash_error)
  | Basic (Binop_f T_i64 iop) =>
    if ves is (ConstFloat64 c2) :: (ConstFloat64 c1) :: ves' then
      expect (@app_binop_f f64t iop c1 c2) (fun c => (s, vs, RS_normal (vs_to_es ((ConstFloat64 c) :: ves')))) (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
    else (s, vs, crash_error)
  | Basic (Binop_f _ _) => (s, vs, crash_error)
  (* testops *)
  | Basic (Testop T_i32 testop) =>
    if ves is (ConstInt32 c) :: ves' then
      (s, vs, RS_normal (vs_to_es ((ConstInt32 (wasm.wasm_bool (@app_testop_i i32t testop c))) :: ves')))
    else (s, vs, crash_error)
  | Basic (Testop T_i64 testop) =>
    if ves is (ConstInt64 c) :: ves' then
      (s, vs, RS_normal (vs_to_es ((ConstInt32 (wasm.wasm_bool (@app_testop_i i64t testop c))) :: ves')))
    else (s, vs, crash_error)
  | Basic (Testop _ _) => (s, vs, crash_error)
  (* relops *)
  | Basic (Relop_i T_i32 iop) =>
    if ves is (ConstInt32 c2) :: (ConstInt32 c1) :: ves' then
      (s, vs, RS_normal (vs_to_es (ConstInt32 (wasm.wasm_bool (@app_relop_i i32t iop c1 c2)) :: ves')))
    else (s, vs, crash_error)
  | Basic (Relop_i T_i64 iop) =>
    if ves is (ConstInt64 c2) :: (ConstInt64 c1) :: ves' then
      (s, vs, RS_normal (vs_to_es (ConstInt32 (wasm.wasm_bool (@app_relop_i i64t iop c1 c2)) :: ves')))
    else (s, vs, crash_error)
  | Basic (Relop_i _ _) => (s, vs, crash_error)
  | Basic (Relop_f T_i32 iop) =>
    if ves is (ConstFloat32 c2) :: (ConstFloat32 c1) :: ves' then
      (s, vs, RS_normal (vs_to_es (ConstInt32 (wasm.wasm_bool (@app_relop_f f32t iop c1 c2)) :: ves')))
    else (s, vs, crash_error)
  | Basic (Relop_f T_i64 iop) =>
    if ves is (ConstFloat64 c2) :: (ConstFloat64 c1) :: ves' then
      (s, vs, RS_normal (vs_to_es (ConstInt32 (wasm.wasm_bool (@app_relop_f f64t iop c1 c2)) :: ves')))
    else (s, vs, crash_error)
  | Basic (Relop_f _ _) => (s, vs, crash_error)
  (* convert *)
  | Basic (Cvtop t2 Convert t1 sx) =>
    if ves is v :: ves' then
      if types_agree t1 v
      then expect (cvt t2 sx v) (fun v' => (s, vs, RS_normal (vs_to_es (v' :: ves')))) (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
      else (s, vs, crash_error)
    else (s, vs, crash_error)
  | Basic (Cvtop t2 Reinterpret t1 sx) =>
    if ves is v :: ves' then
      if types_agree t1 v && (sx == None)
      then (s, vs, RS_normal (vs_to_es (wasm.wasm_deserialise (bits v) t2 :: ves')))
      else (s, vs, crash_error)
    else (s, vs, crash_error)
  (**)
  | Basic Unreachable => (s, vs, RS_normal ((vs_to_es ves) ++ [::Trap]))
  | Basic Nop => (s, vs, RS_normal (vs_to_es ves))
  | Basic Drop =>
    if ves is v :: ves' then
      (s, vs, RS_normal (vs_to_es ves'))
    else (s, vs, crash_error)
  | Basic Select =>
    if ves is (ConstInt32 c) :: v2 :: v1 :: ves' then
      if c == Wasm_int.int_zero i32m
      then (s, vs, RS_normal (vs_to_es (v2 :: ves')))
      else (s, vs, RS_normal (vs_to_es (v1 :: ves')))
    else (s, vs, crash_error)
  | Basic (Block (Tf t1s t2s) es) =>
    if length ves >= length t1s
    then
      let: (ves', ves'')  := split_n ves (length t1s) in
      (s, vs, RS_normal (vs_to_es ves'' ++ [::Label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)]))
    else (s, vs, crash_error)
  | Basic (Loop (Tf t1s t2s) es) =>
    if length ves >= length t1s
    then
      let: (ves', ves'') := split_n ves (length t1s) in
      (s, vs, RS_normal (vs_to_es ves'' ++ [::Label (length t1s) [::Basic (Loop (Tf t1s t2s) es)] (vs_to_es ves' ++ to_e_list es)]))
    else (s, vs, crash_error)
  | Basic (If tf es1 es2) =>
    if ves is ConstInt32 c :: ves' then
      if c == Wasm_int.int_zero i32m
      then (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Block tf es2)]))
      else (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Block tf es1)]))
    else (s, vs, crash_error)
  | Basic (Br j) => (s, vs, RS_break j ves)
  | Basic (Br_if j) =>
    if ves is ConstInt32 c :: ves' then
      if c == Wasm_int.int_zero i32m
      then (s, vs, RS_normal (vs_to_es ves'))
      else (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Br j)]))
    else (s, vs, crash_error)
  | Basic (Br_table js j) =>
    if ves is ConstInt32 c :: ves' then
      let k := Wasm_int.nat_of_int i32m c in
      if k < length js
      then
        expect (List.nth_error js k) (fun js_at_k =>
            (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Br js_at_k)])))
          (s, vs, crash_error) (* Isa mismatch *)
      else (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Br j)]))
    else (s, vs, crash_error)
  | Basic (Call j) =>
    if sfunc s i j is Some sfunc_i_j then
      (s, vs, RS_normal (vs_to_es ves ++ [::Callcl sfunc_i_j]))
    else (s, vs, crash_error) (* Isa mismatch *)
  | Basic (Call_indirect j) =>
    if ves is ConstInt32 c :: ves' then
      match stab s i (Wasm_int.nat_of_int i32m c) with
      | Some cl =>
        if stypes s i j == Some (cl_type cl)
        then (s, vs, RS_normal (vs_to_es ves' ++ [::Callcl cl]))
        else (s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
      | None => (s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
      end
    else (s, vs, crash_error)
  | Basic Return => (s, vs, RS_return ves)
  | Basic (Get_local j) =>
    if j < length vs
    then
      expect (List.nth_error vs j) (fun vs_at_j =>
          (s, vs, RS_normal (vs_to_es (vs_at_j :: ves))))
        (s, vs, crash_error) (* Isa mismatch *)
    else (s, vs, crash_error)
  | Basic (Set_local j) =>
    if ves is v :: ves' then
      if j < length vs
      then (s, update_list_at vs j v, RS_normal (vs_to_es ves'))
      else (s, vs, crash_error)
    else (s, vs, crash_error)
  | Basic (Tee_local j) =>
    if ves is v :: ves' then
      (s, vs, RS_normal (vs_to_es (v :: ves) ++ [::Basic (Set_local j)]))
    else (s, vs, crash_error)
  | Basic (Get_global j) =>
    if sglob_val s i j is Some xx
    then (s, vs, RS_normal (vs_to_es (xx :: ves)))
    else (s, vs, crash_error) (* Isa mismatch *)
  | Basic (Set_global j) =>
    if ves is v :: ves' then
      if supdate_glob s i j v is Some xx
      then (xx, vs, RS_normal (vs_to_es ves'))
      else (s, vs, crash_error)
    else (s, vs, crash_error)
  | Basic (Load t None a off) =>
    if ves is ConstInt32 k :: ves' then
      expect
        (smem_ind s i)
        (fun j =>
           if List.nth_error (s_mem s) j is Some mem_s_j then
             expect
               (load (mem_s_j) (Wasm_int.nat_of_int i32m k) off (t_length t))
               (fun bs => (s, vs, RS_normal (vs_to_es (wasm.wasm_deserialise bs t :: ves'))))
               (s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
           else (s, vs, crash_error) (* Isa mismatch *))
        (s, vs, crash_error)
    else (s, vs, crash_error)
  | Basic (Load t (Some (tp, sx)) a off) =>
    if ves is ConstInt32 k :: ves' then
      expect
        (smem_ind s i)
        (fun j =>
           if List.nth_error (s_mem s) j is Some mem_s_j then
             expect
               (load_packed sx (mem_s_j) (Wasm_int.nat_of_int i32m k) off (tp_length tp) (t_length t))
               (fun bs => (s, vs, RS_normal (vs_to_es (wasm.wasm_deserialise bs t :: ves'))))
               (s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
           else (s, vs, crash_error) (* Isa mismatch *))
        (s, vs, crash_error)
    else (s, vs, crash_error)
  | Basic (Store t None a off) =>
    if ves is v :: ConstInt32 k :: ves' then
      if types_agree t v
      then
        expect
          (smem_ind s i)
          (fun j =>
             if List.nth_error (s_mem s) j is Some mem_s_j then
               expect
                 (store mem_s_j (Wasm_int.nat_of_int i32m k) off (bits v) (t_length t))
                 (fun mem' =>
                    (upd_s_mem s (update_list_at (s_mem s) j mem'), vs, RS_normal (vs_to_es ves')))
                 (s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
             else (s, vs, crash_error) (* Isa mismatch *))
          (s, vs, crash_error)
      else (s, vs, crash_error)
    else (s, vs, crash_error)
  | Basic (Store t (Some tp) a off) =>
    if ves is v :: ConstInt32 k :: ves' then
      if types_agree t v
      then
        expect
          (smem_ind s i)
          (fun j =>
             if List.nth_error (s_mem s) j is Some mem_s_j then
               expect
                 (store_packed mem_s_j (Wasm_int.nat_of_int i32m k) off (bits v) (tp_length tp))
                 (fun mem' =>
                    (upd_s_mem s (update_list_at (s_mem s) j mem'), vs, RS_normal (vs_to_es ves')))
                 (s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
             else (s, vs, crash_error) (* Isa mismatch *))
          (s, vs, crash_error)
      else (s, vs, crash_error)
    else (s, vs, crash_error)
  | Basic Current_memory =>
    expect
      (smem_ind s i)
      (fun j =>
         if List.nth_error (s_mem s) j is Some s_mem_s_j then
           (s, vs, RS_normal (vs_to_es (ConstInt32 (Wasm_int.int_of_nat i32m (mem_size s_mem_s_j)) :: ves)))
         else (s, vs, crash_error) (* Isa mismatch *))
      (s, vs, crash_error)
  | Basic Grow_memory =>
    if ves is ConstInt32 c :: ves' then
      expect
        (smem_ind s i)
        (fun j =>
          if List.nth_error (s_mem s) j is Some s_mem_s_j then
            let l := mem_size s_mem_s_j in
            expect
              (mem_grow_impl s_mem_s_j (Wasm_int.nat_of_int i32m c))
              (fun mem' =>
                 (upd_s_mem s (update_list_at (s_mem s) j mem'), vs, RS_normal (vs_to_es (ConstInt32 (Wasm_int.int_of_nat i32m l) :: ves')))
              )
              (s, vs, crash_error)
          else (s, vs, crash_error) (* Isa mismatch *))
        (s, vs, crash_error)
    else (s, vs, crash_error)
  | Basic (EConst _) => (s, vs, crash_error)
  | Callcl cl =>
    match cl with
    | Func_native i' (Tf t1s t2s) ts es =>
      let n := length t1s in
      let m := length t2s in
      if length ves >= n
      then
        let (ves', ves'') := split_n ves n in
        let zs := n_zeros ts in
        (s, vs, RS_normal (vs_to_es ves'' ++ [::Local m i' (rev ves' ++ zs) [::Basic (Block (Tf [::] t2s) es)]]))
      else (s, vs, crash_error)
    | Func_host (Tf t1s t2s) f =>
      let n := length t1s in
      let m := length t2s in
      if length ves >= n
      then
        let (ves', ves'') := split_n ves n in
        match host_apply_impl s (Tf t1s t2s) f (rev ves') with
        | Some (s', rves) =>
          if all2 types_agree t2s rves
          then (s', vs, RS_normal (vs_to_es ves'' ++ v_to_e_list rves))
          else (s, vs, crash_error)
        | None => (s, vs, RS_normal (vs_to_es ves'' ++ [::Trap]))
        end
      else (s, vs, crash_error)
    end
  | Label ln les es =>
    if es_is_trap es
    then (s, vs, RS_normal (vs_to_es ves ++ [::Trap]))
    else
      if const_list es
      then (s, vs, RS_normal (vs_to_es ves ++ es))
      else
        match d with
        | 0 => (s, vs, RS_crash C_exhaustion)
        | d'.+1 => (* TODO: we diverge from the Isabelle model here, which does not take a step *)
          let: (s', vs', res) := run_step d' i (s, vs, es) in
          match res with
          | RS_break 0 bvs =>
            if length bvs >= ln
            then (s', vs', RS_normal ((vs_to_es ((List.firstn ln bvs) ++ ves)) ++ les))
            else (s', vs', crash_error)
          | RS_break (n.+1) bvs => (s', vs', RS_break n bvs)
          | RS_return rvs => (s', vs', RS_return rvs)
          | RS_normal es' =>
            (s', vs', RS_normal (vs_to_es ves ++ [::Label ln les es']))
          | _ => (s', vs', crash_error)
          end
        end
  | Local ln j vls es =>
    if es_is_trap es
    then (s, vs, RS_normal (vs_to_es ves ++ [::Trap]))
    else
      if const_list es
      then
        if length es == ln
        then (s, vs, RS_normal (vs_to_es ves ++ es))
        else (s, vs, crash_error)
      else
        match d with
        | 0 => (s, vs, RS_crash C_exhaustion)
        | d'.+1 =>
          let: (s', vls', res) := run_step d' j (s, vls, es) in
          match res with
          | RS_return rvs =>
            if length rvs >= ln
            then (s', vs, RS_normal (vs_to_es (List.firstn ln rvs ++ ves)))
            else (s', vs, crash_error)
          | RS_normal es' =>
            (s', vs, RS_normal (vs_to_es ves ++ [::Local ln j vls' es']))
          | RS_crash error => (s', vs, RS_crash error)
          | RS_break _ _ => (s', vs, crash_error)
          end
        end
  | Trap => (s, vs, crash_error)
  end.

Definition run_step := run_step_param run_one_step.

Fixpoint run_v (fuel : fuel) (d : depth) (i : instance) (tt : config_tuple) : ((store_record * res) % type) :=
  match tt with
  | (s, vs, es) =>
    match fuel with
    | 0 => (s, R_crash C_exhaustion)
    | fuel.+1 =>
      if es_is_trap es
      then (s, R_trap)
      else
        if const_list es
        then (s, R_value (fst (split_vals_e es)))
        else
          let '(s', vs', res) := run_step d i (s, vs, es) in
          match res with
          | RS_normal es' => run_v fuel d i (s', vs', es')
          | RS_crash error => (s, R_crash error)
          | _ => (s, R_crash C_error)
          end
    end
  end.

End Host.
