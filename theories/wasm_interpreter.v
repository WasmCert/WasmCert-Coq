(* Wasm interpreter *)
(* (C) J. Pichon - see LICENSE.txt *)
From mathcomp
Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import wasm.


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
  case => /=;
            try
    by (intros; apply: ReflectF).
    by apply: ReflectT.
Qed.

Definition es_is_trap (es : list administrative_instruction) : bool :=
  match es with
  | e :: _ => e_is_trap e
  | [::] => false
  end.

Variable mem_grow_impl : mem -> nat -> option mem.
Axiom mem_grow_impl_correct :
  forall m n m',
    mem_grow_impl m n = Some m' ->
    mem_grow m n = m'.

Variable host_apply_impl : store_record -> function_type -> wasm.host -> list value -> option (store_record * list value).
Axiom host_apply_impl_correct :
  forall s tf h vs m',
    host_apply_impl s tf h vs = Some m' ->
    exists hs, wasm.host_apply s tf h vs hs = Some m'.

Fixpoint run_one_step (d : depth) (i : nat) (tt : config_one_tuple_without_e) (e : administrative_instruction) : res_tuple :=
  let run_step :=
      fix run_step (d : depth) (i : nat) (tt : config_tuple) : res_tuple :=
        match tt with
        | (s, vs, es) =>
          let (ves, es') := split_vals_e es in
          match es' with
          | [::] => (s, vs, crash_error)
          | e :: es'' =>
            if e_is_trap e
            then
              (if (es'' != [::]) || (ves != [::])
               then (s, vs, RS_normal [::Trap])
               else (s, vs, crash_error))
            else
              (let '(s', vs', r) := run_one_step d i (s, vs, (rev ves)) e in
               match r with
               | RS_normal res => (s', vs', RS_normal (res ++ es''))
               | _ => (s', vs', r)
               end)
          end
        end
  in
  match tt with
  | (s, vs, ves) =>
    match e with
    (* unop *)
    | Basic (Unop_i T_i32 iop) =>
      match ves with
      | (ConstInt32 c) :: ves' =>
        (s, vs, RS_normal (vs_to_es ((ConstInt32 (@app_unop_i i32_t iop c)) :: ves')))
      | _ => (s, vs, crash_error)
      end
    | Basic (Unop_i T_i64 iop) =>
      match ves with
      | (ConstInt64 c) :: ves' =>
        (s, vs, RS_normal (vs_to_es ((ConstInt64 (@app_unop_i i64_t iop c)) :: ves')))
      | _ => (s, vs, crash_error)
      end
    | Basic (Unop_i _ _) => (s, vs, crash_error)
    | Basic (Unop_f T_f32 iop) =>
      match ves with
      | (ConstFloat32 c) :: ves' =>
        (s, vs, RS_normal (vs_to_es ((ConstFloat32 (@app_unop_f f32_t iop c)) :: ves')))
      | _ => (s, vs, crash_error)
      end
    | Basic (Unop_f T_f64 iop) =>
      match ves with
      | (ConstFloat64 c) :: ves' =>
        (s, vs, RS_normal (vs_to_es ((ConstFloat64 (@app_unop_f f64_t iop c)) :: ves')))
      | _ => (s, vs, crash_error)
      end
    | Basic (Unop_f _ _) => (s, vs, crash_error)
    (* binop *)
    | Basic (Binop_i T_i32 iop) =>
      match ves with
      | (ConstInt32 c2) :: (ConstInt32 c1) :: ves' =>
        expect (@app_binop_i i32_t iop c1 c2) (fun c => (s, vs, RS_normal (vs_to_es ((ConstInt32 c) :: ves')))) (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
      | _ => (s, vs, crash_error)
      end
    | Basic (Binop_i T_i64 iop) =>
      match ves with
      | (ConstInt64 c2) :: (ConstInt64 c1) :: ves' =>
        expect (@app_binop_i i64_t iop c1 c2) (fun c => (s, vs, RS_normal (vs_to_es ((ConstInt64 c) :: ves')))) (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
      | _ => (s, vs, crash_error)
      end
    | Basic (Binop_i _ _) => (s, vs, crash_error)
    | Basic (Binop_f T_i32 iop) =>
      match ves with
      | (ConstFloat32 c2) :: (ConstFloat32 c1) :: ves' =>
        expect (@app_binop_f f32_t iop c1 c2) (fun c => (s, vs, RS_normal (vs_to_es ((ConstFloat32 c) :: ves')))) (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
      | _ => (s, vs, crash_error)
      end
    | Basic (Binop_f T_i64 iop) =>
      match ves with
      | (ConstFloat64 c2) :: (ConstFloat64 c1) :: ves' =>
        expect (@app_binop_f f64_t iop c1 c2) (fun c => (s, vs, RS_normal (vs_to_es ((ConstFloat64 c) :: ves')))) (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
      | _ => (s, vs, crash_error)
      end
    | Basic (Binop_f _ _) => (s, vs, crash_error)
    (* testops *)
    | Basic (Testop T_i32 testop) =>
      match ves with
      | (ConstInt32 c) :: ves' =>
        (s, vs, RS_normal (vs_to_es ((ConstInt32 (wasm.wasm_bool (@app_testop_i i32_t testop c))) :: ves')))
      | _ => (s, vs, crash_error)
      end
    | Basic (Testop T_i64 testop) =>
      match ves with
      | (ConstInt64 c) :: ves' =>
        (s, vs, RS_normal (vs_to_es ((ConstInt32 (wasm.wasm_bool (@app_testop_i i64_t testop c))) :: ves')))
      | _ => (s, vs, crash_error)
      end
    | Basic (Testop _ _) => (s, vs, crash_error)
    (* relops *)
    | Basic (Relop_i T_i32 iop) =>
      match ves with
      | (ConstInt32 c2) :: (ConstInt32 c1) :: ves' =>
        (s, vs, RS_normal (vs_to_es (ConstInt32 (wasm.wasm_bool (@app_relop_i i32_t iop c1 c2)) :: ves')))
      | _ => (s, vs, crash_error)
      end
    | Basic (Relop_i T_i64 iop) =>
      match ves with
      | (ConstInt64 c2) :: (ConstInt64 c1) :: ves' =>
        (s, vs, RS_normal (vs_to_es (ConstInt32 (wasm.wasm_bool (@app_relop_i i64_t iop c1 c2)) :: ves')))
      | _ => (s, vs, crash_error)
      end
    | Basic (Relop_i _ _) => (s, vs, crash_error)
    | Basic (Relop_f T_i32 iop) =>
      match ves with
      | (ConstFloat32 c2) :: (ConstFloat32 c1) :: ves' =>
        (s, vs, RS_normal (vs_to_es (ConstInt32 (wasm.wasm_bool (@app_relop_f f32_t iop c1 c2)) :: ves')))
      | _ => (s, vs, crash_error)
      end
    | Basic (Relop_f T_i64 iop) =>
      match ves with
      | (ConstFloat64 c2) :: (ConstFloat64 c1) :: ves' =>
        (s, vs, RS_normal (vs_to_es (ConstInt32 (wasm.wasm_bool (@app_relop_f f64_t iop c1 c2)) :: ves')))
      | _ => (s, vs, crash_error)
      end
    | Basic (Relop_f _ _) => (s, vs, crash_error)
    (* convert *)
    | Basic (Cvtop t2 Convert t1 sx) =>
      match ves with
      | v :: ves' =>
        if types_agree t1 v
        then expect (cvt t2 sx v) (fun v' => (s, vs, RS_normal (vs_to_es (v' :: ves')))) (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
        else (s, vs, crash_error)
      | [::] => (s, vs, crash_error)
      end
    | Basic (Cvtop t2 Reinterpret t1 sx) =>
      match ves with
      | v :: ves' =>
        if types_agree t1 v && (sx == None)
        then (s, vs, RS_normal (vs_to_es (wasm.wasm_deserialise (bits v) t2 :: ves')))
        else (s, vs, crash_error)
      | [::] => (s, vs, crash_error)
      end
    (**)
    | Basic Unreachable => (s, vs, RS_normal ((vs_to_es ves) ++ [::Trap]))
    | Basic Nop => (s, vs, RS_normal (vs_to_es ves))
    | Basic Drop =>
      match ves with
      | v :: ves' => (s, vs, RS_normal (vs_to_es ves'))
      | [::] => (s, vs, crash_error)
      end
    | Basic Select =>
      match ves with
      | (ConstInt32 c) :: v2 :: v1 :: ves' =>
        if c == Wasm_int.int_zero (Wasm_int.mixin wasm.i32_r)
        then (s, vs, RS_normal (vs_to_es (v2 :: ves')))
        else (s, vs, RS_normal (vs_to_es (v1 :: ves')))
      | _ => (s, vs, crash_error)
      end
    | Basic (Block (Tf t1s t2s) es) =>
      if length ves >= length t1s
      then
        let (ves', ves'')  := split_n ves (length t1s) in
        (s, vs, RS_normal (vs_to_es ves'' ++ [::Label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)]))
      else (s, vs, crash_error)
    | Basic (Loop (Tf t1s t2s) es) =>
      if length ves >= length t1s
      then
        let (ves', ves'') := split_n ves (length t1s) in
        (s, vs, RS_normal (vs_to_es ves'' ++ [::Label (length t1s) [::Basic (Loop (Tf t1s t2s) es)] (vs_to_es ves' ++ to_e_list es)]))
      else (s, vs, crash_error)
    | Basic (If tf es1 es2) =>
      match ves with
      | ConstInt32 c :: ves' =>
        if c == Wasm_int.int_zero (Wasm_int.mixin wasm.i32_r)
        then (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Block tf es2)]))
        else (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Block tf es1)]))
      | _ => (s, vs, crash_error)
      end
    | Basic (Br j) => (s, vs, RS_break j ves)
    | Basic (Br_if j) =>
      match ves with
      | ConstInt32 c :: ves' =>
        if c == Wasm_int.int_zero (Wasm_int.mixin wasm.i32_r)
        then (s, vs, RS_normal (vs_to_es ves'))
        else (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Br j)]))
      | _ => (s, vs, crash_error)
      end
    | Basic (Br_table js j) =>
      match ves with
      | ConstInt32 c :: ves' =>
        let k := Wasm_int.nat_of_int (Wasm_int.mixin wasm.i32_r) c in
        if k < length js
        then
          match List.nth_error js k with
          | Some js_at_k => (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Br js_at_k)]))
          | None => (s, vs, crash_error) (* Isa mismatch *)
          end
        else (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Br j)]))
      | _ => (s, vs, crash_error)
      end
    | Basic (Call j) =>
      match sfunc s i j with
      | Some sfunc_i_j =>
        (s, vs, RS_normal (vs_to_es ves ++ [::Callcl sfunc_i_j]))
      | None => (s, vs, crash_error) (* Isa mismatch *)
      end
    | Basic (Call_indirect j) =>
      match ves with
      | ConstInt32 c :: ves' =>
        match stab s i (Wasm_int.nat_of_int (Wasm_int.mixin wasm.i32_r) c) with
        | Some cl =>
          if stypes s i j == Some (cl_type cl)
          then (s, vs, RS_normal (vs_to_es ves' ++ [::Callcl cl]))
          else (s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
        | None => (s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
        end
      | _ => (s, vs, crash_error)
      end
    | Basic Return => (s, vs, RS_return ves)
    | Basic (Get_local j) =>
      if j < length vs
      then
        match List.nth_error vs j with
        | Some vs_at_j =>(s, vs, RS_normal (vs_to_es (vs_at_j :: ves)))
        | None => (s, vs, crash_error) (* Isa mismatch *)
        end
      else (s, vs, crash_error)
    | Basic (Set_local j) =>
      match ves with
      | v :: ves' =>
        if j < length vs
        then (s, update_list_at vs j v, RS_normal (vs_to_es ves'))
        else (s, vs, crash_error)
      | [::] => (s, vs, crash_error)
      end
    | Basic (Tee_local j) =>
      match ves with
      | v :: ves' =>
        (s, vs, RS_normal (vs_to_es (v :: ves) ++ [::Basic (Set_local j)]))
      | _ => (s, vs, crash_error)
      end
    | Basic (Get_global j) =>
      match sglob_val s i j with
      | Some xx => (s, vs, RS_normal (vs_to_es (xx :: ves)))
      | None => (s, vs, crash_error) (* Isa mismatch *)
      end
    | Basic (Set_global j) =>
      match ves with
      | v :: ves' =>
        match supdate_glob s i j v with
        | Some xx =>
          (xx, vs, RS_normal (vs_to_es ves'))
        | None => (s, vs, crash_error)
        end
      | [::] => (s, vs, crash_error)
      end
    | Basic (Load t None a off) =>
      match ves with
      | ConstInt32 k :: ves' =>
        expect
          (smem_ind s i)
          (fun j =>
             match List.nth_error (s_mem s) j with
             | Some mem_s_j =>
               expect
                 (load (mem_s_j) (Wasm_int.nat_of_int (Wasm_int.mixin wasm.i32_r) k) off (t_length t))
                 (fun bs => (s, vs, RS_normal (vs_to_es (wasm.wasm_deserialise bs t :: ves'))))
                 (s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
             | None => (s, vs, crash_error) (* Isa mismatch *)
             end)
          (s, vs, crash_error)
      | _ => (s, vs, crash_error)
      end
    | Basic (Load t (Some (tp, sx)) a off) =>
      match ves with
      | ConstInt32 k :: ves' =>
        expect
          (smem_ind s i)
          (fun j =>
             match List.nth_error (s_mem s) j with
             | Some mem_s_j =>
               expect
                 (load_packed sx (mem_s_j) (Wasm_int.nat_of_int (Wasm_int.mixin wasm.i32_r) k) off (tp_length tp) (t_length t))
                 (fun bs => (s, vs, RS_normal (vs_to_es (wasm.wasm_deserialise bs t :: ves'))))
                 (s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
             | None => (s, vs, crash_error) (* Isa mismatch *)
             end)
          (s, vs, crash_error)
      | _ => (s, vs, crash_error)
      end
    | Basic (Store t None a off) =>
      match ves with
      | v :: ConstInt32 k :: ves' =>
        if types_agree t v
        then
          expect
            (smem_ind s i)
            (fun j =>
               match List.nth_error (s_mem s) j with
               | Some mem_s_j =>
                 expect
                   (store mem_s_j (Wasm_int.nat_of_int (Wasm_int.mixin wasm.i32_r) k) off (bits v) (t_length t))
                   (fun mem' =>
                      (upd_s_mem s (update_list_at (s_mem s) j mem'), vs, RS_normal (vs_to_es ves')))
                   (s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
               | None => (s, vs, crash_error) (* Isa mismatch *)
               end)
            (s, vs, crash_error)
        else (s, vs, crash_error)
      | _ => (s, vs, crash_error)
      end
    | Basic (Store t (Some tp) a off) =>
      match ves with
      | v :: ConstInt32 k :: ves' =>
        if types_agree t v
        then
          expect
            (smem_ind s i)
            (fun j =>
               match List.nth_error (s_mem s) j with
               | Some mem_s_j =>
                 expect
                   (store_packed mem_s_j (Wasm_int.nat_of_int (Wasm_int.mixin wasm.i32_r) k) off (bits v) (tp_length tp))
                   (fun mem' =>
                      (upd_s_mem s (update_list_at (s_mem s) j mem'), vs, RS_normal (vs_to_es ves')))
                   (s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
               | None => (s, vs, crash_error) (* Isa mismatch *)
               end)
            (s, vs, crash_error)
        else (s, vs, crash_error)
      | _ => (s, vs, crash_error)
      end
    | Basic Current_memory =>
      expect
        (smem_ind s i)
        (fun j =>
           match List.nth_error (s_mem s) j with
           | Some s_mem_s_j =>
             (s, vs, RS_normal (vs_to_es (ConstInt32 (Wasm_int.int_of_nat (Wasm_int.mixin wasm.i32_r) (mem_size s_mem_s_j)) :: ves)))
           | None =>
             (s, vs, crash_error) (* Isa mismatch *)
           end)
        (s, vs, crash_error)
    | Basic Grow_memory =>
      match ves with
      | ConstInt32 c :: ves' =>
        expect
          (smem_ind s i)
          (fun j =>
             match List.nth_error (s_mem s) j with
             | Some s_mem_s_j =>
               let l := mem_size s_mem_s_j in
               expect
                 (mem_grow_impl s_mem_s_j (Wasm_int.nat_of_int (Wasm_int.mixin wasm.i32_r) c))
                 (fun mem' =>
                    (upd_s_mem s (update_list_at (s_mem s) j mem'), vs, RS_normal (vs_to_es (ConstInt32 (Wasm_int.int_of_nat (Wasm_int.mixin wasm.i32_r) l) :: ves')))
                 )
                 (s, vs, crash_error)
             | None => (s, vs, crash_error) (* Isa mismatch *)
             end)
          (s, vs, crash_error)
      | _ => (s, vs, crash_error)
      end
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
          | 0 => (s, vs, crash_error)
          | d'.+1 => (* TODO: we diverge from the Isabelle model here, which does not take a step *)
            let '(s', vs', res) := run_step d' i (s, vs, es) in
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
          (if length es == ln
           then (s, vs, RS_normal (vs_to_es ves ++ es))
           else (s, vs, crash_error))
        else
          match d with
          | 0 => (s, vs, crash_error)
          | d'.+1 =>
            let '(s', vls', res) := run_step d' j (s, vls, es) in
            match res with
            | RS_return rvs =>
              if length rvs >= ln
              then (s', vs, RS_normal (vs_to_es (List.firstn ln rvs ++ ves)))
              else (s', vs, crash_error)
            | RS_normal es' =>
              (s', vs, RS_normal (vs_to_es ves ++ [::Local ln j vls' es']))
            | _ => (s', vs, RS_crash C_exhaustion)
            end
          end
    | Trap => (s, vs, crash_error)
    end
  end.

(* TODO: avoid repetition *)
Fixpoint run_step (d : depth) (i : nat) (tt : config_tuple) : res_tuple :=
  match tt with
  | (s, vs, es) =>
    let (ves, es') := split_vals_e es in
    match es' with
    | [::] => (s, vs, crash_error)
    | e :: es'' =>
      if e_is_trap e
      then
        (if (es'' != [::]) || (ves != [::])
         then (s, vs, RS_normal [::Trap])
         else (s, vs, crash_error))
      else
        (let '(s', vs', r) := run_one_step d i (s, vs, (rev ves)) e in
         match r with
         | RS_normal res => (s', vs', RS_normal (res ++ es''))
         | _ => (s', vs', r)
         end)
    end
  end.

Fixpoint run_v (n : fuel) (d : depth) (i : nat) (tt : config_tuple) : ((store_record * res) % type) :=
  match tt with
  | (s, vs, es) =>
    match n with
    | 0 => (s, R_crash C_exhaustion)
    | n'.+1 =>
      if es_is_trap es
      then (s, R_trap)
      else
        if const_list es
        then (s, R_value (fst (split_vals_e es)))
        else
          let '(s', vs', res) := run_step d i (s, vs, es) in
          match res with
          | RS_normal es' => run_v n' d i (s', vs', es')
          | RS_crash error => (s, R_crash error)
          | _ => (s, R_crash C_error)
          end
    end
  end.
