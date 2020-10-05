(** Wasm operational semantics **)
(** The interpreter in the [interpreter] module is an executable version of this operational semantics. **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Coq Require Import ZArith.BinInt.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Export operations host.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Host.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record := store_record host_function.
Let administrative_instruction := administrative_instruction host_function.
Let host_state := host_state host_instance.

Inductive reduce_simple : seq administrative_instruction -> seq administrative_instruction -> Prop :=

(** unop **)
  | rs_unop : forall v op t,
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_unop t op)] [::AI_basic (BI_const (@app_unop op v))]
                   
(** binop **)
  | rs_binop_success : forall v1 v2 v op t,
    app_binop op v1 v2 = Some v ->
    reduce_simple [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] [::AI_basic (BI_const v)]
  | rs_binop_failure : forall v1 v2 op t,
    app_binop op v1 v2 = None ->
    reduce_simple [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] [::AI_trap]
                  
  (** testops **)
  | rs_testop_i32 :
    forall c testop,
    reduce_simple [::AI_basic (BI_const (ConstInt32 c)); AI_basic (BI_testop T_i32 testop)] [::AI_basic (BI_const (ConstInt32 (wasm_bool (@app_testop_i i32t testop c))))]
  | rs_testop_i64 :
    forall c testop,
    reduce_simple [::AI_basic (BI_const (ConstInt64 c)); AI_basic (BI_testop T_i64 testop)] [::AI_basic (BI_const (ConstInt32 (wasm_bool (@app_testop_i i64t testop c))))]

  (** relops **)
  | rs_relop: forall v1 v2 t op,
    reduce_simple [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] [::AI_basic (BI_const (ConstInt32 (wasm_bool (app_relop op v1 v2))))]
                    
  (** convert and reinterpret **)
  | rs_convert_success :
    forall t1 t2 v v' sx,
    types_agree t1 v ->
    cvt t2 sx v = Some v' ->
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] [::AI_basic (BI_const v')]
  | rs_convert_failure :
    forall t1 t2 v sx,
    types_agree t1 v ->
    cvt t2 sx v = None ->
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] [::AI_trap]
  | rs_reinterpret :
    forall t1 t2 v,
    types_agree t1 v ->
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] [::AI_basic (BI_const (wasm_deserialise (bits v) t2))]

  (** control-flow operations **)
  | rs_unreachable :
    reduce_simple [::AI_basic BI_unreachable] [::AI_trap]
  | rs_nop :
    reduce_simple [::AI_basic BI_nop] [::]
  | rs_drop :
    forall v,
    reduce_simple [::AI_basic (BI_const v); AI_basic BI_drop] [::]
  | rs_select_false :
    forall n v1 v2,
    n = Wasm_int.int_zero i32m ->
    reduce_simple [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (ConstInt32 n)); AI_basic BI_select] [::AI_basic (BI_const v2)]
  | rs_select_true :
    forall n v1 v2,
    n <> Wasm_int.int_zero i32m ->
    reduce_simple [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (ConstInt32 n)); AI_basic BI_select] [::AI_basic (BI_const v1)]
  | rs_block :
      forall vs es n m t1s t2s,
        const_list vs ->
        length vs = n ->
        length t1s = n ->
        length t2s = m ->
        reduce_simple (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) [::AI_label m [::] (vs ++ to_e_list es)]
  | rs_loop :
      forall vs es n m t1s t2s,
        const_list vs ->
        length vs = n ->
        length t1s = n ->
        length t2s = m ->
        reduce_simple (vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)]) [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)]
  | rs_if_false :
      forall n tf e1s e2s,
        n = Wasm_int.int_zero i32m ->
        reduce_simple ([::AI_basic (BI_const (ConstInt32 n)); AI_basic (BI_if tf e1s e2s)]) [::AI_basic (BI_block tf e2s)]
  | rs_if_true :
      forall n tf e1s e2s,
        n <> Wasm_int.int_zero i32m ->
        reduce_simple ([::AI_basic (BI_const (ConstInt32 n)); AI_basic (BI_if tf e1s e2s)]) [::AI_basic (BI_block tf e1s)]
  | rs_label_const :
      forall n es vs,
        const_list vs ->
        reduce_simple [::AI_label n es vs] vs
  | rs_label_trap :
      forall n es,
        reduce_simple [::AI_label n es [::AI_trap]] [::AI_trap]
  | rs_br :
      forall n vs es i LI lh,
        const_list vs ->
        length vs = n ->
        lfilled i lh (vs ++ [::AI_basic (BI_br i)]) LI ->
        reduce_simple [::AI_label n es LI] (vs ++ es)
  | rs_br_if_false :
      forall n i,
        n = Wasm_int.int_zero i32m ->
        reduce_simple [::AI_basic (BI_const (ConstInt32 n)); AI_basic (BI_br_if i)] [::]
  | rs_br_if_true :
      forall n i,
        n <> Wasm_int.int_zero i32m ->
        reduce_simple [::AI_basic (BI_const (ConstInt32 n)); AI_basic (BI_br_if i)] [::AI_basic (BI_br i)]
  | rs_br_table : (* ??? *)
      forall iss c i j,
        length iss > Wasm_int.nat_of_uint i32m c ->
        List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
        reduce_simple [::AI_basic (BI_const (ConstInt32 c)); AI_basic (BI_br_table iss i)] [::AI_basic (BI_br j)]
  | rs_br_table_length :
      forall iss c i,
        length iss <= (Wasm_int.nat_of_uint i32m c) ->
        reduce_simple [::AI_basic (BI_const (ConstInt32 c)); AI_basic (BI_br_table iss i)] [::AI_basic (BI_br i)]
  | rs_local_const :
      forall es n f,
        const_list es ->
        length es = n ->
        reduce_simple [::AI_local n f es] es
  | rs_local_trap :
      forall n f,
        reduce_simple [::AI_local n f [::AI_trap]] [::AI_trap]
  | rs_return : (* ??? *)
      forall n i vs es lh f,
        const_list vs ->
        length vs = n ->
        lfilled i lh (vs ++ [::AI_basic BI_return]) es ->
        reduce_simple [::AI_local n f es] vs
  | rs_tee_local :
      forall i v,
        is_const v ->
        reduce_simple [::v; AI_basic (BI_tee_local i)] [::v; v; AI_basic (BI_set_local i)]
  | rs_trap :
      forall es lh,
        es <> [::AI_trap] ->
        lfilled 0 lh [::AI_trap] es ->
        reduce_simple es [::AI_trap]
  .

(*
Inductive reduce : store_record -> list value -> list administrative_instruction -> instance -> store_record -> list value -> list administrative_instruction -> Prop :=
| r_simple :
    forall e e' s vs i,
      reduce_simple e e' ->
      reduce s vs e i s vs e'
| r_call :
    forall s vs i j f,
      sfunc s i j = Some f ->
      reduce s vs [::AI_basic (Call j)] i s vs [::Invoke f]
| r_call_indirect_success :
    forall s i j cl c vs tf,
      stab s i (Wasm_int.nat_of_uint i32m c) = Some cl ->
      stypes s i j = Some tf ->
      cl_type cl = tf ->
      reduce s vs [::AI_basic (BI_const (ConstInt32 c)); AI_basic (Call_indirect j)] i s vs [::Invoke cl]
| r_call_indirect_failure1 :
    forall s i j c cl vs,
      stab s i (Wasm_int.nat_of_uint i32m c) = Some cl ->
      stypes s i j <> Some (cl_type cl) ->
      reduce s vs [::AI_basic (BI_const (ConstInt32 c)); AI_basic (Call_indirect j)] i s vs [::AI_trap]
| r_call_indirect_failure2 :
    forall s i j c vs,
      stab s i (Wasm_int.nat_of_uint i32m c) = None ->
      reduce s vs [::AI_basic (BI_const (ConstInt32 c)); AI_basic (Call_indirect j)] i s vs [::AI_trap]
| r_invoke_native :
    forall cl t1s t2s ts es ves vcs n m k zs vs s i j,
      cl = Func_native j (Tf t1s t2s) ts es ->
      ves = v_to_e_list vcs ->
      length vcs = n ->
      length ts = k ->
      length t1s = n ->
      length t2s = m ->
      n_zeros ts = zs ->
      reduce s vs (ves ++ [::Invoke cl]) i s vs [::Local m j (vcs ++ zs) [::AI_basic (Block (Tf [::] t2s) es)]]
| r_invoke_host_success :
    forall cl f t1s t2s ves vcs m n s s' vcs' vs i,
      cl = Func_host (Tf t1s t2s) f ->
      ves = v_to_e_list vcs ->
      length vcs = n ->
      length t1s = n ->
      length t2s = m ->
      host_apply s (Tf t1s t2s) f vcs (* FIXME: hs *) = Some (s', vcs') ->
      reduce s vs (ves ++ [::Invoke cl]) i s' vs (v_to_e_list vcs')
| r_invoke_host_failure :
    forall cl t1s t2s f ves vcs n m s vs i,
      cl = Func_host (Tf t1s t2s) f ->
      ves = v_to_e_list vcs ->
      length vcs = n ->
      length t1s = n ->
      length t2s = m ->
      reduce s vs (ves ++ [::Invoke cl]) i s vs [::AI_trap]
| r_get_local :
    forall vi v vs i j s,
      length vi = j ->
      reduce s (vi ++ [::v] ++ vs) [::AI_basic (Get_local j)] i s (vi ++ [::v] ++ vs) [::AI_basic (BI_const v)]
| r_set_local :
    forall vs j v i s vd,
      length vs > j ->
      reduce s vs [::AI_basic (BI_const v); AI_basic (Set_local j)] i s (set_nth vd vs j v) [::]
| r_get_global :
    forall s vs j i v,
      sglob_val s i j = Some v ->
      reduce s vs [::AI_basic (Get_global j)] i s vs [::AI_basic (BI_const v)]
| r_set_global :
    forall s i j v s' vs,
      supdate_glob s i j v = Some s' ->
      reduce s vs [::AI_basic (BI_const v); AI_basic (Set_global j)] i s' vs [::]
| r_load_success :
    forall s i t bs vs k a off m j,
      smem_ind s i = Some j ->
      List.nth_error s.(s_mems) j = Some m ->
      load m (Wasm_int.N_of_uint i32m k) off (t_length t) = Some bs ->
      reduce s vs [::AI_basic (BI_const (ConstInt32 k)); AI_basic (Load t None a off)] i s vs [::AI_basic (BI_const (wasm_deserialise bs t))]
| r_load_failure :
    forall s i t vs k a off m j,
      smem_ind s i = Some j ->
      List.nth_error s.(s_mems) j = Some m ->
      load m (Wasm_int.N_of_uint i32m k) off (t_length t) = None ->
      reduce s vs [::AI_basic (BI_const (ConstInt32 k)); AI_basic (Load t None a off)] i s vs [::AI_trap]
| r_load_packed_success :
    forall s i t tp vs k a off m j bs sx,
      smem_ind s i = Some j ->
      List.nth_error s.(s_mems) j = Some m ->
      load_packed sx m (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t) = Some bs ->
      reduce s vs [::AI_basic (BI_const (ConstInt32 k)); AI_basic (Load t (Some (tp, sx)) a off)] i s vs [::AI_basic (BI_const (wasm_deserialise bs t))]
| r_load_packed_failure :
    forall s i t tp vs k a off m j sx,
      smem_ind s i = Some j ->
      List.nth_error s.(s_mems) j = Some m ->
      load_packed sx m (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t) = None ->
      reduce s vs [::AI_basic (BI_const (ConstInt32 k)); AI_basic (Load t (Some (tp, sx)) a off)] i s vs [::AI_trap]
| r_store_success :
    forall t v s i j vs mem' k a off m,
      types_agree t v ->
      smem_ind s i = Some j ->
      List.nth_error s.(s_mems) j = Some m ->
      store m (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) = Some mem' ->
      reduce s vs [::AI_basic (BI_const (ConstInt32 k)); AI_basic (BI_const v); AI_basic (Store t None a off)] i (upd_s_mem s (update_list_at s.(s_mems) j mem')) vs [::]
| r_store_failure :
    forall t v s i j m k off a vs,
      types_agree t v ->
      smem_ind s i = Some j ->
      List.nth_error s.(s_mems) j = Some m ->
      store m (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) = None ->
      reduce s vs [::AI_basic (BI_const (ConstInt32 k)); AI_basic (BI_const v); AI_basic (Store t None a off)] i s vs [::AI_trap]
| r_store_packed_success :
    forall t v s i j m k off a vs mem' tp,
      types_agree t v ->
      smem_ind s i = Some j ->
      List.nth_error s.(s_mems) j = Some m ->
      store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp) = Some mem' ->
      reduce s vs [::AI_basic (BI_const (ConstInt32 k)); AI_basic (BI_const v); AI_basic (Store t (Some tp) a off)] i (upd_s_mem s (update_list_at s.(s_mems) j mem')) vs [::]
| r_store_packed_failure :
    forall t v s i j m k off a vs tp,
      types_agree t v ->
      smem_ind s i = Some j ->
      List.nth_error s.(s_mems) j = Some m ->
      store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp) = None ->
      reduce s vs [::AI_basic (BI_const (ConstInt32 k)); AI_basic (BI_const v); AI_basic (Store t (Some tp) a off)] i s vs [::AI_trap]
| r_current_memory :
    forall i j m n s vs,
      smem_ind s i = Some j ->
      List.nth_error s.(s_mems) j = Some m ->
      mem_size m = n ->
      reduce s vs [::AI_basic (Current_memory)] i s vs [::AI_basic (BI_const (ConstInt32 (Wasm_int.int_of_Z i32m (Z.of_nat n))))]
| r_grow_memory_success :
    forall s i j m n mem' vs c,
      smem_ind s i = Some j ->
      List.nth_error s.(s_mems) j = Some m ->
      mem_size m = n ->
      mem_grow m (Wasm_int.N_of_uint i32m c) = Some mem' ->
      reduce s vs [::AI_basic (BI_const (ConstInt32 c)); AI_basic Grow_memory] i (upd_s_mem s (update_list_at s.(s_mems) j mem')) vs [::AI_basic (BI_const (ConstInt32 (Wasm_int.int_of_Z i32m (Z.of_nat n))))]
| r_grow_memory_failure :
    forall i j m n s vs c,
      smem_ind s i = Some j ->
      List.nth_error s.(s_mems) j = Some m ->
      mem_size m = n ->
      reduce s vs [::AI_basic (BI_const (ConstInt32 c)); AI_basic Grow_memory] i s vs [::AI_basic (BI_const (ConstInt32 int32_minus_one))]
| r_label :
    forall s vs es les i s' vs' es' les' k lh,
      reduce s vs es i s' vs' es' ->
      lfilled k lh es les ->
      lfilled k lh es' les' ->
      reduce s vs les i s' vs' les'
| r_local :
    forall s vs es i s' vs' es' n v0s j,
      reduce s vs es i s' vs' es' ->
      reduce s v0s [::Local n i vs es] j s' v0s [::Local n i vs' es'].
*)

Inductive reduce : host_state -> store_record -> frame -> list administrative_instruction ->
                   host_state -> store_record -> frame -> list administrative_instruction -> Prop :=
  | r_simple :
      forall e e' s f hs,
        reduce_simple e e' ->
        reduce hs s f e hs s f e'

  (** calling operations **)
  | r_call :
      forall s f i cl hs,
        sfunc s f.(f_inst) i = Some cl ->
        reduce hs s f [::AI_basic (BI_call i)] hs s f [::AI_invoke cl]
  | r_call_indirect_success :
      forall s f i cl c tf hs,
        stab s f.(f_inst) (Wasm_int.nat_of_uint i32m c) = Some cl ->
        stypes s f.(f_inst) i = Some tf ->
        cl_type cl = tf ->
        reduce hs s f [::AI_basic (BI_const (ConstInt32 c)); AI_basic (BI_call_indirect i)] hs s f [::AI_invoke cl]
  | r_call_indirect_failure1 :
      forall s f i c cl hs,
        stab s f.(f_inst) (Wasm_int.nat_of_uint i32m c) = Some cl ->
        stypes s f.(f_inst) i <> Some (cl_type cl) ->
        reduce hs s f [::AI_basic (BI_const (ConstInt32 c)); AI_basic (BI_call_indirect i)] hs s f [::AI_trap]
  | r_call_indirect_failure2 :
      forall s f i c hs,
        stab s f.(f_inst) (Wasm_int.nat_of_uint i32m c) = None ->
        reduce hs s f [::AI_basic (BI_const (ConstInt32 c)); AI_basic (BI_call_indirect i)] hs s f [::AI_trap]
  | r_invoke_native :
      forall cl t1s t2s ts es ves vcs n m k zs s f f' i hs,
        cl = FC_func_native i (Tf t1s t2s) ts es ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length ts = k ->
        length t1s = n ->
        length t2s = m ->
        n_zeros ts = zs ->
        f'.(f_inst) = i ->
        f'.(f_locs) = vcs ++ zs ->
        reduce hs s f (ves ++ [::AI_invoke cl]) hs s f [::AI_local m f' [::AI_basic (BI_block (Tf [::] t2s) es)]]
  | r_invoke_host_success :
      forall cl h t1s t2s ves vcs m n s s' r f hs hs',
        cl = FC_func_host (Tf t1s t2s) h ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length t1s = n ->
        length t2s = m ->
        host_application hs s (Tf t1s t2s) h vcs hs' (Some (s', r)) ->
        reduce hs s f (ves ++ [::AI_invoke cl]) hs' s' f (result_to_stack r)
  | r_invoke_host_diverge :
      forall cl t1s t2s h ves vcs n m s f hs hs',
        cl = FC_func_host (Tf t1s t2s) h ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length t1s = n ->
        length t2s = m ->
        host_application hs s (Tf t1s t2s) h vcs hs' None ->
        reduce hs s f (ves ++ [::AI_invoke cl]) hs' s f (ves ++ [::AI_invoke cl])

  (** get, set, load, and store operations **)
  | r_get_local :
      forall f v j s hs,
        List.nth_error f.(f_locs) j = Some v ->
        reduce hs s f [::AI_basic (BI_get_local j)] hs s f [::AI_basic (BI_const v)]
  | r_set_local :
      forall f f' i v s vd hs,
        f'.(f_inst) = f.(f_inst) ->
        f'.(f_locs) = set_nth vd f.(f_locs) i v ->
        reduce hs s f [::AI_basic (BI_const v); AI_basic (BI_set_local i)] hs s f' [::]
  | r_get_global :
      forall s f i v hs,
        sglob_val s f.(f_inst) i = Some v ->
        reduce hs s f [::AI_basic (BI_get_global i)] hs s f [::AI_basic (BI_const v)]
  | r_set_global :
      forall s f i v s' hs,
        supdate_glob s f.(f_inst) i v = Some s' ->
        reduce hs s f [::AI_basic (BI_const v); AI_basic (BI_set_global i)] hs s' f [::]
  | r_load_success :
    forall s i f t bs k a off m hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load m (Wasm_int.N_of_uint i32m k) off (t_length t) = Some bs ->
      reduce hs s f [::AI_basic (BI_const (ConstInt32 k)); AI_basic (BI_load t None a off)] hs s f [::AI_basic (BI_const (wasm_deserialise bs t))]
  | r_load_failure :
    forall s i f t k a off m hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load m (Wasm_int.N_of_uint i32m k) off (t_length t) = None ->
      reduce hs s f [::AI_basic (BI_const (ConstInt32 k)); AI_basic (BI_load t None a off)] hs s f [::AI_trap]
  | r_load_packed_success :
    forall s i f t tp k a off m bs sx hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load_packed sx m (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t) = Some bs ->
      reduce hs s f [::AI_basic (BI_const (ConstInt32 k)); AI_basic (BI_load t (Some (tp, sx)) a off)] hs s f [::AI_basic (BI_const (wasm_deserialise bs t))]
  | r_load_packed_failure :
    forall s i f t tp k a off m sx hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load_packed sx m (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t) = None ->
      reduce hs s f [::AI_basic (BI_const (ConstInt32 k)); AI_basic (BI_load t (Some (tp, sx)) a off)] hs s f [::AI_trap]
  | r_store_success :
    forall t v s i f mem' k a off m hs,
      types_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store m (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) = Some mem' ->
      reduce hs s f [::AI_basic (BI_const (ConstInt32 k)); AI_basic (BI_const v); AI_basic (BI_store t None a off)] hs (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::]
  | r_store_failure :
    forall t v s i f m k off a hs,
      types_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store m (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) = None ->
      reduce hs s f [::AI_basic (BI_const (ConstInt32 k)); AI_basic (BI_const v); AI_basic (BI_store t None a off)] hs s f [::AI_trap]
  | r_store_packed_success :
    forall t v s i f m k off a mem' tp hs,
      types_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp) = Some mem' ->
      reduce hs s f [::AI_basic (BI_const (ConstInt32 k)); AI_basic (BI_const v); AI_basic (BI_store t (Some tp) a off)] hs (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::]
  | r_store_packed_failure :
    forall t v s i f m k off a tp hs,
      types_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp) = None ->
      reduce hs s f [::AI_basic (BI_const (ConstInt32 k)); AI_basic (BI_const v); AI_basic (BI_store t (Some tp) a off)] hs s f [::AI_trap]

  (** memory **)
  | r_current_memory :
      forall i f m n s hs,
        smem_ind s f.(f_inst) = Some i ->
        List.nth_error s.(s_mems) i = Some m ->
        mem_size m = n ->
        reduce hs s f [::AI_basic (BI_current_memory)] hs s f [::AI_basic (BI_const (ConstInt32 (Wasm_int.int_of_Z i32m (Z.of_nat n))))]
  | r_grow_memory_success :
    forall s i f m n mem' c hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      mem_size m = n ->
      mem_grow m (Wasm_int.N_of_uint i32m c) = Some mem' ->
      reduce hs s f [::AI_basic (BI_const (ConstInt32 c)); AI_basic BI_grow_memory] hs (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::AI_basic (BI_const (ConstInt32 (Wasm_int.int_of_Z i32m (Z.of_nat n))))]
  | r_grow_memory_failure :
      forall i f m n s c hs,
        smem_ind s f.(f_inst) = Some i ->
        List.nth_error s.(s_mems) i = Some m ->
        mem_size m = n ->
        reduce hs s f [::AI_basic (BI_const (ConstInt32 c)); AI_basic BI_grow_memory] hs s f [::AI_basic (BI_const (ConstInt32 int32_minus_one))]

  (** label and local **)
  | r_label :
      forall s f es les s' f' es' les' k lh hs hs',
        reduce hs s f es hs' s' f' es' ->
        lfilled k lh es les ->
        lfilled k lh es' les' ->
        reduce hs s f les hs' s' f' les'
  | r_local :
      forall s f es s' f' es' n f0 hs hs',
        reduce hs s f es hs' s' f' es' ->
        reduce hs s f0 [::AI_local n f es] hs' s' f0 [::AI_local n f' es']
  .

Definition reduce_tuple hs_s_f_es hs'_s'_f'_es' : Prop :=
  let '(hs, s, f, es) := hs_s_f_es in
  let '(hs', s', f', es') := hs'_s'_f'_es' in
  reduce hs s f es hs' s' f' es'.
      
Definition reduce_trans :
    host_state * store_record * frame * seq administrative_instruction ->
    host_state * store_record * frame * seq administrative_instruction -> Prop :=
  Relations.Relation_Operators.clos_refl_trans _ reduce_tuple.

End Host.

