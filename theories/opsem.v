(** Wasm operational semantics **)
(** The interpreter in the [interpreter] module is an executable version of this operational semantics. **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Coq Require Import ZArith.BinInt NArith.BinNat.
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
Let host_state := host_state host_instance.

Inductive reduce_simple : seq administrative_instruction -> seq administrative_instruction -> Prop :=

(** unop **)
  | rs_unop : forall v op t,
    reduce_simple [::$VA v; AI_basic (BI_unop t op)] [::$VA (@app_unop op v)]
                   
(** binop **)
  | rs_binop_success : forall v1 v2 v op t,
    app_binop op v1 v2 = Some v ->
    reduce_simple [::$VA v1; $VA v2; AI_basic (BI_binop t op)] [::$VA v]
  | rs_binop_failure : forall v1 v2 op t,
    app_binop op v1 v2 = None ->
    reduce_simple [::$VA v1; $VA v2; AI_basic (BI_binop t op)] [::AI_trap]
                  
  (** testops **)
  | rs_testop_i32 :
    forall c testop,
    reduce_simple [::$VA (VAL_int32 c); AI_basic (BI_testop T_i32 testop)] [::$VA (VAL_int32 (wasm_bool (@app_testop_i i32t testop c)))]
  | rs_testop_i64 :
    forall c testop,
    reduce_simple [::$VA (VAL_int64 c); AI_basic (BI_testop T_i64 testop)] [::$VA (VAL_int32 (wasm_bool (@app_testop_i i64t testop c)))]

  (** relops **)
  | rs_relop: forall v1 v2 t op,
    reduce_simple [::$VA v1; $VA v2; AI_basic (BI_relop t op)] [::$VA (VAL_int32 (wasm_bool (app_relop op v1 v2)))]
                    
  (** convert and reinterpret **)
  | rs_convert_success :
    forall t1 t2 v v' sx,
    types_agree (T_num t1) (VAL_num v) ->
    cvt t2 sx v = Some v' ->
    reduce_simple [::$VA v; AI_basic (BI_cvtop t2 CVO_convert t1 sx)] [::$VA v']
  | rs_convert_failure :
    forall t1 t2 v sx,
    types_agree (T_num t1) (VAL_num v) ->
    cvt t2 sx v = None ->
    reduce_simple [::$VA v; AI_basic (BI_cvtop t2 CVO_convert t1 sx)] [::AI_trap]
  | rs_reinterpret :
    forall t1 t2 v,
    types_agree (T_num t1) (VAL_num v) ->
    reduce_simple [::$VA v; AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] [::$VA (wasm_deserialise (bits v) t2)]

  (** control-flow operations **)
  | rs_unreachable :
    reduce_simple [::AI_basic BI_unreachable] [::AI_trap]
  | rs_nop :
    reduce_simple [::AI_basic BI_nop] [::]
  | rs_drop :
    forall v,
    reduce_simple [::$VA v; AI_basic BI_drop] [::]
  | rs_select_false :
    forall n v1 v2 ot,
    n = Wasm_int.int_zero i32m ->
    reduce_simple [::$VA v1; $VA v2; $VA (VAL_int32 n); AI_basic (BI_select ot)] [::$VA v2]
  | rs_select_true :
    forall n v1 v2 ot,
    n <> Wasm_int.int_zero i32m ->
    reduce_simple [::$VA v1; $VA v2; $VA (VAL_int32 n); AI_basic (BI_select ot)] [::$VA v1]
  | rs_label_const :
      forall n es vs,
        const_list vs ->
        reduce_simple [::AI_label n es vs] vs
  | rs_label_trap :
      forall n es,
        reduce_simple [::AI_label n es [::AI_trap]] [::AI_trap]
  | rs_br :
      forall n vs es (i: labelidx) LI (lh: lholed i),
        const_list vs ->
        length vs = n ->
        lfilled lh (vs ++ [::AI_basic (BI_br i)]) LI ->
        reduce_simple [::AI_label n es LI] (vs ++ es)
  | rs_br_if_false :
      forall n i,
        n = Wasm_int.int_zero i32m ->
        reduce_simple [::$VA (VAL_int32 n); AI_basic (BI_br_if i)] [::]
  | rs_br_if_true :
      forall n i,
        n <> Wasm_int.int_zero i32m ->
        reduce_simple [::$VA (VAL_int32 n); AI_basic (BI_br_if i)] [::AI_basic (BI_br i)]
  | rs_br_table :
      forall iss c i j,
        length iss > Wasm_int.nat_of_uint i32m c ->
        List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
        reduce_simple [::$VA (VAL_int32 c); AI_basic (BI_br_table iss i)] [::AI_basic (BI_br j)]
  | rs_br_table_length :
      forall iss c i,
        length iss <= (Wasm_int.nat_of_uint i32m c) ->
        reduce_simple [::$VA (VAL_int32 c); AI_basic (BI_br_table iss i)] [::AI_basic (BI_br i)]
  | rs_local_const :
      forall es n f,
        const_list es ->
        length es = n ->
        reduce_simple [::AI_local n f es] es
  | rs_local_trap :
      forall n f,
        reduce_simple [::AI_local n f [::AI_trap]] [::AI_trap]
  | rs_return :
      forall n (i: labelidx) vs es (lh: lholed i) f,
        const_list vs ->
        length vs = n ->
        lfilled lh (vs ++ [::AI_basic BI_return]) es ->
        reduce_simple [::AI_local n f es] vs
  | rs_tee_local :
      forall i v,
        is_const v ->
        reduce_simple [::v; AI_basic (BI_local_tee i)] [::v; v; AI_basic (BI_local_set i)]
  | rs_trap :
      forall es (lh: lholed 0),
        es <> [::AI_trap] ->
        lfilled lh [::AI_trap] es ->
        reduce_simple es [::AI_trap]
  .


Inductive reduce : host_state -> store_record -> frame -> list administrative_instruction ->
                   host_state -> store_record -> frame -> list administrative_instruction -> Prop :=
  | r_simple :
      forall e e' s f hs,
        reduce_simple e e' ->
        reduce hs s f e hs s f e'
  | r_block :
    forall hs s f vs es n m tb t1s t2s,
      expand f.(f_inst) tb = Some (Tf t1s t2s) ->
      const_list vs ->
      length vs = n ->
      length t1s = n ->
      length t2s = m ->
      reduce hs s f (vs ++ [::AI_basic (BI_block tb es)]) hs s f [::AI_label m [::] (vs ++ to_e_list es)]
  | rs_loop :
      forall hs s f vs es n m tb t1s t2s,
      expand f.(f_inst) tb = Some (Tf t1s t2s) ->
      const_list vs ->
      length vs = n ->
      length t1s = n ->
      length t2s = m ->
      reduce hs s f (vs ++ [::AI_basic (BI_loop tb es)]) hs s f [::AI_label n [::AI_basic (BI_loop tb es)] (vs ++ to_e_list es)]
  | rs_if_false :
    forall hs s f c vs es1 es2 n m tb t1s t2s,
      expand f.(f_inst) tb = Some (Tf t1s t2s) ->
      c = Wasm_int.int_zero i32m ->
      const_list vs ->
      length vs = m ->
      length t1s = m ->
      length t2s = n ->
      reduce hs s f (vs ++ [::$VA (VAL_int32 c); AI_basic (BI_if tb es1 es2)]) hs s f [::AI_label n [::] (vs ++ to_e_list es2)]
  | rs_if_true :
    forall hs s f c vs es1 es2 n m tb t1s t2s,
      expand f.(f_inst) tb = Some (Tf t1s t2s) ->
      c <> Wasm_int.int_zero i32m ->
      const_list vs ->
      length vs = m ->
      length t1s = m ->
      length t2s = n ->
      reduce hs s f (vs ++ [::$VA (VAL_int32 c); AI_basic (BI_if tb es1 es2)]) hs s f [::AI_label n [::] (vs ++ to_e_list es1)]
  (** calling operations **)
  | r_call :
      forall s f (i: funcidx) a hs,
        List.nth_error f.(f_inst).(inst_funcs) i = Some a ->
        reduce hs s f [::AI_basic (BI_call i)] hs s f [::AI_invoke a]
  | r_call_indirect_success :
      forall s f x (y: typeidx) a cl i hs,
        stab_elem s f.(f_inst) x (Wasm_int.nat_of_uint i32m i) = Some (VAL_ref_func a) ->
        List.nth_error s.(s_funcs) a = Some cl ->
        List.nth_error f.(f_inst).(inst_types) y = Some (cl_type cl) ->
        reduce hs s f [::$VA (VAL_int32 i); AI_basic (BI_call_indirect x y)] hs s f [::AI_invoke a]
  | r_call_indirect_failure1 :
      forall s f x (y: typeidx) a cl i hs,
        stab_elem s f.(f_inst) x (Wasm_int.nat_of_uint i32m i) = Some (VAL_ref_func a) ->
        List.nth_error s.(s_funcs) a = Some cl ->
        List.nth_error f.(f_inst).(inst_types) y <> Some (cl_type cl) ->
        reduce hs s f [::$VA (VAL_int32 i); AI_basic (BI_call_indirect x y)] hs s f [::AI_trap]
  | r_call_indirect_failure2 :
      forall s f x (y: typeidx) a i hs,
        stab_elem s f.(f_inst) x (Wasm_int.nat_of_uint i32m i) = Some (VAL_ref_func a) ->
        List.nth_error s.(s_funcs) a = None ->
        reduce hs s f [::$VA (VAL_int32 i); AI_basic (BI_call_indirect x y)] hs s f [::AI_trap]
  | r_call_indirect_failure3 :
      forall s f x (y: typeidx) i hs,
        stab_elem s f.(f_inst) x (Wasm_int.nat_of_uint i32m i) = None ->
        reduce hs s f [::$VA (VAL_int32 i); AI_basic (BI_call_indirect x y)] hs s f [::AI_trap]
  | r_call_indirect_failure4 :
      forall s f x (y: typeidx) i hs t,
        stab_elem s f.(f_inst) x (Wasm_int.nat_of_uint i32m i) = Some (VAL_ref_null t) ->
        reduce hs s f [::$VA (VAL_int32 i); AI_basic (BI_call_indirect x y)] hs s f [::AI_trap]
  | r_invoke_native :
      forall a cl t1s t2s ts es ves vcs n m k zs s f f' i hs,
        List.nth_error s.(s_funcs) (N.to_nat a) = Some cl ->
        cl = FC_func_native i (Tf t1s t2s) ts es ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length ts = k ->
        length t1s = n ->
        length t2s = m ->
        n_zeros ts = zs ->
        f'.(f_inst) = i ->
        f'.(f_locs) = vcs ++ zs ->
        reduce hs s f (ves ++ [::AI_invoke a]) hs s f [::AI_local m f' [::AI_label m [::] (to_e_list es)]]
  | r_invoke_host_success :
      forall a cl h t1s t2s ves vcs m n s s' r f hs hs',
        List.nth_error s.(s_funcs) (N.to_nat a) = Some cl ->
        cl = FC_func_host (Tf t1s t2s) h ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length t1s = n ->
        length t2s = m ->
        host_application hs s (Tf t1s t2s) h vcs hs' (Some (s', r)) ->
        reduce hs s f (ves ++ [::AI_invoke a]) hs' s' f (result_to_stack r)
  | r_invoke_host_diverge :
      forall a cl t1s t2s h ves vcs n m s f hs hs',
        List.nth_error s.(s_funcs) (N.to_nat a) = Some cl ->
        cl = FC_func_host (Tf t1s t2s) h ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length t1s = n ->
        length t2s = m ->
        host_application hs s (Tf t1s t2s) h vcs hs' None ->
        reduce hs s f (ves ++ [::AI_invoke a]) hs' s f (ves ++ [::AI_invoke a])

  (** get, set, load, and store operations **)
  | r_local_get :
      forall f v j s hs,
        List.nth_error f.(f_locs) (N.to_nat j) = Some v ->
        reduce hs s f [::AI_basic (BI_local_get j)] hs s f [::AI_basic (BI_const v)]
  | r_local_set :
      forall f f' i v s vd hs,
        f'.(f_inst) = f.(f_inst) ->
        N.to_nat i < length f.(f_locs) ->
        f'.(f_locs) = set_nth vd f.(f_locs) (N.to_nat i) v ->
        reduce hs s f [::AI_basic (BI_const v); AI_basic (BI_local_set i)] hs s f' [::]
  | r_global_get :
      forall s f i v hs,
        sglob_val s f.(f_inst) (N.to_nat i) = Some v ->
        reduce hs s f [::AI_basic (BI_global_get i)] hs s f [::AI_basic (BI_const v)]
  | r_global_set :
      forall s f i v s' hs,
        supdate_glob s f.(f_inst) (N.to_nat i) v = Some s' ->
        reduce hs s f [::AI_basic (BI_const v); AI_basic (BI_global_set i)] hs s' f [::]
               
  (** table **)
  | r_table_get_success :
    forall x i tabv s f hs,
      stab_elem s f.(f_inst) x (Wasm_int.nat_of_uint i32m i) = Some tabv ->
      reduce hs s f [::$VA (VAL_int32 i); AI_basic (BI_table_get x)] hs s f [::AI_basic (BI_const (VAL_ref tabv))]
  | r_table_get_failure :
    forall x i s f hs,
      stab_elem s f.(f_inst) x (Wasm_int.nat_of_uint i32m i) = None ->
      reduce hs s f [::$VA (VAL_int32 i); AI_basic (BI_table_get x)] hs s f [::AI_trap]
  | r_table_set_success :
    forall x i tabv s s' f hs,
      stab_update s f.(f_inst) x (Wasm_int.nat_of_uint i32m i) tabv = Some s' ->
      reduce hs s f [::$VA (VAL_int32 i); AI_basic (BI_const (VAL_ref tabv)); AI_basic (BI_table_set x)] hs s' f [::]
  | r_table_set_failure :
    forall x i tabv s s' f hs,
      stab_update s f.(f_inst) x (Wasm_int.nat_of_uint i32m i) tabv = None ->
      reduce hs s f [::$VA (VAL_int32 i); AI_basic (BI_const (VAL_ref tabv)); AI_basic (BI_table_set x)] hs s' f [::]
             
  (** memory **)
  | r_load_success :
    forall s i f t bs k a off m hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load m (Wasm_int.N_of_uint i32m k) off (tnum_length t) = Some bs ->
      reduce hs s f [::$VA (VAL_int32 k); AI_basic (BI_load t None a off)] hs s f [::$VA (wasm_deserialise bs t)]
  | r_load_failure :
    forall s i f t k a off m hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load m (Wasm_int.N_of_uint i32m k) off (tnum_length t) = None ->
      reduce hs s f [::$VA (VAL_int32 k); AI_basic (BI_load t None a off)] hs s f [::AI_trap]
  | r_load_packed_success :
    forall s i f t tp k a off m bs sx hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load_packed sx m (Wasm_int.N_of_uint i32m k) off (tp_length tp) (tnum_length t) = Some bs ->
      reduce hs s f [::$VA (VAL_int32 k); AI_basic (BI_load t (Some (tp, sx)) a off)] hs s f [::$VA (wasm_deserialise bs t)]
  | r_load_packed_failure :
    forall s i f t tp k a off m sx hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load_packed sx m (Wasm_int.N_of_uint i32m k) off (tp_length tp) (tnum_length t) = None ->
      reduce hs s f [::$VA (VAL_int32 k); AI_basic (BI_load t (Some (tp, sx)) a off)] hs s f [::AI_trap]
  | r_store_success :
    forall t v s i f mem' k a off m hs,
      typeof_num v = t ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store m (Wasm_int.N_of_uint i32m k) off (bits v) (tnum_length t) = Some mem' ->
      reduce hs s f [::$VA (VAL_int32 k); $VA v; AI_basic (BI_store t None a off)] hs (upd_s_mem s (set_nth mem' s.(s_mems) i mem')) f [::]
  | r_store_failure :
    forall t v s i f m k off a hs,
      typeof_num v = t ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store m (Wasm_int.N_of_uint i32m k) off (bits v) (tnum_length t) = None ->
      reduce hs s f [::$VA (VAL_int32 k); $VA v; AI_basic (BI_store t None a off)] hs s f [::AI_trap]
  | r_store_packed_success :
    forall t v s i f m k off a mem' tp hs,
      typeof_num v = t ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp) = Some mem' ->
      reduce hs s f [::$VA (VAL_int32 k); $VA v; AI_basic (BI_store t (Some tp) a off)] hs (upd_s_mem s (set_nth mem' s.(s_mems) i mem')) f [::]
  | r_store_packed_failure :
    forall t v s i f m k off a tp hs,
      typeof_num v = t ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp) = None ->
      reduce hs s f [::$VA (VAL_int32 k); $VA v; AI_basic (BI_store t (Some tp) a off)] hs s f [::AI_trap]
  | r_memory_size :
      forall i f m n s hs,
        smem_ind s f.(f_inst) = Some i ->
        List.nth_error s.(s_mems) i = Some m ->
        mem_size m = n ->
        reduce hs s f [::AI_basic (BI_memory_size)] hs s f [::$VA (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n)))]
  | r_memory_grow_success :
    forall s i f m n mem' c hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      mem_size m = n ->
      mem_grow m (Wasm_int.N_of_uint i32m c) = Some mem' ->
      reduce hs s f [::$VA (VAL_int32 c); AI_basic BI_memory_grow] hs (upd_s_mem s (set_nth mem' s.(s_mems) i mem')) f [::$VA (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n)))]
  | r_memory_grow_failure :
      forall i f m n s c hs,
        smem_ind s f.(f_inst) = Some i ->
        List.nth_error s.(s_mems) i = Some m ->
        mem_size m = n ->
        reduce hs s f [::$VA (VAL_int32 c); AI_basic BI_memory_grow] hs s f [::$VA (VAL_int32 int32_minus_one)]
  (** label and local **)
  | r_label :
      forall k s f es les s' f' es' les' (lh: lholed k) hs hs',
        reduce hs s f es hs' s' f' es' ->
        lfilled lh es les ->
        lfilled lh es' les' ->
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

