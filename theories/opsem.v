(** Wasm operational semantics **)
(** The interpreter in the [interpreter_func] module is an executable version of this operational semantics. **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Coq Require Import ZArith.BinInt NArith.BinNat.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Export operations host.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section Host.

Context `{ho: host}.

Inductive reduce_simple : seq administrative_instruction -> seq administrative_instruction -> Prop :=

(** unop **)
  | rs_unop : forall v op t,
    reduce_simple [::$VN v; AI_basic (BI_unop t op)] [::$VN (@app_unop op v)]
                   
(** binop **)
  | rs_binop_success : forall v1 v2 v op t,
    app_binop op v1 v2 = Some v ->
    reduce_simple [::$VN v1; $VN v2; AI_basic (BI_binop t op)] [::$VN v]
  | rs_binop_failure : forall v1 v2 op t,
    app_binop op v1 v2 = None ->
    reduce_simple [::$VN v1; $VN v2; AI_basic (BI_binop t op)] [::AI_trap]
                  
  (** testops **)
  | rs_testop_i32 :
    forall c testop,
    reduce_simple [::$VN (VAL_int32 c); AI_basic (BI_testop T_i32 testop)] [::$VN (VAL_int32 (wasm_bool (@app_testop_i i32t testop c)))]
  | rs_testop_i64 :
    forall c testop,
    reduce_simple [::$VN (VAL_int64 c); AI_basic (BI_testop T_i64 testop)] [::$VN (VAL_int32 (wasm_bool (@app_testop_i i64t testop c)))]

  (** relops **)
  | rs_relop: forall v1 v2 t op,
    reduce_simple [::$VN v1; $VN v2; AI_basic (BI_relop t op)] [::$VN (VAL_int32 (wasm_bool (app_relop op v1 v2)))]
                    
  (** cvtop **)
  | rs_convert_success :
    forall t1 t2 v v' op sx,
    types_agree (T_num t1) (VAL_num v) ->
    cvtop_valid t2 op t1 sx ->  
    eval_cvt t2 op sx v = Some v' ->
    reduce_simple [::$VN v; AI_basic (BI_cvtop t2 op t1 sx)] [::$VN v']
  | rs_convert_failure :
    forall t1 t2 v sx op,
    types_agree (T_num t1) (VAL_num v) ->
    cvtop_valid t2 op t1 sx ->  
    eval_cvt t2 op sx v = None ->
    reduce_simple [::$VN v; AI_basic (BI_cvtop t2 op t1 sx)] [::AI_trap]

  (** reference operations **)
  | rs_ref_is_null_true:
    forall t,
    reduce_simple [:: $V (VAL_ref (VAL_ref_null t)); AI_basic BI_ref_is_null] [::$VN (VAL_int32 Wasm_int.Int32.one)]
  (* This formulation might cause some difficulty in the proofs, but it's the most faithful to the spec *)
  | rs_ref_is_null_false:
    forall ref,
    (forall t, ref <> VAL_ref_null t) ->
    reduce_simple [:: $V (VAL_ref ref); AI_basic BI_ref_is_null] [::$VN (VAL_int32 Wasm_int.Int32.zero)]
                  
  (** control-flow operations **)
  | rs_unreachable :
    reduce_simple [::AI_basic BI_unreachable] [::AI_trap]
  | rs_nop :
    reduce_simple [::AI_basic BI_nop] [::]
  | rs_drop :
    forall v,
    reduce_simple [::$V v; AI_basic BI_drop] [::]
  | rs_select_false :
    forall n v1 v2 ot,
    n = Wasm_int.int_zero i32m ->
    reduce_simple [::$V v1; $V v2; $VN (VAL_int32 n); AI_basic (BI_select ot)] [::$V v2]
  | rs_select_true :
    forall n v1 v2 ot,
    n <> Wasm_int.int_zero i32m ->
    reduce_simple [::$V v1; $V v2; $VN (VAL_int32 n); AI_basic (BI_select ot)] [::$V v1]
  | rs_label_const :
      forall n es vs,
        const_list vs ->
        reduce_simple [::AI_label n es vs] vs
  | rs_label_trap :
      forall n es,
        reduce_simple [::AI_label n es [::AI_trap]] [::AI_trap]
  | rs_if_false :
    forall c tb es1 es2,
      c = Wasm_int.int_zero i32m ->
      reduce_simple ([::$VN (VAL_int32 c); AI_basic (BI_if tb es1 es2)]) [::AI_basic (BI_block tb es2)]
  | rs_if_true :
    forall c tb es1 es2,
      c <> Wasm_int.int_zero i32m ->
      reduce_simple ([::$VN (VAL_int32 c); AI_basic (BI_if tb es1 es2)]) [::AI_basic (BI_block tb es1)]
  | rs_br :
      forall n vs es i LI (lh: lholed i),
        const_list vs ->
        length vs = n ->
        lfill lh (vs ++ [::AI_basic (BI_br (N.of_nat i))]) = LI ->
        reduce_simple [::AI_label n es LI] (vs ++ es)
  | rs_br_if_false :
      forall n i,
        n = Wasm_int.int_zero i32m ->
        reduce_simple [::$VN (VAL_int32 n); AI_basic (BI_br_if i)] [::]
  | rs_br_if_true :
      forall n i,
        n <> Wasm_int.int_zero i32m ->
        reduce_simple [::$VN (VAL_int32 n); AI_basic (BI_br_if i)] [::AI_basic (BI_br i)]
  | rs_br_table :
      forall iss c i j,
        N.lt (Wasm_int.N_of_uint i32m c) (N.of_nat (length iss)) ->
        lookup_N iss (Wasm_int.N_of_uint i32m c) = Some j ->
        reduce_simple [::$VN (VAL_int32 c); AI_basic (BI_br_table iss i)] [::AI_basic (BI_br j)]
  | rs_br_table_length :
      forall iss c i,
        N.le (N.of_nat (length iss)) (Wasm_int.N_of_uint i32m c) ->
        reduce_simple [::$VN (VAL_int32 c); AI_basic (BI_br_table iss i)] [::AI_basic (BI_br i)]
  | rs_local_const :
      forall es n f,
        const_list es ->
        length es = n ->
        reduce_simple [::AI_frame n f es] es
  | rs_local_trap :
      forall n f,
        reduce_simple [::AI_frame n f [::AI_trap]] [::AI_trap]
  | rs_local_tee :
      forall i v,
        reduce_simple [::$V v; AI_basic (BI_local_tee i)] [::$V v; $V v; AI_basic (BI_local_set i)]
  | rs_return :
      forall n i vs es (lh: lholed i) f,
        const_list vs ->
        length vs = n ->
        lfill lh (vs ++ [::AI_basic BI_return]) = es ->
        reduce_simple [::AI_frame n f es] vs
  | rs_trap :
      forall es (lh: lholed 0),
        es <> [::AI_trap] ->
        lfill lh [::AI_trap] = es ->
        reduce_simple es [::AI_trap]
.

Inductive reduce : host_state -> store_record -> frame -> list administrative_instruction ->
                   host_state -> store_record -> frame -> list administrative_instruction -> Prop :=
  | r_simple :
      forall e e' s f hs,
        reduce_simple e e' ->
        reduce hs s f e hs s f e'
  | r_ref_func:
    forall hs s f addr x,
      lookup_N f.(f_inst).(inst_funcs) x = Some addr ->
      reduce hs s f [::AI_basic (BI_ref_func x)] hs s f [::AI_ref addr]
  | r_block :
    forall hs s f vs es n m tb t1s t2s,
      expand f.(f_inst) tb = Some (Tf t1s t2s) ->
      const_list vs ->
      length vs = n ->
      length t1s = n ->
      length t2s = m ->
      reduce hs s f (vs ++ [::AI_basic (BI_block tb es)]) hs s f [::AI_label m [::] (vs ++ to_e_list es)]
  | r_loop :
      forall hs s f vs es n m tb t1s t2s,
      expand f.(f_inst) tb = Some (Tf t1s t2s) ->
      const_list vs ->
      length vs = n ->
      length t1s = n ->
      length t2s = m ->
      reduce hs s f (vs ++ [::AI_basic (BI_loop tb es)]) hs s f [::AI_label n [::AI_basic (BI_loop tb es)] (vs ++ to_e_list es)]
  (** calling operations **)
  | r_call :
      forall s f (i: funcidx) a hs,
        lookup_N f.(f_inst).(inst_funcs) i = Some a ->
        reduce hs s f [::AI_basic (BI_call i)] hs s f [::AI_invoke a]
  | r_call_indirect_success :
      forall s f x (y: typeidx) a cl i hs,
        stab_elem s f.(f_inst) x (Wasm_int.N_of_uint i32m i) = Some (VAL_ref_func a) ->
        lookup_N s.(s_funcs) a = Some cl ->
        lookup_N f.(f_inst).(inst_types) y = Some (cl_type cl) ->
        reduce hs s f [::$VN (VAL_int32 i); AI_basic (BI_call_indirect x y)] hs s f [::AI_invoke a]
  | r_call_indirect_failure_mismatch :
      forall s f x (y: typeidx) a cl i hs,
        stab_elem s f.(f_inst) x (Wasm_int.N_of_uint i32m i) = Some (VAL_ref_func a) ->
        lookup_N s.(s_funcs) a = Some cl ->
        lookup_N f.(f_inst).(inst_types) y <> Some (cl_type cl) ->
        reduce hs s f [::$VN (VAL_int32 i); AI_basic (BI_call_indirect x y)] hs s f [::AI_trap]
  | r_call_indirect_failure_bound :
      forall s f x (y: typeidx) i hs,
        stab_elem s f.(f_inst) x (Wasm_int.N_of_uint i32m i) = None ->
        reduce hs s f [::$VN (VAL_int32 i); AI_basic (BI_call_indirect x y)] hs s f [::AI_trap]
  | r_call_indirect_failure_null_ref :
      forall s f x (y: typeidx) i hs t,
        stab_elem s f.(f_inst) x (Wasm_int.N_of_uint i32m i) = Some (VAL_ref_null t) ->
        reduce hs s f [::$VN (VAL_int32 i); AI_basic (BI_call_indirect x y)] hs s f [::AI_trap]
  | r_invoke_native :
      forall addr cl ts1 ts2 code x ts es ves vs n m k defaults s f inst hs,
        lookup_N s.(s_funcs) addr = Some cl ->
        cl = FC_func_native (Tf ts1 ts2) inst code ->
        code = Build_module_func x ts es ->
        ves = v_to_e_list vs ->
        length vs = n ->
        length ts = k ->
        length ts1 = n ->
        length ts2 = m ->
        map default_val ts = defaults ->
        reduce hs s f (ves ++ [::AI_invoke addr]) hs s f [::AI_frame m (Build_frame (vs ++ defaults) inst) [::AI_label m [::] (to_e_list es)]]
  | r_invoke_host_success :
      forall a cl h t1s t2s ves vcs m n s s' r f hs hs',
        lookup_N s.(s_funcs) a = Some cl ->
        cl = FC_func_host (Tf t1s t2s) h ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length t1s = n ->
        length t2s = m ->
        host_application hs s (Tf t1s t2s) h vcs hs' (Some (s', r)) ->
        reduce hs s f (ves ++ [::AI_invoke a]) hs' s' f (result_to_stack r)
  | r_invoke_host_diverge :
      forall a cl t1s t2s h ves vcs n m s f hs hs',
        lookup_N s.(s_funcs) a = Some cl ->
        cl = FC_func_host (Tf t1s t2s) h ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length t1s = n ->
        length t2s = m ->
        host_application hs s (Tf t1s t2s) h vcs hs' None ->
        reduce hs s f (ves ++ [::AI_invoke a]) hs' s f [::AI_trap]

  (** get, set, load, and store operations **)
  | r_local_get :
      forall f v j s hs,
        lookup_N f.(f_locs) j = Some v ->
        reduce hs s f [::AI_basic (BI_local_get j)] hs s f [::v_to_e v]
  | r_local_set :
      forall f f' i v s vd hs,
        f'.(f_inst) = f.(f_inst) ->
        N.to_nat i < length f.(f_locs) ->
        f'.(f_locs) = set_nth vd f.(f_locs) (N.to_nat i) v ->
        reduce hs s f [::v_to_e v; AI_basic (BI_local_set i)] hs s f' [::]
  | r_global_get :
      forall s f i v hs,
        sglob_val s f.(f_inst) i = Some v ->
        reduce hs s f [::AI_basic (BI_global_get i)] hs s f [::v_to_e v]
  | r_global_set :
      forall s f i v s' hs,
        supdate_glob s f.(f_inst) i v = Some s' ->
        reduce hs s f [::v_to_e v; AI_basic (BI_global_set i)] hs s' f [::]

(** table **)
| r_table_get_success :
  forall x i tabv s f hs,
    stab_elem s f.(f_inst) x (Wasm_int.N_of_uint i32m i) = Some tabv ->
    reduce hs s f [::$VN (VAL_int32 i); AI_basic (BI_table_get x)] hs s f [::v_to_e (VAL_ref tabv)]
| r_table_get_failure :
  forall x i s f hs,
    stab_elem s f.(f_inst) x (Wasm_int.N_of_uint i32m i) = None ->
    reduce hs s f [::$VN (VAL_int32 i); AI_basic (BI_table_get x)] hs s f [::AI_trap]
| r_table_set_success :
  forall x i tabv s s' f hs,
    stab_update s f.(f_inst) x (Wasm_int.N_of_uint i32m i) tabv = Some s' ->
    reduce hs s f [::$VN (VAL_int32 i); v_to_e (VAL_ref tabv); AI_basic (BI_table_set x)] hs s' f [::]
| r_table_set_failure :
  forall x i tabv s f hs,
    stab_update s f.(f_inst) x (Wasm_int.N_of_uint i32m i) tabv = None ->
    reduce hs s f [::$VN (VAL_int32 i); v_to_e (VAL_ref tabv); AI_basic (BI_table_set x)] hs s f [::AI_trap]
| r_table_size :
  forall x tab sz s f hs,
    stab s f.(f_inst) x = Some tab ->
    tab_size tab = sz ->
    reduce hs s f [:: AI_basic (BI_table_size x)] hs s f [::$VN (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat sz)))]
| r_table_grow_success :
  forall x n sz tabinit s f s' hs,
    stab_grow s f.(f_inst) x (Wasm_int.N_of_uint i32m n) tabinit = Some (s', sz) ->
    reduce hs s f [::v_to_e (VAL_ref tabinit); $VN (VAL_int32 n); AI_basic (BI_table_grow x)]
      hs s' f [::$VN (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat sz)))]
| r_table_grow_failure :
  forall x n tabinit s f hs,
    stab_grow s f.(f_inst) x (Wasm_int.N_of_uint i32m n) tabinit = None ->
    reduce hs s f [::v_to_e (VAL_ref tabinit); $VN (VAL_int32 n); AI_basic (BI_table_grow x)]
      hs s f [::$VN (VAL_int32 int32_minus_one)]
| r_table_fill_bound :
  forall x i n tab tabv s f hs,
    let i_z := Wasm_int.Z_of_uint i32m i in
    let n_z := Wasm_int.Z_of_uint i32m n in
    stab s f.(f_inst) x = Some tab ->
    (Z.add i_z n_z > Z.of_nat (tab_size tab))%Z ->
    reduce hs s f [::$VN (VAL_int32 i); v_to_e (VAL_ref tabv); $VN (VAL_int32 n); AI_basic (BI_table_fill x)]
      hs s f [::AI_trap]
| r_table_fill_return :
  forall x i n tab tabv s f hs,
    let i_z := Wasm_int.Z_of_uint i32m i in
    let n_z := Wasm_int.Z_of_uint i32m n in
    stab s f.(f_inst) x = Some tab ->
    (Z.add i_z n_z <= Z.of_nat (tab_size tab))%Z ->
    (n_z = 0)%Z ->
    reduce hs s f [::$VN (VAL_int32 i); v_to_e (VAL_ref tabv); $VN (VAL_int32 n); AI_basic (BI_table_fill x)]
      hs s f [::]
| r_table_fill_step :
  forall x i n tab tabv n' i' s f hs,
    let i_z := Wasm_int.Z_of_uint i32m i in
    let n_z := Wasm_int.Z_of_uint i32m n in
    stab s f.(f_inst) x = Some tab ->
    (Z.add i_z n_z <= Z.of_nat (tab_size tab))%Z ->
    (n_z <> 0)%Z ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    i' = Wasm_int.int_of_Z i32m (Z.add i_z 1) ->
    reduce hs s f [::$VN (VAL_int32 i); v_to_e (VAL_ref tabv); $VN (VAL_int32 n); AI_basic (BI_table_fill x)]
      hs s f [::$VN (VAL_int32 i); v_to_e (VAL_ref tabv); AI_basic (BI_table_set x);
              $VN (VAL_int32 i'); v_to_e (VAL_ref tabv); $VN (VAL_int32 n'); AI_basic (BI_table_fill x)]
| r_table_copy_bound :
  forall x y src dst n tabx taby s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    stab s f.(f_inst) x = Some tabx ->
    stab s f.(f_inst) y = Some taby ->
    ((src_z + n_z > Z.of_nat (tab_size taby))%Z \/
     (dst_z + n_z > Z.of_nat (tab_size tabx))%Z) ->
    reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_table_copy x y)]
      hs s f [::AI_trap]
| r_table_copy_return :
  forall x y src dst n tabx taby s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    stab s f.(f_inst) x = Some tabx ->
    stab s f.(f_inst) y = Some taby ->
    (src_z + n_z <= Z.of_nat (tab_size taby))%Z ->
    (dst_z + n_z <= Z.of_nat (tab_size tabx))%Z ->
    (n_z = 0)%Z ->
    reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_table_copy x y)]
      hs s f [::]
| r_table_copy_forward :
  forall x y src dst n tabx taby src' dst' n' s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    stab s f.(f_inst) x = Some tabx ->
    stab s f.(f_inst) y = Some taby ->
    (src_z + n_z <= Z.of_nat (tab_size taby))%Z ->
    (dst_z + n_z <= Z.of_nat (tab_size tabx))%Z ->
    (n_z <> 0)%Z ->
    (dst_z <= src_z)%Z ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    src' = Wasm_int.int_of_Z i32m (Z.add src_z 1) ->
    dst' = Wasm_int.int_of_Z i32m (Z.add dst_z 1) ->
    reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_table_copy x y)]
      hs s f [:: $VN (VAL_int32 dst); $VN (VAL_int32 src); AI_basic (BI_table_get y); AI_basic (BI_table_set x);
              $VN (VAL_int32 dst'); $VN (VAL_int32 src'); $VN (VAL_int32 n'); AI_basic (BI_table_copy x y)]
| r_table_copy_backward :
  forall x y src dst n tabx taby src' dst' n' s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    stab s f.(f_inst) x = Some tabx ->
    stab s f.(f_inst) y = Some taby ->
    (src_z + n_z <= Z.of_nat (tab_size taby))%Z ->
    (dst_z + n_z <= Z.of_nat (tab_size tabx))%Z ->
    (n_z <> 0)%Z ->
    (dst_z > src_z)%Z ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    src' = Wasm_int.int_of_Z i32m (Z.sub (Z.add src_z n_z) 1) ->
    dst' = Wasm_int.int_of_Z i32m (Z.sub (Z.add dst_z n_z) 1) ->
    reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_table_copy x y)]
      hs s f [:: $VN (VAL_int32 dst'); $VN (VAL_int32 src'); AI_basic (BI_table_get y); AI_basic (BI_table_set x);
              $VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n'); AI_basic (BI_table_copy x y)]
| r_table_init_bound :
  forall x y src dst n tab elem s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    stab s f.(f_inst) x = Some tab ->
    selem s f.(f_inst) y = Some elem ->
    ((src_z + n_z > Z.of_nat (elem_size elem))%Z \/
     (dst_z + n_z > Z.of_nat (tab_size tab))%Z) ->
    reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_table_init x y)]
      hs s f [::AI_trap]
| r_table_init_return :
  forall x y src dst n tab elem s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    stab s f.(f_inst) x = Some tab ->
    selem s f.(f_inst) y = Some elem ->
    (src_z + n_z <= Z.of_nat (elem_size elem))%Z ->
    (dst_z + n_z <= Z.of_nat (tab_size tab))%Z ->
    (n_z = 0)%Z ->
    reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_table_init x y)]
      hs s f [::]
| r_table_init_step :
  forall x y src dst n tab elem src' dst' n' v s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    stab s f.(f_inst) x = Some tab ->
    selem s f.(f_inst) y = Some elem ->
    (src_z + n_z <= Z.of_nat (elem_size elem))%Z ->
    (dst_z + n_z <= Z.of_nat (tab_size tab))%Z ->
    (n_z <> 0)%Z ->
    lookup_N elem.(eleminst_elem) (Wasm_int.N_of_uint i32m src) = Some v ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    src' = Wasm_int.int_of_Z i32m (Z.add src_z 1) ->
    dst' = Wasm_int.int_of_Z i32m (Z.add dst_z 1) ->
    reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_table_init x y)]
      hs s f [:: $VN (VAL_int32 dst); v_to_e (VAL_ref v); AI_basic (BI_table_set x);
              $VN (VAL_int32 dst'); $VN (VAL_int32 src'); $VN (VAL_int32 n'); AI_basic (BI_table_init x y)]
| r_elem_drop:
  forall x hs s f s',
    selem_drop s f.(f_inst) x = Some s' ->
    reduce hs s f [::AI_basic (BI_elem_drop x)] hs s' f [::]
           
(** memory **)
| r_load_success :
  forall s f t bs k a off m hs,
    smem s f.(f_inst) = Some m ->
    load m (Wasm_int.N_of_uint i32m k) off (tnum_length t) = Some bs ->
    reduce hs s f [::$VN (VAL_int32 k); AI_basic (BI_load t None a off)] hs s f [::$VN (wasm_deserialise bs t)]
| r_load_failure :
  forall s f t k a off m hs,
    smem s f.(f_inst) = Some m ->
    load m (Wasm_int.N_of_uint i32m k) off (tnum_length t) = None ->
    reduce hs s f [::$VN (VAL_int32 k); AI_basic (BI_load t None a off)] hs s f [::AI_trap]
| r_load_packed_success :
  forall s f t tp k a off m bs sx hs,
    smem s f.(f_inst) = Some m ->
    load_packed sx m (Wasm_int.N_of_uint i32m k) off (tp_length tp) (tnum_length t) = Some bs ->
    reduce hs s f [::$VN (VAL_int32 k); AI_basic (BI_load t (Some (tp, sx)) a off)] hs s f [::$VN (wasm_deserialise bs t)]
| r_load_packed_failure :
  forall s f t tp k a off m sx hs,
    smem s f.(f_inst) = Some m ->
    load_packed sx m (Wasm_int.N_of_uint i32m k) off (tp_length tp) (tnum_length t) = None ->
    reduce hs s f [::$VN (VAL_int32 k); AI_basic (BI_load t (Some (tp, sx)) a off)] hs s f [::AI_trap]
| r_store_success :
  forall t v s f k a off s' hs,
    smem_store s f.(f_inst) (Wasm_int.N_of_uint i32m k) off v t = Some s' ->
    reduce hs s f [::$VN (VAL_int32 k); $VN v; AI_basic (BI_store t None a off)] hs s' f [::]
| r_store_failure :
  forall t v s f k off a hs,
    smem_store s f.(f_inst) (Wasm_int.N_of_uint i32m k) off v t = None ->
    reduce hs s f [::$VN (VAL_int32 k); $VN v; AI_basic (BI_store t None a off)] hs s f [::AI_trap]
| r_store_packed_success :
  forall t v s s' a f k off tp hs,
    smem_store_packed s f.(f_inst) (Wasm_int.N_of_uint i32m k) off v tp = Some s' ->
    typeof_num v = t ->
    reduce hs s f [::$VN (VAL_int32 k); $VN v; AI_basic (BI_store t (Some tp) a off)] hs s' f [::]
| r_store_packed_failure :
  forall t v s a f k off tp hs,
    smem_store_packed s f.(f_inst) (Wasm_int.N_of_uint i32m k) off v tp = None ->
    typeof_num v = t ->
    reduce hs s f [::$VN (VAL_int32 k); $VN v; AI_basic (BI_store t (Some tp) a off)] hs s f [::AI_trap]
| r_memory_size :
  forall f m n s hs,
    smem s f.(f_inst) = Some m ->
    mem_size m = n ->
    reduce hs s f [::AI_basic (BI_memory_size)] hs s f [::$VN (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N n)))]
| r_memory_grow_success :
  forall s f s' sz c hs,
    smem_grow s f.(f_inst) (Wasm_int.N_of_uint i32m c) = Some (s', sz) ->
    reduce hs s f [::$VN (VAL_int32 c); AI_basic BI_memory_grow] hs s' f [::$VN (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N sz)))]
| r_memory_grow_failure :
  forall s f c hs,
    smem_grow s f.(f_inst) (Wasm_int.N_of_uint i32m c) = None ->
    reduce hs s f [::$VN (VAL_int32 c); AI_basic BI_memory_grow] hs s f [::$VN (VAL_int32 int32_minus_one)]
| r_memory_fill_bound:
  forall s f mem d n v hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let d_z := Wasm_int.Z_of_uint i32m d in
    smem s f.(f_inst) = Some mem ->
    (Z.add n_z d_z > Z.of_nat (mem_length mem))%Z ->
    reduce hs s f [::$VN (VAL_int32 d); $VN (VAL_int32 v); $VN (VAL_int32 n); AI_basic (BI_memory_fill)]
           hs s f [::AI_trap]
| r_memory_fill_return:
  forall s f mem d n v hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let d_z := Wasm_int.Z_of_uint i32m d in
    smem s f.(f_inst) = Some mem ->
    (Z.add n_z d_z <= Z.of_nat (mem_length mem))%Z ->
    (n_z = 0)%Z ->
    reduce hs s f [::$VN (VAL_int32 d); $VN (VAL_int32 v); $VN (VAL_int32 n); AI_basic (BI_memory_fill)]
           hs s f [::]
| r_memory_fill_step:
  forall s f mem d n d' n' v hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let d_z := Wasm_int.Z_of_uint i32m d in
    smem s f.(f_inst) = Some mem ->
    (Z.add n_z d_z <= Z.of_nat (mem_length mem))%Z ->
    (n_z <> 0)%Z ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    d' = Wasm_int.int_of_Z i32m (Z.add d_z 1) ->
    reduce hs s f [::$VN (VAL_int32 d); $VN (VAL_int32 v); $VN (VAL_int32 n); AI_basic (BI_memory_fill)]
      hs s f [::$VN (VAL_int32 d); $VN (VAL_int32 v); AI_basic (BI_store T_i32 (Some Tp_i8) N0 N0);
                $VN (VAL_int32 d'); $VN (VAL_int32 v); $VN (VAL_int32 n'); AI_basic (BI_memory_fill)]
| r_memory_copy_bound :
  forall src dst n mem s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    smem s f.(f_inst) = Some mem ->
    ((Z.add src_z n_z > Z.of_nat (mem_length mem))%Z \/
     (Z.add dst_z n_z > Z.of_nat (mem_length mem))%Z) ->
    reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_memory_copy)]
      hs s f [::AI_trap]
| r_memory_copy_return :
  forall src dst n mem s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    smem s f.(f_inst) = Some mem ->
    (Z.add src_z n_z <= Z.of_nat (mem_length mem))%Z ->
    (Z.add dst_z n_z <= Z.of_nat (mem_length mem))%Z ->
    (n_z = 0)%Z ->
    reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_memory_copy)]
      hs s f [::]
| r_memory_copy_forward :
  forall src dst n mem src' dst' n' s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    smem s f.(f_inst) = Some mem ->
    (Z.add src_z n_z <= Z.of_nat (mem_length mem))%Z ->
    (Z.add dst_z n_z <= Z.of_nat (mem_length mem))%Z ->
    (n_z <> 0)%Z ->
    (dst_z <= src_z)%Z ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    src' = Wasm_int.int_of_Z i32m (Z.add src_z 1) ->
    dst' = Wasm_int.int_of_Z i32m (Z.add dst_z 1) ->
    reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_memory_copy)]
      hs s f [:: $VN (VAL_int32 dst); $VN (VAL_int32 src); AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) N0 N0); AI_basic (BI_store T_i32 (Some (Tp_i8)) N0 N0);
              $VN (VAL_int32 dst'); $VN (VAL_int32 src'); $VN (VAL_int32 n'); AI_basic (BI_memory_copy)]
| r_memory_copy_backward :
  forall src dst n mem src' dst' n' s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    smem s f.(f_inst) = Some mem ->
    (Z.add src_z n_z <= Z.of_nat (mem_length mem))%Z ->
    (Z.add dst_z n_z <= Z.of_nat (mem_length mem))%Z ->
    (n_z <> 0)%Z ->
    (dst_z > src_z)%Z ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    src' = Wasm_int.int_of_Z i32m (Z.add src_z (Z.sub n_z 1)) ->
    dst' = Wasm_int.int_of_Z i32m (Z.add dst_z (Z.sub n_z 1)) ->
    reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_memory_copy)]
      hs s f [:: $VN (VAL_int32 dst'); $VN (VAL_int32 src'); AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) N0 N0); AI_basic (BI_store T_i32 (Some (Tp_i8)) N0 N0);
              $VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n'); AI_basic (BI_memory_copy)]
| r_memory_init_bound :
  forall x src dst n mem data s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    smem s f.(f_inst) = Some mem ->
    sdata s f.(f_inst) x = Some data ->
    ((Z.add src_z n_z > Z.of_nat (data_size data))%Z \/
     (Z.add dst_z n_z > Z.of_nat (mem_length mem))%Z) ->
    reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_memory_init x)]
      hs s f [::AI_trap]
| r_memory_init_return :
  forall x src dst n mem data s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    smem s f.(f_inst) = Some mem ->
    sdata s f.(f_inst) x = Some data ->
    (Z.add src_z n_z <= Z.of_nat (data_size data))%Z ->
    (Z.add dst_z n_z <= Z.of_nat (mem_length mem))%Z ->
    (n_z = 0)%Z ->
    reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_memory_init x)]
      hs s f [::]
| r_memory_init_step :
  forall x src dst n mem data src' dst' n' b s f hs,
    let n_z := Wasm_int.Z_of_uint i32m n in
    let src_z := Wasm_int.Z_of_uint i32m src in
    let dst_z := Wasm_int.Z_of_uint i32m dst in
    smem s f.(f_inst) = Some mem ->
    sdata s f.(f_inst) x = Some data ->
    (Z.add src_z n_z <= Z.of_nat (data_size data))%Z ->
    (Z.add dst_z n_z <= Z.of_nat (mem_length mem))%Z ->
    (n_z <> 0)%Z ->
    lookup_N data.(datainst_data) (Wasm_int.N_of_uint i32m src) = Some b ->
    n' = Wasm_int.int_of_Z i32m (Z.sub n_z 1) ->
    src' = Wasm_int.int_of_Z i32m (Z.add src_z 1) ->
    dst' = Wasm_int.int_of_Z i32m (Z.add dst_z 1) ->
    reduce hs s f [::$VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 n); AI_basic (BI_memory_init x)]
      hs s f [:: $VN (VAL_int32 dst); v_to_e (VAL_num (wasm_deserialise [::b] T_i32)); AI_basic (BI_store T_i32 (Some Tp_i8) N0 N0);
              $VN (VAL_int32 dst'); $VN (VAL_int32 src'); $VN (VAL_int32 n'); AI_basic (BI_memory_init x)]
| r_data_drop:
  forall x hs s f s',
    sdata_drop s f.(f_inst) x = Some s' ->
    reduce hs s f [::AI_basic (BI_data_drop x)] hs s' f [::]
               
  (** label and frame **)
  | r_label :
      forall s f es les s' f' es' les' k (lh: lholed k) hs hs',
        reduce hs s f es hs' s' f' es' ->
        lfill lh es = les ->
        lfill lh es' = les' ->
        reduce hs s f les hs' s' f' les'
  | r_frame :
      forall s f es s' f' es' n f0 hs hs',
        reduce hs s f es hs' s' f' es' ->
        reduce hs s f0 [::AI_frame n f es] hs' s' f0 [::AI_frame n f' es']
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

