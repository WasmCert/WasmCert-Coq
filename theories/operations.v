(** Basic operations over Wasm datatypes **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From compcert Require Floats.
From Wasm Require Export common memory datatypes_properties list_extra.
From Coq Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Operations.
  Context `{memory: Memory} `{hfc: host_function_class}.

(* Placeholder for better array lookup in the future. *)
Definition lookup_N {T: Type} (l: list T) (n: N) : option T :=
  List.nth_error l (N.to_nat n).

Definition empty_t_context := Build_t_context nil nil nil nil nil nil nil nil nil None nil.

(** read `len` bytes from `m` starting at `start_idx` *)
Definition read_bytes (m : meminst) (start_idx : N) (len : nat) : option bytes :=
  those
    (List.map
      (fun off =>
        let idx := N.add start_idx (N.of_nat off) in
        mem_lookup idx m.(meminst_data))
    (iota 0 len)).

(** write bytes `bs` to `m` starting at `start_idx` *)
Fixpoint write_bytes (m : mem_t) (start_idx : N) (bs : bytes) : option mem_t :=
  match bs with
  | nil => Some m
  | b :: bs' =>
      match mem_update start_idx b m with
      | Some m' => write_bytes m' (N.add start_idx 1%N) bs'
      | None => None
      end
  end.

Definition write_bytes_meminst (m: meminst) (start_idx : N) (bs: bytes) : option meminst :=
  match write_bytes m.(meminst_data) start_idx bs with
  | Some md' =>
      Some (Build_meminst m.(meminst_type) md')
  | None => None
  end.

Definition bits (v : value_num) : bytes :=
  match v with
  | VAL_int32 c => serialise_i32 c
  | VAL_int64 c => serialise_i64 c
  | VAL_float32 c => serialise_f32 c
  | VAL_float64 c => serialise_f64 c
  end.

Definition ml_valid (m: mem_t) : Prop :=
  N.modulo (mem_length m) page_size = 0%N.

Definition mem_length (m : meminst) : N :=
  mem_length m.(meminst_data).

Definition mem_size (m : meminst) : N :=
  N.div (mem_length m) page_size.

(** Grow the memory a given number of pages.
  * @param len_delta: the number of pages to grow the memory by
  *)

Definition mem_grow (m : meminst) (len_delta : N) : option meminst :=
  let new_size := N.add (mem_size m) len_delta in
  if N.leb new_size mem_limit_bound then
    match mem_grow (N.mul len_delta page_size) m.(meminst_data) with
    | Some new_mem_data =>
        match m.(meminst_type).(lim_max) with
        | Some maxlim =>
            if N.leb new_size maxlim then
              Some {|
                  meminst_data := new_mem_data;
                  meminst_type :=
                    Build_limits new_size m.(meminst_type).(lim_max);
                |}
            else None
        | None =>
            Some {|
                meminst_data := new_mem_data;
                meminst_type := Build_limits new_size m.(meminst_type).(lim_max);
              |}
        end
    | None => None
    end
  else None.

Definition ptv_to_nm (ptv: packed_type_vec) : N * N :=
  match ptv with
  | Tptv_8_8 => (8%N, 8%N)
  | Tptv_16_4 => (16%N, 4%N)
  | Tptv_32_2 => (32%N, 2%N)
  end.

Definition ztv_to_n (ztv: zero_type_vec) : N :=
  match ztv with
  | Tztv_32 => 32%N
  | Tztv_64 => 64%N
  end.

Definition width_to_n (ww: width_vec) : N :=
  match ww with
  | Twv_8 => 8%N
  | Twv_16 => 16%N
  | Twv_32 => 32%N
  | Twv_64 => 64%N
  end.

Definition load_vec_bounds (lv_arg: load_vec_arg) (m_arg: memarg) : bool :=
  match lv_arg with
  | LVA_packed ptv sx =>
      let (n, m) := ptv_to_nm ptv in
      N.leb (N.pow 2 m_arg.(memarg_align)) (N.mul (N.div n 8) m)
  | LVA_zero ztv =>
      N.leb (N.pow 2 m_arg.(memarg_align)) (N.div (ztv_to_n ztv) 8)
  | LVA_splat width =>
      N.leb (N.pow 2 m_arg.(memarg_align)) (N.div (width_to_n width) 8)
  end.

Definition load_vec_lane_bounds (width: width_vec) (m_arg: memarg) (x: laneidx) : bool :=
   (N.leb (N.pow 2 (memarg_align m_arg)) (width_to_n width / 8))%N &&
                         (N.ltb x (128 / width_to_n width)%N). 

(* TODO: We crucially need documentation here. *)

(* Operation for the memory_load instruction.
   Length is specified in bytes.
 *)
Definition load (m : meminst) (n : N) (off : static_offset) (l : N) : option bytes :=
  if N.leb (N.add n (N.add off l)) (mem_length m)
  then read_bytes m (N.add n off) l
  else None.

Definition int_of_bytes (bs: list byte) (m: N) : value_num :=
  VAL_int32 int32_minus_one.

(* TODO: placeholder for vector load -- currently unimplemented. *)
Definition load_vec (m: meminst) (i: N) (lvarg: load_vec_arg) (marg: memarg) : option value_vec :=
  (* Placeholder just so that this operation can return both successful and error result *)
(*  let ea := i + marg.(memarg_offset) in
  match load_vec_arg with
  | LVA_packed ptv sx =>
      let (m, n) := ptv_to_nm in
      if N.leb (ea + (N.div (N.mul m n) 8%N)) (m.(mem_length)) then
        let bs = int_of_bytes (take (drop m
  if ea + *)
  match (i == marg.(memarg_offset)) with
  | true => Some (VAL_vec128 tt)
  | _ => None
  end.

Definition load_vec_lane (m: meminst) (i: N) (v: value_vec) (width: width_vec) (marg: memarg) (x: laneidx) : option value_vec :=
  match (i == marg.(memarg_offset)) with
  | true => Some v
  | _ => None
  end.

Definition store (m : meminst) (n : N) (off : static_offset) (bs : bytes) (l : nat) : option meminst :=
  if N.leb (n + off + N.of_nat l) (mem_length m)
  then write_bytes_meminst m (n + off) (bytes_takefill #00 l bs)
  else None.

(* The first argument of wrap doesn't affect the opsem at all, so this is fine.
Might need a change in the future if this behaviour changes. *)
Definition store_packed := store.

Definition store_vec_lane (m: meminst) (n: N) (v: value_vec) (width: width_vec) (marg: memarg) (x: laneidx) : option meminst :=
  match (n == marg.(memarg_offset)) with
  | true => Some m
  | _ => None
  end.

Definition wasm_deserialise (bs : bytes) (vt : number_type) : value_num :=
  match vt with
  | T_i32 => VAL_int32 (Wasm_int.Int32.repr (common.Memdata.decode_int bs))
  | T_i64 => VAL_int64 (Wasm_int.Int64.repr (common.Memdata.decode_int bs))
  | T_f32 => VAL_float32 (Floats.Float32.of_bits (Integers.Int.repr (common.Memdata.decode_int bs)))
  | T_f64 => VAL_float64 (Floats.Float.of_bits (Integers.Int64.repr (common.Memdata.decode_int bs)))
  end.

(** Sign extension **)
Definition sign_extend_n (n: N) (bytelen: N) : Z :=
  let half_intval := N.pow 2 (bytelen * 8 - 1) in
  let val_z :=
    if N.ltb n half_intval then
      BinInt.Z.of_N n
    else
      BinInt.Z.sub (BinInt.Z.of_N n) (BinInt.Z.of_N (2 * half_intval)) in
  val_z.

(* l is the byte length of the target type, therefore can only be 4/8 *)
Definition sign_extend_bytes (s : sx) (l : N) (bs : bytes) : bytes :=
  match s with
  | SX_U => bytes_takefill #00 (N.to_nat l) bs
  | SX_S =>
      (* compcert decodes to unsigned *)
      let val_n := BinInt.Z.to_N (common.Memdata.decode_int bs) in
      let val_z := sign_extend_n val_n (N.of_nat (List.length bs)) in
        Memdata.encode_int l val_z
  end.

(* last argument is in bytes *)
Definition load_packed (s : sx) (m : meminst) (n : N) (off : static_offset) (lp : N) (l : N) : option bytes :=
  match load m n off lp with
  | Some bs => Some (sign_extend_bytes s l bs)
  | None => None
  end.

Definition bitzero (t : number_type) : value_num :=
  match t with
  | T_i32 => VAL_int32 (Wasm_int.int_zero i32m)
  | T_i64 => VAL_int64 (Wasm_int.int_zero i64m)
  | T_f32 => VAL_float32 (Wasm_float.float_zero f32m)
  | T_f64 => VAL_float64 (Wasm_float.float_zero f64m)
  end.

(** std-doc:
Each value type has an associated default value; it is the respective value 0 for number types and
 null for reference types.

Note that this verison is pre-defined as an option for forward extensions (GC) that introduce non-defaultable types.

https://www.w3.org/TR/wasm-core-2/exec/runtime.html#default-val
**)
Definition default_val (t: value_type) : option value :=
  match t with
  | T_num t => Some (VAL_num (bitzero t))
  | T_vec t => Some (VAL_vec (VAL_vec128 tt))
  | T_ref t => Some (VAL_ref (VAL_ref_null t))
  | T_bot => None
  end.

Definition default_vals (ts : seq value_type) : option (seq value) :=
  those (map default_val ts).


Definition func_agree (t1 t2: function_type) : bool :=
  t1 == t2.

Definition table_agree (t1 t2: table_type) : bool :=
  (t1.(tt_elem_type) == t2.(tt_elem_type)).

Definition mem_agree (t1 t2: memory_type) : bool :=
  true.
  
Definition global_agree (t1 t2: global_type) : bool :=
  t1 == t2.
          
Definition context_agree (C C': t_context) : bool :=
  (C.(tc_types) == C'.(tc_types)) &&
  (all2 func_agree C.(tc_funcs) C'.(tc_funcs)) &&
  (all2 table_agree C.(tc_tables) C'.(tc_tables)) &&
  (all2 mem_agree C.(tc_mems) C'.(tc_mems)) &&
  (all2 global_agree C.(tc_globals) C'.(tc_globals)) &&
  (C.(tc_elems) == C'.(tc_elems)) &&
  (C.(tc_datas) == C'.(tc_datas)) &&
  (C.(tc_refs) == C'.(tc_refs)) &&
  (C.(tc_locals) == C'.(tc_locals)) &&
  (C.(tc_labels) == C'.(tc_labels)) &&
  (C.(tc_return) == C'.(tc_return)).


(* Auxiliary definitions for expressing numerics semantics and typing *)
Definition unop_type_agree (t: number_type) (op: unop): bool :=
  match op with
  | Unop_i _ | Unop_extend _ => (t == T_i32) || (t == T_i64)
  | Unop_f _ => (t == T_f32) || (t == T_f64)
  end.

Definition binop_type_agree (t: number_type) (op: binop): bool :=
  match op with
  | Binop_i _ => (t == T_i32) || (t == T_i64)
  | Binop_f _ => (t == T_f32) || (t == T_f64)
  end.

Definition relop_type_agree (t: number_type) (op: relop): bool :=
  match op with
  | Relop_i _ => (t == T_i32) || (t == T_i64)
  | Relop_f _ => (t == T_f32) || (t == T_f64)
  end.

Definition typeof_num (v : value_num) : number_type :=
  match v with
  | VAL_int32 _ => T_i32
  | VAL_int64 _ => T_i64
  | VAL_float32 _ => T_f32
  | VAL_float64 _ => T_f64
  end.

Definition unop_typecheck (v: value_num) (t: number_type) (op: unop): bool :=
  (typeof_num v == t) && unop_type_agree t op.

Definition binop_typecheck (v1 v2: value_num) (t: number_type) (op: binop) : bool :=
  (typeof_num v1 == t) && (typeof_num v2 == t) && binop_type_agree t op.

Definition relop_typecheck (v1 v2: value_num) (t: number_type) (op: relop) : bool :=
  (typeof_num v1 == t) && (typeof_num v2 == t) && relop_type_agree t op.


Definition typeof_vec (v: value_vec) : vector_type :=
  match v with
  | VAL_vec128 _ => T_v128
  end.

Definition option_projl (A B : Type) (x : option (A * B)) : option A :=
  option_map fst x.

Definition option_projr (A B : Type) (x : option (A * B)) : option B :=
  option_map snd x.

Definition tnum_length (t : number_type) : N :=
  match t with
  | T_i32 => 4
  | T_i64 => 8
  | T_f32 => 4
  | T_f64 => 8
  end.

Definition tvec_length (t: vector_type) : N :=
  match t with
  | T_v128 => 16
  end.
    

Definition tp_length (tp : packed_type) : N :=
  match tp with
  | Tp_i8 => 1
  | Tp_i16 => 2
  | Tp_i32 => 4
  end.

Definition is_int_t (t : number_type) : bool :=
  match t with
  | T_i32 => true
  | T_i64 => true
  | T_f32 => false
  | T_f64 => false
  end.

Definition is_float_t (t : number_type) : bool :=
  match t with
  | T_i32 => false
  | T_i64 => false
  | T_f32 => true
  | T_f64 => true
  end.

Definition is_ref_t (t: value_type) : bool :=
  match t with
  | T_ref _ => true
  | T_bot => true
  | _ => false
  end.

Definition is_mut (tg : global_type) : bool :=
  tg_mut tg == MUT_var.

Definition app_unop_i {T: Type} (mx : Wasm_int.mixin_of T) (iop : unop_i) : T -> T :=
  match iop with
  | UOI_ctz => Wasm_int.int_ctz mx
  | UOI_clz => Wasm_int.int_clz mx
  | UOI_popcnt => Wasm_int.int_popcnt mx
  end.

Definition app_unop_f {T: Type} (mx : Wasm_float.mixin_of T) (fop : unop_f) : T -> T :=
  match fop with
  | UOF_neg => Wasm_float.float_neg mx
  | UOF_abs => Wasm_float.float_abs mx
  | UOF_ceil => Wasm_float.float_ceil mx
  | UOF_floor => Wasm_float.float_floor mx
  | UOF_trunc => Wasm_float.float_trunc mx
  | UOF_nearest => Wasm_float.float_nearest mx
  | UOF_sqrt => Wasm_float.float_sqrt mx
  end.

Definition app_unop_extend (n: N) (v: value_num) : value_num :=
  (* wrap to the lowest n bits, then extend *)
  let val_n :=
    match v with
    | VAL_int32 c => Wasm_int.N_of_uint i32m c
    | VAL_int64 c => Wasm_int.N_of_uint i64m c
    | _ => 0%N (* Cannot happen *)
    end in
  let modulus_n := N.pow 2 (8 * n) in
  let wrapped_n := N.modulo val_n modulus_n in
  let val_z := sign_extend_n wrapped_n n in
  match v with
  | VAL_int32 _ => VAL_int32 (Wasm_int.int_of_Z i32m val_z)
  | VAL_int64 _ => VAL_int64 (Wasm_int.int_of_Z i64m val_z)
  | _ => v (* Cannot happen *)
  end.

Definition app_unop (op: unop) (v: value_num) : value_num :=
  match op with
  | Unop_i iop =>
    match v with
    | VAL_int32 c => VAL_int32 (app_unop_i i32m iop c)
    | VAL_int64 c => VAL_int64 (app_unop_i i64m iop c)
    | _ => v
    end
  | Unop_f fop =>
    match v with
    | VAL_float32 c => VAL_float32 (app_unop_f f32m fop c)
    | VAL_float64 c => VAL_float64 (app_unop_f f64m fop c)
    | _ => v
    end
  | Unop_extend n => app_unop_extend (N.div n 8) v
  end.

Definition app_binop_i {T: Type} (mx : Wasm_int.mixin_of T) (iop : binop_i)
    : T -> T -> option T :=
  let: add_some := fun f c1 c2 => Some (f c1 c2) in
  match iop with
  | BOI_add => add_some (Wasm_int.int_add mx)
  | BOI_sub => add_some (Wasm_int.int_sub mx)
  | BOI_mul => add_some (Wasm_int.int_mul mx)
  | BOI_div SX_U => Wasm_int.int_div_u mx
  | BOI_div SX_S => Wasm_int.int_div_s mx
  | BOI_rem SX_U => Wasm_int.int_rem_u mx
  | BOI_rem SX_S => Wasm_int.int_rem_s mx
  | BOI_and => add_some (Wasm_int.int_and mx)
  | BOI_or => add_some (Wasm_int.int_or mx)
  | BOI_xor => add_some (Wasm_int.int_xor mx)
  | BOI_shl => add_some (Wasm_int.int_shl mx)
  | BOI_shr SX_U => add_some (Wasm_int.int_shr_u mx)
  | BOI_shr SX_S => add_some (Wasm_int.int_shr_s mx)
  | BOI_rotl => add_some (Wasm_int.int_rotl mx)
  | BOI_rotr => add_some (Wasm_int.int_rotr mx)
  end.

Definition app_binop_f {T: Type} (mx : Wasm_float.mixin_of T) (fop : binop_f)
    : T -> T -> option T :=
  let: add_some := fun f c1 c2 => Some (f c1 c2) in
  match fop with
  | BOF_add => add_some (Wasm_float.float_add mx)
  | BOF_sub => add_some (Wasm_float.float_sub mx)
  | BOF_mul => add_some (Wasm_float.float_mul mx)
  | BOF_div => add_some (Wasm_float.float_div mx)
  | BOF_min => add_some (Wasm_float.float_min mx)
  | BOF_max => add_some (Wasm_float.float_max mx)
  | BOF_copysign => add_some (Wasm_float.float_copysign mx)
  end.

Definition app_binop (op: binop) (v1: value_num) (v2: value_num) :=
  match op with
  | Binop_i iop =>
    match v1 with
    | VAL_int32 c1 =>
      match v2 with
      | VAL_int32 c2 => option_map (fun v => VAL_int32 v) (app_binop_i i32m iop c1 c2)
      |  _ => None
      end                              
    | VAL_int64 c1 =>
      match v2 with
      | VAL_int64 c2 => option_map (fun v => VAL_int64 v) (app_binop_i i64m iop c1 c2)
      |  _ => None
      end                              
    | _ => None
    end
  | Binop_f fop =>
    match v1 with
    | VAL_float32 c1 =>
      match v2 with
      | VAL_float32 c2 => option_map (fun v => VAL_float32 v) (app_binop_f f32m fop c1 c2)
      |  _ => None
      end                              
    | VAL_float64 c1 =>
      match v2 with
      | VAL_float64 c2 => option_map (fun v => VAL_float64 v) (app_binop_f f64m fop c1 c2)
      |  _ => None
      end                              
    | _ => None
    end
  end.

Definition app_testop_i {T: Type} (mx : Wasm_int.mixin_of T) (o : testop) : T -> bool :=
  match o with
  | Eqz => Wasm_int.int_eqz mx
  end.

Definition app_relop_i {T: Type} (mx: Wasm_int.mixin_of T) (rop : relop_i)
    : T -> T -> bool :=
  match rop with
  | ROI_eq => Wasm_int.int_eq mx
  | ROI_ne => Wasm_int.int_ne mx
  | ROI_lt SX_U => Wasm_int.int_lt_u mx
  | ROI_lt SX_S => Wasm_int.int_lt_s mx
  | ROI_gt SX_U => Wasm_int.int_gt_u mx
  | ROI_gt SX_S => Wasm_int.int_gt_s mx
  | ROI_le SX_U => Wasm_int.int_le_u mx
  | ROI_le SX_S => Wasm_int.int_le_s mx
  | ROI_ge SX_U => Wasm_int.int_ge_u mx
  | ROI_ge SX_S => Wasm_int.int_ge_s mx
  end.

Definition app_relop_f {T: Type} (mx: Wasm_float.mixin_of T) (rop : relop_f)
    : T -> T -> bool :=
  match rop with
  | ROF_eq => Wasm_float.float_eq mx
  | ROF_ne => Wasm_float.float_ne mx
  | ROF_lt => Wasm_float.float_lt mx
  | ROF_gt => Wasm_float.float_gt mx
  | ROF_le => Wasm_float.float_le mx
  | ROF_ge => Wasm_float.float_ge mx
  end.

Definition app_relop (op: relop) (v1: value_num) (v2: value_num) :=
  match op with
  | Relop_i iop =>
    match v1 with
    | VAL_int32 c1 =>
      match v2 with
      | VAL_int32 c2 => app_relop_i i32m iop c1 c2
      |  _ => false
      end                              
    | VAL_int64 c1 =>
      match v2 with
      | VAL_int64 c2 => app_relop_i i64m iop c1 c2
      |  _ => false
      end                              
    | _ => false
    end
  | Relop_f fop =>
    match v1 with
    | VAL_float32 c1 =>
      match v2 with
      | VAL_float32 c2 => app_relop_f f32m fop c1 c2
      |  _ => false
      end                              
    | VAL_float64 c1 =>
      match v2 with
      | VAL_float64 c2 => app_relop_f f64m fop c1 c2
      |  _ => false
      end
    | _ => false
    end
  end.

Definition app_unop_vec (op: unop_vec) (v1: value_vec) : value_vec :=
  v1.

Definition app_binop_vec (op: binop_vec) (v1 v2: value_vec) : value_vec :=
  v1.

Definition app_ternop_vec (op: ternop_vec) (v1 v2 v3: value_vec) : value_vec :=
  v1.

Definition app_test_vec (op: test_vec) (v1: value_vec) : bool :=
  true.

Definition app_shift_vec (op: shift_vec) (v1: value_vec) (v2: i32) : value_vec :=
  v1.

Definition app_splat_vec (shape: shape_vec) (v1: value_num) : value_vec :=
  VAL_vec128 tt.

Definition app_extract_vec (shape: shape_vec) (s: option sx) (n: laneidx) (v1: value_vec) : value_num :=
  match shape with
  | SV_ishape svi =>
      match svi with
      | SVI_64_2 => bitzero T_i64
      | _ => bitzero T_i32
      end
  | SV_fshape svf =>
      match svf with
      | SVF_32_4 => bitzero T_f32
      | SVF_64_2 => bitzero T_f64
      end
  end.

Definition app_replace_vec (shape: shape_vec) (n: laneidx) (v1: value_vec) (v2: value_num) : value_vec :=
  v1.

Definition shape_dim (shape: shape_vec) : N :=
  match shape with
  | SV_ishape svi =>
      match svi with
      | SVI_8_16 => 16
      | SVI_16_8 => 8
      | SVI_32_4 => 4
      | SVI_64_2 => 2
      end
  | SV_fshape svf =>
      match svf with
      | SVF_32_4 => 4
      | SVF_64_2 => 2
      end
  end.

Definition rglob_is_mut (g : module_global) : bool :=
  g.(modglob_type).(tg_mut) == MUT_var.

Definition option_bind (A B : Type) (f : A -> option B) (x : option A) :=
  match x with
  | None => None
  | Some y => f y
  end.

Definition cl_type (cl : funcinst) : function_type :=
  match cl with
  | FC_func_native tf _ _ => tf
  | FC_func_host tf _ => tf
  end.

Definition upd_s_func (s : store_record) (fs: list funcinst) : store_record :=
  {|
    s_funcs := fs;
    s_tables := s.(s_tables);
    s_mems := s.(s_mems);
    s_globals := s.(s_globals);
    s_elems := s.(s_elems);
    s_datas := s.(s_datas);
  |}.

Definition upd_s_table (s : store_record) (ts: list tableinst) : store_record :=
  {|
    s_funcs := s.(s_funcs);
    s_tables := ts;
    s_mems := s.(s_mems);
    s_globals := s.(s_globals);
    s_elems := s.(s_elems);
    s_datas := s.(s_datas);
  |}.

Definition upd_s_mem (s : store_record) (ms : list meminst) : store_record :=
  {|
    s_funcs := s.(s_funcs);
    s_tables := s.(s_tables);
    s_mems := ms;
    s_globals := s.(s_globals);
    s_elems := s.(s_elems);
    s_datas := s.(s_datas);
  |}.

Definition upd_s_global (s : store_record) (gs : list globalinst) : store_record :=
  {|
    s_funcs := s.(s_funcs);
    s_tables := s.(s_tables);
    s_mems := s.(s_mems);
    s_globals := gs;
    s_elems := s.(s_elems);
    s_datas := s.(s_datas);
  |}.

Definition upd_s_elem (s : store_record) (es : list eleminst) : store_record :=
  {|
    s_funcs := s.(s_funcs);
    s_tables := s.(s_tables);
    s_mems := s.(s_mems);
    s_globals := s.(s_globals);
    s_elems := es;
    s_datas := s.(s_datas);
  |}.

Definition upd_s_data (s : store_record) (ds : list datainst) : store_record :=
  {|
    s_funcs := s.(s_funcs);
    s_tables := s.(s_tables);
    s_mems := s.(s_mems);
    s_globals := s.(s_globals);
    s_elems := s.(s_elems);
    s_datas := ds;
  |}.

Definition iota_N (offset: nat) (len: nat) : list N :=
  map N.of_nat (iota offset len).

Definition stypes (s : store_record) (i : moduleinst) (j : typeidx) : option function_type :=
  lookup_N (inst_types i) j.


Definition sfunc_ind (s : store_record) (i : moduleinst) (j : funcidx) : option funcaddr :=
  lookup_N (inst_funcs i) j.

Definition sfunc (s : store_record) (i : moduleinst) (j : funcidx) : option funcinst :=
  match sfunc_ind s i j with
  | Some a => lookup_N (s_funcs s) a
  | None => None
  end.

Definition sglob_ind (s : store_record) (i : moduleinst) (j : globalidx) : option globaladdr :=
  lookup_N (inst_globals i) j.

Definition sglob (s : store_record) (i : moduleinst) (j : globalidx) : option globalinst :=
  match sglob_ind s i j with
  | Some a => lookup_N (s_globals s) a
  | None => None
  end.

Definition sglob_val (s : store_record) (i : moduleinst) (j : globalidx) : option value :=
  option_map g_val (sglob s i j).

Definition smem_ind (s : store_record) (i : moduleinst) : option memaddr :=
  lookup_N i.(inst_mems) 0%N.

Definition smem (s: store_record) (inst: moduleinst) : option meminst :=
  match lookup_N inst.(inst_mems) 0%N with
  | Some a => lookup_N s.(s_mems) a
  | None => None
  end.

Definition tab_size (t: tableinst) : nat :=
  length (tableinst_elem t).

Definition stab_ind (s: store_record) (inst: moduleinst) (x: tableidx) : option tableaddr :=
  lookup_N inst.(inst_tables) x.

Definition stab (s: store_record) (inst: moduleinst) (x: tableidx): option tableinst :=
  match lookup_N inst.(inst_tables) x with
  | Some a => lookup_N s.(s_tables) a
  | None => None
  end.

Definition stab_elem (s: store_record) (inst: moduleinst) (x: tableidx) (i: elemidx) : option value_ref :=
  match lookup_N inst.(inst_tables) x with
  | Some tabaddr =>
      match lookup_N s.(s_tables) tabaddr with
      | Some tab => lookup_N tab.(tableinst_elem) i
      | _ => None
      end
  | _ => None
  end.

Definition stab_update (s: store_record) (inst: moduleinst) (x: tableidx) (i: elemidx) (tabv: value_ref) : option store_record :=
  match lookup_N inst.(inst_tables) x with
  | Some tabaddr =>
      match lookup_N s.(s_tables) tabaddr with
      | Some tab =>
          if (N.ltb i (N.of_nat (tab_size tab))) then
            let: tab' := {| tableinst_type := tab.(tableinst_type);
                           tableinst_elem := set_nth tabv tab.(tableinst_elem) (N.to_nat i) tabv |} in
            let: tabs' := set_nth tab' s.(s_tables) (N.to_nat tabaddr) tab' in
            Some (Build_store_record (s_funcs s) tabs' (s_mems s) (s_globals s) (s_elems s) (s_datas s))
          else None
      | None => None
      end
  | None => None
  end.

Definition smem_store (s: store_record) (inst: moduleinst) (n: N) (off: static_offset) (v: value_num) (t: number_type) : option store_record :=
  match lookup_N inst.(inst_mems) 0%N with
  | Some addr =>
      match lookup_N s.(s_mems) addr with
      | Some mem =>
        match store mem n off (bits v) (tnum_length t) with
        | Some mem' =>
           Some (upd_s_mem s (set_nth mem' s.(s_mems) (N.to_nat addr) mem'))
        | None => None
        end
      | None => None
      end
  | None => None
  end.

Definition smem_store_packed (s: store_record) (inst: moduleinst) (n: N) (off: static_offset) (v: value_num) (tp: packed_type) : option store_record :=
  match lookup_N inst.(inst_mems) 0%N with
  | Some addr =>
      match lookup_N s.(s_mems) addr with
      | Some mem =>
        match store_packed mem n off (bits v) (tp_length tp) with
        | Some mem' =>
           Some (upd_s_mem s (set_nth mem' s.(s_mems) (N.to_nat addr) mem'))
        | None => None
        end
      | None => None
      end
  | None => None
  end.

Definition smem_store_vec_lane (s: store_record) (inst: moduleinst) (n: N) (v: value_vec) (width: width_vec) (marg: memarg) (x: laneidx) : option store_record :=
  match lookup_N inst.(inst_mems) 0%N with
  | Some addr =>
      match lookup_N s.(s_mems) addr with
      | Some mem =>
        match store_vec_lane mem n v width marg x with
        | Some mem' =>
           Some (upd_s_mem s (set_nth mem' s.(s_mems) (N.to_nat addr) mem'))
        | None => None
        end
      | None => None
      end
  | None => None
  end.

Definition smem_grow (s: store_record) (inst: moduleinst) (n: N) : option (store_record * N) :=
  match lookup_N inst.(inst_mems) 0%N with
  | Some addr =>
      match lookup_N s.(s_mems) addr with
      | Some mem =>
          match mem_grow mem n with
          | Some mem' =>
              Some (upd_s_mem s (set_nth mem' s.(s_mems) (N.to_nat addr) mem'), mem_size mem)
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition growtable (tab: tableinst) (n: N) (tabinit: value_ref) : option tableinst :=
  let len := (N.of_nat (tab_size tab) + n)%N in
  if N.leb u32_bound len then None
  else
    let: {| tt_limits := lim; tt_elem_type := tabtype |} := tab.(tableinst_type) in
    let lim' := {| lim_min := len; lim_max := lim.(lim_max) |} in
    if limit_valid_range lim' table_limit_bound then
      let elem' := tab.(tableinst_elem) ++ (List.repeat tabinit (N.to_nat n)) in
      let tab' := {| tableinst_type := {| tt_limits := lim'; tt_elem_type := tabtype |}; tableinst_elem := elem' |} in
      Some tab'
    else
      None.

Definition stab_grow (s: store_record) (inst: moduleinst) (x: tableidx) (n: N) (tabinit: value_ref) : option (store_record * nat) :=
  match lookup_N inst.(inst_tables) x with
  | Some tabaddr =>
      match lookup_N s.(s_tables) tabaddr with
      | Some tab =>
          match growtable tab n tabinit with
          | Some tab' => 
              let tabs' := (set_nth tab' s.(s_tables) (N.to_nat tabaddr) tab') in
              Some ((Build_store_record (s_funcs s) tabs' (s_mems s) (s_globals s) (s_elems s) (s_datas s)), tab_size tab)
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition elem_size (e: eleminst) : nat :=
  length (eleminst_elem e).

Definition selem (s: store_record) (inst: moduleinst) (x: elemidx): option eleminst :=
  match lookup_N inst.(inst_elems) x with
  | Some eaddr => lookup_N s.(s_elems) eaddr
  | _ => None
  end.

Definition selem_drop (s: store_record) (inst: moduleinst) (x: elemidx) : option store_record :=
  match lookup_N inst.(inst_elems) x with
  | Some eaddr =>
      match lookup_N s.(s_elems) eaddr with
      | Some elem =>
          let empty_elem := {| eleminst_type := elem.(eleminst_type); eleminst_elem := [::] |} in
          let: elems' := set_nth empty_elem s.(s_elems) (N.to_nat eaddr) empty_elem in
          Some (Build_store_record (s_funcs s) (s_tables s) (s_mems s) (s_globals s) elems' (s_datas s))
      | None => None
      end
  | None => None
  end.

Definition data_size (d: datainst) : nat :=
  length (datainst_data d).

Definition sdata (s: store_record) (inst: moduleinst) (x: dataidx): option datainst :=
  match lookup_N inst.(inst_datas) x with
  | Some daddr => lookup_N s.(s_datas) daddr
  | _ => None
  end.

Definition sdata_drop (s: store_record) (inst: moduleinst) (x: dataidx) : option store_record :=
  match lookup_N inst.(inst_datas) x with
  | Some daddr =>
      match lookup_N s.(s_datas) daddr with
      | Some data =>
          let empty_data := {| datainst_data := [::] |} in
          let: datas' := set_nth empty_data s.(s_datas) (N.to_nat daddr) empty_data in
          Some (Build_store_record (s_funcs s) (s_tables s) (s_mems s) (s_globals s) (s_elems s) datas')
      | None => None
      end
  | None => None
  end.   

Definition supdate_glob_s (s : store_record) (k : globaladdr) (v : value) : option store_record :=
  option_map
    (fun g =>
      let: g' := Build_globalinst (g_type g) v in
      let: gs' := set_nth g' (s_globals s) (N.to_nat k) g' in
      Build_store_record (s_funcs s) (s_tables s) (s_mems s) gs' (s_elems s) (s_datas s))
    (lookup_N (s_globals s) k).

Definition supdate_glob (s : store_record) (i : moduleinst) (j : globalidx) (v : value) : option store_record :=
  option_bind
    (fun k => supdate_glob_s s k v)
    (sglob_ind s i j).


Definition func_extension (f1 f2: funcinst) : bool :=
  f1 == f2.

Definition limits_extension (l1 l2: limits) : bool :=
  (N.leb l1.(lim_min) l2.(lim_min)) &&
    (l1.(lim_max) == l2.(lim_max)).

Definition table_type_extension (t1 t2: table_type) : bool :=
  (t1.(tt_elem_type) == t2.(tt_elem_type)) &&
  (limits_extension t1.(tt_limits) t2.(tt_limits)).

(* Spec has an error here -- same for mem extension *)
Definition table_extension (t1 t2 : tableinst) : bool :=
  (table_type_extension t1.(tableinst_type) t2.(tableinst_type)) &&
  (tab_size t1 <= tab_size t2).

Definition mem_extension (m1 m2 : meminst) : bool :=
  (limits_extension m1.(meminst_type) m2.(meminst_type)) &&
  (N.leb (mem_length m1) (mem_length m2)).

Definition global_extension (g1 g2: globalinst) : bool :=
  (g_type g1 == g_type g2) &&
    let (mut, t) := g_type g1 in
    ((mut == MUT_var) || (g_val g1 == g_val g2)).

(* Note: std spec has a bug. *)
Definition elem_extension (e1 e2: eleminst) : bool :=
  ((eleminst_elem e1 == eleminst_elem e2) || (eleminst_elem e2 == [::])) &&
    (eleminst_type e1 == eleminst_type e2).

Definition data_extension (d1 d2: datainst) : bool :=
  (datainst_data d1 == datainst_data d2) || (datainst_data d2 == [::]).

Definition component_extension {T: Type} (ext_rel: T -> T -> bool) (l1 l2: list T): bool :=
  (length l1 <= length l2) &&
  all2 ext_rel l1 (take (length l1) l2).

(* The invariant of the typing context preserved by the opsem.
   The entire typing context used to be invariant in Wasm 1.0.
   However, with the introduction of the full table/memory types in Wasm 2.0,
   the table/memory grow instructions modify the corresponding types.
*)
Definition context_extension C C' : bool :=
  (C.(tc_types) == C'.(tc_types)) &&
  (C.(tc_funcs) == C'.(tc_funcs)) &&
  (all2 table_type_extension C.(tc_tables) C'.(tc_tables)) &&
  (all2 limits_extension C.(tc_mems) C'.(tc_mems)) &&
  (C.(tc_globals) == C'.(tc_globals)) &&
  (C.(tc_elems) == C'.(tc_elems)) &&
  (C.(tc_datas) == C'.(tc_datas)) &&
  (C.(tc_refs) == C'.(tc_refs)) &&
  (C.(tc_locals) == C'.(tc_locals)) &&
  (C.(tc_labels) == C'.(tc_labels)) &&
  (C.(tc_return) == C'.(tc_return)).

Definition store_extension (s s' : store_record) : bool :=
  component_extension func_extension s.(s_funcs) s'.(s_funcs) &&
  component_extension table_extension s.(s_tables) s'.(s_tables) &&
  component_extension mem_extension s.(s_mems) s'.(s_mems) &&
  component_extension global_extension s.(s_globals) s'.(s_globals) &&
  component_extension elem_extension s.(s_elems) s'.(s_elems) &&
  component_extension data_extension s.(s_datas) s'.(s_datas).

Definition to_e_list (bes : list basic_instruction) : seq administrative_instruction :=
  map AI_basic bes.

(* Two versions of converting admin instructions back to basic *)
Definition to_b_single (e: administrative_instruction) : basic_instruction :=
  match e with
  | AI_basic x => x
  | _ => BI_const_num (VAL_int32 (Wasm_int.Int32.zero))
  end.

Definition to_b_list (es: seq administrative_instruction) : seq basic_instruction :=
  map to_b_single es.

Definition to_b_single_opt (e: administrative_instruction) : option basic_instruction :=
  match e with
  | AI_basic x => Some x
  | _ => None
  end.

Definition to_b_list_opt (es: seq administrative_instruction) : option (seq basic_instruction) :=
  those (map to_b_single_opt es).

Definition e_is_basic (e: administrative_instruction) : bool :=
  match e with
  | AI_basic _ => true
  | _ => false
  end.

Definition es_is_basic (es: list administrative_instruction): bool :=
  all e_is_basic es.

Definition vref_to_e (vref: value_ref) : administrative_instruction :=
  match vref with
  | VAL_ref_null t => AI_basic (BI_ref_null t)
  | VAL_ref_func addr => AI_ref addr
  | VAL_ref_extern eaddr => AI_ref_extern eaddr
  end.

Definition v_to_e (v: value) : administrative_instruction :=
  match v with
  | VAL_num v => AI_basic (BI_const_num v)
  | VAL_vec v => AI_basic (BI_const_vec v)
  | VAL_ref v => vref_to_e v
  end.                      

(** [v_to_e_list]: 
    takes a list of [v] and gives back a list where each [v] is mapped to the corresponding administrative instruction. **)
Definition v_to_e_list (ves : seq value) : seq administrative_instruction :=
  map v_to_e ves.

Definition e_to_vref (e: administrative_instruction) : value_ref :=
  match e with
  | AI_basic (BI_ref_null t) => VAL_ref_null t
  | AI_ref addr => VAL_ref_func addr
  | AI_ref_extern eaddr => VAL_ref_extern eaddr
  | _ => VAL_ref_null T_funcref
  end.

Definition e_to_vref_opt (e: administrative_instruction) : option value_ref :=
  match e with
  | AI_basic (BI_ref_null t) => Some (VAL_ref_null t)
  | AI_ref addr => Some (VAL_ref_func addr)
  | AI_ref_extern eaddr => Some (VAL_ref_extern eaddr)
  | _ => None
  end.

(* Two versions of converting admin instructions into values *)
Definition e_to_v (e: administrative_instruction) : value :=
  match e with
  | AI_basic (BI_const_num v) => VAL_num v
  | AI_basic (BI_const_vec v) => VAL_vec v
  | _ => (VAL_ref (e_to_vref e))
  end.

Definition e_to_v_list (es: seq administrative_instruction) : list value :=
  map e_to_v es.

Definition e_to_v_opt (e: administrative_instruction) : option value :=
  match e with
  | AI_basic (BI_const_num v) => Some (VAL_num v)
  | AI_basic (BI_const_vec v) => Some (VAL_vec v)
  | _ => option_map VAL_ref (e_to_vref_opt e)
  end.

Definition e_to_v_list_opt (es: list administrative_instruction) : option (list value) :=
  those (map e_to_v_opt es).

Definition is_const (e : administrative_instruction) : bool :=
  match e_to_v_opt e with
  | Some _ => true
  | None => false
  end.

Definition const_list (es : list administrative_instruction) : bool :=
  List.forallb is_const es.

(* The expected terminal instructions *)
Definition terminal_form (es: seq administrative_instruction) :=
  const_list es \/ es = [::AI_trap].

(* Filling label context hole *)
Fixpoint lfill {k} (lh : lholed k) (es : seq administrative_instruction) : seq administrative_instruction :=
  match lh with
  | LH_base vs es' => v_to_e_list vs ++ es ++ es'
  | LH_rec _ vs n es' lh' es'' => v_to_e_list vs ++ [:: AI_label n es' (lfill lh' es)] ++ es''
  end.

(* interpreter related *)

Fixpoint split_vals (es : seq basic_instruction) : seq value * seq basic_instruction :=
  match es with
  | e :: es' =>
      match e_to_v_opt (AI_basic e) with
        | Some v => 
            let: (vs', es'') := split_vals es' in
            (v :: vs', es'')
      | None => (nil, es)
      end
  | nil => (nil, nil)
  end.

(** [split_vals_e es]: takes the maximum initial segment of [es] whose elements
    are all of the form [Basic (EConst v)];
    returns a pair of lists [(ves, es')] where [ves] are those [v]'s in that initial
    segment and [es] is the remainder of the original [es]. **)
Fixpoint split_vals_e (es : seq administrative_instruction) : seq value * seq administrative_instruction :=
  match es with
  | e :: es' =>
      match e_to_v_opt e with
        | Some v => 
            let: (vs', es'') := split_vals_e es' in
            (v :: vs', es'')
      | None => (nil, es)
      end
  | nil => (nil, nil)
  end.

Fixpoint split_n (es : seq value) (n : nat) : seq value * seq value :=
  match (es, n) with
  | ([::], _) => ([::], [::])
  | (_, 0) => ([::], es)
  | (e :: esX, n.+1) =>
    let: (es', es'') := split_n esX n in
    (e :: es', es'')
  end.

(* TODO: eliminate the use of this *)
Definition expect {A B : Type} (ao : option A) (f : A -> B) (b : B) : B :=
  oapp f b ao.

Definition expect' {A B : Type} (ao : option A) (f : A -> B) (b : B) : B :=
  match ao as ao0 return (ao = ao0) -> B with
  | Some a => (fun _ => f a)
  | None => fun _ => b
  end (Logic.eq_refl ao).

Definition vs_to_es (vs : seq value) : seq administrative_instruction :=
  v_to_e_list (rev vs).

Definition e_is_trap (e : administrative_instruction) : bool :=
  (e == AI_trap).

Definition es_is_trap (es : seq administrative_instruction) : bool :=
  (es == [:: AI_trap]).

Definition expand (inst: moduleinst) (tb: block_type) : option function_type :=
  match tb with
  | BT_id n => lookup_N inst.(inst_types) n
  | BT_valtype (Some t) => Some (Tf [::] [::t])
  | BT_valtype None => Some (Tf [::] [::])
  end.
  
(** Converting a result into a stack. **)
Definition result_to_stack (r : result) :=
  match r with
  | result_values vs => v_to_e_list vs
  | result_trap => [:: AI_trap]
  end.

Definition load_store_t_bounds (a : alignment_exponent) (tp : option packed_type) (t : number_type) : bool :=
  match tp with
  | None => N.leb (N.pow 2 a) (tnum_length t)
  | Some tp' => N.leb (N.pow 2 a) (tp_length tp') && (tp_length tp' < tnum_length t) && (is_int_t t)
  end.

Definition cvt_wrap t v : option value_num :=
  match t with
  | T_i32 =>
      match v with
      | VAL_int64 c => Some (VAL_int32 (wasm_wrap c))
      | _ => None
      end
  | _ => None
  end.

Definition cvt_trunc t s v : option value_num :=
  match t with
  | T_i32 =>
      option_map VAL_int32
        (match v with
         | VAL_float32 c =>
             match s with
             | Some SX_U => Wasm_float.float_ui32_trunc f32m c
             | Some SX_S => Wasm_float.float_si32_trunc f32m c
             | None => None
             end
         | VAL_float64 c =>
             match s with
             | Some SX_U => Wasm_float.float_ui32_trunc f64m c
             | Some SX_S => Wasm_float.float_si32_trunc f64m c
             | None => None
             end
         | _ => None
         end)
  | T_i64 =>
      option_map VAL_int64
        (match v with
         | VAL_float32 c =>
             match s with
             | Some SX_U => Wasm_float.float_ui64_trunc f32m c
             | Some SX_S => Wasm_float.float_si64_trunc f32m c
             | None => None
             end
         | VAL_float64 c =>
             match s with
             | Some SX_U => Wasm_float.float_ui64_trunc f64m c
             | Some SX_S => Wasm_float.float_si64_trunc f64m c
             | None => None
             end
         | _ => None
         end)
  | _ => None
  end.

(* This is still partial as there could be a mismatch between the input
   value and type. The underlying operation trunc_sat is total. *)
Definition cvt_trunc_sat t s v : option value_num :=
  match t with
  | T_i32 =>
      option_map VAL_int32
        (match v with
         | VAL_float32 c =>
             match s with
             | Some SX_U => Some (Wasm_float.float_ui32_trunc_sat f32m c)
             | Some SX_S => Some (Wasm_float.float_si32_trunc_sat f32m c)
             | None => None
             end
         | VAL_float64 c =>
             match s with
             | Some SX_U => Some (Wasm_float.float_ui32_trunc_sat f64m c)
             | Some SX_S => Some (Wasm_float.float_si32_trunc_sat f64m c)
             | None => None
             end
         | _ => None
         end)
  | T_i64 =>
      option_map VAL_int64
        (match v with
         | VAL_float32 c =>
             match s with
             | Some SX_U => Some (Wasm_float.float_ui64_trunc_sat f32m c)
             | Some SX_S => Some (Wasm_float.float_si64_trunc_sat f32m c)
             | None => None
             end
         | VAL_float64 c =>
             match s with
             | Some SX_U => Some (Wasm_float.float_ui64_trunc_sat f64m c)
             | Some SX_S => Some (Wasm_float.float_si64_trunc_sat f64m c)
             | None => None
             end
         | _ => None
         end)
  | _ => None
  end.

Definition cvt_extend t s v: option value_num :=
  match t with
  | T_i64 =>
      match v with
      | VAL_int32 c =>
          match s with
          | Some SX_U => Some (VAL_int64 (wasm_extend_u c))
          | Some SX_S => Some (VAL_int64 (wasm_extend_s c))
          | None => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition cvt_convert t s v : option value_num :=
  match t with
  | T_f32 =>
      option_map VAL_float32
        (match v with
         | VAL_int32 c =>
             match s with
             | Some SX_U => Some (Wasm_float.float_convert_ui32 f32m c)
             | Some SX_S => Some (Wasm_float.float_convert_si32 f32m c)
             | None => None
             end
         | VAL_int64 c =>
             match s with
             | Some SX_U => Some (Wasm_float.float_convert_ui64 f32m c)
             | Some SX_S => Some (Wasm_float.float_convert_si64 f32m c)
             | None => None
             end
         | _ => None
         end)
  | T_f64 =>
      option_map VAL_float64
        (match v with
         | VAL_int32 c =>
             match s with
             | Some SX_U => Some (Wasm_float.float_convert_ui32 f64m c)
             | Some SX_S => Some (Wasm_float.float_convert_si32 f64m c)
             | None => None
             end
         | VAL_int64 c =>
             match s with
             | Some SX_U => Some (Wasm_float.float_convert_ui64 f64m c)
             | Some SX_S => Some (Wasm_float.float_convert_si64 f64m c)
             | None => None
             end
         | _ => None
         end)
  | _ => None
  end.

Definition cvt_demote t v : option value_num :=
  match t with
  | T_f32 =>
      match v with
      | VAL_float64 c => Some (VAL_float32 (wasm_demote c))
      | _ => None
      end
  | _ => None
  end.

Definition cvt_promote t v : option value_num :=
  match t with
  | T_f64 =>
      match v with
      | VAL_float32 c => Some (VAL_float64 (wasm_promote c))
      | _ => None
      end
  | _ => None
  end.

Definition eval_cvt (t : number_type) (op: cvtop) (s : option sx) (v : value_num) : option value_num :=
  match op with
  | CVO_wrap => cvt_wrap t v
  | CVO_extend => cvt_extend t s v
  | CVO_trunc => cvt_trunc t s v
  | CVO_trunc_sat => cvt_trunc_sat t s v
  | CVO_convert => cvt_convert t s v
  | CVO_demote => cvt_demote t v
  | CVO_promote => cvt_promote t v
  | CVO_reinterpret => Some (wasm_deserialise (bits v) t)
  end.

(* Enumerates all the valid argument types for each convert operations *)
Definition cvtop_valid (t2: number_type) (op: cvtop) (t1: number_type) (s: option sx): bool :=
  ((op == CVO_wrap) && (t2 == T_i32) && (t1 == T_i64) && (s == None)) ||
  ((op == CVO_extend) && (t2 == T_i64) && (t1 == T_i32) && (s != None)) ||
  ((op == CVO_trunc) && (is_int_t t2) && (is_float_t t1) && (s != None)) ||
  ((op == CVO_trunc_sat) && (is_int_t t2) && (is_float_t t1) && (s != None)) ||
  ((op == CVO_convert) && (is_float_t t2) && (is_int_t t1) && (s != None)) ||
  ((op == CVO_demote) && (t2 == T_f32) && (t1 == T_f64) && (s == None)) ||
  ((op == CVO_promote) && (t2 == T_f64) && (t1 == T_f32) && (s == None)) ||
  ((op == CVO_reinterpret) && ((is_int_t t2 && is_float_t t1) || (is_float_t t2 && is_int_t t1)) && (s == None)).

End Operations.

#[export]
Hint Unfold v_to_e: core.

Notation "$V v" := (v_to_e v) (at level 60).
