(** Wasm typing rules **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export operations subtyping.
From Coq Require Import NArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Context `{hfc: host_function_class} `{memory: Memory}.

(** std-doc:
For the purpose of checking external values against imports, such values are classified by external types. The following auxiliary typing rules specify this typing relation relative to a store S in which the referenced instances live.
 **)
Definition ext_func_typing (s: store_record) (addr: funcaddr) : option function_type :=
  match lookup_N s.(s_funcs) addr with
  | Some x => Some (cl_type x)
  | None => None
  end.

Definition ext_table_typing (s: store_record) (addr: tableaddr) : option table_type :=
  match lookup_N s.(s_tables) addr with
  | Some x => Some (tableinst_type x)
  | None => None
  end.
  
Definition ext_mem_typing (s: store_record) (addr: memaddr) : option memory_type :=
  match lookup_N s.(s_mems) addr with
  | Some x => Some (meminst_type x)
  | None => None
  end.

Definition ext_global_typing (s: store_record) (addr: globaladdr) : option global_type :=
  match lookup_N s.(s_globals) addr with
  | Some x => Some (g_type x)
  | None => None
  end.

Definition ext_typing (s: store_record) (v: extern_value) : option extern_type :=
  match v with
  | EV_func a => option_map ET_func (ext_func_typing s a)
  | EV_table a => option_map ET_table (ext_table_typing s a)
  | EV_mem a => option_map ET_mem (ext_mem_typing s a)
  | EV_global a => option_map ET_global (ext_global_typing s a)
   end.                                 

(** std-doc:
For the purpose of checking argument values against the parameter types of exported functions, values are classified by value types. The following auxiliary typing rules specify this typing relation relative to a store S in which possibly referenced addresses live.
 **)

Definition typeof_ref (s: store_record) (v: value_ref) : option reference_type :=
  match v with
  | VAL_ref_null t => Some t
  | VAL_ref_func addr =>
      match ext_func_typing s addr with
      | Some ft => Some T_funcref
      | _ => None
      end
  | VAL_ref_extern eaddr => Some T_externref
  end.

Definition typeof_value (s: store_record) (v: value) : option value_type :=
  match v with
  | VAL_num v' => Some (T_num (typeof_num v'))
  | VAL_vec v' => Some (T_vec (typeof_vec v'))
  | VAL_ref v' => option_map T_ref (typeof_ref s v')
  end.                      

(* This works as long as the principal type of values is not a scheme. Otherwise, this needs to be a Prop in future extensions *)
Definition value_typing (s: store_record) (v: value) (t: value_type) : bool :=
  match typeof_value s v with
  | Some vt => (vt <t: t)
  | None => false
  end.

Definition values_typing (s: store_record) (vs: list value) (tf: list value_type) : bool :=
  all2 (value_typing s) vs tf.

Definition typeof_shape_unpacked (shape: vshape) : number_type :=
  match shape with
  | VS_i vsi =>
      match vsi with
      | VSI_8_16 => T_i32
      | VSI_16_8 => T_i32
      | VSI_32_4 => T_i32
      | VSI_64_2 => T_i64
      end
  | VS_f vsf =>
      match vsf with
      | VSF_32_4 => T_f32
      | VSF_64_2 => T_f64
      end
  end.
  
Definition result_types_agree (s: store_record) (ts : result_type) r : bool :=
  match r with
  | result_values vs => values_typing s vs ts
  | result_trap => true
  end.

(** std-doc:
https://www.w3.org/TR/wasm-core-2/exec/runtime.html#exec-expand
**)
Definition expand_t (C: t_context) (tb: block_type) : option instr_type :=
  match tb with
  | BT_id n => lookup_N C.(tc_types) n
  | BT_valtype (Some t) => Some (Tf [::] [::t])
  | BT_valtype None => Some (Tf [::] [::])
  end.

Definition convert_helper (sxo : option sx) t1 t2 : bool :=
  match (sxo, t1, t2) with
  | (Some SX_U, T_i32, T_i64)  (* i32.wrap_i64 *)
  | (Some SX_S, T_i32, T_f32)  (* i32.trunc_f32_s *)
  | (Some SX_U, T_i32, T_f32)  (* i32.trunc_f32_u *)
  | (Some SX_S, T_i32, T_f64)  (* i32.trunc_f64_s *)
  | (Some SX_U, T_i32, T_f64)  (* i32.trunc_f64_u *)
  | (Some SX_S, T_i64, T_i32)  (* i64.extend_i32_s *)
  | (Some SX_U, T_i64, T_i32)  (* i64.extend_i32_u *)
  | (Some SX_S, T_i64, T_f32)  (* i64.trunc_f32_s *)
  | (Some SX_U, T_i64, T_f32)  (* i64.trunc_f32_u *)
  | (Some SX_S, T_i64, T_f64)  (* i64.trunc_f64_s *)
  | (Some SX_U, T_i64, T_f64)  (* i64.trunc_f64_u *)
  | (Some SX_S, T_f32, T_i32)  (* f32.convert_i32_s *)
  | (Some SX_U, T_f32, T_i32)  (* f32.convert_i32_u *)
  | (Some SX_S, T_f32, T_i64)  (* f32.convert_i64_s *)
  | (Some SX_U, T_f32, T_i64)  (* f32.convert_i64_u *)
  | (None, T_f32, T_f64)       (* f32.demote_f64 *)
  | (Some SX_S, T_f64, T_i32)  (* f64.convert_i32_s *)
  | (Some SX_U, T_f64, T_i32)  (* f64.convert_i32_u *)
  | (Some SX_S, T_f64, T_i64)  (* f64.convert_i64_s *)
  | (Some SX_U, T_f64, T_i64)  (* f64.convert_i64_u *)
  | (None, T_f64, T_f32)       (* f64.promote_f32 *)
  | (None, T_i32, T_f32)       (* i32.reinterpret_f32 *)
  | (None, T_i64, T_f64)       (* i64.reinterpret_f64 *)
  | (None, T_f32, T_i32)       (* f32.reinterpret_i32 *)
  | (None, T_f64, T_i64)       (* f64.reinterpret_i64 *)
      => true
  | _ => false
  end.

Definition upd_local_label_return C loc lab ret :=
  Build_t_context
    (tc_types C)
    (tc_funcs C)
    (tc_tables C)
    (tc_mems C)
    (tc_globals C)
    (tc_elems C)
    (tc_datas C)
    loc
    lab
    ret
    (tc_refs C).

Definition upd_refs C refs :=
{|
  tc_types := tc_types C;
  tc_funcs := tc_funcs C;
  tc_tables := tc_tables C;
  tc_mems := tc_mems C;
  tc_globals := tc_globals C;
  tc_elems := tc_elems C;
  tc_datas := tc_datas C;
  tc_locals := tc_locals C;
  tc_labels := tc_labels C;
  tc_return := tc_return C;
  tc_refs := refs
|}.

Definition upd_local C loc :=
  upd_local_label_return C loc (tc_labels C) (tc_return C).

Definition upd_label C lab :=
  upd_local_label_return C (tc_locals C) lab (tc_return C).

Definition upd_return C ret :=
  upd_local_label_return C (tc_locals C) (tc_labels C) ret.

(* Helper for typing Select. Needs to get an update when updating to GC to implement
   subtyping *)
Definition is_numeric_type (t: value_type) : bool :=
  match t with
  | T_num _ => true
  | T_vec _ => true
  | T_bot => true
  | _ => false
  end.

(** std-doc:
Instructions are classified by stack types that describe how instructions manipulate the operand stack.

The types describe the required input stack with operand types that an instruction pops off and
the provided output stack with result values of types that it pushes back. Stack types are akin 
to function types, except that they allow individual operands to be classified as ⊥ (bottom), 
indicating that the type is unconstrained. As an auxiliary notion, an operand type t1
matches another operand type t2, if t1 is either ⊥ or equal to t2. This is extended to stack
types in a point-wise manner.

https://www.w3.org/TR/wasm-core-2/valid/instructions.html
 **)
Inductive be_typing : t_context -> seq basic_instruction -> instr_type -> Prop :=
| bet_const_num : forall C v, be_typing C [::BI_const_num v] (Tf [::] [::T_num (typeof_num v)])
| bet_const_vec : forall C v, be_typing C [::BI_const_vec v] (Tf [::] [::T_vec (typeof_vec v)])
| bet_ref_null: forall C t, be_typing C [::BI_ref_null t] (Tf [::] [::T_ref t])
| bet_ref_is_null: forall C t, be_typing C [::BI_ref_is_null] (Tf [::T_ref t] [::T_num T_i32])
| bet_ref_func: forall C t x,
    lookup_N (tc_funcs C) x = Some t ->
    List.In x (tc_refs C) ->
    be_typing C [::BI_ref_func x] (Tf [::] [::T_ref T_funcref])
| bet_unop : forall C t op,
    unop_type_agree t op -> be_typing C [::BI_unop t op] (Tf [::T_num t] [::T_num t])
| bet_binop : forall C t op,
    binop_type_agree t op -> be_typing C [::BI_binop t op] (Tf [::T_num t; T_num t] [::T_num t])
| bet_testop : forall C t op, is_int_t t -> be_typing C [::BI_testop t op] (Tf [::T_num t] [::T_num T_i32])
| bet_relop: forall C t op,
    relop_type_agree t op -> be_typing C [::BI_relop t op] (Tf [::T_num t; T_num t] [::T_num T_i32])
| bet_cvtop : forall C op t1 t2 sx,
    cvtop_valid t2 op t1 sx ->
    be_typing C [::BI_cvtop t2 op t1 sx] (Tf [::T_num t1] [::T_num t2])
| bet_vunop: forall C sh op,
    be_typing C [::BI_vunop sh op] (Tf [::T_vec T_v128] [::T_vec T_v128])
| bet_vbinop: forall C sh op,
    be_typing C [::BI_vbinop sh op] (Tf [::T_vec T_v128; T_vec T_v128] [::T_vec T_v128])
| bet_vternop: forall C sh op,
    be_typing C [::BI_vternop sh op] (Tf [::T_vec T_v128; T_vec T_v128; T_vec T_v128] [::T_vec T_v128])
| bet_vtestop: forall C sh op,
    be_typing C [::BI_vtestop sh op] (Tf [::T_vec T_v128] [::T_num T_i32])
| bet_vshiftop: forall C sh op,
    be_typing C [::BI_vshiftop sh op] (Tf [::T_vec T_v128; T_num T_i32] [::T_vec T_v128])
| bet_splat_vec: forall C sh,
    be_typing C [::BI_splat_vec sh] (Tf [::T_num (typeof_shape_unpacked sh)] [::T_vec T_v128])
| bet_extract_vec: forall C sh sx x,
    N.ltb x (shape_dim sh) = true ->
    be_typing C [::BI_extract_vec sh sx x] (Tf [::T_vec T_v128] [::T_num (typeof_shape_unpacked sh)])
| bet_replace_vec: forall C shape x,
    N.ltb x (shape_dim shape) = true ->
    be_typing C [::BI_replace_vec shape x] (Tf [::T_vec T_v128; T_num (typeof_shape_unpacked shape)] [::T_vec T_v128])
| bet_unreachable : forall C ts ts',
  be_typing C [::BI_unreachable] (Tf ts ts')
| bet_nop : forall C, be_typing C [::BI_nop] (Tf [::] [::])
| bet_drop : forall C t, be_typing C [::BI_drop] (Tf [::t] [::])
| bet_select_Some : forall C t, be_typing C [::BI_select (Some [::t])] (Tf [:: t; t; T_num T_i32] [::t])
| bet_select_None : forall C t, is_numeric_type t -> be_typing C [::BI_select None] (Tf [:: t; t; T_num T_i32] [::t])
| bet_block : forall C tb tn tm es,
  expand_t C tb = Some (Tf tn tm) ->
  be_typing (upd_label C ([::tm] ++ (tc_labels C))) es (Tf tn tm) ->
  be_typing C [::BI_block tb es] (Tf tn tm)
| bet_loop : forall C tb tn tm es,
  expand_t C tb = Some (Tf tn tm) ->
  be_typing (upd_label C ([::tn] ++ (tc_labels C))) es (Tf tn tm) ->
  be_typing C [::BI_loop tb es] (Tf tn tm)
| bet_if_wasm : forall C tb tn tm es1 es2,
  expand_t C tb = Some (Tf tn tm) ->
  be_typing (upd_label C ([::tm] ++ (tc_labels C))) es1 (Tf tn tm) ->
  be_typing (upd_label C ([::tm] ++ (tc_labels C))) es2 (Tf tn tm) ->
  be_typing C [::BI_if tb es1 es2] (Tf (tn ++ [::T_num T_i32]) tm)
| bet_br : forall C i t1s ts t2s,
  lookup_N C.(tc_labels) i = Some ts ->
  be_typing C [::BI_br i] (Tf (t1s ++ ts) t2s)
| bet_br_if : forall C i ts,
  lookup_N C.(tc_labels) i = Some ts ->
  be_typing C [::BI_br_if i] (Tf (ts ++ [::T_num T_i32]) ts)
| bet_br_table : forall C i ins ts t1s t2s,
  List.Forall (fun i => (exists ts', lookup_N C.(tc_labels) i = Some ts' /\ ts <ts: ts')) (ins ++ [::i]) ->
  be_typing C [::BI_br_table ins i] (Tf (t1s ++ (ts ++ [::T_num T_i32])) t2s)
| bet_return : forall C ts t1s t2s,
  tc_return C = Some ts ->
  be_typing C [::BI_return] (Tf (t1s ++ ts) t2s)
| bet_call : forall C i tf,
  lookup_N (tc_funcs C) i = Some tf ->
  be_typing C [::BI_call i] tf
| bet_call_indirect : forall C x y tabtype t1s t2s,
  lookup_N (tc_tables C) x = Some tabtype ->
  tabtype.(tt_elem_type) = T_funcref ->
  lookup_N (tc_types C) y = Some (Tf t1s t2s) ->
  be_typing C [::BI_call_indirect x y] (Tf (t1s ++ [::T_num T_i32]) t2s)
| bet_return_call : forall C x t1s t2s t3s t4s,
  lookup_N (tc_funcs C) x = Some (Tf t1s t2s) ->
  tc_return C = Some t2s ->
  be_typing C [::BI_return_call x] (Tf (t3s ++ t1s) t4s)
| bet_return_call_indirect : forall C x y tabt t1s t2s t3s t4s,
  lookup_N (tc_tables C) x = Some tabt ->
  tabt.(tt_elem_type) = T_funcref ->
  lookup_N (tc_types C) y = Some (Tf t1s t2s) -> 
  tc_return C = Some t2s ->
  be_typing C [::BI_return_call_indirect x y] (Tf (t3s ++ t1s ++ [::T_num T_i32]) t4s)
| bet_local_get : forall C x t,
  lookup_N (tc_locals C) x = Some t ->
  be_typing C [::BI_local_get x] (Tf [::] [::t])
| bet_local_set : forall C x t,
  lookup_N (tc_locals C) x = Some t ->
  be_typing C [::BI_local_set x] (Tf [::t] [::])
| bet_local_tee : forall C x t,
  lookup_N (tc_locals C) x = Some t ->
  be_typing C [::BI_local_tee x] (Tf [::t] [::t])
| bet_global_get : forall C x gt t,
  lookup_N (tc_globals C) x = Some gt ->  
  tg_t gt = t ->
  be_typing C [::BI_global_get x] (Tf [::] [::t])
| bet_global_set : forall C x gt t,
  lookup_N (tc_globals C) x = Some gt ->  
  tg_t gt = t ->
  is_mut gt ->
  be_typing C [::BI_global_set x] (Tf [::t] [::])
| bet_table_get : forall C x tabtype t,
  lookup_N (tc_tables C) x = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  be_typing C [::BI_table_get x] (Tf [::T_num T_i32] [::T_ref t])
| bet_table_set : forall C x tabtype t,
  lookup_N (tc_tables C) x = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  be_typing C [::BI_table_set x] (Tf [::T_num T_i32; T_ref t] [::])
| bet_table_size : forall C x tabtype,
  lookup_N (tc_tables C) x = Some tabtype ->
  be_typing C [::BI_table_size x] (Tf [::] [::T_num T_i32])
| bet_table_grow : forall C x tabtype t,
  lookup_N (tc_tables C) x = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  be_typing C [::BI_table_grow x] (Tf [::T_ref t; T_num T_i32] [::T_num T_i32])
| bet_table_fill : forall C x tabtype t,
  lookup_N (tc_tables C) x = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  be_typing C [::BI_table_fill x] (Tf [::T_num T_i32; T_ref t; T_num T_i32] [::])
| bet_table_copy : forall C x y tabtype1 tabtype2 t,
  lookup_N (tc_tables C) x = Some tabtype1 ->
  tabtype1.(tt_elem_type) = t ->
  lookup_N (tc_tables C) y = Some tabtype2 ->
  tabtype2.(tt_elem_type) = t ->
  be_typing C [::BI_table_copy x y] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_table_init : forall C x y tabtype t,
  lookup_N (tc_tables C) x = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  lookup_N (tc_elems C) y = Some t ->
  be_typing C [::BI_table_init x y] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_elem_drop : forall C x t,
  lookup_N (tc_elems C) x = Some t ->
  be_typing C [::BI_elem_drop x] (Tf [::] [::])
| bet_load : forall C m_arg tp_sx t mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  load_store_t_bounds m_arg.(memarg_align) (option_projl tp_sx) t ->
  be_typing C [::BI_load t tp_sx m_arg] (Tf [::T_num T_i32] [::T_num t])
| bet_load_vec : forall C lv_arg m_arg mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  load_vec_bounds lv_arg m_arg ->
  be_typing C [::BI_load_vec lv_arg m_arg] (Tf [::T_num T_i32] [::T_vec T_v128])
| bet_load_vec_lane : forall C width m_arg x mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  load_store_vec_lane_bounds width m_arg x ->
  be_typing C [::BI_load_vec_lane width m_arg x] (Tf [::T_num T_i32; T_vec T_v128] [::T_vec T_v128])
| bet_store : forall C m_arg tp t mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  load_store_t_bounds m_arg.(memarg_align) tp t ->
  be_typing C [::BI_store t tp m_arg] (Tf [::T_num T_i32; T_num t] [::])
| bet_store_vec : forall C m_arg mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  store_vec_bounds m_arg ->
  be_typing C [::BI_store_vec m_arg] (Tf [::T_num T_i32; T_vec T_v128] [::])
| bet_store_vec_lane : forall C width m_arg x mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  load_store_vec_lane_bounds width m_arg x ->
  be_typing C [::BI_store_vec_lane width m_arg x] (Tf [::T_num T_i32; T_vec T_v128] [::])
| bet_memory_size : forall C mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  be_typing C [::BI_memory_size] (Tf [::] [::T_num T_i32])
| bet_memory_grow : forall C mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  be_typing C [::BI_memory_grow] (Tf [::T_num T_i32] [::T_num T_i32])
| bet_memory_fill : forall C mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  be_typing C [::BI_memory_fill] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_memory_copy : forall C mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  be_typing C [::BI_memory_copy] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_memory_init : forall C x mem dat,
  lookup_N (tc_mems C) 0%N = Some mem ->
  lookup_N (tc_datas C) x = Some dat ->
  be_typing C [::BI_memory_init x] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_data_drop : forall C x dat,
  lookup_N (tc_datas C) x = Some dat ->
  be_typing C [::BI_data_drop x] (Tf [::] [::])
| bet_empty : forall C,
  be_typing C [::] (Tf [::] [::])
| bet_composition : forall C es e t1s t2s t3s,
  be_typing C es (Tf t1s t2s) ->
  be_typing C [::e] (Tf t2s t3s) ->
  be_typing C (es ++ [::e]) (Tf t1s t3s)
(** Subtyping rule from the upcoming GC proposal
[https://github.com/WebAssembly/gc/blob/main/proposals/gc/Overview.md]
**)
| bet_subtyping : forall C es t1s t2s t1s' t2s',
  be_typing C es (Tf t1s t2s) ->
  (Tf t1s t2s) <ti: (Tf t1s' t2s') ->
  be_typing C es (Tf t1s' t2s')
.

Definition expr_typing (C: t_context) (bes: list basic_instruction) (ts: result_type) : Prop :=
  be_typing C bes (Tf nil ts).

Definition func_typing (C: t_context) (code: module_func) (tf: function_type) : Prop :=
  let: {| modfunc_type := x; modfunc_locals := ts; modfunc_body := bes |} := code in
  match lookup_N C.(tc_types) x with
  | Some (Tf ts1 ts2) =>
      tf = (Tf ts1 ts2) /\
      let C' := upd_local_label_return C (ts1 ++ ts) [:: ts2] (Some ts2) in
      expr_typing C' bes ts2 /\
      (* This is an artificial restriction added due to the implementation of subtyping from the future GC proposal, but without the implementing non-defaultable locals *)
      default_vals ts <> None
  | None => False
  end.
    
(** std-doc:
The following typing rules specify when a runtime store S is valid. A valid store must consist of
 function, table, memory, global, and module instances that are themselves valid, relative to S.

To that end, each kind of instance is classified by a respective function, table, memory, or global
 type. Module instances are classified by module contexts, which are regular contexts repurposed as
 module types describing the index spaces defined by a module.
https://www.w3.org/TR/wasm-core-2/appendix/properties.html#store-validity
**)

Section Store_validity. 

(* funcinst typing is dependent on a later definition, although stated before it in the spec document. *)
  
Definition tableinst_typing (s: store_record) (ti: tableinst) : option table_type :=
  let '{| tableinst_type := ti_type; tableinst_elem := refs |} := ti in
  if tabletype_valid ti_type then
    if N.of_nat (length refs) == ti_type.(tt_limits).(lim_min) then
      if all (fun ref => value_typing s (VAL_ref ref) (T_ref (ti_type.(tt_elem_type)))) refs then
        Some ti_type
      else None
    else None
  else None.

Definition meminst_typing (s: store_record) (mi: meminst) : option memory_type :=
  let '{| meminst_type := mi_type; meminst_data := ds |} := mi in
  if memtype_valid mi_type then
    if mem_length mi == N.mul (mi_type.(lim_min)) page_size then
      Some mi_type
    else None
  else None.

Definition globalinst_typing (s: store_record) (gi: globalinst) : option global_type :=
  let '{| g_type := gi_type; g_val := gv |} := gi in
  if globaltype_valid gi_type then
    if value_typing s gv (gi_type.(tg_t)) then
      Some gi_type
    else None
  else None.

Definition eleminst_typing (s: store_record) (ei: eleminst) : option reference_type :=
  let '{| eleminst_type := ei_type; eleminst_elem := refs |} := ei in
  if all (fun ref => value_typing s (VAL_ref ref) (T_ref ei_type)) refs then
    Some ei_type
  else None.

Definition datainst_typing (s: store_record) (di: datainst): option ok :=
  Some tt.

Definition exportinst_typing (s: store_record) (expi: exportinst) : option ok :=
  let '{| exportinst_name := e_name; exportinst_val := e_val |} := expi in
  if ext_typing s e_val != None then
    Some tt
  else None.

(** std-doc:
[https://webassembly.github.io/spec/core/appendix/properties.html#module-instances-xref-exec-runtime-syntax-moduleinst-mathit-moduleinst]

This definition is currently computable -- hopefully it remains so in the future; otherwise we need to make it back to a Prop/Bool.
 **)
Definition inst_typing (s : store_record) (inst : moduleinst) : option t_context :=
  let '{| inst_types := ts; inst_funcs := fs; inst_tables := tbs; inst_mems := ms; inst_globals := gs; inst_elems := es; inst_datas := ds; inst_exports := exps |} := inst in
  if (all functype_valid ts) then
    match those (map (ext_func_typing s) fs) with
    | Some tfs =>
        match those (map (ext_table_typing s) tbs) with
        | Some tts =>
            match those (map (ext_mem_typing s) ms) with
            | Some tms =>
                match those (map (ext_global_typing s) gs) with
                | Some tgs =>
                    match those (map (fun a => match lookup_N s.(s_elems) a with
                                            | Some ei => eleminst_typing s ei
                                            | None => None
                                            end) es) with
                    | Some tes =>
                        match those (map (fun a => match lookup_N s.(s_datas) a with
                                                | Some di => datainst_typing s di
                                                | None => None
                                                end) ds) with
                        | Some tds =>
                            Some (Build_t_context ts tfs tts tms tgs tes tds nil nil None (iota_N 0 (length fs)))
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None => None
    end
  else None.

Definition inst_typecheck (s: store_record) (inst: moduleinst) (C: t_context) : bool :=
  inst_typing s inst == Some C.

Definition frame_typing (s: store_record) (f: frame) (C: t_context): Prop :=
  match inst_typing s f.(f_inst) with
  | Some C0 =>
      exists ts, C = upd_local C0 (ts ++ tc_locals C0) /\
              values_typing s f.(f_locs) ts
  | None => False
  end.

(** std-doc:
Typing rules for administrative instructions are specified as follows. In addition to the context C, typing
 of these instructions is defined under a given store S. To that end, all previous typing judgements are 
generalized to include the store by implicitly adding S to all rules – S is never modified by the 
pre-existing rules, but it is accessed in the extra rules for administrative instructions given below.

https://www.w3.org/TR/wasm-core-2/appendix/properties.html#administrative-instructions
**)
Inductive e_typing : store_record -> t_context -> seq administrative_instruction -> instr_type -> Prop :=
| ety_a : forall s C bes tf,
  be_typing C bes tf -> e_typing s C (to_e_list bes) tf
| ety_composition : forall s C es e t1s t2s t3s,
  e_typing s C es (Tf t1s t2s) ->
  e_typing s C [::e] (Tf t2s t3s) ->
  e_typing s C (es ++ [::e]) (Tf t1s t3s)
| ety_subtyping : forall s C es t1s t2s t1s' t2s',
  e_typing s C es (Tf t1s t2s) ->
  (Tf t1s t2s) <ti: (Tf t1s' t2s') ->
  e_typing s C es (Tf t1s' t2s')
| ety_trap : forall s C tf,
  e_typing s C [::AI_trap] tf
| ety_ref_extern : forall s C a,
  e_typing s C [::AI_ref_extern a] (Tf [::] [::T_ref T_externref])
| ety_ref : forall s C a tf,
  ext_func_typing s a = Some tf ->
  e_typing s C [::AI_ref a] (Tf [::] [::T_ref T_funcref])
| ety_invoke : forall s (a: funcaddr) C tf,
  ext_func_typing s a = Some tf ->
  e_typing s C [::AI_invoke a] tf
(* The soundness section of the tail call proposal doesn't contain a rule for return_invoke; this typing rule is a placeholder and will be decided later. *)
| ety_return_invoke : forall s (a: funcaddr) C ts1 ts2 ts3 ts4,
  ext_func_typing s a = Some (Tf ts1 ts2) ->
  C.(tc_return) = Some ts2 ->  
  e_typing s C [::AI_return_invoke a] (Tf (ts3 ++ ts1) ts4)
| ety_label : forall s C e0s es ts t2s n,
  e_typing s C e0s (Tf ts t2s) ->
  e_typing s (upd_label C ([::ts] ++ tc_labels C)) es (Tf [::] t2s) ->
  length ts = n ->
  e_typing s C [::AI_label n e0s es] (Tf [::] t2s)
| ety_frame : forall s C n f es ts,
  thread_typing s (Some ts) (f, es) ts ->
  length ts = n ->
  e_typing s C [::AI_frame n f es] (Tf [::] ts)

with thread_typing : store_record -> option result_type -> thread -> result_type -> Prop :=
| mk_thread_typing : forall s f es rs ts C C',
  frame_typing s f C ->
  C' = upd_return C rs ->
  e_typing s C' es (Tf nil ts) ->
  thread_typing s rs (f, es) ts
.

Scheme e_typing_ind' := Induction for e_typing Sort Prop
  with thread_typing_ind' := Induction for thread_typing Sort Prop.

Definition funcinst_typing (s: store_record) (fi: funcinst) (tf0: function_type): Prop :=
  cl_type fi = tf0 /\
  match fi with
  | FC_func_native tf inst code =>
      functype_valid tf /\
        match inst_typing s inst with
        | Some C => func_typing C code tf
        | None => False
        end
  | FC_func_host tf hf =>
      functype_valid tf (* No host function assumptions *)
  end.

Definition store_typing (s : store_record) : Prop :=
  match s with
  | Build_store_record fs tabs ms gs es ds =>
    (List.Forall (fun x => exists t, funcinst_typing s x t) fs) /\
    (List.Forall (fun x => exists t, tableinst_typing s x = Some t) tabs) /\
    (List.Forall (fun x => exists t, meminst_typing s x = Some t) ms) /\
    (List.Forall (fun x => exists t, globalinst_typing s x = Some t) gs) /\
    (List.Forall (fun x => exists t, eleminst_typing s x = Some t) es) /\
    (List.Forall (fun x => exists t, datainst_typing s x = Some t) ds)
  end.

Definition config_typing (s: store_record) (th: thread) (ts: result_type) : Prop :=
  store_typing s /\ thread_typing s None th ts.

End Store_validity.

End Host.
