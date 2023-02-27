(** Wasm typing rules **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import operations.
From Coq Require Import NArith.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Variable host_function : eqType.

Let function_closure := function_closure host_function.
Let store_record := store_record host_function.


(** std-doc:
Helper function to decide if there's a valid conversion operation.

See cvtop under: https://www.w3.org/TR/wasm-core-2/syntax/instructions.html#numeric-instructions
**)
Definition convert_helper (sxo : option sx) t1 t2 : bool :=
  (sxo == None) ==
  ((is_float_t t1 && is_float_t t2) || (is_int_t t1 && is_int_t t2 && (tnum_length t1 < tnum_length t2))).

Definition convert_cond (t1 t2: number_type) (sxo : option sx) : bool :=
  (t1 != t2) && convert_helper sxo t1 t2.


Definition upd_local_label_return C loc lab ret :=
  Build_t_context
    (tc_type C)
    (tc_func C)
    (tc_table C)
    (tc_memory C)
    (tc_global C)
    (tc_elem C)
    (tc_data C)
    loc
    lab
    ret
    (tc_ref C).

Definition upd_local C loc :=
  upd_local_label_return C loc (tc_label C) (tc_return C).

Definition upd_label C lab :=
  upd_local_label_return C (tc_local C) lab (tc_return C).

Definition upd_return C ret :=
  upd_local_label_return C (tc_local C) (tc_label C) ret.


Inductive result_typing : result -> result_type -> Prop :=
  | result_typing_values : forall vs, result_typing (result_values vs) (map typeof vs)
  | result_typing_trap : forall ts, result_typing result_trap ts
  .

Inductive unop_type_agree: number_type -> unop -> Prop :=
  | Unop_i32_agree: forall op, unop_type_agree T_i32 (Unop_i op)
  | Unop_i64_agree: forall op, unop_type_agree T_i64 (Unop_i op)
  | Unop_f32_agree: forall op, unop_type_agree T_f32 (Unop_f op)
  | Unop_f64_agree: forall op, unop_type_agree T_f64 (Unop_f op)
  .
   
Inductive binop_type_agree: number_type -> binop -> Prop :=
  | Binop_i32_agree: forall op, binop_type_agree T_i32 (Binop_i op)
  | Binop_i64_agree: forall op, binop_type_agree T_i64 (Binop_i op)
  | Binop_f32_agree: forall op, binop_type_agree T_f32 (Binop_f op)
  | Binop_f64_agree: forall op, binop_type_agree T_f64 (Binop_f op)
  .
  
Inductive relop_type_agree: number_type -> relop -> Prop :=
  | Relop_i32_agree: forall op, relop_type_agree T_i32 (Relop_i op)
  | Relop_i64_agree: forall op, relop_type_agree T_i64 (Relop_i op)
  | Relop_f32_agree: forall op, relop_type_agree T_f32 (Relop_f op)
  | Relop_f64_agree: forall op, relop_type_agree T_f64 (Relop_f op)
  .

Definition is_numeric_type (t: value_type) : bool :=
  match t with
  | T_num _ => true
  | T_vec _ => true
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
Inductive be_typing : t_context -> seq basic_instruction -> function_type -> Type :=
| bet_const : forall C v, be_typing C [::BI_const v] (Tf [::] [::typeof v])
| bet_unop : forall C t op,
    unop_type_agree t op -> be_typing C [::BI_unop t op] (Tf [::T_num t] [::T_num t])
| bet_binop : forall C t op,
    binop_type_agree t op -> be_typing C [::BI_binop t op] (Tf [::T_num t; T_num t] [::T_num t])
| bet_testop : forall C t op, is_int_t t -> be_typing C [::BI_testop t op] (Tf [::T_num t] [::T_num T_i32])
| bet_relop: forall C t op,
    relop_type_agree t op -> be_typing C [::BI_relop t op] (Tf [::T_num t; T_num t] [::T_num T_i32])
| bet_convert : forall C t1 t2 sx, t1 <> t2 -> convert_helper sx t1 t2 ->
  be_typing C [::BI_cvtop t1 CVO_convert t2 sx] (Tf [::T_num t2] [::T_num t1])
| bet_reinterpret : forall C t1 t2, t1 <> t2 -> (tnum_length t1) = (tnum_length t2) ->
  be_typing C [::BI_cvtop t1 CVO_reinterpret t2 None] (Tf [::T_num t2] [::T_num t1])
| bet_unreachable : forall C ts ts',
  be_typing C [::BI_unreachable] (Tf ts ts')
| bet_nop : forall C, be_typing C [::BI_nop] (Tf [::] [::])
| bet_drop : forall C t, be_typing C [::BI_drop] (Tf [::t] [::])
| bet_select_Some : forall C t, be_typing C [::BI_select (Some [::t])] (Tf [:: t; t; T_num T_i32] [::t])
| bet_select_None : forall C t, is_numeric_type t -> be_typing C [::BI_select None] (Tf [:: t; t; T_num T_i32] [::t])
| bet_block : forall C tb tn tm es,
  expand_t C tb = Some (Tf tn tm) ->
  be_typing (upd_label C ([::tm] ++ (tc_label C))) es (Tf tn tm) ->
  be_typing C [::BI_block tb es] (Tf tn tm)
| bet_loop : forall C tb tn tm es,
  expand_t C tb = Some (Tf tn tm) ->
  be_typing (upd_label C ([::tn] ++ (tc_label C))) es (Tf tn tm) ->
  be_typing C [::BI_loop tb es] (Tf tn tm)
| bet_if_wasm : forall C tb tn tm es1 es2,
  expand_t C tb = Some (Tf tn tm) ->
  be_typing (upd_label C ([::tm] ++ (tc_label C))) es1 (Tf tn tm) ->
  be_typing (upd_label C ([::tm] ++ (tc_label C))) es2 (Tf tn tm) ->
  be_typing C [::BI_if tb es1 es2] (Tf (tn ++ [::T_num T_i32]) tm)
| bet_br : forall C i t1s ts t2s,
  List.nth_error C.(tc_label) (N.to_nat i) = Some ts ->
  be_typing C [::BI_br i] (Tf (t1s ++ ts) t2s)
| bet_br_if : forall C i ts,
  List.nth_error C.(tc_label) (N.to_nat i) = Some ts ->
  be_typing C [::BI_br_if i] (Tf (ts ++ [::T_num T_i32]) ts)
| bet_br_table : forall C i ins ts t1s t2s,
  List.Forall (fun i => (List.nth_error C.(tc_label) (N.to_nat i) = Some ts)) (ins ++ [::i])  ->
  be_typing C [::BI_br_table ins i] (Tf (t1s ++ (ts ++ [::T_num T_i32])) t2s)
| bet_return : forall C ts t1s t2s,
  tc_return C = Some ts ->
  be_typing C [::BI_return] (Tf (app t1s ts) t2s)
| bet_call : forall C i tf,
  List.nth_error (tc_func C) (N.to_nat i) = Some tf ->
  be_typing C [::BI_call i] tf
| bet_call_indirect : forall C x y tabtype t1s t2s,
  List.nth_error (tc_table C) (N.to_nat x) = Some tabtype ->
  tabtype.(tt_elem_type) = T_funcref ->
  List.nth_error (tc_type C) (N.to_nat y) = Some (Tf t1s t2s) ->
  be_typing C [::BI_call_indirect x y] (Tf (t1s ++ [::T_num T_i32]) t2s)
| bet_local_get : forall C x t,
  List.nth_error (tc_local C) (N.to_nat x) = Some t ->
  be_typing C [::BI_local_get x] (Tf [::] [::t])
| bet_local_set : forall C x t,
  List.nth_error (tc_local C) (N.to_nat x) = Some t ->
  be_typing C [::BI_local_set x] (Tf [::t] [::])
| bet_local_tee : forall C x t,
  List.nth_error (tc_local C) (N.to_nat x) = Some t ->
  be_typing C [::BI_local_tee x] (Tf [::t] [::t])
| bet_global_get : forall C x t,
  option_map tg_t (List.nth_error (tc_global C) (N.to_nat x)) = Some t ->
  be_typing C [::BI_global_get x] (Tf [::] [::t])
| bet_global_set : forall C x g t,
  List.nth_error (tc_global C) (N.to_nat x) = Some g ->  
  tg_t g = t ->
  is_mut g ->
  be_typing C [::BI_global_set x] (Tf [::t] [::])
| bet_table_get : forall C x tabtype t,
  List.nth_error (tc_table C) (N.to_nat x) = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  be_typing C [::BI_table_get x] (Tf [::T_num T_i32] [::T_ref t])
| bet_table_set : forall C x tabtype t,
  List.nth_error (tc_table C) (N.to_nat x) = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  be_typing C [::BI_table_set x] (Tf [::T_num T_i32; T_ref t] [::])
| bet_table_size : forall C x tabtype,
  List.nth_error (tc_table C) (N.to_nat x) = Some tabtype ->
  be_typing C [::BI_table_size x] (Tf [::] [::T_num T_i32])
| bet_table_grow : forall C x tabtype t,
  List.nth_error (tc_table C) (N.to_nat x) = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  be_typing C [::BI_table_grow x] (Tf [::T_ref t; T_num T_i32] [::T_num T_i32])
| bet_table_fill : forall C x tabtype t,
  List.nth_error (tc_table C) (N.to_nat x) = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  be_typing C [::BI_table_fill x] (Tf [::T_num T_i32; T_ref t; T_num T_i32] [::T_num T_i32])
| bet_table_copy : forall C x y tabtype1 tabtype2 t,
  List.nth_error (tc_table C) (N.to_nat x) = Some tabtype1 ->
  tabtype1.(tt_elem_type) = t ->
  List.nth_error (tc_table C) (N.to_nat y) = Some tabtype2 ->
  tabtype2.(tt_elem_type) = t ->
  be_typing C [::BI_table_copy x y] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_table_init : forall C x y tabtype t,
  List.nth_error (tc_table C) (N.to_nat x) = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  List.nth_error (tc_elem C) (N.to_nat y) = Some t ->
  be_typing C [::BI_table_init x y] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_elem_drop : forall C x t,
  List.nth_error (tc_elem C) (N.to_nat x) = Some t ->
  be_typing C [::BI_elem_drop x] (Tf [::] [::])
| bet_load : forall C a off tp_sx t,
  tc_memory C <> nil ->
  load_store_t_bounds a (option_projl tp_sx) t ->
  be_typing C [::BI_load t tp_sx a off] (Tf [::T_num T_i32] [::T_num t])
| bet_store : forall C a off tp t,
  tc_memory C <> nil ->
  load_store_t_bounds a tp t ->
  be_typing C [::BI_store t tp a off] (Tf [::T_num T_i32; T_num t] [::])
| bet_memory_size : forall C,
  tc_memory C <> nil ->
  be_typing C [::BI_memory_size] (Tf [::] [::T_num T_i32])
| bet_memory_grow : forall C,
  tc_memory C <> nil ->
  be_typing C [::BI_memory_grow] (Tf [::T_num T_i32] [::T_num T_i32])
| bet_memory_fill : forall C,
  tc_memory C <> nil ->
  be_typing C [::BI_memory_fill] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_memory_copy : forall C,
  tc_memory C <> nil ->
  be_typing C [::BI_memory_copy] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_memory_init : forall C x,
  tc_memory C <> nil ->
  N.to_nat x < length (tc_data C) ->
  be_typing C [::BI_memory_init x] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_empty : forall C,
  be_typing C [::] (Tf [::] [::])
| bet_composition : forall C es e t1s t2s t3s,
  be_typing C es (Tf t1s t2s) ->
  be_typing C [::e] (Tf t2s t3s) ->
  be_typing C (app es [::e]) (Tf t1s t3s)
| bet_weakening : forall C es ts t1s t2s,
  be_typing C es (Tf t1s t2s) ->
  be_typing C es (Tf (app ts t1s) (app ts t2s))
.


(** std-doc:
The following typing rules specify when a runtime store S is valid. A valid store must consist of
 function, table, memory, global, and module instances that are themselves valid, relative to S.

To that end, each kind of instance is classified by a respective function, table, memory, or global
 type. Module instances are classified by module contexts, which are regular contexts repurposed as
 module types describing the index spaces defined by a module.

https://www.w3.org/TR/wasm-core-2/appendix/properties.html#store-validity
**)
Section Store_validity.

Definition funci_agree (fs : seq function_closure) (n : funcaddr) (f : function_type) : bool :=
  option_map cl_type (List.nth_error fs n) == Some f.

Definition tab_typing (t : tableinst) (tt : table_type) : bool :=
  (tt.(tt_limits).(lim_min) <= tab_size t) &&
  (t.(tableinst_type) == tt).

Definition tabi_agree (ts: list tableinst) (n : tableaddr) (tab_t : table_type) : bool :=
  option_map (fun tab => tab_typing tab tab_t) (List.nth_error ts n) == Some true.

Definition mem_typing (m : meminst) (m_t : memory_type) : bool :=
  (N.leb m_t.(lim_min) (mem_size m)) &&
  (m.(meminst_type) == m_t).

Definition memi_agree (ms : list meminst) (n : memaddr) (mem_t : memory_type) : bool :=
  option_map (fun mem => mem_typing mem mem_t) (List.nth_error ms n) == Some true.

Definition globali_agree (gs : list globalinst) (n : globaladdr) (tg : global_type) : bool :=
  option_map g_type (List.nth_error gs n) == Some tg.

(* TODO: figure out what's missing for elem/data/ref *)
(** std-doc:
https://www.w3.org/TR/wasm-core-2/appendix/properties.html#module-instances-xref-exec-runtime-syntax-moduleinst-mathit-moduleinst
**)
Definition inst_typing (s : store_record) (inst : instance) (C : t_context) : bool :=
  let '{| inst_types := ts; inst_funcs := fs; inst_tables := tbs; inst_mems := ms; inst_globals := gs;
       inst_elems := es; inst_datas := ds; inst_exports := exps |} := inst in
  match C with
  | {| tc_type := ts'; tc_func := tfs; tc_table := tabs_t; tc_memory := mems_t; tc_global := tgs; tc_elem := nil; tc_data := nil; tc_local := nil; tc_label := nil; tc_return := None; tc_ref := nil; |} =>
    (ts == ts') &&
    (all2 (funci_agree s.(s_funcs)) fs tfs) &&
    (all2 (globali_agree s.(s_globals)) gs tgs) &&
    (all2 (tabi_agree s.(s_tables)) tbs tabs_t) &&
    (all2 (memi_agree s.(s_mems)) ms mems_t)
  | _ => false
  end.


Lemma inst_typing_expand (s: store_record) (inst: instance) (C: t_context) (tb: block_type) :
  inst_typing s inst C ->
  expand inst tb = expand_t C tb.
Proof.
  destruct tb, inst, C => //=.
  destruct tc_elem, tc_data, tc_local, tc_label, tc_return, tc_ref => //.
  move => Htype.
  repeat (move/andP in Htype; destruct Htype as [Htype _]).
  by move/eqP in Htype; subst.
Qed.


Inductive frame_typing: store_record -> frame -> t_context -> Prop :=
| mk_frame_typing: forall s i tvs C f,
    inst_typing s i C ->
    f.(f_inst) = i ->
    map typeof f.(f_locs) = tvs ->
    frame_typing s f (upd_local C (tc_local C ++ tvs))
  .

Lemma functions_agree_injective: forall s i t t',
  funci_agree s i t ->
  funci_agree s i t' ->
  t = t'.
Proof.
  move => s i t t' H1 H2.
  unfold funci_agree in *.
  move/eqP in H1. move/eqP in H2.
  rewrite H2 in H1 => {H2}.
  by move: H1 => [H1].
Qed.

Inductive cl_typing : store_record -> function_closure -> function_type -> Prop :=
  | cl_typing_native : forall i s C C' ts t1s t2s es tf,
    inst_typing s i C ->
    tf = Tf t1s t2s ->
    C' = upd_local_label_return C (tc_local C ++ t1s ++ ts) ([::t2s] ++ tc_label C) (Some t2s) ->
    be_typing C' es (Tf [::] t2s) ->
    cl_typing s (FC_func_native i tf ts es) (Tf t1s t2s)
  | cl_typing_host : forall s tf h,
    cl_typing s (FC_func_host tf h) tf
  .

(** std-doc:
Typing rules for administrative instructions are specified as follows. In addition to the context C, typing
 of these instructions is defined under a given store S. To that end, all previous typing judgements are 
generalized to include the store by implicitly adding S to all rules – S is never modified by the 
pre-existing rules, but it is accessed in the extra rules for administrative instructions given below.

https://www.w3.org/TR/wasm-core-2/appendix/properties.html#administrative-instructions
**)

Inductive e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
| ety_a : forall s C bes tf,
  be_typing C bes tf -> e_typing s C (to_e_list bes) tf
| ety_composition : forall s C es e t1s t2s t3s,
  e_typing s C es (Tf t1s t2s) ->
  e_typing s C [::e] (Tf t2s t3s) ->
  e_typing s C (es ++ [::e]) (Tf t1s t3s)
| ety_weakening : forall s C es ts t1s t2s,
  e_typing s C es (Tf t1s t2s) ->
  e_typing s C es (Tf (ts ++ t1s) (ts ++ t2s))
| ety_trap : forall s C tf,
  e_typing s C [::AI_trap] tf
| ety_ref_extern : forall s C a,
  e_typing s C [::AI_ref_extern a] (Tf [::] [::T_ref T_externref])
| ety_ref : forall s C a tf,
  funci_agree s.(s_funcs) a tf ->
  e_typing s C [::AI_ref a] (Tf [::] [::T_ref T_funcref])
| ety_invoke : forall s (a: funcaddr) C cl tf,
  List.nth_error s.(s_funcs) a = Some cl ->
  cl_typing s cl tf ->
  e_typing s C [::AI_invoke a] tf
| ety_label : forall s C e0s es ts t2s n,
  e_typing s C e0s (Tf ts t2s) ->
  e_typing s (upd_label C ([::ts] ++ tc_label C)) es (Tf [::] t2s) ->
  length ts = n ->
  e_typing s C [::AI_label n e0s es] (Tf [::] t2s)
| ety_local : forall s C n f es ts,
  s_typing s (Some ts) f es ts ->
  length ts = n ->
  e_typing s C [::AI_local n f es] (Tf [::] ts)

with s_typing : store_record -> option (seq value_type) -> frame -> seq administrative_instruction -> seq value_type -> Prop :=
| mk_s_typing : forall s f es rs ts C C0,
  frame_typing s f C0 ->
  C = upd_return C0 rs ->
  e_typing s C es (Tf [::] ts) ->
  (rs = Some ts \/ rs = None) ->
  s_typing s rs f es ts
.

Scheme e_typing_ind' := Induction for e_typing Sort Prop
  with s_typing_ind' := Induction for s_typing Sort Prop.

Definition cl_typing_self (s : store_record) (fc : function_closure) : Prop :=
  cl_typing s fc (cl_type fc).

Lemma cl_typing_unique : forall s cl tf, cl_typing s cl tf -> tf = cl_type cl.
Proof.
  move=> s + tf. case.
  - move => i ts bes t H /=; by inversion H.
  - move => f h H; by inversion H.
Qed.

Definition cl_type_check_single (s:store_record) (f:function_closure):=
  exists tf, cl_typing s f tf.

Definition tabcl_agree (s : store_record) (tref: reference_type) (v : value_ref) : Prop :=
  match v with
  | VAL_ref_null tref' => tref = tref'
  | VAL_ref_func a => (a < length s.(s_funcs)) /\ (tref = T_funcref)
  | VAL_ref_extern _ => tref = T_externref
  end.

Definition tabsize_agree (t: tableinst) : Prop :=
  match t.(tableinst_type).(tt_limits).(lim_max) with
  | None => True
  | Some n => tab_size t <= n
  end.

Definition tab_agree (s: store_record) (t: tableinst): Prop :=
  List.Forall (tabcl_agree s t.(tableinst_type).(tt_elem_type)) (t.(tableinst_elem)) /\
  tabsize_agree t.

Definition mem_agree (m : meminst) : Prop :=
  match m.(meminst_type).(lim_max) with
  | None => True
  | Some n => mem_size m <= n
  end.

Definition store_typing (s : store_record) : Prop :=
  match s with
  | Build_store_record fs tclss mss gs es ds =>
    List.Forall (cl_type_check_single s) fs /\
    List.Forall (tab_agree s) tclss /\
    List.Forall mem_agree mss
  end.


Inductive config_typing : store_record -> frame -> seq administrative_instruction -> seq value_type -> Prop :=
| mk_config_typing :
  forall s f es ts,
  store_typing s ->
  s_typing s None f es ts ->
  config_typing s f es ts.

End Store_validity.


End Host.

