(** Definition of Wasm datatypes **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

Require Import common.
Require Export numerics bytes.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Basic Datatypes **)

(* TODO: Documentation. *)

Definition immediate := nat. (* i *)

Definition static_offset := nat. (* off *)

Definition alignment_exponent := nat. (* a *)

Record limits := Mk_limits { lim_min : nat; lim_max : option nat; }.

Record memory : Type :=
  {mem_data : list byte; mem_limit: limits;}.

Inductive value_type : Type := (* t *)
  | T_i32
  | T_i64
  | T_f32
  | T_f64
  .


Definition result_type := seq value_type.
(** Note from the specification:
  In the current version of WebAssembly, at most one value is allowed as a result.
  However, this may be generalized to sequences of values in future versions. **)
(* FIXME: Do we want to enforce it? *)

Inductive packed_type : Type := (* tp *)
  | Tp_i8
  | Tp_i16
  | Tp_i32
  .

Inductive mutability : Type := (* mut *)
  | T_immut
  | T_mut
  .

Record global_type := (* tg *)
  { tg_mut : mutability; tg_t : value_type }.

Inductive function_type := (* tf *)
  | Tf : list value_type -> list value_type -> function_type
  (** Note from the specification:
    In the current version of Wasm, the result list has an arity of at most [1]. **)
  (* FIXME: Shouldn’t we enforce it? *)
  .

(** Typing context. **)
Record t_context := {
  tc_types_t : list function_type;
  tc_func_t : list function_type;
  tc_global : list global_type;
  tc_table : option nat;
  tc_memory : option nat;
  tc_local : list value_type;
  tc_label : list (list value_type);
  tc_return : option (list value_type);
}.

(* FIXME: What it is? Should we remove it?

Record s_context := {
  sc_inst : list t_context;
  sc_funcs : list function_type;
  sc_tab : list nat;
  sc_memory : list nat;
  sc_globs : list global_type;
}.

*)

Inductive value : Type := (* v *)
  | ConstInt32 : i32 -> value
  | ConstInt64 : i64 -> value
  | ConstFloat32 : f32 -> value
  | ConstFloat64 : f64 -> value
  .

Inductive result : Type :=
  | result_values : list value -> result
  (** Note from the specification:
    In the current version of WebAssembly, a result can consist of at most one value. **)
  | result_trap : result
  .

(** * Basic Instructions **)

Inductive sx : Type :=
  | sx_S
  | sx_U
  .

Inductive unop_i : Type :=
  | Clz
  | Ctz
  | Popcnt
  .

Inductive unop_f : Type :=
  | Neg
  | Abs
  | Ceil
  | Floor
  | Trunc
  | Nearest
  | Sqrt
  .

Inductive binop_i : Type :=
  | Add
  | Sub
  | Mul
  | Div : sx -> binop_i
  | Rem : sx -> binop_i
  | And
  | Or
  | Xor
  | Shl
  | Shr : sx -> binop_i
  | Rotl
  | Rotr
  .

Inductive binop_f : Type :=
  | Addf
  | Subf
  | Mulf
  | Divf
  | Min
  | Max
  | Copysign
  .

Inductive testop : Type :=
  | Eqz
  .

Inductive relop_i : Type :=
  | Eq
  | Ne
  | Lt : sx -> relop_i
  | Gt : sx -> relop_i
  | Le : sx -> relop_i
  | Ge : sx -> relop_i
  .

Inductive relop_f : Type :=
  | Eqf
  | Nef
  | Ltf
  | Gtf
  | Lef
  | Gef
  .

Inductive cvtop : Type :=
  | Convert
  | Reinterpret
  .

Inductive basic_instruction : Type := (* be *)
  | Unreachable
  | Nop
  | Drop
  | Select
  | Block : function_type -> list basic_instruction -> basic_instruction
  | Loop : function_type -> list basic_instruction -> basic_instruction
  | If : function_type -> list basic_instruction -> list basic_instruction -> basic_instruction
  | Br : immediate -> basic_instruction
  | Br_if : immediate -> basic_instruction
  | Br_table : list immediate -> immediate -> basic_instruction
  | Return
  | Call : immediate -> basic_instruction
  | Call_indirect : immediate -> basic_instruction
  | Get_local : immediate -> basic_instruction
  | Set_local : immediate -> basic_instruction
  | Tee_local : immediate -> basic_instruction
  | Get_global : immediate -> basic_instruction
  | Set_global : immediate -> basic_instruction
  | Load : value_type -> option (packed_type * sx) -> alignment_exponent -> static_offset -> basic_instruction
  | Store : value_type -> option packed_type -> alignment_exponent -> static_offset -> basic_instruction
  | Current_memory
  | Grow_memory
  | EConst : value -> basic_instruction
  | Unop_i : value_type -> unop_i -> basic_instruction
  | Unop_f : value_type -> unop_f -> basic_instruction
  | Binop_i : value_type -> binop_i -> basic_instruction
  | Binop_f : value_type -> binop_f -> basic_instruction
  | Testop : value_type -> testop -> basic_instruction
  | Relop_i : value_type -> relop_i -> basic_instruction
  | Relop_f : value_type -> relop_f -> basic_instruction
  | Cvtop : value_type -> cvtop -> value_type -> option sx -> basic_instruction
  .

(** * Functions and Store **)

Section Host.

(** We assume a family of host functions. **)
Variable host_function : Type.

Record instance : Type := (* inst *) {
  i_types : list function_type;
  i_funcs : list immediate;
  i_tab : option immediate;
  i_memory : option immediate;
  i_globs : list immediate;
}.

Inductive function_closure : Type := (* cl *)
  | Func_native : instance -> function_type -> list value_type -> list basic_instruction -> function_closure
  | Func_host : function_type -> host_function -> function_closure
  .

Record tabinst : Type :=
  {table_data: list (option nat); table_limit: limits;}.

Record global : Type := {
  g_mut : mutability;
  g_val : value;
}.

Record store_record : Type := (* s *) Build_store_record {
  s_funcs : list function_closure;
  s_tab : list tabinst;
  s_memory : list memory;
  s_globs : list global;
}.

(** * Administrative Instructions **)

Inductive administrative_instruction : Type := (* e *)
  | Basic : basic_instruction -> administrative_instruction
  | Trap
  | Invoke : function_closure -> administrative_instruction
  | Label : nat -> seq administrative_instruction -> seq administrative_instruction -> administrative_instruction
  | Local : nat -> instance -> list value -> seq administrative_instruction -> administrative_instruction
  .

Inductive lholed : Type :=
  | LBase : list administrative_instruction -> list administrative_instruction -> lholed
  | LRec : list administrative_instruction -> nat -> list administrative_instruction -> lholed -> list administrative_instruction -> lholed
  .

End Host.

Arguments Func_native [host_function].
Arguments Basic {host_function}.
Arguments Trap {host_function}.


(* TODO: these types were moved from parsing *)
Definition expr := list basic_instruction.

Inductive labelidx : Type :=
| Mk_labelidx : nat -> labelidx.

Inductive funcidx : Type :=
| Mk_funcidx : nat -> funcidx.
Inductive typeidx : Type :=
| Mk_typeidx : nat -> typeidx.

Inductive localidx : Type :=
| Mk_localidx : nat -> localidx.

Inductive globalidx : Type :=
| Mk_globalidx : nat -> globalidx.

Inductive elem_type : Type :=
| elem_type_tt : elem_type (* TODO: am I interpreting the spec correctly? *).

Record table_type : Type := Mk_table_type {
  tt_limits : limits;
  tt_elem_type : elem_type;
}.

Record mem_type : Type := Mk_mem_type { mem_type_lims : limits }.

Inductive import_desc : Type :=
| ID_func : nat -> import_desc
| ID_table : table_type -> import_desc
| ID_mem : mem_type -> import_desc
| ID_global : global_type -> import_desc.

Definition name := list ascii.

Record import : Type := Mk_import {
  imp_module : name;
  imp_name : name;
  imp_desc : import_desc;
}.

Record module : Type := {
  mod_types : list function_type;
  mod_funcs : list func2;
  mod_tables : list table;
  mod_mems : list mem;
  mod_globals : list global2;
  mod_elements : list element;
  mod_data : list data;
  mod_start : option start;
  mod_imports : list import;
  mod_exports : list export;
}.

