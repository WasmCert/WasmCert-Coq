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

Definition memory := list byte.

Inductive value_type : Type := (* t *)
  | T_i32
  | T_i64
  | T_f32
  | T_f64
  .

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
Context `(host_function : Type).

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

Definition tabinst := list (option function_closure).

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
  | Callcl : function_closure -> administrative_instruction
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

