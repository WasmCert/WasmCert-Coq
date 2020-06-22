(** Definition of Wasm datatypes **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

(* TODO: use better representations that "nat", which is expensive;
   maybe N? maybe a 32-bit word type? *)

(* TODO: sanitise names *)

Require Import common.
Require Export numerics bytes.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From compcert Require common.Memdata.
Require Import Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* TODO: Documentation. *)

(* TODO: make these have structure; this will require monad-ifying the whole thing *)
Definition host := unit.
Definition host_state := unit.

Definition immediate (* i *) :=
  (* TODO: this is not a great representation *)
  nat.

Definition static_offset := (* off *) nat.

Definition alignment_exponent := (* a *) nat.

Definition serialise_i32 (i : i32) : bytes :=
  common.Memdata.encode_int 4%nat (numerics.Wasm_int.Int32.unsigned i).

Definition serialise_i64 (i : i64) : bytes :=
  common.Memdata.encode_int 8%nat (numerics.Wasm_int.Int64.unsigned i).

Definition serialise_f32 (f : f32) : bytes :=
  common.Memdata.encode_int 4%nat (Integers.Int.unsigned (numerics.Wasm_float.FloatSize32.to_bits f)).

Definition serialise_f64 (f : f64) : bytes :=
  common.Memdata.encode_int 8%nat (Integers.Int64.unsigned (numerics.Wasm_float.FloatSize64.to_bits f)).

Record limits := {
  lim_min : nat;
  lim_max : option nat;
}.

Record memory : Type := {
  mem_data : list byte;
  mem_limit: limits;
}.

Inductive value_type : Type := (* t *)
| T_i32
| T_i64
| T_f32
| T_f64.

Inductive packed_type : Type := (* tp *)
| Tp_i8
| Tp_i16
| Tp_i32.

Inductive mutability : Type := (* mut *)
| T_immut
| T_mut.

Record global_type := (* tg *) {
  tg_mut : mutability;
  tg_t : value_type
}.

Inductive function_type := (* tf *)
| Tf : list value_type -> list value_type -> function_type.

Inductive elem_type : Type :=
| elem_type_tt : elem_type (* TODO: am I interpreting the spec correctly? *).

Record table_type : Type := {
  tt_limits : limits;
  tt_elem_type : elem_type;
}.

Record t_context := {
  tc_types_t : list function_type;
  tc_func_t : list function_type;
  tc_global : list global_type;
  tc_table : list table_type (* TODO: follows the spec; mismatch with the isabelle version *);
  tc_memory : list limits;
  tc_local : list value_type;
  tc_label : list (list value_type);
  tc_return : option (list value_type);
}.

(* FIXME: Should we remove it?

Record s_context := {
  sc_inst : list t_context;
  sc_funcs : list function_type;
  sc_tab : list nat;
  sc_memory : list nat;
  sc_globs : list global_type;
}.

*)

Inductive sx : Type :=
| SX_S
| SX_U.

Inductive unop_i : Type :=
| Clz
| Ctz
| Popcnt.

Inductive unop_f : Type :=
| Neg
| Abs
| Ceil
| Floor
| Trunc
| Nearest
| Sqrt.

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
| Rotr.

Inductive binop_f : Type :=
| Addf
| Subf
| Mulf
| Divf
| Min
| Max
| Copysign.

Inductive testop : Type :=
| Eqz.

Inductive relop_i : Type :=
| Eq
| Ne
| Lt : sx -> relop_i
| Gt : sx -> relop_i
| Le : sx -> relop_i
| Ge : sx -> relop_i.

Inductive relop_f : Type :=
| Eqf
| Nef
| Ltf
| Gtf
| Lef
| Gef.

Inductive cvtop : Type :=
| Convert
| Reinterpret.

(**
WebAssembly computations manipulate values of the four basic value types:
integers and floating-point data of 32 or 64 bit width each, respectively.
*)
Inductive value : Type := (* v *)
| ConstInt32 : i32 -> value
| ConstInt64 : i64 -> value
| ConstFloat32 : f32 -> value
| ConstFloat64 : f64 -> value.

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
| Cvtop : value_type -> cvtop -> value_type -> option sx -> basic_instruction.

(**
A module instance is the runtime representation of a module. It is created by
instantiating a module, and collects runtime representations of all entities
that are imported, defined, or exported by the module.

Each component references runtime instances corresponding to respective
declarations from the original module – whether imported or defined – in the
order of their static indices. Function instances, table instances, memory
instances, and global instances are referenced with an indirection through
their respective addresses in the store.

It is an invariant of the semantics that all export instances in a given module
instance have different names.
*)
Record instance : Type := (* inst *) {
  i_types : list function_type;
  i_funcs : list immediate;
  i_tab : list immediate;
  i_memory : list immediate;
  i_globs : list immediate;
}.

Inductive function_closure : Type := (* cl *)
| Func_native : instance -> function_type -> list value_type -> list basic_instruction -> function_closure
| Func_host : function_type -> host -> function_closure.

(**
Each function element is either empty, representing an uninitialized table
entry, or a function address. Function elements can be mutated through the
execution of an element segment or by external means provided by the embedder.
*)
Definition funcelem := option nat.

(**
A table instance is the runtime representation of a table. It holds a vector of
function elements and an optional maximum size, if one was specified in the
table type at the table’s definition site.

It is an invariant of the semantics that the length of the element vector never
exceeds the maximum size, if present.
*)
Record tableinst : Type := {
  table_data: list funcelem;
  table_max_opt: option nat;
}.

Record global : Type := {
  g_mut : mutability;
  g_val : value;
}.

(**
The store represents all global state that can be manipulated by WebAssembly
programs. It consists of the runtime representation of all instances of
functions, tables, memories, and globals that have been allocated during the
life time of the abstract machine
*)
Record store_record : Type := (* s *) {
  s_funcs : list function_closure;
  s_tables : list tableinst;
  s_mems : list memory;
  s_globals : list global;
}.

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

Definition mem_type : Type := limits.

Inductive import_desc : Type :=
| ID_func : nat -> import_desc
| ID_table : table_type -> import_desc
| ID_mem : mem_type -> import_desc
| ID_global : global_type -> import_desc.

Definition name := list Byte.byte.

Record module_import : Type := {
  imp_module : name;
  imp_name : name;
  imp_desc : import_desc;
}.

Record module_table := {
  t_type : table_type;
}.

Record module_glob : Type := {
  mg_type : global_type;
  mg_init : expr;
}.

Record module_start := {
  start_func : nat;
}.

Record module_element : Type := {
  elem_table : nat;
  elem_offset : expr;
  elem_init : list nat;
}.

Record func : Type := {
  fc_locals : list value_type;
  fc_expr : expr;
}.

Record module_data : Type := {
  dt_data : nat;
  dt_offset : expr;
  dt_init : list Byte.byte;
}.

Inductive module_export_desc : Type :=
| ED_func : nat -> module_export_desc
| ED_table : nat -> module_export_desc
| ED_mem : nat -> module_export_desc
| ED_global : nat -> module_export_desc.

Record module_export : Type := {
  exp_name : name;
  exp_desc : module_export_desc;
}.

Inductive module_section : Type :=
| Sec_custom : list Byte.byte -> module_section
| Sec_type : list function_type -> module_section
| Sec_import : list module_import -> module_section
| Sec_function : list typeidx -> module_section
| Sec_table : list module_table -> module_section
| Sec_memory : list mem_type -> module_section
| Sec_global : list module_glob -> module_section
| Sec_export : list module_export -> module_section
| Sec_start : module_start -> module_section
| Sec_element : list module_element -> module_section
| Sec_code : list func -> module_section
| Sec_data : list module_data -> module_section.

Record module_func : Type := {
  mf_type : typeidx;
  mf_locals : list value_type;
  mf_body : expr;
}.

Record module : Type := {
  mod_types : list function_type;
  mod_funcs : list module_func;
  mod_tables : list module_table;
  mod_mems : list mem_type;
  mod_globals : list module_glob;
  mod_elem : list module_element;
  mod_data : list module_data;
  mod_start : option module_start;
  mod_imports : list module_import;
  mod_exports : list module_export;
}.

Inductive extern_t : Type :=
| ET_func : function_type -> extern_t
| ET_tab : table_type -> extern_t
| ET_mem : mem_type -> extern_t
| ET_glob : global_type -> extern_t.