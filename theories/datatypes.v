(** Definition of Wasm datatypes **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

(* TODO: use better representations that "nat", which is expensive;
   maybe N? maybe a 32-bit word type? *)

(* TODO: sanitise names *)

From Wasm Require Import common.
From Wasm Require Export numerics bytes.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From compcert Require common.Memdata.
Require Import Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Basic Datatypes **)

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

Record limits : Type := {
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
  | T_f64
  .


Inductive packed_type : Type := (* tp *)
  | Tp_i8
  | Tp_i16
  | Tp_i32
  .

(* TODO: the standard calls those const and var *)
Inductive mutability : Type := (* mut *)
  | MUT_immut
  | MUT_mut
  .

Record global_type : Type := (* tg *) {
  tg_mut : mutability;
  tg_t : value_type
}.

(** std-doc:
Result types classify the result of executing instructions or functions, which is a sequence of values written with brackets.
*)
Definition result_type : Type :=
  list value_type.
(** Note from the specification:
  In the current version of WebAssembly, at most one value is allowed as a result.
  However, this may be generalized to sequences of values in future versions. **)
(* FIXME: Do we want to enforce it? *)


(** std-doc:
Function types classify the signature of functions, mapping a vector of
parameters to a vector of results. They are also used to classify the inputs
and outputs of instructions.
*)
Inductive function_type := (* tf *)
  | Tf : result_type -> result_type -> function_type
  (** Note from the specification:
    In the current version of Wasm, the result list has an arity of at most [1]. **)
  (* FIXME: Shouldn’t we enforce it? *)
  .

(** std-doc:
The element type funcref is the infinite union of all function types. A table
of that type thus contains references to functions of heterogeneous type.
*)
Inductive elem_type : Type :=
| ELT_funcref : elem_type.

(** std-doc:
Table types classify tables over elements of element types within a size range.

Like memories, tables are constrained by limits for their minimum and
optionally maximum size. The limits are given in numbers of entries.
*)
Record table_type : Type := {
  tt_limits : limits;
  tt_elem_type : elem_type;
}.

(** Typing context. **)
(** std-doc:
Validity of an individual definition is specified relative to a context, which
collects relevant information about the surrounding module and the definitions
in scope:
- Types: the list of types defined in the current module.
- Functions: the list of functions declared in the current module, represented
  by their function type.
- Tables: the list of tables declared in the current module, represented by
  their table type.
- Memories: the list of memories declared in the current module, represented by
  their memory type.
- Globals: the list of globals declared in the current module, represented by
  their global type.
- Locals: the list of locals declared in the current function (including
  parameters), represented by their value type.
- Labels: the stack of labels accessible from the current position, represented
  by their result type.
- Return: the return type of the current function, represented as an optional
  result type that is absent when no return is allowed, as in free-standing
  expressions.
In other words, a context contains a sequence of suitable types for each index
space, describing each defined entry in that space. Locals, labels and return
type are only used for validating instructions in function bodies, and are left
empty elsewhere. The label stack is the only part of the context that changes
as validation of an instruction sequence proceeds.
*)
Record t_context : Type := {
  tc_types_t : list function_type;
  tc_func_t : list function_type;
  tc_global : list global_type;
  tc_table : list table_type (* TODO: follows the spec; mismatch with the isabelle version *);
  tc_memory : list limits;
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


(** std-doc:
WebAssembly computations manipulate values of the four basic value types:
integers and floating-point data of 32 or 64 bit width each, respectively.
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
  | SX_S
  | SX_U
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

Definition funcaddr := immediate (* TODO: should be funcidx *).
Definition tableaddr := immediate (* TODO: should be tableidx *).
Definition memaddr := immediate. (* TODO: should be memidx *)
Definition globaladdr := immediate. (* TODO: should be globalidx *)


(** std-doc:
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
  i_funcs : list funcaddr;
  i_tab : list tableaddr;
  i_memory : list memaddr;
  i_globs : list globaladdr;
  (* TODO: exports field? *)
}.

(** std-doc:
A function instance is the runtime representation of a function. It effectively
is a closure of the original function over the runtime module instance of its
originating module. The module instance is used to resolve references to other
definitions during execution of the function.
*)
Inductive function_closure : Type := (* cl *)
  | Func_native : instance -> function_type -> list value_type -> list basic_instruction -> function_closure
  | Func_host : function_type -> host_function -> function_closure
  .

(** std-doc:
Each function element is either empty, representing an uninitialized table
entry, or a function address. Function elements can be mutated through the
execution of an element segment or by external means provided by the embedder.
*)
Definition funcelem := option nat.

(** std-doc:
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

(** std-doc:
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

Definition expr := list basic_instruction.

Inductive labelidx : Type :=
| Mk_labelidx : nat -> labelidx.

Inductive funcidx : Type :=
| Mk_funcidx : nat -> funcidx.

Inductive tableidx : Type :=
| Mk_tableidx : nat -> tableidx.

Inductive memidx : Type :=
| Mk_memidx : nat -> memidx.

Inductive typeidx : Type :=
| Mk_typeidx : nat -> typeidx.

Inductive localidx : Type :=
| Mk_localidx : nat -> localidx.

Inductive globalidx : Type :=
| Mk_globalidx : nat -> globalidx.

Inductive mem_type : Type :=
| Mk_mem_type : limits -> mem_type.

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

Record module_table : Type := {
  t_type : table_type;
}.

Record module_glob : Type := {
  mg_type : global_type;
  mg_init : expr;
}.

Record module_start : Type := {
  start_func : funcidx;
}.

Record module_element : Type := {
  elem_table : tableidx;
  elem_offset : expr;
  elem_init : list funcidx;
}.

Record code_func : Type := {
  fc_locals : list value_type;
  fc_expr : expr;
}.

Record module_data : Type := {
  dt_data : memidx;
  dt_offset : expr;
  dt_init : list Byte.byte;
}.

Inductive module_export_desc : Type :=
| ED_func : funcidx -> module_export_desc
| ED_table : tableidx -> module_export_desc
| ED_mem : memidx -> module_export_desc
| ED_global : globalidx -> module_export_desc.

Record module_export : Type := {
  exp_name : name;
  exp_desc : module_export_desc;
}.

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

End Host.

Arguments Func_native [host_function].
Arguments Basic {host_function}.
Arguments Trap {host_function}.

