(** Definition of Wasm datatypes
    See https://webassembly.github.io/spec/core/syntax/index.html
    and https://webassembly.github.io/spec/core/exec/index.html **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

(* TODO: use better representations than "nat", which is expensive;
   maybe N? maybe a 32-bit word type? *)

Require Import BinNat.
From Wasm Require array.
From Wasm Require Import common memory memory_list.
From Wasm Require Export numerics bytes.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From compcert Require common.Memdata.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Basic Datatypes **)

(* TODO: Documentation. *)

(* TODO: make these have structure; this will require monad-ifying the whole thing *)

Definition immediate (* i *) :=
  (* TODO: this is not a great representation *)
  nat.

Definition static_offset := (* off *) N. (* TODO: should be u32 *)

Definition alignment_exponent := (* a *) N. (* TODO: should be u32 *)

Definition serialise_i32 (i : i32) : bytes :=
  common.Memdata.encode_int 4%nat (numerics.Wasm_int.Int32.unsigned i).

Definition serialise_i64 (i : i64) : bytes :=
  common.Memdata.encode_int 8%nat (numerics.Wasm_int.Int64.unsigned i).

Definition serialise_f32 (f : f32) : bytes :=
  common.Memdata.encode_int 4%nat (Integers.Int.unsigned (numerics.Wasm_float.FloatSize32.to_bits f)).

Definition serialise_f64 (f : f64) : bytes :=
  common.Memdata.encode_int 8%nat (Integers.Int64.unsigned (numerics.Wasm_float.FloatSize64.to_bits f)).

(** std-doc:
Limits classify the size range of resizeable storage associated with memory types and table types.
If no maximum is given, the respective storage can grow to any size.
[https://webassembly.github.io/spec/core/syntax/types.html#limits]
 *)
Record limits : Type := {
  lim_min : N; (* TODO: should be u32 *)
  lim_max : option N; (* TODO: should be u32 *)
}.

(* TODO: factor this out, following the `memory` branch *)
Module Byte_Index <: array.Index_Sig.
Definition Index := N.
Definition Value := byte.
Definition index_eqb := N.eqb.
End Byte_Index.

Module Byte_array := array.Make Byte_Index.

Record data_vec : Type := {
  dv_length : N;
  dv_array : Byte_array.array;
}.

Record memory : Type := {
  mem_data : memory_list;
  mem_max_opt: option N; (* TODO: should be u32 *)
}.

(** std-doc:
Memory types classify linear memories and their size range.
The limits constrain the minimum and optionally the maximum size of a memory. The limits are given in units of page size.
[https://webassembly.github.io/spec/core/syntax/types.html#memory-types]
*)
Definition memory_type := limits.

(** std-doc:
Value types classify the individual values that WebAssembly code can compute with and the values that a variable accepts.
The types i32 and i64 classify 32 and 64 bit integers, respectively. Integers are not inherently signed or unsigned, their interpretation is determined by individual operations.

The types f32 and f64 classify 32 and 64 bit floating-point data, respectively. They correspond to the respective binary floating-point representations, also known as single and double precision, as defined by the IEEE 754-2019 standard (Section 3.3).
[https://webassembly.github.io/spec/core/syntax/types.html#value-types]
*)
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
(** std-doc:
[https://webassembly.github.io/spec/core/syntax/types.html#global-types]
*)
Inductive mutability : Type := (* mut *)
  | MUT_immut
  | MUT_mut
  .

(** std-doc:
Global types classify global variables, which hold a value and can either be mutable or immutable.
[https://webassembly.github.io/spec/core/syntax/types.html#global-types]
*)
Record global_type : Type := (* tg *) {
  tg_mut : mutability;
  tg_t : value_type
}.

(** std-doc:
Result types classify the result of executing instructions or functions, which is a sequence of values written with brackets.
[https://webassembly.github.io/spec/core/syntax/types.html#result-types]
*)
Definition result_type : Type :=
  list value_type.
(** Note from the specification:
  In the current version of WebAssembly, at most one value is allowed as a result.
  However, this may be generalized to sequences of values in future versions. **)


(** std-doc:
Function types classify the signature of functions, mapping a vector of
parameters to a vector of results. They are also used to classify the inputs
and outputs of instructions.
[https://webassembly.github.io/spec/core/syntax/types.html#function-types]
*)
Inductive function_type := (* tf *)
  | Tf : result_type -> result_type -> function_type
  (** Note from the specification:
    In the current version of Wasm, the result list has an arity of at most [1]. **)
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
[https://webassembly.github.io/spec/core/syntax/types.html#table-types]
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
  tc_table : list table_type;
  tc_memory : list memory_type;
  tc_local : list value_type;
  tc_label : list (list value_type);
  tc_return : option (list value_type);
}.

(** std-doc:
WebAssembly computations manipulate values of the four basic value types:
integers and floating-point data of 32 or 64 bit width each, respectively.
*)
Inductive value : Type := (* v *)
  | VAL_int32 : i32 -> value
  | VAL_int64 : i64 -> value
  | VAL_float32 : f32 -> value
  | VAL_float64 : f64 -> value
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
  | UOI_clz
  | UOI_ctz
  | UOI_popcnt
  .

Inductive unop_f : Type :=
  | UOF_neg
  | UOF_abs
  | UOF_ceil
  | UOF_floor
  | UOF_trunc
  | UOF_nearest
  | UOF_sqrt
  .

Inductive unop : Type :=
  | Unop_i : unop_i -> unop
  | Unop_f : unop_f -> unop
  .

Inductive binop_i : Type :=
  | BOI_add
  | BOI_sub
  | BOI_mul
  | BOI_div : sx -> binop_i
  | BOI_rem : sx -> binop_i
  | BOI_and
  | BOI_or
  | BOI_xor
  | BOI_shl
  | BOI_shr : sx -> binop_i
  | BOI_rotl
  | BOI_rotr
  .

Inductive binop_f : Type :=
  | BOF_add
  | BOF_sub
  | BOF_mul
  | BOF_div
  | BOF_min
  | BOF_max
  | BOF_copysign
  .

Inductive binop : Type :=
  | Binop_i : binop_i -> binop
  | Binop_f : binop_f -> binop
  .
  
Inductive testop : Type :=
  | TO_eqz
  .

Inductive relop_i : Type :=
  | ROI_eq
  | ROI_ne
  | ROI_lt : sx -> relop_i
  | ROI_gt : sx -> relop_i
  | ROI_le : sx -> relop_i
  | ROI_ge : sx -> relop_i
  .

Inductive relop_f : Type :=
  | ROF_eq
  | ROF_ne
  | ROF_lt
  | ROF_gt
  | ROF_le
  | ROF_ge
  .
  
Inductive relop : Type :=
  | Relop_i : relop_i -> relop
  | Relop_f : relop_f -> relop
  .

Inductive cvtop : Type :=
  | CVO_convert
  | CVO_reinterpret
  .

Inductive basic_instruction : Type := (* be *)
  | BI_unreachable
  | BI_nop
  | BI_drop
  | BI_select
  | BI_block : function_type -> list basic_instruction -> basic_instruction
  | BI_loop : function_type -> list basic_instruction -> basic_instruction
  | BI_if : function_type -> list basic_instruction -> list basic_instruction -> basic_instruction
  | BI_br : immediate -> basic_instruction
  | BI_br_if : immediate -> basic_instruction
  | BI_br_table : list immediate -> immediate -> basic_instruction
  | BI_return
  | BI_call : immediate -> basic_instruction
  | BI_call_indirect : immediate -> basic_instruction
  | BI_return_call : immediate -> basic_instruction
  | BI_return_call_indirect : immediate -> basic_instruction
  | BI_get_local : immediate -> basic_instruction
  | BI_set_local : immediate -> basic_instruction
  | BI_tee_local : immediate -> basic_instruction
  | BI_get_global : immediate -> basic_instruction
  | BI_set_global : immediate -> basic_instruction
  | BI_load : value_type -> option (packed_type * sx) -> alignment_exponent -> static_offset -> basic_instruction
  | BI_store : value_type -> option packed_type -> alignment_exponent -> static_offset -> basic_instruction
  | BI_current_memory
  | BI_grow_memory
  | BI_const : value -> basic_instruction
  | BI_unop : value_type -> unop -> basic_instruction
  | BI_binop : value_type -> binop -> basic_instruction
  | BI_testop : value_type -> testop -> basic_instruction
  | BI_relop : value_type -> relop -> basic_instruction
  | BI_cvtop : value_type -> cvtop -> value_type -> option sx -> basic_instruction
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
  inst_types : list function_type;
  inst_funcs : list funcaddr;
  inst_tab : list tableaddr;
  inst_memory : list memaddr;
  inst_globs : list globaladdr;
  (* TODO: exports field? *)
  }.

(** std-doc:
A function instance is the runtime representation of a function. It effectively
is a closure of the original function over the runtime module instance of its
originating module. The module instance is used to resolve references to other
definitions during execution of the function.
*)
Inductive function_closure : Type := (* cl *)
  | FC_func_native : instance -> function_type -> list value_type -> list basic_instruction -> function_closure
  | FC_func_host : function_type -> host_function -> function_closure
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
  table_max_opt: option N; (* TODO: should be u32 *)
}.

(** std-doc:
https://webassembly.github.io/spec/core/syntax/types.html#global-types
*)
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

(** std-doc:

[https://webassembly.github.io/spec/core/exec/runtime.html#syntax-frame]
*)
Record frame : Type := (* f *) {
  f_locs: list value;
  f_inst: instance
}.

(** * Administrative Instructions **)

(** std-doc:
WebAssembly code consists of sequences of instructions. Its computational model is based on a stack machine in that instructions manipulate values on an implicit operand stack, consuming (popping) argument values and producing or returning (pushing) result values.

In addition to dynamic operands from the stack, some instructions also have static immediate arguments, typically indices or type annotations, which are part of the instruction itself.

Some instructions are structured in that they bracket nested sequences of instructions.
[https://webassembly.github.io/spec/core/syntax/instructions.html]

In order to express the reduction of traps, calls, and control instructions,
the syntax of instructions is extended to include the following administrative
instructions:
*)
Inductive administrative_instruction : Type := (* e *)
| AI_basic : basic_instruction -> administrative_instruction
| AI_trap
| AI_invoke : funcaddr -> administrative_instruction
| AI_return_invoke : funcaddr -> administrative_instruction
| AI_label : nat -> seq administrative_instruction -> seq administrative_instruction -> administrative_instruction
| AI_local : nat -> frame -> seq administrative_instruction -> administrative_instruction
.

(** std-doc:
In order to specify the reduction of branches, the following syntax of block contexts is defined, indexed by the count k of labels surrounding a hole [_] that marks the place where the next step of computation is taking place:
https://www.w3.org/TR/wasm-core-1/#syntax-ctxt-block
 *)

Inductive lholed : nat -> Type :=
| LH_base : list value -> list administrative_instruction -> lholed 0
| LH_rec {k: nat}: list value -> nat -> list administrative_instruction -> lholed k -> list administrative_instruction -> lholed (S k)
.

(** std-doc:
Function bodies, initialization values for globals, and offsets of element or data segments are given as expressions, which are sequences of instructions terminated by an 𝖾𝗇𝖽 marker.
In some places, validation restricts expressions to be constant, which limits the set of allowable instructions.
[https://webassembly.github.io/spec/core/syntax/instructions.html#expressions]
*)
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

Inductive import_desc : Type :=
| ID_func : nat -> import_desc
| ID_table : table_type -> import_desc
| ID_mem : memory_type -> import_desc
| ID_global : global_type -> import_desc.

Definition name := list Byte.byte.

Record module_import : Type := {
  imp_module : name;
  imp_name : name;
  imp_desc : import_desc;
}.

Record module_table : Type := {
  modtab_type : table_type;
}.

Record module_glob : Type := {
  modglob_type : global_type;
  modglob_init : expr;
}.

Record module_start : Type := {
  modstart_func : funcidx;
}.

Record module_element : Type := {
  modelem_table : tableidx;
  modelem_offset : expr;
  modelem_init : list funcidx;
}.

Record code_func : Type := {
  fc_locals : list value_type;
  fc_expr : expr;
}.

Record module_data : Type := {
  moddata_data : memidx;
  moddata_offset : expr;
  moddata_init : list Byte.byte;
}.

Inductive module_export_desc : Type :=
| MED_func : funcidx -> module_export_desc
| MED_table : tableidx -> module_export_desc
| MED_mem : memidx -> module_export_desc
| MED_global : globalidx -> module_export_desc.

Record module_export : Type := {
  modexp_name : name;
  modexp_desc : module_export_desc;
}.

Record module_func : Type := {
  modfunc_type : typeidx;
  modfunc_locals : list value_type;
  modfunc_body : expr;
}.

(** std-doc:
WebAssembly programs are organized into modules, which are the unit of deployment, loading, and compilation. A module collects definitions for types, functions, tables, memories, and globals. In addition, it can declare imports and exports and provide initialization logic in the form of data and element segments or a start function.
[https://webassembly.github.io/spec/core/syntax/modules.html]
*)
Record module : Type := {
  mod_types : list function_type;
  mod_funcs : list module_func;
  mod_tables : list module_table;
  mod_mems : list memory_type;
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
| ET_mem : memory_type -> extern_t
| ET_glob : global_type -> extern_t
.


Definition config_tuple : Type := store_record * frame * list administrative_instruction.

End Host.
Arguments FC_func_native [host_function].

