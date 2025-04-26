(** Definition of Wasm datatypes
    See https://webassembly.github.io/spec/core/syntax/index.html
    and https://webassembly.github.io/spec/core/exec/index.html **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Wasm Require array.
From Wasm Require Export common numerics bytes memory.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From compcert Require common.Memdata.
Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
 

(** * Basic Datatypes **)

(** std-doc:
Definitions are referenced with zero-based indices. Each class of definition has its own index space, as distinguished by the following classes.

The index space for functions, tables, memories and globals includes respective imports declared in the same module. The indices of these imports precede the indices of other definitions in the same index space.

Element indices reference element segments and data indices reference data segments.

The index space for locals is only accessible inside a function and includes the parameters of that function, which precede the local variables.

Label indices reference structured control instructions inside an instruction sequence.

[https://www.w3.org/TR/wasm-core-2/syntax/modules.html#indices]
*)
Definition u32 : Set := N.
Definition u8: Set := N.

(* 2^32 *)
Definition u32_bound : N := 4294967296%N.

Definition typeidx : Set := u32.
Definition funcidx : Set := u32.
Definition tableidx : Set := u32.
Definition memidx : Set := u32.
Definition globalidx : Set := u32.
Definition elemidx : Set := u32.
Definition dataidx : Set := u32.
Definition localidx : Set := u32.
Definition labelidx : Set := u32.

(** std-doc:
Function instances, table instances, memory instances, and global instances, element instances, 
and data instances in the store are referenced with abstract addresses. These are simply indices 
into the respective store component. In addition, an embedder may supply an uninterpreted set of 
host addresses.

An embedder may assign identity to exported store objects corresponding to their addresses, even 
where this identity is not observable from within WebAssembly code itself (such as for function 
instances or immutable globals).

[https://www.w3.org/TR/wasm-core-2/exec/runtime.html#addresses]
*)

Definition addr := N.

Definition funcaddr : Set := addr.
Definition tableaddr : Set := addr.
Definition memaddr : Set := addr.
Definition globaladdr : Set := addr.
Definition elemaddr : Set := addr.
Definition dataaddr : Set := addr.
Definition externaddr : Set := addr.

(** std-doc:
WebAssembly programs operate on primitive numeric values. Moreover, in the definition of programs, immutable sequences of values occur to represent more complex data, such as text strings or other vectors.
*)

Inductive value_num : Type := 
  | VAL_int32 : i32 -> value_num
  | VAL_int64 : i64 -> value_num
  | VAL_float32 : f32 -> value_num
  | VAL_float64 : f64 -> value_num
.

(* We are not implementing SIMD at the moment. *)
Inductive value_vec : Set :=
  | VAL_vec128: unit -> value_vec
.

(* TODO: Unicode support? *)
Definition name := list Byte.byte.

Section Types.

(** std-doc:
Number types classify numeric values.

The types i32 and i64 classify 32 and 64 bit integers, respectively. Integers are not inherently signed or unsigned, their interpretation is determined by individual operations.

The types f32 and f64 classify 32 and 64 bit floating-point data, respectively. They correspond to the respective binary floating-point representations, also known as single and double precision, as defined by the IEEE 754-2019 standard (Section 3.3).

[https://www.w3.org/TR/wasm-core-2/syntax/types.html#number-types]
*)
Inductive number_type : Set := 
  | T_i32
  | T_i64
  | T_f32
  | T_f64
  .


(** std-doc:

Vector types classify vectors of numeric values processed by vector instructions (also known as SIMD instructions, single instruction multiple data).

The type v128 corresponds to a 128 bit vector of packed integer or floating-point data. The packed data can be interpreted as signed or unsigned integers, single or double precision floating-point values, or a single 128 bit type. The interpretation is determined by individual operations.

Vector types, like number types are transparent, meaning that their bit patterns can be observed. Values of vector type can be stored in memories.

[https://www.w3.org/TR/wasm-core-2/syntax/types.html#vector-types]
*)
  
Inductive vector_type : Set :=
| T_v128
.

(** std-doc:

Reference types classify first-class references to objects in the runtime store.

The type funcref denotes the infinite union of all references to functions, regardless of their function types.

The type externref denotes the infinite union of all references to objects owned by the embedder and that can be passed into WebAssembly under this type.

Reference types are opaque, meaning that neither their size nor their bit pattern can be observed. Values of reference type can be stored in tables.

[https://www.w3.org/TR/wasm-core-2/syntax/types.html#reference-types]
*)
Inductive reference_type : Set := 
| T_funcref
| T_externref
.

(** std-doc:

Value types classify the individual values that WebAssembly code can compute with and the values that a variable accepts. They are either number types, vector types, or reference types.

[https://www.w3.org/TR/wasm-core-2/syntax/types.html#value-types]
*)
(* Note here that we incorporate the bottom type (indicating that the type is unconstrained) in the operand types as part of the base value type, so that we can later drop the distinction between function types and stack types (and operand type vs value type). This is also a preparation for future extensions such as the funcref/GC proposal. *)
Inductive value_type: Set := (* t *)
| T_num: number_type -> value_type
| T_vec: vector_type -> value_type
| T_ref: reference_type -> value_type
| T_bot: value_type
.

(** std-doc:
Result types classify the result of executing instructions or functions, which is a sequence of values, written with brackets.

[https://www.w3.org/TR/wasm-core-2/syntax/types.html#result-types]
*)
Definition result_type : Set :=
  list value_type.

(** std-doc:

Function types classify the signature of functions, mapping a vector of
parameters to a vector of results. They are also used to classify the inputs
and outputs of instructions.

[https://www.w3.org/TR/wasm-core-2/syntax/types.html#function-types]
*)
Inductive function_type := (* tf *)
| Tf : result_type -> result_type -> function_type
.

(* This is a definition for future extensions, where instruction types are no longer
the same as function types. *)
Definition instr_type := function_type.

(** std-doc:
Limits classify the size range of resizeable storage associated with memory types and table types.
If no maximum is given, the respective storage can grow to any size.

[https://www.w3.org/TR/wasm-core-2/syntax/types.html#limits]
*)
Record limits : Set := {
  lim_min : u32;
  lim_max : option u32;
}.

(** std-doc:
Limits must have meaningful bounds that are within a given range.
https://www.w3.org/TR/wasm-core-2/valid/types.html#limits
**)
Definition limit_valid_range (lim: limits) (k: N) : bool :=
  (N.leb lim.(lim_min) k) &&
    match lim.(lim_max) with
    | Some lmax => (N.leb lim.(lim_min) lmax) && (N.leb lmax k)
    | None => true
    end.


(** std-doc:
Memory types classify linear memories and their size range.
The limits constrain the minimum and optionally the maximum size of a memory. The limits are given in units of page size.

[https://www.w3.org/TR/wasm-core-2/syntax/types.html#memory-types]
*)
Definition memory_type := limits.


(** std-doc:
Table types classify tables over elements of reference types within a size range.

Like memories, tables are constrained by limits for their minimum and
optionally maximum size. The limits are given in numbers of entries.

[https://www.w3.org/TR/wasm-core-2/syntax/types.html#table-types]
*)
Record table_type : Set := {
  tt_limits : limits;
  tt_elem_type : reference_type;
}.


(** std-doc:

[https://www.w3.org/TR/wasm-core-2/syntax/types.html#global-types]
*)
Inductive mutability : Set := (* mut *)
  | MUT_const
  | MUT_var
  .


(** std-doc:
Global types classify global variables, which hold a value and can either be mutable or immutable.

[https://www.w3.org/TR/wasm-core-2/syntax/types.html#global-types]
*)
Record global_type : Set := (* tg *) {
  tg_mut : mutability;
  tg_t : value_type
}.

  
(** std-doc:
External types classify imports and external values with their respective types.

[https://www.w3.org/TR/wasm-core-2/syntax/types.html#external-types]
*)
  
Inductive extern_type : Set :=
| ET_func : function_type -> extern_type
| ET_table : table_type -> extern_type
| ET_mem : memory_type -> extern_type
| ET_global : global_type -> extern_type
.

(** std-doc:
A structured instruction can consume input and produce output on the operand stack according to its annotated block type. 
*)
Inductive block_type : Set :=
| BT_id: typeidx -> block_type
| BT_valtype: option value_type -> block_type
.

(** std-doc: 
Most types are universally valid. However, restrictions apply to limits, which must be checked during validation. Moreover, block types are converted to plain function types for ease of processing.
**)

Definition functype_valid (ft: function_type) : bool :=
  true.

Definition table_limit_bound : N := (N.sub u32_bound 1%N).

Definition tabletype_valid (tt: table_type) : bool :=
  limit_valid_range tt.(tt_limits) table_limit_bound.

Definition mem_limit_bound : N := 65536%N.

Definition memtype_valid (mt: memory_type) : bool :=
  limit_valid_range mt mem_limit_bound.

Definition globaltype_valid (gt: global_type) : bool :=
  true.

End Types.


Definition static_offset := (* off *) u32. 

Definition alignment_exponent := (* a *) u32. 

Definition serialise_i32 (i : i32) : bytes :=
  common.Memdata.encode_int 4%nat (numerics.Wasm_int.Int32.unsigned i).

Definition serialise_i64 (i : i64) : bytes :=
  common.Memdata.encode_int 8%nat (numerics.Wasm_int.Int64.unsigned i).

Definition serialise_f32 (f : f32) : bytes :=
  common.Memdata.encode_int 4%nat (Integers.Int.unsigned (numerics.Wasm_float.FloatSize32.to_bits f)).

Definition serialise_f64 (f : f64) : bytes :=
  common.Memdata.encode_int 8%nat (Integers.Int64.unsigned (numerics.Wasm_float.FloatSize64.to_bits f)).

  
Section Instructions.
  
(** * Basic Instructions **)


Inductive sx : Set :=
  | SX_S
  | SX_U
  .

Inductive unop_i : Set :=
  | UOI_clz
  | UOI_ctz
  | UOI_popcnt
  .

Inductive unop_f : Set :=
  | UOF_abs
  | UOF_neg
  | UOF_sqrt
  | UOF_ceil
  | UOF_floor
  | UOF_trunc
  | UOF_nearest
  .

Inductive unop : Set :=
  | Unop_i : unop_i -> unop
  | Unop_f : unop_f -> unop
  | Unop_extend : N -> unop
  .

Inductive binop_i : Set :=
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

Inductive binop_f : Set :=
  | BOF_add
  | BOF_sub
  | BOF_mul
  | BOF_div
  | BOF_min
  | BOF_max
  | BOF_copysign
  .

Inductive binop : Set :=
  | Binop_i : binop_i -> binop
  | Binop_f : binop_f -> binop
  .
  
Inductive testop : Set :=
  | TO_eqz
  .

Inductive relop_i : Set :=
  | ROI_eq
  | ROI_ne
  | ROI_lt : sx -> relop_i
  | ROI_gt : sx -> relop_i
  | ROI_le : sx -> relop_i
  | ROI_ge : sx -> relop_i
  .

Inductive relop_f : Set :=
  | ROF_eq
  | ROF_ne
  | ROF_lt
  | ROF_gt
  | ROF_le
  | ROF_ge
  .
  
Inductive relop : Set :=
  | Relop_i : relop_i -> relop
  | Relop_f : relop_f -> relop
  .

(* TODO: comment on the other cvtops *)
Inductive cvtop : Set :=
  | CVO_wrap
  | CVO_extend
  | CVO_trunc
  | CVO_trunc_sat
  | CVO_convert
  | CVO_demote
  | CVO_promote
  | CVO_reinterpret
  .

Inductive packed_type : Set := (* tp *)
  | Tp_i8
  | Tp_i16
  | Tp_i32
  .

Inductive shape_vec_i: Set :=
  | SVI_8_16
  | SVI_16_8
  | SVI_32_4
  | SVI_64_2
  .
  
Inductive shape_vec_f: Set :=
  | SVF_32_4
  | SVF_64_2
  .
  
Inductive shape_vec : Set := (* shape *)
  | SV_ishape: shape_vec_i -> shape_vec
  | SV_fshape: shape_vec_f -> shape_vec
  .

Inductive unop_vec : Set :=
  | VUO_not
  .
  
Inductive binop_vec : Set :=
  | VBO_and
  .
  
Inductive ternop_vec : Set :=
  | VTO_bitselect
  .
  
Inductive test_vec : Set :=
  | VT_any_true
  .
  
Inductive shift_vec : Set :=
  | VSH_any_true
  .

Definition laneidx := u8.

Inductive packed_type_vec :=
  | Tptv_8_8
  | Tptv_16_4
  | Tptv_32_2
.

Inductive zero_type_vec :=
  | Tztv_32
  | Tztv_64
.

Inductive width_vec :=
  | Twv_8
  | Twv_16
  | Twv_32
  | Twv_64
  .

Inductive load_vec_arg :=
  | LVA_packed: packed_type_vec -> sx -> load_vec_arg
  | LVA_zero: zero_type_vec -> load_vec_arg
  | LVA_splat: width_vec -> load_vec_arg
  .

Record memarg : Set :=
  { memarg_offset : u32;
    memarg_align: u32
  }.
  
Inductive basic_instruction : Type := (* be *)
(** std-doc:
Numeric instructions provide basic operations over numeric values of specific type. These operations closely match respective operations available in hardware.
 **)
  | BI_const_num : value_num -> basic_instruction
  | BI_unop : number_type -> unop -> basic_instruction
  | BI_binop : number_type -> binop -> basic_instruction
  | BI_testop : number_type -> testop -> basic_instruction
  | BI_relop : number_type -> relop -> basic_instruction
  | BI_cvtop : number_type -> cvtop -> number_type -> option sx -> basic_instruction
(** std-doc: (not implemented yet)
Vector instructions (also known as SIMD instructions, single data multiple value) provide basic operations over values of vector type.
Vector instructions can be grouped into several subcategories:

Constants: return a static constant.
Unary Operations: consume one v128 operand and produce one v128 result.
Binary Operations: consume two v128 operands and produce one v128 result.
Ternary Operations: consume three v128 operands and produce one v128 result.
Tests: consume one v128 operand and produce a Boolean integer result.
Shifts: consume a v128 operand and a i32 operand, producing one v128 result.
Splats: consume a value of numeric type and produce a v128 result of a specified shape.
Extract lanes: consume a v128 operand and return the numeric value in a given lane.
Replace lanes: consume a v128 operand and a numeric value for a given lane, and produce a v128 result.
**)
  | BI_const_vec : value_vec -> basic_instruction
  | BI_unop_vec: unop_vec -> basic_instruction
  | BI_binop_vec: binop_vec -> basic_instruction
  | BI_ternop_vec: ternop_vec -> basic_instruction
  | BI_test_vec: test_vec -> basic_instruction
  | BI_shift_vec: shift_vec -> basic_instruction
  | BI_splat_vec: shape_vec -> basic_instruction
  | BI_extract_vec: shape_vec -> option sx -> laneidx -> basic_instruction
  | BI_replace_vec: shape_vec -> laneidx -> basic_instruction
(** std-doc:
Instructions in this group are concerned with accessing references.
**)
  | BI_ref_null : reference_type -> basic_instruction  
  | BI_ref_is_null
  | BI_ref_func : funcidx -> basic_instruction
(** std-doc:
Instructions in this group can operate on operands of any value type.
**)
  | BI_drop
  | BI_select : option (list value_type) -> basic_instruction
(** std-doc: 
Variable instructions are concerned with access to local or global variables.
**)
  | BI_local_get : localidx -> basic_instruction
  | BI_local_set : localidx -> basic_instruction
  | BI_local_tee : localidx -> basic_instruction
  | BI_global_get : globalidx -> basic_instruction
  | BI_global_set : globalidx -> basic_instruction
(** std-doc:
Instructions in this group are concerned with tables.
**)
  | BI_table_get : tableidx -> basic_instruction
  | BI_table_set : tableidx -> basic_instruction
  | BI_table_size : tableidx -> basic_instruction
  | BI_table_grow : tableidx -> basic_instruction
  | BI_table_fill : tableidx -> basic_instruction
  | BI_table_copy : tableidx -> tableidx -> basic_instruction
  | BI_table_init : tableidx -> elemidx -> basic_instruction
  | BI_elem_drop : elemidx -> basic_instruction
(** std-doc:
Instructions in this group are concerned with linear memory.
**)
  | BI_load : number_type -> option (packed_type * sx) -> memarg -> basic_instruction
  | BI_load_vec : load_vec_arg -> memarg -> basic_instruction
  (* the lane version has a different type signature *)
  | BI_load_vec_lane : width_vec -> memarg -> laneidx -> basic_instruction
  | BI_store : number_type -> option packed_type -> memarg-> basic_instruction
  | BI_store_vec_lane : width_vec -> memarg -> laneidx -> basic_instruction
  | BI_memory_size
  | BI_memory_grow
  | BI_memory_fill
  | BI_memory_copy
  | BI_memory_init: dataidx -> basic_instruction
  | BI_data_drop: dataidx -> basic_instruction
(** std-doc:
Instructions in this group affect the flow of control.
**)
  | BI_nop
  | BI_unreachable
  | BI_block : block_type -> list basic_instruction -> basic_instruction
  | BI_loop : block_type -> list basic_instruction -> basic_instruction
  | BI_if : block_type -> list basic_instruction -> list basic_instruction -> basic_instruction
  | BI_br : labelidx -> basic_instruction
  | BI_br_if : labelidx -> basic_instruction
  | BI_br_table : list labelidx -> labelidx -> basic_instruction
  | BI_return
  | BI_call : funcidx -> basic_instruction
  | BI_call_indirect : tableidx -> typeidx -> basic_instruction
  .


(** std-doc:
Function bodies, initialization values for globals, and offsets of element or data segments are given as expressions, which are sequences of instructions terminated by an 𝖾𝗇𝖽 marker.

In some places, validation restricts expressions to be constant, which limits the set of allowable instructions.

*)
Definition expr := list basic_instruction.

End Instructions.

(** std-doc:
WebAssembly computations manipulate values of either the four basic number types, i.e., integers and floating-point data of 32 or 64 bit width each, of vectors of 128 bit width, or of reference type.

In most places of the semantics, values of different types can occur. In order to avoid ambiguities, values are therefore represented with an abstract syntax that makes their type explicit. It is convenient to reuse the same notation as for the 
const instructions and ref.null producing them.

References other than null are represented with additional administrative instructions. They either are function references, pointing to a specific function address, or external references pointing to an uninterpreted form of extern address that can be defined by the embedder to represent its own objects.
*)
Inductive value_ref : Set :=
| VAL_ref_null: reference_type -> value_ref
| VAL_ref_func: funcaddr -> value_ref
| VAL_ref_extern: externaddr -> value_ref
.

Inductive value : Type :=
| VAL_num: value_num -> value
| VAL_vec: value_vec -> value
| VAL_ref: value_ref -> value
.


Section Modules.    

(** std-doc:
The imports component of a module defines a set of imports that are required for instantiation.

Each import is labeled by a two-level name space, consisting of a module name and a name for
 an entity within that module. Importable definitions are functions, tables, memories, and globals.
 Each import is specified by a descriptor with a respective type that a definition provided during
 instantiation is required to match.

Every import defines an index in the respective index space. In each index space, the indices of imports go before the first index of any definition contained in the module itself.

[https://www.w3.org/TR/wasm-core-2/syntax/modules.html#imports]
*)
Inductive module_import_desc : Set :=
| MID_func : typeidx -> module_import_desc
| MID_table : table_type -> module_import_desc
| MID_mem : memory_type -> module_import_desc
| MID_global : global_type -> module_import_desc.

Record module_import : Set := {
  imp_module : name;
  imp_name : name;
  imp_desc : module_import_desc;
}.

Record module_func : Type := {
  modfunc_type : typeidx;
  modfunc_locals : list value_type;
  modfunc_body : expr;
}.

Record module_table : Set := {
  modtab_type : table_type;
}.

Record module_mem : Set := {
  modmem_type : memory_type;
}.

Record module_global : Type := {
  modglob_type : global_type;
  modglob_init : expr;
}.


(** std-doc:
The initial contents of a table is uninitialized. Element segments can be used to initialize a 
subrange of a table from a static vector of elements.

The elems component of a module defines a vector of element segments. Each element segment defines 
a reference type and a corresponding list of constant element expressions.

Element segments have a mode that identifies them as either passive, active, or declarative. 
A passive element segment’s elements can be copied to a table using the table.init instruction. 
An active element segment copies its elements into a table during instantiation, as specified by 
a table index and a constant expression defining an offset into that table. A declarative element 
segment is not available at runtime but merely serves to forward-declare references that are formed 
in code with instructions like ref.func.

The offset is given by a constant expression.

Element segments are referenced through element indices.
[https://www.w3.org/TR/wasm-core-2/syntax/modules.html#element-segments]
*)

Inductive module_elemmode : Type :=
| ME_passive
| ME_active : tableidx -> expr -> module_elemmode
| ME_declarative
.

Record module_element : Type := {
  modelem_type : reference_type;
  modelem_init : list expr;
  modelem_mode : module_elemmode;  
}.


(** std-doc:
The initial contents of a memory are zero bytes. Data segments can be used to initialize a range 
of memory from a static vector of bytes.

The datas component of a module defines a vector of data segments.

Like element segments, data segments have a mode that identifies them as either passive or active. 
A passive data segment’s contents can be copied into a memory using the memory.init instruction. 
An active data segment copies its contents into a memory during instantiation, as specified by a 
memory index and a constant expression defining an offset into that memory.

The initial contents of a table is uninitialized. Element segments can be used to initialize a 
subrange of a table from a static vector of elements.

Data segments are referenced through data indices.
[https://www.w3.org/TR/wasm-core-2/syntax/modules.html#data-segments]
*)

Inductive module_datamode : Type :=
| MD_passive
| MD_active : memidx -> expr -> module_datamode
.

Record module_data : Type := {
  moddata_init : list byte;
  moddata_mode : module_datamode;  
}.

Record module_start : Set := {
  modstart_func : funcidx;
}.


Inductive module_export_desc : Set :=
| MED_func : funcidx -> module_export_desc
| MED_table : tableidx -> module_export_desc
| MED_mem : memidx -> module_export_desc
| MED_global : globalidx -> module_export_desc.

Record module_export : Set := {
  modexp_name : name;
  modexp_desc : module_export_desc;
}.

(** std-doc:
WebAssembly programs are organized into modules, which are the unit of deployment, loading, and compilation. A module collects definitions for types, functions, tables, memories, and globals. In addition, it can declare imports and exports and provide initialization logic in the form of data and element segments or a start function.
[https://webassembly.github.io/spec/core/syntax/modules.html]
*)
Record module : Type := {
  mod_types : list function_type;
  mod_funcs : list module_func;
  mod_tables : list module_table;
  mod_mems : list module_mem;
  mod_globals : list module_global;
  mod_elems : list module_element;
  mod_datas : list module_data;
  mod_start : option module_start;
  mod_imports : list module_import;
  mod_exports : list module_export;
}.
    
End Modules.

(** Validation **)

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
- Element Segments: the list of element segments declared in the current module,
  represented by their element type.
- Data Segments: the list of data segments declared in the current module, each
  represented by an ok entry.
- Locals: the list of locals declared in the current function (including
  parameters), represented by their value type.
- Labels: the stack of labels accessible from the current position, represented
  by their result type.
- Return: the return type of the current function, represented as an optional
  result type that is absent when no return is allowed, as in free-standing
  expressions.
- References: the list of function indices that occur in the module outside functions and can hence be used to form references inside them.

In other words, a context contains a sequence of suitable types for each index
space, describing each defined entry in that space. Locals, labels and return
type are only used for validating instructions in function bodies, and are left
empty elsewhere. The label stack is the only part of the context that changes
as validation of an instruction sequence proceeds.

[https://www.w3.org/TR/wasm-core-2/valid/conventions.html#contexts]
 *)

Definition ok: Set := unit.

Record t_context : Set := {
  tc_types : list function_type;
  tc_funcs : list function_type;
  tc_tables : list table_type;
  tc_mems : list memory_type;
  tc_globals : list global_type;
  tc_elems : list reference_type;
  tc_datas : list ok;
  tc_locals : list value_type;
  tc_labels : list result_type;
  tc_return : option result_type;
  tc_refs : list funcidx;
}.

Inductive result : Type :=
| result_values : list value -> result
(** Note from the specification:
  In the current version of WebAssembly, a result can consist of at most one value. **)
| result_trap : result
.


(** * Functions and Store **)


(** std-doc:
A table instance is the runtime representation of a table. It records its type and 
holds a vector of reference values.

Table elements can be mutated through table instructions, the execution of an active 
element segment, or by external means provided by the embedder.

It is an invariant of the semantics that all table elements have a type equal to the 
element type of tabletype. It also is an invariant that the length of the element vector 
never exceeds the maximum size of tabletype, if present.

[https://www.w3.org/TR/wasm-core-2/exec/runtime.html#table-instances]
*)
Record tableinst : Set := {
  tableinst_type : table_type;
  tableinst_elem : list value_ref;
}.


(** std-doc:
A memory instance is the runtime representation of a linear memory. It records 
its type and holds a vector of bytes.

The length of the vector always is a multiple of the WebAssembly page size, which 
is defined to be the constant 65536 – abbreviated 64Ki.

The bytes can be mutated through memory instructions, the execution of an active data 
segment, or by external means provided by the embedder.

It is an invariant of the semantics that the length of the byte vector, divided by page 
size, never exceeds the maximum size of memtype, if present.

[https://www.w3.org/TR/wasm-core-2/exec/runtime.html#memory-instances]
*)

Section Memory.

Context `{Memory}.

Record meminst : Type := {
  meminst_type : memory_type;
  meminst_data: mem_t;
}.

(** std-doc:
A global instance is the runtime representation of a global variable. It records its 
type and holds an individual value.

The value of mutable globals can be mutated through variable instructions or by external 
means provided by the embedder.

It is an invariant of the semantics that the value has a type equal to the value type of globaltype.

[https://www.w3.org/TR/wasm-core-2/exec/runtime.html#global-instances]
*)
Record globalinst : Type := {
  g_type : global_type;
  g_val : value;
}.


(** std-doc:
An element instance is the runtime representation of an element segment. It holds a vector 
of references and their common type.

[https://www.w3.org/TR/wasm-core-2/exec/runtime.html#element-instances]
*)
Record eleminst : Set := {
  eleminst_type : reference_type;
  eleminst_elem : list value_ref;
}.


(** std-doc:
A data instance is the runtime representation of a data segment. It holds a vector of bytes.

[https://www.w3.org/TR/wasm-core-2/exec/runtime.html#data-instances]
*)
Record datainst : Set := {
  datainst_data : list byte;
}.

(** std-doc:
An external value is the runtime representation of an entity that can be imported or 
exported. It is an address denoting either a function instance, table instance, memory 
instance, or global instances in the shared store.

[https://www.w3.org/TR/wasm-core-2/exec/runtime.html#external-values]
*)
Inductive extern_value: Set :=
| EV_func: funcaddr -> extern_value
| EV_table: tableaddr -> extern_value
| EV_mem: memaddr -> extern_value
| EV_global: globaladdr -> extern_value
.


(** std-doc:
An export instance is the runtime representation of an export. It defines the export’s 
name and the associated external value.

[https://www.w3.org/TR/wasm-core-2/exec/runtime.html#export-instances]
*)
Record exportinst : Type := {
  exportinst_name: name;
  exportinst_val: extern_value;
}.


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

[https://www.w3.org/TR/wasm-core-2/exec/runtime.html#module-instances]
*)
Record moduleinst : Type := (* inst *) {
  inst_types : list function_type;
  inst_funcs : list funcaddr;
  inst_tables : list tableaddr;
  inst_mems : list memaddr;
  inst_globals : list globaladdr;
  inst_elems : list elemaddr;
  inst_datas : list dataaddr;
  inst_exports: list exportinst;  
  }.

Definition empty_moduleinst := Build_moduleinst nil nil nil nil nil nil nil nil.


(** We assume a family of host functions. **)
Class host_function_class : Type :=
  { host_function : Type; 
    host_function_eq_dec : forall f1 f2 : host_function, {f1 = f2} + {f1 <> f2}
  }.

Section Host.

  Context `{host_function_class}.

(** std-doc:
A function instance is the runtime representation of a function. It effectively
is a closure of the original function over the runtime module instance of its
originating module. The module instance is used to resolve references to other
definitions during execution of the function.

A host function is a function expressed outside WebAssembly but passed to a module 
as an import. The definition and behavior of host functions are outside the scope 
of this specification. For the purpose of this specification, it is assumed that 
when invoked, a host function behaves non-deterministically, but within certain 
constraints that ensure the integrity of the runtime.

[https://www.w3.org/TR/wasm-core-2/exec/runtime.html#function-instances]
*)
Inductive funcinst : Type := (* cl *)
  | FC_func_native : function_type -> moduleinst -> module_func -> funcinst
  | FC_func_host (tf: function_type) (hf: host_function) : funcinst
.

(** std-doc:
The store represents all global state that can be manipulated by WebAssembly programs. 
It consists of the runtime representation of all instances of functions, tables, 
memories, and globals, element segments, and data segments that have been allocated 
during the life time of the abstract machine.

It is an invariant of the semantics that no element or data instance is addressed from 
anywhere else but the owning module instances.

[https://www.w3.org/TR/wasm-core-2/exec/runtime.html#store]
*)
Record store_record : Type := (* s *) {
  s_funcs : list funcinst;
  s_tables : list tableinst;
  s_mems : list meminst;
  s_globals : list globalinst;
  s_elems: list eleminst;
  s_datas: list datainst;
}.

                            
(** std-doc:

[https://www.w3.org/TR/wasm-core-2/exec/runtime.html#activations-and-frames]
*)
Record frame : Type := (* f *) {
  f_locs: list value;
  f_inst: moduleinst
}.

Definition empty_frame := Build_frame nil empty_moduleinst.


(** * Administrative Instructions **)

(** std-doc:
WebAssembly code consists of sequences of instructions. Its computational model is based 
on a stack machine in that instructions manipulate values on an implicit operand stack, 
consuming (popping) argument values and producing or returning (pushing) result values.

In addition to dynamic operands from the stack, some instructions also have static 
immediate arguments, typically indices or type annotations, which are part of the 
instruction itself.

Some instructions are structured in that they bracket nested sequences of instructions.
[https://webassembly.github.io/spec/core/syntax/instructions.html]

In order to express the reduction of traps, calls, and control instructions,
the syntax of instructions is extended to include the following administrative
instructions:
*)
Inductive administrative_instruction : Type := (* e *)
| AI_basic : basic_instruction -> administrative_instruction
| AI_trap
| AI_ref : funcaddr -> administrative_instruction
| AI_ref_extern: externaddr -> administrative_instruction
| AI_invoke : funcaddr -> administrative_instruction
| AI_label : nat -> list administrative_instruction -> list administrative_instruction -> administrative_instruction
| AI_frame : nat -> frame -> list administrative_instruction -> administrative_instruction
.

(** std-doc:
In order to specify the reduction of branches, the following syntax of block 
contexts is defined, indexed by the count k of labels surrounding a hole [_] that 
marks the place where the next step of computation is taking place.

This definition allows to index active labels surrounding a branch or return instruction.

[https://www.w3.org/TR/wasm-core-2/exec/runtime.html#block-contexts]
 *)

Inductive lholed : nat -> Type :=
| LH_base : list value -> list administrative_instruction -> lholed 0
| LH_rec {k: nat}: list value -> nat -> list administrative_instruction -> lholed k -> list administrative_instruction -> lholed (S k)
.

(** std-doc:
A configuration consists of the current store and an executing thread.

A thread is a computation over instructions that operates relative to a current 
frame referring to the module instance in which the computation runs, i.e., where 
the current function originates from.

[https://www.w3.org/TR/wasm-core-2/exec/runtime.html#configurations]
 *)
Definition thread : Type := frame * list administrative_instruction.

Definition config_tuple : Type := store_record * thread.
End Host.
End Memory.

(* Notations for values to basic/admin instructions *)
Notation "$VN v" := (AI_basic (BI_const_num v)) (at level 60).
Notation "$VV v" := (AI_basic (BI_const_vec v)) (at level 60).
