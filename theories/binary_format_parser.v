(** Parser for the binary Wasm format. **)
(* (C) J. Pichon - see LICENSE.txt *)
(* TODO: all the numeric stuff is in dire need of testing *)

From Wasm Require Import datatypes datatypes_properties typing.
From compcert Require Import Integers.
From parseque Require Import Parseque.
Require Import Strings.Byte.
Require Import leb128.
Require Import BinNat.
Require Import PeanoNat.

Notation "p $> b" := (cmap b p) (at level 59, right associativity).

Section Language.

Context
  {Toks : nat -> Type} `{Sized Toks byte}
  {M : Type -> Type} `{RawMonad M} `{RawAlternative M}.

Definition byte_parser A n := Parser Toks byte M A n.
Definition be_parser n := byte_parser basic_instruction n.

Definition exact_byte (b : byte) {n} : byte_parser byte n :=
  guardM
    (fun b' =>
      if byte_eqb b' b then Some b'
      else None)
    anyTok.

(* TODO: need to make sure these do the right thing *)

Definition parse_u32_as_N {n} : byte_parser N n :=
  extract parse_unsigned n.

Definition parse_u32_as_int32 {n} : byte_parser Wasm_int.Int32.int n :=
  (* TODO: limit size *)
  (fun x => Wasm_int.Int32.repr (BinIntDef.Z.of_N x)) <$> (extract parse_unsigned n).

Definition parse_u32_zero_as_int32 {n} : byte_parser Wasm_int.Int32.int n :=
  (* TODO: limit size *)
  exact_byte x00 $> Wasm_int.Int32.zero.

Definition parse_s32 {n} : byte_parser Wasm_int.Int32.int n :=
  (* TODO: limit size *)
  (fun x => Wasm_int.Int32.repr x) <$> (extract parse_signed n).

Definition parse_s64 {n} : byte_parser Wasm_int.Int64.int n :=
  (* TODO: limit size *)
  (fun x => Wasm_int.Int64.repr x) <$> (extract parse_signed n).

Fixpoint k_plus_one_anyTok (k : nat) {n} : byte_parser (list byte) n :=
  match k with
  | 0 => (fun x => cons x nil) <$> anyTok
  | S k' => ((fun x xs => cons x xs) <$> anyTok) <*> k_plus_one_anyTok k'
  end.

Definition parse_f32 {n} : byte_parser Wasm_float.FloatSize32.T n :=
  (fun bs => Floats.Float32.of_bits (Integers.Int.repr (common.Memdata.decode_int (List.map compcert_byte_of_byte bs)))) <$> (k_plus_one_anyTok 3).

Definition parse_f64 {n} : byte_parser Wasm_float.FloatSize64.T n :=
(fun bs => Floats.Float.of_bits (Integers.Int64.repr (common.Memdata.decode_int (List.map compcert_byte_of_byte bs)))) <$> (k_plus_one_anyTok 7).

Definition parse_u32_as_nat {n} : byte_parser nat n :=
  (fun x => (N.to_nat x)) <$> parse_u32_as_N.

Definition parse_vec_length {n} : byte_parser nat n :=
  (fun x => (Wasm_int.nat_of_uint i32m x)) <$> parse_u32_as_int32.

Fixpoint parse_vec_aux {B} {n} (f : byte_parser B n) (k : nat)
  : byte_parser (list B) n :=
  match k with
  | 0 => (fun x => cons x nil) <$> f (* TODO: this is wrong in general, but OK with `vec`?!? *)
  | S 0 => (fun x => cons x nil) <$> f
  | S k' => (cons <$> f) <*> parse_vec_aux f k'
  end.

Definition parse_vec {B} {n} (f : byte_parser B n) : byte_parser (list B) n :=
  (* TODO: this is vomit-inducingly bad, but I have no clue how to avoid this :-( *)
  (parse_u32_zero_as_int32 $> nil) <|>
  (parse_vec_length >>= (fun k => parse_vec_aux f k)).

Definition parse_labelidx {n} : byte_parser labelidx n :=
  (fun x => Mk_labelidx (Wasm_int.nat_of_uint i32m x)) <$> parse_u32_as_int32.

Definition parse_funcidx {n} : byte_parser funcidx n :=
  (fun x => Mk_funcidx (Wasm_int.nat_of_uint i32m x)) <$> parse_u32_as_int32.

Definition parse_tableidx {n} : byte_parser tableidx n :=
  (fun x => Mk_tableidx (Wasm_int.nat_of_uint i32m x)) <$> parse_u32_as_int32.

Definition parse_memidx {n} : byte_parser memidx n :=
  (fun x => Mk_memidx (Wasm_int.nat_of_uint i32m x)) <$> parse_u32_as_int32.

Definition parse_typeidx {n} : byte_parser typeidx n :=
  (fun x => Mk_typeidx (Wasm_int.nat_of_uint i32m x)) <$> parse_u32_as_int32.

Definition parse_localidx {n} : byte_parser localidx n :=
  (fun x => Mk_localidx (Wasm_int.nat_of_uint i32m x)) <$> parse_u32_as_int32.

Definition parse_globalidx {n} : byte_parser globalidx n :=
  (fun x => Mk_globalidx (Wasm_int.nat_of_uint i32m x)) <$> parse_u32_as_int32.

Definition parse_value_type {n} : byte_parser value_type n :=
  (exact_byte x7f $> T_i32) <|>
  (exact_byte x7e $> T_i64) <|>
  (exact_byte x7d $> T_f32) <|>
  (exact_byte x7c $> T_f64).

Definition parse_block_type {n} : byte_parser (list value_type) n :=
  (fun x => cons x nil) <$> parse_value_type.

Definition parse_block_type_as_function_type {n} : byte_parser function_type n :=
  (exact_byte x40 $> Tf nil nil) <|>
  (Tf nil <$> parse_block_type).

Definition parse_unreachable {n} : byte_parser basic_instruction n :=
  exact_byte x00 $> BI_unreachable.

Definition parse_nop {n} : byte_parser basic_instruction n :=
  exact_byte x01 $> BI_nop.

Definition extract_labelidx {B} (f : nat -> B) (x : labelidx) : B :=
  match x with Mk_labelidx n => f n end.

Definition extract_funcidx {B} (f : nat -> B) (x : funcidx) : B :=
  match x with Mk_funcidx n => f n end.

Definition extract_typeidx {B} (f : nat -> B) (x : typeidx) : B :=
  match x with Mk_typeidx n => f n end.

Definition extract_localidx {B} (f : nat -> B) (x : localidx) : B :=
  match x with Mk_localidx n => f n end.

Definition extract_globalidx {B} (f : nat -> B) (x : globalidx) : B :=
  match x with Mk_globalidx n => f n end.

Definition parse_br {n} : byte_parser basic_instruction n :=
  exact_byte x0c &> (extract_labelidx BI_br <$> parse_labelidx).

Definition parse_br_if {n} : byte_parser basic_instruction n :=
  exact_byte x0d &> (extract_labelidx BI_br_if <$> parse_labelidx).

Definition parse_br_table_aux (xs : list labelidx) (x : labelidx) :=
  BI_br_table (List.map (extract_labelidx (fun x => x)) xs) (extract_labelidx (fun x => x) x).

Definition parse_br_table {n} : byte_parser basic_instruction n :=
  exact_byte x0e &>
  ((parse_br_table_aux <$> parse_vec parse_labelidx) <*> parse_labelidx).

Definition parse_return {n} : byte_parser basic_instruction n :=
  exact_byte x0f $> BI_return.

Definition parse_call {n} : byte_parser basic_instruction n :=
  exact_byte x10 &> (extract_funcidx BI_call <$> parse_funcidx).

Definition parse_call_indirect {n} : byte_parser basic_instruction n :=
  exact_byte x11 &> (extract_typeidx BI_call_indirect <$> parse_typeidx <& exact_byte x00).

Definition parse_return_call {n} : byte_parser basic_instruction n :=
  exact_byte x12 &> (extract_funcidx BI_return_call <$> parse_funcidx).

Definition parse_return_call_indirect {n} : byte_parser basic_instruction n :=
  exact_byte x13 &> (extract_typeidx BI_return_call_indirect <$> parse_typeidx <& exact_byte x00).

Definition parse_drop {n} : byte_parser basic_instruction n :=
  exact_byte x1a $> BI_drop.

Definition parse_select {n} : byte_parser basic_instruction n :=
  exact_byte x1b $> BI_select.

Definition parse_parametric_instruction {n} : byte_parser basic_instruction n :=
  parse_drop <|> parse_select.

Definition parse_local_get {n} : byte_parser basic_instruction n :=
  exact_byte x20 &> (extract_localidx BI_get_local <$> parse_localidx).

Definition parse_local_set {n} : byte_parser basic_instruction n :=
  exact_byte x21 &> (extract_localidx BI_set_local <$> parse_localidx).

Definition parse_local_tee {n} : byte_parser basic_instruction n :=
  exact_byte x22 &> (extract_localidx BI_tee_local <$> parse_localidx).

Definition parse_global_get {n} : byte_parser basic_instruction n :=
  exact_byte x23 &> (extract_globalidx BI_get_global <$> parse_globalidx).

Definition parse_global_set {n} : byte_parser basic_instruction n :=
  exact_byte x24 &> (extract_globalidx BI_set_global <$> parse_globalidx).

Definition parse_variable_instruction {n} : byte_parser basic_instruction n :=
  parse_local_get <|>
  parse_local_set <|>
  parse_local_tee <|>
  parse_global_get <|>
  parse_global_set.

Definition parse_alignment_exponent {n} : byte_parser BinNat.N.t n :=
  (fun x => (Wasm_int.N_of_uint i32m x)) <$> parse_u32_as_int32.

Definition parse_static_offset {n} : byte_parser BinNat.N.t n :=
  (fun x => (Wasm_int.N_of_uint i32m x)) <$> parse_u32_as_int32.

Definition parse_memarg {n} : byte_parser (alignment_exponent * static_offset) n :=
  parse_alignment_exponent <&> parse_static_offset.

Definition parse_i32_load {n} : byte_parser basic_instruction n :=
  exact_byte x28 &> (uncurry (BI_load T_i32 None) <$> parse_memarg).

Definition parse_i64_load {n} : byte_parser basic_instruction n :=
  exact_byte x29 &> (uncurry (BI_load T_i64 None) <$> parse_memarg).

Definition parse_f32_load {n} : byte_parser basic_instruction n :=
  exact_byte x2a &> (uncurry (BI_load T_f32 None) <$> parse_memarg).

Definition parse_f64_load {n} : byte_parser basic_instruction n :=
  exact_byte x2b &> (uncurry (BI_load T_f64 None) <$> parse_memarg).

Definition parse_i32_load8_s {n} : byte_parser basic_instruction n :=
  exact_byte x2c &> (uncurry (BI_load T_i32 (Some (Tp_i8, SX_S))) <$> parse_memarg).

Definition parse_i32_load8_u {n} : byte_parser basic_instruction n :=
  exact_byte x2d &> (uncurry (BI_load T_i32 (Some (Tp_i8, SX_U))) <$> parse_memarg).

Definition parse_i32_load16_s {n} : byte_parser basic_instruction n :=
  exact_byte x2e &> (uncurry (BI_load T_i32 (Some (Tp_i16, SX_S))) <$> parse_memarg).

Definition parse_i32_load16_u {n} : byte_parser basic_instruction n :=
  exact_byte x2f &> (uncurry (BI_load T_i32 (Some (Tp_i16, SX_U))) <$> parse_memarg).

Definition parse_i64_load8_s {n} : byte_parser basic_instruction n :=
  exact_byte x30 &> (uncurry (BI_load T_i64 (Some (Tp_i8, SX_S))) <$> parse_memarg).

Definition parse_i64_load8_u {n} : byte_parser basic_instruction n :=
  exact_byte x31 &> (uncurry (BI_load T_i64 (Some (Tp_i8, SX_U))) <$> parse_memarg).

Definition parse_i64_load16_s {n} : byte_parser basic_instruction n :=
  exact_byte x32 &> (uncurry (BI_load T_i64 (Some (Tp_i16, SX_S))) <$> parse_memarg).

Definition parse_i64_load16_u {n} : byte_parser basic_instruction n :=
  exact_byte x33 &> (uncurry (BI_load T_i64 (Some (Tp_i16, SX_U))) <$> parse_memarg).

Definition parse_i64_load32_s {n} : byte_parser basic_instruction n :=
  exact_byte x34 &> (uncurry (BI_load T_i64 (Some (Tp_i32, SX_S))) <$> parse_memarg).

Definition parse_i64_load32_u {n} : byte_parser basic_instruction n :=
  exact_byte x35 &> (uncurry (BI_load T_i64 (Some (Tp_i32, SX_U))) <$> parse_memarg).

Definition parse_i32_store {n} : byte_parser basic_instruction n :=
  exact_byte x36 &> (uncurry (BI_store T_i32 None) <$> parse_memarg).

Definition parse_i64_store {n} : byte_parser basic_instruction n :=
  exact_byte x37 &> (uncurry (BI_store T_i64 None) <$> parse_memarg).

Definition parse_f32_store {n} : byte_parser basic_instruction n :=
  exact_byte x38 &> (uncurry (BI_store T_f32 None) <$> parse_memarg).

Definition parse_f64_store {n} : byte_parser basic_instruction n :=
  exact_byte x39 &> (uncurry (BI_store T_f64 None) <$> parse_memarg).

Definition parse_i32_store8 {n} : byte_parser basic_instruction n :=
  exact_byte x3a &> (uncurry (BI_store T_i32 (Some Tp_i8)) <$> parse_memarg).

Definition parse_i32_store16 {n} : byte_parser basic_instruction n :=
  exact_byte x3b &> (uncurry (BI_store T_i32 (Some Tp_i16)) <$> parse_memarg).

Definition parse_i64_store8 {n} : byte_parser basic_instruction n :=
  exact_byte x3c &> (uncurry (BI_store T_i32 (Some Tp_i8)) <$> parse_memarg).

Definition parse_i64_store16 {n} : byte_parser basic_instruction n :=
  exact_byte x3d &> (uncurry (BI_store T_i32 (Some Tp_i16)) <$> parse_memarg).

Definition parse_i64_store32 {n} : byte_parser basic_instruction n :=
  exact_byte x3e &> (uncurry (BI_store T_i32 (Some Tp_i32)) <$> parse_memarg).

Definition parse_memory_size {n} : byte_parser basic_instruction n :=
  exact_byte x3f &> (exact_byte x00 $> BI_current_memory).

Definition parse_memory_grow {n} : byte_parser basic_instruction n :=
  exact_byte x40 &> (exact_byte x00 $> BI_grow_memory).

Definition parse_memory_instruction {n} : byte_parser basic_instruction n :=
  parse_i32_load <|>
  parse_i64_load <|>
  parse_f32_load <|>
  parse_f64_load <|>
  parse_i32_load8_s <|>
  parse_i32_load8_u <|>
  parse_i32_load16_s <|>
  parse_i32_load16_u <|>
  parse_i64_load8_s <|>
  parse_i64_load8_u <|>
  parse_i64_load16_s <|>
  parse_i64_load16_u <|>
  parse_i64_load32_s <|>
  parse_i64_load32_u <|>
  parse_i32_store <|>
  parse_i64_store <|>
  parse_f32_store <|>
  parse_f64_store <|>
  parse_i32_store8 <|>
  parse_i32_store16 <|>
  parse_i64_store8 <|>
  parse_i64_store16 <|>
  parse_i64_store32 <|>
  parse_memory_size <|>
  parse_memory_grow.

Definition parse_i32_const {n} : be_parser n :=
  exact_byte x41 &> ((fun x => BI_const (VAL_int32 x)) <$> parse_s32).

Definition parse_i64_const {n} : be_parser n :=
  exact_byte x42 &> ((fun x => BI_const (VAL_int64 x)) <$> parse_s64).

Definition parse_f32_const {n} : be_parser n :=
  exact_byte x43 &> ((fun x => BI_const (VAL_float32 x)) <$> parse_f32).

Definition parse_f64_const {n} : be_parser n :=
  exact_byte x44 &> ((fun x => BI_const (VAL_float64 x)) <$> parse_f64).

(* :-( *)
Definition parse_numeric_instruction {n} : be_parser n :=
  parse_i32_const <|>
  parse_i64_const <|>
  parse_f32_const <|>
  parse_f64_const <|>
  exact_byte x45 $> BI_testop T_i32 TO_eqz <|>
  exact_byte x46 $> BI_relop T_i32 (Relop_i ROI_eq) <|>
  exact_byte x47 $> BI_relop T_i32 (Relop_i ROI_ne) <|>
  exact_byte x48 $> BI_relop T_i32 (Relop_i (ROI_lt SX_S)) <|>
  exact_byte x49 $> BI_relop T_i32 (Relop_i (ROI_lt SX_U)) <|>
  exact_byte x4a $> BI_relop T_i32 (Relop_i (ROI_gt SX_S)) <|>
  exact_byte x4b $> BI_relop T_i32 (Relop_i (ROI_gt SX_U)) <|>
  exact_byte x4c $> BI_relop T_i32 (Relop_i (ROI_le SX_S)) <|>
  exact_byte x4d $> BI_relop T_i32 (Relop_i (ROI_le SX_U)) <|>
  exact_byte x4e $> BI_relop T_i32 (Relop_i (ROI_ge SX_S)) <|>
  exact_byte x4f $> BI_relop T_i32 (Relop_i (ROI_ge SX_U)) <|>

  exact_byte x50 $> BI_testop T_i64 TO_eqz <|>
  exact_byte x51 $> BI_relop T_i64 (Relop_i ROI_eq) <|>
  exact_byte x52 $> BI_relop T_i64 (Relop_i ROI_ne) <|>
  exact_byte x53 $> BI_relop T_i64 (Relop_i (ROI_lt SX_S)) <|>
  exact_byte x54 $> BI_relop T_i64 (Relop_i (ROI_lt SX_U)) <|>
  exact_byte x55 $> BI_relop T_i64 (Relop_i (ROI_gt SX_S)) <|>
  exact_byte x56 $> BI_relop T_i64 (Relop_i (ROI_gt SX_U)) <|>
  exact_byte x57 $> BI_relop T_i64 (Relop_i (ROI_le SX_S)) <|>
  exact_byte x58 $> BI_relop T_i64 (Relop_i (ROI_le SX_U)) <|>
  exact_byte x59 $> BI_relop T_i64 (Relop_i (ROI_ge SX_S)) <|>
  exact_byte x5a $> BI_relop T_i64 (Relop_i (ROI_ge SX_U)) <|>

  exact_byte x5b $> BI_relop T_f32 (Relop_f ROF_eq) <|>
  exact_byte x5c $> BI_relop T_f32 (Relop_f ROF_ne) <|>
  exact_byte x5d $> BI_relop T_f32 (Relop_f ROF_lt) <|>
  exact_byte x5e $> BI_relop T_f32 (Relop_f ROF_gt) <|>
  exact_byte x5f $> BI_relop T_f32 (Relop_f ROF_le) <|>
  exact_byte x60 $> BI_relop T_f32 (Relop_f ROF_ge) <|>

  exact_byte x61 $> BI_relop T_f64 (Relop_f ROF_eq) <|>
  exact_byte x62 $> BI_relop T_f64 (Relop_f ROF_ne) <|>
  exact_byte x63 $> BI_relop T_f64 (Relop_f ROF_lt) <|>
  exact_byte x64 $> BI_relop T_f64 (Relop_f ROF_gt) <|>
  exact_byte x65 $> BI_relop T_f64 (Relop_f ROF_le) <|>
  exact_byte x66 $> BI_relop T_f64 (Relop_f ROF_ge) <|>

  exact_byte x67 $> BI_unop T_i32 (Unop_i UOI_clz) <|>
  exact_byte x68 $> BI_unop T_i32 (Unop_i UOI_ctz) <|>
  exact_byte x69 $> BI_unop T_i32 (Unop_i UOI_popcnt) <|>
  exact_byte x6a $> BI_binop T_i32 (Binop_i BOI_add) <|>
  exact_byte x6b $> BI_binop T_i32 (Binop_i BOI_sub) <|>
  exact_byte x6c $> BI_binop T_i32 (Binop_i BOI_mul) <|>
  exact_byte x6d $> BI_binop T_i32 (Binop_i (BOI_div SX_S)) <|>
  exact_byte x6e $> BI_binop T_i32 (Binop_i (BOI_div SX_U)) <|>
  exact_byte x6f $> BI_binop T_i32 (Binop_i (BOI_rem SX_S)) <|>
  exact_byte x70 $> BI_binop T_i32 (Binop_i (BOI_rem SX_U)) <|>
  exact_byte x71 $> BI_binop T_i32 (Binop_i BOI_and) <|>
  exact_byte x72 $> BI_binop T_i32 (Binop_i BOI_or) <|>
  exact_byte x73 $> BI_binop T_i32 (Binop_i BOI_xor) <|>
  exact_byte x74 $> BI_binop T_i32 (Binop_i BOI_shl) <|>
  exact_byte x75 $> BI_binop T_i32 (Binop_i (BOI_shr SX_S)) <|>
  exact_byte x76 $> BI_binop T_i32 (Binop_i (BOI_shr SX_U)) <|>
  exact_byte x77 $> BI_binop T_i32 (Binop_i BOI_rotl) <|>
  exact_byte x78 $> BI_binop T_i32 (Binop_i BOI_rotr) <|>

  exact_byte x79 $> BI_unop T_i64 (Unop_i UOI_clz) <|>
  exact_byte x7a $> BI_unop T_i64 (Unop_i UOI_ctz) <|>
  exact_byte x7b $> BI_unop T_i64 (Unop_i UOI_popcnt) <|>
  exact_byte x7c $> BI_binop T_i64 (Binop_i BOI_add) <|>
  exact_byte x7d $> BI_binop T_i64 (Binop_i BOI_sub) <|>
  exact_byte x7e $> BI_binop T_i64 (Binop_i BOI_mul) <|>
  exact_byte x7f $> BI_binop T_i64 (Binop_i (BOI_div SX_S)) <|>
  exact_byte x80 $> BI_binop T_i64 (Binop_i (BOI_div SX_U)) <|>
  exact_byte x81 $> BI_binop T_i64 (Binop_i (BOI_rem SX_S)) <|>
  exact_byte x82 $> BI_binop T_i64 (Binop_i (BOI_rem SX_U)) <|>
  exact_byte x83 $> BI_binop T_i64 (Binop_i BOI_and) <|>
  exact_byte x84 $> BI_binop T_i64 (Binop_i BOI_or) <|>
  exact_byte x85 $> BI_binop T_i64 (Binop_i BOI_xor) <|>
  exact_byte x86 $> BI_binop T_i64 (Binop_i BOI_shl) <|>
  exact_byte x87 $> BI_binop T_i64 (Binop_i (BOI_shr SX_S)) <|>
  exact_byte x88 $> BI_binop T_i64 (Binop_i (BOI_shr SX_U)) <|>
  exact_byte x89 $> BI_binop T_i64 (Binop_i BOI_rotl) <|>
  exact_byte x8a $> BI_binop T_i64 (Binop_i BOI_rotr) <|>

  exact_byte x8b $> BI_unop T_f32 (Unop_f UOF_abs) <|>
  exact_byte x8c $> BI_unop T_f32 (Unop_f UOF_neg) <|>
  exact_byte x8d $> BI_unop T_f32 (Unop_f UOF_ceil) <|>
  exact_byte x8e $> BI_unop T_f32 (Unop_f UOF_floor) <|>
  exact_byte x8f $> BI_unop T_f32 (Unop_f UOF_trunc) <|>
  exact_byte x90 $> BI_unop T_f32 (Unop_f UOF_nearest) <|>
  exact_byte x91 $> BI_unop T_f32 (Unop_f UOF_sqrt) <|>
  exact_byte x92 $> BI_binop T_f32 (Binop_f BOF_add) <|>
  exact_byte x93 $> BI_binop T_f32 (Binop_f BOF_sub) <|>
  exact_byte x94 $> BI_binop T_f32 (Binop_f BOF_mul) <|>
  exact_byte x95 $> BI_binop T_f32 (Binop_f BOF_div) <|>
  exact_byte x96 $> BI_binop T_f32 (Binop_f BOF_min) <|>
  exact_byte x97 $> BI_binop T_f32 (Binop_f BOF_max) <|>
  exact_byte x98 $> BI_binop T_f32 (Binop_f BOF_copysign) <|>

  exact_byte x99 $> BI_unop T_f64 (Unop_f UOF_abs) <|>
  exact_byte x9a $> BI_unop T_f64 (Unop_f UOF_neg) <|>
  exact_byte x9b $> BI_unop T_f64 (Unop_f UOF_ceil) <|>
  exact_byte x9c $> BI_unop T_f64 (Unop_f UOF_floor) <|>
  exact_byte x9d $> BI_unop T_f64 (Unop_f UOF_trunc) <|>
  exact_byte x9e $> BI_unop T_f64 (Unop_f UOF_nearest) <|>
  exact_byte x9f $> BI_unop T_f64 (Unop_f UOF_sqrt) <|>
  exact_byte xa0 $> BI_binop T_f64 (Binop_f BOF_add) <|>
  exact_byte xa1 $> BI_binop T_f64 (Binop_f BOF_sub) <|>
  exact_byte xa2 $> BI_binop T_f64 (Binop_f BOF_mul) <|>
  exact_byte xa3 $> BI_binop T_f64 (Binop_f BOF_div) <|>
  exact_byte xa4 $> BI_binop T_f64 (Binop_f BOF_min) <|>
  exact_byte xa5 $> BI_binop T_f64 (Binop_f BOF_max) <|>
  exact_byte xa6 $> BI_binop T_f64 (Binop_f BOF_copysign) <|>

  (* TODO: I am really not sure whether this is right :-s *)
  exact_byte xa7 $> BI_cvtop T_i32 CVO_convert T_i64 (Some SX_U) <|>  (* i32.wrap_i64 *) (*XXX SX_U doesn't really make sense here *)
  exact_byte xa8 $> BI_cvtop T_i32 CVO_convert T_f32 (Some SX_S) <|>  (* i32.trunc_f32_s *)
  exact_byte xa9 $> BI_cvtop T_i32 CVO_convert T_f32 (Some SX_U) <|>  (* i32.trunc_f32_u *)
  exact_byte xaa $> BI_cvtop T_i32 CVO_convert T_f64 (Some SX_S) <|>  (* i32.trunc_f64_s *)
  exact_byte xab $> BI_cvtop T_i32 CVO_convert T_f64 (Some SX_U) <|>  (* i32.trunc_f64_u *)
  exact_byte xac $> BI_cvtop T_i64 CVO_convert T_i32 (Some SX_S) <|>  (* i64.extend_i32_s *)
  exact_byte xad $> BI_cvtop T_i64 CVO_convert T_i32 (Some SX_U) <|>  (* i64.extend_i32_u *)
  exact_byte xae $> BI_cvtop T_i64 CVO_convert T_f32 (Some SX_S) <|>  (* i64.trunc_f32_s *)
  exact_byte xaf $> BI_cvtop T_i64 CVO_convert T_f32 (Some SX_U) <|>  (* i64.trunc_f32_u *)
  exact_byte xb0 $> BI_cvtop T_i64 CVO_convert T_f64 (Some SX_S) <|>  (* i64.trunc_f64_s *)
  exact_byte xb1 $> BI_cvtop T_i64 CVO_convert T_f64 (Some SX_U) <|>  (* i64.trunc_f64_u *)
  exact_byte xb2 $> BI_cvtop T_f32 CVO_convert T_i32 (Some SX_S) <|>  (* f32.convert_i32_s *)
  exact_byte xb3 $> BI_cvtop T_f32 CVO_convert T_i32 (Some SX_U) <|>  (* f32.convert_i32_u *)
  exact_byte xb4 $> BI_cvtop T_f32 CVO_convert T_i64 (Some SX_S) <|>  (* f32.convert_i64_s *)
  exact_byte xb5 $> BI_cvtop T_f32 CVO_convert T_i64 (Some SX_U) <|>  (* f32.convert_i64_u *)
  exact_byte xb6 $> BI_cvtop T_f32 CVO_convert T_f64 None <|>         (* f32.demote_f64 *)
  exact_byte xb7 $> BI_cvtop T_f64 CVO_convert T_i32 (Some SX_S) <|>  (* f64.convert_i32_s *)
  exact_byte xb8 $> BI_cvtop T_f64 CVO_convert T_i32 (Some SX_U) <|>  (* f64.convert_i32_u *)
  exact_byte xb9 $> BI_cvtop T_f64 CVO_convert T_i64 (Some SX_S) <|>  (* f64.convert_i64_s *)
  exact_byte xba $> BI_cvtop T_f64 CVO_convert T_i64 (Some SX_U) <|>  (* f64.convert_i64_u *)
  exact_byte xbb $> BI_cvtop T_f64 CVO_convert T_f32 None <|>         (* f64.promote_f32 *)
  exact_byte xbc $> BI_cvtop T_i32 CVO_reinterpret T_f32 None <|>     (* i32.reinterpret_f32 *)
  exact_byte xbd $> BI_cvtop T_i64 CVO_reinterpret T_f64 None <|>     (* i64.reinterpret_f64 *)
  exact_byte xbe $> BI_cvtop T_f32 CVO_reinterpret T_i32 None <|>     (* f32.reinterpret_i32 *)
  exact_byte xbf $> BI_cvtop T_f64 CVO_reinterpret T_i64 None.        (* f64.reinterpret_i64 *)

Record Language (n : nat) : Type := MkLanguage {
  _be : byte_parser basic_instruction n;
  _bes_end_with_x0b : byte_parser (list basic_instruction) n;
  _bes_end_with_x05 : byte_parser (list basic_instruction) n;
  _bes_end_with_x0b_or_x05_ctd : byte_parser (list basic_instruction * list basic_instruction) n;
}.

Arguments MkLanguage {_}.

Context
  {Tok : Type} {A B : Type} {n : nat}.

Definition language : [ Language ] := Fix Language (fun k rec =>
  let be_aux := Induction.map _be _ rec in
  let bes_end_with_x0b_aux := Induction.map _bes_end_with_x0b _ rec in
  let bes_end_with_x05_aux := Induction.map _bes_end_with_x05 _ rec in
  let bes_end_with_x0b_or_x05_ctd_aux := Induction.map _bes_end_with_x0b_or_x05_ctd _ rec in
  let parse_block :=
    exact_byte x02 &> ((BI_block <$> parse_block_type_as_function_type) <*> bes_end_with_x0b_aux) in
  let parse_loop :=
    exact_byte x03 &> ((BI_loop <$> parse_block_type_as_function_type) <*> bes_end_with_x0b_aux) in
  let parse_if_body :=
    (((fun x y => (x, y)) <$> parse_block_type_as_function_type) <*> bes_end_with_x0b_or_x05_ctd_aux) in
  let parse_if :=
    (fun '(x, (y, z)) => BI_if x y z) <$> (exact_byte x04 &> parse_if_body) in
  let parse_be :=
    parse_unreachable <|>
    parse_nop <|>
    parse_block <|>
    parse_loop <|>
    parse_if <|>
    parse_br <|>
    parse_br_if <|>
    parse_br_table <|>
    parse_return <|>
    parse_call <|>
    parse_call_indirect <|>
    parse_return_call <|>
    parse_return_call_indirect <|>
    parse_parametric_instruction <|>
    parse_variable_instruction <|>
    parse_memory_instruction <|>
    parse_numeric_instruction in
  let parse_bes_end_with_x0b :=
    (exact_byte x0b $> nil) <|>
    ((cons <$> parse_be) <*> bes_end_with_x0b_aux) in
  let parse_bes_end_with_x05 :=
    (exact_byte x05 $> nil) <|>
    ((cons <$> parse_be) <*> bes_end_with_x05_aux) in
  let parse_bes_end_with_x0b_or_x05_ctd :=
    ((nil, nil) <$ exact_byte x0b) <|>
    (((fun x => (nil, x)) <$ exact_byte x05) <*> parse_bes_end_with_x0b) <|>
    (((fun x '(y, z) => (cons x y, z)) <$> parse_be) <*> bes_end_with_x0b_or_x05_ctd_aux) in
  MkLanguage parse_be parse_bes_end_with_x0b parse_bes_end_with_x05 parse_bes_end_with_x0b_or_x05_ctd).

Definition parse_be : [ byte_parser basic_instruction ] := fun n => _be n (language n).
Definition parse_bes_end_with_x0b : [ byte_parser (list basic_instruction) ] := fun n => _bes_end_with_x0b n (language n).

Definition parse_expr {n} : byte_parser (list basic_instruction) n :=
  (* TODO: is that right? *)
  parse_bes_end_with_x0b n.

Definition parse_function_type {n} : byte_parser function_type n :=
  exact_byte x60 &> (uncurry Tf <$> parse_vec parse_value_type <&> parse_vec parse_value_type).

Definition parse_limits {n} : byte_parser limits n :=
  exact_byte x00 &> ((fun min => {| lim_min := min; lim_max := None |}) <$> parse_u32_as_N) <|>
  exact_byte x01 &> ((fun min max => {| lim_min := min; lim_max := Some max |}) <$> parse_u32_as_N) <*> parse_u32_as_N.

Definition parse_elem_type {n} : byte_parser elem_type n :=
  exact_byte x70 $> ELT_funcref.

Definition parse_table_type {n} : byte_parser table_type n :=
  ((fun ety lims => {| tt_limits := lims; tt_elem_type := ety |}) <$> parse_elem_type) <*> parse_limits.

Definition parse_memory_type {n} : byte_parser memory_type n :=
  (fun lim => lim) <$> parse_limits.

Definition parse_mut {n} : byte_parser mutability n :=
  exact_byte x00 $> MUT_immut <|>
  exact_byte x01 $> MUT_mut.

Definition parse_global_type {n} : byte_parser global_type n :=
  ((fun x y => Build_global_type y x) <$> parse_value_type) <*> parse_mut.

Definition parse_import_desc {n} : byte_parser import_desc n :=
  exact_byte x00 &> (extract_typeidx ID_func <$> parse_typeidx) <|>
  exact_byte x01 &> (ID_table <$> parse_table_type) <|>
  exact_byte x02 &> (ID_mem <$> parse_memory_type) <|>
  exact_byte x03 &> (ID_global <$> parse_global_type).

Definition parse_module_import {n} : byte_parser module_import n :=
  ((fun modul name desc => {| imp_module := modul; imp_name := name; imp_desc := desc; |}) <$> parse_vec anyTok) <*>
  parse_vec anyTok <*> parse_import_desc.

Definition parse_module_glob {n} : byte_parser module_glob n :=
  ((fun ty e => {| modglob_type := ty; modglob_init := e |}) <$> parse_global_type) <*> parse_expr.

Definition parse_module_export_desc {n} : byte_parser module_export_desc n :=
  (exact_byte x00 &> (MED_func <$> parse_funcidx)) <|>
  (exact_byte x01 &> (MED_table <$> parse_tableidx)) <|>
  (exact_byte x02 &> (MED_mem <$> parse_memidx)) <|>
  (exact_byte x03 &> (MED_global <$> parse_globalidx)).

Definition parse_module_export {n} : byte_parser module_export n :=
  ((fun name desc => {| modexp_name := name; modexp_desc := desc |}) <$>
  parse_vec anyTok) <*> parse_module_export_desc.

Definition parse_module_start {n} : byte_parser module_start n :=
  (fun func => {| modstart_func := func |}) <$> parse_funcidx.

Definition parse_module_element {n} : byte_parser module_element n :=
  ((fun table offset init => {| modelem_table := table; modelem_offset := offset; modelem_init := init |}) <$>
  parse_tableidx) <*> parse_expr <*> parse_vec parse_funcidx.

Definition parse_nat_value_type {n} : byte_parser (list value_type) n :=
  ((fun k t => List.repeat t k) <$> parse_u32_as_nat) <*> parse_value_type.

Definition parse_locals {n} : byte_parser (list value_type) n :=
  (fun tss => tss) <$> parse_nat_value_type.

Definition parse_func {n} : byte_parser code_func n :=
  ((fun locals e => {| fc_locals := List.concat locals; fc_expr := e |}) <$> parse_vec parse_locals) <*> parse_expr.

Definition parse_code {n} : byte_parser code_func n :=
  guardM
    (fun sf =>
      match sf with
      (* TODO: we are supposed to check that the size matches *)
      | (s, f) => (* if Nat.eqb s (func_size f) then *) Some f (* else None *)
      end)
    (parse_u32_as_nat <&> parse_func).

Definition parse_module_table {n} : byte_parser module_table n :=
  (fun tty => {| modtab_type := tty |}) <$> parse_table_type.

Definition parse_module_data {n} : byte_parser module_data n :=
  ((fun data offset init => {| moddata_data := data; moddata_offset := offset; moddata_init := init |}) <$>
  parse_memidx) <*> parse_expr <*> parse_vec anyTok.

Definition parse_customsec {n} : byte_parser (list byte) n :=
  exact_byte x00 &> parse_vec anyTok.

Definition parse_typesec {n} : byte_parser (list function_type) n :=
  exact_byte x01 &> parse_u32_as_int32 &> parse_vec parse_function_type.

Definition parse_importsec {n} : byte_parser (list module_import) n :=
  exact_byte x02 &> parse_u32_as_int32 &> parse_vec parse_module_import.

Definition parse_funcsec {n} : byte_parser (list typeidx) n :=
  exact_byte x03 &> parse_u32_as_int32 &> parse_vec parse_typeidx.

Definition parse_tablesec {n} : byte_parser (list module_table) n :=
  exact_byte x04 &> parse_u32_as_int32 &> parse_vec parse_module_table.

Definition parse_memsec {n} : byte_parser (list memory_type) n :=
  exact_byte x05 &> parse_u32_as_int32 &> parse_vec parse_memory_type.

Definition parse_globalsec {n} : byte_parser (list module_glob) n :=
  exact_byte x06 &> parse_u32_as_int32 &> parse_vec parse_module_glob.

Definition parse_exportsec {n} : byte_parser (list module_export) n :=
  exact_byte x07 &> parse_u32_as_int32 &> parse_vec parse_module_export.

Definition parse_startsec {n} : byte_parser module_start n :=
  exact_byte x08 &> parse_u32_as_int32 &> parse_module_start.

Definition parse_elemsec {n} : byte_parser (list module_element) n :=
  exact_byte x09 &> parse_u32_as_int32 &> parse_vec parse_module_element.

Definition parse_codesec {n} : byte_parser (list code_func) n :=
  exact_byte x0a &> parse_u32_as_int32 &> parse_vec parse_code.

Definition parse_datasec {n} : byte_parser (list module_data) n :=
  exact_byte x0b &> parse_u32_as_int32 &> parse_vec parse_module_data.

Definition parse_magic {n} : byte_parser unit n :=
  (exact_byte x00 &> exact_byte x61 &> exact_byte x73 &> exact_byte x6d) $> tt.

Definition parse_version {n} : byte_parser unit n :=
  (exact_byte x01 &> exact_byte x00 &> exact_byte x00 &> exact_byte x00) $> tt.

Definition parse_customsec_forget {A n} : byte_parser (A -> A) n :=
  (fun _ x => x) <$> parse_customsec.

Definition parse_with_customsec_star_before {A : Type} {n} f :=
  @iterater _ _ _ _ _ _ _ _ _ A n parse_customsec_forget f.

(*
Definition parse_with_customsec_star_after {A : Type} {n} f :=
  @iteratel _ _ _ _ _ _ _ _ _ A n f parse_customsec_forget.
*)

Record parsing_module : Type := {
  pmod_types : list function_type;
  pmod_funcs : list typeidx;
  pmod_tables : list module_table;
  pmod_mems : list memory_type;
  pmod_globals : list module_glob;
  pmod_elem : list module_element;
  pmod_data : list module_data;
  pmod_start : option module_start;
  pmod_imports : list module_import;
  pmod_exports : list module_export;
  pmod_code : list code_func;
}.

Definition merge_parsing_modules (m1 m2 : parsing_module) : parsing_module := {|
  pmod_types := List.app m1.(pmod_types) m2.(pmod_types);
  pmod_funcs := List.app m1.(pmod_funcs) m2.(pmod_funcs);
  pmod_tables := List.app m1.(pmod_tables) m2.(pmod_tables);
  pmod_mems := List.app m1.(pmod_mems) m2.(pmod_mems);
  pmod_globals := List.app m1.(pmod_globals) m2.(pmod_globals);
  pmod_elem := List.app m1.(pmod_elem) m2.(pmod_elem);
  pmod_data := List.app m1.(pmod_data) m2.(pmod_data);
  pmod_start :=
    match (m1.(pmod_start), m2.(pmod_start)) with
    | (None, Some st) => Some st
    | (Some st, _) => Some st (* we break the tie *)
    | (None, None) => None
    end;
  pmod_imports := List.app m1.(pmod_imports) m2.(pmod_imports);
  pmod_exports := List.app m1.(pmod_exports) m2.(pmod_exports);
  pmod_code := List.app m1.(pmod_code) m2.(pmod_code);
|}.

Definition parse_typesec_wrapper {n} : byte_parser parsing_module n :=
  (fun types => {|
    pmod_types := types;
    pmod_funcs := nil;
    pmod_tables := nil;
    pmod_mems := nil;
    pmod_globals := nil;
    pmod_elem := nil;
    pmod_data := nil;
    pmod_start := None;
    pmod_imports := nil;
    pmod_exports := nil;
    pmod_code := nil;
  |}) <$>
  (parse_with_customsec_star_before parse_typesec).

Definition parse_importsec_wrapper {n} : byte_parser parsing_module n :=
  (fun imports => {|
    pmod_types := nil;
    pmod_funcs := nil;
    pmod_tables := nil;
    pmod_mems := nil;
    pmod_globals := nil;
    pmod_elem := nil;
    pmod_data := nil;
    pmod_start := None;
    pmod_imports := imports;
    pmod_exports := nil;
    pmod_code := nil;
  |}) <$>
  (parse_with_customsec_star_before parse_importsec).

Definition parse_funcsec_wrapper {n} : byte_parser parsing_module n :=
  (fun funcs => {|
    pmod_types := nil;
    pmod_funcs := funcs;
    pmod_tables := nil;
    pmod_mems := nil;
    pmod_globals := nil;
    pmod_elem := nil;
    pmod_data := nil;
    pmod_start := None;
    pmod_imports := nil;
    pmod_exports := nil;
    pmod_code := nil;
  |}) <$>
  (parse_with_customsec_star_before parse_funcsec).

Definition parse_tablesec_wrapper {n} : byte_parser parsing_module n :=
  (fun tables => {|
    pmod_types := nil;
    pmod_funcs := nil;
    pmod_tables := tables;
    pmod_mems := nil;
    pmod_globals := nil;
    pmod_elem := nil;
    pmod_data := nil;
    pmod_start := None;
    pmod_imports := nil;
    pmod_exports := nil;
    pmod_code := nil;
  |}) <$>
  (parse_with_customsec_star_before parse_tablesec).

Definition parse_memsec_wrapper {n} : byte_parser parsing_module n :=
  (fun mems => {|
    pmod_types := nil;
    pmod_funcs := nil;
    pmod_tables := nil;
    pmod_mems := mems;
    pmod_globals := nil;
    pmod_elem := nil;
    pmod_data := nil;
    pmod_start := None;
    pmod_imports := nil;
    pmod_exports := nil;
    pmod_code := nil;
  |}) <$>
  (parse_with_customsec_star_before parse_memsec).

Definition parse_globalsec_wrapper {n} : byte_parser parsing_module n :=
  (fun globals => {|
    pmod_types := nil;
    pmod_funcs := nil;
    pmod_tables := nil;
    pmod_mems := nil;
    pmod_globals := globals;
    pmod_elem := nil;
    pmod_data := nil;
    pmod_start := None;
    pmod_imports := nil;
    pmod_exports := nil;
    pmod_code := nil;
  |}) <$>
  (parse_with_customsec_star_before parse_globalsec).

Definition parse_exportsec_wrapper {n} : byte_parser parsing_module n :=
  (fun exports => {|
    pmod_types := nil;
    pmod_funcs := nil;
    pmod_tables := nil;
    pmod_mems := nil;
    pmod_globals := nil;
    pmod_elem := nil;
    pmod_data := nil;
    pmod_start := None;
    pmod_imports := nil;
    pmod_exports := exports;
    pmod_code := nil;
  |}) <$>
  (parse_with_customsec_star_before parse_exportsec).

Definition parse_startsec_wrapper {n} : byte_parser parsing_module n :=
  (fun start => {|
    pmod_types := nil;
    pmod_funcs := nil;
    pmod_tables := nil;
    pmod_mems := nil;
    pmod_globals := nil;
    pmod_elem := nil;
    pmod_data := nil;
    pmod_start := Some start;
    pmod_imports := nil;
    pmod_exports := nil;
    pmod_code := nil;
  |}) <$>
  (parse_with_customsec_star_before parse_startsec).

Definition parse_elemsec_wrapper {n} : byte_parser parsing_module n :=
  (fun elem => {|
    pmod_types := nil;
    pmod_funcs := nil;
    pmod_tables := nil;
    pmod_mems := nil;
    pmod_globals := nil;
    pmod_elem := elem;
    pmod_data := nil;
    pmod_start := None;
    pmod_imports := nil;
    pmod_exports := nil;
    pmod_code := nil;
  |}) <$>
  (parse_with_customsec_star_before parse_elemsec).

Definition parse_codesec_wrapper {n} : byte_parser parsing_module n :=
  (fun code => {|
    pmod_types := nil;
    pmod_funcs := nil;
    pmod_tables := nil;
    pmod_mems := nil;
    pmod_globals := nil;
    pmod_elem := nil;
    pmod_data := nil;
    pmod_start := None;
    pmod_imports := nil;
    pmod_exports := nil;
    pmod_code := code;
  |}) <$>
  (parse_with_customsec_star_before parse_codesec).

Definition parse_datasec_wrapper {n} : byte_parser parsing_module n :=
  (fun data => {|
    pmod_types := nil;
    pmod_funcs := nil;
    pmod_tables := nil;
    pmod_mems := nil;
    pmod_globals := nil;
    pmod_elem := nil;
    pmod_data := data;
    pmod_start := None;
    pmod_imports := nil;
    pmod_exports := nil;
    pmod_code := nil;
  |}) <$>
  (parse_with_customsec_star_before parse_datasec).

(** this is not in the spec, it is here to force productivity;
    we make it be different from all section markers *)
Definition end_marker : byte := x0c.

Definition parse_module_end {n} : byte_parser parsing_module n :=
  (fun _ => {|
    pmod_types := nil;
    pmod_funcs := nil;
    pmod_tables := nil;
    pmod_mems := nil;
    pmod_globals := nil;
    pmod_elem := nil;
    pmod_data := nil;
    pmod_start := None;
    pmod_imports := nil;
    pmod_exports := nil;
    pmod_code := nil;
  |}) <$>
  (parse_with_customsec_star_before (exact_byte end_marker)).

Definition parse_datasec_onwards {n} : byte_parser parsing_module n :=
  ((merge_parsing_modules <$> parse_datasec_wrapper) <*> parse_module_end) <|>
  parse_module_end.

Definition parse_codesec_onwards {n} : byte_parser parsing_module n :=
  ((merge_parsing_modules <$> parse_codesec_wrapper) <*> parse_datasec_onwards) <|>
  parse_datasec_onwards.

Definition parse_elemsec_onwards {n} : byte_parser parsing_module n :=
  ((merge_parsing_modules <$> parse_elemsec_wrapper) <*> parse_codesec_onwards) <|>
  parse_codesec_onwards.

Definition parse_startsec_onwards {n} : byte_parser parsing_module n :=
  ((merge_parsing_modules <$> parse_startsec_wrapper) <*> parse_elemsec_onwards) <|>
  parse_elemsec_onwards.

Definition parse_exportsec_onwards {n} : byte_parser parsing_module n :=
  ((merge_parsing_modules <$> parse_exportsec_wrapper) <*> parse_startsec_onwards) <|>
  parse_startsec_onwards.

Definition parse_globalsec_onwards {n} : byte_parser parsing_module n :=
  ((merge_parsing_modules <$> parse_globalsec_wrapper) <*> parse_exportsec_onwards) <|>
  parse_exportsec_onwards.

Definition parse_memsec_onwards {n} : byte_parser parsing_module n :=
  ((merge_parsing_modules <$> parse_memsec_wrapper) <*> parse_globalsec_onwards) <|>
  parse_globalsec_onwards.

Definition parse_tablesec_onwards {n} : byte_parser parsing_module n :=
  ((merge_parsing_modules <$> parse_tablesec_wrapper) <*> parse_memsec_onwards) <|>
  parse_memsec_onwards.

Definition parse_funcsec_onwards {n} : byte_parser parsing_module n :=
  ((merge_parsing_modules <$> parse_funcsec_wrapper) <*> parse_tablesec_onwards) <|>
  parse_tablesec_onwards.

Definition parse_importsec_onwards {n} : byte_parser parsing_module n :=
  ((merge_parsing_modules <$> parse_importsec_wrapper) <*> parse_funcsec_onwards) <|>
  parse_funcsec_onwards.

Definition parse_typesec_onwards {n} : byte_parser parsing_module n :=
  ((merge_parsing_modules <$> parse_typesec_wrapper) <*> parse_importsec_onwards) <|>
  parse_importsec_onwards.

Definition module_of_parsing_module (m : parsing_module) : module := {|
  mod_types := m.(pmod_types);
  mod_funcs :=
    (* TODO: what if these lists are of different length? *)
    List.map
      (fun '(a, b) =>
        {| modfunc_type := a; modfunc_locals := b.(fc_locals); modfunc_body := b.(fc_expr) |})
      (List.combine m.(pmod_funcs) m.(pmod_code));
  mod_tables := m.(pmod_tables);
  mod_mems := m.(pmod_mems);
  mod_globals := m.(pmod_globals);
  mod_elem := m.(pmod_elem);
  mod_data := m.(pmod_data);
  mod_start := m.(pmod_start);
  mod_imports := m.(pmod_imports);
  mod_exports := m.(pmod_exports);
|}.

Definition parse_module {n} : byte_parser module n :=
  module_of_parsing_module <$>
  (parse_magic &>
  parse_version &>
  parse_typesec_onwards).

End Language.


Inductive Singleton (A : Type) : A -> Type :=
  MkSingleton : forall a, Singleton A a.

Arguments Singleton {_}.
Arguments MkSingleton {_}.

Class Tokenizer (A : Type) : Type :=
  MkTokenizer { _tokenize : list byte -> list A }.

Definition tokenize {A : Type} `{Tokenizer A} : list byte -> list A := _tokenize.

Arguments MkTokenizer {_}.

Definition fromText {A : Type} `{Tokenizer A} (s : list byte) : list A :=
  tokenize s.

#[export]
Instance tokBytes : Tokenizer byte := MkTokenizer (fun x => x).

Section Run.

Context
  {M : Type -> Type} `{RawMonad M} `{RawAlternative M} `{RawMonadRun M}
  {Tok : Type} `{Tokenizer Tok}
  {A : Type}.

Definition run : list byte -> [ Parser (SizedList Tok) Tok M A ] -> option A := fun s p =>
  let tokens := (fromText s : list Tok) in
  let n      := List.length tokens in
  let input  := mkSizedList tokens in
  let result := runParser (p n) (Nat.le_refl n) input in
  let valid  := fun s => match Success.size s with | O => Some (Success.value s) | _ => None end in
  match mapM valid (runMonad result) with
    | Some (cons hd _) => Some hd
    | _                => None
  end.

End Run.

Definition run_parse_be (bs : list byte) : option basic_instruction :=
  run bs parse_be.

Definition run_parse_expr (bs : list byte) : option (list basic_instruction) :=
  run bs (fun n => parse_expr).

Definition run_parse_bes (bs : list byte) : option (list basic_instruction) :=
  run_parse_expr (bs ++ (x0b :: nil)).

Definition run_parse_module (bs : list byte) : option module :=
  run (bs ++ cons end_marker nil) (fun n => parse_module).
