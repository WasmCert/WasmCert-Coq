(** Parser for the binary Wasm format. **)
(* TODO: make this use byte. *)
(* TODO: write a relational spec, and prove they correspond *)

From Wasm Require Import datatypes datatypes_properties.
From compcert Require Import Integers.
From parseque Require Import Parseque.
Require Import Ascii Byte.
Require Import leb128.
Require Import Coq.Arith.Le.

Notation "p $> b" := (cmap b p) (at level 59, right associativity).

Section Language.

Context
  {Toks : nat -> Type} `{Sized Toks byte}
  {M : Type -> Type} `{RawMonad M} `{RawAlternative M}.

Definition byte_parser A n := Parser Toks byte M A n.
Definition be_parser n := byte_parser basic_instruction n.

Definition exact_byte (b : byte) {n}: byte_parser byte n :=
  (* TODO: this is a horrible hack to avoid the fact that `Scheme Equality for byte`
     does not terminate in a reasonable amount of time. *)
  guardM
    (fun b' =>
      if Ascii.eqb (ascii_of_byte b') (ascii_of_byte b) then Some b'
      else None)
    anyTok.

Definition parse_u32 {n} : byte_parser Wasm_int.Int32.int n :=
  (* TODO: limit size *)
  (fun x => Wasm_int.Int32.repr (BinIntDef.Z.of_N x)) <$> (extract parse_unsigned n).

Definition parse_u32_zero {n} : byte_parser Wasm_int.Int32.int n :=
  (* TODO: limit size *)
  exact_byte x00 $> Wasm_int.Int32.zero.

Definition parse_s32 {n} : byte_parser Wasm_int.Int32.int n :=
  (* TODO: limit size *)
  (fun x => Wasm_int.Int32.repr x) <$> (extract parse_signed n).

Definition parse_s64 {n} : byte_parser Wasm_int.Int64.int n :=
  (* TODO: limit size *)
  (fun x => Wasm_int.Int64.repr x) <$> (extract parse_signed n).

Definition parse_f32 {n} : byte_parser Wasm_float.FloatSize32.T n :=
  (* TODO: use  Flocq.IEEE754.Bits.b32_of_bits *)
  (* TODO: steal IEEE 754-2019 (Section 3.4) bit pattern in little endian from Flocq? *)
  exact_byte x00 $> Wasm_float.Float32.pos_zero.

Definition parse_f64 {n} : byte_parser Wasm_float.FloatSize64.T n :=
  (* TODO: steal IEEE 754-2019 (Section 3.4) bit pattern in little endian from Flocq? *)
  exact_byte x00 $> Wasm_float.Float64.pos_zero.

Definition parse_u32_nat {n} : byte_parser nat n :=
  (fun x => (Wasm_int.nat_of_uint i32m x)) <$> parse_u32.

Definition parse_vec_length {n} : byte_parser nat n :=
  (fun x => (Wasm_int.nat_of_uint i32m x)) <$> parse_u32.

Fixpoint parse_vec_aux {B} {n} (f : byte_parser B n) (k : nat)
  : byte_parser (list B) n :=
  match k with
  | 0 => (fun x => cons x nil) <$> f (* TODO: this is wrong in general, but OK with `vec`?!? *)
  | S 0 => (fun x => cons x nil) <$> f
  | S k' => (cons <$> f) <*> parse_vec_aux f k'
  end.

Definition parse_vec {B} {n} (f : byte_parser B n) : byte_parser (list B) n :=
  (* TODO: this is vomit-inducingly bad, but I have no clue how to avoid this :-( *)
  (parse_u32_zero $> nil) <|>
  (parse_vec_length >>= (fun k => parse_vec_aux f k)).

Definition parse_labelidx {n} : byte_parser labelidx n :=
  (fun x => Mk_labelidx (Wasm_int.nat_of_uint i32m x)) <$> parse_u32.

Definition parse_funcidx {n} : byte_parser funcidx n :=
  (fun x => Mk_funcidx (Wasm_int.nat_of_uint i32m x)) <$> parse_u32.

Definition parse_typeidx {n} : byte_parser typeidx n :=
  (fun x => Mk_typeidx (Wasm_int.nat_of_uint i32m x)) <$> parse_u32.

Definition parse_localidx {n} : byte_parser localidx n :=
  (fun x => Mk_localidx (Wasm_int.nat_of_uint i32m x)) <$> parse_u32.

Definition parse_globalidx {n} : byte_parser globalidx n :=
  (fun x => Mk_globalidx (Wasm_int.nat_of_uint i32m x)) <$> parse_u32.

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
  exact_byte x00 $> Unreachable.

Definition parse_nop {n} : byte_parser basic_instruction n :=
  exact_byte x01 $> Nop.

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
  exact_byte x0c &> (extract_labelidx Br <$> parse_labelidx).

Definition parse_br_if {n} : byte_parser basic_instruction n :=
  exact_byte x0d &> (extract_labelidx Br_if <$> parse_labelidx).

Definition parse_br_table_aux (xs : list labelidx) (x : labelidx) :=
  Br_table (List.map (extract_labelidx (fun x => x)) xs) (extract_labelidx (fun x => x) x).

Definition parse_br_table {n} : byte_parser basic_instruction n :=
  exact_byte x0e &>
  ((parse_br_table_aux <$> parse_vec parse_labelidx) <*> parse_labelidx).

Definition parse_return {n} : byte_parser basic_instruction n :=
  exact_byte x0f $> Return.

Definition parse_call {n} : byte_parser basic_instruction n :=
  exact_byte x10 &> (extract_funcidx Call <$> parse_funcidx).

Definition parse_call_indirect {n} : byte_parser basic_instruction n :=
  exact_byte x11 &> (extract_typeidx Call <$> parse_typeidx <& exact_byte x00).

Definition parse_drop {n} : byte_parser basic_instruction n :=
  exact_byte x1a $> Drop.

Definition parse_select {n} : byte_parser basic_instruction n :=
  exact_byte x1b $> Select.

Definition parse_parametric_instruction {n} : byte_parser basic_instruction n :=
  parse_drop <|> parse_select.

Definition parse_local_get {n} : byte_parser basic_instruction n :=
  exact_byte x20 &> (extract_localidx Get_local <$> parse_localidx).

Definition parse_local_set {n} : byte_parser basic_instruction n :=
  exact_byte x21 &> (extract_localidx Set_local <$> parse_localidx).

Definition parse_local_tee {n} : byte_parser basic_instruction n :=
  exact_byte x22 &> (extract_localidx Tee_local <$> parse_localidx).

Definition parse_global_get {n} : byte_parser basic_instruction n :=
  exact_byte x23 &> (extract_globalidx Get_global <$> parse_globalidx).

Definition parse_global_set {n} : byte_parser basic_instruction n :=
  exact_byte x24 &> (extract_globalidx Set_global <$> parse_globalidx).

Definition parse_variable_instruction {n} : byte_parser basic_instruction n :=
  parse_local_get <|>
  parse_local_set <|>
  parse_local_tee <|>
  parse_global_get <|>
  parse_global_set.

Definition parse_alignment_exponent {n} : byte_parser nat n :=
  (fun x => (Wasm_int.nat_of_uint i32m x)) <$> parse_u32.

Definition parse_static_offset {n} : byte_parser nat n :=
  (fun x => (Wasm_int.nat_of_uint i32m x)) <$> parse_u32.

Definition parse_memarg {n} : byte_parser (alignment_exponent * static_offset) n :=
  parse_alignment_exponent <&> parse_static_offset.

Definition parse_i32_load {n} : byte_parser basic_instruction n :=
  exact_byte x28 &> (prod_curry (Load T_i32 None) <$> parse_memarg).

Definition parse_i64_load {n} : byte_parser basic_instruction n :=
  exact_byte x29 &> (prod_curry (Load T_i64 None) <$> parse_memarg).

Definition parse_f32_load {n} : byte_parser basic_instruction n :=
  exact_byte x2a &> (prod_curry (Load T_f32 None) <$> parse_memarg).

Definition parse_f64_load {n} : byte_parser basic_instruction n :=
  exact_byte x2b &> (prod_curry (Load T_f64 None) <$> parse_memarg).

Definition parse_i32_load8_s {n} : byte_parser basic_instruction n :=
  exact_byte x2c &> (prod_curry (Load T_i32 (Some (Tp_i8, SX_S))) <$> parse_memarg).

Definition parse_i32_load8_u {n} : byte_parser basic_instruction n :=
  exact_byte x2d &> (prod_curry (Load T_i32 (Some (Tp_i8, SX_U))) <$> parse_memarg).

Definition parse_i32_load16_s {n} : byte_parser basic_instruction n :=
  exact_byte x2e &> (prod_curry (Load T_i32 (Some (Tp_i16, SX_S))) <$> parse_memarg).

Definition parse_i32_load16_u {n} : byte_parser basic_instruction n :=
  exact_byte x2f &> (prod_curry (Load T_i32 (Some (Tp_i16, SX_U))) <$> parse_memarg).

Definition parse_i64_load8_s {n} : byte_parser basic_instruction n :=
  exact_byte x30 &> (prod_curry (Load T_i64 (Some (Tp_i8, SX_S))) <$> parse_memarg).

Definition parse_i64_load8_u {n} : byte_parser basic_instruction n :=
  exact_byte x31 &> (prod_curry (Load T_i64 (Some (Tp_i8, SX_U))) <$> parse_memarg).

Definition parse_i64_load16_s {n} : byte_parser basic_instruction n :=
  exact_byte x32 &> (prod_curry (Load T_i64 (Some (Tp_i16, SX_S))) <$> parse_memarg).

Definition parse_i64_load16_u {n} : byte_parser basic_instruction n :=
  exact_byte x33 &> (prod_curry (Load T_i64 (Some (Tp_i16, SX_U))) <$> parse_memarg).

Definition parse_i64_load32_s {n} : byte_parser basic_instruction n :=
  exact_byte x34 &> (prod_curry (Load T_i64 (Some (Tp_i32, SX_S))) <$> parse_memarg).

Definition parse_i64_load32_u {n} : byte_parser basic_instruction n :=
  exact_byte x35 &> (prod_curry (Load T_i64 (Some (Tp_i32, SX_U))) <$> parse_memarg).

Definition parse_i32_store {n} : byte_parser basic_instruction n :=
  exact_byte x36 &> (prod_curry (Store T_i32 None) <$> parse_memarg).

Definition parse_i64_store {n} : byte_parser basic_instruction n :=
  exact_byte x37 &> (prod_curry (Store T_i64 None) <$> parse_memarg).

Definition parse_f32_store {n} : byte_parser basic_instruction n :=
  exact_byte x38 &> (prod_curry (Store T_f32 None) <$> parse_memarg).

Definition parse_f64_store {n} : byte_parser basic_instruction n :=
  exact_byte x39 &> (prod_curry (Store T_f64 None) <$> parse_memarg).

Definition parse_i32_store8 {n} : byte_parser basic_instruction n :=
  exact_byte x3a &> (prod_curry (Store T_i32 (Some Tp_i8)) <$> parse_memarg).

Definition parse_i32_store16 {n} : byte_parser basic_instruction n :=
  exact_byte x3b &> (prod_curry (Store T_i32 (Some Tp_i16)) <$> parse_memarg).

Definition parse_i64_store8 {n} : byte_parser basic_instruction n :=
  exact_byte x3c &> (prod_curry (Store T_i32 (Some Tp_i8)) <$> parse_memarg).

Definition parse_i64_store16 {n} : byte_parser basic_instruction n :=
  exact_byte x3d &> (prod_curry (Store T_i32 (Some Tp_i16)) <$> parse_memarg).

Definition parse_i64_store32 {n} : byte_parser basic_instruction n :=
  exact_byte x3e &> (prod_curry (Store T_i32 (Some Tp_i32)) <$> parse_memarg).

Definition parse_memory_size {n} : byte_parser basic_instruction n :=
  exact_byte x3f &> (exact_byte x00 $> Current_memory).

Definition parse_memory_grow {n} : byte_parser basic_instruction n :=
  exact_byte x40 &> (exact_byte x00 $> Grow_memory).

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
  exact_byte x41 &> ((fun x => EConst (ConstInt32 x)) <$> parse_s32).

Definition parse_i64_const {n} : be_parser n :=
  exact_byte x42 &> ((fun x => EConst (ConstInt64 x)) <$> parse_s64).

Definition parse_f32_const {n} : be_parser n :=
  exact_byte x43 &> ((fun x => EConst (ConstFloat32 x)) <$> parse_f32).

Definition parse_f64_const {n} : be_parser n :=
  exact_byte x44 &> ((fun x => EConst (ConstFloat64 x)) <$> parse_f64).

(* :-( *)
Definition parse_numeric_instruction {n} : be_parser n :=
  parse_i32_const <|>
  parse_i64_const <|>
  parse_f32_const <|>
  parse_f64_const <|>
  exact_byte x45 $> Testop T_i32 Eqz <|>
  exact_byte x46 $> Relop_i T_i32 Eq <|>
  exact_byte x47 $> Relop_i T_i32 Ne <|>
  exact_byte x48 $> Relop_i T_i32 (Lt SX_S) <|>
  exact_byte x49 $> Relop_i T_i32 (Lt SX_U) <|>
  exact_byte x4a $> Relop_i T_i32 (Gt SX_S) <|>
  exact_byte x4b $> Relop_i T_i32 (Gt SX_U) <|>
  exact_byte x4c $> Relop_i T_i32 (Le SX_S) <|>
  exact_byte x4d $> Relop_i T_i32 (Le SX_U) <|>
  exact_byte x4e $> Relop_i T_i32 (Ge SX_S) <|>
  exact_byte x4f $> Relop_i T_i32 (Ge SX_U) <|>

  exact_byte x50 $> Testop T_i64 Eqz <|>
  exact_byte x51 $> Relop_i T_i64 Eq <|>
  exact_byte x52 $> Relop_i T_i64 Ne <|>
  exact_byte x53 $> Relop_i T_i64 (Lt SX_S) <|>
  exact_byte x54 $> Relop_i T_i64 (Lt SX_U) <|>
  exact_byte x55 $> Relop_i T_i64 (Gt SX_S) <|>
  exact_byte x56 $> Relop_i T_i64 (Gt SX_U) <|>
  exact_byte x57 $> Relop_i T_i64 (Le SX_S) <|>
  exact_byte x58 $> Relop_i T_i64 (Le SX_U) <|>
  exact_byte x59 $> Relop_i T_i64 (Ge SX_S) <|>
  exact_byte x5a $> Relop_i T_i64 (Ge SX_U) <|>

  exact_byte x5b $> Relop_f T_f32 Eqf <|>
  exact_byte x5c $> Relop_f T_f32 Nef <|>
  exact_byte x5d $> Relop_f T_f32 Ltf <|>
  exact_byte x5e $> Relop_f T_f32 Gtf <|>
  exact_byte x5f $> Relop_f T_f32 Lef <|>
  exact_byte x60 $> Relop_f T_f32 Gef <|>

  exact_byte x61 $> Relop_f T_f64 Eqf <|>
  exact_byte x62 $> Relop_f T_f64 Nef <|>
  exact_byte x63 $> Relop_f T_f64 Ltf <|>
  exact_byte x64 $> Relop_f T_f64 Gtf <|>
  exact_byte x65 $> Relop_f T_f64 Lef <|>
  exact_byte x66 $> Relop_f T_f64 Gef <|>

  exact_byte x67 $> Unop_i T_i32 Clz <|>
  exact_byte x68 $> Unop_i T_i32 Ctz <|>
  exact_byte x69 $> Unop_i T_i32 Popcnt <|>
  exact_byte x6a $> Binop_i T_i32 Add <|>
  exact_byte x6b $> Binop_i T_i32 Sub <|>
  exact_byte x6c $> Binop_i T_i32 Mul <|>
  exact_byte x6d $> Binop_i T_i32 (Div SX_S) <|>
  exact_byte x6e $> Binop_i T_i32 (Div SX_U) <|>
  exact_byte x6f $> Binop_i T_i32 (Rem SX_S) <|>
  exact_byte x70 $> Binop_i T_i32 (Rem SX_U) <|>
  exact_byte x71 $> Binop_i T_i32 And <|>
  exact_byte x72 $> Binop_i T_i32 Or <|>
  exact_byte x73 $> Binop_i T_i32 Xor <|>
  exact_byte x74 $> Binop_i T_i32 Shl <|>
  exact_byte x75 $> Binop_i T_i32 (Shr SX_S) <|>
  exact_byte x76 $> Binop_i T_i32 (Shr SX_U) <|>
  exact_byte x77 $> Binop_i T_i32 Rotl <|>
  exact_byte x78 $> Binop_i T_i32 Rotr <|>

  exact_byte x79 $> Unop_i T_i64 Clz <|>
  exact_byte x7a $> Unop_i T_i64 Ctz <|>
  exact_byte x7b $> Unop_i T_i64 Popcnt <|>
  exact_byte x7c $> Binop_i T_i64 Add <|>
  exact_byte x7d $> Binop_i T_i64 Sub <|>
  exact_byte x7e $> Binop_i T_i64 Mul <|>
  exact_byte x7f $> Binop_i T_i64 (Div SX_S) <|>
  exact_byte x80 $> Binop_i T_i64 (Div SX_U) <|>
  exact_byte x81 $> Binop_i T_i64 (Rem SX_S) <|>
  exact_byte x82 $> Binop_i T_i64 (Rem SX_U) <|>
  exact_byte x83 $> Binop_i T_i64 And <|>
  exact_byte x84 $> Binop_i T_i64 Or <|>
  exact_byte x85 $> Binop_i T_i64 Xor <|>
  exact_byte x86 $> Binop_i T_i64 Shl <|>
  exact_byte x87 $> Binop_i T_i64 (Shr SX_S) <|>
  exact_byte x88 $> Binop_i T_i64 (Shr SX_U) <|>
  exact_byte x89 $> Binop_i T_i64 Rotl <|>
  exact_byte x8a $> Binop_i T_i64 Rotr <|>

  exact_byte x8b $> Unop_f T_f32 Abs <|>
  exact_byte x8c $> Unop_f T_f32 Neg <|>
  exact_byte x8d $> Unop_f T_f32 Ceil <|>
  exact_byte x8e $> Unop_f T_f32 Floor <|>
  exact_byte x8f $> Unop_f T_f32 Trunc <|>
  exact_byte x90 $> Unop_f T_f32 Nearest <|>
  exact_byte x91 $> Unop_f T_f32 Sqrt <|>
  exact_byte x92 $> Binop_f T_f32 Addf <|>
  exact_byte x93 $> Binop_f T_f32 Subf <|>
  exact_byte x94 $> Binop_f T_f32 Mulf <|>
  exact_byte x95 $> Binop_f T_f32 Divf <|>
  exact_byte x96 $> Binop_f T_f32 Min <|>
  exact_byte x97 $> Binop_f T_f32 Max <|>
  exact_byte x98 $> Binop_f T_f32 Copysign <|>

  exact_byte x99 $> Unop_f T_f64 Abs <|>
  exact_byte x9a $> Unop_f T_f64 Neg <|>
  exact_byte x9b $> Unop_f T_f64 Ceil <|>
  exact_byte x9c $> Unop_f T_f64 Floor <|>
  exact_byte x9d $> Unop_f T_f64 Trunc <|>
  exact_byte x9e $> Unop_f T_f64 Nearest <|>
  exact_byte x9f $> Unop_f T_f64 Sqrt <|>
  exact_byte xa0 $> Binop_f T_f64 Addf <|>
  exact_byte xa1 $> Binop_f T_f64 Subf <|>
  exact_byte xa2 $> Binop_f T_f64 Mulf <|>
  exact_byte xa3 $> Binop_f T_f64 Divf <|>
  exact_byte xa4 $> Binop_f T_f64 Min <|>
  exact_byte xa5 $> Binop_f T_f64 Max <|>
  exact_byte xa6 $> Binop_f T_f64 Copysign <|>

  (* TODO: I am really not sure whether this is right :-s *)
  exact_byte xa7 $> Cvtop T_i32 Convert T_i64 (Some SX_U) <|>
  exact_byte xa8 $> Cvtop T_i32 Convert T_f32 (Some SX_S) <|>
  exact_byte xa9 $> Cvtop T_i32 Convert T_f32 (Some SX_U) <|>
  exact_byte xaa $> Cvtop T_i32 Convert T_f64 (Some SX_S) <|>
  exact_byte xab $> Cvtop T_i32 Convert T_f64 (Some SX_U) <|>
  exact_byte xac $> Cvtop T_i64 Convert T_i32 (Some SX_S) <|>
  exact_byte xad $> Cvtop T_i64 Convert T_i32 (Some SX_U) <|>
  exact_byte xae $> Cvtop T_i64 Convert T_f32 (Some SX_S) <|>
  exact_byte xaf $> Cvtop T_i64 Convert T_f32 (Some SX_U) <|>
  exact_byte xb0 $> Cvtop T_i64 Convert T_f64 (Some SX_S) <|>
  exact_byte xb1 $> Cvtop T_i64 Convert T_f64 (Some SX_U) <|>
  exact_byte xb2 $> Cvtop T_f32 Convert T_i32 (Some SX_S) <|>
  exact_byte xb3 $> Cvtop T_f32 Convert T_i32 (Some SX_U) <|>
  exact_byte xb4 $> Cvtop T_f32 Convert T_i64 (Some SX_S) <|>
  exact_byte xb5 $> Cvtop T_f32 Convert T_i64 (Some SX_U) <|>
  exact_byte xb6 $> Cvtop T_f32 Convert T_f64 None <|>
  exact_byte xb7 $> Cvtop T_f64 Convert T_i32 (Some SX_S) <|>
  exact_byte xb8 $> Cvtop T_f64 Convert T_i32 (Some SX_U) <|>
  exact_byte xb9 $> Cvtop T_f64 Convert T_i64 (Some SX_S) <|>
  exact_byte xba $> Cvtop T_f64 Convert T_i64 (Some SX_U) <|>
  exact_byte xbb $> Cvtop T_f32 Convert T_f64 None <|>
  exact_byte xbc $> Cvtop T_i32 Reinterpret T_f32 None <|>
  exact_byte xbd $> Cvtop T_i64 Reinterpret T_f64 None <|>
  exact_byte xbe $> Cvtop T_f32 Reinterpret T_i32 None <|>
  exact_byte xbf $> Cvtop T_f64 Reinterpret T_i64 None.

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
    exact_byte x02 &> ((Block <$> parse_block_type_as_function_type) <*> bes_end_with_x0b_aux) in
  let parse_loop :=
    exact_byte x03 &> ((Loop <$> parse_block_type_as_function_type) <*> bes_end_with_x0b_aux) in
  let parse_if_body :=
    (((fun x y => (x, y)) <$> parse_block_type_as_function_type) <*> bes_end_with_x0b_or_x05_ctd_aux) in
  let parse_if :=
    (fun '(x, (y, z)) => If x y z) <$> (exact_byte x04 &> parse_if_body) in
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
  exact_byte x60 &> (prod_curry Tf <$> parse_vec parse_value_type <&> parse_vec parse_value_type).

Definition parse_limits {n} : byte_parser limits n :=
  exact_byte x00 &> ((fun min => {| lim_min := min; lim_max := None |}) <$> parse_u32_nat) <|>
  exact_byte x01 &> ((fun min max => {| lim_min := min; lim_max := Some max |}) <$> parse_u32_nat) <*> parse_u32_nat.

Definition parse_elem_type {n} : byte_parser elem_type n :=
  exact_byte x70 $> ELT_funcref.

Definition parse_table_type {n} : byte_parser table_type n :=
  ((fun lims ety => {| tt_limits := lims; tt_elem_type := ety |}) <$> parse_limits) <*> parse_elem_type.

Definition parse_mem_type {n} : byte_parser mem_type n :=
  parse_limits.

Definition parse_mut {n} : byte_parser mutability n :=
  exact_byte x00 $> MUT_immut <|>
  exact_byte x01 $> MUT_mut.

Definition parse_global_type {n} : byte_parser global_type n :=
  ((fun x y => Build_global_type y x) <$> parse_value_type) <*> parse_mut.

Definition parse_import_desc {n} : byte_parser import_desc n :=
  exact_byte x00 &> (extract_typeidx ID_func <$> parse_typeidx) <|>
  exact_byte x01 &> (ID_table <$> parse_table_type) <|>
  exact_byte x02 &> (ID_mem <$> parse_mem_type) <|>
  exact_byte x03 &> (ID_global <$> parse_global_type).

Definition parse_module_import {n} : byte_parser module_import n :=
  ((fun mod name desc => {| imp_module := mod; imp_name := name; imp_desc := desc; |}) <$> parse_vec anyTok) <*>
  parse_vec anyTok <*> parse_import_desc.

Definition parse_module_glob {n} : byte_parser module_glob n :=
  ((fun ty e => {| mg_type := ty; mg_init := e |}) <$> parse_global_type) <*> parse_expr.

Definition parse_module_export_desc {n} : byte_parser module_export_desc n :=
  exact_byte x00 &> (ED_func <$> parse_u32_nat) <|>
  exact_byte x01 &> (ED_table <$> parse_u32_nat) <|>
  exact_byte x02 &> (ED_mem <$> parse_u32_nat) <|>
  exact_byte x03 &> (ED_global <$> parse_u32_nat).

Definition parse_module_export {n} : byte_parser module_export n :=
  ((fun name desc => {| exp_name := name; exp_desc := desc |}) <$> parse_vec anyTok) <*> parse_module_export_desc.

Definition parse_module_start {n} : byte_parser module_start n :=
  (fun func => {| start_func := func |}) <$> parse_u32_nat.

Definition parse_module_element {n} : byte_parser module_element n :=
  ((fun table offset init => {| elem_table := table; elem_offset := offset; elem_init := init |}) <$>
  parse_u32_nat) <*> parse_expr <*> parse_vec parse_u32_nat.

Definition parse_nat_value_type {n} : byte_parser (list value_type) n :=
  ((fun k t => List.repeat t k) <$> parse_u32_nat) <*> parse_value_type.

Definition parse_locals {n} : byte_parser (list value_type) n :=
  (fun tss => List.concat tss) <$> (parse_vec parse_nat_value_type).

Definition parse_func {n} : byte_parser code_func n :=
  ((fun locals e => {| fc_locals := List.concat locals; fc_expr := e |})  <$> parse_vec parse_locals) <*> parse_expr.

Definition parse_code {n} : byte_parser code_func n :=
  guardM
    (fun sf =>
      match sf with
      (* TODO: we are supposed to check that the size matches *)
      | (s, f) => (* if Nat.eqb s (func_size f) then *) Some f (* else None *)
      end)
    (parse_u32_nat <&> parse_func).

Definition parse_module_table {n} : byte_parser module_table n :=
  (fun tty => {| t_type := tty |}) <$> parse_table_type.

Definition parse_module_data {n} : byte_parser module_data n :=
  ((fun data offset init => {| dt_data := data; dt_offset := offset; dt_init := init |}) <$>
  parse_u32_nat) <*> parse_expr <*> parse_vec anyTok.

Definition parse_customsec {n} : byte_parser (list byte) n :=
  exact_byte x00 &> parse_u32 &> parse_vec anyTok.

Definition parse_typesec {n} : byte_parser (list function_type) n :=
  exact_byte x01 &> parse_u32 &> parse_vec parse_function_type.

Definition parse_importsec {n} : byte_parser (list module_import) n :=
  exact_byte x02 &> parse_u32 &> parse_vec parse_module_import.

Definition parse_funcsec {n} : byte_parser (list typeidx) n :=
  exact_byte x03 &> parse_u32 &> parse_vec parse_typeidx.

Definition parse_tablesec {n} : byte_parser (list module_table) n :=
  exact_byte x04 &> parse_u32 &> parse_vec parse_module_table.

Definition parse_memsec {n} : byte_parser (list mem_type) n :=
  exact_byte x05 &> parse_u32 &> parse_vec parse_limits.

Definition parse_globalsec {n} : byte_parser (list module_glob) n :=
  exact_byte x06 &> parse_u32 &> parse_vec parse_module_glob.

Definition parse_exportsec {n} : byte_parser (list module_export) n :=
  exact_byte x07 &> parse_u32 &> parse_vec parse_module_export.

Definition parse_startsec {n} : byte_parser module_start n :=
  exact_byte x08 &> parse_u32 &> parse_module_start.

Definition parse_elemsec {n} : byte_parser (list module_element) n :=
  exact_byte x09 &> parse_u32 &> parse_vec parse_module_element.

Definition parse_codesec {n} : byte_parser (list code_func) n :=
  exact_byte x0a &> parse_u32 &> parse_vec parse_code.

Definition parse_datasec {n} : byte_parser (list module_data) n :=
  exact_byte x0b &> parse_u32 &> parse_vec parse_module_data.

Definition parse_magic {n} : byte_parser unit n :=
  (exact_byte x00 &> exact_byte x61 &> exact_byte x73 &> exact_byte x6d) $> tt.

Definition parse_version {n} : byte_parser unit n :=
  (exact_byte x01 &> exact_byte x00 &> exact_byte x00 &> exact_byte x00) $> tt.

Definition parse_customsec_forget {A n} : byte_parser (A -> A) n :=
  (fun _ x => x) <$> parse_customsec.

Definition parse_with_customsec_star_before {A : Type} {n} :=
  @iterater _ _ _ _ _ _ _ _ _ A n parse_customsec_forget.

Definition parse_with_customsec_star_after {A : Type} {n} f :=
  @iteratel _ _ _ _ _ _ _ _ _ A n f parse_customsec_forget.

Record parsing_module : Type := {
  pmod_types : list function_type;
  pmod_funcs : list typeidx;
  pmod_tables : list module_table;
  pmod_mems : list mem_type;
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

(** this is not in the spec, it is here to force productivity *)
Definition end_marker : byte := x0b.

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
  ((merge_parsing_modules <$> parse_globalsec_wrapper) <*> parse_startsec_onwards) <|>
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
        {| mf_type := a; mf_locals := b.(fc_locals); mf_body := b.(fc_expr) |})
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
  let result := runParser (p n) (le_refl n) input in
  let valid  := fun s => match Success.size s with | O => Some (Success.value s) | _ => None end in
  match mapM valid (runMonad result) with
    | Some (cons hd _) => Some hd
    | _                => None
  end.

End Run.

Definition run_parse_be (bs : list byte) : option basic_instruction :=
  run bs parse_be.

Definition run_parse_be_from_asciis (bs : list ascii) : option basic_instruction :=
  run (List.map byte_of_ascii bs) parse_be.

Definition run_parse_expr (bs : list byte) : option (list basic_instruction) :=
  run bs (fun n => parse_expr).

Definition run_parse_bes (bs : list byte) : option (list basic_instruction) :=
  run_parse_expr (bs ++ (x0b :: nil)).

Definition run_parse_module (bs : list byte) : option module :=
  run (bs ++ cons end_marker nil) (fun n => parse_module).

Definition run_parse_module_from_asciis (bs : list ascii) : option module :=
  run_parse_module (List.map byte_of_ascii bs).