(** Parser for the binary Wasm format. **)
(* TODO: move a few types to the [datatypes] or [bytes] modules. *)
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
  {Toks : nat -> Type} `{Sized Toks ascii}
  {M : Type -> Type} `{RawMonad M} `{RawAlternative M}.

Definition w_parser A n := Parser Toks ascii M A n.
Definition be_parser n := w_parser basic_instruction n.

Definition u32 {n} : w_parser Wasm_int.Int32.int n :=
  (* TODO: limit size *)
  (fun x => Wasm_int.Int32.repr (BinIntDef.Z.of_N x)) <$> (extract unsigned_ n).

Definition exact_byte (x : byte) {n} : w_parser ascii n :=
  exact (ascii_of_byte x).

Definition u32_zero {n} : w_parser Wasm_int.Int32.int n :=
  (* TODO: limit size *)
  exact_byte x00 $> Wasm_int.Int32.zero.

Definition s32 {n} : w_parser Wasm_int.Int32.int n :=
  (* TODO: limit size *)
  (fun x => Wasm_int.Int32.repr x) <$> (extract signed_ n).

Definition s64 {n} : w_parser Wasm_int.Int64.int n :=
  (* TODO: limit size *)
  (fun x => Wasm_int.Int64.repr x) <$> (extract signed_ n).

Definition f32 {n} : w_parser Wasm_float.FloatSize32.T n :=
  (* TODO: use  Flocq.IEEE754.Bits.b32_of_bits *)
  (* TODO: steal IEEE 754-2019 (Section 3.4) bit pattern in little endian from Flocq? *)
  exact_byte x00 $> Wasm_float.Float32.pos_zero.

Definition f64 {n} : w_parser Wasm_float.FloatSize64.T n :=
  (* TODO: steal IEEE 754-2019 (Section 3.4) bit pattern in little endian from Flocq? *)
  exact_byte x00 $> Wasm_float.Float64.pos_zero.

Definition u32_nat {n} : w_parser nat n :=
  (fun x => (Wasm_int.nat_of_uint i32m x)) <$> u32.

Definition veclen {n} : w_parser nat n :=
  (fun x => (Wasm_int.nat_of_uint i32m x)) <$> u32.

Fixpoint vec_aux {B} {n} (f : w_parser B n) (k : nat)
  : w_parser (list B) n :=
  match k with
  | 0 => (fun x => cons x nil) <$> f (* TODO: this is wrong in general, but OK with `vec`?!? *)
  | S 0 => (fun x => cons x nil) <$> f
  | S k' => (cons <$> f) <*> vec_aux f k'
  end.

Definition vec {B} {n} (f : w_parser B n)
  : w_parser (list B) n :=
  (* TODO: this is vomit-inducingly bad, but I have no clue how to avoid this :-( *)
  (u32_zero $> nil) <|>
  (veclen >>= (fun k => vec_aux f k)).

Definition labelidx_ {n} : w_parser labelidx n :=
  (fun x => Mk_labelidx (Wasm_int.nat_of_uint i32m x)) <$> u32.

Definition funcidx_ {n} : w_parser funcidx n :=
  (fun x => Mk_funcidx (Wasm_int.nat_of_uint i32m x)) <$> u32.

Definition typeidx_ {n} : w_parser typeidx n :=
  (fun x => Mk_typeidx (Wasm_int.nat_of_uint i32m x)) <$> u32.

Definition localidx_ {n} : w_parser localidx n :=
  (fun x => Mk_localidx (Wasm_int.nat_of_uint i32m x)) <$> u32.

Definition globalidx_ {n} : w_parser globalidx n :=
  (fun x => Mk_globalidx (Wasm_int.nat_of_uint i32m x)) <$> u32.

Definition value_type_ {n} : w_parser value_type n :=
  (exact_byte x7f $> T_i32) <|>
  (exact_byte x7e $> T_i64) <|>
  (exact_byte x7d $> T_f32) <|>
  (exact_byte x7c $> T_f64).

Definition block_type_ {n} : w_parser (list value_type) n :=
  (fun x => cons x nil) <$> value_type_.

Definition block_type_as_function_type {n} : w_parser function_type n :=
  (exact_byte x40 $> Tf nil nil) <|>
  (Tf nil <$> block_type_).

Definition unreachable {n} : w_parser basic_instruction n :=
  exact_byte x00 $> Unreachable.

Definition nop {n} : w_parser basic_instruction n :=
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

Definition br {n} : w_parser basic_instruction n :=
  exact_byte x0c &> (extract_labelidx Br <$> labelidx_).

Definition br_if {n} : w_parser basic_instruction n :=
  exact_byte x0d &> (extract_labelidx Br_if <$> labelidx_).

Definition br_table_aux (xs : list labelidx) (x : labelidx) :=
  Br_table (List.map (extract_labelidx (fun x => x)) xs) (extract_labelidx (fun x => x) x).

Definition br_table {n} : w_parser basic_instruction n :=
  exact_byte x0e &>
  ((br_table_aux <$> vec labelidx_) <*> labelidx_).

Definition return_ {n} : w_parser basic_instruction n :=
  exact_byte x0f $> Return.

Definition call {n} : w_parser basic_instruction n :=
  exact_byte x10 &> (extract_funcidx Call <$> funcidx_).

Definition call_indirect {n} : w_parser basic_instruction n :=
  exact_byte x11 &> (extract_typeidx Call <$> typeidx_ <& exact_byte x00).

Definition drop {n} : w_parser basic_instruction n :=
  exact_byte x1a $> Drop.

Definition select {n} : w_parser basic_instruction n :=
  exact_byte x1b $> Select.

Definition parametric_instruction {n} : w_parser basic_instruction n :=
  drop <|> select.

Definition local_get {n} : w_parser basic_instruction n :=
  exact_byte x20 &> (extract_localidx Get_local <$> localidx_).

Definition local_set {n} : w_parser basic_instruction n :=
  exact_byte x21 &> (extract_localidx Set_local <$> localidx_).

Definition local_tee {n} : w_parser basic_instruction n :=
  exact_byte x22 &> (extract_localidx Tee_local <$> localidx_).

Definition global_get {n} : w_parser basic_instruction n :=
  exact_byte x23 &> (extract_globalidx Get_global <$> globalidx_).

Definition global_set {n} : w_parser basic_instruction n :=
  exact_byte x24 &> (extract_globalidx Set_global <$> globalidx_).

Definition variable_instruction {n} : w_parser basic_instruction n :=
  local_get <|>
  local_set <|>
  local_tee <|>
  global_get <|>
  global_set.

Definition alignment_exponent_ {n} : w_parser nat n :=
  (fun x => (Wasm_int.nat_of_uint i32m x)) <$> u32.

Definition static_offset_ {n} : w_parser nat n :=
  (fun x => (Wasm_int.nat_of_uint i32m x)) <$> u32.

Definition memarg {n} : w_parser (alignment_exponent * static_offset) n :=
  alignment_exponent_ <&> static_offset_.

Definition i32_load {n} : w_parser basic_instruction n :=
  exact_byte x28 &> (prod_curry (Load T_i32 None) <$> memarg).

Definition i64_load {n} : w_parser basic_instruction n :=
  exact_byte x29 &> (prod_curry (Load T_i64 None) <$> memarg).

Definition f32_load {n} : w_parser basic_instruction n :=
  exact_byte x2a &> (prod_curry (Load T_f32 None) <$> memarg).

Definition f64_load {n} : w_parser basic_instruction n :=
  exact_byte x2b &> (prod_curry (Load T_f64 None) <$> memarg).

Definition i32_load8_s {n} : w_parser basic_instruction n :=
  exact_byte x2c &> (prod_curry (Load T_i32 (Some (Tp_i8, sx_S))) <$> memarg).

Definition i32_load8_u {n} : w_parser basic_instruction n :=
  exact_byte x2d &> (prod_curry (Load T_i32 (Some (Tp_i8, sx_U))) <$> memarg).

Definition i32_load16_s {n} : w_parser basic_instruction n :=
  exact_byte x2e &> (prod_curry (Load T_i32 (Some (Tp_i16, sx_S))) <$> memarg).

Definition i32_load16_u {n} : w_parser basic_instruction n :=
  exact_byte x2f &> (prod_curry (Load T_i32 (Some (Tp_i16, sx_U))) <$> memarg).

Definition i64_load8_s {n} : w_parser basic_instruction n :=
  exact_byte x30 &> (prod_curry (Load T_i64 (Some (Tp_i8, sx_S))) <$> memarg).

Definition i64_load8_u {n} : w_parser basic_instruction n :=
  exact_byte x31 &> (prod_curry (Load T_i64 (Some (Tp_i8, sx_U))) <$> memarg).

Definition i64_load16_s {n} : w_parser basic_instruction n :=
  exact_byte x32 &> (prod_curry (Load T_i64 (Some (Tp_i16, sx_S))) <$> memarg).

Definition i64_load16_u {n} : w_parser basic_instruction n :=
  exact_byte x33 &> (prod_curry (Load T_i64 (Some (Tp_i16, sx_U))) <$> memarg).

Definition i64_load32_s {n} : w_parser basic_instruction n :=
  exact_byte x34 &> (prod_curry (Load T_i64 (Some (Tp_i32, sx_S))) <$> memarg).

Definition i64_load32_u {n} : w_parser basic_instruction n :=
  exact_byte x35 &> (prod_curry (Load T_i64 (Some (Tp_i32, sx_U))) <$> memarg).

Definition i32_store {n} : w_parser basic_instruction n :=
  exact_byte x36 &> (prod_curry (Store T_i32 None) <$> memarg).

Definition i64_store {n} : w_parser basic_instruction n :=
  exact_byte x37 &> (prod_curry (Store T_i64 None) <$> memarg).

Definition f32_store {n} : w_parser basic_instruction n :=
  exact_byte x38 &> (prod_curry (Store T_f32 None) <$> memarg).

Definition f64_store {n} : w_parser basic_instruction n :=
  exact_byte x39 &> (prod_curry (Store T_f64 None) <$> memarg).

Definition i32_store8 {n} : w_parser basic_instruction n :=
  exact_byte x3a &> (prod_curry (Store T_i32 (Some Tp_i8)) <$> memarg).

Definition i32_store16 {n} : w_parser basic_instruction n :=
  exact_byte x3b &> (prod_curry (Store T_i32 (Some Tp_i16)) <$> memarg).

Definition i64_store8 {n} : w_parser basic_instruction n :=
  exact_byte x3c &> (prod_curry (Store T_i32 (Some Tp_i8)) <$> memarg).

Definition i64_store16 {n} : w_parser basic_instruction n :=
  exact_byte x3d &> (prod_curry (Store T_i32 (Some Tp_i16)) <$> memarg).

Definition i64_store32 {n} : w_parser basic_instruction n :=
  exact_byte x3e &> (prod_curry (Store T_i32 (Some Tp_i32)) <$> memarg).

Definition memory_size {n} : w_parser basic_instruction n :=
  exact_byte x3f &> (exact_byte x00 $> Current_memory).

Definition memory_grow {n} : w_parser basic_instruction n :=
  exact_byte x40 &> (exact_byte x00 $> Grow_memory).

Definition memory_instruction {n} : w_parser basic_instruction n :=
  i32_load <|>
  i64_load <|>
  f32_load <|>
  f64_load <|>
  i32_load8_s <|>
  i32_load8_u <|>
  i32_load16_s <|>
  i32_load16_u <|>
  i64_load8_s <|>
  i64_load8_u <|>
  i64_load16_s <|>
  i64_load16_u <|>
  i64_load32_s <|>
  i64_load32_u <|>
  i32_store <|>
  i64_store <|>
  f32_store <|>
  f64_store <|>
  i32_store8 <|>
  i32_store16 <|>
  i64_store8 <|>
  i64_store16 <|>
  i64_store32 <|>
  memory_size <|>
  memory_grow.

Definition i32_const {n} : be_parser n :=
  exact_byte x41 &> ((fun x => EConst (ConstInt32 x)) <$> s32).

Definition i64_const {n} : be_parser n :=
  exact_byte x42 &> ((fun x => EConst (ConstInt64 x)) <$> s64).

Definition f32_const {n} : be_parser n :=
  exact_byte x43 &> ((fun x => EConst (ConstFloat32 x)) <$> f32).

Definition f64_const {n} : be_parser n :=
  exact_byte x44 &> ((fun x => EConst (ConstFloat64 x)) <$> f64).

(* :-( *)
Definition numeric_instruction {n} : be_parser n :=
  i32_const <|>
  i64_const <|>
  f32_const <|>
  f64_const <|>
  exact_byte x45 $> Testop T_i32 Eqz <|>
  exact_byte x46 $> Relop_i T_i32 Eq <|>
  exact_byte x47 $> Relop_i T_i32 Ne <|>
  exact_byte x48 $> Relop_i T_i32 (Lt sx_S) <|>
  exact_byte x49 $> Relop_i T_i32 (Lt sx_U) <|>
  exact_byte x4a $> Relop_i T_i32 (Gt sx_S) <|>
  exact_byte x4b $> Relop_i T_i32 (Gt sx_U) <|>
  exact_byte x4c $> Relop_i T_i32 (Le sx_S) <|>
  exact_byte x4d $> Relop_i T_i32 (Le sx_U) <|>
  exact_byte x4e $> Relop_i T_i32 (Ge sx_S) <|>
  exact_byte x4f $> Relop_i T_i32 (Ge sx_U) <|>

  exact_byte x50 $> Testop T_i64 Eqz <|>
  exact_byte x51 $> Relop_i T_i64 Eq <|>
  exact_byte x52 $> Relop_i T_i64 Ne <|>
  exact_byte x53 $> Relop_i T_i64 (Lt sx_S) <|>
  exact_byte x54 $> Relop_i T_i64 (Lt sx_U) <|>
  exact_byte x55 $> Relop_i T_i64 (Gt sx_S) <|>
  exact_byte x56 $> Relop_i T_i64 (Gt sx_U) <|>
  exact_byte x57 $> Relop_i T_i64 (Le sx_S) <|>
  exact_byte x58 $> Relop_i T_i64 (Le sx_U) <|>
  exact_byte x59 $> Relop_i T_i64 (Ge sx_S) <|>
  exact_byte x5a $> Relop_i T_i64 (Ge sx_U) <|>

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
  exact_byte x6d $> Binop_i T_i32 (Div sx_S) <|>
  exact_byte x6e $> Binop_i T_i32 (Div sx_U) <|>
  exact_byte x6f $> Binop_i T_i32 (Rem sx_S) <|>
  exact_byte x70 $> Binop_i T_i32 (Rem sx_U) <|>
  exact_byte x71 $> Binop_i T_i32 And <|>
  exact_byte x72 $> Binop_i T_i32 Or <|>
  exact_byte x73 $> Binop_i T_i32 Xor <|>
  exact_byte x74 $> Binop_i T_i32 Shl <|>
  exact_byte x75 $> Binop_i T_i32 (Shr sx_S) <|>
  exact_byte x76 $> Binop_i T_i32 (Shr sx_U) <|>
  exact_byte x77 $> Binop_i T_i32 Rotl <|>
  exact_byte x78 $> Binop_i T_i32 Rotr <|>

  exact_byte x79 $> Unop_i T_i64 Clz <|>
  exact_byte x7a $> Unop_i T_i64 Ctz <|>
  exact_byte x7b $> Unop_i T_i64 Popcnt <|>
  exact_byte x7c $> Binop_i T_i64 Add <|>
  exact_byte x7d $> Binop_i T_i64 Sub <|>
  exact_byte x7e $> Binop_i T_i64 Mul <|>
  exact_byte x7f $> Binop_i T_i64 (Div sx_S) <|>
  exact_byte x80 $> Binop_i T_i64 (Div sx_U) <|>
  exact_byte x81 $> Binop_i T_i64 (Rem sx_S) <|>
  exact_byte x82 $> Binop_i T_i64 (Rem sx_U) <|>
  exact_byte x83 $> Binop_i T_i64 And <|>
  exact_byte x84 $> Binop_i T_i64 Or <|>
  exact_byte x85 $> Binop_i T_i64 Xor <|>
  exact_byte x86 $> Binop_i T_i64 Shl <|>
  exact_byte x87 $> Binop_i T_i64 (Shr sx_S) <|>
  exact_byte x88 $> Binop_i T_i64 (Shr sx_U) <|>
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
  exact_byte xa7 $> Cvtop T_i32 Convert T_i64 (Some sx_U) <|>
  exact_byte xa8 $> Cvtop T_i32 Convert T_f32 (Some sx_S) <|>
  exact_byte xa9 $> Cvtop T_i32 Convert T_f32 (Some sx_U) <|>
  exact_byte xaa $> Cvtop T_i32 Convert T_f64 (Some sx_S) <|>
  exact_byte xab $> Cvtop T_i32 Convert T_f64 (Some sx_U) <|>
  exact_byte xac $> Cvtop T_i64 Convert T_i32 (Some sx_S) <|>
  exact_byte xad $> Cvtop T_i64 Convert T_i32 (Some sx_U) <|>
  exact_byte xae $> Cvtop T_i64 Convert T_f32 (Some sx_S) <|>
  exact_byte xaf $> Cvtop T_i64 Convert T_f32 (Some sx_U) <|>
  exact_byte xb0 $> Cvtop T_i64 Convert T_f64 (Some sx_S) <|>
  exact_byte xb1 $> Cvtop T_i64 Convert T_f64 (Some sx_U) <|>
  exact_byte xb2 $> Cvtop T_f32 Convert T_i32 (Some sx_S) <|>
  exact_byte xb3 $> Cvtop T_f32 Convert T_i32 (Some sx_U) <|>
  exact_byte xb4 $> Cvtop T_f32 Convert T_i64 (Some sx_S) <|>
  exact_byte xb5 $> Cvtop T_f32 Convert T_i64 (Some sx_U) <|>
  exact_byte xb6 $> Cvtop T_f32 Convert T_f64 None <|>
  exact_byte xb7 $> Cvtop T_f64 Convert T_i32 (Some sx_S) <|>
  exact_byte xb8 $> Cvtop T_f64 Convert T_i32 (Some sx_U) <|>
  exact_byte xb9 $> Cvtop T_f64 Convert T_i64 (Some sx_S) <|>
  exact_byte xba $> Cvtop T_f64 Convert T_i64 (Some sx_U) <|>
  exact_byte xbb $> Cvtop T_f32 Convert T_f64 None <|>
  exact_byte xbc $> Cvtop T_i32 Reinterpret T_f32 None <|>
  exact_byte xbd $> Cvtop T_i64 Reinterpret T_f64 None <|>
  exact_byte xbe $> Cvtop T_f32 Reinterpret T_i32 None <|>
  exact_byte xbf $> Cvtop T_f64 Reinterpret T_i64 None.

Record Language (n : nat) : Type := MkLanguage
{ _be : w_parser basic_instruction n;
  _bes : w_parser (list basic_instruction) n;
}.

Arguments MkLanguage {_}.

Context
  {Tok : Type} {A B : Type} {n : nat}.

Definition language : [ Language ] := Fix Language (fun _ rec =>
  let bes_aux := Induction.map _bes _ rec in
  let block := exact_byte x02 &> ((Block <$> block_type_as_function_type) <*> bes_aux) <& exact_byte x0b in
  let loop := exact_byte x03 &> ((Loop <$> block_type_as_function_type) <*> bes_aux) <& exact_byte x0b in
  let if_rest :=
    (exact_byte x0b $> nil) <|>
    ((exact_byte x05 &> bes_aux) <& exact_byte x0b) in
  let if_ := exact_byte x04 &> ((If <$> block_type_as_function_type) <*> bes_aux <*> if_rest) in
  let be :=
    unreachable <|>
    nop <|>
    block <|>
    loop <|>
    if_ <|>
    br <|>
    br_if <|>
    br_table <|>
    return_ <|>
    call <|>
    call_indirect <|>
    parametric_instruction <|>
    variable_instruction <|>
    memory_instruction <|>
    numeric_instruction in
  let bes := (fun l => NEList.toList l) <$> nelist be in
  MkLanguage be bes).

Definition be : [ w_parser basic_instruction ] := fun n => _be n (language n).
Definition bes : [ w_parser (list basic_instruction) ] := fun n => _bes n (language n).

Definition end_ {n} : w_parser unit n :=
  cmap tt (exact_byte x0b).

Definition expr_ {n} : w_parser (list basic_instruction) n :=
  extract bes n. (* TODO: is that right? *)

Definition byte_ {n} : w_parser ascii n :=
  anyTok.

Definition function_type_ {n} : w_parser function_type n :=
  exact_byte x60 &> (prod_curry Tf <$> vec value_type_ <&> vec value_type_).

Definition limits_ {n} : w_parser limits n :=
  exact_byte x00 &> ((fun min => Mk_limits min None) <$> u32_nat) <|>
  exact_byte x01 &> ((fun min max => Mk_limits min (Some max)) <$> u32_nat) <*> u32_nat.

Definition elem_type_ {n} : w_parser elem_type n :=
  exact_byte x70 $> elem_type_tt.

Definition table_type_ {n} : w_parser table_type n :=
  prod_curry Mk_table_type <$> (limits_ <&> elem_type_).

Definition mem_type_ {n} : w_parser mem_type n :=
  Mk_mem_type <$> limits_.

Definition mut_ {n} : w_parser mutability n :=
  exact_byte x00 $> T_immut <|>
  exact_byte x01 $> T_mut.

Definition global_type_ {n} : w_parser global_type n :=
  ((fun x y => Build_global_type y x) <$> value_type_) <*> mut_.

Definition import_desc_ {n} : w_parser import_desc n :=
  exact_byte x00 &> (extract_typeidx ID_func <$> typeidx_) <|>
  exact_byte x01 &> (ID_table <$> table_type_) <|>
  exact_byte x02 &> (ID_mem <$> mem_type_) <|>
  exact_byte x03 &> (ID_global <$> global_type_).



Definition import_ {n} : w_parser import n :=
  (Mk_import <$> vec byte_) <*> vec byte_ <*> import_desc_.

Definition global2_ {n} : w_parser global2 n :=
  (Build_global2 <$> global_type_) <*> expr_.

Definition export_desc_ {n} : w_parser export_desc n :=
  exact_byte x00 &> (ED_func <$> u32_nat) <|>
  exact_byte x01 &> (ED_table <$> u32_nat) <|>
  exact_byte x02 &> (ED_mem <$> u32_nat) <|>
  exact_byte x03 &> (ED_global <$> u32_nat).

Definition export_ {n} : w_parser export n :=
  (Build_export <$> vec byte_) <*> export_desc_.

Definition start_ {n} : w_parser start n :=
  Build_start <$> u32_nat.

Definition element_ {n} : w_parser element n :=
  (Build_element <$> u32_nat) <*> expr_ <*> vec u32_nat.

Definition locals_ {n} : w_parser (list value_type) n :=
  vec value_type_.

Definition func_ {n} : w_parser func n :=
  ((fun xs => Build_func (List.concat xs)) <$> vec locals_) <*> expr_.

Definition code_ {n} : w_parser func n :=
  guardM
    (fun sf =>
      match sf with
      (* TODO: we are supposed to check that the size matches *)
      | (s, f) => (* if Nat.eqb s (func_size f) then *) Some f (* else None *)
      end)
    (u32_nat <&> func_).

Definition table_ {n} : w_parser table n :=
  Mk_table <$> table_type_.

Definition data_ {n} : w_parser data n :=
  (Build_data <$> u32_nat) <*> expr_ <*> vec byte_.

Definition customsec {n} : w_parser (list ascii) n :=
  exact_byte x00 &> vec byte_.

Definition typesec {n} : w_parser (list function_type) n :=
  exact_byte x01 &> vec function_type_.

Definition importsec {n} : w_parser (list import) n :=
  exact_byte x02 &> vec import_.

Definition funcsec {n} : w_parser (list typeidx) n :=
  exact_byte x03 &> vec typeidx_.

Definition tablesec {n} : w_parser (list table) n :=
  exact_byte x04 &>  vec table_.

Definition memsec {n} : w_parser (list mem) n :=
  exact_byte x05 &> vec limits_.

Definition globalsec {n} : w_parser (list global2) n :=
  exact_byte x06 &> vec global2_.

Definition exportsec {n} : w_parser (list export) n :=
  exact_byte x07 &> vec export_.

Definition startsec {n} : w_parser start n :=
  exact_byte x08 &> start_.

Definition elemsec {n} : w_parser (list element) n :=
  exact_byte x09 &> vec element_.

Definition codesec {n} : w_parser (list func) n :=
  exact_byte x0a &> vec code_.

Definition datasec {n} : w_parser (list data) n :=
  exact_byte x0b &> (vec data_).

Definition section_ {n} : w_parser section n :=
  Sec_custom <$> customsec <|>
  Sec_type <$> typesec <|>
  Sec_import <$> importsec <|>
  Sec_function <$> funcsec <|>
  Sec_table <$> tablesec <|>
  Sec_memory <$> memsec <|>
  Sec_global <$> globalsec <|>
  Sec_export <$> exportsec <|>
  Sec_start <$> startsec <|>
  Sec_element <$> elemsec <|>
  Sec_code <$> codesec <|>
  Sec_data <$> datasec.

Definition magic {n} : w_parser unit n :=
  (exact_byte x00 &> exact_byte x61 &> exact_byte x73 &> exact_byte x6d) $> tt.

Definition version {n} : w_parser unit n :=
  (exact_byte x01 &> exact_byte x00 &> exact_byte x00 &> exact_byte x00) $> tt.

Definition customsec_forget_ {A n} : w_parser (A -> A) n :=
  (fun _ x => x) <$> customsec.

Definition with_customsec_star_before {A : Type} {n} :=
  @iterater _ _ _ _ _ _ _ _ _ A n customsec_forget_.

Definition with_customsec_star_after {A : Type} {n} f :=
  @iteratel _ _ _ _ _ _ _ _ _ A n f customsec_forget_.

Definition tail_ {n} : w_parser _ n :=
  (with_customsec_star_before elemsec) <&>
  (with_customsec_star_before codesec) <&>
  (with_customsec_star_before (with_customsec_star_after datasec)).

Definition module_ {n} : w_parser module n :=
(* TODO: this is missing all the customsecs! *)
  magic &>
  version &>
  (((fun functype import typeidx table mem global export secd_ecd =>
    match secd_ecd with
    | inl (start, (elem, code, data)) =>
      let func := nil in
      Build_module functype func table mem global elem data (Some start) import export
    | inr (elem, code, data) =>
      let func := nil in
      Build_module functype func table mem global elem data None import export
    end
  ) <$>
  (with_customsec_star_before typesec)) <*>
  (with_customsec_star_before importsec)) <*>
  (with_customsec_star_before funcsec) <*>
  (with_customsec_star_before tablesec) <*>
  (with_customsec_star_before memsec) <*>
  (with_customsec_star_before globalsec) <*>
  (with_customsec_star_before exportsec) <*>
  ((inl <$> (with_customsec_star_before startsec) <&> tail_) <|> (inr <$> tail_)).

End Language.


Inductive Singleton (A : Type) : A -> Type :=
  MkSingleton : forall a, Singleton A a.

Arguments Singleton {_}.
Arguments MkSingleton {_}.

Class Tokenizer (A : Type) : Type :=
  MkTokenizer { _tokenize : list ascii -> list A }.

Definition tokenize {A : Type} `{Tokenizer A} : list ascii -> list A := _tokenize.

Arguments MkTokenizer {_}.

Definition fromText {A : Type} `{Tokenizer A} (s : list ascii) : list A :=
  tokenize s.

Instance tokBytes : Tokenizer ascii := MkTokenizer (fun x => x).

Section Run.

Context
  {M : Type -> Type} `{RawMonad M} `{RawAlternative M} `{RawMonadRun M}
  {Tok : Type} `{Tokenizer Tok}
  {A : Type}.

Definition run : list ascii -> [ Parser (SizedList Tok) Tok M A ] -> option A := fun s p =>
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

Definition parse_wasm (bs : list Ascii.ascii) : option basic_instruction :=
  run bs be.

Definition parse_wasm_bytes (bs : list byte) : option basic_instruction :=
  run (List.map ascii_of_byte bs) be.
