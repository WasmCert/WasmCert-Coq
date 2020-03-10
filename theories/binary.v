(* Parser for the binary Wasm format *)
(* TODO: hook up to an OCaml harness and test!!! *)
(* TODO: move a few types to wasm.v *)
(* TODO: write a relational spec, and prove they correspond *)

(* TODO: make this more robust *)
Add Rec LoadPath "/home/xy/wasm_coq/_build/default/theories" as Wasm.

From Wasm Require Import wasm.
From compcert Require Import Integers.
Require Import Parseque.
(*Require Import Running.*)
Require Import bytes.
Require Import leb128.
Require Import Coq.Arith.Le.

Notation "p $> b" := (cmap b p) (at level 59, right associativity).

Section Language.

Context
  {Toks : nat -> Type} `{Sized Toks Integers.Byte.int}
  {M : Type -> Type} `{RawMonad M} `{RawAlternative M}.

Definition w_parser A n := Parser Toks Integers.Byte.int M A n.
Definition be_parser n := w_parser basic_instruction n.

Definition u32 {n} : w_parser Wasm_int.Int32.int n :=
  (fun x => Wasm_int.Int32.repr (BinIntDef.Z.of_nat x)) <$> unsigned_ n. (* TODO: limit size *)
  
Definition u32_zero {n} : w_parser Wasm_int.Int32.int n :=
  exact #00 $> Wasm_int.Int32.zero.

Definition s32 {n} : w_parser Wasm_int.Int32.int n :=
  exact #00 $> Wasm_int.Int32.zero (* TODO: implement LEB128 *).

Definition s64 {n} : w_parser Wasm_int.Int64.int n :=
  exact #00 $> Wasm_int.Int64.zero (* TODO: implement LEB128 *).

Definition f32 {n} : w_parser Wasm_float.FloatSize32.T n :=
  exact #00 $> Wasm_float.Float32.pos_zero (* TODO: steal IEEE 754-2019 (Section 3.4) bit pattern in little endian from Flocq? *).

Definition f64 {n} : w_parser Wasm_float.FloatSize64.T n :=
  exact #00 $> Wasm_float.Float64.pos_zero (* TODO: steal IEEE 754-2019 (Section 3.4) bit pattern in little endian from Flocq? *).

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

Inductive labelidx : Type :=
| Mk_labelidx : nat -> labelidx.

Definition labelidx_ {n} : w_parser labelidx n :=
  (fun x => Mk_labelidx (Wasm_int.nat_of_uint i32m x)) <$> u32.

Inductive funcidx : Type :=
| Mk_funcidx : nat -> funcidx.

Definition funcidx_ {n} : w_parser funcidx n :=
  (fun x => Mk_funcidx (Wasm_int.nat_of_uint i32m x)) <$> u32.

Inductive typeidx : Type :=
| Mk_typeidx : nat -> typeidx.

Definition typeidx_ {n} : w_parser typeidx n :=
  (fun x => Mk_typeidx (Wasm_int.nat_of_uint i32m x)) <$> u32.

Inductive localidx : Type :=
| Mk_localidx : nat -> localidx.

Definition localidx_ {n} : w_parser localidx n :=
  (fun x => Mk_localidx (Wasm_int.nat_of_uint i32m x)) <$> u32.

Inductive globalidx : Type :=
| Mk_globalidx : nat -> globalidx.

Definition globalidx_ {n} : w_parser globalidx n :=
  (fun x => Mk_globalidx (Wasm_int.nat_of_uint i32m x)) <$> u32.

Definition value_type_ {n} : w_parser value_type n :=
  (exact #7F $> T_i32) <|>
  (exact #7E $> T_i64) <|>
  (exact #7D $> T_f32) <|>
  (exact #7C $> T_f64).

Definition block_type_ {n} : w_parser (list value_type) n :=
  (fun x => cons x nil) <$> value_type_.

Definition block_type_as_function_type {n} : w_parser function_type n :=
    (exact #40 $> Tf nil nil) <|>
    (Tf nil <$> block_type_).

Definition unreachable {n} : w_parser basic_instruction n :=
  exact #00 $> Unreachable.

Definition nop {n} : w_parser basic_instruction n :=
  exact #01 $> Nop.

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
  exact #0C &> (extract_labelidx Br <$> labelidx_).

Definition br_if {n} : w_parser basic_instruction n :=
  exact #0D &> (extract_labelidx Br_if <$> labelidx_).

Definition br_table_aux (xs : list labelidx) (x : labelidx) :=
  Br_table (List.map (extract_labelidx (fun x => x)) xs) (extract_labelidx (fun x => x) x).

Definition br_table {n} : w_parser basic_instruction n :=
  exact #0E &>
  ((br_table_aux
  <$> vec labelidx_) <*> labelidx_).

Definition return_ {n} : w_parser basic_instruction n :=
  exact #0F $> Return.

Definition call {n} : w_parser basic_instruction n :=
  exact #10 &> (extract_funcidx Call <$> funcidx_).

Definition call_indirect {n} : w_parser basic_instruction n :=
  exact #11 &> (extract_typeidx Call <$> typeidx_ <& exact #00). (* TODO: why the trailing #00 in the spec? *)

Definition drop {n} : w_parser basic_instruction n :=
  exact #1A $> Drop.

Definition select {n} : w_parser basic_instruction n :=
  exact #1B $> Select.

Definition parametric_instruction {n} : w_parser basic_instruction n :=
  drop <|>
  select.

Definition local_get {n} : w_parser basic_instruction n :=
  exact #20 &> (extract_localidx Get_local <$> localidx_).

Definition local_set {n} : w_parser basic_instruction n :=
  exact #21 &> (extract_localidx Set_local <$> localidx_).

Definition local_tee {n} : w_parser basic_instruction n :=
  exact #22 &> (extract_localidx Tee_local <$> localidx_).

Definition global_get {n} : w_parser basic_instruction n :=
  exact #23 &> (extract_globalidx Get_global <$> globalidx_).

Definition global_set {n} : w_parser basic_instruction n :=
  exact #24 &> (extract_globalidx Set_global <$> globalidx_).

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
  exact #28 &> (prod_curry (Load T_i32 None) <$> memarg).

Definition i64_load {n} : w_parser basic_instruction n :=
  exact #29 &> (prod_curry (Load T_i64 None) <$> memarg).

Definition f32_load {n} : w_parser basic_instruction n :=
  exact #2A &> (prod_curry (Load T_f32 None) <$> memarg).

Definition f64_load {n} : w_parser basic_instruction n :=
  exact #2B &> (prod_curry (Load T_f64 None) <$> memarg).

Definition i32_load8_s {n} : w_parser basic_instruction n :=
  exact #2C &> (prod_curry (Load T_i32 (Some (Tp_i8, sx_S))) <$> memarg).

Definition i32_load8_u {n} : w_parser basic_instruction n :=
  exact #2D &> (prod_curry (Load T_i32 (Some (Tp_i8, sx_U))) <$> memarg).

Definition i32_load16_s {n} : w_parser basic_instruction n :=
  exact #2E &> (prod_curry (Load T_i32 (Some (Tp_i16, sx_S))) <$> memarg).

Definition i32_load16_u {n} : w_parser basic_instruction n :=
  exact #2F &> (prod_curry (Load T_i32 (Some (Tp_i16, sx_U))) <$> memarg).

Definition i64_load8_s {n} : w_parser basic_instruction n :=
  exact #30 &> (prod_curry (Load T_i64 (Some (Tp_i8, sx_S))) <$> memarg).

Definition i64_load8_u {n} : w_parser basic_instruction n :=
  exact #31 &> (prod_curry (Load T_i64 (Some (Tp_i8, sx_U))) <$> memarg).

Definition i64_load16_s {n} : w_parser basic_instruction n :=
  exact #32 &> (prod_curry (Load T_i64 (Some (Tp_i16, sx_S))) <$> memarg).

Definition i64_load16_u {n} : w_parser basic_instruction n :=
  exact #33 &> (prod_curry (Load T_i64 (Some (Tp_i16, sx_U))) <$> memarg).

Definition i64_load32_s {n} : w_parser basic_instruction n :=
  exact #34 &> (prod_curry (Load T_i64 (Some (Tp_i32, sx_S))) <$> memarg).

Definition i64_load32_u {n} : w_parser basic_instruction n :=
  exact #35 &> (prod_curry (Load T_i64 (Some (Tp_i32, sx_U))) <$> memarg).

Definition i32_store {n} : w_parser basic_instruction n :=
  exact #36 &> (prod_curry (Store T_i32 None) <$> memarg).

Definition i64_store {n} : w_parser basic_instruction n :=
  exact #37 &> (prod_curry (Store T_i64 None) <$> memarg).

Definition f32_store {n} : w_parser basic_instruction n :=
  exact #38 &> (prod_curry (Store T_f32 None) <$> memarg).

Definition f64_store {n} : w_parser basic_instruction n :=
  exact #39 &> (prod_curry (Store T_f64 None) <$> memarg).

Definition i32_store8 {n} : w_parser basic_instruction n :=
  exact #3A &> (prod_curry (Store T_i32 (Some Tp_i8)) <$> memarg).

Definition i32_store16 {n} : w_parser basic_instruction n :=
  exact #3B &> (prod_curry (Store T_i32 (Some Tp_i16)) <$> memarg).

Definition i64_store8 {n} : w_parser basic_instruction n :=
  exact #3C &> (prod_curry (Store T_i32 (Some Tp_i8)) <$> memarg).

Definition i64_store16 {n} : w_parser basic_instruction n :=
  exact #3D &> (prod_curry (Store T_i32 (Some Tp_i16)) <$> memarg).

Definition i64_store32 {n} : w_parser basic_instruction n :=
  exact #3E &> (prod_curry (Store T_i32 (Some Tp_i32)) <$> memarg).

Definition memory_size {n} : w_parser basic_instruction n :=
  exact #3F &> (exact #00 $> Current_memory).

Definition memory_grow {n} : w_parser basic_instruction n :=
  exact #40 &> (exact #00 $> Grow_memory).

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
  exact #41 &> ((fun x => EConst (ConstInt32 x)) <$> s32).

Definition i64_const {n} : be_parser n :=
  exact #42 &> ((fun x => EConst (ConstInt64 x)) <$> s64).

Definition f32_const {n} : be_parser n :=
  exact #43 &> ((fun x => EConst (ConstFloat32 x)) <$> f32).

Definition f64_const {n} : be_parser n :=
  exact #44 &> ((fun x => EConst (ConstFloat64 x)) <$> f64).

(* :-( *)
Definition numeric_instruction {n} : be_parser n :=
  i32_const <|>
  i64_const <|>
  f32_const <|>
  f64_const <|>
  exact #45 $> Testop T_i32 Eqz <|>
  exact #46 $> Relop_i T_i32 Eq <|>
  exact #47 $> Relop_i T_i32 Ne <|>
  exact #48 $> Relop_i T_i32 (Lt sx_S) <|>
  exact #49 $> Relop_i T_i32 (Lt sx_U) <|>
  exact #4A $> Relop_i T_i32 (Gt sx_S) <|>
  exact #4B $> Relop_i T_i32 (Gt sx_U) <|>
  exact #4C $> Relop_i T_i32 (Le sx_S) <|>
  exact #4D $> Relop_i T_i32 (Le sx_U) <|>
  exact #4E $> Relop_i T_i32 (Ge sx_S) <|>
  exact #4F $> Relop_i T_i32 (Ge sx_U) <|>

  exact #50 $> Testop T_i64 Eqz <|>
  exact #51 $> Relop_i T_i64 Eq <|>
  exact #52 $> Relop_i T_i64 Ne <|>
  exact #53 $> Relop_i T_i64 (Lt sx_S) <|>
  exact #54 $> Relop_i T_i64 (Lt sx_U) <|>
  exact #55 $> Relop_i T_i64 (Gt sx_S) <|>
  exact #56 $> Relop_i T_i64 (Gt sx_U) <|>
  exact #57 $> Relop_i T_i64 (Le sx_S) <|>
  exact #58 $> Relop_i T_i64 (Le sx_U) <|>
  exact #59 $> Relop_i T_i64 (Ge sx_S) <|>
  exact #5A $> Relop_i T_i64 (Ge sx_U) <|>

  exact #5B $> Relop_f T_f32 Eqf <|>
  exact #5C $> Relop_f T_f32 Nef <|>
  exact #5D $> Relop_f T_f32 Ltf <|>
  exact #5E $> Relop_f T_f32 Gtf <|>
  exact #5F $> Relop_f T_f32 Lef <|>
  exact #60 $> Relop_f T_f32 Gef <|>

  exact #61 $> Relop_f T_f64 Eqf <|>
  exact #62 $> Relop_f T_f64 Nef <|>
  exact #63 $> Relop_f T_f64 Ltf <|>
  exact #64 $> Relop_f T_f64 Gtf <|>
  exact #65 $> Relop_f T_f64 Lef <|>
  exact #66 $> Relop_f T_f64 Gef <|>

  exact #67 $> Unop_i T_i32 Clz <|>
  exact #68 $> Unop_i T_i32 Ctz <|>
  exact #69 $> Unop_i T_i32 Popcnt <|>
  exact #6A $> Binop_i T_i32 Add <|>
  exact #6B $> Binop_i T_i32 Sub <|>
  exact #6C $> Binop_i T_i32 Mul <|>
  exact #6D $> Binop_i T_i32 (Div sx_S) <|>
  exact #6E $> Binop_i T_i32 (Div sx_U) <|>
  exact #6F $> Binop_i T_i32 (Rem sx_S) <|>
  exact #70 $> Binop_i T_i32 (Rem sx_U) <|>
  exact #71 $> Binop_i T_i32 And <|>
  exact #72 $> Binop_i T_i32 Or <|>
  exact #73 $> Binop_i T_i32 Xor <|>
  exact #74 $> Binop_i T_i32 Shl <|>
  exact #75 $> Binop_i T_i32 (Shr sx_S) <|>
  exact #76 $> Binop_i T_i32 (Shr sx_U) <|>
  exact #77 $> Binop_i T_i32 Rotl <|>
  exact #78 $> Binop_i T_i32 Rotr <|>

  exact #79 $> Unop_i T_i64 Clz <|>
  exact #7A $> Unop_i T_i64 Ctz <|>
  exact #7B $> Unop_i T_i64 Popcnt <|>
  exact #7C $> Binop_i T_i64 Add <|>
  exact #7D $> Binop_i T_i64 Sub <|>
  exact #7E $> Binop_i T_i64 Mul <|>
  exact #7F $> Binop_i T_i64 (Div sx_S) <|>
  exact #80 $> Binop_i T_i64 (Div sx_U) <|>
  exact #81 $> Binop_i T_i64 (Rem sx_S) <|>
  exact #82 $> Binop_i T_i64 (Rem sx_U) <|>
  exact #83 $> Binop_i T_i64 And <|>
  exact #84 $> Binop_i T_i64 Or <|>
  exact #85 $> Binop_i T_i64 Xor <|>
  exact #86 $> Binop_i T_i64 Shl <|>
  exact #87 $> Binop_i T_i64 (Shr sx_S) <|>
  exact #88 $> Binop_i T_i64 (Shr sx_U) <|>
  exact #89 $> Binop_i T_i64 Rotl <|>
  exact #8A $> Binop_i T_i64 Rotr <|>

  exact #8B $> Unop_f T_f32 Abs <|>
  exact #8C $> Unop_f T_f32 Neg <|>
  exact #8D $> Unop_f T_f32 Ceil <|>
  exact #8E $> Unop_f T_f32 Floor <|>
  exact #8F $> Unop_f T_f32 Trunc <|>
  exact #90 $> Unop_f T_f32 Nearest <|>
  exact #91 $> Unop_f T_f32 Sqrt <|>
  exact #92 $> Binop_f T_f32 Addf <|>
  exact #93 $> Binop_f T_f32 Subf <|>
  exact #94 $> Binop_f T_f32 Mulf <|>
  exact #95 $> Binop_f T_f32 Divf <|>
  exact #96 $> Binop_f T_f32 Min <|>
  exact #97 $> Binop_f T_f32 Max <|>
  exact #98 $> Binop_f T_f32 Copysign <|>

  exact #99 $> Unop_f T_f64 Abs <|>
  exact #9A $> Unop_f T_f64 Neg <|>
  exact #9B $> Unop_f T_f64 Ceil <|>
  exact #9C $> Unop_f T_f64 Floor <|>
  exact #9D $> Unop_f T_f64 Trunc <|>
  exact #9E $> Unop_f T_f64 Nearest <|>
  exact #9F $> Unop_f T_f64 Sqrt <|>
  exact #A0 $> Binop_f T_f64 Addf <|>
  exact #A1 $> Binop_f T_f64 Subf <|>
  exact #A2 $> Binop_f T_f64 Mulf <|>
  exact #A3 $> Binop_f T_f64 Divf <|>
  exact #A4 $> Binop_f T_f64 Min <|>
  exact #A5 $> Binop_f T_f64 Max <|>
  exact #A6 $> Binop_f T_f64 Copysign <|>

  (* TODO: I am really not sure whether this is right :-s *)
  exact #A7 $> Cvtop T_i32 Convert T_i64 (Some sx_U) <|>
  exact #A8 $> Cvtop T_i32 Convert T_f32 (Some sx_S) <|>
  exact #A9 $> Cvtop T_i32 Convert T_f32 (Some sx_U) <|>
  exact #AA $> Cvtop T_i32 Convert T_f64 (Some sx_S) <|>
  exact #AB $> Cvtop T_i32 Convert T_f64 (Some sx_U) <|>
  exact #AC $> Cvtop T_i64 Convert T_i32 (Some sx_S) <|>
  exact #AD $> Cvtop T_i64 Convert T_i32 (Some sx_U) <|>
  exact #AE $> Cvtop T_i64 Convert T_f32 (Some sx_S) <|>
  exact #AF $> Cvtop T_i64 Convert T_f32 (Some sx_U) <|>
  exact #B0 $> Cvtop T_i64 Convert T_f64 (Some sx_S) <|>
  exact #B1 $> Cvtop T_i64 Convert T_f64 (Some sx_U) <|>
  exact #B2 $> Cvtop T_f32 Convert T_i32 (Some sx_S) <|>
  exact #B3 $> Cvtop T_f32 Convert T_i32 (Some sx_U) <|>
  exact #B4 $> Cvtop T_f32 Convert T_i64 (Some sx_S) <|>
  exact #B5 $> Cvtop T_f32 Convert T_i64 (Some sx_U) <|>
  exact #B6 $> Cvtop T_f32 Convert T_f64 None <|>
  exact #B7 $> Cvtop T_f64 Convert T_i32 (Some sx_S) <|>
  exact #B8 $> Cvtop T_f64 Convert T_i32 (Some sx_U) <|>
  exact #B9 $> Cvtop T_f64 Convert T_i64 (Some sx_S) <|>
  exact #BA $> Cvtop T_f64 Convert T_i64 (Some sx_U) <|>
  exact #BB $> Cvtop T_f32 Convert T_f64 None <|>
  exact #BC $> Cvtop T_i32 Reinterpret T_f32 None <|>
  exact #BD $> Cvtop T_i64 Reinterpret T_f64 None <|>
  exact #BE $> Cvtop T_f32 Reinterpret T_i32 None <|>
  exact #BF $> Cvtop T_f64 Reinterpret T_i64 None.

Record Language (n : nat) : Type := MkLanguage
{ _be : w_parser basic_instruction n;
  _bes : w_parser (list basic_instruction) n;
}.

Arguments MkLanguage {_}.

Context
  {Tok : Type} {A B : Type} {n : nat}.

Definition language : [ Language ] := Fix Language (fun _ rec =>
  let bes_aux := Induction.map _bes _ rec in
  let block := exact #02 &> ((Block <$> block_type_as_function_type) <*> bes_aux) <& exact #0B in
  let loop := exact #03 &> ((Loop <$> block_type_as_function_type) <*> bes_aux) <& exact #0B in
  let if_rest :=
    (exact #0B $> nil) <|>
    ((exact #05 &> bes_aux) <& exact #0B) in
  let if_ := exact #04 &> ((If <$> block_type_as_function_type) <*> bes_aux <*> if_rest) in
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
  cmap tt (exact #0B).

Definition expr := list basic_instruction.

Definition expr_ {n} : w_parser (list basic_instruction) n :=
  extract bes n. (* TODO: is that right? *)

Definition byte_ {n} : w_parser Integers.Byte.int n :=
  anyTok.

Definition function_type_ {n} : w_parser function_type n :=
  exact #60 &> (prod_curry Tf <$> vec value_type_ <&> vec value_type_).

Record limits := Mk_limits { lim_min : nat; lim_max : option nat; }.

Definition limits_ {n} : w_parser limits n :=
  exact #00 &> ((fun min => Mk_limits min None) <$> u32_nat) <|>
  exact #01 &> ((fun min max => Mk_limits min (Some max)) <$> u32_nat) <*> u32_nat.

Inductive elem_type : Type :=
| elem_type_tt : elem_type (* TODO: am I interpreting the spec correctly? *).

Definition elem_type_ {n} : w_parser elem_type n :=
  exact #70 $> elem_type_tt.

Record table_type : Type := Mk_table_type {
  tt_limits : limits;
  tt_elem_type : elem_type;
}.

Definition table_type_ {n} : w_parser table_type n :=
  prod_curry Mk_table_type <$> (limits_ <&> elem_type_).

Record mem_type : Type := Mk_mem_type { mem_type_lims : limits }.

Definition mem_type_ {n} : w_parser mem_type n :=
Mk_mem_type <$> limits_.

Inductive import_desc : Type :=
| ID_func : nat -> import_desc
| ID_table : table_type -> import_desc
| ID_mem : mem_type -> import_desc
| ID_global : global_type -> import_desc.

Definition mut_ {n} : w_parser mutability n :=
  exact #00 $> T_immut <|>
  exact #01 $> T_mut.

Definition global_type_ {n} : w_parser global_type n :=
  ((fun x y => Build_global_type y x) <$> value_type_) <*> mut_.

Definition import_desc_ {n} : w_parser import_desc n :=
  exact #00 &> (extract_typeidx ID_func <$> typeidx_) <|>
  exact #01 &> (ID_table <$> table_type_) <|>
  exact #02 &> (ID_mem <$> mem_type_) <|>
  exact #03 &> (ID_global <$> global_type_).

Definition name := list Integers.Byte.int.

Record import : Type := Mk_import {
  imp_module : name;
  imp_name : name;
  imp_desc : import_desc;
}.

Definition import_ {n} : w_parser import n :=
  (Mk_import <$> vec byte_) <*> vec byte_ <*> import_desc_.

Record table := Mk_table { t_type : table_type }.

Definition table_ {n} : w_parser table n :=
  Mk_table <$> table_type_.

Definition mem := limits.

Record global2 : Type := {
  g_type : global_type;
  g_init : expr;
}.

Definition global2_ {n} : w_parser global2 n :=
  (Build_global2 <$> global_type_) <*> expr_.

Inductive export_desc : Type :=
| ED_func : nat -> export_desc
| ED_table : nat -> export_desc
| ED_mem : nat -> export_desc
| ED_global : nat -> export_desc.

Definition export_desc_ {n} : w_parser export_desc n :=
  exact #00 &> (ED_func <$> u32_nat) <|>
  exact #01 &> (ED_table <$> u32_nat) <|>
  exact #02 &> (ED_mem <$> u32_nat) <|>
  exact #03 &> (ED_global <$> u32_nat).

Record export : Type := {
  exp_name : name;
  exp_desc : export_desc;
}.

Definition export_ {n} : w_parser export n :=
  (Build_export <$> vec byte_) <*> export_desc_.

Record start := { start_func : nat; }.

Definition start_ {n} : w_parser start n :=
  Build_start <$> u32_nat.

Record element : Type := {
  elem_table : nat;
  elem_offset : expr;
  elem_init : list nat;
}.

Definition element_ {n} : w_parser element n :=
  (Build_element <$> u32_nat) <*> expr_ <*> vec u32_nat.

Record func : Type := {
  fc_locals : list value_type;
  fc_expr : expr;
}.

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

Record data : Type := {
  dt_data : nat;
  dt_offset : expr;
  dt_init : list Integers.Byte.int;
}.

Definition data_ {n} : w_parser data n :=
  (Build_data <$> u32_nat) <*> expr_ <*> vec byte_.

Inductive section : Type :=
| Sec_custom : list Integers.Byte.int -> section
| Sec_type : list function_type -> section
| Sec_import : list import -> section
| Sec_function : list typeidx -> section
| Sec_table : list table -> section
| Sec_memory : list mem -> section
| Sec_global : list global2 -> section
| Sec_export : list export -> section
| Sec_start : start -> section
| Sec_element : list element -> section
| Sec_code : list func -> section
| Sec_data : list data -> section.

Definition customsec {n} : w_parser (list Integers.Byte.int) n :=
  exact #00 &> vec byte_.

Definition typesec {n} : w_parser (list function_type) n :=
  exact #01 &> vec function_type_.

Definition importsec {n} : w_parser (list import) n :=
  exact #02 &> vec import_.

Definition funcsec {n} : w_parser (list typeidx) n :=
  exact #03 &> vec typeidx_.

Definition tablesec {n} : w_parser (list table) n :=
  exact #04 &>  vec table_.

Definition memsec {n} : w_parser (list mem) n :=
  exact #05 &> vec limits_.

Definition globalsec {n} : w_parser (list global2) n :=
  exact #06 &> vec global2_.

Definition exportsec {n} : w_parser (list export) n :=
  exact #07 &> vec export_.

Definition startsec {n} : w_parser start n :=
  exact #08 &> start_.

Definition elemsec {n} : w_parser (list element) n :=
  exact #09 &> vec element_.

Definition codesec {n} : w_parser (list func) n :=
  exact #0A &> vec code_.

Definition datasec {n} : w_parser (list data) n :=
  exact #0B &> (vec data_).

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
  (exact #00 &> exact #61 &> exact #73 &> exact #6D) $> tt.

Definition version {n} : w_parser unit n :=
  (exact #01 &> exact #00 &> exact #00 &> exact #00) $> tt.

Record func2 : Type := {
  fc2_type : typeidx;
  fc2_locals : list value_type;
  fc2_body : expr;
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

Inductive either (A B : Type) :=
| Left : A -> either A B
| Right : B -> either A B.

Definition module_ {n} : w_parser module n :=
(* TODO: this is missing all the customsecs! *)
  magic &>
  version &>
  (((fun functype import typeidx table mem global export secd_ecd =>
    match secd_ecd with
    | Left (start, (elem, code, data)) =>
      let func := nil in
      Build_module functype func table mem global elem data (Some start) import export
    | Right (elem, code, data) =>
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
  ((Left _ _ <$> (with_customsec_star_before startsec) <&> tail_) <|> (Right _ _ <$> tail_)).

End Language.


Inductive Singleton (A : Type) : A -> Type :=
  MkSingleton : forall a, Singleton A a.

Arguments Singleton {_}.
Arguments MkSingleton {_}.

Class Tokenizer (A : Type) : Type :=
  MkTokenizer { _tokenize : list Integers.Byte.int -> list A }.

Definition tokenize {A : Type} `{Tokenizer A} : list Integers.Byte.int -> list A := _tokenize.

Arguments MkTokenizer {_}.

Definition fromText {A : Type} `{Tokenizer A} (s : list Integers.Byte.int) : list A :=
  tokenize s.

Instance tokBytes : Tokenizer Integers.Byte.int := MkTokenizer (fun x => x).

Section Run.

Context
  {M : Type -> Type} `{RawMonad M} `{RawAlternative M} `{RawMonadRun M}
  {Tok : Type} `{Tokenizer Tok}
  {A : Type}.

Definition run : list Integers.Byte.int -> [ Parser (SizedList Tok) Tok M A ] -> option A := fun s p =>
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

Definition parse_wasm (bs : list Integers.Byte.int) : option basic_instruction :=
  run bs be.

Extraction "parse_wasm" parse_wasm.