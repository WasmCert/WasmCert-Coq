(** Parser for the binary Wasm format. **)
(* (C) J. Pichon - see LICENSE.txt *)
(* TODO: all the numeric stuff is in dire need of testing *)

(* Some documentation from the original agdarsec paper:
   gallais.github.io/pdf/agdarsec18.pdf
*)

From Wasm Require Import datatypes_properties typing.
From compcert Require Import Integers.
From parseque Require Import Parseque.
Require Import Strings.Byte.
Require Import leb128.
Require Import BinNat BinInt.
Require Import PeanoNat.

Notation "p $> b" := (cmap b p) (at level 59, right associativity).

Section Language.

Context
  {Toks : nat -> Type} `{Sized Toks byte}
  {M : Type -> Type} `{RawMonad M} `{RawAlternative M}.

Definition byte_parser A n := Parser Toks byte M A n.
Definition be_parser n := byte_parser basic_instruction n.

(* Given a parser, produce a new parser that also returns the number of tokens consumed by it. *)
Definition sized_parser {T: Type} {n} (f: byte_parser T n) : byte_parser (T * nat) n.
Proof.
  apply MkParser.
  intros m Hmlen toks.
  remember (runParser f Hmlen toks) as run_res.
  refine (_app _ _ _ run_res).
  refine (_pure _ _).
  intros ret; destruct ret as [value size Hsmall leftovers].
  exact (Success.MkSuccess (value, m - size) Hsmall leftovers).
Defined.

Definition assert_sized {T: Type} {n} (f: byte_parser T n) (constraint: nat -> bool) : byte_parser T n :=
  guardM
    (fun '(ret, sz) =>
       if constraint sz then Some ret
       else None)
    (sized_parser f).

Definition exact_byte (b : byte) {n} : byte_parser byte n :=
  guardM
    (fun b' =>
      if byte_eqb b' b then Some b'
      else None)
    anyTok.

Definition parse_u32_as_N {n} : byte_parser N n :=
  guardM
    (fun n => if (N.leb n 4294967295%N) then Some n
           else None)
  (assert_sized (extract parse_unsigned n) (fun sz => sz <=? 5)).

Definition assert_u32 {n} (k: N) : byte_parser N n :=
  guardM
    (fun parsed_n => if N.eqb parsed_n k then Some k else None)
    parse_u32_as_N.

Definition parse_s32 {n} : byte_parser Wasm_int.Int32.int n :=
  guardM
    (fun x => if (andb (Z.leb x 2147483647%Z)
                 (Z.leb (-2147483648)%Z x)) then
                  Some (Wasm_int.Int32.repr x)
                else None)
  (assert_sized (extract parse_signed n) (fun sz => sz <=? 5)).

Definition parse_s64 {n} : byte_parser Wasm_int.Int64.int n :=
  guardM
    (fun x => if (andb (Z.leb x 9223372036854775807%Z)
                 (Z.leb (-9223372036854775808)%Z x)) then
                  Some (Wasm_int.Int64.repr x)
                else None)
    (assert_sized (extract parse_signed n) (fun sz => sz <=? 10)).

Definition parse_vec_length {n} : byte_parser N n :=
  parse_u32_as_N.

(* Safe vector parsing, without going through nat.
   Also avoids hanging when the parameter is too large.
 *)
Fixpoint parse_vec_aux_positive {B} {n} (f: byte_parser B n) (p: positive) :
  byte_parser (list B) n :=
  match p with
  | xH => (fun x => cons x nil) <$> f
  | xO p' => (fun '(l1, l2) => List.app l1 l2) <$> (parse_vec_aux_positive f p' &>>= (fun _ => parse_vec_aux_positive f p'))
  | xI p' => (((fun '(h, (l1, l2)) => cons h (List.app l1 l2))) <$> (f &>>= (fun _ => (parse_vec_aux_positive f p' &>>= (fun _ => parse_vec_aux_positive f p')))))
  end.

Definition parse_vec_aux {B} {n} (f : byte_parser B n) (k : N)
  : byte_parser (list B) n:=  
  match k with
  | 0%N => fail (* nil *)
  | Npos p => parse_vec_aux_positive f p
  end.

(* parsing a length-indexed list *)
Definition parse_vec {B} {n} (f : byte_parser B n) : byte_parser (list B) n :=
  (fun len_list => 
     match len_list with
     | (_, Some xs) => xs
     | (_, None) => nil
     end) <$>
  (parse_vec_length &?>>= (fun k => parse_vec_aux f k)).

Definition parse_f32 {n} : byte_parser Wasm_float.FloatSize32.T n :=
  (fun bs => Floats.Float32.of_bits (Integers.Int.repr (common.Memdata.decode_int (List.map compcert_byte_of_byte bs)))) <$> (parse_vec_aux anyTok 4%N).

Definition parse_f64 {n} : byte_parser Wasm_float.FloatSize64.T n :=
  (fun bs => Floats.Float.of_bits (Integers.Int64.repr (common.Memdata.decode_int (List.map compcert_byte_of_byte bs)))) <$> (parse_vec_aux anyTok 8%N).

(* Kept as separate definitions in case a distincion is required in the future *)
Definition parse_labelidx {n} : byte_parser labelidx n :=
  parse_u32_as_N.

Definition parse_funcidx {n} : byte_parser funcidx n :=
  parse_u32_as_N.

Definition parse_tableidx {n} : byte_parser tableidx n :=
  parse_u32_as_N.

Definition parse_memidx {n} : byte_parser memidx n :=
  parse_u32_as_N.

Definition parse_typeidx {n} : byte_parser typeidx n :=
  parse_u32_as_N.

Definition parse_localidx {n} : byte_parser localidx n :=
  parse_u32_as_N.

Definition parse_globalidx {n} : byte_parser globalidx n :=
  parse_u32_as_N.

Definition parse_elemidx {n} : byte_parser elemidx n :=
  parse_u32_as_N.

Definition parse_dataidx {n} : byte_parser dataidx n :=
  parse_u32_as_N.

Definition parse_number_type {n} : byte_parser number_type n :=
  (exact_byte x7f $> T_i32) <|>
  (exact_byte x7e $> T_i64) <|>
  (exact_byte x7d $> T_f32) <|>
  (exact_byte x7c $> T_f64).

Definition parse_vector_type {n} : byte_parser vector_type n :=
  (exact_byte x7b $> T_v128).

Definition parse_reference_type {n} : byte_parser reference_type n :=
  (exact_byte x70 $> T_funcref) <|>
  (exact_byte x6f $> T_externref).

Definition parse_value_type {n} : byte_parser value_type n :=
  T_num <$> parse_number_type <|>
  T_vec <$> parse_vector_type <|>
  T_ref <$> parse_reference_type.

Definition parse_block_type {n} : byte_parser block_type n :=
  (exact_byte x40 $> BT_valtype None) <|>
  (fun t => BT_valtype (Some t)) <$> parse_value_type <|>
  BT_id <$> parse_typeidx. (* TODO: needs to be s33? *)


Definition parse_unreachable {n} : byte_parser basic_instruction n :=
  exact_byte x00 $> BI_unreachable.

Definition parse_nop {n} : byte_parser basic_instruction n :=
  exact_byte x01 $> BI_nop.

(* Might be better to keep these redundant conversions for typechecking in case; it's always easy to erase them than to recover them *)
Definition extract_labelidx {B} (f : N -> B) (x : labelidx) : B :=
  f x.

Definition extract_funcidx {B} (f : N -> B) (x : funcidx) : B :=
  f x.

Definition extract_typeidx {B} (f : N -> B) (x : typeidx) : B :=
  f x.

Definition extract_localidx {B} (f : N -> B) (x : localidx) : B :=
  f x.

Definition extract_globalidx {B} (f : N -> B) (x : globalidx) : B :=
  f x.

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
  exact_byte x11 &>
  ((BI_call_indirect <$> parse_typeidx) <*> parse_tableidx).


(* Reference instructions *)
Definition parse_ref_null {n}: byte_parser basic_instruction n :=
  exact_byte xd0 &> (BI_ref_null <$> parse_reference_type).

Definition parse_ref_is_null {n} : byte_parser basic_instruction n :=
  exact_byte xd1 $> BI_ref_is_null.

Definition parse_ref_func {n} : byte_parser basic_instruction n :=
  exact_byte xd2 &> (BI_ref_func <$> parse_funcidx).

Definition parse_reference_instruction {n} : byte_parser basic_instruction n :=
  parse_ref_null <|>
  parse_ref_is_null <|>
  parse_ref_func.


(* Variable instructions *)
Definition parse_drop {n} : byte_parser basic_instruction n :=
  exact_byte x1a $> BI_drop.

Definition parse_select_None {n} : byte_parser basic_instruction n :=
  exact_byte x1b $> (BI_select None).

Definition parse_select_Some {n} : byte_parser basic_instruction n :=
  exact_byte x1c &>
  ((fun vts => BI_select (Some vts)) <$> parse_vec parse_value_type).

Definition parse_parametric_instruction {n} : byte_parser basic_instruction n :=
  parse_drop <|>
  parse_select_None <|>
  parse_select_Some.

Definition parse_local_get {n} : byte_parser basic_instruction n :=
  exact_byte x20 &> (extract_localidx BI_local_get <$> parse_localidx).

Definition parse_local_set {n} : byte_parser basic_instruction n :=
  exact_byte x21 &> (extract_localidx BI_local_set <$> parse_localidx).

Definition parse_local_tee {n} : byte_parser basic_instruction n :=
  exact_byte x22 &> (extract_localidx BI_local_tee <$> parse_localidx).

Definition parse_global_get {n} : byte_parser basic_instruction n :=
  exact_byte x23 &> (extract_globalidx BI_global_get <$> parse_globalidx).

Definition parse_global_set {n} : byte_parser basic_instruction n :=
  exact_byte x24 &> (extract_globalidx BI_global_set <$> parse_globalidx).

Definition parse_variable_instruction {n} : byte_parser basic_instruction n :=
  parse_local_get <|>
  parse_local_set <|>
  parse_local_tee <|>
  parse_global_get <|>
  parse_global_set.

(* Table instructions *)
Definition parse_table_get {n} : byte_parser basic_instruction n :=
  exact_byte x25 &> (BI_table_get <$> parse_tableidx).

Definition parse_table_set {n} : byte_parser basic_instruction n :=
  exact_byte x26 &> (BI_table_set <$> parse_tableidx).

(* Order of the arguments is reversed in the binary format *)
Definition parse_table_init {n} : byte_parser basic_instruction n :=
  exact_byte xfc &> assert_u32 12%N &> (((fun y x => BI_table_init x y) <$> parse_elemidx) <*> parse_tableidx).

Definition parse_elem_drop {n} : byte_parser basic_instruction n :=
  exact_byte xfc &> assert_u32 13%N &> (BI_elem_drop <$> parse_elemidx).

Definition parse_table_copy {n} : byte_parser basic_instruction n :=
  exact_byte xfc &> assert_u32 14%N &> ((BI_table_copy <$> parse_tableidx) <*> parse_tableidx).

Definition parse_table_grow {n} : byte_parser basic_instruction n :=
  exact_byte xfc &> assert_u32 15%N &> (BI_table_grow <$> parse_tableidx).

Definition parse_table_size {n} : byte_parser basic_instruction n :=
  exact_byte xfc &> assert_u32 16%N &> (BI_table_size <$> parse_tableidx).

Definition parse_table_fill {n} : byte_parser basic_instruction n :=
  exact_byte xfc &> assert_u32 17%N &> (BI_table_fill <$> parse_tableidx).

Definition parse_table_instruction {n}: byte_parser basic_instruction n :=
  parse_table_get <|>
  parse_table_set <|>
  parse_table_init <|>
  parse_elem_drop <|>
  parse_table_copy <|>
  parse_table_grow <|>
  parse_table_size <|>
  parse_table_fill.

Definition parse_alignment_exponent {n} : byte_parser N n :=
  parse_u32_as_N.

Definition parse_static_offset {n} : byte_parser N n :=
  parse_u32_as_N.

Definition parse_memarg {n} : byte_parser memarg n :=
  (fun ao =>
     match ao with
     | (a, o) => {| memarg_offset := o; memarg_align := a |}
     end) <$>
    (parse_alignment_exponent <&> parse_static_offset).

Definition parse_i32_load {n} : byte_parser basic_instruction n :=
  exact_byte x28 &> ((BI_load T_i32 None) <$> parse_memarg).

Definition parse_i64_load {n} : byte_parser basic_instruction n :=
  exact_byte x29 &> ((BI_load T_i64 None) <$> parse_memarg).

Definition parse_f32_load {n} : byte_parser basic_instruction n :=
  exact_byte x2a &> ((BI_load T_f32 None) <$> parse_memarg).

Definition parse_f64_load {n} : byte_parser basic_instruction n :=
  exact_byte x2b &> ((BI_load T_f64 None) <$> parse_memarg).

Definition parse_i32_load8_s {n} : byte_parser basic_instruction n :=
  exact_byte x2c &> ((BI_load T_i32 (Some (Tp_i8, SX_S))) <$> parse_memarg).

Definition parse_i32_load8_u {n} : byte_parser basic_instruction n :=
  exact_byte x2d &> ((BI_load T_i32 (Some (Tp_i8, SX_U))) <$> parse_memarg).

Definition parse_i32_load16_s {n} : byte_parser basic_instruction n :=
  exact_byte x2e &> ((BI_load T_i32 (Some (Tp_i16, SX_S))) <$> parse_memarg).

Definition parse_i32_load16_u {n} : byte_parser basic_instruction n :=
  exact_byte x2f &> ((BI_load T_i32 (Some (Tp_i16, SX_U))) <$> parse_memarg).

Definition parse_i64_load8_s {n} : byte_parser basic_instruction n :=
  exact_byte x30 &> ((BI_load T_i64 (Some (Tp_i8, SX_S))) <$> parse_memarg).

Definition parse_i64_load8_u {n} : byte_parser basic_instruction n :=
  exact_byte x31 &> ((BI_load T_i64 (Some (Tp_i8, SX_U))) <$> parse_memarg).

Definition parse_i64_load16_s {n} : byte_parser basic_instruction n :=
  exact_byte x32 &> ((BI_load T_i64 (Some (Tp_i16, SX_S))) <$> parse_memarg).

Definition parse_i64_load16_u {n} : byte_parser basic_instruction n :=
  exact_byte x33 &> ((BI_load T_i64 (Some (Tp_i16, SX_U))) <$> parse_memarg).

Definition parse_i64_load32_s {n} : byte_parser basic_instruction n :=
  exact_byte x34 &> ((BI_load T_i64 (Some (Tp_i32, SX_S))) <$> parse_memarg).

Definition parse_i64_load32_u {n} : byte_parser basic_instruction n :=
  exact_byte x35 &> ((BI_load T_i64 (Some (Tp_i32, SX_U))) <$> parse_memarg).

Definition parse_i32_store {n} : byte_parser basic_instruction n :=
  exact_byte x36 &> ((BI_store T_i32 None) <$> parse_memarg).

Definition parse_i64_store {n} : byte_parser basic_instruction n :=
  exact_byte x37 &> ((BI_store T_i64 None) <$> parse_memarg).

Definition parse_f32_store {n} : byte_parser basic_instruction n :=
  exact_byte x38 &> ((BI_store T_f32 None) <$> parse_memarg).

Definition parse_f64_store {n} : byte_parser basic_instruction n :=
  exact_byte x39 &> ((BI_store T_f64 None) <$> parse_memarg).

Definition parse_i32_store8 {n} : byte_parser basic_instruction n :=
  exact_byte x3a &> ((BI_store T_i32 (Some Tp_i8)) <$> parse_memarg).

Definition parse_i32_store16 {n} : byte_parser basic_instruction n :=
  exact_byte x3b &> ((BI_store T_i32 (Some Tp_i16)) <$> parse_memarg).

Definition parse_i64_store8 {n} : byte_parser basic_instruction n :=
  exact_byte x3c &> ((BI_store T_i64 (Some Tp_i8)) <$> parse_memarg).

Definition parse_i64_store16 {n} : byte_parser basic_instruction n :=
  exact_byte x3d &> ((BI_store T_i64 (Some Tp_i16)) <$> parse_memarg).

Definition parse_i64_store32 {n} : byte_parser basic_instruction n :=
  exact_byte x3e &> ((BI_store T_i64 (Some Tp_i32)) <$> parse_memarg).

Definition parse_memory_size {n} : byte_parser basic_instruction n :=
  exact_byte x3f &> (exact_byte x00 $> BI_memory_size).

Definition parse_memory_grow {n} : byte_parser basic_instruction n :=
  exact_byte x40 &> (exact_byte x00 $> BI_memory_grow).

Definition parse_memory_init {n} : byte_parser basic_instruction n :=
  exact_byte xfc &> assert_u32 8%N &> (((fun x _ => BI_memory_init x) <$> parse_dataidx) <*> exact_byte x00).

Definition parse_data_drop {n} : byte_parser basic_instruction n :=
  exact_byte xfc &> assert_u32 9%N &> ((fun x => BI_data_drop x) <$> parse_dataidx).

(* Defined in this way so that it's easier to add multimemory in the future *)
Definition parse_memory_copy {n} : byte_parser basic_instruction n :=
  exact_byte xfc &> assert_u32 10%N &> (((fun _ _ => BI_memory_copy) <$> exact_byte x00) <*> exact_byte x00).

Definition parse_memory_fill {n} : byte_parser basic_instruction n :=
  exact_byte xfc &> assert_u32 11%N &> ((fun _ => BI_memory_fill) <$> exact_byte x00).

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
  parse_memory_grow <|>
  parse_memory_init <|>
  parse_data_drop <|>
  parse_memory_copy <|>
  parse_memory_fill.

Definition parse_i32_const {n} : be_parser n :=
  exact_byte x41 &> ((fun x => BI_const_num (VAL_int32 x)) <$> parse_s32).

Definition parse_i64_const {n} : be_parser n :=
  exact_byte x42 &> ((fun x => BI_const_num (VAL_int64 x)) <$> parse_s64).

Definition parse_f32_const {n} : be_parser n :=
  exact_byte x43 &> ((fun x => BI_const_num (VAL_float32 x)) <$> parse_f32).

Definition parse_f64_const {n} : be_parser n :=
  exact_byte x44 &> ((fun x => BI_const_num (VAL_float64 x)) <$> parse_f64).

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

  exact_byte xa7 $> BI_cvtop T_i32 CVO_wrap T_i64 None <|>  (* i32.wrap_i64 *)
  exact_byte xa8 $> BI_cvtop T_i32 CVO_trunc T_f32 (Some SX_S) <|>  (* i32.trunc_f32_s *)
  exact_byte xa9 $> BI_cvtop T_i32 CVO_trunc T_f32 (Some SX_U) <|>  (* i32.trunc_f32_u *)
  exact_byte xaa $> BI_cvtop T_i32 CVO_trunc T_f64 (Some SX_S) <|>  (* i32.trunc_f64_s *)
  exact_byte xab $> BI_cvtop T_i32 CVO_trunc T_f64 (Some SX_U) <|>  (* i32.trunc_f64_u *)
  exact_byte xac $> BI_cvtop T_i64 CVO_extend T_i32 (Some SX_S) <|>  (* i64.extend_i32_s *)
  exact_byte xad $> BI_cvtop T_i64 CVO_extend T_i32 (Some SX_U) <|>  (* i64.extend_i32_u *)
  exact_byte xae $> BI_cvtop T_i64 CVO_trunc T_f32 (Some SX_S) <|>  (* i64.trunc_f32_s *)
  exact_byte xaf $> BI_cvtop T_i64 CVO_trunc T_f32 (Some SX_U) <|>  (* i64.trunc_f32_u *)
  exact_byte xb0 $> BI_cvtop T_i64 CVO_trunc T_f64 (Some SX_S) <|>  (* i64.trunc_f64_s *)
  exact_byte xb1 $> BI_cvtop T_i64 CVO_trunc T_f64 (Some SX_U) <|>  (* i64.trunc_f64_u *)
  exact_byte xb2 $> BI_cvtop T_f32 CVO_convert T_i32 (Some SX_S) <|>  (* f32.convert_i32_s *)
  exact_byte xb3 $> BI_cvtop T_f32 CVO_convert T_i32 (Some SX_U) <|>  (* f32.convert_i32_u *)
  exact_byte xb4 $> BI_cvtop T_f32 CVO_convert T_i64 (Some SX_S) <|>  (* f32.convert_i64_s *)
  exact_byte xb5 $> BI_cvtop T_f32 CVO_convert T_i64 (Some SX_U) <|>  (* f32.convert_i64_u *)
  exact_byte xb6 $> BI_cvtop T_f32 CVO_demote T_f64 None <|>         (* f32.demote_f64 *)
  exact_byte xb7 $> BI_cvtop T_f64 CVO_convert T_i32 (Some SX_S) <|>  (* f64.convert_i32_s *)
  exact_byte xb8 $> BI_cvtop T_f64 CVO_convert T_i32 (Some SX_U) <|>  (* f64.convert_i32_u *)
  exact_byte xb9 $> BI_cvtop T_f64 CVO_convert T_i64 (Some SX_S) <|>  (* f64.convert_i64_s *)
  exact_byte xba $> BI_cvtop T_f64 CVO_convert T_i64 (Some SX_U) <|>  (* f64.convert_i64_u *)
  exact_byte xbb $> BI_cvtop T_f64 CVO_promote T_f32 None <|>         (* f64.promote_f32 *)
  exact_byte xbc $> BI_cvtop T_i32 CVO_reinterpret T_f32 None <|>     (* i32.reinterpret_f32 *)
  exact_byte xbd $> BI_cvtop T_i64 CVO_reinterpret T_f64 None <|>     (* i64.reinterpret_f64 *)
  exact_byte xbe $> BI_cvtop T_f32 CVO_reinterpret T_i32 None <|>     (* f32.reinterpret_i32 *)
  exact_byte xbf $> BI_cvtop T_f64 CVO_reinterpret T_i64 None <|>     (* f64.reinterpret_i64 *)
  
  exact_byte xc0 $> BI_unop T_i32 (Unop_extend 8%N) <|>      (* i32.extend8_s *)
  exact_byte xc1 $> BI_unop T_i32 (Unop_extend 16%N) <|>     (* i32.extend16_s *)
  exact_byte xc2 $> BI_unop T_i64 (Unop_extend 8%N) <|>      (* i64.extend8_s *)
  exact_byte xc3 $> BI_unop T_i64 (Unop_extend 16%N) <|>     (* i64.extend16_s *)
  exact_byte xc4 $> BI_unop T_i64 (Unop_extend 32%N) <|>     (* i64.extend32_s *)

  (* inn.trunc_sat_fmm_sx *)
  (exact_byte xfc &> assert_u32 0%N $> (BI_cvtop T_i32 CVO_trunc_sat T_f32 (Some SX_S))) <|>
  (exact_byte xfc &> assert_u32 1%N $> (BI_cvtop T_i32 CVO_trunc_sat T_f32 (Some SX_U))) <|>
  (exact_byte xfc &> assert_u32 2%N $> (BI_cvtop T_i32 CVO_trunc_sat T_f64 (Some SX_S))) <|>
  (exact_byte xfc &> assert_u32 3%N $> (BI_cvtop T_i32 CVO_trunc_sat T_f64 (Some SX_U))) <|>
  (exact_byte xfc &> assert_u32 4%N $> (BI_cvtop T_i64 CVO_trunc_sat T_f32 (Some SX_S))) <|>
  (exact_byte xfc &> assert_u32 5%N $> (BI_cvtop T_i64 CVO_trunc_sat T_f32 (Some SX_U))) <|>
  (exact_byte xfc &> assert_u32 6%N $> (BI_cvtop T_i64 CVO_trunc_sat T_f64 (Some SX_S))) <|>
  (exact_byte xfc &> assert_u32 7%N $> (BI_cvtop T_i64 CVO_trunc_sat T_f64 (Some SX_U))).

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
    exact_byte x02 &> ((BI_block <$> parse_block_type) <*> bes_end_with_x0b_aux) in
  let parse_loop :=
    exact_byte x03 &> ((BI_loop <$> parse_block_type) <*> bes_end_with_x0b_aux) in
  let parse_if_body :=
    (((fun x y => (x, y)) <$> parse_block_type) <*> bes_end_with_x0b_or_x05_ctd_aux) in
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
    parse_reference_instruction <|>
    parse_parametric_instruction <|>
    parse_variable_instruction <|>
    parse_table_instruction <|>
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
  parse_bes_end_with_x0b n.

Definition parse_function_type {n} : byte_parser function_type n :=
  exact_byte x60 &> (uncurry Tf <$> parse_vec parse_value_type <&> parse_vec parse_value_type).

Definition parse_limits {n} : byte_parser limits n :=
  exact_byte x00 &> ((fun min => {| lim_min := min; lim_max := None |}) <$> parse_u32_as_N) <|>
  (exact_byte x01 &> ((fun min max => {| lim_min := min; lim_max := Some max |}) <$> parse_u32_as_N) <*> parse_u32_as_N).

Definition parse_table_type {n} : byte_parser table_type n :=
  ((fun ety lims => {| tt_limits := lims; tt_elem_type := ety |}) <$> parse_reference_type) <*> parse_limits.

Definition parse_memory_type {n} : byte_parser memory_type n :=
  (fun lim => lim) <$> parse_limits.

Definition parse_mut {n} : byte_parser mutability n :=
  exact_byte x00 $> MUT_const <|>
  exact_byte x01 $> MUT_var.

Definition parse_global_type {n} : byte_parser global_type n :=
  ((fun x y => Build_global_type y x) <$> parse_value_type) <*> parse_mut.

Definition parse_import_desc {n} : byte_parser module_import_desc n :=
  exact_byte x00 &> (extract_typeidx MID_func <$> parse_typeidx) <|>
  exact_byte x01 &> (MID_table <$> parse_table_type) <|>
  exact_byte x02 &> (MID_mem <$> parse_memory_type) <|>
  exact_byte x03 &> (MID_global <$> parse_global_type).

Definition parse_module_import {n} : byte_parser module_import n :=
  ((fun modul name desc => {| imp_module := modul; imp_name := name; imp_desc := desc; |}) <$> parse_vec anyTok) <*>
  parse_vec anyTok <*> parse_import_desc.

Definition parse_module_global {n} : byte_parser module_global n :=
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

Definition parse_elemkind {n}: byte_parser reference_type n :=
  exact_byte x00 $> T_funcref.

(* Slightly messy, but so is the spec *)
(* https://webassembly.github.io/spec/core/binary/modules.html#element-section *)
Definition parse_module_element_0 {n} : byte_parser module_element n :=
  ((fun es (fids: list funcidx) => {| modelem_type := T_funcref; modelem_init := List.map (fun y => cons (BI_ref_func y) nil) fids; modelem_mode := ME_active 0%N es; |}) <$> parse_expr) <*> parse_vec parse_funcidx.

Definition parse_module_element_1 {n} : byte_parser module_element n :=
  ((fun t (fids: list funcidx) => {| modelem_type := t; modelem_init := List.map (fun y => cons (BI_ref_func y) nil) fids; modelem_mode := ME_passive; |}) <$> parse_elemkind) <*> parse_vec parse_funcidx.

Definition parse_module_element_2 {n} : byte_parser module_element n :=
  ((((fun (x: tableidx) es t (fids: list funcidx) => {| modelem_type := t; modelem_init := List.map (fun y => cons (BI_ref_func y) nil) fids; modelem_mode := ME_active x es; |}) <$> parse_tableidx) <*> parse_expr) <*> parse_elemkind) <*> parse_vec parse_funcidx.

Definition parse_module_element_3 {n} : byte_parser module_element n :=
  ((fun t (fids: list funcidx) => {| modelem_type := t; modelem_init := List.map (fun y => cons (BI_ref_func y) nil) fids; modelem_mode := ME_declarative; |}) <$> parse_elemkind) <*> parse_vec parse_funcidx.

Definition parse_module_element_4 {n} : byte_parser module_element n :=
  ((fun es els => {| modelem_type := T_funcref; modelem_init := els; modelem_mode := ME_active 0%N es; |}) <$> parse_expr) <*> parse_vec parse_expr.

Definition parse_module_element_5 {n} : byte_parser module_element n :=
  ((fun t els => {| modelem_type := t; modelem_init := els; modelem_mode := ME_passive; |}) <$> parse_reference_type) <*> parse_vec parse_expr.

Definition parse_module_element_6 {n} : byte_parser module_element n :=
  ((((fun (x: tableidx) es t els => {| modelem_type := t; modelem_init := els; modelem_mode := ME_active x es; |}) <$> parse_tableidx) <*> parse_expr) <*> parse_reference_type) <*> parse_vec parse_expr.

Definition parse_module_element_7 {n} : byte_parser module_element n :=
  ((fun t els => {| modelem_type := t; modelem_init := els; modelem_mode := ME_declarative; |}) <$> parse_reference_type) <*> parse_vec parse_expr.

Definition parse_module_element {n}: byte_parser module_element n :=
  assert_u32 0%N &> parse_module_element_0 <|>
  assert_u32 1%N &> parse_module_element_1 <|>
  assert_u32 2%N &> parse_module_element_2 <|>
  assert_u32 3%N &> parse_module_element_3 <|>
  assert_u32 4%N &> parse_module_element_4 <|>
  assert_u32 5%N &> parse_module_element_5 <|>
  assert_u32 6%N &> parse_module_element_6 <|>
  assert_u32 7%N &> parse_module_element_7.

Definition parse_N_value_type {n} : byte_parser (list value_type) n :=
  ((fun k t => List.repeat t (N.to_nat k)) <$> parse_u32_as_N) <*> parse_value_type.

Definition parse_locals {n} : byte_parser (list value_type) n :=
  (fun tss => tss) <$> parse_N_value_type.

(* Spec defines code and functypes separately *)
Definition module_func_without_type : Type := (list value_type) * expr.

Definition parse_code_func {n} : byte_parser module_func_without_type n :=
  ((fun locals e => (List.concat locals, e)) <$> parse_vec parse_locals) <*> parse_expr.

Definition parse_code {n} : byte_parser module_func_without_type n :=
  guardM
    (fun sf =>
      match sf with
      (* TODO: we are supposed to check that the size matches *)
      (* There's no obvious function in Parseque that returns the number of tokens conumed *)
      | (s, f) => (* if Nat.eqb s (func_size f) then *) Some f (* else None *)
      end)
    (parse_u32_as_N <&> parse_code_func).

Definition parse_module_table {n} : byte_parser module_table n :=
  (fun tty => {| modtab_type := tty |}) <$> parse_table_type.

Definition parse_module_mem {n} : byte_parser module_mem n :=
  (fun tty => {| modmem_type := tty |}) <$> parse_memory_type.

Definition parse_module_data_0 {n} : byte_parser module_data n :=
  ((fun es (init: list byte) =>
      {| moddata_init := List.map compcert_byte_of_byte init; moddata_mode := MD_active 0%N es; |})
     <$> parse_expr) <*> parse_vec anyTok.

Definition parse_module_data_1 {n} : byte_parser module_data n :=
  (fun (init: list byte) =>
     {| moddata_init := List.map compcert_byte_of_byte init; moddata_mode := MD_passive; |})
    <$> parse_vec anyTok.

Definition parse_module_data_2 {n} : byte_parser module_data n :=
  (((fun x es (init: list byte) =>
       {| moddata_init := List.map compcert_byte_of_byte init; moddata_mode := MD_active x es; |})
      <$> parse_memidx) <*> parse_expr) <*> parse_vec anyTok.

Definition parse_module_data {n} : byte_parser module_data n :=
  assert_u32 0%N &> parse_module_data_0 <|>
  assert_u32 1%N &> parse_module_data_1 <|>
  assert_u32 2%N &> parse_module_data_2.

Definition parse_name {n} : byte_parser name n :=
  parse_vec anyTok.

Definition parse_customsec {n} : byte_parser (name * list byte) n :=
  exact_byte x00 &>
    ((fun '(name, _, obs) =>
       match obs with
       | Some bs => (name, bs)
       | None => (name, nil)
       end
    ) <$>
    (parse_u32_as_N >>=
    (fun sz_sec =>
       (sized_parser parse_name) &?>>=
         (fun '(name, sz_name) =>
            let sz_leftover := (N.sub sz_sec (N.of_nat sz_name)) in
            parse_vec_aux anyTok sz_leftover
         )))).
         
(* Low priority: check that the sections have the correct byte sizes? *)
Definition parse_typesec {n} : byte_parser (list function_type) n :=
  exact_byte x01 &> parse_u32_as_N &> parse_vec parse_function_type.

Definition parse_importsec {n} : byte_parser (list module_import) n :=
  exact_byte x02 &> parse_u32_as_N &> parse_vec parse_module_import.

Definition parse_funcsec {n} : byte_parser (list typeidx) n :=
  exact_byte x03 &> parse_u32_as_N &> parse_vec parse_typeidx.

Definition parse_tablesec {n} : byte_parser (list module_table) n :=
  exact_byte x04 &> parse_u32_as_N &> parse_vec parse_module_table.

Definition parse_memsec {n} : byte_parser (list module_mem) n :=
  exact_byte x05 &> parse_u32_as_N &> parse_vec parse_module_mem.

Definition parse_globalsec {n} : byte_parser (list module_global) n :=
  exact_byte x06 &> parse_u32_as_N &> parse_vec parse_module_global.

Definition parse_exportsec {n} : byte_parser (list module_export) n :=
  exact_byte x07 &> parse_u32_as_N &> parse_vec parse_module_export.

Definition parse_startsec {n} : byte_parser module_start n :=
  exact_byte x08 &> parse_u32_as_N &> parse_module_start.

Definition parse_elemsec {n} : byte_parser (list module_element) n :=
  exact_byte x09 &> parse_u32_as_N &> parse_vec parse_module_element.

Definition parse_codesec {n} : byte_parser (list module_func_without_type) n :=
  exact_byte x0a &> parse_u32_as_N &> parse_vec parse_code.

Definition parse_datasec {n} : byte_parser (list module_data) n :=
  exact_byte x0b &> parse_u32_as_N &> parse_vec parse_module_data.

Definition parse_datacountsec {n} : byte_parser N n :=
  exact_byte x0c &> parse_u32_as_N &> parse_u32_as_N.

Definition parse_magic {n} : byte_parser unit n :=
  (exact_byte x00 &> exact_byte x61 &> exact_byte x73 &> exact_byte x6d) $> tt.

Definition parse_version {n} : byte_parser unit n :=
  (exact_byte x01 &> exact_byte x00 &> exact_byte x00 &> exact_byte x00) $> tt.

Definition parse_customsec_forget {A n} : byte_parser (A -> A) n :=
  (fun _ x => x) <$> parse_customsec.

Definition parse_with_customsec_star_before {A : Type} {n} f :=
  @iterater _ _ _ _ _ _ _ _ _ A n parse_customsec_forget f.

Definition parse_with_customsec_star_after {A : Type} {n} f :=
  @iteratel _ _ _ _ _ _ _ _ _ A n f parse_customsec_forget.

Record parsing_module : Type := {
  pmod_types : list function_type;
  pmod_funcs : list typeidx;
  pmod_tables : list module_table;
  pmod_mems : list module_mem;
  pmod_globals : list module_global;
  pmod_elems : list module_element;
  pmod_datas : list module_data;
  pmod_start : option module_start;
  pmod_imports : list module_import;
  pmod_exports : list module_export;
  pmod_code : list module_func_without_type;
  }.

Definition parse_typesec_wrapper {n} : byte_parser (list function_type) n :=
  (parse_with_customsec_star_before parse_typesec).

Definition parse_importsec_wrapper {n} : byte_parser (list module_import) n :=
  (parse_with_customsec_star_before parse_importsec).

Definition parse_funcsec_wrapper {n} : byte_parser (list typeidx) n :=
  (parse_with_customsec_star_before parse_funcsec).

Definition parse_tablesec_wrapper {n} : byte_parser (list module_table) n :=
  (parse_with_customsec_star_before parse_tablesec).

Definition parse_memsec_wrapper {n} : byte_parser (list module_mem) n :=
  (parse_with_customsec_star_before parse_memsec).

Definition parse_globalsec_wrapper {n} : byte_parser (list module_global) n :=
  (parse_with_customsec_star_before parse_globalsec).

Definition parse_exportsec_wrapper {n} : byte_parser (list module_export) n :=
  (parse_with_customsec_star_before parse_exportsec).

Definition parse_startsec_wrapper {n} : byte_parser module_start n :=
  (parse_with_customsec_star_before parse_startsec).

Definition parse_elemsec_wrapper {n} : byte_parser (list module_element) n :=
  (parse_with_customsec_star_before parse_elemsec).

Definition parse_datacountsec_wrapper {n} : byte_parser N n :=
  (parse_with_customsec_star_before parse_datacountsec).

Definition parse_codesec_wrapper {n} : byte_parser (list module_func_without_type) n :=
  (parse_with_customsec_star_before parse_codesec).

Definition parse_datasec_wrapper {n} : byte_parser (list module_data) n :=
  (parse_with_customsec_star_before parse_datasec).

Definition parse_module_end {n} : byte_parser unit n :=
  (parse_with_customsec_star_before (@fail _ _ _ _ _ _ unit _)) $> tt.

Definition option_to_list {T: Type} (ol: option (list T)) : list T :=
  match ol with
  | Some l => l
  | None => nil 
  end.

Definition datacount_agree (len: N) (ocount: option N) : bool :=
  match ocount with
  | Some n => N.eqb len n
  | None => true
  end.

Definition parse_module_sections_after {n} {A} (f: byte_parser A n) : byte_parser module n :=
  guardM
  (fun results =>
     match results with
     | (_, otypes, oimports, ofts, otables, omems, oglobals, oexports, ostart, oelems, odatacount, ocodes, odatas) =>
         let types := option_to_list otypes in
         let imports := option_to_list oimports in
         let fts := option_to_list ofts in
         let tables := option_to_list otables in
         let mems := option_to_list omems in
         let globals := option_to_list oglobals in
         let exports := option_to_list oexports in
         let elems := option_to_list oelems in
         let codes := option_to_list ocodes in
         let datas := option_to_list odatas in
   (* Check that the information across different sections are consistent *)
         if (Nat.eqb (List.length fts) (List.length codes)) then
           if (datacount_agree (N.of_nat (List.length datas)) odatacount) then
             Some {|
               mod_types := types;
               mod_funcs :=
                 List.map
                   (fun '(a, (b, c)) =>
                      {| modfunc_type := a; modfunc_locals := b; modfunc_body := c |})
                   (List.combine fts codes);
               mod_tables := tables;
               mod_mems := mems;
               mod_globals := globals;
               mod_elems := elems;
               mod_datas := datas;
               mod_start := ostart;
               mod_imports := imports;
               mod_exports := exports
             |}
           else None
         else None
     end
  )
  (parse_with_customsec_star_after
  (* "<&?>" is right associative, but we want the other way round here *)
  (((((((((((((f <&?>
  parse_typesec_wrapper) <&?>
  parse_importsec_wrapper) <&?>
  parse_funcsec_wrapper) <&?>
  parse_tablesec_wrapper) <&?>
  parse_memsec_wrapper) <&?>
  parse_globalsec_wrapper) <&?>
  parse_exportsec_wrapper) <&?>
  parse_startsec_wrapper) <&?>
  parse_elemsec_wrapper) <&?>
  parse_datacountsec_wrapper) <&?>
  parse_codesec_wrapper) <&?>
  parse_datasec_wrapper))).

Definition parse_module {n} : byte_parser module n :=
  parse_module_sections_after
    (parse_magic &>
     parse_version).

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
  run bs (fun n => parse_module).
