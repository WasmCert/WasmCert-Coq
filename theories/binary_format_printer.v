(** Wasm AST to binary.
Breaks non-determinism ties; see binary_format_spec.v for the spec. *)
Require Import datatypes_properties numerics.
From compcert Require Integers.
Require Import Strings.Byte.
Require leb128.
Require Import Coq.Arith.Le.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Definition binary_of_value_type (t : value_type) : byte :=
  match t with
  | T_i32 => x7f
  | T_i64 => x7e
  | T_f32 => x7d
  | T_f64 => x7c
  end.

Definition binary_of_block_type_aux (bt : list value_type) : list byte :=
  match bt with
  | nil => x40 :: nil
  | cons t nil => binary_of_value_type t :: nil
  | _ => (* TODO: this should never occur *) nil
  end.

Definition binary_of_block_type (ft : function_type) : list byte :=
  match ft with
  | Tf nil rt => binary_of_block_type_aux rt
  | _ => (* TODO: should never happen *) nil
  end.

Definition binary_of_u32_nat (n : nat) : list byte :=
  leb128.encode_unsigned (BinNatDef.N.of_nat n).

Definition binary_of_idx n := binary_of_u32_nat n.

Definition binary_of_vec {A} (f : A -> list byte) (es : list A) : list byte :=
  (binary_of_u32_nat (List.length es)) ++ (List.concat (List.map f es)).

Definition binary_of_memarg a o : list byte :=
  binary_of_u32_nat a ++ binary_of_u32_nat o.

Definition binary_of_i32 (x : i32) : list byte :=
  leb128.encode_signed (Wasm_int.Int32.signed x).

Definition binary_of_i64 (x : i64) : list byte :=
  leb128.encode_signed (Wasm_int.Int64.signed x).

Definition binary_of_f32 (x : f32) : list byte :=
  List.map byte_of_compcert_byte (serialise_f32 x).

Definition binary_of_f64 (x : f64) : list byte :=
  List.map byte_of_compcert_byte (serialise_f64 x).

(** An opaque definition for cases that can’t happen because of the well-formed properties. **)
Definition dummy : list byte.
Proof. exact (x00 :: x00 :: x00 :: nil). Qed.

Fixpoint binary_of_be (be : basic_instruction) : list byte :=
  let binary_of_instrs bes := List.concat (List.map binary_of_be bes) in
  match be with
  | BI_unreachable => x00 :: nil
  | BI_nop => x01 :: nil
  | BI_block rt ins =>
    x02 :: binary_of_block_type rt ++ binary_of_instrs ins ++ x0b :: nil
  | BI_loop rt ins =>
    x03 :: binary_of_block_type rt ++ binary_of_instrs ins ++ x0b :: nil
  | BI_if rt ins nil =>
    x04 :: binary_of_block_type rt ++ binary_of_instrs ins ++ x0b :: nil
  | BI_if rt ins1 ins2 =>
    x04 :: binary_of_block_type rt ++ binary_of_instrs ins1 ++ x05 :: nil ++ binary_of_instrs ins2 ++ x0b :: nil
  | BI_br l => x0c :: binary_of_idx l
  | BI_br_if l => x0d :: binary_of_idx l
  | BI_br_table ls l_N =>
    x0e :: binary_of_vec binary_of_idx ls ++ binary_of_idx l_N
  | BI_return => x0f :: nil
  | BI_call x => x10 :: binary_of_idx x
  | BI_call_indirect x => x11 :: binary_of_idx x ++ x00 :: nil
  | BI_return_call x => x12 :: binary_of_idx x
  | BI_return_call_indirect x => x13 :: binary_of_idx x ++ x00 :: nil
  | BI_drop => x1a :: nil
  | BI_select => x1b :: nil
  | BI_get_local x => x20 :: binary_of_idx x
  | BI_set_local x => x21 :: binary_of_idx x
  | BI_tee_local x => x22 :: binary_of_idx x
  | BI_get_global x => x23 :: binary_of_idx x
  | BI_set_global x => x24 :: binary_of_idx x
  | BI_load T_i32 None a o => x28 :: binary_of_memarg a o
  | BI_load T_i64 None a o => x29 :: binary_of_memarg a o
  | BI_load T_f32 None a o => x2a :: binary_of_memarg a o
  | BI_load T_f32 (Some _) _ _ => dummy
  | BI_load T_f64 None a o => x2b :: binary_of_memarg a o
  | BI_load T_f64 (Some _) _ _ => dummy
  | BI_load T_i32 (Some (Tp_i8, SX_S)) a o => x2c :: binary_of_memarg a o
  | BI_load T_i32 (Some (Tp_i8, SX_U)) a o => x2d :: binary_of_memarg a o
  | BI_load T_i32 (Some (Tp_i16, SX_S)) a o => x2e :: binary_of_memarg a o
  | BI_load T_i32 (Some (Tp_i16, SX_U)) a o => x2f :: binary_of_memarg a o
  | BI_load T_i32 (Some (Tp_i32, _)) _ _ => dummy
  | BI_load T_i64 (Some (Tp_i8, SX_S)) a o => x30 :: binary_of_memarg a o
  | BI_load T_i64 (Some (Tp_i8, SX_U)) a o => x31 :: binary_of_memarg a o
  | BI_load T_i64 (Some (Tp_i16, SX_S)) a o => x32 :: binary_of_memarg a o
  | BI_load T_i64 (Some (Tp_i16, SX_U)) a o => x33 :: binary_of_memarg a o
  | BI_load T_i64 (Some (Tp_i32, SX_S)) a o => x34 :: binary_of_memarg a o
  | BI_load T_i64 (Some (Tp_i32, SX_U)) a o => x35 :: binary_of_memarg a o
  | BI_store T_i32 None a o => x36 :: binary_of_memarg a o
  | BI_store T_i64 None a o => x37 :: binary_of_memarg a o
  | BI_store T_f32 None a o => x38 :: binary_of_memarg a o
  | BI_store T_f32 (Some _) _ _  => dummy
  | BI_store T_f64 None a o => x39 :: binary_of_memarg a o
  | BI_store T_f64 (Some _) _ _ => dummy
  | BI_store T_i32 (Some Tp_i8) a o => x3a :: binary_of_memarg a o
  | BI_store T_i32 (Some Tp_i16) a o => x3b :: binary_of_memarg a o
  | BI_store T_i32 (Some Tp_i32) _ _ => dummy
  | BI_store T_i64 (Some Tp_i8) a o => x3c :: binary_of_memarg a o
  | BI_store T_i64 (Some Tp_i16) a o => x3d :: binary_of_memarg a o
  | BI_store T_i64 (Some Tp_i32) a o => x3e :: binary_of_memarg a o
  | BI_current_memory => x3f :: x00 :: nil
  | BI_grow_memory => x40 :: x00 :: nil
  | BI_const (VAL_int32 x) => x41 :: binary_of_i32 x
  | BI_const (VAL_int64 x) => x42 :: binary_of_i64 x
  | BI_const (VAL_float32 x) => x43 :: binary_of_f32 x
  | BI_const (VAL_float64 x) => x44 :: binary_of_f64 x
  | BI_testop T_i32 Eqz => x45 :: nil
  | BI_testop T_i64 Eqz => x50 :: nil
  | BI_testop T_f32 _ => dummy
  | BI_testop T_f64 _ => dummy
  | BI_relop T_i32 (Relop_i ROI_eq) => x46 :: nil
  | BI_relop T_i32 (Relop_i ROI_ne) => x47 :: nil
  | BI_relop T_i32 (Relop_i (ROI_lt SX_S)) => x48 :: nil
  | BI_relop T_i32 (Relop_i (ROI_lt SX_U)) => x49 :: nil
  | BI_relop T_i32 (Relop_i (ROI_gt SX_S)) => x4a :: nil
  | BI_relop T_i32 (Relop_i (ROI_gt SX_U)) => x4b :: nil
  | BI_relop T_i32 (Relop_i (ROI_le SX_S)) => x4c :: nil
  | BI_relop T_i32 (Relop_i (ROI_le SX_U)) => x4d :: nil
  | BI_relop T_i32 (Relop_i (ROI_ge SX_S)) => x4e :: nil
  | BI_relop T_i32 (Relop_i (ROI_ge SX_U)) => x4f :: nil
  | BI_relop T_i64 (Relop_i ROI_eq) => x51 :: nil
  | BI_relop T_i64 (Relop_i ROI_ne) => x52 :: nil
  | BI_relop T_i64 (Relop_i (ROI_lt SX_S)) => x53 :: nil
  | BI_relop T_i64 (Relop_i (ROI_lt SX_U)) => x54 :: nil
  | BI_relop T_i64 (Relop_i (ROI_gt SX_S)) => x55 :: nil
  | BI_relop T_i64 (Relop_i (ROI_gt SX_U)) => x56 :: nil
  | BI_relop T_i64 (Relop_i (ROI_le SX_S)) => x57 :: nil
  | BI_relop T_i64 (Relop_i (ROI_le SX_U)) => x58 :: nil
  | BI_relop T_i64 (Relop_i (ROI_ge SX_S)) => x59 :: nil
  | BI_relop T_i64 (Relop_i (ROI_ge SX_U)) => x5a :: nil
  | BI_relop T_f32 (Relop_i _) => dummy
  | BI_relop T_f64 (Relop_i _) => dummy
  | BI_relop T_f32 (Relop_f ROF_eq) => x5b :: nil
  | BI_relop T_f32 (Relop_f ROF_ne) => x5c :: nil
  | BI_relop T_f32 (Relop_f ROF_lt) => x5d :: nil
  | BI_relop T_f32 (Relop_f ROF_gt) => x5e :: nil
  | BI_relop T_f32 (Relop_f ROF_le) => x5f :: nil
  | BI_relop T_f32 (Relop_f ROF_ge) => x60 :: nil
  | BI_relop T_f64 (Relop_f ROF_eq) => x61 :: nil
  | BI_relop T_f64 (Relop_f ROF_ne) => x62 :: nil
  | BI_relop T_f64 (Relop_f ROF_lt) => x63 :: nil
  | BI_relop T_f64 (Relop_f ROF_gt) => x64 :: nil
  | BI_relop T_f64 (Relop_f ROF_le) => x65 :: nil
  | BI_relop T_f64 (Relop_f ROF_ge) => x66 :: nil
  | BI_relop T_i32 (Relop_f _) => dummy
  | BI_relop T_i64 (Relop_f _) => dummy
  | BI_unop T_i32 (Unop_i UOI_clz) => x67 :: nil
  | BI_unop T_i32 (Unop_i UOI_ctz) => x68 :: nil
  | BI_unop T_i32 (Unop_i UOI_popcnt) => x69 :: nil
  | BI_binop T_i32 (Binop_i BOI_add) => x6a :: nil
  | BI_binop T_i32 (Binop_i BOI_sub) => x6b :: nil
  | BI_binop T_i32 (Binop_i BOI_mul) => x6c :: nil
  | BI_binop T_i32 (Binop_i (BOI_div SX_S)) => x6d :: nil
  | BI_binop T_i32 (Binop_i (BOI_div SX_U)) => x6e :: nil
  | BI_binop T_i32 (Binop_i (BOI_rem SX_S)) => x6f :: nil
  | BI_binop T_i32 (Binop_i (BOI_rem SX_U)) => x70 :: nil
  | BI_binop T_i32 (Binop_i BOI_and) => x71 :: nil
  | BI_binop T_i32 (Binop_i BOI_or) => x72 :: nil
  | BI_binop T_i32 (Binop_i BOI_xor) => x73 :: nil
  | BI_binop T_i32 (Binop_i BOI_shl) => x74 :: nil
  | BI_binop T_i32 (Binop_i (BOI_shr SX_S)) => x75 :: nil
  | BI_binop T_i32 (Binop_i (BOI_shr SX_U)) => x76 :: nil
  | BI_binop T_i32 (Binop_i BOI_rotl) => x77 :: nil
  | BI_binop T_i32 (Binop_i BOI_rotr) => x78 :: nil
  | BI_binop T_f32 (Binop_i _) => dummy
  | BI_binop T_f64 (Binop_i _) => dummy
  | BI_unop T_i64 (Unop_i UOI_clz) => x79 :: nil
  | BI_unop T_i64 (Unop_i UOI_ctz) => x7a :: nil
  | BI_unop T_i64 (Unop_i UOI_popcnt) => x7b :: nil
  | BI_unop T_f32 (Unop_i _) => dummy
  | BI_unop T_f64 (Unop_i _) => dummy
  | BI_binop T_i64 (Binop_i BOI_add) => x7c :: nil
  | BI_binop T_i64 (Binop_i BOI_sub) => x7d :: nil
  | BI_binop T_i64 (Binop_i BOI_mul) => x7e :: nil
  | BI_binop T_i64 (Binop_i (BOI_div SX_S)) => x7f :: nil
  | BI_binop T_i64 (Binop_i (BOI_div SX_U)) => x80 :: nil
  | BI_binop T_i64 (Binop_i (BOI_rem SX_S)) => x81 :: nil
  | BI_binop T_i64 (Binop_i (BOI_rem SX_U)) => x82 :: nil
  | BI_binop T_i64 (Binop_i BOI_and) => x83 :: nil
  | BI_binop T_i64 (Binop_i BOI_or) => x84 :: nil
  | BI_binop T_i64 (Binop_i BOI_xor) => x85 :: nil
  | BI_binop T_i64 (Binop_i BOI_shl) => x86 :: nil
  | BI_binop T_i64 (Binop_i (BOI_shr SX_S)) => x87 :: nil
  | BI_binop T_i64 (Binop_i (BOI_shr SX_U)) => x88 :: nil
  | BI_binop T_i64 (Binop_i BOI_rotl) => x89 :: nil
  | BI_binop T_i64 (Binop_i BOI_rotr) => x8a :: nil
  | BI_unop T_f32 (Unop_f UOF_abs) => x8b :: nil
  | BI_unop T_f32 (Unop_f UOF_neg) => x8c :: nil
  | BI_unop T_f32 (Unop_f UOF_ceil) => x8d :: nil
  | BI_unop T_f32 (Unop_f UOF_floor) => x8e :: nil
  | BI_unop T_f32 (Unop_f UOF_trunc) => x8f :: nil
  | BI_unop T_f32 (Unop_f UOF_nearest) => x90 :: nil
  | BI_unop T_f32 (Unop_f UOF_sqrt) => x91 :: nil
  | BI_unop T_i32 (Unop_f _) => dummy
  | BI_unop T_i64 (Unop_f _) => dummy
  | BI_binop T_f32 (Binop_f BOF_add) => x92 :: nil
  | BI_binop T_f32 (Binop_f BOF_sub) => x93 :: nil
  | BI_binop T_f32 (Binop_f BOF_mul) => x94 :: nil
  | BI_binop T_f32 (Binop_f BOF_div) => x95 :: nil
  | BI_binop T_f32 (Binop_f BOF_min) => x96 :: nil
  | BI_binop T_f32 (Binop_f BOF_max) => x97 :: nil
  | BI_binop T_f32 (Binop_f BOF_copysign) => x98 :: nil
  | BI_unop T_f64 (Unop_f UOF_abs) => x99 :: nil
  | BI_unop T_f64 (Unop_f UOF_neg) => x9a :: nil
  | BI_unop T_f64 (Unop_f UOF_ceil) => x9b :: nil
  | BI_unop T_f64 (Unop_f UOF_floor) => x9c :: nil
  | BI_unop T_f64 (Unop_f UOF_trunc) => x9d :: nil
  | BI_unop T_f64 (Unop_f UOF_nearest) => x9e :: nil
  | BI_unop T_f64 (Unop_f UOF_sqrt) => x9f :: nil
  | BI_binop T_f64 (Binop_f BOF_add) => xa0 :: nil
  | BI_binop T_f64 (Binop_f BOF_sub) => xa1 :: nil
  | BI_binop T_f64 (Binop_f BOF_mul) => xa2 :: nil
  | BI_binop T_f64 (Binop_f BOF_div) => xa3 :: nil
  | BI_binop T_f64 (Binop_f BOF_min) => xa4 :: nil
  | BI_binop T_f64 (Binop_f BOF_max) => xa5 :: nil
  | BI_binop T_f64 (Binop_f BOF_copysign) => xa6 :: nil
  | BI_binop T_i32 (Binop_f _) => dummy
  | BI_binop T_i64 (Binop_f _) => dummy
  (* TODO: I am really not sure whether the cases below are right :-s *)
  | BI_cvtop T_i32 CVO_convert T_i64 (Some SX_U) (* TODO: is this correct? *) => xa7 :: nil
  | BI_cvtop T_i32 CVO_convert T_i64 _ => dummy
  | BI_cvtop T_i32 CVO_convert T_f32 (Some SX_S) => xa8 :: nil
  | BI_cvtop T_i32 CVO_convert T_f32 (Some SX_U) => xa9 :: nil
  | BI_cvtop T_i32 CVO_convert T_f32 None => dummy
  | BI_cvtop T_i32 CVO_convert T_f64 (Some SX_S) => xaa :: nil
  | BI_cvtop T_i32 CVO_convert T_f64 (Some SX_U) => xab :: nil
  | BI_cvtop T_i32 CVO_convert T_f64 None => dummy
  | BI_cvtop T_i32 CVO_convert T_i32 _ => dummy
  | BI_cvtop T_i64 CVO_convert T_i32 (Some SX_S) => xac :: nil
  | BI_cvtop T_i64 CVO_convert T_i32 (Some SX_U) => xad :: nil
  | BI_cvtop T_i64 CVO_convert T_i32 None => dummy
  | BI_cvtop T_i64 CVO_convert T_f32 (Some SX_S) => xae :: nil
  | BI_cvtop T_i64 CVO_convert T_f32 (Some SX_U) => xaf :: nil
  | BI_cvtop T_i64 CVO_convert T_f32 None => dummy
  | BI_cvtop T_i64 CVO_convert T_f64 (Some SX_S) => xb0 :: nil
  | BI_cvtop T_i64 CVO_convert T_f64 (Some SX_U) => xb1 :: nil
  | BI_cvtop T_i64 CVO_convert T_f64 _ => dummy
  | BI_cvtop T_i64 CVO_convert T_i64 _ => dummy
  | BI_cvtop T_f32 CVO_convert T_i32 (Some SX_S) => xb2 :: nil
  | BI_cvtop T_f32 CVO_convert T_i32 (Some SX_U) => xb3 :: nil
  | BI_cvtop T_f32 CVO_convert T_i32 None => dummy
  | BI_cvtop T_f32 CVO_convert T_i64 (Some SX_S) => xb4 :: nil
  | BI_cvtop T_f32 CVO_convert T_i64 (Some SX_U) => xb5 :: nil
  | BI_cvtop T_f32 CVO_convert T_i64 None => dummy
  | BI_cvtop T_f32 CVO_convert T_f64 None => xb6 :: nil
  | BI_cvtop T_f32 CVO_convert T_f64 (Some _) => dummy
  | BI_cvtop T_f32 CVO_convert T_f32 _ => dummy
  | BI_cvtop T_f64 CVO_convert T_i32 (Some SX_S) => xb7 :: nil
  | BI_cvtop T_f64 CVO_convert T_i32 (Some SX_U) => xb8 :: nil
  | BI_cvtop T_f64 CVO_convert T_i32 None => dummy
  | BI_cvtop T_f64 CVO_convert T_i64 (Some SX_S) => xb9 :: nil
  | BI_cvtop T_f64 CVO_convert T_i64 (Some SX_U) => xba :: nil
  | BI_cvtop T_f64 CVO_convert T_i64 None => dummy
  | BI_cvtop T_f64 CVO_convert T_f32 None => xbb :: nil
  | BI_cvtop T_f64 CVO_convert T_f32 (Some _) => dummy
  | BI_cvtop T_f64 CVO_convert T_f64 _ => dummy
  | BI_cvtop T_i32 CVO_reinterpret T_f32 None => xbc :: nil
  | BI_cvtop T_i64 CVO_reinterpret T_f64 None => xbc :: nil
  | BI_cvtop T_f32 CVO_reinterpret T_i32 None => xbc :: nil
  | BI_cvtop T_f64 CVO_reinterpret T_i64 None => xbc :: nil
  | BI_cvtop T_i32 CVO_reinterpret T_i32 _ => dummy
  | BI_cvtop T_i32 CVO_reinterpret T_i64 _ => dummy
  | BI_cvtop T_i32 CVO_reinterpret T_f64 _ => dummy
  | BI_cvtop T_i64 CVO_reinterpret T_i32 _ => dummy
  | BI_cvtop T_i64 CVO_reinterpret T_i64 _ => dummy
  | BI_cvtop T_i64 CVO_reinterpret T_f32 _ => dummy
  | BI_cvtop T_f32 CVO_reinterpret T_i64 _ => dummy
  | BI_cvtop T_f32 CVO_reinterpret T_f32 _ => dummy
  | BI_cvtop T_f32 CVO_reinterpret T_f64 _ => dummy
  | BI_cvtop T_f64 CVO_reinterpret T_i32 _ => dummy
  | BI_cvtop T_f64 CVO_reinterpret T_f32 _ => dummy
  | BI_cvtop T_f64 CVO_reinterpret T_f64 _ => dummy
  | BI_cvtop _ CVO_reinterpret _ (Some _) => dummy
  end.

(** Expressions are encoded by their instruction sequence terminated with an
explicit `0x0B` opcode for `end`. *)
Definition binary_of_expr (bes : list basic_instruction) : list byte  :=
  List.concat (List.map binary_of_be bes) ++ x0b :: nil.

Definition magic : list byte :=
  x00 :: x61 :: x73 :: x6d:: nil.

Definition version : list byte :=
  x01 :: x00 :: x00 :: x00 :: nil.

Definition with_length (bs : list byte) : list byte :=
  leb128.encode_unsigned (bin_of_nat (List.length bs)) ++ bs.

Definition binary_of_result_type rt : list byte :=
  binary_of_vec(fun v => binary_of_value_type v :: nil) rt.

Definition binary_of_functype (ft : function_type) : list byte :=
  let 'Tf rt1 rt2 := ft in
  x60 :: binary_of_result_type rt1 ++ binary_of_result_type rt2.

Definition binary_of_typesec (ts : list function_type) : list byte :=
  x01 :: with_length (binary_of_vec binary_of_functype ts).

Definition binary_of_typeidx (t : typeidx) : list byte :=
  let 'Mk_typeidx i := t in
  leb128.encode_unsigned (bin_of_nat i).

Definition binary_of_funcidx (t : funcidx) : list byte :=
  let 'Mk_funcidx i := t in
  leb128.encode_unsigned (bin_of_nat i).

Definition binary_of_tableidx (t : tableidx) : list byte :=
  let 'Mk_tableidx i := t in
  leb128.encode_unsigned (bin_of_nat i).

Definition binary_of_memidx (t : memidx) : list byte :=
  let 'Mk_memidx i := t in
  leb128.encode_unsigned (bin_of_nat i).

Definition binary_of_globalidx (t : globalidx) : list byte :=
  let 'Mk_globalidx i := t in
  leb128.encode_unsigned (bin_of_nat i).

Definition binary_of_name (n : name) : list byte :=
  binary_of_vec (fun n => cons n nil) n.

Definition binary_of_elem_type (et : elem_type) : list byte :=
  match et with
  | ET_funcref => cons x70 nil
  end.

Definition binary_of_limits (l : limits) : list byte :=
  match l.(lim_max) with
  | None => x00 :: leb128.encode_unsigned (bin_of_nat l.(lim_min))
  | Some max =>
    x01 ::
    leb128.encode_unsigned (bin_of_nat l.(lim_min)) ++
    leb128.encode_unsigned (bin_of_nat max)
  end.

Definition binary_of_table_type (t_ty : table_type) : list byte :=
  binary_of_elem_type t_ty.(tt_elem_type) ++
  binary_of_limits t_ty.(tt_limits).

Definition binary_of_mutability (m : mutability) : list byte :=
  match m with
  | MUT_immut => cons x00 nil
  | MUT_mut => cons x01 nil
  end.

Definition binary_of_global_type (g_ty : global_type) : list byte :=
  cons (binary_of_value_type g_ty.(tg_t)) nil ++
  binary_of_mutability g_ty.(tg_mut).

Definition binary_of_memory_type (m : memory_type) : list byte :=
  binary_of_limits m.

Definition binary_of_import_desc (imp_desc : import_desc) : list byte :=
  match imp_desc with
  | ID_func tidx => x00 :: binary_of_typeidx (Mk_typeidx tidx)
  | ID_table t_ty => x01 :: binary_of_table_type t_ty
  | ID_mem m_ty => x02 :: binary_of_memory_type m_ty
  | ID_global g_ty => x03 :: binary_of_global_type g_ty
  end.

Definition binary_of_module_import (imp : module_import) : list byte :=
  binary_of_name imp.(imp_module) ++
  binary_of_name imp.(imp_name) ++
  binary_of_import_desc imp.(imp_desc).

Definition binary_of_importsec (imps : list module_import) : list byte :=
  x02 :: with_length (binary_of_vec binary_of_module_import imps).

Definition binary_of_funcsec (fs : list module_func) : list byte :=
  x03 :: with_length (binary_of_vec binary_of_typeidx (List.map (fun f => f.(modfunc_type)) fs)).

Definition binary_of_module_table (t : module_table) : list byte :=
  binary_of_table_type t.(modtab_type).

Definition binary_of_tablesec (ts : list module_table) : list byte :=
  x04 :: with_length (binary_of_vec binary_of_module_table ts).

Definition binary_of_memsec (ms : list memory_type) : list byte :=
  x05 :: with_length (binary_of_vec binary_of_memory_type ms).

Definition binary_of_module_glob (g : module_glob) : list byte :=
  binary_of_global_type g.(modglob_type) ++
  binary_of_expr g.(modglob_init).

Definition binary_of_globalsec (gs : list module_glob) : list byte :=
  x06 :: with_length (binary_of_vec binary_of_module_glob gs).

Definition binary_of_export_desc (ed : module_export_desc) : list byte :=
  match ed with
  | MED_func n => x00 :: binary_of_funcidx n
  | MED_table n => x01 :: binary_of_tableidx n
  | MED_mem n => x02 :: binary_of_memidx n
  | MED_global n => x03 :: binary_of_globalidx n
  end.

Definition binary_of_module_export (e : module_export) : list byte :=
  binary_of_name e.(modexp_name) ++
  binary_of_export_desc e.(modexp_desc).

Definition binary_of_exportssec (es : list module_export) : list byte :=
  x07 :: with_length (binary_of_vec binary_of_module_export es).

Definition binary_of_module_start (s : module_start) : list byte :=
  binary_of_funcidx s.(modstart_func).

Definition binary_of_startsec (s : module_start) : list byte :=
  x08 :: with_length (binary_of_module_start s).

Definition binary_of_module_elem (e : module_element) : list byte :=
  binary_of_tableidx e.(modelem_table) ++
  binary_of_expr e.(modelem_offset) ++
  binary_of_vec binary_of_funcidx e.(modelem_init).

Definition binary_of_elemsec (es : list module_element) : list byte :=
  x09 :: with_length (binary_of_vec binary_of_module_elem es).

Definition binary_of_local (n_t : nat * value_type) : list byte :=
  let '(n, t) := n_t in
  leb128.encode_unsigned (bin_of_nat n) ++
  cons (binary_of_value_type t) nil.

Fixpoint bunch_locals_aux (cur_ty : value_type) (cur_count : nat) (acc : list (nat * value_type)) (tys : list value_type) : list (nat * value_type) :=
  match tys with
  | nil => List.rev ((cur_count, cur_ty) :: acc)
  | cons ty tys' =>
    if cur_ty == ty then bunch_locals_aux cur_ty (cur_count + 1) acc tys'
    else bunch_locals_aux ty 1 ((cur_count, cur_ty) :: acc) tys'
  end.

Definition bunch_locals (tys : list value_type) : list (nat * value_type) :=
  match tys with
  | nil => nil
  | cons ty tys' => bunch_locals_aux ty 1 nil tys'
  end.

Definition binary_of_code_func (cf : code_func) : list byte :=
  binary_of_vec binary_of_local (bunch_locals cf.(fc_locals)) ++
  binary_of_expr cf.(fc_expr).

Definition binary_of_code (mf : module_func) : list byte :=
  let func := {| fc_locals := mf.(modfunc_locals); fc_expr := mf.(modfunc_body) |} in
  let func_bin := binary_of_code_func func in
  let func_len := List.length func_bin in
  leb128.encode_unsigned (bin_of_nat func_len) ++
  func_bin.

Definition binary_of_codesec (fs : list module_func) : list byte :=
  x0a :: with_length (binary_of_vec binary_of_code fs).

Definition binary_of_data (d : module_data) : list byte :=
  binary_of_memidx d.(moddata_data) ++
  binary_of_expr d.(moddata_offset) ++
  binary_of_vec (fun x => cons x nil) d.(moddata_init).

Definition binary_of_datasec (ds : list module_data) : list byte :=
  x0b :: with_length (binary_of_vec binary_of_data ds).

Definition only_if_non_nil {A} (f : list A -> list byte) (xs : list A) : list byte :=
  match xs with
  | nil => nil
  | _ :: _ => f xs
  end.

Definition only_if_non_none {A} (f : A -> list byte) (xo : option A) : list byte :=
  match xo with
  | None => nil
  | Some x => f x
  end.

Definition binary_of_module (m : module) : list byte :=
  magic ++ version ++
  only_if_non_nil binary_of_typesec m.(mod_types) ++
  only_if_non_nil binary_of_importsec m.(mod_imports) ++
  only_if_non_nil binary_of_funcsec m.(mod_funcs) ++
  only_if_non_nil binary_of_tablesec m.(mod_tables) ++
  only_if_non_nil binary_of_memsec m.(mod_mems) ++
  only_if_non_nil binary_of_globalsec m.(mod_globals) ++
  only_if_non_nil binary_of_exportssec m.(mod_exports) ++
  only_if_non_none binary_of_startsec m.(mod_start) ++
  only_if_non_nil binary_of_elemsec m.(mod_elem) ++
  only_if_non_nil binary_of_codesec m.(mod_funcs) ++
  only_if_non_nil binary_of_datasec m.(mod_data).
