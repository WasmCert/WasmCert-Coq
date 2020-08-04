(** Wasm AST to binary.
Breaks non-determinism ties; see binary_format_spec.v for the spec. *)
Require Import datatypes_properties numerics.
From compcert Require Integers.
Require Import Byte.
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
  leb128.encode_signed x.(Wasm_int.Int32.intval).

Definition binary_of_i64 (x : i64) : list byte :=
  leb128.encode_signed x.(Wasm_int.Int64.intval).

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
  | Unreachable => x00 :: nil
  | Nop => x01 :: nil
  | Block rt ins =>
    x02 :: binary_of_block_type rt ++ binary_of_instrs ins ++ x0b :: nil
  | Loop rt ins =>
    x03 :: binary_of_block_type rt ++ binary_of_instrs ins ++ x0b :: nil
  | If rt ins nil =>
    x04 :: binary_of_block_type rt ++ binary_of_instrs ins ++ x0b :: nil
  | If rt ins1 ins2 =>
    x04 :: binary_of_block_type rt ++ binary_of_instrs ins1 ++ x05 :: nil ++ binary_of_instrs ins2 ++ x0b :: nil
  | Br l => x0c :: binary_of_idx l
  | Br_if l => x0d :: binary_of_idx l
  | Br_table ls l_N =>
    x0e :: binary_of_vec binary_of_idx ls ++ binary_of_idx l_N
  | Return => x0f :: nil
  | Call x => x10 :: binary_of_idx x
  | Call_indirect x => x11 :: binary_of_idx x ++ x00 :: nil
  | Drop => x1a :: nil
  | Select => x1b :: nil
  | Get_local x => x20 :: binary_of_idx x
  | Set_local x => x21 :: binary_of_idx x
  | Tee_local x => x22 :: binary_of_idx x
  | Get_global x => x23 :: binary_of_idx x
  | Set_global x => x24 :: binary_of_idx x
  | Load T_i32 None a o => x28 :: binary_of_memarg a o
  | Load T_i64 None a o => x29 :: binary_of_memarg a o
  | Load T_f32 None a o => x2a :: binary_of_memarg a o
  | Load T_f32 (Some _) _ _ => dummy
  | Load T_f64 None a o => x2b :: binary_of_memarg a o
  | Load T_f64 (Some _) _ _ => dummy
  | Load T_i32 (Some (Tp_i8, SX_S)) a o => x2c :: binary_of_memarg a o
  | Load T_i32 (Some (Tp_i8, SX_U)) a o => x2d :: binary_of_memarg a o
  | Load T_i32 (Some (Tp_i16, SX_S)) a o => x2e :: binary_of_memarg a o
  | Load T_i32 (Some (Tp_i16, SX_U)) a o => x2f :: binary_of_memarg a o
  | Load T_i32 (Some (Tp_i32, _)) _ _ => dummy
  | Load T_i64 (Some (Tp_i8, SX_S)) a o => x30 :: binary_of_memarg a o
  | Load T_i64 (Some (Tp_i8, SX_U)) a o => x31 :: binary_of_memarg a o
  | Load T_i64 (Some (Tp_i16, SX_S)) a o => x32 :: binary_of_memarg a o
  | Load T_i64 (Some (Tp_i16, SX_U)) a o => x33 :: binary_of_memarg a o
  | Load T_i64 (Some (Tp_i32, SX_S)) a o => x34 :: binary_of_memarg a o
  | Load T_i64 (Some (Tp_i32, SX_U)) a o => x35 :: binary_of_memarg a o
  | Store T_i32 None a o => x36 :: binary_of_memarg a o
  | Store T_i64 None a o => x37 :: binary_of_memarg a o
  | Store T_f32 None a o => x38 :: binary_of_memarg a o
  | Store T_f32 (Some _) _ _  => dummy
  | Store T_f64 None a o => x39 :: binary_of_memarg a o
  | Store T_f64 (Some _) _ _ => dummy
  | Store T_i32 (Some Tp_i8) a o => x3a :: binary_of_memarg a o
  | Store T_i32 (Some Tp_i16) a o => x3b :: binary_of_memarg a o
  | Store T_i32 (Some Tp_i32) _ _ => dummy
  | Store T_i64 (Some Tp_i8) a o => x3c :: binary_of_memarg a o
  | Store T_i64 (Some Tp_i16) a o => x3d :: binary_of_memarg a o
  | Store T_i64 (Some Tp_i32) a o => x3e :: binary_of_memarg a o
  | Current_memory => x3f :: x00 :: nil
  | Grow_memory => x40 :: x00 :: nil
  | EConst (ConstInt32 x) => x41 :: binary_of_i32 x
  | EConst (ConstInt64 x) => x42 :: binary_of_i64 x
  | EConst (ConstFloat32 x) => x43 :: binary_of_f32 x
  | EConst (ConstFloat64 x) => x44 :: binary_of_f64 x
  | Testop T_i32 Eqz => x45 :: nil
  | Testop T_i64 Eqz => x50 :: nil
  | Testop T_f32 _ => dummy
  | Testop T_f64 _ => dummy
  | Relop_i T_i32 Eq => x46 :: nil
  | Relop_i T_i32 Ne => x47 :: nil
  | Relop_i T_i32 (Lt SX_S) => x48 :: nil
  | Relop_i T_i32 (Lt SX_U) => x49 :: nil
  | Relop_i T_i32 (Gt SX_S) => x4a :: nil
  | Relop_i T_i32 (Gt SX_U) => x4b :: nil
  | Relop_i T_i32 (Le SX_S) => x4c :: nil
  | Relop_i T_i32 (Le SX_U) => x4d :: nil
  | Relop_i T_i32 (Ge SX_S) => x4e :: nil
  | Relop_i T_i32 (Ge SX_U) => x4f :: nil
  | Relop_i T_i64 Eq => x51 :: nil
  | Relop_i T_i64 Ne => x52 :: nil
  | Relop_i T_i64 (Lt SX_S) => x53 :: nil
  | Relop_i T_i64 (Lt SX_U) => x54 :: nil
  | Relop_i T_i64 (Gt SX_S) => x55 :: nil
  | Relop_i T_i64 (Gt SX_U) => x56 :: nil
  | Relop_i T_i64 (Le SX_S) => x57 :: nil
  | Relop_i T_i64 (Le SX_U) => x58 :: nil
  | Relop_i T_i64 (Ge SX_S) => x59 :: nil
  | Relop_i T_i64 (Ge SX_U) => x5a :: nil
  | Relop_i T_f32 _ => dummy
  | Relop_i T_f64 _ => dummy
  | Relop_f T_f32 Eqf => x5b :: nil
  | Relop_f T_f32 Nef => x5c :: nil
  | Relop_f T_f32 Ltf => x5d :: nil
  | Relop_f T_f32 Gtf => x5e :: nil
  | Relop_f T_f32 Lef => x5f :: nil
  | Relop_f T_f32 Gef => x60 :: nil
  | Relop_f T_f64 Eqf => x61 :: nil
  | Relop_f T_f64 Nef => x62 :: nil
  | Relop_f T_f64 Ltf => x63 :: nil
  | Relop_f T_f64 Gtf => x64 :: nil
  | Relop_f T_f64 Lef => x65 :: nil
  | Relop_f T_f64 Gef => x66 :: nil
  | Relop_f T_i32 _ => dummy
  | Relop_f T_i64 _ => dummy
  | Unop_i T_i32 Clz => x67 :: nil
  | Unop_i T_i32 Ctz => x68 :: nil
  | Unop_i T_i32 Popcnt => x69 :: nil
  | Binop_i T_i32 Add => x6a :: nil
  | Binop_i T_i32 datatypes.Sub => x6b :: nil
  | Binop_i T_i32 Mul => x6c :: nil
  | Binop_i T_i32 (Div SX_S) => x6d :: nil
  | Binop_i T_i32 (Div SX_U) => x6e :: nil
  | Binop_i T_i32 (Rem SX_S) => x6f :: nil
  | Binop_i T_i32 (Rem SX_U) => x70 :: nil
  | Binop_i T_i32 And => x71 :: nil
  | Binop_i T_i32 Or => x72 :: nil
  | Binop_i T_i32 Xor => x73 :: nil
  | Binop_i T_i32 Shl => x74 :: nil
  | Binop_i T_i32 (Shr SX_S) => x75 :: nil
  | Binop_i T_i32 (Shr SX_U) => x76 :: nil
  | Binop_i T_i32 Rotl => x77 :: nil
  | Binop_i T_i32 Rotr => x78 :: nil
  | Binop_i T_f32 _ => dummy
  | Binop_i T_f64 _ => dummy
  | Unop_i T_i64 Clz => x79 :: nil
  | Unop_i T_i64 Ctz => x7a :: nil
  | Unop_i T_i64 Popcnt => x7b :: nil
  | Unop_i T_f32 _ => dummy
  | Unop_i T_f64 _ => dummy
  | Binop_i T_i64 Add => x7c :: nil
  | Binop_i T_i64 datatypes.Sub => x7d :: nil
  | Binop_i T_i64 Mul => x7e :: nil
  | Binop_i T_i64 (Div SX_S) => x7f :: nil
  | Binop_i T_i64 (Div SX_U) => x80 :: nil
  | Binop_i T_i64 (Rem SX_S) => x81 :: nil
  | Binop_i T_i64 (Rem SX_U) => x82 :: nil
  | Binop_i T_i64 And => x83 :: nil
  | Binop_i T_i64 Or => x84 :: nil
  | Binop_i T_i64 Xor => x85 :: nil
  | Binop_i T_i64 Shl => x86 :: nil
  | Binop_i T_i64 (Shr SX_S) => x87 :: nil
  | Binop_i T_i64 (Shr SX_U) => x88 :: nil
  | Binop_i T_i64 Rotl => x89 :: nil
  | Binop_i T_i64 Rotr => x8a :: nil
  | Unop_f T_f32 Abs => x8b :: nil
  | Unop_f T_f32 Neg => x8c :: nil
  | Unop_f T_f32 Ceil => x8d :: nil
  | Unop_f T_f32 Floor => x8e :: nil
  | Unop_f T_f32 Trunc => x8f :: nil
  | Unop_f T_f32 Nearest => x90 :: nil
  | Unop_f T_f32 Sqrt => x91 :: nil
  | Unop_f T_i32 _ => dummy
  | Unop_f T_i64 _ => dummy
  | Binop_f T_f32 Addf => x92 :: nil
  | Binop_f T_f32 Subf => x93 :: nil
  | Binop_f T_f32 Mulf => x94 :: nil
  | Binop_f T_f32 Divf => x95 :: nil
  | Binop_f T_f32 Min => x96 :: nil
  | Binop_f T_f32 Max => x97 :: nil
  | Binop_f T_f32 Copysign => x98 :: nil
  | Unop_f T_f64 Abs => x99 :: nil
  | Unop_f T_f64 Neg => x9a :: nil
  | Unop_f T_f64 Ceil => x9b :: nil
  | Unop_f T_f64 Floor => x9c :: nil
  | Unop_f T_f64 Trunc => x9d :: nil
  | Unop_f T_f64 Nearest => x9e :: nil
  | Unop_f T_f64 Sqrt => x9f :: nil
  | Binop_f T_f64 Addf => xa0 :: nil
  | Binop_f T_f64 Subf => xa1 :: nil
  | Binop_f T_f64 Mulf => xa2 :: nil
  | Binop_f T_f64 Divf => xa3 :: nil
  | Binop_f T_f64 Min => xa4 :: nil
  | Binop_f T_f64 Max => xa5 :: nil
  | Binop_f T_f64 Copysign => xa6 :: nil
  | Binop_f T_i32 _ => dummy
  | Binop_f T_i64 _ => dummy
  (* TODO: I am really not sure whether the cases below are right :-s *)
  | Cvtop T_i32 Convert T_i64 (Some SX_U) (* TODO: is this correct? *) => xa7 :: nil
  | Cvtop T_i32 Convert T_i64 _ => dummy
  | Cvtop T_i32 Convert T_f32 (Some SX_S) => xa8 :: nil
  | Cvtop T_i32 Convert T_f32 (Some SX_U) => xa9 :: nil
  | Cvtop T_i32 Convert T_f32 None => dummy
  | Cvtop T_i32 Convert T_f64 (Some SX_S) => xaa :: nil
  | Cvtop T_i32 Convert T_f64 (Some SX_U) => xab :: nil
  | Cvtop T_i32 Convert T_f64 None => dummy
  | Cvtop T_i32 Convert T_i32 _ => dummy
  | Cvtop T_i64 Convert T_i32 (Some SX_S) => xac :: nil
  | Cvtop T_i64 Convert T_i32 (Some SX_U) => xad :: nil
  | Cvtop T_i64 Convert T_i32 None => dummy
  | Cvtop T_i64 Convert T_f32 (Some SX_S) => xae :: nil
  | Cvtop T_i64 Convert T_f32 (Some SX_U) => xaf :: nil
  | Cvtop T_i64 Convert T_f32 None => dummy
  | Cvtop T_i64 Convert T_f64 (Some SX_S) => xb0 :: nil
  | Cvtop T_i64 Convert T_f64 (Some SX_U) => xb1 :: nil
  | Cvtop T_i64 Convert T_f64 _ => dummy
  | Cvtop T_i64 Convert T_i64 _ => dummy
  | Cvtop T_f32 Convert T_i32 (Some SX_S) => xb2 :: nil
  | Cvtop T_f32 Convert T_i32 (Some SX_U) => xb3 :: nil
  | Cvtop T_f32 Convert T_i32 None => dummy
  | Cvtop T_f32 Convert T_i64 (Some SX_S) => xb4 :: nil
  | Cvtop T_f32 Convert T_i64 (Some SX_U) => xb5 :: nil
  | Cvtop T_f32 Convert T_i64 None => dummy
  | Cvtop T_f32 Convert T_f64 None => xb6 :: nil
  | Cvtop T_f32 Convert T_f64 (Some _) => dummy
  | Cvtop T_f32 Convert T_f32 _ => dummy
  | Cvtop T_f64 Convert T_i32 (Some SX_S) => xb7 :: nil
  | Cvtop T_f64 Convert T_i32 (Some SX_U) => xb8 :: nil
  | Cvtop T_f64 Convert T_i32 None => dummy
  | Cvtop T_f64 Convert T_i64 (Some SX_S) => xb9 :: nil
  | Cvtop T_f64 Convert T_i64 (Some SX_U) => xba :: nil
  | Cvtop T_f64 Convert T_i64 None => dummy
  | Cvtop T_f64 Convert T_f32 None => xbb :: nil
  | Cvtop T_f64 Convert T_f32 (Some _) => dummy
  | Cvtop T_f64 Convert T_f64 _ => dummy
  | Cvtop T_i32 Reinterpret T_f32 None => xbc :: nil
  | Cvtop T_i64 Reinterpret T_f64 None => xbc :: nil
  | Cvtop T_f32 Reinterpret T_i32 None => xbc :: nil
  | Cvtop T_f64 Reinterpret T_i64 None => xbc :: nil
  | Cvtop T_i32 Reinterpret T_i32 _ => dummy
  | Cvtop T_i32 Reinterpret T_i64 _ => dummy
  | Cvtop T_i32 Reinterpret T_f64 _ => dummy
  | Cvtop T_i64 Reinterpret T_i32 _ => dummy
  | Cvtop T_i64 Reinterpret T_i64 _ => dummy
  | Cvtop T_i64 Reinterpret T_f32 _ => dummy
  | Cvtop T_f32 Reinterpret T_i64 _ => dummy
  | Cvtop T_f32 Reinterpret T_f32 _ => dummy
  | Cvtop T_f32 Reinterpret T_f64 _ => dummy
  | Cvtop T_f64 Reinterpret T_i32 _ => dummy
  | Cvtop T_f64 Reinterpret T_f32 _ => dummy
  | Cvtop T_f64 Reinterpret T_f64 _ => dummy
  | Cvtop _ Reinterpret _ (Some _) => dummy
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
  x03 :: with_length (binary_of_vec binary_of_typeidx (List.map (fun f => f.(mf_type)) fs)).

Definition binary_of_module_table (t : module_table) : list byte :=
  binary_of_table_type t.(t_type).

Definition binary_of_tablesec (ts : list module_table) : list byte :=
  x04 :: with_length (binary_of_vec binary_of_module_table ts).

Definition binary_of_memsec (ms : list memory_type) : list byte :=
  x05 :: with_length (binary_of_vec binary_of_memory_type ms).

Definition binary_of_module_glob (g : module_glob) : list byte :=
  binary_of_global_type g.(mg_type) ++
  binary_of_expr g.(mg_init).

Definition binary_of_globalsec (gs : list module_glob) : list byte :=
  x06 :: with_length (binary_of_vec binary_of_module_glob gs).

Definition binary_of_export_desc (ed : module_export_desc) : list byte :=
  match ed with
  | ED_func n => x00 :: binary_of_funcidx n
  | ED_table n => x01 :: binary_of_tableidx n
  | ED_mem n => x02 :: binary_of_memidx n
  | ED_global n => x03 :: binary_of_globalidx n
  end.

Definition binary_of_module_export (e : module_export) : list byte :=
  binary_of_name e.(exp_name) ++
  binary_of_export_desc e.(exp_desc).

Definition binary_of_exportssec (es : list module_export) : list byte :=
  x07 :: with_length (binary_of_vec binary_of_module_export es).

Definition binary_of_module_start (s : module_start) : list byte :=
  binary_of_funcidx s.(start_func).

Definition binary_of_startsec (s : module_start) : list byte :=
  x08 :: with_length (binary_of_vec binary_of_module_start (cons s nil)).

Definition binary_of_module_elem (e : module_element) : list byte :=
  binary_of_tableidx e.(elem_table) ++
  binary_of_expr e.(elem_offset) ++
  binary_of_vec binary_of_funcidx e.(elem_init).

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
  let func := {| fc_locals := mf.(mf_locals); fc_expr := mf.(mf_body) |} in
  let func_bin := binary_of_code_func func in
  let func_len := List.length func_bin in
  leb128.encode_unsigned (bin_of_nat func_len) ++
  func_bin.

Definition binary_of_codesec (fs : list module_func) : list byte :=
  x0a :: with_length (binary_of_vec binary_of_code fs).

Definition binary_of_data (d : module_data) : list byte :=
  binary_of_memidx d.(dt_data) ++
  binary_of_expr d.(dt_offset) ++
  binary_of_vec (fun x => cons x nil) d.(dt_init).

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
