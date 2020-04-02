Require Import datatypes_properties numerics.
From compcert Require Import Integers.
From parseque Require Import Parseque.
Require Import Ascii Byte.
Require Import leb128.
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
  encode_unsigned (BinNatDef.N.of_nat n).

Definition binary_of_idx n := binary_of_u32_nat n.

Definition binary_of_vec {A} (f : A -> list byte) (es : list A) : list byte :=
  (binary_of_u32_nat (List.length es)) ++ (List.concat (List.map f es)).

Definition binary_of_memarg a o : list byte :=
  binary_of_u32_nat a ++ binary_of_u32_nat o.

Definition binary_of_i32 (x : i32) : list byte :=
  (* TODO *)
  x00 :: x00 :: x00 :: nil.

Definition binary_of_i64 (x : i64) : list byte :=
  (* TODO *)
  x00 :: x00 :: x00 :: nil.

Definition binary_of_f32 (x : f32) : list byte :=
  (* TODO *)
  x00 :: x00 :: x00 :: nil.

Definition binary_of_f64 (x : f64) : list byte :=
  (* TODO *)
  x00 :: x00 :: x00 :: nil.

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
  | Load T_f64 None a o => x2b :: binary_of_memarg a o
  | Load T_i32 (Some (Tp_i8, sx_S)) a o => x2c :: binary_of_memarg a o
  | Load T_i32 (Some (Tp_i8, sx_U)) a o => x2d :: binary_of_memarg a o
  | Load T_i32 (Some (Tp_i16, sx_S)) a o => x2e :: binary_of_memarg a o
  | Load T_i32 (Some (Tp_i16, sx_U)) a o => x2f :: binary_of_memarg a o
  | Load T_i64 (Some (Tp_i8, sx_S)) a o => x30 :: binary_of_memarg a o
  | Load T_i64 (Some (Tp_i8, sx_U)) a o => x31 :: binary_of_memarg a o
  | Load T_i64 (Some (Tp_i16, sx_S)) a o => x32 :: binary_of_memarg a o
  | Load T_i64 (Some (Tp_i16, sx_U)) a o => x33 :: binary_of_memarg a o
  | Load T_i64 (Some (Tp_i32, sx_S)) a o => x34 :: binary_of_memarg a o
  | Load T_i64 (Some (Tp_i32, sx_U)) a o => x35 :: binary_of_memarg a o
  | Store T_i32 None a o => x36 :: binary_of_memarg a o
  | Store T_i64 None a o => x37 :: binary_of_memarg a o
  | Store T_f32 None a o => x38 :: binary_of_memarg a o
  | Store T_f64 None a o => x39 :: binary_of_memarg a o
  | Store T_i32 (Some Tp_i8) a o => x3a :: binary_of_memarg a o
  | Store T_i32 (Some Tp_i16) a o => x3b :: binary_of_memarg a o
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
  | Relop_i T_i32 Eq => x46 :: nil
  | Relop_i T_i32 Ne => x47 :: nil
  | Relop_i T_i32 (Lt sx_S) => x48 :: nil
  | Relop_i T_i32 (Lt sx_U) => x49 :: nil
  | Relop_i T_i32 (Gt sx_S) => x4a :: nil
  | Relop_i T_i32 (Gt sx_U) => x4b :: nil
  | Relop_i T_i32 (Le sx_S) => x4c :: nil
  | Relop_i T_i32 (Le sx_U) => x4d :: nil
  | Relop_i T_i32 (Ge sx_S) => x4e :: nil
  | Relop_i T_i32 (Ge sx_U) => x4f :: nil
  | Testop T_i64 Eqz => x50 :: nil
  | Relop_i T_i64 Eq => x51 :: nil
  | Relop_i T_i64 Ne => x52 :: nil
  | Relop_i T_i64 (Lt sx_S) => x53 :: nil
  | Relop_i T_i64 (Lt sx_U) => x54 :: nil
  | Relop_i T_i64 (Gt sx_S) => x55 :: nil
  | Relop_i T_i64 (Gt sx_U) => x56 :: nil
  | Relop_i T_i64 (Le sx_S) => x57 :: nil
  | Relop_i T_i64 (Le sx_U) => x58 :: nil
  | Relop_i T_i64 (Ge sx_S) => x59 :: nil
  | Relop_i T_i64 (Ge sx_U) => x5a :: nil
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

  | _ => (* TODO: deal with all the other cases *) x00 :: x00 :: x00 :: nil
  end.

Definition binary_of_expr bes := List.concat (List.map binary_of_be bes) ++ x0b :: nil.

Definition binary_of_module (m : module) : list byte :=
  (* TODO *)
  nil.
