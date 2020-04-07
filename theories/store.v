(** Definition of the Wasm store **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

Require Import common.
Require Export numerics bytes datatypes host.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Record instance : Type := (* inst *) {
  i_types : list function_type;
  i_funcs : list immediate;
  i_tab : option immediate;
  i_memory : option immediate;
  i_globs : list immediate;
}.

Inductive function_closure : Type := (* cl *)
| Func_native : instance -> function_type -> list value_type -> list basic_instruction -> function_closure
| Func_host : function_type -> host_function function_closure.

Definition tabinst := list (option function_closure).

Record global : Type := {
  g_mut : mutability;
  g_val : value;
}.

Record store_record : Type := (* s *) Build_store_record {
  s_funcs : list function_closure;
  s_tab : list tabinst;
  s_memory : list memory;
  s_globs : list global;
}.

Inductive administrative_instruction : Type := (* e *)
  | Basic : basic_instruction -> administrative_instruction
  | Trap
  | Callcl : function_closure -> administrative_instruction
  | Label : nat -> seq administrative_instruction -> seq administrative_instruction -> administrative_instruction
  | Local : nat -> instance -> list value -> seq administrative_instruction -> administrative_instruction
  .

Inductive lholed : Type :=
  | LBase : list administrative_instruction -> list administrative_instruction -> lholed
  | LRec : list administrative_instruction -> nat -> list administrative_instruction -> lholed -> list administrative_instruction -> lholed
  .
