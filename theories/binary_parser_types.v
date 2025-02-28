(*

(** Datatypes used in the binary parser. **)
(* (C) J. Pichon - see LICENSE.txt *)

Require Import common.
Require Export numerics datatypes.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Definition expr := list basic_instruction.

Inductive labelidx : Type :=
| Mk_labelidx : nat -> labelidx.

Inductive funcidx : Type :=
| Mk_funcidx : nat -> funcidx.
Inductive typeidx : Type :=
| Mk_typeidx : nat -> typeidx.

Inductive localidx : Type :=
| Mk_localidx : nat -> localidx.

Inductive globalidx : Type :=
| Mk_globalidx : nat -> globalidx.

Record limits := Mk_limits { lim_min : nat; lim_max : option nat; }.

Inductive elem_type : Type :=
| elem_type_tt : elem_type (* TODO: am I interpreting the spec correctly? *).

Record table_type : Type := Mk_table_type {
  tt_limits : limits;
  tt_elem_type : elem_type;
}.

Record mem_type : Type := Mk_mem_type { mem_type_lims : limits }.

Inductive import_desc : Type :=
| ID_func : nat -> import_desc
| ID_table : table_type -> import_desc
| ID_mem : mem_type -> import_desc
| ID_global : global_type -> import_desc.

Definition name := list ascii.

Record import : Type := Mk_import {
  imp_module : name;
  imp_name : name;
  imp_desc : import_desc;
}.

Record table := Mk_table { t_type : table_type }.

Definition mem := limits.

Record global2 : Type := {
  g_type : global_type;
  g_init : expr;
}.

Record start := { start_func : nat; }.

Record element : Type := {
  elem_table : nat;
  elem_offset : expr;
  elem_init : list nat;
}.

Record func : Type := {
  fc_locals : list value_type;
  fc_expr : expr;
}.

Record data : Type := {
  dt_data : nat;
  dt_offset : expr;
  dt_init : list ascii;
}.

Inductive export_desc : Type :=
| ED_func : nat -> export_desc
| ED_table : nat -> export_desc
| ED_mem : nat -> export_desc
| ED_global : nat -> export_desc.

Record export : Type := {
  exp_name : name;
  exp_desc : export_desc;
}.

Inductive section : Type :=
| Sec_custom : list ascii -> section
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

*)
