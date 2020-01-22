(** Wasm text format **)
(* (C) M. Bodin - see LICENSE.txt *)

%{

From mathcomp Require Import seq.
Require Import wasm.

%}

(** * Declarations **)

%token<String.string> id
%token I32 I64 F32 F64
%token EOF

%type<value_type> valtype
%type<basic_instruction> instr
%type<basic_instruction> plaininstr
%type<basic_instruction> blockinstr

%start<unit> main

%%

(** * Grammar **)

(** ** Types **)

valtype:
  | I32 { T_i32 }
  | I64 { T_i64 }
  | F32 { T_f32 }
  | F64 { T_f64 }


(** ** Instructions **)

instr:
  | in = plaininstr { in }
  | in = blockinstr { in }

plaininstr:
  | UNREACHABLE { Unreachable }
  | NOP { Nop }
  | BR; l = labelidx { Br l }
  | BRIF; l = labelidx { Br_if l }
  | BRTABLE; l = labelidx { Br_if l }

main: (* TODO *)
