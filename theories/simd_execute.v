From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat.
From Wasm Require Import datatypes.
From Coq Require Import String.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Cannot use Module Type + Declare Module because it doesn't extract *)
Module SIMD_ops.
  
Parameter app_vunop_str : vunop -> string -> string.
Parameter app_vbinop_str : vbinop -> string -> string -> string.
Parameter app_vternop_str : vternop -> string -> string -> string -> string.
Parameter app_vtestop_str : vtestop -> string -> string.
Parameter app_vshiftop_str : vtestop -> string -> string -> string.

End SIMD_ops.

Module Export simd_ops_export := SIMD_ops.

