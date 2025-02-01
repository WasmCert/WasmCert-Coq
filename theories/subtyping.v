From Wasm Require Import datatypes_properties.
From mathcomp Require Import eqtype ssrbool seq.

(** The mechanisation implements a restricted version of the subtyping system
from the upcoming GC proposal to the current set of Wasm 2.0 types.
Namely, t_1 <: t_2 iff t_1 is the bottom type, or the two types are equal.

This allows smoother transition into the upcoming proposals and avoids
the need to deal with the artificial stack type in Wasm 2.0, which is a
temporary solution.

For more details on the GC proposal, check
[https://github.com/WebAssembly/gc/blob/main/proposals/gc/Overview.md]
**)
Section Subtyping.

Definition value_subtyping (t1: value_type) (t2: value_type) : bool :=
  (t1 == t2) || (t1 == T_bot).

Definition values_subtyping (ts1: list value_type) (ts2: list value_type) : bool :=
  all2 value_subtyping ts1 ts2.

(** Function subtyping and instruction subtyping are covariant on the types
produced and contravariant on the types consumed.
**)
Definition func_subtyping (tf tf': function_type) : bool :=
  let '(Tf ts1 ts2) := tf in
  let '(Tf ts1' ts2') := tf' in
    values_subtyping ts1' ts1 &&
    values_subtyping ts2 ts2'.

Definition instr_subtyping (tf tf': function_type) : Prop :=
  let '(Tf ts1 ts2) := tf in
  let '(Tf ts1' ts2') := tf' in
  exists ts ts' ts1_sub ts2_sub,
    ts1' = ts ++ ts1_sub /\
    ts2' = ts' ++ ts2_sub /\
    values_subtyping ts ts' /\  
    values_subtyping ts1_sub ts1 /\
    values_subtyping ts2 ts2_sub.

End Subtyping.

Notation "t1 <t: t2" := (value_subtyping t1 t2) (at level 30).
Notation "ts1 <ts: ts2" := (values_subtyping ts1 ts2) (at level 60).
Notation "tf1 <ti: tf2" := (instr_subtyping tf1 tf2) (at level 60).
Notation "tf1 <tf: tf2" := (func_subtyping tf1 tf2) (at level 60).
