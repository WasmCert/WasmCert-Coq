(** a typeclass for a Wasm memory *)
(* (C) J. Pichon - see LICENSE.txt *)

Require Import BinNat.
Require Import bytes.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype.

Module Memory.

Definition mem_make_t Mem_t := byte -> N -> Mem_t.
Definition mem_length_t Mem_t := Mem_t -> N.
Definition mem_grow_t Mem_t := N -> Mem_t -> Mem_t.
Definition mem_lookup_t Mem_t := N -> Mem_t -> option byte.
Definition mem_update_t Mem_t := N -> byte -> Mem_t -> option Mem_t.

Definition mem_ax_lookup_out_of_bounds
  (Mem_t : Type)
  (mem_make : mem_make_t Mem_t)
  (mem_length : mem_length_t Mem_t)
  (mem_grow : mem_grow_t Mem_t)
  (mem_lookup : mem_lookup_t Mem_t)
  (mem_update : mem_update_t Mem_t) :=
  forall mem i, N.ge i (mem_length mem) -> mem_lookup i mem = None.

Definition mem_ax_lookup_make
  (Mem_t : Type)
  (mem_make : mem_make_t Mem_t)
  (mem_length : mem_length_t Mem_t)
  (mem_grow : mem_grow_t Mem_t)
  (mem_lookup : mem_lookup_t Mem_t)
  (mem_update : mem_update_t Mem_t) :=
  forall i len b, N.lt i len -> mem_lookup i (mem_make b len) = Some b.

Definition mem_ax_lookup_update
  (Mem_t : Type)
  (mem_make : mem_make_t Mem_t)
  (mem_length : mem_length_t Mem_t)
  (mem_grow : mem_grow_t Mem_t)
  (mem_lookup : mem_lookup_t Mem_t)
  (mem_update : mem_update_t Mem_t) :=
  forall mem mem' i b, N.lt i (mem_length mem) -> Some mem' = mem_update i b mem -> mem_lookup i mem' = Some b.

Definition mem_ax_lookup_skip
  (Mem_t : Type)
  (mem_make : mem_make_t Mem_t)
  (mem_length : mem_length_t Mem_t)
  (mem_grow : mem_grow_t Mem_t)
  (mem_lookup : mem_lookup_t Mem_t)
  (mem_update : mem_update_t Mem_t) :=
  forall mem mem' i i' b, i <> i' -> Some mem' = mem_update i' b mem -> mem_lookup i mem' = mem_lookup i mem.

Definition mem_ax_length_constant_update
  (Mem_t : Type)
  (mem_make : mem_make_t Mem_t)
  (mem_length : mem_length_t Mem_t)
  (mem_grow : mem_grow_t Mem_t)
  (mem_lookup : mem_lookup_t Mem_t)
  (mem_update : mem_update_t Mem_t) :=
  forall i b mem mem', Some mem' = mem_update i b mem -> mem_length mem' = mem_length mem.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section ClassDef.

Record mixin_of (Mem_t : Type) : Type := Mixin {
  mem_make : byte -> N -> Mem_t;
  mem_length : Mem_t -> N;
  mem_grow : mem_grow_t Mem_t;
  mem_lookup : mem_lookup_t Mem_t;
  mem_update : N -> byte -> Mem_t -> option Mem_t;
  _ : mem_ax_lookup_out_of_bounds Mem_t mem_make mem_length mem_grow mem_lookup mem_update;
  _ : mem_ax_lookup_make Mem_t mem_make mem_length mem_grow mem_lookup mem_update;
  _ : mem_ax_lookup_update Mem_t mem_make mem_length mem_grow mem_lookup mem_update;
  _ : mem_ax_lookup_skip Mem_t mem_make mem_length mem_grow mem_lookup mem_update;
  _ : mem_ax_length_constant_update Mem_t mem_make mem_length mem_grow mem_lookup mem_update;
}.

End ClassDef.

End Memory.
