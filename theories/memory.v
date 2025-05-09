(** a typeclass for a Wasm mem interface and specification *)

From Coq Require Import BinNat.
From Wasm Require Import bytes common.
From HB Require Import structures.
From mathcomp Require Import ssrbool eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Memory.

  Class Memory := {
      mem_t : Type;
      mem_make : byte -> N -> mem_t;
      mem_length : mem_t -> N;
      mem_lookup : N -> mem_t -> option byte;
      mem_grow : N -> mem_t -> mem_t;
      mem_update : N -> byte -> mem_t -> option mem_t;

      mem_eq_dec:
      forall (m1 m2: mem_t),
        {m1 = m2} + {m1 <> m2};
      
      mem_lookup_oob :
      forall mem i,
        N.ge i (mem_length mem) ->
        mem_lookup i mem = None;
      
      mem_make_length :
      forall b len,
        mem_length (mem_make b len) = len;

      mem_make_lookup :
      forall i len b,
        N.lt i len ->
        mem_lookup i (mem_make b len) = Some b;
      
(*      mem_update_exists :
      forall mem i b,
        N.lt i (mem_length mem) ->
        { mem' | mem_update i b mem = Some mem'};*)

      mem_update_lookup :
      forall mem mem' i b,
        mem_update i b mem = Some mem' ->
        mem_lookup i mem' = Some b;
      
      mem_update_lookup_ne :
      forall mem mem' i i' b,
        i <> i' ->
        mem_update i' b mem = Some mem' ->
        mem_lookup i mem' = mem_lookup i mem;
      
      mem_update_length :
      forall i b mem mem',
        mem_update i b mem = Some mem' ->
        mem_length mem' = mem_length mem;

      mem_grow_lookup :
      forall i n mem mem',
        N.lt i (mem_length mem) ->
        mem_grow n mem = mem' ->
        mem_lookup i mem' = mem_lookup i mem;

      mem_grow_length :
      forall n mem mem',
        mem_grow n mem = mem' ->
        mem_length mem' = N.add (mem_length mem) n;
    }.

Context `{Memory}.
  
Definition mem_eqb v1 v2 : bool := mem_eq_dec v1 v2.
Definition eqmemP : Equality.axiom mem_eqb :=
  eq_dec_Equality_axiom mem_eq_dec.

HB.instance Definition mem_eqMixin := hasDecEq.Build mem_t eqmemP.
  
End Memory.

(* Some constants regarding Wasm memory *)
Definition page_size : N := 65536%N.

Definition page_limit : N := 65536%N.
