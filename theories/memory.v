(** a typeclass for a Wasm mem interface and specification *)

From Coq Require Import BinNat.
From Wasm Require Import bytes common.
From HB Require Import structures.
From mathcomp Require Import ssrbool eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Memory.

  (* Some constants regarding Wasm memory *)
  Definition page_size : N := 65536%N.

  Definition page_limit : N := 65536%N.

  Definition byte_limit : N := N.mul page_size page_limit.

  Class Memory := {
      mem_t : Type;
      mem_make : byte -> N -> mem_t;
      mem_length : mem_t -> N;
      mem_lookup : N -> mem_t -> option byte;
      (* Doesn't have to succeed *)
      mem_grow : N -> mem_t -> option mem_t;
      mem_update : N -> byte -> mem_t -> option mem_t;

      mem_lookup_ib :
      forall mem i,
        N.lt i (mem_length mem) ->
        mem_lookup i mem <> None;

      mem_lookup_oob :
      forall mem i,
        N.ge i (mem_length mem) ->
        mem_lookup i mem = None;
      
      mem_make_length :
      forall b len,
        mem_length (mem_make b len) = N.min len byte_limit;

      mem_make_lookup :
      forall i len b,
        N.lt i (N.min len byte_limit) ->
        mem_lookup i (mem_make b len) = Some b;
      
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

      mem_update_ib :
      forall mem i b,
        N.lt i (mem_length mem) ->
        mem_update i b mem <> None;

      mem_update_oob :
      forall mem i b,
        N.ge i (mem_length mem) ->
        mem_update i b mem = None;

      mem_grow_lookup :
      forall i n mem mem',
        N.lt i (mem_length mem) ->
        mem_grow n mem = Some mem' ->
        mem_lookup i mem' = mem_lookup i mem;

      mem_grow_length :
      forall n mem mem',
        mem_grow n mem = Some mem' ->
        mem_length mem' = N.add (mem_length mem) n;
    }.

Context `{Memory}.
  
End Memory.
