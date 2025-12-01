(** a typeclass for a Wasm mem interface and specification *)

From Coq Require Import BinNat.
From Wasm Require Import bytes common.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype.

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

      (* Technically derivable from the others *)
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
  
  Lemma mem_lookup_some_length: forall m i,
      mem_lookup i m <> None ->
      N.lt i (mem_length m).
  Proof.
    move => m i Hlookup.
    destruct (N.ltb i (mem_length m)) eqn:Hlt; first by lias.
    exfalso.
    move/N.ltb_spec0 in Hlt.
    by apply mem_lookup_oob in Hlt.
  Qed.
  
  Lemma mem_lookup_none_length: forall m i,
      mem_lookup i m = None ->
      N.ge i (mem_length m).
  Proof.
    move => m i Hlookup.
    destruct (N.ltb i (mem_length m)) eqn:Hlt; move/N.ltb_spec0 in Hlt; last done.
    by apply mem_lookup_ib in Hlt.
  Qed.
  
  Lemma mem_length_boundary : forall m i,
      mem_lookup (N.pred i) m <> None ->
      mem_lookup i m = None ->
      mem_length m = i.
  Proof.
    move => m i Hlookup1 Hlookup2.
    apply mem_lookup_some_length in Hlookup1.
    apply mem_lookup_none_length in Hlookup2.
    apply N.le_succ_l in Hlookup1.
    by lias.
  Qed.
  
End Memory.

Section BlockUpdateMemory.
  
  Class BlockUpdateMemory := {
      m: Memory;
      mem_update_gen: N -> N -> (N -> byte) -> mem_t -> option mem_t;
      
      mem_update_gen_ib:
      forall n len gen m,
        N.le (N.add n len) (mem_length m) ->
        mem_update_gen n len gen m <> None;
      
      mem_update_gen_oob:
      forall n len gen m,
        N.gt (N.add n len) (mem_length m) ->
        mem_update_gen n len gen m = None;
      
      mem_update_gen_lookup:
      forall n len gen m m' i,
        mem_update_gen n len gen m = Some m' ->
        N.lt i len ->
        mem_lookup (N.add n i) m' = Some (gen i);
                                         
      mem_update_gen_lookup_lt:
      forall n len gen m m' i,
        mem_update_gen n len gen m = Some m' ->
        N.lt i n ->
        mem_lookup i m' = mem_lookup i m;

      mem_update_gen_lookup_ge:
      forall n len gen m m' i,
        mem_update_gen n len gen m = Some m' ->
        N.ge i (N.add n len) ->
        mem_lookup i m' = mem_lookup i m;
    }.

  #[global]
    Instance memory_from_bum `{bum: BlockUpdateMemory} : Memory := m.
  
  Hint Resolve memory_from_bum : typeclass_instances.

  Lemma mem_update_gen_length `{BlockUpdateMemory}: forall n len gen m m',
      mem_update_gen n len gen m = Some m' ->
      mem_length m = mem_length m'.
  Proof.
    move => n len gen m m' Hupdate.
    apply mem_length_boundary.
    - destruct (N.ltb (N.pred (mem_length m')) (N.add n len)) eqn:Hlt; move/N.ltb_spec0 in Hlt.
      + destruct (N.ltb (N.pred (mem_length m')) n) eqn:Hlt2; move/N.ltb_spec0 in Hlt2.
        { eapply mem_update_gen_lookup_lt in Hlt2; eauto.
          admit.
        }
        
  Admitted.
  
End BlockUpdateMemory.
