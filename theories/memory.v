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

      (* Technically derivable from the lookup axioms; see the proofs for mem_check_gen *)
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
  
  Lemma mem_lookup_some_length': forall m i b,
      mem_lookup i m = Some b ->
      N.lt i (mem_length m).
  Proof.
    move => m i b Hlookup.
    apply mem_lookup_some_length.
    by rewrite Hlookup.
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
      mem_lookup i m <> None ->
      mem_lookup (N.succ i) m = None ->
      mem_length m = N.succ i.
  Proof.
    move => m i Hlookup1 Hlookup2.
    apply mem_lookup_some_length in Hlookup1.
    apply mem_lookup_none_length in Hlookup2.
    apply N.le_succ_l in Hlookup1.
    by lias.
  Qed.

  Lemma mem_length_extensional_aux: forall m m',
      (forall i, (mem_lookup i m == None) = (mem_lookup i m' == None)) ->
      ~ (mem_length m < mem_length m')%N.
  Proof.
    move => m m' Heq Hlt.
    specialize (Heq (mem_length m)).
    rewrite mem_lookup_oob in Heq; last by lias.
    rewrite eq_refl in Heq; symmetry in Heq; move/eqP in Heq.
    by specialize (mem_lookup_ib Hlt).
  Qed.
  
  Lemma mem_length_extensional : forall m m',
      (forall i, (mem_lookup i m == None) = (mem_lookup i m' == None)) ->
      mem_length m = mem_length m'.
  Proof.
    move => m m' Heq.
    specialize (mem_length_extensional_aux Heq) as Hbound1.
    assert (~ (mem_length m' < mem_length m)%N) as Hbound2.
    { apply mem_length_extensional_aux.
      by move => i; specialize (Heq i).
    }
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

  Context `{BlockUpdateMemory}.

  Lemma mem_update_gen_some_length: forall n len gen m,
      mem_update_gen n len gen m <> None ->
      N.le (N.add n len) (mem_length m).
  Proof.
    move => n len gen m Hupdate.
    destruct (N.leb (N.add n len) (mem_length m)) eqn:Hle; move/N.leb_spec0 in Hle => //.
    exfalso.
    apply Hupdate, mem_update_gen_oob.
    by lias.
  Qed.
  
  Lemma mem_update_gen_some_length': forall n len gen m b,
      mem_update_gen n len gen m = Some b ->
      N.le (N.add n len) (mem_length m).
  Proof.
    move => n len gen m b Hupdate.
    apply mem_update_gen_some_length with (gen := gen); eauto.
    by rewrite Hupdate.
  Qed.
  
  Lemma mem_update_gen_lookup_ex: forall n len gen m m' i,
      mem_update_gen n len gen m = Some m' ->
      (mem_lookup i m == None) = (mem_lookup i m' == None).
  Proof.
    move => n len gen m m' i Hupdate.
    destruct (N.ltb i n) eqn:Hlt; move/N.ltb_spec0 in Hlt.
    - specialize (mem_update_gen_lookup_lt Hupdate Hlt) as Heq.
      by rewrite Heq.
    - destruct (N.ltb i (N.add n len)) eqn:Hlt2; move/N.ltb_spec0 in Hlt2.
      + assert (N.lt (N.sub i n) len) as Hlt3; first by lias.
        specialize (mem_update_gen_lookup Hupdate Hlt3) as Hlookupgen.
        replace (n+(i-n)%N)%N with i in Hlookupgen; last by lias.
        rewrite Hlookupgen.
        assert (mem_lookup i m <> None) as Hlookup.
        { apply mem_lookup_ib.
          apply mem_update_gen_some_length' in Hupdate.
          by lias.
        }
        by lias.
      + specialize (mem_update_gen_lookup_ge Hupdate Hlt2) as Heq.
        by rewrite Heq.
  Qed.
        
  Lemma mem_update_gen_length : forall n len gen m m',
      mem_update_gen n len gen m = Some m' ->
      mem_length m = mem_length m'.
  Proof.
    move => n len gen m m' Hupdate.
    apply mem_length_extensional.
    move => i.
    destruct (mem_lookup i m) eqn:Hlookup1; 
      destruct (mem_lookup i m') eqn:Hlookup2 => //=; exfalso.
    - move/eqP in Hlookup2.
      erewrite <- mem_update_gen_lookup_ex in Hlookup2; eauto.
      by rewrite Hlookup1 in Hlookup2.
    - move/eqP in Hlookup1.
      erewrite -> mem_update_gen_lookup_ex in Hlookup1; eauto.
      by rewrite Hlookup2 in Hlookup1.
  Qed.
  
End BlockUpdateMemory.
