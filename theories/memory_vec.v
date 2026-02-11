(** an implementation of Wasm memory based on a custom implementation of
 something like std::vector.

 Note that Coq's Array is persistent, therefore modifications and lookups are
 not truely O(1). As a result, extraction needs to manually extract Array
 operations to an efficient data structure in OCaml.
 *)

From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat.
From Coq Require Import ZArith Lia.
From Wasm Require Import numerics bytes memory common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N_scope.

(* Persistent vector, but removing some functions and relaxing the max_length
   to 2^32-1. Also adding a different method of creating an array for
   growing vectors.
 *)
Section Array.

Context {A: Type}.
  
Parameter array : Type -> Type.
Parameter arr_make : N -> A -> array A.
(* The same as make but initialises its prefix with values from
   the prefix of another array.
   Does not overflow if the length exceeds the make length.
   This is used in the vector_grow function.
 *)
Parameter arr_make_copy: N -> A -> array A -> N -> array A.
Parameter arr_get : array A -> N -> A.
Parameter arr_default : array A -> A.
Parameter arr_set : array A -> N -> A -> array A.
(* Takes the length and the generator for the block *)
Parameter arr_set_gen : array A -> N -> N -> (N -> A) -> array A.
Parameter arr_length : array A -> N.
Parameter arr_copy : array A -> array A.

Definition max_arr_length : N := byte_limit.

Notation " t .[ i ] " := (arr_get t i) (at level 5).
Notation " t .[ i <- a ] " := (arr_set t i a) (at level 5).

Parameter get_out_of_bounds :
  forall (t : array A) (i : N),
    N.ltb i (arr_length t) = false -> t.[i] = arr_default t.
Parameter get_set_same :
  forall (t : array A) (i : N) (a : A),
    N.ltb i (arr_length t) = true -> t.[i<-a].[i] = a.
Parameter get_set_other :
  forall (t : array A) (i j : N) (a : A),
    i <> j -> t.[i<-a].[j] = t.[j].
Parameter default_set :
  forall (t : array A) (i : N) (a : A),
    arr_default t.[i<-a] = arr_default t.
Parameter get_make :
  forall (a : A) (size i : N),
    (arr_make size a).[i] = a.
Parameter get_make_copy:
  forall (a: A) (size i: N) (t: array A) (initlen: N),
    N.ltb i size ->
    N.leb initlen (arr_length t) ->
    N.ltb i (arr_length t) ->
    (arr_make_copy size a t initlen).[i] = t.[i].
Parameter get_make_copy_default:
  forall (a: A) (size i: N) (t: array A) (initlen: N),
    N.ltb i size ->
    N.leb initlen (arr_length t) ->
    N.leb initlen i ->
    (arr_make_copy size a t initlen).[i] = a.
Parameter leb_length :
  forall (t : array A),
    N.leb (arr_length t) max_arr_length = true.
Parameter length_make :
  forall (size : N) (a : A),
    arr_length (arr_make size a) =
      N.min size max_arr_length.
Parameter length_make_copy :
  forall (size : N) (a : A) (t: array A) (initlen: N),
    arr_length (arr_make_copy size a t initlen) =
      N.min size max_arr_length.
Parameter length_set :
  forall (t : array A) (i : N) (a : A),
    arr_length t.[i<-a] = arr_length t.

(* Some added axioms for set_gen *)
Parameter length_set_gen :
  forall (t : array A) (i : N) (len: N) (gen: N -> A),
    arr_length (arr_set_gen t i len gen) = arr_length t.

Parameter arr_set_gen_lookup:
  forall n len gen m i,
    N.ltb i len ->
    arr_get (arr_set_gen m n len gen) (N.add n i) = (gen i).

Parameter arr_set_gen_lt:
  forall n len gen m i,
    N.ltb i n ->
    arr_get (arr_set_gen m n len gen) i = arr_get m i.

Parameter arr_set_gen_ge:
  forall n len gen m i,
    N.leb (N.add n len) i ->
    arr_get (arr_set_gen m n len gen) i = arr_get m i.
                                         
Parameter get_copy :
  forall (t : array A) (i : N),
    (arr_copy t).[i] = t.[i].
Parameter length_copy :
  forall (t : array A), arr_length (arr_copy t) = arr_length t.
Parameter array_ext :
  forall (t1 t2 : array A),
    arr_length t1 = arr_length t2 ->
    (forall i : N,
        N.ltb i (arr_length t1) = true -> t1.[i] = t2.[i]) ->
    arr_default t1 = arr_default t2 -> t1 = t2.
Parameter default_copy :
  forall (t : array A), arr_default (arr_copy t) = arr_default t.
Parameter default_make :
  forall (a : A) (size : N),
    arr_default (arr_make size a) = a.
Parameter get_set_same_default :
  forall (t : array A) (i : N),
    t.[i<-arr_default t].[i] = arr_default t.
Parameter get_not_default_lt :
  forall (t : array A) (x : N),
    t.[x] <> arr_default t -> N.ltb x (arr_length t) = true.

End Array.

(* A slightly modified implementation of growable arrays, given that point
   update is too slow. *)
Section vector.
  Context {T: Type}.

  Implicit Types x : T.

  Context `{def_val: T}.
  
  Record vector :=
    { v_data: array T;
      v_size: N;
      v_capacity: N;
      v_init: T := def_val;
      v_size_valid: v_size <= v_capacity;
      v_capacity_eq: v_capacity = (arr_length v_data);
      v_uninitialised:
      forall (i : N),
        v_size <= i ->
        i < v_capacity ->
        arr_get v_data i = v_init;
    }.

  Definition vector_length vec : N :=
    vec.(v_size).

  Definition vector_make (len: N) : vector.
  Proof.
    remember (N.min len byte_limit) as capped_len.
    refine (@Build_vector (arr_make capped_len def_val) capped_len capped_len _ _ _).
    - by lias.
    - rewrite length_make; subst.
      unfold max_arr_length.
      by lias.
    - move => ???; by lias.
  Defined.
    
  Definition vector_lookup vec n : option T :=
    if N.ltb n (vector_length vec) then
      Some (arr_get vec.(v_data) n)
    else None.

  Definition vector_update (vec: vector) (n: N) (x: T) : option vector.
  Proof.
    destruct (N.ltb n (vector_length vec)) eqn:Hn.
    - refine (Some (@Build_vector (arr_set vec.(v_data) n x) vec.(v_size) vec.(v_capacity) _ _ _)).
      + by apply v_size_valid.
      + rewrite length_set.
        by apply v_capacity_eq.
      + move => i Hlb Hub.
        rewrite get_set_other => //; first by apply v_uninitialised.
        unfold vector_length in Hn.
        by lias.
    - exact None.
  Defined.
  
  Definition vector_update_gen (vec: vector) (n: N) (len: N) (gen: N -> T) : option vector.
  Proof.
    destruct (N.leb (N.add n len) (vector_length vec)) eqn:Hn.
    - refine (Some (@Build_vector (arr_set_gen vec.(v_data) n len (fun offset => gen offset)) vec.(v_size) vec.(v_capacity) _ _ _)).
      + by apply v_size_valid.
      + rewrite length_set_gen.
        by apply v_capacity_eq.
      + move => i Hlb Hub.
        rewrite arr_set_gen_ge => //; first by apply v_uninitialised.
        unfold vector_length in Hn.
        by lias.
    - exact None.
  Defined.

  Lemma N_min_idem_r : forall n m,
      N.min (N.min n m) m = N.min n m.
  Proof.
    by lias.
  Qed.

  Definition vector_grow (vec: vector) (n: N) : option vector.
  Proof.
    remember (vec.(v_size) + n) as newsize.
    destruct (newsize <=? byte_limit) eqn: Hbound.
    - destruct (newsize <=? vec.(v_capacity)) eqn: Hcap.
      + refine (Some (@Build_vector vec.(v_data) newsize vec.(v_capacity) _ _ _)).
        { by lias. }
        { by apply v_capacity_eq. }
        { unfold vector_length in *.
          move => i Hnewsize Hcapi.
          apply v_uninitialised; by lias.
        }
      + remember (N.min (N.max newsize (vec.(v_capacity) * 2%N)) byte_limit) as new_capacity.
        refine (Some (@Build_vector (arr_make_copy new_capacity def_val vec.(v_data) vec.(v_size)) newsize new_capacity _ _ _)).
        { move/N.leb_spec0 in Hbound; by lias. }
        {  
          rewrite length_make_copy.
          unfold max_arr_length.
          by lias.
        }
        { 
          unfold vector_length in *.
          move => i Hnewsize Hcapi.
          rewrite get_make_copy_default => //; try by lias.
          rewrite - v_capacity_eq.
          apply/N.leb_spec0.
          by apply v_size_valid.
        }
    - exact None.
  Defined.

  Lemma vector_size_bound: forall vec,
      v_size vec <= byte_limit.
  Proof.
    move => vec.
    specialize (@v_size_valid vec) as Hvalid.
    specialize (v_capacity_eq vec) as Hcap.
    rewrite Hcap in Hvalid.
    specialize (leb_length (v_data vec)) as Hlenub; move/N.leb_spec0 in Hlenub.
    unfold max_arr_length in Hlenub.
    clear Hcap.
    cbn in *; by lias.
  Qed.

End vector.

Section MemoryVec.

  Definition memory_vec : Type := @vector byte wasm_memory_default_byte.
  Definition mv_length := @vector_length byte wasm_memory_default_byte.
  Definition mv_make n := @vector_make byte wasm_memory_default_byte n.
  Definition mv_lookup i v := @vector_lookup byte wasm_memory_default_byte v i.
  Definition mv_update i b v := @vector_update byte wasm_memory_default_byte v i b.
  Definition mv_update_gen i n gen m := @vector_update_gen byte wasm_memory_default_byte m i n gen.
  Definition mv_grow n v:= @vector_grow byte wasm_memory_default_byte v n.

  Lemma mv_lookup_ib:
    forall mem i,
      (i < mv_length mem)%N ->
      mv_lookup i mem <> None.
  Proof.
    move => mem i => /=.
    rewrite /mv_length /mv_lookup /vector_lookup.
    move => H.
    apply N.ltb_lt in H.
    by rewrite H.
  Qed.

  Lemma mv_lookup_oob:
    forall mem i,
      (i >= mv_length mem)%N ->
      mv_lookup i mem = None.
  Proof.
    move => mem i => /=.
    rewrite /mv_length /mv_lookup /vector_lookup.
    move => H.
    apply N.ge_le in H; move/N.leb_spec0 in H.
    rewrite N.leb_antisym in H.
    move/negPf in H.
    by rewrite H.
  Qed.

  Lemma mv_make_length:
    forall len, mv_length (mv_make len) = N.min len byte_limit.
  Proof.
    done.
  Qed.
    
  Lemma mv_make_lookup:
    forall i len,
      (i < N.min len byte_limit) ->
      mv_lookup i (mv_make len) = Some wasm_memory_default_byte.
  Proof.
    move => i len Hlen /=.
    unfold mv_lookup, vector_lookup.
    setoid_rewrite mv_make_length.
    move/N.ltb_spec0 in Hlen; rewrite Hlen => /=.
    unfold mv_make => /=.
    by rewrite get_make.
  Qed.

Lemma mv_update_length :
  forall mem mem' i b,
    mv_update i b mem = Some mem' ->
    mv_length mem' = mv_length mem.
Proof.
  move => mem mem' i b.
  rewrite /mv_update /vector_update.
  simplify_dependent_case.
  by move => [<-] /=.
Qed.
  
Lemma mv_update_lookup :
  forall mem mem' i b,
    mv_update i b mem = Some mem' ->
    mv_lookup i mem' = Some b.
Proof.
  move => mem mem' i b.
  rewrite /mv_lookup /vector_lookup.
  move => Hupdate.
  erewrite mv_update_length; eauto.
  unfold mv_update, vector_update in Hupdate.
  simplify_dependent_case_hyp Hupdate.
  move => [<-] /=.
  rewrite Hdep_case get_set_same => //.
  unfold vector_length in Hdep_case.
  specialize (v_capacity_eq mem) as Hcap.
  specialize (@v_size_valid _ _ mem) as Hsize.
  by lias.
Qed.

  
Lemma mv_update_lookup_ne:
  forall mem mem' i j b,
    i <> j ->
    mv_update j b mem = Some mem' ->
    mv_lookup i mem' = mv_lookup i mem.
Proof.
  move => mem mem' i j b Hneq.
  unfold mv_lookup, vector_lookup.
  unfold mv_update, vector_update.
  simplify_dependent_case.
  move => [<-] /=.
  unfold vector_length.
  destruct (i <? v_size mem) eqn:Hindex => //.
  rewrite get_set_other => //.
  by lias.
Qed.
  
Lemma mv_grow_length :
  forall n mem mem',
    mv_grow n mem = Some mem' ->
    mv_length mem' = (mv_length mem + n)%N.
Proof.
  move => n mem mem'.
  unfold mv_grow, vector_grow.
  do 2 simplify_dependent_case => //; move => [<-] => /=; done.
Qed.

Lemma mv_update_ib:
  forall mem i b,
    (i < mv_length mem)%N ->
    mv_update i b mem <> None.
Proof.
  move => mem i b Hlt => /=.
  rewrite /mv_update /vector_update.
  simplify_dependent_case.
  unfold mv_length in Hlt.
  apply N.ltb_lt in Hlt.
  by lias.
Qed.

Lemma mv_update_oob:
  forall mem i b,
    (i >= mv_length mem)%N ->
    mv_update i b mem = None.
Proof.
  move => mem i b Hge => /=.
  rewrite /mv_update /vector_update.
  simplify_dependent_case.
  exfalso.
  unfold mv_length in Hge.
  by lias.
Qed.

Lemma mv_update_gen_ib:
  forall (n len : N) (gen : N -> byte) (m : vector),
  n + len <= mv_length m -> mv_update_gen n len gen m <> None.
Proof.
  move => n len gen m Hlt.
  rewrite /mv_update_gen /vector_update_gen.
  simplify_dependent_case.
  unfold mv_length in Hlt.
  apply N.leb_le in Hlt.
  by lias.
Qed.
  
Lemma mv_update_gen_oob:
  forall (n len : N) (gen : N -> byte) (m : vector),
  n + len > mv_length m -> mv_update_gen n len gen m = None.
Proof.
  move => n len gen m Hgt.
  rewrite /mv_update_gen /vector_update_gen.
  simplify_dependent_case; exfalso.
  move/N.leb_spec0 in Hgt.
  by lias.
Qed.
    
Lemma mv_update_gen_lookup:
  forall n len gen m m' i,
    mv_update_gen n len gen m = Some m' ->
    N.lt i len ->
    mv_lookup (N.add n i) m' = Some (gen i).
Proof.
  move => n len gen m m' i Hupdate Hlt.
  rewrite /mv_update_gen /vector_update_gen /vector_length in Hupdate.
  simplify_dependent_case_hyp Hupdate.
  move => [<-] => /=.
  rewrite /mv_lookup /vector_lookup => /=.
  replace (n + i <? v_size m) with true; last by lias.
  rewrite arr_set_gen_lookup; by lias.
Qed.
  
Lemma mv_update_gen_lookup_lt:
  forall n len gen m m' i,
    mv_update_gen n len gen m = Some m' ->
    N.lt i n ->
    mv_lookup i m' = mv_lookup i m.
Proof.
  move => n len gen m m' i Hupdate Hlt.
  rewrite /mv_update_gen /vector_update_gen /vector_length in Hupdate.
  simplify_dependent_case_hyp Hupdate.
  move => [<-] => /=.
  rewrite /mv_lookup /vector_lookup => /=.
  rewrite arr_set_gen_lt; by lias.
Qed.
  
Lemma mv_update_gen_lookup_ge:
  forall n len gen m m' i,
    mv_update_gen n len gen m = Some m' ->
    N.ge i (N.add n len) ->
    mv_lookup i m' = mv_lookup i m.
Proof.
  move => n len gen m m' i Hupdate Hlt.
  rewrite /mv_update_gen /vector_update_gen /vector_length in Hupdate.
  simplify_dependent_case_hyp Hupdate.
  move => [<-] => /=.
  rewrite /mv_lookup /vector_lookup => /=.
  by rewrite arr_set_gen_ge; lias.
Qed.
  
Lemma mv_grow_lookup :
  forall i n mem mem',
    (i < mv_length mem)%N ->
    mv_grow n mem = Some mem' ->
    mv_lookup i mem' = mv_lookup i mem.
Proof.
  move => i n mem mem' Hlen.
  assert (i < mv_length mem + n) as Hlengrow; first by lias.
  move/N.ltb_spec0 in Hlen.
  move/N.ltb_spec0 in Hlengrow.
  unfold mv_grow, vector_grow.
  do 2 simplify_dependent_case; move => [<-] => /=; unfold mv_lookup, vector_lookup => /=; rewrite Hlen Hlengrow.
  - done.
  - unfold mv_length, vector_length in *.
    move/N.leb_spec0 in Hdep_case.
    move/N.leb_spec0 in Hdep_case0.
    move/N.ltb_spec0 in Hlen.
    move/N.ltb_spec0 in Hlengrow.
    assert (i < byte_limit) as Hibound; first by lias.
    specialize (@v_size_valid _ _ mem) as Hsize.
    specialize (v_capacity_eq mem) as Hcap.
    rewrite Hcap in Hsize.
    unfold vector_length in Hlen.
    rewrite get_make_copy => //; by lias.
Qed.

Lemma mv_grow_default:
  forall (n len : N) (mem mem' : memory_vec) (i : N),
  i < n ->
  mv_grow n mem = Some mem' ->
  mv_length mem = len ->
  mv_lookup (len + i) mem' = Some wasm_memory_default_byte.
Proof.
  move => n len mem mem' i Hlt Hgrow Hlen.
  unfold mv_grow, vector_grow in *.
  simplify_dependent_case_hyp Hgrow.
  simplify_dependent_case; move => [<-] => /=; unfold mv_lookup, vector_lookup => /=; subst; unfold mv_length.
  - unfold vector_length; replace (_ <? _) with true; last by lias.
    f_equal.
    apply v_uninitialised; last by lias.
    by lias.
  - unfold vector_length; replace (_ <? _) with true; last by clear - Hlt; lias.
    f_equal.
    rewrite get_make_copy_default; try by lias.
    + apply/N.ltb_spec0.
      move/N.leb_spec0 in Hdep_case.
      by lias.
    + rewrite - v_capacity_eq.
      apply/N.leb_spec0.
      by apply v_size_valid.
Qed.

#[export]
  Instance Memory_vec: BlockUpdateMemory.
Proof.
  eapply (@Build_BlockUpdateMemory (@Build_Memory memory_vec mv_make mv_length mv_lookup mv_grow mv_update _ _ _ _ _ _ _ _ _ _ _) mv_update_gen).
  Unshelve.
  - exact mv_update_gen_ib.
  - exact mv_update_gen_oob.
  - exact mv_update_gen_lookup.
  - exact mv_update_gen_lookup_lt.
  - exact mv_update_gen_lookup_ge.
  - exact mv_lookup_ib.
  - exact mv_lookup_oob.
  - exact mv_make_length.
  - exact mv_make_lookup.
  - exact mv_update_lookup.
  - exact mv_update_lookup_ne.
  - exact mv_update_ib.
  - exact mv_update_oob.
  - exact mv_grow_lookup.
  - exact mv_grow_length.
  - exact mv_grow_default.
Qed.
    
End MemoryVec.
