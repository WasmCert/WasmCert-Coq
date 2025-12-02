(** an implementation of Wasm memory based on a custom implementation of
 something like std::vector.

 Note that Coq's Array is persistent, therefore modifications and lookups are
 not truely O(1). As a result, extraction needs to manually extract Array
 operations to an efficient data structure in OCaml.
 *)

From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat.
From Coq Require Import BinInt BinNat NArith Lia Uint63.
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
Parameter arr_make : PrimInt63.int -> A -> array A.
(* The same as make but initialises its prefix with values from
   the prefix of another array.
   Does not overflow if the length exceeds the make length.
   This is used in the vector_grow function.
 *)
Parameter arr_make_copy: PrimInt63.int -> A -> array A -> PrimInt63.int -> array A.
Parameter arr_get : array A -> PrimInt63.int -> A.
Parameter arr_default : array A -> A.
Parameter arr_set : array A -> PrimInt63.int -> A -> array A.
(* Takes the length and the generator for the block *)
Parameter arr_set_gen : array A -> PrimInt63.int -> PrimInt63.int -> (PrimInt63.int -> A) -> array A.
Parameter arr_length : array A -> PrimInt63.int.
Parameter arr_copy : array A -> array A.

Definition max_arr_length : PrimInt63.int := Uint63.of_Z (Z.of_N byte_limit).

Notation " t .[ i ] " := (arr_get t i) (at level 5).
Notation " t .[ i <- a ] " := (arr_set t i a) (at level 5).

Parameter get_out_of_bounds :
  forall (t : array A) (i : PrimInt63.int),
    PrimInt63.ltb i (arr_length t) = false -> t.[i] = arr_default t.
Parameter get_set_same :
  forall (t : array A) (i : PrimInt63.int) (a : A),
    PrimInt63.ltb i (arr_length t) = true -> t.[i<-a].[i] = a.
Parameter get_set_other :
  forall (t : array A) (i j : PrimInt63.int) (a : A),
    i <> j -> t.[i<-a].[j] = t.[j].
Parameter default_set :
  forall (t : array A) (i : PrimInt63.int) (a : A),
    arr_default t.[i<-a] = arr_default t.
Parameter get_make :
  forall (a : A) (size i : PrimInt63.int),
    (arr_make size a).[i] = a.
Parameter get_make_copy:
  forall (a: A) (size i: PrimInt63.int) (t: array A) (initlen: PrimInt63.int),
    PrimInt63.ltb i size ->
    PrimInt63.leb initlen (arr_length t) ->
    PrimInt63.ltb i (arr_length t) ->
    (arr_make_copy size a t initlen).[i] = t.[i].
Parameter get_make_copy_default:
  forall (a: A) (size i: PrimInt63.int) (t: array A) (initlen: PrimInt63.int),
    PrimInt63.ltb i size ->
    PrimInt63.leb initlen (arr_length t) ->
    PrimInt63.leb initlen i ->
    (arr_make_copy size a t initlen).[i] = a.
Parameter leb_length :
  forall (t : array A),
    PrimInt63.leb (arr_length t) max_arr_length = true.
Parameter length_make :
  forall (size : PrimInt63.int) (a : A),
    arr_length (arr_make size a) =
      Uint63.min size max_arr_length.
Parameter length_make_copy :
  forall (size : PrimInt63.int) (a : A) (t: array A) (initlen: PrimInt63.int),
    arr_length (arr_make_copy size a t initlen) =
      Uint63.min size max_arr_length.
Parameter length_set :
  forall (t : array A) (i : PrimInt63.int) (a : A),
    arr_length t.[i<-a] = arr_length t.

(* Some added axioms for set_gen *)
Parameter length_set_gen :
  forall (t : array A) (i : PrimInt63.int) (len: PrimInt63.int) (gen: PrimInt63.int -> A),
    arr_length (arr_set_gen t i len gen) = arr_length t.

Parameter arr_set_gen_lookup:
  forall n len gen m i,
    PrimInt63.ltb i len ->
    arr_get (arr_set_gen m n len gen) (PrimInt63.add n i) = (gen i).

Parameter arr_set_gen_lt:
  forall n len gen m i,
    PrimInt63.ltb i n ->
    arr_get (arr_set_gen m n len gen) i = arr_get m i.

Parameter arr_set_gen_ge:
  forall n len gen m i,
    PrimInt63.ltb (PrimInt63.add n len) i ->
    arr_get (arr_set_gen m n len gen) i = arr_get m i.
                                         
Parameter get_copy :
  forall (t : array A) (i : PrimInt63.int),
    (arr_copy t).[i] = t.[i].
Parameter length_copy :
  forall (t : array A), arr_length (arr_copy t) = arr_length t.
Parameter array_ext :
  forall (t1 t2 : array A),
    arr_length t1 = arr_length t2 ->
    (forall i : PrimInt63.int,
        PrimInt63.ltb i (arr_length t1) = true -> t1.[i] = t2.[i]) ->
    arr_default t1 = arr_default t2 -> t1 = t2.
Parameter default_copy :
  forall (t : array A), arr_default (arr_copy t) = arr_default t.
Parameter default_make :
  forall (a : A) (size : PrimInt63.int),
    arr_default (arr_make size a) = a.
Parameter get_set_same_default :
  forall (t : array A) (i : PrimInt63.int),
    t.[i<-arr_default t].[i] = arr_default t.
Parameter get_not_default_lt :
  forall (t : array A) (x : PrimInt63.int),
    t.[x] <> arr_default t -> PrimInt63.ltb x (arr_length t) = true.

End Array.

(* A slightly modified implementation of growable arrays, given that point
   update is too slow. *)
Section vector.
  Context {T: Type}.

  Implicit Types x : T.
  
  Definition Uint63_of_N n : PrimInt63.int := Uint63.of_Z (Z.of_N n).
  Definition Uint63_to_N z : N := Z.to_N (Uint63.to_Z z).

  Definition Uint63_of_positive p : PrimInt63.int := Uint63.of_Z (Zpos p).
  Definition Uint63_to_positive z : positive := Z.to_pos (Uint63.to_Z z).
  
  Record vector :=
    { v_data: array T;
      v_size: N;
      v_capacity: N;
      v_init: T;
      v_size_valid: v_size <= v_capacity;
      v_capacity_eq: v_capacity = Uint63_to_N (arr_length v_data);
    }.

  Definition vector_length vec : N :=
    vec.(v_size).

  Definition vector_make (len: N) x : vector.
  Proof.
    remember (N.min len byte_limit) as capped_len.
    refine (@Build_vector (arr_make (Uint63_of_N capped_len) x) capped_len capped_len x _ _).
    - by lias.
    - rewrite length_make; subst.
      unfold max_arr_length, Uint63_to_N, Uint63_of_N.
      rewrite Uint63.min_spec Znat.Z2N.inj_min.
      repeat rewrite of_Z_spec.
      repeat rewrite Znat.Z2N.inj_mod => //; try by lias.
      repeat rewrite Znat.N2Z.id.
      rewrite N.mod_small; cbn; by lias.
  Defined.
    
  Definition vector_lookup vec n : option T :=
    if N.ltb n (vector_length vec) then
      Some (arr_get vec.(v_data) (Uint63_of_N n))
    else None.

  Definition vector_update (vec: vector) (n: N) (x: T) : option vector.
  Proof.
    refine
    (if N.ltb n (vector_length vec) then
      Some (@Build_vector (arr_set vec.(v_data) (Uint63_of_N n) x) vec.(v_size) vec.(v_capacity) vec.(v_init) _ _)
     else None).
    - by apply v_size_valid.
    - rewrite length_set.
      by apply v_capacity_eq.
  Defined.
  
  Definition vector_update_gen (vec: vector) (n: N) (len: N) (gen: N -> T) : option vector.
  Proof.
    refine
    (if N.leb (N.add n len) (vector_length vec) then
      Some (@Build_vector (arr_set_gen vec.(v_data) (Uint63_of_N n) (Uint63_of_N len) (fun offset => gen (Uint63_to_N offset))) vec.(v_size) vec.(v_capacity) vec.(v_init) _ _)
     else None).
    - by apply v_size_valid.
    - rewrite length_set_gen.
      by apply v_capacity_eq.
  Defined.

  Lemma N_min_idem_r : forall n m,
      N.min (N.min n m) m = N.min n m.
  Proof.
    by lias.
  Qed.

  Program Definition vector_grow (vec: vector) (n: N) : option vector :=
    let newsize := vector_length vec + n in
    match newsize <=? byte_limit as p1 return ((newsize <=? byte_limit) = p1) -> _ with
    | true => (fun _ => 
        match newsize <=? vec.(v_capacity) as p2 return (newsize <=? vec.(v_capacity) = p2) -> _ with
        | true =>
            (fun _ => Some (@Build_vector vec.(v_data) newsize vec.(v_capacity) vec.(v_init) _ _))
        | false =>
            let new_capacity := (N.min (N.max newsize (vec.(v_capacity) * 2%N)) byte_limit) in
            let x := vec.(v_init) in
            let new_vd := arr_make_copy (Uint63_of_N new_capacity) x vec.(v_data) (Uint63_of_N vec.(v_size)) in
            (fun _ => Some (@Build_vector new_vd newsize new_capacity x _ _))
        end (Logic.eq_refl (newsize <=? vec.(v_capacity))))
    | false => (fun _ => None)
    end (Logic.eq_refl (newsize <=? byte_limit)).
  Next Obligation.
    by lias.
  Qed.
  Next Obligation.
    by apply v_capacity_eq.
  Qed.
  Next Obligation.
    move/N.leb_spec0 in e0.
    by lias.
  Qed.
  Next Obligation.
    rewrite length_make_copy.
    unfold Uint63_to_N, Uint63_of_N.
    rewrite min_spec Znat.Z2N.inj_min of_Z_spec.
    rewrite Znat.Z2N.inj_mod; try by lias.
    rewrite Znat.N2Z.id.
    rewrite N.mod_small; cbn; by lias.
  Qed.

  Lemma vector_size_bound: forall vec,
      v_size vec <= byte_limit.
  Proof.
    move => vec.
    specialize (@v_size_valid vec) as Hvalid.
    specialize (v_capacity_eq vec) as Hcap.
    unfold Uint63_to_N in Hcap.
    rewrite Hcap in Hvalid.
    specialize (leb_length (v_data vec)) as Hlenub; move/Uint63.lebP in Hlenub.
    unfold max_arr_length in Hlenub.
    clear Hcap.
    cbn in *; by lias.
  Qed.

End vector.

Section MemoryVec.

  Definition memory_vec : Type := @vector byte.
  Definition mv_length := @vector_length byte.
  Definition mv_make n b := @vector_make byte b n.
  Definition mv_lookup i v := @vector_lookup byte v i.
  Definition mv_update i b v := @vector_update byte v i b.
  Definition mv_update_gen i n gen m := @vector_update_gen byte m i n gen.
  Definition mv_grow n v:= @vector_grow byte v n.

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
    forall b len, mv_length (mv_make b len) = N.min len byte_limit.
  Proof.
    done.
  Qed.
    
  Lemma mv_make_lookup:
    forall i len b,
      (i < N.min len byte_limit) ->
      mv_lookup i (mv_make b len) = Some b.
  Proof.
    move => i len b Hlen /=.
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
  move => mem mem' i b Hupdate.
  unfold mv_update, vector_update in Hupdate.
  by remove_bools_options.
Qed.
  
  Lemma mv_update_lookup :
    forall mem mem' i b,
      mv_update i b mem = Some mem' ->
      mv_lookup i mem' = Some b.
  Proof.
    move => mem mem' i b Hupdate.
    unfold mv_lookup, vector_lookup.
    erewrite mv_update_length; eauto.
    unfold mv_update, vector_update in *.
    remove_bools_options => /=.
    rewrite Hif.
    rewrite get_set_same => //.
    unfold vector_length in Hif.
    specialize (v_capacity_eq mem) as Hcap.
    specialize (@v_size_valid _ mem) as Hsize.
    move/N.ltb_spec0 in Hif.
    apply/ltbP.
    unfold Uint63_of_N.
    unfold Uint63_to_N in Hcap.
    rewrite of_Z_spec.
    apply (f_equal Z.of_N) in Hcap.
    rewrite Znat.Z2N.id in Hcap.
    - rewrite - Hcap.
      assert (Z.of_N i mod wB <= Z.of_N i)%Z as Hbound.
      { apply Z.mod_le; by lias. }
      (* lots of transitivity *)
      by lias.
    - specialize (to_Z_bounded (arr_length (v_data mem))).
      by lias.
  Qed.

Lemma mv_update_lookup_ne:
  forall mem mem' i j b,
    i <> j ->
    mv_update j b mem = Some mem' ->
    mv_lookup i mem' = mv_lookup i mem.
Proof.
  move => mem mem' i j b Hneq Hupdate.
  unfold mv_lookup, vector_lookup.
  unfold mv_update, vector_update in Hupdate.
  remove_bools_options => /=.
  move/N.ltb_spec0 in Hif.
  unfold vector_length.
  destruct (i <? v_size mem) eqn:Hindex => //.
  rewrite get_set_other => //.
  unfold Uint63_of_N.
  move => Hinjeq.
  unfold vector_length in Hif.
  move/N.ltb_spec0 in Hindex.
  specialize (@vector_size_bound _ mem) as Hsizebound.
  assert (i < byte_limit) as Hiub; first by lias.
  assert (j < byte_limit) as Hjub; first by lias.
  apply (f_equal to_Z) in Hinjeq.
  do 2 (rewrite of_Z_spec in Hinjeq).
  cbn in *.
  do 2 (rewrite Z.mod_small in Hinjeq => //; last by lias).
  by lias.
Qed.
  
Lemma mv_grow_length :
  forall n mem mem',
    mv_grow n mem = Some mem' ->
    mv_length mem' = (mv_length mem + n)%N.
Proof.
  move => n mem mem'.
  unfold mv_grow, vector_grow.
  generalize (Logic.eq_refl ((vector_length mem + n) <=? byte_limit)).
  generalize ((vector_length mem + n) <=? byte_limit) at 2 3.
  case => Hub => //=.
  generalize (Logic.eq_refl ((vector_length mem + n) <=? v_capacity mem)).
  generalize ((vector_length mem + n) <=? v_capacity mem) at 2 3.
  case => Hgrow //=; move => [<-] => /=; done.
Qed.

Lemma mv_update_ib:
  forall mem i b,
    (i < mv_length mem)%N ->
    mv_update i b mem <> None.
Proof.
  move => mem i b => /=.
  rewrite /mv_length /mv_update /vector_update.
  move => H.
  apply N.ltb_lt in H.
  by rewrite H.
Qed.

Lemma mv_update_oob:
  forall mem i b,
    (i >= mv_length mem)%N ->
    mv_update i b mem = None.
Proof.
  move => mem i b => /=.
  rewrite /mv_length /mv_update /vector_update.
  move => H.
  apply N.ge_le in H; move/N.leb_spec0 in H.
  rewrite N.leb_antisym in H.
  move/negPf in H.
  by rewrite H.
Qed.

Lemma mv_update_gen_ib:
  forall (n len : N) (gen : N -> byte) (m : vector),
  n + len <= mv_length m -> mv_update_gen n len gen m <> None.
Proof.
  move => n len gen m Hle.
  rewrite /mv_update_gen /vector_update_gen.
  move/N.leb_spec0 in Hle.
  by rewrite Hle.
Qed.
  
Lemma mv_update_gen_oob:
  forall (n len : N) (gen : N -> byte) (m : vector),
  n + len > mv_length m -> mv_update_gen n len gen m = None.
Proof.
  move => n len gen m Hgt.
  rewrite /mv_update_gen /vector_update_gen.
  move/N.leb_spec0 in Hgt.
  destruct (n + len <=? mv_length m) eqn:Hle => //.
  - exfalso; by apply Hgt.
  - by rewrite Hle.
Qed.
    
Lemma mv_update_gen_lookup:
  forall n len gen m m' i,
    mv_update_gen n len gen m = Some m' ->
    N.lt i len ->
    mv_lookup (N.add n i) m' = Some (gen i).
Proof.
  move => n len gen m m' i Hupdate Hlt.
  rewrite /mv_update_gen /vector_update_gen /vector_length in Hupdate.
  remove_bools_options.
  rewrite /mv_lookup /vector_lookup => /=.
  replace (n + i <? v_size m) with true; last by lias.
Admitted.

Lemma mv_update_gen_lookup_lt:
  forall n len gen m m' i,
    mv_update_gen n len gen m = Some m' ->
    N.lt i n ->
    mv_lookup i m' = mv_lookup i m.
Proof.
Admitted.


Lemma mv_update_gen_lookup_ge:
  forall n len gen m m' i,
    mv_update_gen n len gen m = Some m' ->
    N.ge i (N.add n len) ->
    mv_lookup i m' = mv_lookup i m.
Proof.
Admitted.
  
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
  generalize (Logic.eq_refl ((vector_length mem + n) <=? byte_limit)).
  generalize ((vector_length mem + n) <=? byte_limit) at 2 3.
  case => Hub => //=.
  generalize (Logic.eq_refl ((vector_length mem + n) <=? v_capacity mem)).
  generalize ((vector_length mem + n) <=? v_capacity mem) at 2 3.
  case => Hgrow //=; move => [<-] => /=; unfold mv_lookup, vector_lookup => /=; rewrite Hlen Hlengrow.
  - done.
  - move/N.leb_spec0 in Hub.
    move/N.leb_spec0 in Hgrow.
    unfold mv_length in *.
    move/N.ltb_spec0 in Hlen.
    move/N.ltb_spec0 in Hlengrow.
    assert (i < byte_limit) as Hibound; first by lias.
    specialize (@v_size_valid _ mem) as Hsize.
    specialize (v_capacity_eq mem) as Hcap.
    unfold Uint63_to_N in Hcap.
    rewrite Hcap in Hsize.
    apply Znat.N2Z.inj_le in Hsize.
    specialize (to_Z_bounded (arr_length (v_data mem))) as HZbound.
    rewrite Znat.Z2N.id in Hsize => //; last by lias.
    rewrite get_make_copy => //; unfold Uint63_of_N.
    + apply/Uint63.ltbP.
      repeat rewrite of_Z_spec.
      do 2 (rewrite Z.mod_small; last by cbn; cbn in Hub; lias).
      by lias.
    + apply/Uint63.lebP.
      rewrite of_Z_spec.
      rewrite Z.mod_small; by lias.
    + apply/Uint63.ltbP.
      rewrite of_Z_spec.
      rewrite Z.mod_small; last by cbn; cbn in Hibound; lias.
      unfold vector_length in Hlen.
      by lias.
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
  - by intros; eapply mv_update_length; eauto.
  - exact mv_update_ib.
  - exact mv_update_oob.
  - exact mv_grow_lookup.
  - exact mv_grow_length.
Qed.
    
End MemoryVec.
