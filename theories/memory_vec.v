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
   to 2^32-1. *)
Section Array.

Context {A: Type}.
  
Parameter array : Type -> Type.
Parameter arr_make : PrimInt63.int -> A -> array A.
(* The same as make but initialises its prefix with values from
   the prefix of another array.
   Does not overflow if the length exceeds the make length.
   This is used in the vector_grow function.
 *)
Parameter arr_make_init: PrimInt63.int -> A -> array A -> PrimInt63.int -> array A.
Parameter arr_get : array A -> PrimInt63.int -> A.
Parameter arr_default : array A -> A.
Parameter arr_set : array A -> PrimInt63.int -> A -> array A.
Parameter arr_length : array A -> PrimInt63.int.
Parameter arr_copy : array A -> array A.

Definition max_arr_length : PrimInt63.int := Uint63.of_Z (Zpos 0xffffffff).

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
Parameter get_make_init:
  forall (a: A) (size i: PrimInt63.int) (t: array A) (initlen: PrimInt63.int),
    PrimInt63.ltb i size ->
    PrimInt63.leb initlen (arr_length t) ->
    PrimInt63.ltb i (arr_length t) ->
    (arr_make_init size a t initlen).[i] = t.[i].
Parameter get_make_init_default:
  forall (a: A) (size i: PrimInt63.int) (t: array A) (initlen: PrimInt63.int),
    PrimInt63.ltb i size ->
    PrimInt63.leb initlen (arr_length t) ->
    PrimInt63.leb initlen i ->
    (arr_make_init size a t initlen).[i] = a.
Parameter leb_length :
  forall (t : array A),
    PrimInt63.leb (arr_length t) max_arr_length = true.
Parameter length_make :
  forall (size : PrimInt63.int) (a : A),
    arr_length (arr_make size a) =
      (if PrimInt63.leb size max_arr_length then size else max_arr_length).
Parameter length_make_init :
  forall (size : PrimInt63.int) (a : A) (t: array A) (initlen: PrimInt63.int),
    arr_length (arr_make_init size a t initlen) =
      (if PrimInt63.leb size max_arr_length then size else max_arr_length).
Parameter length_set :
  forall (t : array A) (i : PrimInt63.int) (a : A),
    arr_length t.[i<-a] = arr_length t.
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
      (*v_size_valid: v_size <= v_capacity;
      v_capacity_eq: v_capacity = Uint63_to_N (arr_length v_data);*)
    }.

  Coercion Uint63.of_Z: Z >-> PrimInt63.int.

  Coercion Uint63_of_N: N >-> PrimInt63.int.

  Coercion Uint63_of_positive: positive >-> PrimInt63.int.

  Definition vector_len vec : N :=
    vec.(v_size).

  Definition vector_make (len: N) x : vector :=
    Build_vector (arr_make len x) len len x.

  Definition vector_lookup vec n : option T :=
    if n <? vector_len vec then
      Some (arr_get vec.(v_data) n)
    else None.

  Definition vector_update vec n x : option vector :=
    if n <? vector_len vec then
      Some (Build_vector (arr_set vec.(v_data) n x) vec.(v_size) vec.(v_capacity) vec.(v_init))
    else None.
          
  Definition vector_grow vec n : vector :=
    let newsize := vector_len vec + n in
    if newsize <=? vec.(v_capacity) then
      Build_vector vec.(v_data) newsize vec.(v_capacity) vec.(v_init)
    else
      let new_capacity := N.max newsize (vec.(v_capacity) * 2%N) in
      let x := vec.(v_init) in
      let new_vd := arr_make_init new_capacity x vec.(v_data) vec.(v_size) in
      Build_vector new_vd newsize new_capacity x.
  
End vector.

Section MemoryVec.

  Definition memory_vec : Type := @vector byte.
  Definition mv_length := @vector_len byte.
  Definition mv_make n b := @vector_make byte b n.
  Definition mv_lookup i v := @vector_lookup byte v i.
  Definition mv_update i b v:= @vector_update byte v i b.
  Definition mv_grow n v:= @vector_grow byte v n.

Axiom array_neq: forall (mem1 mem2: memory_vec),
    mem1 <> mem2.

  Lemma mv_eq_dec: forall (mem1 mem2: memory_vec),
      {mem1 = mem2} + {mem1 <> mem2}.
  Proof.
    right; apply array_neq.
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
    forall b len, mv_length (mv_make b len) = len.
  Proof.
    done.
  Qed.
    
  Lemma mv_make_lookup:
    forall i len b,
      (i < len)%N ->
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
    unfold vector_len in Hif.
    apply/Uint63.ltbP.
    admit.
  Admitted.

Lemma mv_update_lookup_ne:
  forall mem mem' i j b,
    i <> j ->
    mv_update j b mem = Some mem' ->
    mv_lookup i mem' = mv_lookup i mem.
Proof.
  move => mem mem' i j b Hneq Hupdate.
  unfold mv_lookup.
  admit.
Admitted.
  
Lemma mv_grow_length :
  forall n mem mem',
    mv_grow n mem = mem' ->
    mv_length mem' = (mv_length mem + n)%N.
Proof.
  move => n mem mem' Hgrow.
  unfold mv_grow in Hgrow; subst.
  unfold mv_length => /=.
  admit.
Admitted.

Lemma mv_grow_lookup :
  forall i n mem mem',
    (i < mv_length mem)%N ->
    mv_grow n mem = mem' ->
    mv_lookup i mem' = mv_lookup i mem.
Proof.
  move => i n mem mem' Hlen Hgrow.
  unfold mv_lookup.
  move/N.ltb_spec0 in Hlen.
Admitted.
  
#[export]
  Instance Memory_vec: Memory.
Proof.
  apply (@Build_Memory memory_vec mv_make mv_length mv_lookup mv_grow mv_update).
  - exact mv_eq_dec.
  - exact mv_lookup_oob.
  - exact mv_make_length.
  - exact mv_make_lookup.
  - exact mv_update_lookup.
  - exact mv_update_lookup_ne.
  - by intros; eapply mv_update_length; eauto.
  - exact mv_grow_lookup.
  - exact mv_grow_length.
Qed.

End MemoryVec.

(*

  (*
  (* Efficient tree building, starting from 1 *)
Fixpoint gmap_iota (offset: positive) (len: positive) (b: byte) : gmap positive byte :=
  match len with
  | xH => {[ offset := b ]}
  | xO p => (gmap_iota offset p b) ∪ (gmap_iota (offset + p) p b)
  | xI p => <[ (offset + (xO p)) := b ]> ((gmap_iota offset p b) ∪ (gmap_iota (offset + p) p b))
  end.

(*
Lemma gmap_iota_disjoint :
  forall offset len b,
    map_disjoint (gmap_iota offset len b) (gmap_iota (offset + len) len b).
Proof.
  move => offset len; move: offset.
  induction len.
Qed.
*)

Lemma gmap_iota_spec: forall offset len b,
    map_to_list (gmap_iota offset len b) ≡
      (List.map (fun i => (Pos.of_nat i, b)) (iota (Pos.to_nat offset) (Pos.to_nat len))).
Proof.
  move => offset len; move: offset.
  induction len; move => offset b => /=.
  (* xI *)
  - rewrite (map_to_list_insert _ (offset+len~0) b).
Qed.

Definition mt_make : byte -> N -> memory_tree.
Proof.
  refine (fun v (len: N) =>
    {| mt_init := v;
      mt_data :=
        match len with
        | N0 => ∅
        | Npos p => gmap_iota 1 p v
        end;
      mt_size := len
    |}).
  
Defined.
*)
End MemoryList.
*)
