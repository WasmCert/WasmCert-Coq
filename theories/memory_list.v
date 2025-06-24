(** an implementation of Wasm memory based on a list *)

From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat.
From Coq Require Import BinNums ZArith NArith Lia.
From Wasm Require Import numerics bytes memory common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MemoryList.

  Record memory_list : Type := {
      ml_init : byte;
      ml_data : list byte;
    }.

  Definition ml_make :=
    fun v len =>
      let capped_len := N.min len byte_limit in
      {| ml_init := v; ml_data := mkseq (fun _ => v) (N.to_nat capped_len) |}.

  Definition ml_length :=
    fun ml => N.of_nat (size ml.(ml_data)).

  Definition ml_grow :=
    fun len_delta ml =>
      let new_length := N.add len_delta (N.of_nat (length ml.(ml_data))) in
      if new_length <=? byte_limit then
      Some {|
          ml_init := ml.(ml_init);
          ml_data := ml.(ml_data) ++ mkseq (fun _ => ml.(ml_init)) (N.to_nat len_delta)
        |}
      else None.

  Definition ml_lookup :=
    fun i ml =>
      if N.ltb i (ml_length ml) then
        Some (seq.nth ml.(ml_init) ml.(ml_data) (N.to_nat i))
      else None.

  Definition ml_update :=
    fun i v ml =>
      if N.ltb i (ml_length ml)
      then Some {| ml_init := ml.(ml_init);
                  ml_data := set_nth ml.(ml_init) ml.(ml_data) (N.to_nat i) v
                |}
      else None.

  Lemma ml_lookup_ib:
    forall mem i,
      (i < ml_length mem)%N ->
      ml_lookup i mem <> None.
  Proof.
    move => mem i => /=.
    rewrite /ml_length /ml_lookup.
    move => H.
    apply N.ltb_lt in H.
    by rewrite H.
  Qed.

  Lemma ml_lookup_oob:
    forall mem i,
      (i >= ml_length mem)%N ->
      ml_lookup i mem = None.
  Proof.
    move => mem i => /=.
    rewrite /ml_length /ml_lookup.
    move => H.
    apply N.ge_le in H; move/N.leb_spec0 in H.
    rewrite N.leb_antisym in H.
    move/negPf in H.
    by rewrite H.
  Qed.
  
  Lemma ml_make_length:
    forall b len,
      ml_length (ml_make b len) = N.min len byte_limit.
  Proof.
    move => b len => /=.
    unfold ml_length, ml_make.
    rewrite size_mkseq.
    by rewrite N2Nat.id.
  Qed.

  Lemma ml_make_lookup:
    forall i len b,
      (i < N.min len byte_limit)%N ->
      ml_lookup i (ml_make b len) = Some b.
  Proof.
    move => i len b Hlen /=.
    unfold ml_lookup.
    erewrite ml_make_length; eauto.
    move/N.ltb_spec0 in Hlen; rewrite Hlen => /=.
    rewrite nth_mkseq => //.
    by lias.
  Qed.

Lemma ml_update_length :
  forall mem mem' i b,
    ml_update i b mem = Some mem' ->
    ml_length mem' = ml_length mem.
Proof.
  move => mem mem' i b Hupdate.
  unfold ml_update in Hupdate.
  remove_bools_options.
  unfold ml_length in * => /=.
  rewrite size_set_nth.
  f_equal.
  apply/ssrnat.maxn_idPr.
  by lias.
Qed.

  Lemma Nat2N_inj_le: forall n m,
      n <= m ->
      (N.of_nat n <= N.of_nat m)%N.
  Proof.
    by lias.
  Qed.
  
  Lemma ml_update_lookup :
    forall mem mem' i b,
      ml_update i b mem = Some mem' ->
      ml_lookup i mem' = Some b.
  Proof.
    move => mem mem' i b Hupdate.
    unfold ml_lookup.
    erewrite ml_update_length; eauto.
    unfold ml_update in *.
    remove_bools_options => /=.
    by rewrite nth_set_nth /= eq_refl.
  Qed.

Lemma ml_update_lookup_ne:
  forall mem mem' i j b,
    i <> j ->
    ml_update j b mem = Some mem' ->
    ml_lookup i mem' = ml_lookup i mem.
Proof.
  move => mem mem' i j b Hneq Hupdate.
  unfold ml_lookup.
  erewrite ml_update_length; eauto.
  unfold ml_update in *.
  remove_bools_options => /=.
  destruct (i <? ml_length mem)%N eqn:Hlt => //.
  f_equal.
  rewrite nth_set_nth => /=.
  replace ((N.to_nat i) == (N.to_nat j)) with false => //.
  by lias.
Qed.

Lemma ml_grow_length :
  forall n mem mem',
    ml_grow n mem = Some mem' ->
    ml_length mem' = (ml_length mem + n)%N.
Proof.
  move => n mem mem' Hgrow.
  unfold ml_grow in Hgrow; subst.
  unfold ml_length.
  remove_bools_options => /=.
  move/Nat.leb_spec0 in Hif.
  rewrite size_cat size_mkseq.
  by lias.
Qed.

Lemma ml_update_ib:
  forall mem i b,
    (i < ml_length mem)%N ->
    ml_update i b mem <> None.
Proof.
  move => mem i b => /=.
  rewrite /ml_length /ml_update.
  move => H.
  apply N.ltb_lt in H.
  by rewrite H.
Qed.

Lemma ml_update_oob:
  forall mem i b,
    (i >= ml_length mem)%N ->
    ml_update i b mem = None.
Proof.
  move => mem i b => /=.
  rewrite /ml_length /ml_update.
  move => H.
  apply N.ge_le in H; move/N.leb_spec0 in H.
  rewrite N.leb_antisym in H.
  move/negPf in H.
  by rewrite H.
Qed.

Lemma ml_grow_lookup :
  forall i n mem mem',
    (i < ml_length mem)%N ->
    ml_grow n mem = Some mem' ->
    ml_lookup i mem' = ml_lookup i mem.
Proof.
  move => i n mem mem' Hlen Hgrow.
  unfold ml_lookup.
  move/N.ltb_spec0 in Hlen.
  rewrite Hlen.
  erewrite ml_grow_length; eauto.
  replace (i <? ml_length mem + n)%N with true; last by lias.
  f_equal.
  unfold ml_grow in Hgrow; remove_bools_options.
  rewrite nth_cat.
  unfold ml_length in Hlen.
  replace (N.to_nat i < size (ml_data mem)) with true; by lias.
Qed.
  
#[export]
  Instance Memory_list: Memory.
Proof.
  apply (@Build_Memory memory_list ml_make ml_length ml_lookup ml_grow ml_update).
  - exact ml_lookup_ib.
  - exact ml_lookup_oob.
  - exact ml_make_length.
  - exact ml_make_lookup.
  - exact ml_update_lookup.
  - exact ml_update_lookup_ne.
  - by intros; eapply ml_update_length; eauto.
  - exact ml_update_ib.
  - exact ml_update_oob.
  - exact ml_grow_lookup.
  - exact ml_grow_length.
Qed.

End MemoryList.
