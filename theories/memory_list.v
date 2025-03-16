(** an implementation of Wasm memory based on a list *)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import BinNat Lia.
From Wasm Require Import numerics bytes memory.

Record memory_list : Type := {
  ml_init : byte;
  ml_data : list byte;
}.

Definition mem_make : Memory.mem_make_t memory_list :=
  fun v len => {| ml_init := v; ml_data := List.repeat v (N.to_nat len) |}.

Definition mem_length : Memory.mem_length_t memory_list :=
    fun ml => N.of_nat (List.length ml.(ml_data)).

Definition mem_grow : Memory.mem_grow_t memory_list :=
  fun len_delta ml =>
    {|
      ml_init := ml.(ml_init);
      ml_data := ml.(ml_data) ++ List.repeat ml.(ml_init) (N.to_nat len_delta)
    |}.

Definition mem_lookup : Memory.mem_lookup_t memory_list :=
  fun i ml => List.nth_error ml.(ml_data) (N.to_nat i).

Definition mem_update : Memory.mem_update_t memory_list :=
  fun i v ml =>
    if N.ltb i (N.of_nat (List.length ml.(ml_data)))
    then Some {| ml_init := ml.(ml_init);
                ml_data := take (N.to_nat i) ml.(ml_data) ++ [::v] ++ drop (N.to_nat i+1) ml.(ml_data) |}
    else None.

Lemma memory_list_ax_lookup_out_of_bounds :
  Memory.mem_ax_lookup_out_of_bounds memory_list mem_make mem_length mem_grow mem_lookup mem_update.
Proof.
  move => mem i.
  rewrite /mem_length /mem_lookup.
  move => H.
  apply (List.nth_error_None mem.(ml_data) (N.to_nat i)).
  apply N.ge_le in H.
  move: H.
  set x := (length (ml_data mem)).
  move => H.
  lia.
Qed.
  
Lemma nth_repeat :
forall A b i len, i < len ->
@List.nth_error A (List.repeat b len) i = Some b.
Proof.
  move => A b.
  elim => [|i].
  { case => [|len]; first by lia.
    by move => _. }
  { move => IH len.
    case: len => [|len'].
    { move => Hctr.
      exfalso.
      lia. }
    { move => Hlen /=.
      apply: IH.
      lia. } }
Qed.
  
Lemma lookup_split : forall A (l : list A) i b,
  i < List.length l ->
  List.nth_error (take i l ++ b :: drop (i+1) l) i = Some b.
Proof.
  move => A.
  elim => [|x l].
  { move => i b /= Hlen.
    exfalso.
    lia. }
  { move => IH.
    case => [|i]; first by reflexivity.
    move => b /= Hlen.
    have Hlen': i < length l by lia.
    by apply: IH. }
Qed.
  
Lemma bar : forall A n n' (l : list A) v,
  n <> n' -> n' < List.length l ->
  List.nth_error (take n' l ++ v :: drop (n' + 1) l) n =
  List.nth_error l n.
Proof.
  move => A.
  induction n; move => n' l v; destruct n', l => //=; try lia; move => Hneq Hlen; first by rewrite drop0.
  apply IHn => //; lia.
Qed.
  
Lemma length_is_size: forall {X:Type} (l: list X),
  length l = size l.
Proof.
  move => X l. by elim: l.
Qed.

Lemma split_preserves_length : forall A i b (l : list A),
  i < List.length l ->
  List.length (take i l ++ b :: drop (i + 1) l) = List.length l.
Proof.
  move => A i b l Hlen.
  repeat rewrite length_is_size.
  rewrite size_cat => /=.
  rewrite size_take size_drop.
  rewrite length_is_size in Hlen.
  move/ssrnat.ltP in Hlen.
  rewrite Hlen.
  rewrite PeanoNat.Nat.add_1_r.
  rewrite ssrnat.subnSK => //.
  rewrite ssrnat.subnKC => //.
  move/ssrnat.ltP in Hlen.
  apply/ssrnat.leP.
  (* lia come on? *)
  by apply PeanoNat.Nat.lt_le_incl.
Qed.

Lemma memory_list_ax_lookup_make : Memory.mem_ax_lookup_make memory_list mem_make mem_length mem_grow mem_lookup mem_update.
Proof.
  move => i len b mem.
  apply: nth_repeat.
  lia.
Qed.

Lemma memory_list_ax_lookup_update :
  Memory.mem_ax_lookup_update memory_list mem_make mem_length mem_grow mem_lookup mem_update.
Proof.
  move => mem mem' i b H H0.
  rewrite /mem_update in H0.
  apply N.ltb_lt in H.
  rewrite /mem_length in H.
  rewrite H in H0.
  case: mem' H0 => init_ data_ [Hinit Hdata].
  rewrite Hinit Hdata /= {init_ data_ Hinit Hdata}.
  set nn := N.to_nat i.
  have Hx: nn < length (ml_data mem).
  apply N.ltb_lt in H.
  lia.
  by apply: lookup_split.
Qed.

Lemma memory_list_ax_lookup_skip :
  Memory.mem_ax_lookup_skip memory_list mem_make mem_length mem_grow mem_lookup mem_update.
Proof.
  move => mem mem' i i' b Hii' H0.
  case: mem' H0 => init_ data_.
  rewrite /mem_update /mem_lookup.
  case_eq (N.ltb i' (N.of_nat (length (ml_data mem)))); last by discriminate.
  move => Hlen [Hinit Hdata] /=.
  rewrite Hdata => {Hdata}.
  apply: bar.
  lia.
  apply N.ltb_lt in Hlen.
  lia.
Qed.

Lemma memory_list_ax_length_constant_update :
  Memory.mem_ax_length_constant_update memory_list mem_make mem_length mem_grow mem_lookup mem_update.
Proof.
  move => i b [dv_init1 dv_list1] [dv_init2 dv_list2].
  rewrite /mem_update /mem_length /=.
  case_eq (N.ltb i (N.of_nat (length dv_list1))); last by discriminate.
  move => Hlen [Hinit Hlist].
  apply N.ltb_lt in Hlen.
  rewrite Hlist.
  f_equal.
  apply: (split_preserves_length _ (N.to_nat i) b dv_list1).
  lia.
Qed.

Require Import bytes common.
From HB Require Import structures.

Definition memory_list_eq_dec : forall (i1 i2 : memory_list), {i1 = i2} + {i1 <> i2}.
Proof. decidable_equality. Defined.

Definition memory_list_eqb i1 i2 : bool := memory_list_eq_dec i1 i2.

Definition eqmemory_listP : Equality.axiom memory_list_eqb :=
  eq_dec_Equality_axiom memory_list_eq_dec.

HB.instance Definition memory_list_eqMixin := hasDecEq.Build memory_list eqmemory_listP.

Definition list_memoryMixin :=
  Memory.Mixin
    memory_list_ax_lookup_out_of_bounds
    memory_list_ax_lookup_make
    memory_list_ax_lookup_update
    memory_list_ax_lookup_skip
    memory_list_ax_length_constant_update.
