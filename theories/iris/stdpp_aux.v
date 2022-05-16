From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import fin_maps list.
Require Import list_extra.

Lemma fmap_split: forall {X Y:Type} (f: X -> Y) vs es1 es2,
  fmap f vs = es1 ++ es2 ->
  fmap f (take (length es1) vs) = es1 /\ fmap f (drop (length es1) vs) = es2.
Proof.
  move => X Y f vs es1.
  move : f vs.
  elim: es1; destruct vs => //=.
  move => es2 Hmap.
  inversion Hmap; subst; clear Hmap.
  apply H in H2. destruct H2; subst.
  split => //=.
  by f_equal.
Qed.
  
Lemma fmap_insert_set_nth: forall T (l: list T) i vd v,
  i < length l ->
  <[i := v]> l = set_nth vd l i v.
Proof.
  move => T l i vd v Hlen.
  move: i vd v Hlen.
  induction l; move => i vd v Hlen; destruct i => //=; simpl in Hlen; try by lia.
  apply lt_S_n in Hlen.
  f_equal.
  by apply IHl.
Qed.

Lemma those_projection_backward {T: Type} (l0: list (option T)) (l1: list T):
  (forall k, match l0 !! k with
        | Some x => x
        | None => None
        end
        = l1 !! k) ->
  length l0 = length l1 ->
  those l0 = Some l1.
Proof.
  move: l0 l1.
  induction l0; destruct l1 => //=; move => H Hlen.
  specialize (H 0) as H0.
  simpl in H0.
  subst.
  inversion Hlen; clear Hlen.
  rewrite - those_those0.
  simpl.
  unfold option_map.
  apply IHl0 in H1 => //; first by rewrite those_those0 H1.
  move => k.
  specialize (H (S k)).
  by simpl in H.
Qed.
