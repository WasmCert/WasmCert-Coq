From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import list fin_maps gmap.
Require Import list_extra properties.

Lemma map_fmap {T1 T2: Type} (f: T1 -> T2) (l: list T1):
  map f l = fmap f l.
Proof.
  trivial.
Qed.

Lemma nth_error_lookup {T: Type} (l: list T) i:
  nth_error l i = l !! i.
Proof.
  move: i.
  by induction l; move => i; destruct i => //=.
Qed.
  
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

Lemma list_fmap_app a b c d e :
  list_fmap a b c (d ++ e) = list_fmap a b c d ++ list_fmap a b c e.
Proof.
  fold (fmap c (d ++ e)).
  rewrite fmap_app.
  done.
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

Lemma repeat_lookup {T: Type} (x: T) (n i: nat):
  i < n <->
  (repeat x n) !! i = Some x.
Proof.
  split. 
  - move : n.
    induction i; move => n HLen; destruct n => //=; try lia.
    apply IHi.
    lia.
  - move => Hlookup.
    apply lookup_lt_Some in Hlookup.
    by rewrite repeat_length in Hlookup.
Qed.

Lemma repeat_lookup_None {T: Type} (x: T) (n i: nat):
  i >= n <->
  (repeat x n) !! i = None.
Proof.
  split. 
  - move : n.
    induction i; move => n HLen; destruct n => //=; try lia.
    apply IHi.
    lia.
  - move => Hlookup.
    apply lookup_ge_None in Hlookup.
    by rewrite repeat_length in Hlookup.
Qed.

Lemma fmap_fmap_lookup {T1 T2 T: Type} (f1: T1 -> T) (f2: T2 -> T) (l1: list T1) (l2: list T2):
  fmap f1 l1 = fmap f2 l2 ->
  forall i, fmap f1 (l1 !! i) = fmap f2 (l2 !! i).
Proof.
  move => Heq i.
  assert (length l1 = length l2) as Hlen.
  { erewrite <- fmap_length with (f := f1).
    rewrite Heq.
    by rewrite fmap_length.
  }
  destruct (l1 !! i) eqn:Hl1; destruct (l2 !! i) eqn:Hl2 => //=.
  - assert ((fmap f1 l1) !! i = (fmap f2 l2) !! i) as Heqi; first by rewrite Heq.
    repeat rewrite list_lookup_fmap in Heqi.
    rewrite Hl1 Hl2 in Heqi.
    by simpl in Heqi.
  - by apply lookup_lt_Some in Hl1; apply lookup_ge_None in Hl2; lias.
  - by apply lookup_lt_Some in Hl2; apply lookup_ge_None in Hl1; lias.
Qed.
