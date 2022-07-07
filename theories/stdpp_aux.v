From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import list fin_maps gmap.
Require Import list_extra properties.

(* Additional lemmas to reduce friction among stdpp/ssreflect/coq*)

Ltac forward H Hname :=
  lazymatch type of H with
  | ?Hx -> _ => let Hp := fresh "Hp" in
              assert Hx as Hp; last specialize (H Hp) as Hname end.

(* automatically remembers a lookup result and make the hypothesis ready for destruct *)
Ltac remember_lookup :=
  match goal with
  | |- context C [?m !! ?x = _] =>
    let Hlookup := fresh "Hlookup" in
    remember (m !! x) as lookup_res eqn: Hlookup; symmetry in Hlookup
  end.

(* resolving predicates related to maps and lookups in stdpp. *)
Ltac resolve_finmap :=
  repeat match goal with
         | H: (list_to_map _) !! _ = Some _ |- _ =>
           let H2 := fresh "H2" in 
           apply elem_of_list_to_map in H as H2; clear H
         | H: (list_to_map _) !! _ = None |- _ =>
           let H2 := fresh "H2" in 
           apply not_elem_of_list_to_map in H as H2; clear H
         | H: _ ∈ fmap _ _ |- _ =>
           let Heq := fresh "Heq" in
           let Helem := fresh "Helem" in
           apply elem_of_list_fmap in H; destruct H as [? [Heq Helem]]; subst; simpl in *
         | H: ?x ∈ map_to_list _ |- _ =>
           destruct x; apply elem_of_map_to_list in H
         | H: _ ∈ imap _ _ |- _ =>
           let Heq := fresh "Heq" in
           let Helem := fresh "Helem" in
           apply elem_of_lookup_imap in H; destruct H as [? [? [Heq Helem]]]
         | H: (_, _) = (_, _) |- _ =>
           inversion H; subst; clear H
         | H: _ |- NoDup (fmap fst _) =>
           apply NoDup_fmap_fst; intros; subst; simpl in *; try by []
         | H: _ |- NoDup (map_to_list _) =>
           apply NoDup_map_to_list; try by []
         | H1: ?m !! ?x = _, H2: ?m !! ?x = _ |- _ =>
           rewrite H2 in H1; subst; simpl in *; clear H2
         | H: Some _ = Some _ |- _ =>
           inversion H; subst; simpl in *; try by []
         | H: _ |- (_, _) ∈ map_to_list _ =>
           apply elem_of_map_to_list
         | H: _ ∈ ?l |- _ =>
           let Helem := fresh "Helem" in
           try is_var l; apply elem_of_list_lookup in H; destruct H as [? Helem]
         | _ => simpl in *; try by eauto
         end.

(* Turns out that this is surprisingly not a standard lemma in stdpp and non-trivial to prove. *)
Lemma nodup_imap_inj1 {T X: Type} (l: list T) (f: nat -> T -> X):
  (forall n1 n2 t1 t2, f n1 t1 = f n2 t2 -> n1 = n2) ->
  NoDup (imap f l).
Proof.
  move: f.
  induction l => //=; first by intros; apply NoDup_nil.
  move => f HInj1. apply NoDup_cons. split.
  - move => HContra. apply elem_of_lookup_imap in HContra.
    destruct HContra as [i [y [Heq Helem]]].
    by apply HInj1 in Heq.
  - apply IHl. move => n1 n2 t1 t2 Heq.
    simpl in Heq. apply HInj1 in Heq. lia.
Qed.
    
Definition map_related {K: Type} {M: Type -> Type} {H0: forall A: Type, Lookup K A (M A)} {A: Type} (r: relation A) (m1 m2: M A) :=
  forall (i: K) (x: A), m1 !! i = Some x -> exists y, m2 !! i = Some y /\ r x y.

Lemma N_nat_bin n:
  n = N.of_nat (ssrnat.nat_of_bin n).
Proof.
  destruct n => //=.
  replace (ssrnat.nat_of_pos p) with (Pos.to_nat p); first by rewrite positive_nat_N.
  induction p => //=.
  - rewrite Pos2Nat.inj_xI.
    f_equal.
    rewrite IHp.
    rewrite ssrnat.NatTrec.doubleE.
    rewrite - ssrnat.mul2n.
    by lias.
  - rewrite Pos2Nat.inj_xO.
    rewrite IHp.
    rewrite ssrnat.NatTrec.doubleE.
    rewrite - ssrnat.mul2n.
    by lias.
Qed.

Lemma fold_left_preserve {A B: Type} (P: A -> Prop) (f: A -> B -> A) (l: list B) (acc: A) :
  P acc ->
  (forall (x:A) (act: B), P x -> P (f x act)) ->
  P (fold_left f l acc).
Proof.
  rewrite -fold_left_rev_right.
  revert acc.
  induction l;simpl;auto.
  intros acc Ha Hnext.
  rewrite foldr_snoc /=. apply IHl =>//.
  apply Hnext=>//.
Qed.    

Lemma nat_bin n:
  ssrnat.nat_of_bin n = N.to_nat n.
Proof.
  rewrite -> (N_nat_bin n).
  rewrite Nat2N.id.
  by rewrite <- N_nat_bin.
Qed.
  
Lemma take_all_alt {X: Type} (l: list X) n:
  n = length l ->
  take n l = l.
Proof.
  move => H. subst. by rewrite firstn_all.
Qed.

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

Lemma seq_map_fmap {X Y: Type} (f: X -> Y) (l: list X):
  seq.map f l = fmap f l.
Proof.
  by [].
Qed.

Lemma repeat_lookup_Some {X: Type} n (v: X) i res:
  repeat v n !! i = Some res ->
  res = v /\ i < n.
Proof.
  move => Hrlookup.
  assert (i < length (repeat v n)); first by eapply lookup_lt_Some.

  split; last by rewrite repeat_length in H.
  assert (repeat v n !! i = Some v); first by apply repeat_lookup; rewrite repeat_length in H.
  rewrite H0 in Hrlookup.
  by inversion Hrlookup.
Qed.

Lemma zip_lookup_Some {T1 T2: Type} (l1 : list T1) (l2: list T2) i x1 x2:
  length l1 = length l2 ->
  l1 !! i = Some x1 ->
  l2 !! i = Some x2 ->
  (zip l1 l2) !! i = Some (x1, x2).
Proof.
  move : l2 i x1 x2.
  induction l1; intros; destruct l2; destruct i => //=.
  - simpl in *.
    by inversion H0; inversion H1.
  - simpl in *.
    apply IHl1 => //.
    by inversion H.
Qed.

Lemma zip_lookup_Some_inv {X Y: Type} (l1: list X) (l2: list Y) k v1 v2:
  (zip l1 l2) !! k = Some (v1, v2) ->
  l1 !! k = Some v1 /\ l2 !! k = Some v2.
Proof.
  move: l2 k v1 v2.
  induction l1; intros; destruct l2; destruct k; simpl in * => //=.
  - by inversion H.
  - by apply IHl1.
Qed.
    
Lemma list_to_map_zip_lookup {X Y: Type} (E: EqDecision X) (H: Countable X) (l1 : list X) (l2: list Y) (k: X) (v: Y) (m: gmap X Y):
  NoDup l1 ->
  length l1 = length l2 ->
  (((list_to_map (zip l1 l2)): gmap X Y) !! k = Some v <->
   (exists k', l1 !! k' = Some k /\ l2 !! k' = Some v)).
Proof.
  move => Hnd Hlen.
  split; move => Hl.
  { rewrite <- elem_of_list_to_map in Hl; last first.
    { rewrite fst_zip => //; by lias. }
    resolve_finmap.
    exists x.
    by apply zip_lookup_Some_inv in Helem.
  }
  destruct Hl as [k' [Hl1 Hl2]].
  rewrite <- elem_of_list_to_map; last first.
  { rewrite fst_zip => //; by lias. }
  apply elem_of_list_lookup.
  exists k'.
  by apply zip_lookup_Some.
Qed.
  
Lemma list_to_map_zip_insert {X Y: Type} (E: EqDecision X) (H: Countable X) (l1 : list X) (l2: list Y) (k: X) (k': nat) (v: Y) (m: gmap X Y):
  NoDup l1 ->
  m = list_to_map (zip l1 l2) ->
  length l1 = length l2 ->
  l1 !! k' = Some k ->
  <[ k := v ]> m = list_to_map (zip l1 (<[ k' := v ]> l2)).
Proof.
  move => Hnd -> Hlen Hk.
  apply map_eq.
  move => i.
  destruct (decide (i=k)); subst => //=.
  - rewrite lookup_insert.
    symmetry.
    rewrite list_to_map_zip_lookup => //.
    { exists k'.
      split => //.
      rewrite list_lookup_insert => //.
      by apply lookup_lt_Some in Hk; lias.
    }
    { by rewrite insert_length. }
  - rewrite lookup_insert_ne => //.
    destruct (list_to_map (zip l1 _) !! i) eqn:Hli => /=.
    { symmetry.
      apply list_to_map_zip_lookup => //.
      { by rewrite insert_length. }
      { apply elem_of_list_to_map in Hli; last first.
        { rewrite fst_zip => //; by lias. }
        apply elem_of_list_lookup in Hli.
        destruct Hli as [j Hli].
        apply zip_lookup_Some_inv in Hli.
        exists j.
        rewrite list_lookup_insert_ne => //.
        destruct Hli as [Hli _].
        move => HContra; subst.
        by rewrite Hk in Hli; inversion Hli.
      }
    }
    {
      resolve_finmap.
      rewrite fst_zip in H2; last by lias.
      rewrite not_elem_of_list_to_map_1 => //.
      rewrite fst_zip => //.
      by rewrite insert_length; lias.
    }
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

Lemma skipn_is_drop_n {T: Type} (l: list T) n:
  drop n l = seq.drop n l.
Proof.
  move: n.
  by induction l; destruct n => //=.
Qed.
  
Lemma nth_error_none_fmap {A B} (l : seq.seq A) n (f : A -> B) :
  nth_error l n = None -> nth_error (f <$> l) n = None.
Proof.
  repeat rewrite nth_error_lookup.
  rewrite list_lookup_fmap.
  by move => Hl; rewrite Hl.
Qed.

Lemma fmap_update_list_at {A B} l i x (f : A -> B) :
  f <$> update_list_at l i x = update_list_at (f <$> l) i (f x).
Proof.
  unfold update_list_at.
  rewrite fmap_app => /=.
  rewrite - fmap_drop => /=.
  f_equal.
  repeat rewrite - firstn_is_take_n.
  by rewrite fmap_take.
Qed. 

Lemma rcons_eq (T: Type) (es1: list T) e1 es2 e2:
  es1 ++ [e1] = es2 ++ [e2] ->
  es1 = es2 /\ e1 = e2.
Proof.
  move: es2.
  induction es1 => //; move => es2 H.
  - destruct es2 => //=; first simpl in H; inversion H => //.
    by destruct es2.
  - destruct es2 => //=; first by destruct es1 => //.
    inversion H; subst; clear H.
    apply IHes1 in H2 as [-> ->].
    split => //.
Qed.
  
Lemma lookup_snoc {A : Type} (l : list A) (a : A) :
  (l ++ [a]) !! (length l) = Some a.
Proof.
  induction l;auto.
Qed.

Lemma elem_of_app_l :
  ∀ (A : Type) (l1 l2 : seq.seq A) (x : A) (eqA : EqDecision A), x ∈ l1 ++ l2 ↔ x ∈ l1 ∨ (x ∈ l2 ∧ x ∉ l1).
Proof.
  intros A l1 l2 x eqA.
  induction l1.
  { rewrite app_nil_l.
    split;intros.
    right.
    split;auto.
    apply not_elem_of_nil.
    destruct H as [? | [? ?]];try done.
    inversion H.
  }
  { simpl. destruct (decide (x = a)).
    { simplify_eq. split.
      intros Ha. left. constructor.
      intros _. constructor. }
    { split.
      { intros [Hcontr|[Ha | [Ha Hnin]]%IHl1]%elem_of_cons;[done|..].
        left. by constructor.
        right. split;auto. apply not_elem_of_cons;auto. }
      { intros [[Hcontr|Ha]%elem_of_cons|[Hin Hnin]];[done|..].
        constructor. apply elem_of_app. by left.
        constructor. apply elem_of_app. by right. }
    }
  }
Qed.

Lemma app_eq_singleton: ∀ T (l1 l2 : list T) (a : T),
    l1 ++ l2 = [a] ->
    (l1 = [a] ∧ l2 = []) ∨ (l1 = [] ∧ l2 = [a]).
Proof.
  intros.
  apply app_eq_unit in H as [?|?]; by [ right | left ].
Qed.
