(** Common useful definitions **)
(* (C) M. Bodin - see LICENSE.txt *)

Require Import Lia.
From mathcomp Require Import ssreflect ssrnat ssrbool seq eqtype.
From compcert Require Integers.
From Wasm Require Export pickability.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Structures **)

Lemma Z_eqP : Equality.axiom Coqlib.zeq.
Proof.
  move=> x y. case: Coqlib.zeq; by [ left | right ].
Qed.

Definition Z_eqMixin := EqMixin Z_eqP.

Canonical Structure Z_eqType := EqType BinNums.Z Z_eqMixin.

Lemma Pos_eqP : Equality.axiom BinPosDef.Pos.eqb.
Proof.
  move=> x y. apply: Bool.iff_reflect. by rewrite BinPos.Pos.eqb_eq.
Qed.
                                                                      
Definition Pos_eqMixin := EqMixin Pos_eqP.

Canonical Structure Pos_eqType := EqType BinNums.positive Pos_eqMixin.

(** * Equalities **)

(** Try to rewrite the goal such that [lia] has more chance to deal with it. **)
Ltac lias_simpl :=
  intros;
  repeat lazymatch goal with
  | |- ~ _ => intro
  | |- is_true (~~ _) => apply/negP
  | |- context C [subn] => rewrite /subn /subn_rec
  | |- context C [addn] => rewrite /addn /addn_rec
  | |- is_true (leq _ _) => apply/leP
  | |- is_true (@eq_op nat_eqType _ _) => rewrite -eqnE; apply/eqnP
  | |- is_true (@eq_op Z_eqType _ _) => apply/Z_eqP
  | |- is_true (@eq_op Pos_eqType _ _) => apply/Pos_eqP
  | |- context C [BinNums.Zpos (BinPos.Pos.of_succ_nat ?n)] =>
    rewrite -> (Znat.Zpos_P_of_succ_nat n);
    rewrite <- (Znat.Nat2Z.inj_succ n)
  | |- _ /\ _ => split
  | |- is_true (_ && _) => apply/andP; split
  | |- _ <-> _ => split; intros
  | H: context C [subn] |- _ => unfold subn, subn_rec in H
  | H: context C [addn] |- _ => unfold addn, addn_rec in H
  | H: is_true (~~ _) |- _ => move/negP: H => H
  | H: _ /\ _ |- _ => move: H; intros [? ?]
  | H: _ <-> _ |- _ => move: H; intros [? ?]
  | H: is_true (_ && _) |- _ => move/andP: H; intros [? ?]
  | H: context C [is_true (leq _ _)] |- _ => move: H => /leP H
  | H: context C [is_true (@eq_op nat_eqType _ _)] |- _ => move: H; rewrite -eqnE => /eqnP H
  | H: context C [is_true (@eq_op Z_eqType _ _)] |- _ => move: H => /Z_eqP H
  | H: context C [is_true (@eq_op Pos_eqType _ _)] |- _ => move: H => /Pos_eqP H
  | H: context C [BinNums.Zpos (BinPos.Pos.of_succ_nat ?n)] |- _ =>
    rewrite -> (Znat.Zpos_P_of_succ_nat n) in H;
    rewrite <- (Znat.Nat2Z.inj_succ n) in H
  (* The following cases have a higher chance of failing, and should be kept after this comment. *)
  | |- ?x = false => apply/negP; intro
  | H: context C [?x = false] |- _ => move: H => /negP H
  | |- ?x = true => fold (is_true x)
  | H: context C [?x = true] |- _ => fold (is_true x) in H
  end;
  repeat rewrite <- PeanoNat.Nat.add_1_l in *;
  try unfold Logic.not in *;
  try by [].

(** An extension of [lia] that just tries to rewrite things in the way [lia] that expects. **)
Ltac lias :=
  lias_simpl;
  let unfold_head _ :=
    let rec aux f :=
      lazymatch f with
      | ?g _ => aux g
      | _ => unfold f
      end in
    lazymatch goal with
    | |- ?f => aux f
    end in
  let rec aux _ :=
    solve [ lia
          | nia
          | unfold_head tt; aux tt
          | apply: Bool.eq_true_iff_eq; lias_simpl; aux tt ] in
  aux tt || (simpl; lias_simpl; aux tt).

(** Rewrite an arithmetic equality. **)
Ltac rewrite_by E :=
  let R := fresh "R" in
  have R: E;
    [ by [ auto | lias ]
    | rewrite {} R ].

Ltac remove_bools_options :=
  repeat lazymatch goal with
  | H: is_true (_ && _ ) |- _ =>
    move/andP in H; destruct H
  | H: (_ && _) = true |- _ =>
    move/andP in H; destruct H                                    
  | H: is_true (_ == _) |- _ =>
    move/eqP in H
  | H: is_true (_ || _) |- _=>
    move/orP in H; destruct H
  | H: Some _ = Some _ |- _ =>
    inversion H; subst; clear H
  | H: option_map _ _ = _ |- _ =>
    unfold option_map in H
  | H: match ?exp with
       | Some _ => _
       | None => _
       end = _
    |- _ =>
    let Hoption := fresh "Hoption" in
    destruct exp eqn:Hoption; try by []
  | H: is_true match ?exp with
       | Some _ => _
       | None => _
       end
    |- _ =>
    let Hoption := fresh "Hoption" in
    destruct exp eqn:Hoption; try by []
  end.


(** A useful lemma to link the results of [Scheme Equality] to [Equality.axiom]. **)
Lemma eq_dec_Equality_axiom : forall t (eq_dec : forall x y : t, {x = y} + {x <> y}),
  let eqb v1 v2 := is_left (eq_dec v1 v2) in
  Equality.axiom eqb.
Proof.
  move=> t eq_dec eqb x y. rewrite /eqb. case: (eq_dec x y).
  - move=> E. by apply/ReflectT.
  - move=> E. by apply/ReflectF.
Qed.

(** A useful lemma for the converse: getting a [_ep_dec] from an [Equality.axiom]. **)
Definition Equality_axiom_eq_dec t (eqb : t -> t -> bool) (A : Equality.axiom eqb) :
    forall x y : t, {x = y} + {x <> y}.
Proof.
  move=> x y. move: (A x y). case E: (eqb x y); inversion 1; by [ left | right ].
Defined.

(** As [eqType] can be inferred thanks to canonical instance, this lemma provides
  another way of building a [_eq_dec]. **)
Lemma eqType_eq_dec : forall (A : eqType) (a1 a2 : A),
  {a1 = a2} + {a1 <> a2}.
Proof.
  move=> A a1 a2. case_eq (a1 == a2) => /eqP.
  - by left.
  - by right.
Defined.

Ltac decidable_equality_step :=
  first [
      by apply: eq_comparable
    | apply: List.list_eq_dec
    | apply: Coqlib.option_eq
    | apply: PeanoNat.Nat.eq_dec
    | by eauto
    | intros; apply: decP; by (exact _ || eauto)
    | decide equality ].

(** Solve a goal of the form [forall a1 a2, {a1 = a2} + {a1 <> a2}]. **)
Ltac decidable_equality :=
  repeat decidable_equality_step.

(** A lemma to move from [BoolSpec] to [reflect] predicates. **)
Lemma BoolSpec_reflect : forall P b,
  BoolSpec P (~P) b ->
  reflect P b.
Proof.
  move=> P b. case: b => S.
  - apply: ReflectT. by inversion S.
  - apply: ReflectF. by inversion S.
Qed.

(** And conversely. **)
Lemma reflect_BoolSpec : forall P b,
  reflect P b ->
  BoolSpec P (~P) b.
Proof.
  move=> P b. by case; [ apply: BoolSpecT | apply: BoolSpecF ].
Qed.

Import ZArith.BinInt.

Lemma gtb_spec0 : forall x y, reflect (x > y)%Z (x >? y)%Z.
Proof.
  move=> x y. apply: Bool.iff_reflect. rewrite Z.gtb_lt. by lias.
Qed.

Lemma geb_spec0 : forall x y, reflect (x >= y)%Z (x >=? y)%Z.
Proof.
  move=> x y. apply: Bool.iff_reflect. rewrite Z.geb_le. by lias.
Qed.


Definition curry A B C (f : A -> B -> C) (ab : A * B) :=
  let: (a, b) := ab in
  f a b.

Definition uncurry A B C (f : A * B -> C) a b := f (a, b).

Lemma curry_uncurry : forall A B C (f : A * B -> C) ab,
  curry (uncurry f) ab = f ab.
Proof. by move=> A B C f [a b]. Qed.

Lemma uncurry_curry : forall A B C (f : A -> B -> C) a b,
  uncurry (curry f) a b = f a b.
Proof. by []. Qed.


(** * Lemmas about lists. **)

Lemma List_In_in_mem : forall (A : eqType) e (l : seq A),
  e \in l <-> List.In e l.
Proof.
  induction l.
  - by [].
  - rewrite in_cons /= -IHl. split.
    + move/orP => [E|I]; [ left | right => // ]. symmetry. by apply/eqP.
    + move=> [E|I]; apply/orP; [ left | right => // ]. by apply/eqP.
Qed.

Lemma filter_notin : forall (A : eqType) a (l : seq A) p,
  a \notin l ->
  filter p l = filter (fun b => (b != a) && p b) l.
Proof.
  move=> A a l p N. apply: eq_in_filter => x I.
  rewrite is_true_bool. split.
  - move=> P. apply/andP. split => //. apply/eqP => ?. subst. by move/negP: N.
  - by move/andP => [? ?].
Qed.

Lemma filter_out_zlt : forall (a : nat) l,
  (Z.of_nat a) \notin l ->
  [seq x <- l | Coqlib.zlt x (Z.of_nat a)]
  = [seq x <- l | Coqlib.zlt x (Z.pos (Pos.of_succ_nat a))].
Proof.
  move=> a l N. rewrite (filter_notin _ N). apply: eq_in_filter.
  move=> x I. rewrite Znat.Zpos_P_of_succ_nat -Znat.Nat2Z.inj_succ.
  case_eq (x == Z.of_nat a) => /eqP.
  - move=> E. subst. exfalso. by move/negP: N.
  - move=> D. by destruct Coqlib.zlt as [L|L], Coqlib.zlt as [L'|L'] => //; exfalso; lias.
Qed.

Lemma filter_for_all : forall A p (l : seq A),
  all p l ->
  filter p l = l.
Proof. move=> A p l F. by apply/all_filterP. Qed.

Lemma list_all_forall : forall A p (l : seq A),
  all p l <-> forall a, List.In a l -> p a.
Proof.
  move=> A p. elim => /=.
  - by split.
  - move=> a l IH. split.
    + move/andP => [P F] e [?|I].
      * by subst.
      * move: F. rewrite {} IH => AP. by apply: AP.
    + move=> F. apply/andP. rewrite IH. split.
      * apply: F. by left.
      * move=> e I. apply: F. by right.
Qed.

Lemma filter_none : forall A p (l : seq A),
  all (fun b => ~~ p b) l ->
  filter p l = [::].
Proof.
  move=> A p. elim.
  - by [].
  - move=> a l IH /= /andP [N F]. destruct p => //. by rewrite IH.
Qed.

Lemma filter_and : forall A p1 p2 (l : seq A),
  filter (fun a => p1 a && p2 a) l
  = filter p1 (filter p2 l).
Proof.
  move=> A p1 p2. elim.
  - by [].
  - move=> a l E /=. destruct p2 => /=; destruct p1 => //=. by rewrite E.
Qed.

Lemma firstn_is_take_n: forall {X:Type} (l:seq X) n,
    List.firstn n l = take n l.
Proof.
  move => + + n. induction n.
  - symmetry. by apply take0.
  - move => X l. destruct l => //=. by f_equal.
Qed.

(** If [List.nth_error] succeeds, then the list can be split into three parts. **)
Lemma split3: forall {X:Type} (l:seq X) n v,
    n < size l ->
    List.nth_error l n = Some v ->
    l = take n l ++ [::v] ++ drop (n+1) l.
Proof.
  move => X.
  elim => //= a l IH n v.
  elim: n => [_ [H]|n IH2 Ha Hb].
  - by rewrite /= H drop0.
  - by rewrite /= -(IH _ _ Ha Hb).
Qed.

Lemma rev_move: forall {X:Type} (l1 l2:seq X),
  rev l1 = l2 -> l1 = rev l2.
Proof.
  move => X l1 l2 HRev. rewrite -HRev. symmetry. by apply: revK.
Qed.

Lemma rev0 : forall A, rev [::] = ([::] : seq A).
Proof. reflexivity. Qed.

Lemma seq_nth_eq : forall A (d : A) l1 l2,
  seq.size l1 = seq.size l2 ->
  (forall n, n < seq.size l1 -> seq.nth d l1 n = seq.nth d l2 n) ->
  l1 = l2.
Proof.
  move=> A d. elim.
  - by case.
  - move=> e1 l1 IH. case => //= e2 l2 E F. f_equal.
    + fold (nth d (e1 :: l1) 0). by rewrite F.
    + apply: IH.
      * by lias.
      * move=> n I. have I': n.+1 < (size l1).+1; first by lias.
        by apply F in I'.
Qed.

Lemma nil_rcons : forall A l (a : A),
  [::] <> rcons l a.
Proof. move=> A. by case. Qed.

Fixpoint last_error {A} (l : list A) : option A :=
  match l with
  | [::] => None
  | [::x] => Some x
  | _ :: l' => last_error l'
  end.

Lemma last_error_rcons : forall A l (a : A),
  last_error (rcons l a) = Some a.
Proof.
  move=> A. elim; first by [].
  move=> e l IH a /=. rewrite IH.
  move: (@nil_rcons _ l a). by destruct rcons.
Qed.

Lemma rcons_last_error : forall A l (a : A),
  last_error l = Some a ->
  exists l', l = rcons l' a.
Proof.
  move=> A l. induction l using last_ind; first by [].
  move=> a. rewrite last_error_rcons. case=> ?. subst. by eexists.
Qed.

Lemma last_error_nil : forall A (l : list A),
  last_error l = None <-> l = [::].
Proof.
  move=> A. case => //= a l.
  induction l using last_ind; first by [].
  split=> //. rewrite last_error_rcons. by destruct rcons.
Qed.

Lemma last_error_last : forall A l (a : A),
  last_error l = Some a ->
  exists e l', l = e :: l' /\ a = last e l'.
Proof.
  move=> A. case=> // e l' a E.
  exists e. exists l'. split => //.
  move: (rcons_last_error E) => [l'' E'].
  by rewrite -(last_cons e) E' last_rcons.
Qed.

Lemma all2_swap : forall A B (f : A -> B -> bool) l1 l2,
  all2 f l1 l2 = all2 (fun x y => f y x) l2 l1.
Proof.
  move=> A B f. elim.
  - by case.
  - move=> a1 l1 IH. case=> //= a2 l2. by rewrite IH.
Qed.

Lemma all2_eq : forall A B (f1 f2 : A -> B -> bool) l1 l2,
  (forall a b, f1 a b = f2 a b) ->
  all2 f1 l1 l2 = all2 f2 l1 l2.
Proof.
  move=> A B f1 f2. elim.
  - by case.
  - move=> a1 l1 IH. case=> //= a2 l2 E. by rewrite E IH.
Qed.

Lemma map_all2 : forall A (B : eqType) (f : A -> B) l,
  all2 (fun a1 a2 => f a1 == a2) l (map f l).
Proof.
  move=> A B f. elim => //=.
  move=> a1 l1 IH. by apply/andP.
Qed.

Lemma all2_map_left : forall A (B : eqType) (f : A -> B) l1 l2,
  all2 (fun a1 a2 => f a1 == a2) l1 l2 ->
  map f l1 = l2.
Proof.
  move=> A B f. elim.
  - by case.
  - move=> a1 l1 IH. case=> //= a2 l2 /andP [E F]. f_equal.
    + by move/eqP: E.
    + by apply: IH.
Qed.

Lemma all2_map_right : forall A (B : eqType) (f : A -> B) l1 l2,
  all2 (fun a1 a2 => a1 == f a2) l1 l2 ->
  l1 = map f l2.
Proof.
  move=> > F. symmetry. apply: all2_map_left. rewrite all2_swap.
  by erewrite all2_eq; first apply: F.
Qed.

Lemma all2_mapP : forall A (B : eqType) (f : A -> B) l1 l2,
  reflect (map f l1 = l2) (all2 (fun a1 a2 => f a1 == a2) l1 l2).
Proof.
  move=> >. apply: Bool.iff_reflect. split.
  - move=> ?. subst. by rewrite map_all2.
  - by apply: all2_map_left.
Qed.

Lemma cat0_inv : forall T (s1 s2 : seq T),
  s1 ++ s2 = [::] ->
  s1 = [::] /\ s2 = [::].
Proof.
  move=> T s1 s2 E.
  move: (size_cat s1 s2). rewrite {} E => /=. case s1.
  - case s2 => E.
    + done.
    + move => ? A. inversion A.
  - move => ? ? A. inversion A.
Qed.


(** * An equivalent to [List.Forall], but in [Type] instead of [Prop]. **)

Module TProp.

Inductive Forall (A : Type) (P : A -> Type) : seq A -> Type :=
  | Forall_nil : Forall P nil
  | Forall_cons : forall e l, P e -> Forall P l -> Forall P (e :: l)
  .

Fixpoint max A l (F : Forall (fun (_ : A) => nat) l) : nat :=
  match F with
  | Forall_nil => 0
  | Forall_cons _ _ n F => Nat.max n (max F)
  end.

Fixpoint map A P Q (f : forall a, P a -> Q a) (l : seq A) (F : Forall P l) : Forall Q l :=
  match F with
  | Forall_nil => Forall_nil _
  | Forall_cons _ _ p F => Forall_cons (f _ p) (map f F)
  end.

Fixpoint to_list A B (l : list A) (F : Forall (fun _ => B) l) :=
  match F with
  | Forall_nil => [::]
  | Forall_cons _ _ p F => p :: to_list F
  end.

Fixpoint from_list A (l : list A) : Forall (fun _ => A) l :=
  match l with
  | [::] => Forall_nil _
  | e :: l => Forall_cons e (from_list l)
  end.

Lemma Forall_forall : forall A (P : A -> Prop) l,
  Forall P l ->
  forall e, List.In e l -> P e.
Proof.
  move=> A P l. elim {l}.
  - by [].
  - move=> e l Pe F IH e' /=. case.
    + move=> E. by subst.
    + by apply: IH.
Qed.

Lemma forall_Forall : forall A (P : A -> Prop) l,
  (forall e, List.In e l -> P e) ->
  Forall P l.
Proof.
  move=> A P. elim.
  - move=> _. by apply: Forall_nil.
  - move=> e l IH H. apply: Forall_cons.
    + apply: H. by left.
    + apply: IH => e' I. apply: H. by right.
Defined.

Lemma Forall_List_Forall : forall A (P : A -> Prop) l,
  Forall P l ->
  List.Forall P l.
Proof.
  move=> > F. apply List.Forall_forall. by apply: Forall_forall F.
Qed.

Definition List_Forall_Forall : forall A (P : A -> Prop) l,
  List.Forall P l ->
  Forall P l.
Proof.
  move=> > F. apply: forall_Forall. by apply List.Forall_forall.
Defined.

Definition Forall_cat A (P : A -> Prop) (l1 l2 : list A) (F1 : Forall P l1) (F2 : Forall P l2)
  : Forall P (l1 ++ l2).
Proof.
  induction F1 => //. by apply: Forall_cons.
Defined.

Definition Forall_catrev A (P : A -> Prop) : forall (l1 l2 : list A),
  Forall P l1 -> Forall P l2 -> Forall P (rev l1 ++ l2).
Proof.
  move=> l1 + F1. induction F1 => // l2 F2.
  rewrite rev_cons -cats1 -catA. apply: IHF1. by apply: Forall_cons.
Defined.

Definition Forall_rev A (P : A -> Prop) (l : list A) (F : Forall P l) : Forall P (rev l).
Proof.
  rewrite -(cats0 (rev l)). apply: Forall_catrev => //. by apply: Forall_nil.
Defined.

(* FIXME: There are too many opaque things there: I’m afraid that this is not provable.
Definition Forall_catrevE : forall A (P : A -> Prop) l1 l2 (F1 : Forall P l1) (F2 : Forall P l2),
  Forall_catrev F1 F2 = Forall_cat (Forall_rev F1) F2.
Proof.
  move=> A P l1 + F1. induction F1 => l2 F2.
  - rewrite/Forall_rev /eq_rect => /=.
Qed.
*)

Definition Forall_forall_eq_dec : forall A l1 l2,
  Forall (fun x : A => forall y, {x = y} + {x <> y}) l1 ->
  {l1 = l2} + {l1 <> l2}.
Proof.
  move=> A l1 + F. elim F.
  - by elim; [ left | right ].
  - clear. move=> e1 l1 C F IH. case; first by right.
    move=> e2 l2. destruct (C e2); last by right; inversion 1.
    destruct (IH l2); last by right; inversion 1.
    left. by subst.
Defined.

End TProp.


(** * Stronger Induction Principles **)

(** Try to fold an expression everywhere.
  More robust than [fold e in *]. **)
Ltac efold e :=
  repeat match goal with H : _ |- _ => progress fold e in H end;
  fold e.

(** Given a goal of the form [{C a1 … an = C a1' … an'} + {C a1 … an <> C a1' … an'}],
  replaces it with the goals [{a1 = a1'} + {a1 <> a1'}], …, [{an = an'} + {an <> an'}]. **)
Ltac decide_equality_injection :=
  lazymatch goal with
  | |- {?c1 = ?c2} + {_} =>
    let rec aux c1 c2 next :=
      lazymatch constr:((c1, c2)) with
      | (?c, ?c) => next tt
      | (?c1 ?a1, ?c2 ?a2) =>
        let H := fresh "decide" in
        assert (H : {a1 = a2} + {a1 <> a2});
          [| aux c1 c2 ltac:(fun _ =>
               destruct H as [H|H];
                 [ rewrite H; next tt
                 | right; by inversion 1 ]) ]
      end in
    aux c1 c2 ltac:(fun _ => by left)
  end.

(** Similar than [decidable_equality], but based on another induction principle.
  It will make use of hypotheses based on [TProp.Forall]. **)
Ltac decidable_equality_using rect :=
  let x := fresh "x" in
  let y := fresh "y" in
  move=> x; induction x using rect => y; destruct y;
    first [ by right; discriminate
          | decide_equality_injection;
            first [ by apply: TProp.Forall_forall_eq_dec
                  | decidable_equality ] ].

(** Given an induction principle, return the number of cases of the type. **)
Ltac count_cases rect :=
  let rec count_args rectf :=
    lazymatch rectf with
    | forall a, False => constr:(0)
    | _ -> ?rectf' =>
      let r := count_args rectf' in
      constr:(r.+1)
    end in
  lazymatch type of rect with
  | forall P : ?t -> Type, @?rectf P =>
    let r := constr:(rectf (fun _ : t => False)) in
    let r := eval simpl in r in
    count_args r
  end.

(** Returns a boolean depending on whether [t] and [t'] are reducible to one each other. **)
Ltac is_reducible t t' :=
  match t with
  | _ => let r := constr:((fun (_ : t = t') => true) (ltac:(reflexivity))) in
         eval simpl in r
  | _ => constr:(false)
  end.

(** Given an induction principle, return the type of a stronger induction principle.
  The projection is there to focus the induction principle on a different type (e.g. [list t]
  instead of [t]): possible values are [@id], [list], and [option]. **)
Ltac rect'_type_projection proj rect :=
  let fold_type t ta :=
    (* Try to fold [t] in [ta]. *)
    match tt with
    | _ => eval fold t in ta
    | _ => constr:(ta)
    end in
  let added_hyp t ta :=
    lazymatch ta with
    | list t => constr:(@TProp.Forall t)
    | option t => constr:(fun P (o : ta) => forall a : t, o = Some a -> P a)
    | _ => constr:(fun (_ : t -> Type) (_ : ta) => True)
    end in
  let add_hyp t ta P a r :=
    let h := added_hyp t ta in
    let h := constr:(h P a) in
    let h := eval simpl in h in
    lazymatch h with
    | True => r
    | _ => constr:(h -> r)
    end in
  let set_hyp t ta P a r :=
    let r := add_hyp t ta P a r in
    exact r in
  let update_hyp t hyp :=
    lazymatch hyp with
    | fun P => P _ => constr:(hyp)
    | fun P => forall a1 : ?t1, P (?C a1) =>
      let t1 :=  fold_type t t1 in
      constr:(fun P : t -> Type => forall a1 : t1,
        ltac:(set_hyp t t1 P a1 (P (C a1))))
    | fun P => forall (a1 : ?t1) (a2 : ?t2), P (?C a1 a2) =>
      let t1 :=  fold_type t t1 in
      let t2 :=  fold_type t t2 in
      constr:(fun P : t -> Type => forall (a1 : t1) (a2 : t2),
        ltac:(set_hyp t t1 P a1
          ltac:(add_hyp t t2 P a2 (P (C a1 a2)))))
    | fun P => forall (a1 : ?t1) (a2 : ?t2) (a3 : ?t3), P (?C a1 a2 a3) =>
      let t1 :=  fold_type t t1 in
      let t2 :=  fold_type t t2 in
      let t3 :=  fold_type t t3 in
      constr:(fun P : t -> Type => forall (a1 : t1) (a2 : t2) (a3 : t3),
        ltac:(set_hyp t t1 P a1
          ltac:(add_hyp t t2 P a2
            ltac:(add_hyp t t3 P a3 (P (C a1 a2 a3))))))
    | fun P => forall (a1 : ?t1) (a2 : ?t2) (a3 : ?t3) (a4 : ?t4), P (?C a1 a2 a3 a4) =>
      let t1 :=  fold_type t t1 in
      let t2 :=  fold_type t t2 in
      let t3 :=  fold_type t t3 in
      let t4 :=  fold_type t t4 in
      constr:(fun P : t -> Type => forall (a1 : t1) (a2 : t2) (a3 : t3) (a4 : t4),
        ltac:(set_hyp t t1 P a1
          ltac:(add_hyp t t2 P a2
            ltac:(add_hyp t t3 P a3
              ltac:(add_hyp t t4 P a4 (P (C a1 a2 a3 a4)))))))
    | fun P => forall (a1 : ?t1) (a2 : ?t2) (a3 : ?t3) (a4 : ?t4) (a5 : ?t5), P (?C a1 a2 a3 a4 a5) =>
      let t1 :=  fold_type t t1 in
      let t2 :=  fold_type t t2 in
      let t3 :=  fold_type t t3 in
      let t4 :=  fold_type t t4 in
      let t5 :=  fold_type t t5 in
      constr:(fun P : t -> Type => forall (a1 : t1) (a2 : t2) (a3 : t3) (a4 : t4) (a5 : t5),
        ltac:(set_hyp t t1 P a1
          ltac:(add_hyp t t2 P a2
            ltac:(add_hyp t t3 P a3
              ltac:(add_hyp t t4 P a4
                ltac:(add_hyp t t4 P a4 (P (C a1 a2 a3 a4 a5))))))))
    | fun P => forall (a1 : ?t1) (a2 : ?t2) (a3 : ?t3) (a4 : ?t4) (a5 : ?t5) (a6 : ?t6), P (?C a1 a2 a3 a4 a5 a6) =>
      let t1 :=  fold_type t t1 in
      let t2 :=  fold_type t t2 in
      let t3 :=  fold_type t t3 in
      let t4 :=  fold_type t t4 in
      let t5 :=  fold_type t t5 in
      let t6 :=  fold_type t t6 in
      constr:(fun P : t -> Type => forall (a1 : t1) (a2 : t2) (a3 : t3) (a4 : t4) (a5 : t5) (a6 : t6),
        ltac:(set_hyp t t1 P a1
          ltac:(add_hyp t t2 P a2
            ltac:(add_hyp t t3 P a3
              ltac:(add_hyp t t4 P a4
                ltac:(add_hyp t t5 P a5
                  ltac:(add_hyp t t6 P a6 (P (C a1 a2 a3 a4 a5 a6)))))))))
    end in
  let conclusion t rectf :=
    lazymatch rectf with
    | fun P => forall a : t, P a =>
      lazymatch proj with
      | @id => constr:(rectf)
      | list => constr:(fun P => forall l : list t, TProp.Forall P l)
      | option => constr:(fun P => forall (o : option t) (a : t), o = Some a -> P a)
      end
    end in
  let rec map_hyps t rectf :=
    lazymatch rectf with
    | fun P => @?hyp P -> @?rectf' P =>
      let r := update_hyp t hyp in
      let r' := map_hyps t rectf' in
      constr:(fun P => r P -> r' P)
    | fun P => forall a : ?t', P a =>
      (* The type [t'] might not be syntactically [t], but should be convertible. *)
      let rectf' := constr:(fun P => forall a : t, P a) in
      conclusion t rectf'
    end in
  lazymatch type of rect with
  | forall P : ?t -> Type, @?rectf P =>
    let r := map_hyps t rectf in
    let r := constr:(forall P, r P) in
    eval simpl in r
  end.


(** The main instantiation. **)
Ltac rect'_type rect := rect'_type_projection @id rect.

(** Instantiation for lists. **)
Ltac rect'_type_list rect := rect'_type_projection list rect.

(** Instantiation for option types. **)
Ltac rect'_type_option rect := rect'_type_projection option rect.

(** Prove a goal whose type matches the type generated by [rect'_type] with the same parameter. **)
Ltac rect'_build_projection proj rect :=
  let t :=
    lazymatch type of rect with
    | forall P : ?t -> Type, _ => t
    end in
  let g := rect'_type_projection proj rect in
  refine (_ : g);
  let P := fresh "P" in
  intro P;
  repeat (
    try fold t;
    lazymatch goal with
    | |- forall a : t, P a => idtac
    | |- forall l : list t, TProp.Forall P l =>
      let l := fresh "l" in
      let a := fresh "a" in
      intro l; induction l as [| a l ];
      [ solve [ apply TProp.Forall_nil ]
      | apply TProp.Forall_cons; [ generalize a | assumption ] ]
    | |- forall (o : option t) (a : t), o = Some a -> P a =>
      let o := fresh "o" in
      let a := fresh "a" in
      intros o a; destruct o;
        let E := fresh "E" in
        intro E; inversion E;
        generalize a
    | |- _ -> _ => intro
    end);
  let rect := fresh "rect" in
  fix rect 1;
  let rect_list := fresh "rect_list" in
  refine (
    let rect_list :=
      fix rect_list es : TProp.Forall P es :=
        match es with
        | [::] => TProp.Forall_nil _
        | e :: l => TProp.Forall_cons (rect e) (rect_list l)
        end in _);
  let do_it := clear rect rect_list; auto in
  let use_hyps :=
    try fold t;
    intros;
    try fold t in *;
    repeat match goal with
    | a : t |- _ =>
      lazymatch goal with
      | H : P a |- _ => fail
      | _ => move: (rect a) => ?
      end
    | l : list t |- _ =>
      lazymatch goal with
      | H : TProp.Forall P l |- _ => fail
      | _ => move: (rect_list l) => ?
      end
    | o : option t |- _ => destruct o
    end in
  case; try solve [ do_it | use_hyps; do_it ].

(** The main instantiation. **)
Ltac rect'_build rect := rect'_build_projection @id rect.

(** Instantiation for lists. **)
Ltac rect'_build_list rect := rect'_build_projection list rect.

(** Instantiation for option types. **)
Ltac rect'_build_option rect := rect'_build_projection option rect.

(** * Lemmas about pickability. **)

Lemma list_search_prefix_pickable : forall A (P : seq A -> Prop),
  comparable A ->
  (forall l, decidable (P l)) ->
  forall l l', pickable (fun lf => l' = l ++ lf /\ P lf).
Proof.
  move=> A + C + l. elim l.
  - move=> P D l'. case (D l') => d.
    + left. by exists l'.
    + right. move=> [lf [E nd]]. by subst.
  - move {l} => a l IH P D l'. case l'.
    + right. by move => [lf [E _]].
    + move {l'} => a' l'. case (C a a') => E.
      * subst. case (IH _ D l').
        -- move=> E. left. destruct E as (lf&E'&p). exists lf. by rewrite E'.
        -- move=> nE. right. move=> [lf [E p]]. apply: nE. exists lf. by inversion E.
      * right. move=> [lf [E' _]]. inversion E'. by apply: E.
Defined.

Lemma list_search_suffix_pickable : forall A (P : seq A -> Prop),
  comparable A ->
  (forall l, decidable (P l)) ->
  forall l l', pickable (fun ls => l' = ls ++ l /\ P ls).
Proof.
  move=> A P C D l l'.
  have Dr: forall l, decidable (P (rev l)).
  { clear - D. move=> l. by apply: D. }
  case (list_search_prefix_pickable C Dr (rev l) (rev l')) => E.
  - left. destruct E as (lf&E&p). exists (rev lf). split => //.
    by rewrite -(revK l') E rev_cat revK.
  - right. move=> [ls [El' p]]. apply: E. exists (rev ls).
    by rewrite revK El' rev_cat.
Defined.

Lemma list_split_pickable2_gen : forall A (P : seq A -> seq A -> Prop) l,
  (forall l1 l2, l = l1 ++ l2 -> decidable (P l1 l2)) ->
  pickable2 (fun l1 l2 => l = l1 ++ l2 /\ P l1 l2).
Proof.
  move=> A + l. elim l.
  - move=> P D. case (D [::] [::]) => // Y.
    + left. by exists ([::], [::]).
    + right. move=> [l1 [l2 [E p]]]. symmetry in E. move: (cat0_inv E) => [? ?]. by subst.
  - move {l} => a l IH P D.
    have Da: forall l1 l2, l = l1 ++ l2 -> decidable (P (a :: l1) l2).
    { clear - D. move=> l1 l2 ?. apply: D. by subst. }
    have Pa: pickable2 (fun l1 l2 => a :: l = l1 ++ l2 /\ P l1 l2 /\ l1 <> [::]).
    {
      have Pa: pickable2 (fun l1 l2 => a :: l = (a :: l1) ++ l2 /\ P (a :: l1) l2).
      {
        apply: pickable2_equiv; last by apply (IH _ Da). move=> l1 l2. split.
        - move=> [E p]. by subst.
        - move=> [E p]. by inversion E.
      }
      case Pa.
      - move=> [[l1 l2] [E p]]. left. exists (a :: l1, l2). by split.
      - move=> Ex. right. move=> [l1 [l2 [E [p d]]]].
        apply: Ex. destruct l1 as [|a' l1] => //. inversion E.
        exists l1. exists l2. by subst.
    }
    case Pa.
    + move=> [[l1 l2] [E [p d]]]. left. by exists (l1, l2).
    + move=> nE. case (D [::] (a :: l)) => //.
      * left. exists ([::], a :: l). by split.
      * move=> np. right. move=> [l1 [l2 [E p]]]. apply: nE.
        exists l1. exists l2. repeat split => //. move=> ?. subst. simpl in E. by subst.
Defined.

Lemma list_split_pickable2 : forall A (P : seq A -> seq A -> Prop),
  (forall l1 l2, decidable (P l1 l2)) ->
  forall l, pickable2 (fun l1 l2 => l = l1 ++ l2 /\ P l1 l2).
Proof.
  move=> A P D l. by apply: list_split_pickable2_gen.
Defined.

Lemma list_search_split_pickable2 : forall A (P : seq A -> seq A -> Prop),
  comparable A ->
  (forall l1 l2, decidable (P l1 l2)) ->
  forall l l', pickable2 (fun l1 l2 => l' = l1 ++ l ++ l2 /\ P l1 l2).
Proof.
  move=> A P C D l l'.
  move: (list_split_pickable2 (P := fun l1 l2 => exists l2', l2 = l ++ l2' /\ P l1 l2')) => D'.
  apply: (pickable2_convert (f := fun '(l1, l2) => (l1, drop (size l) l2))); last apply: (D' _ l').
  - move=> l1 l2 [E1 [l2' [E2 p]]]. subst. rewrite drop_cat.
    rewrite_by ((size l < size l) = false). rewrite_by (size l - size l = 0). by rewrite drop0.
  - move=> l1 l2 [E p]. exists l1. exists (l ++ l2). repeat split => //. by exists l2.
  - move=> l1 l2. apply pickable_decidable. by apply: list_search_prefix_pickable.
Defined.

Lemma list_split_pickable3_gen : forall A (P : seq A -> seq A -> seq A -> Prop) l,
  (forall l1 l2 l3, l = l1 ++ l2 ++ l3 -> decidable (P l1 l2 l3)) ->
  pickable3 (fun l1 l2 l3 => l = l1 ++ l2 ++ l3 /\ P l1 l2 l3).
Proof.
  move=> A P l D.
  have D1: forall l23 l1, l = l1 ++ l23 -> pickable2 (fun l2 l3 => l23 = l2 ++ l3 /\ P l1 l2 l3).
  { move=> l23 l1 E. apply: list_split_pickable2_gen. move=> ? ? E'. subst. by apply D. }
  have: pickable2 (fun l1 l23 => l = l1 ++ l23 /\ exists l2 l3, l23 = l2 ++ l3 /\ P l1 l2 l3).
  { apply: list_split_pickable2_gen. move=> l1 l23 E. by convert_pickable (D1 _ _ E). }
  case.
  - move=> [[l1 l23] [E1 H]]. left. case (D1 _ _ E1).
    + move=> [[l2 l3] [E2 p]]. exists (l1, l2, l3). by subst.
    + move=> Ex. exfalso. apply: Ex. move: H => [l2 [l3 [E2 p]]]. exists l2. by exists l3.
  - move=> Ex. right. move=> [l1 [l2 [l3 [E p]]]]. apply: Ex. exists l1. exists (l2 ++ l3).
    split => //. by repeat eexists.
Defined.

Lemma list_split_pickable3 : forall A (P : seq A -> seq A -> seq A -> Prop),
  (forall l1 l2 l3, decidable (P l1 l2 l3)) ->
  forall l, pickable3 (fun l1 l2 l3 => l = l1 ++ l2 ++ l3 /\ P l1 l2 l3).
Proof.
  move=> A P D l. by apply: list_split_pickable3_gen.
Defined.


