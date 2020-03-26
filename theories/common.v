(** Common useful definitions **)
(* (C) M. Bodin - see LICENSE.txt *)

Require Import Lia.
From mathcomp Require Import ssreflect ssrnat ssrbool seq eqtype.
From compcert Require Integers.

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

(** A useful lemma to link the results of [Scheme Equality] to [Equality.axiom]. **)
Lemma eq_dec_Equality_axiom : forall t (eq_dec : forall x y : t, {x = y} + {x <> y}),
  let eqb v1 v2 := is_left (eq_dec v1 v2) in
  Equality.axiom eqb.
Proof.
  move=> t eq_dec eqb x y. rewrite /eqb. case: (eq_dec x y).
  - move=> E. by apply/ReflectT.
  - move=> E. by apply/ReflectF.
Qed.

(** A useful lemma for the converse: getting a [_dec_eq] from an [Equality.axiom]. **)
Definition Equality_axiom_eq_dec t (eqb : t -> t -> bool) (A : Equality.axiom eqb) :
    forall x y : t, {x = y} + {x <> y}.
  move=> x y. move: (A x y). case E: (eqb x y); inversion 1; by [ left | right ].
Defined.

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
  move=> P b. case; by [ apply: BoolSpecT | apply: BoolSpecF ].
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


(** * Lemmas about lists. **)

Lemma is_true_bool : forall b1 b2 : bool,
  (b1 = b2) <-> (b1 <-> b2).
Proof.
  by do 2 case => /=; split=> //> [H1 H2]; exfalso; eauto.
Qed.

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

Lemma all_filter : forall A p (l : seq A),
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

End TProp.
