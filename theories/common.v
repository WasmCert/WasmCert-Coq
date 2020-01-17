(** Common useful definitions **)
(* (C) M. Bodin - see LICENSE.txt *)

Require Import Lia.
From ExtLib Require Import Data.HList.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** An extension of [lia] that just tries to rewrite things in the way [lia] that expects.
  Not very optimised. **)
Ltac lias :=
  let rec iter f l :=
    match l with
    | @Hnil _ _ => idtac
    | @Hcons _ _ _ _ ?t ?l' =>
      try f t; iter f l'
    end in
  iter ltac:(fun t => rewrite /t)
    (Hcons subn (Hcons subn_rec (Hcons addn (Hcons addn_rec Hnil))) : hlist id _);
  let reflects :=
    constr:(Hcons (@ltP) (Hcons (@leP) Hnil : hlist id _)) in
  iter ltac:(fun t => move/t) reflects;
  iter ltac:(fun t => apply/t; try lia) reflects;
  try lia;
  match goal with
  | |- ?f _ => unfold f; lia
  end.

(** Rewrite an arithmetic equality. **)
Ltac rewrite_by E :=
  let R := fresh "R" in
  have R: E;
    [ by [auto|lias]
    | rewrite {} R ].

(** A useful lemma to link the results of [Scheme Equality] to [Equality.axiom]. **)
Lemma Equality_axiom_eq_dec : forall t (eq_dec : forall x y : t, {x = y} + {x <> y}),
  let eqb v1 v2 := is_left (eq_dec v1 v2) in
  Equality.axiom eqb.
Proof.
  move=> t eq_dec eqb x y. rewrite /eqb. case: (eq_dec x y).
  - move=> E. by apply/ReflectT.
  - move=> E. by apply/ReflectF.
Qed.

(** A useful lemma for the converse: getting a [_dec_eq] from an [Equality.axiom]. **)
Definition eq_dec_Equality_axiom t (eqb : t -> t -> bool) (A : Equality.axiom eqb) :
    forall x y : t, {x = y} + {x <> y}.
  move=> x y. move: (A x y). case E: (eqb x y); inversion 1; by [ left | right ].
Defined.

