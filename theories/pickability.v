(** Definitions to build computable functions. **)
(* (C) M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrbool.

Set Implicit Arguments.

(** * General lemmas about decidability **)

Lemma decidable_equiv : forall P1 P2,
  (P1 <-> P2) ->
  decidable P1 ->
  decidable P2.
Proof.
  move=> P1 P2 [I1 I2] [H | nH].
  - by left; auto.
  - by right; auto.
Defined.

Lemma is_true_bool : forall b1 b2 : bool,
  (b1 = b2) <-> (b1 <-> b2).
Proof.
  by do 2 case => /=; split=> //> [H1 H2]; exfalso; eauto.
Qed.

Lemma is_true_decidable : forall b : bool, decidable b.
Proof.
  by case; [ left | right ].
Defined.

(** * Definition of Pickability **)

(** A variant of [decidable] in which we provide a witness. **)
Definition pickable A (P : A -> Prop) :=
  { x | P x } + { ~ exists x, P x }.

Definition pickable2 A1 A2 (P : A1 -> A2 -> Prop) :=
  { x | let '(x1, x2) := x in P x1 x2 } + { ~ exists x1 x2, P x1 x2 }.

Definition pickable3 A1 A2 A3 (P : A1 -> A2 -> A3 -> Prop) :=
  { x | let '(x1, x2, x3) := x in P x1 x2 x3 } + { ~ exists x1 x2 x3, P x1 x2 x3 }.

Definition pickable4 A1 A2 A3 A4 (P : A1 -> A2 -> A3 -> A4 -> Prop) :=
  { x | let '(x1, x2, x3, x4) := x in P x1 x2 x3 x4 } + { ~ exists x1 x2 x3 x4, P x1 x2 x3 x4 }.

Definition pickable5 A1 A2 A3 A4 A5 (P : A1 -> A2 -> A3 -> A4 -> A5 -> Prop) :=
  { x | let '(x1, x2, x3, x4, x5) := x in P x1 x2 x3 x4 x5 } + { ~ exists x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 }.

(** * Lemmas about pickability **)

Lemma pickable_decidable : forall A (P : A -> Prop),
  pickable P ->
  decidable (exists x, P x).
Proof.
  move=> A P. case.
  - move=> [x p]. left. by exists x.
  - move=> N. by right.
Defined.

Lemma pickable2_decidable : forall A1 A2 (P : A1 -> A2 -> Prop),
  pickable2 P ->
  decidable (exists x1 x2, P x1 x2).
Proof.
  move=> A1 A2 P. case.
  - move=> [[x1 x2] p]. left. by exists x1; exists x2.
  - move=> N. by right.
Defined.

Lemma pickable3_decidable : forall A1 A2 A3 (P : A1 -> A2 -> A3 -> Prop),
  pickable3 P ->
  decidable (exists x1 x2 x3, P x1 x2 x3).
Proof.
  move=> A1 A2 A3 P. case.
  - move=> [[[x1 x2] x3] p]. left. by exists x1; exists x2; exists x3.
  - move=> N. by right.
Defined.

Lemma pickable4_decidable : forall A1 A2 A3 A4 (P : A1 -> A2 -> A3 -> A4 -> Prop),
  pickable4 P ->
  decidable (exists x1 x2 x3 x4, P x1 x2 x3 x4).
Proof.
  move=> A1 A2 A3 A4 P. case.
  - move=> [[[[x1 x2] x3] x4] p]. left. by exists x1; exists x2; exists x3; exists x4.
  - move=> N. by right.
Defined.

Lemma pickable5_decidable : forall A1 A2 A3 A4 A5 (P : A1 -> A2 -> A3 -> A4 -> A5 -> Prop),
  pickable5 P ->
  decidable (exists x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5).
Proof.
  move=> A1 A2 A3 A4 A5 P. case.
  - move=> [[[[[x1 x2] x3] x4] x5] p]. left. by exists x1; exists x2; exists x3; exists x4; exists x5.
  - move=> N. by right.
Defined.

Lemma pickable_equiv : forall A (P1 P2 : A -> Prop),
  (forall a, P1 a <-> P2 a) ->
  pickable P1 ->
  pickable P2.
Proof.
  move=> A P1 P2 E. case.
  - move=> [x p]. left. exists x. by apply E.
  - move=> N. right. move=> [x p]. apply: N. exists x. by apply E.
Defined.

Lemma pickable2_equiv : forall A1 A2 (P1 P2 : A1 -> A2 -> Prop),
  (forall a1 a2, P1 a1 a2 <-> P2 a1 a2) ->
  pickable2 P1 ->
  pickable2 P2.
Proof.
  move=> A1 A2 P1 P2 E. case.
  - move=> [[x1 x2] p]. left. exists (x1, x2). by apply E.
  - move=> N. right. move=> [x1 [x2 p]]. apply: N. exists x1. exists x2. by apply E.
Defined.

Lemma pickable3_equiv : forall A1 A2 A3 (P1 P2 : A1 -> A2 -> A3 -> Prop),
  (forall a1 a2 a3, P1 a1 a2 a3 <-> P2 a1 a2 a3) ->
  pickable3 P1 ->
  pickable3 P2.
Proof.
  move=> A1 A2 A3 P1 P2 E. case.
  - move=> [[[x1 x2] x3] p]. left. exists (x1, x2, x3). by apply E.
  - move=> N. right. move=> [x1 [x2 [x3 p]]]. apply: N.
    exists x1. exists x2. exists x3. by apply E.
Defined.

Lemma pickable4_equiv : forall A1 A2 A3 A4 (P1 P2 : A1 -> A2 -> A3 -> A4 -> Prop),
  (forall a1 a2 a3 a4, P1 a1 a2 a3 a4 <-> P2 a1 a2 a3 a4) ->
  pickable4 P1 ->
  pickable4 P2.
Proof.
  move=> A1 A2 A3 A4 P1 P2 E. case.
  - move=> [[[[x1 x2] x3] x4] p]. left. exists (x1, x2, x3, x4). by apply E.
  - move=> N. right. move=> [x1 [x2 [x3 [x4 p]]]]. apply: N.
    exists x1. exists x2. exists x3. exists x4. by apply E.
Defined.

Lemma pickable5_equiv : forall A1 A2 A3 A4 A5 (P1 P2 : A1 -> A2 -> A3 -> A4 -> A5 -> Prop),
  (forall a1 a2 a3 a4 a5, P1 a1 a2 a3 a4 a5 <-> P2 a1 a2 a3 a4 a5) ->
  pickable5 P1 ->
  pickable5 P2.
Proof.
  move=> A1 A2 A3 A4 A5 P1 P2 E. case.
  - move=> [[[[[x1 x2] x3] x4] x5] p]. left. exists (x1, x2, x3, x4, x5). by apply E.
  - move=> N. right. move=> [x1 [x2 [x3 [x4 [x5 p]]]]]. apply: N.
    exists x1. exists x2. exists x3. exists x4. exists x5. by apply E.
Defined.

Lemma pickable_convert : forall A B (P1 P2 : _ -> Prop) (f : A -> B),
  (forall a, P1 a -> P2 (f a)) ->
  (forall b, P2 b -> exists a, P1 a) ->
  pickable P1 ->
  pickable P2.
Proof.
  move=> A B P1 P2 f E1 E2. case.
  - move=> [x p]. left. exists (f x). by apply: E1.
  - move=> N. right. move=> [x p]. apply: N. move: (E2 _ p) => [a p']. by exists a.
Defined.

Lemma pickable2_convert : forall A1 A2 B1 B2 (P1 P2 : _ -> _ -> Prop) (f : A1 * A2 -> B1 * B2),
  (forall a1 a2, P1 a1 a2 -> let (b1, b2) := f (a1, a2) in P2 b1 b2) ->
  (forall b1 b2, P2 b1 b2 -> exists a1 a2, P1 a1 a2) ->
  pickable2 P1 ->
  pickable2 P2.
Proof.
  move=> A1 A2 B1 B2 P1 P2 f E1 E2. case.
  - move=> [[x1 x2] p]. left. exists (f (x1, x2)). by apply: E1.
  - move=> N. right. move=> [x1 [x2 p]]. apply: N. move: (E2 _ _ p) => [a1 [a2 p']].
    exists a1. by exists a2.
Defined.

Lemma pickable2_weaken : forall A1 A2 (P : A1 -> A2 -> Prop),
  pickable2 P ->
  pickable (fun a1 => exists a2, P a1 a2).
Proof.
  move=> A1 A2 P. case.
  - move=> [[x1 x2] p]. left. exists x1. by exists x2.
  - move=> nE. right. move=> [x1 [x2 p]]. apply: nE. exists x1. by exists x2.
Qed.

Lemma pickable3_weaken : forall A1 A2 A3 (P : A1 -> A2 -> A3 -> Prop),
  pickable3 P ->
  pickable2 (fun a1 a2 => exists a3, P a1 a2 a3).
Proof.
  move=> A1 A2 A3 P. case.
  - move=> [[[x1 x2] x3] p]. left. exists (x1, x2). by exists x3.
  - move=> nE. right. move=> [x1 [x2 [x3 p]]]. apply: nE. exists x1. exists x2. by exists x3.
Qed.

Lemma pickable4_weaken : forall A1 A2 A3 A4 (P : A1 -> A2 -> A3 -> A4 -> Prop),
  pickable4 P ->
  pickable3 (fun a1 a2 a3 => exists a4, P a1 a2 a3 a4).
Proof.
  move=> A1 A2 A3 A4 P. case.
  - move=> [[[[x1 x2] x3] x4] p]. left. exists (x1, x2, x3). by exists x4.
  - move=> nE. right. move=> [x1 [x2 [x3 [x4 p]]]]. apply: nE.
    exists x1. exists x2. exists x3. by exists x4.
Qed.

Lemma pickable5_weaken : forall A1 A2 A3 A4 A5 (P : A1 -> A2 -> A3 -> A4 -> A5 -> Prop),
  pickable5 P ->
  pickable4 (fun a1 a2 a3 a4 => exists a5, P a1 a2 a3 a4 a5).
Proof.
  move=> A1 A2 A3 A4 A5 P. case.
  - move=> [[[[[x1 x2] x3] x4] x5] p]. left. exists (x1, x2, x3, x4). by exists x5.
  - move=> nE. right. move=> [x1 [x2 [x3 [x4 [x5 p]]]]]. apply: nE.
    exists x1. exists x2. exists x3. exists x4. by exists x5.
Qed.


