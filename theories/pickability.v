(** Definitions to build computable functions. **)
(* (C) M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * General lemmas about decidability **)

Lemma decidable_and : forall P1 P2,
  decidable P1 ->
  decidable P2 ->
  decidable (P1 /\ P2).
Proof.
  move=> P1 P2. case.
  - move=> p1. case.
    + move=> p2. by left.
    + move=> np2. right. by move=> [? ?].
  - move=> np1 _. right. by move=> [? ?].
Defined.

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
Defined.

Lemma pickable3_weaken : forall A1 A2 A3 (P : A1 -> A2 -> A3 -> Prop),
  pickable3 P ->
  pickable2 (fun a1 a2 => exists a3, P a1 a2 a3).
Proof.
  move=> A1 A2 A3 P. case.
  - move=> [[[x1 x2] x3] p]. left. exists (x1, x2). by exists x3.
  - move=> nE. right. move=> [x1 [x2 [x3 p]]]. apply: nE. exists x1. exists x2. by exists x3.
Defined.

Lemma pickable4_weaken : forall A1 A2 A3 A4 (P : A1 -> A2 -> A3 -> A4 -> Prop),
  pickable4 P ->
  pickable3 (fun a1 a2 a3 => exists a4, P a1 a2 a3 a4).
Proof.
  move=> A1 A2 A3 A4 P. case.
  - move=> [[[[x1 x2] x3] x4] p]. left. exists (x1, x2, x3). by exists x4.
  - move=> nE. right. move=> [x1 [x2 [x3 [x4 p]]]]. apply: nE.
    exists x1. exists x2. exists x3. by exists x4.
Defined.

Lemma pickable5_weaken : forall A1 A2 A3 A4 A5 (P : A1 -> A2 -> A3 -> A4 -> A5 -> Prop),
  pickable5 P ->
  pickable4 (fun a1 a2 a3 a4 => exists a5, P a1 a2 a3 a4 a5).
Proof.
  move=> A1 A2 A3 A4 A5 P. case.
  - move=> [[[[[x1 x2] x3] x4] x5] p]. left. exists (x1, x2, x3, x4). by exists x5.
  - move=> nE. right. move=> [x1 [x2 [x3 [x4 [x5 p]]]]]. apply: nE.
    exists x1. exists x2. exists x3. exists x4. by exists x5.
Defined.

Lemma pickable_augment : forall A1 A2 (P : A2 -> Prop),
  A1 ->
  pickable P ->
  pickable2 (fun _ : A1 => P).
Proof.
  move=> A1 A2 P x1. case.
  - move=> [x2 p]. left. by exists (x1, x2).
  - move=> nE. right. move=> [_ [x2 p]]. apply: nE. by exists x2.
Defined.

Lemma pickable2_augment : forall A1 A2 A3 (P : A2 -> A3 -> Prop),
  A1 ->
  pickable2 P ->
  pickable3 (fun _ : A1 => P).
Proof.
  move=> A1 A2 A3 P x1. case.
  - move=> [[x2 x3] p]. left. by exists (x1, x2, x3).
  - move=> nE. right. move=> [_ [x2 [x3 p]]]. apply: nE. exists x2. by exists x3.
Defined.

Lemma pickable3_augment : forall A1 A2 A3 A4 (P : A2 -> A3 -> A4 -> Prop),
  A1 ->
  pickable3 P ->
  pickable4 (fun _ : A1 => P).
Proof.
  move=> A1 A2 A3 A4 P x1. case.
  - move=> [[[x2 x3] x4] p]. left. by exists (x1, x2, x3, x4).
  - move=> nE. right. move=> [_ [x2 [x3 [x4 p]]]]. apply: nE.
    exists x2. exists x3. by exists x4.
Defined.

Lemma pickable4_augment : forall A1 A2 A3 A4 A5 (P : A2 -> A3 -> A4 -> A5 -> Prop),
  A1 ->
  pickable4 P ->
  pickable5 (fun _ : A1 => P).
Proof.
  move=> A1 A2 A3 A4 A5 P x1. case.
  - move=> [[[[x2 x3] x4] x5] p]. left. by exists (x1, x2, x3, x4, x5).
  - move=> nE. right. move=> [_ [x2 [x3 [x4 [x5 p]]]]]. apply: nE.
    exists x2. exists x3. exists x4. by exists x5.
Defined.

Lemma decidable_pickable : forall A P,
  A ->
  decidable P ->
  pickable (fun _ : A => P).
Proof.
  move=> A P a. case.
  - move=> p. left. by exists a.
  - move=> nP. right. by move=> [_ p].
Defined.

Lemma pickable2_decidable : forall A1 A2 (P : A1 -> A2 -> Prop),
  pickable2 P ->
  decidable (exists x1 x2, P x1 x2).
Proof.
  move=> A1 A2 P p. apply: pickable_decidable. by apply: pickable2_weaken.
Defined.

Lemma pickable3_decidable : forall A1 A2 A3 (P : A1 -> A2 -> A3 -> Prop),
  pickable3 P ->
  decidable (exists x1 x2 x3, P x1 x2 x3).
Proof.
  move=> A1 A2 A3 P p. apply: pickable2_decidable. by apply: pickable3_weaken.
Defined.

Lemma pickable4_decidable : forall A1 A2 A3 A4 (P : A1 -> A2 -> A3 -> A4 -> Prop),
  pickable4 P ->
  decidable (exists x1 x2 x3 x4, P x1 x2 x3 x4).
Proof.
  move=> A1 A2 A3 A4 P p. apply: pickable3_decidable. by apply: pickable4_weaken.
Defined.

Lemma pickable5_decidable : forall A1 A2 A3 A4 A5 (P : A1 -> A2 -> A3 -> A4 -> A5 -> Prop),
  pickable5 P ->
  decidable (exists x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5).
Proof.
  move=> A1 A2 A3 A4 A5 P p. apply: pickable4_decidable. by apply: pickable5_weaken.
Defined.

Lemma pickable2_rotate : forall A1 A2 (P : A1 -> A2 -> Prop),
  pickable2 P ->
  pickable2 (fun a2 a1 => P a1 a2).
Proof.
  move=> A1 A2 P. case.
  - move=> [[x1 x2] p]. left. by exists (x2, x1).
  - move=> nE. right. move=> [x1 [x2 p]]. apply: nE.
    exists x2. by exists x1.
Defined.

Lemma pickable3_rotate : forall A1 A2 A3 (P : A1 -> A2 -> A3 -> Prop),
  pickable3 P ->
  pickable3 (fun a2 a3 a1 => P a1 a2 a3).
Proof.
  move=> A1 A2 A3 P. case.
  - move=> [[[x1 x2] x3] p]. left. by exists (x2, x3, x1).
  - move=> nE. right. move=> [x2 [x3 [x1 p]]]. apply: nE.
    exists x1. exists x2. by exists x3.
Defined.

Lemma pickable4_rotate : forall A1 A2 A3 A4 (P : A1 -> A2 -> A3 -> A4 -> Prop),
  pickable4 P ->
  pickable4 (fun a2 a3 a4 a1 => P a1 a2 a3 a4).
Proof.
  move=> A1 A2 A3 A4 P. case.
  - move=> [[[[x1 x2] x3] x4] p]. left. by exists (x2, x3, x4, x1).
  - move=> nE. right. move=> [x2 [x3 [x4 [x1 p]]]]. apply: nE.
    exists x1. exists x2. exists x3. by exists x4.
Defined.

Lemma pickable5_rotate : forall A1 A2 A3 A4 A5 (P : A1 -> A2 -> A3 -> A4 -> A5 -> Prop),
  pickable5 P ->
  pickable5 (fun a2 a3 a4 a5 a1 => P a1 a2 a3 a4 a5).
Proof.
  move=> A1 A2 A3 A4 A5 P. case.
  - move=> [[[[[x1 x2] x3] x4] x5] p]. left. by exists (x2, x3, x4, x5, x1).
  - move=> nE. right. move=> [x2 [x3 [x4 [x5 [x1 p]]]]]. apply: nE.
    exists x1. exists x2. exists x3. exists x4. by exists x5.
Defined.


(** * Tactics **)

(** Return the function associated to a function call, whichever the arity. **)
Ltac get_head H :=
  lazymatch H with
  | ?f _ => get_head f
  | ?f => constr:(f)
  end.

(** Given a [pickable_n], apply the right [pickable_n_weaken] lemma. **)
Ltac pickable_weaken H :=
  lazymatch type of H with
  | pickable _ => constr:(pickable_decidable H)
  | pickable2 _ => constr:(pickable2_weaken H)
  | pickable3 _ => constr:(pickable3_weaken H)
  | pickable4 _ => constr:(pickable4_weaken H)
  | pickable5 _ => constr:(pickable5_weaken H)
  end.

(** Given a [pickable_n], and an element [a : A1], apply the right [pickable_n_augment] lemma. **)
Ltac pickable_augment a H :=
  lazymatch type of H with
  | decidable _ => constr:(decidable_pickable a H)
  | pickable _ => constr:(pickable_augment a H)
  | pickable2 _ => constr:(pickable2_augment a H)
  | pickable3 _ => constr:(pickable3_augment a H)
  | pickable4 _ => constr:(pickable4_augment a H)
  end.

(** Given a [pickable_n], apply the right [pickable_n_rotate] lemma. **)
Ltac pickable_rotate H :=
  lazymatch type of H with
  | decidable _ => constr:(H)
  | pickable _ => constr:(H)
  | pickable2 _ => constr:(pickable2_rotate H)
  | pickable3 _ => constr:(pickable3_rotate H)
  | pickable4 _ => constr:(pickable4_rotate H)
  | pickable5 _ => constr:(pickable5_rotate H)
  end.

(** Return the arity [n] of a [pickable_n] property. **)
Ltac pickable_arity H :=
  let h := get_head H in
  lazymatch h with
  | decidable => constr:(0 : nat)
  | pickable => constr:(1 : nat)
  | pickable2 => constr:(2 : nat)
  | pickable3 => constr:(3 : nat)
  | pickable4 => constr:(4 : nat)
  | pickable5 => constr:(5 : nat)
  end.

(** Given a [pickable_n] property, produce a [decidable]. **)
Ltac to_decidable H :=
  lazymatch type of H with
  | pickable _ => constr:(pickable_decidable H)
  | _ => to_decidable ltac:(pickable_weaken H)
  end.

(** A tactic to try to apply the right lemmas above to make [H] appliable to the goal. **)
Ltac convert_pickable H :=
  lazymatch goal with
  | |- ?g =>
    let ag := pickable_arity g in
    let rec aux H :=
			let Ht := type of H in
      let aH := pickable_arity Ht in
      let le := eval compute in (Nat.leb ag aH) in
      lazymatch le with
      | true =>
        let eq := eval compute in (Nat.eqb ag aH) in
        lazymatch eq with
        | true => (* ag = aH *)
          lazymatch g with
          | decidable _ => first [ apply H | refine (decidable_equiv _ H) ]
          | pickable _ => first [ apply H | refine (pickable_equiv _ H) ]
          | pickable2 _ => first [ apply H | refine (pickable2_equiv _ H) ]
          | pickable3 _ => first [ apply H | refine (pickable3_equiv _ H) ]
          | pickable4 _ => first [ apply H | refine (pickable4_equiv _ H) ]
          | pickable5 _ => first [ apply H | refine (pickable5_equiv _ H) ]
          end; auto
        | false => (* ag < aH *)
          let rec aux' n H :=
            lazymatch n with
            | 0 => fail
            | S ?n =>
              let H := pickable_weaken H in
              first [ aux H
                    | let H := pickable_rotate H in
                      aux' n H ]
            end in
          aux' aH H
        end
      | false => (* ag > aH *)
        let rec aux' n H :=
          lazymatch n with
          | 0 => fail
          | S ?n =>
            let H := pickable_augment H in
            first [ aux H
                  | let H := pickable_rotate H in
                    aux' n H ]
          end in
        aux' aH H
      end in
    aux H
  end.

