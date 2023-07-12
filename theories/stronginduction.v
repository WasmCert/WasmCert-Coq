(* from https://github.com/tchajed/strong-induction *)

(** Here we prove the principle of strong induction, induction on the natural
  numbers where the inductive hypothesis includes all smaller natural numbers. *)

Require Import PeanoNat.

Section StrongInduction.

  Variable P : nat -> Type.

  (** The stronger inductive hypothesis given in strong induction. The standard
    [nat] induction principle provides only [n = pred m], with [P 0] required
    separately. *)
  Hypothesis IH : forall m, (forall n, n < m -> P n) -> P m.

  Lemma P0 : P 0.
  Proof.
    apply IH; intros.
    exfalso; inversion H.
  Qed.

  Hint Resolve P0 : core.

  Lemma pred_increasing : forall n m,
    n <= m ->
    Nat.pred n <= Nat.pred m.
  Proof.
    induction n; simpl; intros.
    - apply le_0_n.
    - induction H; subst; simpl; auto.
      destruct m; auto.
  Qed.

  (** * Strengthen the induction hypothesis. *)

  Local Lemma strong_rect_all : forall n,
    (forall m, m <= n -> P m).
  Proof.
    induction n.
    - intros m H. assert (m = 0).
      { inversion H. auto. }
      subst. auto.
    - intros m H. apply IH.
      intros m' H'. apply IHn.
      apply le_S_n. eapply Nat.le_trans; eauto.
  Qed.

  Theorem strong_rect : forall n, P n.
  Proof.
    eauto using strong_rect_all.
  Qed.

End StrongInduction.

Definition strong_induction (P : nat -> Prop) := strong_rect P.

Tactic Notation "strong" "induction" ident(n) := induction n using strong_rect.
