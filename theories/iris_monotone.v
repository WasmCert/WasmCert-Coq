From iris.algebra Require Export cmra auth.
From iris.base_logic Require Import base_logic.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.
Local Arguments ofe_dist !_ /.
Local Arguments ofe_equiv ! _ /.

Definition monotone {A : Type} (R : relation A) : Type := list A.

Definition principal {A : Type} (R : relation A) (a : A) :
  monotone R := [a].

Section monotone.
Local Set Default Proof Using "Type".
Context {A : ofe} {R : relation A}.
Implicit Types a b : A.
Implicit Types x y : monotone R.

Definition Below (a : A) (x : monotone R) := ∃ b, b ∈ x ∧ R a b.

Lemma Below_app a x y : Below a (x ++ y) ↔ Below a x ∨ Below a y.
Proof.
  split.
  - intros (b & [|]%elem_of_app & ?); [left|right]; exists b; eauto.
  - intros [(b & Hb1 & Hb2)|(b & Hb1 & Hb2)]; exists b; rewrite elem_of_app; eauto.
Qed.

Lemma Below_principal a b : Below a (principal R b) ↔ R a b.
Proof.
  split.
  - intros (c & ->%elem_of_list_singleton & ?); done.
  - intros Hab; exists b; split; first apply elem_of_list_singleton; done.
Qed.

(* OFE *)
Instance monotone_dist : Dist (monotone R) :=
  λ n x y, ∀ a, Below a x ↔ Below a y.

Instance monotone_equiv : Equiv (monotone R) := λ x y, ∀ n, x ≡{n}≡ y.

Definition monotone_ofe_mixin : OfeMixin (monotone R).
Proof.
  split.
  - rewrite /equiv /monotone_equiv /dist /monotone_dist; intuition auto using O.
  - intros n; split.
    + rewrite /dist /monotone_dist /equiv /monotone_equiv; intuition.
    + rewrite /dist /monotone_dist /equiv /monotone_equiv; intros ? ? Heq a.
      split; apply Heq.
    + rewrite /dist /monotone_dist /equiv /monotone_equiv;
        intros ? ? ? Heq Heq' a.
      split; intros Hxy.
      * apply Heq'; apply Heq; auto.
      * apply Heq; apply Heq'; auto.
  - intros n x y; rewrite /dist /monotone_dist; auto.
Qed.
Canonical Structure monotoneC := Ofe (monotone R) monotone_ofe_mixin.

(* CMRA *)
Instance monotone_validN : ValidN (monotone R) := λ n x, True.
Instance monotone_valid : Valid (monotone R) := λ x, True.

Program Instance monotone_op : Op (monotone R) := λ x y, x ++ y.
Instance monotone_pcore : PCore (monotone R) := Some.

Instance monotone_comm : Comm (≡) (@op (monotone R) _).
Proof.
  intros x y n a; rewrite /Below.
  setoid_rewrite elem_of_app; split=> Ha; firstorder.
Qed.
Instance monotone_assoc : Assoc (≡) (@op (monotone R) _).
Proof.
  intros x y z n a; rewrite /Below /=.
  repeat setoid_rewrite elem_of_app; split=> Ha; firstorder.
Qed.
Lemma monotone_idemp (x : monotone R) : x ⋅ x ≡ x.
Proof.
  intros n a; rewrite /Below.
  setoid_rewrite elem_of_app; split=> Ha; firstorder.
Qed.

Instance monotone_validN_ne n :
  Proper (dist n ==> impl) (@validN (monotone R) _ n).
Proof. intros x y ?; rewrite /impl; auto. Qed.
Instance monotone_validN_proper n : Proper (equiv ==> iff) (@validN (monotone R) _ n).
Proof. move=> x y /equiv_dist H; auto. Qed.

Instance monotone_op_ne' x : NonExpansive (op x).
Proof.
  intros n y1 y2; rewrite /dist /monotone_dist /equiv /monotone_equiv /Below.
  rewrite /=; setoid_rewrite elem_of_app => Heq a.
  specialize (Heq a); destruct Heq as [Heq1 Heq2].
  split; intros [b [[Hb|Hb] HRb]]; eauto.
  - destruct Heq1 as [? [? ?]]; eauto.
  - destruct Heq2 as [? [? ?]]; eauto.
Qed.
Instance monotone_op_ne : NonExpansive2 (@op (monotone R) _).
Proof. by intros n x1 x2 Hx y1 y2 Hy; rewrite Hy !(comm _ _ y2) Hx. Qed.
Instance monotone_op_proper :
  Proper ((≡) ==> (≡) ==> (≡)) (@op (monotone R) _) := ne_proper_2 _.

Lemma monotone_included (x y : monotone R) : x ≼ y ↔ y ≡ x ⋅ y.
Proof.
  split; [|by intros ?; exists y].
  by intros [z Hz]; rewrite Hz assoc monotone_idemp.
Qed.

Definition monotone_cmra_mixin : CmraMixin (monotone R).
Proof.
  apply cmra_total_mixin; try apply _ || by eauto.
  - intros ?; apply monotone_idemp.
  - rewrite /equiv /monotone_equiv /dist /monotone_dist; eauto.
Qed.
Canonical Structure monotoneR : cmra := Cmra (monotone R) monotone_cmra_mixin.

Global Instance monotone_cmra_total : CmraTotal monotoneR.
Proof. rewrite /CmraTotal; eauto. Qed.
Global Instance monotone_core_id (x : monotone R) : CoreId x.
Proof. by constructor. Qed.

Global Instance monotone_cmra_discrete : CmraDiscrete monotoneR.
Proof.
  split; auto.
  intros ? ?.
  rewrite /dist /equiv /= /cmra_dist /cmra_equiv /=
          /monotone_dist /monotone_equiv /dist /monotone_dist; eauto.
Qed.

Instance monotone_empty : Unit (monotone R) := @nil A.
Lemma auth_ucmra_mixin : UcmraMixin (monotone R).
Proof. split; done. Qed.

Canonical Structure monotoneUR := Ucmra (monotone R) auth_ucmra_mixin.

Global Instance principal_ne
       `{HRne : !∀ n, Proper ((dist n) ==> (dist n) ==> iff) R} :
  NonExpansive (principal R).
Proof. intros n a1 a2 Ha; split; rewrite /= !Below_principal !Ha; done. Qed.

Global Instance principal_proper
       {HRne : ∀ n, Proper ((dist n) ==> (dist n) ==> iff) R} :
  Proper ((≡) ==> (≡)) (principal R) := ne_proper _.

Global Instance principal_discrete a : Discrete (principal R a).
Proof.
  intros y; rewrite /dist /ofe_dist /= /equiv /ofe_equiv /= /monotone_equiv;
    eauto.
Qed.

Lemma principal_injN_general n a b :
  principal R a ≡{n}≡ principal R b → R a a → R a b.
Proof.
  rewrite /principal /dist /monotone_dist => Hab Haa.
  - destruct (Hab a) as [Ha _]; edestruct Ha as [? [?%elem_of_list_singleton ?]];
    subst; eauto.
    eexists _; split; first apply elem_of_list_singleton; eauto.
Qed.

Lemma principal_inj_general a b :
  principal R a ≡ principal R b → R a a → R a b.
Proof. intros Hab; apply (principal_injN_general 0); eauto. Qed.

Global Instance principal_injN_general' `{!Reflexive R} n :
  Inj (λ a b, R a b ∧ R b a) (dist n) (principal R).
Proof.
  intros x y Hxy; split; eapply (principal_injN_general n); eauto.
Qed.

Global Instance principal_inj_general' `{!Reflexive R} :
  Inj (λ a b, R a b ∧ R b a) (≡) (principal R).
Proof.
  intros x y Hxy; specialize (Hxy 0); eapply principal_injN_general'; eauto.
Qed.

Global Instance principal_injN `{!Reflexive R} {Has : AntiSymm (≡) R} n :
  Inj (dist n) (dist n) (principal R).
Proof.
  intros x y [Hxy Hyx]%principal_injN_general'.
  erewrite (@anti_symm _ _ _ Has); eauto.
Qed.
Global Instance principal_inj `{!Reflexive R} `{!AntiSymm (≡) R} :
  Inj (≡) (≡) (principal R).
Proof. intros ???. apply equiv_dist=>n. by apply principal_injN, equiv_dist. Qed.

Lemma principal_R_opN_base `{!Transitive R} n x y :
  (∀ b, b ∈ y → ∃ c, c ∈ x ∧ R b c) → y ⋅ x ≡{n}≡ x.
Proof.
  intros HR; split; rewrite /op /monotone_op Below_app; [|by firstorder].
  intros [(c & (d & Hd1 & Hd2)%HR & Hc2)|]; [|done].
  exists d; split; [|transitivity c]; done.
Qed.

Lemma principal_R_opN `{!Transitive R} n a b :
  R a b → principal R a ⋅ principal R b ≡{n}≡ principal R b.
Proof.
  intros; apply principal_R_opN_base; intros c; rewrite /principal.
  setoid_rewrite elem_of_list_singleton => ->; eauto.
Qed.

Lemma principal_R_op `{!Transitive R} a b :
  R a b → principal R a ⋅ principal R b ≡ principal R b.
Proof. by intros ? ?; apply principal_R_opN. Qed.

Lemma principal_op_RN n a b x :
  R a a → principal R a ⋅ x ≡{n}≡ principal R b → R a b.
Proof.
  intros Ha HR.
  destruct (HR a) as [[z [HR1%elem_of_list_singleton HR2]] _];
    last by subst; eauto.
  rewrite /op /monotone_op /principal Below_app Below_principal; auto.
Qed.

Lemma principal_op_R a b x :
  R a a → principal R a ⋅ x ≡ principal R b → R a b.
Proof. intros ? ?; eapply (principal_op_RN 0); eauto. Qed.

Lemma principal_op_R' `{!Reflexive R} a b x :
  principal R a ⋅ x ≡ principal R b → R a b.
Proof. intros; eapply principal_op_R; eauto. Qed.

Lemma principal_includedN `{!PreOrder R} n a b :
  principal R a ≼{n} principal R b ↔ R a b.
Proof.
  split.
  - intros [z Hz]; eapply principal_op_RN; last by rewrite Hz; eauto.
    reflexivity.
  - intros ?; exists (principal R b); rewrite principal_R_opN; eauto.
Qed.

Lemma principal_included `{!PreOrder R} a b :
  principal R a ≼ principal R b ↔ R a b.
Proof.
  split.
  - intros [z Hz]; eapply principal_op_R; last by rewrite Hz; eauto.
    reflexivity.
  - intros ?; exists (principal R b); rewrite principal_R_op; eauto.
Qed.

(** Internalized properties *)
Lemma monotone_equivI `{!(∀ n : nat, Proper (dist n ==> dist n ==> iff) R)}
      `{!Reflexive R} `{!AntiSymm (≡) R} {M} a b :
  principal R a ≡ principal R b ⊣⊢ (a ≡ b : uPred M).
Proof.
  uPred.unseal. do 2 split.
  - intros Hx. exact: principal_injN.
  - intros Hx. exact: principal_ne.
Qed.

Lemma monotone_local_update_grow `{!Transitive R} a q na:
  R a na →
  (principal R a, q) ~l~> (principal R na, principal R na).
Proof.
  intros Hana Hanb.
  apply local_update_unital_discrete.
  intros z _ Habz.
  split; first done.
  intros n; specialize (Habz n).
  intros x; split.
  - intros (y & ->%elem_of_list_singleton & Hy2).
    by exists na; split; first constructor.
  - intros (y & [->|Hy1]%elem_of_cons & Hy2).
    + by exists na; split; first constructor.
    + exists na; split; first constructor.
      specialize (Habz x) as [_ [c [->%elem_of_list_singleton Hc2]]].
      { exists y; split; first (by apply elem_of_app; right); eauto. }
      etrans; eauto.
Qed.

Lemma monotone_local_update_get_frag `{!PreOrder R} a na:
  R na a →
  (principal R a, ε) ~l~> (principal R a, principal R na).
Proof.
  intros Hana.
  apply local_update_unital_discrete.
  intros z _.
  rewrite left_id.
  intros <-.
  split; first done.
  apply monotone_included.
  by apply principal_included.
Qed.

Lemma monotone_update `{!PreOrder R} a b c:
  R a b →
  R c b →
  ● principal R a ~~> ● principal R b ⋅ ◯ principal R c.
Proof.
  intros Hab Hcb.
  etrans.
  { apply auth_update_alloc; apply (monotone_local_update_grow _ _ b); done. }
  etrans; first apply cmra_update_op_l.
  apply auth_update_alloc.
  apply monotone_local_update_get_frag; done.
Qed.


End monotone.

Arguments monotoneC {_} _.
Arguments monotoneR {_} _.
Arguments monotoneUR {_} _.


(** Having an instance of this class for a relation R allows almost
all lemmas provided in this module to be used. See type classes
required by some of preceding the lemmas and instances in the to see
how this works.

The only lemma that requires extra conditions on R is the injectivity
of principal which requires antisymmetry. *)
Class ProperPreOrder {A : Type} `{Dist A} (R : relation A) := {
  ProperPreOrder_preorder :> PreOrder R;
  ProperPreOrder_ne :> ∀ n, Proper ((dist n) ==> (dist n) ==> iff) R
}.
