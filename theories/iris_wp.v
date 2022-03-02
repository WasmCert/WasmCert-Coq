From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Export language.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.


Class irisGS (Λ : language) (Σ : gFunctors) := IrisG {
  iris_invGS :> invGS Σ;

  (** The state interpretation is an invariant that should hold in
  between each step of reduction. Here [Λstate] is the global state,
  the first [nat] is the number of steps already performed by the
  program, [list Λobservation] are the remaining observations, and the
  last [nat] is the number of forked-off threads (not the total number
  of threads, which is one higher because there is always a main
  thread). *)
  state_interp : state Λ → nat → list (observation Λ) → nat → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : val Λ → iProp Σ;

  (** Number of additional logical steps (i.e., later modality in the
  definition of WP) per physical step, depending on the physical steps
  counter. In addition to these steps, the definition of WP adds one
  extra later per physical step to make sure that there is at least
  one later for each physical step. *)
  num_laters_per_step : nat → nat;

  (** When performing pure steps, the state interpretation needs to be
  adapted for the change in the [ns] parameter.

  Note that we use an empty-mask fancy update here. We could also use
  a basic update or a bare magic wand, the expressiveness of the
  framework would be the same. If we removed the modality here, then
  the client would have to include the modality it needs as part of
  the definition of [state_interp]. Since adding the modality as part
  of the definition [state_interp_mono] does not significantly
  complicate the formalization in Iris, we prefer simplifying the
  client. *)
  state_interp_mono σ ns κs nt:
    state_interp σ ns κs nt ={∅}=∗ state_interp σ (S ns) κs nt
}.
Global Opaque iris_invGS.

Definition wp_pre `{!irisGS Λ Σ} {A : Type} (P: A -> iProp Σ) (s : stuckness)
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  (match to_val e1 with
  | Some v => |={E}=> Φ v (* ∗ P *)
  | None => ∀ σ1 ns κ κs nt,
     (state_interp σ1 ns (κ ++ κs) nt) ={E,∅}=∗
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝
         ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
         state_interp σ2 (S ns) κs (length efs + nt) ∗
         ∃ a, P a ∗
         (P a -∗ wp E e2 Φ) ∗
         [∗ list] i ↦ ef ∈ efs, wp ⊤ ef fork_post
end)%I.

Local Instance wp_pre_contractive `{!irisGS Λ Σ} {A : Type} (P : A -> iProp Σ) s: Contractive (wp_pre P s).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ.
  do 24 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IH]; simpl => //.
  - repeat (f_contractive || f_equiv); apply Hwp.
  - by rewrite -IH.
Qed.

Definition wp_def `{!irisGS Λ Σ} `{P : A -> iProp Σ} : Wp (iProp Σ) (expr Λ) (val Λ) stuckness :=
  λ (s: stuckness), fixpoint (wp_pre P s).
Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Λ Σ _ _ _}.
Global Existing Instance wp'.
Lemma wp_eq  `{!irisGS Λ Σ} `{P : A -> iProp Σ} : @wp _ _ _ _ (@wp' _ _ _ _ P) = @wp_def Λ Σ _ _ P.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.


Section wp.
  Context `{Pred : A -> iProp Σ, !irisGS Λ Σ}.
          
  Implicit Types s : stuckness.
  Implicit Types Q : state Λ -> iProp Σ.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Instance wp_instance : Wp (iProp Σ) (expr Λ) (val Λ) stuckness.
  Proof using Pred irisGS0 Λ Σ. eapply wp'. Unshelve. - apply A. - apply Pred. Defined.

  (* Reprove some useful auxiliary lemmas *)
  Lemma wp_unfold s E e Φ :
    WP e @ s; E {{ Φ }} ⊣⊢ wp_pre Pred s (wp (PROP:=iProp Σ) s) E e Φ.
  Proof. rewrite wp_eq. apply (fixpoint_unfold (wp_pre Pred s)). Qed.

  Lemma wp_value_fupd' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
  Proof. rewrite wp_unfold /wp_pre to_of_val. auto. Qed.

  Global Instance wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
  Proof.
    revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
    rewrite !wp_unfold /wp_pre /=.
    (* FIXME: figure out a way to properly automate this proof *)
    (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
       is very slow here *)
    do 23 (f_contractive || f_equiv).
    
    (* FIXME : simplify this proof once we have a good definition and a
       proper instance for step_fupdN. *)
    induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
    do 5 (f_contractive || f_equiv).
    rewrite IH; [done|lia|]. intros v. eapply dist_S, HΦ.
  Qed.
  Global Instance wp_proper s E e :
    Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
  Qed.
  Global Instance wp_contractive s E e n :
    TCEq (to_val e) None →
    Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
  Proof.
    intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
    do 23 (f_contractive || f_equiv).
    (* FIXME : simplify this proof once we have a good definition and a
       proper instance for step_fupdN. *)
    induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
    repeat f_equiv.
  Qed.

  Lemma wp_strong_mono s1 s2 E1 E2 e Φ Ψ :
    s1 ⊑ s2 → E1 ⊆ E2 →
    WP e @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s2; E2 {{ Ψ }}.
  Proof.
    iIntros (? HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
    rewrite !wp_unfold /wp_pre /=.
    destruct (to_val e) as [v|] eqn:?.
    { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
    iIntros (σ1 ns κ κs nt) "Hσ".
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
    iMod ("H" with "[$]") as "[% H]".
    iModIntro. iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep).
    iMod ("H" with "[//]") as "H". iIntros "!> !>".  iMod "H". iModIntro.
    iApply (step_fupdN_wand with "[H]"); first by iApply "H".
    iIntros ">[$ H]". iDestruct "H" as (a) "(H' & H & Hefs)".
    iMod "Hclose" as "_". iModIntro. iExists _. iFrame. iSplitR "Hefs".
    - iIntros "Hpred". iApply ("IH" with "[//] [Hpred H] HΦ"). iApply "H". iFrame.
    - iApply (big_sepL_impl with "Hefs"); iIntros "!>" (k ef _).
      iIntros "H". iApply ("IH" with "[] H"); auto.
  Qed.

  Lemma fupd_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
  Proof.
    rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
    { by iMod "H". }
    iIntros (σ1 ns κ κs nt) "Hσ1". iMod "H". by iApply "H".
  Qed.
  Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
  Proof. iIntros "H". iApply (wp_strong_mono s s E with "H"); auto.
         (* iIntros (v) "[H H']". iMod "H". iModIntro. iFrame.  *)Qed.
  
  Lemma wp_atomic s E1 E2 e Φ a `{!Atomic (stuckness_to_atomicity s) e} :
    (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v ∗ Pred a }}) ⊢ WP e @ s; E1 {{ v, Φ v ∗ Pred a }}.
  Proof.
    iIntros "H". rewrite !wp_unfold /wp_pre.
    destruct (to_val e) as [v|] eqn:He.
    { by iDestruct "H" as ">>>$". }
    iIntros (σ1 ns κ κs nt) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
    iModIntro. iIntros (e2 σ2 efs Hstep).
    iApply (step_fupdN_wand with "[H]"); first by iApply "H".
    iIntros ">[Hσ H]". iDestruct "H" as (a') "(H' & H & Hefs)". destruct s.
    - rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
      + iDestruct ("H" with "H'") as ">>[? ?]". iFrame.
        iModIntro. iExists _. iFrame. iIntros "?".
        iApply wp_unfold. rewrite /wp_pre /= He2. by iFrame.
      + iDestruct ("H" with "H'") as "H".
        iMod ("H" $! _ _ [] with "[$]") as "[H _]". iDestruct "H" as %(? & ? & ? & ? & ?).
        by edestruct (atomic _ _ _ _ _ Hstep).
    - destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val].
      rewrite wp_value_fupd'. iMod ("H" with "[$]") as ">[H H']".
      iModIntro. iFrame "Hσ Hefs". iExists _. iFrame. iIntros "?". iApply wp_value_fupd'. by iFrame.
  Qed.

  (** In this stronger version of [wp_step_fupdN], the masks in the
      step-taking fancy update are a bit weird and somewhat difficult to
      use in practice. Hence, we prove it for the sake of completeness,
      but [wp_step_fupdN] is just a little bit weaker, suffices in
      practice and is easier to use.

   See the statement of [wp_step_fupdN] below to understand the use of
   ordinary conjunction here. *)
  Lemma wp_step_fupdN_strong n s E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    (∀ σ ns κs nt, state_interp σ ns κs nt
                   ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
      ((|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> P) ∗
        WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
        WP e @ s; E1 {{ Φ }}.
  Proof.
    destruct n as [|n].
    { iIntros (_ ?) "/= [_ [HP Hwp]]".
      iApply (wp_strong_mono with "Hwp"); [done..|].
      iIntros (v) "H". iFrame. iApply ("H" with "[>HP]"). by do 2 iMod "HP". }
    rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "H".
    iIntros (σ1 ns κ κs nt) "Hσ".
    destruct (decide (n ≤ num_laters_per_step ns)) as [Hn|Hn]; first last.
    { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. }
    iDestruct "H" as "[_ [>HP Hwp]]". iMod ("Hwp" with "[$]") as "[$ H]". iMod "HP".
    iIntros "!>" (e2 σ2 efs Hstep). iMod ("H" $! e2 σ2 efs with "[% //]") as "H".
    iIntros "!>!>". iMod "H". iMod "HP". iModIntro.
    revert n Hn. generalize (num_laters_per_step ns)=>n0 n Hn.
    iInduction n as [|n] "IH" forall (n0 Hn).
    - iApply (step_fupdN_wand with "H").
      iIntros ">[$ H]".
      iDestruct "H" as (a) "(pred & Hwp & H)". iFrame. iMod "HP".
      iModIntro. iExists _. iFrame. iIntros "H'". iDestruct ("Hwp" with "H'") as "Hwp".
      iApply (wp_strong_mono with "Hwp"); [done|set_solver|].
      iIntros (v) "HΦ". iFrame. iApply ("HΦ" with "HP").
    - destruct n0 as [|n0]; [lia|]=>/=. iMod "HP". iMod "H". iIntros "!> !>".
      iMod "HP". iMod "H". iModIntro. iApply ("IH" with "[] HP H").
      auto with lia.
  Qed.


  (** * Derived rules *)
  Lemma wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
  Proof.
    iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
    iIntros (v) "?". iFrame. by iApply HΦ.
  Qed.
  Lemma wp_stuck_mono s1 s2 E e Φ :
    s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
  Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
  Lemma wp_stuck_weaken s E e Φ :
    WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
  Proof. apply wp_stuck_mono. by destruct s. Qed.
  Lemma wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
  Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
  Global Instance wp_mono' s E e :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
  Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
  Global Instance wp_flip_mono' s E e :
    Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
  Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

  Lemma wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
  Proof. intros <-. by apply wp_value_fupd'. Qed.
  Lemma wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
  Proof. rewrite wp_value_fupd'. auto. Qed.
  Lemma wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
  Proof. intros <-. apply wp_value'. Qed.

  Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
  Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
  Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
  Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

  (** This lemma states that if we can prove that [n] laters are used in
      the current physical step, then one can perform an n-steps fancy
      update during that physical step. The resources needed to prove the
      bound on [n] are not used up: they can be reused in the proof of
      the WP or in the proof of the n-steps fancy update. In order to
      describe this unusual resource flow, we use ordinary conjunction as
      a premise. *)
  Lemma wp_step_fupdN n s E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    (∀ σ ns κs nt, state_interp σ ns κs nt
                   ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
      ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗
      WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
      WP e @ s; E1 {{ Φ }}.
  Proof.
    iIntros (??) "H". iApply (wp_step_fupdN_strong with "[H]"); [done|].
    iApply (and_mono_r with "H"). apply sep_mono_l. iIntros "HP".
    iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
    iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
    { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
    iModIntro. iApply (step_fupdN_wand with "HP"). iIntros "H".
    iApply fupd_mask_frame; [|iMod "H"; iModIntro]; [set_solver|].
    by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
  Qed.
  Lemma wp_step_fupd s E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
  Proof.
    iIntros (??) "HR H".
    iApply (wp_step_fupdN_strong 1 _ E1 E2 with "[-]"); [done|..]. iSplit.
    - iIntros (????) "_". iMod (fupd_mask_subseteq ∅) as "_"; [set_solver+|].
      auto with lia.
    - iFrame "H". iMod "HR" as "$". auto.
  Qed.

  Lemma wp_frame_step_l s E1 E2 e Φ R :
    TCEq (to_val e) None → E2 ⊆ E1 →
    (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
  Proof.
    iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
    iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
  Qed.
  Lemma wp_frame_step_r s E1 E2 e Φ R :
    TCEq (to_val e) None → E2 ⊆ E1 →
    WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
  Proof.
    rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
    apply wp_frame_step_l.
  Qed.
  Lemma wp_frame_step_l' s E e Φ R :
    TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
  Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed.
  Lemma wp_frame_step_r' s E e Φ R :
    TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
  Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed.

  Lemma wp_wand s E e Φ Ψ :
    WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
  Proof.
    iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
    iIntros (?) "?". by iApply "H".
  Qed.
  Lemma wp_wand_l s E e Φ Ψ :
    (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
  Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp"). done. Qed.
  Lemma wp_wand_r s E e Φ Ψ :
    WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
  Proof. iIntros "[Hwp H]". by iApply (wp_wand with "Hwp H"). Qed.
  Lemma wp_frame_wand s E e Φ R :
    R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
  Proof.
    iIntros "HR HWP". iApply (wp_wand with "HWP").
    iIntros (v) "HΦ". iFrame. by iApply "HΦ".
  Qed.

  (* Some lifting lemmas restated and reproved *)
  Local Hint Resolve reducible_no_obs_reducible : core.

  Lemma wp_lift_step_fupdN s E Φ e1 :
    to_val e1 = None →
    (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝
      ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
      state_interp σ2 (S ns) κs (length efs + nt) ∗ ∃ a, Pred a ∗
      (Pred a -∗ WP e2 @ s; E {{ Φ }}) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
      ⊢ WP e1 @ s; E {{ Φ }}.
  Proof. by rewrite wp_unfold /wp_pre=>->. Qed.

  Lemma wp_lift_step_fupd s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅}=∗ ▷ |={∅,E}=>
      state_interp σ2 (S ns) κs (length efs + nt) ∗ ∃ a, Pred a ∗
      (Pred a -∗ WP e2 @ s; E {{ Φ }}) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    intros ?. rewrite -wp_lift_step_fupdN; [|done]. simpl. do 22 f_equiv.
    rewrite -step_fupdN_intro; [|done]. rewrite -bi.laterN_intro. auto.
  Qed.

  Lemma wp_lift_stuck E Φ e :
    to_val e = None →
    (∀ σ ns κs nt, state_interp σ ns κs nt ={E,∅}=∗ ⌜stuck e σ⌝)
      ⊢ WP e @ E ?{{ Φ }}.
  Proof.
    rewrite wp_unfold /wp_pre=>->. iIntros "H" (σ1 ns κ κs nt) "Hσ".
    iMod ("H" with "Hσ") as %[? Hirr]. iModIntro. iSplit; first done.
    iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
  Qed.

  (** Derived lifting lemmas. *)
  Lemma wp_lift_step s E Φ e1 :
    to_val e1 = None →
    (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗ ∃ a, Pred a ∗
      (Pred a -∗ WP e2 @ s; E {{ Φ }}) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
      ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (?????) "Hσ".
    iMod ("H" with "Hσ") as "[$ H]". iIntros "!> * % !> !>". by iApply "H".
  Qed.

  Lemma wp_lift_pure_step_no_fork `{!Inhabited (state Λ)} s E E' Φ e1 a :
    (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
    (∀ κ σ1 e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
    (|={E}[E']▷=> ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ → (Pred a -∗ WP e2 @ s; E {{ Φ }}))
      ⊢ Pred a -∗ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (Hsafe Hstep) "H". iIntros "pred". iApply wp_lift_step.
    { specialize (Hsafe inhabitant). destruct s; eauto using reducible_not_val. }
    iIntros (σ1 ns κ κs nt) "Hσ". iMod "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
    { iPureIntro. destruct s; done. }
    iNext. iIntros (e2 σ2 efs ?).
    destruct (Hstep κ σ1 e2 σ2 efs) as (-> & <- & ->); auto.
    iMod (state_interp_mono with "Hσ") as "$".
    iMod "Hclose" as "_". iMod "H". iModIntro.
    iExists a. iDestruct ("H" with "[//]") as "$". iFrame. done.
  Qed.

  Lemma wp_lift_pure_stuck `{!Inhabited (state Λ)} E Φ e :
    (∀ σ, stuck e σ) →
    True ⊢ WP e @ E ?{{ Φ }}.
  Proof.
    iIntros (Hstuck) "_". iApply wp_lift_stuck.
    - destruct(to_val e) as [v|] eqn:He; last done.
      rewrite -He. by case: (Hstuck inhabitant).
    - iIntros (σ ns κs nt) "_". iApply fupd_mask_intro; auto with set_solver.
  Qed.

  (* Atomic steps don't need any mask-changing business here, one can
     use the generic lemmas here. *)
  Lemma wp_lift_atomic_step_fupd {s E1 E2 Φ} e1 a :
    to_val e1 = None →
    (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E1}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E1}[E2]▷=∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      from_option Φ False (to_val e2) ∗ Pred a ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
      ⊢ WP e1 @ s; E1 {{ v, Φ v ∗ Pred a }}.
  Proof.
    iIntros (?) "H".
    iApply (wp_lift_step_fupd s E1 _ e1)=>//; iIntros (σ1 ns κ κs nt) "Hσ1".
    iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose" (e2 σ2 efs ?). iMod "Hclose" as "_".
    iMod ("H" $! e2 σ2 efs with "[#]") as "H"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
    iMod "Hclose" as "_". iMod "H" as "($ & HQ & pred & $)".
    destruct (to_val e2) eqn:?; last by iExFalso.
    iApply fupd_mask_intro;[auto|].
    iIntros "Hcls". iExists a. iFrame.
    iIntros "Ha". iApply wp_value;[|iFrame]. by apply of_to_val.
  Qed.

  Lemma wp_lift_atomic_step {s E Φ} e1 a :
    to_val e1 = None →
    (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      from_option Φ False (to_val e2) ∗ Pred a ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
      ⊢ WP e1 @ s; E {{ v, Φ v ∗ Pred a }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
    iIntros (?????) "?". iMod ("H" with "[$]") as "[$ H]".
    iIntros "!> *". iIntros (Hstep) "!> !>".
    by iApply "H".
  Qed.

  Lemma wp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s E E' Φ} e1 e2 a :
    (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
    (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' →
                         κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
    (|={E}[E']▷=> Pred a -∗ WP e2 @ s; E {{ Φ }}) ⊢ Pred a -∗ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step_no_fork s E E'); try done.
    { naive_solver. }
    iApply (step_fupd_wand with "H"); iIntros "H".
    iIntros (κ e' efs' σ (_&?&->&?)%Hpuredet); auto.
  Qed.

  Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s E E' e1 e2 φ n Φ a :
    PureExec φ n e1 e2 →
    φ →
    (|={E}[E']▷=>^n Pred a -∗ WP e2 @ s; E {{ Φ }}) ⊢ Pred a -∗ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
    iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
    iApply wp_lift_pure_det_step_no_fork.
    - intros σ. specialize (Hsafe σ). destruct s; eauto using reducible_not_val.
    - done.
    - by iApply (step_fupd_wand with "Hwp").
  Qed.

  Lemma wp_pure_step_later `{!Inhabited (state Λ)} s E e1 e2 φ n Φ a :
    PureExec φ n e1 e2 →
    φ →
    ▷^n (Pred a -∗ WP e2 @ s; E {{ Φ }}) ⊢ Pred a -∗ WP e1 @ s; E {{ Φ }}.
  Proof.
    intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
    induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
  Qed.

  (* proofmode classes *)
  Global Instance frame_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p s E1 E2 e P Φ a :
    ElimModal (Atomic (stuckness_to_atomicity s) e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ v, Φ v ∗ Pred a }})%I (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v ∗ Pred a }})%I | 100.
  Proof.
    intros ?. rewrite intuitionistically_if_elim
                      fupd_frame_r wand_elim_r wp_atomic. auto.
  Qed.

  Global Instance add_modal_fupd_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e s Φ a :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s) e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ v, Φ v ∗ Pred a }})%I
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) ∗ Pred a }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[H [H' $]]". iApply "H'". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.


End wp.
