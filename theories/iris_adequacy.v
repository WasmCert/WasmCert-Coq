From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import wsat.
From iris.prelude Require Import options.
Import uPred.
Require Import iris_wp.

(** This file contains the adequacy statements of the Iris program logic. First
we prove a number of auxilary results. *)

Section adequacy.
Context `{Pred : A -> iProp Σ, !irisGS Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation wptp s t Φs := ([∗ list] e;Φ ∈ t;Φs, WP e @ s; ⊤ {{ Φ }})%I.

Instance wp_instance : Wp (iProp Σ) (expr Λ) (val Λ) stuckness.
  Proof using Pred irisGS0 Λ Σ. eapply wp'. Unshelve. - apply A. - apply Pred. Defined.

Lemma wp_step s e1 σ1 ns κ κs e2 σ2 efs nt Φ :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 ns (κ ++ κs) nt -∗ WP e1 @ s; ⊤ {{ Φ }}
    ={⊤,∅}=∗ |={∅}▷=>^(S $ num_laters_per_step ns) |={∅,⊤}=>
  state_interp σ2 (S ns) κs (nt + length efs) ∗ ∃ a, Pred a ∗
  (Pred a -∗ WP e2 @ s; ⊤ {{ Φ }}) ∗
  wptp s efs (replicate (length efs) fork_post).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (?) "Hσ H".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iMod ("H" $! σ1 ns with "Hσ") as "(_ & H)". iModIntro.
  iApply (step_fupdN_wand with "[H]"); first by iApply "H". iIntros ">[H H']".
  iDestruct "H'" as (a) "[H1 H2]".
  iModIntro. iApply bi.sep_exist_l. iExists _.
  rewrite Nat.add_comm big_sepL2_replicate_r;eauto. iFrame.
Qed.

Lemma wptp_step s es1 es2 κ κs σ1 ns σ2 Φs nt :
  step (es1,σ1) κ (es2, σ2) →
  state_interp σ1 ns (κ ++ κs) nt -∗ wptp s es1 Φs -∗
  ∃ nt', |={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step$ ns) |={∅,⊤}=>
         state_interp σ2 (S ns) κs (nt + nt') ∗
         wptp s es2 (Φs ++ replicate nt' fork_post).
Proof.
  iIntros (Hstep) "Hσ Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs t2' t3 Hstep]; simplify_eq/=.
  iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ->) "[? Ht]".
  iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs3 ->) "[Ht ?]".
  iExists _. iMod (wp_step with "Hσ Ht") as "H"; first done. iModIntro.
  iApply (step_fupdN_wand with "H"). iIntros ">[$ H]".
  iDestruct "H" as (a) "(H& He2 & Hefs)".
  rewrite -(assoc_L app) -app_comm_cons. iFrame.
  iApply "He2". done.
Qed.

(* The total number of laters used between the physical steps number
   [start] (included) to [start+ns] (excluded). *)
Local Fixpoint steps_sum (num_laters_per_step : nat → nat) (start ns : nat) : nat :=
  match ns with
  | O => 0
  | S ns =>
    S $ num_laters_per_step start + steps_sum num_laters_per_step (S start) ns
  end.

Lemma wptp_steps s n es1 es2 κs κs' σ1 ns σ2 Φs nt :
  nsteps n (es1, σ1) κs (es2, σ2) →
  state_interp σ1 ns (κs ++ κs') nt -∗ wptp s es1 Φs
  ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅,⊤}=> ∃ nt',
    state_interp σ2 (n + ns) κs' (nt + nt') ∗
    wptp s es2 (Φs ++ replicate nt' fork_post).
Proof.
  revert nt es1 es2 κs κs' σ1 ns σ2 Φs.
  induction n as [|n IH]=> nt es1 es2 κs κs' σ1 ns σ2 Φs /=.
  { inversion_clear 1; iIntros "? ?"; iExists 0=> /=.
    rewrite Nat.add_0_r right_id_L. iFrame. by iApply fupd_mask_subseteq. }
  iIntros (Hsteps) "Hσ He". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)) Nat_iter_add plus_n_Sm.
  iDestruct (wptp_step with "Hσ He") as (nt') ">H"; first eauto; simplify_eq.
  iModIntro. iApply step_fupdN_S_fupd. iApply (step_fupdN_wand with "H").
  iIntros ">(Hσ & He)". iMod (IH with "Hσ He") as "IH"; first done. iModIntro.
  iApply (step_fupdN_wand with "IH"). iIntros ">IH".
  iDestruct "IH" as (nt'') "[??]".
  rewrite -Nat.add_assoc -(assoc_L app) -replicate_plus. by eauto with iFrame.
Qed.

Lemma wp_not_stuck κs nt e σ ns Φ :
  state_interp σ ns κs nt -∗ WP e {{ Φ }} ={⊤}=∗ ⌜not_stuck e σ⌝.
Proof.
  rewrite wp_unfold /wp_pre /not_stuck. iIntros "Hσ H".
  destruct (to_val e) as [v|] eqn:?; first by eauto.
  iSpecialize ("H" $! σ ns [] κs with "Hσ"). rewrite sep_elim_l.
  iMod (fupd_plain_mask with "H") as %?; eauto.
Qed.

Lemma wptp_strong_adequacy Φs κs' s n es1 es2 κs σ1 ns σ2 nt:
  nsteps n (es1, σ1) κs (es2, σ2) →
  state_interp σ1 ns (κs ++ κs') nt -∗ wptp s es1 Φs
  ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅,⊤}=> ∃ nt',
    ⌜ ∀ e2, s = NotStuck → e2 ∈ es2 → not_stuck e2 σ2 ⌝ ∗
    state_interp σ2 (n + ns) κs' (nt + nt') ∗
    [∗ list] e;Φ ∈ es2;Φs ++ replicate nt' fork_post, from_option Φ True (to_val e).
Proof.
  iIntros (Hstep) "Hσ He". iMod (wptp_steps with "Hσ He") as "Hwp"; first done.
  iModIntro. iApply (step_fupdN_wand with "Hwp").
  iMod 1 as (nt') "(Hσ & Ht)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    ⌜ ∀ e2, s = NotStuck → e2 ∈ es2 → not_stuck e2 σ2 ⌝%I
    (state_interp σ2 (n + ns) κs' (nt + nt') ∗
     wptp s es2 (Φs ++ replicate nt' fork_post))%I
    with "[$Hσ $Ht]") as "(%&Hσ&Hwp)".
  { iIntros "(Hσ & Ht)" (e' -> He').
    move: He' => /(elem_of_list_split _ _)[?[?->]].
    iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ?) "[? Hwp]".
    iDestruct (big_sepL2_cons_inv_l with "Hwp") as (Φ Φs3 ->) "[Hwp ?]".
    iMod (wp_not_stuck with "Hσ Hwp") as "$"; auto. }
  iExists _. iSplitR; first done. iFrame "Hσ".
  iApply big_sepL2_fupd.
  iApply (big_sepL2_impl with "Hwp").
  iIntros "!#" (? e Φ ??) "Hwp".
  destruct (to_val e) as [v2|] eqn:He2'; last done.
  apply of_to_val in He2' as <-. simpl. iApply wp_value_fupd'. done.
Qed.
End adequacy.

(** Iris's generic adequacy result *)
Theorem wp_strong_adequacy {A : Type} Σ Λ `{!invGpreS Σ} {Pred : A -> iProp Σ} es σ1 n κs t2 σ2 φ
        (num_laters_per_step : nat → nat) :
  (∀ `{Hinv: !invGS Σ},
      ⊢ |={⊤}=> ∃
         (s: stuckness)
         (stateI : state Λ → nat → list (observation Λ) → nat → iProp Σ)
         (Φs : list (val Λ → iProp Σ))
         (fork_post : val Λ → iProp Σ)
         (* Note: existentially quantifying over Iris goal! [iExists _] should
         usually work. *)
         state_interp_mono,
       let _ : irisGS Λ Σ := IrisG _ _ Hinv stateI fork_post num_laters_per_step
                                  state_interp_mono
       in
       let _ : Wp (iPropI Σ) (expr Λ) (val Λ) stuckness := @wp _ _ _ _ (@wp' _ _ _ _ Pred) in
       stateI σ1 0 κs 0 ∗
       ([∗ list] e;Φ ∈ es;Φs, WP e @ s; ⊤ {{ Φ }}) ∗
       (∀ es' t2',
         (* es' is the final state of the initial threads, t2' the rest *)
         ⌜ t2 = es' ++ t2' ⌝ -∗
         (* es' corresponds to the initial threads *)
         ⌜ length es' = length es ⌝ -∗
         (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
         threads in [t2] are not stuck *)
         ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         stateI σ2 n [] (length t2') -∗
         (* If the initial threads are done, their post-condition [Φ] holds *)
         ([∗ list] e;Φ ∈ es';Φs, from_option Φ True (to_val e)) -∗
         (* For all forked-off threads that are done, their postcondition
            [fork_post] holds. *)
         ([∗ list] v ∈ omap to_val t2', fork_post v) -∗
         (* Under all these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_mask_subseteq] to introduce the fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝)) →
  nsteps n (es, σ1) κs (t2, σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp ?.
  apply (step_fupdN_soundness _ (steps_sum num_laters_per_step 0 n))=> Hinv.
  iMod Hwp as (s stateI Φ fork_post state_interp_mono) "(Hσ & Hwp & Hφ)".
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iMod (@wptp_strong_adequacy _ _ _ _
       (IrisG _ _ Hinv stateI fork_post num_laters_per_step state_interp_mono) _ []
    with "[Hσ] Hwp") as "H"; [done|by rewrite right_id_L|].
  iAssert (|={∅}▷=>^(steps_sum num_laters_per_step 0 n) |={∅}=> ⌜φ⌝)%I
    with "[-]" as "H"; last first.
  { destruct steps_sum; [done|]. by iApply step_fupdN_S_fupd. }
  iApply (step_fupdN_wand with "H").
  iMod 1 as (nt' ?) "(Hσ & Hval) /=".
  iDestruct (big_sepL2_app_inv_r with "Hval") as (es' t2' ->) "[Hes' Ht2']".
  iDestruct (big_sepL2_length with "Ht2'") as %Hlen2.
  rewrite replicate_length in Hlen2; subst.
  iDestruct (big_sepL2_length with "Hes'") as %Hlen3.
  rewrite -plus_n_O.
  iApply ("Hφ" with "[//] [%] [//] Hσ Hes'"); [congruence|].
  by rewrite big_sepL2_replicate_r // big_sepL_omap.
Qed.

(** Since the full adequacy statement is quite a mouthful, we prove some more
intuitive and simpler corollaries. These lemmas are morover stated in terms of
[rtc erased_step] so one does not have to provide the trace. *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → not_stuck e2 σ2
}.

Lemma adequate_alt {Λ} s e1 σ1 (φ : val Λ → state Λ → Prop) :
  adequate s e1 σ1 φ ↔ ∀ t2 σ2,
    rtc erased_step ([e1], σ1) (t2, σ2) →
      (∀ v2 t2', t2 = of_val v2 :: t2' → φ v2 σ2) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2).
Proof.
  split.
  - intros []; naive_solver.
  - constructor; naive_solver.
Qed.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, erased_step (t2, σ2) (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ efs), σ3, κ; econstructor; eauto.
Qed.

(** This simpler form of adequacy requires the [irisGS] instance that you use
everywhere to syntactically be of the form
{|
  iris_invGS := ...;
  state_interp σ _ κs _ := ...;
  fork_post v := ...;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _;
|}
In other words, the state interpretation must ignore [ns] and [nt], the number
of laters per step must be 0, and the proof of [state_interp_mono] must have
this specific proof term.
*)
Corollary wp_adequacy {A: Type} Σ Λ `{!invGpreS Σ} s e σ φ {Pred : A -> iProp Σ}:
  (∀ `{Hinv : !invGS Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisGS Λ Σ :=
           IrisG _ _ Hinv (λ σ _ κs _, stateI σ κs) fork_post (λ _, 0)
                 (λ _ _ _ _, fupd_intro _ _)
       in
       let _ : Wp (iPropI Σ) (expr Λ) (val Λ) stuckness := @wp _ _ _ _ (@wp' _ _ _ _ Pred) in
       stateI σ κs ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod Hwp as (stateI fork_post) "[Hσ Hwp]".
  iExists s, (λ σ _ κs _, stateI σ κs), [(λ v, ⌜φ v⌝%I)], fork_post, _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> ? ?) "_ H _".
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|done].
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[Hwp H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.

Corollary wp_invariance {A: Type} Σ Λ `{!invGpreS Σ} s e1 σ1 t2 σ2 φ {Pred : A -> iProp Σ} :
  (∀ `{Hinv : !invGS Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisGS Λ Σ := IrisG _ _ Hinv (λ σ _, stateI σ) fork_post
          (λ _, 0) (λ _ _ _ _, fupd_intro _ _) in
       let _ : Wp (iPropI Σ) (expr Λ) (val Λ) stuckness := @wp _ _ _ _ (@wp' _ _ _ _ Pred) in
       stateI σ1 κs 0 ∗ WP e1 @ s; ⊤ {{ _, True }} ∗
       (stateI σ2 [] (pred (length t2)) -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)) →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod (Hwp _ κs) as (stateI fork_post) "(Hσ & Hwp & Hφ)".
  iExists s, (λ σ _, stateI σ), [(λ _, True)%I], fork_post, _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> _ _) "Hσ H _ /=".
  iDestruct (big_sepL2_cons_inv_r with "H") as (? ? ->) "[_ H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_intro_discard; first set_solver.
Qed.









(*

From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.program_logic Require Import language.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import wsat.
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.
Require Export stdpp_aux iris iris_locations iris_atomicity iris_wp_def.
Require Export datatypes host operations properties opsem.

Import uPred.

Import DummyHosts.

(** This file contains the adequacy statements of the Iris program logic. First
we prove a number of auxilary results. *)

Close Scope byte_scope.

Section adequacy.
  
Let reduce := @reduce host_function host_instance.

Let reducible := @reducible wasm_lang.

Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

Implicit Types e : iris.expr.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ. (*
Implicit Types Φs : list (val → iProp Σ).
*)

(*
   t and Φs should be a list of expr and iProp each; for each pair in t and Φ,
   we have WP e {{ Φ }}.

   Why is this definition useful, though?
 *)
Notation wptp s t Φs := ([∗ list] e;Φ ∈ t;Φs, WP e @ s; ⊤ {{ Φ }})%I.
 

(* Given that (e1, σ1) -> (e2, σ2) with 'effects' efs, plus the state interp
   of σ1 and a WP spec of e1, we get after a number of steps(??) the state
   interp of σ2 and the corresponding WP for e2 (with the frame resource),
   and a final list of wps for the effects(??).
*)
Lemma wp_step s e1 σ1 ns κ κs e2 σ2 efs nt Φ :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 ns (κ ++ κs) nt -∗ WP e1 @ s; ⊤ {{ Φ }}
  ={⊤,∅}=∗ |={∅}▷=>^(S $ num_laters_per_step ns) |={∅,⊤}=>
  state_interp σ2 ns κs (nt + length efs) ∗
  ∃ f, ↪[frame] f ∗ (↪[frame] f -∗ WP e2 @ s; ⊤ {{ Φ }}) ∗
  wptp s efs (replicate (length efs) fork_post).
Proof.
  rewrite {1}wp_unfold /wasm_wp_pre. iIntros (?) "Hσ H".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iMod ("H" $! σ1 with "Hσ") as "(_ & H)".
  iMod ("H" $! e2 σ2 efs with "[//]") as "H".
  iApply (step_fupdN_wand with "[H]"); first by iApply "H". iIntros "!>H".
  iMod "H" as (f) "(?&?&?&?)".
  iModIntro.
  iFrame.
  iExists f.
  rewrite big_sepL2_replicate_r => //.
  by iFrame.
Qed.

(* Seems similar to above, but uses step instead of prim_step. *)
Lemma wptp_step s es1 es2 κ κs σ1 ns σ2 Φs nt :
  step (es1,σ1) κ (es2, σ2) →
  state_interp σ1 ns (κ ++ κs) nt -∗ wptp s es1 Φs -∗
  ∃ nt', |={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step$ ns) |={∅,⊤}=>
         state_interp σ2 (S ns) κs (nt + nt') ∗
         wptp s es2 (Φs ++ replicate nt' fork_post).
Proof.
  iIntros (Hstep) "Hσ Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs t2' t3 Hstep]; simplify_eq/=.
  iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ->) "[? Ht]".
  iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs3 ->) "[Ht ?]".
  iExists (length efs). iMod (wp_step with "Hσ Ht") as "H"; first by [].
  (* TODO: these are bad patterns -- they exist because our state_interp does
     not use the ns, nt or observations, so these variables cannot be
     instantiated automatically. *)
  instantiate (1 := 0).
  instantiate (1 := []).
  instantiate (1 := 0).
  iModIntro.
  iApply (step_fupdN_wand with "H").
  iIntros "H".
  iMod "H" as "($ & H)".
  iDestruct "H" as (f) "(Hframe & He2 & Hefs)".
  iModIntro.
  rewrite -(assoc_L app) -app_comm_cons. iFrame.
  (* TODO: We can actually prove a stronger result here. Check if this makes
     sense. *)
  by iApply "He2".
Qed.

(* The total number of laters used between the physical steps number
   [start] (included) to [start+ns] (excluded). *)
Local Fixpoint steps_sum (num_laters_per_step : nat → nat) (start ns : nat) : nat :=
  match ns with
  | O => 0
  | S ns =>
    S $ num_laters_per_step start + steps_sum num_laters_per_step (S start) ns
  end.

Definition nsteps := @iris.program_logic.language.nsteps wasm_lang.

Lemma wp_not_stuck κs ns nt e σ Φ :
  state_interp σ ns κs nt -∗ WP e {{ Φ }} ={⊤}=∗ ⌜language.not_stuck e σ⌝.
Proof.
  rewrite wp_unfold /wasm_wp_pre /not_stuck. iIntros "Hσ H".
  destruct (to_val e) as [v|] eqn:?; first by eauto.
  iSpecialize ("H" $! σ 0 [] κs 0 with "Hσ"). rewrite sep_elim_l.
  iMod (fupd_plain_mask with "H") as %?; eauto.
Qed.

Lemma wptp_steps s n es1 es2 κs κs' σ1 σ2 Φs ns nt :
  nsteps n (es1, σ1) κs (es2, σ2) →
  state_interp σ1 ns (κs ++ κs') nt -∗ wptp s es1 Φs
  ={⊤}[∅]▷=∗^n ∃ nt',
    state_interp σ2 (ns + n) κs' (nt + nt') ∗ wptp s es2 (Φs ++ replicate nt' fork_post).
Proof.
  revert nt es1 es2 κs κs' σ1 σ2 Φs.
  induction n as [|n IH]=> nt es1 es2 κs κs' σ1 σ2 Φs /=.
  { inversion_clear 1; iIntros "? ?"; iExists 0=> /=.
    rewrite right_id_L. by iFrame. }
  iIntros (Hsteps) "Hσ He". inversion_clear Hsteps as [|?? [t1' σ1']].
  iDestruct (wptp_step with "Hσ He") as (nt') ">H"; first eauto; simplify_eq.
  instantiate (1 := 0).
  instantiate (1 := []).
  instantiate (1 := 0).
  iMod "H". iIntros "!> !>". iMod "H".
  (* Why does iMod work here???? *)
  iMod "H" as "(Hσ & He)".
  iModIntro.
  iApply (step_fupdN_wand with "[Hσ He]"); first by iApply (IH with "Hσ He").
  instantiate (1 := 0).
  instantiate (1 := []).
  iDestruct 1 as (nt'') "[??]". rewrite -(assoc_L app) -replicate_plus.
  by eauto with iFrame.
Qed.

Lemma wptp_strong_adequacy Φs κs' s n es1 es2 κs σ1 ns σ2 nt:
  nsteps n (es1, σ1) κs (es2, σ2) →
  state_interp σ1 ns (κs ++ κs') nt -∗
  wptp s es1 Φs ={⊤}[∅]▷=∗^(S n) ∃ nt',
    ⌜ ∀ e2, s = NotStuck → e2 ∈ es2 → not_stuck e2 σ2 ⌝ ∗
    state_interp σ2 (n + ns) κs' (nt + nt') ∗
    [∗ list] e;Φ ∈ es2;Φs ++ replicate nt' fork_post, from_option Φ True (to_val e).
Proof.
  iIntros (Hstep) "Hσ He". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "Hσ He") as "Hwp"; first done.
  iApply (step_fupdN_wand with "Hwp").
  iDestruct 1 as (nt') "(Hσ & Ht)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    ⌜ ∀ e2, s = NotStuck → e2 ∈ es2 → not_stuck e2 σ2 ⌝%I
    (state_interp σ2 ns κs' (nt + nt') ∗ wptp s es2 (Φs ++ replicate nt' fork_post))%I
    with "[$Hσ $Ht]") as "(%&Hσ&Hwp)".
  { iIntros "(Hσ & Ht)" (e' -> He').
    move: He' => /(elem_of_list_split _ _)[?[?->]].
    iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ?) "[? Hwp]".
    iDestruct (big_sepL2_cons_inv_l with "Hwp") as (Φ Φs3 ->) "[Hwp ?]".
    iMod (wp_not_stuck with "Hσ Hwp") as "$"; auto. }
  iApply step_fupd_fupd. iApply step_fupd_intro; first done. iNext.
  iExists _. iSplitR; first done. iFrame "Hσ".
  iApply big_sepL2_fupd.
  iApply (big_sepL2_impl with "Hwp").
  iIntros "!#" (? e Φ ??) "Hwp".
  destruct (to_val e) as [v2|] eqn:He2'; last done.
  apply of_to_val in He2' as <-. simpl. iApply wp_value_fupd'. done.
Qed.

Lemma wp_singleton_strong_adequacy Φ κs' s n e1 e2 κs σ1 ns σ2 nt:
  nsteps n ([e1], σ1) κs ([e2], σ2) →
  state_interp σ1 ns (κs ++ κs') nt -∗
  WP e1 @ s; ⊤ {{ Φ }} ={⊤}[∅]▷=∗^(S n) ∃ nt',
    ⌜ s = NotStuck→ not_stuck e2 σ2 ⌝ ∗
    state_interp σ2 (n + ns) κs' (nt + nt') ∗
    from_option Φ True (to_val e2).
Proof.
Admitted.

(** Iris's generic adequacy result *)
Theorem wp_strong_adequacy Σ `{!invGpreS Σ}  (* `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ} *) e σ1 n κs e2 σ2 φ :
  (∀  `{Hinv: invGS Σ},
      ⊢ |={⊤}=> ∃
         (s: stuckness)
         (stateI : state → nat → list (observation ) → nat → iProp Σ)
         (Φ : (val → iProp Σ))
         (fork_post : val → iProp Σ)
         (* Note: existentially quantifying over Iris goal! [iExists _] should
         usually work. *)
         state_interp_mono,
       let _ : irisGS Σ := IrisG _ Hinv stateI fork_post num_laters_per_step
                                  state_interp_mono
       in
       stateI σ1 0 κs 0 ∗
       ([∗ list] e;Φ ∈ es;Φs, WP e @ s; ⊤ {{ Φ }}) ∗
       (∀ es' t2',
         (* es' is the final state of the initial threads, t2' the rest *)
         ⌜ t2 = es' ++ t2' ⌝ -∗
         (* es' corresponds to the initial threads *)
         ⌜ length es' = length es ⌝ -∗
         (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
       (* (WP e @ s; ⊤ {{ Φ }}) ∗ *)
        (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
         threads in [t2] are not stuck *)
         ((* ((⌜ s = NotStuck → not_stuck e2 σ2 ⌝) -∗ *)

         (* The state interpretation holds for [σ2] *)
         stateI σ2 n [] (length t2') -∗
         (* If the initial threads are done, their post-condition [Φ] holds *)
         from_option Φ True (to_val e) -∗
         (* Under all these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_mask_subseteq] to introduce the fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝)) →
  nsteps n ([e], σ1) [] ([e2], σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp ?.
  apply (step_fupdN_soundness _ (steps_sum num_laters_per_step 0 n))=> Hinv.
  iMod Hwp as (s stateI Φ fork_post state_interp_mono) "(Hσ & Hwp & Hφ)".
  eapply (step_fupdN_soundness _ (steps_sum num_laters_per_step 0 n))=> Hinv.
  (* eapply (step_fupdN_soundness' _ (S (S n)))=> Hinv. rewrite Nat_iter_S. *)
  iDestruct Hwp as "HH".
  Unshelve.


  iMod ""
  iMod Hwp as "HH" . "(Hσ & Hwp & Hφ)".
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iMod (@wptp_strong_adequacy _ []
    with "[Hσ] Hwp") as "H"; [done|by rewrite right_id_L|].
  iAssert (|={∅}▷=>^(steps_sum num_laters_per_step 0 n) |={∅}=> ⌜φ⌝)%I
    with "[-]" as "H"; last first.
  { destruct steps_sum;[done|]. by iApply step_fupdN_S_fupd. }
  iApply (step_fupdN_wand with "H").
  iMod 1 as (nt' ?) "(Hσ & Hval) /=".
  iDestruct (big_sepL2_app_inv_r with "Hval") as (es' t2' ->) "[Hes' Ht2']".
  iDestruct (big_sepL2_length with "Ht2'") as %Hlen2.
  rewrite replicate_length in Hlen2; subst.
  iDestruct (big_sepL2_length with "Hes'") as %Hlen3.
  rewrite -plus_n_O.
  iApply ("Hφ" with "[//] [%] [//] Hσ Hes'"); [congruence|].
  by rewrite big_sepL2_replicate_r // big_sepL_omap.
Qed.
(** Iris's generic adequacy result *)
(* Note that we're not parametric on language here -- we just use wasm_lang. *)
Theorem wp_strong_adequacy e1 σ1 n κs e2 σ2 φ (num_laters_per_step: nat -> nat) :
  (  ⊢ |={⊤}=> ∃
         (s: stuckness)
         (Φ : val → iProp Σ),
       state_interp σ1 0 κs 0 ∗
     (* Instead of thread pool es, we just have one main thread and need to have
        one single wp. *)
         WP e1 @ s; ⊤ {{ Φ }} ∗
   (*    ([∗ list] e;Φ ∈ es;Φs, WP e @ s; ⊤ {{ Φ }}) ∗ *)
       (
         (* es' is the final state of the initial threads, t2' the rest *)
       (*  ⌜ t2 = [e2]⌝ -∗*)
    (*     (* es' corresponds to the initial threads *)
         ⌜ length es' = length es ⌝ -∗*)
         (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
         threads in [t2] are not stuck *)
         ⌜ s = NotStuck → not_stuck e2 σ2 ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         state_interp σ2 n [] 0 -∗
         (* If the initial threads are done, their post-condition [Φ] holds *)
         (* TODO: add back a single WP for es'*)
         from_option Φ True (to_val e2) -∗
     (*    ([∗ list] e;Φ ∈ es';Φs, from_option Φ True (to_val e)) -∗ *)
         (* For all forked-off threads that are done, their postcondition
            [fork_post] holds. *)
     (*    ([∗ list] v ∈ omap to_val t2', fork_post v) -∗ *)
         (* Under all these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_mask_subseteq] to introduce the fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝)) →
  nsteps n ([e1], σ1) κs ([e2], σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp Hstep.
  apply (step_fupdN_soundness φ (steps_sum num_laters_per_step 0 n))=> Hinv.
  (*iMod Hwp as (s Φ) "(Hσ & Hwp & Hφ)".*)
  iDestruct Hwp as "Hwp".
  Search ElimModal.
  iApply fupd_mask_intro; first by set_solver.
  iIntros "Hmask". (*
  iDestruct (@wp_singleton_strong_adequacy _ (*(IrisG _ Hinv stateI fork_post num_laters_per_step state_interp_mono)*) _ _ with "[Hσ] Hwp") as "H" => //.
  { admit. }
  iSimpl.
  iMod "H".
  iMod (@wp_steps _
       (IrisG _ Hinv stateI fork_post num_laters_per_step state_interp_mono) _ []
    with "[Hσ] Hwp") as "H"; [done|by rewrite right_id_L|].*)
  iAssert (|={∅}▷=>^(steps_sum num_laters_per_step 0 n) |={∅}=> ⌜φ⌝)%I
    with "[-]" as "H"; last first.
  { destruct steps_sum; [done|]. by iApply step_fupdN_S_fupd. }
  iApply (step_fupdN_wand with "H").
  iMod 1 as (nt' ?) "(Hσ & Hval) /=".
  iDestruct (big_sepL2_app_inv_r with "Hval") as (es' t2' ->) "[Hes' Ht2']".
  iDestruct (big_sepL2_length with "Ht2'") as %Hlen2.
  rewrite replicate_length in Hlen2; subst.
  iDestruct (big_sepL2_length with "Hes'") as %Hlen3.
  rewrite -plus_n_O.
  iApply ("Hφ" with "[//] [%] [//] Hσ Hes'"); [congruence|].
  by rewrite big_sepL2_replicate_r // big_sepL_omap.

Qed.

(** Since the full adequacy statement is quite a mouthful, we prove some more
intuitive and simpler corollaries. These lemmas are morover stated in terms of
[rtc erased_step] so one does not have to provide the trace. *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → not_stuck e2 σ2
}.

Lemma adequate_alt {Λ} s e1 σ1 (φ : val Λ → state Λ → Prop) :
  adequate s e1 σ1 φ ↔ ∀ t2 σ2,
    rtc erased_step ([e1], σ1) (t2, σ2) →
      (∀ v2 t2', t2 = of_val v2 :: t2' → φ v2 σ2) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2).
Proof.
  split.
  - intros []; naive_solver.
  - constructor; naive_solver.
Qed.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, erased_step (t2, σ2) (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ efs), σ3, κ; econstructor; eauto.
Qed.

Corollary wp_adequacy Σ Λ `{!invPreG Σ} s e σ φ :
  (∀ `{Hinv : !invG Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ Hinv (λ σ κs _, stateI σ κs) fork_post in
       stateI σ κs ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod Hwp as (stateI fork_post) "[Hσ Hwp]".
  iExists s, (λ σ κs _, stateI σ κs), [(λ v, ⌜φ v⌝%I)], fork_post => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> ? ?) "_ H _".
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|done].
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[Hwp H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.

Corollary wp_invariance Σ Λ `{!invPreG Σ} s e1 σ1 t2 σ2 φ :
  (∀ `{Hinv : !invG Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ Hinv stateI fork_post in
       stateI σ1 κs 0 ∗ WP e1 @ s; ⊤ {{ _, True }} ∗
       (stateI σ2 [] (pred (length t2)) -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)) →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod (Hwp _ κs) as (stateI fork_post) "(Hσ & Hwp & Hφ)".
  iExists s, stateI, [(λ _, True)%I], fork_post => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> _ _) "Hσ H _ /=".
  iDestruct (big_sepL2_cons_inv_r with "H") as (? ? ->) "[_ H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_intro_discard; first set_solver.
Qed.


End adequacy.

Print irisG.



(* This is wptp_step but with the single step replaced by the nsteps predicate. *)
Lemma wptp_steps s n es1 es2 κs κs' σ1 ns σ2 Φs nt :
  nsteps n (es1, σ1) κs (es2, σ2) →
  state_interp σ1 ns (κs ++ κs') nt -∗ wptp s es1 Φs
  ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅,⊤}=> ∃ nt',
    state_interp σ2 (n + ns) κs' (nt + nt') ∗
    wptp s es2 (Φs ++ replicate nt' fork_post).
Proof.
  revert nt es1 es2 κs κs' σ1 ns σ2 Φs.
  induction n as [|n IH]=> nt es1 es2 κs κs' σ1 ns σ2 Φs /=.
  { inversion_clear 1; iIntros "? ?"; iExists 0=> /=.
    rewrite right_id_L. iFrame. by iApply fupd_mask_subseteq. }
  iIntros (Hsteps) "Hσ He". inversion_clear Hsteps as [|?? [t1' σ1']].
  iDestruct (wptp_step with "Hσ He") as (nt') ">H"; first eauto; simplify_eq.
  iModIntro. iApply step_fupdN_S_fupd. iApply (step_fupdN_wand with "H").
  iIntros "H".
  iIntros ">(Hσ & He)". iMod (IH with "Hσ He") as "IH"; first done. iModIntro.
  iApply (step_fupdN_wand with "IH"). iIntros ">IH".
  iDestruct "IH" as (nt'') "[??]".
  rewrite -Nat.add_assoc -(assoc_L app) -replicate_plus. by eauto with iFrame.
Qed.

Lemma wp_not_stuck κs nt e σ ns Φ :
  state_interp σ ns κs nt -∗ WP e {{ Φ }} ={⊤}=∗ ⌜not_stuck e σ⌝.
Proof.
  rewrite wp_unfold /wp_pre /not_stuck. iIntros "Hσ H".
  destruct (to_val e) as [v|] eqn:?; first by eauto.
  iSpecialize ("H" $! σ ns [] κs with "Hσ"). rewrite sep_elim_l.
  iMod (fupd_plain_mask with "H") as %?; eauto.
Qed.

Lemma wptp_strong_adequacy Φs κs' s n es1 es2 κs σ1 ns σ2 nt:
  nsteps n (es1, σ1) κs (es2, σ2) →
  state_interp σ1 ns (κs ++ κs') nt -∗ wptp s es1 Φs
  ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅,⊤}=> ∃ nt',
    ⌜ ∀ e2, s = NotStuck → e2 ∈ es2 → not_stuck e2 σ2 ⌝ ∗
    state_interp σ2 (n + ns) κs' (nt + nt') ∗
    [∗ list] e;Φ ∈ es2;Φs ++ replicate nt' fork_post, from_option Φ True (to_val e).
Proof.
  iIntros (Hstep) "Hσ He". iMod (wptp_steps with "Hσ He") as "Hwp"; first done.
  iModIntro. iApply (step_fupdN_wand with "Hwp").
  iMod 1 as (nt') "(Hσ & Ht)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    ⌜ ∀ e2, s = NotStuck → e2 ∈ es2 → not_stuck e2 σ2 ⌝%I
    (state_interp σ2 (n + ns) κs' (nt + nt') ∗
     wptp s es2 (Φs ++ replicate nt' fork_post))%I
    with "[$Hσ $Ht]") as "(%&Hσ&Hwp)".
  { iIntros "(Hσ & Ht)" (e' -> He').
    move: He' => /(elem_of_list_split _ _)[?[?->]].
    iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ?) "[? Hwp]".
    iDestruct (big_sepL2_cons_inv_l with "Hwp") as (Φ Φs3 ->) "[Hwp ?]".
    iMod (wp_not_stuck with "Hσ Hwp") as "$"; auto. }
  iExists _. iSplitR; first done. iFrame "Hσ".
  iApply big_sepL2_fupd.
  iApply (big_sepL2_impl with "Hwp").
  iIntros "!#" (? e Φ ??) "Hwp".
  destruct (to_val e) as [v2|] eqn:He2'; last done.
  apply of_to_val in He2' as <-. simpl. iApply wp_value_fupd'. done.
Qed.
End adequacy.

(** Iris's generic adequacy result *)
Theorem wp_strong_adequacy Σ Λ `{!invGpreS Σ} es σ1 n κs t2 σ2 φ
        (num_laters_per_step : nat → nat) :
  (∀ `{Hinv : !invGS Σ},
    ⊢ |={⊤}=> ∃
         (s: stuckness)
         (stateI : state Λ → nat → list (observation Λ) → nat → iProp Σ)
         (Φs : list (val Λ → iProp Σ))
         (fork_post : val Λ → iProp Σ)
         (* Note: existentially quantifying over Iris goal! [iExists _] should
         usually work. *)
         state_interp_mono,
       let _ : irisGS Λ Σ := IrisG _ _ Hinv stateI fork_post num_laters_per_step
                                  state_interp_mono
       in
       stateI σ1 0 κs 0 ∗
       ([∗ list] e;Φ ∈ es;Φs, WP e @ s; ⊤ {{ Φ }}) ∗
       (∀ es' t2',
         (* es' is the final state of the initial threads, t2' the rest *)
         ⌜ t2 = es' ++ t2' ⌝ -∗
         (* es' corresponds to the initial threads *)
         ⌜ length es' = length es ⌝ -∗
         (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
         threads in [t2] are not stuck *)
         ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         stateI σ2 n [] (length t2') -∗
         (* If the initial threads are done, their post-condition [Φ] holds *)
         ([∗ list] e;Φ ∈ es';Φs, from_option Φ True (to_val e)) -∗
         (* For all forked-off threads that are done, their postcondition
            [fork_post] holds. *)
         ([∗ list] v ∈ omap to_val t2', fork_post v) -∗
         (* Under all these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_mask_subseteq] to introduce the fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝)) →
  nsteps n (es, σ1) κs (t2, σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp ?.
  apply (step_fupdN_soundness _ (steps_sum num_laters_per_step 0 n))=> Hinv.
  iMod Hwp as (s stateI Φ fork_post state_interp_mono) "(Hσ & Hwp & Hφ)".
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iMod (@wptp_strong_adequacy _ _
       (IrisG _ _ Hinv stateI fork_post num_laters_per_step state_interp_mono) _ []
    with "[Hσ] Hwp") as "H"; [done|by rewrite right_id_L|].
  iAssert (|={∅}▷=>^(steps_sum num_laters_per_step 0 n) |={∅}=> ⌜φ⌝)%I
    with "[-]" as "H"; last first.
  { destruct steps_sum; [done|]. by iApply step_fupdN_S_fupd. }
  iApply (step_fupdN_wand with "H").
  iMod 1 as (nt' ?) "(Hσ & Hval) /=".
  iDestruct (big_sepL2_app_inv_r with "Hval") as (es' t2' ->) "[Hes' Ht2']".
  iDestruct (big_sepL2_length with "Ht2'") as %Hlen2.
  rewrite replicate_length in Hlen2; subst.
  iDestruct (big_sepL2_length with "Hes'") as %Hlen3.
  rewrite -plus_n_O.
  iApply ("Hφ" with "[//] [%] [//] Hσ Hes'"); [congruence|].
  by rewrite big_sepL2_replicate_r // big_sepL_omap.
Qed.

(** Since the full adequacy statement is quite a mouthful, we prove some more
intuitive and simpler corollaries. These lemmas are morover stated in terms of
[rtc erased_step] so one does not have to provide the trace. *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → not_stuck e2 σ2
}.

Lemma adequate_alt {Λ} s e1 σ1 (φ : val Λ → state Λ → Prop) :
  adequate s e1 σ1 φ ↔ ∀ t2 σ2,
    rtc erased_step ([e1], σ1) (t2, σ2) →
      (∀ v2 t2', t2 = of_val v2 :: t2' → φ v2 σ2) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2).
Proof.
  split.
  - intros []; naive_solver.
  - constructor; naive_solver.
Qed.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, erased_step (t2, σ2) (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ efs), σ3, κ; econstructor; eauto.
Qed.

(** This simpler form of adequacy requires the [irisGS] instance that you use
everywhere to syntactically be of the form
{|
  iris_invGS := ...;
  state_interp σ _ κs _ := ...;
  fork_post v := ...;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _;
|}
In other words, the state interpretation must ignore [ns] and [nt], the number
of laters per step must be 0, and the proof of [state_interp_mono] must have
this specific proof term.
*)
Corollary wp_adequacy Σ Λ `{!invGpreS Σ} s e σ φ :
  (∀ `{Hinv : !invGS Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisGS Λ Σ :=
           IrisG _ _ Hinv (λ σ _ κs _, stateI σ κs) fork_post (λ _, 0)
                 (λ _ _ _ _, fupd_intro _ _)
       in
       stateI σ κs ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod Hwp as (stateI fork_post) "[Hσ Hwp]".
  iExists s, (λ σ _ κs _, stateI σ κs), [(λ v, ⌜φ v⌝%I)], fork_post, _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> ? ?) "_ H _".
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|done].
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[Hwp H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.

Corollary wp_invariance Σ Λ `{!invGpreS Σ} s e1 σ1 t2 σ2 φ :
  (∀ `{Hinv : !invGS Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisGS Λ Σ := IrisG _ _ Hinv (λ σ _, stateI σ) fork_post
              (λ _, 0) (λ _ _ _ _, fupd_intro _ _) in
       stateI σ1 κs 0 ∗ WP e1 @ s; ⊤ {{ _, True }} ∗
       (stateI σ2 [] (pred (length t2)) -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)) →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod (Hwp _ κs) as (stateI fork_post) "(Hσ & Hwp & Hφ)".
  iExists s, (λ σ _, stateI σ), [(λ _, True)%I], fork_post, _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> _ _) "Hσ H _ /=".
  iDestruct (big_sepL2_cons_inv_r with "H") as (? ? ->) "[_ H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_intro_discard; first set_solver.
Qed.

*)

*)
*)
