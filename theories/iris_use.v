(** Example of Iris usage **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre lifting.
From iris.base_logic Require Export gen_heap proph_map.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export datatypes host operations properties opsem.
Require Import Coq.Program.Equality.


(* Refactoring discussion points:

  1. Ltac within sections cannot be used outside the section unless redefined..
     As a result tactics like only_one_reduction can't be effectively put aside;
     (* OK -- will be resolved once a determinacy lemma is proved *)

  2. Typeclass instances issue (interaction with Variables) for moving 
     examples to a separate file (or in general, out of the current section).
     (* OK -- refer to other projects to see how to put instances into context *)

 *)

(*
  Call stack discussion points:

  1. Is it really required to have an explicit call stack as a resource (which doesn't seem to be possible anyway since resources can only be determined by the state)?

  2. Mixture of frame and label contexts.
*)

Set Default Proof Using "Type". (* what is this? *)

Close Scope byte_scope.

Let expr := iris.expr.
Let val := iris.val.
Let to_val := iris.to_val.


Section Host.

Variable host_function : eqType.

Let host := host.host host_function.
Let function_closure := function_closure host_function.
Let store_record := store_record host_function.

Variable host_instance : host.

Let reduce := @reduce host_function host_instance.



Let wasm_mixin : LanguageMixin _ _ _ := wasm_mixin host_instance.

Canonical Structure wasm_lang := Language wasm_mixin.

Let reducible := @reducible wasm_lang.

Let prim_step := @iris.prim_step host_function host_instance.


(* TODO: change the fields to use actual sensible names *)
Class wfuncG Σ := WFuncG {
  func_invG : invG Σ;
  func_gen_hsG :> gen_heapG N function_closure Σ;
}.

Class wtabG Σ := WTabG {
  tab_invG : invG Σ;
  tab_gen_hsG :> gen_heapG (N*N) funcelem Σ;
}.

Class wmemG Σ := WMemG {
  mem_invG : invG Σ;
  mem_gen_hsG :> gen_heapG (N*N) byte Σ;
}.

Class wmemsizeG Σ := WMemsizeG {
  memsize_invG : invG Σ;
  memsize_gen_hsG :> gen_heapG N N Σ;
}.

Class wglobG Σ := WGlobG {
  glob_invG : invG Σ;
  glob_gen_hsG :> gen_heapG N global Σ;
}.
(*
Class wstackG Σ := WStackG {
  stack_invG : invG Σ;
  stack_gen_hsG :> gen_heapG unit (list frame) Σ;
}.
*)

Class wlocsG Σ := WLocsG {
  locs_invG : invG Σ;
  locs_gen_hsG :> gen_heapG N value Σ;
}.

Class winstG Σ := WInstG {
  inst_invG: invG Σ;
  inst_gen_hsG :> gen_heapG unit instance Σ;
}.
 

Notation "n ↦[wf]{ q } v" := (mapsto (L:=N) (V:=function_closure) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wf]{ q } v") : bi_scope.
Notation "n ↦[wf] v" := (mapsto (L:=N) (V:=function_closure) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wf] v") : bi_scope.
Notation "n ↦[wt]{ q } [ i ] v" := (mapsto (L:=N*N) (V:=funcelem) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wt]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wt][ i ] v" := (mapsto (L:=N*N) (V:=funcelem) (n, i) (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wt][ i ] v") : bi_scope.
Notation "n ↦[wm]{ q } [ i ] v" := (mapsto (L:=N*N) (V:=byte) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wm]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wm][ i ] v" := (mapsto (L:=N*N) (V:=byte) (n, i) (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wm][ i ] v") : bi_scope.
Notation "n ↦[wmlength] v" := (mapsto (L:=N) (V:=N) n (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wmlength] v") : bi_scope.
Notation "n ↦[wg]{ q } v" := (mapsto (L:=N) (V:=global) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wg]{ q } v") : bi_scope.
Notation "n ↦[wg] v" := (mapsto (L:=N) (V:=global) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wg] v") : bi_scope.
Notation "n ↦[wl]{ q } v" := (mapsto (L:=N) (V:=value) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wl]{ q } v") : bi_scope.
Notation "n ↦[wl] v" := (mapsto (L:=N) (V:=value) n (DfracOwn 1) v%V)
                           (at level 20, format "n ↦[wl] v") : bi_scope.
Notation " ↦[wi] v" := (mapsto (L:=unit) (V:=instance) tt (DfracOwn 1) v%V)
                         (at level 20, format " ↦[wi] v") : bi_scope.
 
Definition proph_id := positive. (* ??? *)


(*
(* Memory size predicate using Monotone? *)
Definition R : relation N := fun x y => (x<y)%N.

Class MemsizeG Σ := memsizeG {
    MemsizeIG_monauth :> inG Σ (authUR (monotoneUR R));
}.

Definition MemsizeΣ := #[GFunctor (authUR (monotoneUR R))].

Instance subG_MonRefIGΣ {Σ} : subG MemsizeΣ Σ → MemsizeG Σ.
Proof. solve_inG. Qed.

Context `{!MemsizeG Σ}.

Definition mem_size_exact (γ: gname) sz := (own γ (● (principal R sz)))%I.

(* This should not be necessary *)
Definition mem_size_at_least (γ: gname) sz := (own γ (◯ (principal R sz)))%I.

(* Have to convert to 1-indexed, since Iris ghost names only allow positive. *)
Definition gen_mem_size (l: list memory) :=
  ([∗ list] i ↦ m ∈ l, mem_size_exact (Pos.of_succ_nat i) (mem_size m))%I.


Print gen_heap_interp.
 *)

Instance eqdecision_frame: EqDecision frame.
Proof. decidable_equality. Qed.


(* TODO: Global Instance doesn't seem to actually make this global... *)
Global Instance heapG_irisG `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, wmemsizeG Σ, !wglobG Σ, (*wstackG Σ *) !wlocsG Σ, !winstG Σ} : irisG wasm_lang Σ := {
  iris_invG := func_invG; (* Check: do we actually need this? *)
  state_interp σ _ κs _ :=
    let: (_, s, locs, inst) := σ in
     ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
      (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
      (gen_heap_interp (gmap_of_list s.(s_globals)) ∗
      (gen_heap_interp (gmap_of_list locs)) ∗
      (gen_heap_interp (<[tt := inst]> ∅)) ∗
    (*  (gen_heap_interp (<[tt := [ {| f_locs := locs; f_inst := inst |}]]> ∅)) ∗*)
      (gen_heap_interp (gmap_of_list (fmap mem_length s.(s_mems))))
      )
    )%I;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
}.





(* Auxiliary lemmas *)


(* Warning: this axiom is not actually true -- Wasm does not have a deterministic
   opsem for mem_grow and host function calls; due to the interaction between r_label
   and rs_trap, traps also have non-det behaviours in terms of reduction paths.
   However, the rest of the opsem are indeed deterministic. Use with caution. *)
(* TODO: find a condition for es that guarantees deterministic reduction. *)
Local Axiom reduce_det: forall hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2,
  reduce hs f ws es hs1 f1 ws1 es1 ->
  reduce hs f ws es hs2 f2 ws2 es2 ->
  (hs1, f1, ws1, es1) = (hs2, f2, ws2, es2).



(* A Definition of a context dependent WP for WASM expressions *)

Definition wp_wasm `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, (*!wstackG Σ*)!wlocsG Σ, !winstG Σ}
          (s : stuckness) (E : coPset) (e : language.expr wasm_lang)
           (Φ : val -> iProp Σ) (i : nat) (lh : lholed) : iProp Σ := 
  ∀ LI, ⌜lfilled i lh e LI⌝ -∗ WP LI @ s; E {{ Φ }}.

Notation "'WP' e @ s ; E 'CTX' i ; lh {{ Φ } }" := (wp_wasm s E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh {{ Φ } }" := (wp_wasm NotStuck E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh ? {{ Φ } }" := (wp_wasm MaybeStuck E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e 'CTX' i ; lh {{ Φ } }" := (wp_wasm NotStuck ⊤ e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e 'CTX' i ; lh ? {{ Φ } }" := (wp_wasm MaybeStuck ⊤ e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ s ; E 'CTX_EMPTY' {{ Φ } }" := (wp_wasm s E e%E Φ 0 (LH_base [] []))
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.


Notation "'WP' e @ s ; E 'CTX' i ; lh {{ v , Q } }" := (wp_wasm s E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ s ; E 'CTX_EMPTY' {{ v , Q } }" := (wp_wasm s E e%E (λ v, Q) 0 (LH_base [] []))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'CTX_EMPTY'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh {{ v , Q } }" := (wp_wasm NotStuck E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @ '[' E  '/' ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm MaybeStuck E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' E  '/' ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'CTX' i ; lh {{ v , Q } }" := (wp_wasm NotStuck ⊤ e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm MaybeStuck ⊤ e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(*
Definition lstack : Type := list (nat * frame * nat * lholed).

Inductive lframe: lstack -> list administrative_instruction -> list administrative_instruction -> Prop :=
  LframeBase: forall es,
    lframe [] es es
| LframeRec: forall (n: nat) (f: frame) k lh ls es es' LI,
    lframe ls es es' ->
    lfilled k lh es' LI ->
    lframe ((n,f,k,lh)::ls) es [AI_local n f LI].
 *)

Definition wp_wasm_frame `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !winstG Σ, !wlocsG Σ}
          (s : stuckness) (E : coPset) (es : language.expr wasm_lang)
          (Φ : val -> iProp Σ) (n: nat) (f: frame) : iProp Σ :=
  WP [AI_local n f es] @ s; E {{ Φ }}.

Notation "'WP' e @ s ; E 'FRAME' n ; f {{ Φ } }" := (wp_wasm_frame s E e%E Φ n f)
  (at level 20, only parsing) : bi_scope.

Notation "'WP' e @ s ; E 'FRAME' n ; f {{ v , Q } }" := (wp_wasm_frame s E e%E (λ v, Q) n f)
  (at level 20, e, Q, n, f at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ; f ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* wp for instructions *)

Section lifting.
Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, (*!wstackG Σ*)!wlocsG Σ, !winstG Σ}.

(* Predicate for memory blocks *)

(* TODO: switch to monotone implementation of mem_size once we have that? *)
Definition mem_block (n: N) (m: memory) :=
  (([∗ list] i ↦ b ∈ (m.(mem_data).(ml_data)), n ↦[wm][ (N.of_nat i) ] b ) ∗
     n ↦[wmlength] mem_length m)%I.
(* mem_size_exact (N.succ_pos n) (mem_size m))%I*)

Notation "n ↦[wmblock] m" := (mem_block n m)
                           (at level 20, format "n ↦[wmblock] m"): bi_scope.

Definition mem_block_equiv (m1 m2: memory) :=
  m1.(mem_data).(ml_data) = m2.(mem_data).(ml_data).

Notation "m1 ≡ₘ m2" := (mem_block_equiv m1 m2)
                        (at level 70, format "m1 ≡ₘ m2").


(* empty lists, frame and context rules *)

Lemma wp_wasm_empty_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) e :
  ⊢ WP e @ s ; E {{ Φ }} ∗-∗ WP e @ s ; E CTX_EMPTY {{ Φ }}.
Proof.
  iSplit.
  { iIntros "HWP". iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill. subst. erewrite app_nil_l; erewrite app_nil_r. done. }
  { iIntros "HWP".
    iDestruct ("HWP" $! e with "[]") as "$".
    iPureIntro. cbn. rewrite app_nil_r eqseqE. apply eq_refl. }
Qed.

Lemma wp_nil (s : stuckness) (E : coPset) (Φ : iProp Σ) :
  Φ ⊢ WP [] @ s ; E CTX_EMPTY {{ fun v => Φ }}%I.
Proof.
  iIntros "H". iApply wp_wasm_empty_ctx.
  by rewrite wp_unfold /wp_pre.
Qed.

Lemma wp_seq_ctx (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed) :
  (WP es1 @ NotStuck; E {{ w, Ψ w }} ∗
  ∀ w, Ψ w -∗ WP (iris.of_val w ++ es2) @ s; E CTX i; lh {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E CTX i; lh {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ i lh).
{ iIntros "[Hes1 Hes2]".
  (* iDestruct (wp_wasm_empty_ctx with "Hes1") as "Hes1". *)
  iIntros (LI Hfilled).
  repeat rewrite wp_unfold /wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val LI) as [vs|] eqn:Hetov.
  { destruct vs.
    { pose proof (filled_is_val_imm _ _ _ _ _ Hetov Hfilled) as
        [vs [es' [-> [-> [Hconst1 Hconst2]]]]].
      apply const_list_is_val in Hconst1 as [v1 Hv1].
      apply const_list_is_val in Hconst2 as [v2 Hv2].
      edestruct fill_val as [vs12 [Hvs12 Heql]];eauto.
      assert (Hvs12':=Hvs12).
      apply to_val_cat in Hvs12' as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      iMod "Hes1".
      iSpecialize ("Hes2" with "Hes1").
      unfold iris.of_val.
      rewrite - fmap_app take_drop.
      rewrite of_val_imm.
      pose proof (lfilled_swap (iris.of_val (immV vs12)) Hfilled) as [LI' Hfilled'].
      iSpecialize ("Hes2" $! _ Hfilled').
      rewrite wp_unfold /wp_pre /=.
      assert (iris.to_val LI' = Some (immV l)) as ->;[|iFrame].
      apply lfilled_Ind_Equivalent in Hfilled'. inversion Hfilled';subst.
      apply to_val_cat_inv;auto. apply to_val_cat_inv;auto. apply iris.to_of_val.
    }
    { apply to_val_trap_is_singleton in Hetov. subst.
      apply lfilled_Ind_Equivalent in Hfilled.
      inversion Hfilled;subst.
      2: { exfalso. do 2 destruct vs =>//=. }
      apply app_eq_singleton in H as [[HH HH']|[HH HH']];subst.
      { exfalso. destruct es1,es2,es' =>//=. }
      apply app_eq_singleton in HH' as [[HH HH']|[HH HH']];subst.
      { apply app_eq_singleton in HH as [[-> ->]|[-> ->]].
        simpl.
        all:iMod "Hes1".
        all: iSpecialize ("Hes2" with "Hes1").
        all:rewrite /=.
        all: iDestruct (wp_wasm_empty_ctx with "Hes2") as "Hes2".
        all:by rewrite wp_unfold /wp_pre /=. }
      { destruct es1,es2 =>//=.
        iMod "Hes1".
        iSpecialize ("Hes2" with "Hes1").
        rewrite /=.
        iSpecialize ("Hes2" $! [AI_trap] with "[]").
        { iPureIntro. constructor. }
        by rewrite wp_unfold /wp_pre /=.  }
    }
  }
  {
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1".
    iSpecialize ("Hes2" with "Hes1").
    iSpecialize ("Hes2" $! _ Hfilled).
    rewrite wp_unfold /wp_pre /=.
    rewrite Hetov.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "Hσ").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "Hσ").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      apply append_reducible with (es2:=es2) in H1;auto.
      eapply lfilled_reducible. apply Hfilled. auto.
    - iIntros (e2 σ2 efs HStep').
      eapply lfilled_prim_step_split_reduce_r in HStep' as Heq;[|apply Hfilled|apply H1].
      destruct Heq as [e' [HStep'' Hlfilled']].
      apply prim_step_obs_efs_empty in HStep'' as Hemp. inversion Hemp;subst;clear Hemp.
      apply prim_step_obs_efs_empty in HStep' as Hemp. inversion Hemp;subst;clear Hemp.
      iSpecialize ("H2" $! e' σ2 [] HStep'').
      iMod "H2".
      repeat iModIntro.
      repeat iMod "H2".
      iModIntro.
      iDestruct "H2" as "(Hσ & Hes'' & Hefs)".
      iFrame.
      iDestruct ("IH" with "[$Hes'' $Hes2]") as "Hcont".
      iSplit;[|done]. iApply "Hcont". auto.
  } } }
Qed.

(*
value1
value2
value3
Trap
expr3
expr2
expr1

could reduce to either a Trap directly, or 
value1
Trap
expr1,

But ultimately they reduce to a single Trap.
*)

(*
Lemma wp_trap s E es Φ:
  WP @ s; E ([AI_trap] ++ es) {{ w, Φ w }} ⊢
  |={E}=> Φ trapV.
Proof.
  rewrite wp_unfold/ wp_pre.
Admitted.
 *)

(* behaviour of seq might be a bit unusual due to how reductions work. *)
(* Note that the sequence wp is also true without the premise that Ψ doesn't trap, but it is very tricky to prove that version. The following is the fault-avoiding version.*)
Lemma wp_seq (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
  (¬ Ψ trapV) ∗ 
  (WP es1 @ s; E {{ w, Ψ w }} ∗
  ∀ w, Ψ w -∗ WP (iris.of_val w ++ es2) @ s; E {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ).
  iIntros "(Hntrap & Hes1 & Hes2)".
  repeat rewrite wp_unfold /wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val (es1 ++ es2)) as [vs|] eqn:Hetov.
  {
    destruct vs.
    {
      apply to_val_cat in Hetov as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      iMod "Hes1".
      iSpecialize ("Hes2" with "Hes1").
      unfold iris.of_val.
      rewrite - fmap_app take_drop.
      rewrite of_val_imm.
      rewrite wp_unfold /wp_pre /=.
      rewrite of_val_imm iris.to_of_val.
      by iAssumption.
    }
    {
      apply to_val_trap_is_singleton in Hetov.
      apply app_eq_singleton in Hetov as [[-> ->]|[-> ->]].
      all:iMod "Hes1".
      all: iSpecialize ("Hes2" with "Hes1").
      all:rewrite /=.
      all:by rewrite wp_unfold /wp_pre /=. 
    }
  }
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1".
    iSpecialize ("Hes2" with "Hes1").
    rewrite wp_unfold /wp_pre /=.
    rewrite Hetov.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "Hσ").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "Hσ").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      by apply append_reducible.
    - iIntros (e2 σ2 efs HStep).
      assert (κ = [] /\ efs = []) as [-> ->]; first by apply prim_step_obs_efs_empty in HStep; inversion HStep.
      apply prim_step_split_reduce_r in HStep; last by [].
      destruct HStep as [[es'' [-> HStep]] | [n [m [lh [Hlf1 Hlf2]]]]].
      + iSpecialize ("H2" $! es'' σ2 [] HStep).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iModIntro.
        destruct σ2 as [[??] ?].
        iDestruct "H2" as "(Hσ & Hes'' & Hefs)".
        iFrame.
        iApply "IH".
        by iFrame.
      + move/lfilledP in Hlf1.
        inversion Hlf1; subst; clear Hlf1.
        assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
        { unfold iris.prim_step.
          destruct σ as [[[??]?]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          move => HContra; subst.
          by destruct n.
        }
        iSpecialize ("H2" $! [AI_trap] σ [] HStep2).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        destruct σ as [[??] ?].
        iDestruct "H2" as "(Hσ & Hes'' & Hefs)".
        replace [AI_trap] with (iris.of_val trapV) => //.
        rewrite wp_value_fupd'.
        iMod "Hes''".
        by iSpecialize ("Hntrap" with "Hes''").
  }
Qed.

(*
(* This requires inverting wp again........ It would be really amazing
   if we can actually prove this, since I can't find anywhere in Iris where
   this has been done. *)
Lemma wp_trap_lfilled (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (es : language.expr wasm_lang) (lh: lholed):
  lfilled 0 lh [AI_trap] es ->
  WP es @ s; E {{ v, Φ v }} ⊢
  |={E}=> Φ trapV.
Proof.
  move => Hlf.
  iIntros "H".
  repeat rewrite wp_unfold /wp_pre /=.
  move/lfilledP in Hlf.
  inversion Hlf; subst; clear Hlf.
  (* if both vs and es' are empty then we're good: wp_value is directly applicable. *)
  destruct (iris.to_val (vs ++ [AI_trap] ++ es')) as [v|] eqn:Hetov.
  {
    destruct v.
    (* actual value, which is impossible *)
    {
      apply to_val_cat in Hetov as [Hvs He].
      apply to_val_cat in He as [Het He'].
      simpl in Het.
      by inversion He'.
    }
    (* trapV *)
    {
      apply iris.of_to_val in Hetov.
      simpl in Hetov.
      destruct vs; by [destruct es' | destruct vs].
    }
  }
  rewrite Hetov.
  (* We now need to feed an explicit configuration and state to the premise. *)
Admitted.

Lemma wp_seq_trap (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
  (WP es1 @ s; E {{ w, ⌜ w = trapV ⌝ }} ∗
  WP ([AI_trap] ++ es2) @ s; E {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v }}.
Proof.
  iIntros "(Hes1 & Hes2)".
  repeat rewrite wp_unfold /wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val (es1 ++ es2)) as [vs|] eqn:Hetov.
  {
    destruct vs.
    {
      apply to_val_cat in Hetov as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      by iMod "Hes1" as "%Hes1".
    }
    {
      apply to_val_trap_is_singleton in Hetov.
      apply app_eq_singleton in Hetov as [[-> ->]|[-> ->]] => //.
      iMod "Hes1" => //.
      by iDestruct "Hes1" as "%Hes1".
    }
  }
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1" as "->".
    destruct es2 => //.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "Hσ").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "Hσ").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      by apply append_reducible.
    - iIntros (e2 σ2 efs HStep).
      apply prim_step_split_reduce_r_correct in HStep; last by [].
      destruct HStep as [[es'' [-> HStep]] | [n [m [Hlf [-> HStep]]]]].
      + iSpecialize ("H2" $! es'' σ2 efs HStep).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iModIntro.
        destruct σ2 as [[??] ?].
        iDestruct "H2" as "(Hσ & Hes'' & Hefs)".
        iFrame.
Admitted.
*)

(* The following operation mirrors the opsem of AI_trap *)
(* in which a trap value swallows all other stack values *)
Definition val_combine (v1 v2 : val) :=
  match v1 with
  | immV l => match v2 with
             | immV l' => immV (l ++ l')
             | trapV => trapV
             end
  | trapV => trapV
  end.

(* Knowing hypothesis "Hred : objs -> _" (with frames (locs, inst) and (locs', inst')),
   attempts to exfalso away most of the possible ways Hred could hold, leaving the user
   with only the one possible desired case. Tactic will also attempt to trivially solve
   this one case, but may give it to user if attempt fails. *)

(*
Ltac only_one_reduction Hred objs locs inst locs' inst' :=
  let a := fresh "a" in
  let aft := fresh "aft" in
  let bef := fresh "bef" in
  let e := fresh "e" in
  let e' := fresh "e'" in
  let es := fresh "es" in
  let es0 := fresh "es" in
  let es1 := fresh "es" in
  let es2 := fresh "es" in
  let f := fresh "f" in
  let f' := fresh "f" in
  let g := fresh "g" in
  let hs := fresh "hs" in
  let hs' := fresh "hs" in
  let H := fresh "H" in
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  let Hconst := fresh "Hconst" in
  let Heqes0 := fresh "Heqes" in
  let Heqes2 := fresh "Heqes" in
  let Heqg := fresh "Heqg" in
  let Ht1s := fresh "Ht1s" in
  let Ht2s := fresh "Ht2s" in
  let Hvs := fresh "Hvs" in
  let Hxl1 := fresh "Hxl1" in
  let IHreduce := fresh "IHreduce" in
  let k := fresh "k" in
  let l := fresh "l" in
  let l' := fresh "l" in
  let les := fresh "les" in
  let les' := fresh "les" in
  let lh := fresh "lh" in
  let m := fresh "m" in
  let n0 := fresh "n" in
  let n' := fresh "n" in
  let s := fresh "s" in
  let t1s := fresh "t1s" in
  let t2s := fresh "t2s" in
  let vs := fresh "vs" in
  remember objs as es0 eqn:Heqes0 ;
  remember {| f_locs := locs ; f_inst := inst |} as f eqn:Heqf ;
  remember {| f_locs := locs' ; f_inst := inst' |} as f' eqn:Heqf' ;
  apply Logic.eq_sym in Heqes0 ;
  induction Hred as [e e' s ? hs H | | | | | a | a | a | | | | | | | | | | | | | | | |
                      s ? es les s' f' es' les' k lh hs hs' Hred IHreduce H0 H1 | ];
  (* induction on the reduction. Most cases will be trivially solved by the following
     two attemps : *)
  (try by inversion Heqes0) ;
  (try by found_intruse (AI_invoke a) Heqes0 Hxl1) ;
  (* reduce_simple case : *)
  first (destruct H as [ | | | | | | | | | | | | | | 
                    vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                    vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                  | | | | | | | | | | | | | 
                         es' lh Htrap' H0 ]  ;
         (* by case_analysis on the reduce_simple. most cases solved by just the 
            following inversion ; some cases need a little extra help *)
         inversion Heqes0 as [[ Hhd ]] ; subst ;
         (try by found_intruse (AI_basic (BI_block (Tf t1s t2s) es)) Hhd Hxl1) ;
         (try by found_intruse (AI_basic (BI_loop (Tf t1s t2s) es)) Hhd Hxl1) ;
         (try by filled_trap H0 Hxl1) ) ;
  (* lfilled case *)
  last (rewrite <- Heqes0 in H0 ;
        (* the simple_filled tactic unfolds lfilled, solves the case where k>0,
           and in the case k=0 leaves user with hypothesis H0 modified to now be
           les = bef ++ es ++ aft *)
        simple_filled2 H0 k lh bef aft n0 l l' ;
        first
          ( apply Logic.eq_sym in H0 ;
            remember ([] : seq.seq administrative_instruction) as g eqn:Heqg in s;
            let rec auxb H0 :=
              (* We maintain as an invariant that when auxb H0 is called,
                 H0 is the hypothesis "H0 : bef ++ es ++ aft = [some explicit sequence]" *)
              ( let b0 := fresh "b" in
                let Hb0 := fresh "Hb" in
                let H2 := fresh "H" in
                destruct bef as [| b0 bef ] ;
                [ (* case bef = []. Our invariant gives us that
                     "H0 : es ++ aft = [some explicit sequence]".
                     Recall g was defined as [] with "Heqg : g = []". *)
                  let rec auxe H0 g Heqg :=
                    (* We maintain as an invariant than when auxe H0 g Heqg is called,
                       H0 is the hypothesis "H0 : es ++ aft = [some explicit sequence]",
                       Hred is the hypothesis "Hred : (g ++ es) -> es'",
                       and Heqg is "Heqg : g = [some (other) explicit sequence]" *)
                    ( let e0 := fresh "e" in
                      let g' := fresh "g" in
                      let He0 := fresh "He" in
                      let Heqg' := fresh "Heqg" in
                      let H2 := fresh "H" in
                      destruct es as [| e0 es] ;
                      [ (* case es = []. Our invariants give us that
                           "Hred : g -> es' " with g described explicitly in Heqg.
                           Thus to conclude, we can … *)
                        rewrite <- Heqg in Hred ;
                        remember g as es2 eqn:Heqes2 in Hred ;
                        apply Logic.eq_sym in Heqes2 ;
                        rewrite Heqg in Heqes2 ;
                        (* use our induction hypothesis 
                           (case where bef = aft = []), or …  *)
                        (( by simpl in H0 ; rewrite H0 in H1 ;
                           unfold lfilled, lfill in H1 ;
                           destruct (const_list []) ; [| false_assumption] ;
                           apply b2p in H1 ; rewrite H1 ; rewrite app_nil_r ;
                           apply IHreduce ; subst ; trivial) +
                           (* use no_reduce (case where bef or aft is nonempty, and thus
                              g is shorter than the original objs). Strict subsequences
                              of valid reduction sequences tend to not reduce, so this
                              will work most of the time *)
                           (exfalso ; no_reduce Heqes2 Hred) )
                      | (* case es = e0 :: es. Our invariant gives us that
                           "H0 : e0 :: es ++ aft = [some explicit sequence]". We can
                           try to conclude by inverting H0, in case the explicit sentence is
                           empty *)
                        (by inversion H0) +
                          (* else, we know the explicit sentence is nonempty. 
                             Now by inverting H0 we get 
                             "H2 : es ++ aft = [some shorter explicit sequence]"
                             The invariant also gives us
                             "Hred : (g ++ e0 :: es) -> es'", so to maintain the invariant  
                             we define g' to be g ++ [e0] and create an equation Heqg' that
                             describes g' explicitly *)
                          ( inversion H0 as [[ He0 H2 ]] ;
                            rewrite He0 in Hred ;
                            remember (g ++ [e0]) as g' eqn:Heqg' ;
                            rewrite Heqg in Heqg' ;
                            rewrite He0 in Heqg' ;
                            simpl in Heqg' ;
                            (* we can now make a recursive call to auxe. The length of the
                               explicit list in H2 has strictly decreased *)
                            auxe H2 g' Heqg'
                          )
                      ]
                    ) in auxe H0 g Heqg
                | (* case bef = b0 :: bef. Our invariant gives us that
                     "H0 : b0 :: bef ++ es ++ aft = [some explicit sequence]".
                     We can attempt to conclude by inverting H0, which will work if
                     the explicit sequence is empty *)
                  (by inversion H0 ) +
                    (* else, we know the explicit sequence is nonempty, so by inverting
                       H0, we get "H2 : bef ++ es ++ aft = [some explicit sequence]" *)
                    ( inversion H0 as [[ Hb0 H2 ]] ;
                      auxb H2 )
                ]
              ) in auxb H0
          )
       ) ;        
  (* at this point, only one case should be remaining.
     we attempt to solve this case too trivially, as the following line is often
     what user would be going to do next anyway *)
  try by inversion Heqes0 ; subst ; inversion Heqf' ; subst ; iFrame.
*)

(* An attempt at making reduce_det a proved lemma. Work in progress

Lemma reduce_det: forall hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2,
  reduce hs f ws es hs1 f1 ws1 es1 ->
  reduce hs f ws es hs2 f2 ws2 es2 ->
  ( In (AI_basic BI_grow_memory) es -> False ) ->
  ( forall a, In (AI_invoke a) es -> False) -> 
  (hs1, f1, ws1, es1) = (hs2, f2, ws2, es2).
Proof.
  intros hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2 Hred1 Hred2 Hgrow_memory Hinvoke.
  destruct es as [ | e0 es ].
  { empty_list_no_reduce Hred1. }
  destruct es as [ | e1 es ].
  { remember [e0] as es.
    apply Logic.eq_sym in Heqes.
    destruct e0.
    destruct b ; try by exfalso ; no_reduce Heqes Hred1. *)

Lemma wp_val (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v0 : value) (es : language.expr wasm_lang) :
  (* Like for wp_seq, this lemma is true without the trap condition, but would
     be problematic to prove without it. *)
  ((¬ Φ trapV) ∗
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV [v0]) v))  }}
  ⊢ WP ((AI_basic (BI_const v0)) :: es) @ s ; E {{ v, Φ v }})%I.
Proof.
  (* This also needs an iLob. *)
  iLöb as "IH" forall (v0 es Φ).
  iIntros "(Hntrap & H)".
  repeat rewrite wp_unfold /wp_pre /=.
  destruct (iris.to_val es) as [vs|] eqn:Hes.
  {
    destruct vs.
    { by apply of_to_val in Hes as <-.
      }
    { apply to_val_trap_is_singleton in Hes as ->.
      iIntros (σ ns κ κs nt) "Hσ".
      iMod "H".
      destruct σ as [[[hs ws] locs] inst].
      iApply fupd_frame_l. iSplit.
      { destruct s;auto. iPureIntro.
        unfold language.reducible.
        pose proof (AI_trap_reducible_2 _ host_instance [AI_basic (BI_const v0)]) as H.
        apply H;auto. }
      iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hmask".
      iIntros (es2 σ2 efs HStep).
      rewrite -cat1s in HStep.
      assert ((κ, efs) = ([],[])) as Hobsefs; first by eapply prim_step_obs_efs_empty.
      inversion Hobsefs; subst; clear Hobsefs.
      destruct σ2 as [[[hs2 ws2] locs2] inst2].
      iModIntro. iNext. iMod "Hmask".
      iApply fupd_mask_intro_subseteq. solve_ndisj.
      unfold iris.prim_step in *.
      assert (iris.prim_step (host_instance:=host_instance)
                             ([AI_basic (BI_const v0)] ++ [AI_trap])%SEQ 
                             (hs, ws, locs, inst) [] [AI_trap] (hs, ws, locs, inst) []) as Hstep.
      { repeat constructor. econstructor;auto.
        instantiate (1:=LH_base [AI_basic (BI_const v0)] []).
        rewrite /lfilled /lfill => //=. }
      destruct HStep as [HStep _].
      destruct Hstep as [Hstep _].
      apply AI_trap_reduce_det in HStep => //.
      inversion HStep; subst; clear HStep.
      iFrame.
      iSplit => //.
      iApply wp_value => //.
      by rewrite/IntoVal.
    }
  }
  {
    iIntros (σ ns κ κs nt) "Hσ".
    iSpecialize ("H" $! σ ns κ κs nt with "Hσ").
    iMod "H".
    iModIntro.
    iDestruct "H" as "(%H1 & H)".
    iSplit.
    - iPureIntro.
      destruct s => //=.
      rewrite - cat1s.
      by eapply prepend_reducible; eauto.
    - iIntros (es2 σ2 efs HStep).
      rewrite -cat1s in HStep.
      eapply reduce_ves in H1; last by apply HStep.
      assert (κ = [] /\ efs = []) as [-> ->]; first by apply prim_step_obs_efs_empty in HStep; inversion HStep.
      destruct H1 as [[-> HStep2] | [lh1 [lh2 [Hlf1 [Hlf2 ->]]]]].
      + iSpecialize ("H" $! (drop 1 es2) σ2 [] HStep2).
        iMod "H".
        repeat iModIntro.
        repeat iMod "H".
        iModIntro.
        iDestruct "H" as "(Hσ & Hes & Hefs)".
        iSimpl.
        iFrame.
        iSplit => //.
        iApply "IH".
        by iFrame.
      + move/lfilledP in Hlf1.
        inversion Hlf1; subst; clear Hlf1.
        move/lfilledP in Hlf2.
        inversion Hlf2; subst; clear Hlf2.
        assert (iris.prim_step (vs0 ++ [AI_trap] ++ es'0) σ2 [] [AI_trap] σ2 []) as HStep2.
        { unfold iris.prim_step.
          destruct σ2 as [[[??]?]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          - move => HContra.
            by replace (vs0 ++ [AI_trap] ++ es'0)%SEQ with [AI_trap] in Hes.
          - apply/lfilledP.
            by apply LfilledBase.
        }
        iSpecialize ("H" $! [AI_trap] σ2 [] HStep2).
        iMod "H".
        repeat iModIntro.
        repeat iMod "H".
        iDestruct "H" as "(Hσ & Hes & Hefs)".
        rewrite wp_unfold /wp_pre /=.
        iMod "Hes".
        by iSpecialize ("Hntrap" with "Hes").
  }
Qed.
  
Lemma wp_val_app' (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs (es : language.expr wasm_lang) :
  (* □ is required here -- this knowledge needs to be persistent instead of 
     one-off. *)
  (□ (¬ Φ trapV )) ∗
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV vs) v)) }}%I
  ⊢ WP ((v_to_e_list vs) ++ es) @ s ; E {{ v, Φ v }}%I.

Proof.
  iInduction vs as [|c vs] "IH" forall (Φ s E es).
  { simpl.
    iIntros "(#Hntrap & HWP)".
    destruct s.
    2: iApply wp_stuck_weaken.
    all: iApply (wp_wand with "HWP").
    all: iIntros (v).
    all: destruct v => /=.
    all: iIntros "HΦ" => //.
  }
  { iIntros "(#Hntrap & HWP)".
    iSimpl.
    iApply wp_val.
    iSplitR => //.
    iApply "IH" => //=.
    iSplit => //.
    iApply (wp_mono with "HWP").
    iIntros (vs') "HΦ".
    iSimpl. destruct vs';auto.
  }
Qed.
  
Lemma wp_val_app (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs v' (es : language.expr wasm_lang) :
  iris.to_val vs = Some (immV v') ->
  (□ (¬ Φ trapV )) ∗
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV v') v)) }}%I
  ⊢ WP (vs ++ es) @ s ; E {{ v, Φ v }}%I.
Proof.
  iIntros "%Hves [#Hntrap Hwp]".
  apply iris.of_to_val in Hves; subst.
  iApply wp_val_app'.
  by iFrame.
Qed.
                                  
(* basic instructions with simple(pure) reductions *)

(* numerics *)

Axiom only_one_reduction_placeholder: False.

(* placeholder until the actual tactic is sorted *)
Ltac only_one_reduction H es locs inst locs' inst':=
  exfalso; by apply only_one_reduction_placeholder.
  

Lemma wp_unop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v v' : value) (t: value_type) (op: unop):
  app_unop op v = v' ->
  Φ (immV [v']) ⊢
  WP [AI_basic (BI_const v); AI_basic (BI_unop t op)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Hunop) "HΦ".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[[ hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. apply r_simple. rewrite <- Hunop. apply rs_unop.
  - destruct σ as [[[hs ws] locs] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'].
    destruct HStep as (H & -> & ->).    
    only_one_reduction H [AI_basic (BI_const v) ; AI_basic (BI_unop t op)]
                       locs inst locs' inst'.       
Qed.

  
Lemma wp_binop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v1 v2 v : value) (t: value_type) (op: binop):
  app_binop op v1 v2 = Some v ->
  Φ (immV [v]) ⊢
  WP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Hbinop) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v)], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_binop_success.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                          AI_basic (BI_binop t op)] locs inst locs' inst'.
  (*  inversion Heqf' ; subst. rewrite Hbinop in H. inversion H; subst. by iFrame.
    rewrite Hbinop in H ; inversion H.*)
Qed.

(* There is a problem with this case: AI_trap is not a value in our language.
   This can of course be circumvented if we only consider 'successful reductions',
   but otherwise this needs some special treatment. *)

(* 20210929: with [::AI_trap] potentially becoming a value, this might get proved at some point *)
Lemma wp_binop_failure (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v1 v2 : value) (t: value_type) (op: binop):
  Φ trapV ∗
  ⌜app_binop op v1 v2 = None⌝ ⊢
  WP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros "(HΦ & %Hbinop)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_trap], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_binop_failure.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last by apply r_simple, rs_binop_failure.
    inversion H; subst; clear H.
    iFrame.
    iSimpl => //.
Qed.
    
Lemma wp_relop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v1 v2 : value) (b: bool) (t: value_type) (op: relop):
  app_relop op v1 v2 = b ->
  Φ (immV [(VAL_int32 (wasm_bool b))]) ⊢
  WP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Hrelop) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (wasm_bool b)))], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_relop.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                          AI_basic (BI_relop t op)] locs inst locs' inst'. 
Qed.

Lemma wp_testop_i32 (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v : i32) (b: bool) (t: value_type) (op: testop):
  app_testop_i (e:=i32t) op v = b ->
  Φ (immV [(VAL_int32 (wasm_bool b))]) ⊢
    WP [AI_basic (BI_const (VAL_int32 v)); AI_basic (BI_testop T_i32 op)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Htestop) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (wasm_bool b)))], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_testop_i32.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_basic (BI_const (VAL_int32 v));
                          AI_basic (BI_testop T_i32 op) ]
                       locs inst locs' inst'.
Qed.

Lemma wp_testop_i64 (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v : i64) (b: bool) (t: value_type) (op: testop):
  app_testop_i (e:=i64t) op v = b ->
  Φ (immV [(VAL_int32 (wasm_bool b))]) ⊢
    WP [AI_basic (BI_const (VAL_int64 v)); AI_basic (BI_testop T_i64 op)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Htestop) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (wasm_bool b)))], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_testop_i64.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_basic (BI_const (VAL_int64 v)) ;
                          AI_basic (BI_testop T_i64 op)]
                       locs inst locs' inst'.
Qed.

Lemma wp_cvtop_convert (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v v': value) (t1 t2: value_type) (sx: option sx):
  cvt t2 sx v = Some v' ->
  types_agree t1 v ->
  Φ (immV [v']) ⊢
    WP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Hcvtop Htype) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_convert_success.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_basic (BI_const v) ; AI_basic (BI_cvtop t2 CVO_convert t1 sx)]
                       locs inst locs' inst'.
    (*rewrite Hcvtop in H0. inversion H0 ; inversion Heqf' ; subst ; iFrame ;done.
    rewrite Hcvtop in H0 ; inversion H0.*)
Qed.

Lemma wp_cvtop_reinterpret (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v v': value) (t1 t2: value_type):
  wasm_deserialise (bits v) t2 = v' ->
  types_agree t1 v ->
  Φ (immV [v']) ⊢
    WP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Hcvtop Htype) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_reinterpret.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_basic (BI_const v) ;
                          AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)]
                       locs inst locs' inst'.
Qed.

(* Non-numerics -- stack operations, control flows *)

Lemma wp_nop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ):
  Φ (immV []) ⊢
    WP [AI_basic (BI_nop)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_nop.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_basic (BI_nop)] locs inst locs' inst'.
Qed.




Lemma wp_drop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) v :
  Φ (immV []) ⊢ WP [AI_basic (BI_const v) ; AI_basic BI_drop] @ s; E {{ w, Φ w }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [], σ, [].
    destruct σ as [[[ hs ws ] locs ] inst ].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple ; apply rs_drop.
  - destruct σ as [[[ hs ws ] locs ] inst ].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[ hs' ws' ] locs' ] inst'].
    destruct HStep as (H & -> & ->).
    only_one_reduction H [AI_basic (BI_const v); AI_basic BI_drop] locs inst locs' inst'. 
Qed.

Lemma wp_select_false (s: stuckness) (E :coPset) (Φ : val -> iProp Σ) n v1 v2 :
  n = Wasm_int.int_zero i32m ->
  Φ (immV [v2]) ⊢ WP [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                      AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_select) ] @ s;
E {{ w, Φ w }}.
Proof.
  iIntros (Hn) "HΦ".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v2)], σ, [].
    destruct σ as [[[ hs ws ] locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply r_simple ; by apply rs_select_false.
  - destruct σ as [[[ hs ws ] locs ] inst ].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[ hs' ws' ] locs' ] inst'].
    destruct HStep as (H & -> & ->).
    only_one_reduction H [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                          AI_basic (BI_const (VAL_int32 n)) ; AI_basic BI_select]
                       locs inst locs' inst'.
Qed.

Lemma wp_select_true (s: stuckness) (E : coPset) (Φ: val -> iProp Σ) n v1 v2 :
  n <> Wasm_int.int_zero i32m ->
  Φ (immV [v1]) ⊢ WP [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                      AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_select) ] @ s;
E {{ w, Φ w }}.
Proof.
  iIntros (Hn) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v1)], σ, [].
    destruct σ as [[[ hs ws ] locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply r_simple ; by apply rs_select_true.
  - destruct σ as [[[ hs ws ] locs ] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[ hs' ws' ] locs' ] inst'].
    destruct HStep as (H & -> & ->).
    only_one_reduction H [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                          AI_basic (BI_const (VAL_int32 n)) ; AI_basic BI_select]
                       locs inst locs' inst'.
Qed.
    
(* Control flows *)

            
               

Fixpoint labels e :=
  match e with
  | AI_label _ _ LI => S (list_sum (map labels LI))
  | _ => 0
  end .
Definition amount_of_labels es := list_sum (map labels es).

Lemma amount_of_labels_app l1 l2 :
  amount_of_labels (app l1 l2) = amount_of_labels l1 + amount_of_labels l2.
Proof.
  unfold amount_of_labels. rewrite map_app. rewrite list_sum_app. done.  
Qed. 
  
(*
Fixpoint depth e :=
  match e with
  | AI_label _ _ LI => fold_left (fun d e => max d (depth e)) LI 0
  | _ => 0
  end .

Definition maximum_depth es := fold_left (fun d e => max d (depth e)) es 0. 
*)
(*
Fixpoint flatten_labels es :=
  match es with
  | [] => []
  | AI_label n es LI :: q => flatten_labels LI ++ flatten_labels q
  | t :: q => t :: flatten_labels q
  end .

Inductive amount_of_labels : (seq.seq administrative_instruction) -> nat -> Prop :=
| NilLabels : amount_of_labels [] 0
| LabelLabels : forall n es LI q kLI kq,
    amount_of_labels LI kLI ->
    amount_of_labels q kq ->
    amount_of_labels (AI_label n es LI :: q) (S (kLI + kq))
| BasicLabels : forall a q k, amount_of_labels q k -> amount_of_labels (AI_basic a :: q) k 
| TrapLabels : forall q k, amount_of_labels q k -> amount_of_labels (AI_trap :: q) k 
| InvokeLabels : forall a q k, amount_of_labels q k -> amount_of_labels (AI_invoke a :: q) k
| LocalLabels : forall a b c q k, amount_of_labels q k ->
                             amount_of_labels (AI_local a b c :: q) k.

Lemma got_an_amount i lh es LI kes :
  amount_of_labels es kes -> lfilled i lh es LI -> exists k, amount_of_labels LI k.
  intros Hes Hfill.  cut (forall n, length LI < n -> exists k, amount_of_labels LI k).
  { intro H ; assert (length LI < S (length LI)) as Hlen ;
      [ lia | by apply (H (S (length LI)) Hlen)]. }
  intros n Hlen. generalize dependent LI ; generalize dependent i ;
                   generalize dependent lh ; generalize dependent es ;
                   induction n ; intros es Hes lh i LI Hfill Hlen.
  { exfalso ; lia. } 
  induction i.
  unfold lfilled, lfill in Hfill.
  destruct lh ; last by false_assumption.
  remember (const_list l) as b.
  destruct b ; last by false_assumption.
  apply b2p in Hfill.
  assert (amount_of_labels (l ++ es) kes). {
    clear Hfill. induction l => //=.
(*    generalize dependent LI ; induction l ; intros LI Hfill.
    { simpl in Hfill ; rewrite app_nil_r in Hfill ; by subst. }
    destruct LI ; inversion Hfill. *)
    unfold const_list in Heqb. simpl in Heqb. apply Logic.eq_sym in Heqb.
    apply andb_true_iff in Heqb as [Ha Hl]. unfold is_const in Ha.
    destruct a ; try by false_assumption. apply BasicLabels.
    apply IHl => //=. }
  destruct l0 ; first by (rewrite app_nil_r in Hfill ; subst ; exists kes).
  apply (IHn es Hes (LH_base l []) 0).
  
  

Lemma got_an_amount es : exists k, amount_of_labels es k.
  induction es. { exists 0. exact NilLabels. }
  destruct IHes as [k Hlab].
  induction Hlab.
  exists k ; by apply BasicLabels.
  exists k ; by apply TrapLabels.
  exists k ; by apply InvokeLabels.
  
  
 

Fixpoint depth e :=
  match e with
    | AI_label _ _ LI ->  *)

Lemma wp_br (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n vs es i LI lh :
  const_list vs ->
  length vs = n ->
  lfilled i lh (vs ++ [::AI_basic (BI_br i)]) LI ->
  ▷ WP (vs ++ es) @ s; E {{ Φ }}
  ⊢ WP [AI_label n es LI] @ s; E {{ Φ }}.
Proof.
  iIntros (Hvs Hlen Hfill) "HΦ".
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  - iPureIntro. destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], (vs ++ es), σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    constructor. econstructor =>//.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_label n es LI] locs inst locs' inst'.
    (* Here, only_one_reduction should've left some work for the user to do.
       The following commented code is part of the work the user should have done
       It will likely be used in the reduce_det lemma, in progress *)
Qed.
(*
    + simple_filled Hfill i lh bef aft n l l'.
      * found_intruse (AI_basic (BI_br 0)) Hfill Hxl1.
        -- by intruse_among_values vs0 Hxl1 H.
        -- apply in_or_app. right. apply in_or_app. left.
           apply in_or_app. right. left. done.
      * by intruse_among_values vs0 Hxl1 H.
    + simple_filled Hfill i lh bef aft n l l'.
      found_intruse (AI_basic (BI_br 0)) Hfill Hxl1.
      apply in_or_app ; right. apply in_or_app ; left.
      apply in_or_app ; right ; left ; done.
    + cut (forall n lh0 lh i0 i0' i i' LI0,
              lfilled i0 lh0 (vs0 ++ [AI_basic (BI_br i0')]) LI0 ->
              lfilled i lh (vs ++ [AI_basic (BI_br i')]) LI0 ->
              amount_of_labels LI0 < n ->
              vs = vs0).
      intro Hn ; assert (amount_of_labels LI0 < S (amount_of_labels LI0)) as Hlen ;
        [ lia |
          by rewrite (Hn (S (amount_of_labels LI0)) lh0 lh i0 i0 i i LI0
                         H1 Hfill Hlen) ; inversion Heqf' ; subst ; iFrame].
      clear Heqes. 
      intro n. 
      induction n ;
        intros lh1 lh2 i1 i1' i2 i2' LI Hfill1 Hfill2 Hlen ; first ( exfalso ; lia ).
      unfold lfilled, lfill in Hfill2. destruct i2.
      { destruct lh2 as [bef2 aft2|] ; last by false_assumption.
        remember (const_list bef2) as b eqn:Hbef2.
        destruct b ; last by false_assumption.
        apply b2p in Hfill2.
        unfold lfilled, lfill in Hfill1 ; destruct i1.
        { destruct lh1 as [bef1 aft1|] ; last by false_assumption.
          remember (const_list bef1) as b0 eqn:Hbef1.
          destruct b0 ; last by false_assumption.
          apply b2p in Hfill1.
          rewrite Hfill2 in Hfill1. do 2 rewrite <- app_assoc in Hfill1.
          rewrite app_assoc in Hfill1. rewrite (app_assoc bef1 _ _) in Hfill1.
          apply first_values in Hfill1 as [Hvv _] ; (try by left) ;
            try by unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
          by apply app_inj_2 in Hvv as [_ ?]. }
        fold lfill in Hfill1. destruct lh1 ; first by false_assumption.
        remember (const_list l) as b.
        destruct b ; last by false_assumption.
        destruct (lfill i1 lh1 _) ; last by false_assumption.
        apply b2p in Hfill1. rewrite Hfill2 in Hfill1.
        rewrite <- app_assoc in Hfill1. rewrite app_assoc in Hfill1.
        apply first_values in Hfill1 as ( _ & Habs & _ ) => //= ; try by left.
        unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
      fold lfill in Hfill2. 
      destruct lh2 as [| bef2 n2 l2 lh2 aft2] ; first by false_assumption.
      remember (const_list bef2) as b ; destruct b ; last by false_assumption.
      remember (lfill i2 lh2 (vs ++ [AI_basic (BI_br i2')])) as les.
      destruct les ; last by false_assumption.
      apply b2p in Hfill2.
      unfold lfilled, lfill in Hfill1 ; destruct i1.
      { destruct lh1 as [bef1 aft1 |] ; last by false_assumption.
        remember (const_list bef1) as b ; destruct b ; last by false_assumption.
        apply b2p in Hfill1. rewrite Hfill2 in Hfill1.
        rewrite <- app_assoc in Hfill1. rewrite app_assoc in Hfill1.
        apply first_values in Hfill1 as ( _ & Habs & _ ) => //= ; try by left.
        unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
      fold lfill in Hfill1.
      destruct lh1 as [| bef1 n1 l1 lh1 aft1] ; first by false_assumption.
      remember (const_list bef1) as b ; destruct b ; last by false_assumption.
      remember (lfill i1 lh1 (vs0 ++ [AI_basic (BI_br i1')])) as les0.
      destruct les0 ; last by false_assumption.
      apply b2p in Hfill1. rewrite Hfill2 in Hfill1.
      apply first_values in Hfill1 as ( Hl & Hlab & _ ) => //= ; try by left.
      inversion Hlab ; subst.
      apply (IHn lh1 lh2 i1 i1' i2 i2' l0) => //=.
      unfold lfilled ; rewrite <- Heqles0 ; done.
      unfold lfilled ; rewrite <- Heqles ; done.
      rewrite amount_of_labels_app in Hlen.
      assert (AI_label n1 l1 l0 :: aft2 = [AI_label n1 l1 l0] ++ aft2) as Heq => //=.
      rewrite Heq in Hlen. rewrite amount_of_labels_app in Hlen. simpl in Hlen.
      rewrite Nat.add_0_r in Hlen. rewrite <- Nat.add_succ_l in Hlen.
      fold (amount_of_labels l0) in Hlen. lia.
    + iDestruct "Hσ" as "( ? & ? & ? & ? & ? & ? & ? )". iFrame.
      unfold lfilled in Hfill ; destruct i.
      { unfold lfill in Hfill.
        destruct lh as [bef0 aft0|] ; last by false_assumption.
        remember (const_list bef0) as b eqn:Hbef0.
        destruct b ; last by false_assumption.
        apply b2p in Hfill. subst.
        destruct bef ;
          last by (inversion H1 as [[ Hhd Htl ]] ;
                   found_intruse (AI_label n0 l l0) Htl Hxl1).
        inversion H1 ; subst.
        unfold lfilled in H2.
        remember (lfill (S k) (LH_rec [] (length vs) l lh1 []) _) as les. 
        destruct les ; last by false_assumption. apply b2p in H2. subst.
        unfold lfill in Heqles. destruct (const_list []) ; try by false_assumption.
        destruct k. { destruct lh1 as [bef1 aft1|] ; last by inversion Heqles.
                      remember (const_list bef1) as b eqn:Hbef1.
                      destruct b ; inversion Heqles.
                      unfold lfill in Heqles1.
                      rewrite <- Hbef1 in Heqles1. inversion Heqles1.      


Admitted. *)


      
Lemma wp_block (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs es n m t1s t2s :
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ▷ WP [::AI_label m [::] (vs ++ to_e_list es)] @ s; E {{ Φ }}
  ⊢ WP (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) @ s; E {{ Φ }}.
Proof.
  iIntros (Hvs Hlen1 Hlen2 Hlen3) "HΦ".
  iApply wp_lift_step => //=.
  apply to_val_cat_None2. done.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  - iPureIntro. destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], _, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    constructor. econstructor =>//.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last by eapply r_simple, rs_block.
    inversion H; subst; clear H.
    by iFrame.
Qed.

Lemma wp_label_value (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es m ctx v :
  iris.to_val es = Some (immV v) -> 
  Φ (immV v) ⊢ WP [::AI_label m ctx es] @ s; E {{ Φ }}.
Proof.
  iIntros (Hval) "HP".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], es, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.  apply rs_label_const.
    eapply to_val_const_list. apply Hval.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es1 σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { apply r_simple.  apply rs_label_const.
         eapply to_val_const_list. apply Hval. }
    inversion H; subst; clear H.
    rewrite Hval. by iFrame.
Qed.
Lemma wp_label_trap (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es m ctx :
  iris.to_val es = Some trapV -> 
  Φ trapV ⊢ WP [::AI_label m ctx es] @ s; E {{ Φ }}.
Proof.
  iIntros (Hval) "HP".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [AI_trap], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply to_val_trap_is_singleton in Hval as ->.
    apply r_simple.  apply rs_label_trap.
  - apply to_val_trap_is_singleton in Hval as ->.
    destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es1 σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { apply r_simple.  apply rs_label_trap. }
    inversion H; subst; clear H.
    by iFrame.
Qed.

Lemma wp_val_return (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs vs' es' es'' n :
  const_list vs ->
  WP vs' ++ vs ++ es'' @ s; E {{ Φ }}
  ⊢ WP vs @ s; E CTX 1; LH_rec vs' n es' (LH_base [] []) es'' {{ Φ }}.
Proof.
  iIntros (Hconst) "HWP".
  iLöb as "IH".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  inversion Hfill;subst.
  inversion H8;subst.
  assert (vs' ++ [AI_label n es' ([] ++ vs ++ [])] ++ es''
          = ((vs' ++ [AI_label n es' ([] ++ vs ++ [])]) ++ es''))%SEQ as ->.
  { erewrite app_assoc. auto. }
  apply const_list_is_val in Hconst as [v1 Hv1].
  apply const_list_is_val in H7 as [v2 Hv2].
  eapply to_val_cat_inv in Hv1 as Hvv;[|apply Hv2].
  iApply (wp_seq _ _ Φ (λ ret, ⌜ret = immV (v2 ++ v1)⌝)%I).
  iSplit => //.
  iSplitR.
  iApply wp_val_app; first by apply Hv2.
  iSplit => //.
  iApply wp_label_value;[|auto]. erewrite app_nil_l. erewrite app_nil_r. apply Hv1.
  iIntros (w ->). erewrite iris.of_to_val;[|apply Hvv]. rewrite app_assoc. auto.
Qed.

Lemma wp_base (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs vs' es'' :
  const_list vs ->
  WP vs' ++ vs ++ es'' @ s; E {{ Φ }}
  ⊢ WP vs @ s; E CTX 0; LH_base vs' es'' {{ Φ }}.
Proof.
  iIntros (Hconst) "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  inversion Hfill;subst. iFrame.
Qed.

Fixpoint push_base (lh : lholed) n es' vs_pre es_post :=
  match lh with
  | LH_base vs_pre' es_post' => LH_rec vs_pre' n es' (LH_base vs_pre es_post) es_post'
  | LH_rec vs m es'' lh' es => LH_rec vs m es'' (push_base lh' n es' vs_pre es_post) es
  end.

Fixpoint frame_base (lh : lholed) l1 l2 :=
  match lh with
  | LH_base vs es => LH_base (vs ++ l1) (l2 ++ es)
  | LH_rec vs m es' lh' es => LH_rec vs m es' (frame_base lh' l1 l2) es
  end.

Lemma lfilledInd_push i : ∀ lh n es' es LI l1 l2,
  const_list l1 ->
  lfilledInd i lh ([::AI_label n es' (l1 ++ es ++ l2)]) LI ->
  lfilledInd (S i) (push_base lh n es' l1 l2) es LI.
Proof.
  induction i.
  all: intros lh n es' es LI l1 l2 Hconst Hfill.
  { inversion Hfill;subst.
    constructor. auto. constructor. auto.
    (* apply lfilled_Ind_Equivalent. cbn. rewrite eqseqE app_nil_r. done.  *)}
  { inversion Hfill;subst. simpl. constructor. auto.
    apply IHi. auto. auto. }
Qed.
Lemma lfilledInd_frame i : ∀ lh l1 es l2 LI,
    const_list l1 ->
    lfilledInd i lh (l1 ++ es ++ l2) LI ->
    lfilledInd i (frame_base lh l1 l2) (es) LI.
Proof.
  induction i.
  all: intros lh l1 es l2 LI Hconst Hfill.
  { inversion Hfill;subst.
    assert (vs ++ (l1 ++ es ++ l2) ++ es'
            = (vs ++ l1) ++ es ++ (l2 ++ es'))%SEQ as ->.
    { repeat erewrite app_assoc. auto. }
    constructor. apply const_list_concat;auto. }
  { inversion Hfill;subst. simpl. constructor. auto.
    apply IHi. auto. auto. }
Qed.
      

Lemma wp_base_push (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es l1 l2 i lh :
  const_list l1 ->
  WP es @ s; E CTX i; frame_base lh l1 l2 {{ Φ }}
  ⊢ WP l1 ++ es ++ l2 @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hconst) "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  apply lfilledInd_frame in Hfill.
  iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
  iPureIntro. by apply lfilled_Ind_Equivalent. auto.
Qed.
Lemma wp_label_push (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es i lh n es' l1 l2 :
  const_list l1 ->
  WP es @ s; E CTX S i; push_base lh n es' l1 l2 {{ Φ }}
  ⊢ WP [::AI_label n es' (l1 ++ es ++ l2)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hconst) "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  apply lfilledInd_push in Hfill.
  iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
  iPureIntro. by apply lfilled_Ind_Equivalent. auto.
Qed.
Lemma wp_label_push_nil (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es i lh n es' :
  WP es @ s; E CTX S i; push_base lh n es' [] [] {{ Φ }}
  ⊢ WP [::AI_label n es' es] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros "HWP".
  iDestruct (wp_label_push with "HWP") as "HWP". auto.
  erewrite app_nil_l. erewrite app_nil_r. done.
Qed.

Lemma lfilled_to_val i  :
  ∀ lh es LI, is_Some (iris.to_val LI) ->
  lfilled i lh es LI ->
  is_Some (iris.to_val es).
Proof.
  induction i.
   { intros lh es LI [x Hsome] Hfill.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill;subst.
    destruct (to_val es) eqn:Hnone;eauto.
    exfalso.
    apply (to_val_cat_None1 _ es') in Hnone.
    apply (to_val_cat_None2 vs) in Hnone.
    rewrite Hnone in Hsome. done.
  }
  { intros lh es LI Hsome Hfill.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill;simplify_eq.
    clear -Hsome. exfalso.
    induction vs =>//=.
    simpl in Hsome. by inversion Hsome.
    simpl in Hsome; inversion Hsome.
    destruct a =>//=.
    destruct b =>//=.
    destruct (iris.to_val (vs ++ [AI_label n es' LI0] ++ es'')%SEQ) eqn:Hcontr.
    apply IHvs;eauto.
    rewrite Hcontr in H. done.
    destruct vs;done.
  }
Qed.

Lemma wp_block_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (i : nat) (lh : lholed) vs t1s t2s es n m :
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ▷ WP [::AI_label m [::] (vs ++ to_e_list es)] @ s; E CTX i; lh {{ Φ }}
  ⊢ WP (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hconst Hn Hn' Hm) "HWP".
  iIntros (LI Hfill).
  destruct (iris.to_val LI) eqn:Hcontr.
  { apply lfilled_to_val in Hfill as [v' Hv];eauto.
    assert (iris.to_val [AI_basic (BI_block (Tf t1s t2s) es)] = None) as Hnone;auto.
    apply (to_val_cat_None2 vs) in Hnone.
    rewrite Hv in Hnone. done. }
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  { iPureIntro. destruct s;auto.
    apply lfilled_swap with (es':=[::AI_label m [::] (vs ++ to_e_list es)]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].
    eexists [],_,σ,[]. simpl.
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple. eapply rs_block.
    apply Hconst. apply Hn. apply Hn'. apply Hm. eauto. eauto. }
  destruct σ as [[[hs ws] locs] inst] => //=.
  iApply fupd_mask_intro;[solve_ndisj|].
  iIntros "Hcls !>" (es1 σ2 efs HStep).
  iMod "Hcls". iModIntro.
  destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
  apply lfilled_swap with (es':=[::AI_label m [::] (vs ++ to_e_list es)]) in Hfill as Hfill'.
  destruct Hfill' as [LI' Hfill'].
  destruct HStep as [H [-> ->]].
  eapply reduce_det in H; cycle 1.
  { eapply r_label. apply r_simple. eapply rs_block;eauto. all: eauto. }
  inversion H; subst; clear H.
  iFrame. iSplit;[|done].
  iSpecialize ("HWP" $! _ Hfill'). iFrame.
Qed.

Lemma wp_br_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n vs es i lh vs' es' :
  const_list vs ->
  length vs = n ->
  ▷ WP (vs' ++ vs ++ es ++ es') @ s; E {{ Φ }}
  ⊢ WP vs ++ [::AI_basic (BI_br i)] @ s; E CTX S i; LH_rec vs' n es lh es' {{ Φ }}.
Proof.
  iIntros (Hvs Hlen) "HΦ".
  iIntros (LI Hfill).
  destruct (iris.to_val LI) eqn:Hcontr.
  { apply lfilled_to_val in Hfill as [v' Hv];eauto.
    assert (iris.to_val [AI_basic (BI_br i)] = None) as Hnone;auto.
    apply (to_val_cat_None2 (vs)) in Hnone.
    rewrite Hv in Hnone. done. }
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  { apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
    iPureIntro. destruct s;auto.
    apply lfilled_Ind_Equivalent in H8 as Hfill'.
    apply lfilled_swap with (es':=vs ++ es) in Hfill' as Hfill''.
    destruct Hfill'' as [LI' Hfill''].    
    eexists [],_,σ,[].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.   
    eapply r_label with (lh:=(LH_base vs' es')).
    2: { erewrite cons_middle. apply lfilled_Ind_Equivalent.
         econstructor;auto. }
    2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
    apply r_simple. eapply rs_br.
    apply Hvs. auto. eauto. }
  destruct σ as [[[hs ws] locs] inst] => //=.
  iApply fupd_mask_intro;[solve_ndisj|].
  iIntros "Hcls !>" (es1 σ2 efs HStep).
  iMod "Hcls". iModIntro.
  destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
  apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
  apply lfilled_Ind_Equivalent in H8 as Hfill'.
  apply lfilled_swap with (es':=vs ++ es) in Hfill' as Hfill''.
  destruct Hfill'' as [LI' Hfill''].    
  destruct HStep as [H [-> ->]].
  eapply reduce_det in H; cycle 1.
  { eapply r_label with (lh:=(LH_base vs' es')).
    2: { apply lfilled_Ind_Equivalent.
         econstructor;auto. }
    2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
    apply r_simple. eapply rs_br. apply Hvs. all:eauto. }
  inversion H; subst; clear H.
  iFrame. iSplit;[|done].
  erewrite !app_assoc. iFrame.
Qed.

Lemma wp_loop_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs es n m t1s t2s i lh :
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ▷ WP [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)] @ s; E CTX i; lh {{ Φ }}
  ⊢ WP vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hvs Hn Hn' Hm) "HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iDestruct ("HP" $! _ Hfill') as "HP".
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill].
    assert (iris.to_val [AI_basic (BI_loop (Tf t1s t2s) es)] = None) as HH;auto.
    apply (to_val_cat_None2 vs) in HH. rewrite Hfill in HH. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_loop;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_loop;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    by iFrame.
Qed.
Lemma wp_loop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs es n m t1s t2s :
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ▷ WP [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)] @ s; E {{ Φ }}
  ⊢ WP vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)] @ s; E {{ Φ }}.
Proof.
  iIntros (Hvs Hn Hn' Hm) "HP".
  iApply wp_wasm_empty_ctx. iApply wp_loop_ctx;eauto.
  iNext. iApply wp_wasm_empty_ctx. iFrame.
Qed.

Lemma wp_if_true_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s i lh :
  n ≠ Wasm_int.int_zero i32m ->
  ▷ WP [::AI_basic (BI_block tf e1s)] @ s; E CTX i; lh {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hn) "HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iDestruct ("HP" $! _ Hfill') as "HP".
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_if_true;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_if_true;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    by iFrame.
Qed.
Lemma wp_if_true (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s :
  n ≠ Wasm_int.int_zero i32m ->
  ▷ WP [::AI_basic (BI_block tf e1s)] @ s; E {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "HP".
  iApply wp_wasm_empty_ctx. iApply wp_if_true_ctx;eauto.
  iNext. iApply wp_wasm_empty_ctx. iFrame.
Qed.
  
Lemma wp_if_false_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s i lh :
  n = Wasm_int.int_zero i32m ->
  ▷ WP [::AI_basic (BI_block tf e2s)] @ s; E CTX i; lh {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hn) "HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iDestruct ("HP" $! _ Hfill') as "HP".
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_if_false;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_if_false;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    by iFrame.
Qed.
Lemma wp_if_false (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s :
  n = Wasm_int.int_zero i32m ->
  ▷ WP [::AI_basic (BI_block tf e2s)] @ s; E {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "HP".
  iApply wp_wasm_empty_ctx. iApply wp_if_false_ctx;eauto.
  iNext. iApply wp_wasm_empty_ctx. iFrame.
Qed.

Lemma wp_br_if_true_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n i j lh :
  n ≠ Wasm_int.int_zero i32m ->
  ▷ WP [::AI_basic (BI_br i)] @ s; E CTX j; lh {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] @ s; E CTX j; lh {{ Φ }}.
Proof.
  iIntros (Hn) "HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iDestruct ("HP" $! _ Hfill') as "HP".
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_br_if_true;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_br_if_true;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    by iFrame.
Qed.
Lemma wp_br_if_true (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n i :
  n ≠ Wasm_int.int_zero i32m ->
  ▷ WP [::AI_basic (BI_br i)] @ s; E {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "HP".
  iApply wp_wasm_empty_ctx. iApply wp_br_if_true_ctx;eauto.
  iNext. iApply wp_wasm_empty_ctx. iFrame.
Qed.

(* The following expression reduces to a value reguardless of context, 
   and thus does not need a context aware version *)
Lemma wp_br_if_false (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n i :
  n = Wasm_int.int_zero i32m ->
  ▷ Φ (immV [])
  ⊢ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] @ s; E {{ Φ }}.
Proof.
  iIntros (Hn) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_br_if_false.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last by apply r_simple, rs_br_if_false.
    inversion H; subst; clear H.
    by iFrame.
Qed.


Lemma wp_br_table_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i j k lh :
  ssrnat.leq (S (Wasm_int.nat_of_uint i32m c)) (length iss) ->
  List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
  ▷ WP [::AI_basic (BI_br j)] @ s; E CTX k; lh {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E CTX k; lh {{ Φ }}.
Proof.
  iIntros (Hiss Hj) "HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iDestruct ("HP" $! _ Hfill') as "HP".
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. apply rs_br_table;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_br_table;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    by iFrame.
Qed.
Lemma wp_br_table (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i j :
  ssrnat.leq (S (Wasm_int.nat_of_uint i32m c)) (length iss) ->
  List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
  ▷ WP [::AI_basic (BI_br j)] @ s; E {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E {{ Φ }}.
Proof.
  iIntros (? ?) "HP".
  iApply wp_wasm_empty_ctx. iApply wp_br_table_ctx;eauto.
  iNext. iApply wp_wasm_empty_ctx. iFrame.
Qed.

Lemma wp_br_table_length_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i j lh :
  ssrnat.leq (length iss) (Wasm_int.nat_of_uint i32m c) ->
  ▷ WP [::AI_basic (BI_br i)] @ s; E CTX j; lh {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E CTX j; lh {{ Φ }}.
Proof.
  iIntros (Hiss) "HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iDestruct ("HP" $! _ Hfill') as "HP".
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. apply rs_br_table_length;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_br_table_length;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    by iFrame.
Qed.
Lemma wp_br_table_length (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i :
  ssrnat.leq (length iss) (Wasm_int.nat_of_uint i32m c) ->
  ▷ WP [::AI_basic (BI_br i)] @ s; E {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "HP".
  iApply wp_wasm_empty_ctx. iApply wp_br_table_length_ctx;eauto.
  iNext. iApply wp_wasm_empty_ctx. iFrame.
Qed.

 (*| rs_return :
      forall n i vs es lh f,
        const_list vs ->
        length vs = n ->
        lfilled i lh (vs ++ [::AI_basic BI_return]) es ->
        reduce_simple [::AI_local n f es] vs*)
(* return is a contextual rule, but it is also a function rule. Before we tackle with wp, 
   we must have set up the way in which to handle AI_local. 
   intuitively, AI_local functions as a fresh bind, in a fresh ctx, very similar to wp_seq_ctx 
   solution idea: another WP now that can abstract away the AI_local "wrapper", using AI_local 
   instead of AI_label. Note that AI_label and contexts can still occur within an AI_local....
   Main difference is that AI_local is not nested in the same way as label, in which label 
   knows about the nesting structure for br, whereas local "stops" br from exiting.

   Why is there a need for a new WP? because there can be a nested label structure inside a 
   label, and we need to have knowledge of that for the return instruction. The label wrapper
   is always the outermost layer! so current ctxWP does not work for that reason.
*)

(* Frame rules attempt *)

Definition frame_interp (f: frame) : iProp Σ :=
  ([∗ list] n ↦ v ∈ f.(f_locs), (N.of_nat n) ↦[wl] v) ∗ ( ↦[wi] f.(f_inst)).

Lemma wp_return (s: stuckness) (E: coPset) (Φ: val -> iProp Σ) es vs vs0 n f i lh:
  iris.to_val vs = Some (immV vs0) ->
  length vs = n ->
  lfilled i lh (vs ++ [AI_basic BI_return]) es ->
  (Φ (immV vs0) ⊢ WP [AI_local n f es] @ s; E {{ v, Φ v }})%I.
Proof.
  iIntros (Hval Hlen Hlf) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  assert (const_list vs) as Hcvs; first by apply to_val_const_list in Hval.
  iSplit.
  - iPureIntro. destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], vs, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    constructor. econstructor =>//.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iModIntro.
    iIntros (es1 σ2 efs HStep).
    iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last by (apply r_simple; eapply rs_return).
    inversion H; subst; clear H.
    rewrite Hval.
    by iFrame.
Qed.

Lemma wp_return_frame (s: stuckness) (E: coPset) (Φ: val -> iProp Σ) vs vs0 n f i lh LI:
  iris.to_val vs = Some (immV vs0) ->
  length vs = n ->
  lfilled i lh (vs ++ [AI_basic BI_return]) LI -> 
  (Φ (immV vs0) ⊢ WP LI @ s; E FRAME n ; f {{ v, Φ v }}).
Proof.
  iIntros (Hval Hlen Hlf) "HΦ".
  by iApply wp_return.
Qed.

(*
  The major problem is, even if we have the knowledge that the inner instruction
  *could* execute and return some desired result given an appropriate frame 
  resource wf, how do we actually *produce* that resource from the current state, 
  even temporarily, to extract information from that knowledge? Resources cannot be 
  crafted from thin air.
 *)

Lemma wp_seq_frame (s: stuckness) (E: coPset) (Φ Ψ: val -> iProp Σ) (es1 es2: language.expr wasm_lang) (wf wf2 wf3: frame) (n: nat):
  ((¬ Ψ trapV) ∗
    (frame_interp wf -∗
     WP es1 @ NotStuck; E {{ w, Ψ w ∗ frame_interp wf2 }}) ∗
  (∀ w, (Ψ w ∗ frame_interp wf2) -∗ WP (iris.of_val w ++ es2) @ s; E FRAME n; wf2 {{ v, Φ v ∗ frame_interp wf3 }})
  ⊢ WP es1 ++ es2 @ s; E FRAME n; wf {{ v, Φ v }})%I.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ wf wf2 wf3 n).
  iIntros "(Hntrap & Hes1 & Hes2)".
  repeat rewrite wp_unfold /wp_pre /=.

Admitted.

                      
(*
Definition frame_push_local (ls: lstack) n f := rcons ls (n, f, 0, LH_base [::] [::]).
 *)
(*
Fixpoint inner_frame (ls: lstack) : option frame :=
  match ls with
  | [::] => None
  | [::(n, f, k, lh)] => Some f
  | cf :: cs => inner_frame cs
  end.

Fixpoint update_inner_frame (ls: lstack) (f: frame) : option lstack :=
  match ls with
  | [::] => None
  | [::(n, f', k, lh)] => Some [::(n, f, k, lh)]
  | cf :: cs => match update_inner_frame cs f with
              | Some ls' => Some (cf :: ls')
              | None => None
              end
  end.
*)


(* 
  The main difference here is that, changes in frames (AI_local) have impact on the local variables from the aspect of the internal expression, which are part of the state -- while pushing a label has no such impact. 

  We need to somehow account for this whenever we enter or leave a call frame. In particular, in both the 2nd and the 3rd premises, we need to give them resources of the locals and current instance -- whatever they produce, the corresponding modification needs to be made to the frame stored in the lstack construct. In some sense we're providing a wrapper for the internal instructions to execute.
 *)

(* Firstly, we could enter a local frame by temporarily forget about the current frame and construct the new frame 
   resources in place. 

   We ensure that no frame resources from inside is leaked to the outer frame by forcing the inner frame information 
   to be separated by (frame_interp f'); the requirement that f' has the same number of locals guarantee that no local
   variable inside the frame could escape from the frame.
   

*)
Lemma wp_frame_push_local (s: stuckness) (E: coPset) (Φ: val -> iProp Σ) n f n0 f0 es:
  (*  length f.(f_locs) = length f'.(f_locs) -> *)
  WP es @ NotStuck; E FRAME n ; f {{ v, Φ v }} ⊢
  WP [AI_local n f es] @ s; E FRAME n0 ; f0 {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es Φ n f n0 f0).
  iIntros "Hwp".
  unfold wp_wasm_frame.
  repeat rewrite wp_unfold /wp_pre /=.
  iIntros (σ ????) "Hσ".
  destruct σ as [[[hs ws] locs] inst].
  iApply fupd_mask_intro; first by solve_ndisj.
  iIntros "Hmask".
  iSplit.
  { destruct s => //=.
    iSpecialize ("Hwp" $! (hs, ws, locs, inst) ns κ κs nt with "Hσ").
    iPureIntro.
    econstructor.
    eexists.
    (* This will not work, instead it's just for observation. *)
    exists (hs, ws, locs, inst), [].
    unfold language.prim_step => /=.
    repeat split => //.
    apply r_local.
    admit.
  }
Admitted.




(* basic instructions with non-simple(non-pure) reductions *)

(* Function related *)

Lemma wp_call: False.
Proof.
Admitted.

Lemma wp_call_indirect: False.
Proof.
Admitted.

(* Function frame *)
Lemma wp_local: False.
Proof.
Admitted.

(* Reduction result for call/call_indirect *)
Lemma wp_invoke: False.
Proof.
Admitted.



(* Instance related *)

Lemma wp_get_local (s : stuckness) (E : coPset) (v: value) (i: nat) (ϕ: val -> Prop):
  ϕ (immV [v]) ->
  N.of_nat i ↦[wl] v ⊢
  WP ([AI_basic (BI_get_local i)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ N.of_nat i ↦[wl] v }}.
Proof.
  iIntros (Hϕ) "Hli".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] inst].
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ? & ?)".
  iDestruct (gen_heap_valid with "Hl Hli") as "%Hli".
  rewrite gmap_of_list_lookup Nat2N.id in Hli.
  rewrite - nth_error_lookup in Hli.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v)], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    by apply r_get_local.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last eapply r_get_local; eauto.
    inversion H; subst; clear H.
    by iFrame => //=.
Qed.

Lemma wp_set_local (s : stuckness) (E : coPset) (v v0: value) (i: nat) (ϕ: val -> Prop):
  ϕ (immV []) ->
  N.of_nat i ↦[wl] v0 ⊢
  WP ([AI_basic (BI_const v); AI_basic (BI_set_local i)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ N.of_nat i ↦[wl] v }}.
Proof.
  iIntros (Hϕ) "Hli".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] inst].
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ? & ?)".
  iDestruct (gen_heap_valid with "Hl Hli") as "%Hli".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], (hs, ws, set_nth v locs i v, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    by eapply r_set_local.
  - iIntros "!>" (es σ2 efs HStep).
    (* modify locs[i]. This has to be done before the update modality is used. *)
    iMod (gen_heap_update with "Hl Hli") as "(Hl & Hli)".
    iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last eapply r_set_local with (f' := {| f_locs := set_nth v locs i v; f_inst := inst |}); eauto.
    inversion H; subst; clear H.
    iFrame.
    repeat iSplit => //.
    assert (i < length locs) as Hlength.
    { rewrite gmap_of_list_lookup Nat2N.id in Hli.
      by apply lookup_lt_Some in Hli.
    }
    rewrite - gmap_of_list_insert; rewrite Nat2N.id => //.
    by erewrite fmap_insert_set_nth.
Qed.

(* tee_local is not atomic in the Iris sense, since it requires 2 steps to be reduced to a value. *)
Lemma wp_tee_local (s : stuckness) (E : coPset) (v v0: value) (n: nat) (ϕ: val -> Prop):
  (not (ϕ trapV)) ->
  ϕ (immV [v]) ->
  N.of_nat n ↦[wl] v0 ⊢
  WP ([AI_basic (BI_const v); AI_basic (BI_tee_local n)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ N.of_nat n ↦[wl] v }}.
Proof.
  iIntros (Hntrap Hϕ) "Hli".
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  destruct σ as [[[hs ws] locs] inst].
  iApply fupd_mask_intro; first by solve_ndisj.
  iIntros "Hfupd".
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ? & ?)".
  iDestruct (gen_heap_valid with "Hl Hli") as "%Hli".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v); AI_basic (BI_const v); AI_basic (BI_set_local n)], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_tee_local => //.
  - iIntros "!>" (es σ2 efs HStep).
    iMod "Hfupd".
    iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last apply r_simple, rs_tee_local => //=.
    inversion H; subst; clear H.
    iFrame.
    repeat iSplit => //.
    iApply wp_val => //=.
    iSplitR => //; first by iIntros "(%HContra & _)". 
    iApply wp_mono; last iApply wp_set_local; eauto => //.
Qed.

(* r_get_global involves finding the reference index to the global store via
   the instance first. *)

(* TODO: Weaken the ownership of instance (and global) *)
Lemma wp_get_global (s : stuckness) (E : coPset) (v: value) (inst: instance) (n: nat) (ϕ: val -> Prop) (g: global) (k: nat):
  inst.(inst_globs) !! n = Some k ->
  g.(g_val) = v ->
  ϕ (immV [v]) ->
  (↦[wi] inst ∗
  N.of_nat k ↦[wg] g) ⊢
                      WP ([AI_basic (BI_get_global n)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ ↦[wi] inst ∗ N.of_nat k ↦[wg] g }}.
Proof.
  iIntros (Hinstg Hgval Hϕ) "(Hinst & Hglob)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hg & ? & Hi & ?)".
  iDestruct (gen_heap_valid with "Hg Hglob") as "%Hglob".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  rewrite gmap_of_list_lookup Nat2N.id in Hglob.
  rewrite - nth_error_lookup in Hglob.
  rewrite - nth_error_lookup in Hinstg.
  rewrite lookup_insert in Hinst.
  inversion Hinst; subst; clear Hinst.
  assert ( sglob_val (host_function:=host_function) ws
                     (f_inst {| f_locs := locs; f_inst := inst |}) n =
           Some (g_val g) ) as Hsglob.
  { unfold sglob_val, option_map, sglob, option_bind, sglob_ind => /=.
    by rewrite Hinstg Hglob.
  }
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (g_val g))], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    by apply r_get_global.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] winst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last by apply r_get_global.
    inversion H; subst; clear H.
    by iFrame => /=.
Qed.
(*
Print  sglob_val.
Print supdate_glob.
*)
Lemma wp_set_global (s : stuckness) (E : coPset) (v:value) (inst :instance) (n:nat)
      (Φ : val -> Prop) (g: global) (k:nat):
  inst.(inst_globs) !! n = Some k ->
  Φ (immV []) ->
  ( ↦[wi] inst ∗
    N.of_nat k ↦[wg] g) ⊢
                        WP [AI_basic (BI_const v) ; AI_basic (BI_set_global n)] @ s ; E {{ w,  ⌜ Φ w ⌝ ∗ ↦[wi] inst ∗ N.of_nat k ↦[wg] {| g_mut := g_mut g ; g_val := v |} }}.
Proof.
  iIntros (Hinstg HΦ) "[Hinst Hglob]".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[ hs ws] locs ] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hg & ? & Hi & ?)". 
  iDestruct (gen_heap_valid with "Hg Hglob") as "%Hglob".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  rewrite gmap_of_list_lookup Nat2N.id in Hglob.
  rewrite - nth_error_lookup in Hglob.
  rewrite - nth_error_lookup in Hinstg.
  rewrite lookup_insert in Hinst.
  inversion Hinst ; subst ; clear Hinst.
  iDestruct (gen_heap_update with "Hg Hglob") as "H".
  remember {|
      s_funcs := datatypes.s_funcs ws;
      s_tables := datatypes.s_tables ws;
      s_mems := datatypes.s_mems ws;
      s_globals :=
        update_list_at (datatypes.s_globals ws) k
          {| g_mut := g_mut g; g_val := v |}
    |} as ws'.
  assert ( supdate_glob (host_function := host_function) ws
                     (f_inst {| f_locs := locs ; f_inst := inst |}) n v =
             Some ws') as Hsglob.
  { unfold supdate_glob, option_bind, sglob_ind, supdate_glob_s, option_map => /=.
    by rewrite Hinstg Hglob Heqws'. }
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], (hs, ws', locs, inst), [].
    unfold language.prim_step => /=. repeat split => /=.
    by apply r_set_global.
  - iIntros "!>" (es σ2 efs Hstep). iMod "H". iModIntro. 
    destruct σ2 as [[[ hs2 ws2 ] locs' ] inst'].
    destruct Hstep as (H & -> & ->).
    only_one_reduction H [AI_basic (BI_const v) ; AI_basic (BI_set_global n)]
                       locs inst locs' inst'.   
 (*   inversion Heqes ; subst. inversion Heqf' ; subst. rewrite H in Hsglob.
    destruct s0. simpl in Hsglob. inversion Hsglob. simpl.
    iDestruct "H" as "[Hg Hk]". iFrame. iSplit ; last done.
    assert (N.to_nat (N.of_nat k) < length s_globals) as Hlen.
    { rewrite Nat2N.id. simpl in Hglob. 
      apply nth_error_Some. rewrite Hglob. done. }
    rewrite <- (gmap_of_list_insert (l:= s_globals) {|g_mut := g_mut g ; g_val := v0 |} (n := N.of_nat k) Hlen).
    rewrite Nat2N.id.
    cut (<[k:={| g_mut := g_mut g ; g_val := v0 |}]> s_globals =
           update_list_at s_globals k {| g_mut := g_mut g ; g_val := v0 |}) ;
      [ intro Heq ; rewrite Heq ; done |].
    rewrite Nat2N.id in Hlen. unfold update_list_at.
    clear - Hlen. (* Hglob Hinstg Hsglob H1. *)
    generalize dependent s_globals. 
    induction k ; intros s_globals Hlen. 
    { destruct s_globals.
      { exfalso. simpl in Hlen. lia. }
      simpl. unfold drop. done. }
    destruct s_globals. { exfalso ; simpl in Hlen ; lia. }
    simpl. simpl in IHk. assert (k < (length s_globals)). { simpl in Hlen. lia. }
    rewrite (IHk s_globals H). done.
Qed.*)
    Admitted.


Lemma update_list_same_dom (l : seq.seq global) k v :
  k < length l -> 
  dom (gset N) (gmap_of_list l) = dom (gset N) (gmap_of_list (update_list_at l k v)).
Proof.
  induction k ; unfold update_list_at. 
  destruct l. simpl. intro ; exfalso ; lia.
  intro ; simpl. destruct l. simpl. unfold gmap_of_list. simpl.
  unfold dom, gset_dom, mapset.mapset_dom, mapset.mapset_dom_with, merge, gmap_merge.
  unfold merge, pmap.Pmerge. Search (gmap_of_list _).
  
Admitted.

(* Auxiliary lemmas for load/store *)

Lemma store_length (m m': memory) (n: N) (off: static_offset) (bs: bytes) (l: nat) :
  store m n off bs l = Some m' ->
  length m.(mem_data).(ml_data) = length m'.(mem_data).(ml_data).
Proof.
Admitted.

Lemma mem_equiv_length (m m': memory):
  m ≡ₘ m' ->
  mem_length m = mem_length m'.
Proof.
  move => Hm.
  unfold mem_length, memory_list.mem_length.
  by rewrite Hm.
Qed.

Lemma store_data_inj (m1 m2 m1': memory) (n: N) (off: static_offset) (bs: bytes) (l: nat) :
  m1 ≡ₘ m2 ->
  store m1 n off bs l = Some m1' ->
  exists m2', store m2 n off bs l = Some m2' /\ m1' ≡ₘ m2'.
Proof.
  move => Hmequiv Hstore.
  Print memory_list.
  exists (Build_memory (Build_memory_list (ml_init (mem_data m2)) (ml_data (mem_data m1'))) (mem_max_opt m2)).
  unfold store in Hstore.
  unfold store.
Admitted.

Lemma update_list_at_insert {T: Type} (l: list T) (x: T) (n: nat):
  n < length l ->
  update_list_at l n x = <[n := x]> l.
Proof.
  move => Hlen.
  unfold update_list_at.
  move: n x Hlen.
  elim: l => //=.
  - move => n.
    by destruct n; lia.
  - move => a l IH n x Hlen.
    destruct n => //=.
    f_equal.
    apply IH.
    lia.
Qed.
    
(* A version of gen_heap_update specifically for wasm memories. *)
Lemma gen_heap_update_big_wm σ n ml ml':
  gen_heap_interp σ -∗ 
  ([∗ list] i ↦ b ∈ ml, N.of_nat n ↦[wm][N.of_nat i] b) ==∗
  gen_heap_interp ((new_2d_gmap_at_n (N.of_nat n) ml') ∪ σ) ∗
  ([∗ list] i ↦ b ∈ ml', N.of_nat n ↦[wm][N.of_nat i] b).
Proof.
(*  revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
  { rewrite left_id_L. auto. }
  iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
  decompose_map_disjoint.
  rewrite !big_opM_insert // -insert_union_l //.
  by iMod (gen_heap_alloc with "Hσ'σ") as "($ & $ & $)";
    first by apply lookup_union_None.*)
Admitted.



Lemma wp_load: False.
Proof.
Admitted.

Lemma wp_store (s: stuckness) (E: coPset) (t: value_type) (v: value) (inst: instance) (mem mem': memory) (off: static_offset) (a: alignment_exponent) (k: i32) (n: nat) (ϕ: val -> Prop) :
  types_agree t v ->
  inst.(inst_memory) !! 0 = Some n ->
  store mem (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) = Some mem' ->
  ϕ (immV []) ->
  ( ↦[wi] inst ∗
  N.of_nat n ↦[wmblock] mem) ⊢
  (WP ([AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t None a off)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ ↦[wi] inst ∗ (N.of_nat n) ↦[wmblock] mem' }}).
Proof.
  iIntros (Hvt Hinstn Hstore Hϕ) "[Hinst Hwmblock]".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  unfold mem_block.
  iDestruct "Hwmblock" as "(Hwmdata & Hwmlength)".
  iDestruct "Hσ" as "(? & ? & Hm & ? & ? & Hi & Hγ)".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  rewrite lookup_insert in Hinst.
  inversion Hinst; subst; clear Hinst.
  iDestruct (gen_heap_valid with "Hγ Hwmlength") as "%Hwmlength".
  rewrite gmap_of_list_lookup list_lookup_fmap Nat2N.id in Hwmlength.
  destruct (s_mems ws !! n) as [m|] eqn: Hm => //.
  simpl in Hwmlength.
  inversion Hwmlength as [Hwmlength']; clear Hwmlength.
  iAssert ( (∀ i, ⌜(ml_data (mem_data mem)) !! i = (ml_data (mem_data m)) !! i ⌝)%I) as "%Hmeq".
  {
    iIntros (i).
    destruct (ml_data (mem_data mem) !! i) eqn:Hmd.
    - iDestruct (big_sepL_lookup with "Hwmdata") as "H" => //.
      iDestruct (gen_heap_valid with "Hm H") as "%H".
      rewrite gmap_of_list_2d_lookup list_lookup_fmap Nat2N.id Hm in H.
      unfold memory_to_list in H.
      simpl in H.
      by rewrite Nat2N.id in H.
    - apply lookup_ge_None in Hmd.
      iPureIntro.
      symmetry.
      apply lookup_ge_None.
      unfold mem_length, memory_list.mem_length in Hwmlength'.
      lia.
  }
  iAssert (⌜mem ≡ₘm⌝%I) as "%Hmem".
  {
    unfold mem_block_equiv.
    by rewrite (list_eq (ml_data (mem_data mem)) (ml_data (mem_data m))).
  }
  specialize (store_data_inj mem m mem' (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) Hmem Hstore) as [m' [Hstore' Hmdata']].
  rewrite - nth_error_lookup in Hm.
  rewrite - nth_error_lookup in Hinstn.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [], (hs, upd_s_mem ws (update_list_at (s_mems ws) n m'), locs, inst), [].
    repeat split => //.
    by eapply r_store_success.
  - iIntros "!>" (es σ2 efs HStep).
    (* Need something like gen_heap_update_big here to update all at once *)
    iMod (gen_heap_update_big_wm with "Hm Hwmdata") as "(Hm & Hwmdata)".
    iModIntro.
    destruct σ2 as [[[hs2 ws2] locs2] winst2].
    destruct HStep as [HStep [-> ->]].
    eapply reduce_det in HStep; last by eapply r_store_success.
    inversion HStep; subst; clear HStep => /=.
    iFrame.
    rewrite update_list_at_insert; last by rewrite nth_error_lookup in Hm; apply lookup_lt_Some in Hm.
    erewrite gmap_of_memory_insert_block => //; [ idtac | by rewrite - nth_error_lookup | by apply store_length in Hstore'; lia ].
    rewrite list_fmap_insert.
    assert (mem_length m' = mem_length m) as Hmsize.
    { apply store_length in Hstore'. by unfold mem_length, memory_list.mem_length; rewrite Hstore'. }
    rewrite Hmsize.
    assert (mem_length mem' = mem_length mem) as Hmsize'.
    { apply mem_equiv_length in Hmem.
      apply mem_equiv_length in Hmdata'.
      lia.
    }
    rewrite Hmsize'.
    rewrite list_insert_id; last by rewrite list_lookup_fmap; rewrite - nth_error_lookup; rewrite Hm.
    rewrite Hmdata' Hwmlength'.
    by iFrame.
Qed.
    
Lemma wp_current_memory (s: stuckness) (E: coPset) (k: nat) (n: N) (inst: instance) (mem: memory) (ϕ: val -> Prop) :
  inst.(inst_memory) !! 0 = Some k ->
  ϕ (immV [(VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (N.div n page_size))))]) ->
  ( ↦[wi] inst ∗
   (N.of_nat k) ↦[wmlength] n) ⊢
   WP ([AI_basic (BI_current_memory)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ ↦[wi] inst ∗ (N.of_nat k) ↦[wmlength] n }}.
Proof.
  iIntros (Hi Hϕ) "[Hinst Hmemlength]".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & Hm & ? & ? & Hi & Hγ)".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  iDestruct (gen_heap_valid with "Hγ Hmemlength") as "%Hmemlength".
  rewrite lookup_insert in Hinst.
  inversion Hinst; subst; clear Hinst.
  rewrite - nth_error_lookup in Hi.
  rewrite gmap_of_list_lookup list_lookup_fmap Nat2N.id in Hmemlength => /=.
  destruct (s_mems ws !! k) eqn:Hmemlookup => //.
  rewrite - nth_error_lookup in Hmemlookup.
  simpl in Hmemlength.
  inversion Hmemlength; clear Hmemlength.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (N.div n page_size)))))], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_current_memory => //.
    unfold mem_size.
    by f_equal.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last eapply r_current_memory; eauto.
    inversion H; subst; clear H.
    unfold mem_size.
    by iFrame => //=.
Qed.

Lemma reduce_grow_memory hs ws f c hs' ws' f' es' k mem mem':
  f.(f_inst).(inst_memory) !! 0 = Some k ->
  nth_error (s_mems ws) k = Some mem ->
  reduce hs ws f [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_grow_memory)] hs' ws' f' es' ->
  ((hs', ws', f', es') = (hs, ws, f, [AI_basic (BI_const (VAL_int32 int32_minus_one))] ) \/
   (hs', ws', f', es') = (hs, (upd_s_mem ws (update_list_at (s_mems ws) k mem')), f, [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))))]) /\
  mem_grow mem (Wasm_int.N_of_uint i32m c) = Some mem').
Proof.
  move => Hinst Hmem HReduce.
  destruct f as [locs inst].
  destruct f' as [locs' inst'].
  (*only_one_reduction HReduce [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))))] locs inst locs' inst'.*)
Admitted.

Lemma wp_grow_memory (s: stuckness) (E: coPset) (k: nat) (n: N) (inst: instance) (mem: memory) (Φ Ψ: val -> iProp Σ) (c: i32) :
  inst.(inst_memory) !! 0 = Some k ->
  match mem_max_opt mem with
  | Some maxlim => (mem_size mem + (Wasm_int.N_of_uint i32m c) <=? maxlim)%N
  | None => true
  end ->
  (Φ (immV [VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))]) ∗
  (Ψ (immV [VAL_int32 int32_minus_one])) ∗
   ↦[wi] inst ∗
     (N.of_nat k) ↦[wmblock] mem ) ⊢ WP ([AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_grow_memory)]) @ s; E {{ w, ((Φ w ∗ (N.of_nat k) ↦[wmblock] {| mem_data:= {| ml_init := ml_init mem.(mem_data); ml_data := ml_data mem.(mem_data) ++ repeat (#00)%byte (N.to_nat ((Wasm_int.N_of_uint i32m c) * page_size)) |}; mem_max_opt:= mem_max_opt mem |}) ∨ (Ψ w ∗ (N.of_nat k) ↦[wmblock] mem)) ∗ ↦[wi] inst  }}.
Proof.
  iIntros (Hi Hmsizelim) "(HΦ & HΨ & Hinst & Hmemblock)".
  iDestruct "Hmemblock" as "(Hmemdata & Hmemlength)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & Hm & ? & ? & Hi & Hγ)".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  iDestruct (gen_heap_valid with "Hγ Hmemlength") as "%Hmemlength".
  rewrite lookup_insert in Hinst.
  inversion Hinst; subst; clear Hinst.
  rewrite - nth_error_lookup in Hi.
  rewrite gmap_of_list_lookup list_lookup_fmap Nat2N.id in Hmemlength => /=.
  destruct (s_mems ws !! k) eqn:Hmemlookup => //.
  simpl in Hmemlength.
  inversion Hmemlength as [Hmemlength']; clear Hmemlength.
  iAssert ( (∀ i, ⌜(ml_data (mem_data mem)) !! i = (ml_data (mem_data m)) !! i ⌝)%I) as "%Hmeq".
  {
    iIntros (i).
    destruct (ml_data (mem_data mem) !! i) eqn:Hmd.
    - iDestruct (big_sepL_lookup with "Hmemdata") as "H" => //.
      iDestruct (gen_heap_valid with "Hm H") as "%H".
      rewrite gmap_of_list_2d_lookup list_lookup_fmap Nat2N.id Hmemlookup in H.
      unfold memory_to_list in H.
      simpl in H.
      by rewrite Nat2N.id in H.
    - apply lookup_ge_None in Hmd.
      iPureIntro.
      symmetry.
      apply lookup_ge_None.
      unfold mem_length, memory_list.mem_length in Hmemlength'.
      lia.
  }
  iAssert (⌜mem ≡ₘm⌝%I) as "%Hmem".
  {
    unfold mem_block_equiv.
    by rewrite (list_eq (ml_data (mem_data mem)) (ml_data (mem_data m))).
  }
  iSplit.
  assert (exists mem', mem_grow mem (Wasm_int.N_of_uint i32m c) = Some mem') as [mem' Hmem'].
  { unfold mem_grow.
    destruct (mem_max_opt mem) eqn:Hmaxsize; eexists => //.
    by rewrite Hmsizelim.
  }
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))))], (hs, (upd_s_mem ws (update_list_at (s_mems ws) k mem')), locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_grow_memory_success => //.
    rewrite - nth_error_lookup in Hmemlookup.
    rewrite Hmemlookup.
    f_equal.
  (* There's a small bug in memory_list: mem_grow should not be using ml_init but #00 instead. Finish this when that is fixed *)
    admit.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    (* DO NOT USE reduce_det here -- grow_memory is NOT determinstic. *)
    eapply reduce_grow_memory in H; [ idtac | by rewrite - nth_error_lookup | by rewrite nth_error_lookup ].
    destruct H as [HReduce | [HReduce Hmem']]; inversion HReduce; subst; clear HReduce; iFrame.
    (* failure *)
    + iSplit => //.
      iRight.
      iFrame.
      by rewrite Hmemlength'.
    (* success *)
    + admit.
Admitted.






End lifting.

(* What should a function spec look like?
  A (Wasm) function closure is of the form

    FC_func_native inst ft vts bes

  but this is not an expression nor a value, so we need to define our custom version of wp for it, like

    ▷ WP (FC_func_native inst ft vts bes) {{ v, Φ v }}.

    ( Would WP bes {{ ... }} be enough? )

  to express our function specs.

  What should such a wp require (to be established), and how to use it? 

  Given a spec in the above form, we expect to be able to use it to
    figure out a spec for Invoke i, when s.funcs[i] is a Wasm function...
 
  s.funcs[a] = FC_func_native i (Tf t1s t2s) ts bes ->
  f' = {| inst := i; locs := vcs ++ zs |} ->
  ... ->
  (hs, s, f, ves ++ [AI_invoke a]) ↪ 
  (hs, s, f, [AI_local m f' [AI_basic (BI_block (Tf [] t2s) bes)]])

Lemma invoke_native_spec `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ, !wlocsG Σ} (s : stuckness) (E : coPset) (Φs: list (val -> iProp Σ)) inst ft vts bes :
  [∗ list] i ↦ Φ ∈ Φs, (i ↦[wf] FC_func_native inst ft vts bes ∗ □ (WP (FC_func_native inst ft vts bes)
*)

End Host.

Local Hint Resolve language.val_irreducible : core.
Local Hint Resolve to_of_val : core.
Local Hint Unfold language.irreducible : core.

