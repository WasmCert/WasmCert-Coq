From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules.
Require Export datatypes host operations properties opsem typing.
Require Export iris_logrel.
Import uPred.

Section fundamental.
  Import DummyHosts. (* placeholder *)

  Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.

  Ltac take_drop_app_rewrite n :=
    match goal with
    | |- context [ WP ?e @ _; _ CTX _; _ {{ _ }} %I ] =>
        rewrite -(list.take_drop n e);simpl take; simpl drop
    | |- context [ WP ?e @ _; _ {{ _ }} %I ] =>
        rewrite -(list.take_drop n e);simpl take; simpl drop
    | |- context [ WP ?e @ _; _ FRAME _; _ CTX _; _  {{ _, _ }} %I ] =>
        rewrite -(list.take_drop n e);simpl take; simpl drop
    | |- context [ WP ?e @ _; _ FRAME _; _ {{ _ }} %I ] =>
        rewrite -(list.take_drop n e);simpl take; simpl drop
    end.
  
  Ltac take_drop_app_rewrite_twice n m :=
    take_drop_app_rewrite n;
    match goal with
    | |- context [ WP _ ++ ?e @ _; _ CTX _; _ {{ _ }} %I ] =>
        rewrite -(list.take_drop (length e - m) e);simpl take; simpl drop
    | |- context [ WP _ ++ ?e @ _; _ {{ _ }} %I ] =>
        rewrite -(list.take_drop (length e - m) e);simpl take; simpl drop
    end.

  Lemma interp_value_type_of v : (⊢ interp_value (Σ:=Σ) (typeof v) v)%I.
  Proof.
    unfold interp_value.
    destruct v;simpl;eauto.
  Qed.
    
  Theorem be_fundamental C es τ : be_typing C es τ -> ⊢ semantic_typing (HWP:=HWP) C (to_e_list es) τ.
  Proof.
    induction 1.
    
    {
      unfold semantic_typing, interp_expression.
      iIntros (i lh f vs).
      destruct C,i.
      iIntros "(#Hi & Hf & %Hlh) #Hv".
      iDestruct "Hf" as (locs Heq) "[#Hlocs Hf]".
      iDestruct "Hv" as "[-> | Hv]".
      { take_drop_app_rewrite_twice 0 1.
        iApply (wp_wand_r _ _ _ (λ vs, interp_val [typeof v] vs ∗  ↪[frame]f)%I). iSplitL.
        { iApply (wp_trap with "[] [$]");auto. by iLeft. }
        iIntros (v0) "[? ?]". iFrame. iExists _. iFrame. }
      { iDestruct "Hv" as (ws ->) "Hv".
        iDestruct (big_sepL2_nil_inv_r with "Hv") as %->.
        iApply (wp_wand_r _ _ _ (λ vs, interp_val [typeof v] vs ∗  ↪[frame]f)%I). iSplitL.
        { rewrite app_nil_l.
          iApply wp_value;[by instantiate (1:= immV [_])|].
          iFrame. iRight. iExists _. iSplit;eauto.
          iSimpl; iSplit =>//. iApply interp_value_type_of. }
        iIntros (v0) "[? ?]". iFrame. iExists _. iFrame. 
      }
    }


    12: {
      unfold semantic_typing, interp_expression.
      iIntros (i lh f vs).
      destruct C,i.
      set (C := {|
                 tc_types_t := tc_types_t;
                 tc_func_t := tc_func_t;
                 tc_global := tc_global;
                 tc_table := tc_table;
                 tc_memory := tc_memory;
                 tc_local := tc_local;
                 tc_label := tc_label;
                 tc_return := tc_return
               |}
          ).
      set (i := {|
                 inst_types := inst_types;
                 inst_funcs := inst_funcs;
                 inst_tab := inst_tab;
                 inst_memory := inst_memory;
                 inst_globs := inst_globs
               |}).
      iIntros "(#Hi & Hf & %Hlh) #Hv".
      iDestruct "Hv" as "[-> | Hv]".
      { iDestruct "Hf" as (locs Heq) "[#Hlocs Hf]". 
        take_drop_app_rewrite_twice 0 1.
        iApply (wp_wand_r _ _ _ (λ vs, interp_val tm vs ∗  ↪[frame]f)%I). iSplitL.
        { iApply (wp_trap with "[] [$]");auto. by iLeft. }
        iIntros (v0) "[? ?]". iFrame. iExists _. iFrame. }
      iDestruct "Hv" as (ws ->) "Hv".
      iDestruct (big_sepL2_length with "Hv") as %Hlen.
      iDestruct "Hf" as (locs Heq) "[#Hlocs Hf]".
      iApply (wp_loop with "Hf");eauto.
      { apply v_to_e_is_const_list. }
      { rewrite fmap_length //. }
      iNext. iIntros "Hf".
      iDestruct (IHbe_typing with "[Hf] []") as "HH".
      { iFrame "# ∗". unfold interp_ctx. simpl. instantiate (1:=LH_rec (of_val (immV ws)) (length tn) _ lh _).
        iSplit;[iExists _;eauto|].
        iPureIntro. destruct Hlh as [Hbase Hlenh]. auto. }
      { instantiate (1:=immV ws). iRight. eauto. }
      iApply wp_wasm_empty_ctx.
      iApply wp_label_push_nil. iSimpl.
      unfold interp_expression,interp_val.
      iAssert (WP of_val (immV ws) ++ to_e_list es
                  {{ vs, ⌜vs = trapV⌝ ∗ (∃ f0 : leibnizO frame,  ↪[frame]f0) }} ∨
              WP of_val (immV ws) ++ to_e_list es
                 {{ vs, (∃ ws0 : seq.seq (leibnizO value), ⌜vs = immV ws0⌝ ∗ ([∗ list] w;τ ∈ ws0;tm, interp_value τ w))
                          ∗ (∃ f0 : leibnizO frame,  ↪[frame]f0) }})%I with "[HH]" as "HHH".
      { }

      
      iApply wp_seq_ctx.

      iDestruct "HH" as (f0) "HH". iExists f0.
      


      
      iDestruct (IHbe_typing with "[Hf] []") as "HH".
      { iFrame "# ∗". unfold interp_ctx. simpl. instantiate (1:=LH_rec (of_val (immV ws)) (length tn) _ lh _).
        iPureIntro. destruct Hlh as [Hbase Hlen]. auto. }
      { instantiate (1:=immV ws). iRight. eauto. }
      iDestruct "HH" as (f0) "HH". iExists f0.
      iDestruct (big_sepL2_length with "Hv") as %Hlen.
      iApply wp_loop;eauto.
      { apply v_to_e_is_const_list. }
      { rewrite fmap_length //. }
      { eauto. } apply const_list_of_val.
     


End fundamental.
