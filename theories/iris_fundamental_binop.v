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
Require Export iris_logrel iris_fundamental_helpers.
Import uPred.

Section fundamental.
  Import DummyHosts. (* placeholder *)

  Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* ----------------------------------------- BINOP --------------------------------------- *)
  
  Lemma binop_type_agree_interp t op w1 w2 :
    binop_type_agree t op →
    ⊢ interp_value (Σ:=Σ) t w1 -∗
    interp_value t w2 -∗
    ∀ w, ⌜app_binop op w1 w2 = Some w⌝ -∗ interp_value t w.
  Proof.
    iIntros (Hbinop) "Hw1 Hw2".
    inversion Hbinop.
    { iDestruct "Hw1" as (w1') "->".
      iDestruct "Hw2" as (w2') "->".
      iIntros (w Happ).
      cbn in Happ.
      destruct op0;unfold option_map in Happ;simplify_eq;eauto.
      { destruct s;eauto.
        { destruct (Wasm_int.Int32.idiv_s w1' w2');simplify_eq;eauto. }
        { destruct (Wasm_int.Int32.idiv_u w1' w2');simplify_eq;eauto. }
      }
      { destruct s;eauto.
        { destruct (Wasm_int.Int32.irem_s w1' w2');simplify_eq;eauto. }
        { destruct (Wasm_int.Int32.irem_u w1' w2');simplify_eq;eauto. }
      }
      { destruct s;eauto.
        { destruct (Wasm_int.Int32.shr w1' w2');simplify_eq;eauto. }
        { destruct (Wasm_int.Int32.ishr_u w1' w2');simplify_eq;eauto. }
      }
    }
    { iDestruct "Hw1" as (w1') "->".
      iDestruct "Hw2" as (w2') "->".
      iIntros (w Happ).
      destruct op0;simpl in Happ;simplify_eq;eauto.
      { unfold option_map in Happ.
        destruct s;eauto.
        { destruct (Wasm_int.Int64.idiv_s w1' w2');simplify_eq;eauto. }
        { destruct (Wasm_int.Int64.idiv_u w1' w2');simplify_eq;eauto. }
      }
      { unfold option_map in Happ.
        destruct s;eauto.
        { destruct (Wasm_int.Int64.irem_s w1' w2');simplify_eq;eauto. }
        { destruct (Wasm_int.Int64.irem_u w1' w2');simplify_eq;eauto. }
      }
      { unfold option_map in Happ.
        destruct s;eauto.
        { destruct (Wasm_int.Int64.shr w1' w2');simplify_eq;eauto. }
        { destruct (Wasm_int.Int64.ishr_u w1' w2');simplify_eq;eauto. }
      }
    }
    { iDestruct "Hw1" as (w1') "->".
      iDestruct "Hw2" as (w2') "->".
      iIntros (w Happ).
      destruct op0;simpl in Happ;simplify_eq;eauto. }
    { iDestruct "Hw1" as (w1') "->".
      iDestruct "Hw2" as (w2') "->".
      iIntros (w Happ).
      destruct op0;simpl in Happ;simplify_eq;eauto. }
  Qed.
    
  Lemma typing_binop C t op : binop_type_agree t op ->
                              ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_binop t op]) (Tf [t; t] [t]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hbinop i lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]".
    iIntros (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    { iDestruct "Hv" as (ws ->) "Hv".
      iDestruct (big_sepL2_length with "Hv") as %Hlen.
      destruct ws as [|w1 ws];[done|destruct ws as [|w2 ws];[done|destruct ws;[|done]]].
      iSimpl in "Hv".
      iDestruct "Hv" as "[Hv1 [Hv2 _]]".

      destruct (app_binop op w1 w2) eqn:Hsome.
      
      { iSimpl.
        iApply (wp_wand _ _ _ (λ v, ⌜v = immV [from_option id w1 (app_binop op w1 w2)]⌝ ∗ ↪[frame] f)%I with "[Hf]").
        { iApply (wp_binop with "Hf");eauto. rewrite Hsome. eauto. }
        iIntros (w0) "[-> Hf]".
        iSplitR;[|iExists _;iFrame].
        iLeft. iRight.
        iExists _. iSplit;auto.
        iSimpl. iSplit =>//. iApply (binop_type_agree_interp with "Hv1 Hv2");eauto.
        rewrite Hsome. eauto. }

      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iSimpl.
        iApply wp_binop_failure;auto. }
      { iIntros (v) "[-> Hf]". iSplitR;[|iExists _;iFrame]. iLeft. by iLeft. }
    }
  Qed.

  
End fundamental.
