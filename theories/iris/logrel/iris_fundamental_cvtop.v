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


  Context `{!wasmG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Lemma interp_value_cvt t1 sx w1 v :
    cvt t1 sx w1 = Some v ->
    ⊢ interp_value (Σ:=Σ) t1 v.
  Proof.
    iIntros (Hcvt).
    unfold interp_value.
    unfold cvt in Hcvt.
    destruct t1,v;eauto.
    all: unfold option_map in Hcvt.
    all: (destruct (cvt_i32 sx w1);done) +
           (destruct (cvt_i64 sx w1);done) +
           (destruct (cvt_f32 sx w1);done) +
           (destruct (cvt_f64 sx w1);done) + auto.
  Qed.

  Lemma interp_value_reinterpret t1 w1 :
    ⊢ interp_value (Σ:=Σ) t1 (wasm_deserialise (bits w1) t1).
  Proof.
    destruct t1;simpl;eauto.
  Qed.
    
  (* ----------------------------------------- CVTOP --------------------------------------- *)

  Lemma typing_cvtop_convert C t1 t2 sx : ⊢ semantic_typing (* HWP:=HWP*) C (to_e_list [BI_cvtop t1 CVO_convert t2 sx]) (Tf [t2] [t1]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (i lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|w1 ws];[done|destruct ws;[|done]].
    iSimpl in "Hv".
    iDestruct "Hv" as "[Hv1 _]".
    iSimpl.
    
    iApply (wp_wand _ _ _ (λne vs, interp_val [t1] vs ∗ ↪[frame] f)%I with "[Hf]").
    { iAssert (⌜types_agree t2 w1⌝)%I as %Htyp.
      { destruct t2. all:iDestruct "Hv1" as (?) "->";eauto. }
      destruct (cvt t1 sx w1) eqn:Hsome.      
      { iApply (wp_cvtop_convert with "Hf");eauto.
        iSimpl. iRight. iExists _. iSplit;eauto.
        iSimpl. iSplit;[|done]. iApply interp_value_cvt. eauto. }
      { iApply (wp_cvtop_convert_failure with "Hf");eauto.
        iSimpl. by iLeft. }
    }

    iIntros (v) "[H Hf]".
    iFrame. iExists _. iFrame.
  Qed.

  Lemma typing_cvtop_reinterpret C t1 t2 : ⊢ semantic_typing (*HWP:=HWP*) C (to_e_list [BI_cvtop t1 CVO_reinterpret t2 None]) (Tf [t2] [t1]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (i lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|w1 ws];[done|destruct ws;[|done]].
    iSimpl in "Hv".
    iDestruct "Hv" as "[Hv1 _]".
    iSimpl.
    
    iApply (wp_wand _ _ _ (λne vs, interp_val [t1] vs ∗ ↪[frame] f)%I with "[Hf]").
    { iAssert (⌜types_agree t2 w1⌝)%I as %Htyp.
      { destruct t2. all:iDestruct "Hv1" as (?) "->";eauto. }
      iApply (wp_cvtop_reinterpret with "Hf");eauto.
      iSimpl. iRight. iExists _. iSplit;eauto.
      iSimpl. iSplit;[|done]. iApply interp_value_reinterpret.
    }

    iIntros (v) "[H Hf]".
    iFrame. iExists _. iFrame.
  Qed.


End fundamental.
