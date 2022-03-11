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

  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Lemma interp_instance_get_mem C i :
    tc_memory C ≠ [] ->
    ⊢ interp_instance (HWP:=HWP) C i -∗
      ∃ τm mem, ⌜nth_error (tc_memory C) 0 = Some τm⌝
              ∗ ⌜nth_error (inst_memory i) 0 = Some mem⌝
              ∗ interp_mem τm (N.of_nat mem).
  Proof.
    destruct C,i.
    iIntros (Hnil) "[_ [_ [ _ [#Hi _]]]]".
    iSimpl.
    simpl in Hnil.
    destruct tc_memory;try done.
    iSimpl in "Hi".
    destruct inst_memory;try done.
    iExists _,_. repeat iSplit;eauto.
  Qed.
    
  (* ----------------------------------------- LOAD ---------------------------------------- *)

  Lemma typing_load C a tp_sx t off : tc_memory C ≠ [] ->
                        load_store_t_bounds a (option_projl tp_sx) t ->
                        ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_load t tp_sx a off]) (Tf [T_i32] [t]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hnil Hload i lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|w ws];[done|destruct ws;[|done]].
    iSimpl in "Hv". iDestruct "Hv" as "[Hv _]".
    iDestruct "Hv" as (z) "->".
    iSimpl.

    iDestruct (interp_instance_get_mem with "Hi") as (τm mem Hlook1 Hlook2) "#Hm";auto.
    iApply fupd_wp.
    iDestruct "Hfv" as (locs Hlocs) "[#Hlocs Hown]".
    iMod (na_inv_acc with "Hm Hown") as "(Hms & Hown & Hcls)";[solve_ndisj..|].
    iDestruct "Hms" as (ms) "[>Hmemblock >%Hmemtyping]".
    iDestruct "Hmemblock" as "[Hmem Hsize]".

    destruct tp_sx.
    { (* it is a packed load *)
      admit.
    }

    { (* it is a regular load *)
      admit.
    }

  Admitted.
    

End fundamental.
