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

  (* --------------------------------------- GROW_MEMORY ----------------------------------- *)

  Lemma typing_grow_memory C : tc_memory C ≠ [] ->
                               ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_grow_memory]) (Tf [T_i32] [T_i32]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hnil i lh).
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
    rewrite nth_error_lookup in Hlook1.
    rewrite nth_error_lookup in Hlook2.
    iApply fupd_wp.
    iDestruct "Hfv" as (locs Hlocs) "[#Hlocs Hown]".
    iMod (na_inv_acc with "Hm Hown") as "(Hms & Hown & Hcls)";[solve_ndisj..|].
    iDestruct "Hms" as (ms) "[>Hmemblock >%Hmemtyping]".
    iDestruct "Hmemblock" as "[Hmem Hsize]".
    iModIntro.

    iApply wp_fupd.
    iApply (wp_wand _ _ _ (λ vs, ((⌜vs = immV _⌝ ∗ _) ∨ (⌜vs = immV _⌝ ∗ _))∗ _)%I with "[Hsize Hf]").
    { iApply (wp_grow_memory with "[$Hf $Hsize]");[by rewrite Hlocs /=|].
      iSplit;eauto. }
    iIntros (v) "[Hdisj Hf]".
    iDestruct "Hdisj" as "[[-> [Hb Hsize]]|[-> Hsize]]".
    { iDestruct "Hb" as (b) "Hb".
      iMod ("Hcls" with "[$Hown Hsize Hmem Hb]") as "Hown".
      { iNext.
        set (mem' := {| ml_init := ml_init (mem_data ms) ;
                       ml_data := ml_data (mem_data ms) ++
                                  repeat b (N.to_nat (Wasm_int.N_of_uint i32m z * page_size))|}).
        iExists {| mem_data := mem' ;
                  mem_max_opt := (mem_max_opt ms) |}.
        unfold mem_block. simpl ml_data.
        rewrite big_sepL_app.
        iFrame. iSplitL;[iSplitL "Hb"|].
        { iApply (big_sepL_mono with "Hb").
          iIntros (k y Hy). iSimpl. iIntros "H".
          rewrite Nat2N.id. iFrame. }
        { unfold mem_length, memory_list.mem_length. simpl ml_data.
          rewrite app_length repeat_length.
          assert ((N.of_nat (length (ml_data (mem_data ms))) +
                     Wasm_int.N_of_uint i32m z * page_size)%N =
                    N.of_nat (length (ml_data (mem_data ms)) +
                      N.to_nat (Z.to_N (Wasm_int.Int32.unsigned z) * page_size))) as ->;[simpl;lia|iFrame]. }
        { iPureIntro.
          unfold mem_typing, mem', mem_size, mem_length, memory_list.mem_length.
          unfold mem_typing, mem', mem_size, mem_length, memory_list.mem_length in Hmemtyping. simpl in *.
          rewrite app_length repeat_length.
          revert Hmemtyping. move/andP=>[Hle Hcond]. apply/andP. split;auto.
          apply N.leb_le in Hle. apply N.leb_le.
          rewrite Nat2N.inj_add N2Nat.id.
          rewrite N.div_add;[lia|]. unfold page_size. lia.
        }
      }
      iSplitR;[|iExists _;iFrame;iExists _;eauto].
      iModIntro. iLeft;iRight.
      iExists _;iSplit;[eauto|].
      iSimpl. iSplit =>//. iExists _;eauto.
    }
    { iMod ("Hcls" with "[$Hown Hsize Hmem]") as "Hown".
      { iNext. iExists _. iFrame. auto. }
      iSplitR;[|iExists _;iFrame;iExists _;eauto].
      iModIntro. iLeft;iRight.
      iExists _;iSplit;[eauto|].
      iSimpl. iSplit =>//. iExists _;eauto.
    }
  Qed.    

End fundamental.
