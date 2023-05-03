From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Require Export iris_logrel iris_fundamental_helpers.
Import uPred.
  
Section fundamental.


  Context `{!wasmG Σ, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Lemma mem_extract_mid (len : nat) ml_data (start : N) m (cond : N -> Prop) :
    (∀ a, start <= a ∧ a < start + N.of_nat len -> cond a)%N ->
    len > 0
    → (N.of_nat (length ml_data) >= start + N.of_nat len)%N
    → ⊢ ([∗ list] i↦b ∈ ml_data, ⌜cond (N.of_nat i)⌝ → m↦[wm][N.of_nat i]b) -∗
        ∃ bv : bytes, m↦[wms][start]bv ∗
          (m↦[wms][start]bv -∗ [∗ list] i↦b ∈ ml_data, ⌜cond (N.of_nat i)⌝ → m↦[wm][N.of_nat i]b) ∗
          ⌜length bv = len⌝.
  Proof.
    revert ml_data start m cond.
    iInduction len as [|len] "IH";iIntros (ml_data start m cond Hcond Hgt Hbounds) "Hm";[lia|].
    assert (is_Some (ml_data !! N.to_nat start)) as [x Hx].
    { apply lookup_lt_is_Some_2.
      rewrite /mem_length /memory_list.mem_length /= in Hbounds. lia. }
    unfold mem_block_at_pos;simpl.
    iDestruct (big_sepL_delete' with "Hm") as "[Hm Hcls]";[apply Hx|].
    iSpecialize ("Hm" with "[]").
    { iPureIntro. apply Hcond. lia. }
    destruct len.
    { iExists [x]. iSimpl. rewrite PeanoNat.Nat.add_0_r.
      rewrite N2Nat.id.
      iFrame. iSplit =>//.
      iIntros "[Hm _]".
      iDestruct (big_sepL_delete' with "[$Hcls Hm]") as "$";eauto. rewrite N2Nat.id;auto. }
    rewrite N2Nat.id.
    iDestruct ("IH" $! ml_data (start + 1)%N m (λ (i : N), start ≠ i ∧ cond i) with "[] [] [] [Hcls]") as "HH";try (iPureIntro;lia).
    { iPureIntro. intros. split;[lia|]. apply Hcond. lia. }
    { iApply (big_sepL_mono with "Hcls");iIntros (y k Hy) "H".
      iIntros ([Hy1 Hy2]). iApply "H";iPureIntro;auto; lia. }
    iDestruct "HH" as (bv) "[Hm1 [HH %Hlen]]".
    iExists (x :: bv). simpl.
    rewrite PeanoNat.Nat.add_0_r N2Nat.id.
    iFrame.
    iSplitL "Hm1".
    { iApply (big_sepL_mono with "Hm1");iIntros (y k Hy) "H".
      assert (N.of_nat (N.to_nat start + S y) = N.of_nat (N.to_nat (start + 1) + y)) as ->;[|iFrame].
      lia. }
    iSplitL;[|iPureIntro;lia].
    iIntros "[Hy H]".
    iDestruct ("HH" with "[H]") as "HH".
    { iApply (big_sepL_mono with "H");iIntros (y k Hy) "H".
      assert (N.of_nat (N.to_nat start + S y) = N.of_nat (N.to_nat (start + 1) + y)) as ->;[|iFrame].
      lia. }
    iApply big_sepL_delete';eauto.
    iSplitL "Hy";[iIntros (_);rewrite N2Nat.id;eauto|].
    iApply (big_sepL_mono with "HH");iIntros (y k Hy) "H".
    iIntros (? ?). iApply "H". iPureIntro. split;auto. lia.
  Qed.

  Lemma mem_extract ms start len m :
    len > 0  ->
    (mem_length ms >= start + N.of_nat len)%N ->
    ⊢ ([∗ list] i↦b ∈ ml_data (mem_data ms), m ↦[wm][N.of_nat i] b) -∗
      (∃ bv, m ↦[wms][ start ] bv ∗
            (m ↦[wms][ start ] bv -∗ [∗ list] i↦b ∈ ml_data (mem_data ms), m ↦[wm][N.of_nat i] b) ∗
            ⌜length bv = len⌝).
  Proof.
    destruct ms. simpl in *.
    destruct mem_data. simpl.
    unfold mem_length,memory_list.mem_length;simpl.
    iIntros (Hlt Hbounds) "Hm".
    iDestruct (big_sepL_cond_impl with "Hm") as "Hm".
    iDestruct (mem_extract_mid _ _ _ _ (λ _, True) with "[Hm]") as "Hm";eauto.
    iDestruct "Hm" as (bv) "[? [H ?]]".
    iExists _. iFrame. iIntros "?".
    iApply big_sepL_cond_impl. iApply "H";iFrame.
  Qed.
    
    
  (* ----------------------------------------- LOAD ---------------------------------------- *)

  Lemma typing_load C a tp_sx t off : tc_memory C ≠ [] ->
                        load_store_t_bounds a (option_projl tp_sx) t ->
                        ⊢ semantic_typing C (to_e_list [BI_load t tp_sx a off]) (Tf [T_i32] [t]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hnil Hload i lh hl).
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

    iDestruct (interp_instance_get_mem with "Hi") as (τm mem Hlook1 Hlook2) "[_ #Hm]";auto.
    rewrite nth_error_lookup in Hlook1.
    rewrite nth_error_lookup in Hlook2.
    iApply fupd_wp.
    iDestruct "Hfv" as (locs Hlocs) "[#Hlocs Hown]".
    iMod (na_inv_acc with "Hm Hown") as "(Hms & Hown & Hcls)";[solve_ndisj..|].
    iDestruct "Hms" as (ms) ">Hmemblock".
    iDestruct "Hmemblock" as "[Hmem Hsize]".
    iModIntro.

    destruct tp_sx.
    { (* it is a packed load *)
      destruct p.

      destruct (N_lt_dec (mem_length ms) ((Wasm_int.N_of_uint i32m z) + off + (N.of_nat (tp_length p))))%N.
      { iApply wp_fupd.
        iApply (wp_wand _ _ _ (λ vs, (⌜vs = trapV⌝ ∗ _) ∗ _)%I with "[Hsize Hf]").
        { by iApply (wp_load_packed_failure with "[$Hf $Hsize]");[by rewrite Hlocs /=|by apply N.lt_gt|]. }
        iIntros (v) "[[-> Hsize] Hf]".
        iMod ("Hcls" with "[$Hown Hsize Hmem]") as "Hown".
        { iNext. iExists _. iFrame. }
        iModIntro.
        iSplitR;[by iLeft; iLeft|iExists _;iFrame].
        iExists _. eauto. 
      }
      { iDestruct (mem_extract _ (Wasm_int.N_of_uint i32m z + off) (tp_length p) with "Hmem") as (bv) "[Ha [Hmem %Hlenbv]]";[destruct p;simpl;lia|lia|].
        iApply wp_fupd.
        iApply (wp_wand _ _ _ (λ vs, (⌜vs = immV _⌝ ∗ _) ∗ _)%I with "[Ha Hf]").
        { iApply (wp_load_packed_deserialize with "[$Hf $Ha]");eauto;by rewrite Hlocs /=. }
        iIntros (v) "[[-> Ha] Hf]".
        iDestruct ("Hmem" with "Ha") as "Hmem".
        iMod ("Hcls" with "[$Hown Hsize Hmem]") as "Hown".
        { iNext. iExists _. iFrame. }
        iModIntro.
        iSplitR;[iLeft; iRight|iExists _;iFrame;iExists _;eauto].
        iExists _. iSplit;[eauto|]. iSimpl.
        iSplit =>//. unfold interp_value.
        destruct t;iSimpl;eauto.
      }
    }

    { (* it is a regular load *)
      
      destruct (N_lt_dec (mem_length ms) ((Wasm_int.N_of_uint i32m z) + off + (N.of_nat (t_length t))))%N.
      { iApply wp_fupd.
        iApply (wp_wand _ _ _ (λ vs, (⌜vs = trapV⌝ ∗ _) ∗ _)%I with "[Hsize Hf]").
        { by iApply (wp_load_failure with "[$Hf $Hsize]");[by rewrite Hlocs /=|by apply N.lt_gt|]. }
        iIntros (v) "[[-> Hsize] Hf]".
        iMod ("Hcls" with "[$Hown Hsize Hmem]") as "Hown".
        { iNext. iExists _. iFrame. }
        iModIntro.
        iSplitR;[by iLeft; iLeft|iExists _;iFrame].
        iExists _. eauto. 
      }
      { iDestruct (mem_extract _ (Wasm_int.N_of_uint i32m z + off) (t_length t) with "Hmem") as (bv) "[Ha [Hmem %Hlenbv]]";[destruct t;simpl;lia|lia|].
        iApply wp_fupd.
        iApply (wp_wand _ _ _ (λ vs, (⌜vs = immV _⌝ ∗ _) ∗ _)%I with "[Ha Hf]").
        { iApply (wp_load_deserialize with "[$Hf $Ha]");eauto;by rewrite Hlocs /=. }
        iIntros (v) "[[-> Ha] Hf]".
        iDestruct ("Hmem" with "Ha") as "Hmem".
        iMod ("Hcls" with "[$Hown Hsize Hmem]") as "Hown".
        { iNext. iExists _. iFrame. }
        iModIntro.
        iSplitR;[iLeft; iRight|iExists _;iFrame;iExists _;eauto].
        iExists _. iSplit;[eauto|]. iSimpl.
        iSplit =>//. unfold interp_value.
        destruct t;iSimpl;eauto.
      }

    }
  Qed.

End fundamental.
