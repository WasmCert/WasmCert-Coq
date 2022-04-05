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

  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !wtablimitG Σ, !wmemlimitG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Definition update_list_range {A : Type} (l l' : list A) (i : nat) :=
    (take i l) ++ l' ++ (drop (i + length l') l).

  Lemma update_list_range_length {A : Type} (l l' : list A) (i : nat) :
    i + length l' <= length l ->
    length l = length (update_list_range l l' i).
  Proof.
    revert l' i.
    induction l;intros l' i.
    { rewrite /update_list_range /= drop_nil take_nil.
      destruct i,l';simpl; try lia. }
    { destruct i;intros Hl';simpl in *.
      { destruct l';[done|].
        simpl in Hl'.
        rewrite /update_list_range /=. f_equiv.
        unfold update_list_range in IHl. 
        pose proof (IHl l' 0).
        rewrite /update_list_range /= in H. rewrite H;auto;lia. }
      { f_equiv. apply IHl. lia. }
    }
  Qed.

  Lemma update_list_range_lookup {A : Type}  (l l' : list A) (i : nat) (a : A) :
    i + length l' <= length l ->
    l' !! 0 = Some a ->
    update_list_range l l' i !! i = Some a.
  Proof.
    revert l' i.
    induction l;intros l' i.
    { rewrite /update_list_range /= drop_nil take_nil.
      intros Hi Hl'. destruct i,l';try done. lia. }
    { destruct i;intros Hl';simpl in *.
      { destruct l';[done|].
        simpl in Hl'.
        rewrite /update_list_range /=. auto. }
      { intros Hl. apply IHl;eauto. lia. }
    }
  Qed.
    
  Lemma mem_extract_insert_mid (len : nat) ml_data (start : N) m (cond : N -> Prop) :
    (∀ a, start <= a ∧ a < start + N.of_nat len -> cond a)%N ->
    len > 0
    → (N.of_nat (length ml_data) >= start + N.of_nat len)%N
    → ⊢ ([∗ list] i↦b ∈ ml_data, ⌜cond (N.of_nat i)⌝ → m↦[wm][N.of_nat i]b) -∗
        ∃ bv : bytes, m↦[wms][start]bv ∗
         (∀ bv', ⌜length bv = length bv'⌝ -∗
                  m↦[wms][start] bv' -∗ [∗ list] i↦b ∈ update_list_range ml_data bv' (N.to_nat start), ⌜cond (N.of_nat i)⌝ → m↦[wm][N.of_nat i]b) ∗
          ⌜length bv = len⌝.
  Proof.
    revert ml_data start m cond.
    iInduction len as [|len] "IH";iIntros (ml_data start m cond Hcond Hgt Hbounds) "Hm";[lia|].
    assert (is_Some (ml_data !! N.to_nat start)) as [x Hx].
    { apply lookup_lt_is_Some_2.
      rewrite /mem_length /memory_list.mem_length /= in Hbounds. lia. }
    unfold mem_block_at_pos;simpl.
    destruct len.
    { iDestruct (big_sepL_insert_acc with "Hm") as "[Hm Hcls]";[apply Hx|].
      iSpecialize ("Hm" with "[]").
      { iPureIntro. apply Hcond. lia. }
      iExists [x]. iSimpl. rewrite PeanoNat.Nat.add_0_r.
      rewrite N2Nat.id.
      iFrame. iSplit =>//.
      iIntros (vs' Hlen') "Hm".
      destruct vs' as [|w vs'];[done|destruct vs';[|done]].
      unfold update_list_range. iSimpl in "Hm".
      iDestruct "Hm" as "[Hm _]". rewrite PeanoNat.Nat.add_0_r N2Nat.id.
      iDestruct ("Hcls" with "[Hm]") as "HH";[iIntros (_);iFrame|].
      rewrite list.insert_take_drop;[|lia].
      rewrite separate1 Nat.add_1_r. iFrame. }    

    iDestruct (big_sepL_delete' with "Hm") as "[Hm Hcls]";[apply Hx|].
    
    iDestruct ("IH" $! ml_data (start + 1)%N m (λ (i : N), start ≠ i ∧ cond i) with "[] [] [] [Hcls]") as "HH";try (iPureIntro;lia).
    { iPureIntro. intros. split;[lia|]. apply Hcond. lia. }
    { iApply (big_sepL_mono with "Hcls");iIntros (y k Hy) "H".
      iIntros ([Hy1 Hy2]). iApply "H";iPureIntro;auto; lia. }
    iDestruct "HH" as (bv) "[Hm1 [HH %Hlen]]".
    iExists (x :: bv). simpl.
    rewrite PeanoNat.Nat.add_0_r N2Nat.id.
    iSpecialize ("Hm" with "[]").
    { iPureIntro. apply Hcond. lia. }
    iFrame.
    iSplitL "Hm1".
    { iApply (big_sepL_mono with "Hm1");iIntros (y k Hy) "H".
      assert (N.of_nat (N.to_nat start + S y) = N.of_nat (N.to_nat (start + 1) + y)) as ->;[|iFrame].
      lia. }
    iSplitL;[|iPureIntro;lia].
    iIntros (bv' Hbvlen) "Hy".
    destruct bv';[done|]. simpl in Hbvlen. inversion Hbvlen.
    iSimpl in "Hy". iDestruct "Hy" as "[Hy Hm]".
    iDestruct ("HH" with "[] [Hm]") as "HH";[eauto|..].
    { iApply (big_sepL_mono with "Hm");iIntros (y k Hy) "H".
      assert (N.of_nat (N.to_nat start + S y) = N.of_nat (N.to_nat (start + 1) + y)) as ->;[|iFrame].
      lia. }
    iApply big_sepL_delete';[apply update_list_range_lookup;eauto;simpl;rewrite -H0 Hlen;lia|].
    rewrite PeanoNat.Nat.add_0_r.
    iSplitL "Hy";[iIntros (_);rewrite N2Nat.id;eauto|].
    rewrite /update_list_range /=.
    iApply big_sepL_app. simpl.
    iDestruct (big_sepL_app with "HH") as "[H1 H2]".
    iSplitL "H1".
    { rewrite -(take_drop (N.to_nat start) (take (N.to_nat (start + 1)) ml_data)).
      iDestruct (big_sepL_app with "H1") as "[H1 _]".
      rewrite take_take. assert (N.to_nat start `min` N.to_nat (start + 1) = N.to_nat start) as ->;[lia|].
      iApply (big_sepL_mono with "H1").
      iIntros (y k Hy) "H".
      iIntros (Hcond1 Hcond2);iApply "H";iPureIntro;split;auto. lia. } 
    iSplitR "H2".
    { rewrite take_length. iIntros (Hcontr). exfalso. lia. }
    rewrite !take_length.
    assert (N.to_nat (start + 1) + length bv' = N.to_nat start + S (length bv')) as ->;[lia|].
    iApply (big_sepL_mono with "H2").
    iIntros (y k Hy) "H".
    assert (N.of_nat (N.to_nat start `min` length ml_data + S y) =
              N.of_nat (N.to_nat (start + 1) `min` length ml_data + y)) as ->;[lia|].
    iIntros (Hcond1 Hcond2). iApply "H". iPureIntro. split;[lia|auto].
  Qed.

  Lemma mem_extract_insert ms start len m :
    len > 0  ->
    (mem_length ms >= start + N.of_nat len)%N ->
    ⊢ ([∗ list] i↦b ∈ ml_data (mem_data ms), m ↦[wm][N.of_nat i] b) -∗
      (∃ bv, m ↦[wms][ start ] bv ∗
        (∀ bv', ⌜length bv = length bv'⌝ -∗ m ↦[wms][ start ] bv' -∗
                [∗ list] i↦b ∈ update_list_range (ml_data (mem_data ms)) bv' (N.to_nat start), m ↦[wm][N.of_nat i] b) ∗
            ⌜length bv = len⌝).
  Proof.
    destruct ms. simpl in *.
    destruct mem_data. simpl.
    unfold mem_length,memory_list.mem_length;simpl.
    iIntros (Hlt Hbounds) "Hm".
    iDestruct (big_sepL_cond_impl with "Hm") as "Hm".
    iDestruct (mem_extract_insert_mid _ _ _ _ (λ _, True) with "[Hm]") as "Hm";eauto.
    iDestruct "Hm" as (bv) "[? [H ?]]".
    iExists _. iFrame. iIntros (? ?) "?".
    iApply big_sepL_cond_impl. iApply "H";iFrame. auto.
  Qed.

  (* ----------------------------------------- STORE --------------------------------------- *)

  Lemma typing_store C a tp t off : tc_memory C ≠ [] ->
                                    load_store_t_bounds a tp t ->
                                    ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_store t tp a off]) (Tf [T_i32; t] []).
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
    destruct ws as [|w ws];[done|destruct ws as [|w1 ws];[done|destruct ws;[|done]]].
    iSimpl in "Hv". iDestruct "Hv" as "[Hv [Hv1 _]]".
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

    iAssert (⌜types_agree t w1⌝)%I as %Htypes.
    { destruct t;iDestruct "Hv1" as (z') "->";eauto. }

    destruct tp.
    { (* it is a packed store *)
      assert (tp_length p < t_length t) as Hlt.
      { rewrite /= in Hload. revert Hload. move/andP =>[Hload Hint].
        revert Hload. move/andP =>[Ha Htp].
        revert Htp. move/ssrnat.leP;lia. }

      destruct (N_lt_dec (mem_length ms) ((Wasm_int.N_of_uint i32m z) + off + (N.of_nat (tp_length p))))%N.
      { iApply wp_fupd.
        iApply (wp_wand _ _ _ (λ vs, (⌜vs = trapV⌝ ∗ _) ∗ _)%I with "[Hsize Hf]").
        { iApply (wp_store_packed_failure with "[$Hf $Hsize]");[|by rewrite Hlocs /=|by apply N.lt_gt|];auto. }
        iIntros (v) "[[-> Hsize] Hf]".
        iMod ("Hcls" with "[$Hown Hsize Hmem]") as "Hown".
        { iNext. iExists _. iFrame. }
        iModIntro.
        iSplitR;[by iLeft; iLeft|iExists _;iFrame].
        iExists _. eauto. 
      }
      { iDestruct (mem_extract_insert _ (Wasm_int.N_of_uint i32m z + off) (tp_length p) with "Hmem") as (bv) "[Ha [Hmem %Hlenbv]]";[destruct p;simpl;lia|lia|].
        iApply wp_fupd.
        iApply (wp_wand _ _ _ (λ vs, (⌜vs = immV _⌝ ∗ _) ∗ _)%I with "[Ha Hf]").
        { iApply (wp_store_packed with "[$Hf $Ha]");eauto. by rewrite Hlocs /=. }
        iIntros (v) "[[-> Ha] Hf]".
        iDestruct ("Hmem" with "[] Ha") as "Hmem".
        { rewrite length_bytes_takefill Hlenbv. auto. }

        (* closing the invariant requires showing that its size has not changed *)
        iMod ("Hcls" with "[$Hown Hsize Hmem]") as "Hown".
        { iNext. unfold mem_block.
          set (mem' := {| ml_init := ml_init (mem_data ms) ;
                         ml_data := update_list_range (ml_data (mem_data ms))
                                                      (bytes_takefill #00%byte (tp_length p) (bits w1))
                                                      (N.to_nat (Wasm_int.N_of_uint i32m z + off)) |}).
          iExists {| mem_data := mem' ;
                    mem_max_opt := (mem_max_opt ms) |}.
          iFrame. unfold mem_length, memory_list.mem_length. iSimpl.
          rewrite -update_list_range_length;[iFrame|].
          { rewrite length_bytes_takefill. simpl in n.
            unfold mem_length, memory_list.mem_length in n. lia. }
        }
        iModIntro.
        iSplitR;[iLeft; iRight|iExists _;iFrame;iExists _;eauto].
        iExists _. iSplit;[eauto|]. done.
      }
    }

    { destruct (N_lt_dec (mem_length ms) ((Wasm_int.N_of_uint i32m z) + off + (N.of_nat (t_length t))))%N.
      { iApply wp_fupd.
        iApply (wp_wand _ _ _ (λ vs, (⌜vs = trapV⌝ ∗ _) ∗ _)%I with "[Hsize Hf]").
        { iApply (wp_store_failure with "[$Hf $Hsize]");[|by rewrite Hlocs /=|by apply N.lt_gt|];auto. }
        iIntros (v) "[[-> Hsize] Hf]".
        iMod ("Hcls" with "[$Hown Hsize Hmem]") as "Hown".
        { iNext. iExists _. iFrame. }
        iModIntro.
        iSplitR;[by iLeft; iLeft|iExists _;iFrame].
        iExists _. eauto. 
      }
      { iDestruct (mem_extract_insert _ (Wasm_int.N_of_uint i32m z + off) (t_length t) with "Hmem") as (bv) "[Ha [Hmem %Hlenbv]]";[destruct t;simpl;lia|lia|].
        iApply wp_fupd.
        iApply (wp_wand _ _ _ (λ vs, (⌜vs = immV _⌝ ∗ _) ∗ _)%I with "[Ha Hf]").
        { iApply (wp_store with "[$Hf $Ha]");eauto. by rewrite Hlocs /=. }
        iIntros (v) "[[-> Ha] Hf]".
        iDestruct ("Hmem" with "[] Ha") as "Hmem".
        { erewrite length_bits;eauto. }

        (* closing the invariant requires showing that its size has not changed *)
        iMod ("Hcls" with "[$Hown Hsize Hmem]") as "Hown".
        { iNext. unfold mem_block.
          set (mem' := {| ml_init := ml_init (mem_data ms) ;
                         ml_data := update_list_range (ml_data (mem_data ms))
                                                      (bits w1)
                                                      (N.to_nat (Wasm_int.N_of_uint i32m z + off)) |}).
          iExists {| mem_data := mem' ;
                    mem_max_opt := (mem_max_opt ms) |}.
          iFrame. unfold mem_length, memory_list.mem_length. iSimpl.
          rewrite -update_list_range_length;[iFrame|].
          { erewrite length_bits;[|eauto]. simpl in n.
            unfold mem_length, memory_list.mem_length in n. lia. }
        }
        iModIntro.
        iSplitR;[iLeft; iRight|iExists _;iFrame;iExists _;eauto].
        iExists _. iSplit;[eauto|]. done.
      }
    }

  Qed.

    
    

End fundamental.
