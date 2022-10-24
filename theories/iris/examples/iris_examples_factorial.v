From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules iris_example_helper iris_host proofmode.
Require Export datatypes operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

(* Example Programs *)
Section Factorial.
  Context `{!wasmG Σ}.

  (* --------------------------------------------------------------------------------------------- *)
  (* ------------------------- LOCAL STATE EXAMPLE: FACTORIAL ------------------------------------ *)
  (* --------------------------------------------------------------------------------------------- *)

  Definition factorial_instrs fact : seq.seq basic_instruction :=
    [(BI_get_local 0);
     (BI_const (xx 1));
     (BI_relop T_i32 (Relop_i (ROI_le SX_U)));
     (BI_if (Tf [] [T_i32])
        [BI_const (xx 1)]
        
        [BI_get_local 0;
         BI_const (xx 1);
         BI_binop T_i32 (Binop_i BOI_sub);
         BI_call fact;
         BI_get_local 0;
         BI_binop T_i32 (Binop_i BOI_mul)])].
  Definition factorial fact := to_e_list (factorial_instrs fact).

  Lemma factPred:
    ∀ n : nat, 1 < n -> ssrnat.muln n (ssrnat.factorial (n - 1)) = (ssrnat.factorial n).
  Proof.
    intros n Hlt.
    induction n. lia.
    destruct n;[lia|].
    destruct n;auto.
  Qed.

  Definition fact_val n : val -> iProp Σ := λ v, ⌜v = immV [xx (ssrnat.factorial (Wasm_int.nat_of_uint i32m n))]⌝%I.

  Lemma factorial_spec fact (n : Equality.sort i32) i a :
    (ssrnat.factorial (Wasm_int.nat_of_uint i32m n) < Wasm_int.Int32.modulus)%Z -> (* no overflow *)
    inst_funcs i !! fact = Some a -> (* factorial function is in the instance *)
    (0 <= (Wasm_int.Int32.intval n))%Z -> (* the parameter must be positive *)
    
    ↪[frame] Build_frame [VAL_int32 n] i -∗
    (N.of_nat a) ↦[wf] (FC_func_native i (Tf [T_i32] [T_i32]) [] (factorial_instrs fact)) -∗
    WP factorial fact {{ v, (fact_val n v
                             ∗ (N.of_nat a) ↦[wf] (FC_func_native i (Tf [T_i32] [T_i32]) [] (factorial_instrs fact)))
                             ∗ ↪[frame] Build_frame [VAL_int32 n] i }}.
  Proof.
    iLöb as "IH" forall (n).
  { (* { is to fix annoying indent problem... *)
    iIntros (Hoverflow Hle Ha) "Hf Hi".
    rewrite /factorial.
    iSimpl.
    set f := {| f_locs := [VAL_int32 n]; f_inst := i |}.
    match goal with
    | |- context [ (▷ ?H)%I ] => set IH := H
    end.

    (* get_local 0 *)
    take_drop_app_rewrite 1.
    iApply (wp_seq _ _ _ (λ v', ⌜v' = immV _⌝ ∗ ↪[frame] f)%I).
    iSplitR;[by iIntros "[%Hcontr _]"|].
    iSplitL "Hf".
    { iApply (wp_get_local with "[] [$]"). unfold f. eauto.
      simpl. eauto. }
    
    (* le *)
    iIntros (w) "[-> Hf] /=".
    take_drop_app_rewrite 3.
    iApply (wp_seq _ _ _ (λ v', ⌜v' = immV [_]⌝ ∗ ↪[frame] f)%I).
    iSplitR;[by iIntros "[%Hcontr _]"|].
    iSplitL "Hf".
    { iApply (wp_relop with "[$]"). eauto. eauto. }

    (* br if *)
    iIntros (w) "[-> Hf] /=".
    (* case distinction *)
    destruct (~~ Wasm_int.Int32.ltu (Wasm_int.Int32.repr 1) n) eqn:Hbool;simpl.
    { (* base case: n <= 1 *)
      (* setup the true branch *)
      apply negb_true in Hbool.
      iApply (wp_if_true with "[$]");[auto|]. simpl.
      iNext. iIntros "Hf".
      iApply iRewrite_nil_l.
      iApply (wp_block with "[$]");eauto.
      iNext. iIntros "Hf".
      iApply wp_wasm_empty_ctx.
      iApply wp_label_push_nil. simpl.

      (* return from block *)
      iApply (wp_val_return with "[$]");auto.

      (* halt and post condition *)
      iIntros "Hf".
      simpl. iApply (iris_wp.wp_value _ _ _ _ (immV ([xx 1]))). by cbv.
      iFrame. iPureIntro. f_equiv. f_equiv.
      unfold xx. f_equiv. f_equiv. clear -Hle Hbool.
      destruct n;simpl in *.
      unfold Wasm_int.Int32.ltu in Hbool. simpl in *.
      destruct (Coqlib.zlt 1 intval);[done|].
      assert (intval = 1 ∨ intval = 0);[lia|].
      destruct H as [-> | ->];lias. }

    { (* inductive step *)
      (* setup the false branch *)
      apply negbFE in Hbool.
      iApply (wp_if_false with "[$]");[auto|].
      iNext. iIntros "Hf".
      iApply iRewrite_nil_l.
      iApply (wp_block with "[$]");eauto.
      iNext. iIntros "Hf".
      iApply wp_wasm_empty_ctx.
      iApply wp_label_push_nil. simpl.

      (* get_local 0 *)
      take_drop_app_rewrite 1.
      iApply (wp_seq_ctx _ _ _ (λ v', ⌜v' = immV _⌝ ∗ ↪[frame] f)%I).
      iSplitR; [by iIntros "[%Hcontr _]"|].
      iSplitL "Hf".
      { iApply (wp_get_local with "[] [$]"). unfold f. eauto.
        simpl. eauto. }

      (* sub *)
      iIntros (w) "[-> Hf] /=".
      take_drop_app_rewrite 3.
      iApply (wp_seq_ctx _ _ _ (λ v', ⌜v' = immV _⌝ ∗ ↪[frame] f)%I).
      iSplitR; [by iIntros "[%Hcontr _]"|].
      iSplitL "Hf".
      { iApply (wp_binop with "[$]"). eauto. eauto. }

      (* recursive call *)
      simpl.
      iIntros (w) "[-> Hf] /=".
      take_drop_app_rewrite 2.
      iApply (wp_seq_ctx _ _ _ (λ v', (⌜v' = immV _⌝ ∗ N.of_nat a ↦[wf] _) ∗ ↪[frame] f)%I).
      iSplitR; [by iIntros "[[%Hcontr _] _]"|].
      iSplitL.
      { (* call *)
        iApply wp_wasm_empty_ctx.
        take_drop_app_rewrite_twice 1 0.
        iApply wp_base_push;auto. simpl.
        iApply (wp_call_ctx with "[$]"). unfold f. simpl. eauto.
        iNext. iIntros "Hf".

        (* invoke native *)
        iApply wp_base. simpl.
        take_drop_app_rewrite 1.
        iApply (wp_invoke_native with "Hf Hi");eauto.
        iNext. iIntros "[Hf Hi]".
        simpl.

        (* scope change before invoking the IH *)
        rewrite -wp_frame_rewrite.
        iApply wp_wasm_empty_ctx_frame.
        take_drop_app_rewrite 1.
        iApply (wp_seq_ctx_frame _ _ _ (λ v', ⌜v' = immV _⌝ ∗ N.of_nat a ↦[wf] _)%I with "[$Hf Hi]").
        { intros LI HLI%lfilled_Ind_Equivalent. inversion HLI;subst. cbn. auto. }
        iSplitR; [by iIntros "[%Hcontr _]"|].
        iSplitL.
        { (* focus on block *)
          iIntros "Hf".
          take_drop_app_rewrite 0.
          iApply (wp_block with "[$]");eauto.
          iNext. iIntros "Hf".
          iApply wp_wasm_empty_ctx.
          assert ([] ++ to_e_list (factorial_instrs fact) =
                    ([] ++ to_e_list (factorial_instrs fact) ++ []))%SEQ as ->;[auto|].
          iApply wp_label_push;auto.
          iApply iRewrite_nil_r_ctx.
          iApply wp_seq_ctx.
          iSplitR;cycle 1.
          { iSplitL. (* apply IH *)
            unfold IH.
            iApply ("IH" with "[] [] [] Hf Hi");auto.
            - iPureIntro.
              (* prove that (n - 1) does not overflow *)
              clear -Ha Hbool Hoverflow.
              destruct n. simpl in *.
              unfold Wasm_int.Int32.ltu in Hbool. simpl in *.
              destruct (Coqlib.zlt 1 intval);[|done].
              rewrite Wasm_int.Int32.Z_mod_modulus_eq Zmod_small;try lia.
              rewrite Z2Nat.inj_sub;[|lia].
              rewrite (Nat2Z.id 1).
              apply Zmult_gt_0_lt_reg_r with (p:=intval). lia.
              assert ((ssrnat.factorial (Z.to_nat intval - 1) * intval)%Z
                      = ssrnat.muln (Z.to_nat intval) (ssrnat.factorial (Z.to_nat intval - 1))) as Heq.
              { unfold ssrnat.muln. unfold ssrnat.muln_rec. lia. }
              rewrite Heq factPred;[|lia]. etrans. apply Hoverflow.
              apply Z.lt_mul_diag_r;lia.
              
            - iPureIntro.
              (* prove that (n - 1) is gt 0 *)
              clear -Ha Hbool.
              destruct n. simpl in *.
              unfold Wasm_int.Int32.ltu in Hbool. simpl in *.
              destruct (Coqlib.zlt 1 intval);[|done].
              rewrite Wasm_int.Int32.Z_mod_modulus_eq Zmod_small;lia.

            - (* return *)
              iIntros (w) "[[-> Hi] Hf] /=".
              iApply (wp_val_return with "[$] [Hi]"). auto.
              iIntros "Hf /=".
              iApply iris_wp.wp_value. instantiate (1 := immV [_]). reflexivity.
              iFrame. eauto. }
          { simpl. by iIntros "[[%Hcontr _] _]". } }

        (* return to outer scope *)
        iIntros (w) "[[-> Hi] Hf] /=".
        iApply wp_wasm_empty_ctx_frame.
        rewrite wp_frame_rewrite.
        iApply (wp_frame_value with "[$Hf]"); eauto.
      }
      
      (* finish program after call *)
      iIntros (w) "[[-> Hi] Hf] /=".
      
      (* get_local 0 *)
      take_drop_app_rewrite_twice 1 1.
      iApply wp_base_push;auto.
      take_drop_app_rewrite 1.
      iApply (wp_seq_ctx _ _ _ (λ v', ⌜v' = immV _⌝ ∗ ↪[frame]f)%I).
      iSplitR;[by iIntros "[%Hcontr _]"|].
      iSplitL "Hf".
      { iApply (wp_get_local with "[] [$Hf]"). eauto. simpl. eauto. }

      (* mul *)
      iIntros (w) "[-> Hf] /=".
      iApply wp_base_pull. simpl.
      take_drop_app_rewrite 3.
      iApply (wp_seq_ctx _ _ _ (λ v', ⌜v' = immV _⌝ ∗ ↪[frame] f)%I).
      iSplitR;[by iIntros "[%Hcontr _]"|].
      iSplitL "Hf".
      { iApply (wp_binop with "[$]"). simpl. eauto. eauto. }

      (* return *)
      iIntros (w) "[-> Hf] /=".
      iApply (wp_val_return with "[$]");auto.
      iIntros "Hf /=".

      (* postcondition *)
      iApply iris_wp.wp_value. instantiate (1 := immV [_]). reflexivity.
      iFrame. iPureIntro.

      unfold xx.
      repeat f_equiv.
      unfold Wasm_int.Int32.imul, Wasm_int.Int32.mul. simpl.
      f_equiv.
      clear -Ha Hbool Hoverflow.
      unfold Wasm_int.Int32.ltu in Hbool.
      destruct n;simpl in *.
      destruct (Coqlib.zlt 1 intval);[|done].
      rewrite !Wasm_int.Int32.Z_mod_modulus_eq.
      assert ((intval - 1) `mod` Wasm_int.Int32.modulus = intval - 1)%Z as ->.
      { rewrite Zmod_small;lia. }
      rewrite Z2Nat.inj_sub;[|lia].
      rewrite (Nat2Z.id 1).
      assert ((ssrnat.factorial (Z.to_nat intval - 1) * intval)%Z
              = ssrnat.muln (Z.to_nat intval) (ssrnat.factorial (Z.to_nat intval - 1))) as Heq.
      { unfold ssrnat.muln. unfold ssrnat.muln_rec. lia. }
      rewrite Zmod_small.
      rewrite Heq factPred;lia.
      split. lia.
      apply Zmult_gt_0_lt_reg_r with (p:=intval). lia.
      rewrite Heq factPred. 2: lia.
      etrans. apply Hoverflow.
      apply Z.lt_mul_diag_r;lia.
  } }
  Qed.

  Lemma invoke_factorial_spec fact (n : Equality.sort i32) i a f0 :
    (ssrnat.factorial (Wasm_int.nat_of_uint i32m n) < Wasm_int.Int32.modulus)%Z -> (* no overflow *)
    inst_funcs i !! fact = Some a -> (* factorial function is in the instance *)
    (0 <= (Wasm_int.Int32.intval n))%Z -> (* the parameter must be positive *)
    
    ↪[frame] f0 -∗
    (N.of_nat a) ↦[wf] (FC_func_native i (Tf [T_i32] [T_i32]) [] (factorial_instrs fact)) -∗
    WP [AI_basic (BI_const (VAL_int32 n));
        AI_invoke a]
    {{ v, (⌜v = immV [xx (ssrnat.factorial (Wasm_int.nat_of_uint i32m n))]⌝
            ∗ (N.of_nat a) ↦[wf] (FC_func_native i (Tf [T_i32] [T_i32]) [] (factorial_instrs fact)))
            ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hoverflow Hi Hpos) "Hf Hi".
    take_drop_app_rewrite 1.
    iApply (wp_invoke_native with "[$] [$]");eauto.
    iNext. iIntros "[Hf Hi]".
    rewrite /= -wp_frame_rewrite.
    iApply wp_wasm_empty_ctx_frame.
    take_drop_app_rewrite 1.
    iApply (wp_seq_ctx_frame _ _ _ (λ v, fact_val n v ∗ (N.of_nat a) ↦[wf] _)%I with "[$Hf Hi]").
    { intros LI HLI%lfilled_Ind_Equivalent. inversion HLI;subst. cbn. auto. }
    iSplitR;[by iIntros "[%Hcontr _]"|].
    iSplitL.
    { iIntros "Hf".
      take_drop_app_rewrite 0.
      iApply (wp_block with "[$]");eauto.
      iNext. iIntros "Hf".
      erewrite app_nil_l.
      iApply wp_wasm_empty_ctx.
      iApply wp_label_push_nil. simpl push_base.
      take_drop_app_rewrite (length (factorial_instrs fact)).
      iApply (wp_seq_ctx _ _ _ (λ v, (fact_val n v ∗ (N.of_nat a) ↦[wf] _) ∗ ↪[frame] _)%I).
      iSplitR;[by iIntros "[[%Hcontr _] _]"|].
      iSplitL.
      { iApply (factorial_spec with "[$] [$]");eauto. }
      iIntros (w) "[[%Hfact Hi] Hf] /=".
      iApply (wp_val_return with "[$]");[subst;auto|].
      iIntros "Hf /=".
      iApply iris_wp.wp_value. instantiate (1:=immV [_]). subst;done.
      iFrame. auto. }
    iIntros (w) "[[%Hfact Hi] Hf]".
    iApply wp_wasm_empty_ctx_frame.
    iApply (wp_frame_value with "[$]"); [subst;eauto..|].
    iNext.
    iFrame. auto.
  Qed.

End Factorial.

Section Factorial.
  Context `{!wasmG Σ}.
  
  (* --------------------------------------------------------------------------------------------- *)
  (* ------------------------- LANDIN'S KNOT EXAMPLE: FACTORIAL ---------------------------------- *)
  (* --------------------------------------------------------------------------------------------- *)


  Definition myrec_instr h_mut_tab :=
    [BI_const (xx 0);
     BI_get_local 0;
     BI_call h_mut_tab].
  Definition myrec h_mut_tab := to_e_list (myrec_instr h_mut_tab).

  Definition F_instr rec_typ :=
    [(BI_get_local 0);
     (BI_const (xx 1));
     (BI_relop T_i32 (Relop_i (ROI_le SX_U)));
     (BI_if (Tf [] [T_i32])
        [BI_const (xx 1)]
        
        [BI_get_local 0;
         BI_const (xx 1);
         BI_binop T_i32 (Binop_i BOI_sub);
         BI_const (xx 0);
         BI_call_indirect rec_typ;
         BI_get_local 0;
         BI_binop T_i32 (Binop_i BOI_mul)])].
  Definition F rec_typ :=
    to_e_list (F_instr rec_typ).

  Definition fact_instr F myrec fact_typ :=
    [BI_get_local 0;
     BI_const F;
     BI_call myrec;
     BI_const (xx 0);
     BI_call_indirect fact_typ].
  Definition fact F myrec fact_typ :=
    to_e_list (fact_instr F myrec fact_typ).

  
  Lemma F_spec fact rec_typ tab (n : Equality.sort i32) i a :
    (ssrnat.factorial (Wasm_int.nat_of_uint i32m n) < Wasm_int.Int32.modulus)%Z -> (* no overflow *)
    (0 <= (Wasm_int.Int32.intval n))%Z -> (* the parameter must be positive *)

    inst_funcs i !! fact = Some a -> (* factorial function is in the instance *)
    inst_types i !! rec_typ = Some (Tf [T_i32] [T_i32]) ->
    inst_tab i !!  0 = Some tab ->
    
    ↪[frame] Build_frame [VAL_int32 n] i -∗
    (N.of_nat tab) ↦[wt][N.of_nat (yy 0)] Some a -∗
    (N.of_nat a) ↦[wf] (FC_func_native i (Tf [T_i32] [T_i32]) [] (F_instr rec_typ)) -∗
    WP F rec_typ {{ v, (fact_val n v
                             ∗ (N.of_nat tab) ↦[wt][N.of_nat (yy 0)] Some a 
                             ∗ (N.of_nat a) ↦[wf] (FC_func_native i (Tf [T_i32] [T_i32]) [] (F_instr rec_typ)))
                             ∗ ↪[frame] Build_frame [VAL_int32 n] i }}.
  Proof.
    iLöb as "IH" forall (n).
  { (* { is to fix annoying indent problem... *)
    iIntros (Hoverflow Hle Ha Htyp Htab) "Hf Htab Hi".
    rewrite /F.
    iSimpl.
    set f := {| f_locs := [VAL_int32 n]; f_inst := i |}.
    match goal with
    | |- context [ (▷ ?H)%I ] => set IH := H
    end.

    (* get_local 0 *)
    take_drop_app_rewrite 1.
    iApply (wp_seq _ _ _ (λ v', ⌜v' = immV _⌝ ∗ ↪[frame] f)%I).
    iSplitR;[by iIntros "[%Hcontr _]"|].
    iSplitL "Hf".
    { iApply (wp_get_local with "[] [$]"). unfold f. eauto.
      simpl. eauto. }
    
    (* le *)
    iIntros (w) "[-> Hf] /=".
    take_drop_app_rewrite 3.
    iApply (wp_seq _ _ _ (λ v', ⌜v' = immV [_]⌝ ∗ ↪[frame] f)%I).
    iSplitR;[by iIntros "[%Hcontr _]"|].
    iSplitL "Hf".
    { iApply (wp_relop with "[$]"). eauto. eauto. }

    (* br if *)
    iIntros (w) "[-> Hf] /=".
    (* case distinction *)
    destruct (~~ Wasm_int.Int32.ltu (Wasm_int.Int32.repr 1) n) eqn:Hbool;simpl.
    { (* base case: n <= 1 *)
      (* setup the true branch *)
      apply negb_true in Hbool.
      iApply (wp_if_true with "[$]");[auto|]. simpl.
      iNext. iIntros "Hf".
      iApply iRewrite_nil_l.
      iApply (wp_block with "[$]");eauto.
      iNext. iIntros "Hf".
      iApply wp_wasm_empty_ctx.
      iApply wp_label_push_nil. simpl.

      (* return from block *)
      iApply (wp_val_return with "[$]");auto.

      (* halt and post condition *)
      iIntros "Hf".
      simpl. iApply (iris_wp.wp_value _ _ _ _ (immV ([xx 1]))). by cbv.
      iFrame. iPureIntro. f_equiv. f_equiv.
      unfold xx. f_equiv. f_equiv. clear -Hle Hbool.
      destruct n;simpl in *.
      unfold Wasm_int.Int32.ltu in Hbool. simpl in *.
      destruct (Coqlib.zlt 1 intval);[done|].
      assert (intval = 1 ∨ intval = 0);[lia|].
      destruct H as [-> | ->];lias. }

    { (* inductive step *)
      (* setup the false branch *)
      apply negbFE in Hbool.
      iApply (wp_if_false with "[$]");[auto|].
      iNext. iIntros "Hf".
      iApply iRewrite_nil_l.
      iApply (wp_block with "[$]");eauto.
      iNext. iIntros "Hf".
      iApply wp_wasm_empty_ctx.
      iApply wp_label_push_nil. simpl.

      (* get_local 0 *)
      take_drop_app_rewrite 1.
      iApply (wp_seq_ctx _ _ _ (λ v', ⌜v' = immV _⌝ ∗ ↪[frame] f)%I).
      iSplitR; [by iIntros "[%Hcontr _]"|].
      iSplitL "Hf".
      { iApply (wp_get_local with "[] [$]"). unfold f. eauto.
        simpl. eauto. }

      (* sub *)
      iIntros (w) "[-> Hf] /=".
      take_drop_app_rewrite 3.
      iApply (wp_seq_ctx _ _ _ (λ v', ⌜v' = immV _⌝ ∗ ↪[frame] f)%I).
      iSplitR; [by iIntros "[%Hcontr _]"|].
      iSplitL "Hf".
      { iApply (wp_binop with "[$]"). eauto. eauto. }

      (* recursive call: now happens indirectly through the higher order store *)
      simpl.
      iIntros (w) "[-> Hf] /=".
      take_drop_app_rewrite 3.
      iApply (wp_seq_ctx _ _ _ (λ v', (⌜v' = immV _⌝ ∗ N.of_nat tab↦[wt][0%N]Some a ∗ N.of_nat a ↦[wf] _) ∗ ↪[frame] f)%I).
      iSplitR; [by iIntros "[[%Hcontr _] _]"|].
      iSplitL.
      { (* call *)
        iApply wp_wasm_empty_ctx.
        take_drop_app_rewrite_twice 1 0.
        iApply wp_base_push;auto. simpl.
        iApply (wp_call_indirect_success_ctx with "[Htab] [$] [$]");auto. unfold f. simpl. eauto.
        iNext. iIntros "[Htab [Hi Hf]]".

        (* invoke native *)
        iApply wp_base. simpl.
        take_drop_app_rewrite 1.
        iApply (wp_invoke_native with "Hf Hi");eauto.
        iNext. iIntros "[Hf Hi]".
        simpl.

        (* scope change before invoking the IH *)
        rewrite -wp_frame_rewrite.
        iApply wp_wasm_empty_ctx_frame.
        take_drop_app_rewrite 1.
        iApply (wp_seq_ctx_frame _ _ _ (λ v', ⌜v' = immV _⌝ ∗ N.of_nat tab ↦[wt][0%N]Some a ∗ N.of_nat a ↦[wf] _)%I with "[$Hf Hi Htab]").
        { intros LI HLI%lfilled_Ind_Equivalent. inversion HLI;subst. cbn. auto. }
        iSplitR; [by iIntros "[%Hcontr _]"|].
        iSplitL.
        { (* focus on block *)
          iIntros "Hf".
          take_drop_app_rewrite 0.
          iApply (wp_block with "[$]");eauto.
          iNext. iIntros "Hf".
          iApply wp_wasm_empty_ctx.
          assert ([] ++ to_e_list (F_instr rec_typ) =
                    ([] ++ to_e_list (F_instr rec_typ) ++ []))%SEQ as ->;[auto|].
          iApply wp_label_push;auto.
          iApply iRewrite_nil_r_ctx.
          iApply wp_seq_ctx.
          iSplitR;cycle 1.
          { iSplitL. (* apply IH *)
            unfold IH.
            iApply ("IH" with "[] [] [] [] [] Hf Htab Hi");auto.
            - iPureIntro.
              (* prove that (n - 1) does not overflow *)
              clear -Ha Hbool Hoverflow.
              destruct n. simpl in *.
              unfold Wasm_int.Int32.ltu in Hbool. simpl in *.
              destruct (Coqlib.zlt 1 intval);[|done].
              rewrite Wasm_int.Int32.Z_mod_modulus_eq Zmod_small;try lia.
              rewrite Z2Nat.inj_sub;[|lia].
              rewrite (Nat2Z.id 1).
              apply Zmult_gt_0_lt_reg_r with (p:=intval). lia.
              assert ((ssrnat.factorial (Z.to_nat intval - 1) * intval)%Z
                      = ssrnat.muln (Z.to_nat intval) (ssrnat.factorial (Z.to_nat intval - 1))) as Heq.
              { unfold ssrnat.muln. unfold ssrnat.muln_rec. lia. }
              rewrite Heq factPred;[|lia]. etrans. apply Hoverflow.
              apply Z.lt_mul_diag_r;lia.
              
            - iPureIntro.
              (* prove that (n - 1) is gt 0 *)
              clear -Ha Hbool.
              destruct n. simpl in *.
              unfold Wasm_int.Int32.ltu in Hbool. simpl in *.
              destruct (Coqlib.zlt 1 intval);[|done].
              rewrite Wasm_int.Int32.Z_mod_modulus_eq Zmod_small;lia.

            - (* return *)
              iIntros (w) "[[-> [Htab Hi]] Hf] /=".
              iApply (wp_val_return with "[$] [Hi Htab]"). auto.
              iIntros "Hf /=".
              iApply iris_wp.wp_value. instantiate (1 := immV [_]). reflexivity.
              iFrame. eauto. }
          { simpl. by iIntros "[[%Hcontr _] _]". } }

        (* return to outer scope *)
        iIntros (w) "[[-> [Htab Hi]] Hf] /=".
        iApply wp_wasm_empty_ctx_frame.
        rewrite wp_frame_rewrite.
        iApply (wp_frame_value with "[$Hf]"); eauto. iFrame. eauto.
      }
      
      (* finish program after call *)
      iIntros (w) "[[-> Hi] Hf] /=".
      
      (* get_local 0 *)
      take_drop_app_rewrite_twice 1 1.
      iApply wp_base_push;auto.
      take_drop_app_rewrite 1.
      iApply (wp_seq_ctx _ _ _ (λ v', ⌜v' = immV _⌝ ∗ ↪[frame]f)%I).
      iSplitR;[by iIntros "[%Hcontr _]"|].
      iSplitL "Hf".
      { iApply (wp_get_local with "[] [$Hf]"). eauto. simpl. eauto. }

      (* mul *)
      iIntros (w) "[-> Hf] /=".
      iApply wp_base_pull. simpl.
      take_drop_app_rewrite 3.
      iApply (wp_seq_ctx _ _ _ (λ v', ⌜v' = immV _⌝ ∗ ↪[frame] f)%I).
      iSplitR;[by iIntros "[%Hcontr _]"|].
      iSplitL "Hf".
      { iApply (wp_binop with "[$]"). simpl. eauto. eauto. }

      (* return *)
      iIntros (w) "[-> Hf] /=".
      iApply (wp_val_return with "[$]");auto.
      iIntros "Hf /=".

      (* postcondition *)
      iApply iris_wp.wp_value. instantiate (1 := immV [_]). reflexivity.
      iFrame. iPureIntro.

      unfold xx.
      repeat f_equiv.
      unfold Wasm_int.Int32.imul, Wasm_int.Int32.mul. simpl.
      f_equiv.
      clear -Ha Hbool Hoverflow.
      unfold Wasm_int.Int32.ltu in Hbool.
      destruct n;simpl in *.
      destruct (Coqlib.zlt 1 intval);[|done].
      rewrite !Wasm_int.Int32.Z_mod_modulus_eq.
      assert ((intval - 1) `mod` Wasm_int.Int32.modulus = intval - 1)%Z as ->.
      { rewrite Zmod_small;lia. }
      rewrite Z2Nat.inj_sub;[|lia].
      rewrite (Nat2Z.id 1).
      assert ((ssrnat.factorial (Z.to_nat intval - 1) * intval)%Z
              = ssrnat.muln (Z.to_nat intval) (ssrnat.factorial (Z.to_nat intval - 1))) as Heq.
      { unfold ssrnat.muln. unfold ssrnat.muln_rec. lia. }
      rewrite Zmod_small.
      rewrite Heq factPred;lia.
      split. lia.
      apply Zmult_gt_0_lt_reg_r with (p:=intval). lia.
      rewrite Heq factPred. 2: lia.
      etrans. apply Hoverflow.
      apply Z.lt_mul_diag_r;lia.
  } }
  Qed.

  Lemma myrec_spec h_mut_tab a mut_tab fidx i :
    inst_funcs i !! h_mut_tab = Some a -> (* modify table host call is in the instance *)

    ↪[frame] Build_frame [fidx] i -∗
    N.of_nat a↦[wf]FC_func_host (Tf [T_i32; T_i32] []) mut_tab -∗
    WP myrec h_mut_tab {{ v, (⌜v = callHostV (Tf [T_i32; T_i32] []) mut_tab [xx 0; fidx] (LL_base [] [])⌝
                             ∗ N.of_nat a↦[wf]FC_func_host (Tf [T_i32; T_i32] []) mut_tab) ∗ ↪[frame] Build_frame [fidx] i }}.
  Proof.
    iIntros (Hh) "Hf Ha".
    take_drop_app_rewrite_twice 1 1.

    iApply wp_wasm_empty_ctx.
    iApply wp_base_push;auto. simpl.
    take_drop_app_rewrite 1.

    (* get_local 0 *)
    iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV _⌝ ∗ _)%I).
    iSplitR;[by iIntros "[%Hcontr _]"|].
    iSplitL "Hf".
    { iApply (wp_get_local with "[] [$]");eauto. }
    iIntros (w) "[-> Hf] /=".

    iApply wp_base_pull.
    take_drop_app_rewrite_twice 2 0.
    iApply wp_base_push;auto.

    iApply (wp_call_ctx with "[$]");eauto.
    iNext. iIntros "Hf".

    iApply wp_base_pull.
    iApply wp_wasm_empty_ctx. simpl.
    take_drop_app_rewrite 2.
    iApply (wp_invoke_host _ _ _ [xx 0; fidx] with "[$] [$]");auto. 
    iNext. iIntros "Ha Hf".
    iApply iris_wp.wp_value;[apply iris.of_to_val; eauto|].
    iFrame. auto.
  Qed.

End Factorial.

Section FactorialHostMain.
  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}.

  Definition main_instr fact glob :=
    [BI_get_global glob;
     BI_call fact;
     BI_set_global glob].
  Definition main fact glob := to_e_list (main_instr fact glob).

  Lemma main_host_spec fact glob F myrec tab mut_tab f_fact f_F f_myrec f_mut_tab g_glob t_fact_typ mt i tabval n idnstart f Φ :
    inst_funcs i !! fact = Some f_fact ->
    inst_funcs i !! (Wasm_int.nat_of_uint i32m F) = Some f_F ->
    inst_funcs i !! myrec = Some f_myrec ->
    inst_funcs i !! mut_tab = Some f_mut_tab ->
    inst_types i !! t_fact_typ = Some (Tf [T_i32] [T_i32]) ->
    inst_tab i !! 0 = Some tab ->
    inst_globs i !! glob = Some g_glob ->

    (ssrnat.factorial (Wasm_int.nat_of_uint i32m n) < Wasm_int.Int32.modulus)%Z -> (* no overflow *)
    (0 <= (Wasm_int.Int32.intval n))%Z -> (* the parameter must be positive *)

    (∀ v : host_val, ⌜v = immHV []⌝ ∗ (∃ w : value, fact_val n (immV [w]) ∗ (N.of_nat g_glob) ↦[wg] {| g_mut := MUT_mut; g_val := w |}) -∗ Φ v) -∗
    ↪[frame] (* Build_frame [] i *) f -∗
    (N.of_nat f_fact) ↦[wf] FC_func_native i (Tf [T_i32] [T_i32]) [] (fact_instr (VAL_int32 F) myrec t_fact_typ) -∗
    (N.of_nat f_F) ↦[wf] FC_func_native i (Tf [T_i32] [T_i32]) [] (F_instr t_fact_typ) -∗
    (N.of_nat f_myrec) ↦[wf] FC_func_native i (Tf [T_i32] []) [] (myrec_instr mut_tab) -∗
    (N.of_nat f_mut_tab) ↦[wf] FC_func_host (Tf [T_i32; T_i32] []) (Mk_hostfuncidx mt) -∗
    (N.of_nat mt) ↦[ha] HA_modify_table -∗
    (N.of_nat tab) ↦[wt][N.of_nat (yy 0)] tabval -∗
    (N.of_nat g_glob) ↦[wg] {| g_mut := MUT_mut; g_val := VAL_int32 n |} -∗
    (N.of_nat idnstart) ↦[wf]FC_func_native i (Tf [] []) [] (main_instr fact glob) -∗
                                                                                                                                                              
    WP (([], [AI_invoke idnstart]) : host_expr) {{ Φ }}.
    (* WP (([],to_e_list (main_instr fact glob)) : host_expr) {{ v, ∃ w, ⌜v = immHV []⌝ *)
    (*                                                              ∗ fact_val n (immV [w]) *)
    (*                                                              ∗ (N.of_nat g_glob) ↦[wg] {| g_mut := MUT_mut; g_val := w |} }}. *)
  Proof.
    iIntros (Hfact HF Hmyrec Hmut_tab Ht Htab Hglob Hoverflow Hpos).
    iIntros "HΦ Hf Hfact HF Hmyrec Hmut_tab Hmt Htab Hg Hstart".
    (* host bind *)
    iApply wp_lift_wasm.
    (* invoke main *)
    take_drop_app_rewrite 0.
    iApply (wp_invoke_native with "[$] [$]");eauto.
    iNext. iIntros "[Hf Hstart]".
    (* local bind *)
    iApply (wp_frame_bind with "[$]");auto.
    iIntros "Hf".
    (* block *)
    take_drop_app_rewrite 0.
    iApply (wp_block with "[$]");eauto.
    iNext. iIntros "Hf".
    (* label bind *)
    build_ctx (to_e_list (main_instr fact glob)).
    iApply wp_label_bind. simpl.
    (* get_global *)
    bind_seq_base_imm [AI_basic (BI_get_global glob)] with "[Hg Hf]".
    iApply (wp_get_global with "[] [$] [$]");eauto.
    iIntros (w) "[-> [Hg Hf]] /=".
    (* call fact *)
    build_ctx [AI_basic (BI_call fact)].
    iApply (wp_call_ctx with "[$]");eauto.
    iNext. iIntros "Hf".
    deconstruct_ctx.
    (* invoke f_fact *)
    bind_seq_base_callhost [AI_basic (BI_const (VAL_int32 n)); AI_invoke f_fact] with "[Hf Hfact Hmyrec Htab Hmut_tab]".
    { (* f_fact *)
      take_drop_app_rewrite 1.
      iApply (wp_invoke_native with "[$] [$Hfact]");eauto.
      iNext. iIntros "[Hf Hfact]".
      iApply (wp_frame_bind with "Hf");auto.
      iIntros "Hf".
      take_drop_app_rewrite 0.
      iApply (wp_block with "[$]");auto.
      iNext. iIntros "Hf".
      erewrite app_nil_l.
      build_ctx (to_e_list (fact_instr (VAL_int32 F) myrec t_fact_typ)).
      iApply wp_label_bind.
      (* get_local 0 *)
      bind_seq_base_imm [AI_basic (BI_get_local 0)] with "[Hf]".
      iApply (wp_get_local with "[] [$]");eauto.
      iIntros (w) "[-> Hf] /=".
      (* call myrec *)
      build_ctx [AI_basic (BI_call myrec)].
      iApply (wp_call_ctx with "[$]");eauto.
      iNext. iIntros "Hf".
      deconstruct_ctx.
      (* invoke f_myrec *)
      bind_seq_base_callhost [AI_basic (BI_const (VAL_int32 F)); AI_invoke f_myrec] with "[Hf Hmyrec Hmut_tab]".
      { (* myrec *)
        take_drop_app_rewrite 1.
        iApply (wp_invoke_native with "[$] [$]");eauto.
        iNext. iIntros "[Hf Hmyrec] /=".
        iApply (wp_frame_bind with "Hf");auto.
        iIntros "Hf".
        take_drop_app_rewrite 0.
        iApply (wp_block with "[$]");auto.
        iNext. iIntros "Hf".
        build_ctx (to_e_list (myrec_instr mut_tab)).
        iApply wp_label_bind.
        (* myrec body *)
        iApply (wp_wand with "[Hf Hmut_tab]").
        iApply (myrec_spec with "[$] [$]");eauto.
        iIntros (v) "[[-> Hmut_tab] Hf]".
        deconstruct_ctx.
        iApply iris_wp.wp_value;[apply iris.of_to_val;eauto|].
        iExists _. iSplitR "Hf";[|iFrame]. iIntros "Hf".
        iApply wp_frame_rewrite.
        iApply iris_wp.wp_value;[apply iris.of_to_val;eauto|].
        iSplitR;eauto. iCombine "Hmyrec Hmut_tab Hf" as "HH". instantiate (1:=λ _,_). iExact "HH". }
      iIntros (w) "[-> [Hmyrec [Hmut_tab Hf]]]".
      (* iApply wp_base_pull. *)
      (* iApply wp_wasm_empty_ctx. *)
      iApply iris_wp.wp_value;[apply iris.of_to_val;eauto|].
      deconstruct_ctx.
      iApply iris_wp.wp_value;[apply iris.of_to_val;eauto|simpl].
      iExists _. iFrame. iIntros "Hf".
      iApply wp_frame_rewrite.
      iApply iris_wp.wp_value;[apply iris.of_to_val;eauto|simpl].
      iSplit;eauto.
      iCombine "Htab Hfact Hmyrec Hmut_tab Hf" as "HH".
      instantiate (1:=λ _, _). iExact "HH".
    }
    iIntros (w) "[-> [Htab [Hfact [Hmyrec [Hmut_tab Hf]]]]]".
    iApply iris_wp.wp_value;[apply iris.of_to_val;eauto|simpl].
    deconstruct_ctx.
    iApply iris_wp.wp_value;[apply iris.of_to_val;eauto|simpl].
    iExists _. iFrame. iIntros "Hf".
    iApply iris_wp.wp_value;[apply iris.of_to_val;eauto|simpl].

    iApply wp_call_host_modify_table;[eauto|build_llfill|simpl;reflexivity|eauto|eauto|].
    iFrame. iNext. iIntros "[Hf [Ha Htab]]".

    iApply wp_lift_wasm.
    iApply (wp_frame_bind with "[$]");auto.
    iIntros "Hf".
    match goal with | |- context [ AI_local ?i ?f ?es :: ?e ] => set (P:=AI_local i f es :: e); set (l:=es) end.
    build_ctx P.
    iApply wp_label_bind.
    bind_seq_base_imm [AI_local 1 {| f_locs := [VAL_int32 n]; f_inst := i |} l] with "[Hf Htab HF]".
    { iApply (wp_frame_bind with "[$]");auto.
      iIntros "Hf". subst l.
      match goal with | |- context [ AI_label ?i ?f ?es ] => set (l:=es) end.
      build_ctx l; subst l.
      iApply wp_label_bind.
      match goal with | |- context [ AI_local ?i ?f ?es ] => set (l:=es) end.
      bind_seq_base_imm [AI_local 0 {| f_locs := [VAL_int32 F]; f_inst := i |} l] with "[Hf]";[subst l|].
      { iApply (wp_frame_bind with "[$]");auto.
        iIntros "Hf".
        iApply (wp_wand _ _ _ (λ v, ⌜v = immV _⌝ ∗ _)%I with "[Hf]"). iApply (wp_label_value with "Hf");eauto.
        iIntros (v) "[-> Hf]". iExists _. iFrame.
        iIntros "Hf /=".
        iApply (wp_frame_value with "[$]");eauto. }
      iIntros (v) "[-> Hf] /=".
      (* BI_call_indirect *)
      build_ctx [AI_basic (BI_const (xx 0));AI_basic (BI_call_indirect t_fact_typ)].
      iApply (wp_call_indirect_success_ctx with "[Htab] HF Hf");eauto.
      iNext. iIntros "[Htab [HF Hf]]".
      deconstruct_ctx.
      (* invoke f_F *)
      take_drop_app_rewrite 1.
      iApply (wp_invoke_native with "[$] [$]");eauto.
      iNext. iIntros "[Hf HF]".
      (* f_F *)
      iApply (wp_frame_bind with "[$]");auto.
      iIntros "Hf".
      take_drop_app_rewrite 0. iApply (wp_block with "[$]");eauto.
      iNext. iIntros "Hf".
      build_ctx (to_e_list (F_instr t_fact_typ)).
      iApply wp_label_bind.
      iApply (wp_wand with "[-]").
      iApply (F_spec with "[$] [$] [$]");eauto.
      iIntros (v) "[[%Hspec [Htab HF]] Hf]".
      rewrite Hspec.
      (* return from block and frame *)
      iApply (wp_val_return with "[$]");auto.
      iIntros "Hf".
      iApply iris_wp.wp_value;[unfold IntoVal;eapply iris.of_to_val;eauto|].
      iExists _. iFrame. iIntros "Hf".
      iApply (wp_wand _ _ _ (λ v, ⌜v = _⌝ ∗ _ )%I with "[Hf]").
      iApply (wp_frame_value with "[$]");eauto.
      iIntros (v') "[-> Hf]". rewrite Hspec.
      iApply (wp_val_return with "[$]");auto.
      iIntros "Hf /=".
      iApply iris_wp.wp_value;[unfold IntoVal;eapply iris.of_to_val;rewrite Hspec;eauto|].
      iExists _. iFrame. iIntros "Hf".
      iApply (wp_wand _ _ _ (λ v, ⌜v = immV _⌝ ∗ _ )%I with "[Hf]").
      iApply (wp_frame_value with "[$]");rewrite Hspec;auto.
      iIntros (v') "[-> Hf]".
      iSplit;[eauto|].
      iCombine "Htab HF Hf" as "HH". instantiate (1:=λ _, _). iExact "HH".
    }
    iIntros (v) "[-> [Htab [HF Hf]]] /=".
    iApply (wp_wand _ _ _ (λ v, ⌜v = immV _⌝ ∗ _)%I with "[Hg Hf]").
    iApply (wp_set_global with "[] [$] [$]");eauto.
    iIntros (v) "[-> [Hg Hf]]".
    iApply (wp_val_return with "[$]");auto.
    iIntros "Hf /=".    
    iApply iris_wp.wp_value;[unfold IntoVal;eapply iris.of_to_val;eauto|].
    iExists _. iFrame. iIntros "Hf".
    iApply (wp_wand _ _ _ (λ v, ⌜v = immV _⌝ ∗ _ )%I with "[Hf]").
    iApply (wp_frame_value with "[$]");eauto.
    iIntros (v) "[-> Hf]".
    iApply wp_value;eauto.
    iApply "HΦ". eauto.
  Qed.
    
End FactorialHostMain.

Section FactorialHost.
  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}.

  Definition factorial_module :=
    {|
      mod_types := [ Tf [T_i32] [T_i32] ; Tf [T_i32] [] ; Tf [T_i32; T_i32] [] ; Tf [] [] ] ;
      mod_funcs :=
      [ {|
          modfunc_type := Mk_typeidx 1 ;
          modfunc_locals := [] ;
          modfunc_body := myrec_instr 0
        |};
        {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [] ;
          modfunc_body := F_instr 0
        |};
        {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [] ;
          modfunc_body := fact_instr (xx 2) 1 0
        |};
        {|
          modfunc_type := Mk_typeidx 3 ;
          modfunc_locals := [] ;
          modfunc_body := main_instr 3 0
        |}
      ] ;
      mod_tables := [ {| modtab_type := {| tt_limits := {| lim_min := 1 ; lim_max := None |} ; tt_elem_type := ELT_funcref |} |} ] ; 
      mod_mems := [] ;
      mod_globals := [ (* {| modglob_type := {| tg_mut := MUT_mut ; tg_t := T_i32 |} ; modglob_init := [BI_const (xx 0)] |} *) ] ;
      mod_elem := [] ;
      mod_data := [] ;
      mod_start := Some (Build_module_start (Mk_funcidx 4)) ;
      mod_imports :=
        [ {|
            imp_module := list_byte_of_string "Host" ;
            imp_name := list_byte_of_string "modify_table" ;
            imp_desc := ID_func 2
          |};
          {|
            imp_module := list_byte_of_string "Host" ;
            imp_name := list_byte_of_string "ret" ;
            imp_desc := ID_global {| tg_mut := MUT_mut ; tg_t := T_i32 |}
          |}
        ];
      mod_exports := []
    |}.

  Definition factorial_impts : seq.seq extern_t := [ET_func (Tf [T_i32; T_i32] []); ET_glob {| tg_mut := MUT_mut ; tg_t := T_i32 |}].

  Ltac type_next_rewrite :=
  match goal with
  | |- context [ be_typing _ ?e _  ] =>
      rewrite -(list.take_drop (length e - 1) e);simpl take; simpl drop
  end.
  Ltac type_next :=
  match goal with
  | |- context [ be_typing _ ?e _  ] =>
      rewrite -(list.take_drop (length e - 1) e);simpl take; simpl drop;
      eapply bet_composition;[|econstructor;eauto];simpl
  end.
  Ltac weaken :=
  match goal with
  | |- context [ be_typing _ ?e (Tf ?t1 ?t)  ] =>
      try rewrite <- (app_nil_r t1);
      rewrite -(list.take_drop (length t - 1) t);simpl take; simpl drop;
      eapply bet_weakening;constructor;auto
  end.
  Ltac type_go := repeat (constructor || type_next || weaken || (type_next_rewrite; eapply bet_composition; [constructor|])).

  Lemma factorial_module_typing :
    module_typing factorial_module (factorial_impts) [].
  Proof. unfold module_typing.
    exists [Tf [T_i32] []; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [] []],[ (* {| tg_mut := MUT_mut ; tg_t := T_i32 |} *) ]. simpl.
    repeat split;eauto.
    { rewrite ! Forall2_cons. repeat split;auto; cbn;auto.
      { type_go. }
      { type_go.
        type_next_rewrite.
        eapply bet_composition. instantiate (1:=[T_i32]).
        type_next_rewrite.
        eapply bet_composition. instantiate (1:=[T_i32;T_i32]).
        type_next_rewrite.
        eapply bet_composition. instantiate (1:=[T_i32]).
        type_next_rewrite.
        eapply bet_composition. instantiate (1:=[T_i32;T_i32]).
        all: type_go. }
      { type_go.
        type_next_rewrite.
        eapply bet_composition. instantiate (1:=[T_i32]).
        type_next_rewrite.
        eapply bet_composition. instantiate (1:=[T_i32;T_i32]).
        type_go. rewrite <- (app_nil_r [T_i32]).
        rewrite -(list.take_drop (1) [T_i32;T_i32]);simpl take; simpl drop.
        eapply bet_weakening.
        type_go.
        weaken. }
      { type_go. }
    }
    { rewrite ! Forall2_cons. repeat split;auto; cbn;auto. }
  Qed.

  Definition factorial_module_instantiate :=
    [ ID_instantiate [] 0 [0%N;1%N] ].

  Notation "{{{ P }}} es {{{ v , Q }}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).

  Lemma instantiate_factorial hidx gidx mod_tab n :
    (ssrnat.factorial (Wasm_int.nat_of_uint i32m n) < Wasm_int.Int32.modulus)%Z -> (* no overflow *)
    (0 <= (Wasm_int.Int32.intval n))%Z -> (* the parameter must be positive *)
    
    ⊢ {{{ (N.of_nat hidx) ↦[wf] (FC_func_host (Tf [T_i32; T_i32] []) (Mk_hostfuncidx mod_tab)) ∗
          (N.of_nat mod_tab) ↦[ha] HA_modify_table ∗
          (N.of_nat gidx) ↦[wg] {| g_mut := MUT_mut; g_val := VAL_int32 n |} ∗
          0%N ↪[mods] factorial_module ∗
          (∃ name, 0%N ↪[vis] {| modexp_name := name; modexp_desc := MED_func (Mk_funcidx hidx) |}) ∗
          (∃ name, 1%N ↪[vis] {| modexp_name := name; modexp_desc := MED_global (Mk_globalidx gidx) |}) ∗
          ↪[frame] empty_frame
      }}}
        ((factorial_module_instantiate,[]) : host_expr) 
      {{{ v, ⌜v = immHV []⌝ ∗ ∃ w, fact_val n (immV [w]) ∗ (N.of_nat gidx) ↦[wg] {| g_mut := MUT_mut; g_val := w |} }}} .
  Proof.
    iIntros (Hoverflow Hpos Φ). iModIntro. iIntros "(Hmod_tab & HA & Hglob & Hmod & Hvis1 & Hvis2 & Hf) HΦ".
    iDestruct "Hvis1" as (name1) "Hvis1".
    iDestruct "Hvis2" as (name2) "Hvis2".
    iApply (instantiation_spec_operational_start_seq with "[$Hf] [$Hmod Hvis1 Hvis2 Hmod_tab Hglob] [HΦ HA]") => //.
    { apply factorial_module_typing. }
    { unfold module_restrictions. cbn. repeat split;exists [];auto. }
    { cbn. instantiate (5:=[_;_]).
      instantiate (1:={[N.of_nat gidx := {| g_mut := MUT_mut; g_val := VAL_int32 n |} ]}).
      instantiate (1:=∅).
      instantiate (1:=∅).
      instantiate (1:= {[N.of_nat hidx := _ ]}).
      iSplitL "Hvis1 Hvis2";[|iSplit;[|auto]].
      simpl. iFrame. done.
      rewrite /instantiation_resources_pre_wasm /=.
      iSplitL;[|iPureIntro;split;apply Forall_nil;auto].
      iSplitL "Hmod_tab";[|iSplitR;[|iSplitR]].
      { rewrite /import_func_wasm_check /func_typecheck ! Forall2_cons /=.
        iSplit. iApply big_sepM_singleton. iFrame. iPureIntro.
        repeat split; auto. eexists _. rewrite lookup_singleton. eauto. set_solver. set_solver. }
      { iSplit. by iApply big_sepM_empty. iPureIntro.
        rewrite /tab_typecheck /tab_domcheck /factorial_impts ! Forall2_cons /=.
        repeat split; auto. }
      { iSplit. by iApply big_sepM_empty. iPureIntro.
        rewrite /mem_typecheck /mem_domcheck /factorial_impts ! Forall2_cons /=.
        repeat split; auto. }
      { rewrite /import_glob_wasm_check /glob_typecheck ! Forall2_cons /=.
        iSplit. iApply big_sepM_singleton. iFrame. iPureIntro.
        repeat split; auto. eexists _. rewrite lookup_singleton. eauto. set_solver. set_solver. }
    }

    iIntros (idnstart) "Hf [Hmod [[Hvis1 [Hvis2 _]] Hi]]".
    iDestruct "Hi" as (i) "[Hi _]".
    unfold instantiation_resources_post_wasm.
    iDestruct "Hi" as (g_inits tab_allocs mem_allocs glob_allocs wts' wms')
                        "(Hres & %Hpre & %Htaballocs & %Hwts' & %Hcheck1
                          & %Hmemalloc & %Hwms' & %Hcheck2 & %Hinit & %Hgloballocs & [Hfuncs [Htab [_ _]]])".
    simplify_eq. destruct i. cbn in *.
    destruct Hpre as [Htypes [Hprefuncs [_ [_ [Hpreglobs Hstart]]]]].
    repeat (destruct inst_funcs;[done|]).
    destruct inst_globs;[by inversion Hpreglobs|].
    apply b2p in Hstart.
    apply prefix_cons_inv_1 in Hprefuncs.
    apply prefix_cons_inv_1 in Hpreglobs.
    simplify_eq.
    iDestruct "Hfuncs" as "[Hmyrec [HF [Hfact [Hmain _]]]] /=".

    set (i:={| inst_types := [Tf [T_i32] [T_i32]; Tf [T_i32] []; Tf [T_i32; T_i32] []; Tf [] []];
               inst_funcs := [:: f, f0, f1, f2, idnstart & inst_funcs];
               inst_tab := inst_tab;
               inst_memory := inst_memory;
               inst_globs := g :: inst_globs
            |}).
    rewrite -/i.

    rewrite drop_0. iDestruct (big_sepL2_length with "Htab") as %Htablen. destruct inst_tab;[done|].
    iDestruct "Htab" as "[[[Ht _] _] _]".

    iDestruct "Hres" as "[[Hmodtab _] [_ [_ [Hglob _]]]]".
    rewrite /import_func_resources /import_glob_resources !big_sepM_singleton.

    iApply (main_host_spec with "[$] [$] [$] [$] [$] [$] [$] [$] [$]");eauto;unfold i;simpl;auto.
  Qed.
    
    
End FactorialHost.
