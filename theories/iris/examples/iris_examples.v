From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules.
Require Export datatypes host operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

(* Example Programs *)
Section Examples.
  
Import DummyHosts.

Let reduce := @reduce host_function host_instance.

Let reducible := @reducible wasm_lang.

Context `{!wasmG Σ}.

Definition xx i := (VAL_int32 (Wasm_int.int_of_Z i32m i)).
Definition xb b := (VAL_int32 (wasm_bool b)).

Let expr := iris.expr.

Definition my_add : expr :=
  [AI_basic (BI_const (xx 3));
     AI_basic (BI_const (xx 2));
  AI_basic (BI_binop T_i32 (Binop_i BOI_add))].

Lemma myadd_spec (s : stuckness) (E : coPset) (Φ: val -> iProp Σ) (f0: frame): 
  ↪[frame] f0 -∗ Φ (immV [xx 5]) -∗ WP my_add @ s; E {{ v, Φ v ∗  ↪[frame] f0  }}.
Proof.
  iIntros "HP".
  unfold my_add.
  by iApply wp_binop.
Qed.

(* An example to show framing from the stack. *)
Definition my_add2: expr :=
  [AI_basic (BI_const (xx 1));
  AI_basic (BI_const (xx 2));
  AI_basic (BI_binop T_i32 (Binop_i BOI_add));
  AI_basic (BI_const (xx 2));
  AI_basic (BI_binop T_i32 (Binop_i BOI_add))].

Lemma myadd2_spec (s : stuckness) (E : coPset) (Φ: val -> iProp Σ) f0:
  ↪[frame] f0 -∗ Φ (immV [xx 5]) -∗ WP my_add2 @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros "Hf0 HΦ".
  replace my_add2 with (take 3 my_add2 ++ drop 3 my_add2) => //.
  iApply wp_seq => /=.
  instantiate (1 := fun v => (⌜ v = immV [xx 3] ⌝ ∗ ↪[frame] f0)%I ).
  iSplitL ""; first by iIntros "(%H & ?)".
  iSplitL "Hf0"; first by iApply (wp_binop with "[$]") => //.
  iIntros (?) "(-> & Hf0)" => /=.
  by iApply (wp_binop with "[$]").
Qed.

(* --------------------------------------------------------------------------------------------- *)
(* -------------------------------- CONTROL FLOW EXAMPLES -------------------------------------- *)
(* --------------------------------------------------------------------------------------------- *)

(* Helper lemmas and tactics for necessary list manipulations for expressions *)
Lemma iRewrite_nil_l (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (e : iris.expr) :
  (WP [] ++ e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Φ }}).
Proof. rewrite app_nil_l. auto. Qed.
Lemma iRewrite_nil_r (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (e : iris.expr) :
  (WP e ++ [] @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Φ }}).
Proof. rewrite app_nil_r. auto. Qed.
Lemma iRewrite_nil_l_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (e : iris.expr) i lh :
  (WP [] ++ e @ s; E CTX i; lh {{ Φ }} ⊢ WP e @ s; E CTX i; lh {{ Φ }}).
Proof. rewrite app_nil_l. auto. Qed.
Lemma iRewrite_nil_r_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (e : iris.expr) i lh :
  (WP e ++ [] @ s; E CTX i; lh {{ Φ }} ⊢ WP e @ s; E CTX i; lh {{ Φ }}).
Proof. rewrite app_nil_r. auto. Qed.

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

(* Examples of blocks that return normally *)
Lemma label_check_easy f0:
  ↪[frame] f0
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32;T_i32])
            [::BI_const (xx 2); BI_const (xx 3)] )] {{ λ v, ⌜v = immV [xx 2;xx 3]⌝ ∗ ↪[frame] f0}}.
Proof.
  rewrite -iRewrite_nil_l.
  iIntros "Hf0"; iApply (wp_block with "[$]");eauto. iNext.
  iIntros "Hf0".
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil. simpl.
  iApply (wp_val_return with "[$]");auto.
  iIntros "Hf0"; iApply wp_value;eauto. done.
Qed.

Lemma label_check_easy' f0 :
  ↪[frame] f0
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32;T_i32])
                   [:: (BI_block (Tf [] [T_i32;T_i32])
                                [::BI_const (xx 2); BI_const (xx 3)] )] )] {{ λ v, ⌜v = immV [xx 2;xx 3]⌝ ∗ ↪[frame] f0 }}.
Proof.
  rewrite -iRewrite_nil_l.
  iIntros "Hf0".
  iApply (wp_block with "[$]");eauto. iNext.
  iIntros "Hf0".
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil. simpl.
  iApply iRewrite_nil_r_ctx.
  iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 2; xx 3]⌝ ∗ ↪[frame] f0)%I).
  iSplitR; [by iIntros "[%Hcontr _]"|].
  iSplitL "Hf0"; first by iApply label_check_easy.
  iIntros (w) "(-> & Hf0)". simpl.
  iApply (wp_val_return with "[$]") ;auto.
  iIntros "Hf0".
  iApply wp_value;eauto. done.
Qed.

Lemma br_check_bind_return f0 :
  ↪[frame] f0
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32])
         [:: BI_block (Tf [] [])
            [::BI_const (xx 3); BI_br 1] ])] {{ λ v, ⌜v = immV [xx 3]⌝ ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf".
  iApply iRewrite_nil_l.
  iApply (wp_block with "[$]");eauto. iNext.
  simpl. iIntros "Hf".
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil.
  simpl.
  iApply iRewrite_nil_l_ctx.
  iApply (wp_block_ctx with "[$]");eauto. iNext.
  simpl. iIntros "Hf".
  iApply wp_label_push_nil.
  simpl.
  take_drop_app_rewrite 1.
  iApply (wp_br_ctx with "[$]");auto. iNext.
  iIntros "Hf".
  iApply wp_value;auto. done.
Qed.

Lemma br_check_bind_return_2 f0 :
  ↪[frame] f0
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32])
         [:: BI_block (Tf [] [])
            [::BI_const (xx 2);BI_const (xx 3); BI_br 1] ])] {{ λ v, ⌜v = immV [xx 3]⌝ ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf".
  iApply iRewrite_nil_l.
  iApply (wp_block with "[$]");eauto. iNext. iIntros "?".
  simpl.
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil.
  simpl.
  iApply iRewrite_nil_l_ctx.
  iApply (wp_block_ctx with "[$]");eauto. iNext. iIntros "?".
  simpl.
  iApply wp_label_push_nil.
  simpl.
  take_drop_app_rewrite 1.
  iApply iRewrite_nil_r_ctx.
  rewrite -app_assoc.
  iApply wp_base_push;auto.
  take_drop_app_rewrite 1.
  iApply (wp_br_ctx with "[$]");auto. iNext. iIntros "?".
  iApply wp_value;auto. done.
Qed.

Lemma br_check_bind_return_3 f0 :
  ↪[frame] f0
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32])
         [:: BI_block (Tf [] [])
            [::BI_const (xx 2); BI_const (xx 3); (BI_binop T_i32 (Binop_i BOI_add)); BI_br 1] ])] {{ λ v, ⌜v = immV [xx 5]⌝ ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf".
  iApply iRewrite_nil_l.
  iApply (wp_block with "[$]");eauto. iNext. simpl. iIntros "?".
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil.
  iApply iRewrite_nil_l_ctx.
  iApply (wp_block_ctx with "[$]");eauto;simpl. iNext. iIntros "?".
  iApply wp_label_push_nil. simpl.
  take_drop_app_rewrite 3.
  iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 5]⌝ ∗ ↪[frame] f0)%I).
  iSplitR; [by iIntros "[%Hcontr _]"|].
  iSplitL.
  { iApply (wp_binop with "[$]");eauto. }
  iIntros (w) "[-> ?]". simpl.
  take_drop_app_rewrite 1.
  iApply iRewrite_nil_l_ctx.
  iApply iRewrite_nil_r_ctx. rewrite -!app_assoc.
  iApply (wp_br_ctx with "[$]");auto. iNext. iIntros "?". simpl.
  iApply wp_value;eauto. done.  
Qed.

Lemma br_check_bind_return_4 f0 :
  ↪[frame] f0
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32]) (* this block returns normally *)
                   [:: BI_const (xx 1);
                    BI_block (Tf [] [T_i32]) (* this block gets br'ed to *)
                             [::BI_block (Tf [] []) (* this block will never return *)
                               [::BI_const (xx 2);
                                BI_const (xx 3);
                                (BI_binop T_i32 (Binop_i BOI_add));
                                BI_br 1;
                                (BI_binop T_i32 (Binop_i BOI_add))] (* this expression gets stuck without br *) ];
                    (BI_binop T_i32 (Binop_i BOI_add)) ])] (* this expression only reds after previous block is reduced *)
    {{ λ v, ⌜v = immV [xx 6]⌝ ∗ ↪[frame] f0}}.
Proof.
  iIntros "?".
  iApply iRewrite_nil_l.
  iApply (wp_block with "[$]");eauto. iNext. iIntros "?". simpl.
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil. simpl.
  iApply iRewrite_nil_r_ctx.
  iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 6]⌝ ∗ ↪[frame] f0)%I).
  iSplitR; [by iIntros "[%Hcontr _]"|].
  iSplitL.
  { take_drop_app_rewrite_twice 1 1.
    iApply wp_wasm_empty_ctx.
    iApply wp_base_push;auto. simpl.
    iApply iRewrite_nil_r_ctx.
    iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 5]⌝ ∗ ↪[frame] f0)%I).
    iSplitR; [by iIntros "[%Hcontr _]"|].
    iSplitL.
    { iApply iRewrite_nil_l.
      iApply (wp_block with "[$]");eauto. iNext. iIntros "?". simpl.
      iApply wp_wasm_empty_ctx.
      iApply wp_label_push_nil. simpl.
      iApply iRewrite_nil_l_ctx.
      iApply (wp_block_ctx with "[$]");eauto. simpl. iNext. iIntros "?".
      iApply wp_label_push_nil. simpl.
      take_drop_app_rewrite 3.
      iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 5]⌝ ∗ ↪[frame] f0)%I).
      iSplitR; [by iIntros "[%Hcontr _]"|].
      iSplitL.
      { iApply (wp_binop with "[$]");eauto. }
      iIntros (w) "[-> ?]". simpl.
      take_drop_app_rewrite 2.
      iApply iRewrite_nil_l_ctx.
      iApply wp_base_push;auto. simpl.
      take_drop_app_rewrite 1.
      iApply (wp_br_ctx with "[$]");auto. iNext. iIntros "?".
      iApply wp_value;eauto. done. }
    iIntros (w) "[-> ?]". simpl.
    iApply wp_base;auto. simpl.
    iApply (wp_binop with "[$]");eauto. }
  iIntros (w) "[-> ?] /=".
  iApply (wp_val_return with "[$]");auto;simpl. iIntros "?".
  iApply wp_value;eauto. done.
Qed.
  

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
Definition factorial fact : expr := to_e_list (factorial_instrs fact).

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
  iLöb as "IH" forall (n). { (* { is to fix annoying indent problem... *)
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
  { iApply (wp_get_local with "[$]"). unfold f. eauto.
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
    simpl. iApply (wp_value _ _ _ _ (immV ([xx 1]))). by cbv.
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
    { iApply (wp_get_local with "[$]"). unfold f. eauto.
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
            iApply wp_value. instantiate (1 := immV [_]). reflexivity.
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
    { iApply (wp_get_local with "[$Hf]"). eauto. simpl. eauto. }

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
    iApply wp_value. instantiate (1 := immV [_]). reflexivity.
    iFrame. iPureIntro.

    unfold xx.
    repeat f_equiv.
    unfold Wasm_int.Int32.imul, Wasm_int.Int32.mul. simpl.
    f_equiv.
    (* rewrite Wasm_int.Int32.Z_mod_modulus_eq. *)
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
    iApply wp_value. instantiate (1:=immV [_]). subst;done.
    iFrame. auto. }
  iIntros (w) "[[%Hfact Hi] Hf]".
  iApply wp_wasm_empty_ctx_frame.
  iApply (wp_frame_value with "[$]"); [subst;eauto..|].
  iNext.
  iFrame. auto.
Qed.


(* --------------------------------------------------------------------------------------------- *)
(* ------------------------- SIMPLE CALL INDIRECT EXAMPLE -------------------------------------- *)
(* --------------------------------------------------------------------------------------------- *)

(* Module 1 *)

Definition f1_instrs : seq.seq basic_instruction :=
  [BI_const (xx 0);
   BI_load T_i32 None 0%N 0%N].
Definition f1 : expr := to_e_list f1_instrs.
Definition store42_instrs : seq.seq basic_instruction :=
  [BI_const (xx 0);
   BI_const (xx 42);
   BI_store T_i32 None 0%N 0%N].
Definition store42 : expr := to_e_list (store42_instrs).

(* Module 2 *)

Definition store11_instrs : seq.seq basic_instruction :=
  [BI_const (xx 0);
   BI_const (xx 11);
   BI_store T_i32 None 0%N 0%N].
Definition store11 : expr := to_e_list (store11_instrs).
Definition doIt_instrs i: seq.seq basic_instruction :=
  [BI_const (xx 0);
   BI_call_indirect i].
Definition doIt i : expr := to_e_list (doIt_instrs i).

(* Note that the frame instance will be different for the spec of the two modules. *)

Lemma f1_spec f n v :
  types_agree T_i32 v ->
  f.(f_inst).(inst_memory) !! 0 = Some n ->
  ↪[frame] f -∗
  (N.of_nat n) ↦[wms][ 0%N ] (bits v) -∗
  WP f1 {{ w, (⌜w = immV [v]⌝ ∗ (N.of_nat n) ↦[wms][ 0%N ] (bits v)) ∗ ↪[frame] f }}.
Proof.
  iIntros (Htypes Hfmem) "Hf Hn".
  iApply wp_wand_r. iSplitL.
  iApply (wp_load (λ w, ⌜w = immV [v]⌝)%I with "[$Hf Hn]");eauto.
  iIntros (w) "[[-> Hn] Hf]".
  iFrame. auto.
Qed.

Lemma store42_spec f n c :
  f.(f_inst).(inst_memory) !! 0 = Some n ->
  ↪[frame] f -∗
   (N.of_nat n) ↦[wms][ 0%N ] (bits (VAL_int32 c)) -∗
   WP store42 {{ w, (⌜w = immV []⌝ ∗ (N.of_nat n) ↦[wms][ 0%N ] (bits (xx 42))) ∗ ↪[frame] f }}.
Proof.
  iIntros (Hfmem) "Hf Hn".
  iApply wp_wand_r. iSplitL.  
  iApply (wp_store (λ w, ⌜w = immV ([])⌝)%I with "[$Hf Hn]");eauto.
  by rewrite Memdata.encode_int_length.
  iIntros (v) "[[-> Hn] Hf]". rewrite /= N.add_0_l.
  iFrame. auto.
Qed.


Lemma store11_spec f n c :
  f.(f_inst).(inst_memory) !! 0 = Some n ->
  ↪[frame] f -∗
   (N.of_nat n) ↦[wms][ 0%N ] (bits (VAL_int32 c)) -∗
   WP store11 {{ w, (⌜w = immV []⌝ ∗ (N.of_nat n) ↦[wms][ 0%N ] (bits (xx 11))) ∗ ↪[frame] f }}.
Proof.
  iIntros (Hfmem) "Hf Hn".
  iApply wp_wand_r. iSplitL.  
  iApply (wp_store (λ w, ⌜w = immV ([])⌝)%I with "[$Hf Hn]");eauto.
  by rewrite Memdata.encode_int_length.
  iIntros (v) "[[-> Hn] Hf]". rewrite /= N.add_0_l.
  iFrame. auto.
Qed.

Lemma doIt_spec t i2 f0 a v n :
  (inst_types (f_inst f0)) !! t = Some (Tf [] [T_i32]) ->
  (inst_tab (f_inst f0)) !! 0 = Some t ->
  types_agree T_i32 v ->
  inst_memory i2 !! 0 = Some n ->
  (* ghost state of current instance *)
  (N.of_nat t) ↦[wt][ 0%N ] (Some a) -∗
  (N.of_nat a) ↦[wf] (FC_func_native i2 (Tf [] [T_i32]) [] f1_instrs) -∗
  ↪[frame] f0 -∗
  (* ghost state of instance i2 *)
  N.of_nat n ↦[wms][0] bits v -∗
  WP doIt t {{  λ _, True ∗ ↪[frame] f0  }}.
Proof.
  iIntros (Htype Ht Hv Hn) "Ht Ha Hf Hn".
  iApply (wp_call_indirect_success with "[Ht] Ha Hf");eauto.
  iNext. iIntros "[Ht [Ha Hf]]".
  take_drop_app_rewrite 0.
  iApply (wp_invoke_native with "Hf Ha");eauto.
  iNext. iIntros "[Hf Ha] /=".
  rewrite /= -wp_frame_rewrite.
  iApply wp_wasm_empty_ctx_frame.
  take_drop_app_rewrite 1.
  iApply (wp_seq_ctx_frame _ _ _ (λ w, ⌜w = immV [v]⌝ ∗ N.of_nat n↦[wms][0]bits v)%I).
  iFrame "Hf".
  iSplitR;[by iIntros "[%Hcontr _]"|].
  iSplitL "Hn".
  { iIntros "Hf /=".
    take_drop_app_rewrite 0.
    iApply (wp_block with "[$]");eauto.
    iNext. Local Opaque to_e_list.
    iIntros "Hf /=".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil. simpl push_base.
    iApply iRewrite_nil_r_ctx.
    iApply (wp_seq_ctx with "[-]").
    iSplitR; cycle 1.
    iSplitL.
    iApply (f1_spec with "Hf Hn");auto.
    iIntros (w) "[[-> Hn] Hf] /=".
    iApply (wp_val_return with "[$]");auto.
    iIntros "Hf /=".
    iApply wp_value. by instantiate (1:=immV [_]).
    iFrame. auto.
    by iIntros "[[%Hcontr _] _]".
  }

  iIntros (w) "[[-> Hn] Hf] /=".
  iApply wp_wasm_empty_ctx_frame.
  iApply (wp_frame_value with "[$]");eauto.
Qed.

End Examples.

