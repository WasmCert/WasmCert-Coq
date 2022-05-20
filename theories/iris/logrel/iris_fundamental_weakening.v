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

  Context `{!wasmG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Lemma get_base_l_push_const {i : nat} (lh : valid_holed i) w :
    get_base_l (vh_push_const lh w) = (w ++ get_base_l lh) ∨
      get_base_l (vh_push_const lh w) = get_base_l lh.
  Proof.
    induction lh.
    { left. auto. }
    { simpl. by right. }
  Qed.

  Lemma push_const_lh_depth {i : nat} (lh : valid_holed i) w :
    lh_depth (lh_of_vh lh) = lh_depth (lh_of_vh (vh_push_const lh w)).
  Proof.
    induction lh;simpl;auto.
  Qed.

  Lemma simple_get_base_l_push_const (lh : simple_valid_holed) w :
    simple_get_base_l (sh_push_const lh w) = (w ++ simple_get_base_l lh) ∨
    simple_get_base_l (sh_push_const lh w) = simple_get_base_l lh.
  Proof.
    induction lh.
    { left. auto. }
    { simpl. by right. }
  Qed.

  Lemma sh_push_const_lh_depth (lh : simple_valid_holed) w :
    lh_depth (lh_of_sh lh) = lh_depth (lh_of_sh (sh_push_const lh w)).
  Proof.
    induction lh;simpl;auto.
  Qed.
  
  (* -------------------------------------- WEAKENING -------------------------------------- *)

  Lemma typing_weakening C es t1s t2s ts : (⊢ semantic_typing (HWP:=HWP) C es (Tf t1s t2s)) ->
                                           ⊢ semantic_typing (HWP:=HWP) C es (Tf (ts ++ t1s) (ts ++ t2s)).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (HIH i lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { iApply iRewrite_nil_l.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_app_inv_r with "Hv") as (ws1 ws2 Heq) "[Hv1 Hv2]".
    rewrite Heq. simpl of_val. rewrite fmap_app - app_assoc.

    iApply (wp_wand with "[-]");cycle 1.
    { iIntros (v) "H". unfold interp_val. rewrite -or_assoc. iExact "H". }

    iApply wp_val_can_trap_app;[apply to_val_fmap|].
    iFrame.
    iSplitR.
    { iModIntro. iIntros "[Hcontr | [Hcontr | Hcontr] ]";[by iDestruct "Hcontr" as (? ?) "_"|..].
      { rewrite fixpoint_interp_br_eq. iDestruct "Hcontr" as (? ? ? ? ?) "_". done. }
      { iDestruct "Hcontr" as (? ? ?) "_";done. } }
    iIntros "Hf".

    assert ((λ v : value, AI_basic (BI_const v)) <$> ws2 = of_val (immV ws2)) as ->;[auto|].

    iApply (wp_wand with "[-]").
    { iApply (HIH with "[] [] [-]");iFrame "∗ # %".
      iRight. iExists _. iSplit;eauto. }

    iIntros (v) "[Hw Hf0]".
    iFrame.
    iDestruct "Hw" as "[[Hw|#Hw]|[Hw|Hw]]".
    { by iLeft. }
    { iRight. iLeft.
      iDestruct "Hw" as (ws' ->) "Hw".
      iSimpl. iExists _. iSplit;eauto.
      iApply big_sepL2_app;eauto. }
    { iRight. iRight. iLeft.
      rewrite fixpoint_interp_br_eq.
      iDestruct "Hw" as (j lh' w' p -> Hbase Hsize) "Hbr".
      iApply fixpoint_interp_br_eq.
      unfold val_combine.

      iExists j,(vh_push_const lh' ws1),_,p. iSplit;[auto|].
      iSplit;[eauto|]. rewrite -push_const_lh_depth. iSplit;[auto|].
      iDestruct "Hbr" as (? ? ? ? ? ? ? ?) "(H&H0&H1&H2&H3&H4)".
      
      pose proof (get_base_l_push_const lh' ws1) as [Hbase'|Hbase'].
      
      { iExists _,_,_,_,_,_,_,(ts ++ τs''). iFrame "H H0 H1 H2".
        iSplitL "H3".
        { iDestruct "H3" as "[%Hcontr|#Hw]";[done|].
          iRight.
          iDestruct "Hw" as (w0 Heq') "Hw". simplify_eq.
          iExists _. iSplit;eauto.
          rewrite -app_assoc. rewrite Hbase'.
          iApply big_sepL2_app;eauto. }
        iDestruct (big_sepL2_length with "Hv1") as %Hlen1.
        rewrite Hbase' Hbase.
        rewrite app_length -drop_drop -Hlen1 drop_app. iFrame.
      }
      { rewrite Hbase in Hbase'. rewrite Hbase'.
        iExists _,_,_,_,_,_,_,(τs''). iFrame "H H0 H1 H2". iFrame.
      }
    }
    { iRight. iRight. iRight.
      iDestruct "Hw" as (sh ws' -> Hbase) "Hret".
      destruct (tc_return C);[|done].
      iDestruct "Hret" as (τs'') "Hret".
      iExists (sh_push_const sh _),_.
      unfold val_combine.

      iSplit;[auto|]. iSplit;[auto|].
      iDestruct "Hret" as "[#Hws' Hret]".
      iDestruct "Hws'" as "[%Hcontr|Hws']";[done|].
      iDestruct "Hws'" as (ws'' Heqws'') "Hws'". inversion Heqws''. subst ws''.

      pose proof (simple_get_base_l_push_const sh ws1) as [Hbase'|Hbase'].
      { rewrite Hbase' Hbase.
        iExists (ts ++ τs'').
        iSplitR.
        { rewrite -app_assoc. iRight.
          iExists _. iSplit;eauto.
          iApply big_sepL2_app;iFrame "#". }

        simpl of_val.
        rewrite -(take_drop (length τs'') ws') in Hbase.
        rewrite Hbase in Hbase'. rewrite app_assoc in Hbase'.
        
        pose proof (sfill_to_lfilled (sh_push_const sh ws1) ([AI_basic BI_return])) as Hj.
        pose proof (sfill_to_lfilled sh ([AI_basic BI_return])) as Hj'.
        eapply lfilled_simple_get_base_pull in Hj as Hj2;eauto.
        destruct Hj2 as [lh' Hlh'].
        eapply lfilled_simple_get_base_pull in Hj' as Hj3;eauto.
        destruct Hj3 as [lh'' Hlh''].
        
        iDestruct (big_sepL2_length with "Hws'") as %Hlen.
        rewrite app_length in Hlen.
        rewrite -(take_drop (length τs'') ws').
        iDestruct (big_sepL2_app_inv with "Hws'") as "[Hws1 Hws2]".
        { right. rewrite drop_length. lia. }
        iDestruct (big_sepL2_length with "Hws2") as %Hlen'.        

        iIntros (f0 f1) "Hf". iSpecialize ("Hret" $! f0 with "[$]").
        iApply (wp_ret_shift with "Hret");[| |apply Hlh''|apply Hlh'].
        { apply const_list_of_val. }
        { rewrite fmap_length. auto. }
      }
      { rewrite Hbase in Hbase'. rewrite Hbase'.
        iExists (τs'').
        iSplitR.
        { iRight. iExists _. iSplit;eauto. }

        simpl of_val.
        rewrite -(take_drop (length τs'') ws') in Hbase.
        rewrite -(take_drop (length τs'') ws') in Hbase'.
        
        pose proof (sfill_to_lfilled (sh_push_const sh ws1) ([AI_basic BI_return])) as Hj.
        pose proof (sfill_to_lfilled sh ([AI_basic BI_return])) as Hj'.
        eapply lfilled_simple_get_base_pull in Hj as Hj2;eauto.
        destruct Hj2 as [lh' Hlh'].
        eapply lfilled_simple_get_base_pull in Hj' as Hj3;eauto.
        destruct Hj3 as [lh'' Hlh''].
        
        iDestruct (big_sepL2_length with "Hws'") as %Hlen.
        rewrite app_length in Hlen.
        rewrite -(take_drop (length τs'') ws').
        iDestruct (big_sepL2_app_inv with "Hws'") as "[Hws1 Hws2]".
        { right. rewrite drop_length. lia. }
        iDestruct (big_sepL2_length with "Hws2") as %Hlen'.        

        iIntros (f0 f1) "Hf". iSpecialize ("Hret" $! f0 with "[$]").
        iApply (wp_ret_shift with "Hret");[| |apply Hlh''|apply Hlh'].
        { apply const_list_of_val. }
        { rewrite fmap_length. auto. }
      }
      
    }
  Qed.
    

End fundamental.
