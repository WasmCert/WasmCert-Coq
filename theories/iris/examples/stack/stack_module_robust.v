From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_fundamental_helpers stack_specs stack_instantiation iris_interp_instance_alloc proofmode.
Require Export iris_example_helper.
Require Export datatypes operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.
   

Section RobustStack.
  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ,
      !logrel_na_invs Σ, !hasG Σ}.

  Notation "{{{ P }}} es {{{ v , Q }}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).
  
  Definition stack_adv_instantiate :=
    [ ID_instantiate [0%N ; 1%N ; 2%N ; 3%N ; 4%N ; 5%N ; 6%N] 0 [] ;
      ID_instantiate [] 1 [0%N ; 1%N ; 2%N ; 3%N ; 4%N ; 5%N ; 6%N] ].

  Definition stack_module_imports := expts.

  Lemma instantiate_stack_adv_spec adv_module start :
    module_typing adv_module expts [] -> (* we assume the adversary module imports the stack module) *)
    mod_start adv_module = Some start -> (* that it does have a start function *)
    module_restrictions adv_module -> (* that it adheres to the module restrictions (i.e. only constant initializers for globals) *)
    module_elem_bound_check_gmap ∅ [] adv_module -> (* if the adversary module declares a table, there cannot be more initializers that its size *)
    module_data_bound_check_gmap ∅ [] adv_module -> (* if the adversary module declares a memory, there cannot be more initializers that its size *)

    ⊢ {{{ 0%N ↪[mods] stack_module ∗
          1%N ↪[mods] adv_module ∗
          na_own logrel_nais ⊤ ∗
          (∃ vs0 vs1 vs2 vs3 vs4 vs5 vs6, [∗ list] v↦vs∈[vs0;vs1;vs2;vs3;vs4;vs5;vs6], N.of_nat v ↪[vis] vs) ∗
          ↪[frame] empty_frame
      }}}
        ((stack_adv_instantiate,[]) : host_expr) 
      {{{ v, True }}} .
  Proof.
    iIntros (Htyp Hnostart Hrestrict Hboundst Hboundsm).
    iModIntro. iIntros (Φ) "(Hmod_stack & Hmod_adv & Hown & 
                        Hvisvst & Hemptyframe) HΦ".
    iDestruct "Hvisvst" as (vs0 vs1 vs2 vs3 vs4 vs5 vs6) "Hvis".

    (* instantiate stack module *)
    iApply (wp_seq_host_nostart NotStuck with "[] [$Hmod_stack] [Hvis] ") => //.
    2: { iIntros "Hmod_stack".
      iApply weakestpre.wp_mono;cycle 1.
      iApply (instantiate_stack_spec with "[$]").
      { iFrame "Hvis". }
      iIntros (v) "[Hvsucc [$ Hv]]".
      iCombine "Hvsucc Hv" as "Hv".
      iExact "Hv". }
    { by iIntros "(% & ?)". }
    iIntros (w) "Hstack Hmod_stack".

    iDestruct "Hstack" as "(-> & Hstack)".
    
    iDestruct "Hstack" as (idf0 idf1 idf2 idf3 idf4 idf5 idt) "Hstack".
    iDestruct "Hstack" as (nm0 nm1 nm2 nm3 nm4 nm5 nm6 f0 f1 f2) "Hstack".
    iDestruct "Hstack" as (f3 f4 f5 istack l0 l1 l2 l3 l4 l5) "Hstack".
    iDestruct "Hstack" as (stacktab isStack newStackAddrIs) "Hstack".
    iDestruct "Hstack" as "(HimpsH & HimpsW & %Hnodup & %Htablen & HnewStackAddrIs 
    & #Hnewstack & #Hisempty & #Hisfull & #Hpop & #Hpush & #Hmap & #Hmaptrap) /=".
    
    (* Cleanup of stack resources *)
    iDestruct "HimpsW" as "(_ & Hidf0 & Hidf1 & Hidf2 & Hidf3 & Hidf4 & Hidf5 & Hidtab & _) /=".
     repeat (rewrite lookup_insert + (rewrite lookup_insert_ne;[|done])).
    iDestruct "Hidf0" as (cl0) "[Himpfcl0 Hcl0]".
    iDestruct "Hidf1" as (cl1) "[Himpfcl1 Hcl1]".
    iDestruct "Hidf2" as (cl2) "[Himpfcl2 Hcl2]".
    iDestruct "Hidf3" as (cl3) "[Himpfcl3 Hcl3]".
    iDestruct "Hidf4" as (cl4) "[Himpfcl4 Hcl4]".
    iDestruct "Hidf5" as (cl5) "[Himpfcl5 Hcl5]".
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl1") as "%H01" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl2") as "%H02" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl3") as "%H03" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl4") as "%H04" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl5") as "%H05" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl2") as "%H12" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl3") as "%H13" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl4") as "%H14" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl5") as "%H15" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl2 Himpfcl3") as "%H23" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl2 Himpfcl4") as "%H24" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl2 Himpfcl5") as "%H25" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl3 Himpfcl4") as "%H34" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl3 Himpfcl5") as "%H35" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl4 Himpfcl5") as "%H45" ; first by eauto.
    repeat (rewrite lookup_insert + (rewrite lookup_insert_ne;[|done])).
    iDestruct "Hcl0" as %[Heq1 Heq2];inversion Heq1;inversion Heq2;clear Heq1 Heq2.
    iDestruct "Hcl1" as %[Heq1 Heq2];inversion Heq1;inversion Heq2;clear Heq1 Heq2.
    iDestruct "Hcl2" as %[Heq1 Heq2];inversion Heq1;inversion Heq2;clear Heq1 Heq2.
    iDestruct "Hcl3" as %[Heq1 Heq2];inversion Heq1;inversion Heq2;clear Heq1 Heq2.
    iDestruct "Hcl4" as %[Heq1 Heq2];inversion Heq1;inversion Heq2;clear Heq1 Heq2.
    iDestruct "Hcl5" as %[Heq1 Heq2];inversion Heq1;inversion Heq2;clear Heq1 Heq2.
    subst cl0 cl1 cl2 cl3 cl4 cl5.
    iDestruct "Hidtab" as (tab tt) "[Hidtab [%Heq %Htt]]". inversion Heq;subst tab.
    clear H01 H02 H03 H04 H05 H12 H13 H14 H15 H23 H24 H25 H34 H35 H45 H1 H3 H5 H7 H9 H11.
    iDestruct "HimpsH" as "(Hvis0 & Hvis1 & Hvis2 & Hvis3 & Hvis4 & Hvis5 & Hvis6 & _)".

    (* instantiate adversary module *)

    (* first we must establish the validity of each import object *)
    

    

End RobustStack.
