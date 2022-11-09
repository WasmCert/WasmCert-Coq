From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris_fundamental_helpers stack_instantiation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section StackModule.
  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}.

  Set Bullet Behavior "Strict Subproofs".

  Lemma stackModuleInvIff P1 P2 Q :
    (∀ n l, P1 n l ≡ P2 n l) -> ⊢ (stackModuleInv P1 Q ∗-∗ @stackModuleInv Σ P2 Q)%I.
  Proof.
    intros Hcond.
    iSplit;iIntros "H".
    - iDestruct "H" as (?) "(? & ? & Hl)".
      iExists _. iFrame.
      iDestruct "Hl" as (?) "[? Hl]".
      iExists _. iFrame.
      iApply (big_sepL_mono with "Hl").
      intros. simpl. iIntros "H".
      iDestruct "H" as (stk) "H".
      rewrite Hcond. eauto.
    - iDestruct "H" as (?) "(? & ? & Hl)".
      iExists _. iFrame.
      iDestruct "Hl" as (?) "[? Hl]".
      iExists _. iFrame.
      iApply (big_sepL_mono with "Hl").
      intros. simpl. iIntros "H".
      iDestruct "H" as (stk) "H".
      rewrite - Hcond. eauto.
  Qed.      
  
  Lemma instantiate_stack_valid `{!logrel_na_invs Σ} (s : stuckness) (E: coPset) (exp_addrs: list N) (stack_mod_addr : N):
    length exp_addrs = 8 ->
  (* Knowing we hold the stack module… *)
  stack_mod_addr ↪[mods] stack_module -∗
   (* … and we own the vis pointers … *)
   own_vis_pointers exp_addrs -∗
     (* … instantiating the stack-module (by lazyness, this is expressed here with
        a take 1 in order to avoir rewriting the instantiation), yields the following : *)
     WP ((stack_instantiate_para exp_addrs stack_mod_addr, []) : host_expr)
     @ s ; E
             {{ λ v : host_val,
                 (* Instantiation succeeds *)
                 ⌜ v = immHV [] ⌝ ∗
                 (* we still own the stack_module *)
                 stack_mod_addr ↪[mods] stack_module ∗ 
                  ∃ (idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt : nat)
                    (name0 name1 name2 name3 name4 name5 name6 name7 : name)
                    (f0 f1 f2 f3 f4 f5 f6: list basic_instruction)
                    (i0 : instance)
                    (l0 l1 l2 l3 l4 l5 l6: list value_type)
                    tab 
                    (isStack : N -> seq.seq i32 -> iPropI Σ)
                    (nextStackAddrIs : nat -> iPropI Σ), 
                    (* Our exports are in the vis 0%N thru 7%N. Note that everything is 
                       existantially quantified. In fact, all the f_i, i_i and l_i 
                       could be given explicitely, but we quantify them existantially 
                       to show modularity : we do not care what the functions are, 
                       we only care about their spec (see next comment). This also
                       makes this lemma more readable than if we stated explicitely all
                       the codes of the functions *)
                    let inst_vis := (map (λ '(name, idf),
                                                 {| modexp_name := name ;
                                                   modexp_desc := MED_func (Mk_funcidx idf)
                                                 |}) [(name0, idf0) ; (name1, idf1) ;
                                                      (name2, idf2) ; (name3, idf3) ;
                                                      (name4, idf4) ; (name5, idf5); (name6, idf6) ])
                                        ++ [ {| modexp_name := name7 ;
                                               modexp_desc := MED_table (Mk_tableidx idt) |} ]
                    in let inst_map := (list_to_map (zip (fmap N.of_nat [idf0; idf1; idf2; idf3; idf4; idf5; idf6])
                                                    [(FC_func_native i0 (Tf [] [T_i32]) l0 f0) ;
                                                     (FC_func_native i0 (Tf [T_i32] [T_i32]) l1 f1) ;
                                                     (FC_func_native i0 (Tf [T_i32] [T_i32]) l2 f2) ;
                                                     (FC_func_native i0 (Tf [T_i32] [T_i32]) l3 f3) ;
                                                     (FC_func_native i0 (Tf [T_i32; T_i32] []) l4 f4) ;
                                                     (FC_func_native i0 (Tf [T_i32; T_i32] []) l5 f5) ;
                                                     (FC_func_native i0 (Tf [T_i32] [T_i32]) l6 f6)]))
                    in let inst_map_exp := (list_to_map (zip (fmap N.of_nat [idf0; idf1; idf2; idf3; idf4])
                                                    [(FC_func_native i0 (Tf [] [T_i32]) l0 f0) ;
                                                     (FC_func_native i0 (Tf [T_i32] [T_i32]) l1 f1) ;
                                                     (FC_func_native i0 (Tf [T_i32] [T_i32]) l2 f2) ;
                                                     (FC_func_native i0 (Tf [T_i32] [T_i32]) l3 f3) ;
                                                     (FC_func_native i0 (Tf [T_i32; T_i32] []) l4 f4)])) in
                    let tab_data := tab.(table_data) in
                    let tab_size := length tab_data in
                    (* These two import functions state that all [vis] and [wf] point 
                       to the correct exports/functions, i.e. a client will be able 
                       to successfully import them *)
                    import_resources_host exp_addrs inst_vis ∗
                    import_resources_wasm_typecheck_sepL2 inst_vis expts inst_map
                    (<[ N.of_nat idt := tab ]> ∅) 
                    ∅ ∅ ∗
                    ⌜ NoDup (modexp_desc <$> inst_vis) ⌝ ∗
                    (* This is technically redundant, but is commonly used in other modules that import the stack *)
                    ⌜ NoDup [idf0; idf1; idf2; idf3; idf4; idf5; idf6] ⌝ ∗
                    ⌜ tab_size >= 1 ⌝ ∗
                    na_inv logrel_nais stkN (stackModuleInv (λ n, isStack n) nextStackAddrIs) ∗
                    (* table starts out as empty *)
                    ([∗ list] elem ∈ tab_data, ⌜elem = None⌝) ∗
                    (* each export function is valid *)
                    [∗ map] f↦cl ∈ inst_map_exp, interp_closure [] (cl_type cl) cl
             }}.
  Proof.
    iIntros (Hvislen) "Hmod Hvis".
    do 9 (destruct exp_addrs => //).
    iDestruct (own_vis_pointers_nodup with "Hvis") as "%Hnodup".
    iApply (weakestpre.wp_strong_mono s _ E
             with "[Hmod Hvis]") => //.
    iApply (instantiation_spec_operational_no_start
             with "[Hmod Hvis]") ;
      try exact module_typing_stack => //.
    - by unfold stack_module.
    - unfold module_restrictions => /=.
      repeat split => //=.
      exists [] => //.
      exists [] => //.
      exists [] => //.
    - unfold instantiation_resources_pre.
      iSplitL "Hmod" ; first done.
      unfold instantiation_resources_pre_wasm.
      rewrite irwt_nodup_equiv.
      repeat iSplit.
      + by unfold import_resources_host.
      + iPureIntro. apply dom_empty.
      + iPureIntro. apply dom_empty.
      + iPureIntro. apply dom_empty.
      + iPureIntro. apply dom_empty.
      + done.
      + iPureIntro. unfold module_elem_bound_check_gmap => //=.
      + iPureIntro. unfold module_data_bound_check_gmap => //=.
      + by iFrame. 
      + done.
      + simpl. by apply NoDup_nil.
        
    - iIntros (v) "Hinst".
      unfold instantiation_resources_post.
      iDestruct "Hinst" as "(%Hvsucc & Hmod & Himphost & Hinst)".
      iFrame "Hmod".
      subst v; iSplitR => //.
      iDestruct "Hinst" as (inst) "[Himpwasm Hexphost]".
      iDestruct "Himpwasm" as (g_inits t_inits m_inits gms wts wms) "(Himpwasm & %Hinst & -> & -> & %Hbound & -> & -> & %Hbound' & %Hginit & -> & Hexpwasm)".
      destruct Hinst as (Hinsttype & Hinstfunc & Hinsttab & Hinstmem & Hinstglob).

      Opaque list_to_map.
      Opaque zip_with.
      
      unfold module_inst_resources_wasm, module_export_resources_host => /=.
      destruct inst => /=.
      iDestruct "Hexpwasm" as "(Hwf & Hwt & Hwm & Hwg)".
      iDestruct (module_inst_resources_func_nodup with "Hwf") as "%Hnodupwf".
      unfold module_inst_resources_func, module_inst_resources_tab, module_inst_resources_mem => /=.

      simpl in Hinsttype; subst inst_types.
      
      iDestruct (big_sepL2_length with "Hwf") as "%Hiflen".
      simpl in Hiflen.
      unfold get_import_func_count in * => /=; simpl in Hiflen.

      iDestruct (big_sepL2_length with "Hwt") as "%Hitlen".
      simpl in Hitlen.
      unfold get_import_table_count in * => /=; simpl in Hitlen.
      
      iDestruct (big_sepL2_length with "Hwm") as "%Himlen".
      simpl in Himlen.
      unfold get_import_mem_count in * => /=; simpl in Himlen.
      
      iDestruct (big_sepL2_length with "Hwg") as "%Higlen".
      simpl in Higlen.
      unfold get_import_global_count in * => /=; simpl in Higlen.

      rewrite -> drop_0 in *.

      do 8 (destruct inst_funcs => //).
      do 2 (destruct inst_tab => //).
      do 2 (destruct inst_memory => //).
      destruct inst_globs => //.
      iExists f, f0, f1, f2, f3, f4, f5, t.

      iSimpl in "Hexphost".
      iDestruct "Hexphost" as "(Hexp0 & Hexp1 & Hexp2 & Hexp3 & Hexp4 & Hexp5 & Hexp6 & Hexp7 & _)".
      iDestruct "Hexp0" as (name0) "Hexp0".
      iDestruct "Hexp1" as (name1) "Hexp1".
      iDestruct "Hexp2" as (name2) "Hexp2".
      iDestruct "Hexp3" as (name3) "Hexp3".
      iDestruct "Hexp4" as (name4) "Hexp4".
      iDestruct "Hexp5" as (name5) "Hexp5".
      iDestruct "Hexp6" as (name6) "Hexp6".
      iDestruct "Hexp7" as (name7) "Hexp7".
      iExists name0, name1, name2, name3, name4, name5, name6, name7.
      
      iExists _, _, _, _, _, _, _.
      iExists _.
      iExists _, _, _, _, _, _, _.
      iExists _.
      iExists (λ a b, isStack a b m).
      iExists (λ n, (N.of_nat m↦[wmlength] N.of_nat n)%I).

      iSplitL "Hexp0 Hexp1 Hexp2 Hexp3 Hexp4 Hexp5 Hexp6 Hexp7"; first by iFrame => /=.
      
      iDestruct "Hwf" as "(Hf & Hf0 & Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & _)".
      iDestruct "Hwt" as "(Ht & _)".
      iDestruct "Hwm" as "(Hm & _)".

      iDestruct "Hm" as "(Hmem & Hmemlength & Hmlim)".
      
      iSplitL "Hf Hf0 Hf1 Hf2 Hf3 Hf4 Hf5 Ht".
      { unfold import_resources_wasm_typecheck_sepL2.
        iSplitR.
        { unfold import_resources_wasm_domcheck.
          by repeat rewrite dom_insert.
        }
        { simpl.
          apply (NoDup_fmap_2 N.of_nat) in Hnodupwf.
          iSplitL "Hf";
            last iSplitL "Hf0"; 
            last iSplitL "Hf1"; 
            last iSplitL "Hf2"; 
            last iSplitL "Hf3"; 
            last iSplitL "Hf4"; 
            last iSplitL "Hf5";
            last first.
          { iModIntro; iSplit => //.
            iExists _, _.
            iFrame.
            rewrite lookup_insert.
            iPureIntro.
            by split => //.
          }
          all: (iExists _; iFrame; rewrite - elem_of_list_to_map => //=; iPureIntro; split => //; apply elem_of_list_In; repeat ((try by left); right)).
        }
      }
      
      iSplitR.
      { iPureIntro.
        eapply (NoDup_fmap_2 (λ x, (MED_func (Mk_funcidx x)))) in Hnodupwf.
        { simpl in Hnodupwf.
          rewrite separate7.
          apply NoDup_app; split => //.
          split => //; last by apply NoDup_singleton.
          by set_solver+.
        }
        Unshelve.
        { move => x y Heq. by inversion Heq. }
      }

      iSplitR => //.
      
      iSplitR => //=; first by iPureIntro; lia.

        iMod (na_inv_alloc logrel_nais _ stkN (stackModuleInv _ (λ n : nat, N.of_nat m↦[wmlength]N.of_nat n)%I) with "[Hmemlength]") as "#Hstk".
        { iNext. iExists 0. iSplit.
          - iPureIntro. apply N.divide_0_r.
          - iFrame. iExists []. simpl. iSplit;auto. iPureIntro. constructor. lias. }
        iFrame "Hstk". iClear "∗".
        set (i0 := {| inst_types := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
                     inst_funcs := [f; f0; f1; f2; f3; f4];
                     inst_tab := [t];
                     inst_memory := [m];
                     inst_globs := []
                   |}).
        iSplitR;[simpl;auto|].
        iDestruct (na_inv_iff with "Hstk []") as "Hstk'".
        { iNext; iModIntro. iSplit.
          - iIntros "H". iDestruct (stackModuleInvIff with "H") as "H";[|iExact "H"].
            intros. simpl. 
            apply class_instances.as_emp_valid_equiv.
            iSplit;iIntros "H";iExact "H".
          - iIntros "H". iDestruct (stackModuleInvIff with "H") as "H";[|iExact "H"].
            intros. simpl.
            apply class_instances.as_emp_valid_equiv.
            iSplit;iIntros "H";iExact "H". }

        iApply big_opM_map_to_list.
        rewrite map_to_list_to_map; last first.
        { rewrite fst_zip => //. rewrite separate5 in Hnodupwf.
          apply NoDup_app in Hnodupwf as [Hnodupwf _].
          by apply (NoDup_fmap_2 N.of_nat) in Hnodupwf.
        }
        iModIntro.
        Transparent zip_with.
        simpl.
        repeat (iSplitR => //; first (iSplit => //; iIntros "!>!>")).
        * iApply (valid_new_stack with "Hstk'").
        * iApply (valid_is_empty with "Hstk'").
        * iApply (valid_is_full with "Hstk'").
        * iApply (valid_pop with "Hstk'").
        * iApply (valid_push with "Hstk'").
  Qed.        
   
End StackModule.
