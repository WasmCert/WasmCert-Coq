From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_fundamental_helpers stack_specs stack_instantiation.
Require Export datatypes operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Section StackModule.
  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}.

  Set Bullet Behavior "Strict Subproofs".

  Definition stack_t_context :=
  {| tc_types_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
    tc_func_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []; Tf [T_i32; T_i32] []];
    tc_global := [];
    tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
    tc_memory := [ {| lim_min := 0; lim_max := None |}];
    tc_local := [];
    tc_label := [];
    tc_return := None
  |}.

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
  
  Lemma instantiate_stack_valid `{!logrel_na_invs Σ} (s : stuckness) (E: coPset) (hv0 hv1 hv2 hv3 hv4 hv5 hv6 : module_export) :
  (* Knowing 0%N holds the stack module… *)
  0%N ↪[mods] stack_module -∗
     (* … and we own the vis 0%N thru 4%N … *)
     ([∗ list] k↦hvk ∈ [hv0 ; hv1 ; hv2 ; hv3 ; hv4 ; hv5 ; hv6], N.of_nat k ↪[vis] hvk) -∗
     (* … instantiating the stack-module (by lazyness, this is expressed here with
        a take 1 in order to avoir rewriting the instantiation), yields the following : *)
     WP ((stack_instantiate, []) : host_expr)
     @ s ; E
             {{ λ v : host_val,
                 (* Instantiation succeeds *)
                 ⌜ v = immHV [] ⌝ ∗
                 (* 0%N still owns the stack_module *)
                 0%N ↪[mods] stack_module ∗ 
                  ∃ (idf0 idf1 idf2 idf3 idf4 idf5 idt : nat)
                    (name0 name1 name2 name3 name4 name5 name6 : name)
                    (f0 f1 f2 f3 f4 f5 : list basic_instruction)
                    (i0 : instance)
                    (l0 l1 l2 l3 l4 l5 : list value_type)
                    tab 
                    (isStack : Z -> seq.seq i32 -> iPropI Σ)
                    (nextStackAddrIs : nat -> iPropI Σ), 
                    (* Our exports are in the vis 0%N thru 4%N. Note that everything is 
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
                                                      (name4, idf4) ; (name5, idf5) ])
                                        ++ [ {| modexp_name := name6 ;
                                               modexp_desc := MED_table (Mk_tableidx idt) |} ]
                    in 
                    let inst_map := fold_left (λ fs '(idf,i,t,l,f),
                                                <[ N.of_nat idf := FC_func_native i t l f ]> fs)
                                              (rev [(idf0, i0, Tf [] [T_i32], l0, f0) ;
                                               (idf1, i0, Tf [T_i32] [T_i32], l1, f1) ;
                                                    (idf2, i0, Tf [T_i32] [T_i32], l2, f2) ;
                                                    (idf3, i0, Tf [T_i32] [T_i32], l3, f3) ;
                                                    (idf4, i0, Tf [T_i32 ; T_i32] [], l4, f4) ;
                                              (idf5, i0, Tf [T_i32 ; T_i32] [], l5, f5)])
                                              ∅ in
                    let tab_data := tab.(table_data) in
                    let tab_size := length tab_data in
                    (* These two import functions state that all [vis] and [wf] point 
                       to the correct exports/functions, i.e. a client will be able 
                       to successfully import them *)
                    import_resources_host [0%N; 1%N; 2%N; 3%N; 4%N ; 5%N ; 6%N] inst_vis ∗
                    import_resources_wasm_typecheck_sepL2 inst_vis expts inst_map
                    (<[ N.of_nat idt := tab ]> ∅) 
                    ∅ ∅ ∗
                    ⌜ NoDup (modexp_desc <$> inst_vis) ⌝ ∗
                    ⌜ tab_size >= 1 ⌝ ∗
                    na_inv logrel_nais stkN (stackModuleInv (λ n, isStack (Z.of_N n)) nextStackAddrIs) ∗
                    (* table starts out as empty *)
                    ([∗ list] elem ∈ tab_data, ⌜elem = None⌝) ∗
                    (* each export function is valid *)
                    [∗ map] f↦cl ∈ delete (N.of_nat idf5) inst_map, interp_closure [] (cl_type cl) cl
             }}.
  Proof.
    iIntros "Hmod (Hhv0 & Hhv1 & Hhv2 & Hhv3 & Hhv4 & Hhv5 & Hhv6 & _)".
    iApply (weakestpre.wp_strong_mono s _ E
             with "[Hmod Hhv0 Hhv1 Hhv2 Hhv3 Hhv4 Hhv5 Hhv6]") => //.
    iApply (instantiation_spec_operational_no_start
             with "[Hmod Hhv0 Hhv1 Hhv2 Hhv3 Hhv4 Hhv5 Hhv6]") ;
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
      + unfold export_ownership_host.
        iSplitL "Hhv0".
        by iExists _.
        iSplitL "Hhv1".
        by iExists _.
        iSplitL "Hhv2".
        by iExists _.
        iSplitL "Hhv3".
        by iExists _.
        iSplitL "Hhv4".
        by iExists _.
        iSplitL "Hhv5".
        by iExists _.
        iSplitL "Hhv6".
        by iExists _.
        done.
      + done.
      + simpl. by apply NoDup_nil.
    - iIntros (v) "Hinst".
      unfold instantiation_resources_post.
      iDestruct "Hinst" as "(%Hvsucc & Hmod & Himphost & Hinst)".
      subst v; iSplitR => //.
      iDestruct "Hinst" as (inst) "[Himpwasm Hexphost]".
      iDestruct "Himpwasm" as (g_inits t_inits m_inits gms wts wms) "(Himpwasm & %Hinst & -> & -> & %Hbound & -> & -> & %Hbound' & %Hginit & -> & Hexpwasm)".
      destruct Hinst as (Hinsttype & Hinstfunc & Hinsttab & Hinstmem & Hinstglob).
      unfold module_inst_resources_wasm, module_export_resources_host => /=.
      destruct inst => /=.
      iDestruct "Hexpwasm" as "(Hexpwf & Hexpwt & Hexpwm & Hexpwg)".
      unfold module_inst_resources_func, module_inst_resources_glob,
        module_inst_resources_tab, module_inst_resources_mem => /=.
      unfold big_sepL2 => /=.
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf Hexpwf]".
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf0 Hexpwf]".
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf1 Hexpwf]".
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf2 Hexpwf]".
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf3 Hexpwf]".
      destruct inst_funcs as [| ? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf4 Hexpwf]".
      destruct inst_funcs ; last done.
      destruct inst_tab ; first done.
      iDestruct "Hexpwt" as "[Htab Hexpwt]".
      destruct inst_tab ; last done.
      destruct inst_memory as [|m inst_memory] ; first done.
      iDestruct "Hexpwm" as "[Hexpwm ?]".
      destruct inst_memory ; last done.
      iDestruct "Hexpwm" as "(Hexpwm & Hmemlength & Hmemlim)".
      destruct inst_globs ; last done.
      iDestruct "Hexphost" as "(Hexp0 & Hexp1 & Hexp2 & Hexp3 & Hexp4 & Hexp5 & Hexp6 & _)".
      iDestruct "Hexp0" as (name0) "Hexp0".
      iDestruct "Hexp1" as (name1) "Hexp1".
      iDestruct "Hexp2" as (name2) "Hexp2".
      iDestruct "Hexp3" as (name3) "Hexp3".
      iDestruct "Hexp4" as (name4) "Hexp4".
      iDestruct "Hexp5" as (name5) "Hexp5".
      iDestruct "Hexp6" as (name6) "Hexp6".
      simpl in * ; subst.
      iSplitL "Hmod" ; first done.
      iExists f, f0, f1, f2, f3, f4, t.
      iExists name0, name1, name2, name3, name4, name5, name6.
      iExists _, _, _, _, _, _.
      iExists _.
      iExists _, _, _, _, _, _.
      iExists _.
      iExists (λ a b, isStack (Z.to_N a) b m).
      iExists (λ n, (N.of_nat m↦[wmlength] N.of_nat n)%I).
      iDestruct (mapsto_frac_ne with "Hf Hf0") as "%H01" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf Hf1") as "%H02" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf Hf2") as "%H03" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf Hf3") as "%H04" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf Hf4") as "%H05" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf0 Hf1") as "%H12" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf0 Hf2") as "%H13" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf0 Hf3") as "%H14" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf0 Hf4") as "%H15" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf1 Hf2") as "%H23" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf1 Hf3") as "%H24" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf1 Hf4") as "%H25" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf2 Hf3") as "%H34" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf2 Hf4") as "%H35" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf3 Hf4") as "%H45" ; first by eauto.
      iSplitL "Hexp0 Hexp1 Hexp2 Hexp3 Hexp4 Hexp5 Hexp6".
      unfold import_resources_host.
      iFrame. by iModIntro.
      iSplitL "Hf Hf0 Hf1 Hf2 Hf3 Hf4 Htab".
      iSplitR.
      + iPureIntro.
        simpl.
        repeat rewrite dom_insert.
        done.
      + iSplitL "Hf".
        iExists _.
        iFrame.
        iPureIntro.
        rewrite lookup_insert.
        split => //.
        iSplitL "Hf0".
        iExists _ ; iFrame.
        iPureIntro.
        rewrite lookup_insert_ne ; last assumption.
        rewrite lookup_insert.
        split => //.
        iSplitL "Hf1".
        iExists _ ; iFrame.
        iPureIntro.
        do 2 (rewrite lookup_insert_ne ; last assumption).
        rewrite lookup_insert.
        split => //.
        iSplitL "Hf2".
        iExists _ ; iFrame.
        iPureIntro.
        do 3 (rewrite lookup_insert_ne ; last assumption).
        rewrite lookup_insert.
        split => //.
        iSplitL "Hf3".
        iExists _ ; iFrame.
        iPureIntro.
        do 4 (rewrite lookup_insert_ne ; last assumption).
        rewrite lookup_insert.
        split => //.
        iSplitL "Hf4".
        iExists _ ; iFrame.
        iPureIntro.
        do 5 (rewrite lookup_insert_ne ; last assumption).
        rewrite lookup_insert.
        split => //.
        iSplitL; cbn; last done.
        iExists _, _ ; iFrame.
        iPureIntro.
        rewrite lookup_insert.
        split => //.
      + iSplitR.
        { iPureIntro.
          repeat (apply NoDup_cons; split; cbn; first by set_solver).
          by apply NoDup_nil.
        }
        iSplitR.
        iPureIntro.
        simpl.
        lia.

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
            intros. simpl. rewrite N2Z.id.
            apply class_instances.as_emp_valid_equiv.
            iSplit;iIntros "H";iExact "H".
          - iIntros "H". iDestruct (stackModuleInvIff with "H") as "H";[|iExact "H"].
            intros. simpl. rewrite N2Z.id.
            apply class_instances.as_emp_valid_equiv.
            iSplit;iIntros "H";iExact "H". }
        
        repeat (rewrite delete_insert_ne;[|done]). 
        repeat (rewrite big_sepM_insert;[|simplify_map_eq; done]).
        rewrite delete_insert;[|auto].
        repeat iSplitR;iModIntro;[..|iApply big_sepM_empty;done];auto;iModIntro;iNext.
        * iApply (valid_new_stack with "Hstk'").
        * iApply (valid_is_empty with "Hstk'").
        * iApply (valid_is_full with "Hstk'").
        * iApply (valid_pop with "Hstk'").
        * iApply (valid_push with "Hstk'").
  Qed.        
   
End StackModule.
