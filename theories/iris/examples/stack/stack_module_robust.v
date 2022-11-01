From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_fundamental_helpers stack_specs stack_instantiation iris_interp_instance_alloc proofmode stack_instantiation_interp.
Require Export iris_example_helper.
Require Export datatypes operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.
   

Section RobustStack.
  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ,
      !logrel_na_invs Σ, !hasG Σ}.

  Set Bullet Behavior "Strict Subproofs".

  Notation "{{{ P }}} es {{{ v , Q }}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).
  
  Definition stack_adv_instantiate :=
    [ ID_instantiate [0%N ; 1%N ; 2%N ; 3%N ; 4%N ; 5%N ; 6%N] 0 [] ;
      ID_instantiate [] 1 [0%N ; 1%N ; 2%N ; 3%N ; 4%N ] ].

  Definition stack_module_imports :=
    [ET_func (Tf [] [T_i32]);
     ET_func (Tf [T_i32] [T_i32]);
     ET_func (Tf [T_i32] [T_i32]);
     ET_func (Tf [T_i32] [T_i32]);
     ET_func (Tf [T_i32; T_i32] [])].

  Lemma module_typing_exports_length m impts expts :
    module_typing m impts expts ->
    length (mod_exports m) = length expts.
  Proof.
    intros Hm.
    destruct Hm as [? [? Hm]].
    destruct m. simpl in Hm.
    destruct Hm as [_ [_ [_ [_ [_ [_ [_ [_ Hm]]]]]]]].
    apply Forall2_length in Hm. auto.
  Qed.

  Lemma interp_instance_func_lookup n f t l inst :
    inst_funcs inst !! n = Some f ->
    interp_instance t l inst -∗
    ∃ τf, ⌜tc_func_t t !! n = Some τf⌝ ∗ interp_function τf (λ _, interp_closure l) (N.of_nat f).
  Proof.
    iIntros (Hlook) "Hi".
    destruct t,inst;simpl in *.
    iDestruct "Hi" as "[_ [Hi _]]".
    iDestruct (big_sepL2_length with "Hi") as %Hlen.
    assert (is_Some (tc_func_t !! n)) as [x Hx].
    { apply lookup_lt_is_Some_2. rewrite - Hlen. apply lookup_lt_is_Some_1. eauto. }
    iExists x. iSplit;auto.
    iDestruct (big_sepL2_lookup with "Hi") as "HH";eauto.
  Qed.

  Lemma module_typing_start_type m impts expts fts gts t start idnstart inst n tf l :
    module_typing_body m impts expts fts gts ->
    tc_func_t t = ext_t_funcs impts ++ fts ->
    mod_start m = Some start ->
    modstart_func start = Mk_funcidx n ->
    inst_funcs inst !! n = Some idnstart ->
    tc_func_t t !! n = Some tf ->
    interp_instance t l inst -∗ ⌜tf = Tf [] []⌝.
  Proof.
    iIntros (Hmod Heq Hstart Hn Hinstn Htn) "Hi".
    destruct t, m, inst;simpl in *.
    iDestruct "Hi" as "[_ [Hi _]]".
    iDestruct (big_sepL2_lookup with "Hi") as (cl) "Hx";eauto.
    simpl in *. destruct Hmod as [_ [_ [_ [_ [_ [_ [Hmod _]]]]]]].
    simplify_eq. simpl in Hmod.
    unfold module_start_typing in Hmod.
    rewrite Hn /= in Hmod. apply andb_true_iff in Hmod as [Hle Hmod].
    rewrite nth_error_lookup in Hmod.
    rewrite Htn in Hmod.
    revert Hmod. move =>/eqP =>Hmod. auto.
  Qed.

  Lemma module_typing_func_not_import m impts expts fts gts t inst n r1 r2 f :
    t = {|tc_types_t := mod_types m;
      tc_func_t := (ext_t_funcs impts ++ fts)%list;
      tc_global := (ext_t_globs impts ++ gts)%list;
      tc_table := (ext_t_tabs impts ++ map (λ t : module_table, modtab_type t) (mod_tables m))%list;
      tc_memory := (ext_t_mems impts ++ (mod_mems m))%list;
      tc_local := [];
      tc_label := [];
      tc_return := None
    |} ->
    get_import_func_count m = length (ext_t_funcs impts) ->
    module_typing_body m impts expts fts gts ->
    inst_funcs inst !! n = Some f ->
    tc_func_t t !! n = Some (Tf r1 r2) ->
    (Tf r1 r2) ∉ ext_t_funcs impts ->
    ∃ n' fidx locs es, (drop (get_import_func_count m) (inst_funcs inst)) !! n' = Some f
                      ∧ mod_funcs m !! n' = Some {| modfunc_type := Mk_typeidx fidx; modfunc_locals := locs; modfunc_body := es |}
                      ∧ nth fidx (mod_types m) (Tf [] []) = Tf r1 r2
                      ∧ be_typing (upd_local_label_return t (r1 ++ locs) [r2] (Some r2)) es (Tf [] r2).
  Proof.
    intros Heq Hlen Hm Hn Htn Hnin.
    destruct m, inst, t;simpl in *.
    simplify_eq. inversion Heq;subst.
    destruct Hm as [Hfuncs _].
    rewrite Hlen.
    apply lookup_app_Some in Htn as [Hcontr | [Hlen' Htn]].
    { exfalso. apply Hnin. apply elem_of_list_lookup. eauto. }
    exists (n - length (ext_t_funcs impts)).
    eapply Forall2_lookup_r in Hfuncs as Hf;eauto.
    destruct Hf as [x [Hx Htyp]].
    destruct x. destruct modfunc_type.
    exists n0, modfunc_locals, modfunc_body.
    rewrite lookup_drop le_plus_minus_r //.
    destruct Htyp as [? [HH ?]]. simpl in *.
    repeat split;auto.     
    revert HH. move =>/eqP. auto.
  Qed.
    
  Lemma instantiate_stack_adv_spec adv_module start :
    module_typing adv_module stack_module_imports [] -> (* we assume the adversary module imports the stack module) *)
    mod_start adv_module = Some {| modstart_func := Mk_funcidx start |} -> (* that it does have a start function *)
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
        {{{ v, ((⌜v = trapHV ∨ v = immHV []⌝) ∗ na_own logrel_nais ⊤
                  ∗ ∃ newStackAddrIs isStack, na_inv logrel_nais stkN (stackModuleInv (λ n0, isStack (Z.of_N n0)) newStackAddrIs))
                 ∗ ↪[frame] empty_frame }}} .
  Proof.
    iIntros (Htyp Hnostart Hrestrict Hboundst Hboundsm).
    iModIntro. iIntros (Φ) "(Hmod_stack & Hmod_adv & Hown & 
                        Hvisvst & Hemptyframe) HΦ".
    iDestruct "Hvisvst" as (vs0 vs1 vs2 vs3 vs4 vs5 vs6) "Hvis".

    (* instantiate stack module *)
    iApply (wp_seq_host_nostart NotStuck with "[] [$Hmod_stack] [Hvis] ") => //.
    2: { iIntros "Hmod_stack".
      iApply weakestpre.wp_mono;cycle 1.
      iApply (instantiate_stack_valid with "[$]").
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
    iDestruct "Hstack" as "(HimpsH & HimpsW & %Hnodup & %Htablen & #Hinv & #Hnewstack & #Hinterp)".
    
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
    repeat (rewrite delete_insert_ne;[|done]). rewrite delete_insert;[|auto].
    clear (* H01 H02 H03 H04 H05 H12 H13 H14 H15 H23 H24 H25 H34 H35 H45 *) H1 H3 H5 H7 H9 H11.
    iDestruct "HimpsH" as "(Hvis0 & Hvis1 & Hvis2 & Hvis3 & Hvis4 & Hvis5 & Hvis6 & _)".

    (* instantiate adversary module *)
    iApply (weakestpre.wp_wand _ _ _ (λ v, _)%I with "[-HΦ] [HΦ]");cycle 1.
    { iIntros (v) "Hv". iApply "HΦ". iExact "Hv". }
    { iApply (instantiation_spec_operational_start_seq with "[$Hemptyframe] [$Hmod_adv Hvis0 Hvis1 Hvis2 Hvis3 Hvis4
      Himpfcl0 Himpfcl1 Himpfcl2 Himpfcl3 Himpfcl4]");[eauto|apply Htyp|auto|..].
      - instantiate (5:=[_;_;_;_;_]).
        unfold import_resources_host. iSimpl. iFrame "Hvis0 Hvis1 Hvis2 Hvis3 Hvis4".
        instantiate (1:=∅).
        instantiate (1:=∅).
        instantiate (1:=∅).
        instantiate (1:={[ (N.of_nat idf0):=_ ; (N.of_nat idf1):=_ ; (N.of_nat idf2):=_ ; (N.of_nat idf3):=_ ; (N.of_nat idf4):=_]}).
        
        iSplit;[iSplit;[|auto]|iSplit].
        + unfold import_resources_wasm_typecheck.
          iSplitL. unfold import_func_wasm_check,import_func_resources.
          rewrite /func_typecheck /func_domcheck /= !dom_insert_L !Forall2_cons Forall2_nil /=.
          iClear "Hinterp".
          do 4 (rewrite big_sepM_insert;[|simplify_map_eq;auto]).
          rewrite big_sepM_singleton. iFrame. simplify_map_eq.
          iSplit;iPureIntro. repeat split;eauto. set_solver -.
          repeat iSplit;auto.
          2: rewrite /tab_typecheck !Forall2_cons /= //.
          3: rewrite /mem_typecheck !Forall2_cons /= //.
          4: rewrite /glob_typecheck !Forall2_cons /= //.
          rewrite /import_tab_resources big_sepM_empty //.
          rewrite /import_mem_resources big_sepM_empty //.
          rewrite /import_glob_resources big_sepM_empty //.
        + unfold export_ownership_host. auto.
        + iPureIntro. erewrite module_typing_exports_length;eauto. auto.
      - iIntros (idnstart) "Hf Hres".
        iDestruct "Hres" as "[Hadv [Himp Hinst]]".
        iDestruct "Hinst" as (inst) "[Hres Hexpts]".
        unfold instantiation_resources_post_wasm.
        iDestruct "Hres" as (g_inits tab_allocs mem_allocs glob_allocs wts' wms')
                             "(Himpres & % & % & % & % & % & % & % & [% %] & % & Hres)".
        iApply weakestpre.fupd_wp.
        apply mod_imps_len_t in Htyp as Hcount.
        destruct Htyp as [fts [gts Htyp]]. simplify_eq.
        simpl in *. destruct H as [? [? [? [? [? ?]]]]].
        iMod (interp_instance_alloc with "[] [] [] Himpres Hres") as "[#Hi [Hres Himpres]]";[apply Htyp|auto|auto|..].
        { instantiate (1:=[]). iFrame "Hinterp". }
        { by iApply big_sepM_empty. }
        { by iApply big_sepM_empty. }
        iModIntro.
        rewrite -/(module_typing_body adv_module stack_module_imports [] fts gts) in Htyp.


        iApply wp_lift_wasm.
        take_drop_app_rewrite 0.
        destruct (mod_start adv_module) eqn:Hstart.
        2: { congruence. }
        destruct (modstart_func m) eqn:Hstartfunc.
        rewrite /check_start Hstart /= Hstartfunc /= nth_error_lookup in H8. apply b2p in H8.
        iDestruct (interp_instance_func_lookup with "Hi") as (tf Htf) "_";[eauto|].
        iDestruct (module_typing_start_type with "Hi") as %Heq;[apply Htyp|auto|apply Hstart|apply Hstartfunc|eauto|eauto|].
        subst tf.
        iDestruct "Hres" as "[Hres _]".
        unfold module_inst_resources_func_invs.
        eapply (module_typing_func_not_import) in Htyp as Hf;eauto;auto;cycle 1.
        { destruct Hcount as [-> _]. auto. }
        { simpl. set_solver -. }
        destruct Hf as [n' [fidx [locs [es [Hlook1 [Hlook2 [Hnth Hestyp]]]]]]].
        iDestruct (big_sepL2_lookup with "Hres") as "#Hstart";[eauto..|].
        iSimpl in "Hstart". rewrite H Hnth.
        iApply fupd_wp.
        iMod (na_inv_acc with "Hstart Hown") as "(>Hid & Hown & Hcls)";[solve_ndisj..|].
        iApply (wp_invoke_native with "Hf Hid");eauto.
        iModIntro. iNext. iIntros "[Hf Hid]".
        iApply fupd_wp. iMod ("Hcls" with "[$]") as "Hown".
        iModIntro.
        rewrite - wp_frame_rewrite.
        iApply wp_wasm_empty_ctx_frame.
        take_drop_app_rewrite 0.
        iApply (wp_block_local_ctx with "Hf");auto.
        iNext. iIntros "Hf".
        iApply wp_wasm_empty_ctx_frame.
        rewrite wp_frame_rewrite.
        iDestruct (be_fundamental_local with "Hi") as "Hcont";[auto|apply Hestyp|..].
        unfold interp_expression_closure_no_host.
        iApply (wp_wand with "[Hf Hown]").
        iApply ("Hcont" with "Hf Hown []").
        repeat erewrite app_nil_l.
        iRight. iExists _. iSplitR;[eauto|]. iApply n_zeros_interp_values.
        iIntros (v) "[[Hv Hown] Hf]".
        iDestruct "Hv" as "[-> | Hv]".
        + iApply weakestpre.wp_value;[unfold IntoVal;eapply of_to_val;eauto|].
          iFrame. auto.
        + iDestruct "Hv" as (ws) "[-> Hv]".
          iDestruct (big_sepL2_length with "Hv") as %Hnil. destruct ws;[|done].
          iApply weakestpre.wp_value;[unfold IntoVal;eapply of_to_val;eauto|].
          iFrame. auto. }
  Qed.

End RobustStack.
