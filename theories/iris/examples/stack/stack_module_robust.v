From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris_fundamental_helpers iris_interp_instance_alloc proofmode stack_instantiation_interp.
Require Export iris_example_helper.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section RobustStack.
  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ,
      !logrel_na_invs Σ, !hasG Σ}.

  Set Bullet Behavior "Strict Subproofs".

  Notation "{{{ P }}} es {{{ v , Q }}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).
  
  Definition stack_adv_instantiate :=
    [ ID_instantiate [0%N ; 1%N ; 2%N ; 3%N ; 4%N ; 5%N ; 6%N; 7%N] 0 [] ;
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
          own_vis_pointers [0%N; 1%N; 2%N; 3%N; 4%N; 5%N; 6%N; 7%N] ∗
          ↪[frame] empty_frame
      }}}
        ((stack_adv_instantiate,[]) : host_expr) 
        {{{ v, ((⌜v = trapHV ∨ v = immHV []⌝) ∗ na_own logrel_nais ⊤
                  ∗ ∃ newStackAddrIs isStack, na_inv logrel_nais stkN (stackModuleInv (λ n0, isStack n0) newStackAddrIs))
                 ∗ ↪[frame] empty_frame }}} .
  Proof.
    iIntros (Htyp Hnostart Hrestrict Hboundst Hboundsm).
    iModIntro. iIntros (Φ) "(Hmod_stack & Hmod_adv & Hown & 
                        Hvis & Hemptyframe) HΦ".

    (* instantiate stack module *)
    iApply (wp_seq_host_nostart NotStuck with "[] [$Hmod_stack] [Hvis] ") => //.
    2: { iIntros "Hmod_stack".
      iApply weakestpre.wp_mono;cycle 1.
      iApply (instantiate_stack_valid with "[$]") => //.
      iIntros (v) "[Hvsucc [$ Hv]]".
      iCombine "Hvsucc Hv" as "Hv".
      iExact "Hv". }
    { by iIntros "(% & ?)". }
    
    iIntros (w) "Hstack Hmod_stack".

    iDestruct "Hstack" as "(-> & Hstack)".
    
    iDestruct "Hstack" as (idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt) "Hstack".
    iDestruct "Hstack" as (nm0 nm1 nm2 nm3 nm4 nm5 nm6 nm7 f0 f1) "Hstack".
    iDestruct "Hstack" as (f2 f3 f4 f5 f6 istack l0 l1 l2 l3) "Hstack".
    iDestruct "Hstack" as (l4 l5 l6 stacktab isStack newStackAddrIs) "Hstack".
    iDestruct "Hstack" as "(HimpsH & HimpsW & %Hnodup & %Hfnodup & %Htablen & #Hinv & #Hnewstack & #Hinterp)".
    
    (* Cleanup of stack resources *)
    Opaque list_to_map.
    Opaque zip_with.
    iDestruct "HimpsW" as "(_ & Hidf0 & Hidf1 & Hidf2 & Hidf3 & Hidf4 & Hidf5 & Hidf6 & Hidtab & _) /=".

    iDestruct "Hidf0" as (cl0) "[Himpfcl0 %Hcltype0]".
    iDestruct "Hidf1" as (cl1) "[Himpfcl1 %Hcltype1]".
    iDestruct "Hidf2" as (cl2) "[Himpfcl2 %Hcltype2]".
    iDestruct "Hidf3" as (cl3) "[Himpfcl3 %Hcltype3]".
    iDestruct "Hidf4" as (cl4) "[Himpfcl4 %Hcltype4]".
    iDestruct "Hidf5" as (cl5) "[Himpfcl5 %Hcltype5]".
    iDestruct "Hidf6" as (cl6) "[Himpfcl6 %Hcltype6]".

    apply (NoDup_fmap_2 N.of_nat) in Hfnodup; simpl in Hfnodup.
    
    remember (list_to_map _) as mtmp.
    rewrite -> Heqmtmp in *.
    rewrite -> list_to_map_zip_lookup in Hcltype0, Hcltype1, Hcltype2, Hcltype3, Hcltype4, Hcltype5, Hcltype6 => //.
    destruct Hcltype0 as ((k0 & Hind0 & Hcl0) & _).
    destruct Hcltype1 as ((k1 & Hind1 & Hcl1) & _).
    destruct Hcltype2 as ((k2 & Hind2 & Hcl2) & _).
    destruct Hcltype3 as ((k3 & Hind3 & Hcl3) & _).
    destruct Hcltype4 as ((k4 & Hind4 & Hcl4) & _).
    destruct Hcltype5 as ((k5 & Hind5 & Hcl5) & _).
    destruct Hcltype6 as ((k6 & Hind6 & Hcl6) & _).
    assert (k0=0) as ->; first by eapply NoDup_lookup => //.
    assert (k1=1) as ->; first by eapply NoDup_lookup => //.
    assert (k2=2) as ->; first by eapply NoDup_lookup => //.
    assert (k3=3) as ->; first by eapply NoDup_lookup => //.
    assert (k4=4) as ->; first by eapply NoDup_lookup => //.
    assert (k5=5) as ->; first by eapply NoDup_lookup => //.
    assert (k6=6) as ->; first by eapply NoDup_lookup => //.
    inversion Hcl0.
    inversion Hcl1.
    inversion Hcl2.
    inversion Hcl3.
    inversion Hcl4.
    inversion Hcl5.
    inversion Hcl6.
    subst cl0 cl1 cl2 cl3 cl4 cl5 cl6.
    clear Hcl0 Hcl1 Hcl2 Hcl3 Hcl4 Hcl5 Hcl6 Hind0 Hind1 Hind2 Hind3 Hind4 Hind5 Hind6.

    rewrite lookup_insert.
    iDestruct "Hidtab" as (tab tt) "[Hidtab [%Heq %Htt]]". inversion Heq;subst tab; clear Heq.
    iDestruct "HimpsH" as "(Hvis0 & Hvis1 & Hvis2 & Hvis3 & Hvis4 & Hvis5 & Hvis6 & Hvis7 & _)".

    (* instantiate adversary module *)
    iApply (weakestpre.wp_wand _ _ _ (λ v, _)%I with "[-HΦ] [HΦ]");cycle 1.
    { iIntros (v) "Hv". iApply "HΦ". iExact "Hv". }
    { iApply (instantiation_spec_operational_start_seq with "[$Hemptyframe] [$Hmod_adv Hvis0 Hvis1 Hvis2 Hvis3 Hvis4 Himpfcl0 Himpfcl1 Himpfcl2 Himpfcl3 Himpfcl4]");[eauto|apply Htyp|auto|..].
      - instantiate (5:=[_;_;_;_;_]).
        unfold import_resources_host. iSimpl. iFrame "Hvis0 Hvis1 Hvis2 Hvis3 Hvis4".
        instantiate (1:=∅).
        instantiate (1:=∅).
        instantiate (1:=∅).
        instantiate (1:= (list_to_map (zip (fmap N.of_nat [idf0; idf1; idf2; idf3; idf4]) [_;_;_;_;_]))).

        rewrite separate5 in Hfnodup.
        apply NoDup_app in Hfnodup as [Hfnodup _].
        
        iSplit;[iSplit;[|auto]|iSplit].
        + simpl.
          iSplitL. unfold import_func_wasm_check,import_func_resources.
          rewrite /func_typecheck /func_domcheck /= !dom_insert_L !Forall2_cons Forall2_nil /=.
          iClear "Hinterp".
          iSplit => //.
          { 
            iApply big_opM_map_to_list.
            rewrite map_to_list_to_map; last done.
            Transparent zip_with.
            iFrame.
            done.
          }
          iSplit => //.
          { iPureIntro.
            repeat (split; first eexists) => //.
            all: rewrite -> list_to_map_zip_lookup => //.
            { split; first exists 0 => //; done. }
            { split; first exists 1 => //; done. }
            { split; first exists 2 => //; done. }
            { split; first exists 3 => //; done. }
            { split; first exists 4 => //; done. }
          }
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
        Transparent list_to_map.
        Transparent zip_with.
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
        + iApply weakestpre.wp_value; first by unfold IntoVal; apply language.of_to_val; eauto.
          iFrame. auto.
        + iDestruct "Hv" as (ws) "[-> Hv]".
          iDestruct (big_sepL2_length with "Hv") as %Hnil. destruct ws;[|done].
          iApply weakestpre.wp_value; first by unfold IntoVal; apply language.of_to_val;eauto.
          iFrame. auto. }
  Qed.

End RobustStack.
