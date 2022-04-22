From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_rules iris_fundamental iris_wp.
Require Export datatypes host operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Import DummyHosts.

Section InterpInstance.

  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ, !wtablimitG Σ, !wmemlimitG Σ,
        !logrel_na_invs Σ, HWP:host_program_logic}.

  Definition interp_closure_pre τctx (fimps : gmap N function_closure) (i : instance) (n : N) (τf : function_type) :=
    λne (cl : leibnizO function_closure),
         match cl with
         | FC_func_native j τ' t_locs b_es =>
             match fimps !! n with
             | Some cl' => (⌜cl' = cl⌝ ∗ interp_closure (HWP:=HWP) τf cl)%I
             | None => (⌜i = j ∧ τf = τ' ∧
                         let 'Tf tn tm := τf in
                         be_typing (upd_local_label_return τctx (tn ++ t_locs) [tm] (Some tm)) b_es (Tf [] tm)⌝)%I
             end
         | _ => interp_closure (HWP:=HWP) τf cl
         end.
  Global Instance interp_closure_pre_persistent τctx fimps n i τf cl : Persistent (interp_closure_pre τctx fimps i n τf cl).
  Proof. destruct cl,f;try apply _. Qed.
  Global Instance interp_closure_persistent τf cl : Persistent (interp_closure (HWP:=HWP) τf cl).
  Proof. destruct cl,f;try apply _. Qed.
  
  Definition interp_instance_pre (τctx : t_context) (fimps : gmap N function_closure) :=
    λne (i : leibnizO instance), interp_instance' τctx (interp_closure_pre τctx fimps i) (interp_closure_pre τctx fimps i) i.
  Global Instance interp_instance_pre_persistent τctx fimps i : Persistent (interp_instance_pre τctx fimps i).
  Proof. apply interp_instance_persistent';intros; destruct cl,f; apply _.  Qed.

  Lemma n_zeros_length l :
    length (n_zeros l) = length l.
  Proof.
    induction l;auto. simpl. rewrite IHl. 
    auto.
  Qed.

  Lemma n_zeros_interp_values l :
    ⊢ ([∗ list] y1;y2 ∈ n_zeros l;l, interp_value (Σ:=Σ) y2 y1)%I.
  Proof.
    iApply big_sepL2_forall.
    iSplit;[iPureIntro;apply n_zeros_length|].
    iIntros (k z v Hz Hv).
    unfold n_zeros in Hz.
    apply lookup_lt_Some in Hv as Hlt.
    apply take_drop_middle in Hv.
    rewrite -Hv in Hz.
    rewrite seq.map_cat seq.map_cons /= in Hz.
    rewrite list_lookup_middle in Hz;simplify_eq.
    { unfold interp_value. destruct v; iExists _;eauto. }
    rewrite length_is_size size_map -length_is_size.
    rewrite take_length. lia.
  Qed.

  Lemma interp_closure_pre_ind C i ft cl fimps n :
    tc_label C = [] ∧ tc_return C = None ->
    (□ ▷ interp_instance (HWP:=HWP) C i) -∗
    interp_closure_pre C fimps i n ft cl -∗
    interp_closure (HWP:=HWP) ft cl.
  Proof.
    iIntros (Hnil) "#IH #Hcl".
    destruct cl.
    { iSimpl in "Hcl".
      destruct (fimps !! n) eqn:Hlook.
      { destruct f. iDestruct "Hcl" as "[-> [-> Hcl]]".
        iSplit;eauto. }
      { iDestruct "Hcl" as "[-> [-> Htyp]]".
        iSimpl. destruct f. iSplit;[auto|].
        iDestruct "Htyp" as "%Htyp".
        iModIntro.
        iNext.
        iIntros (vcs) "Hv Hown". iIntros (f1) "Hf".
        iDestruct "Hv" as "[%Hcontr|Hv]";[done|iDestruct "Hv" as (v' Heqv) "#Hv"].
        iDestruct (be_fundamental_local with "IH") as "HH";eauto. inversion Heqv.
        
        iDestruct ("HH" $! _ (v' ++ n_zeros l) with "[$] [$] []") as "Hcont".
        { iRight. iExists _. iSplit;[eauto|]. iApply big_sepL2_app;iFrame "#".
          iApply n_zeros_interp_values. }
        iSimpl in "Hcont".
        iIntros (LI Hfill%lfilled_Ind_Equivalent).
        inversion Hfill;inversion H9;simplify_eq.
        repeat erewrite app_nil_l, app_nil_r.
        iFrame. }
    }
    { simpl. auto. }
  Qed.
    
  
  Lemma interp_instance_pre_create τctx i fimps :
    (tc_label τctx) = [] ∧ (tc_return τctx) = None ->
    interp_instance_pre τctx fimps i -∗
    interp_instance (HWP:=HWP) τctx i.
  Proof.
    iIntros (Hnil) "#Hpre".
    iLöb as "IH".
    set (IH := (▷ interp_instance τctx i)%I).
    destruct τctx, i.
    iDestruct "Hpre" as "[Htypes [Hfunc [Htable [Hmem Hglob]]]]".
    iFrame "#". iSplit.
    { iDestruct (big_sepL2_length with "Hfunc") as %Hlen.
      iApply (big_sepL2_forall).
      iSplit;[auto|iIntros (k f ft Hf Hft)].
      iDestruct (big_sepL2_lookup with "Hfunc") as (cl) "[Hfna Hcl]";[eauto..|].
      iExists _. iFrame "Hfna".
      iApply interp_closure_pre_ind;eauto. }
    { destruct (nth_error tc_table 0);auto.
      destruct (nth_error inst_tab 0);[|done].
      iDestruct "Htable" as (table_size table_lim Hlim) "(Hlim & Hsize & Ht)".
      iExists _,_. iFrame "# %".
      iApply (big_sepL_forall).
      iIntros (k f Hf).
      iDestruct (big_sepL_lookup with "Ht") as (τf fe) "[Hfna Hfe]";[eauto|].
      iExists τf,fe. iFrame "#".
      destruct fe;auto.
      iDestruct "Hfe" as (cl) "[Hna Hcl]".
      iExists _;iFrame "#".
      iApply interp_closure_pre_ind;eauto.
    }
  Qed.
      
  Definition import_resources_wasm_typecheck_invs (v_imps: list module_export)
             (t_imps: list extern_t) (wfs: gmap N function_closure)
             (wts: gmap N tableinst) (wms: gmap N memory) (wgs: gmap N global): iProp Σ :=
    import_resources_wasm_domcheck v_imps wfs wts wms wgs ∗
  [∗ list] i ↦ v; t ∈ v_imps; t_imps,
  match v.(modexp_desc) with
  | MED_func (Mk_funcidx i) => ((∃ cl, na_inv logrel_nais (wfN (N.of_nat i)) (N.of_nat i ↦[wf] cl) ∗ ⌜ wfs !! (N.of_nat i) = Some cl /\ t = ET_func (cl_type cl) ⌝)%I)
                                
  | MED_table (Mk_tableidx i) => (∃ tab tt, N.of_nat i ↪[wtsize]tab_size tab ∗
                                           N.of_nat i ↪[wtlimit]table_max_opt tab ∗
                                           ([∗ list] j↦tabelem ∈ table_data tab, na_inv logrel_nais (wtN (N.of_nat i) (N.of_nat j)) (N.of_nat i ↦[wt][N.of_nat j]tabelem))
                                           ∗ ⌜ wts !! (N.of_nat i) = Some tab /\ t = ET_tab tt /\ tab_typing tab tt ⌝)
                                  
  | MED_mem (Mk_memidx i) => (∃ mem mt, (na_inv logrel_nais (wmN (N.of_nat i)) (∃ (mem : memory),
                                ([∗ list] j ↦ b ∈ (mem.(mem_data).(ml_data)), N.of_nat i ↦[wm][N.of_nat j] b) ∗
                                N.of_nat i ↦[wmlength] mem_length mem)) ∗
                            N.of_nat i ↪[wmlimit] mem_max_opt mem ∗ ⌜ wms !! (N.of_nat i) = Some mem /\ t = ET_mem mt /\ mem_typing mem mt ⌝)
                              
  | MED_global (Mk_globalidx i) => (∃ g gt, na_inv logrel_nais (wgN (N.of_nat i)) (∃ w, N.of_nat i ↦[wg] Build_global (tg_mut gt) w ∗ interp_value (tg_t gt) w)
                                                  ∗ ⌜ wgs !! (N.of_nat i) = Some g /\ t = ET_glob gt /\ global_agree g gt ⌝)
  end.

  Global Instance imports_invs_persistent v_imps t_imps wfs wts wms wgs : Persistent (import_resources_wasm_typecheck_invs v_imps t_imps wfs wts wms wgs).
  Proof.
    apply bi.sep_persistent;[apply _|].
    apply big_sepL2_persistent=>n exp expt.
    destruct (modexp_desc exp);[destruct f;apply _|
                                 destruct t;apply _|
                                 destruct m;apply _|
                                 destruct g;apply _].
  Qed.


  Lemma import_resources_wasm_typecheck_alloc E v_imps t_imps wfs wts wms wgs :
    import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs ={E}=∗
    import_resources_wasm_typecheck_invs v_imps t_imps wfs wts wms wgs.
  Proof.
    iIntros "[Hdom Himps]".
    iFrame "Hdom".
    iApply big_sepL2_fupd.
    iApply (big_sepL2_mono with "Himps");intros k exp expt Hlook1 Hlook2;simpl.
    destruct (modexp_desc exp);[destruct f|destruct t|destruct m|destruct g];iIntros "Hres".
    { iDestruct "Hres" as (cl) "[Hres ?]". iExists _. iFrame.
      iApply na_inv_alloc. iNext. iFrame. }
    { iDestruct "Hres" as (tab tt) "[[Hres [? ?]] ?]". iExists _,_. iFrame.
      iApply big_sepL_fupd.
      iApply (big_sepL_mono with "Hres");intros k' el Hlook;simpl.
      iIntros "Hn".
      iApply na_inv_alloc. iNext;iFrame. }
    { iDestruct "Hres" as (mem mt) "[[Hres [? ?]] ?]". iExists _,_. iFrame.
      iApply na_inv_alloc. iNext. iExists _. iFrame. }
    { iDestruct "Hres" as (g gt) "[Hres %]". iExists _,_. iFrame "%".
      destruct H as (?&?&?).
      iApply na_inv_alloc. iNext. iFrame.
      destruct gt;simplify_eq. rewrite /global_agree /= in H1.
      revert H1. move/andP =>[Hmut Htyp].
      revert Htyp. move/eqP=>Htyp.
      revert Hmut. move/eqP=>Hmut.
      rewrite Htyp. destruct g;simplify_eq. simpl. iExists g_val. iFrame.
      iApply interp_value_type_of. }
  Qed.

  Lemma import_resources_wasm_typecheck_lengths v_imps t_imps wfs wts wms wgs :
    import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
    ⌜length (ext_func_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) = length (ext_t_funcs t_imps)
    ∧ length (ext_tab_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) = length (ext_t_tabs t_imps)
    ∧ length (ext_mem_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) = length (ext_t_mems t_imps)
    ∧ length (ext_glob_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) = length (ext_t_globs t_imps)⌝.
  Proof.
    iIntros "[_ Hi]".
    iDestruct (big_sepL2_length with "Hi") as %Hlen.
    iInduction (v_imps) as [] "IH"
  forall (t_imps Hlen).
    { simpl. destruct t_imps;done. }
    { destruct t_imps;[done|].
      simpl in Hlen. inversion Hlen.
      iDestruct "Hi" as "[Hx Hi]".
      iDestruct ("IH" with "[] Hi") as %HlenIH;auto;iClear "Hi".
      rewrite map_cons.
      destruct (modexp_desc a).
      { destruct f. simpl. destruct HlenIH as (Heq1&Heq2&Heq3&Heq4).
        iDestruct "Hx" as (?) "[_ [_ %H]]".
        rewrite H //. simpl. rewrite Heq1 Heq2 Heq3 Heq4. auto. }
      { destruct t. simpl. destruct HlenIH as (Heq1&Heq2&Heq3&Heq4).
        iDestruct "Hx" as (? ?) "[_ [_ [%H _]]]".
        rewrite H //. simpl. rewrite Heq1 Heq2 Heq3 Heq4. auto. }
      { destruct m. simpl. destruct HlenIH as (Heq1&Heq2&Heq3&Heq4).
        iDestruct "Hx" as (? ?) "[_ [_ [%H _]]]".
        rewrite H //. simpl. rewrite Heq1 Heq2 Heq3 Heq4. auto. }
      { destruct g. simpl. destruct HlenIH as (Heq1&Heq2&Heq3&Heq4).
        iDestruct "Hx" as (? ?) "[_ [_ [%H _]]]".
        rewrite H //. simpl. rewrite Heq1 Heq2 Heq3 Heq4. auto. }
    }
  Qed.

  Definition module_inst_resources_func_invs (mfuncs: list module_func) (inst: instance) (inst_f: list funcaddr) : iProp Σ :=
    ([∗ list] f; addr ∈ mfuncs; inst_f,
       (* Allocated wasm resources *)
       na_inv logrel_nais (wfN (N.of_nat addr))
       (N.of_nat addr ↦[wf] (FC_func_native
                              inst
                              (nth match f.(modfunc_type) with
                                   | Mk_typeidx k => k
                                   end (inst.(inst_types)) (Tf [] []))
                              f.(modfunc_locals)
                                  f.(modfunc_body)))
    )%I.

  Lemma module_inst_resources_func_invs_alloc E mfuncs inst inst_f :
    module_inst_resources_func mfuncs inst inst_f ={E}=∗
    module_inst_resources_func_invs mfuncs inst inst_f .
  Proof.
    iIntros "Himps".
    iApply big_sepL2_fupd.
    iApply (big_sepL2_mono with "Himps");intros k exp expt Hlook1 Hlook2;simpl.
    iIntros "Hf".
    iApply na_inv_alloc. iNext. iFrame.
  Qed.

  (*Lemma module_inst_resources_func_NoDup mfuncs inst inst_f :
    module_inst_resources_func mfuncs inst inst_f -∗
    ⌜NoDup inst_f⌝.
  Proof.
    iIntros "H". iDestruct (big_sepL2_length with "H") as %Hlen.
    iInduction inst_f as [] "IH" forall (mfuncs Hlen).
    { iPureIntro. destruct mfuncs;[|done]. by apply NoDup_nil. }
    { destruct mfuncs;[done|].
      rewrite NoDup_cons.      
      iDestruct "H" as "[H H']".
      simpl in Hlen. inversion Hlen.
      iSplit.
      { iIntros (Hcontr).
        apply elem_of_list_lookup in Hcontr as [k Hk].
        apply lookup_lt_Some in Hk as Hlt. rewrite -H0 in Hlt.
        apply lookup_lt_is_Some_2 in Hlt as [cl Hk'].
        iDestruct (big_sepL2_lookup with "H'") as "H'";eauto.
        iDestruct (mapsto_valid_2 with "H H'") as "[% ?]". done. }
      { iDestruct ("IH" with "[] H'") as "H'";auto. }
    } 
  Qed.*)

  Lemma ext_func_addrs_elem_of fa v_imps :
    fa ∈ ext_func_addrs (modexp_desc <$> v_imps) ->
    ∃ name, Build_module_export name (MED_func (Mk_funcidx fa)) ∈ v_imps.
  Proof.
    induction v_imps.
    { cbn. intros Hcontr;inversion Hcontr. }
    { cbn. intros H. destruct (modexp_desc a) eqn:Ha.
      { simpl in *. destruct f.
        apply elem_of_cons in H as [-> | Ha'].
        { destruct a. eexists. simpl in Ha. rewrite Ha. constructor. }
        { apply IHv_imps in Ha' as [name Ha']. exists name. constructor. auto. }
      }
      all: simpl in *.
      all: apply IHv_imps in H as [name Ha']; exists name; constructor; auto. 
    }
  Qed.
  Lemma ext_tab_addrs_elem_of fa v_imps :
    fa ∈ ext_tab_addrs (modexp_desc <$> v_imps) ->
    ∃ name, Build_module_export name (MED_table (Mk_tableidx fa)) ∈ v_imps.
  Proof.
    induction v_imps.
    { cbn. intros Hcontr;inversion Hcontr. }
    { cbn. intros H. destruct (modexp_desc a) eqn:Ha.
      2: { simpl in *. destruct t.
        apply elem_of_cons in H as [-> | Ha'].
        { destruct a. eexists. simpl in Ha. rewrite Ha. constructor. }
        { apply IHv_imps in Ha' as [name Ha']. exists name. constructor. auto. }
      }
      all: simpl in *.
      all: apply IHv_imps in H as [name Ha']; exists name; constructor; auto. 
    }
  Qed.
  Lemma ext_mem_addrs_elem_of fa v_imps :
    fa ∈ ext_mem_addrs (modexp_desc <$> v_imps) ->
    ∃ name, Build_module_export name (MED_mem (Mk_memidx fa)) ∈ v_imps.
  Proof.
    induction v_imps.
    { cbn. intros Hcontr;inversion Hcontr. }
    { cbn. intros H. destruct (modexp_desc a) eqn:Ha.
      3: { simpl in *. destruct m.
        apply elem_of_cons in H as [-> | Ha'].
        { destruct a. eexists. simpl in Ha. rewrite Ha. constructor. }
        { apply IHv_imps in Ha' as [name Ha']. exists name. constructor. auto. }
      }
      all: simpl in *.
      all: apply IHv_imps in H as [name Ha']; exists name; constructor; auto. 
    }
  Qed.
  Lemma ext_glob_addrs_elem_of fa v_imps :
    fa ∈ ext_glob_addrs (modexp_desc <$> v_imps) ->
    ∃ name, Build_module_export name (MED_global (Mk_globalidx fa)) ∈ v_imps.
  Proof.
    induction v_imps.
    { cbn. intros Hcontr;inversion Hcontr. }
    { cbn. intros H. destruct (modexp_desc a) eqn:Ha.
      4: { simpl in *. destruct g.
        apply elem_of_cons in H as [-> | Ha'].
        { destruct a. eexists. simpl in Ha. rewrite Ha. constructor. }
        { apply IHv_imps in Ha' as [name Ha']. exists name. constructor. auto. }
      }
      all: simpl in *.
      all: apply IHv_imps in H as [name Ha']; exists name; constructor; auto. 
    }
  Qed.    

  Lemma module_res_imports_disj v_imps t_imps wfs wts wms wgs m inst :
    import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗ 
     module_inst_resources_func (mod_funcs m) inst (drop (get_import_func_count m) (inst_funcs inst)) -∗
     ⌜∀ i fa, (drop (get_import_func_count m) (inst_funcs inst)) !! i = Some fa -> wfs !! (N.of_nat fa) = None⌝.
  Proof.
    iIntros "[[%Hdom _] Hi] Hf".
    iIntros (i fa Hsome).
    iDestruct (big_sepL2_length with "Hf") as %Hlen.
    apply lookup_lt_Some in Hsome as Hlt. rewrite -Hlen in Hlt.
    apply lookup_lt_is_Some_2 in Hlt as [cl Hk'].
    iDestruct (big_sepL2_lookup with "Hf") as "H";eauto.
    destruct (wfs !! (N.of_nat fa)) eqn:Hnone;auto.
    apply elem_of_dom_2 in Hnone.
    apply leibniz_equiv in Hdom.
    rewrite Hdom in Hnone.
    apply elem_of_list_to_set in Hnone.
    eapply elem_of_list_fmap_2 in Hnone as [fa' [Heqfa' Hnone]]. simplify_eq.
    apply ext_func_addrs_elem_of in Hnone as [nm Hnone].
    apply elem_of_list_lookup in Hnone as [k Hk].
    iDestruct (big_sepL2_length with "Hi") as %Hlen'.
    apply lookup_lt_Some in Hk as Hlt'.
    rewrite Hlen' in Hlt'.
    apply lookup_lt_is_Some_2 in Hlt' as [? ?].
    iDestruct (big_sepL2_lookup with "Hi") as "HH";eauto.
    simpl. iDestruct "HH" as (cl') "[H' _]".
    iDestruct (mapsto_valid_2 with "H H'") as "[% ?]". done.
  Qed.    
    

  Definition module_inst_resources_tab_invs (mtabs: list module_table) (t_inits : gmap (nat * nat) funcelem) (inst_t: list tableaddr) : iProp Σ :=
    ([∗ list] i↦tab; addr ∈ mtabs; inst_t,
       let tab := (match tab.(modtab_type).(tt_limits) with
                                 | {| lim_min := min; lim_max := omax |} =>
                                     (Build_tableinst
                                        (imap
                                           (λ (j : nat) (_ : funcelem),
                                             match t_inits !! (i, j) with
                                             | Some felem => felem
                                             | None => None : funcelem
                                             end) (repeat (None : funcelem) (ssrnat.nat_of_bin min))))
                                       (omax)
                   end) in
       N.of_nat addr ↪[wtsize]tab_size tab ∗ N.of_nat addr ↪[wtlimit]table_max_opt tab ∗
       ([∗ list] j↦tabelem ∈ table_data tab, na_inv logrel_nais (wtN (N.of_nat addr) (N.of_nat j)) (N.of_nat addr ↦[wt][N.of_nat j]tabelem))       
    )%I.

  Lemma module_inst_resources_tab_invs_alloc E mtabs t_inits inst_t :
    module_inst_resources_tab mtabs t_inits inst_t ={E}=∗
    module_inst_resources_tab_invs mtabs t_inits inst_t.
  Proof.
    iIntros "Himps".
    iApply big_sepL2_fupd.
    iApply (big_sepL2_mono with "Himps");intros k exp expt Hlook1 Hlook2;simpl.
    iIntros "[Hlim [Hsize Hf]]". iFrame.
    iApply big_sepL_fupd.
    iApply (big_sepL_mono with "Hlim");intros k' x Hx;simpl. iIntros "H".
    iApply na_inv_alloc. iNext. iFrame.
  Qed.

  Definition module_inst_resources_mem_invs (mmems: list memory_type) (inst_m: list memaddr) : iProp Σ := 
    ([∗ list] mem; addr ∈ mmems; inst_m, N.of_nat addr ↪[wmlimit] lim_max mem ∗
       na_inv logrel_nais (wmN (N.of_nat addr))
              (∃ (mem : memory),
                  ([∗ list] i ↦ b ∈ (mem.(mem_data).(ml_data)), (N.of_nat addr) ↦[wm][ (N.of_nat i) ] b) ∗
                                                                (N.of_nat addr) ↦[wmlength] mem_length mem)
       (* (N.of_nat addr ↦[wmblock] (match mem with *)
       (*                           | {| lim_min:= min; lim_max := omax |} => *)
       (*                               Build_memory *)
       (*                                 {| ml_init := #00%byte; ml_data := repeat #00%byte (N.to_nat min) |} *)
       (*                                 (omax) *)
       (*                           end)) *)
    ).

  Lemma module_inst_resources_mem_invs_alloc E mmems m_inits inst_m :
    module_inst_resources_mem mmems m_inits inst_m  ={E}=∗
    module_inst_resources_mem_invs mmems inst_m.
  Proof.
    iIntros "Himps".
    iApply big_sepL2_fupd.
    iApply (big_sepL2_mono with "Himps");intros k exp expt Hlook1 Hlook2;simpl.
    iIntros "[Hf [Hlen Hlim]]". destruct exp. simpl. iFrame "Hlim".
    iApply na_inv_alloc. iNext. iExists _. iFrame.
  Qed.
  
  Definition module_inst_resources_glob_invs (mglobs: list module_glob) (g_inits: list value) (inst_g: list globaladdr) (gts : seq.seq global_type) : iProp Σ :=
    ([∗ list] i↦g; addr ∈ mglobs; inst_g,
       ∃ w τg, ⌜g_inits !! i = Some w⌝ ∗ ⌜gts !! i = Some τg⌝ ∗
       na_inv logrel_nais (wgN (N.of_nat addr)) (∃ w, N.of_nat addr ↦[wg] Build_global (tg_mut τg) w
                                                               ∗ interp_value (tg_t τg) w)
    ).

  Global Instance module_inst_resources_glob_invs_persistent mglobs g_inits inst_g gts : Persistent (module_inst_resources_glob_invs mglobs g_inits inst_g gts).
  Proof. apply big_sepL2_persistent;intros;apply _. Qed.

  (* The following lemma depends on the restriction that the module only contains constants *)
  Lemma module_inst_resources_glob_invs_alloc E mglobs g_inits inst_g impts gts :
    let c' :=
       {|
         tc_types_t := [];
         tc_func_t := [];
         tc_global := ext_t_globs impts;
         tc_table := [];
         tc_memory := [];
         tc_local := [];
         tc_label := [];
         tc_return := None
       |} in
    Forall2 (module_glob_typing c') mglobs gts ->
    (fmap typeof g_inits = fmap (tg_t ∘ modglob_type) mglobs) ->

    module_inst_resources_glob mglobs g_inits inst_g ={E}=∗
    module_inst_resources_glob_invs mglobs g_inits inst_g gts.
  Proof.
    iIntros (c' Hginitsval Hinittyp) "Himps".
    iApply big_sepL2_fupd.
    iApply (big_sepL2_mono with "Himps");intros k exp expt Hlook1 Hlook2;simpl.
    iIntros "Hf".
    destruct (nth_error g_inits k) eqn:Hnth;[|done].
    rewrite nth_error_lookup in Hnth.
    eapply Forall2_lookup_l in Hginitsval as [gt [Hgt Htyp]];eauto.
    iExists _,_. iSplitR;[eauto|]. iSplitR;[eauto|].
    unfold module_glob_typing in Htyp. destruct exp;simpl in *.
    destruct Htyp as [Hconst [Heq Htyp]]. subst.
    iApply na_inv_alloc.
    iNext. iExists _. iFrame.
    assert ((typeof <$> g_inits) !! k = Some (typeof v)).
    { rewrite list_lookup_fmap. rewrite Hnth. eauto. }
    rewrite Hinittyp in H.
    rewrite (list_fmap_compose (datatypes.modglob_type) tg_t mglobs) in H.
    apply list_lookup_fmap_inv in H as [gt [Heq1 H]].
    rewrite list_lookup_fmap Hlook1 /= in H.
    simplify_eq. rewrite -Heq1.
    iApply interp_value_type_of.
  Qed.

  Lemma get_import_count_length m t_imps c :
    Forall2 (λ imp e, module_import_typing c (imp_desc imp) e) (mod_imports m) t_imps ->
    get_import_func_count m = length (ext_t_funcs t_imps)
    ∧ get_import_table_count m = length (ext_t_tabs t_imps)
    ∧ get_import_mem_count m = length (ext_t_mems t_imps)
    ∧ get_import_global_count m = length (ext_t_globs t_imps).
  Proof.
    revert m; induction t_imps;intros m Himps.
    { destruct m.
      simpl in *.
      apply Forall2_length in Himps as Hlen. 
      destruct mod_imports;[|done].
      by cbn. }
    { unfold ext_t_funcs.
      rewrite length_is_size size_pmap -size_filter. simpl.
      destruct m.
      simpl in *.
      apply Forall2_length in Himps as Hlen.
      destruct mod_imports;[done|].
      apply Forall2_cons in Himps as [Hcons Himps].
      cbn in Hcons. cbn.
      set (m' :=
             {| mod_types := mod_types;
               mod_funcs := mod_funcs;
               mod_tables := mod_tables;
               mod_mems := mod_mems;
               mod_globals := mod_globals;
               mod_elem := mod_elem;
               mod_data := mod_data;
               mod_start := mod_start;
               mod_imports := mod_imports;
               mod_exports := mod_exports |}
          ).
      destruct (imp_desc m),a; try done.
      all: simpl; rewrite size_filter.
      all: unfold ext_t_funcs,ext_t_tabs,ext_t_mems,ext_t_globs in IHt_imps.
      all: rewrite length_is_size size_pmap /= in IHt_imps.
      all: destruct IHt_imps with m' as [? [? [? ?]]];auto. }
  Qed.

  Lemma inst_funcs_length_imp_app ifts t_imps v_imps inst_funcs m fts c :
    ifts = ext_t_funcs t_imps  ->
    ext_func_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps) `prefix_of` inst_funcs ->
    length (ext_func_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) = length (ext_t_funcs t_imps) ->
    length (mod_funcs m) = length (drop (get_import_func_count m) inst_funcs) ->
    length v_imps = length t_imps ->
    length (mod_funcs m) = length fts ->
    Forall2 (λ imp e, module_import_typing c (imp_desc imp) e) (mod_imports m) t_imps ->

    length inst_funcs = length (ifts ++ fts).
  Proof.
    intros Heq Hprefunc Hlenir Hlenfr Himp_len Hlenfr' Himps.
    destruct m. simpl in *.
    rewrite Hlenfr' in Hlenfr.
    destruct Hprefunc as [inst_funcs_new Heqf].
    rewrite Heqf. rewrite !app_length.
    rewrite Hlenfr Hlenir.
    edestruct get_import_count_length as [-> _];eauto.
    rewrite drop_length.
    rewrite Heqf. rewrite app_length. rewrite Hlenir.
    rewrite nat_minus_plus Heq. auto.
  Qed.

  Lemma inst_tabs_length_imp_app ifts t_imps v_imps inst_funcs m fts c :
    ifts = ext_t_tabs t_imps  ->
    ext_tab_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps) `prefix_of` inst_funcs ->
    length (ext_tab_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) = length (ext_t_tabs t_imps) ->
    length (mod_tables m) = length (drop (get_import_table_count m) inst_funcs) ->
    length v_imps = length t_imps ->
    length (mod_tables m) = length fts ->
    Forall2 (λ imp e, module_import_typing c (imp_desc imp) e) (mod_imports m) t_imps ->

    length inst_funcs = length (ifts ++ fts).
  Proof.
    intros Heq Hprefunc Hlenir Hlenfr Himp_len Hlenfr' Himps.
    destruct m. simpl in *.
    rewrite Hlenfr' in Hlenfr.
    destruct Hprefunc as [inst_funcs_new Heqf].
    rewrite Heqf. rewrite !app_length.
    rewrite Hlenfr Hlenir.
    edestruct get_import_count_length as [_ [-> _]];eauto.
    rewrite drop_length.
    rewrite Heqf. rewrite app_length. rewrite Hlenir.
    rewrite nat_minus_plus Heq. auto.
  Qed.

  Lemma inst_mem_length_imp_app ifts t_imps v_imps inst_funcs m fts c :
    ifts = ext_t_mems t_imps  ->
    ext_mem_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps) `prefix_of` inst_funcs ->
    length (ext_mem_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) = length (ext_t_mems t_imps) ->
    length (mod_mems m) = length (drop (get_import_mem_count m) inst_funcs) ->
    length v_imps = length t_imps ->
    length (mod_mems m) = length fts ->
    Forall2 (λ imp e, module_import_typing c (imp_desc imp) e) (mod_imports m) t_imps ->

    length inst_funcs = length (ifts ++ fts).
  Proof.
    intros Heq Hprefunc Hlenir Hlenfr Himp_len Hlenfr' Himps.
    destruct m. simpl in *.
    rewrite Hlenfr' in Hlenfr.
    destruct Hprefunc as [inst_funcs_new Heqf].
    rewrite Heqf. rewrite !app_length.
    rewrite Hlenfr Hlenir.
    edestruct get_import_count_length as [_ [_ [-> _]]];eauto.
    rewrite drop_length.
    rewrite Heqf. rewrite app_length. rewrite Hlenir.
    rewrite nat_minus_plus Heq. auto.
  Qed.

  Lemma inst_glob_length_imp_app ifts t_imps v_imps inst_funcs m fts c :
    ifts = ext_t_globs t_imps  ->
    ext_glob_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps) `prefix_of` inst_funcs ->
    length (ext_glob_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) = length (ext_t_globs t_imps) ->
    length (mod_globals m) = length (drop (get_import_global_count m) inst_funcs) ->
    length v_imps = length t_imps ->
    length (mod_globals m) = length fts ->
    Forall2 (λ imp e, module_import_typing c (imp_desc imp) e) (mod_imports m) t_imps ->

    length inst_funcs = length (ifts ++ fts).
  Proof.
    intros Heq Hprefunc Hlenir Hlenfr Himp_len Hlenfr' Himps.
    destruct m. simpl in *.
    rewrite Hlenfr' in Hlenfr.
    destruct Hprefunc as [inst_funcs_new Heqf].
    rewrite Heqf. rewrite !app_length.
    rewrite Hlenfr Hlenir.
    edestruct get_import_count_length as [_ [_ [_ ->]]];eauto.
    rewrite drop_length.
    rewrite Heqf. rewrite app_length. rewrite Hlenir.
    rewrite nat_minus_plus Heq. auto.
  Qed.

  Lemma import_funcs_lookup t_imps v_imps k ft fa wfs wts wms wgs:
    ext_t_funcs t_imps !! k = Some ft ->
    ext_func_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps) !! k = Some fa ->
    import_resources_wasm_typecheck_invs v_imps t_imps wfs wts wms wgs -∗
    ⌜∃ k', t_imps !! k' = Some (ET_func ft) ∧ ∃ fm, v_imps !! k' = Some fm ∧ modexp_desc fm = MED_func (Mk_funcidx fa)⌝.
  Proof.
    iIntros (Hft Hfa) "[_ Himps]".
    iDestruct (big_sepL2_length with "Himps") as %Hlen.
    iInduction (t_imps) as [] "IH" forall (v_imps k Hlen Hft Hfa).
    { inversion Hft. }
    { destruct v_imps;[done|].
      simpl in Hlen;inversion Hlen.
      destruct k.
      { iDestruct "Himps" as "[Hf Himps]".
        simpl in Hfa. 
        destruct (modexp_desc m) eqn:Hmod.
        { iClear "Himps".
          destruct f. simpl in Hfa. simplify_eq.
          iDestruct "Hf" as (cl) "[Hfa %Ha]".
          destruct Ha as [Hwfs Ha]. subst a.
          simpl in Hft. simplify_eq.
          iExists 0. iSimpl. iSplit;auto.
          iExists _. iSplit;eauto. }
        { destruct t. cbn in Hfa.
          iDestruct "Hf" as (tab tt) "[? [? [? %Ha]]]".
          destruct Ha as [Hwts [Heq Htyp]].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). simpl. eauto. }
        { destruct m0. cbn in Hfa.
          iDestruct "Hf" as (mem mt) "[? [? %Ha]]".
          destruct Ha as [Hwts [Heq Htyp]].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). simpl. eauto. }
        { destruct g. cbn in Hfa.
          iDestruct "Hf" as (g gt) "[? %Ha]".
          destruct Ha as [Hwts [Heq Htyp]].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). simpl. eauto. }
      }
      { iDestruct "Himps" as "[Hf Himps]".
        simpl in *.
        destruct (modexp_desc m) eqn:Hmod.
        all: simpl in *.
        { destruct f. iDestruct "Hf" as (cl) "[Hfa %Ha]".
          destruct Ha as [Hwfs Ha]. subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
        { destruct t. iDestruct "Hf" as (tab tt) "[? [? [? %Ha]]]".
          destruct Ha as [Hwts [Heq Htyp]]. subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
        { destruct m0. iDestruct "Hf" as (mem mt) "[? [? %Ha]]".
          destruct Ha as [Hwts [Heq Htyp]]. subst a;simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
        { destruct g. iDestruct "Hf" as (g gt) "[? %Ha]".
          destruct Ha as [Hwts [Heq Htyp]].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
      }
    }
  Qed.

  Lemma import_tabs_lookup t_imps v_imps k ft fa wfs wts wms wgs:
    ext_t_tabs t_imps !! k = Some ft ->
    ext_tab_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps) !! k = Some fa ->
    import_resources_wasm_typecheck_invs v_imps t_imps wfs wts wms wgs -∗
    ⌜∃ k', t_imps !! k' = Some (ET_tab ft) ∧ ∃ fm, v_imps !! k' = Some fm ∧ modexp_desc fm = MED_table (Mk_tableidx fa)⌝.
  Proof.
    iIntros (Hft Hfa) "[_ Himps]".
    iDestruct (big_sepL2_length with "Himps") as %Hlen.
    iInduction (t_imps) as [] "IH" forall (v_imps k Hlen Hft Hfa).
    { inversion Hft. }
    { destruct v_imps;[done|].
      simpl in Hlen;inversion Hlen.
      destruct k.
      { iDestruct "Himps" as "[Hf Himps]".
        simpl in Hfa. 
        destruct (modexp_desc m) eqn:Hmod.
        2: { iClear "Himps".
          destruct t. simpl in Hfa. simplify_eq.
          iDestruct "Hf" as (? ?) "[Hfa [? [? %Ha]]]".
          destruct Ha as [Hwfs [Ha HH]]. subst.
          simpl in Hft. simplify_eq.
          iExists 0. iSimpl. iSplit;auto.
          iExists _. iSplit;eauto. }
        { destruct f. cbn in Hfa.
          iDestruct "Hf" as (?) "[? %Ha]".
          destruct Ha as [Hwts Heq].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). simpl. eauto. }
        { destruct m0. cbn in Hfa.
          iDestruct "Hf" as (mem mt) "[? [? %Ha]]".
          destruct Ha as [Hwts [Heq Htyp]].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). simpl. eauto. }
        { destruct g. cbn in Hfa.
          iDestruct "Hf" as (g gt) "[? %Ha]".
          destruct Ha as [Hwts [Heq Htyp]].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). simpl. eauto. }
      }
      { iDestruct "Himps" as "[Hf Himps]".
        simpl in *.
        destruct (modexp_desc m) eqn:Hmod.
        all: simpl in *.
        2: { destruct t. iDestruct "Hf" as (? ?) "[? [? [Hfa %Ha]]]".
          destruct Ha as [Hwfs [Ha ?]]. subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
        { destruct f. iDestruct "Hf" as (?) "[? %Ha]".
          destruct Ha as [Hwts Heq]. subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
        { destruct m0. iDestruct "Hf" as (mem mt) "[? [? %Ha]]".
          destruct Ha as [Hwts [Heq Htyp]]. subst a;simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
        { destruct g. iDestruct "Hf" as (g gt) "[? %Ha]".
          destruct Ha as [Hwts [Heq Htyp]].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
      }
    }
  Qed.

  Lemma import_mems_lookup t_imps v_imps k ft fa wfs wts wms wgs:
    ext_t_mems t_imps !! k = Some ft ->
    ext_mem_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps) !! k = Some fa ->
    import_resources_wasm_typecheck_invs v_imps t_imps wfs wts wms wgs -∗
    ⌜∃ k', t_imps !! k' = Some (ET_mem ft) ∧ ∃ fm, v_imps !! k' = Some fm ∧ modexp_desc fm = MED_mem (Mk_memidx fa)⌝.
  Proof.
    iIntros (Hft Hfa) "[_ Himps]".
    iDestruct (big_sepL2_length with "Himps") as %Hlen.
    iInduction (t_imps) as [] "IH" forall (v_imps k Hlen Hft Hfa).
    { inversion Hft. }
    { destruct v_imps;[done|].
      simpl in Hlen;inversion Hlen.
      destruct k.
      { iDestruct "Himps" as "[Hf Himps]".
        simpl in Hfa. 
        destruct (modexp_desc m) eqn:Hmod.
        3: { iClear "Himps".
          destruct m0. simpl in Hfa. simplify_eq.
          iDestruct "Hf" as (? ?) "[Hfa [? %Ha]]".
          destruct Ha as [Hwfs [Ha HH]]. subst.
          simpl in Hft. simplify_eq.
          iExists 0. iSimpl. iSplit;auto.
          iExists _. iSplit;eauto. }
        { destruct f. cbn in Hfa.
          iDestruct "Hf" as (?) "[? %Ha]".
          destruct Ha as [Hwts Heq].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). simpl. eauto. }
        { destruct t. cbn in Hfa.
          iDestruct "Hf" as (? ?) "[? [? [? %Ha]]]".
          destruct Ha as [Hwts [Heq Htyp]].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). simpl. eauto. }
        { destruct g. cbn in Hfa.
          iDestruct "Hf" as (g gt) "[? %Ha]".
          destruct Ha as [Hwts [Heq Htyp]].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). simpl. eauto. }
      }
      { iDestruct "Himps" as "[Hf Himps]".
        simpl in *.
        destruct (modexp_desc m) eqn:Hmod.
        all: simpl in *.
        3: { destruct m0. iDestruct "Hf" as (? ?) "[?[Hfa %Ha]]".
          destruct Ha as [Hwfs [Ha ?]]. subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
        { destruct f. iDestruct "Hf" as (?) "[? %Ha]".
          destruct Ha as [Hwts Heq]. subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
        { destruct t. iDestruct "Hf" as (mem mt) "[? [? [? %Ha]]]".
          destruct Ha as [Hwts [Heq Htyp]]. subst a;simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
        { destruct g. iDestruct "Hf" as (g gt) "[? %Ha]".
          destruct Ha as [Hwts [Heq Htyp]].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
      }
    }
  Qed.

  Lemma import_globs_lookup t_imps v_imps k ft fa wfs wts wms wgs:
    ext_t_globs t_imps !! k = Some ft ->
    ext_glob_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps) !! k = Some fa ->
    import_resources_wasm_typecheck_invs v_imps t_imps wfs wts wms wgs -∗
    ⌜∃ k', t_imps !! k' = Some (ET_glob ft) ∧ ∃ fm, v_imps !! k' = Some fm ∧ modexp_desc fm = MED_global (Mk_globalidx fa)⌝.
  Proof.
    iIntros (Hft Hfa) "[_ Himps]".
    iDestruct (big_sepL2_length with "Himps") as %Hlen.
    iInduction (t_imps) as [] "IH" forall (v_imps k Hlen Hft Hfa).
    { inversion Hft. }
    { destruct v_imps;[done|].
      simpl in Hlen;inversion Hlen.
      destruct k.
      { iDestruct "Himps" as "[Hf Himps]".
        simpl in Hfa. 
        destruct (modexp_desc m) eqn:Hmod.
        4: { iClear "Himps".
          destruct g. simpl in Hfa. simplify_eq.
          iDestruct "Hf" as (? ?) "[Hfa [? %Ha]]".
          destruct Ha as [Hwfs Ha]. subst.
          simpl in Hft. simplify_eq.
          iExists 0. iSimpl. iSplit;auto.
          iExists _. iSplit;eauto. }
        { destruct f. cbn in Hfa.
          iDestruct "Hf" as (?) "[? %Ha]".
          destruct Ha as [Hwts Heq].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). simpl. eauto. }
        { destruct t. cbn in Hfa.
          iDestruct "Hf" as (? ?) "[? [? [? %Ha]]]".
          destruct Ha as [Hwts [Heq Htyp]].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). simpl. eauto. }
        { destruct m0. cbn in Hfa.
          iDestruct "Hf" as (g gt) "[? [_ %Ha]]".
          destruct Ha as [Hwts [Heq Htyp]].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). simpl. eauto. }
      }
      { iDestruct "Himps" as "[Hf Himps]".
        simpl in *.
        destruct (modexp_desc m) eqn:Hmod.
        all: simpl in *.
        4: { destruct g. iDestruct "Hf" as (? ?) "[?[Hfa %Ha]]".
          destruct Ha as [Hwfs Ha]. subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
        { destruct f. iDestruct "Hf" as (?) "[? %Ha]".
          destruct Ha as [Hwts Heq]. subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
        { destruct t. iDestruct "Hf" as (mem mt) "[? [? [? %Ha]]]".
          destruct Ha as [Hwts [Heq Htyp]]. subst a;simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
        { destruct m0. iDestruct "Hf" as (g gt) "[? [? %Ha]]".
          destruct Ha as [Hwts [Heq Htyp]].
          subst a. simpl in Hft.
          iDestruct ("IH" with "[] [] [] Himps") as (k') "HH";eauto.
          iExists (S k'). eauto. }
      }
    }
  Qed.

  (*
  Lemma interp_table_alloc n0 (P : function_type -> nat -> iProp Σ) n :
    (∀ x y, Persistent (P x y)) ->
    ([∗ list] j↦tabelem ∈ repeat None n0, na_inv logrel_nais (wtN (N.of_nat n) (N.of_nat j))
                                                                         (N.of_nat n↦[wt][N.of_nat j]tabelem)) -∗
    [∗ list] i↦_ ∈ repeat 0 n0, 
      ∃ (τf : function_type) (fe : funcelem),
        na_inv logrel_nais (wtN (N.of_nat n) (N.of_nat i))
               (N.of_nat n↦[wt][N.of_nat i]fe) ∗ from_option (P τf) True fe.
  Proof.
    iIntros (Hpers) "#H".
    iApply (big_sepL_forall).
    iIntros (k x Hlook).
    apply lookup_lt_Some in Hlook as Hlt.
    rewrite repeat_length in Hlt.
    eapply repeat_lookup in Hlt as Hy.
    iDestruct (big_sepL_lookup with "H") as "H'";eauto.
    Unshelve. exact (Tf [] []).
  Qed.*)

  Lemma repeat_imap_eq {A B C : Type} (a : A) (b : B) (f : nat -> C) (m : nat) :
    imap (λ i _, f i) (repeat a m) = imap (λ i _, f i) (repeat b m).
  Proof.
    remember (repeat a m).
    remember (repeat b m).
    generalize dependent l0.
    generalize dependent m.
    generalize dependent f.
    induction l;intros f m Hl l0 Hl0.
    { destruct m;try done. simpl in Hl0. rewrite Hl0.
      simpl. auto. }
    { destruct m;[done|].
      destruct l0;inversion Hl0.
      simplify_eq.
      simpl. f_equiv.
      assert ((λ (i : nat) (_ : A), f i) ∘ S =
                (λ (i : nat) (_ : A), f (S i))) as ->;auto.
      assert ((λ (i : nat) (_ : B), f i) ∘ S =
                (λ (i : nat) (_ : B), f (S i))) as ->;auto.
      
      eapply IHl;eauto. simpl in Hl. inversion Hl;auto.
    }
  Qed.

  Lemma repeat_imap_lookup {A B : Type} (a a' : A) (f : nat -> B) (m k : nat) :
    (repeat a m) !! k = Some a' ->
    (imap (λ i _, f i) (repeat a m)) !! k = Some (f k).
  Proof.
    remember (repeat a m).
    generalize dependent m.
    generalize dependent f.
    generalize dependent k.
    induction l;intros k f m Hl Hin.
    { done. }
    { destruct m;[done|].
      simpl in Hl. inversion Hl;subst a0.
      destruct k.
      { simpl in Hin. inversion Hin. auto. }
      { simpl in *.
        assert ((λ (i : nat) (_ : A), f i) ∘ S =
                  (λ (i : nat) (_ : A), f (S i))) as ->;auto.
        eapply IHl with (f:=(λ (i : nat), f (S i))) in Hin;eauto.
        rewrite H1 in Hin. rewrite Hin. auto.
      }
    }
  Qed.
    

  Definition module_typing_body (m : module) (impts : list extern_t) (expts : list extern_t) fts gts : Prop :=
    let '{| 
            mod_types := tfs;
            mod_funcs := fs;
            mod_tables := ts;
            mod_mems := ms;
            mod_globals := gs;
            mod_elem := els;
            mod_data := ds;
            mod_start := i_opt;
            mod_imports := imps;
            mod_exports := exps;
          |} := m in
    let ifts := ext_t_funcs impts in
    let its := ext_t_tabs impts in
    let ims := ext_t_mems impts in
    let igs := ext_t_globs impts in
    let c := {|
              tc_types_t := tfs;
              tc_func_t := List.app ifts fts;
              tc_global := List.app igs gts;
              tc_table := List.app its (List.map (fun t => t.(modtab_type)) ts);
              tc_memory := List.app ims ms; (* TODO: should use `mem_type`s *) (* UPD: fixed? *)
              tc_local := nil;
              tc_label := nil;
              tc_return := None;
            |} in
    let c' := {|
               tc_types_t := nil;
               tc_func_t := nil;
               tc_global := igs;
               tc_table := nil;
               tc_memory := nil;
               tc_local := nil;
               tc_label := nil;
               tc_return := None;
             |} in
    List.Forall2 (module_func_typing c) fs fts /\
      seq.all module_tab_typing ts /\
      seq.all module_mem_typing ms /\
      List.Forall2 (module_glob_typing c') gs gts /\
      List.Forall (module_elem_typing c) els /\
      List.Forall (module_data_typing c) ds /\
      pred_option (module_start_typing c) i_opt /\
      List.Forall2 (fun imp => module_import_typing c imp.(imp_desc)) imps impts /\
      List.Forall2 (fun exp => module_export_typing c exp.(modexp_desc)) exps expts.

  Lemma module_typing_body_eq m impts expts :
    module_typing m impts expts <-> ∃ fts gts, module_typing_body m impts expts fts gts.
  Proof. auto. Qed.

  Lemma module_tab_init_values_lookup m inst l k n :
    module_tab_init_values m inst l !! (0,k) = Some n ->
    ∃ j elem,
      l !! j = Some elem ∧
        match modelem_table elem with
        | Mk_tableidx i =>
            build_tab_initialiser (inst_funcs inst) elem i (assert_const1_i32_to_nat (modelem_offset elem)) !! (0,k) = Some n
        end.
  Proof.
    induction l.
    { cbn. done. }
    { cbn in *. destruct (modelem_table a) eqn:Hn0.
      intros Hlook.
      eassert (is_Some (_ !! (0,k))) as Hissome;eauto.
      apply lookup_union_is_Some in Hissome as [[n' Hsome]|[n' Hsome]].
      { erewrite lookup_union_Some_l in Hlook;eauto. simplify_eq.
        apply IHl in Hsome.
        destruct Hsome as [j [elem Hj]].
        exists (S j),elem. simpl. auto. }
      { destruct (module_tab_init_values m inst l !! (0,k)) eqn:Hsome'.
        { erewrite lookup_union_Some_l in Hlook;eauto. simplify_eq.
          destruct IHl as [j [elem Hj]];auto.
          exists (S j),elem. simpl. auto. }
        { exists 0,a. split;auto.
          rewrite Hn0.
          erewrite lookup_union_r in Hlook;auto. } 
      }
    }
  Qed.

  Lemma build_tab_initialiser_lookup instfuncs elem i k n :
    (build_tab_initialiser instfuncs elem i (assert_const1_i32_to_nat (modelem_offset elem))) !! (0,k) = Some (Some n) ->
    ∃ j fid, k = i + j + (assert_const1_i32_to_nat (modelem_offset elem)) ∧ (modelem_init elem) !! j = Some (Mk_funcidx fid) ∧
               instfuncs !! fid = Some n.
  Proof.
    destruct elem;simpl.
    unfold build_tab_initialiser. simpl.
    induction modelem_init using rev_ind.
    { simpl. done. }
    { rewrite - fold_left_rev_right imap_app /= rev_unit /=.
      destruct x. rewrite !PeanoNat.Nat.add_0_r.
      destruct (decide ((i,length modelem_init + assert_const1_i32_to_nat modelem_offset) = (0,k))).
      { rewrite e lookup_insert. intros Heq. simplify_eq.
        rewrite nth_error_lookup in Heq.
        exists (length modelem_init),n0.
        split;[lia|].
        split;[by apply list_lookup_middle|auto]. }
      { rewrite lookup_insert_ne// fold_left_rev_right.        
        intros Hlook.
        apply IHmodelem_init in Hlook as [j [fid [Haddeq [Hlook Hn]]]].
        apply lookup_lt_Some in Hlook as Hlt.
        exists j,fid. repeat split;auto.
        rewrite lookup_app_l//.
      }
    }
  Qed.
    
  
  Definition module_inst_resources_wasm_invs (m : module) (inst : instance) (g_inits : seq.seq value) (gts : seq.seq global_type) t_inits :=
    (module_inst_resources_func_invs (mod_funcs m) inst
     (drop (get_import_func_count m) (inst_funcs inst)) ∗
    module_inst_resources_tab_invs (mod_tables m) t_inits
     (drop (get_import_table_count m) (inst_tab inst)) ∗
    module_inst_resources_mem_invs (mod_mems m)
     (drop (get_import_mem_count m) (inst_memory inst))∗
    module_inst_resources_glob_invs (mod_globals m) g_inits
     (drop (get_import_global_count m) (inst_globs inst)) gts)%I.
                                    
  
  Lemma interp_instance_alloc E m t_imps t_exps v_imps (wfs : gmap N function_closure) wts wms wgs g_inits t_inits m_inits inst fts gts :
    let C := {|
              tc_types_t := (mod_types m);
              tc_func_t := ((ext_t_funcs t_imps) ++ fts)%list;
              tc_global := ((ext_t_globs t_imps) ++ gts)%list;
              tc_table := ((ext_t_tabs t_imps) ++ map (λ t : module_table, modtab_type t) (mod_tables m))%list;
              tc_memory := ((ext_t_mems t_imps) ++ (mod_mems m))%list;
              tc_local := [];
              tc_label := [];
              tc_return := None;
            |} in
    module_typing_body m t_imps t_exps fts gts ->
    (inst.(inst_types) = m.(mod_types) /\
       let v_imp_descs := map (fun mexp => mexp.(modexp_desc)) v_imps in
       prefix (ext_func_addrs v_imp_descs) inst.(inst_funcs) /\
         prefix (ext_tab_addrs v_imp_descs) inst.(inst_tab) /\
         prefix (ext_mem_addrs v_imp_descs) inst.(inst_memory) /\
         prefix (ext_glob_addrs v_imp_descs) inst.(inst_globs)) ->
    module_init_values m inst t_inits m_inits g_inits ->
    
    ([∗ map] _↦cl ∈ wfs, interp_closure (HWP:=HWP) (cl_type cl) cl)%I -∗ (* we must assume that the imported closures are valid *)
    ([∗ map] n↦t ∈ wts, interp_table (tab_size t) (interp_closure_pre C wfs inst) n) -∗ (* that imported tables are valid *)
    ([∗ map] n↦m ∈ wms, interp_mem n) -∗ (* that imported memories are valid *)
    
                                                                   
    import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
    module_inst_resources_wasm m inst t_inits m_inits g_inits
    ={E}=∗ interp_instance (HWP:=HWP) C inst ∗
           module_inst_resources_wasm_invs m inst g_inits gts t_inits (* it is useful to remember the exact values for each allocated invariant *).
  Proof.
    iIntros (C Hmod Himps_of_inst Hinit_vals) "#Himps_val #Htabs_val #Hmems_val Hir Hmr".
    subst C.
    set (ifts := ext_t_funcs t_imps).
    set (its := ext_t_tabs t_imps).
    set (ims := ext_t_mems t_imps).
    set (igs := ext_t_globs t_imps).
    
    iDestruct "Hmr" as "(Hfr & Htr & Hmr & Hgr)".
    iDestruct (module_res_imports_disj with "Hir Hfr") as %Hdisj.
    iDestruct (import_resources_wasm_typecheck_lengths with "Hir") as %(Hlenir&Hlenir0&Hlenir1&Hlenir2).
    iMod (import_resources_wasm_typecheck_alloc with "Hir") as "#Hir".    
    (* iDestruct (module_inst_resources_func_NoDup with "Hfr") as %Hnodup. *)
    iMod (module_inst_resources_func_invs_alloc with "Hfr") as "#Hfr".
    iMod (module_inst_resources_tab_invs_alloc with "Htr") as "#Htr".
    iMod (module_inst_resources_mem_invs_alloc with "Hmr") as "#Hmr".
    iMod (module_inst_resources_glob_invs_alloc with "Hgr") as "#Hgr";[eauto..|].
    { destruct m. simpl in Hmod.
      destruct Hmod as (Htypes & Htables & Hmems & Hglobals
                        & Helem & Hdata & Hstart & Himps & Hexps). eauto. }
    { destruct Hinit_vals as [? [? [? ?]]]. auto. }
    iModIntro. iFrame "#".
    
    iApply (interp_instance_pre_create _ wfs);[auto|].
    unfold interp_instance_pre. remember inst. destruct inst. rewrite Heqi.
    rewrite Heqi in Himps_of_inst.
    destruct Himps_of_inst as (Htypeq & Hprefunc & Hpretables & Hpremem & Hpreglob).
    iSplitR.
    { destruct m. simpl in Hmod.
      simpl in *. auto. }

    (* functions *)
    iSplitR.
    { iSimpl in "Hfr". simpl in Hprefunc.
      iApply big_sepL2_forall.
      iDestruct (big_sepL2_length with "Hfr") as %Hlenfr.      
      iSplit.
      { iDestruct "Hir" as "[Hdom Hir]".
        iDestruct (big_sepL2_length with "Hir") as %Himp_len.
        destruct m. simpl in Hmod.
        destruct Hmod as (Htypes & Htables & Hmems & Hglobals
                          & Helem & Hdata & Hstart & Himps & Hexps).
        iPureIntro. eapply inst_funcs_length_imp_app;eauto. simpl.
        by apply Forall2_length in Htypes as Hlenfr'. }
      iIntros (k fa ft Hfa Hft).
      destruct Hprefunc as [fdecls Himpdeclapp].
      rewrite Himpdeclapp in Hfa.
      unfold ifts in Hft.
      apply lookup_app_Some in Hft as [Hft | [Hge Hft]].
      { (* the function is imported, and semantic typing has been established prior *)
        apply lookup_lt_Some in Hft as Hlt.
        rewrite -Hlenir in Hlt.
        rewrite lookup_app_l in Hfa;[|apply Hlt].
        iDestruct (import_funcs_lookup with "Hir") as %Hlook;eauto.
        destruct Hlook as [k' [Hft' Ha']].
        destruct Ha' as [fm [Hfm' Heq]].
        iDestruct "Hir" as "[Hdom Hir]".
        iDestruct (big_sepL2_lookup with "Hir") as "Haa";eauto.
        rewrite Heq. iDestruct "Haa" as (cl) "[Hown %Hcl]".
        destruct Hcl as [Hwfs Hfteq]. simplify_eq.
        iDestruct (big_sepM_lookup with "Himps_val") as "Ha";[eauto|].
        iExists cl. iFrame "#". iSimpl.
        destruct cl;eauto. rewrite Hwfs; eauto. 
      }
      { (* the function is declared and syntactically well-typed *)
        unfold module_inst_resources_func_invs.
        destruct m. simpl in Hmod.
        destruct Hmod as (Htypes & Htables & Hmems & Hglobals
                          & Helem & Hdata & Hstart & Himps & Hexps).
        rewrite Himpdeclapp.
        eassert (get_import_func_count _ = length _) as ->.
        { eapply get_import_count_length;eauto. }
        rewrite -Hlenir. rewrite drop_app.
        eapply Forall2_lookup_r in Htypes as [mf [Hmf Hftyp]];[|eauto].
        simpl.
        rewrite lookup_app_r in Hfa;[|rewrite Hlenir//].
        rewrite Hlenir in Hfa.
        
        assert (wfs !! (N.of_nat fa) = None) as Hnone.
        { apply Hdisj with ((k - length (ext_t_funcs t_imps))). rewrite Heqi. simpl datatypes.inst_funcs.
          rewrite Himpdeclapp.
          eassert (get_import_func_count _ = length _) as ->.
          { eapply get_import_count_length;eauto. }
          rewrite -Hlenir drop_app. rewrite Hlenir. auto. }

        iDestruct (big_sepL2_lookup with "Hfr") as "Hf";[eauto..|].
        destruct mf,ft. simpl in *.
        destruct modfunc_type;simplify_eq.
        iExists _. iFrame "#".
        rewrite Hnone. iSplit;[auto|].
        destruct Hftyp as [Hle [Heq Hftyp]].
        revert Heq. move/eqP =>Heq. rewrite Heq. iSplit;auto. }
    }

    (* function tables *)
    iSplitR.
    { iClear "Hmr Hgr". iSimpl in "Htr". simpl in Hpretables.
      destruct Hpretables as [fdecls Himpdeclapp].
      remember m.
      destruct m. rename m0 into m. simpl in Hmod.
      rewrite Heqm0 in Hmod.
      destruct Hmod as (Htypes & Htables & Hmems & Hglobals
                        & Helem & Hdata & Hstart & Himps & Hexps).
      rewrite Heqm0.
      eassert (get_import_table_count _ = length _) as ->.
      { eapply get_import_count_length;simpl;eauto. }
      rewrite Himpdeclapp. simpl datatypes.mod_tables.
      rewrite -Hlenir0 drop_app.
      rewrite -/its in Hlenir0.
      iDestruct (big_sepL2_length with "Htr") as %Htbllen.
      remember (its).
      destruct l.
      { destruct mod_tables;auto.
        destruct ((ext_tab_addrs
                 (map (λ mexp : module_export, modexp_desc mexp) v_imps)));[|done].
        (* the function table is declared *)
        simpl nth_error.
        destruct fdecls;[done|].
        unfold module_inst_resources_tab_invs.
        iSimpl in "Htr".
        iDestruct "Htr" as "[[Htsize [Hlim Ht]] _]".
        iExists _,_. iFrame "Htsize". iFrame "Hlim".
        destruct (tt_limits (modtab_type m0)).
        simpl table_data. unfold tab_size. simpl.
        iSplit.
        { iPureIntro. apply/ssrnat.leP. lia. }
        { rewrite (repeat_imap_eq _ 0).
          rewrite imap_length repeat_length.
          (* the table can be initialised with imported or declared functions *)
          iApply big_sepL_forall.
          iIntros (k j Hj).
          apply repeat_imap_lookup with (f := λ i, match t_inits !! (0, i) with
                                                   | Some felem => felem
                                                   | None => None
                                                   end) in Hj.
          iDestruct (big_sepL_lookup _ _ k with "Ht") as "Hk";[eauto|].
          destruct (t_inits !! (0,k)) eqn:Hk.
          { destruct o.
            { destruct Hinit_vals as [Ht_inits _].
              rewrite Ht_inits /= in Hk.
              apply module_tab_init_values_lookup in Hk as [i' [elem He]].
              rewrite Heqm0 /= in He.
              destruct elem, modelem_table;simpl in *.
              destruct He as [He Ht].
              apply build_tab_initialiser_lookup in Ht as [h [fid [Hadd [Hinit Hinst_funcs]]]].
              rewrite Heqi in Hinst_funcs.
              simpl in *.
              destruct (decide (fid < (get_import_func_count m))).
              { (* the initialiser is imported *)
                destruct Hprefunc as [decls Hfunceq]. rewrite Hfunceq in Hinst_funcs.
                rewrite lookup_app_l in Hinst_funcs;cycle 1.
                { rewrite Hlenir.
                  eassert (get_import_func_count m = length _) as <-.
                  { eapply get_import_count_length;eauto. rewrite Heqm0. eauto. }
                  auto. }
                assert (is_Some (ext_t_funcs t_imps !! fid)) as [ft Hft].
                { apply lookup_lt_is_Some.
                  eassert (get_import_func_count m = length _) as <-.
                  { eapply get_import_count_length;eauto. rewrite Heqm0. eauto. }
                  auto. }
                iDestruct (import_funcs_lookup with "Hir") as %Hk';[eauto..|].
                destruct Hk' as [k' [Ht_imps [fm [Hv_imps Hfm]]]].
                iDestruct "Hir" as "[%Hdom Hir]".
                iDestruct (big_sepL2_lookup with "Hir") as "HH";[eauto..|].
                rewrite Hfm. iDestruct "HH" as (cl) "[Hown [%Hcl %Hcltyp]]". inversion Hcltyp.
                iDestruct (big_sepM_lookup with "Himps_val") as "Hcl";[apply Hcl|].
                iExists _,_. iFrame "Hk". iSimpl.
                iExists _. iFrame "Hown".
                destruct cl;[|auto]. rewrite Hcl. auto. }
              { (* the initialiser is declared *)
                destruct Hprefunc as [decls Hfunceq]. rewrite Hfunceq in Hinst_funcs.
                eassert (drop (get_import_func_count m) inst_funcs !! (fid - _) = Some n0) as Hfid.
                { rewrite lookup_app_r in Hinst_funcs;cycle 1.
                  { rewrite Hlenir.
                    eassert (get_import_func_count m = length _) as <-.
                    { eapply get_import_count_length;eauto. rewrite Heqm0. eauto. }
                    clear -n2. lia. }
                  eassert (get_import_func_count m = length _) as ->.
                  { eapply get_import_count_length;eauto. rewrite Heqm0. eauto. }
                  rewrite -Hlenir Hfunceq. rewrite drop_app. eauto. }
                rewrite -Heqm0.
                iDestruct (big_sepL2_length with "Hfr") as %Hfrlen.
                apply lookup_lt_Some in Hfid as Hltfid.
                rewrite -Hfrlen in Hltfid.
                apply lookup_lt_is_Some in Hltfid as [fm Hfm].
                eapply Forall2_lookup_l in Htypes as [mf [Hmf Hftyp]];[|eauto].
                iDestruct (big_sepL2_lookup with "Hfr") as "HH";[eauto..|].
                destruct mf,fm,modfunc_type;simpl in *.
                destruct Hftyp as [Hle [Hnth Hftyp]].
                revert Hnth; move/eqP => Hnth.
                assert (wfs !! (N.of_nat n0) = None) as Hnone.
                { eapply Hdisj. rewrite Heqi;eauto. }
                iExists _,_. iFrame "#". iSimpl.
                iExists _. iFrame "#". iSimpl. rewrite  Hnone.
                iPureIntro.
                repeat split;auto. rewrite Htypeq Heqm0 /= Hnth.
                rewrite -/its -Heql app_nil_l in Hftyp. auto. }                  
            }
            { iExists (Tf [] []),_. iFrame "#". }
          }
          { iExists (Tf [] []),_. iFrame "#". }
        }
      }
          
      { (* the function table is imported *)
        rewrite /its in Heql.
        remember (ext_tab_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)).
        destruct l0;[done|].
        iDestruct (import_tabs_lookup (k:=0) with "Hir") as %HH;[rewrite -Heql;eauto|rewrite -Heql0;eauto|].
        destruct HH as [k' [Hlook1 Hfm]]. destruct Hfm as [fm [Hlook2 Hfm]].
        iDestruct "Hir" as "[%Hdom Hir]".
        iDestruct (big_sepL2_lookup with "Hir") as "Hk'";[eauto..|].
        rewrite Hfm. iDestruct "Hk'" as (tab tt) "(Hsize & Hlim & Helem & %Htyping)".
        destruct Htyping as (Hwts & Htteq & Htyping). simplify_eq.
        iDestruct (big_sepM_lookup with "Htabs_val") as "Htval";[eauto|].
        iExists _,_. iFrame "#".
        by apply andb_true_iff in Htyping as [? ->].        
      }
    }

    (* memory *)
    iSplitR.
    { iClear "Hfr Htr". iSimpl in "Hmr". simpl in Hpremem.
      destruct Hpremem as [fdecls Himpdeclapp].
      destruct m. simpl in Hmod.
      destruct Hmod as (Htypes & Htables & Hmems & Hglobals
                        & Helem & Hdata & Hstart & Himps & Hexps).
      eassert (get_import_mem_count _ = length _) as ->.
      { eapply get_import_count_length;simpl;eauto. }
      rewrite Himpdeclapp. simpl datatypes.mod_mems.
      rewrite -Hlenir1 drop_app.
      rewrite -/ims in Hlenir1.
      iDestruct (big_sepL2_length with "Hmr") as %Hmemlen.
      remember (ims).
      destruct l.
      { destruct mod_mems;auto.
        destruct ((ext_mem_addrs
                 (map (λ mexp : module_export, modexp_desc mexp) v_imps)));[|done].
        (* the memory is declared *)
        simpl nth_error.
        destruct fdecls;[done|].
        unfold module_inst_resources_mem_invs.
        iSimpl in "Hmr".
        iDestruct "Hmr" as "[[$ $] _]". }
      { (* the memory is imported *)
        rewrite /ims in Heql.
        remember (ext_mem_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)).
        destruct l0;[done|].
        iDestruct (import_mems_lookup (k:=0) with "Hir") as %HH;[rewrite -Heql;eauto|rewrite -Heql0;eauto|].
        destruct HH as [k' [Hlook1 Hfm]]. destruct Hfm as [fm [Hlook2 Hfm]].
        iDestruct "Hir" as "[%Hdom Hir]".
        iDestruct (big_sepL2_lookup with "Hir") as "Hk'";[eauto..|].
        rewrite Hfm. iDestruct "Hk'" as (mem mt) "(Hmem & Hlim & %Htyp)".
        destruct Htyp as (Hwms & Hmemeq & Htyping). simplify_eq.
        iDestruct (big_sepM_lookup with "Hmems_val") as "Htval";[eauto|].
        revert Htyping. move/andP=>[? Htyping];revert Htyping;move/eqP =>Heq.
        rewrite Heq. iFrame "#".
      }
    }

    (* globals *)
    { iClear "Hfr Hmr Htr". iSimpl in "Hgr". simpl in Hpreglob.
      destruct Hpreglob as [fdecls Himpdeclapp].
      destruct m. simpl in Hmod.
      destruct Hmod as (Htypes & Htables & Hmems & Hglobals
                        & Helem & Hdata & Hstart & Himps & Hexps).
      eassert (get_import_global_count _ = length _) as ->.
      { eapply get_import_count_length;simpl;eauto. }
      rewrite Himpdeclapp. simpl datatypes.mod_globals.
      rewrite -Hlenir2 drop_app.
      rewrite -/igs in Hlenir2.
      iDestruct (big_sepL2_length with "Hgr") as %Hgloblen.
      iApply big_sepL2_app.
      { (* imported globals *)
        iApply big_sepL2_forall.
        iSplit;auto.
        iIntros (k n gt Hlook1 Hlook2).
        rewrite /igs in Hlook2.
        iDestruct (import_globs_lookup with "Hir") as %Hh;[eauto..|].
        destruct Hh as [k' [Hk' Hfm]].
        destruct Hfm as [fm [Hfm Hfmeq]].
        iDestruct "Hir" as "[%Hdom Hir]".
        iDestruct (big_sepL2_lookup with "Hir") as "Hg";[eauto..|].
        rewrite Hfmeq.
        iDestruct "Hg" as (g gt') "[Hinv %Hconds]".
        destruct Hconds as (Hwgs & Hgteq & Hagree).
        simplify_eq.
        unfold interp_global. simpl.
        destruct (tg_mut gt') eqn:Hmut.
        { iExists interp_value. iFrame "Hinv". iModIntro. auto. }
        { iFrame "Hinv". }        
      }
      { (* declared globals *)
        iApply big_sepL2_forall.
        apply Forall2_length in Hglobals as Hgloblen'.
        rewrite -Hgloblen Hgloblen'. iSplit;auto.
        iIntros (k n gt Hlook1 Hlook2).
        eapply Forall2_lookup_r in Hglobals as [g [Hg Hgtyp]];eauto.
        iDestruct (big_sepL2_lookup with "Hgr") as (w τg) "[%Hginit [%Hgts Hg]]";[eauto..|].
        rewrite Hlook2 in Hgts. inversion Hgts.
        unfold interp_global. iSimpl. 
        destruct (tg_mut τg) eqn:Hmut.
        { iExists interp_value. iFrame "Hg". iModIntro. auto. }
        { iFrame "Hg". }        
      }
    }
  Qed.
    

End InterpInstance.
