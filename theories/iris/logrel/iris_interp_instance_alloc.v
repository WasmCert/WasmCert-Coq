From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.

Require Export iris_host iris_fundamental.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section InterpInstance.

  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ,
        !logrel_na_invs Σ}.

  Definition interp_closure_pre τctx (fimps : gmap N function_closure) (i : instance) hl (n : N) (τf : function_type) :=
    λne (cl : leibnizO function_closure),
         match cl with
         | FC_func_native j τ' t_locs b_es =>
             match fimps !! n with
             | Some cl' => (⌜cl' = cl⌝ ∗ interp_closure hl τf cl)%I
             | None => (⌜i = j ∧ τf = τ' ∧
                         let 'Tf tn tm := τf in
                         be_typing (upd_local_label_return τctx (tn ++ t_locs) [tm] (Some tm)) b_es (Tf [] tm)⌝)%I
             end
         | _ => interp_closure hl τf cl
         end.
  Global Instance interp_closure_pre_persistent τctx fimps n i τf cl hl : Persistent (interp_closure_pre τctx fimps i n τf hl cl).
  Proof. destruct cl,f;try apply _. Qed.
  Global Instance interp_closure_persistent τf cl hl : Persistent (interp_closure hl τf cl).
  Proof. destruct cl,f;try apply _. Qed.
  
  Definition interp_instance_pre (τctx : t_context) (fimps : gmap N function_closure) hl :=
    λne (i : leibnizO instance), interp_instance' τctx (interp_closure_pre τctx fimps i hl) (interp_closure_pre τctx fimps i hl) i.
  Global Instance interp_instance_pre_persistent τctx fimps i hl : Persistent (interp_instance_pre τctx fimps i hl).
  Proof. apply interp_instance_persistent';intros; destruct cl,f; apply _.  Qed.

  Lemma n_zeros_interp_values l :
    ⊢ ([∗ list] y1;y2 ∈ n_zeros l;l, interp_value (Σ:=Σ) y2 y1)%I.
  Proof.
    iApply big_sepL2_forall.
    iSplit;[iPureIntro;apply map_length|].
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

  Lemma interp_closure_pre_ind C i ft cl fimps n (hl : seq.seq (hostfuncidx * function_type)) :
    tc_label C = [] ∧ tc_return C = None ->
    (□ ▷ interp_instance C hl i) -∗
    interp_closure_pre C fimps i hl n ft cl -∗
    interp_closure hl ft cl.
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
        iIntros (vcs f) "Hv Hown Hf".
        iDestruct "Hv" as "[%Hcontr|Hv]";[done|iDestruct "Hv" as (v' Heqv) "#Hv"].
        iDestruct (be_fundamental_local_stuck_host with "IH") as "HH";eauto. inversion Heqv.
        
        iDestruct ("HH" $! _ (v' ++ n_zeros l) with "[$] [$] []") as "Hcont".
        { iRight. iExists _. iSplit;[eauto|]. iApply big_sepL2_app;iFrame "#".
          iApply n_zeros_interp_values. }
        iSimpl in "Hcont".
        iIntros (LI Hfill%lfilled_Ind_Equivalent).
        inversion Hfill;inversion H9;simplify_eq.
        repeat erewrite app_nil_l, app_nil_r.
        unfold interp_expression_closure_stuck_host.
        iApply (wp_wand with "Hcont"). iIntros (v) "[[$ $] $]".
      }
    }
    { simpl. auto. }
  Qed.
    
  
  Lemma interp_instance_pre_create τctx i fimps hl :
    (tc_label τctx) = [] ∧ (tc_return τctx) = None ->
    interp_instance_pre τctx fimps hl i -∗
    interp_instance τctx hl i.
  Proof.
    iIntros (Hnil) "#Hpre".
    iLöb as "IH".
    set (IH := (▷ interp_instance τctx hl i)%I).
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

  Definition import_func_nainv (wfs: gmap N function_closure) : iProp Σ :=
    [∗ map] i ↦ v ∈ wfs, na_inv logrel_nais (wfN i) (i ↦[wf] v).

  Definition import_tab_nainv (wts: gmap N tableinst) : iProp Σ :=
    [∗ map] i ↦ v ∈ wts, ((i ↪[wtsize] tab_size v) ∗
                          (i ↪[wtlimit] table_max_opt v) ∗
                          ([∗ list] j↦tabelem ∈ table_data v,
                           na_inv logrel_nais (wtN i (N.of_nat j)) (i ↦[wt][N.of_nat j] tabelem))).

  Definition import_mem_nainv (wms: gmap N memory) : iProp Σ :=
    [∗ map] i ↦ v ∈ wms, ((na_inv logrel_nais (wmN i) (∃ (mem: memory),
                                                         ([∗ list] j ↦ b ∈ (mem.(mem_data).(ml_data)), i ↦[wm][N.of_nat j] b) ∗
                                            i ↦[wmlength] mem_length mem)) ∗
                                        i ↪[wmlimit] mem_max_opt v).

  Definition import_glob_nainv (wgs: gmap N global) : iProp Σ :=
    [∗ map] i ↦ v ∈ wgs, na_inv logrel_nais (wgN i)
                                      (∃ w, i ↦[wg] Build_global (g_mut v) w
                                           ∗ interp_value (typeof (g_val v)) w).

  Definition import_func_wasm_check_invs v_imps t_imps wfs : iProp Σ :=
    import_func_nainv wfs ∗  
    ⌜ func_domcheck v_imps wfs /\
    func_typecheck v_imps t_imps wfs ⌝.

  Definition import_tab_wasm_check_invs v_imps t_imps wts : iProp Σ :=
    import_tab_nainv wts ∗
    ⌜ tab_domcheck v_imps wts /\
    tab_typecheck v_imps t_imps wts ⌝.
  
  Definition import_mem_wasm_check_invs v_imps t_imps wms : iProp Σ :=
    import_mem_nainv wms ∗
    ⌜ mem_domcheck v_imps wms /\
    mem_typecheck v_imps t_imps wms ⌝.
  
  Definition import_glob_wasm_check_invs v_imps t_imps wgs : iProp Σ :=
    import_glob_nainv wgs ∗
    ⌜ glob_domcheck v_imps wgs /\ 
    glob_typecheck v_imps t_imps wgs ⌝.
  
  Definition import_resources_wasm_typecheck_invs (v_imps: list module_export)
             (t_imps: list extern_t) (wfs: gmap N function_closure)
             (wts: gmap N tableinst) (wms: gmap N memory) (wgs: gmap N global): iProp Σ :=
    import_func_wasm_check_invs v_imps t_imps wfs ∗
    import_tab_wasm_check_invs v_imps t_imps wts ∗
    import_mem_wasm_check_invs v_imps t_imps wms ∗
    import_glob_wasm_check_invs v_imps t_imps wgs.
  
  
  Global Instance imports_invs_persistent v_imps t_imps wfs wts wms wgs : Persistent (import_resources_wasm_typecheck_invs v_imps t_imps wfs wts wms wgs).
  Proof.  
    repeat (apply bi.sep_persistent;[apply _|]).
    by apply _.
  Qed.

  Lemma import_func_wasm_check_alloc E v_imps t_imps wfs:
    import_func_wasm_check v_imps t_imps wfs ={E}=∗
    import_func_wasm_check_invs v_imps t_imps wfs.
  Proof.
    iIntros "(Hm & %Ht & %Hdom)".
    unfold import_func_wasm_check_invs.
    iSplitL => //.
    unfold import_func_resources, import_func_nainv.
    iApply big_sepM_fupd.
    iApply (big_sepM_mono with "Hm").
    iIntros (k v Hl) "Hm".
    iApply na_inv_alloc.
    by iNext.
  Qed.
                                            
  Lemma import_tab_wasm_check_alloc E v_imps t_imps wfs:
    import_tab_wasm_check v_imps t_imps wfs ={E}=∗
    import_tab_wasm_check_invs v_imps t_imps wfs.
  Proof.
    iIntros "(Hm & %Ht & %Hdom)".
    unfold import_tab_wasm_check_invs.
    iSplitL => //.
    unfold import_tab_resources, import_tab_nainv.
    iApply big_sepM_fupd.
    iApply (big_sepM_mono with "Hm").
    iIntros (k v Hl) "(?&?&?)".
    iFrame.
    iApply big_sepL_fupd.
    iApply (big_sepL_mono with "[$]").
    iIntros (???)"?".
    iApply na_inv_alloc.
    by iNext.
  Qed.
  
  Lemma import_mem_wasm_check_alloc E v_imps t_imps wfs:
    import_mem_wasm_check v_imps t_imps wfs ={E}=∗
    import_mem_wasm_check_invs v_imps t_imps wfs.
  Proof.
    iIntros "(Hm & %Ht & %Hdom)".
    unfold import_mem_wasm_check_invs.
    iSplitL => //.
    unfold import_mem_resources, import_mem_nainv.
    iApply big_sepM_fupd.
    iApply (big_sepM_mono with "Hm").
    iIntros (k v Hl) "(?&?&?)".
    iFrame.
    iApply na_inv_alloc. iNext.
    iExists _.
    by iFrame.
  Qed.
  
  Lemma import_glob_wasm_check_alloc E v_imps t_imps wfs:
    import_glob_wasm_check v_imps t_imps wfs ={E}=∗
    import_glob_wasm_check_invs v_imps t_imps wfs.
  Proof.
    iIntros "(Hm & %Ht & %Hdom)".
    unfold import_glob_wasm_check_invs.
    iSplitL => //.
    unfold import_glob_resources, import_glob_nainv.
    iApply big_sepM_fupd.
    iApply (big_sepM_mono with "Hm").
    iIntros (k v Hl) "Hm".
    iApply na_inv_alloc.
    iNext.
    iExists (g_val v).
    destruct v => /=.
    iFrame.
    destruct g_val => /=; by iExists _.
  Qed.
  
  Lemma import_resources_wasm_typecheck_alloc E v_imps t_imps wfs wts wms wgs :
    import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs ={E}=∗
    import_resources_wasm_typecheck_invs v_imps t_imps wfs wts wms wgs.
  Proof.
    iIntros "(Hfwc & Htwc & Hmwc & Hgwc)".
    iMod (import_func_wasm_check_alloc with "Hfwc"); iFrame.
    iMod (import_tab_wasm_check_alloc with "Htwc"); iFrame.
    iMod (import_mem_wasm_check_alloc with "Hmwc"); iFrame.
    iMod (import_glob_wasm_check_alloc with "Hgwc"); iFrame.
    by [].
  Qed.

  (* Note that the premise is not an iff, so we can only prove one side of the 
     inequality. However, we'll be able to prove the eventual lemma by combining
     them with an auxiliary lemma. *)
  Lemma import_func_wasm_check_lengths v_imps t_imps wfs:
    import_func_wasm_check v_imps t_imps wfs -∗
    ⌜length (ext_func_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) <= length (ext_t_funcs t_imps) ⌝.
  Proof.
    unfold ext_func_addrs.
    rewrite map_length.
    iIntros "(_ & %Ht & _)".
    iPureIntro.
    move: Ht.
    move: t_imps.
    induction v_imps; unfold func_typecheck; intros; destruct t_imps; try by apply Forall2_length in Ht.
    inversion Ht; subst; clear Ht.
    specialize (IHv_imps t_imps H4).
    simpl.
    destruct a, modexp_desc; simpl in *; [destruct f|destruct t|destruct m|destruct g]; try by (destruct e; lias) => //=.
    destruct H2 as (?&?&->) => /=.
    by lias.
  Qed.

  Lemma import_tab_wasm_check_lengths v_imps t_imps wfs:
    import_tab_wasm_check v_imps t_imps wfs -∗
    ⌜length (ext_tab_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) <= length (ext_t_tabs t_imps) ⌝.
  Proof.
    unfold ext_tab_addrs.
    rewrite map_length.
    iIntros "(_ & %Ht & _)".
    iPureIntro.
    move: Ht.
    move: t_imps.
    induction v_imps; unfold tab_typecheck; intros; destruct t_imps; try by apply Forall2_length in Ht.
    inversion Ht; subst; clear Ht.
    specialize (IHv_imps t_imps H4).
    simpl.
    destruct a, modexp_desc; simpl in *; [destruct f|destruct t|destruct m|destruct g]; try by (destruct e; lias) => //=.
    destruct H2 as (?&?&?&->&?) => /=.
    by lias.
  Qed.
  
  Lemma import_mem_wasm_check_lengths v_imps t_imps wfs:
    import_mem_wasm_check v_imps t_imps wfs -∗
    ⌜length (ext_mem_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) <= length (ext_t_mems t_imps) ⌝.
  Proof.
    unfold ext_mem_addrs.
    rewrite map_length.
    iIntros "(_ & %Ht & _)".
    iPureIntro.
    move: Ht.
    move: t_imps.
    induction v_imps; unfold mem_typecheck; intros; destruct t_imps; try by apply Forall2_length in Ht.
    inversion Ht; subst; clear Ht.
    specialize (IHv_imps t_imps H4).
    simpl.
    destruct a, modexp_desc; simpl in *; [destruct f|destruct t|destruct m|destruct g]; try by (destruct e; lias) => //=.
    destruct H2 as (?&?&?&->&?) => /=.
    by lias.
  Qed.
  
  Lemma import_glob_wasm_check_lengths v_imps t_imps wfs:
    import_glob_wasm_check v_imps t_imps wfs -∗
    ⌜length (ext_glob_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) <= length (ext_t_globs t_imps) ⌝.
  Proof.
    unfold ext_glob_addrs.
    rewrite map_length.
    iIntros "(_ & %Ht & _)".
    iPureIntro.
    move: Ht.
    move: t_imps.
    induction v_imps; unfold glob_typecheck; intros; destruct t_imps; try by apply Forall2_length in Ht.
    inversion Ht; subst; clear Ht.
    specialize (IHv_imps t_imps H4).
    simpl.
    destruct a, modexp_desc; simpl in *; [destruct f|destruct t|destruct m|destruct g]; try by (destruct e; lias) => //=.
    destruct H2 as (?&?&?&->&?) => /=.
    by lias.
  Qed.

  Lemma v_length_split v_imps:
    length v_imps = length (ext_func_addrs v_imps) +
                    length (ext_tab_addrs v_imps) +
                    length (ext_mem_addrs v_imps) +
                    length (ext_glob_addrs v_imps).
  Proof.
    unfold ext_func_addrs, ext_tab_addrs, ext_mem_addrs, ext_glob_addrs in *.
    repeat rewrite map_length.
    induction v_imps => //=.
    destruct a; by lias => //=.
  Qed.
  
  Lemma t_length_split t_imps:
    length t_imps = length (ext_t_funcs t_imps) +
                    length (ext_t_tabs t_imps) +
                    length (ext_t_mems t_imps) +
                    length (ext_t_globs t_imps).
  Proof.
    induction t_imps => //=.
    destruct a; by lias => //=.
  Qed.

  Lemma irwt_vtlen v_imps t_imps wfs wts wms wgs:
    import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
    ⌜ length v_imps = length t_imps ⌝.
  Proof.
    iIntros "(Hfc & Htc & Hmc & Hgc)".
    iDestruct "Hfc" as "(_&%Hftc&_)".
    by apply Forall2_length in Hftc.
  Qed.

  (* We know that the bound is strict:
     ∑ x = ∑ y -> ∀ i, x_i <= y_i -> ∀ i, x_i = y_i.
  *)
  Lemma import_resources_wasm_typecheck_lengths v_imps t_imps wfs wts wms wgs :
    import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
    ⌜length (ext_func_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) = length (ext_t_funcs t_imps)
    ∧ length (ext_tab_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) = length (ext_t_tabs t_imps)
    ∧ length (ext_mem_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) = length (ext_t_mems t_imps)
    ∧ length (ext_glob_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) = length (ext_t_globs t_imps)⌝.
  Proof.
    iIntros "H".
    iDestruct (irwt_vtlen with "H") as "%Hvtlen".
    iDestruct "H" as "(Hfc & Htc & Hmc & Hgc)".
    iDestruct (import_func_wasm_check_lengths with "Hfc") as "%Hflen".
    iDestruct (import_tab_wasm_check_lengths with "Htc") as "%Htlen".
    iDestruct (import_mem_wasm_check_lengths with "Hmc") as "%Hmlen".
    iDestruct (import_glob_wasm_check_lengths with "Hgc") as "%Hglen".
    iPureIntro.
    remember ((map (fun e => modexp_desc e) v_imps)) as v_imps'.
    replace (length v_imps) with (length v_imps') in Hvtlen; last by subst; rewrite map_length.
    rewrite v_length_split t_length_split in Hvtlen.
    by lias.
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

  Lemma module_res_imports_disj v_imps t_imps wfs m inst :
    import_func_wasm_check v_imps t_imps wfs -∗ 
     module_inst_resources_func (mod_funcs m) inst (drop (get_import_func_count m) (inst_funcs inst)) -∗
     ⌜∀ i fa, (drop (get_import_func_count m) (inst_funcs inst)) !! i = Some fa -> wfs !! (N.of_nat fa) = None⌝.
  Proof.
    unfold import_func_wasm_check_invs.
    iIntros "H Hf".
    iDestruct "H" as "(Hr & (%Hi & %Hdom))".
    unfold import_func_nainv.
    unfold func_domcheck in Hdom.
    unfold func_typecheck in Hi.
    iIntros (i fa Hsome).
    iDestruct (big_sepL2_length with "Hf") as %Hlen.
    apply lookup_lt_Some in Hsome as Hlt. rewrite -Hlen in Hlt.
    apply lookup_lt_is_Some_2 in Hlt as [cl Hk'].
    iDestruct (big_sepL2_lookup with "Hf") as "H";eauto.
    destruct (wfs !! (N.of_nat fa)) eqn:Hnone;auto.
    iDestruct (big_sepM_lookup with "Hr") as "H'" => //.
    apply elem_of_dom_2 in Hnone.
    apply leibniz_equiv in Hdom.
    rewrite Hdom in Hnone.
    apply elem_of_list_to_set in Hnone.
    eapply elem_of_list_fmap_2 in Hnone as [fa' [Heqfa' Hnone]]. simplify_eq.
    apply ext_func_addrs_elem_of in Hnone as [nm Hnone].
    apply elem_of_list_lookup in Hnone as [k Hk].
    assert (length v_imps = length t_imps) as Hlen'; first by apply Forall2_length in Hi.
    apply lookup_lt_Some in Hk as Hlt'.
    rewrite Hlen' in Hlt'.
    apply lookup_lt_is_Some_2 in Hlt' as [? ?].
    rewrite -> Forall2_lookup in Hi.
    specialize (Hi k).
    rewrite Hk H in Hi.
    inversion Hi; subst; clear Hi.
    simpl in *.
    simpl. destruct H2 as [cl' [Hwfs ->]].
    iDestruct (mapsto_valid_2 with "H H'") as "[% ?]". done.
  Qed. 
    

  Definition module_inst_resources_tab_invs (mtabs : list tableinst) (inst_t : list tableaddr) : iProp Σ :=
    ([∗ list] i↦tab; addr ∈ mtabs; inst_t,
       N.of_nat addr ↪[wtsize]tab_size tab ∗ N.of_nat addr ↪[wtlimit]table_max_opt tab ∗
                ([∗ list] j↦tabelem ∈ table_data tab, na_inv logrel_nais (wtN (N.of_nat addr) (N.of_nat j)) (N.of_nat addr ↦[wt][N.of_nat j]tabelem))
    )%I.

  Lemma module_inst_resources_tab_invs_alloc E mtabs inst_t :
    module_inst_resources_tab mtabs inst_t ={E}=∗
    module_inst_resources_tab_invs mtabs inst_t.
  Proof.
    iIntros "Himps".
    iApply big_sepL2_fupd.
    iApply (big_sepL2_mono with "Himps");intros k exp expt Hlook1 Hlook2;simpl.
    iIntros "[Hlim [Hsize Hf]]". iFrame.
    iApply big_sepL_fupd.
    iApply (big_sepL_mono with "Hlim");intros k' x Hx;simpl. iIntros "H".
    iApply na_inv_alloc. iNext. iFrame.
  Qed.

  Definition module_inst_resources_mem_invs (mmems : list memory) (inst_m : list memaddr) : iProp Σ :=
    ([∗ list] mem;addr ∈ mmems;inst_m, N.of_nat addr ↪[wmlimit] mem_max_opt mem ∗
       na_inv logrel_nais (wmN (N.of_nat addr))
              (∃ (mem : memory),
                  ([∗ list] i ↦ b ∈ (mem.(mem_data).(ml_data)), (N.of_nat addr) ↦[wm][ (N.of_nat i) ] b) ∗
                                                                (N.of_nat addr) ↦[wmlength] mem_length mem)      
    )%I.

  Lemma module_inst_resources_mem_invs_alloc E mmems inst_m :
    module_inst_resources_mem mmems inst_m  ={E}=∗
    module_inst_resources_mem_invs mmems inst_m.
  Proof.
    iIntros "Himps".
    iApply big_sepL2_fupd.
    iApply (big_sepL2_mono with "Himps");intros k exp expt Hlook1 Hlook2;simpl.
    iIntros "[Hf [Hlen Hlim]]". destruct exp. simpl. iFrame "Hlim".
    iApply na_inv_alloc. iNext. iExists _. iFrame.
  Qed.

  Definition module_inst_resources_glob_invs (mglobs : list global) (inst_g : list globaladdr) (gts : seq.seq global_type) : iProp Σ :=
    ([∗ list] i ↦ g;addr ∈ mglobs; inst_g,
       ∃ τg, ⌜gts !! i = Some τg⌝ ∗
       na_inv logrel_nais (wgN (N.of_nat addr)) (∃ w, N.of_nat addr ↦[wg] Build_global (tg_mut τg) w ∗ interp_value (tg_t τg) w)
    )%I.

  Global Instance module_inst_resources_glob_invs_persistent mglobs inst_g gts : Persistent (module_inst_resources_glob_invs mglobs inst_g gts).
  Proof. apply big_sepL2_persistent;intros;apply _. Qed.

  Lemma module_inst_global_init_lookup mglob_base g_inits k x :
    module_inst_global_init mglob_base g_inits !! k = Some x ->
    (∃ v g, g_inits !! k = Some v ∧ mglob_base !! k = Some g ∧ x = (global_init_replace_single g v)) ∨ mglob_base !! k = Some x.
  Proof.
    intros Hlook.
    generalize dependent k. generalize dependent g_inits.
    induction mglob_base;[done|auto..].
    intros g_inits k Hlook. destruct k.
    { destruct g_inits; cbn in *; auto. left. simplify_eq. eauto. }
    { destruct g_inits;cbn in *;auto. }
  Qed.

  Lemma bitzero_interp_value tg_t :
    ⊢ interp_value (Σ:=Σ) tg_t (bitzero tg_t).
  Proof.
    destruct tg_t;simpl;eauto.
  Qed.
    
  (* The following lemma depends on the restriction that the module global inits only contains constants *)
  Lemma module_inst_resources_glob_invs_alloc E (glob_inits : list global) mglobs g_inits inst_g impts gts :
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
    (typeof <$> g_inits = (tg_t ∘ modglob_type) <$> mglobs) ->
    glob_inits = module_inst_global_init (module_inst_build_globals mglobs) g_inits ->

    module_inst_resources_glob glob_inits inst_g ={E}=∗
    module_inst_resources_glob_invs glob_inits inst_g gts.
  Proof.
    iIntros (c' Hginitsval Hinittyp Hglob_inits) "Himps".
    iApply big_sepL2_fupd.
    iApply (big_sepL2_mono with "Himps");intros k exp expt Hlook1 Hlook2;simpl.
    iIntros "Hf".
    simplify_eq.
    apply module_inst_global_init_lookup in Hlook1 as Hlook'.
    destruct Hlook' as [Hg_inits | Hglob].
    { destruct Hg_inits as [v [g [Hg_inits [Hmglobs Heq]]]].
      subst exp.
      apply list_lookup_fmap_inv in Hmglobs as Hmglobs'.
      destruct Hmglobs' as [m [Heqg Hmglobs']].
      destruct m,modglob_type;simpl in *. subst g.
      eapply Forall2_lookup_l in Hginitsval as [gt [Hgt Htyp]];eauto.
      rewrite /global_init_replace_single /=.
      iExists _. iSplitR;[eauto|].
      unfold module_glob_typing in Htyp.
      destruct Htyp as [Hconst [Heq Htyp]]. subst.
      simpl.
      iApply na_inv_alloc.
      iNext. iExists _. iFrame.
      assert ((typeof <$> g_inits) !! k = Some (typeof v)).
      { rewrite list_lookup_fmap. rewrite Hg_inits. eauto. }
      rewrite Hinittyp in H.
      rewrite (list_fmap_compose (modglob_type) (datatypes.tg_t) mglobs) in H.
      apply list_lookup_fmap_inv in H as [gt [Heq1 H]].
      rewrite list_lookup_fmap Hmglobs' /= in H. simplify_eq.
      simpl in Heq1. rewrite -Heq1.
      iApply interp_value_type_of. }
    { apply list_lookup_fmap_inv in Hglob as [g [Hgeq Hg]].
      destruct g,modglob_type;simpl in *.
      eapply Forall2_lookup_l in Hginitsval as [gt [Hgt Htyp]];eauto.
      iExists _. iSplitR;[eauto|].
      unfold module_glob_typing in Htyp. destruct exp;simpl in *.
      destruct Htyp as [Hconst [Heq Htyp]]. subst.
      simpl. inversion Hgeq;simplify_eq.      
      iApply na_inv_alloc.
      iNext. iExists _. iFrame.
      iApply bitzero_interp_value.
    }
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
    func_typecheck v_imps t_imps wfs ->
    tab_typecheck v_imps t_imps wts ->
    mem_typecheck v_imps t_imps wms ->
    glob_typecheck v_imps t_imps wgs ->
    exists k', t_imps !! k' = Some (ET_func ft) ∧ ∃ fm, v_imps !! k' = Some fm ∧ modexp_desc fm = MED_func (Mk_funcidx fa).
  Proof.
    rewrite map_fmap.
    move : k ft fa t_imps.
    induction v_imps; move => k ft fa t_imps Htl Hvl Hfc Htc Hmc Hgc; destruct t_imps; simpl in * => //.
    - inversion Hfc; subst; clear Hfc.
      inversion Htc; subst; clear Htc.
      inversion Hmc; subst; clear Hmc.
      inversion Hgc; subst; clear Hgc.
      destruct a, modexp_desc; simpl in *.
      { destruct f.
        destruct H2 as [cl [Hwfs ->]].
        destruct k; simpl in *.
        { exists 0.
          inversion Htl; subst; clear Htl.
          inversion Hvl; subst; clear Hvl.
          split => //.
          by eexists.
        }
        { specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
          destruct IHv_imps as [k' IH].
          by exists (S k').
        }
      }
      { destruct t.
        destruct H3 as [tab [tt [Hwts [-> Htt]]]].
        simpl in Hvl.
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
      { destruct m.
        destruct H5 as [mem [mt [Hwms [-> Hmt]]]].
        simpl in Hvl.
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
      { destruct g.
        destruct H7 as [g [gt [Hwgs [-> Hgt]]]].
        simpl in Hvl.
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
  Qed.

  Lemma import_tabs_lookup t_imps v_imps k ft fa wfs wts wms wgs:
    ext_t_tabs t_imps !! k = Some ft ->
    ext_tab_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps) !! k = Some fa ->
    func_typecheck v_imps t_imps wfs ->
    tab_typecheck v_imps t_imps wts ->
    mem_typecheck v_imps t_imps wms ->
    glob_typecheck v_imps t_imps wgs ->
    exists k', t_imps !! k' = Some (ET_tab ft) ∧ ∃ fm, v_imps !! k' = Some fm ∧ modexp_desc fm = MED_table (Mk_tableidx fa).
  Proof.
    rewrite map_fmap.
    move : k ft fa t_imps.
    induction v_imps; move => k ft fa t_imps Htl Hvl Hfc Htc Hmc Hgc; destruct t_imps; simpl in * => //.
    - inversion Hfc; subst; clear Hfc.
      inversion Htc; subst; clear Htc.
      inversion Hmc; subst; clear Hmc.
      inversion Hgc; subst; clear Hgc.
      destruct a, modexp_desc; simpl in *.
      { destruct f.
        destruct H2 as [cl [Hwfs ->]].
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
      { destruct t.
        destruct H3 as [tab [tt [Hwts [-> Htt]]]].
        destruct k; simpl in *.
        { exists 0.
          inversion Htl; subst; clear Htl.
          inversion Hvl; subst; clear Hvl.
          split => //.
          by eexists.
        }
        simpl in Hvl.
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
      { destruct m.
        destruct H5 as [mem [mt [Hwms [-> Hmt]]]].
        simpl in Hvl.
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
      { destruct g.
        destruct H7 as [g [gt [Hwgs [-> Hgt]]]].
        simpl in Hvl.
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
  Qed.

  Lemma import_mems_lookup t_imps v_imps k ft fa wfs wts wms wgs:
    ext_t_mems t_imps !! k = Some ft ->
    ext_mem_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps) !! k = Some fa ->
    func_typecheck v_imps t_imps wfs ->
    tab_typecheck v_imps t_imps wts ->
    mem_typecheck v_imps t_imps wms ->
    glob_typecheck v_imps t_imps wgs ->
    exists k', t_imps !! k' = Some (ET_mem ft) ∧ ∃ fm, v_imps !! k' = Some fm ∧ modexp_desc fm = MED_mem (Mk_memidx fa).
  Proof.
    rewrite map_fmap.
    move : k ft fa t_imps.
    induction v_imps; move => k ft fa t_imps Htl Hvl Hfc Htc Hmc Hgc; destruct t_imps; simpl in * => //.
    - inversion Hfc; subst; clear Hfc.
      inversion Htc; subst; clear Htc.
      inversion Hmc; subst; clear Hmc.
      inversion Hgc; subst; clear Hgc.
      destruct a, modexp_desc; simpl in *.
      { destruct f.
        destruct H2 as [cl [Hwfs ->]].
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
      { destruct t.
        destruct H3 as [tab [tt [Hwts [-> Htt]]]].
        unfold ext_func_addrs in Hvl.
        simpl in Hvl.
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
      { destruct m.
        destruct H5 as [mem [mt [Hwms [-> Hmt]]]].
        destruct k; simpl in *.
        { exists 0.
          inversion Htl; subst; clear Htl.
          inversion Hvl; subst; clear Hvl.
          split => //.
          by eexists.
        }
        simpl in Hvl.
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
      { destruct g.
        destruct H7 as [g [gt [Hwgs [-> Hgt]]]].
        unfold ext_func_addrs in Hvl.
        simpl in Hvl.
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
 Qed.

  Lemma import_globs_lookup t_imps v_imps k ft fa wfs wts wms wgs:
    ext_t_globs t_imps !! k = Some ft ->
    ext_glob_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps) !! k = Some fa ->
    func_typecheck v_imps t_imps wfs ->
    tab_typecheck v_imps t_imps wts ->
    mem_typecheck v_imps t_imps wms ->
    glob_typecheck v_imps t_imps wgs ->
    exists k', t_imps !! k' = Some (ET_glob ft) ∧ ∃ fm, v_imps !! k' = Some fm ∧ modexp_desc fm = MED_global (Mk_globalidx fa).
  Proof.
    rewrite map_fmap.
    move : k ft fa t_imps.
    induction v_imps; move => k ft fa t_imps Htl Hvl Hfc Htc Hmc Hgc; destruct t_imps; simpl in * => //.
    - inversion Hfc; subst; clear Hfc.
      inversion Htc; subst; clear Htc.
      inversion Hmc; subst; clear Hmc.
      inversion Hgc; subst; clear Hgc.
      destruct a, modexp_desc; simpl in *.
      { destruct f.
        destruct H2 as [cl [Hwfs ->]].
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
      { destruct t.
        destruct H3 as [tab [tt [Hwts [-> Htt]]]].
        simpl in Hvl.
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
      { destruct m.
        destruct H5 as [mem [mt [Hwms [-> Hmt]]]].
        simpl in Hvl.
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
      { destruct g.
        destruct H7 as [g [gt [Hwgs [-> Hgt]]]].
        destruct k; simpl in *.
        { exists 0.
          inversion Htl; subst; clear Htl.
          inversion Hvl; subst; clear Hvl.
          split => //.
          by eexists.
        }
        simpl in Hvl.
        specialize (IHv_imps k ft fa t_imps Htl Hvl H4 H6 H8 H10).
        destruct IHv_imps as [k' IH].
        by exists (S k').
      }
  Qed.

  Lemma repeat_imap_eq {A B C : Type} (a : A) (b : B) (f : nat -> C) (m : nat) :
    imap (λ i _, f i) (repeat a m) = imap (λ i _, f i) (repeat b m).
  Proof.
    generalize dependent f.
    induction m => //=; move => f.
    f_equal.
    assert ((λ (i : nat) (_ : A), f i) ∘ S =
              (λ (i : nat) (_ : A), f (S i))) as ->;auto.
    assert ((λ (i : nat) (_ : B), f i) ∘ S =
              (λ (i : nat) (_ : B), f (S i))) as ->;auto.
  Qed.

  Lemma repeat_imap_lookup {A B : Type} (a a' : A) (f : nat -> B) (m k : nat) :
    (repeat a m) !! k = Some a' ->
    (imap (λ i _, f i) (repeat a m)) !! k = Some (f k).
  Proof.
    move => Hlookup; apply repeat_lookup_Some in Hlookup as [-> Hlen].
    rewrite list_lookup_imap => /=.
    apply (repeat_lookup a) in Hlen.
    by rewrite Hlen.
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
              tc_memory := List.app ims ms;
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

  Lemma fold_left_preserve_index {A B: Type} (P: A -> Prop) (f: A -> B -> A) (l: list B) (acc: A) :
    P acc ->
    (forall (x:A) (act: B), P x -> (∃ i, l !! i = Some act) -> P (f x act)) ->
    P (fold_left f l acc).
  Proof.
    rewrite -fold_left_rev_right.
    revert acc.
    induction l;simpl;auto.
    intros acc Ha Hnext.
    rewrite foldr_snoc /=. apply IHl =>//.
    apply Hnext=>//. exists 0. auto.
    intros. apply Hnext=>//. destruct H0 as [? ?]. exists (S x0). auto.
  Qed.

  Lemma fold_left_preserve_filter {A B C : Type} (F : B -> Prop) (H : ∀ x, Decision (F x))
        (P: A -> C -> Prop) (f: A -> B -> A) (f' : C -> B -> C) (l: list B) (acc: A) (acc': C) :
    P acc acc' ->
    (forall (x:A) (y:C) (act:B), F act -> P x y -> P (f x act) (f' y act)) ->
    (forall (x:A) (y:C) (act:B), ¬ F act -> P x y -> P (f x act) y) ->
    P (fold_left f l acc) (fold_left f' (filter F l) acc').
  Proof.
    repeat rewrite -fold_left_rev_right.
    revert acc acc'.
    induction l;simpl;auto.
    intros acc acc' Ha Hnext Hskip.
    destruct (decide (F a)).
    { rewrite filter_cons_True// /=.
      rewrite !foldr_snoc /=.
      apply IHl =>//. apply Hnext=>//. }
    { rewrite filter_cons_False// /=.
      rewrite foldr_snoc /=.
      apply IHl =>//. apply Hskip=>//. }
  Qed.

  Lemma fold_left_preserve_filter_index {A B C : Type} (F : B -> Prop) (H : ∀ x, Decision (F x))
        (P: A -> C -> Prop) (f: A -> B -> A) (f' : C -> B -> C) (l: list B) (acc: A) (acc': C) :
    P acc acc' ->
    (forall (x:A) (y:C) (act:B), F act -> (∃ i, l !! i = Some act) -> P x y -> P (f x act) (f' y act)) ->
    (forall (x:A) (y:C) (act:B), ¬ F act -> (∃ i, l !! i = Some act) -> P x y -> P (f x act) y) ->
    P (fold_left f l acc) (fold_left f' (filter F l) acc').
  Proof.
    repeat rewrite -fold_left_rev_right.
    revert acc acc'.
    induction l;simpl;auto.
    intros acc acc' Ha Hnext Hskip.
    destruct (decide (F a)).
    { rewrite filter_cons_True// /=.
      rewrite !foldr_snoc /=.
      apply IHl =>//. apply Hnext=>//. exists 0;auto.
      intros. apply Hnext;auto. destruct H1 as [? ?]. exists (S x0);auto.
      intros. apply Hskip;auto. destruct H1 as [? ?]. exists (S x0);auto. }
    { rewrite filter_cons_False// /=.
      rewrite foldr_snoc /=.
      apply IHl =>//. apply Hskip=>//. exists 0;auto.
      intros. apply Hnext;auto. destruct H1 as [? ?]. exists (S x0);auto.
      intros. apply Hskip;auto. destruct H1 as [? ?]. exists (S x0);auto. }
  Qed.

  Lemma fold_left_preserve_filter_twice {A B C : Type} (F : B -> Prop) (H : ∀ x, Decision (F x))
        (P: A -> C -> Prop) (f: A -> B -> A) (f' : C -> B -> C) (l: list B) (acc: A) (acc': C) :
    (P acc acc') ->
    (forall (x:A) (y:C) (act:B), F act -> (P x y) -> P (f x act) (f' y act)) ->
    (forall (x:A) (y:C) (act:B), ¬ F act -> (P x y) -> P (f x act) y) ->
    P (fold_left f l acc) (fold_left f' (filter F l) acc').
  Proof.
    repeat rewrite -fold_left_rev_right.
    revert acc acc'.
    induction l;simpl;auto.
    intros acc acc' Ha Hnext Hskip.
    destruct (decide (F a)).
    { rewrite filter_cons_True// /=.
      rewrite !foldr_snoc /=.
      eapply IHl =>//. eapply Hnext=>//. }
    { rewrite filter_cons_False// /=.
      rewrite foldr_snoc /=.
      apply IHl =>//. apply Hskip => //. }
  Qed.

  Lemma fold_left_preserve_twice {A B C : Type}
        (P: A -> C -> Prop) (f: A -> B -> A) (f' : C -> B -> C) (l: list B) (acc: A) (acc': C) :
    (P acc acc') ->
    (forall (x:A) (y:C) (act:B), (P x y) -> P (f x act) (f' y act)) ->
    P (fold_left f l acc) (fold_left f' l acc').
  Proof.
    repeat rewrite -fold_left_rev_right.
    revert acc acc'.
    induction l;simpl;auto.
    intros acc acc' Ha Hnext.
    rewrite !foldr_snoc /=.
    eapply IHl =>//. eapply Hnext=>//.
  Qed.

  Lemma fold_left_preserve_twice_index {A B C : Type}
        (P: A -> C -> Prop) (f: A -> B -> A) (f' : C -> B -> C) (l: list B) (acc: A) (acc': C) :
    (P acc acc') ->
    (forall (x:A) (y:C) (act:B), (∃ i, l !! i = Some act) -> (P x y) -> P (f x act) (f' y act)) ->
    P (fold_left f l acc) (fold_left f' l acc').
  Proof.
    repeat rewrite -fold_left_rev_right.
    revert acc acc'.
    induction l;simpl;auto.
    intros acc acc' Ha Hnext.
    rewrite !foldr_snoc /=.
    eapply IHl =>//. eapply Hnext=>//. exists 0;eauto.
    intros. apply Hnext;auto. destruct H as [? ?]. exists (S x0);auto.
  Qed.
  
  Lemma fold_left_preserve_filter_impl {A B C : Type} (F : B -> Prop) (H : ∀ x, Decision (F x))
        (P: A -> Prop) (Q : C -> Prop) (f: A -> B -> A) (f' : C -> B -> C) (l: list B) (acc: A) (acc': C) :
    (P acc -> Q acc') ->
    (forall (x:A) (y:C) (act:B), F act -> (P x -> Q y) -> P (f x act) -> Q (f' y act)) ->
    (forall (x:A) (y:C) (act:B), ¬ F act -> (P x -> Q y) ->P (f x act) -> Q y) ->
    P (fold_left f l acc) -> Q (fold_left f' (filter F l) acc').
  Proof.
    repeat rewrite -fold_left_rev_right.
    revert acc acc'.
    induction l;simpl;auto.
    intros acc acc' Ha Hnext Hskip HP.
    destruct (decide (F a)).
    { rewrite filter_cons_True// /=.
      rewrite !foldr_snoc /=.
      rewrite foldr_snoc in HP.
      eapply IHl =>//. intros. eapply Hnext=>//. }
    { rewrite filter_cons_False// /=.
      rewrite foldr_snoc /= in HP.
      apply IHl with (f acc a);auto.
      eapply Hskip => //. }
  Qed.
  
  Definition module_inst_resources_wasm_invs (m : module) (inst : instance) (gts : seq.seq global_type) t_inits m_inits g_inits :=
    (module_inst_resources_func_invs (mod_funcs m) inst
     (drop (get_import_func_count m) (inst_funcs inst)) ∗
    module_inst_resources_tab_invs t_inits
     (drop (get_import_table_count m) (inst_tab inst)) ∗
    module_inst_resources_mem_invs m_inits
     (drop (get_import_mem_count m) (inst_memory inst))∗
    module_inst_resources_glob_invs g_inits
    (drop (get_import_global_count m) (inst_globs inst)) gts)%I.

  Global Instance modelem_filter_dec n : ∀ x : module_element,
     Decision
       ((λ me : module_element,
           match modelem_table me with
           | Mk_tableidx m => n = m
           end) x).
  Proof. intros x. destruct x,modelem_table. simpl. apply _. Qed.  
  Definition module_element_filter_relevant_idx (e : seq.seq module_element) (n : nat) :=
    filter (λ me, match (modelem_table me) with
                  | Mk_tableidx m => n = m
                  end) e.

  Definition module_inst_build_table_filter (m : module) (inst: instance) (n : nat) (mt : module_table) : tableinst :=
  fold_left (fun t '{| modelem_table := mt; modelem_offset := moff; modelem_init := me_init |} =>
               let itc := get_import_table_count m in 
               match mt with
               | Mk_tableidx k =>
                   if k <? itc then t else
                       table_init_replace_single t (assert_const1_i32_to_nat moff) (lookup_funcaddr inst me_init)
               end
            ) (module_element_filter_relevant_idx (mod_elem m) n) (module_inst_table_base_create mt).
  (* using filters is an nice definition, but makes the proofs very bad because the types of the two fold_lefts do not match.... *)
  Definition module_inst_build_table (m : module) (inst: instance) (n : nat) (mt : module_table) : tableinst :=
  fold_left (fun t '{| modelem_table := mt; modelem_offset := moff; modelem_init := me_init |} =>
               let itc := get_import_table_count m in 
               match mt with
               | Mk_tableidx k =>
                   if k <? itc then t else
                     if decide (k = n) then 
                       table_init_replace_single t (assert_const1_i32_to_nat moff) (lookup_funcaddr inst me_init)
                     else t
               end
            ) (mod_elem m) (module_inst_table_base_create mt).

  Lemma module_inst_build_table_filter_eq m inst n mt :
    module_inst_build_table_filter m inst n mt = module_inst_build_table m inst n mt.
  Proof.
    unfold module_inst_build_table_filter,
      module_inst_build_table,
      module_element_filter_relevant_idx.
    apply fold_left_preserve_filter;auto.
    { intros x y act. destruct act, modelem_table;simpl.
      intros Heq1 Heq2. simplify_eq. rewrite decide_True//. }
    { intros x y act. destruct act, modelem_table;simpl.
      intros Heq1 Heq2. simplify_eq. rewrite decide_False//. edestruct (n0 <? _);auto. }
  Qed.

  
  Definition module_inst_build_table_map (m : module) (inst : instance) : seq.seq tableinst :=
    imap (λ j mt, module_inst_build_table m inst (j + get_import_table_count m) mt) (mod_tables m).
  Lemma imap_id {A : Type} acc :
    (imap (λ (_ : nat) (a : A), a) acc) = acc.
  Proof. induction acc;auto. simpl. rewrite IHacc. auto. Qed.

  Lemma module_inst_build_tables_lookup m i j a x :
    (mod_tables m) !! j = Some a ->
    module_inst_build_tables m i !! j = Some x ->
    x = module_inst_build_table m i (j + get_import_table_count m) a.
  Proof.
    unfold module_inst_build_tables, module_inst_build_table.
    revert x.
    apply fold_left_preserve_twice with (acc':=(module_inst_table_base_create a)).
    { intros x Ha Hx.
      apply list_lookup_fmap_inv in Hx.
      destruct Hx as [k [Heq Hlook]].
      simplify_eq. auto. }
    { intros tl t me Hme x Ha.
      destruct me,modelem_table.
      destruct (n <? get_import_table_count m) eqn:Hn.
      { eauto. }
      apply PeanoNat.Nat.ltb_ge in Hn.
      destruct (nth_error tl (n - get_import_table_count m)) eqn:Hnth;cycle 1.
      { intros Htl.
        eapply Hme in Ha as Heq;eauto.
        apply lookup_lt_Some in Htl as Hlt.
        rewrite nth_error_lookup in Hnth.
        apply lookup_ge_None in Hnth as Hge.
        destruct (decide (n = j + get_import_table_count m));eauto.
        lia. }
      { rewrite nth_error_lookup in Hnth.
        destruct (decide (n = j + get_import_table_count m)).
        { assert (n - get_import_table_count m = j) as Heqj;[lia|].
          subst j.
          eapply Hme in Ha as Heq;eauto.
          apply lookup_lt_Some in Hnth as Hlt'.
          rewrite list_lookup_insert//. intros Heq'.
          simplify_eq. auto. }
        { rewrite list_lookup_insert_ne//. apply Hme;auto. lia. }
      }
    }
  Qed.

  Lemma module_inst_build_tables_lookup_None m i j :
    (mod_tables m) !! j = None ->
    module_inst_build_tables m i !! j = None.
  Proof.
    pose proof (module_inst_build_tables_length m i).
    intros Hmod.
    apply lookup_ge_None in Hmod.
    rewrite -H in Hmod.
    by apply lookup_ge_None in Hmod.
  Qed.

  Lemma module_inst_build_tables_lookup_is_Some m i j a :
    (mod_tables m) !! j = Some a ->
    is_Some (module_inst_build_tables m i !! j).
  Proof.
    pose proof (module_inst_build_tables_length m i).
    intros Hmod.
    apply lookup_lt_Some in Hmod.
    rewrite -H in Hmod.
    by apply lookup_lt_is_Some in Hmod.
  Qed.

  Lemma module_inst_build_table_map_lookup m inst i m0 :
    (mod_tables m) !! i = Some m0 ->
    module_inst_build_table_map m inst !! i =
      Some (module_inst_build_table m inst (i + get_import_table_count m) m0).
  Proof.
    intros Hm.
    unfold module_inst_build_table_map.
    by rewrite list_lookup_imap Hm /=.
  Qed.

  Lemma module_inst_build_table_map_lookup_None m inst i :
    (mod_tables m) !! i = None ->
    module_inst_build_table_map m inst !! i = None.
  Proof.
    intros Hm.
    unfold module_inst_build_table_map.
    by rewrite list_lookup_imap Hm /=.
  Qed.
    
  Lemma module_inst_build_table_map_eq m inst :
    module_inst_build_table_map m inst = module_inst_build_tables m inst.
  Proof.
    apply list_eq.
    intros i.
    destruct ((mod_tables m) !! i) eqn:Hsome.
    { apply module_inst_build_tables_lookup_is_Some with (i:=inst) in Hsome as Hx.
      destruct Hx as [x Hx].
      eapply module_inst_build_tables_lookup in Hx as Heq;eauto.
      rewrite Hx Heq. by apply module_inst_build_table_map_lookup. }
    { apply module_inst_build_tables_lookup_None with (i:=inst) in Hsome as Hx.
      eapply module_inst_build_table_map_lookup_None with (inst:=inst) in Hsome as Hy.
      by rewrite Hx Hy. }
  Qed.

  Lemma module_inst_built_table_max_opt_eq m i n m0 :
    table_max_opt (module_inst_build_table m i n m0) = lim_max (tt_limits (modtab_type m0)).
  Proof.
    unfold module_inst_build_table.
    apply fold_left_preserve.
    { destruct m0,  modtab_type, tt_limits.
      by rewrite /module_inst_table_base_create /=. }
    { intros tt me Heq.
      destruct me,modelem_table.
      destruct (n0 <? get_import_table_count m);auto.
      destruct (decide (n0 = n));auto. }
  Qed.

  Lemma module_inst_build_table_length m i n m0 :
    length (table_data (module_inst_build_table m i n m0)) = N.to_nat (lim_min (tt_limits (modtab_type m0))).
  Proof.
    unfold module_inst_build_table.
    apply fold_left_preserve.
    { destruct m0,  modtab_type, tt_limits.
      rewrite /module_inst_table_base_create /=.
      by rewrite repeat_length.
    }
    { intros tt me Heq.
      destruct me,modelem_table.
      destruct (n0 <? get_import_table_count m);auto.
      destruct (decide (n0 = n));auto.
      erewrite <-table_init_replace_single_preserve_len;eauto.
    }
  Qed.

  Lemma module_inst_build_table_lt_is_Some m i n m0 j :
    j < N.to_nat (lim_min (tt_limits (modtab_type m0))) ->
    is_Some (table_data (module_inst_build_table m i n m0) !! j).
  Proof.
    intros Hlt.
    rewrite <-module_inst_build_table_length with (m:=m) (i:=i) (n:=n) in Hlt. 
    by apply lookup_lt_is_Some in Hlt.
  Qed.

  Lemma repeat_lookup_eq :
    ∀ (T : Type) (x y : T) (n i : nat), repeat x n !! i = Some y -> x = y.
  Proof.
    intros T x y n i Hx.
    apply lookup_lt_Some in Hx as Hlt.
    eapply repeat_lookup in Hlt.
    rewrite repeat_length in Hlt.
    erewrite Hx in Hlt;simplify_eq. auto.
  Qed.  
  
  Lemma module_inst_build_table_lookup_Some m i n m0 j x :
    table_data (module_inst_build_table m i n m0) !! j = Some x ->
    x = None ∨ (∃ k moff minit idx f, (inst_funcs i) !! idx = Some f ∧ x = Some f ∧ mod_elem m !! k = Some (Build_module_element (Mk_tableidx n) moff minit)
                                ∧ n <? (get_import_table_count m) = false
                                ∧ ∃ ei, minit !! ei = Some (Mk_funcidx idx)).
  Proof.
    unfold module_inst_build_table.
    revert j x.
    apply fold_left_preserve_index;intros j x.
    { intros Hx.
      unfold module_inst_table_base_create in Hx.
      destruct m0,modtab_type,tt_limits. simpl in Hx.
      apply repeat_lookup_eq in Hx as Heq. subst x. auto. }
    { intros Hlook [id Helem].
      destruct x,modelem_table;simpl.
      destruct (n0 <? get_import_table_count m) eqn:Hlt;auto.
      destruct (decide (n0 = n));auto. subst.
      intros j0 x Hx.
      unfold table_init_replace_single in Hx.
      simpl in Hx.
      apply lookup_lt_Some in Hx as Hlt'.
      rewrite take_length in Hlt'.
      rewrite lookup_take in Hx;[|lia].
      apply lookup_app_Some in Hx as [Hx | Hx].
      { apply lookup_take_Some in Hx as [Hx Hlt2].
        apply Hlook in Hx;auto. }
      destruct Hx as [Hle Hx].
      apply lookup_app_Some in Hx as [Hx | Hx].
      { apply list_lookup_fmap_inv in Hx.
        destruct Hx as [idx [Heq Hx]].
        destruct idx. subst x.
        destruct ((inst_funcs i) !! n0) eqn:Hnth; last by left.
        right. exists id,modelem_offset,modelem_init,n0,n1.
        repeat split;auto. eauto. }
      destruct Hx as [Hle' Hx].
      rewrite lookup_drop in Hx.
      apply Hlook in Hx;auto.
    }
  Qed.

  Definition module_import_init_tab (m: module) (inst: instance) (n : nat) (mt: tableinst) : tableinst :=
  fold_left (fun t '{| modelem_table := mt; modelem_offset := moff; modelem_init := me_init |} =>
               let itc := get_import_table_count m in 
               match mt with
               | Mk_tableidx k =>
                 if k <? itc then
                   match nth_error inst.(inst_tab) k with
                   | Some t_addr =>
                       if decide (t_addr = n) then
                         table_init_replace_single t (assert_const1_i32_to_nat moff) (lookup_funcaddr inst me_init) else t
                   | None => t
                   end
                 else t
               end
            ) m.(mod_elem) mt.

  Lemma module_import_init_tabs_lookup m i wts n tab tab' :
    wts !! n = Some tab ->
    module_import_init_tabs m i wts !! n = Some tab' ->
    tab' = module_import_init_tab m i (N.to_nat n) tab.
  Proof.
    unfold module_import_init_tabs,module_import_init_tab.
    revert tab'.
    apply fold_left_preserve_twice with (acc':=tab).
    { intros tab' Htab Htab'. simplify_eq. auto. }
    { intros tt tt' me IH tab' Htab Htab'.
      destruct me,modelem_table.
      destruct (n0 <? get_import_table_count m) eqn:Hlt;auto.
      destruct (nth_error (inst_tab i) n0) eqn:Hnth;auto.
      rewrite nth_error_lookup in Hnth.
      destruct (tt !! N.of_nat t) eqn:Hsome;cycle 1.
      { destruct (decide (t = N.to_nat n));auto.
        simplify_eq. rewrite N2Nat.id in Hsome.
        simplify_eq. }
      destruct (decide (t = N.to_nat n));cycle 1.
      { rewrite lookup_insert_ne// in Htab';[|lia]. eauto. }
      { simplify_eq. rewrite N2Nat.id in Htab'.
        rewrite lookup_insert in Htab'.
        rewrite N2Nat.id in Hsome.
        eapply IH in Htab as Hsome';eauto. subst. simplify_eq. auto. }
    }
  Qed.

  Lemma module_import_init_tab_lookup_length m i n tab :
    length (table_data (module_import_init_tab m i n tab)) = length (table_data tab).
  Proof.
    unfold module_import_init_tab.
    apply fold_left_preserve;auto.
    intros x tt Hlen.
    destruct tt,modelem_table.
    destruct (n0 <? get_import_table_count m);auto.
    destruct (nth_error (inst_tab i) n0);auto.
    destruct (decide (t = n));auto.
    erewrite <- table_init_replace_single_preserve_len;eauto.
  Qed.
  
  Lemma module_import_init_tabs_is_Some m i wts n :
    is_Some (wts !! n) <->
    is_Some (module_import_init_tabs m i wts !! n).
  Proof.
    unfold module_import_init_tabs.
    apply fold_left_preserve.
    { eauto. }
    { intros x act Hiff.
      destruct act,modelem_table.
      destruct (n0 <? get_import_table_count m);auto.
      destruct (nth_error (inst_tab i) n0);auto.
      destruct (x !! N.of_nat t) eqn:Hsome;auto.
      destruct (decide (N.of_nat t = n)).
      { subst. rewrite lookup_insert. split; auto.
        intros [yy Hsome']. simplify_eq. apply Hiff. eauto.
      }
      { rewrite lookup_insert_ne;auto. }
    }
  Qed.

  Lemma module_import_init_tabs_Some m i wts n x :
    module_import_init_tabs m i wts !! n = Some x ->
    is_Some (wts !! n).
  Proof.
    intros Hsome.
    rewrite module_import_init_tabs_is_Some. eauto.
  Qed.
    
  Lemma module_import_init_tab_lookup_Some m i n tab j x :
    table_data (module_import_init_tab m i n tab) !! j = Some x ->
    table_data tab !! j = Some x ∨
      (∃ k moff minit idx n1, (inst_tab i) !! idx = Some n
                              ∧ x = (inst_funcs i) !! n1
                              ∧ mod_elem m !! k = Some (Build_module_element (Mk_tableidx idx) moff minit)
                              ∧ idx <? (get_import_table_count m) = true
                              ∧ ∃ ei, minit !! ei = Some (Mk_funcidx n1)).
  Proof.
    unfold module_import_init_tab.
    revert j.
    apply fold_left_preserve_index.
    { intros j Htab. auto. }
    { intros tt me IH [i' Hi'] j.
      destruct me,modelem_table;simpl.
      destruct (n0 <? get_import_table_count m) eqn:Hlt;auto.
      destruct (nth_error (inst_tab i) n0) eqn:Hnth;auto.
      rewrite nth_error_lookup in Hnth.
      destruct (decide (t = n));auto.
      { simplify_eq. intros Hx.
        
        pose proof (table_init_replace_single_preserve_len tt
                        (assert_const1_i32_to_nat modelem_offset)
                        (lookup_funcaddr i modelem_init)) as Hleneq.
        unfold table_init_replace_single in Hx.
        simpl in Hx.
        apply lookup_lt_Some in Hx as Hlt'.
        rewrite take_length in Hlt'.
        rewrite lookup_take in Hx;[|lia].
        apply lookup_app_Some in Hx as [Hx | Hx].
        { apply lookup_take_Some in Hx as [Hx Hlt2].
          apply IH. auto. }
        destruct Hx as [Hle Hx].
        apply lookup_app_Some in Hx as [Hx | Hx].
        { apply list_lookup_fmap_inv in Hx.
          destruct Hx as [idx [Heq Hx]].
          destruct idx. subst x.
          right. exists i',modelem_offset,modelem_init,n0,n1.
          repeat split;eauto.
        }
        destruct Hx as [Hle' Hx].
        rewrite lookup_drop in Hx.
        destruct (decide (assert_const1_i32_to_nat modelem_offset < length (table_data tt)));cycle 1.
        { apply not_lt in n1.
          assert (assert_const1_i32_to_nat modelem_offset `min` length (table_data tt) =
                    length (table_data tt)) as Heq'';[lia|].
          revert Hx Hle' Hle Hlt'. rewrite !app_length !drop_length !take_length !Heq''.
          clear. intros. exfalso. lia. }
        assert (assert_const1_i32_to_nat modelem_offset +
           length (lookup_funcaddr i modelem_init) +
           (j -
            length
              (take (assert_const1_i32_to_nat modelem_offset) (table_data tt)) -
              length (lookup_funcaddr i modelem_init)) = j) as Heqj.
        { rewrite take_length.          
        assert (assert_const1_i32_to_nat modelem_offset `min` length (table_data tt) =
                  assert_const1_i32_to_nat modelem_offset) as Heq'';[lia|].
        rewrite Heq''. rewrite -PeanoNat.Nat.sub_add_distr. apply le_plus_minus_r.
        rewrite take_length in Hle'. rewrite take_length in Hle.
        rewrite Heq'' in Hle'. rewrite Heq'' in Hle.
          clear -Hle Hle'. revert Hle Hle'.
          unfold funcaddr,immediate,funcelem. lia.
        }
        apply IH. rewrite -Heqj. auto. }
    }
  Qed.

  Lemma module_import_init_tab_table_max_opt_eq m i n x :
    table_max_opt (module_import_init_tab m i n x) = table_max_opt x.
  Proof.
    unfold module_import_init_tab.
    apply fold_left_preserve;auto.
    intros tt me. destruct me,modelem_table.
    destruct (n0 <? get_import_table_count m);auto.
    destruct (nth_error (inst_tab i) n0);auto.
    destruct (decide (t = n));auto.
  Qed.

  Lemma module_inst_build_mems_length m i :
    length (module_inst_build_mems m i) = length (mod_mems m).
  Proof.
    unfold module_inst_build_mems.
    apply fold_left_preserve.
    { rewrite fmap_length. auto. }
    { intros mm md Hlen. destruct md,moddata_data.
      destruct (n <? get_import_mem_count m);auto.
      destruct (nth_error mm (n - get_import_mem_count m)) eqn:Hsome;auto.
      by rewrite insert_length. }
  Qed.

  Definition module_inst_build_mem (m : module) (inst: instance) (n : nat) (mmem : memory) : memory :=
  fold_left (fun mem '{| moddata_data := md; moddata_offset := moff; moddata_init := md_init |} =>
               let imc := get_import_mem_count m in 
               match md with
               | Mk_memidx k =>
                 if k <? imc then mem else 
                   (* These are guaranteed to succeed due to validation. *)
                   if decide (n = k) then mem_init_replace_single mem (assert_const1_i32_to_nat moff) (fmap compcert_byte_of_byte md_init)
                   else mem
               end
            ) m.(mod_data) mmem.
  
  Lemma module_inst_build_mems_lookup m i (n : nat) (mmem : memory_type) (x : memory) :
    module_inst_build_mems m i !! n = Some x ->
    (mod_mems m) !! n = Some mmem ->
    x = module_inst_build_mem m i (n + get_import_mem_count m) (module_inst_mem_base_func mmem).
  Proof.
    unfold module_inst_build_mems,module_inst_build_mem.
    remember (module_inst_mem_base_func mmem).
    revert x.
    apply fold_left_preserve_twice with (acc':=m0).
    { intros x Hmem1 Hmem2. simplify_eq.
      apply list_lookup_fmap_inv in Hmem1 as [m' [Heq Hmem1]].
      simplify_eq. rewrite Hmem1 in Hmem2. inversion Hmem2;auto. }
    { intros mm mem md IH x.
      destruct md,moddata_data.
      destruct (n0 <? get_import_mem_count m) eqn:Hlt;auto.
      apply PeanoNat.Nat.ltb_ge in Hlt.
      destruct (nth_error mm (n0 - get_import_mem_count m)) eqn:Hsome;cycle 1.
      { intros Hmem1 Hmem2. eapply IH in Hmem2 as Heq;eauto. subst x.
        rewrite nth_error_lookup in Hsome.
        apply lookup_ge_None in Hsome.
        apply lookup_lt_Some in Hmem1.
        destruct (decide (n + get_import_mem_count m = n0));[lia|auto].
      }
      rewrite nth_error_lookup in Hsome.
      apply lookup_lt_Some in Hsome as Hlt'.
      destruct (decide (n0 - get_import_mem_count m = n)).
      { subst n. rewrite list_lookup_insert//. intros Heq Hlook.
        rewrite PeanoNat.Nat.sub_add;[|auto]. rewrite decide_True;auto.
        inversion Heq. eapply IH in Hsome;eauto. subst. auto. }
      { rewrite list_lookup_insert_ne//. intros Hmem1 Hmem2.
        rewrite decide_False;auto. lia. }
    }
  Qed.

  Lemma module_inst_build_mems_is_Some m i n :
    is_Some (module_inst_build_mems m i !! n) <-> is_Some ((mod_mems m) !! n).
  Proof.
    split;intros Hsome%lookup_lt_is_Some;apply lookup_lt_is_Some.
    erewrite <-module_inst_build_mems_length;eauto.
    rewrite module_inst_build_mems_length;auto.
  Qed.

  Lemma module_inst_build_mem_max_opt m i n mm :
    mem_max_opt (module_inst_build_mem m i n mm) = mem_max_opt mm.
  Proof.
    unfold module_inst_build_mem.
    apply fold_left_preserve;auto.
    intros mem md. destruct md,moddata_data.
    destruct (n0 <? get_import_mem_count m);auto.
    destruct (decide (n = n0));auto.
  Qed.

  Lemma module_inst_mem_base_func_max_opt mmem :
    mem_max_opt (module_inst_mem_base_func mmem) = lim_max mmem.
  Proof. by destruct mmem;simpl. Qed.

  Definition module_import_init_mem (m: module) (inst: instance) (n : nat) (ms: memory) : memory :=
  fold_left (fun ms '{| moddata_data := md; moddata_offset := moff; moddata_init := md_init |} =>
               let imc := get_import_mem_count m in 
               match md with
               | Mk_memidx k =>
                 if k <? imc then
                   match nth_error inst.(inst_memory) k with
                   | Some m_addr =>
                       if (decide (n = k)) then mem_init_replace_single ms (assert_const1_i32_to_nat moff) (fmap compcert_byte_of_byte md_init)
                       else ms
                   | None => ms
                   end
                 else ms
               end
            ) m.(mod_data) ms.

  Lemma mem_init_replace_single_preserve_len mem offset bs :
    length (ml_data (mem_data (mem_init_replace_single mem offset bs))) = length (ml_data (mem_data mem)).
  Proof.
    unfold mem_init_replace_single. simpl.
    rewrite take_length !app_length take_length drop_length. lia.
  Qed.
  
  Lemma module_import_init_mem_lookup_length m i n mem :
    length (ml_data (mem_data (module_import_init_mem m i n mem))) = length (ml_data (mem_data mem)).
  Proof.
    unfold module_import_init_mem.
    apply fold_left_preserve;auto.
    intros x tt Hlen.
    destruct tt,moddata_data.
    destruct (n0 <? get_import_mem_count m);auto.
    destruct (nth_error (inst_memory i) n0);auto.
    destruct (decide (n = n0));auto.
    rewrite mem_init_replace_single_preserve_len. auto.
  Qed.
  
  Lemma module_import_init_mems_is_Some m i wts n :
    is_Some (wts !! n) <->
    is_Some (module_import_init_mems m i wts !! n).
  Proof.
    unfold module_import_init_mems.
    apply fold_left_preserve.
    { eauto. }
    { intros x act Hiff.
      destruct act,moddata_data.
      destruct (n0 <? get_import_mem_count m);auto.
      destruct (nth_error (inst_memory i) n0);auto.
      destruct (x !! N.of_nat m0) eqn:Hsome;auto.
      destruct (decide (N.of_nat m0 = n)).
      { subst. rewrite lookup_insert. split; auto.
        intros [yy Hsome']. simplify_eq. apply Hiff. eauto.
      }
      { rewrite lookup_insert_ne;auto. }
    }
  Qed.

  Lemma module_inst_global_init_length mglobs vs :
    length (module_inst_global_init mglobs vs) = length mglobs.
  Proof.
    revert vs.
    induction mglobs;auto.
    intros vs. simpl. destruct vs;auto.
    simpl. rewrite IHmglobs. auto.
  Qed.

  Lemma module_import_init_tabs_dom m i wts :
    dom (gset N) (module_import_init_tabs m i wts) = dom (gset N) wts.
  Proof.
    unfold module_import_init_tabs.
    apply fold_left_preserve;auto.
    intros tt me Hdom.
    destruct me, modelem_table.
    destruct (n <? get_import_table_count m);auto.
    destruct (nth_error (inst_tab i) n);auto.
    destruct (tt !! N.of_nat t) eqn:Hlook;auto.
    apply elem_of_dom_2 in Hlook. rewrite dom_insert_L.
    rewrite Hdom. rewrite - subseteq_union_L. rewrite -Hdom. set_solver.
  Qed.

  Lemma module_import_init_mems_dom m i wts :
    dom (gset N) (module_import_init_mems m i wts) = dom (gset N) wts.
  Proof.
    unfold module_import_init_mems.
    apply fold_left_preserve;auto.
    intros tt me Hdom.
    destruct me, moddata_data.
    destruct (n <? get_import_mem_count m);auto.
    destruct (nth_error (inst_memory i) n);auto.
    destruct (tt !! N.of_nat m0) eqn:Hlook;auto.
    apply elem_of_dom_2 in Hlook. rewrite dom_insert_L.
    rewrite Hdom. rewrite - subseteq_union_L. rewrite -Hdom. set_solver.
  Qed.

  Definition map_host_func (v : function_closure) :=
    match v with
    | FC_func_host tf h => Some (tf,h)
    | _ => None
    end.
  Definition filter_Some (a : option (function_type * hostfuncidx)) :=
    match a with | None => False | Some _ => True end.

  Global Instance filter_Some_dec x : Decision (filter_Some x).
  Proof. destruct x;[left|right];eauto.  simpl. done. Qed.
  
  Definition host_funcs (wfs : gmap N function_closure) :=
    filter (filter_Some) (map map_host_func (map_to_list wfs).*2).

  (* Since host functions can only be imported, the host function is already accounted for
     and determined by the validity of imports. Thus, the hl list that the imports are valid against 
     are sufficient to determine the validity of the instance *)

  Lemma interp_instance_alloc hl E (m: module) (t_imps t_exps: list extern_t) (v_imps: list module_export) (wfs : gmap N function_closure) wts wms wgs inst fts gts g_inits :
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
    let tab_inits := module_inst_build_tables m inst in
    let wts' := module_import_init_tabs m inst wts in
    let mem_inits := module_inst_build_mems m inst in
    let wms' := module_import_init_mems m inst wms in
    let glob_inits := module_inst_global_init (module_inst_build_globals m.(mod_globals)) g_inits in
                                                                            
    module_typing_body m t_imps t_exps fts gts ->
    (inst.(inst_types) = m.(mod_types) /\
       let v_imp_descs := map (fun mexp => mexp.(modexp_desc)) v_imps in
       prefix (ext_func_addrs v_imp_descs) inst.(inst_funcs) /\
         prefix (ext_tab_addrs v_imp_descs) inst.(inst_tab) /\
         prefix (ext_mem_addrs v_imp_descs) inst.(inst_memory) /\
         prefix (ext_glob_addrs v_imp_descs) inst.(inst_globs)) ->
    (* module_init_values m inst tab_inits mem_inits glob_inits -> *)
    typeof <$> g_inits = tg_t ∘ modglob_type <$> mod_globals m ->
    
    ([∗ map] _↦cl ∈ wfs, interp_closure hl (cl_type cl) cl)%I -∗ (* we must assume that the imported closures are valid *)
    ([∗ map] n↦t ∈ wts, interp_table (tab_size t) (interp_closure_pre C wfs inst hl) n) -∗ (* that imported tables are valid, note that the table might be reinitialized by current module *)
    ([∗ map] n↦m ∈ wms, interp_mem n) -∗ (* that imported memories are valid *)
    
                                                                   
    import_resources_wasm_typecheck v_imps t_imps wfs wts' wms' wgs -∗
    module_inst_resources_wasm m inst tab_inits mem_inits glob_inits
    ={E}=∗ interp_instance C hl inst ∗
        module_inst_resources_wasm_invs m inst gts tab_inits mem_inits glob_inits ∗
        import_resources_wasm_typecheck_invs v_imps t_imps wfs wts' wms' wgs
  (* it is useful to remember the exact values for each allocated invariant *).
  Proof.
    iIntros (C tab_inits wts' mem_inits wms' glob_inits Hmod Himps_of_inst Hinit_vals) "#Himps_val #Htabs_val #Hmems_val Hir Hmr".
    subst C.
    set (ifts := ext_t_funcs t_imps).
    set (its := ext_t_tabs t_imps).
    set (ims := ext_t_mems t_imps).
    set (igs := ext_t_globs t_imps).

    iDestruct (irwt_vtlen with "Hir") as "%Hvtlen".
    
    iDestruct (module_res_imports_disj with "[Hir] [Hmr]") as %Hdisj => //.
    { by iDestruct "Hir" as "(?&?)". }
    { by iDestruct "Hmr" as "(?&?)". }
    
    iDestruct "Hmr" as "(Hfr & Htr & Hmr & Hgr)".
    iDestruct (import_resources_wasm_typecheck_lengths with "Hir") as %(Hlenir&Hlenir0&Hlenir1&Hlenir2).
    iMod (import_resources_wasm_typecheck_alloc with "Hir") as "#Hir".    
    iMod (module_inst_resources_func_invs_alloc with "Hfr") as "#Hfr".
    iMod (module_inst_resources_tab_invs_alloc with "Htr") as "#Htr".
    iMod (module_inst_resources_mem_invs_alloc with "Hmr") as "#Hmr".
    iMod (module_inst_resources_glob_invs_alloc with "Hgr") as "#Hgr".
    { instantiate (1:=gts).
      instantiate (1:=(mod_globals m)).
      destruct m. simpl in Hmod.
      destruct Hmod as (Htypes & Htables & Hmems & Hglobals
                        & Helem & Hdata & Hstart & Himps & Hexps). simpl. apply Hglobals. }
    1,2: eauto.
    iModIntro. iFrame "#".
    
    iApply (interp_instance_pre_create _ wfs);[auto|].
    unfold interp_instance_pre. remember inst. destruct inst. rewrite Heqi.
    rewrite Heqi in Himps_of_inst.
    destruct Himps_of_inst as (Htypeq & Hprefunc & Hpretables & Hpremem & Hpreglob).
    iSplitR.
    { destruct m. simpl in Hmod.
      simpl in *. auto. }

    iDestruct "Hir" as "(Hfc & Htc & Hmc & Hgc)".
    
    iDestruct "Hfc" as "(Hfinv & %Hfdom & %Hftc)".
    iDestruct "Htc" as "(Htinv & %Htdom & %Httc)".
    iDestruct "Hmc" as "(Hminv & %Hmdom & %Hmtc)".
    iDestruct "Hgc" as "(Hginv & %Hgdom & %Hgtc)".
    
    (* functions *)
    iSplitR.
    { iSimpl in "Hfr". simpl in Hprefunc.
      iApply big_sepL2_forall.
      iDestruct (big_sepL2_length with "Hfr") as %Hlenfr.
      iSplit.
      { destruct m. simpl in Hmod.
        destruct Hmod as (Htypes & Htables & Hmems & Hglobals
                          & Helem & Hdata & Hstart & Himps & Hexps).
        iPureIntro. eapply inst_funcs_length_imp_app => //; last by apply Forall2_length in Htypes. }
      iIntros (k fa ft Hfa Hft).
      destruct Hprefunc as [fdecls Himpdeclapp].
      rewrite Himpdeclapp in Hfa.
      unfold ifts in Hft.
      apply lookup_app_Some in Hft as [Hft | [Hge Hft]].
      { (* the function is imported, and semantic typing has been established prior *)
        apply lookup_lt_Some in Hft as Hlt.
        rewrite -Hlenir in Hlt.
        rewrite lookup_app_l in Hfa;[|apply Hlt].
        specialize (import_funcs_lookup Hft Hfa Hftc Httc Hmtc Hgtc) as Hlook; eauto.
        destruct Hlook as [k' [Hft' Ha']].
        destruct Ha' as [fm [Hfm' Heq]].
        unfold func_typecheck in Hftc.
        rewrite -> Forall2_lookup in Hftc.
        specialize (Hftc k').
        rewrite Hfm' Hft' in Hftc.
        inversion Hftc; subst; clear Hftc.
        rewrite Heq in H1.
        destruct H1 as [cl [Hwfs Heqft]].
        inversion Heqft; subst; clear Heqft.
        simpl in *.
        unfold import_func_nainv.
        iDestruct (big_sepM_lookup with "Hfinv") as "Ha" => //.
        iExists cl. iFrame "Ha".
        iDestruct (big_sepM_lookup with "Himps_val") as "Hown" => //.
        destruct cl;eauto. rewrite Hwfs; by eauto.
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
      { destruct mod_tables eqn:Hmod_tables;auto.
        destruct ((ext_tab_addrs
                 (map (λ mexp : module_export, modexp_desc mexp) v_imps)));[|done].
        (* the function table is declared *)
        simpl nth_error.
        destruct fdecls.
        { exfalso.
          by rewrite /tab_inits module_inst_build_tables_length Heqm0 /= in Htbllen. }
        rewrite -Heqm0 /module_inst_resources_tab_invs /tab_inits.
        assert ((datatypes.mod_tables m) !! 0 = Some m0) as Hsome;[by rewrite Heqm0 /=|].
        apply module_inst_build_tables_lookup_is_Some with (i:=i) in Hsome as Hx.
        destruct Hx as [x Hx].
        eapply module_inst_build_tables_lookup in Hx as Hy;[|eauto].
        rewrite -/(tab_inits) in Hx. rewrite -/tab_inits.
        destruct tab_inits;[done|]. simpl in Hx. inversion Hx;subst x.
        iSimpl in "Htr".
        iDestruct "Htr" as "[[Htsize [Hlim Ht]] _]".
        iExists _,_. iFrame "Htsize". iFrame "Hlim".
        destruct (tt_limits (modtab_type m0)) eqn:Hlim.
        simpl table_data. unfold tab_size. simpl.
        iSplit.
        { iPureIntro. apply/ssrnat.leP.
          rewrite module_inst_built_table_max_opt_eq Hlim /=. lia. }
        { rewrite module_inst_build_table_length.
          (* the table can be initialised with imported or declared functions *)
          iApply big_sepL_forall.
          iIntros (k j Hj).
          apply lookup_lt_Some in Hj as Hlt.
          rewrite repeat_length in Hlt.
          apply module_inst_build_table_lt_is_Some with (m:=m) (i:=i) (n:=get_import_table_count m) in Hlt as [x Hlook].
          iDestruct (big_sepL_lookup _ _ k with "Ht") as "Hk";[eauto|].
          apply module_inst_build_table_lookup_Some in Hlook as Heq.

          destruct Heq as [-> | Hfunc].
          { iExists (Tf [] []),None. iFrame "#". }

          destruct Hfunc as [k' [moff [minit [fid [f [Hidx [-> [Hk [_ Hminit]]]]]]]]].
          
          destruct (decide (fid < (get_import_func_count m))).
          { (* the initialiser is imported *)
            destruct Hprefunc as [decls Hfunceq]. simpl in Hfunceq.
            rewrite Heqi /= Hfunceq in Hidx.

            rewrite lookup_app_l in Hidx;cycle 1.
            { rewrite Hlenir.
              eassert (get_import_func_count m = length _) as <-.
              { eapply get_import_count_length;eauto. rewrite Heqm0. eauto. }
              auto. }
            assert (is_Some (ext_t_funcs t_imps !! fid)) as [ft Hft].
            { apply lookup_lt_is_Some.
              eassert (get_import_func_count m = length _) as <-.
              { eapply get_import_count_length;eauto. rewrite Heqm0. eauto. }
              auto. }
            specialize (import_funcs_lookup Hft Hidx Hftc Httc Hmtc Hgtc) as Hk'; eauto.
            destruct Hk' as [k'' [Ht_imps [fm [Hv_imps Hfm]]]].
            unfold func_typecheck in Hftc.
            rewrite -> Forall2_lookup in Hftc.
            specialize (Hftc k'').
            rewrite Ht_imps Hv_imps in Hftc.
            inversion Hftc; subst; clear Hftc.
            rewrite Hfm in H2.
            destruct H2 as [cl [Hwfs Heqft]].
            unfold import_func_nainv.
            iDestruct (big_sepM_lookup with "Hfinv") as "Hown" => //.
            iDestruct (big_sepM_lookup with "Himps_val") as "Hcl" => //.
            iExists _,_. iFrame "Hk". iSimpl.
            iExists _. iFrame "Hown".
            destruct cl;[|auto].
            rewrite Hwfs. auto. }
           { (* the initialiser is declared *)
             destruct Hprefunc as [decls Hfunceq]. simpl in Hfunceq.
            rewrite Heqi /= Hfunceq in Hidx.
             eassert (drop (get_import_func_count m) inst_funcs !! (fid - (get_import_func_count m)) = Some f) as Hfid.
             { rewrite lookup_app_r in Hidx;cycle 1.
               { rewrite Hlenir.
                 eassert (get_import_func_count m = length (ext_t_funcs t_imps)) as Heq.
                 { eapply get_import_count_length;eauto. rewrite Heqm0. eauto. }
                 rewrite -Heq.
                 clear -n0. lia. }
               eassert (get_import_func_count m = length _) as Heq.
               { eapply get_import_count_length;eauto. rewrite Heqm0. eauto. }
               rewrite Heq.
               rewrite -Hlenir Hfunceq. rewrite drop_app. eauto. }
             iDestruct (big_sepL2_length with "Hfr") as %Hfrlen.
             apply lookup_lt_Some in Hfid as Hltfid.
             rewrite -Hfrlen in Hltfid.
             apply lookup_lt_is_Some in Hltfid as [fm Hfm].
             rewrite Heqm0 /= in Hfm.
             eapply Forall2_lookup_l in Htypes as [mf [Hmf Hftyp]];[|eauto].
             rewrite -Heqm0 in Hfm.
             iDestruct (big_sepL2_lookup with "Hfr") as "HH";[rewrite Heqm0 /= -Heqm0;eauto..|].
             destruct mf,fm,modfunc_type;simpl in *.             
             destruct Hftyp as [Hle [Hnth Hftyp]].             
             revert Hnth; move/eqP => Hnth.
             assert (wfs !! (N.of_nat f) = None) as Hnone.
             { eapply Hdisj. rewrite Heqi;eauto. }
             iExists _,_. iFrame "#". iSimpl.
             iExists _. iFrame "#". iSimpl. rewrite  Hnone.
             iPureIntro.
             repeat split;auto. rewrite Htypeq Heqm0 /= Hnth.
             rewrite -/its -Heql app_nil_l in Hftyp. auto. }
        }
      }
      { (* the function table is imported *)
        rewrite /its in Heql.
        remember (ext_tab_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)).
        destruct l0;[done|].
        assert (ext_t_tabs t_imps !! 0 = Some t) as Htl; first by rewrite <- Heql.
        assert (ext_tab_addrs (map (fun e => modexp_desc e) v_imps) !! 0 = Some n) as Hvl; first by rewrite <- Heql0.
        specialize (import_tabs_lookup Htl Hvl Hftc Httc Hmtc Hgtc) as HH.
        destruct HH as [k' [Hlook1 Hfm]]. destruct Hfm as [fm [Hlook2 Hfm]].
        unfold import_tab_nainv.
        unfold tab_typecheck in Httc.
        rewrite -> Forall2_lookup in Httc.
        specialize (Httc k').
        rewrite Hlook1 Hlook2 in Httc.
        inversion Httc; subst; clear Httc.
        rewrite Hfm in H1.
        destruct H1 as [tab [tt [Hwts [Htteq Htyping]]]].
        inversion Htteq; subst; clear Htteq.
        iDestruct (big_sepM_lookup with "Htinv") as "Hk'";[eauto..|].
        iDestruct "Hk'" as "(Hsize & Hlim & Helem)".
        rewrite /wts' in Hwts.
        apply module_import_init_tabs_Some in Hwts as Hwts'.
        destruct Hwts' as [x Hwts'].
        eapply module_import_init_tabs_lookup with (tab:=x) in Hwts' as HH;[|apply Hwts].
        iDestruct (big_sepM_lookup with "Htabs_val") as "Htval";[eauto|].
        subst tab. unfold tab_size.
        rewrite module_import_init_tab_lookup_length. 
        iExists _,_. iFrame "#". iPureIntro. simplify_eq.
        by apply andb_true_iff in Htyping as [? ->].
      }
    }

    (* memory *)
    iSplitR.
    { iClear "Hfr Htr Hgr Htabs_val Himps_val". iSimpl in "Hmr". simpl in Hpremem.
      destruct Hpremem as [fmems Himpdeclapp].
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
      { rewrite /mem_inits in Hmemlen. destruct mod_mems;auto.
        destruct ((ext_mem_addrs
                 (map (λ mexp : module_export, modexp_desc mexp) v_imps)));[|done].
        (* the memory is declared *)
        simpl nth_error.
        rewrite module_inst_build_mems_length /= in Hmemlen.
        destruct fmems;[done|].
        assert ((n :: fmems) !! 0 = Some n) as Hlook1;auto.
        assert (is_Some (mem_inits !! 0)) as [x Hlook2].
        { apply module_inst_build_mems_is_Some;eauto. }
        eapply module_inst_build_mems_lookup in Hlook2 as Heq;[|eauto].
        revert Heq.
        eassert (get_import_mem_count _ = length _) as ->.
        { eapply get_import_count_length;simpl;eauto. }
        simpl. intros Heq.
        iDestruct (big_sepL2_lookup with "Hmr") as "[? $]";[apply Hlook2|apply Hlook1|].
        by rewrite Heq module_inst_build_mem_max_opt module_inst_mem_base_func_max_opt. }
      { (* the memory is imported *)
        rewrite /ims in Heql.
        remember (ext_mem_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)).
        destruct l0;[done|].
        
        assert (ext_t_mems t_imps !! 0 = Some m) as Htl; first by rewrite <- Heql.
        assert (ext_mem_addrs (map (fun e => modexp_desc e) v_imps) !! 0 = Some n) as Hvl; first by rewrite <- Heql0.
        specialize (import_mems_lookup Htl Hvl Hftc Httc Hmtc Hgtc) as HH.
        destruct HH as [k' [Hlook1 Hfm]]. destruct Hfm as [fm [Hlook2 Hfm]].
        unfold import_mem_nainv.
        unfold mem_typecheck in Hmtc.
        rewrite -> Forall2_lookup in Hmtc.
        specialize (Hmtc k').
        rewrite Hlook1 Hlook2 in Hmtc.
        inversion Hmtc; subst; clear Hmtc.
        rewrite Hfm in H1.
        destruct H1 as [tab [tt [Hwts [Hmeq Htyping]]]].
        inversion Hmeq; subst; clear Hmeq.
        iDestruct (big_sepM_lookup with "Hminv") as "Hk'";[eauto..|].
        iDestruct "Hk'" as "(_ & Hmemlim)".
        assert (is_Some (wms !! N.of_nat n)) as [x Hx].
        { eapply module_import_init_mems_is_Some. eauto. }
        iDestruct (big_sepM_lookup with "Hmems_val") as "$";[eauto|].
        revert Htyping. move/andP=>[? Htyping];revert Htyping;move/eqP =>Heq.
        rewrite Heq. iFrame "#".
      }
    }

    (* globals *)
    { iClear "Hfr Hmr Htr Htabs_val". iSimpl in "Hgr". simpl in Hpreglob.
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
        specialize (import_globs_lookup Hlook2 Hlook1 Hftc Httc Hmtc Hgtc) as Hlook; eauto.
        destruct Hlook as [k' [Hk' Hfm]].
        destruct Hfm as [fm [Hfm Hfmeq]].
        unfold glob_typecheck in Hgtc.
        rewrite -> Forall2_lookup in Hgtc.
        specialize (Hgtc k').
        rewrite Hk' Hfm in Hgtc.
        inversion Hgtc; subst; clear Hgtc.
        rewrite Hfmeq in H1.
        destruct H1 as [g [gt0 [Hwgs [Hgteq Hagree]]]].
        inversion Hgteq; subst; clear Hgteq.
        simpl in *.
        unfold import_func_nainv.
        iDestruct (big_sepM_lookup with "Hginv") as "Hinv" => //.
        unfold global_agree in Hagree.
        move/andP in Hagree.
        destruct Hagree as [Htgmut Htgt].
        move/eqP in Htgmut.
        move/eqP in Htgt.
        rewrite Htgmut.
        destruct g => /=.
        destruct g_mut eqn:Hgmut => //=.
        { rewrite Htgt => /=.
          iExists interp_value. iFrame "Hinv". iModIntro. auto. }
        { rewrite Htgt => /=. iFrame "Hinv". }        
      }
      { (* declared globals *)
        iApply big_sepL2_forall.
        apply Forall2_length in Hglobals as Hgloblen'.
        rewrite -Hgloblen module_inst_global_init_length fmap_length Hgloblen'.
        iSplit;auto.
        iIntros (k n gt Hlook1 Hlook2).
        eapply Forall2_lookup_r in Hglobals as [g [Hg Hgtyp]];eauto.
        assert (is_Some (glob_inits !! k)) as [init Hinit].
        { apply lookup_lt_is_Some. unfold glob_inits. simpl. rewrite module_inst_global_init_length.
          rewrite fmap_length. apply lookup_lt_is_Some. eauto. }
        iDestruct (big_sepL2_lookup with "Hgr") as (τg) "[%Hgts Hg]";[eauto..|].
        rewrite Hlook2 in Hgts. inversion Hgts.
        unfold interp_global. iSimpl. 
        destruct (tg_mut τg) eqn:Hmut.
        { iExists interp_value. iFrame "Hg". iModIntro. auto. }
        { iFrame "Hg". }        
      }
    }
  Qed.
    

End InterpInstance.
