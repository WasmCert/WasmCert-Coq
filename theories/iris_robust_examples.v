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

Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }}) (at level 50).

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

Import DummyHosts.

(* Example Programs *)
Section Examples.

  Import DummyHost.

  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ, !wtablimitG Σ, !wmemlimitG Σ,
        !logrel_na_invs Σ, HWP:host_program_logic}.

  Definition xx i := (VAL_int32 (Wasm_int.int_of_Z i32m i)).
  Definition xb b := (VAL_int32 (wasm_bool b)).

  Lemma wp_seq_can_trap_same_ctx (Φ Ψ : iris.val -> iProp Σ) (s : stuckness) (E : coPset) (es1 es2 : language.expr wasm_lang) f i lh :
    (¬ (Ψ trapV)) ∗ (Φ trapV) ∗ ↪[frame] f ∗
    (↪[frame] f -∗ WP es1 @ NotStuck; E {{ w, (⌜w = trapV⌝ ∨ Ψ w) ∗ ↪[frame] f }}) ∗
    (∀ w, Ψ w ∗ ↪[frame] f -∗ WP (iris.of_val w ++ es2) @ s; E CTX i; lh {{ v, Φ v ∗ ↪[frame] f }})%I
    ⊢ WP (es1 ++ es2) @ s; E CTX i; lh {{ v, Φ v ∗ ↪[frame] f }}.
  Proof.
    iIntros "(HPsi & Hphi & Hf & Hes1 & Hes2)".
    iApply (wp_wand_ctx _ _ _ (λ  v, Φ v ∗ ∃ f0, ↪[frame] f0 ∗ ⌜f0 = f⌝) with "[-]")%I;cycle 1.
    { iIntros (v) "[$ Hv]". iDestruct "Hv" as (f0) "[Hv ->]". iFrame. }
    iApply wp_seq_can_trap_ctx.
    iFrame. iSplitL "Hes1".
    { iIntros "Hf". iDestruct ("Hes1" with "Hf") as "Hes1".
      iApply (wp_wand with "Hes1").
      iIntros (v) "[$ Hv]". iExists _. iFrame. eauto. }
    { iIntros (w f') "[H [Hf ->]]".
      iDestruct ("Hes2" with "[$]") as "Hes2".
      iApply (wp_wand_ctx with "Hes2").
      iIntros (v) "[$ Hv]". iExists _. iFrame. eauto. }
  Qed.

  Lemma wp_seq_can_trap_same_empty_ctx (Φ Ψ : iris.val -> iProp Σ) (s : stuckness) (E : coPset) (es1 es2 : language.expr wasm_lang) f :
    (¬ (Ψ trapV)) ∗ (Φ trapV) ∗ ↪[frame] f ∗
    (↪[frame] f -∗ WP es1 @ NotStuck; E {{ w, (⌜w = trapV⌝ ∨ Ψ w) ∗ ↪[frame] f }}) ∗
    (∀ w, Ψ w ∗ ↪[frame] f -∗ WP (iris.of_val w ++ es2) @ s; E {{ v, Φ v ∗ ↪[frame] f }})%I
    ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v ∗ ↪[frame] f }}.
  Proof.
    iIntros "(HPsi & Hphi & Hf & Hes1 & Hes2)".
    iApply wp_wasm_empty_ctx.
    iApply wp_seq_can_trap_same_ctx.
    iFrame.
    iIntros (w) "?".
    iApply wp_wasm_empty_ctx.
    iApply "Hes2". done.
  Qed.

  Lemma wp_wand s E (e : iris.expr) (Φ Ψ : iris.val -> iProp Σ) :
    WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
  Proof. iApply (wp_wand). Qed.
  
  Definition lse a : iris.expr :=
    to_e_list
      [BI_const (xx 0);
       BI_const (xx 42);
       BI_store T_i32 None 0%N 0%N] ++
      [AI_invoke a] ++
    to_e_list
    [BI_const (xx 0);
     BI_load T_i32 None 0%N 0%N].


  Lemma lse_spec f n a C i es :
    (tc_label C) = [] ∧ (tc_return C) = None ->
    f.(f_inst).(inst_memory) !! 0 = Some n ->
    be_typing (upd_local_label_return C [] [[]] (Some [])) es (Tf [] []) ->
    
    {{{ ↪[frame] f
         ∗ na_own logrel_nais ⊤
         ∗ na_inv logrel_nais (wfN (N.of_nat a)) ((N.of_nat a) ↦[wf] (FC_func_native i (Tf [] []) [] es))
         ∗ interp_instance (HWP:=HWP) C i
         ∗ ∃ c, (N.of_nat n) ↦[wms][ 0%N ] (bits (VAL_int32 c)) }}}
      lse a
      {{{ w, (⌜w = trapV⌝ ∨ ⌜w = immV [xx 42]⌝
                                      ∗ (N.of_nat n) ↦[wms][ 0%N ] (bits (xx 42))
                                      ∗ na_own logrel_nais ⊤)
               ∗ ↪[frame] f }}}.
  Proof.
    iIntros (Hc Hn Hes Φ) "(Hf & Hown & #Ha & #Hi & Hn) HΦ".
    iDestruct "Hn" as (c) "Hn".
    iApply (wp_wand with "[-HΦ] HΦ").

    unfold lse. simpl.

    take_drop_app_rewrite 3.
    iApply (wp_seq _ _ _ (λ w, (⌜w = immV []⌝ ∗ N.of_nat n↦[wms][0] bits (xx 42)) ∗ ↪[frame] f)%I).
    iSplitR;[by iIntros "[[%Hcontr _] _]"|].
    iSplitR "Hown".
    { unfold serialise_i32. simpl. iApply (wp_store (λ w, ⌜w = immV ([])⌝)%I with "[$Hf Hn]");eauto.
      by rewrite Memdata.encode_int_length. }
    iIntros (w) "[[-> Hn] Hf]". iSimpl.

    take_drop_app_rewrite_twice 0 2.
    iApply wp_wasm_empty_ctx.
    iApply wp_base_push;auto.
    rewrite -(app_nil_r [_]).
    iApply (wp_seq_can_trap_same_ctx _ (λ v, interp_values [] v ∗ na_own logrel_nais ⊤)%I).
    iSplitR;[by iIntros "[H _]";iDestruct "H" as (v) "[%Hcontr _]"|].
    iSplitR;[auto|].
    iFrame.
    iSplitL "Hown".
    { iIntros "Hf". iApply fupd_wp.
      iMod (na_inv_acc with "Ha Hown") as "(>Haf & Hown & Hcls)";[solve_ndisj..|].
      rewrite -(app_nil_l [_]).
      iApply (wp_invoke_native with "Hf Haf");eauto.
      iModIntro. iNext. iIntros "[Hf Haf]".
      rewrite -wp_frame_rewrite.
      iApply wp_wasm_empty_ctx_frame.
      take_drop_app_rewrite 0.
      iApply (wp_block_local_ctx with "Hf");[eauto..|].
      iNext. iIntros "Hf".
      iApply wp_wasm_empty_ctx_frame.
      rewrite wp_frame_rewrite.
      
      iApply fupd_wp.
      iMod ("Hcls" with "[$]") as "Hown". iModIntro.
      simpl.

      iDestruct (be_fundamental_local _ _ [] _ [] with "Hi") as "Hl";eauto.
      iSpecialize ("Hl" $! _ [] with "Hf Hown []").
      { iRight. iExists _. iSplit;eauto. }
      unfold interp_expression_closure. simpl.
      iApply (wp_wand with "Hl").
      iIntros (v) "[[[H|H] Hown] HH]";iFrame. iRight;auto.
    }

    iIntros (w) "[[#Hval Hown] Hf]".
    iApply wp_base_pull. iApply wp_wasm_empty_ctx.
    iDestruct "Hval" as (ws) "[-> Heq]".
    iDestruct (big_sepL2_length with "Heq") as %Heq. destruct ws;[|done].
    iSimpl.

    iApply (wp_wand _ _ _ (λ vs, (⌜vs = immV _⌝ ∗ _) ∗ _)%I with "[Hn Hf]").
    { iApply wp_load;eauto;[|iFrame];eauto. }

    iIntros (v) "[[-> Hn] Hf]". iFrame.
    iRight. iFrame. auto.
  Qed.

  Definition interp_closure_pre τctx (fimps : gmap nat function_closure) (i : instance) (n : N) (τf : function_type) :=
    λne (cl : leibnizO function_closure),
         match cl with
         | FC_func_native j τ' t_locs b_es =>
             match fimps !! (N.to_nat n) with
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
  
  Definition interp_instance_pre (τctx : t_context) (fimps : gmap nat function_closure) :=
    λne (i : leibnizO instance), interp_instance' τctx (interp_closure_pre τctx fimps i) i.
  Global Instance interp_instance_pre_persistent τctx fimps i : Persistent (interp_instance_pre τctx fimps i).
  Proof. apply interp_instance_persistent';intros. destruct cl,f; apply _. Qed.

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
      destruct (fimps !! N.to_nat n) eqn:Hlook.
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
    iFrame "#".
    iDestruct (big_sepL2_length with "Hfunc") as %Hlen.
    iSplitR.
    { iApply (big_sepL2_forall).
      iSplit;[auto|iIntros (k f ft Hf Hft)].
      iDestruct (big_sepL2_lookup with "Hfunc") as (cl) "[Hfna Hcl]";[eauto..|].
      iExists _. iFrame "Hfna".
      iApply interp_closure_pre_ind;eauto. }
    { destruct (nth_error tc_table 0).
      destruct (nth_error inst_tab 0);[|done].
      iDestruct "Htable" as (table_size) "[Hlim [Hsize Ht]]".
      iExists _. iFrame "Hsize Hlim".
      iApply (big_sepL_forall).
      iIntros (k x Hlook).
      iDestruct (big_sepL_lookup with "Ht") as (τf fe) "[Htt Hf]";[eauto|].
      iExists τf,_. iFrame "Htt".
      destruct fe;[|auto].
      iDestruct "Hf" as (?) "[Hfna Hf]".
      iExists _. iFrame "Hfna". iApply interp_closure_pre_ind;eauto. done. }
  Qed.
      
  Definition import_resources_wasm_typecheck_invs (v_imps: list module_export)
             (t_imps: list extern_t) (wfs: gmap nat function_closure)
             (wts: gmap nat tableinst) (wms: gmap nat memory) (wgs: gmap nat global): iProp Σ :=
    import_resources_wasm_domcheck v_imps wfs wts wms wgs ∗
  [∗ list] i ↦ v; t ∈ v_imps; t_imps,
  match v.(modexp_desc) with
  | MED_func (Mk_funcidx i) => ((∃ cl, na_inv logrel_nais (wfN (N.of_nat i)) (N.of_nat i ↦[wf] cl) ∗ ⌜ wfs !! i = Some cl /\ t = ET_func (cl_type cl) ⌝)%I)
                                
  | MED_table (Mk_tableidx i) => (∃ tab tt, N.of_nat i ↪[wtsize]tab_size tab ∗
                                           N.of_nat i ↪[wtlimit]table_max_opt tab ∗
                                           ([∗ list] j↦tabelem ∈ table_data tab, na_inv logrel_nais (wtN (N.of_nat i) (N.of_nat j)) (N.of_nat i ↦[wt][N.of_nat j]tabelem))
                                           ∗ ⌜ wts !! i = Some tab /\ t = ET_tab tt /\ tab_typing tab tt ⌝)
                                  
  | MED_mem (Mk_memidx i) => (∃ mem mt, (na_inv logrel_nais (wmN (N.of_nat i)) (∃ (mem : memory),
                                ([∗ list] j ↦ b ∈ (mem.(mem_data).(ml_data)), N.of_nat i ↦[wm][N.of_nat j] b) ∗
                                N.of_nat i ↦[wmlength] mem_length mem)) ∗
                            N.of_nat i ↪[wmlimit] mem_max_opt mem ∗ ⌜ wms !! i = Some mem /\ t = ET_mem mt /\ mem_typing mem mt ⌝)
                              
  | MED_global (Mk_globalidx i) => (∃ g gt, na_inv logrel_nais (wgN (N.of_nat i)) (∃ w, N.of_nat i ↦[wg] Build_global (tg_mut gt) w ∗ interp_value (tg_t gt) w)
                                                  ∗ ⌜ wgs !! i = Some g /\ t = ET_glob gt /\ global_agree g gt ⌝)
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

  Lemma import_resources_wasm_typecheck_func_len v_imps t_imps wfs wts wms wgs :
    import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
    ⌜length (ext_func_addrs (map (λ mexp : module_export, modexp_desc mexp) v_imps)) = length (ext_t_funcs t_imps)⌝.
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
      { destruct f. simpl. rewrite HlenIH.
        iDestruct "Hx" as (?) "[_ [_ %H]]".
        rewrite H //. }
      { destruct t. rewrite HlenIH.
        iDestruct "Hx" as (? ?) "[_ [_ %H]]". destruct H as [H _].
        rewrite H //. }
      { destruct m. rewrite HlenIH.
        iDestruct "Hx" as (? ?) "[_ [_ %H]]". destruct H as [H _].
        rewrite H //. }
      { destruct g. rewrite HlenIH.
        iDestruct "Hx" as (? ?) "[_ [_ %H]]". destruct H as [H _].
        rewrite H //. }
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

  Lemma module_inst_resources_func_NoDup mfuncs inst inst_f :
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

  Lemma module_res_imports_disj v_imps t_imps wfs wts wms wgs m inst :
   import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
   module_inst_resources_func (mod_funcs m) inst (drop (get_import_func_count m) (inst_funcs inst)) -∗
   ⌜∀ i fa, (drop (get_import_func_count m) (inst_funcs inst)) !! i = Some fa -> wfs !! fa = None⌝.
  Proof.
    iIntros "[[%Hdom _] Hi] Hf".
    iIntros (i fa Hsome).
    iDestruct (big_sepL2_length with "Hf") as %Hlen.
    apply lookup_lt_Some in Hsome as Hlt. rewrite -Hlen in Hlt.
    apply lookup_lt_is_Some_2 in Hlt as [cl Hk'].
    iDestruct (big_sepL2_lookup with "Hf") as "H";eauto.
    destruct (wfs !! fa) eqn:Hnone;auto.
    apply elem_of_dom_2 in Hnone.
    rewrite Hdom in Hnone.
    apply elem_of_list_to_set in Hnone.
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
    

  Definition module_inst_resources_tab_invs (mtabs: list module_table) (inst_t: list tableaddr) : iProp Σ :=
    ([∗ list] tab; addr ∈ mtabs; inst_t,
       let tab := (match tab.(modtab_type).(tt_limits) with
                                 | {| lim_min := min; lim_max := omax |} =>
                                     (Build_tableinst
                                        (repeat None (ssrnat.nat_of_bin min)))
                                       (omax)
                   end) in
       N.of_nat addr ↪[wtsize]tab_size tab ∗
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

  Definition module_inst_resources_mem_invs (mmems: list memory_type) (inst_m: list memaddr) : iProp Σ := 
    ([∗ list] mem; addr ∈ mmems; inst_m,
       na_inv logrel_nais (wmN (N.of_nat addr))
       (N.of_nat addr ↦[wmblock] (match mem with
                                 | {| lim_min:= min; lim_max := omax |} =>
                                     Build_memory
                                       {| ml_init := #00%byte; ml_data := repeat #00%byte (N.to_nat min) |}
                                       (omax)
                                 end))
    ).

  Lemma module_inst_resources_mem_invs_alloc E mmems inst_m :
    module_inst_resources_mem mmems inst_m  ={E}=∗
    module_inst_resources_mem_invs mmems inst_m.
  Proof.
    iIntros "Himps".
    iApply big_sepL2_fupd.
    iApply (big_sepL2_mono with "Himps");intros k exp expt Hlook1 Hlook2;simpl.
    iIntros "Hf".
    iApply na_inv_alloc. iNext. iFrame.
  Qed.
  
  Definition module_inst_resources_glob_invs (mglobs: list module_glob) (g_inits: list value) (inst_g: list globaladdr) : iProp Σ :=
    ([∗ list] g; addr ∈ mglobs; inst_g,
       na_inv logrel_nais (wgN (N.of_nat addr)) (∃ w, N.of_nat addr ↦[wg] Build_global (tg_mut (modglob_type g)) w
                                                               ∗ interp_value (tg_t (modglob_type g)) w)
    ).

  Lemma module_inst_resources_glob_invs_alloc E mglobs g_inits inst_g :
    (forall k g i v, mglobs !! k = Some g ->
              inst_g !! k = Some i ->
              g_inits !! i = Some v ->
              ⊢ interp_value (Σ:=Σ) (tg_t (modglob_type g)) v) ->

    module_inst_resources_glob mglobs g_inits inst_g ={E}=∗
    module_inst_resources_glob_invs mglobs g_inits inst_g.
  Proof.
    iIntros (Hginitsval) "Himps".
    iApply big_sepL2_fupd.
    iApply (big_sepL2_mono with "Himps");intros k exp expt Hlook1 Hlook2;simpl.
    iIntros "Hf".
    destruct (nth_error g_inits expt) eqn:Hnth;[|done].
    iApply na_inv_alloc. iNext. iExists _. iFrame.
    iApply Hginitsval;eauto.
    by rewrite -nth_error_lookup.
  Qed.

  Lemma get_import_func_count_length m t_imps c :
    Forall2 (λ imp e, module_import_typing c (imp_desc imp) e) (mod_imports m) t_imps ->
    get_import_func_count m = length (ext_t_funcs t_imps).
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
      all: unfold ext_t_funcs in IHt_imps.
      all: rewrite length_is_size size_pmap /= in IHt_imps.
      all: rewrite <-(IHt_imps m');auto. }
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
    erewrite get_import_func_count_length;[|eauto].
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
  
  Lemma interp_instance_alloc E m t_imps t_exps v_imps wfs wts wms wgs g_inits inst :
    module_typing m t_imps t_exps ->
    (inst.(inst_types) = m.(mod_types) /\
       let v_imp_descs := map (fun mexp => mexp.(modexp_desc)) v_imps in
       prefix (ext_func_addrs v_imp_descs) inst.(inst_funcs) /\
         prefix (ext_tab_addrs v_imp_descs) inst.(inst_tab) /\
         prefix (ext_mem_addrs v_imp_descs) inst.(inst_memory) /\
         prefix (ext_glob_addrs v_imp_descs) inst.(inst_globs)) ->
    (forall k g i v, (mod_globals m) !! k = Some g ->
              (drop (get_import_global_count m) (inst_globs inst)) !! k = Some i ->
              g_inits !! i = Some v ->
              ⊢ interp_value (Σ:=Σ) (tg_t (modglob_type g)) v) ->(* we must assume that the new global initialisers are valid *)
    
    ([∗ map] _↦cl ∈ wfs, interp_closure (HWP:=HWP) (cl_type cl) cl)%I -∗ (* we must assume that the imported closures are valid *)
                                                                   
                                                                   
    import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
    module_inst_resources_wasm m inst g_inits
    ={E}=∗ ∃ C, ⌜tc_label C = [] ∧ tc_local C = [] ∧ tc_return C = None⌝ ∗ interp_instance (HWP:=HWP) C inst.
  Proof.
    iIntros (Hmod Himps_of_inst Hginitsval) "#Himps_val Hir Hmr".
    destruct Hmod as [fts [gts Hmod]].
    set (ifts := ext_t_funcs t_imps).
    set (its := ext_t_tabs t_imps).
    set (ims := ext_t_mems t_imps).
    set (igs := ext_t_globs t_imps).
    set (C :=
           {|
             tc_types_t := (mod_types m);
             tc_func_t := (ifts ++ fts)%list;
             tc_global := (igs ++ gts)%list;
             tc_table := (its ++ map (λ t : module_table, modtab_type t) (mod_tables m))%list;
             tc_memory := (ims ++ (mod_mems m))%list;
             tc_local := [];
             tc_label := [];
             tc_return := None
           |}).

    iExists C. iSplitR;[iModIntro;auto|].
    iDestruct "Hmr" as "(Hfr & Htr & Hmr & Hgr)".
    iDestruct (module_res_imports_disj with "Hir Hfr") as %Hdisj.
    iDestruct (import_resources_wasm_typecheck_func_len with "Hir") as %Hlenir.
    iMod (import_resources_wasm_typecheck_alloc with "Hir") as "#Hir".    
    iDestruct (module_inst_resources_func_NoDup with "Hfr") as %Hnodup.
    iMod (module_inst_resources_func_invs_alloc with "Hfr") as "#Hfr".
    iMod (module_inst_resources_tab_invs_alloc with "Htr") as "#Htr".
    iMod (module_inst_resources_mem_invs_alloc with "Hmr") as "#Hmr".
    iMod (module_inst_resources_glob_invs_alloc with "Hgr") as "#Hgr";[auto|].
    iModIntro.
    
    iApply (interp_instance_pre_create _ wfs);[auto|].
    unfold interp_instance_pre. destruct inst. rewrite /C.
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
        destruct cl;eauto. rewrite Nat2N.id Hwfs; eauto. 
      }
      { (* the function is declared and syntactically well-typed *)
        unfold module_inst_resources_func_invs.
        destruct m. simpl in Hmod.
        destruct Hmod as (Htypes & Htables & Hmems & Hglobals
                          & Helem & Hdata & Hstart & Himps & Hexps).
        rewrite Himpdeclapp.
        eassert (get_import_func_count _ = length _) as ->.
        { eapply get_import_func_count_length;eauto. }
        rewrite -Hlenir. rewrite drop_app.
        eapply Forall2_lookup_r in Htypes as [mf [Hmf Hftyp]];[|eauto].
        simpl.
        rewrite lookup_app_r in Hfa;[|rewrite Hlenir//].
        rewrite Hlenir in Hfa.
        
        assert (wfs !! fa = None) as Hnone.
        { apply Hdisj with ((k - length (ext_t_funcs t_imps))). simpl datatypes.inst_funcs.
          rewrite Himpdeclapp. erewrite get_import_func_count_length;eauto.
          rewrite -Hlenir drop_app. rewrite Hlenir. auto. }

        iDestruct (big_sepL2_lookup with "Hfr") as "Hf";[eauto..|].
        destruct mf,ft. simpl in *.
        destruct modfunc_type;simplify_eq.
        iExists _. iFrame "#". rewrite Nat2N.id.
        rewrite Hnone. iSplit;[auto|].
        destruct Hftyp as [Hle [Heq Hftyp]].
        revert Heq. move/eqP =>Heq. rewrite Heq. iSplit;auto. }
    }

    
      

  Admitted.
    

End Examples.
