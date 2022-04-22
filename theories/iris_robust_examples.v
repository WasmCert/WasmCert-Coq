From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_rules iris_fundamental iris_wp iris_interp_instance_alloc.
Require Export datatypes host operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).

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

  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !wtablimitG Σ, !wmemlimitG Σ,
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
  
  Definition lse_expr a n :=
      [BI_const (xx 0);
       BI_const (xx 42);
       BI_store T_i32 None 0%N 0%N;
       BI_call a;
       BI_const (xx 0);
       BI_load T_i32 None 0%N 0%N;
       BI_set_global n].

  Definition lse a n :=
    to_e_list (lse_expr a n).

  Lemma lse_spec f n j a C i es g k locs :
    (tc_label C) = [] ∧ (tc_return C) = None ->

    f.(f_inst).(inst_memory) !! 0 = Some n ->
    f.(f_inst).(inst_funcs) !! j = Some a ->
    f.(f_inst).(inst_globs) !! g = Some k ->
    
    be_typing (upd_local_label_return C locs [[]] (Some [])) es (Tf [] []) ->
    
    ⊢ {{{ ↪[frame] f
         ∗ na_own logrel_nais ⊤
         ∗ na_inv logrel_nais (wfN (N.of_nat a)) ((N.of_nat a) ↦[wf] (FC_func_native i (Tf [] []) locs es))
         ∗ interp_instance (HWP:=HWP) C i
         ∗ (∃ gv, N.of_nat k ↦[wg] {| g_mut := MUT_mut; g_val := gv |})
         ∗ ∃ c, (N.of_nat n) ↦[wms][ 0%N ] (bits (VAL_int32 c)) }}}
      lse j g
      {{{ w, (⌜w = trapV⌝ ∨ (⌜w = immV []⌝
                                      ∗ (N.of_nat k) ↦[wg] {| g_mut := MUT_mut; g_val := xx 42 |}
                                      ∗ (N.of_nat n) ↦[wms][ 0%N ] (bits (xx 42))
                                      ∗ na_own logrel_nais ⊤))
               ∗ ↪[frame] f }}}.
  Proof.
    iIntros (Hc Hn Ha Hg Hes Φ). iModIntro.
    iIntros "(Hf & Hown & #Ha & #Hi & Hg & Hn) HΦ".
    iDestruct "Hn" as (c) "Hn".
    iDestruct "Hg" as (gv) "Hg".
    iApply (wp_wand with "[-HΦ] HΦ").

    unfold lse.

    take_drop_app_rewrite 3.
    iApply (wp_seq _ _ _ (λ w, (⌜w = immV []⌝ ∗ N.of_nat n↦[wms][0] bits (xx 42)) ∗ ↪[frame] f)%I).
    iSplitR;[by iIntros "[[%Hcontr _] _]"|].
    iSplitR "Hown Hg".
    { unfold serialise_i32. simpl. iApply (wp_store (λ w, ⌜w = immV ([])⌝)%I with "[$Hf Hn]");eauto.
      by rewrite Memdata.encode_int_length. }
    iIntros (w) "[[-> Hn] Hf]". iSimpl.

    take_drop_app_rewrite_twice 0 3.
    iApply wp_wasm_empty_ctx.
    iApply wp_base_push;auto.
    iApply (wp_call_ctx with "Hf");eauto.
    iNext. iIntros "Hf".
    iApply wp_base_pull.
    iApply wp_wasm_empty_ctx.
    iSimpl.
    
    take_drop_app_rewrite_twice 0 3.
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

      iDestruct (be_fundamental_local _ _ [] _ locs with "Hi") as "Hl";eauto.
      iSpecialize ("Hl" $! _ (n_zeros locs) with "Hf Hown []").
      { iRight. iExists _. iSplit;eauto. rewrite app_nil_l. iApply n_zeros_interp_values. }
      unfold interp_expression_closure. simpl.
      iApply (wp_wand with "Hl").
      iIntros (v) "[[[H|H] Hown] HH]";iFrame. iRight;auto.
    }

    iIntros (w) "[[#Hval Hown] Hf]".
    iApply wp_base_pull. iApply wp_wasm_empty_ctx.
    iDestruct "Hval" as (ws) "[-> Heq]".
    iDestruct (big_sepL2_length with "Heq") as %Heq. destruct ws;[|done].
    iSimpl.

    take_drop_app_rewrite 2.
    iApply (wp_seq _ _ _ (λ v, (⌜v = immV _⌝ ∗ _) ∗ _)%I).
    iSplitR;[by iIntros "[[% _] _]";done|].
    iSplitL "Hn Hf".
    { iApply wp_load;eauto;[|iFrame];eauto. }
    iIntros (v) "[[-> Hn] Hf]". iSimpl.

    iApply (wp_wand _ _ _ (λ v, (⌜v = immV _⌝ ∗ _) ∗ _)%I with "[Hf Hg]").
    { iApply (wp_set_global with "[] Hf Hg"); eauto. }

    iIntros (v) "[[-> Hg] Hf]". iFrame.
    iRight. iFrame. auto.
  Qed.

End Examples.

Section Examples_host.

  Import DummyHost.

  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ, !wtablimitG Σ, !wmemlimitG Σ,
        !logrel_na_invs Σ, HWP:host_program_logic,!hvisG Σ, !hmsG Σ}.


  Notation "{{{ P }}} es {{{ v , Q }}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).

  Notation " n ↪[vis]{ q } v" := (ghost_map_elem (V := module_export) visGName n q v%V)
                           (at level 20, q at level 5, format " n ↪[vis]{ q } v") .
  Notation " n ↪[vis] v" := (ghost_map_elem (V := module_export) visGName n (DfracOwn 1) v%V)
                          (at level 20, format " n ↪[vis] v").
  
  Notation " n ↪[mods]{ q } v" := (ghost_map_elem (V := module) msGName n q v%V)
                           (at level 20, q at level 5, format " n ↪[mods]{ q } v") .
  Notation " n ↪[mods] v" := (ghost_map_elem (V := module) msGName n (DfracOwn 1) v%V)
                               (at level 20, format " n ↪[mods] v").

  Lemma wp_wand_host s E (e : host_expr) (Φ Ψ : host_val -> iProp Σ) :
    WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
  Proof. iApply (weakestpre.wp_wand). Qed.
  

  Definition lse_module :=
    {| mod_types := [Tf [] []; Tf [] []];
       mod_funcs :=  [ {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [] ;
          modfunc_body := lse_expr 0 0
        |} ] ;
      mod_tables := [];
      mod_mems := [ {| lim_min := 4%N ; lim_max := None |} ];
      mod_globals := (* [ {| modglob_type := {| tg_mut := MUT_mut; tg_t := T_i32 |} ; modglob_init := [BI_const (xx 0)] |} ]; *) [];
      mod_elem := [];
      mod_data := [];
      mod_start := Some {| modstart_func := Mk_funcidx 1 |};
      mod_imports := [ {| imp_module := list_byte_of_string "Adv";
                         imp_name := list_byte_of_string "adv_call";
                         imp_desc := ID_func 0 |};
                       {| imp_module := list_byte_of_string "Ret";
                         imp_name := list_byte_of_string "ret_glob";
                         imp_desc := ID_global {| tg_mut := MUT_mut; tg_t := T_i32 |} |} ];
      mod_exports := []
    |}.

  Definition lse_func_impts : seq.seq extern_t := [ET_func (Tf [] [])].
  Definition lse_glob_impts : seq.seq extern_t := [ET_glob {| tg_mut := MUT_mut; tg_t := T_i32 |} ].

  Ltac type_next :=
  match goal with
  | |- context [ be_typing _ ?e _  ] =>
      rewrite -(list.take_drop (length e - 1) e);simpl take; simpl drop;
      eapply bet_composition;[|econstructor;eauto];simpl
  end.
  
  Lemma lse_module_typing :
    module_typing lse_module (lse_func_impts ++ lse_glob_impts) [].
  Proof.
    exists [Tf [] []],[ (* {| tg_mut := MUT_mut; tg_t := T_i32 |} *)]. simpl.
    repeat split;eauto.
    { apply Forall2_cons. split;auto. cbn.
      repeat split;auto.
      repeat type_next.
      rewrite <- (take_drop 1 [BI_const _;_]);simpl take;simpl drop.
      eapply bet_composition;[econstructor|].
      rewrite <- (app_nil_r [typeof _]);simpl typeof.
      rewrite <- (take_drop 1 [T_i32;_]);simpl take;simpl drop.
      eapply bet_weakening. apply bet_const. }
    { apply Forall2_cons. split;auto.
      apply Forall2_cons. split;auto. }
  Qed.

  Definition adv_lse_instantiate :=
    [ ID_instantiate [0%N] 0 [] ;
      ID_instantiate [] 1 [0%N;1%N] ].

  
  Lemma instantiate_lse adv_module g_ret wret :
    module_typing adv_module [] lse_func_impts -> (* we assume the adversary module has an export of the () → () *)
    mod_start adv_module = None -> (* that it does not have a start function *)
    module_restrictions adv_module -> (* that it adheres to the module restrictions (i.e. only constant initializers for globals) *)
    module_elem_bound_check_gmap ∅ [] adv_module -> (* if the adversary module declares a table, there cannot be more initializers that its size *)
    module_data_bound_check_gmap ∅ [] adv_module -> (* if the adversary module declares a memory, there cannot be more initializers that its size *)
    typeof wret = T_i32 -> (* the imported return global has type i32 *)

    ⊢ {{{ g_ret ↦[wg] {| g_mut := MUT_mut; g_val := wret |} ∗
          0%N ↪[mods] adv_module ∗
          1%N ↪[mods] lse_module ∗
          na_own logrel_nais ⊤ ∗
          (∃ name, 1%N ↪[vis] {| modexp_name := name; modexp_desc := MED_global (Mk_globalidx (N.to_nat g_ret)) |}) ∗
          (∃ vs, 0%N ↪[vis] vs) }}}
        ((adv_lse_instantiate,[]) : host_expr)
      {{{ v, ⌜v = (trapV : host_val)⌝ ∨ g_ret ↦[wg] {| g_mut := MUT_mut; g_val := xx 42|} }}} .
  Proof.
    iIntros (Htyp Hnostart Hrestrict Hboundst Hboundsm Hgrettyp).
    iModIntro. iIntros (Φ) "(Hgret & Hmod_adv & Hmod_lse & Hown & Hvis1 & Hvis) HΦ".
    iApply (wp_seq_host_nostart with "[$Hmod_adv] [Hvis] ") => //.
    { iIntros "Hmod_adv".
      iApply weakestpre.wp_mono.
      2: iApply (instantiation_spec_operational_no_start _ _ _ [] [] _ _ _ _ ∅ ∅ ∅ ∅);eauto;iFrame.
      2: cbn; repeat iSplit =>//.
      iIntros (v) "[$ Hv']". iExact "Hv'".
      iPureIntro. destruct Htyp as [fts [gts Htyp]].
      destruct adv_module;simpl in *.
      destruct Htyp as (_&_&_&_&_&_&_&_&Htyp).
      apply Forall2_length in Htyp. rewrite /lse_func_impts /= // in Htyp.
    }

    iIntros (w) "(_ & _ & Hinst_adv) Hmod_adv".
    iDestruct "Hinst_adv" as (inst_adv g_adv_inits t_adv_inits m_adv_inits (?&?&?&?&?&?) Htyp_inits) "(Hinst_adv_res & Hadv_exports)".
    iDestruct (big_sepL2_length with "Hadv_exports") as %Hexp_len.
    destruct (mod_exports adv_module) eqn:Hexp;[done|].
    destruct l;[|done].
    iDestruct "Hadv_exports" as "[Hn _]".
    revert Htyp. rewrite module_typing_body_eq =>Htyp.
    destruct Htyp as [fts [gts Htyp]].
    assert (Hmod:=Htyp).
    remember adv_module as advm.
    destruct adv_module. rewrite Heqadvm in Hexp.
    rewrite Heqadvm in Hmod.
    
    simpl in Hexp. subst mod_exports.
    destruct Hmod as (Hmod&_&_&_&_&_&_&Himpts&Hexpts).
    apply Forall2_length in Himpts. destruct mod_imports;[|done].
    unfold lse_func_impts in Hexpts. simpl in Hexpts.
    apply Forall2_cons in Hexpts as [He _].
    unfold module_export_typing in He. simpl in He.
    destruct (modexp_desc m) eqn:Hm;[destruct f|by destruct t|by destruct m0|by destruct g].
    apply andb_true_iff in He as [Hle He].
    destruct (nth_error fts n) eqn:Hn;[|done].
    revert He. move/eqP=>He. subst f.
    iDestruct "Hn" as (name) "Hn".

    rewrite Heqadvm.
    iDestruct "Hinst_adv_res" as "(Hresf & Hrest & Hresm & Hresg) /=".
    rewrite /get_import_func_count
            /get_import_mem_count
            /get_import_table_count
            /get_import_global_count /=.
    rewrite !drop_0 -Heqadvm.
    rewrite nth_error_lookup in Hn.
    eapply Forall2_lookup_r in Hmod as [mf [Hmf Htypf]];[|eauto].
    destruct mf. simpl in Htypf.
    destruct modfunc_type. destruct Htypf as (Hlef & Hnthf & Htypf).
    revert Hlef. move/ssrnat.leP=>Hlef.
    assert (n0 < length mod_types) as Hlt;[lia|].
    rewrite Heqadvm /= in H.
    apply lookup_lt_is_Some in Hlt as [t Ht].
    rewrite - nth_error_lookup in Ht.
    erewrite nth_error_nth in Hnthf;eauto.
    revert Hnthf;move/eqP=>heq. subst t.
    iDestruct (big_sepL2_length with "Hresf") as %Hinstf_len.
    apply lookup_lt_Some in Hmf as Hlt'.
    rewrite Hinstf_len in Hlt'.
    apply lookup_lt_is_Some in Hlt' as [advf Hadv].
    iDestruct (big_sepL2_lookup_acc with "Hresf") as "[Hadvf Hcls]";[eauto..|].
    simpl.
    rewrite - nth_error_lookup in Hadv.
    rewrite H.
    erewrite !nth_error_nth;eauto.
    
    iDestruct "Hvis1" as (gr) "Hvis1".

    iApply (wp_wand_host _ _ _ (λ v, _ ∗ ↪[frame]empty_frame)%I with "[-HΦ] [HΦ]");cycle 1.
    { iIntros (v) "[Hv ?]". iApply "HΦ". iExact "Hv". }
    { iApply (instantiation_spec_operational_start with "[$Hmod_lse Hadvf Hgret Hn Hvis1]");[eauto|..].
      { apply lse_module_typing. }
      { unfold import_resources_host.
        instantiate (1:=[_;_]). iFrame "Hn Hvis1".
        unfold import_resources_wasm_typecheck,export_ownership_host.
        iSimpl. do 3 iSplit =>//.
        { instantiate (1:={[g_ret := {| g_mut := MUT_mut; g_val := wret |} ]}).
          instantiate (1:=∅).
          instantiate (1:=∅).
          instantiate (1:= {[N.of_nat advf := (FC_func_native inst_adv (Tf [] []) modfunc_locals modfunc_body)]}).
          iPureIntro. cbn. repeat split;auto.
          all: try rewrite N2Nat.id.
          all: rewrite dom_singleton_L;clear;set_solver.
        }
        { iSplitR "Hgret".
          { iExists _. iFrame. repeat iSplit;auto.
            iPureIntro. apply lookup_singleton. }
          { iSplit =>//. iExists _,_. rewrite N2Nat.id. iFrame. repeat iSplit;auto.
            iPureIntro. apply lookup_singleton.
            iPureIntro. cbn. rewrite Hgrettyp. done. }
        }
        { iSplit;auto.
          iSplit.
          { rewrite /module_elem_bound_check_gmap /=.
            iPureIntro. by apply Forall_nil. }
          { rewrite /module_data_bound_check_gmap /=.
            iPureIntro. by apply Forall_nil. }
        }
      }
      { iIntros (idnstart) "Hf Hr".
        iDestruct "Hr" as "(Hmod_lse & [Himph _] & [%Hdom [Himpr [Hgret _]]] & H)".
        iSimpl in "Himpr Hgret".
        iDestruct "Himpr" as (cl) "[Hcl %Hcl]". destruct Hcl as [Hlookcl Hcltyp].
        rewrite lookup_singleton in Hlookcl. inversion Hcltyp;inversion Hlookcl.
        iDestruct ("Hcls" with "Hcl") as "Hresf".
        iDestruct "Hgret" as (g gt) "(Hgret & %Hlookg & %Hgteq & %Hagree)".
        rewrite N2Nat.id lookup_singleton in Hlookg. inversion Hgteq;inversion Hlookg. rewrite N2Nat.id.
        
        iApply weakestpre.fupd_wp.
        iMod (interp_instance_alloc with "[] [] [] [] [Hrest Hresm Hresg Hresf]") as "[#Hi [#Hires _]]";
          [apply Htyp|repeat split;eauto|eauto|..].
        2,3,4: by instantiate (1:=∅).
        { rewrite Heqadvm /=. auto. }
        { instantiate (1:=∅). iSplit;auto. }
        { rewrite /module_inst_resources_wasm Heqadvm /=
                  /get_import_table_count
                  /get_import_mem_count
                  /get_import_global_count
                  /get_import_func_count /= !drop_0 -H.
          iFrame. }

        rewrite !app_nil_l.
        iDestruct (big_sepL2_lookup with "Hires") as "Ha".
        { rewrite Heqadvm /=. eauto. }
        { rewrite Heqadvm /= /get_import_func_count /= drop_0 /= -nth_error_lookup. eauto. }
        iSimpl in "Ha". erewrite H, nth_error_nth;eauto.

        iApply wp_host_wasm;[apply HWEV_invoke|]. iSimpl in "H".
        iDestruct "H" as (inst g_inits t_inits m_inits Hinst (Ht_inits & Hm_inits & (Heqg & Hg_inits))) "[Hlse _]".
        destruct g_inits;[|done].
        cbn in Hinst. destruct Hinst as (Hinst_typ & Hinst_f & _ & _ & Hinst_g & Hstart).
        destruct (inst_funcs inst) eqn:Hinstfuncseq;[done|].
        destruct l;[done|]. simpl in Hstart. revert Hstart. move/eqP =>Hstart. subst f0.
        destruct (inst_globs inst) eqn:Hinstglobseq;[by inversion Hinst_g|].
        simpl in Hinst_f, Hinst_g.
        apply prefix_cons_inv_1 in Hinst_f as Heq.
        apply prefix_cons_inv_1 in Hinst_g as Heq'. subst f g0.
        
        iDestruct "Hlse" as "[Hlsef [_ [Hlsem _]]]". iClear "Hmod_lse".
        
        rewrite /lse_module /get_import_func_count /get_import_mem_count /get_import_global_count !drop_0.
        iSimpl in "Hlsef Hlsem".
        rewrite Hinstfuncseq. iSimpl in "Hlsef".
        iDestruct "Hlsef" as "[Hidnstart _]".
        rewrite Hinst_typ. iSimpl in "Hidnstart".
        clear Hdom.
        iDestruct (big_sepL2_length with "Hlsem") as %Hinstmem_len.
        simpl in Hinstmem_len.
        destruct (inst_memory inst) eqn:Hinstmemeq;[done|].
        iDestruct "Hlsem" as "[Hm _]".
        
        take_drop_app_rewrite 0.
        iApply (wp_invoke_native with "Hf Hidnstart");[eauto|eauto..|].
        iModIntro. iNext. iIntros "[Hf Hidnstart]".
        iApply (wp_frame_bind with "Hf"). iIntros "Hf".
        take_drop_app_rewrite 0. iApply (wp_block with "Hf");[auto..|].
        iNext. iIntros "Hf".
        iApply wp_wasm_empty_ctx.
        iApply wp_label_push_nil.
        iApply wp_ctx_bind;[simpl;auto|]. repeat erewrite app_nil_l.

        iApply (wp_wand with "[Hf Hgret Hm Hown]").
        { iApply (lse_spec with "[$Hi $Hf $Hown $Ha Hgret Hm]");[by simpl|simpl..|].
          { rewrite Hinstmemeq;eauto. }
          { rewrite Hinstfuncseq;eauto. }
          { rewrite Hinstglobseq;eauto. }
          { unfold upd_local_label_return;simpl.
            rewrite Heqadvm /=. eauto. }
          { iSplitR "Hm". rewrite N2Nat.id. eauto.
            iDestruct "Hm" as "[Hm _]". iSimpl in "Hm".
            cbn in Hm_inits. rewrite Hm_inits.
            rewrite !lookup_empty.
            iDestruct "Hm" as "(Hm1 & Hm2 & Hm3 & Hm4 & _)". 
            iExists (Wasm_int.int_of_Z i32m 0).
            unfold serialise_i32. cbn. iFrame. done. }
          iIntros (w0) "Hw". iExact "Hw".
        }

        iIntros (wres) "[[-> | [-> [Hgret Hm]]] Hf]". 
        { iApply (wp_wand_ctx with "[Hf]").
          { take_drop_app_rewrite_twice 0 0. iApply (wp_trap_ctx with "Hf");auto. }
          iIntros (v) "[-> Hf]".
          iExists _. iFrame "Hf".
          iIntros "Hf".
          iApply (wp_frame_trap with "Hf").
          iNext. by iLeft. }

        rewrite N2Nat.id. simpl of_val.

        iApply (wp_wand_ctx _ _ _ (λ v, ⌜v = immV []⌝ ∗ _)%I with "[Hf]").
        { iApply (wp_val_return with "Hf");auto.
          iIntros "Hf". iApply wp_value;eauto. done. }
        iIntros (v) "[-> Hf]".
        iExists _. iFrame "Hf".
        iIntros "Hf".
        iApply (wp_frame_value with "Hf");eauto.
      }
    }
    Unshelve. apply HWP.
  Qed.
  

End Examples_host.
