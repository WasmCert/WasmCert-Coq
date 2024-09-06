(** Soundness of the executable instantiation wrt the relational version. **)
(** The main proof to be done is the algorithm for breaking circularities
    in the evaluation of various initialisers. **)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import interpreter_ctx instantiation_func instantiation_properties type_checker_reflects_typing.
From Coq Require Import Program.

Section Host.

Context `{ho: host}.
  
Lemma module_type_checker_sound: forall m t_imps t_exps,
  module_type_checker m = Some (t_imps, t_exps) ->
  module_typing m t_imps t_exps.
Proof.
  move => m t_imps t_exps Hmodcheck.
  unfold module_type_checker in Hmodcheck.
  destruct m.
  destruct (gather_m_f_types mod_types mod_funcs) as [fts | ] eqn:Hmftypes => //;
  destruct (module_imports_typer mod_types mod_imports) as [impts | ] eqn:Hmitypes => //.
  destruct (gather_m_e_types (ext_t_tables impts ++ map modtab_type mod_tables) mod_elems) as [ets | ] eqn:Hmetypes => //.
  destruct (gather_m_d_types (ext_t_mems impts ++ map modmem_type mod_mems) mod_datas) as [dts | ] eqn:Hmdtypes => //.
  destruct (all _ _ && _ && _ && _ && _ && _ && _ && _) eqn:Hallcond => //.
  destruct (module_exports_typer _ mod_exports) eqn:Hmexptypes => //.
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hnameunique].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hstartcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hdatacheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Helemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hglobalcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hmemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hfunccheck Htablecheck].
  unfold module_typing.
  injection Hmodcheck as ->->.
  
  exists fts, (map modtab_type mod_tables), (map modmem_type mod_mems), (gather_m_g_types mod_globals), ets, dts.
  repeat split => //.

  (* types *)
  { by apply Forall_spec => //. }
  
  (* funcs *)
  { clear - Hfunccheck Hmftypes hfc.
    unfold gather_m_f_types in Hmftypes.
    apply Forall2_spec => //; first by apply those_length in Hmftypes; rewrite List.length_map in Hmftypes.
    move => n mfunc [tx ty] Hfuncnth Hftsnth.
    eapply all_projection in Hfunccheck; eauto.
    eapply those_map_lookup in Hmftypes as [ft [Hmap Hnth]]; eauto.
    destruct mfunc, ft.
    unfold gather_m_f_type in Hmap.
    Opaque type_checker.b_e_type_checker.
    simpl in *.
    simplify_multieq.
    split => //.
    rewrite Hmap in Hfunccheck.
    remove_bools_options.
    split => //; last by apply/eqP.
    by apply/b_e_type_checker_reflects_typing.
  }
  (* tables *)
  { apply Forall2_spec => //; first by rewrite List.length_map.
    move => n mtable [tx ty] Htablenth Hftsnth.
    eapply all_projection in Htablecheck; eauto.
    simpl in *.
    unfold module_table_typing, module_table_type_checker in *; rewrite Htablecheck => /=.
    apply nth_error_map in Hftsnth as [mtab [??]].
    simplify_multieq.
    by apply/eqP.
  }
  (* memories *)
  { apply Forall2_spec => //; first by rewrite List.length_map.
    move => n mmem [tx ty] Hmemnth Hftsnth.
    eapply all_projection in Hmemcheck; eauto.
    simpl in *.
    unfold module_mem_typing, module_mem_type_checker in *; rewrite Hmemcheck => /=.
    apply nth_error_map in Hftsnth as [mtab [??]].
    simplify_multieq.
    by apply/eqP.
  }
  (* globals *)
  { clear -Hglobalcheck hfc.
    unfold gather_m_g_types.
    apply Forall2_spec; first by rewrite List.length_map.
    move => n mglob gt Hgnth Hmgnth.
    erewrite List.map_nth_error in Hmgnth; last by eauto.
    injection Hmgnth as <-.
    unfold module_global_typing.
    destruct mglob => /=.
    eapply all_projection in Hglobalcheck; eauto.
    unfold module_global_type_checker in Hglobalcheck.
    move/andP in Hglobalcheck; destruct Hglobalcheck as [? Hbet].
    repeat split => //.
    by move/b_e_type_checker_reflects_typing in Hbet.
  }
  (* elem *)
  { clear -Helemcheck Hmetypes hfc.
    unfold gather_m_e_types in Hmetypes.
    apply Forall2_spec => //; first by apply those_length in Hmetypes; rewrite List.length_map in Hmetypes.
    move => n x tref Hnthelem Hntht.
    eapply those_map_lookup in Hmetypes as [t [Hmap Hnth]]; eauto; simpl in *.
    simplify_multieq.
    eapply all_projection in Helemcheck; eauto.
    unfold module_elem_typing.
    unfold module_elem_type_checker in Helemcheck.
    destruct x; simpl in *.
    move/andP in Helemcheck; destruct Helemcheck as [Helemcheck Hmode].
    move/andP in Helemcheck; destruct Helemcheck as [Hconst Hbet].
    assert (t = modelem_type) as Hteq.
    { unfold gather_m_e_type in Hmap.
      destruct modelem_mode; simpl in *; try by inversion Hmap.
      by remove_bools_options.
    }
    subst t.
    repeat split => //.
    { apply Forall_spec.
      move => m be Hnth.
      split.
      - by eapply all_projection in Hconst; eauto.
      - eapply all_projection in Hbet; eauto.
        by move/b_e_type_checker_reflects_typing in Hbet.
    }
    { unfold module_elem_mode_checker in Hmode; destruct modelem_mode; simpl in * => //.
      remove_bools_options.
      eexists; split; first by eauto.
      destruct t0; repeat split => //.
      by move/b_e_type_checker_reflects_typing in H1.
    }
  }
  (* data *)
  { clear -Hdatacheck Hmdtypes hfc.
    unfold gather_m_d_types in Hmdtypes.
    apply Forall2_spec => //; first by apply those_length in Hmdtypes; rewrite List.length_map in Hmdtypes.
    move => n x tref Hnthdata Hntht.
    eapply those_map_lookup in Hmdtypes as [t [Hmap Hnth]]; eauto; simpl in *.
    simplify_multieq.
    eapply all_projection in Hdatacheck; eauto.
    unfold module_data_typing.
    unfold module_data_type_checker in Hdatacheck.
    destruct x; simpl in *.
    unfold module_data_mode_checker in Hdatacheck; destruct moddata_mode; simpl in * => //; try repeat split => //; remove_bools_options => //.
    eexists; split; first by eauto.
    repeat split => //.
    by move/b_e_type_checker_reflects_typing in H.
  }
  (* imports *)
  { clear - Hmitypes.
    unfold module_imports_typer in Hmitypes.
    apply Forall2_spec; first by apply those_length in Hmitypes; rewrite List.length_map in Hmitypes.
    move => n mi extt Hminth Htinth.
    eapply those_map_lookup in Hmitypes as [Htext [Hmap Hnth]]; eauto.
    simplify_multieq.
    destruct mi; simpl in *.
    unfold module_import_desc_typer in Hmap.
    unfold module_import_typing.
    destruct imp_desc; apply/eqP => /=; remove_bools_options => //; by rewrite eq_refl.
  }
  (* exports *)
  { clear - Hmexptypes.
    unfold module_exports_typer in Hmexptypes.
    apply Forall2_spec; first by apply those_length in Hmexptypes; rewrite List.length_map in Hmexptypes.
    move => n me extt Hmexpth Htexpth.
    eapply those_map_lookup in Hmexptypes as [Htext [Hmap Hnth]]; eauto.
    simplify_multieq.
    destruct me; simpl in *.
    unfold module_export_typer in Hmap.
    unfold module_export_typing.
    simpl in *.
    destruct modexp_desc => //=; remove_bools_options; unfold module_export_desc_typing => /=; rewrite Hoption; by apply/eqP.
  }
Qed.

Lemma external_type_checker_sound: forall s ext t,
  external_type_checker s ext = Some t ->
  external_typing s ext t.
Proof.
  move => s ext t Hextcheck.
  unfold external_type_checker in Hextcheck; move/eqP in Hextcheck.
  by destruct ext; destruct t => //; remove_bools_options; subst.
Qed.

Lemma interp_alloc_sound: forall s m v_imps g_inits r_inits s' inst,
  length g_inits = length m.(mod_globals) ->
  length r_inits = length m.(mod_elems) ->
  interp_alloc_module s m v_imps g_inits r_inits = (s', inst) ->
  alloc_module s m v_imps g_inits r_inits (s', inst).
Proof.
  move => s m v_imps g_inits r_inits s' inst Hgvs_len Hrvs_len Halloc.
  unfold interp_alloc_module in Halloc.
  unfold alloc_module; simpl in *.
  destruct (alloc_funcs _ _ _) as [s1 ifs] eqn:Hallocfuncs.
  destruct (alloc_tabs _ _) as [s2 its] eqn:Halloctabs.
  destruct (alloc_mems _ _) as [s3 ims] eqn:Hallocmems.
  destruct (alloc_globs _ _) as [s4 igs] eqn:Hallocglobs.
  destruct (alloc_elems _ _) as [s5 ies] eqn:Hallocelems.
  destruct (alloc_datas _ _) as [s6 ids] eqn:Hallocdatas.

  injection Halloc as <-<-.
  rewrite Hallocfuncs Halloctabs Hallocmems Hallocglobs Hallocelems Hallocdatas => /=.
  apply alloc_func_iota_N in Hallocfuncs.
  apply alloc_table_iota_N in Halloctabs.
  apply alloc_mem_iota_N in Hallocmems.
  apply alloc_global_iota_N in Hallocglobs; last assumption.
  apply alloc_elem_iota_N in Hallocelems; last assumption.
  apply alloc_data_iota_N in Hallocdatas.

  extract_premise.

  destruct s, s1, s2, s3, s4, s5, s6; simpl in *.
  subst.
  repeat rewrite List.length_map.
  by repeat rewrite eq_refl => /=.
Qed.

(* Breaking circularity: the global initialisers need to be well-typed under a
   context with only the imported globals added. *)
Lemma module_typecheck_glob_aux: forall m t_imps t_exps,
    module_type_checker m = Some (t_imps, t_exps) ->
    exists c, all (module_global_type_checker c) m.(mod_globals).
Proof.
  move => m t_imps t_exps.
  unfold module_type_checker.
  move => Hmodcheck.
  destruct m.
  remove_bools_options.
  simpl in *.
  by eexists; eauto.
Qed.

Lemma module_typecheck_elem_aux: forall m t_imps t_exps,
    module_type_checker m = Some (t_imps, t_exps) ->
    exists c, all (module_elem_type_checker c) m.(mod_elems).
Proof.
  move => m t_imps t_exps.
  unfold module_type_checker.
  move => Hmodcheck.
  destruct m.
  remove_bools_options.
  simpl in *.
  by eexists; eauto.
Qed.
  
Lemma interp_instantiate_imp_instantiate : forall hs hs' s m v_imps s_end inst exps,
  interp_instantiate hs s m v_imps = Some (hs', s_end, inst, exps) ->
  instantiate s m v_imps (s_end, inst, exps).
Proof.
  move => hs hs' s m v_imps s_end inst exps.
  unfold interp_instantiate, instantiate.
  move => Hinterp.
  destruct (module_type_checker m) as [[t_imps_mod t_exps] |] eqn:Hmodcheck => //.
  destruct (those _) as [t_imps | ] eqn:Hextcheck => //.
  destruct (all2 import_subtyping _ _) eqn:Hextsubtyping => //.
  destruct (get_global_inits _ _ (mod_globals m)) as [g_inits |] eqn:Hglobinit => //.
  destruct (get_elem_inits _ _ (mod_elems m)) as [r_inits |] eqn:Heleminit => //.
  destruct (interp_alloc_module s m v_imps g_inits r_inits) as [s' inst'] eqn:Halloc => //.
  injection Hinterp as <- <- Heq.

  exists t_imps_mod, t_imps, t_exps, hs, inst', g_inits, r_inits.

  (* Proving these first so they can be used in the reasoning for initialisers later *)
  assert (module_typing m t_imps_mod t_exps) as Hmodtype; first by apply module_type_checker_sound.
  
  assert (alloc_module s m v_imps g_inits r_inits (s', inst')) as Hallocmodule.
  { apply interp_alloc_sound => //.
    - by apply those_length in Hglobinit; rewrite length_is_size size_map -length_is_size in Hglobinit.
    - by apply those_length in Heleminit; rewrite length_is_size size_map -length_is_size in Heleminit.
  }
  
  assert (List.Forall2 (external_typing s) v_imps t_imps) as Hexttype.
  { apply Forall2_spec.
    - apply those_length in Hextcheck.
      by rewrite List.length_map in Hextcheck.
    - move => n vext text Hnthv Hntht.
      apply external_type_checker_sound.
      eapply those_map_lookup in Hextcheck as [text' [Hmap Hnth]]; eauto.
      by simplify_multieq.
  }
  
  assert (Hgvs_len : length g_inits = length m.(mod_globals)).
  {
    apply those_length in Hglobinit.
    rewrite length_is_size size_map in Hglobinit.
    by rewrite length_is_size.
  }
  
  assert (Hrvs_len : length r_inits = length m.(mod_elems)).
  {
    apply those_length in Heleminit.
    rewrite length_is_size size_map in Heleminit.
    by rewrite length_is_size.
  }

  (* store *)
  unfold interp_alloc_module in Halloc.
  destruct (alloc_funcs _ _ _) as [s1 ifs] eqn:Hallocfuncs.
  destruct (alloc_tabs _ _) as [s2 its] eqn:Halloctabs.
  destruct (alloc_mems _ _) as [s3 ims] eqn:Hallocmems.
  destruct (alloc_globs _ _) as [s4 igs] eqn:Hallocglobs.
  destruct (alloc_elems _ _) as [s5 ies] eqn:Hallocelems.
  destruct (alloc_datas _ _) as [s6 ids] eqn:Hallocdatas.

  injection Halloc as <- Heqinst.
  specialize (alloc_func_iota_N Hallocfuncs) as Hfuncaddrs.
  specialize (alloc_table_iota_N Halloctabs) as Htableaddrs.
  specialize (alloc_mem_iota_N Hallocmems) as Hmemaddrs.
  specialize (alloc_global_iota_N Hallocglobs Hgvs_len) as Hglobaladdrs.
  specialize (alloc_elem_iota_N Hallocelems Hrvs_len) as Helemaddrs.
  specialize (alloc_data_iota_N Hallocdatas) as Hdataaddrs.

  extract_premise.

  destruct s, s1, s2, s3, s4, s5, s6; simpl in *.
  repeat split => //.
  - (* subtyping *)
    by eapply Forall2_all2_impl; eauto.
  - (* global initialisers -- hardest case, since it's the main difference in the 
       executable version *)
    unfold instantiate_globals.
    apply Forall2_spec => //.
    move => n mglob gv Hnth1 Hnth2.
    eapply those_map_lookup in Hglobinit as [gi [Hmap Hnth]]; last by eauto.
    apply module_typecheck_glob_aux in Hmodcheck as [C Hmodcheck].
    unfold module_global_type_checker in Hmodcheck.
    eapply all_projection in Hmodcheck; eauto.
    destruct mglob.
    move/andP in Hmodcheck.
    destruct Hmodcheck as [Hconstexpr Hbetype].
    move/b_e_type_checker_reflects_typing in Hbetype.
    eapply const_exprs_impl in Hconstexpr; last by eauto.
    destruct Hconstexpr as [e [-> Hconst]].
    unfold const_expr in Hconst.
    destruct e => //; subst; simpl in Hmap.
    1,2,3: (* const_num/const_vec/ref_null *)
      injection Hmap as <-;
      simpl in *;
      simplify_multieq;
      by constructor.
    { (* ref_func *)
      remove_bools_options; simplify_multieq.
      by constructor; apply r_ref_func => /=.
    }
    { (* global_get *)
      remove_bools_options; simplify_multieq.
      constructor; apply r_global_get => /=.
      unfold sglob_val, sglob, sglob_ind in *; simpl in *.
      remove_bools_options.
      unfold lookup_N in *.
      by erewrite nth_error_app_Some; eauto.
    }
  - subst.
    unfold instantiate_elems.
    apply Forall2_spec => //.
    move => n melem vs Hnth1 Hnth2.
    eapply those_map_lookup in Heleminit as [ei [Hmap Hnth]]; last by eauto.
    apply module_typecheck_elem_aux in Hmodcheck as [C Hmodcheck].
    unfold module_elem_type_checker in Hmodcheck.
    eapply all_projection in Hmodcheck; eauto.
    destruct melem.
    move/andP in Hmodcheck; destruct Hmodcheck as [Hmodcheck Hmode].
    move/andP in Hmodcheck; destruct Hmodcheck as [Hconstexpr Hbetype].
    simplify_multieq.
    apply Forall2_spec => //=.
    + apply those_length in Hmap.
      by rewrite List.length_map in Hmap; simpl in Hmap.
    + move => i bes vref Hnthinit Hnthei.
      eapply all_projection in Hbetype; eauto.
      eapply all_projection in Hconstexpr; eauto.
      eapply those_map_lookup in Hmap as [vref' [Hmap Hnth']]; eauto.
      move/b_e_type_checker_reflects_typing in Hbetype.
      eapply const_exprs_impl in Hconstexpr; last by eauto.
      destruct Hconstexpr as [e [-> Hconst]].
      unfold const_expr in Hconst.
      destruct e => //; subst; simpl in Hmap.
      { (* ref_null *)
        injection Hmap as <-.
        simpl in *.
        simplify_multieq.
        by constructor.
      }
      { (* ref_func *)
        remove_bools_options; simplify_multieq.
        constructor => /=.
        unfold interp_get_vref in Hmap.
        simpl in Hmap; remove_bools_options.
        by apply r_ref_func.
      }
      { (* global_get *)
        unfold interp_get_vref in Hmap; simpl in Hmap.
        remove_bools_options; simplify_multieq; destruct v => //.
        injection Hmap as ->.
        constructor.
        replace (vref_to_e vref') with (v_to_e (VAL_ref vref')) => //.
        eapply r_global_get => /=.
        unfold sglob_val, sglob, sglob_ind in *; simpl in *.
        remove_bools_options.
        unfold lookup_N in *.
        by erewrite nth_error_app_Some; eauto.
      }
Qed.

End Host.
