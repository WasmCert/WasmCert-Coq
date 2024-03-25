(** Soundness of the executable instantiation wrt the relational version. **)
(** The main proof to be done is the algorithm for breaking circularities
    in the evaluation of various initialisers. **)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import interpreter_ctx instantiation_func instantiation_properties type_checker_reflects_typing.
From Coq Require Import Program.

Lemma Forall2_all2_impl {X Y: Type} (f: X -> Y -> bool) (fprop: X -> Y -> Prop) l1 l2:
  (forall x y, f x y = true -> fprop x y) ->
  all2 f l1 l2 ->
  List.Forall2 fprop l1 l2.
Proof.
  move: l2.
  induction l1; destruct l2 => //=; move => Himpl Hall.
  move/andP in Hall; destruct Hall as [Hf Hall].
  constructor; last by apply IHl1.
  by apply Himpl.
Qed.

Section Host.

Context `{ho: host}.
  
Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                       (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).

Lemma module_type_checker_sound: forall m t_imps t_exps,
  module_type_checker m = Some (t_imps, t_exps) ->
  module_typing m t_imps t_exps.
Proof.
  move => m t_imps t_exps Hmodcheck.
  unfold module_type_checker in Hmodcheck.
  destruct m.
  destruct (gather_m_f_types mod_types mod_funcs) as [fts | ] eqn:Hmftypes => //;
  destruct (module_imports_typer mod_types mod_imports) as [impts | ] eqn:Hmitypes => //.
  destruct (gather_m_e_types (ext_t_tabs impts ++ map modtab_type mod_tables) mod_elems) as [ets | ] eqn:Hmetypes => //.
  destruct (gather_m_d_types (ext_t_mems impts ++ map modmem_type mod_mems) mod_datas) as [dts | ] eqn:Hmdtypes => //.
  destruct (all _ _ && _ && _ && _ && _ && _ && _ && _) eqn:Hallcond => //.
  destruct (module_exports_typer _ mod_exports) eqn:Hmexptypes => //.
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hnameunique].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hstartcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hdatacheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Helemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hglobcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hmemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hfunccheck Htabcheck].
  unfold module_typing.
  injection Hmodcheck as ->->.
  
  exists fts, (map modtab_type mod_tables), (map modmem_type mod_mems), (gather_m_g_types mod_globals), ets, dts.
  repeat split => //.

  (* types *)
  { by apply Forall_spec => //. }
  
  (* funcs *)
  { clear - Hfunccheck Hmftypes hfc.
    unfold gather_m_f_types in Hmftypes.
    apply Forall2_spec => //; first by apply those_length in Hmftypes; rewrite List.map_length in Hmftypes.
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
    by apply/b_e_type_checker_reflects_typing.
  }
  (* globals *)
  { clear -Hglobcheck hfc.
    unfold gather_m_g_types.
    apply Forall2_spec; first by rewrite List.map_length.
    move => n mglob gt Hgnth Hmgnth.
    erewrite List.map_nth_error in Hmgnth; last by eauto.
    injection Hmgnth as <-.
    unfold module_glob_typing.
    destruct mglob => /=.
    eapply all_projection in Hglobcheck; eauto.
    unfold module_global_type_checker in Hglobcheck.
    move/andP in Hglobcheck; destruct Hglobcheck as [? Hbet].
    repeat split => //.
    by move/b_e_type_checker_reflects_typing in Hbet.
  }
  (* elem *)
  { clear -Helemcheck Hmetypes hfc.
    unfold gather_m_e_types in Hmetypes.
    apply Forall2_spec => //; first by apply those_length in Hmetypes; rewrite List.map_length in Hmetypes.
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
    apply Forall2_spec => //; first by apply those_length in Hmdtypes; rewrite List.map_length in Hmdtypes.
    move => n x tref Hnthdata Hntht.
    eapply those_map_lookup in Hmdtypes as [t [Hmap Hnth]]; eauto; simpl in *.
    simplify_multieq.
    eapply all_projection in Hdatacheck; eauto.
    unfold module_data_typing.
    unfold module_data_type_checker in Hdatacheck.
    destruct x; simpl in *.
    unfold module_data_mode_checker in Hdatacheck; destruct moddata_mode; simpl in * => //.
    remove_bools_options.
    eexists; split; first by eauto.
    repeat split => //.
    by move/b_e_type_checker_reflects_typing in H.
  }
  (* imports *)
  { clear - Hmitypes.
    unfold module_imports_typer in Hmitypes.
    apply Forall2_spec; first by apply those_length in Hmitypes; rewrite List.map_length in Hmitypes.
    move => n mi extt Hminth Htinth.
    eapply those_map_lookup in Hmitypes as [Htext [Hmap Hnth]]; eauto.
    simplify_multieq.
    destruct mi; simpl in *.
    unfold module_import_desc_typer in Hmap.
    unfold module_import_typing.
    destruct imp_desc; apply/eqP => /=; by remove_bools_options.
  }
  (* exports *)
  { clear - Hmexptypes.
    unfold module_exports_typer in Hmexptypes.
    apply Forall2_spec; first by apply those_length in Hmexptypes; rewrite List.map_length in Hmexptypes.
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
  apply alloc_func_gen_addrs in Hallocfuncs.
  apply alloc_table_gen_addrs in Halloctabs.
  apply alloc_mem_gen_addrs in Hallocmems.
  apply alloc_global_gen_addrs in Hallocglobs; last assumption.
  apply alloc_elem_gen_addrs in Hallocelems; last assumption.
  apply alloc_data_gen_addrs in Hallocdatas.

  extract_premise.

  destruct s, s1, s2, s3, s4, s5, s6; simpl in *.
  subst.
  repeat rewrite List.map_length.
  by repeat rewrite eq_refl => /=.
Qed.

(* Breaking circularity: the global initialisers need to be well-typed under a
   context with only the imported globals added. *)
Lemma module_typecheck_glob_aux: forall m t_imps t_exps,
    module_type_checker m = Some (t_imps, t_exps) ->
 (*   let c' :=
      {|
        tc_types := [::];
        tc_funcs := [::];
        tc_tables := [::];
        tc_mems := [::];
        tc_globals := ext_t_globs t_imps;
        tc_elems := [::];
        tc_datas := [::];
        tc_locals := [::];
        tc_labels := [::];
        tc_return := None;
        tc_refs := [::]
      |} in*)
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

Lemma module_typecheck_data_aux: forall m t_imps t_exps,
    module_type_checker m = Some (t_imps, t_exps) ->
    exists c, all (module_data_type_checker c) m.(mod_datas).
Proof.
  move => m t_imps t_exps.
  unfold module_type_checker.
  move => Hmodcheck.
  destruct m.
  remove_bools_options.
  simpl in *.
  by eexists; eauto.
Qed.

(* A slightly difficult proof due to having to prove additional properties of the certified interpreter.
   Note that the reduction property can be obtained trivially, but any additional proofs on top are difficult.
   In this case, we're 'misusing' the interpreter (running with the technically 'wrong' store) and proving that 
   the result is still correct regardless -- therefore the predictable trouble here. *)
Lemma interp_get_v_sglob: forall hs s f j k,
    interp_get_v host_application_impl host_application_impl_correct hs s f [::BI_global_get j] = Some k ->
    sglob_val s f.(f_inst) j = Some k.
(*
Proof.
  move => hs s f j k Heval.
  unfold interp_get_v, run_multi_step_raw, interpreter_ctx.run_multi_step_raw in Heval.
  destruct (run_v_init_with_frame s f 1 _) eqn:Hrvi => //.
  cbn in Hrvi.
  injection Hrvi as <-.
  destruct (run_multi_step_ctx _ _) as [ | vs] eqn:Hrmsc => //.
  do 2 destruct vs => //.
  injection Heval as ->.
  unfold run_multi_step_ctx in Hrmsc.

  destruct (run_one_step_ctx _ _ _) as [? cfg Hred | hs' s' rvs <- <- Heqvs | hs' s' rvs n f' <- <- Heqvs | |] eqn:Hrosc => //.
  { destruct cfg as [[[hs0 ccs] sc] e].
    simpl in Hred.
    simpl in Hrosc.
    move: Hrosc.
    (* Coq's destruct has no clue on how to generalize the terms correctly. *)
    move: (@Logic.eq_refl (option value) (sglob_val s f.(f_inst) j)).
    case: {2 3} (sglob_val s f.(f_inst) j) => /=.

    - move => v Hsglob Heval.
      inversion Heval; subst; clear Heval.
      simpl in Hrmsc.
      inversion Hrmsc; subst.
      exact Hsglob.
      
    - move => ? Hcontra.
      by inversion Hcontra.
  }
  { inversion Hrmsc; subst.
    simpl in Heqvs.
    injection Heqvs as Heqv.
    symmetry in Heqv.
    by rewrite ve_inv in Heqv.
  }
  { inversion Hrmsc; subst.
    simpl in Heqvs.
    inversion Heqvs; subst.
    symmetry in H2.
    by rewrite ve_inv in H2.
  }
Qed.
    
Lemma interp_get_v_reduce: forall t hs s c f k bes,
    const_exprs c bes ->
    be_typing c bes (Tf [::] [::t]) ->
    interp_get_v host_application_impl host_application_impl_correct hs s f bes = Some k ->
    reduce_trans (hs, s, f, (to_e_list bes))
                 (hs, s, f, [::$V k]).
Proof.
  move => t hs s c f k bes Hconst Hbet Heval.
  eapply const_exprs_impl in Hconst; eauto.
  destruct Hconst as [be [-> Hconst]].
  unfold const_expr in Hconst.
  destruct be => //.
  1,2,3:
    unfold interp_get_v in Heval;
    simpl in Heval;
    injection Heval as <-;
    by constructor.
  { (* ref_func *)
    admit.
  }
  { (* global_get *) 
    apply interp_get_v_sglob in Heval.
    constructor.
    unfold reduce_tuple.
    by apply r_global_get.
  }
Admitted.
  
Lemma interp_instantiate_imp_instantiate : forall hs s m v_imps s_end inst exps,
  interp_instantiate host_application_impl host_application_impl_correct hs s m v_imps = Some (hs, s_end, inst, exps) ->
  instantiate s m v_imps (s_end, inst, exps).
Proof.
  move => hs s m v_imps s_end inst exps.
  unfold interp_instantiate, instantiate.
  move => Hinterp.
  destruct (module_type_checker m) as [[t_imps_mod t_exps] |] eqn:Hmodcheck => //.
  destruct (those _) as [t_imps | ] eqn:Hextcheck => //.
  destruct (all2 import_subtyping _ _) eqn:Hextsubtyping => //.
  destruct (get_global_inits _ _ _ _ _ (mod_globals m)) as [g_inits |] eqn:Hglobinit => //.
  destruct (get_elem_inits _ _ _ _ _ (mod_elems m)) as [r_inits |] eqn:Heleminit => //.
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
      by rewrite List.map_length in Hextcheck.
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
  specialize (alloc_func_gen_addrs _ _ _ _ _ Hallocfuncs) as Hfuncaddrs.
  specialize (alloc_table_gen_addrs _ _ _ _ Halloctabs) as Htableaddrs.
  specialize (alloc_mem_gen_addrs _ _ _ _ Hallocmems) as Hmemaddrs.
  specialize (alloc_global_gen_addrs _ _ _ _ _ Hallocglobs Hgvs_len) as Hglobaladdrs.
  specialize (alloc_elem_gen_addrs _ _ _ _ _ Hallocelems Hrvs_len) as Helemaddrs.
  specialize (alloc_data_gen_addrs _ _ _ _ Hallocdatas) as Hdataaddrs.

  extract_premise.

  destruct s, s1, s2, s3, s4, s5, s6; simpl in *.
(*
  rewrite Hallocfuncs Halloctabs Hallocmems Hallocglobs Hallocelems Hallocdatas in Hallocmodule.
  simpl in Hallocmodule; remove_bools_options.
*)
  repeat split => //.
  - (* subtyping *)
    by eapply Forall2_all2_impl; eauto.
(*  - (* store eq *)
    repeat rewrite List.map_length.
    by repeat rewrite eq_refl.*)
  - (* global initialisers -- hardest case, since it's the main difference in the 
       executable version *)
    simpl.
    unfold instantiate_globals.
    apply Forall2_spec; first by apply those_length in Hglobinit; rewrite length_is_size size_map in Hglobinit.
    move => n mglob gv Hnth1 Hnth2.
    eapply those_map_lookup in Hglobinit as [gi [Hmap Hnth]]; last by eauto.
    apply module_typecheck_glob_aux in Hmodcheck as [C Hmodcheck].
    unfold module_global_type_checker in Hmodcheck.
    eapply all_projection in Hmodcheck; eauto.
    destruct mglob.
    move/andP in Hmodcheck.
    destruct Hmodcheck as [Hconstexpr Hbetype].
    move/b_e_type_checker_reflects_typing in Hbetype.
    eapply interp_get_v_reduce; eauto.
    eapply const_exprs_impl in Hconstexpr; last by eauto.
    destruct Hconstexpr as [e [-> Hconst]].
    unfold const_expr in Hconst.
    apply interp
    destruct e => //.
    1,2,3: (* const_num/const_vec/ref_null *)
      unfold interp_get_v in Hmap;
      simpl in Hmap;
      injection Hmap as <-;
      simpl in *;
      simplify_multieq;
      by constructor.
    { (* ref_func *)
      unfold interp_get_v in Hmap; simpl in Hmap.
      
    }
    { (* get_global *)
      move/andP in Hconst.
      simpl in *.
      destruct Hconst as [Hlen Himps].
      destruct (ext_t_globs t_imps !! i) eqn:Himpslookup => //.
      apply interp_get_v_sglob in Hglobinit.
      constructor.
      apply r_get_global => /=.
      unfold sglob_val, sglob, sglob_ind in *.
      simpl in *.
      remove_bools_options.
      rewrite List.nth_error_map in Hoption.
      destruct ((ext_globs v_imps) !! i) as [[i0] | ] eqn:Hextv => //.
      eapply vt_imps_globs_lookup in Hexttype; eauto; last by apply external_typing_relate.
      destruct Hexttype as [n' [Hvimpslookup Htimpslookup]].
      injection Halloc as <-<-<-.
      simpl in *.
      rewrite List.nth_error_map List.nth_error_app1; last by apply nth_error_Some_length in Hextv.
      rewrite Hextv => /=.
      rewrite List.nth_error_app1; last by apply nth_error_Some_length in Hoption.
      by rewrite Hoption.
    }
  - clear - instantiate Hmodcheck Helem.
    unfold instantiate_elem.
    apply Forall2_spec.
    { apply those_length in Helem.
      by rewrite length_is_size size_map -length_is_size in Helem.
    }
    move => n melem k Helemlookup Hoff.
    eapply those_spec in Helem; eauto.
    rewrite List.nth_error_map Helemlookup in Helem.
    simpl in Helem.
    injection Helem as Helem.
    eapply module_typecheck_elem_aux in Hmodcheck.
    destruct Hmodcheck as [c Helemcheck].
    eapply all_projection in Helemcheck; eauto.
    unfold module_elem_type_checker in Helemcheck.
    destruct melem, modelem_table => /=.
    remove_bools_options.
    move/b_e_type_checker_reflects_typing in H2.
    unfold interp_get_i32 in Helem; remove_bools_options.
    destruct v => //; injection Helem as ->.
    by eapply interp_get_v_reduce; eauto.
  - clear - instantiate Hmodcheck Hdata.
    unfold instantiate_data.
    apply Forall2_spec.
    { apply those_length in Hdata.
      by rewrite length_is_size size_map -length_is_size in Hdata.
    }
    move => n mdata k Hdatalookup Hoff.
    eapply those_spec in Hdata; eauto.
    rewrite List.nth_error_map Hdatalookup in Hdata.
    simpl in Hdata.
    injection Hdata as Hdata.
    eapply module_typecheck_data_aux in Hmodcheck.
    destruct Hmodcheck as [c Hdatacheck].
    eapply all_projection in Hdatacheck; eauto.
    unfold module_data_type_checker in Hdatacheck.
    destruct mdata, moddata_data => /=.
    remove_bools_options.
    move/b_e_type_checker_reflects_typing in H1.
    unfold interp_get_i32 in Hdata; remove_bools_options.
    destruct v => //; injection Hdata as ->.
    by eapply interp_get_v_reduce; eauto.
  - by unfold check_start.
Qed.
 *)
Admitted.
End Host.
