(** Soundness of the executable instantiation wrt the relational version. **)
(** The main proof to be done is the algorithm for breaking circularities
    in the evaluation of various initialisers. **)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import interpreter_func instantiation_func instantiation_properties type_checker_reflects_typing instantiation_sound.
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

Lemma module_type_checker_sound: forall m t_imps t_exps,
  module_type_checker m = Some (t_imps, t_exps) ->
  module_typing m t_imps t_exps.
Proof.
  move => m t_imps t_exps Hmodcheck.
  unfold module_type_checker in Hmodcheck.
  destruct m.
  destruct (gather_m_f_types mod_types mod_funcs) as [fts | ] eqn:Hmftypes => //;
  destruct (module_imports_typer mod_types mod_imports) as [impts | ] eqn:Hmitypes => //.
  destruct (all _ _ && _ && _ && _ && _ && _ && _ ) eqn:Hallcond => //.
  destruct (module_exports_typer _ mod_exports) eqn:Hmexptypes => //.
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hstartcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hdatacheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Helemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hglobcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hmemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hfunccheck Htabcheck].
  simpl in *.
  unfold module_typing.
  injection Hmodcheck as ->->.
  
  exists fts, (gather_m_g_types mod_globals).
  repeat split => //.
  
  (* funcs *)
  { clear - Hfunccheck Hmftypes.
    unfold gather_m_f_types in Hmftypes.
    apply Forall2_spec; first by apply those_length in Hmftypes; rewrite List.map_length in Hmftypes.
    move => n mfunc tf Hfuncnth Hftsnth.
    eapply all_projection in Hfunccheck; eauto.
    eapply those_spec in Hmftypes; eauto.
    rewrite List.nth_error_map in Hmftypes.
    destruct (mod_funcs !! n) as [mf |] eqn:Hmfnth => //.
    destruct mfunc, modfunc_type, mf, modfunc_type.
    unfold gather_m_f_type in Hmftypes.
    Opaque type_checker.b_e_type_checker.
    simpl in *.
    destruct (n1 < length mod_types) eqn:Hlt => //.
    injection Hmftypes as Hmtnth.
    injection Hfuncnth as ->->->.
    rewrite Hlt Hmtnth in Hfunccheck.
    move/andP in Hfunccheck; destruct Hfunccheck as [_ Hfunccheck].
    destruct tf as [tn tm].
    move/b_e_type_checker_reflects_typing in Hfunccheck.
    repeat split => //.
    erewrite List.nth_error_nth; by eauto.
  }
  (* globals *)
  { clear -Hglobcheck.
    unfold gather_m_g_types.
    apply Forall2_spec; first by rewrite List.map_length.
    move => n mglob gt Hgnth Hmgnth.
    erewrite List.map_nth_error in Hmgnth; last by eauto.
    injection Hmgnth as <-.
    unfold module_glob_typing.
    destruct mglob => /=.
    eapply all_projection in Hglobcheck; eauto.
    unfold module_glob_type_checker in Hglobcheck.
    move/andP in Hglobcheck; destruct Hglobcheck as [? Hbet].
    by move/b_e_type_checker_reflects_typing in Hbet.
  }
  (* elem *)
  { clear -Helemcheck.
    apply Forall_spec.
    move => n x Hnth.
    eapply all_projection in Helemcheck; eauto.
    unfold module_elem_typing.
    unfold module_elem_type_checker in Helemcheck.
    destruct x, modelem_table => /=.
    move/andP in Helemcheck; destruct Helemcheck as [Helemcheck Hinit].
    move/andP in Helemcheck; destruct Helemcheck as [Helemcheck Hlen].
    move/andP in Helemcheck; destruct Helemcheck as [Hconst Hbet].
    by move/b_e_type_checker_reflects_typing in Hbet.
  }
  (* data *)
  { clear -Hdatacheck.
    apply Forall_spec.
    move => n x Hnth.
    eapply all_projection in Hdatacheck; eauto.
    unfold module_data_typing.
    unfold module_data_type_checker in Hdatacheck.
    destruct x, moddata_data => /=.
    move/andP in Hdatacheck; destruct Hdatacheck as [Hdatacheck Hinit].
    move/andP in Hdatacheck; destruct Hdatacheck as [Hconst Hbet].
    by move/b_e_type_checker_reflects_typing in Hbet.
  }
  (* imports *)
  { clear - Hmitypes.
    unfold module_imports_typer in Hmitypes.
    apply Forall2_spec; first by apply those_length in Hmitypes; rewrite List.map_length in Hmitypes.
    move => n mi extt Hminth Htinth.
    eapply those_spec in Hmitypes; eauto.
    rewrite List.nth_error_map in Hmitypes.
    rewrite Hminth in Hmitypes.
    simpl in Hmitypes.
    destruct mi; simpl in *.
    injection Hmitypes as Hmitypes.
    unfold module_import_typer in Hmitypes.
    unfold module_import_typing.
    destruct imp_desc => //=.
    (* func *)
    { destruct (n0 < length mod_types) eqn:Hlt => //.
      destruct (mod_types !! n0) eqn:Hmtnth => //.
      injection Hmitypes as <-.
      by apply/andP.
    }
    (* tab *)
    { destruct (module_tab_typing _) eqn:Hmtt => //.
      injection Hmitypes as <-.
      by apply/andP.
    }
    (* mem *)
    { destruct (module_mem_typing _) eqn:Hmtt => //.
      injection Hmitypes as <-.
      by apply/andP.
    }
    (* glob *)
    { by injection Hmitypes as <-. }
  }
  (* exports *)
  { clear - Hmexptypes.
    unfold module_exports_typer in Hmexptypes.
    apply Forall2_spec; first by apply those_length in Hmexptypes; rewrite List.map_length in Hmexptypes.
    move => n me extt Hmexpth Htexpth.
    eapply those_spec in Hmexptypes; eauto.
    rewrite List.nth_error_map in Hmexptypes.
    rewrite Hmexpth in Hmexptypes.
    simpl in Hmexptypes.
    destruct me; simpl in *.
    injection Hmexptypes as Hmexptypes.
    unfold module_export_typer in Hmexptypes.
    unfold module_export_typing.
    simpl in *.
    destruct modexp_desc => //=.
    (* func *)
    { destruct f => /=.
      destruct (n0 < _) eqn:Hlt => //.
      destruct (_ !! n0) eqn:Hnth => //.
      injection Hmexptypes as <-.
      by apply/andP.
    }
    (* tab *)
    { destruct t.
      destruct (n0 < _) eqn:Hlt => //.
      destruct (_ !! n0) eqn:Hnth => //.
      injection Hmexptypes as <-.
      by apply/andP.
    }
    (* mem *)
    { destruct m.
      destruct (n0 < _) eqn:Hlt => //.
      destruct (_ !! n0) eqn:Hnth => //.
      injection Hmexptypes as <-.
      by apply/andP.
    }
    (* glob *)
    { destruct g.
      destruct (n0 < _) eqn:Hlt => //.
      destruct (_ !! n0) eqn:Hnth => //.
      injection Hmexptypes as <-.
      by apply/andP.
    }
  }
Qed.

Section Interp_instantiate.
  
Import EmptyHost.
Import Interpreter_func_extract.

Let instantiate := instantiate host_function_eqType host_instance.

Lemma external_type_checker_sound: forall s ext t,
  external_type_checker s ext t = true ->
  external_typing host_function_eqType s ext t.
Proof.
  move => s ext t Hextcheck.
  unfold external_type_checker in Hextcheck.
  destruct ext as [[i] | [i] | [i] | [i]]; destruct t => //; remove_bools_options; subst.
  - by eapply ETY_func; eauto.
  - by eapply ETY_tab; eauto.
  - by eapply ETY_mem; eauto.
  - by eapply ETY_glob; eauto.
Qed.

Lemma interp_alloc_sound: forall s m v_imps g_inits s' inst' v_exps',
  length g_inits = length m.(mod_globals) ->
  interp_alloc_module host_function_eqType s m v_imps g_inits = (s', inst', v_exps') ->
  alloc_module host_function_eqType s m v_imps g_inits (s', inst', v_exps').
Proof.
  move => s m v_imps g_inits s' inst' v_exps' Hgvs_len Halloc.
  unfold interp_alloc_module in Halloc.
  unfold alloc_module.
  destruct (alloc_funcs _ _ _ _) as [s1 ifs] eqn:Hallocfuncs.
  destruct (alloc_tabs _ _ _) as [s2 its] eqn:Halloctabs.
  destruct (alloc_mems _ _ _) as [s3 ims] eqn:Hallocmems.
  destruct (alloc_globs _ _ _) as [s4 igs] eqn:Hallocglobs.

  injection Halloc as <-<-<-.
  rewrite Hallocfuncs Halloctabs Hallocmems Hallocglobs => /=.
  apply alloc_func_gen_index in Hallocfuncs.
  apply alloc_tab_gen_index in Halloctabs.
  apply alloc_mem_gen_index in Hallocmems.
  
  apply alloc_glob_gen_index in Hallocglobs; last assumption.

  destruct Hallocfuncs as [Hifs [Hfunc1 [Htab1 [Hmem1 Hglob1]]]]; simpl in *.
  destruct Halloctabs as [Hits [Htab2 [Hfunc2 [Hmem2 Hglob2]]]]; simpl in *.
  destruct Hallocmems as [Hims [Hmem3 [Hfunc3 [Htab3 Hglob3]]]]; simpl in *.
  destruct Hallocglobs as [Higs [Hglob4 [Hfunc4 [Htab4 Hmem4]]]]; simpl in *.

  destruct s, s1, s2, s3, s4; simpl in *.
  rewrite <- Hfunc4 in *. rewrite <- Hfunc3 in *. rewrite <- Hfunc2 in *. rewrite -> Hfunc1 in *.
  rewrite <- Htab4 in *. rewrite <- Htab3 in *. rewrite -> Htab2 in *. rewrite <- Htab1 in *.
  rewrite <- Hmem4 in *. rewrite -> Hmem3 in *. rewrite <- Hmem2 in *. rewrite <- Hmem1 in *.
  rewrite -> Hglob4 in *. rewrite <- Hglob3 in *. rewrite <- Hglob2 in *. rewrite <- Hglob1 in *.
  rewrite gen_index_iota in Hifs.
  rewrite List.map_length gen_index_iota in Hits.
  rewrite gen_index_iota in Hims.
  rewrite gen_index_iota in Higs.
  repeat (apply/andP; split => //).
  - rewrite - Hifs => /=.
    apply/eqP; repeat f_equal.
    clear.
    by induction ifs as [ | a ?] => //=; destruct a; f_equal => //.
  - rewrite - Hits => /=.
    apply/eqP; repeat f_equal.
    clear.
    by induction its as [ | a ?] => //=; destruct a; f_equal => //.
  - rewrite - Hims => /=.
    apply/eqP; repeat f_equal.
    clear.
    by induction ims as [ | a ?] => //=; destruct a; f_equal => //.
  - rewrite Hgvs_len PeanoNat.Nat.min_id -Higs => /=.
    apply/eqP; repeat f_equal.
    clear.
    by induction igs as [ | a ?] => //=; destruct a; f_equal => //.
Qed.

(* Breaking circularity: the global initialisers need to be well-typed under a
   context with only the imported globals added. *)
Lemma module_typecheck_glob_aux: forall m t_imps t_exps,
    module_type_checker m = Some (t_imps, t_exps) ->
    let c' :=
      {|
        tc_types_t := [::];
        tc_func_t := [::];
        tc_global := ext_t_globs t_imps;
        tc_table := [::];
        tc_memory := [::];
        tc_local := [::];
        tc_label := [::];
        tc_return := None
      |} in
    all (module_glob_type_checker c') m.(mod_globals).
Proof.
  move => m t_imps t_exps.
  unfold module_type_checker.
  move => Hmodcheck.
  destruct m.
  destruct (gather_m_f_types mod_types mod_funcs) as [fts | ] eqn:Hmftypes => //;
  destruct (module_imports_typer mod_types mod_imports) eqn:Hmitypes => //.
  destruct (all _ _ && _ && _ && _ && _ && _ && _ ) eqn:Hallcond => //.
  destruct (module_exports_typer _ mod_exports) eqn:Hmexptypes => //.
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hstartcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hdatacheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Helemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hglobcheck].
  simpl in *.
  by injection Hmodcheck as ->->.
Qed.

Lemma module_typecheck_elem_aux: forall m t_imps t_exps,
    module_type_checker m = Some (t_imps, t_exps) ->
    exists c, all (module_elem_type_checker c) m.(mod_elem).
Proof.
  move => m t_imps t_exps.
  unfold module_type_checker.
  move => Hmodcheck.
  destruct m.
  destruct (gather_m_f_types mod_types mod_funcs) as [fts | ] eqn:Hmftypes => //;
  destruct (module_imports_typer mod_types mod_imports) eqn:Hmitypes => //.
  destruct (all _ _ && _ && _ && _ && _ && _ && _ ) eqn:Hallcond => //.
  destruct (module_exports_typer _ mod_exports) eqn:Hmexptypes => //.
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hstartcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hdatacheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Helemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hglobcheck].
  simpl in *.
  by eexists; apply Helemcheck.
Qed.

Lemma module_typecheck_data_aux: forall m t_imps t_exps,
    module_type_checker m = Some (t_imps, t_exps) ->
    exists c, all (module_data_type_checker c) m.(mod_data).
Proof.
  move => m t_imps t_exps.
  unfold module_type_checker.
  move => Hmodcheck.
  destruct m.
  destruct (gather_m_f_types mod_types mod_funcs) as [fts | ] eqn:Hmftypes => //;
  destruct (module_imports_typer mod_types mod_imports) eqn:Hmitypes => //.
  destruct (all _ _ && _ && _ && _ && _ && _ && _ ) eqn:Hallcond => //.
  destruct (module_exports_typer _ mod_exports) eqn:Hmexptypes => //.
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hstartcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hdatacheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Helemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hglobcheck].
  simpl in *.
  by eexists; apply Hdatacheck.
Qed.

Lemma const_split_vals: forall es,
    const_list es ->
    snd (split_vals_e es) = nil.
Proof.
  induction es => //; move => Hconst => /=.
  simpl in Hconst; move/andP in Hconst; destruct Hconst as [Hconst Hconstes].
  destruct a => //=.
  destruct b => //=.
  destruct (split_vals_e es) eqn:Hsplit => //=.
  by apply IHes in Hconstes.
Qed.

Lemma reduce_get_globs {hf hi}: forall hs s f i hs' s' f' v,
    @reduce hf hi hs s f [::AI_basic (BI_get_global i)] hs' s' f' [::AI_basic (BI_const v)] ->
    sglob_val s f.(f_inst) i = Some v.
Proof.
  move => hs s f i hs' s' f' v' Hred.
  dependent induction Hred; subst => //.
  - by inversion H.
  - by do 2 destruct vcs as [| ? vcs] => //.
  - by do 2 destruct vcs as [| ? vcs] => //.
  - move/lfilledP in H.
    move/lfilledP in H0.
    inversion H; inversion H0; subst; clear H; clear H0; try by destruct k0.
    2: { by do 2 destruct vs as [| ? vs] => //. }
    injection H8 as ->; subst.
    destruct vs as [ | a ?] => //; last by destruct a; try by destruct b => //.
    destruct es, es'; simpl in *; subst => //.
    { by destruct es'. }
    { by destruct es. }
    destruct es, es', es'0 => //.
    simpl in *.
    injection H1 as ->.
    injection H6 as ->.
    by apply IHHred.
Qed.

Lemma interp_get_i32_reduce: forall hs s c inst k bes,
    const_exprs c bes ->
    be_typing c bes (Tf [::] [::T_i32]) ->
    interp_get_i32 s inst bes = Some k ->
    @reduce_trans host_function_eqType host_instance (hs, s, (Build_frame nil inst), (to_e_list bes))
                 (hs, s, (Build_frame nil inst), [::AI_basic (BI_const (VAL_int32 k))]).
Proof.
  move => hs s c inst bes k Hconst Hbet Heval.
  unfold interp_get_i32, interp_get_v in Heval.
  eapply const_exprs_impl in Hconst; eauto.
  destruct Hconst as [be [-> Hconst]].
  destruct be => //=.
  - simpl in Heval.
    destruct (interpreter_func.run_step _ _ _ _) as [ | | | | ???? Hred] => //.
    constructor.
    unfold reduce_tuple.
    destruct (es_is_trap es') => //.
    destruct (const_list es') eqn:Hconstlist => //; last by destruct (interpreter_func.run_step _ hs' s' f' es').
    destruct (split_vals_e es') eqn:Hsplit => //; simpl in Heval.
    do 2 destruct l as [ | ? l] => //.
    destruct v => //.
    injection Heval as ->.
    specialize (const_split_vals es' Hconstlist) as Hsplitempty.
    rewrite Hsplit in Hsplitempty; simpl in Hsplitempty; subst l0.
    apply split_vals_e_v_to_e_duality in Hsplit as ->.
    simpl in Hred.
    apply reduce_get_globs in Hred.
    by apply r_get_global.
  - simpl in Heval.
    destruct v => //=.
    injection Heval as ->.
    by constructor.
Qed.

Lemma interp_instantiate_imp_instantiate :
  forall s m v_imps s_end inst v_exps start,
  interp_instantiate s m v_imps = Some ((s_end, inst, v_exps), start) ->
  instantiate s m v_imps ((s_end, inst, v_exps), start).
Proof.
  move => s m v_imps s_end inst v_exps start.
  unfold interp_instantiate, instantiate, instantiation_spec.instantiate.
  move => Hinterp.
  destruct (module_type_checker m) as [[t_imps t_exps] |] eqn:Hmodcheck => //.
  destruct (all2 (external_type_checker s) v_imps t_imps) eqn:Hextcheck => //.
  destruct (those (map _ (mod_globals m))) as [g_inits |] eqn:Hglobinit => //.
  destruct (interp_alloc_module _ s m v_imps g_inits) as [[s' inst'] v_exps'] eqn:Halloc => //.
  destruct (those (map _ (mod_elem m))) as [e_offs | ] eqn:Helem => //.
  destruct (those (map _ (mod_data m))) as [d_offs | ] eqn:Hdata => //.
  destruct (check_bounds_elem _ _ _ _ _ && check_bounds_data _ _ _ _ _) eqn:Hbounds => //.
  move/andP in Hbounds.
  destruct Hbounds as [Helembounds Hdatabounds].
  injection Hinterp as <-<-<-<-.


  exists t_imps, t_exps, tt, s', g_inits, e_offs, d_offs.

  (* Proving these first so they can be used in the reasoning for initialisers later *)
  assert (module_typing m t_imps t_exps) as Hmodtype; first by apply module_type_checker_sound.
  
  assert (alloc_module _ s m v_imps g_inits (s', inst', v_exps')) as Hallocmodule; first by apply interp_alloc_sound; apply those_length in Hglobinit; rewrite length_is_size size_map -length_is_size in Hglobinit.
  
  assert (List.Forall2 (external_typing _ s) v_imps t_imps) as Hexttype; first by eapply Forall2_all2_impl; eauto; by apply external_type_checker_sound.
  
  (* alloc_module *)
  unfold interp_alloc_module, instantiation_spec.interp_alloc_module in Halloc.
  destruct (instantiation_spec.alloc_funcs _ _ _) as [s1 ifs] eqn:Hallocfuncs.
  destruct (instantiation_spec.alloc_tabs _ _ _) as [s2 its] eqn:Halloctabs.
  destruct (instantiation_spec.alloc_mems _ _ _) as [s3 ims] eqn:Hallocmems.
  destruct (instantiation_spec.alloc_globs _ _ _) as [s4 igs] eqn:Hallocglobs.

  apply alloc_func_gen_index in Hallocfuncs.
  apply alloc_tab_gen_index in Halloctabs.
  apply alloc_mem_gen_index in Hallocmems.
  
  assert (Hgvs_len : length g_inits = length m.(mod_globals)).
  {
    apply those_length in Hglobinit.
    rewrite length_is_size size_map in Hglobinit.
    by rewrite length_is_size.
  }
  apply alloc_glob_gen_index in Hallocglobs; last assumption.

  destruct Hallocfuncs as [Hfunidx [Hfunc1 [Htab1 [Hmem1 Hglob1]]]]; simpl in *.
  destruct Halloctabs as [Htabidx [Htab2 [Hfunc2 [Hmem2 Hglob2]]]]; simpl in *.
  destruct Hallocmems as [Hmemidx [Hmem3 [Hfunc3 [Htab3 Hglob3]]]]; simpl in *.
  destruct Hallocglobs as [Hglobidx [Hglob4 [Hfunc4 [Htab4 Hmem4]]]]; simpl in *.

  destruct s, s1, s2, s3, s4; simpl in *.
  rewrite <- Hfunc4 in *. rewrite <- Hfunc3 in *. rewrite <- Hfunc2 in *. rewrite -> Hfunc1 in *.
  rewrite <- Htab4 in *. rewrite <- Htab3 in *. rewrite -> Htab2 in *. rewrite <- Htab1 in *.
  rewrite <- Hmem4 in *. rewrite -> Hmem3 in *. rewrite <- Hmem2 in *. rewrite <- Hmem1 in *.
  rewrite -> Hglob4 in *. rewrite <- Hglob3 in *. rewrite <- Hglob2 in *. rewrite <- Hglob1 in *.
  
  repeat split => //.
  - (* global initialisers -- hardest case, since it's the main difference in the 
       executable version *)
    unfold instantiate_globals.
    unfold interp_get_v in Hglobinit.
    apply Forall2_spec; first by apply those_length in Hglobinit; rewrite length_is_size size_map in Hglobinit.
    move => n mglob gv Hnth1 Hnth2.
    eapply those_spec in Hglobinit; last by eauto.
    apply nth_error_map in Hglobinit as [? [Hnth3 Hglobinit]].
    rewrite Hnth1 in Hnth3; injection Hnth3 as <-.
    apply module_typecheck_glob_aux in Hmodcheck.
    eapply all_projection in Hmodcheck; last by apply Hnth1.
    unfold module_glob_type_checker in Hmodcheck.
    destruct mglob.
    move/andP in Hmodcheck.
    destruct Hmodcheck as [Hconstexpr Hbetype].
    move/b_e_type_checker_reflects_typing in Hbetype.
    eapply const_exprs_impl in Hconstexpr; last by eauto.
    destruct Hconstexpr as [e [-> Hconst]].
    unfold const_expr in Hconst.
    destruct e => //.
    { (* get_global *)
      move/andP in Hconst.
      simpl in *.
      destruct Hconst as [Hlen Himps].
      destruct (ext_t_globs t_imps !! i) eqn:Himpslookup => //.
      destruct (interpreter_func.run_step _ _ _ _) as [ | | | | ???? Hred] => //.
      destruct (es_is_trap es') => //.
      destruct (const_list es') eqn:Hconstlist => //; last by destruct (interpreter_func.run_step _ hs' s'0 f' es').
      destruct (split_vals_e es') eqn:Hsplit => //; simpl in Hglobinit.
      do 2 destruct l as [ | ? l] => //.
      injection Hglobinit as ->.
      specialize (const_split_vals es' Hconstlist) as Hsplitempty.
      rewrite Hsplit in Hsplitempty; simpl in Hsplitempty; subst l0.
      apply Relation_Operators.rt_step => /=.
      apply r_get_global => /=.
      apply split_vals_e_v_to_e_duality in Hsplit as ->.
      apply reduce_get_globs in Hred.
      unfold sglob_val, sglob, sglob_ind in *.
      simpl in *.
      rewrite List.nth_error_map in Hred.
      destruct ((ext_globs v_imps) !! i) as [[i0] | ] eqn:Hextv => //.
      simpl in Hred.
      eapply vt_imps_globs_lookup in Hexttype; eauto; last by apply external_typing_relate.
      destruct Hexttype as [n' [Hvimpslookup Htimpslookup]].
      injection Halloc as <-<-<-.
      simpl in *.
      rewrite List.nth_error_map List.nth_error_app1; last by apply nth_error_Some_length in Hextv.
      rewrite Hextv => /=.
      destruct (s_globals !! i0) eqn:Hsglob => //.
      rewrite List.nth_error_app1; last by apply nth_error_Some_length in Hsglob.
      by rewrite Hsglob.
    }
    { (* const *)
      simpl in Hglobinit.
      injection Hglobinit as <-.
      simpl in *.
      by constructor.
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
    by eapply interp_get_i32_reduce; eauto.
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
    by eapply interp_get_i32_reduce; eauto.
  - by unfold check_start.
Qed.

End Interp_instantiate.
