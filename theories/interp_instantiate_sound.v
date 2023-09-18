From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import interpreter_func instantiation_func instantiation_properties type_checker_reflects_typing instantiation_sound.
From Coq Require Import Program.

Lemma those_length {T: Type} (l1: list (option T)) l2:
  those l1 = Some l2 ->
  length l1 = length l2.
Proof.
  move: l2.
  rewrite - those_those0.
  induction l1 as [|x l1]; destruct l2 as [|y l2] => //=; destruct x => //=; move => Hthose.
  - by destruct (those0 l1) => //.
  - f_equal.
    destruct (those0 l1) eqn:Hthose0 => //=.
    apply IHl1.
    simpl in Hthose.
    injection Hthose as ->.
    by f_equal.
Qed.

Lemma those_spec {T: Type} (l1: list (option T)) l2:
  those l1 = Some l2 ->
  (forall i x, List.nth_error l2 i = Some x ->
          List.nth_error l1 i = Some (Some x)).
Proof.
Admitted.


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
Admitted.

Section Interp_instantiate.
  
Import EmptyHost.
Import Interpreter_func_extract.

Let instantiate := instantiate host_function_eqType host_instance.

Lemma external_type_checker_sound: forall s ext t,
  external_type_checker s ext t = true ->
  external_typing host_function_eqType s ext t.
Proof.
Admitted.

Lemma interp_alloc_sound: forall s m v_imps g_inits s' inst' v_exps',
  interp_alloc_module host_function_eqType s m v_imps g_inits = (s', inst', v_exps') ->
  alloc_module host_function_eqType s m v_imps g_inits (s', inst', v_exps').
Proof.
Admitted.

Print module_type_checker.

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

Qed.


(* TODO: soundness of extracted version. Does not affect the mechanisation itself. *)
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
(*
  (* It's actually a bad idea to split up the proofs given how they depend on each other. Instead it's better to just unfold everything. *)
  (* module_typing *)
  unfold module_type_checker in Hmodcheck.
  destruct m.
  destruct (gather_m_f_types mod_types mod_funcs) as [fts | ] eqn:Hmftypes => //;
  destruct (module_imports_typer mod_types mod_imports) eqn:Hmitypes => //.
  destruct (all _ _ && _ && _ && _ && _ && _ && _ ) eqn:Hallcond => //.
  destruct (module_exports_typer _ mod_exports) eqn:Hmexptypes => //.
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hstartcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hdatacheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Helemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hglobcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hmemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hfunccheck Htabcheck].
  
  injection Hmodcheck as ->->.
  
  
  Opaque type_checker.b_e_type_checker.
  unfold module_func_type_checker in Hfunccheck.

  simpl in *.

  match goal with
  | |- context [ module_typing ?m t_imps t_exps /\ _ ] =>
      assert (module_typing m t_imps t_exps) as Hmodtype
  end.
  {
    unfold module_typing.
    
              
  assert (module_typing _ t_imps t_exps).

  (* alloc_module *)
  unfold interp_alloc_module, instantiation_spec.interp_alloc_module in Halloc.
  destruct (instantiation_spec.alloc_funcs _ _ _) as [s1 ifs].
  destruct (instantiation_spec.alloc_tabs _ _ _) as [s2 its].
  destruct (instantiation_spec.alloc_mems _ _ _) as [s3 ims].
  destruct (instantiation_spec.alloc_globs _ _ _) as [s4 igs].
 *)
  Print module_typing.
  
  repeat split => //.
  - (* module_typing *)
    by apply module_type_checker_sound.
  - eapply Forall2_all2_impl; eauto.
    by apply external_type_checker_sound.
  - by apply interp_alloc_sound.
  - unfold instantiate_globals.
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
    eapply const_exprs_impl in Hconstexpr; [ | instantiate (1 := host_function_eqType); exact host_instance | by eauto].
    destruct Hconstexpr as [e [-> Hconst]].
    unfold const_expr in Hconst.
    destruct e => //.
    { (* get_global *)
      move/andP in Hconst.
      simpl in *.
      destruct Hconst as [Hlen Himps].
      destruct (ext_t_globs t_imps !! i) eqn:Himpslookup => //.
      destruct (run_step_with_measure _ _ _ _) as [ | | | | ???? Hred] eqn:Hrun => //.
      simpl in Hrun.
      destruct (es_is_trap es') => //.
      destruct (const_list es') eqn:Hconstlist => //; last by destruct (run_step_with_measure _ hs' s'0 f' es').
      destruct (split_vals_e es') eqn:Hsplit => //; simpl in Hglobinit.
      do 2 destruct l as [ | ? l] => //.
      injection Hglobinit as ->.
      specialize (const_split_vals es' Hconstlist) as Hsplitempty.
      rewrite Hsplit in Hsplitempty; simpl in Hsplitempty; subst l0.
      apply Relation_Operators.rt_step => /=.
      apply r_get_global => /=.
      apply split_vals_e_v_to_e_duality in Hsplit as ->.
      simpl in *.
      assert (sglob_val s (Build_instance nil nil nil nil (List.map (fun '(Mk_globalidx i) => i) (ext_globs v_imps))) i = Some gv) as Hsglob.
      { admit. }
      admit.
    }
    { (* const *)
      simpl in Hglobinit.
      injection Hglobinit as <-.
      simpl in *.
      by constructor.
    }
    Search all List.nth_error.
    admit.
  - clear - Helem. admit.
  - clear - Hdata. admit.
  - by unfold check_start.
Admitted.
