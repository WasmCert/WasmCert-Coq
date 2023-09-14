From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import interpreter_func instantiation_func instantiation_properties type_checker_reflects_typing.

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

  (* It's actually a bad idea to split up the proofs given how they depend on each other. Instead it's better to just unfold everything. *)
  (* module_typing *)
  unfold module_type_checker in Hmodcheck.
  destruct m.
  destruct (gather_m_f_types mod_types mod_funcs) eqn:Hmftypes => //;
  destruct (module_imports_typer mod_types mod_imports) eqn:Hmitypes => //.
  destruct (all _ _ && _ && _ && _ && _ && _ && _ ) eqn:Hallcond => //.
  destruct (module_exports_typer _ mod_exports) eqn:Hmexptypes => //.
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hstartcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hdatacheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Helemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hglobcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hmemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hfunccheck Htabcheck].

  unfold module_func_type_checker in Hfunccheck; simpl in Hfunccheck.

  (* alloc_module *)
  unfold interp_alloc_module, instantiation_spec.interp_alloc_module in Halloc.
  destruct (instantiation_spec.alloc_funcs _ _ _) as [s1 ifs].
  destruct (instantiation_spec.alloc_tabs _ _ _) as [s2 its].
  destruct (instantiation_spec.alloc_mems _ _ _) as [s3 ims].
  destruct (instantiation_spec.alloc_globs _ _ _) as [s4 igs].

  repeat split => //.
  - (* module_typing *)
    admit.
  - eapply Forall2_all2_impl; eauto.
    by apply external_type_checker_sound.
  - admit.
  - clear - Hglobinit.
    unfold instantiate_globals.
    unfold interp_get_v in Hglobinit.
    apply Forall2_spec; first by apply those_length in Hglobinit; rewrite length_is_size size_map in Hglobinit.
    move => n mglob gv Hnth1 Hnth2.
    eapply those_spec in Hglobinit; last by eauto.
    apply nth_error_map in Hglobinit as [? [Hnth3 Hglobinit]].
    rewrite Hnth1 in Hnth3; injection Hnth3 as <-.
    Search List.nth_error map.
    admit.
  - clear - Helem. admit.
  - clear - Hdata. admit.
  - by unfold check_start.
Admitted.
