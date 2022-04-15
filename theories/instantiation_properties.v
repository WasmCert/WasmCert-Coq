From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From ITree Require Import ITree.
From ITree Require ITreeFacts.
From Wasm Require Import list_extra datatypes datatypes_properties
                         interpreter binary_format_parser operations
                         typing opsem type_checker memory memory_list instantiation.
From Coq Require Import BinNat.

Section Host.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record_eq_dec := @store_record_eq_dec host_function.
Let store_record_eqType := @store_record_eqType host_function.

Local Canonical Structure name_eqType := Eval hnf in EqType name (seq_eqMixin _).

Let store_record := store_record host_function.
Let host_state := host_state host_instance.

Let store_typing := @store_typing host_function.

Let external_typing := @external_typing host_function.

Let executable_host := executable_host host_function.
Variable executable_host_instance : executable_host.
Let host_event := host_event executable_host_instance.

Let instantiate := instantiate host_function host_instance.
Let instantiate_simpl := instantiate_simpl host_function.
(*
Let tab_agree := @typing.tab_agree host_function.
*)
Inductive ext_typing_list: store_record -> seq module_export -> seq extern_t -> Prop :=
| ext_typing_list_nil: forall s,
    ext_typing_list s [::] [::]
| ext_typing_list_cons: forall s v_exp v_exps te tes,
    ext_typing_list s v_exps tes ->
    external_typing s (modexp_desc v_exp) te ->
    ext_typing_list s (v_exp :: v_exps) (te :: tes).

(*
Lemma instantiation_sound (s: store_record) m v_imps s' inst v_exps start:
  store_typing s ->
  instantiate s m v_imps ((s', inst, v_exps), start) ->
  (store_typing s') /\
  (exists C, inst_typing s' inst C) /\
  (exists tes, ext_typing_list s' v_exps tes) /\
  (pred_option (fun i => i < length s'.(s_funcs)) start).
  (* /\ store_extension s s' *)
Proof.
Admitted.

Let tab_agree := @tab_agree host_function.

Lemma tab_agree_aux s_funcs s_tables s_mems s_globals tab func:
  tab_agree {| s_funcs := s_funcs; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} tab ->
  tab_agree {| s_funcs := List.app s_funcs [:: func]; s_tables := s_tables; s_mems := s_mems;
               s_globals := s_globals |} tab .
Proof.
  rewrite /tab_agree /typing.tab_agree.
  move => Htb.
  destruct Htb as [Htable Hs_tables]; subst.
  constructor.
  - (* forall tabcl_agree (table_data tab) *)
    induction (table_data tab) as [| hd tl IH]; first by constructor.
    (* forall tabcl_agree hd :: tl *)
    inversion Htable as [| x y Hhd Htl]; subst.
    constructor.
    (* tabcl_agree hd *)
    destruct hd => //=. 
    rewrite /tabcl_agree in Hhd. simpl in Hhd.
    rewrite size_cat. by rewrite ltn_addr.
    (* forall tabcl_agree tl *)
    apply IH. exact Htl.
  - (* tabsize_agree table *)
    assumption.
Qed.

Let functions_agree := @functions_agree host_function.

Lemma functions_agree_aux s_funcs func f tf: 
  functions_agree s_funcs f tf ->
  functions_agree (List.app s_funcs [:: func]) f tf.
Proof.
  rewrite /functions_agree /typing.functions_agree.
  move/andP => [H1 H2]. move/eqP in H2.
  apply/andP. split.
  + (* f < length (s_funcs [::func])  *)
    rewrite List.app_length.
    by rewrite ltn_addr.
  + (* option_map cl_type (List.nth_error (s_funcs [::func]) f) == Some tf *)
    apply/eqP.
    rewrite <-H2.
    apply f_equal.
    apply List.nth_error_app1.
    by apply/ltP.
Qed.


Lemma all2_forward: forall A B (f1 f2 : A -> B -> bool) l1 l2,
  (forall a b, f1 a b -> f2 a b) ->
  (all2 f1 l1 l2 -> all2 f2 l1 l2).
Proof.
  move=> A B f1 f2. elim.
  - by case.
  - move=> h1 l1 IH. case=> //= h2 l2 E.
    move/andP => [H1 H2].
    apply/andP. split.
    + by apply E.
    + by apply IH => //=.
Qed.

Let cl_type_check_single := @cl_type_check_single host_function.

Lemma cl_type_check_single_aux1 s_funcs s_tables s_mems s_globals inst m_f func:
  cl_type_check_single {| s_funcs := s_funcs; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} func ->
  cl_type_check_single {| s_funcs := s_funcs ++ 
                                     [:: FC_func_native inst
                                         (List.nth match modfunc_type m_f with
                                            | Mk_typeidx n => n
                                            end (inst_types inst) (Tf [::] [::])) (modfunc_locals m_f) 
                                         (modfunc_body m_f)]; 
                          s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} func.
Proof.
  move => Hcl.
  destruct Hcl as [tf' Hcl_typing].
  exists tf'.
  destruct func as [i tf ts es | tf h].
  + (* cl_typing_native *)
    inversion Hcl_typing; subst.
    rename H4 into Hinst_typing. rename H8 into Hbe_typing.
    apply cl_typing_native
      with (C := C)
           (C' := upd_local_label_return C (tc_local C ++ t1s ++ ts) ([::t2s] ++ tc_label C) (Some t2s))
          => //=.
    destruct C.
    rewrite /inst_typing. simpl.
    rewrite /inst_typing in Hinst_typing. simpl in Hinst_typing.
    destruct tc_local => //=.
    destruct tc_label => //=.
    destruct tc_return => //=.
    destruct i.
    move/andP in Hinst_typing. destruct Hinst_typing as [Hinst_typing Hmem].
    move/andP in Hinst_typing. destruct Hinst_typing as [Hinst_typing Htab].
    move/andP in Hinst_typing. destruct Hinst_typing as [Hinst_typing Hglb].
    move/andP in Hinst_typing. destruct Hinst_typing as [Hty Hfunc].
    move/eqP in Hty; subst.
    apply/andP. split => //=.
    apply/andP. split => //=.
    apply/andP. split => //=.
    apply/andP. split => //=.
    eapply all2_forward.
    apply functions_agree_aux.
    by exact Hfunc.
  + (* cl_typing_host *)
    inversion Hcl_typing; subst.
    by apply cl_typing_host.
Qed.

Lemma store_typing_preserve_add_func : forall s_funcs s_tables s_mems s_globals inst m_f,
    store_typing
      {| s_funcs := s_funcs; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} ->
    (*
    add_func s _ _ ...
*)
    store_typing
      {| s_funcs :=
        List.app s_funcs
                 [:: FC_func_native
                     inst
                     (List.nth (match m_f.(modfunc_type) with | Mk_typeidx n => n end) inst.(inst_types) (Tf nil nil))
                     m_f.(modfunc_locals)
                     m_f.(modfunc_body)]
      ; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |}.
Proof.
  move=> s_funcs s_tables s_mems s_globals inst m_f HSTyping.
  Print store_typing.
  inversion HSTyping as [Hcl [ Htb Hmem ]].
  constructor.
  - (* cl_typing *)
    rewrite List.Forall_app.
    split.
    + (* forall cl_type_check_single s_funcs *) 
      apply List.Forall_forall => func Hin.
      rewrite -> List.Forall_forall in Hcl.
      apply cl_type_check_single_aux1.
      by apply Hcl.
    + (* cl_typing_check_single func *) {
        constructor => //=.
        remember (List.nth match modfunc_type m_f with
                           | Mk_typeidx n => n
                           end (inst_types inst) (Tf [::] [::])) as tf.
        exists tf.
        destruct tf as [t1s t2s]. Check List.map.  Search (N).
        remember ({| tc_types_t := inst.(inst_types);
                     tc_func_t := (List.map cl_type s_funcs) ++ [:: (Tf t1s t2s)];
                     tc_global := List.map (fun g => Build_global_type (g_mut g) (typeof (g_val g))) s_globals;
                     tc_table := List.map
                                 (fun t => {| tt_limits := {| lim_min := N.of_nat(tab_size t);
                                                              lim_max := Some (N.of_nat(t.(table_max_opt) + 1)) |};
                                              tt_elem_type := ELT_funcref |})
                                 s_tables;
                     tc_memory := List.map
                                  (fun m => {| lim_min := (mem_size m); lim_max := m.(mem_max_opt) |})
                                s_mems;
                     tc_local := nil;
                     tc_label := nil;
                    tc_return := None |}) as C.
        apply cl_typing_native with
          (C := C)
          (C' := upd_local_label_return C (tc_local C ++ t1s ++ (modfunc_locals m_f)) ([::t2s] ++ tc_label C) (Some t2s)) => //=.
        * (* inst_typing *)
          admit. admit.
          (*
          destruct inst. destruct C. simpl.
          destruct tc_local => //=.
          destruct tc_label => //=.
          destruct tc_return => //=.
          inversion HeqC; subst.
          destruct HeqC. 
          apply/andP. split.
          apply/andP. split.
          apply/andP. split.
          apply/andP. split => //=.
          -- (* functions_agree *) {
            admit.
          }
          -- (* globals_agree *) {
              rewrite /globals_agree.
              admit.
            }
*)
      }
  split.
  - (* tab_agree *)
    apply List.Forall_forall => tab Hin.
    rewrite -> List.Forall_forall in Htb.
    apply tab_agree_aux.
    by apply Htb.
  - (* mem_agree *)
    assumption.
Admitted.

Lemma instantiation_sound_aux s s0 mfuncs inst l acc:
  store_typing s ->
  (s0, l) =
           (let
            '(s', fas) :=
             List.fold_left
               (fun '(s, ys) (x : module_func)
                  => let '(s', y) := alloc_func host_function s x inst in (s', y :: ys))
               mfuncs (s, acc) in (s', List.rev fas)) ->
  store_typing s0.
Proof.
  generalize dependent s.
  generalize dependent acc.
  induction mfuncs => //; move => acc s HType H0.
  - simpl in H0.
    by inversion H0; subst.
  - simpl in H0.
    apply IHmfuncs in H0 => //.
    unfold add_func. 
    apply store_typing_preserve_add_func.
    by destruct s => //.
Qed.
*)

(*
Lemma instantiation_sound_simpl:  forall (s: store_record) m v_imps s' inst v_exps start,
  store_typing s ->
  instantiate_simpl s m v_imps ((s', inst, v_exps), start) ->
  (store_typing s').
  (* (exists C, inst_typing s' inst C) /\
  (exists tes, ext_typing_list s' v_exps tes) /\
  (pred_option (fun i => i < length s'.(s_funcs)) start).*)
  (* /\ store_extension s s' *)
Proof.
  move=> s m v_imps s' inst v_exps start HType HInst. inversion HInst.
  remember (alloc_funcs host_function s (mod_funcs m) inst) as psi.
  destruct psi.
  rewrite /alloc_funcs /alloc_Xs in Heqpsi.
  apply instantiation_sound_aux in Heqpsi => //.
  simpl in Heqpsi.
  move/andP in Heqpsi.
  destruct H0 as [Heqs Heqinst].
  move/eqP in Heqs; subst.
  move/eqP in Heqinst.
  apply instantiation_sound_aux in Heqpsi => //.
Qed.*)


Print alloc_funcs.

Print alloc_func.

Print module_func.

(* This is the key definition: we should really be able to tell what the allocated new function closures are from the information of alloc_funcs. However, we need to formulate this in a way that is convenient for the other parts of the proofs. *)
Definition alloc_funcs_new_closures (modfuncs: list module_func) (inst: instance) : list (function_closure host_function) :=
  List.map (fun (mf: module_func) => 
              (FC_func_native inst
                              (List.nth match mf.(modfunc_type) with
                                        | Mk_typeidx n => n
                                        end
                                        (inst.(inst_types)) (Tf [::] [::]))
                              mf.(modfunc_locals)
                              mf.(modfunc_body))) modfuncs.

(* Same for this, but this is easier to define -- we should also be able to tell what the allocated function indices are. *)
Definition alloc_funcs_new_indices (ws: store_record) (modfuncs: list module_func) : list funcidx.
Admitted.

Lemma alloc_func_ws_res modfuncs ws inst ws' l:
  (ws', l) = alloc_funcs host_function ws modfuncs inst ->
  ws'.(s_funcs) = ws.(s_funcs) ++ alloc_funcs_new_closures modfuncs inst /\
  ws'.(s_tables) = ws.(s_tables) /\
  ws'.(s_mems) = ws.(s_mems) /\
  ws'.(s_globals) = ws.(s_globals).
Proof.
  move: l ws' ws.
  induction modfuncs using List.rev_ind; move => l ws' ws Halloc => /=.
Admitted.
    
Lemma alloc_func_index_res modfuncs ws inst ws' l:
  (ws', l) = alloc_funcs host_function ws modfuncs inst ->
  l = alloc_funcs_new_indices ws modfuncs.
Proof.
Admitted.
  
Lemma alloc_func_sound s s' ifs mod_funcs mod_types fts inst t_context: 
  (s', ifs) = alloc_funcs host_function s mod_funcs inst ->
  List.Forall2 (module_func_typing t_context) mod_funcs fts ->
  t_context.(tc_func_t) = fts ->
  t_context.(tc_types_t) = mod_types ->
  inst.(inst_types) = mod_types ->
  inst.(inst_funcs) = List.map (fun '(Mk_funcidx i) => i) ifs ->
  store_typing s ->
  store_typing s'.
Proof.
  destruct inst, t_context.
  move => Halloc Hftstype ? ? ? ? Hstoretype; simpl in *; subst.
  
  (* Doing induction on mod_funcs is hard since we only have the module validity result for the original module. 
     Instead, note that we can explicitly evaluate what the new store s' is -- intuitively, it should only differ with the original store in the function component, where a few functions are appended. *)
  specialize (alloc_func_ws_res _ _ _ _ _ Halloc) as Hfuncres.
  specialize (alloc_func_index_res _ _ _ _ _ Halloc) as Hindexres.
  
  destruct Hfuncres as [Hfunc [Htab [Hmem Hglob]]].

  (* We have established a relationship between the new store and the old store without using fold_left. We now have to prove the rest. Some of the lemmas proven previously commented out for now) is applicable, but need to be in a more generalised form. *)

Admitted.

Definition module_restriction (m: module) : Prop :=
  m.(mod_tables) = [::] /\
  m.(mod_mems) = [::] /\
  m.(mod_globals) = [::] /\
  m.(mod_elem) = [::] /\
  m.(mod_data) = [::] /\
  m.(mod_start) = None /\
  m.(mod_imports) = [::] /\
  m.(mod_exports) = [::].

Lemma instantiation_sound_simpl:  forall (s: store_record) m v_imps s' inst v_exps start,
  store_typing s ->
  module_restriction m ->
  instantiate s m v_imps ((s', inst, v_exps), start) ->
  (store_typing s').
  (* (exists C, inst_typing s' inst C) /\
  (exists tes, ext_typing_list s' v_exps tes) /\
  (pred_option (fun i => i < length s'.(s_funcs)) start).*)
  (* /\ store_extension s s' *)
Proof.
  move => s m v_imps s' inst v_exps start HStoreType HRestr HInst.

  (* Extract the artificial constraints we're imposing on the module *)
  unfold module_restriction in HRestr.
  destruct m => /=.
  simpl in HRestr.
  destruct HRestr as [-> [-> [-> [-> [-> [-> [-> ->]]]]]]].

  unfold instantiate, instantiation.instantiate in HInst.
  destruct HInst as [t_imps [t_exps [hs' [s'_end [? [? [? [HModType [HImpType [HAllocModule H]]]]]]]]]].

  destruct H as [HInstGlob [HInstElem [HInstData [HBoundElem [HBoundData [HStart HStore]]]]]].
  simpl in *.

  (* There are a lot of hypotheses here, but almost all of them simplify to a trivial condition due to the current constraint on the module. *)

  (* HInstGlob *)
  unfold instantiate_globals in HInstGlob.
  simpl in HInstGlob.
  inversion HInstGlob; subst; clear HInstGlob.

  (* HInstElem *)
  unfold instantiate_elem in HInstElem.
  simpl in HInstElem.
  inversion HInstElem; subst; clear HInstElem.

  (* HInstData *)
  unfold instantiate_data in HInstData.
  simpl in HInstData.
  inversion HInstData; subst; clear HInstData.

  (* HBoundData *)
  unfold check_bounds_data in HBoundData.
  simpl in HBoundData.
  (* this is vacuously true. *)
  clear HBoundData.

  (* HBoundElem *)
  unfold check_bounds_elem in HBoundElem.
  simpl in HBoundElem.
  clear HBoundElem.

  (* HCheckStart *)
  unfold check_start in HStart.
  simpl in HStart.
  move/eqP in HStart; subst.

  (* HStore *)
  unfold init_mems, init_tabs in HStore.
  simpl in HStore.
  move/eqP in HStore; subst.

  (* HModType *)
  (* This is an important part -- it gives a lot of validity information of the function references. *)
  unfold module_typing in HModType.
  destruct HModType as [fts [gts [HFuncType [_ [_ [HGlobType [_ [_ [_ [HImpValid _]]]]]]]]]].
  simpl in *.
  inversion HGlobType; subst; clear HGlobType.
  inversion HImpValid; subst; clear HImpValid.
  repeat rewrite List.app_nil_r in HFuncType.

  (* We know v_imps is empty as well *)
  inversion HImpType; subst; clear HImpType.
  simpl in *.
  

  (* Now, extract information from alloc_module. *)
  remember (alloc_funcs host_function s mod_funcs inst) as s_ifs.
  destruct s_ifs as [s' ifs].
  destruct inst.
  repeat (move/andP in HAllocModule; destruct HAllocModule as [HAllocModule ?]).
  simpl in *.
  move/eqP in H; subst.
  move/eqP in H0; subst.
  move/eqP in H1; subst.
  move/eqP in H2; subst.
  move/eqP in H3; subst.
  move/eqP in H4; subst.
  move/eqP in HAllocModule; subst.
  repeat rewrite List.app_nil_r in Heqs_ifs.

  (* We've reached the original simplified version we want, but with a much better shape of the lemma now for future extension. *)

  by eapply alloc_func_sound; eauto => //.
  
 
Admitted.

