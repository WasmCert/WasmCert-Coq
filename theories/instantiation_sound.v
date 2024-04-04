(** Several soundness properties of the relational instantiation. **)
(** Most notably, the post-instantiation store is a well-typed extension
    of the old store, and the generated module instance is well-typed in 
    that store. **)

From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat.
From Wasm Require Import instantiation_spec instantiation_properties type_preservation.
From Coq Require Import BinNat NArith ZArith.
Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Context `{ho: host}.

Lemma bet_import_subtyping: forall ts fts tts mts gts ets dts locs labs ret refs imps1 imps2 bes tf,
    List.Forall2 import_subtyping imps2 imps1 ->
    be_typing (Build_t_context ts (ext_t_funcs imps1 ++ fts) (ext_t_tables imps1 ++ tts) (ext_t_mems imps1 ++ mts) (ext_t_globals imps1 ++ gts) ets dts locs labs ret refs) bes tf ->
    be_typing (Build_t_context ts (ext_t_funcs imps2 ++ fts) (ext_t_tables imps2 ++ tts) (ext_t_mems imps2 ++ mts) (ext_t_globals imps2 ++ gts) ets dts locs labs ret refs) bes tf.
Proof.
  move => ts fts tts mts gts ets dts locs labs ret refs imps1 imps2 bes tf Hall2 Hbet.
  eapply context_agree_be_typing; eauto.
  unfold context_agree => /=.
  repeat rewrite eq_refl => /=.
  specialize (import_subtyping_comp_len _ _ Hall2) as [Hflen [Htlen [Hmlen Hglen]]].
  apply import_subtyping_components in Hall2 as [Hfsub [Htsub [Hmsub Hgsub]]].
  repeat rewrite length_is_size in Hflen.
  repeat rewrite length_is_size in Htlen.
  repeat rewrite length_is_size in Hmlen.
  repeat rewrite length_is_size in Hglen.
  repeat (apply/andP; split) => //; rewrite all2_cat => //; (apply/andP; split; last by apply reflexive_all2_same; move => ?; apply/eqP); apply all2_spec => //; move => n t1 t2 Hnth1 Hnth2.
  { eapply Forall2_lookup in Hfsub as [t [Hnth Hsub]]; eauto.
    by unfold import_func_subtyping in Hsub; remove_bools_options; simplify_multieq; subst; apply/eqP.
  }
  { eapply Forall2_lookup in Htsub as [t [Hnth Hsub]]; eauto.
    by unfold import_table_subtyping in Hsub; remove_bools_options; simplify_multieq; subst; apply/eqP.
  }
  { eapply Forall2_lookup in Hgsub as [t [Hnth Hsub]]; eauto.
    by unfold import_global_subtyping in Hsub; remove_bools_options; simplify_multieq; subst; apply/eqP.
  }
Qed.
  
Lemma instantiation_sound: forall (s: store_record) m v_imps s' f exps,
  store_typing s ->
  instantiate s m v_imps (s', f, exps) ->
  (store_typing s') /\
  (store_extension s s') /\
  (exists C, frame_typing s' f C).
Proof.
  move => s m v_imps s' f exps HST Hinst.
  unfold instantiate in Hinst.
  destruct Hinst as [t_imps_mod [t_imps [t_exps [hs' [inst [g_inits [r_inits [Hmodtype [Himptype [Hsubtype [Hallocmodule [Hinstglob [Hinstelem [Heqf Heqexps]]]]]]]]]]]]]].

  unfold alloc_module in Hallocmodule.
  destruct (alloc_funcs _ _ _) as [s1 ifs] eqn:Hallocfuncs.
  destruct (alloc_tabs _ _) as [s2 its] eqn:Halloctabs.
  destruct (alloc_mems _ _) as [s3 ims] eqn:Hallocmems.
  destruct (alloc_globs _ _) as [s4 igs] eqn:Hallocglobs.
  destruct (alloc_elems _ _) as [s5 ies] eqn:Hallocelems.
  destruct (alloc_datas _ _) as [s6 ids] eqn:Hallocdatas.

  remove_bools_options.

  apply alloc_func_iota_N in Hallocfuncs.
  apply alloc_table_iota_N in Halloctabs.
  apply alloc_mem_iota_N in Hallocmems.
  apply alloc_global_iota_N in Hallocglobs; last by apply List.Forall2_length in Hinstglob.
  apply alloc_elem_iota_N in Hallocelems; last by apply List.Forall2_length in Hinstelem.
  apply alloc_data_iota_N in Hallocdatas.

  (* Important to prove the goals first separately as there is some sort of dependency *)
  assert (store_extension s s') as Hstoreext.
  { 
    extract_premise.
    destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
    unfold store_extension => /=.
    erewrite component_extension_extend; eauto; last by apply all2_func_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_table_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_mem_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_global_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_elem_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_data_extension_same.
  }

  destruct m; unfold module_typing in Hmodtype; simpl in *.
  destruct Hmodtype as [fts [tts [mts [gts [rts [dts [Hmtypes [Hmfunctype [Hmtabletype [Hmmemtype [Hmglobaltype [Hmelemtype [Hmdatatype [Hstarttype [Hmimptype [Hmexptype Hexpunique]]]]]]]]]]]]]]]].

  remember (Build_t_context mod_types (ext_t_funcs t_imps ++ fts) (ext_t_tables t_imps ++ tts) (ext_t_mems t_imps ++ mts) (ext_t_globals t_imps ++ gts) rts dts nil nil None (iota_N 0 (length inst.(inst_funcs)))) as C.

  assert (inst_typing s' f.(f_inst) = Some C) as HIT.
  {
    extract_premise.
    destruct inst; subst; simpl in *.

    (* Functions *)
    assert (those (map (ext_func_typing s6) inst_funcs) = Some (ext_t_funcs t_imps ++ fts)) as Hfit.
    {
      subst inst_funcs.
      rewrite map_cat.
      apply those_cat.
      (* Imports *)
      { apply those_spec.
        { rewrite List.map_length.
          apply vt_imps_comp_len in Himptype as [? [? [??]]].
          by lias.
        }
        move => n ft Hnthtext.
        rewrite nth_error_map'.
        specialize (vt_imps_funcs_lookup Himptype Hnthtext) as [k [v [Hnthextv [Hnthv Hntht]]]].
        eapply Forall2_lookup in Himptype as [t [Hntht' Hexttype]]; eauto.
        rewrite Hntht in Hntht'; injection Hntht' as <-.
        unfold external_typing, ext_typing in Hexttype.
        remove_bools_options => /=.
        eapply ext_func_typing_extension in Hoption; eauto.
        by rewrite Hnthextv /= Hoption.
      }
      (* New *)
      {
        apply those_spec.
        { rewrite List.map_length iota_N_length.
          by apply List.Forall2_length in Hmfunctype; lias.
        }
        move => n ft Hnth.
        rewrite nth_error_map'.
        eapply Forall2_nth_impl' in Hmfunctype as [x [Hnthm Hmap]]; eauto.
        rewrite iota_N_lookup => /=; last by apply nth_error_Some_length in Hnthm; lias.
        unfold ext_func_typing.
        destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
        unfold lookup_N; rewrite Nat2N.id.
        rewrite List.nth_error_app2; last by lias.
        rewrite nth_error_map' => /=.
        replace (_ + n - _)%coq_nat with n; last by lias.
        rewrite Hnthm => /=; do 2 f_equal.
        unfold gen_func_instance => /=.
        unfold module_func_typing in Hmap; destruct x, ft; destruct Hmap as [Hnthtype [Hbet Hdefaults]].
        by rewrite Hnthtype.
      }
    }
    (* Tables *)
    assert (those (map (ext_table_typing s6) inst_tables) = Some (ext_t_tables t_imps ++ tts)) as Htit.
    {
      subst inst_tables.
      rewrite map_cat.
      apply those_cat.
      (* Imports *)
      { apply those_spec.
        { rewrite List.map_length.
          apply vt_imps_comp_len in Himptype as [? [? [??]]].
          by lias.
        }
        move => n ft Hnthtext.
        rewrite nth_error_map'.
        specialize (vt_imps_tables_lookup Himptype Hnthtext) as [k [v [Hnthextv [Hnthv Hntht]]]].
        eapply Forall2_lookup in Himptype as [t [Hntht' Hexttype]]; eauto.
        rewrite Hntht in Hntht'; injection Hntht' as <-.
        unfold external_typing, ext_typing in Hexttype.
        remove_bools_options => /=.
        rewrite Hnthextv.
        destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
        unfold ext_table_typing in *; remove_bools_options; simpl in *.
        unfold lookup_N in *.
        by erewrite nth_error_app_Some; eauto.
      }
      (* New *)
      {
        apply those_spec.
        { rewrite List.map_length iota_N_length List.map_length.
          by apply List.Forall2_length in Hmtabletype; lias.
        }
        move => n ft Hnth.
        rewrite nth_error_map' List.map_length.
        eapply Forall2_nth_impl' in Hmtabletype as [x [Hnthm Hmap]]; eauto.
        rewrite iota_N_lookup => /=; last by apply nth_error_Some_length in Hnthm; lias.
        unfold ext_table_typing.
        destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
        unfold lookup_N; rewrite Nat2N.id.
        rewrite List.nth_error_app2; last by lias.
        do 2 rewrite nth_error_map' => /=.
        replace (_ + n - _)%coq_nat with n; last by lias.
        rewrite Hnthm => /=; do 2 f_equal.
        unfold gen_table_instance => /=.
        unfold module_table_typing in Hmap; destruct x, ft, modtab_type, tt_limits0; simpl in *.
        by remove_bools_options; subst.
      }
    }
    (* Memories *)
    assert (those (map (ext_mem_typing s6) inst_mems) = Some (ext_t_mems t_imps ++ mts)) as Hmit.
    {
      subst inst_mems.
      rewrite map_cat.
      apply those_cat.
      (* Imports *)
      { apply those_spec.
        { rewrite List.map_length.
          apply vt_imps_comp_len in Himptype as [? [? [??]]].
          by lias.
        }
        move => n ft Hnthtext.
        rewrite nth_error_map'.
        specialize (vt_imps_mems_lookup Himptype Hnthtext) as [k [v [Hnthextv [Hnthv Hntht]]]].
        eapply Forall2_lookup in Himptype as [t [Hntht' Hexttype]]; eauto.
        rewrite Hntht in Hntht'; injection Hntht' as <-.
        unfold external_typing, ext_typing in Hexttype.
        remove_bools_options => /=.
        rewrite Hnthextv.
        destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
        unfold ext_mem_typing in *; remove_bools_options; simpl in *.
        unfold lookup_N in *.
        by erewrite nth_error_app_Some; eauto.
      }
      (* New *)
      {
        apply those_spec.
        { rewrite List.map_length iota_N_length List.map_length.
          by apply List.Forall2_length in Hmmemtype; lias.
        }
        move => n ft Hnth.
        rewrite nth_error_map' List.map_length.
        eapply Forall2_nth_impl' in Hmmemtype as [x [Hnthm Hmap]]; eauto.
        rewrite iota_N_lookup => /=; last by apply nth_error_Some_length in Hnthm; lias.
        unfold ext_mem_typing.
        destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
        unfold lookup_N; rewrite Nat2N.id.
        rewrite List.nth_error_app2; last by lias.
        do 2 rewrite nth_error_map' => /=.
        replace (_ + n - _)%coq_nat with n; last by lias.
        rewrite Hnthm => /=; do 2 f_equal.
        unfold gen_mem_instance => /=.
        unfold module_mem_typing in Hmap; destruct x, ft, modmem_type; simpl in *.
        by remove_bools_options; subst.
      }
    }
    (* Globals *)
    assert (those (map (ext_global_typing s6) inst_globals) = Some (ext_t_globals t_imps ++ gts)) as Hgit.
    {
      subst inst_globals.
      rewrite map_cat.
      apply those_cat.
      (* Imports *)
      { apply those_spec.
        { rewrite List.map_length.
          apply vt_imps_comp_len in Himptype as [? [? [??]]].
          by lias.
        }
        move => n ft Hnthtext.
        rewrite nth_error_map'.
        specialize (vt_imps_globals_lookup Himptype Hnthtext) as [k [v [Hnthextv [Hnthv Hntht]]]].
        eapply Forall2_lookup in Himptype as [t [Hntht' Hexttype]]; eauto.
        rewrite Hntht in Hntht'; injection Hntht' as <-.
        unfold external_typing, ext_typing in Hexttype.
        remove_bools_options => /=.
        rewrite Hnthextv.
        destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
        unfold ext_global_typing in *; remove_bools_options; simpl in *.
        unfold lookup_N in *.
        by erewrite nth_error_app_Some; eauto.
      }
      (* New *)
      {
        apply those_spec.
        { rewrite List.map_length iota_N_length.
          by apply List.Forall2_length in Hmglobaltype; lias.
        }
        move => n ft Hnth.
        rewrite nth_error_map'.
        eapply Forall2_nth_impl' in Hmglobaltype as [x [Hnthm Hmap]]; eauto.
        rewrite iota_N_lookup => /=; last by apply nth_error_Some_length in Hnthm; lias.
        unfold ext_global_typing.
        destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
        unfold lookup_N; rewrite Nat2N.id.
        rewrite List.nth_error_app2; last by lias.
        rewrite nth_error_map' => /=.
        replace (_ + n - _)%coq_nat with n; last by lias.
        unfold instantiate_globals in Hinstglob.
        eapply Forall2_lookup in Hinstglob as [gv [Hnthgv Hreduce]]; eauto.
        rewrite (combine_lookup_spec Hnthm Hnthgv) => /=.
        unfold module_global_typing in Hmap; destruct x; simpl in *.
        by destruct Hmap as [Hconst [-> Hbet]].
      }
    }
    (* Elems *)
    assert (those (map (fun elem =>
                          match (lookup_N (s_elems s6) elem) with
                          | Some ei => eleminst_typing s6 ei
                          | None => None
                          end
                     ) inst_elems) = Some rts) as Heit.
    {
      subst inst_elems.
      (* New *)
      {
        apply those_spec.
        { rewrite List.map_length iota_N_length.
          by apply List.Forall2_length in Hmelemtype; lias.
        }
        move => n ft Hnth.
        rewrite nth_error_map'.
        eapply Forall2_nth_impl' in Hmelemtype as [x [Hnthm Hmap]]; eauto.
        rewrite iota_N_lookup => /=; last by apply nth_error_Some_length in Hnthm; lias.
        replace (s_elems s6) with (s_elems s4 ++ map (fun '(elem, refs) => Build_eleminst (modelem_type elem) refs) (List.combine mod_elems r_inits)); last by destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
        unfold lookup_N; rewrite Nat2N.id.
        rewrite List.nth_error_app2; last by lias.
        rewrite nth_error_map' => /=.
        replace (_ + n - _)%coq_nat with n; last by lias.
        unfold instantiate_elems in Hinstelem.
        eapply Forall2_lookup in Hinstelem as [ev [Hnthev Hreduce]]; eauto.
        unfold module_elem_typing in Hmap; destruct x; simpl in *.
        rewrite (combine_lookup_spec Hnthm Hnthev) => /=.
        destruct Hmap as [-> [Hconstbet Hmodevalid]].
        f_equal.
        resolve_if_true_eq.
        apply Forall_all.
        apply Forall_spec.
        move => n' vref Hnthref.
        eapply Forall2_nth_impl' in Hreduce as [be [Hnthinit Hreduce]]; eauto.
        eapply Forall_lookup in Hconstbet as [Hconst Hbet]; eauto.
        eapply init_value_typing; eauto.
        { move => m addr /= Hnth'.
          destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
          rewrite List.app_length List.map_length.
          apply cat_lookup in Hnth' as [Hnth' | Hnth'].
          - apply ext_funcs_lookup_exist in Hnth' as [k Hnthaddr].
            eapply Forall2_nth_impl in Himptype as [et [Hnthext Hext]]; last by apply Hnthaddr.
            unfold external_typing, ext_typing, ext_func_typing in Hext; simpl in Hext.
            remove_bools_options.
            unfold lookup_N in *.
            apply nth_error_Some_length in Hoption0.
            by lias.
          - apply iota_N_lookup_Some in Hnth' as [-> Hlength].
            by lias.
        }
        { move => gidx v gt /= Hsglob Hntht.
          unfold sglob_val, sglob, sglob_ind in Hsglob.
          destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
          remove_bools_options.
          eapply import_subtyping_globs_impl' in Hsubtype as [gt' [Hnthsub Hsub]]; eauto.
          unfold import_global_subtyping in Hsub; remove_bools_options; subst.
          eapply vt_imps_globals_typing in Hnthsub as [addr [Hnthaddr Htext]]; eauto.
          unfold external_typing, ext_typing, ext_global_typing in Htext.
          simpl in Htext; remove_bools_options.
          unfold lookup_N in *; simplify_multieq.
          rewrite List.nth_error_app1 in Hoption; last by apply nth_error_Some_length in Hoption2.
          simplify_multieq.
          destruct HST as [_ [_ [_ [Hglobtype _]]]].
          eapply Forall_lookup in Hglobtype as [gt Hginsttype]; eauto.
          unfold globalinst_typing in Hginsttype.
          destruct g => /=.
          remove_bools_options; simpl in *.
          by eapply value_typing_extension; eauto.
        }
      }
    }
    (* Datas *)
    assert (those (map (fun data =>
                          match (lookup_N (s_datas s6) data) with
                          | Some ei => datainst_typing s6 ei
                          | None => None
                          end
                     ) inst_datas) = Some dts) as Hdit.
    {
      subst inst_datas.
      (* New *)
      {
        apply those_spec.
        { rewrite List.map_length iota_N_length.
          by apply List.Forall2_length in Hmdatatype; lias.
        }
        move => n ft Hnth.
        rewrite nth_error_map'.
        eapply Forall2_nth_impl' in Hmdatatype as [x [Hnthm Hmap]]; eauto.
        rewrite iota_N_lookup => /=; last by apply nth_error_Some_length in Hnthm; lias.
        replace (s_datas s6) with (s_datas s5 ++ map (fun md => Build_datainst (moddata_init md)) mod_datas); last (destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst).
        unfold lookup_N; rewrite Nat2N.id.
        rewrite List.nth_error_app2; last by lias.
        rewrite nth_error_map' => /=.
        replace (_ + n - _)%coq_nat with n; last by lias.
        unfold module_data_typing in Hmap; destruct x; simpl in *.
        destruct Hmap as [Hmap ->].
        by rewrite Hnthm.
      }
    }

    replace (all functype_valid inst_types) with true; last by symmetry; apply Forall_all.
    rewrite Hfit Htit Hmit Hgit Heit Hdit.
    reflexivity.
  }

  assert (store_typing s') as HST'.
  {
    extract_premise.
    destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
    destruct HST as [Hsfunctype [Hstabletype [Hsmemtype [Hsglobaltype [Hselemtype Hsdatatype]]]]].
    repeat split => //.
    (* Functions *)
    {
      rewrite List.Forall_app; split.
      (* Originals *)
      {
        eapply List.Forall_impl; eauto => /=.
        move => fi [ft Hft].
        exists ft.
        by eapply store_extension_funcinst_typing; eauto.
      }
      (* New *)
      {
        apply Forall_spec.
        move => n fi Hnth.
        apply nth_error_map in Hnth as [mf [Hnth Hmap]].
        subst.
        unfold funcinst_typing.
        eexists; split; first by eauto.
        specialize (List.Forall2_length Hmfunctype) as Hfunclen.
        eapply Forall2_lookup in Hmfunctype as [tf [Hnthtf Hmftype]]; eauto.
        unfold module_func_typing in Hmftype; destruct mf, tf; simpl in *.
        destruct Hmftype as [Hnthmf [Hbet Hdefaultable]].
        unfold gen_func_instance => /=.
        rewrite Hnthmf; split => //.
        rewrite HIT /= Hnthmf H6 Hfunclen; repeat split => //=.
        unfold upd_local_label_return in *; simpl in *.
        eapply bet_import_subtyping; eauto.
        eapply bet_skip_refcheck => /=; eauto.
        unfold upd_refs => /=.
        repeat rewrite List.app_length.
        rewrite iota_N_length.
        repeat f_equal.
        apply vt_imps_comp_len in Himptype.
        apply import_subtyping_comp_len in Hsubtype.
        extract_premise.
        by lias.
      }
    }
    (* Tables *)
    {
      rewrite List.Forall_app; split.
      (* Originals *)
      {
        eapply List.Forall_impl; eauto => /=.
        move => ti [tabt Htabt].
        exists tabt.
        by eapply store_extension_tableinst_typing; eauto.
      }
      (* New *)
      {
        apply Forall_spec.
        move => n fi Hnth.
        apply nth_error_map in Hnth as [mt [Hnth <-]].
        apply nth_error_map in Hnth as [mtab [Hnth <-]].
        eapply Forall2_nth_impl in Hmtabletype as [tabt [Hnthtab Htabtype]]; eauto.
        unfold module_table_typing in Htabtype.
        destruct mtab, modtab_type, tt_limits.
        unfold tableinst_typing, gen_table_instance; simpl in *.
        remove_bools_options; simpl in *; subst.
        rewrite H.
        rewrite List.repeat_length N2Nat.id eq_refl.
        rewrite all_repeat; first by eexists.
        unfold value_typing => /=.
        by rewrite value_subtyping_eq.
      }
    }
    (* Memories *)
    {
      rewrite List.Forall_app; split.
      (* Originals *)
      {
        eapply List.Forall_impl; eauto => /=.
        move => ? [t ?].
        exists t.
        by eapply store_extension_meminst_typing; eauto.
      }
      (* New *)
      {
        apply Forall_spec.
        move => n fi Hnth.
        apply nth_error_map in Hnth as [mt [Hnth <-]].
        apply nth_error_map in Hnth as [mm [Hnth <-]].
        eapply Forall2_nth_impl in Hmmemtype as [mt [Hnthmt Hmemtype]]; eauto.
        unfold module_mem_typing in Hmemtype.
        unfold meminst_typing, gen_mem_instance, memory_list.mem_make, memory_list.mem_length.
        remove_bools_options.
        rewrite H List.repeat_length N2Nat.id N.mul_comm eq_refl.
        by eexists.
      }
    }
    (* Globals *)
    {
      rewrite List.Forall_app; split.
      (* Originals *)
      {
        eapply List.Forall_impl; eauto => /=.
        move => ? [t ?].
        exists t.
        by eapply store_extension_globalinst_typing; eauto.
      }
      (* New *)
      {
        apply Forall_spec.
        move => n fi Hnth.
        apply nth_error_map in Hnth as [[mg gv] [Hnth <-]].
        apply combine_lookup in Hnth as [Hnthmg Hnthgv].
        eapply Forall2_lookup in Hmglobaltype as [gt [Hnth Hmap]]; eauto.
        unfold module_global_typing in Hmap.
        destruct mg; destruct Hmap as [Hconst [<- Hbet]].
        unfold globalinst_typing.
        exists gt.
        destruct gt => /=.
        resolve_if_true_eq.
        simpl in *.
        eapply Forall2_lookup in Hinstglob as [v [Hnthv Hreduce]]; eauto.
        simplify_multieq.
        simpl in *.
        eapply init_value_typing; eauto; simpl in *.
        { move => m addr Hnthaddr.
          rewrite List.app_length List.map_length.
          rewrite H6 in Hnthaddr.
          apply cat_lookup in Hnthaddr as [Hnth' | Hnth'].
          - apply ext_funcs_lookup_exist in Hnth' as [k Hnthaddr].
            eapply Forall2_nth_impl in Himptype as [et [Hnthext Hext]]; last by apply Hnthaddr.
            unfold external_typing, ext_typing, ext_func_typing in Hext; simpl in Hext.
            remove_bools_options.
            unfold lookup_N in *.
            apply nth_error_Some_length in Hoption0.
            by lias.
          - apply iota_N_lookup_Some in Hnth' as [-> Hlength].
            by lias.
        }
        { move => gidx v' gt /= Hsglob Hntht.
          unfold sglob_val, sglob, sglob_ind in Hsglob.
          remove_bools_options.
          eapply import_subtyping_globs_impl' in Hsubtype as [gt' [Hnthsub Hsub]]; eauto.
          unfold import_global_subtyping in Hsub; remove_bools_options; subst.
          eapply vt_imps_globals_typing in Hnthsub as [addr [Hnthaddr Htext]]; eauto.
          unfold external_typing, ext_typing, ext_global_typing in Htext.
          simpl in Htext; remove_bools_options.
          unfold lookup_N in *; simplify_multieq.
          rewrite List.nth_error_app1 in Hoption; last by apply nth_error_Some_length in Hoption2.
          simplify_multieq; simpl in *.
          eapply Forall_lookup in Hsglobaltype as [gt Hginsttype]; eauto.
          unfold globalinst_typing in Hginsttype.
          destruct g => /=.
          remove_bools_options; simpl in *.
          by eapply value_typing_extension; eauto.
        }
      }
    }
    (* Elems *)
    {
      rewrite List.Forall_app; split.
      (* Originals *)
      {
        eapply List.Forall_impl; eauto => /=.
        move => ? [t ?].
        exists t.
        by eapply store_extension_eleminst_typing; eauto.
      }
      (* New *)
      {
        apply Forall_spec.
        move => n fi Hnth.
        apply nth_error_map in Hnth as [[mg gv] [Hnth <-]].
        apply combine_lookup in Hnth as [Hnthmg Hnthgv].
        eapply Forall2_lookup in Hmelemtype as [gt [Hnth Hmap]]; eauto.
        unfold module_elem_typing in Hmap.
        destruct mg; destruct Hmap as [<- [Hconstbet Hmode]].
        unfold eleminst_typing.
        exists gt => /=.
        resolve_if_true_eq.
        apply Forall_all.
        apply Forall_spec.
        move => m vref Hnthv.
        eapply Forall2_nth_impl' in Hinstelem as [melem [Hnthv' Hreduce]]; eauto; simpl in *.
        simplify_multieq; simpl in *.
        eapply Forall2_nth_impl' in Hreduce as [bes [Hnthinit Hreduce]]; eauto.
        eapply Forall_lookup in Hconstbet as [Hconst Hbet]; eauto.
        eapply init_value_typing; eauto; simpl in *.
        { move => n' addr Hnthaddr.
          rewrite List.app_length List.map_length.
          rewrite H6 in Hnthaddr.
          apply cat_lookup in Hnthaddr as [Hnth' | Hnth'].
          - apply ext_funcs_lookup_exist in Hnth' as [k Hnthaddr].
            eapply Forall2_nth_impl in Himptype as [et [Hnthext Hext]]; last by apply Hnthaddr.
            unfold external_typing, ext_typing, ext_func_typing in Hext; simpl in Hext.
            remove_bools_options.
            unfold lookup_N in *.
            apply nth_error_Some_length in Hoption0.
            by lias.
          - apply iota_N_lookup_Some in Hnth' as [-> Hlength].
            by lias.
        }
        { move => gidx v' gt' /= Hsglob Hntht.
          unfold sglob_val, sglob, sglob_ind in Hsglob.
          remove_bools_options.
          eapply import_subtyping_globs_impl' in Hsubtype as [gt'' [Hnthsub Hsub]]; eauto.
          unfold import_global_subtyping in Hsub; remove_bools_options; subst.
          eapply vt_imps_globals_typing in Hnthsub as [addr [Hnthaddr Htext]]; eauto.
          unfold external_typing, ext_typing, ext_global_typing in Htext.
          simpl in Htext; remove_bools_options.
          unfold lookup_N in *; simplify_multieq.
          rewrite List.nth_error_app1 in Hoption; last by apply nth_error_Some_length in Hoption2.
          simplify_multieq; simpl in *.
          eapply Forall_lookup in Hsglobaltype as [gt' Hginsttype]; eauto.
          unfold globalinst_typing in Hginsttype.
          destruct g => /=.
          remove_bools_options; simpl in *.
          by eapply value_typing_extension; eauto.
        }
      }
    }
    (* Data *)
    {
      rewrite List.Forall_app; split.
      (* Originals *)
      {
        eapply List.Forall_impl; eauto => /=.
        move => ? [t ?].
        exists t.
        by eapply store_extension_datainst_typing; eauto.
      }
      (* New *)
      {
        apply Forall_spec.
        move => n fi Hnth.
        apply nth_error_map in Hnth as [md [Hnth <-]].
        eapply Forall2_nth_impl in Hmdatatype as [mt [Hnthmt Hdatatype]]; eauto.
        unfold module_data_typing in Hdatatype.
        unfold datainst_typing.
        by exists tt.
      }
    }
  }
  repeat split => //.
  exists C.
  unfold frame_typing; rewrite HIT.
  exists nil; subst; by split.
Qed.
  
End Host.
