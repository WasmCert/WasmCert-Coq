From mathcomp Require Import ssreflect eqtype seq ssrbool ssrfun.
From iris.program_logic Require Import language weakestpre lifting.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
(* From iris.bi Require Export weakestpre. *)
Require Export iris_locations iris_properties iris_rules_resources iris_wp_def stdpp_aux iris.
Require Export datatypes host operations properties opsem instantiation instantiation_properties.
(* We need a few helper lemmas from preservation. *)
Require Export type_preservation.

Close Scope byte.

Section Iris_instantiation.

Definition assert_const1 (es: expr) : option value :=
  match es with
  | [:: BI_const v] => Some v
  | _ => None
  end.

Definition assert_const1_i32 (es: expr) : option i32 :=
  match es with
  | [:: BI_const (VAL_int32 v)] => Some v
  | _ => None
  end.

Definition assert_const1_i32_to_nat (es:expr) : nat :=
  match assert_const1_i32 es with
  | Some v => nat_of_int v
  | _ => 0
  end.

Definition module_elem_bound_check_gmap (wts: gmap N tableinst) (imp_descs: list module_export_desc) (m: module) :=
  Forall (fun '{| modelem_table := (Mk_tableidx n);
                modelem_offset := eoff;
                modelem_init := fids |} =>
            match assert_const1_i32 eoff with
            | Some eoffi =>
              match (ext_tabs imp_descs) !! n with
              | Some (Mk_tableidx k) =>
                match wts !! (N.of_nat k) with
                | Some ti => nat_of_int eoffi + length fids <= length ti.(table_data)
                | None => False
                end
              | _ => 
                match (m.(mod_tables) !! (n - length (ext_tabs imp_descs))) with
                | Some modtab => (N.of_nat (nat_of_int eoffi + length fids) <= modtab.(modtab_type).(tt_limits).(lim_min))%N
                | None => False
                end
              end
            | None => False
              end
      ) m.(mod_elem).

Definition module_data_bound_check_gmap (wms: gmap N memory) (imp_descs: list module_export_desc) (m: module) :=
  Forall (fun '{| moddata_data := (Mk_memidx n);
                moddata_offset := doff;
                moddata_init := bs |} =>
            match assert_const1_i32 doff with
            | Some doffi =>
              match (ext_mems imp_descs) !! n with
              | Some (Mk_memidx k) =>
                match wms !! (N.of_nat k) with
                | Some mi => (N.of_nat (nat_of_int doffi + length bs) <= mem_length mi)%N
                | None => False
                end
              | _ => 
                match (m.(mod_mems) !! (n - length (ext_mems imp_descs))) with
                | Some modmem => (N.of_nat (nat_of_int doffi + length bs) <= page_size * (modmem.(lim_min)))%N
                | None => False
                end
              end
            | None => False
              end
         ) m.(mod_data).


Context `{!wasmG Σ}.


Definition import_resources_wasm_domcheck (v_imps: list module_export) (wfs: gmap N function_closure) (wts: gmap N tableinst) (wms: gmap N memory) (wgs: gmap N global) : iProp Σ :=
  ⌜ dom (gset N) wfs ≡ list_to_set (fmap N.of_nat (ext_func_addrs (fmap modexp_desc v_imps))) /\
    dom (gset N) wts ≡ list_to_set (fmap N.of_nat (ext_tab_addrs (fmap modexp_desc v_imps))) /\
    dom (gset N) wms ≡ list_to_set (fmap N.of_nat (ext_mem_addrs (fmap modexp_desc v_imps))) /\
    dom (gset N) wgs ≡ list_to_set (fmap N.of_nat (ext_glob_addrs (fmap modexp_desc v_imps))) ⌝.

(* Resources in the Wasm store, corresponding to those referred by the host vis store. This needs to also type-check
   with the module import. *)
Definition import_resources_wasm_typecheck (v_imps: list module_export) (t_imps: list extern_t) (wfs: gmap N function_closure) (wts: gmap N tableinst) (wms: gmap N memory) (wgs: gmap N global): iProp Σ :=
  (* Note that we do not actually need to know the exact content of the imports. However, these information are present
     in this predicate to make sure that they are kept incontact in the post. Note how these four gmaps are quantified
     in the instantiation spec. *)
  import_resources_wasm_domcheck v_imps wfs wts wms wgs ∗
  [∗ list] i ↦ v; t ∈ v_imps; t_imps,
  match v.(modexp_desc) with
  | MED_func (Mk_funcidx i) => ((∃ cl, N.of_nat i ↦[wf] cl ∗ ⌜ wfs !! (N.of_nat i) = Some cl /\ t = ET_func (cl_type cl) ⌝)%I)
  | MED_table (Mk_tableidx i) => (∃ tab tt, N.of_nat i ↦[wtblock] tab ∗ ⌜ wts !! (N.of_nat i) = Some tab /\ t = ET_tab tt /\ tab_typing tab tt ⌝)
  | MED_mem (Mk_memidx i) => (∃ mem mt, N.of_nat i ↦[wmblock] mem ∗ ⌜ wms !! (N.of_nat i) = Some mem /\ t = ET_mem mt /\ mem_typing mem mt ⌝) 
  | MED_global (Mk_globalidx i) => (∃ g gt, N.of_nat i ↦[wg] g ∗ ⌜ wgs !! (N.of_nat i) = Some g /\ t = ET_glob gt /\ global_agree g gt ⌝)
  end.

(*
(* An alternate definition that splits the above into the four different components from the start. *)
Definition import_resources_wasm_typecheck_split (v_imps: list module_export) (t_imps: list extern_t) (wfs: gmap N function_closure) (wts: gmap N tableinst) (wms: gmap N memory) (wgs: gmap N global): iProp Σ :=
  import_resources_wasm_domcheck v_imps wfs wts wms wgs ∗
  ([∗ list] i ↦ v; t ∈ (ext_func_addrs (fmap modexp_desc v_imps)); (ext_t_funcs t_imps), ∃ cl, N.of_nat v ↦[wf] cl ∗ ⌜ wfs !! (N.of_nat v) = Some cl /\ t = (cl_type cl)⌝) ∗
  ([∗ list] i ↦ v; t ∈ (ext_tab_addrs (fmap modexp_desc v_imps)); (ext_t_tabs t_imps), ∃ tab, N.of_nat v ↦[wtblock] tab ∗ ⌜ wts !! (N.of_nat v) = Some tab /\ tab_typing tab t ⌝) ∗
  ([∗ list] i ↦ v; t ∈ (ext_mem_addrs (fmap modexp_desc v_imps)); (ext_t_mems t_imps), ∃ mem, N.of_nat v ↦[wmblock] mem ∗ ⌜ wms !! (N.of_nat v) = Some mem /\ mem_typing mem t ⌝) ∗
  ([∗ list] i ↦ v; t ∈ (ext_glob_addrs (fmap modexp_desc v_imps)); (ext_t_globs t_imps), ∃ g, N.of_nat v ↦[wg] g ∗ ⌜ wgs !! (N.of_nat v) = Some g /\ global_agree g t ⌝).

(* Note that the original definition applies the alt, but not the other way round. *)
Lemma import_resources_wasm_equivalent_aux (v_imps: list module_export) (t_imps: list extern_t) (wfs: gmap N function_closure) (wts: gmap N tableinst) (wms: gmap N memory) (wgs: gmap N global):
  (*import_resources_wasm_domcheck v_imps wfs wts wms wgs*) ⊢
  (([∗ list] i ↦ v; t ∈ v_imps; t_imps,
  match v.(modexp_desc) with
  | MED_func (Mk_funcidx i) => ((∃ cl, N.of_nat i ↦[wf] cl ∗ ⌜ wfs !! (N.of_nat i) = Some cl /\ t = ET_func (cl_type cl) ⌝)%I)
  | MED_table (Mk_tableidx i) => (∃ tab tt, N.of_nat i ↦[wtblock] tab ∗ ⌜ wts !! (N.of_nat i) = Some tab /\ t = ET_tab tt /\ tab_typing tab tt ⌝)
  | MED_mem (Mk_memidx i) => (∃ mem mt, N.of_nat i ↦[wmblock] mem ∗ ⌜ wms !! (N.of_nat i) = Some mem /\ t = ET_mem mt /\ mem_typing mem mt ⌝) 
  | MED_global (Mk_globalidx i) => (∃ g gt, N.of_nat i ↦[wg] g ∗ ⌜ wgs !! (N.of_nat i) = Some g /\ t = ET_glob gt /\ global_agree g gt ⌝) end) ↔
  (([∗ list] i ↦ v; t ∈ (ext_func_addrs (fmap modexp_desc v_imps)); (ext_t_funcs t_imps), ∃ cl, N.of_nat v ↦[wf] cl ∗ ⌜ wfs !! (N.of_nat v) = Some cl /\ t = (cl_type cl)⌝) ∗
  ([∗ list] i ↦ v; t ∈ (ext_tab_addrs (fmap modexp_desc v_imps)); (ext_t_tabs t_imps), ∃ tab, N.of_nat v ↦[wtblock] tab ∗ ⌜ wts !! (N.of_nat v) = Some tab /\ tab_typing tab t ⌝) ∗
  ([∗ list] i ↦ v; t ∈ (ext_mem_addrs (fmap modexp_desc v_imps)); (ext_t_mems t_imps), ∃ mem, N.of_nat v ↦[wmblock] mem ∗ ⌜ wms !! (N.of_nat v) = Some mem /\ mem_typing mem t ⌝) ∗
  ([∗ list] i ↦ v; t ∈ (ext_glob_addrs (fmap modexp_desc v_imps)); (ext_t_globs t_imps), ∃ g, N.of_nat v ↦[wg] g ∗ ⌜ wgs !! (N.of_nat v) = Some g /\ global_agree g t ⌝)))%I.
Proof.
  move: wgs wms wts wfs t_imps.
  iInduction v_imps as [ | v] "IH"; iIntros (wgs wms wts wfs t_imps) => /=; destruct t_imps => //=.
  - iSplit; first by iIntros "?" => //=.
    destruct e; by iIntros "(?&?&?&?)".
  - iSplit; first by iIntros "?".
    destruct v, modexp_desc => /=; by iIntros "(?&?&?&?)".
  - iSplit.
    + destruct v, modexp_desc; iIntros "(Hhead & Htail)" => /=.
      * destruct f.
        iDestruct "Hhead" as (cl) "(Hhead & %Hhead)".
        destruct Hhead as [Hlookup ->].
        iSimpl.
        unfold ext_tab_addrs, ext_mem_addrs, ext_glob_addrs.
        simpl.
        iDestruct ("IH" with "Htail") as "(Hf & Ht & Hm & Hg)".
        iFrame.
        iExists cl; by iFrame.
      * destruct t.
        iDestruct "Hhead" as (tab tt) "(Hhead & %Hhead)".
        destruct Hhead as [Hlookup [-> Htt]].
        iSimpl.
        unfold ext_func_addrs, ext_mem_addrs, ext_glob_addrs.
        simpl.
        iDestruct ("IH" with "Htail") as "(Hf & Ht & Hm & Hg)".
        iFrame.
        iExists tab; by iFrame.
      * destruct m.
        iDestruct "Hhead" as (mem mt) "(Hhead & %Hhead)".
        destruct Hhead as [Hlookup [-> Hmt]].
        iSimpl.
        unfold ext_func_addrs, ext_tab_addrs, ext_glob_addrs.
        simpl.
        iDestruct ("IH" with "Htail") as "(Hf & Ht & Hm & Hg)".
        iFrame.
        iExists mem; by iFrame.
      * destruct g.
        iDestruct "Hhead" as (glob gt) "(Hhead & %Hhead)".
        destruct Hhead as [Hlookup [-> Hgt]].
        iSimpl.
        unfold ext_func_addrs, ext_tab_addrs, ext_mem_addrs.
        simpl.
        iDestruct ("IH" with "Htail") as "(Hf & Ht & Hm & Hg)".
        iFrame.
        iExists glob; by iFrame.
   (* + destruct v, modexp_desc; iIntros "(Hf & Ht & Hm & Hg)" => /=.
      * destruct f.
        unfold ext_func_addrs => /=.
        unfold oapp.
        iDestruct ("IH" with "Hf Ht Hm Hg") as "Hcons".
        iDestruct (big_sepL2_length with "Hf") as "%Hlength".
        simpl in Hlength.
        destruct e => //=.
        admit.
        iDestruct (big_sepL2_length with "Hf") as "%Hlength2".
        iDestruct "Hf" as "(Hhead & Htail)".*)
        admit.
Admitted.
 *)

Definition exp_default := MED_func (Mk_funcidx 0).

Lemma import_resources_wasm_lookup v_imps t_imps wfs wts wms wgs ws:
  ⊢ gen_heap_interp (gmap_of_list (s_funcs ws)) -∗
    gen_heap_interp (gmap_of_table (s_tables ws)) -∗
    gen_heap_interp (gmap_of_memory (s_mems ws)) -∗
    gen_heap_interp (gmap_of_list (s_globals ws)) -∗
    gen_heap_interp (gmap_of_list (fmap tab_size (s_tables ws))) -∗
    gen_heap_interp (gmap_of_list (fmap table_max_opt (s_tables ws))) -∗
    gen_heap_interp (gmap_of_list (fmap mem_length (s_mems ws))) -∗
    gen_heap_interp (gmap_of_list (fmap mem_max_opt (s_mems ws))) -∗
    import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
    ⌜ length v_imps = length t_imps /\ ∀ k v t, v_imps !! k = Some v -> t_imps !! k = Some t ->
      match modexp_desc v with
      | MED_func (Mk_funcidx i) => ∃ cl, ws.(s_funcs) !! i = Some cl /\ wfs !! N.of_nat i = Some cl /\ t = ET_func (cl_type cl) 
      | MED_table (Mk_tableidx i) => ∃ tab tt, ws.(s_tables) !! i = Some tab /\ wts !! N.of_nat i = Some tab /\ t = ET_tab tt /\ tab_typing tab tt
      | MED_mem (Mk_memidx i) => ∃ mem mt b_init, ws.(s_mems) !! i = Some {| mem_data := {| ml_init := b_init; ml_data := mem.(mem_data).(ml_data) |}; mem_max_opt := mem.(mem_max_opt) |} /\ wms !! N.of_nat i = Some mem /\ t = ET_mem mt /\ mem_typing mem mt
      | MED_global (Mk_globalidx i) => ∃ g gt, ws.(s_globals) !! i = Some g /\ wgs !! N.of_nat i = Some g /\ t = ET_glob gt /\ global_agree g gt
      end ⌝.
Proof. 
  iIntros "Hwf Hwt Hwm Hwg Hwtsize Hwtlimit Hwmlength Hwmlimit (Himpwasmdom & Himpwasm)".
  iSplit; first by iApply big_sepL2_length.
  iIntros (k v t Hv Ht).
  destruct v as [? modexp_desc].
  iDestruct (big_sepL2_lookup with "Himpwasm") as "Hvimp" => //.
  destruct modexp_desc as [e|e|e|e]; destruct e as [n] => /=.
  - (* functions *)
    iDestruct "Hvimp" as (cl) "(Hcl & %Hwfs)".
    destruct Hwfs as [Hwfs ->].
    iDestruct (gen_heap_valid with "Hwf Hcl") as "%Hwf".
    rewrite gmap_of_list_lookup in Hwf.
    rewrite Nat2N.id in Hwf.
    rewrite Hwf.
    iPureIntro.
    exists cl.
    by repeat split => //.
  - (* tables *)
    iDestruct "Hvimp" as (tab tt) "(Htab & %Hwts)".
    destruct Hwts as [Hwts [-> Htabletype]]. 
    iDestruct (tab_block_lookup with "Hwt Hwtsize Hwtlimit Htab") as "%Hwt".
    rewrite Nat2N.id in Hwt.
    iPureIntro.
    exists tab, tt.
    by repeat split => //.
  - (* memories *)
    iDestruct "Hvimp" as (mem mt) "(Hmem & %Hwms)".
    destruct Hwms as [Hwms [-> Hmemtype]]. 
    iDestruct (mem_block_lookup with "Hwm Hwmlength Hwmlimit Hmem") as "%Hwm".
    rewrite Nat2N.id in Hwm.
    destruct Hwm as [m [Hwmlookup [Hmdata Hmlimit]]].
    iPureIntro.
    eexists _, mt, m.(mem_data).(ml_init).
    repeat split => //.
    rewrite Hwmlookup.
    f_equal.
    destruct m.
    simpl in *.
    f_equal => //.
    destruct mem_data.
    simpl in *.
    by f_equal.
  - (* globals *)
    iDestruct "Hvimp" as (g gt) "(Hg & %Hwgs)".
    destruct Hwgs as [Hwgs [-> Hgt]].
    iDestruct (gen_heap_valid with "Hwg Hg") as "%Hwg".
    rewrite gmap_of_list_lookup in Hwg.
    rewrite Nat2N.id in Hwg.
    iPureIntro.
    exists g, gt.
    by repeat split => //.
Qed.


Lemma import_resources_wts_subset v_imps t_imps wfs wts wms wgs (ws: store_record):
  ⊢ gen_heap_interp (gmap_of_table (s_tables ws)) -∗
    gen_heap_interp (gmap_of_list (fmap tab_size (s_tables ws))) -∗
    gen_heap_interp (gmap_of_list (fmap table_max_opt (s_tables ws))) -∗
    import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
    ⌜ length v_imps = length t_imps ⌝ -∗
    ⌜ wts ⊆ gmap_of_list (s_tables ws) ⌝.
Proof.
  iIntros "Hwt Hwtsize Hwtlimit (%Himpwasmdom & Himpwasm) %Himplen".
  rewrite map_subseteq_spec.
  iIntros (i x Hwtslookup).
  destruct Himpwasmdom as [_ [Hwtdom _]].
  assert (i ∈ dom (gset N) wts) as Hidom.
  { by apply elem_of_dom. }
  rewrite -> Hwtdom in Hidom.
  rewrite -> elem_of_list_to_set in Hidom.

  unfold ext_tab_addrs, compose in Hidom.
  rewrite -> elem_of_list_fmap in Hidom.
  destruct Hidom as [? [-> Hidom]].
  rewrite -> elem_of_list_fmap in Hidom.
  destruct Hidom as [t [-> Hidom]].
  destruct t.
  rewrite -> elem_of_list_lookup in Hidom.
  destruct Hidom as [k Hdom].
  apply ext_tabs_lookup_exist in Hdom.
  destruct Hdom as [k' Hdom].
  rewrite list_lookup_fmap in Hdom.
  destruct (v_imps !! k') eqn:Hvimpslookup => //.
  simpl in Hdom.

  inversion Hdom; clear Hdom.

  assert (exists t, t_imps !! k' = Some t) as Htimpslookup.
  { apply lookup_lt_Some in Hvimpslookup.
    rewrite Himplen in Hvimpslookup.
    destruct (t_imps !! k') eqn:Htimpslookup; try by eexists.
    apply lookup_ge_None in Htimpslookup.
    by lias.
  }

  destruct Htimpslookup as [t Htimpslookup].
  
  iDestruct (big_sepL2_lookup with "Himpwasm") as "Hvimp" => //.
  rewrite H0.
  iDestruct "Hvimp" as (tab tt) "(Htab & %Hwts)".
  destruct Hwts as [Hwtslookup' [-> Htt]].
  rewrite Hwtslookup in Hwtslookup'.
  inversion Hwtslookup'; subst; clear Hwtslookup'.

  iDestruct (tab_block_lookup with "Hwt Hwtsize Hwtlimit Htab") as "%Hwtblock".

  rewrite gmap_of_list_lookup.

  by rewrite Hwtblock.
Qed.

Definition mem_equiv (m1 m2: memory): Prop :=
  m1.(mem_max_opt) = m2.(mem_max_opt) /\
  m1.(mem_data).(ml_data) = m2.(mem_data).(ml_data).

Definition map_related {K: Type} {M: Type -> Type} {H0: forall A: Type, Lookup K A (M A)} {A: Type} (r: relation A) (m1 m2: M A) :=
  forall (i: K) (x: A), m1 !! i = Some x -> exists y, m2 !! i = Some y /\ r x y.

Lemma import_resources_wms_subset v_imps t_imps wfs wts wms wgs (ws: store_record):
  ⊢ gen_heap_interp (gmap_of_memory (s_mems ws)) -∗
    gen_heap_interp (gmap_of_list (fmap mem_length (s_mems ws))) -∗
    gen_heap_interp (gmap_of_list (fmap mem_max_opt (s_mems ws))) -∗
    import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
    ⌜ length v_imps = length t_imps ⌝ -∗
    ⌜ map_related mem_equiv wms (gmap_of_list (s_mems ws)) ⌝.
Proof.
  iIntros "Hwm Hwmlength Hwmlimit (%Himpwasmdom & Himpwasm) %Himplen".
  unfold map_related.
  iIntros (i x Hwmslookup).
  destruct Himpwasmdom as [_ [_ [Hwmdom _]]].
  assert (i ∈ dom (gset N) wms) as Hidom.
  { by apply elem_of_dom. }
  rewrite -> Hwmdom in Hidom.
  rewrite -> elem_of_list_to_set in Hidom.

  unfold ext_mem_addrs, compose in Hidom.
  rewrite -> elem_of_list_fmap in Hidom.
  destruct Hidom as [? [-> Hidom]].
  rewrite -> elem_of_list_fmap in Hidom.
  destruct Hidom as [memid [-> Hidom]].
  destruct memid.
  rewrite -> elem_of_list_lookup in Hidom.
  destruct Hidom as [k Hdom].
  apply ext_mems_lookup_exist in Hdom.
  destruct Hdom as [k' Hdom].
  rewrite list_lookup_fmap in Hdom.
  destruct (v_imps !! k') eqn:Hvimpslookup => //.
  simpl in Hdom.

  inversion Hdom; clear Hdom.

  assert (exists t, t_imps !! k' = Some t) as Htimpslookup.
  { apply lookup_lt_Some in Hvimpslookup.
    rewrite Himplen in Hvimpslookup.
    destruct (t_imps !! k') eqn:Htimpslookup; try by eexists.
    apply lookup_ge_None in Htimpslookup.
    by lias.
  }

  destruct Htimpslookup as [t Htimpslookup].
  
  iDestruct (big_sepL2_lookup with "Himpwasm") as "Hvimp" => //.
  rewrite H0.
  iDestruct "Hvimp" as (mem mt) "(Hmem & %Hwms)".
  destruct Hwms as [Hwmslookup' [-> Hmt]].
  rewrite Hwmslookup in Hwmslookup'.
  inversion Hwmslookup'; subst; clear Hwmslookup'.

  iDestruct (mem_block_lookup with "Hwm Hwmlength Hwmlimit Hmem") as "%Hwmblock".

  destruct Hwmblock as [mem' [Hwmlookup [Hmdata Hmmax]]].

  rewrite gmap_of_list_lookup.

  rewrite Hwmlookup.
  by iExists mem'.
Qed.

Lemma module_elem_bound_check_gmap_extend wts1 wts2 imp_descs m:
  module_elem_bound_check_gmap wts1 imp_descs m ->
  wts1 ⊆ wts2 ->
  module_elem_bound_check_gmap wts2 imp_descs m.
Proof.
  move => Hbc Hsubset.
  unfold module_elem_bound_check_gmap in *.
  rewrite -> List.Forall_forall in Hbc.
  apply List.Forall_forall.
  move => x Hin.
  specialize (Hbc x Hin).
  destruct x.
  destruct modelem_table.
  destruct (assert_const1_i32 modelem_offset) eqn:Hoffseti32 => //.
  destruct (ext_tabs imp_descs !! n) eqn:Himpslookup => //.
  destruct t.
  destruct (wts1 !! N.of_nat n0) eqn:Hwts1lookup => //.
  replace (wts2 !! N.of_nat n0) with (Some t) => //.
  by erewrite lookup_weaken => //.
Qed.

Lemma module_data_bound_check_gmap_extend wms1 wms2 imp_descs m:
  module_data_bound_check_gmap wms1 imp_descs m ->
  map_related mem_equiv wms1 wms2 ->
  module_data_bound_check_gmap wms2 imp_descs m.
Proof.
  move => Hbc Hrelate.
  unfold module_data_bound_check_gmap in *.
  rewrite -> List.Forall_forall in Hbc.
  apply List.Forall_forall.
  move => x Hin.
  specialize (Hbc x Hin).
  destruct x.
  destruct moddata_data.
  destruct (assert_const1_i32 moddata_offset) eqn:Hoffseti32 => //.
  destruct (ext_mems imp_descs !! n) eqn:Himpslookup => //.
  destruct m0.
  destruct (wms1 !! N.of_nat n0) eqn:Hwms1lookup => //.
  unfold map_related in Hrelate.
  specialize (Hrelate _ _ Hwms1lookup).
  destruct Hrelate as [mem [Hwms2lookup Hmequiv]].
  rewrite Hwms2lookup.
  unfold mem_equiv in Hmequiv.
  destruct Hmequiv as [_ Hmdata].
  replace (mem_length mem) with (mem_length m0) => //.
  unfold mem_length, memory_list.mem_length.
  by rewrite Hmdata.
Qed.

Definition module_glob_init_value (modglobs: list module_glob): option (list value) :=
  those (fmap (assert_const1 ∘ modglob_init) modglobs).

(* Table initialisers work as follows:
   - Each initialiser specifies a tableidx which is an index to the table list in the current module instance. 
   - Each initialiser specifies an offset eo (has to be const), which is the starting index that is going to be filled in.
   - For each f_j in the init array, replace s.tables[inst.tables(tableidx)][offset+j] with inst.funcs(f_j). Note how
     both the tableidx and the f_j (funcidx) here are referring to the index in the current module. 
   
   Memory initiliasers work similarly.
*)

Definition instantiation_resources_pre_wasm m v_imps t_imps wfs wts wms wgs : iProp Σ :=
  import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs ∗
  ⌜ module_elem_bound_check_gmap wts (fmap modexp_desc v_imps) m ⌝ ∗
  ⌜ module_data_bound_check_gmap wms (fmap modexp_desc v_imps) m ⌝.

(* This builds a gmap from (tableid * index) to funcelem, representing the initial values dictated by the elem segment. However, note that the tableid here refers to the id in the instance instead of that in the store.

   Note that this tableid does not count the imported tables. 
 *)
Definition build_tab_initialiser (instfuncs: list funcaddr) (elem: module_element) (tabid: nat) (offset: nat) : gmap (nat * nat) funcelem :=
  fold_left (fun acc actor => actor acc) (imap (fun j e_init => match e_init with
                     | Mk_funcidx fid => map_insert (tabid, j + offset) (nth_error instfuncs fid) end) elem.(modelem_init) ) ∅.

Fixpoint module_tab_init_values (m: module) (inst: instance) (modelems: list module_element) : gmap (nat * nat) funcelem :=
  match modelems with
  | e_init :: e_inits' => match e_init.(modelem_table) with
                        | Mk_tableidx i => (module_tab_init_values m inst e_inits') ∪ (build_tab_initialiser inst.(inst_funcs) e_init i (assert_const1_i32_to_nat (e_init.(modelem_offset))))
                        end
                          
  | [] => ∅
  end.

(* Note that we use compcert byte for our internal memory representation, but module uses the pure Coq version of byte. *)
Definition build_mem_initialiser (datum: module_data) (memid: nat) (offset: nat) : gmap (nat * nat) byte :=
  fold_left (fun acc actor => actor acc)
            (imap (fun j b => map_insert (memid, j + offset) (compcert_byte_of_byte b)) datum.(moddata_init) ) ∅.


Fixpoint module_mem_init_values (m: module) (moddata: list module_data) : gmap (nat * nat) byte :=
  match moddata with
  | d_init :: d_inits' => match d_init.(moddata_data) with
                        | Mk_memidx i => (module_mem_init_values m d_inits') ∪ (build_mem_initialiser d_init i (assert_const1_i32_to_nat (d_init.(moddata_offset))))
                        end
                          
  | [] => ∅
  end.

(* g_inits have the correct types and values. Typing is redundant given the current restriction *)
Definition module_glob_init_values m g_inits :=
  (fmap typeof g_inits = fmap (tg_t ∘ modglob_type) m.(mod_globals)) /\
  module_glob_init_value m.(mod_globals) = Some g_inits.

(* The starting point for newly allocated tables. *)
Definition module_inst_table_base_create :=
  fun mt => match mt.(modtab_type).(tt_limits) with
         | {| lim_min := min; lim_max := omax |} =>
             (Build_tableinst
                (repeat (None: funcelem) (ssrnat.nat_of_bin min))
                (omax))
         end.
Definition module_inst_table_base (mtabs: list module_table) : list tableinst :=
  fmap module_inst_table_base_create mtabs.

(* Given a tableinst, an offset and a list of funcelems, replace the corresponding segment with the initialisers. *)
Definition table_init_replace_single (t: tableinst) (offset: nat) (fns: list funcelem) : tableinst :=
  Build_tableinst
    (take (length t.(table_data)) ((take offset t.(table_data)) ++ fns ++ (drop (offset + length fns) t.(table_data))))
    t.(table_max_opt).

Lemma table_init_replace_single_preserve_len t offset fns t':
  table_init_replace_single t offset fns = t' ->
  length t.(table_data) = length t'.(table_data).
Proof.
  move => Hreplace.
  unfold table_init_replace_single in Hreplace.
  subst => /=.
  rewrite take_length.
  repeat rewrite app_length.
  rewrite take_length drop_length.
  by lias.
Qed.

(* Each of these is guaranteed to be a some due to validation. *)
Definition lookup_funcaddr (inst: instance) (me_init: list funcidx) : list funcelem :=
  fmap (fun '(Mk_funcidx fidx) => nth_error inst.(inst_funcs) fidx) me_init.

(* For each table initialiser elem, if the target table is not imported, then
   we use its content to update the corresponding table build from the base. *)
Definition module_inst_build_tables (m : module) (inst: instance) : list tableinst :=
  fold_left (fun tabs '{| modelem_table := mt; modelem_offset := moff; modelem_init := me_init |} =>
               let itc := get_import_table_count m in 
               match mt with
               | Mk_tableidx k =>
                 if k <? itc then tabs else
                   (* These are guaranteed to succeed due to validation. *)
                   match nth_error tabs (k-itc) with
                   | Some t => <[ (k-itc) := table_init_replace_single t (assert_const1_i32_to_nat moff) (lookup_funcaddr inst me_init) ]> tabs
                   | None => tabs
                   end
               end
                 ) m.(mod_elem) (module_inst_table_base m.(mod_tables)).

Definition module_import_init_tabs (m: module) (inst: instance) (wts: gmap N tableinst) : gmap N tableinst :=
  fold_left (fun wts '{| modelem_table := mt; modelem_offset := moff; modelem_init := me_init |} =>
               let itc := get_import_table_count m in 
               match mt with
               | Mk_tableidx k =>
                 if k <? itc then
                   match nth_error inst.(inst_tab) k with
                   | Some t_addr =>
                     match wts !! (N.of_nat t_addr) with
                     | Some t => <[ (N.of_nat t_addr) := table_init_replace_single t (assert_const1_i32_to_nat moff) (lookup_funcaddr inst me_init) ]> wts
                     | None => wts
                     end
                   | None => wts
                   end
                 else wts
               end
            ) m.(mod_elem) wts.

(* A similar set of predicate but for memories instead. *)
Definition module_inst_mem_base_func := (fun '{| lim_min := min; lim_max := omax |} =>
          (Build_memory
             (Build_memory_list
               #00%byte
               (repeat #00%byte (ssrnat.nat_of_bin min))
               )
             (omax))).

(* The first step of building the correct memories: creating a list of empty memories of the correct sizes. *)
Definition module_inst_mem_base (mmemtypes: list memory_type) : list memory :=
  fmap module_inst_mem_base_func mmemtypes.

(* A function preparing for the contents of memory to be replaced by initialisers. *)
Definition mem_init_replace_single (mem: memory) (offset: nat) (bs: list byte) : memory :=
  Build_memory
    (Build_memory_list
       mem.(mem_data).(ml_init)
       (take (length mem.(mem_data).(ml_data)) ((take offset mem.(mem_data).(ml_data)) ++ bs ++ (drop (offset + length bs) mem.(mem_data).(ml_data)))))
    mem.(mem_max_opt).


(* For each module data segment:
   - Finds the correct memory targeted; we only deal with the case where the 
     memory to be initialised is newly allocated (not imported) here.
   - In that case, simply replace the memory by a new memory with the contents
     replaced by the corresponding initialisers.
   - Return the list of memories obtained: this corresponds to the correct
     contents of all the memories freshly declared in the module.
*)
Definition module_inst_build_mems (m : module) (inst: instance) : list memory :=
  fold_left (fun mems '{| moddata_data := md; moddata_offset := moff; moddata_init := md_init |} =>
               let imc := get_import_mem_count m in 
               match md with
               | Mk_memidx k =>
                 if k <? imc then mems else
                   (* These are guaranteed to succeed due to validation. *)
                   match nth_error mems (k-imc) with
                   | Some mem => <[ (k-imc) := mem_init_replace_single mem (assert_const1_i32_to_nat moff) (fmap compcert_byte_of_byte md_init) ]> mems
                   | None => mems
                   end
               end
                 ) m.(mod_data) (module_inst_mem_base m.(mod_mems)).

(*
   For each module data segment:
   - Finds the correct memory targeted. In this function we deal with the 
     remaining ones, i.e. those targeted at imported memories.
   - We have to locate the memory in the Wasm store by looking up in the instance
     to find the correct index.
   - After that, we recall from wms the correct content of the imported memory.
     This must exists since wms records all of the memories that we have 
     access to.
   - Modify that memory in wms by a new memory with the contents replaced by 
     the corresponding initialisers.
   - Return wms: this is the new gmap recording the correct contents of the
     imported memories.
*)
Definition module_import_init_mems (m: module) (inst: instance) (wms: gmap N memory) : gmap N memory :=
  fold_left (fun wms '{| moddata_data := md; moddata_offset := moff; moddata_init := md_init |} =>
               let imc := get_import_mem_count m in 
               match md with
               | Mk_memidx k =>
                 if k <? imc then
                   match nth_error inst.(inst_memory) k with
                   | Some m_addr =>
                     match wms !! (N.of_nat m_addr) with
                     | Some mem => <[ (N.of_nat m_addr) := mem_init_replace_single mem (assert_const1_i32_to_nat moff) (fmap compcert_byte_of_byte md_init) ]> wms
                     | None => wms
                     end
                   | None => wms
                   end
                 else wms
               end
            ) m.(mod_data) wms.


(* Again the allocated resources but for globals. Note that the initial value
   here is purely dummy. *)
Definition module_inst_global_base (mglobs: list module_glob) : list global :=
  fmap (fun '{| modglob_type := {| tg_mut := tgm; tg_t := tgvt |} ; modglob_init := mgi |} => (Build_global tgm (bitzero tgvt))) mglobs.

Definition global_init_replace_single (g: global) (v: value) : global :=
  Build_global g.(g_mut) v.

Fixpoint module_inst_global_init (gs: list global) (g_inits: list value) : list global :=
  match gs with
  | [::] => [::]
  | g :: gs' =>
    match g_inits with
    | [::] => g :: gs'
    | gi :: g_inits' => global_init_replace_single g gi :: module_inst_global_init gs' g_inits'
    end
  end.

Lemma module_inst_global_init_cat (gs1 gs2: list global) (gi1 gi2: list value):
  length gs1 = length gi1 ->
  module_inst_global_init (gs1 ++ gs2) (gi1 ++ gi2) =
  module_inst_global_init gs1 gi1 ++ module_inst_global_init gs2 gi2.
Proof.
  move : gi1 gi2 gs2.
  induction gs1; move => gi1 gi2 gs2 Hlen; destruct gi1 => //=.
  simpl in Hlen.
  f_equal.
  apply IHgs1.
  by lias.
Qed.
  
(* The newly allocated resources due to instantiation. *)
Definition module_inst_resources_func (mfuncs: list module_func) (inst: instance) (inst_f: list funcaddr) : iProp Σ :=
  ([∗ list] f; addr ∈ mfuncs; inst_f,
   (* Allocated wasm resources *)
     N.of_nat addr ↦[wf] (FC_func_native
                             inst
                             (nth match f.(modfunc_type) with
                                 | Mk_typeidx k => k
                                 end (inst.(inst_types)) (Tf [] []))
                             f.(modfunc_locals)
                             f.(modfunc_body))
  )%I.

Definition module_inst_resources_tab (tabs: list tableinst) (inst_t: list tableaddr) : iProp Σ :=
  ([∗ list] i ↦ tab; addr ∈ tabs; inst_t,
    N.of_nat addr ↦[wtblock] tab
  )%I.

Definition module_inst_resources_mem (mems: list memory) (inst_m: list memaddr) : iProp Σ := 
  ([∗ list] i ↦ mem; addr ∈ mems; inst_m,
    N.of_nat addr ↦[wmblock] mem
  ).

Definition module_inst_resources_glob (globs: list global) (inst_g: list globaladdr) : iProp Σ :=
  ([∗ list] i↦g; addr ∈ globs; inst_g,
    N.of_nat addr ↦[wg] g
  ).

(* The collection of the four types of newly allocated resources *)
Definition module_inst_resources_wasm (m: module) (inst: instance) (tab_inits: list tableinst) (mem_inits: list memory) (glob_inits: list global) : iProp Σ :=
  (module_inst_resources_func m.(mod_funcs) inst (drop (get_import_func_count m) inst.(inst_funcs)) ∗
  module_inst_resources_tab tab_inits (drop (get_import_table_count m) inst.(inst_tab)) ∗
  module_inst_resources_mem mem_inits (drop (get_import_mem_count m) inst.(inst_memory)) ∗                        
  module_inst_resources_glob glob_inits (drop (get_import_global_count m) inst.(inst_globs)))%I.

Definition instantiation_resources_post_wasm m v_imps t_imps wfs wts wms wgs (idfstart: option nat) (inst: instance) : iProp Σ :=
  ∃ (g_inits: list value) tab_inits mem_inits glob_inits wts' wms',  
  import_resources_wasm_typecheck v_imps t_imps wfs wts' wms' wgs ∗ (* locations in the wasm store and type-checks; this described the new contents of tables and memories that have been modified by the initialisers *)
    ⌜ inst.(inst_types) = m.(mod_types) /\
   (* We know what the imported part of the instance must be. *)
  let v_imp_descs := map (fun mexp => mexp.(modexp_desc)) v_imps in
    prefix (ext_func_addrs v_imp_descs) inst.(inst_funcs) /\
    prefix (ext_tab_addrs v_imp_descs) inst.(inst_tab) /\
    prefix (ext_mem_addrs v_imp_descs) inst.(inst_memory) /\
    prefix (ext_glob_addrs v_imp_descs) inst.(inst_globs) /\
    check_start m inst idfstart ⌝ ∗
   (* The relevant initial values of allocated resources, as well as the newly
      initialised segments in the imported tables and memories *)
    ⌜ tab_inits = module_inst_build_tables m inst ⌝ ∗
    ⌜ wts' = module_import_init_tabs m inst wts ⌝ ∗
    ⌜ module_elem_bound_check_gmap wts (fmap modexp_desc v_imps) m ⌝ ∗
    ⌜ mem_inits = module_inst_build_mems m inst ⌝ ∗
    ⌜ wms' = module_import_init_mems m inst wms ⌝ ∗
    ⌜ module_data_bound_check_gmap wms (fmap modexp_desc v_imps) m ⌝ ∗
    ⌜ module_glob_init_values m g_inits ⌝ ∗
    ⌜ glob_inits = module_inst_global_init (module_inst_global_base m.(mod_globals)) g_inits ⌝ ∗
    module_inst_resources_wasm m inst tab_inits mem_inits glob_inits. (* allocated wasm resources. This also specifies the information about the newly allocated part of the instance. *)

Definition module_restrictions (m: module) : Prop :=
  (* Initializers for globals are only values. This is not that much a restriction as it seems, since they can
     only be either values or get_globals (from immutable globals) anyway. *)
  (exists (vs: list value), fmap modglob_init m.(mod_globals) = fmap (fun v => [BI_const v]) vs) /\
  (exists (vi32s: list i32), fmap modelem_offset m.(mod_elem) = fmap (fun v => [BI_const (VAL_int32 v)]) vi32s) /\
  (exists (vi32s: list i32), fmap moddata_offset m.(mod_data) = fmap (fun v => [BI_const (VAL_int32 v)]) vi32s).

Lemma BI_const_assert_const1_i32 (es: list expr) (vs: list i32):
  es = fmap (fun v => [BI_const (VAL_int32 v)]) vs ->
  those (fmap assert_const1_i32 es) = Some vs.
Proof.
  move: es.
  elim: vs => //=.
  - by move => es ->.
  - move => v vs IH es Hes.
    destruct es => //=.
    inversion Hes; subst; clear Hes.
    simpl.
    rewrite - cat1s.
    erewrite those_app => //=; last by apply IH.
    by [].
Qed.

Lemma module_inst_build_tables_length m i :
  length (module_inst_build_tables m i) = length (mod_tables m).
Proof.
  unfold module_inst_build_tables.
  apply fold_left_preserve.
  { apply fmap_length. }
  { intros x me Heq.
    destruct me,modelem_table.
    destruct (n <? get_import_table_count m);auto.
    destruct (nth_error x (n - get_import_table_count m));auto.
    rewrite insert_length//. }
Qed.

Ltac forward H Hname :=
  lazymatch type of H with
  | ?Hx -> _ => let Hp := fresh "Hp" in
              assert Hx as Hp; last specialize (H Hp) as Hname end.

  
Lemma alloc_func_state_update funcs funcs' nf:
  funcs' = funcs ++ nf ->
  gen_heap_interp (gmap_of_list funcs) -∗ |==> 
  ((gen_heap_interp (gmap_of_list funcs')) ∗
   ([∗ list] i ↦ v ∈ nf, N.of_nat (length funcs + i) ↦[wf] v)).
Proof.
  move => Hfuncs; subst.
  iIntros "Hf".
  specialize (gmap_of_list_append_big funcs nf) as Hgmap.
  destruct Hgmap as [Hgunion Hgdisj].
  rewrite Hgunion.
  iDestruct (gen_heap_alloc_big with "Hf") as "Hf" => //.
  iMod "Hf".
  iModIntro.
  iDestruct "Hf" as "(Hf & Hfmaps & Hftoken)".
  rewrite map_union_comm => //.
  iFrame.
  rewrite big_opM_map_to_list.
  rewrite map_to_list_to_map; last first.
  (* TODO: refactor this proof *)
  { apply NoDup_fmap_fst.
    { move => x0 y3 z4 Hin1 Hin2.
      apply elem_of_lookup_imap in Hin1 as [i1 [z1 [Heq3 Hl3]]].
      apply elem_of_lookup_imap in Hin2 as [i2 [z2 [Heq4 Hl4]]].
      inversion Heq3; subst; clear Heq3.
      inversion Heq4; subst; clear Heq4.
      replace i2 with i1 in Hl4; last by lias.
      rewrite Hl3 in Hl4.
      by inversion Hl4.
    }
    {
      apply nodup_imap_inj1.
      move => n1 n2 t1 t2 H2.
      inversion H2; subst; clear H2.
      by lias.
    }
  }
  clear Hgunion Hgdisj.
  iClear "Hftoken".
  iInduction nf as [ | f'] "IH" using List.rev_ind => //=.
  rewrite imap_app.
  repeat rewrite big_sepL_app.
  iDestruct "Hfmaps" as "(Hfm1 & Hfm2)".
  iSplitL "Hfm1"; first by iApply "IH".
  simpl.
  by iFrame.
Qed.

(* TODO: This is an extremely atrocious proof with a lot of repetitions on
   similar but unidentical things. Refactor them as first priority after
   the main work is done. *)
Lemma alloc_tab_state_update tabs tabs' nt:
  tabs' = tabs ++ nt ->
  gen_heap_interp (gmap_of_table tabs) -∗
  gen_heap_interp (gmap_of_list (fmap tab_size tabs)) -∗
  gen_heap_interp (gmap_of_list (fmap table_max_opt tabs)) -∗ |==> 
  ((gen_heap_interp (gmap_of_table tabs')) ∗
   (gen_heap_interp (gmap_of_list (fmap tab_size tabs'))) ∗
   (gen_heap_interp (gmap_of_list (fmap table_max_opt tabs'))) ∗
   ([∗ list] i ↦ v ∈ nt, N.of_nat (length tabs + i) ↦[wtblock] v)).
Proof.
  move => Htabs; subst.
  iIntros "Ht Htsize Htlim".
  
  (* table data *)
  unfold gmap_of_table.
  specialize (gmap_of_list_2d_append_big (fmap table_to_list tabs) (fmap table_to_list nt)) as Hgmap.
  destruct Hgmap as [Hgunion Hgdisj].
  rewrite <- fmap_app in Hgunion.
  rewrite Hgunion.

  iDestruct (gen_heap_alloc_big with "Ht") as "Ht" => //.
  iMod "Ht".
  iDestruct "Ht" as "(Ht & Htmaps & Httoken)".
  rewrite map_union_comm => //.
  iFrame.
  clear Hgunion Hgdisj.
  
  (* table size *)
  specialize (gmap_of_list_append_big (tab_size <$> tabs) (tab_size <$> nt)) as Hgmap.
  destruct Hgmap as [Hgunion Hgdisj].
  rewrite fmap_app.
  rewrite Hgunion.

  iDestruct (gen_heap_alloc_big with "Htsize") as "Htsize" => //.
  iMod "Htsize".
  iDestruct "Htsize" as "(Htsize & Htsizemaps & Htsizetoken)".
  rewrite map_union_comm => //.
  iFrame.
  clear Hgunion Hgdisj.

  (* table lim *)
  specialize (gmap_of_list_append_big (table_max_opt <$> tabs) (table_max_opt <$> nt)) as Hgmap.
  destruct Hgmap as [Hgunion Hgdisj].
  rewrite fmap_app.
  rewrite Hgunion.
  
  iDestruct (gen_heap_alloc_big with "Htlim") as "Htlim" => //.
  iMod "Htlim".
  iDestruct "Htlim" as "(Htlim & Htlimmaps & Htlimtoken)".
  rewrite map_union_comm => //.
  iFrame.
  clear Hgunion Hgdisj.

  iClear "Httoken Htsizetoken Htlimtoken".

  repeat rewrite fmap_length.
  
  iInduction nt as [ | t'] "IH" using List.rev_ind => //=.
  repeat rewrite fmap_app => /=.
  repeat rewrite gmap_of_list_2d_offset_append_general.
  rewrite big_opM_union; last by apply gmap_of_list_2d_offset_append_disjoint; lias.
  repeat rewrite imap_app.
  repeat rewrite list_to_map_app.
  repeat rewrite big_opM_union; last first.
  { apply map_disjoint_list_to_map_l.
    rewrite List.Forall_forall.
    move => [x1 x2] Hin.
    apply not_elem_of_list_to_map => /=.
    apply elem_of_list_In in Hin.
    apply elem_of_lookup_imap in Hin.
    destruct Hin as [i [y [Heq Helem]]].
    inversion Heq; subst; clear Heq.
    move => Hcontra.
    apply elem_of_list_singleton in Hcontra.
    apply Nat2N.inj in Hcontra.
    rewrite list_lookup_fmap in Helem.
    destruct (nt !! i) eqn: Hntl => //.
    apply lookup_lt_Some in Hntl.
    rewrite fmap_length in Hcontra.
    by lias.
  }
  { apply map_disjoint_list_to_map_l.
    rewrite List.Forall_forall.
    move => [x1 x2] Hin.
    apply not_elem_of_list_to_map => /=.
    apply elem_of_list_In in Hin.
    apply elem_of_lookup_imap in Hin.
    destruct Hin as [i [y [Heq Helem]]].
    inversion Heq; subst; clear Heq.
    move => Hcontra.
    apply elem_of_list_singleton in Hcontra.
    apply Nat2N.inj in Hcontra.
    rewrite list_lookup_fmap in Helem.
    destruct (nt !! i) eqn: Hntl => //.
    apply lookup_lt_Some in Hntl.
    rewrite fmap_length in Hcontra.
    by lias.
  }

  iDestruct "Htmaps" as "(Htmapsnew & Htmapsold)".
  iDestruct "Htsizemaps" as "(Htsizemapsold & Htsizemapsnew)".
  iDestruct "Htlimmaps" as "(Htlimmapsold & Htlimmapsnew)".
  
  repeat rewrite big_sepL_app.
  
  repeat rewrite big_opM_map_to_list.
  repeat rewrite map_to_list_to_map; last first.
  { apply NoDup_fmap_fst.
    { move => x0 y3 z4 Hin1 Hin2.
      apply elem_of_lookup_imap in Hin1 as [i1 [z1 [Heq3 Hl3]]].
      apply elem_of_lookup_imap in Hin2 as [i2 [z2 [Heq4 Hl4]]].
      inversion Heq3; subst; clear Heq3.
      inversion Heq4; subst; clear Heq4.
      replace i2 with i1 in Hl4; last by lias.
      rewrite Hl3 in Hl4.
      by inversion Hl4.
    }
    {
      apply nodup_imap_inj1.
      move => n1 n2 t1 t2 H2.
      inversion H2; subst; clear H2.
      by lias.
    }
  }
  { apply NoDup_fmap_fst.
    { move => x0 y3 z4 Hin1 Hin2.
      apply elem_of_lookup_imap in Hin1 as [i1 [z1 [Heq3 Hl3]]].
      apply elem_of_lookup_imap in Hin2 as [i2 [z2 [Heq4 Hl4]]].
      inversion Heq3; subst; clear Heq3.
      inversion Heq4; subst; clear Heq4.
      replace i2 with i1 in Hl4; last by lias.
      rewrite Hl3 in Hl4.
      by inversion Hl4.
    }
    {
      apply nodup_imap_inj1.
      move => n1 n2 t1 t2 H2.
      inversion H2; subst; clear H2.
      by lias.
    }
  }
  { apply NoDup_fmap_fst.
    { move => x0 y3 z4 Hin1 Hin2.
      apply elem_of_lookup_imap in Hin1 as [i1 [z1 [Heq3 Hl3]]].
      apply elem_of_lookup_imap in Hin2 as [i2 [z2 [Heq4 Hl4]]].
      inversion Heq3; subst; clear Heq3.
      inversion Heq4; subst; clear Heq4.
      replace i2 with i1 in Hl4; last by lias.
      rewrite Hl3 in Hl4.
      by inversion Hl4.
    }
    {
      apply nodup_imap_inj1.
      move => n1 n2 t1 t2 H2.
      inversion H2; subst; clear H2.
      by lias.
    }
  }
  { apply NoDup_fmap_fst.
    { move => x0 y3 z4 Hin1 Hin2.
      apply elem_of_lookup_imap in Hin1 as [i1 [z1 [Heq3 Hl3]]].
      apply elem_of_lookup_imap in Hin2 as [i2 [z2 [Heq4 Hl4]]].
      inversion Heq3; subst; clear Heq3.
      inversion Heq4; subst; clear Heq4.
      replace i2 with i1 in Hl4; last by lias.
      rewrite Hl3 in Hl4.
      by inversion Hl4.
    }
    {
      apply nodup_imap_inj1.
      move => n1 n2 t1 t2 H2.
      inversion H2; subst; clear H2.
      by lias.
    }
  }
  { apply NoDup_fmap_fst.
    { move => [a0 b0] y3 z4 Hin1 Hin2.
      apply elem_of_list_fmap in Hin1 as [[[i1 j1] x1] [Heq1 Hl1]].
      apply elem_of_list_fmap in Hin2 as [[[i2 j2] x2] [Heq2 Hl2]].
      inversion Heq1; subst; clear Heq1.
      inversion Heq2; subst; clear Heq2.
      apply flatten_2d_list_lookup in Hl1.
      apply flatten_2d_list_lookup in Hl2.
      assert (i1 = i2); first by lias.
      subst. clear H0.
      rewrite Hl1 in Hl2.
      by inversion Hl2.
    }
    {
      apply NoDup_fmap; last by apply flatten_2d_list_nodup.
      unfold Inj.
      move => n1 n2 H2.
      destruct n1 as [[i1 j1] x1].
      destruct n2 as [[i2 j2] x2].
      inversion H2; subst; clear H2.
      repeat f_equal.
      by lias.
    }
  }
  { apply NoDup_fmap_fst.
    { move => [a0 b0] y3 z4 Hin1 Hin2.
      apply elem_of_lookup_imap in Hin1 as [i1 [z1 [Heq3 Hl3]]].
      apply elem_of_lookup_imap in Hin2 as [i2 [z2 [Heq4 Hl4]]].
      inversion Heq3; subst; clear Heq3.
      inversion Heq4; subst; clear Heq4.
      replace i2 with i1 in Hl4; last by lias.
      rewrite Hl3 in Hl4.
      by inversion Hl4.
    }
    {
      apply nodup_imap_inj1.
      move => n1 n2 t1 t2 H2.
      inversion H2; subst; clear H2.
      by lias.
    }
  }

  repeat rewrite fmap_length.
  repeat unfold tab_block.
  iSplitL "Htmapsold Htsizemapsold Htlimmapsold".
  - by iApply ("IH" with "[$] [$] [$]").
  - simpl.
    iDestruct "Htsizemapsnew" as "(Htsizemapsnew & _)".
    iDestruct "Htlimmapsnew" as "(Htlimmapsnew & _)".
    iMod (mapsto_persist with "Htsizemapsnew") as "Htsizemapsnew".
    iMod (mapsto_persist with "Htlimmapsnew") as "Htlimmapsnew".
    iModIntro.
    iFrame.
    unfold table_to_list.
    iClear "IH".
    remember (table_data t') as td.
    clear Heqtd t'.
    iInduction td as [ | v] "IH" using List.rev_ind => //=.
    rewrite imap_app.
    rewrite big_sepL_app.
    iDestruct "Htmapsnew" as "(Htd0 & (Htd1 & _))" => /=.
    rewrite Nat.add_0_r.
    iSplitL "Htd0" => /=.
    + rewrite Nat2N.inj_add.
      rewrite N.add_comm.
      by iApply "IH".
    + rewrite Nat2N.inj_add.
      rewrite N.add_comm.
      by iFrame.
Qed.  
  
Lemma alloc_mem_state_update mems mems' nm:
  mems' = mems ++ nm ->
  gen_heap_interp (gmap_of_memory mems) -∗
  gen_heap_interp (gmap_of_list (fmap mem_length mems)) -∗
  gen_heap_interp (gmap_of_list (fmap mem_max_opt mems)) -∗ |==> 
  ((gen_heap_interp (gmap_of_memory mems')) ∗
   (gen_heap_interp (gmap_of_list (fmap mem_length mems'))) ∗
   (gen_heap_interp (gmap_of_list (fmap mem_max_opt mems'))) ∗
   ([∗ list] i ↦ v ∈ nm, N.of_nat (length mems + i) ↦[wmblock] v)).
Proof.
  move => Hmems; subst.
  iIntros "Ht Htsize Htlim".
  
  (* table data *)
  unfold gmap_of_memory.
  specialize (gmap_of_list_2d_append_big (fmap memory_to_list mems) (fmap memory_to_list nm)) as Hgmap.
  destruct Hgmap as [Hgunion Hgdisj].
  rewrite <- fmap_app in Hgunion.
  rewrite Hgunion.

  iDestruct (gen_heap_alloc_big with "Ht") as "Ht" => //.
  iMod "Ht".
  iDestruct "Ht" as "(Ht & Htmaps & Httoken)".
  rewrite map_union_comm => //.
  iFrame.
  clear Hgunion Hgdisj.
  
  (* table size *)
  specialize (gmap_of_list_append_big (mem_length <$> mems) (mem_length <$> nm)) as Hgmap.
  destruct Hgmap as [Hgunion Hgdisj].
  rewrite fmap_app.
  rewrite Hgunion.

  iDestruct (gen_heap_alloc_big with "Htsize") as "Htsize" => //.
  iMod "Htsize".
  iDestruct "Htsize" as "(Htsize & Htsizemaps & Htsizetoken)".
  rewrite map_union_comm => //.
  iFrame.
  clear Hgunion Hgdisj.

  (* table lim *)
  specialize (gmap_of_list_append_big (mem_max_opt <$> mems) (mem_max_opt <$> nm)) as Hgmap.
  destruct Hgmap as [Hgunion Hgdisj].
  rewrite fmap_app.
  rewrite Hgunion.
  
  iDestruct (gen_heap_alloc_big with "Htlim") as "Htlim" => //.
  iMod "Htlim".
  iDestruct "Htlim" as "(Htlim & Htlimmaps & Htlimtoken)".
  rewrite map_union_comm => //.
  iFrame.
  clear Hgunion Hgdisj.

  iClear "Httoken Htsizetoken Htlimtoken".

  repeat rewrite fmap_length.
  
  iInduction nm as [ | m'] "IH" using List.rev_ind => //=.
  repeat rewrite fmap_app => /=.
  repeat rewrite gmap_of_list_2d_offset_append_general.
  rewrite big_opM_union; last by apply gmap_of_list_2d_offset_append_disjoint; lias.
  repeat rewrite imap_app.
  repeat rewrite list_to_map_app.
  repeat rewrite big_opM_union; last first.
  { apply map_disjoint_list_to_map_l.
    rewrite List.Forall_forall.
    move => [x1 x2] Hin.
    apply not_elem_of_list_to_map => /=.
    apply elem_of_list_In in Hin.
    apply elem_of_lookup_imap in Hin.
    destruct Hin as [i [y [Heq Helem]]].
    inversion Heq; subst; clear Heq.
    move => Hcontra.
    apply elem_of_list_singleton in Hcontra.
    apply Nat2N.inj in Hcontra.
    rewrite list_lookup_fmap in Helem.
    destruct (nm !! i) eqn: Hnml => //.
    apply lookup_lt_Some in Hnml.
    rewrite fmap_length in Hcontra.
    by lias.
  }
  { apply map_disjoint_list_to_map_l.
    rewrite List.Forall_forall.
    move => [x1 x2] Hin.
    apply not_elem_of_list_to_map => /=.
    apply elem_of_list_In in Hin.
    apply elem_of_lookup_imap in Hin.
    destruct Hin as [i [y [Heq Helem]]].
    inversion Heq; subst; clear Heq.
    move => Hcontra.
    apply elem_of_list_singleton in Hcontra.
    apply Nat2N.inj in Hcontra.
    rewrite list_lookup_fmap in Helem.
    destruct (nm !! i) eqn: Hnml => //.
    apply lookup_lt_Some in Hnml.
    rewrite fmap_length in Hcontra.
    by lias.
  }

  iDestruct "Htmaps" as "(Htmapsnew & Htmapsold)".
  iDestruct "Htsizemaps" as "(Htsizemapsold & Htsizemapsnew)".
  iDestruct "Htlimmaps" as "(Htlimmapsold & Htlimmapsnew)".
  
  repeat rewrite big_sepL_app.
  
  repeat rewrite big_opM_map_to_list.
  repeat rewrite map_to_list_to_map; last first.
  { apply NoDup_fmap_fst.
    { move => x0 y3 z4 Hin1 Hin2.
      apply elem_of_lookup_imap in Hin1 as [i1 [z1 [Heq3 Hl3]]].
      apply elem_of_lookup_imap in Hin2 as [i2 [z2 [Heq4 Hl4]]].
      inversion Heq3; subst; clear Heq3.
      inversion Heq4; subst; clear Heq4.
      replace i2 with i1 in Hl4; last by lias.
      rewrite Hl3 in Hl4.
      by inversion Hl4.
    }
    {
      apply nodup_imap_inj1.
      move => n1 n2 t1 t2 H2.
      inversion H2; subst; clear H2.
      by lias.
    }
  }
  { apply NoDup_fmap_fst.
    { move => x0 y3 z4 Hin1 Hin2.
      apply elem_of_lookup_imap in Hin1 as [i1 [z1 [Heq3 Hl3]]].
      apply elem_of_lookup_imap in Hin2 as [i2 [z2 [Heq4 Hl4]]].
      inversion Heq3; subst; clear Heq3.
      inversion Heq4; subst; clear Heq4.
      replace i2 with i1 in Hl4; last by lias.
      rewrite Hl3 in Hl4.
      by inversion Hl4.
    }
    {
      apply nodup_imap_inj1.
      move => n1 n2 t1 t2 H2.
      inversion H2; subst; clear H2.
      by lias.
    }
  }
  { apply NoDup_fmap_fst.
    { move => x0 y3 z4 Hin1 Hin2.
      apply elem_of_lookup_imap in Hin1 as [i1 [z1 [Heq3 Hl3]]].
      apply elem_of_lookup_imap in Hin2 as [i2 [z2 [Heq4 Hl4]]].
      inversion Heq3; subst; clear Heq3.
      inversion Heq4; subst; clear Heq4.
      replace i2 with i1 in Hl4; last by lias.
      rewrite Hl3 in Hl4.
      by inversion Hl4.
    }
    {
      apply nodup_imap_inj1.
      move => n1 n2 t1 t2 H2.
      inversion H2; subst; clear H2.
      by lias.
    }
  }
  { apply NoDup_fmap_fst.
    { move => x0 y3 z4 Hin1 Hin2.
      apply elem_of_lookup_imap in Hin1 as [i1 [z1 [Heq3 Hl3]]].
      apply elem_of_lookup_imap in Hin2 as [i2 [z2 [Heq4 Hl4]]].
      inversion Heq3; subst; clear Heq3.
      inversion Heq4; subst; clear Heq4.
      replace i2 with i1 in Hl4; last by lias.
      rewrite Hl3 in Hl4.
      by inversion Hl4.
    }
    {
      apply nodup_imap_inj1.
      move => n1 n2 t1 t2 H2.
      inversion H2; subst; clear H2.
      by lias.
    }
  }
  { apply NoDup_fmap_fst.
    { move => [a0 b0] y3 z4 Hin1 Hin2.
      apply elem_of_list_fmap in Hin1 as [[[i1 j1] x1] [Heq1 Hl1]].
      apply elem_of_list_fmap in Hin2 as [[[i2 j2] x2] [Heq2 Hl2]].
      inversion Heq1; subst; clear Heq1.
      inversion Heq2; subst; clear Heq2.
      apply flatten_2d_list_lookup in Hl1.
      apply flatten_2d_list_lookup in Hl2.
      assert (i1 = i2); first by lias.
      subst. clear H0.
      rewrite Hl1 in Hl2.
      by inversion Hl2.
    }
    {
      apply NoDup_fmap; last by apply flatten_2d_list_nodup.
      unfold Inj.
      move => n1 n2 H2.
      destruct n1 as [[i1 j1] x1].
      destruct n2 as [[i2 j2] x2].
      inversion H2; subst; clear H2.
      repeat f_equal.
      by lias.
    }
  }
  { apply NoDup_fmap_fst.
    { move => [a0 b0] y3 z4 Hin1 Hin2.
      apply elem_of_lookup_imap in Hin1 as [i1 [z1 [Heq3 Hl3]]].
      apply elem_of_lookup_imap in Hin2 as [i2 [z2 [Heq4 Hl4]]].
      inversion Heq3; subst; clear Heq3.
      inversion Heq4; subst; clear Heq4.
      replace i2 with i1 in Hl4; last by lias.
      rewrite Hl3 in Hl4.
      by inversion Hl4.
    }
    {
      apply nodup_imap_inj1.
      move => n1 n2 t1 t2 H2.
      inversion H2; subst; clear H2.
      by lias.
    }
  }

  repeat rewrite fmap_length.
  repeat unfold tab_block.
  iSplitL "Htmapsold Htsizemapsold Htlimmapsold".
  - by iApply ("IH" with "[$] [$] [$]").
  - simpl.
    iDestruct "Htsizemapsnew" as "(Htsizemapsnew & _)".
    iDestruct "Htlimmapsnew" as "(Htlimmapsnew & _)".
    iMod (mapsto_persist with "Htlimmapsnew") as "Htlimmapsnew".
    iModIntro.
    iFrame.
    unfold table_to_list.
    iClear "IH".
    unfold memory_to_list.
    remember (ml_data (mem_data m')) as md.
    clear Heqmd m'.
    iInduction md as [ | v] "IH" using List.rev_ind => //=.
    rewrite imap_app.
    rewrite big_sepL_app.
    iDestruct "Htmapsnew" as "(Htd0 & (Htd1 & _))" => /=.
    rewrite Nat.add_0_r.
    iSplitL "Htd0" => /=.
    + rewrite Nat2N.inj_add.
      rewrite N.add_comm.
      by iApply "IH".
    + rewrite Nat2N.inj_add.
      rewrite N.add_comm.
      by iFrame.
Qed.
      
Lemma alloc_glob_state_update globs globs' ng:
  globs' = globs ++ ng ->
  gen_heap_interp (gmap_of_list globs) -∗ |==> 
  ((gen_heap_interp (gmap_of_list globs')) ∗
  ([∗ list] i ↦ v ∈ ng, N.of_nat (length globs + i) ↦[wg] v)).
Proof.
  move => Hglobs; subst.
  iIntros "Hg".
  specialize (gmap_of_list_append_big globs ng) as Hgmap.
  destruct Hgmap as [Hgunion Hgdisj].
  rewrite Hgunion.
  iDestruct (gen_heap_alloc_big with "Hg") as "Hg" => //.
  iMod "Hg".
  iModIntro.
  iDestruct "Hg" as "(Hg & Hgmaps & Hgtoken)".
  rewrite map_union_comm => //.
  iFrame.
  rewrite big_opM_map_to_list.
  rewrite map_to_list_to_map; last first.
  (* TODO: refactor this proof *)
  { apply NoDup_fmap_fst.
    { move => x0 y3 z4 Hin1 Hin2.
      apply elem_of_lookup_imap in Hin1 as [i1 [z1 [Heq3 Hl3]]].
      apply elem_of_lookup_imap in Hin2 as [i2 [z2 [Heq4 Hl4]]].
      inversion Heq3; subst; clear Heq3.
      inversion Heq4; subst; clear Heq4.
      replace i2 with i1 in Hl4; last by lias.
      rewrite Hl3 in Hl4.
      by inversion Hl4.
    }
    {
      apply nodup_imap_inj1.
      move => n1 n2 t1 t2 H2.
      inversion H2; subst; clear H2.
      by lias.
    }
  }
  clear Hgunion Hgdisj.
  iClear "Hgtoken".
  iInduction ng as [ | g'] "IH" using List.rev_ind => //=.
  rewrite imap_app.
  repeat rewrite big_sepL_app.
  iDestruct "Hgmaps" as "(Hgm1 & Hgm2)".
  iSplitL "Hgm1"; first by iApply "IH".
  simpl.
  by iFrame.
Qed.

Lemma insert_at_insert {T: Type} v n (l: list T):
  n < length l ->
  insert_at v n l = <[ n := v ]> l.
Proof.
  move : v n.
  induction l; intros; simpl in H; destruct n => /=; try by inversion H.
  - specialize (IHl v n).
    unfold insert_at.
    simpl.
    f_equal.
    rewrite <- IHl; last by lias.
    by unfold insert_at.
Qed.

Definition update_tab tabs n off td' : option (list tableinst) :=
  match tabs !! n with
  | Some tab =>
    if off + length td' <=? length tab.(table_data) then
      Some (<[ n := {| table_data := take off tab.(table_data) ++ td' ++ drop (off + length td') tab.(table_data); table_max_opt := tab.(table_max_opt) |} ]> tabs)
    else None
  | None => None
  end.

Lemma update_nil_id tabs n off tabs':
  update_tab tabs n off [] = Some tabs' ->
  tabs = tabs'.
Proof.
  unfold update_tab.
  destruct (_ !! _) eqn: Htab => //.
  destruct (_ <=? _) => //.
  move => H.
  inversion H; subst; clear H.
  rewrite Nat.add_0_r.
  rewrite cat_app.
  rewrite -> (take_drop off (table_data t)).
  rewrite list_insert_id => //.
  rewrite Htab.
  by destruct t.
Qed.

(* Nothing interesting, mainly numerical and string massages *)
Lemma update_tab_shift tabs tabs' n off t td':
  update_tab tabs n off (t :: td') = Some tabs' ->
  exists tabs0, update_tab tabs n off [t] = Some tabs0 /\
           update_tab tabs0 n (off+1) td' = Some tabs'.
Proof.
  unfold update_tab.
  destruct (tabs !! n) eqn: Htab => //=.
  destruct (_ <=? _) eqn: Hle => //=.
  move => H.
  inversion H; subst; clear H.
  rewrite -> PeanoNat.Nat.leb_le in Hle.
  eexists. split.
  - assert (off+1 <=? length (table_data t0)) as Hle2.
    { apply PeanoNat.Nat.leb_le.
      by lias. }
    by rewrite Hle2. 
  - rewrite list_lookup_insert => /=; last by eapply lookup_lt_Some.
    rewrite app_length take_length => /=; rewrite drop_length.
    assert (off + 1 + length td' <=? off `min` length (table_data t0) + S (length (table_data t0) - (off+1))) as Hle2.
    {
      apply PeanoNat.Nat.leb_le.
      by lias.
    }
    rewrite Hle2.
    f_equal.
    rewrite list_insert_insert.
    do 2 f_equal.
    replace (take off (table_data t0) ++ _ :: drop (off + 1) (table_data t0)) with (((take off (table_data t0)) ++ [t]) ++ drop (off+1) (table_data t0)); last first.
    {
      rewrite <- app_assoc.
      by f_equal.
    }
    rewrite take_app_alt; last first.
    { rewrite app_length take_length => /=.
      by lias.
    }
    rewrite <- app_assoc => /=.
    do 3 f_equal.
    Search drop "+".
    rewrite <- drop_drop.
    rewrite drop_app_alt; last first.
    { rewrite app_length take_length => /=.
      by lias.
    }
    rewrite drop_drop.
    f_equal.
    by lias.
Qed.
    
(* Auxiliary lemma for handling update of table segments at arbitrary offsets *)
Lemma tab_block_update_aux off td td' n tabs tabs':
  length td = length td' ->
  update_tab tabs n off td' = Some tabs' ->
  ([∗ list] i↦telem ∈ td, (N.of_nat n)↦[wt][N.of_nat (off + i)] telem)%I -∗
   gen_heap_interp (gmap_of_table tabs) -∗
   |==>
  ([∗ list] i↦telem ∈ td', (N.of_nat )n↦[wt][N.of_nat (off + i)] telem) ∗
  gen_heap_interp (gmap_of_table tabs').
Proof.
  move: tabs tabs' n td' off.
  iInduction (td) as [|?] "IH"; iIntros (tabs tabs' n td' off Hlen Hupdate) "Htm Ht"; destruct td' => //=.
  { apply update_nil_id in Hupdate; subst.
    by iFrame. }
  simpl in Hlen.
  iDestruct "Htm" as "(Htm0 & Htm)".
  iDestruct (gen_heap_valid with "Ht Htm0") as "%H".
  iMod (gen_heap_update with "Ht Htm0") as "(Ht & Htm0)".
  iFrame.
  
  assert (length td = length td') as Hlen'; first by lias.
  clear Hlen.
  apply update_tab_shift in Hupdate.
  destruct Hupdate as [tabs0 [Hupd1 Hupd2]].
  iSpecialize ("IH" $! _ tabs' n td' (off+1) Hlen' Hupd2 with "[Htm] [Ht]").
  { iApply (big_sepL_mono with "Htm").
    iIntros (???) "?".
    by replace (off + S k) with (off + 1 + k); last by lias.
  }
  { unfold gmap_of_table in H.
    rewrite gmap_of_list_2d_lookup in H.
    simplify_lookup.
    rewrite list_lookup_fmap in Heq.
    destruct (tabs !! n) eqn: Htablookup => //=.
    simpl in Heq.
    inversion Heq; subst; clear Heq.
    erewrite (gmap_of_table_insert); rewrite Nat2N.id => //=.
    - unfold update_tab in Hupd1.
      rewrite Htablookup in Hupd1.
      simpl in Hupd1.
      destruct (off+1 <=? length (table_data t)) eqn:Hlen => //.
      simpl in Hupd1.
      inversion Hupd1; subst; clear Hupd1.
      replace (off+1) with (S off); last by lias.
      rewrite <- (insert_take_drop (table_data t)).
      + rewrite Nat2N.id.
        by rewrite Nat.add_0_r.
      + rewrite -> PeanoNat.Nat.leb_le in Hlen.
        by lias.
    - unfold table_to_list in H.
      by eapply lookup_lt_Some.
  }
  iMod "IH" as "(Htm & Ht)".
  iFrame.
  iApply (big_sepL_mono with "Htm").
  iIntros (???) "?".
  by replace (off + S k) with (off + 1 + k); last by lias.
Qed.
  
Lemma tab_block_update tab tab' n ws ws':
  tab_size tab = tab_size tab' ->
  table_max_opt tab = table_max_opt tab' -> 
  ws'.(s_tables) = <[ n := tab' ]> ws.(s_tables) ->
  (N.of_nat n) ↦[wtblock] tab -∗
  gen_heap_interp (gmap_of_table ws.(s_tables)) -∗
  gen_heap_interp (gmap_of_list (tab_size <$> ws.(s_tables))) -∗
  gen_heap_interp (gmap_of_list (table_max_opt <$> ws.(s_tables))) -∗
  |==>
  (N.of_nat n) ↦[wtblock] tab' ∗
  gen_heap_interp (gmap_of_table ws'.(s_tables)) ∗
  gen_heap_interp (gmap_of_list (tab_size <$> ws'.(s_tables))) ∗
  gen_heap_interp (gmap_of_list (table_max_opt <$> ws'.(s_tables))).
Proof.
  move => Htabsize Htablim Hws'.
  iIntros "Htmapsto Ht Htsize Htlim".
  iDestruct (tab_block_lookup with "Ht Htsize Htlim Htmapsto") as "%Htab".
  rewrite Nat2N.id in Htab.
  destruct tab => /=.
  destruct tab' => /=.
  simpl in *; subst.
  unfold tab_block.
  iDestruct "Htmapsto" as "(Htm & Htsizem & Htlimm)".
  replace (tab_size <$> s_tables ws') with (tab_size <$> s_tables ws); last first.
  {
    rewrite Hws' => /=.
    rewrite list_fmap_insert => /=.
    rewrite list_insert_id => //.
    rewrite list_lookup_fmap.
    rewrite Htab.
    by rewrite <- Htabsize.
  }
  replace (datatypes.table_max_opt <$> s_tables ws') with (datatypes.table_max_opt <$> s_tables ws); last first.
  {
    rewrite Hws' => /=.
    rewrite list_fmap_insert => /=.   
    rewrite list_insert_id => //.
    rewrite list_lookup_fmap.
    by rewrite Htab.    
  }
  rewrite Hws'; simpl in *.
  rewrite Htabsize.
  iFrame.

  unfold tab_size in *.
  simpl in Htabsize.
  (* Now, update the contents *)
  destruct ws, ws' => /=.
  simpl in *.
  clear s_funcs s_mems s_globals s_funcs0 s_mems0 s_globals0.

  iDestruct (tab_block_update_aux with "[Htm] [Ht]") as "H" => //.
  2: { by instantiate (1 := 0). }
  2: { by iFrame. }
  unfold update_tab.
  rewrite Htab => /=.
  rewrite Htabsize => /=.
  rewrite PeanoNat.Nat.leb_refl.
  repeat f_equal.
  rewrite <- Htabsize.
  rewrite drop_all.
  by rewrite cats0.
Qed.

Lemma init_tab_state_update ws ws' inst e_ind e t_ind tab e_pay:
  init_tab ws inst e_ind e = ws' ->
  t_ind = nth match modelem_table e with | Mk_tableidx i => i end (inst_tab inst) 0 ->
  e_pay = map (fun i => nth_error (inst_funcs inst) match i with
                                                | Mk_funcidx j => j end
              ) (e.(modelem_init)) ->
  e_ind + length e.(modelem_init) <= length (tab.(table_data)) ->
  (N.of_nat t_ind) ↦[wtblock] tab -∗
  gen_heap_interp (gmap_of_table ws.(s_tables)) -∗
  gen_heap_interp (gmap_of_list (tab_size <$> ws.(s_tables))) -∗
  gen_heap_interp (gmap_of_list (table_max_opt <$> ws.(s_tables))) -∗
  |==>
  (N.of_nat t_ind) ↦[wtblock] {| table_data := take e_ind tab.(table_data) ++ e_pay ++ drop (ssrnat.addn e_ind (length e_pay)) tab.(table_data); table_max_opt := tab.(table_max_opt) |} ∗
  gen_heap_interp (gmap_of_table ws'.(s_tables)) ∗
  gen_heap_interp (gmap_of_list (tab_size <$> ws'.(s_tables))) ∗
  gen_heap_interp (gmap_of_list (table_max_opt <$> ws'.(s_tables))).
Proof.
  move => Hinittab Htind Hepay Heboundcheck.
  unfold init_tab in Hinittab.
  iIntros "Htmapsto Ht Htsize Htlim".
  iDestruct (tab_block_lookup with "Ht Htsize Htlim Htmapsto") as "%Htab".
  rewrite Nat2N.id in Htab.
  rewrite <- Htind in Hinittab.
  rewrite <- Hepay in Hinittab.
  assert (nth t_ind (s_tables ws) dummy_table = tab) as Htablookup.
  {
    apply nth_error_nth.
    by rewrite nth_error_lookup.
  }
  rewrite Htablookup in Hinittab.
  (* Only the table content needs to get a state update. However, we have to 
     prove that the other state interps stay the same. *)
  destruct tab => /=.
  iApply (tab_block_update with "[$] [$] [$] [$]") => //.
  {
    unfold tab_size => /=.
    repeat rewrite app_length.
    rewrite take_length drop_length.
    rewrite Hepay.
    rewrite map_length.
    simpl in Heboundcheck.
    by lias.
  }
  {
    rewrite <- Hinittab => /=.
    by rewrite insert_at_insert; last by eapply lookup_lt_Some.
  }
Qed.







Lemma init_tabs_state_update ws ws' inst e_inits m v_imps t_imps wfs wts wms wgs:
  let wts' := module_import_init_tabs m inst wts in
  ⌜init_tabs ws inst e_inits m.(mod_elem) = ws'⌝ -∗
  (import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
  gen_heap_interp (gmap_of_table ws.(s_tables)) -∗
  gen_heap_interp (gmap_of_list (tab_size <$> ws.(s_tables))) -∗
  gen_heap_interp (gmap_of_list (table_max_opt <$> ws.(s_tables))) -∗
  ([∗ list] i↦v ∈ ((λ '{|
                        tt_limits :=
                          {| lim_min := min; lim_max := maxo |}
                      |},
                    {|
                      table_data :=
                        repeat None (ssrnat.nat_of_bin min);
                      table_max_opt := maxo
                    |}) <$> map modtab_type (mod_tables m)),
   N.of_nat (length ws.(s_tables) - length (mod_tables m) + i)↦[wtblock]v) -∗
 |==>
  (import_resources_wasm_typecheck v_imps t_imps wfs wts' wms wgs ∗
  gen_heap_interp (gmap_of_table ws'.(s_tables)) ∗
  gen_heap_interp (gmap_of_list (tab_size <$> ws'.(s_tables))) ∗
  gen_heap_interp (gmap_of_list (table_max_opt <$> ws'.(s_tables))) ∗
  module_inst_resources_tab (module_inst_build_tables m inst) (drop (get_import_table_count m) inst.(inst_tab))))%I.
Proof.
  destruct m => /=.
  move: ws ws' inst e_inits mod_types mod_funcs mod_tables mod_mems mod_globals mod_data mod_start mod_imports mod_exports v_imps t_imps wfs wts wms wgs.
  induction mod_elem; intros.
  - unfold init_tabs.
    rewrite combine_nil => /=.
    iIntros "%Heq"; subst.
    iIntros "Hwasm Hwt Hwtsize Hwtlim Hwtmapsto".
    iFrame.
Admitted.

(*
Lemma init_mems_state_update ws ws' inst d_inits m v_imps t_imps wfs wts wms wgs:
  let wms' := module_import_init_mems m inst wms in
  (* initialisers implementation in basic Wasm *)
  ⌜init_mems ws inst d_inits m.(mod_data) = ws'⌝ -∗
  (* resources and contents for the imported states *)
  (import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
  (* heap interpretations for memory-related states *)
  gen_heap_interp (gmap_of_memory ws.(s_mems)) -∗
  gen_heap_interp (gmap_of_list (mem_length <$> ws.(s_mems))) -∗
  gen_heap_interp (gmap_of_list (mem_max_opt <$> ws.(s_mems))) -∗
  (* memory mapstos *)
  ([∗ list] i↦v ∈ ((λ '{| lim_min := min; lim_max := maxo |},
                   {|
                     mem_data :=
                       mem_make #00%byte
                                match min with
                                | 0%N => 0%N
                                | N.pos q => N.pos (64 * 1024 * q)
                                end;
                     mem_max_opt := maxo
                   |}) <$> mod_mems m),
   N.of_nat (length ws.(s_mems) + i - length (m.(mod_mems)))↦[wmblock]v) -∗
  |==>
  (import_resources_wasm_typecheck v_imps t_imps wfs wts wms' wgs ∗
  gen_heap_interp (gmap_of_memory ws'.(s_mems)) ∗
  gen_heap_interp (gmap_of_list (mem_length <$> ws'.(s_mems))) ∗
  gen_heap_interp (gmap_of_list (mem_max_opt <$> ws'.(s_mems))) ∗
  module_inst_resources_mem (module_inst_build_mems m inst) (drop (get_import_mem_count m) inst.(inst_memory))))%I.
Proof.
Admitted.
*)

Lemma init_mems_state_update ws ws' inst d_inits m v_imps t_imps wfs wts wms wgs:
  let wms' := module_import_init_mems m inst wms in
  ⌜init_mems ws inst d_inits m.(mod_data) = ws'⌝ -∗
  (import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
  gen_heap_interp (gmap_of_memory ws.(s_mems)) -∗
  gen_heap_interp (gmap_of_list (mem_length <$> ws.(s_mems))) -∗
  gen_heap_interp (gmap_of_list (mem_max_opt <$> ws.(s_mems))) -∗
  ([∗ list] i↦v ∈ ((λ '{| lim_min := min; lim_max := maxo |},
                   {|
                     mem_data :=
                       mem_make #00%byte
                                match min with
                                | 0%N => 0%N
                                | N.pos q => N.pos (64 * 1024 * q)
                                end;
                     mem_max_opt := maxo
                   |}) <$> mod_mems m),
   N.of_nat (length ws.(s_mems) + i - length (m.(mod_mems)))↦[wmblock]v) -∗
  |==>
  (import_resources_wasm_typecheck v_imps t_imps wfs wts wms' wgs ∗
  gen_heap_interp (gmap_of_memory ws'.(s_mems)) ∗
  gen_heap_interp (gmap_of_list (mem_length <$> ws'.(s_mems))) ∗
  gen_heap_interp (gmap_of_list (mem_max_opt <$> ws'.(s_mems))) ∗
  module_inst_resources_mem (module_inst_build_mems m inst) (drop (get_import_mem_count m) inst.(inst_memory))))%I.
Proof.
  assert (length (inst_memory inst) = length m.(mod_mems) + get_import_mem_count m) as Hinstmemlen; first admit.
  destruct m => /=.
  move: Hinstmemlen.
  move: ws ws' inst d_inits mod_types mod_funcs mod_tables mod_mems mod_globals mod_elem mod_start mod_imports mod_exports v_imps t_imps wfs wts wms wgs.
  induction mod_data; intros.
  - unfold init_mems.
    rewrite combine_nil => /=.
    iIntros "%Heq"; subst.
    iIntros "Hwasm Hwm Hwmlength Hwmlim Hwmmapsto".
    iFrame.
    iModIntro.
    unfold module_inst_resources_mem.
    unfold module_inst_build_mems => /=.
    unfold module_inst_mem_base.
    unfold module_inst_mem_base_func => /=.
    unfold get_import_mem_count in * => /=.
    
    simpl in Hinstmemlen.
    iRevert (Hinstmemlen).
    iRevert (mod_imports).
    iRevert (inst).
    iRevert "Hwmmapsto".

    iInduction (mod_mems) as [|?] "IH" => //=.
    + iIntros (_ inst mod_imports Hinstmemlen).
      simpl in Hinstmemlen.
      rewrite <- Hinstmemlen.
      by rewrite drop_all.
    + iIntros "Hwmmapsto".
      iIntros (inst mod_imports Hinstmemlen).
      simpl in *.
      destruct inst => /=.
      destruct inst_memory => //.
      iDestruct "Hwmmapsto" as "(Hm & Hwmmapsto)".
      remember (drop _ _) as mindex.
      assert (length mindex > 0) as Hmindexlen.
      { rewrite Heqmindex.
        rewrite drop_length.
        rewrite Hinstmemlen.
        by lias.
      }
      destruct mindex => /=.
      { exfalso.
        simpl in Hmindexlen.
        by inversion Hmindexlen.
      }
      iSplitL "Hm".
      { admit.
      }
      {
        simpl.
        assert (forall a b c, a+(S b) - (S c) = a+b-c); first by lias.
        admit.
      }
  admit.
Admitted.

Lemma module_inst_build_tables_nil m inst:
  m.(mod_tables) = [] ->
  module_inst_build_tables m inst = [].
Proof.
  move => Hempty.
  unfold module_inst_build_tables.
  rewrite Hempty. clear Hempty => /=.
  apply fold_left_preserve => //.
  move => x me ->.
  destruct me => /=.
  destruct modelem_table => /=.
  destruct (n <? get_import_table_count m) eqn:? => //=.
  by rewrite Coqlib.nth_error_nil.
Qed.

Lemma reduce_trans_const s1 f1 v1 s2 f2 v2:
  reduce_trans (s1, f1, [AI_basic (BI_const v1)]) (s2, f2, [AI_basic (BI_const v2)]) ->
  v1 = v2.
Proof.
  move => Hred.
  unfold reduce_trans in Hred.
  apply Operators_Properties.clos_rt_rt1n_iff in Hred.
  inversion Hred => //.
  unfold reduce_tuple in H.
  destruct y as [[??]?].
  by apply test_no_reduce1 in H.
Qed.
  
Lemma instantiation_wasm_spec (v_imps: list module_export) (m: module) t_imps t_exps wfs wts wms wgs (s s': store_record) inst v_exps start: 
  module_typing m t_imps t_exps ->
  module_restrictions m ->
  instantiate s m (fmap modexp_desc v_imps) (s', inst, v_exps, start) ->
  (instantiation_resources_pre_wasm m v_imps t_imps wfs wts wms wgs -∗
   gen_heap_wasm_store s -∗
   |==> (instantiation_resources_post_wasm m v_imps t_imps wfs wts wms wgs start) inst ∗
   gen_heap_wasm_store s').
Proof.
  move => Hmodtype Hmodrestr Hinstantiate.
  iIntros "(Himpwasm & %Hebound & %Hdbound)".
  iIntros "Hσ".
  iDestruct "Hσ" as "(Hwf & Hwt & Hwm & Hwg & Hmsize & Htsize & Hmlimit & Htlimit)".
  
  iDestruct (import_resources_wasm_lookup with "Hwf Hwt Hwm Hwg Htsize Htlimit Hmsize Hmlimit Himpwasm") as "%Himpwasm".
  
  destruct Himpwasm as [Hvtlen Himpwasm].
 
  unfold import_resources_wasm_typecheck.
  unfold instantiation_resources_post_wasm.

  unfold instantiate in Hinstantiate.

  destruct Hinstantiate as [t_imps' [t_exps' [s'' [g_inits [e_offs [d_offs [Hmodtype' [Hexttype [Hallocmod [Hinstglob [Hinstelem [Hinstdata [Helemcb [Hdatacb [Hcheckstart Hs']]]]]]]]]]]]]]].

  specialize (module_typing_det m t_imps t_exps t_imps' t_exps' Hmodtype Hmodtype') as Hteq.
  inversion Hteq as [H].
  symmetry in H, H0; subst; clear Hteq.
  
  destruct Hmodrestr as [[g_inits' Hmodglob] [[e_inits' Hmodelem] [d_inits' Hmoddata]]].

  unfold instantiate_globals in Hinstglob.
  unfold instantiate_elem in Hinstelem.
  unfold instantiate_data in Hinstdata.

  assert (g_inits = g_inits') as Hginitseq.
  {
    apply list_eq.
    move => i.
    rewrite -> Forall2_lookup in Hinstglob.
    specialize (Hinstglob i).
    assert (modglob_init <$> (mod_globals m !! i) = (fun v => [BI_const v]) <$> g_inits' !! i) as Hmgeq; first by repeat rewrite - list_lookup_fmap; rewrite Hmodglob.
    destruct (mod_globals m !! i) eqn:Hmgi => /=.
    - inversion Hinstglob; subst.
      simpl in Hmgeq.
      destruct (g_inits' !! i) eqn:Hmgi' => //.
      simpl in Hmgeq.
      inversion Hmgeq; clear Hmgeq.
      rewrite H2 in H1.
      simpl in H1.
      apply reduce_trans_const in H1.
      by subst.
    - inversion Hinstglob; subst.
      simpl in Hmgeq.
      by destruct (g_inits' !! i) eqn:Hmgi' => //.
  }

  symmetry in Hginitseq.
  subst.
  
  assert (fmap typeof g_inits = fmap (tg_t ∘ modglob_type) m.(mod_globals)) as Hginitstype.
  {
    unfold module_typing in Hmodtype.
    destruct m => /=.
    destruct Hmodtype as [fts [gts [? [? [? [Hglobtype ?]]]]]].
    apply list_eq.
    move => i.
    rewrite -> Forall2_lookup in Hglobtype.
    specialize Hglobtype with i.
    repeat rewrite list_lookup_fmap.
    simpl in *.
    destruct (mod_globals !! i) as [mg | ] eqn: Hmgi.
    - assert (i < length mod_globals) as Hlen; first by eapply lookup_lt_Some.
      simpl in Hmodglob.
      destruct (g_inits !! i) as [gi | ] eqn: Hgii; last first.
      {
        apply lookup_ge_None in Hgii.
        apply Forall2_length in Hinstglob.
        rewrite Hinstglob in Hlen.
        by lias.
      }
      inversion Hglobtype; subst; clear Hglobtype.
      simpl in *.
      unfold module_glob_typing in H5.
      assert ((modglob_init <$> mod_globals) !! i = ((fun v => [BI_const v]) <$> g_inits) !! i) as Hlookup.
      {
        by rewrite Hmodglob.
      }
      repeat rewrite list_lookup_fmap in Hlookup.
      rewrite Hmgi Hgii in Hlookup.
      destruct mg.
      destruct H5 as [Hconstexpr [-> Hbet]].
      simpl in Hlookup.
      inversion Hlookup; subst; clear Hlookup.
      f_equal.
      simpl.
      apply BI_const_typing in Hbet.
      simpl in Hbet.
      by inversion Hbet.
    - assert (i >= length mod_globals) as Hlen; first by eapply lookup_ge_None.
      simpl in Hmodglob.
      destruct (g_inits !! i) as [gi | ] eqn: Hgii; [ by apply lookup_lt_Some in Hgii; apply Forall2_length in Hinstglob; lias | by auto ].
  }
  
  assert (length g_inits = length m.(mod_globals)) as Hginitslen.
  { assert (length (typeof <$> g_inits) = length (tg_t ∘ modglob_type <$> m.(mod_globals))) as Heq; first by rewrite Hginitstype => //.
    by repeat rewrite fmap_length in Heq.
  }
  
  unfold alloc_module in Hallocmod.

  destruct (alloc_funcs s (mod_funcs m) inst) eqn:Hallocfunc.
  destruct (alloc_tabs s0 (map modtab_type (mod_tables m))) eqn:Halloctab.
  destruct (alloc_mems s1 (mod_mems m)) eqn:Hallocmem.
  destruct (alloc_globs s2 (mod_globals m) g_inits) eqn:Hallocglob.

  (* We now have to perform the state update step by step... *)

  (* Simplify the state relations first *)
  destruct s, s0, s1, s2, s3.
  simpl in *.
    
  (* alloc_funcs *)
  apply alloc_func_gen_index in Hallocfunc.
  simpl in Hallocfunc.
  destruct Hallocfunc as [Hfindex [Hfapp [-> [-> ->]]]].
    
  (* alloc_tabs *)
  apply alloc_tab_gen_index in Halloctab.
  simpl in Halloctab.
  destruct Halloctab as [Htindex [Htapp [-> [-> ->]]]].
    
  (* alloc_mems *)
  apply alloc_mem_gen_index in Hallocmem.
  simpl in Hallocmem.
  destruct Hallocmem as [Hmindex [Hmapp [-> [-> ->]]]].
    
  (* alloc_globs *)
  apply alloc_glob_gen_index in Hallocglob => //.
  simpl in Hallocglob.
  destruct Hallocglob as [Hgindex [Hgapp [-> [-> ->]]]].

  simpl in *.

  (* Now we perform the state updates *)

  (* alloc_funcs *)
  iDestruct (alloc_func_state_update with "Hwf") as "Hwf"; first by apply Hfapp.

  iMod "Hwf" as "(Hwf & Hfmapsto)".

  (* alloc_tabs *)
  iDestruct (alloc_tab_state_update with "Hwt Htsize Htlimit") as "Hwt"; first by apply Htapp.

  iMod "Hwt" as "(Hwt & Htsize & Htlimit & Htmapsto)".
    
  (* alloc_mems *)
  iDestruct (alloc_mem_state_update with "Hwm Hmsize Hmlimit") as "Hwm"; first by apply Hmapp.

  iMod "Hwm" as "(Hwm & Hmsize & Hmlimit & Hmmapsto)".

  (* alloc_globs *)
  iDestruct (alloc_glob_state_update with "Hwg") as "Hwg"; first by apply Hgapp.

  iMod "Hwg" as "(Hwg & Hwgmapsto)".

  move/andP in Hallocmod; destruct Hallocmod as [Hallocmod Hvexps]; move/eqP in Hvexps.
  move/andP in Hallocmod; destruct Hallocmod as [Hallocmod ?].
  move/andP in Hallocmod; destruct Hallocmod as [Hallocmod ?].
  move/andP in Hallocmod; destruct Hallocmod as [Hallocmod ?].
  move/andP in Hallocmod; destruct Hallocmod as [Hallocmod ?].
  move/andP in Hallocmod; destruct Hallocmod as [Hallocmod ?].
  move/eqP in Hallocmod; rewrite -> Hallocmod in *.
  
  (* initialisers *)

  remember (init_tabs _ inst _ _) as s4.

  (* init_tabs *)
  symmetry in Heqs4.
 (* iAssert (
        let wts' := module_import_init_tabs m inst wts in
        let ws := {| s_funcs := s_funcs4;
                     s_tables := s_tables4;
                     s_mems := s_mems4;
                     s_globals := s_globals4 |} in
        (*⌜init_tabs host_function ws inst (e_inits m.(mod_elem) = s4⌝*)
  (import_resources_wasm_typecheck imps t_imps wfs wts wms wgs -∗
  gen_heap_interp (gmap_of_table s_tables4) -∗
  gen_heap_interp (gmap_of_list (tab_size <$> s_tables4)) -∗
  gen_heap_interp (gmap_of_list (table_max_opt <$> s_tables4)) -∗
  ([∗ list] i↦v ∈ ((λ '{|
                        tt_limits :=
                          {| lim_min := min; lim_max := maxo |}
                      |},
                    {|
                      table_data :=
                        repeat None (ssrnat.nat_of_bin min);
                      table_max_opt := maxo
                    |}) <$> map modtab_type (mod_tables m)),
   N.of_nat (length s_tables4 - length (mod_tables m) + i)↦[wtblock]v) -∗
 |==>
  (import_resources_wasm_typecheck imps t_imps wfs wts' wms wgs ∗
  gen_heap_interp (gmap_of_table (s4.(datatypes.s_tables))) ∗
  gen_heap_interp (gmap_of_list (tab_size <$> s4.(datatypes.s_tables))) ∗
  gen_heap_interp (gmap_of_list (table_max_opt <$> s4.(datatypes.s_tables))) ∗
  module_inst_resources_tab (module_inst_build_tables m inst) (drop (get_import_table_count m) inst.(inst_tab))))%I) as "H".
    Search e_inits. 
    {
      
    }*)
  iDestruct (init_tabs_state_update $! Heqs4 with "[$] [$] [$] [$] [Htmapsto]") as "H" => /=.
  {
    replace (length s_tables3 - length (mod_tables m)) with (length s_tables0) => //.
    rewrite Htapp.
    rewrite app_length fmap_length map_length.
    by lias.
  }
  iMod "H" as "(Hwimport & Hwt & Htsize & Htlimit & Htmapsto)".

  destruct s4.
    
  specialize (init_tabs_preserve _ _ _ _ _ Heqs4) as [Hf4 [Hm4 Hg4]].
  simpl in Hf4, Hm4, Hg4.
  rewrite -> Hf4, Hm4, Hg4 in *.
  clear Hf4 Hm4 Hg4.
    
  (* init_mems *)
  move/eqP in Hs'.
  symmetry in Hs'.
  Search inst m.
  iDestruct (init_mems_state_update $! Hs' with "[$] [$] [$] [$] [Hmmapsto]") as "H" => /=.
  {
    replace (length s_mems - length (mod_mems m)) with (length s_mems1) => //.
    rewrite Hmapp.
    rewrite app_length fmap_length.
    by rewrite Nat.add_sub.
  }
    
  iMod "H" as "(Hwimport & Hwm & Hmsize & Hmlimit & Hmmapsto)".

  specialize (init_mems_preserve _ _ _ _ _ Hs') as [Hf4 [Ht4 Hg4]].
  simpl in Hf4, Ht4, Hg4.
  rewrite -> Hf4, Ht4, Hg4 in *.
  clear Hf4 Ht4 Hg4.

  (* state update done at this point, framing the gen_heaps away *)
  
  iFrame.

  iModIntro.

  iExists g_inits, (module_inst_build_tables m inst), (module_inst_build_mems m inst), (module_inst_global_init (module_inst_global_base (mod_globals m)) g_inits), (module_import_init_tabs m inst wts), (module_import_init_mems m inst wms).
    
  iFrame.

  (* Tweak the rest to fulfill the remaining (mostly-pure) predicates *)


  
  (* Instance check *)
  iSplit.
  {
    destruct inst.
    move/eqP in H.
    move/eqP in H0.
    move/eqP in H1.
    move/eqP in H2.
    move/eqP in H3.
    simpl in *; subst; simpl in *.
    iPureIntro.
    unfold ext_func_addrs, ext_tab_addrs, ext_mem_addrs, ext_glob_addrs => /=.
    repeat rewrite map_app.
    repeat split => //=; try by apply prefix_app_r => //.
    unfold check_start in * => /=.
    move/eqP in Hcheckstart; subst => /=.
    apply/eqP.
    by rewrite map_app.
  }
  
  (* Next are some trivial equalities on existential variables *)
  do 6 iSplit => //.
  (* global initialiser *)
  iSplit => //.
  { iPureIntro.
    unfold module_glob_init_values.
    split => //.
    unfold module_glob_init_value.
    rewrite list_fmap_compose.
    rewrite Hmodglob.
    clear.
    induction g_inits => //=.
    rewrite - those_those0 => /=.
    rewrite those_those0.
    by rewrite IHg_inits.
  }
  (* Then, a trivial equality again *)
  iSplit => //.

  (* Lastly, confirming that we do have the correct Wasm resources from instantiation. Note that each mapsto resources correspond very nicely to one part of the goal. *)
  unfold module_inst_resources_wasm.

  (* mod imports of m and imps are connected tortuously via t_imps. *)
  specialize (mod_imps_len_t _ _ _ Hmodtype) as [Himpflen [Himptlen [Himpmlen Himpglen]]].

  assert (
    length (ext_func_addrs (modexp_desc <$> v_imps)) = length (ext_t_funcs t_imps) /\
    length (ext_tab_addrs (modexp_desc <$> v_imps)) = length (ext_t_tabs t_imps) /\
    length (ext_mem_addrs (modexp_desc <$> v_imps)) = length (ext_t_mems t_imps) /\
    length (ext_glob_addrs (modexp_desc <$> v_imps)) = length (ext_t_globs t_imps)) as Hvtcomplen.
    {
      clear - Himpwasm Hvtlen.
      move: Hvtlen Himpwasm.
      move: t_imps.
      induction v_imps => /=; move => t_imps Hvtlen Himpwasm; destruct t_imps => //.
      simpl in *.
      specialize (IHv_imps t_imps).
      forward IHv_imps IHv_imps; first by lias.
      forward IHv_imps IHv_imps.
      { intros.
        specialize (Himpwasm (S k) v t).
        simpl in *.
        by specialize (Himpwasm H H0).
      }
      destruct IHv_imps as [Hflen [Htlen [Hmlen Hglen]]].
      specialize (Himpwasm 0 a e).
      do 2 forward Himpwasm Himpwasm => //.
      
      destruct a, modexp_desc; simpl in Himpwasm => /=.
      - destruct f.
        destruct Himpwasm as [? [? [? ->]]] => /=.
        repeat split => //.
        by f_equal.
      - destruct t.
        destruct Himpwasm as [? [? [? [? [-> ?]]]]] => /=.
        repeat split => //.
        by f_equal.
      - destruct m.
        destruct Himpwasm as [? [? [? [? [? [-> ?]]]]]] => /=.
        repeat split => //.
        by f_equal.
      - destruct g.
        destruct Himpwasm as [? [? [? [? [-> ?]]]]] => /=.
        repeat split => //.
        by f_equal.
    }

  destruct Hvtcomplen as [Hvtflen [Hvttlen [Hvtmlen Hvtglen]]].

  (* Functions *)
  iSplitL "Hfmapsto".
  {
    unfold module_inst_resources_func.
    rewrite Himpflen - Hvtflen.
    repeat rewrite map_app.
    move/eqP in H2.
    rewrite H2.
    rewrite map_app drop_app.
    simpl in *.
    unfold gen_index, gen_func_instance.
    remember (mod_funcs m) as mfuncs.
    simpl.
    rewrite Hfindex.
    clear.
    iInduction mfuncs as [ | f'] "IH" using List.rev_ind => //=.
    unfold gen_index.
    rewrite app_length repeat_app imap_app fmap_app => /=.
    rewrite big_sepL_app.
    iDestruct "Hfmapsto" as "(Hh & Ht)".
    simpl.
    iDestruct ("IH" with "Hh") as "Hh".
    iFrame.
    rewrite repeat_length.
    simpl.
    iDestruct "Ht" as "(Ht & _)".
    iSplit => //.
    rewrite fmap_length.
    repeat rewrite Nat.add_0_r.
    rewrite Nat.add_comm.
    by iApply "Ht".
  }
    
  (* Globals *)
  {
    unfold module_inst_resources_glob.
    rewrite Himpglen - Hvtglen.
    move/eqP in H.
    rewrite H.
    repeat rewrite map_app.
    rewrite drop_app.
    remember (mod_globals m) as mglobs.
    rewrite Hgindex.
    clear - Hginitslen.
    iRevert (Hginitslen).
    iRevert "Hwgmapsto".
    iRevert (g_inits).
    iInduction mglobs as [ | g'] "IH" using List.rev_ind => //=.
    iIntros (g_inits) "Hwgmapsto".
    iIntros "%Hginitslen".
    rewrite app_length in Hginitslen.
    assert (exists gi g', g_inits = gi ++ [g']).
    { destruct g_inits => //; first by simpl in Hginitslen; lias.
      clear.
      move: v.
      induction g_inits; intros => /=.
      - by exists [::], v.
      - specialize (IHg_inits a).
        destruct IHg_inits as [gi [g' Heq]].
        exists (v::gi), g'.
        simpl.
        by f_equal.
    }
    destruct H as [gi [gt ->]].
    rewrite app_length in Hginitslen.
    simpl in Hginitslen.
    unfold gen_index.
    rewrite app_length repeat_app imap_app => /=.
    rewrite combine_app => /=; last by lias.
    rewrite fmap_app.
    rewrite repeat_length.
    rewrite big_sepL_app.
    iDestruct "Hwgmapsto" as "(Hh & Ht)".
    iDestruct ("IH" with "Hh") as "Hh".
    iClear "IH".
    iSpecialize ("Hh" with "[%]"); first by lias.
    unfold module_inst_global_base.
    rewrite fmap_app.
    simpl.

    rewrite module_inst_global_init_cat; last by rewrite fmap_length; lias.

    simpl.

    (* Clear out the head of sepL2 *)
    iFrame => /=.

    repeat rewrite Nat.add_0_r.

    iDestruct "Ht" as "(Ht & _)".
    iSplit => //.
    rewrite fmap_length combine_length.
    replace (length gi) with (length mglobs); last by lias.
    rewrite Nat.min_id Nat.add_comm.
    unfold global_init_replace_single.
    destruct g', modglob_type => /=.

    by iApply "Ht".
  }

Qed.

                     

End Iris_instantiation.

