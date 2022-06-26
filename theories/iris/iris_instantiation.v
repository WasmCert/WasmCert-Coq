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

Lemma gen_index_length n len:
  length (gen_index n len) = len.
Proof.
  unfold gen_index.
  rewrite imap_length.
  by rewrite repeat_length.
Qed.

Lemma take_all_alt {X: Type} (l: list X) n:
  n = length l ->
  take n l = l.
Proof.
  move => H. subst. by rewrite firstn_all.
Qed.
  
Lemma seq_map_fmap {X Y: Type} (f: X -> Y) (l: list X):
  seq.map f l = fmap f l.
Proof.
  by [].
Qed.

Lemma repeat_lookup_Some {X: Type} n (v: X) i res:
  repeat v n !! i = Some res ->
  res = v /\ i < n.
Proof.
  move => Hrlookup.
  assert (i < length (repeat v n)); first by eapply lookup_lt_Some.

  split; last by rewrite repeat_length in H.
  assert (repeat v n !! i = Some v); first by apply repeat_lookup; rewrite repeat_length in H.
  rewrite H0 in Hrlookup.
  by inversion Hrlookup.
Qed.

Lemma gen_index_lookup_Some n l i x:
  (gen_index n l) !! i = Some x ->
  x = n + i /\ i < l.
Proof.
  unfold gen_index.
  move => Hl.
  rewrite list_lookup_imap in Hl.
  destruct (repeat _ _ !! i) eqn: Hrl => //.
  simpl in Hl.
  inversion Hl; subst; clear Hl.
  apply repeat_lookup_Some in Hrl as [-> ?].
  by lias.
Qed.
 
Lemma gen_index_NoDup n l:
  NoDup (gen_index n l).
Proof.
  apply NoDup_alt.
  move => i j x Hli Hlj.
  apply gen_index_lookup_Some in Hli as [-> ?].
  apply gen_index_lookup_Some in Hlj as [? ?].
  by lias.
Qed.

Lemma zip_lookup_Some {T1 T2: Type} (l1 : list T1) (l2: list T2) i x1 x2:
  length l1 = length l2 ->
  l1 !! i = Some x1 ->
  l2 !! i = Some x2 ->
  (zip l1 l2) !! i = Some (x1, x2).
Proof.
  move : l2 i x1 x2.
  induction l1; intros; destruct l2; destruct i => //=.
  - simpl in *.
    by inversion H0; inversion H1.
  - simpl in *.
    apply IHl1 => //.
    by inversion H.
Qed.
  
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


Definition import_func_resources (wfs: gmap N function_closure) : iProp Σ :=
  [∗ map] n ↦ v ∈ wfs, n ↦[wf] v.

Definition import_tab_resources (wts: gmap N tableinst) : iProp Σ :=
  [∗ map] n ↦ v ∈ wts, n ↦[wtblock] v.

Definition import_mem_resources (wms: gmap N memory) : iProp Σ :=
  [∗ map] n ↦ v ∈ wms, n ↦[wmblock] v.

Definition import_glob_resources (wgs: gmap N global) : iProp Σ :=
  [∗ map] n ↦ v ∈ wgs, n ↦[wg] v.

Definition func_domcheck v_imps (wfs: gmap N function_closure) : Prop :=
  dom (gset N) wfs ≡ list_to_set (N.of_nat <$> (ext_func_addrs (fmap modexp_desc v_imps))).

Definition tab_domcheck v_imps (wts: gmap N tableinst) : Prop :=
  dom (gset N) wts ≡ list_to_set (N.of_nat <$> (ext_tab_addrs (fmap modexp_desc v_imps))).

Definition mem_domcheck v_imps (wms: gmap N memory) : Prop :=
  dom (gset N) wms ≡ list_to_set (N.of_nat <$> (ext_mem_addrs (fmap modexp_desc v_imps))).

Definition glob_domcheck v_imps (wgs: gmap N global) : Prop :=
  dom (gset N) wgs ≡ list_to_set (N.of_nat <$> (ext_glob_addrs (fmap modexp_desc v_imps))).
      
Definition func_typecheck v_imps t_imps (wfs: gmap N function_closure): Prop :=
  Forall2 (fun v t =>
  match v.(modexp_desc) with
  | MED_func (Mk_funcidx i) => ∃ cl, wfs !! (N.of_nat i) = Some cl /\ t = ET_func (cl_type cl)
  | _ => True
  end) v_imps t_imps.

Definition tab_typecheck v_imps t_imps (wts: gmap N tableinst): Prop :=
  Forall2 (fun v t =>
  match v.(modexp_desc) with
  | MED_table (Mk_tableidx i) => (∃ tab tt,  wts !! (N.of_nat i) = Some tab /\ t = ET_tab tt /\ tab_typing tab tt )
  | _ => True
  end) v_imps t_imps.

Definition mem_typecheck v_imps t_imps (wms: gmap N memory): Prop :=
  Forall2 (fun v t =>
  match v.(modexp_desc) with
  | MED_mem (Mk_memidx i) => (∃ mem mt,  wms !! (N.of_nat i) = Some mem /\ t = ET_mem mt /\ mem_typing mem mt ) 
  | _ => True
  end) v_imps t_imps.

Definition glob_typecheck v_imps t_imps (wgs: gmap N global): Prop :=
  Forall2 (fun v t =>
  match v.(modexp_desc) with
  | MED_global (Mk_globalidx i) => (∃ g gt, wgs !! (N.of_nat i) = Some g /\ t = ET_glob gt /\ global_agree g gt)
  | _ => True
  end) v_imps t_imps.

Definition import_func_wasm_check v_imps t_imps wfs : iProp Σ:=
  import_func_resources wfs ∗
  ⌜func_typecheck v_imps t_imps wfs /\
  func_domcheck v_imps wfs⌝.
  
Definition import_tab_wasm_check v_imps t_imps wts : iProp Σ:=
  import_tab_resources wts ∗
  ⌜tab_typecheck v_imps t_imps wts /\
  tab_domcheck v_imps wts⌝.

Definition import_mem_wasm_check v_imps t_imps wms : iProp Σ:=
  import_mem_resources wms ∗
  ⌜mem_typecheck v_imps t_imps wms /\
  mem_domcheck v_imps wms⌝.

Definition import_glob_wasm_check v_imps t_imps wgs : iProp Σ:=
  import_glob_resources wgs ∗
  ⌜glob_typecheck v_imps t_imps wgs /\
  glob_domcheck v_imps wgs⌝.

Definition import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs: iProp Σ :=
  import_func_wasm_check v_imps t_imps wfs ∗
  import_tab_wasm_check v_imps t_imps wts ∗
  import_mem_wasm_check v_imps t_imps wms ∗
  import_glob_wasm_check v_imps t_imps wgs.

  Ltac unfold_irwt_all :=
    unfold import_func_wasm_check;
    unfold import_tab_wasm_check;
    unfold import_mem_wasm_check;
    unfold import_glob_wasm_check;
    unfold import_func_resources;
    unfold import_tab_resources;
    unfold import_mem_resources;
    unfold import_glob_resources;
    unfold func_typecheck;
    unfold tab_typecheck;
    unfold mem_typecheck;
    unfold glob_typecheck;
    unfold func_domcheck;
    unfold tab_domcheck;
    unfold mem_domcheck;
    unfold glob_domcheck.
  
Definition import_resources_wasm_typecheck_nodup v_imps t_imps wfs wts wms wgs: iProp Σ :=
  import_resources_wasm_domcheck v_imps wfs wts wms wgs ∗
  [∗ list] i ↦ v; t ∈ v_imps; t_imps,
  match v.(modexp_desc) with
  | MED_func (Mk_funcidx i) => ((∃ cl, N.of_nat i ↦[wf] cl ∗ ⌜ wfs !! (N.of_nat i) = Some cl /\ t = ET_func (cl_type cl) ⌝)%I)
  | MED_table (Mk_tableidx i) => (∃ tab tt, N.of_nat i ↦[wtblock] tab ∗ ⌜ wts !! (N.of_nat i) = Some tab /\ t = ET_tab tt /\ tab_typing tab tt ⌝)
  | MED_mem (Mk_memidx i) => (∃ mem mt, N.of_nat i ↦[wmblock] mem ∗ ⌜ wms !! (N.of_nat i) = Some mem /\ t = ET_mem mt /\ mem_typing mem mt ⌝) 
  | MED_global (Mk_globalidx i) => (∃ g gt, N.of_nat i ↦[wg] g ∗ ⌜ wgs !! (N.of_nat i) = Some g /\ t = ET_glob gt /\ global_agree g gt ⌝)
  end.

(* If v_imps do not contain duplicates, then the two versions are equivalent. *)
Definition irwt_nodup_equiv v_imps t_imps wfs wts wms wgs:
  NoDup v_imps ->
  (import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs ≡
   import_resources_wasm_typecheck_nodup v_imps t_imps wfs wts wms wgs).
Proof.
  iRevert (t_imps wfs wts wms wgs).
  iInduction (v_imps) as [|?] "IH"; iIntros (t_imps wfs wts wms wgs Hnodup); destruct t_imps => //=.
  - unfold import_resources_wasm_typecheck_nodup => //=.
    unfold import_resources_wasm_domcheck => /=.
    unfold import_resources_wasm_typecheck.
    unfold_irwt_all => /=.
    iSplit => //=.
    + iIntros "((?&?& %Hfdom) & (?&?& %Htdom) & (?&?& %Hmdom) & (?&?& %Hgdom))".
      by [].
    + iIntros "%H".
      destruct H as ((?&?&?&?)&?).
      apply dom_empty_inv in H.
      apply dom_empty_inv in H0.
      apply dom_empty_inv in H1.
      apply dom_empty_inv in H2.
      subst.
      by repeat iSplit => //.
  - admit.
  - admit.
(*  - iIntros "Hirwt".
    iDestruct "Hirwt" as "(Hfwc & Htwc & Hmwc & Hgwc)".
    iDestruct "Hfwc" as "(Hfm & Hft & %Hfdom)".
    iDestruct "Htwc" as "(Htm & Htt & %Htdom)".
    iDestruct "Hmwc" as "(Hmm & Hmt & %Hmdom)".
    iDestruct "Hgwc" as "(Hgm & Hgt & %Hgdom)".
    unfold import_func_resources.
    unfold import_tab_resources.
    unfold import_mem_resources.
    unfold import_glob_resources.
    unfold import_resources_wasm_typecheck_nodup.*)
    admit.
Admitted.
    
Definition exp_default := MED_func (Mk_funcidx 0).

Lemma import_func_wasm_lookup v_imps t_imps wfs ws :
  ⊢ gen_heap_interp (gmap_of_list (s_funcs ws)) -∗
    import_func_wasm_check v_imps t_imps wfs -∗
    ⌜ length v_imps = length t_imps /\ ∀ k v t, v_imps !! k = Some v -> t_imps !! k = Some t ->
      match modexp_desc v with
      | MED_func (Mk_funcidx i) => ∃ cl, ws.(s_funcs) !! i = Some cl /\ wfs !! N.of_nat i = Some cl /\ t = ET_func (cl_type cl) 
      | _ => True
      end ⌝.
Proof.
  iIntros "Hw (Hm & %Htype & %Hdom)".
  unfold func_typecheck in Htype.
  unfold import_func_resources.
  iSplit; first by erewrite Forall2_length.
  iIntros (k v t Hv Ht).
  rewrite -> Forall2_lookup in Htype.
  specialize (Htype k).
  rewrite Hv Ht in Htype.
  inversion Htype; subst; clear Htype.
  destruct v as [? modexp_desc].
  destruct modexp_desc as [e|e|e|e]; destruct e as [n] => //=.
  simpl in H1.
  destruct H1 as [v [Hlookup ->]].
  iExists v.
  iSplit => //.
  iDestruct (big_sepM_lookup with "Hm") as "Hm" => //.
  iDestruct (gen_heap_valid with "Hw Hm") as "%Hw".
  rewrite gmap_of_list_lookup in Hw.
  by rewrite Nat2N.id in Hw.
Qed.

Lemma import_tab_wasm_lookup v_imps t_imps wts ws :
    gen_heap_interp (gmap_of_table (s_tables ws)) -∗
    gen_heap_interp (gmap_of_list (fmap tab_size (s_tables ws))) -∗
    gen_heap_interp (gmap_of_list (fmap table_max_opt (s_tables ws))) -∗
    import_tab_wasm_check v_imps t_imps wts -∗
    ⌜ length v_imps = length t_imps /\ ∀ k v t, v_imps !! k = Some v -> t_imps !! k = Some t ->
      match modexp_desc v with
      | MED_table (Mk_tableidx i) => ∃ tab tt, ws.(s_tables) !! i = Some tab /\ wts !! N.of_nat i = Some tab /\ t = ET_tab tt /\ tab_typing tab tt
      | _ => True
      end ⌝.
Proof.
  iIntros "Hw Hwsize Hwlim (Hm & %Htype & %Hdom)".
  unfold tab_typecheck in Htype.
  unfold import_tab_resources.
  iSplit; first by erewrite Forall2_length.
  iIntros (k v t Hv Ht).
  rewrite -> Forall2_lookup in Htype.
  specialize (Htype k).
  rewrite Hv Ht in Htype.
  inversion Htype; subst; clear Htype.
  destruct v as [? modexp_desc].
  destruct modexp_desc as [e|e|e|e]; destruct e as [n] => //=.
  simpl in H1.
  destruct H1 as [tab [tt [Hlookup Htt]]].
  iExists tab, tt.
  iSplit => //.
  iDestruct (big_sepM_lookup with "Hm") as "Hm" => //.
  iDestruct (tab_block_lookup with "[$] [$] [$] [$]") as "%Hw".
  by rewrite Nat2N.id in Hw.
Qed.

Lemma import_mem_wasm_lookup v_imps t_imps wms ws :
    gen_heap_interp (gmap_of_memory (s_mems ws)) -∗
    gen_heap_interp (gmap_of_list (fmap mem_length (s_mems ws))) -∗
    gen_heap_interp (gmap_of_list (fmap mem_max_opt (s_mems ws))) -∗
    import_mem_wasm_check v_imps t_imps wms -∗
    ⌜ length v_imps = length t_imps /\ ∀ k v t, v_imps !! k = Some v -> t_imps !! k = Some t ->
      match modexp_desc v with
      | MED_mem (Mk_memidx i) => ∃ mem mt b_init, ws.(s_mems) !! i = Some {| mem_data := {| ml_init := b_init; ml_data := mem.(mem_data).(ml_data) |}; mem_max_opt := mem.(mem_max_opt) |} /\ wms !! N.of_nat i = Some mem /\ t = ET_mem mt /\ mem_typing mem mt
      | _ => True
      end ⌝.
Proof.
  iIntros "Hw Hwsize Hwlim (Hm & %Htype & %Hdom)".
  unfold mem_typecheck in Htype.
  unfold import_mem_resources.
  iSplit; first by erewrite Forall2_length.
  iIntros (k v t Hv Ht).
  rewrite -> Forall2_lookup in Htype.
  specialize (Htype k).
  rewrite Hv Ht in Htype.
  inversion Htype; subst; clear Htype.
  destruct v as [? modexp_desc].
  destruct modexp_desc as [e|e|e|e]; destruct e as [n] => //=.
  simpl in H1.
  destruct H1 as [mem [mt [Hlookup [-> Hmt]]]].
  iDestruct (big_sepM_lookup with "Hm") as "Hm" => //.
  iDestruct (mem_block_lookup with "[$] [$] [$] [$]") as "%Hw".
  iPureIntro.
  rewrite Hlookup.
  destruct Hw as [m [Hw [Hmdata Hmlim]]].
  exists mem, mt, m.(mem_data).(ml_init).
  rewrite Nat2N.id in Hw.
  rewrite Hw.
  destruct m, mem, mem_data => /=.
  simpl in *.
  subst.
  split => //.
Qed.

Lemma import_glob_wasm_lookup v_imps t_imps wgs ws :
  ⊢ gen_heap_interp (gmap_of_list (s_globals ws)) -∗
    import_glob_wasm_check v_imps t_imps wgs -∗
    ⌜ length v_imps = length t_imps /\ ∀ k v t, v_imps !! k = Some v -> t_imps !! k = Some t ->
      match modexp_desc v with
      | MED_global (Mk_globalidx i) => ∃ g gt, ws.(s_globals) !! i = Some g /\ wgs !! N.of_nat i = Some g /\ t = ET_glob gt /\ global_agree g gt
      | _ => True
      end ⌝.
Proof.
  iIntros "Hw (Hm & %Htype & %Hdom)".
  unfold glob_typecheck in Htype.
  unfold import_glob_resources.
  iSplit; first by erewrite Forall2_length.
  iIntros (k v t Hv Ht).
  rewrite -> Forall2_lookup in Htype.
  specialize (Htype k).
  rewrite Hv Ht in Htype.
  inversion Htype; subst; clear Htype.
  destruct v as [? modexp_desc].
  destruct modexp_desc as [e|e|e|e]; destruct e as [n] => //=.
  simpl in H1.
  destruct H1 as [v [vt [Hlookup [-> Hgt]]]].
  iExists v, vt.
  iSplit => //.
  iDestruct (big_sepM_lookup with "Hm") as "Hm" => //.
  iDestruct (gen_heap_valid with "Hw Hm") as "%Hw".
  rewrite gmap_of_list_lookup in Hw.
  by rewrite Nat2N.id in Hw.
Qed.

(* Old lemma *)
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
  iIntros "Hwf Hwt Hwm Hwg Hwtsize Hwtlimit Hwmlength Hwmlimit H".
  iDestruct "H" as "(Hfwc & Htwc & Hmwc & Hgwc)".
  iDestruct (import_func_wasm_lookup with "[$Hwf] [$Hfwc]") as "(% & %Hwf)".
  iDestruct (import_tab_wasm_lookup with "[$Hwt] [$Hwtsize] [$Hwtlimit] [$Htwc]") as "(% & %Hwt)".
  iDestruct (import_mem_wasm_lookup with "[$Hwm] [$Hwmlength] [$Hwmlimit] [$Hmwc]") as "(% & %Hwm)".
  iDestruct (import_glob_wasm_lookup with "[$Hwg] [$Hgwc]") as "(% & %Hwg)".

  iPureIntro.
  split => //.
  move => k v t Hvl Htl.
  specialize (Hwf k v t Hvl Htl).
  specialize (Hwt k v t Hvl Htl).
  specialize (Hwm k v t Hvl Htl).
  specialize (Hwg k v t Hvl Htl).
  destruct v as [? modexp_desc].
  by destruct modexp_desc as [e|e|e|e]; destruct e as [n] => /=; simpl in *.
Qed.

Lemma import_resources_wts_subset v_imps t_imps wts (ws: store_record):
  ⊢ gen_heap_interp (gmap_of_table (s_tables ws)) -∗
    gen_heap_interp (gmap_of_list (fmap tab_size (s_tables ws))) -∗
    gen_heap_interp (gmap_of_list (fmap table_max_opt (s_tables ws))) -∗
    import_tab_wasm_check v_imps t_imps wts -∗
    ⌜ length v_imps = length t_imps ⌝ -∗
    ⌜ wts ⊆ gmap_of_list (s_tables ws) ⌝.
Proof.
  iIntros "Hwt Hwtsize Hwtlimit Htwc %Himplen".
  unfold import_tab_wasm_check.
  unfold tab_domcheck,import_tab_resources, tab_typecheck.
  iDestruct "Htwc" as "(Htm & %Htt & %Hwtdom)".
  rewrite map_subseteq_spec.
  iIntros (i x Hwtslookup).

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

  iDestruct (big_sepM_lookup with "Htm") as "Htm" => //.
  iDestruct (tab_block_lookup with "Hwt Hwtsize Hwtlimit Htm") as "%Hwtblock".

  rewrite gmap_of_list_lookup.

  by rewrite Hwtblock.
Qed.

Definition mem_equiv (m1 m2: memory): Prop :=
  m1.(mem_max_opt) = m2.(mem_max_opt) /\
  m1.(mem_data).(ml_data) = m2.(mem_data).(ml_data).

Definition map_related {K: Type} {M: Type -> Type} {H0: forall A: Type, Lookup K A (M A)} {A: Type} (r: relation A) (m1 m2: M A) :=
  forall (i: K) (x: A), m1 !! i = Some x -> exists y, m2 !! i = Some y /\ r x y.

Lemma import_resources_wms_subset v_imps t_imps wms (ws: store_record):
  ⊢ gen_heap_interp (gmap_of_memory (s_mems ws)) -∗
    gen_heap_interp (gmap_of_list (fmap mem_length (s_mems ws))) -∗
    gen_heap_interp (gmap_of_list (fmap mem_max_opt (s_mems ws))) -∗
    import_mem_wasm_check v_imps t_imps wms -∗
    ⌜ length v_imps = length t_imps ⌝ -∗
    ⌜ map_related mem_equiv wms (gmap_of_list (s_mems ws)) ⌝.
Proof.
  iIntros "Hwm Hwmlength Hwmlimit Hmwc %Himplen".
  unfold map_related.
  iIntros (i x Hwmslookup).
  iDestruct "Hmwc" as "(Hmm & %Hmt & %Hwmdom)".
  unfold import_mem_resources, mem_typecheck.
  unfold mem_domcheck in Hwmdom.
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
  
  iDestruct (big_sepM_lookup with "Hmm") as "Hmm" => //.
  iDestruct (mem_block_lookup with "Hwm Hwmlength Hwmlimit Hmm") as "%Hwmblock".

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
  fmap (fun '(Mk_funcidx fidx) => inst.(inst_funcs) !! fidx) me_init.

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

Definition update_tab (tab: tableinst) off td' : option tableinst :=
  if off + length td' <=? length tab.(table_data) then
    Some ({| table_data := take off tab.(table_data) ++ td' ++ drop (off + length td') tab.(table_data); table_max_opt := tab.(table_max_opt) |})
  else None.

Definition update_tabs (tabs: list tableinst) off n td' : option (list tableinst) :=
  match tabs !! n with
  | Some tab =>
    match update_tab tab off td' with
    | Some tab' => Some (<[ n := tab' ]> tabs)
    | None => None
    end
  | None => None
  end.

Lemma update_tab_length tab off td' tab':
  update_tab tab off td' = Some tab' ->
  length (table_data tab) = length (table_data tab').
Proof.
  unfold update_tab.
  destruct (_ <=? _) eqn:Hle => //.
  move => H; inversion H; subst; clear H.
  apply PeanoNat.Nat.leb_le in Hle => /=.
  repeat rewrite app_length.
  rewrite take_length drop_length.
  by lias.
Qed.

Lemma update_tab_nil_id tab off tab':
  update_tab tab off [] = Some tab' ->
  tab = tab'.
Proof.
  unfold update_tab.
  destruct (_ <=? _) => //.
  move => H.
  inversion H; subst; clear H.
  rewrite Nat.add_0_r.
  rewrite cat_app.
  rewrite -> (take_drop off (table_data tab)).
  by destruct tab.
Qed.

Lemma update_tabs_nil_id tabs n off tabs':
  update_tabs tabs off n [] = Some tabs' ->
  tabs = tabs'.
Proof.
  unfold update_tabs.
  destruct (_ !! _) eqn: Htab => //.
  destruct (update_tab _ _ _) eqn:Hupd => //.
  apply update_tab_nil_id in Hupd; subst.
  rewrite list_insert_id => //.
  by move => H; inversion H.
Qed.

(* Nothing interesting, mainly numerical and string massages *)
Lemma update_tab_shift tab tab' off t td':
  update_tab tab off (t :: td') = Some tab' ->
  exists tab0, update_tab tab off [t] = Some tab0 /\
           update_tab tab0 (off+1) td' = Some tab'.
Proof.
  unfold update_tab.
  destruct (_ <=? _) eqn: Hle => //=.
  move => H.
  inversion H; subst; clear H.
  rewrite -> PeanoNat.Nat.leb_le in Hle.
  eexists. split.
  - assert (off+1 <=? length (table_data tab)) as Hle2.
    { apply PeanoNat.Nat.leb_le.
      simpl in Hle.
      by lias. }
    by rewrite Hle2. 
  - rewrite app_length take_length => /=; rewrite drop_length.
    assert (off + 1 + length td' <=? off `min` length (table_data tab) + S (length (table_data tab) - (off+1))) as Hle2.
    {
      apply PeanoNat.Nat.leb_le.
      simpl in Hle.
      by lias.
    }
    rewrite Hle2.
    do 2 f_equal.
    replace (take off (table_data tab) ++ _ :: drop (off + 1) (table_data tab)) with (((take off (table_data tab)) ++ [t]) ++ drop (off+1) (table_data tab)); last first.
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
    rewrite <- drop_drop.
    rewrite drop_app_alt; last first.
    { rewrite app_length take_length => /=.
      by lias.
    }
    rewrite drop_drop.
    f_equal.
    by lias.
Qed.

Lemma update_tabs_shift tabs tabs' off n t td':
  update_tabs tabs off n (t :: td') = Some tabs' ->
  exists tabs0, update_tabs tabs off n [t] = Some tabs0 /\
           update_tabs tabs0 (off+1) n td' = Some tabs'.
Proof.
  unfold update_tabs.
  destruct (_ !! _) eqn:Htab => //.
  destruct (update_tab _ _ _) eqn:Hupd => //.
  apply update_tab_shift in Hupd.
  destruct Hupd as [tab0 [Hupd1 Hupd2]].
  move => H; inversion H; subst; clear H.
  exists (<[ n := tab0 ]> tabs).
  rewrite Hupd1.
  split => //.
  rewrite list_lookup_insert; last by eapply lookup_lt_Some.
  rewrite Hupd2.
  by rewrite list_insert_insert.
Qed.
  
(* Auxiliary lemma for handling update of table segments at arbitrary offsets *)
Lemma tab_block_update_aux off td td' n tabs tabs':
  length td = length td' ->
  update_tabs tabs off n td' = Some tabs' ->
  ([∗ list] i↦telem ∈ td, (N.of_nat n)↦[wt][N.of_nat (off + i)] telem)%I -∗
   gen_heap_interp (gmap_of_table tabs) -∗
   |==>
  ([∗ list] i↦telem ∈ td', (N.of_nat )n↦[wt][N.of_nat (off + i)] telem) ∗
  gen_heap_interp (gmap_of_table tabs').
Proof.
  move: tabs tabs' n td' off.
  iInduction (td) as [|?] "IH"; iIntros (tabs tabs' n td' off Hlen Hupdate) "Htm Ht"; destruct td' => //=.
  { apply update_tabs_nil_id in Hupdate; subst.
    by iFrame. }
  simpl in Hlen.
  iDestruct "Htm" as "(Htm0 & Htm)".
  iDestruct (gen_heap_valid with "Ht Htm0") as "%H".
  iMod (gen_heap_update with "Ht Htm0") as "(Ht & Htm0)".
  iFrame.
  
  assert (length td = length td') as Hlen'; first by lias.
  clear Hlen.
  apply update_tabs_shift in Hupdate.
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
    unfold update_tabs in Hupd1.
    unfold update_tabs in Hupd2.
    destruct (tabs !! n) eqn: Htablookup => //=.
    simpl in Heq.
    inversion Heq; subst; clear Heq.
    erewrite (gmap_of_table_insert); rewrite Nat2N.id => //=.
    - unfold update_tab in Hupd1.
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
  unfold update_tabs, update_tab.
  rewrite Htab => /=.
  rewrite Htabsize => /=.
  rewrite PeanoNat.Nat.leb_refl.
  repeat f_equal.
  rewrite <- Htabsize.
  rewrite drop_all.
  by rewrite cats0.
Qed.

(* t_ind: the index of targeted table in the store, obtained from the instance
   e_pay: the payload to be written into the table
   e_ind: the offset of the starting location of replacement
*)
Lemma init_tab_state_update ws ws' inst e_off e t_ind tab e_pay:
  init_tab ws inst e_off e = ws' ->
  t_ind = nth match modelem_table e with | Mk_tableidx i => i end (inst_tab inst) 0 ->
  e_pay = fmap (fun '(Mk_funcidx j) => (inst_funcs inst) !! j) (e.(modelem_init)) ->
  e_off + length e.(modelem_init) <= length (tab.(table_data)) ->
  (N.of_nat t_ind) ↦[wtblock] tab -∗
  gen_heap_interp (gmap_of_table ws.(s_tables)) -∗
  gen_heap_interp (gmap_of_list (tab_size <$> ws.(s_tables))) -∗
  gen_heap_interp (gmap_of_list (table_max_opt <$> ws.(s_tables))) -∗
  |==>
  (N.of_nat t_ind) ↦[wtblock] {| table_data := take e_off tab.(table_data) ++ e_pay ++ drop (ssrnat.addn e_off (length e_pay)) tab.(table_data); table_max_opt := tab.(table_max_opt) |} ∗
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
  assert (e_pay = (map (fun i => nth_error (inst_funcs inst) match i with | Mk_funcidx j => j end) (modelem_init e))) as Hepayeq.
  { rewrite Hepay.
    rewrite map_fmap.
    apply list_eq.
    move => i.
    repeat rewrite list_lookup_fmap.
    destruct (modelem_init e !! i) => //=.
    destruct f => /=.
    by rewrite nth_error_lookup. } 
  rewrite <- Hepayeq in Hinittab.
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

Fixpoint update_wts (wts: gmap N tableinst) (inst: instance) (e_offs: list nat) (elems: list module_element) : option (gmap N tableinst) :=
  match elems with
  | [] => Some wts
  | e :: elems' =>
    match e_offs with
    | off :: e_offs' =>
      match e.(modelem_table) with
      | Mk_tableidx n =>
        match inst.(inst_tab) !! n with
        | Some i =>
          match wts !! (N.of_nat i) with
          | Some tab =>
            match update_tab tab off (map (fun '(Mk_funcidx j) => inst.(inst_funcs) !! j) e.(modelem_init)) with
            | Some tab' => update_wts (<[ (N.of_nat i) := tab']> wts) inst e_offs' elems'
            | None => None
            end
          | _ => None
          end
        | None => None
        end
      end
    | _ => None
    end
  end.   

Fixpoint update_wts_partial (wts: gmap N tableinst) (inst: instance) (e_offs: list nat) (elems: list module_element) : option (gmap N tableinst) :=
  match elems with
  | [] => Some wts
  | e :: elems' =>
    match e_offs with
    | off :: e_offs' =>
      match e.(modelem_table) with
      | Mk_tableidx n =>
        match inst.(inst_tab) !! n with
        | Some i =>
          match wts !! (N.of_nat i) with
          | Some tab =>
            match update_tab tab off (map (fun '(Mk_funcidx j) => inst.(inst_funcs) !! j) e.(modelem_init)) with
            | Some tab' => update_wts_partial (<[ (N.of_nat i) := tab']> wts) inst e_offs' elems'
            | None => None
            end
          | _ => update_wts_partial wts inst e_offs' elems'
          end
        | None => None
        end
      end
    | _ => None
    end
  end.   

  
Lemma update_wts_dom_preserve wts wts' inst e_offs elems:
  update_wts wts inst e_offs elems = Some wts' ->
  dom (gset N) wts ≡ dom (gset N) wts'.
Proof.
  move : wts wts' inst elems.
  induction e_offs; unfold update_wts; intros; destruct elems => //=.
  - by inversion H.
  - by inversion H.
  - move: H.
    destruct m => /=.
    destruct modelem_table => /=.
    destruct (inst_tab inst !! n) eqn:Hinstlookup => //=.
    destruct (wts !! _) eqn:Hwtslookup => //=.
    destruct (update_tab _ _ _) eqn:Hupdatetab => //=.
    fold update_wts.
    move => Hwtsupd.
    assert (dom (gset N) wts ≡ (dom (gset N) (<[N.of_nat n0 := t0]> wts))) as Hdomeq; first by rewrite dom_insert_lookup => //.
    rewrite Hdomeq.
    by rewrite IHe_offs => //.
Qed.

Lemma update_wts_partial_dom_preserve wts wts' inst e_offs elems:
  update_wts_partial wts inst e_offs elems = Some wts' ->
  dom (gset N) wts ≡ dom (gset N) wts'.
Proof.
  move : wts wts' inst elems.
  induction e_offs; unfold update_wts_partial; intros; destruct elems => //=.
  - by inversion H.
  - by inversion H.
  - move: H.
    destruct m => /=.
    destruct modelem_table => /=.
    destruct (inst_tab inst !! n) eqn:Hinstlookup => //=.
    fold update_wts_partial.
    destruct (wts !! _) eqn:Hwtslookup => //=.
    + destruct (update_tab _ _ _) eqn:Hupdatetab => //=.
      move => Hwtsupd.
      assert (dom (gset N) wts ≡ (dom (gset N) (<[N.of_nat n0 := t0]> wts))) as Hdomeq; first by rewrite dom_insert_lookup => //.
      rewrite Hdomeq.
      by rewrite IHe_offs => //.
    + move => Hwtsupd.
      by rewrite IHe_offs => //.
Qed.

(*
Lemma update_wts_split (wts1 wts2: gmap N tableinst) inst e_offs elems:
  map_disjoint wts1 wts2 ->
  update_wts (wts1 ∪ wts2) inst e_offs elems = 
  match (update_wts_partial wts1 inst e_offs elems) with
    | Some wts1' =>
      match (update_wts_partial wts2 inst e_offs elems) with
      | Some wts2' => Some (wts1' ∪ wts2')
      | None => None
      end
    | None => None
  end.
Proof.
  move : wts1 wts2 inst elems.
  induction e_offs; unfold update_wts, update_wts_partial; intros; destruct elems => //=.
  - destruct m => /=.
    destruct modelem_table => /=.
    fold update_wts.
    fold update_wts_partial.
    destruct (inst_tab inst !! n) eqn:Hinstlookup => //=.
    
    destruct ((wts1 ∪ wts2) !! _) eqn:Hwtslookup => //=.
    { apply lookup_union_Some in Hwtslookup => //.
      destruct Hwtslookup as [Hwts1l | Hwts2l].
      + rewrite Hwts1l.
        destruct (update_tab t a _) eqn:Hupdatetab => //=.
        rewrite insert_union_l.
        assert (wts2 !! N.of_nat n0 = None) as Hwts2l.
        { by eapply map_disjoint_Some_l. }
        rewrite Hwts2l.
        apply IHe_offs.
        by apply map_disjoint_insert_l_2 => //.
      + rewrite Hwts2l.
        assert (wts1 !! N.of_nat n0 = None) as Hwts1l.
        { by eapply map_disjoint_Some_r. }
        rewrite Hwts1l.
        destruct (update_tab t a _) eqn:Hupdatetab => //=.
        { rewrite insert_union_r => //.
          apply IHe_offs.
          by apply map_disjoint_insert_r_2 => //.
        }
        { by destruct (update_wts_partial _ _ _ _) => //. }
    }
    { apply lookup_union_None in Hwtslookup.
      destruct Hwtslookup as [Hwts1l Hwts2l].
      rewrite Hwts1l Hwts2l.
Admitted.*)

Lemma update_wts_split (wts' wts1 wts2: gmap N tableinst) inst e_offs elems:
  map_disjoint wts1 wts2 ->
  update_wts (wts1 ∪ wts2) inst e_offs elems = Some wts' ->
  match (update_wts_partial wts1 inst e_offs elems) with
    | Some wts1' =>
      match (update_wts_partial wts2 inst e_offs elems) with
      | Some wts2' => wts' = wts1' ∪ wts2'
      | None => False
      end
    | None => False
  end.
Proof.
  move : wts1 wts2 inst elems.
  induction e_offs; unfold update_wts, update_wts_partial; intros; destruct elems => //=.
  - by inversion H0.
  - by inversion H0.
  - move: H0.
    destruct m => /=.
    destruct modelem_table => /=.
    fold update_wts.
    fold update_wts_partial.
    destruct (inst_tab inst !! n) eqn:Hinstlookup => //=.
    
    destruct ((wts1 ∪ wts2) !! _) eqn:Hwtslookup => //=.
    { apply lookup_union_Some in Hwtslookup => //.
      destruct Hwtslookup as [Hwts1l | Hwts2l].
      + rewrite Hwts1l.
        destruct (update_tab t a _) eqn:Hupdatetab => //=.
        rewrite insert_union_l.
        assert (wts2 !! N.of_nat n0 = None) as Hwts2l.
        { by eapply map_disjoint_Some_l. }
        rewrite Hwts2l.
        apply IHe_offs.
        by apply map_disjoint_insert_l_2 => //.
      + rewrite Hwts2l.
        assert (wts1 !! N.of_nat n0 = None) as Hwts1l.
        { by eapply map_disjoint_Some_r. }
        rewrite Hwts1l.
        destruct (update_tab t a _) eqn:Hupdatetab => //=.
        rewrite insert_union_r => //.
        apply IHe_offs.
        by apply map_disjoint_insert_r_2 => //.
   }
Qed.

Lemma update_wts_partial_lookup_type wts wts' inst e_offs elems n tab tt:
  update_wts_partial wts inst e_offs elems = Some wts' ->
  wts !! n = Some tab ->
  tab_typing tab tt ->
  exists tab', wts' !! n = Some tab' /\ tab_typing tab' tt.
Proof.
  move: tt tab n elems inst wts wts'.
  induction e_offs; unfold update_wts_partial; intros; destruct elems => //=.
  - by exists tab; inversion H; subst; split => //.
  - by exists tab; inversion H; subst; split => //.
  - move: H.
    destruct m => /=.
    destruct modelem_table => /=.
    fold update_wts_partial.
    destruct (inst_tab inst !! n0) eqn:Hinstlookup => //.
    destruct (wts !! N.of_nat n1) eqn:Hwtslookup => //=.
    + destruct (update_tab _ _ _) eqn:Hupdtab => //=.
      fold update_wts_partial.
      move => Hupdwts.
      destruct (decide (n = N.of_nat n1)); subst => /=.
      { rewrite H0 in Hwtslookup.
        inversion Hwtslookup; subst; clear Hwtslookup.
        eapply IHe_offs; first by [].
        { by apply lookup_insert. }
        unfold update_tab in Hupdtab.
        unfold tab_typing.
        destruct (_+_ <=? _) eqn:Hle => //.
        apply PeanoNat.Nat.leb_le in Hle.
        rewrite map_length in Hle.
        inversion Hupdtab; subst; clear Hupdtab => /=.
        unfold tab_typing in H1.
        move/andP in H1.
        destruct H1 as [H1 H2].
        destruct t => /=.
        unfold tab_size in * => /=.
        simpl in *.
        repeat rewrite app_length.
        rewrite map_length.
        rewrite take_length drop_length.
        apply/andP; split => //.
        { replace (a `min` length table_data) with a; last by lias.
          replace (a+(length modelem_init+(length table_data-(a+length (modelem_init))))) with (length table_data); try by lias.
          by apply H1.
        }
      }
      { eapply IHe_offs => //=.
        by rewrite lookup_insert_ne => //.
      }
    + move => Hupdwts.
      by eapply IHe_offs => //.
Qed.

Definition wts_bound_check (wts: gmap N tableinst) inst e_offs elems :=
  all2 (fun off e => match inst.(inst_tab) !! (match e.(modelem_table) with | Mk_tableidx i => i end) with
                  | Some i => match wts !! (N.of_nat i) with
                             | Some ti => off + length e.(modelem_init) <=? length (table_data ti)
                             | None => false
                             end
                  | None => false
                  end)
       e_offs elems.

Lemma update_wts_Some wts inst e_offs elems:
  wts_bound_check wts inst e_offs elems ->
  exists wts', update_wts wts inst e_offs elems = Some wts'.
Proof.
  move: wts e_offs.
  induction elems; intros; destruct e_offs; simpl in * => //.
  { by eexists. }
  destruct a, modelem_table; simpl in *.
  destruct (inst_tab inst !! n0) eqn:Hinstlookup => //.
  move/andP in H.
  destruct H as [Hbc Hwts].
  destruct (wts !! N.of_nat n1) eqn:Hwtslookup => //.
  assert (forall tab e, update_tab t n e = Some tab ->
                   wts_bound_check (<[N.of_nat n1 := tab]>wts) inst e_offs elems)as Hwtsbc.
  { move => tab e Hupd.
    apply update_tab_length in Hupd.
    unfold wts_bound_check in *.
    apply all2_Forall2.
    apply all2_Forall2 in Hwts.
    apply Forall2_same_length_lookup.
    split; first by apply Forall2_length in Hwts.
    move => i off elem Hl1 Hl2.
    rewrite -> Forall2_lookup in Hwts.
    specialize (Hwts i).
    rewrite Hl1 Hl2 in Hwts.
    inversion Hwts; subst; clear Hwts.
    destruct elem, modelem_table.
    simpl in *.
    destruct (inst_tab inst !! n2) eqn:Hil => //.
    destruct (decide (n1 = n3)).
    - subst.
      rewrite Hwtslookup in H1.
      rewrite lookup_insert.
      by rewrite <- Hupd.
    - rewrite lookup_insert_ne => //.
      by lias.
  }
  destruct (update_tab t n _) eqn:Hupd => //.
  { apply Hwtsbc in Hupd.
    by apply IHelems.
  }
  exfalso.
  unfold update_tab in Hupd.
  rewrite map_length in Hupd.
  by rewrite Hbc in Hupd.
Qed.
  
Lemma init_tabs_state_update ws ws' inst e_offs elems (wts wts': gmap N tableinst):
  init_tabs ws inst e_offs elems = ws' ->
  wts_bound_check wts inst e_offs elems ->
  update_wts wts inst e_offs elems = Some wts' ->
  gen_heap_interp (gmap_of_table ws.(s_tables)) -∗
  gen_heap_interp (gmap_of_list (tab_size <$> ws.(s_tables))) -∗
  gen_heap_interp (gmap_of_list (table_max_opt <$> ws.(s_tables))) -∗
  ([∗ map] n ↦ tabinst ∈ wts, n ↦[wtblock] tabinst) -∗
  |==>
  gen_heap_interp (gmap_of_table ws'.(s_tables)) ∗
  gen_heap_interp (gmap_of_list (tab_size <$> ws'.(s_tables))) ∗
  gen_heap_interp (gmap_of_list (table_max_opt <$> ws'.(s_tables))) ∗
  ([∗ map] n ↦ tabinst ∈ wts', n ↦[wtblock] tabinst).
Proof.
  move : ws ws' inst e_offs wts wts'.
  iInduction (elems) as [|?] "IH"; iIntros (ws ws' inst e_offs wts wts' Hinittabs Helembc Hupdwts) "Ht Htsize Htlim Htmblock".
  - unfold init_tabs in Hinittabs.
    unfold update_wts in Hupdwts.
    rewrite combine_nil in Hinittabs.
    simpl in Hinittabs.
    destruct e_offs => //; try by (inversion Hupdwts; subst; clear Hupdwts; iFrame).
  - unfold init_tabs in Hinittabs.
    unfold update_wts in Hupdwts.
    destruct e_offs => //.
    rewrite <- cat1s in Hinittabs.
    rewrite <- (cat1s a elems) in Hinittabs.
    rewrite combine_app in Hinittabs => //.
    simpl in Hinittabs.
    destruct a, modelem_table => /=; simpl in *.
    destruct (inst.(inst_tab) !! n0) eqn: Hinsttab => //.
    destruct (wts !! N.of_nat n1) eqn: Htab => //.
    destruct (update_tab _ _ _) eqn: Hupdtab => //.
    fold update_wts in Hupdwts.
    remember (init_tab ws inst n _) as ws0.
    fold (init_tabs ws0 inst e_offs elems) in Hinittabs.
    move/andP in Helembc.
    destruct Helembc as [Hbc Helembc].
    apply PeanoNat.Nat.leb_le in Hbc.

    assert (wts_bound_check (<[ N.of_nat n1 := t0 ]> wts) inst e_offs elems) as Helembc'.
    { unfold wts_bound_check in *.
      apply all2_Forall2.
      apply all2_Forall2 in Helembc.
      eapply Forall2_impl => //.
      move => i elem => /=.
      destruct elem => /=.
      destruct modelem_table => /=.
      destruct (inst_tab inst !! n2) eqn: Hlookup => //.
      destruct (decide (n1 = n3)) eqn: Hn.
      - subst.
        rewrite lookup_insert.
        rewrite Htab.
        move => H.
        apply update_tab_length in Hupdtab.
        by rewrite Hupdtab in H.
      - by rewrite lookup_insert_ne; last by lias.
    }   
    iDestruct ("IH" $! _ _ _ _ _ _ Hinittabs Helembc' Hupdwts) as "H".
    iClear "IH".
    symmetry in Heqws0.
    iDestruct (big_sepM_delete with "Htmblock") as "(Htm0 & Htm)" => //.
    iDestruct (tab_block_lookup with "[$] [$] [$] [$]") as "%Hslookup".
    rewrite Nat2N.id in Hslookup.
    iDestruct (init_tab_state_update) as "Hstep" => //=.
    erewrite nth_error_nth; last by rewrite nth_error_lookup.
    iDestruct ("Hstep" with "Htm0 Ht Htsize Htlim") as "Hint".
    iMod "Hint".
    iDestruct "Hint" as "(Htm0 & Ht & Htsize & Htlim)".
    iDestruct ("H" with "Ht Htsize Htlim") as "Hσ".
    iApply "Hσ".
    unfold update_tab in Hupdtab.
    destruct (n + _ <=? _) eqn:Hle => //.
    apply PeanoNat.Nat.leb_le in Hle.
    inversion Hupdtab; subst; clear Hupdtab.
    simpl in *.
    iApply big_sepM_insert_delete.
    by iFrame.
Qed.

Lemma ext_tab_addrs_aux l:
  ext_tab_addrs l = fmap (fun '(Mk_tableidx i) => i) (ext_tabs l).
Proof.
  by [].
Qed.

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
(*
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
 *)

Lemma big_sepL2_big_sepM {X Y: Type} (E0 : EqDecision X) (H0: Countable X) (l1: list X) (l2: list Y) (Φ: X -> Y -> iProp Σ) (m: gmap X Y):
  NoDup l1 ->
  length l1 = length l2 ->
  m = list_to_map (zip l1 l2) ->
  (([∗ map] k ↦ v ∈ m, Φ k v) -∗
  ([∗ list] i ↦ x; y ∈ l1; l2, Φ x y)%I).
Proof.
  move => Hnd Hlen ->.
  iIntros "Hm".
  iDestruct (big_opM_map_to_list with "Hm") as "Hm".
  rewrite map_to_list_to_map; last rewrite fst_zip => //; last by lias.
  rewrite big_sepL2_alt.
  by iSplit => //.
Qed.

Lemma big_sepM_l2m_zip_f {X Y Z: Type} (E: EqDecision X) (E0: EqDecision Z) (H: Countable X) (H0: Countable Z) (l1 : list X) (l2: list Y) (Φ: Z -> Y -> iProp Σ) (f: X -> Z) :
  length l1 = length l2 ->
  NoDup l1 ->
  Inj eq eq f ->
  ([∗ map] k ↦ v ∈ list_to_map (zip l1 l2), Φ (f k) v)%I ≡ ([∗ map] k ↦ v ∈ list_to_map (zip (f <$> l1) l2), Φ k v)%I.
Proof.
  iRevert (l2).
  iInduction (l1) as [|?] "IH"; iIntros (l2 Hlen Hnd Hinj); destruct l2 => //=; try by repeat rewrite big_sepM_empty.
  simpl in Hlen.
  inversion Hlen; subst; clear Hlen.
  inversion Hnd; subst; clear Hnd.
  rewrite big_opM_insert; last first.
  { apply not_elem_of_list_to_map.
    rewrite fst_zip => //; last by lias.
  }
  rewrite big_opM_insert; last first.
  { apply not_elem_of_list_to_map.
    rewrite fst_zip; last by rewrite fmap_length; lias.
    rewrite elem_of_list_fmap.
    move => HContra.
    destruct HContra as [x [Heq Helem]].
    by apply Hinj in Heq; subst.
  }
  iSplit; iIntros "(?&?)"; iFrame; by iApply "IH".
Qed.

  
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

Lemma zip_lookup_Some_inv {X Y: Type} (l1: list X) (l2: list Y) k v1 v2:
  (zip l1 l2) !! k = Some (v1, v2) ->
  l1 !! k = Some v1 /\ l2 !! k = Some v2.
Proof.
  move: l2 k v1 v2.
  induction l1; intros; destruct l2; destruct k; simpl in * => //=.
  - by inversion H.
  - by apply IHl1.
Qed.
    
Lemma list_to_map_zip_lookup {X Y: Type} (E: EqDecision X) (H: Countable X) (l1 : list X) (l2: list Y) (k: X) (v: Y) (m: gmap X Y):
  NoDup l1 ->
  length l1 = length l2 ->
  (((list_to_map (zip l1 l2)): gmap X Y) !! k = Some v <->
   (exists k', l1 !! k' = Some k /\ l2 !! k' = Some v)).
Proof.
  move => Hnd Hlen.
  split; move => Hl.
  { rewrite <- elem_of_list_to_map in Hl; last first.
    { rewrite fst_zip => //; by lias. }
    simplify_lookup.
    exists x.
    by apply zip_lookup_Some_inv in Helem.
  }
  destruct Hl as [k' [Hl1 Hl2]].
  rewrite <- elem_of_list_to_map; last first.
  { rewrite fst_zip => //; by lias. }
  apply elem_of_list_lookup.
  exists k'.
  by apply zip_lookup_Some.
Qed.
  
Lemma list_to_map_zip_insert {X Y: Type} (E: EqDecision X) (H: Countable X) (l1 : list X) (l2: list Y) (k: X) (k': nat) (v: Y) (m: gmap X Y):
  NoDup l1 ->
  m = list_to_map (zip l1 l2) ->
  length l1 = length l2 ->
  l1 !! k' = Some k ->
  <[ k := v ]> m = list_to_map (zip l1 (<[ k' := v ]> l2)).
Proof.
  move => Hnd -> Hlen Hk.
  apply map_eq.
  move => i.
  destruct (decide (i=k)); subst => //=.
  - rewrite lookup_insert.
    symmetry.
    rewrite list_to_map_zip_lookup => //.
    { exists k'.
      split => //.
      rewrite list_lookup_insert => //.
      by apply lookup_lt_Some in Hk; lias.
    }
    { by rewrite insert_length. }
  - rewrite lookup_insert_ne => //.
    destruct (list_to_map (zip l1 _) !! i) eqn:Hli => /=.
    { symmetry.
      apply list_to_map_zip_lookup => //.
      { by rewrite insert_length. }
      { apply elem_of_list_to_map in Hli; last first.
        { rewrite fst_zip => //; by lias. }
        apply elem_of_list_lookup in Hli.
        destruct Hli as [j Hli].
        apply zip_lookup_Some_inv in Hli.
        exists j.
        rewrite list_lookup_insert_ne => //.
        destruct Hli as [Hli _].
        move => HContra; subst.
        by rewrite Hk in Hli; inversion Hli.
      }
    }
    {
      simplify_lookup.
      rewrite fst_zip in H2; last by lias.
      rewrite not_elem_of_list_to_map_1 => //.
      rewrite fst_zip => //.
      by rewrite insert_length; lias.
    }
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

  specialize (mod_imps_len_t _ _ _ Hmodtype) as Htimpslen.
  destruct Htimpslen as [Hftlen [Httlen [Hmtlen Hgtlen]]].
  
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

   assert (length (ext_t_tabs t_imps) = length (ext_tabs (modexp_desc <$> v_imps))) as Hvttablen.
     {
        clear - Himpwasm Hvtlen.
        move: Himpwasm Hvtlen.
        move: t_imps.
        induction v_imps; destruct t_imps => //=; intros.
        specialize (Himpwasm 0 a e) as Hl.
        simpl in Hl.
        forward Hl Hl => //.
        forward Hl Hl => //.
        clear Hp Hp0.
        destruct a, modexp_desc; simpl in *; [destruct f|destruct t|destruct m|destruct g] => //=.
        { destruct Hl as [? [? [? ->]]].
          apply IHv_imps; last by lias.
          move => k.
          by specialize (Himpwasm (S k)); simpl in *.
        }
        { destruct Hl as [? [? [? [? [-> ?]]]]].
          simpl.
          f_equal.
          apply IHv_imps; last by lias.
          move => k.
          by specialize (Himpwasm (S k)); simpl in *.
        }
        { destruct Hl as [? [? [? [? [? [-> ?]]]]]].
          apply IHv_imps; last by lias.
          move => k.
          by specialize (Himpwasm (S k)); simpl in *.
        }
        { destruct Hl as [? [? [? [? [-> ?]]]]].
          apply IHv_imps; last by lias.
          move => k.
          by specialize (Himpwasm (S k)); simpl in *.
        }
     }

  symmetry in Heqs4.
  rewrite seq_map_fmap in Heqs4.

  fold nat_of_int in Heqs4.
  iDestruct "Himpwasm" as "(Hfwc & Htwc & Hmwc & Hgwc)".
  iDestruct "Htwc" as "(Htm & Htt & %Htdom)".
  unfold tab_domcheck in Htdom.
  
  remember (((λ '{|tt_limits :=
                       {| lim_min := min; lim_max := maxo |}
                   |},
                {|
                  table_data :=
                    repeat None (ssrnat.nat_of_bin min);
                  table_max_opt := maxo
                |}) <$> map modtab_type (mod_tables m))) as tablebase.
  remember ((list_to_map (zip (fmap N_of_nat (gen_index (length s_tables0) (length (mod_tables m)))) tablebase)): gmap N tableinst) as wtsalloc.

  assert (map_disjoint wts wtsalloc) as Hwtsdisj.
  {
    apply map_disjoint_spec.
    move => i t1 t2 Ht1 Ht2.
    
    assert (i ∈ dom (gset N) wts) as Hidom; first by apply elem_of_dom.
    rewrite -> Htdom in Hidom.
    rewrite -> elem_of_list_to_set in Hidom.
    rewrite -> ext_tab_addrs_aux in Hidom.
    rewrite -> elem_of_list_fmap in Hidom.
    destruct Hidom as [y [-> Helem]].
    rewrite -> elem_of_list_fmap in Helem.
    destruct Helem as [y0 [-> Helem]].
    destruct y0 => /=.
    
    rewrite Heqwtsalloc in Ht2.
    apply elem_of_list_to_map_2 in Ht2.
    apply elem_of_zip_l in Ht2.

    apply elem_of_list_fmap in Ht2.
    destruct Ht2 as [y' [Hy' Helem']].
    apply Nat2N.inj in Hy'; subst.
    apply elem_of_list_lookup in Helem'.
    destruct Helem' as [i Hlookup].
    unfold gen_index in Hlookup.
    rewrite -> list_lookup_imap in Hlookup.
    destruct (repeat 0 _ !! i) eqn:Hrlookup => //=.
    simpl in Hlookup.
    inversion Hlookup; subst; clear Hlookup.
    assert (i < length (mod_tables m)) as Hlen.
    { apply lookup_lt_Some in Hrlookup.
      by rewrite repeat_length in Hrlookup. }

    assert ((repeat 0 (length (mod_tables m)) !! i) = Some 0) as Hrlookup'; first by apply repeat_lookup.
    rewrite Hrlookup' in Hrlookup.
    inversion Hrlookup; subst; clear Hrlookup.
    clear Hrlookup'.

    apply elem_of_list_lookup in Helem.
    destruct Helem as [j Hlookup].
    apply ext_tabs_lookup_exist in Hlookup.
    destruct Hlookup as [k Hlookup].
    rewrite list_lookup_fmap in Hlookup.

    destruct (v_imps !! k) eqn:Hvimpslookup => //.
    simpl in Hlookup.

    destruct m0 => /=.
    simpl in Hlookup.
    destruct modexp_desc; try by inversion Hlookup.
    inversion Hlookup; subst; clear Hlookup.

    destruct (t_imps !! k) eqn:Htimpslookup; last by apply lookup_ge_None in Htimpslookup; rewrite <- Hvtlen in Htimpslookup; apply lookup_lt_Some in Hvimpslookup; lias.
    specialize (Himpwasm _ _ _ Hvimpslookup Htimpslookup) as Hvtlookup.
    simpl in Hvtlookup.

    destruct Hvtlookup as [tab [tt [Hwslookup [Hwtslookup [-> Htt]]]]].

    (* We've finally reached the contradiction: s_tables0 cannot contain 
       that many elements. *)

    apply lookup_lt_Some in Hwslookup.
    by lias.
  }

  (* A lemma about looking up in ext_tab_addrs must fall in the original store *)
  assert (forall x j, ext_tab_addrs (modexp_desc <$> v_imps) !! j = Some x -> x < length s_tables0) as Hexttabelem.
  {
    move => x j Helem.
   rewrite ext_tab_addrs_aux in Helem.
   rewrite list_lookup_fmap in Helem.
   destruct (ext_tabs _ !! j) eqn:Hextlookup => //=.
   simpl in Helem.
   destruct t.
   inversion Helem; subst; clear Helem.
   apply ext_tabs_lookup_exist in Hextlookup.
   destruct Hextlookup as [k Hvl].
   rewrite list_lookup_fmap in Hvl.
   destruct (v_imps !! k) eqn: Hvlk => //=.
   simpl in Hvl.
   destruct m0, modexp_desc => //=.
   inversion Hvl; subst; clear Hvl.
   rewrite -> Forall2_lookup in Hexttype.
   specialize (Hexttype k) as Hvtk.
   rewrite list_lookup_fmap Hvlk in Hvtk.
   inversion Hvtk; subst; clear Hvtk.
   inversion H6; subst; clear H6.
   simpl in H7.
   by move/ssrnat.ltP in H7.
  }

  assert (exists wts', update_wts (wts ∪ wtsalloc) inst
    ((fun off => Z.to_nat (Wasm_int.Int32.intval off)) <$> e_offs)
    (mod_elem m) = Some wts') as Hwtsupd.
  {
    apply update_wts_Some.
    unfold wts_bound_check.
    apply all2_Forall2.
    apply Forall2_same_length_lookup.
    split => //.
    { rewrite fmap_length.
      by apply Forall2_length in Hinstelem.
    }
    move => i off elem Hlo Hle.
    rewrite -> Forall2_lookup in Hinstelem.
    specialize (Hinstelem i).
    rewrite list_lookup_fmap in Hlo.
    destruct (e_offs !! i) eqn:Hleo; rewrite Hleo in Hlo => //.
    simpl in Hlo.
    unfold check_bounds_elem in Helemcb.
    simpl in Helemcb.
    apply all2_Forall2 in Helemcb.
    rewrite -> Forall2_lookup in Helemcb.
    specialize (Helemcb i); rewrite Hle Hleo in Helemcb.
    unfold module_elem_bound_check_gmap in Hebound.
    rewrite -> Forall_lookup in Hebound.
    specialize (Hebound i).
    rewrite Hle in Hebound.
    specialize (Hebound elem).
    forward Hebound Hebound => //.
    clear Hp.
    inversion Helemcb; subst; clear Helemcb.
    inversion Hlo; subst; clear Hlo.
    rewrite Hle in Hinstelem.
    assert ((fun (v: Wasm_int.Int32.T) => [BI_const (VAL_int32 v)])<$> e_inits' !! i = modelem_offset <$> Some elem).
    { rewrite <- list_lookup_fmap. rewrite <- Hmodelem.
      by rewrite list_lookup_fmap Hle.
    }
    destruct elem, modelem_table => /=.
    unfold assert_const1_i32 in Hebound.
    simpl in *.
    destruct (e_inits' !! i) eqn:Hleinit => //.
    simpl in H4.
    inversion H4; subst; clear H4.
    inversion Hinstelem; subst; clear Hinstelem.
    simpl in H7.
    apply reduce_trans_const in H7.
    inversion H7; subst; clear H7.

    
    rewrite nth_error_lookup in H6.
    destruct (inst_tab inst !! n) eqn:Hinsttab => //.
    rewrite nth_error_lookup in H6.
    destruct (_ !! n0) eqn:Hnl => //.
    rewrite lookup_app in Hnl.
    move/eqP in H1.
    rewrite -> H1 in *.
    rewrite map_fmap in Hinsttab.
    rewrite list_lookup_fmap in Hinsttab.
    rewrite lookup_app in Hinsttab.
    destruct (ext_tabs _ !! n) eqn:Hextlookup => //.
    { (* Imports *)
      simpl in Hinsttab.
      destruct t1.
      inversion Hinsttab; subst; clear Hinsttab.
      destruct (wts !! N.of_nat n0) eqn:Hwtslookup => //.
      rewrite lookup_union_l; rewrite Hwtslookup => //.
      apply N.leb_le in H6.
      apply Nat.leb_le.
      by lias.
    }
    { (* Alloc *)
      rewrite map_fmap in Htindex.
      rewrite <- list_lookup_fmap in Hinsttab.
      rewrite Htindex in Hinsttab.
      assert (wts !! (N.of_nat n0) = None) as Hwtslookup.
      {
        apply gen_index_lookup_Some in Hinsttab.
        rewrite map_length in Hinsttab.
        destruct Hinsttab as [-> Hlt].
        apply not_elem_of_dom.
        rewrite Htdom.
        rewrite elem_of_list_to_set.
        rewrite elem_of_list_fmap.
        move => Hcontra.
        destruct Hcontra as [y [Heq Helem]].
        apply Nat2N.inj in Heq.
        subst.
        apply elem_of_list_lookup in Helem.
        destruct Helem as [j Helem].
        apply Hexttabelem in Helem.
        by lias.
      }
      rewrite lookup_union_r => //.
      destruct (mod_tables m !! _) eqn:Hmtlookup => //.
      apply N.leb_le in H6.
      erewrite elem_of_list_to_map_1.
      { instantiate (1 := t0).
        apply Nat.leb_le.
        unfold N_of_int in H6.
        by lias.
      }
      { rewrite fst_zip; last first.
        { rewrite map_fmap.
          repeat rewrite fmap_length.
          by rewrite gen_index_length.
        }
        { apply NoDup_fmap; first by lias.
          by apply gen_index_NoDup.
        }
      }
      {
        apply elem_of_list_lookup.
        exists (n0 - length s_tables0).
        apply gen_index_lookup_Some in Hinsttab.
        rewrite map_length in Hinsttab.
        destruct Hinsttab as [-> Hlt].
        apply zip_lookup_Some.
        { repeat rewrite fmap_length.
          by rewrite gen_index_length.
        }
        { rewrite list_lookup_fmap.
          rewrite gen_index_lookup => /=; last by lias.
          do 2 f_equal.
          by lias.
        }
        { destruct (s_tables0 !! _) eqn:Hstlookup => //; first by apply lookup_lt_Some in Hstlookup; lias.
        }
      }
    }    
  }

  destruct Hwtsupd as [wts' Hwtsupd].

  
  iDestruct (init_tabs_state_update with "[Hwt] [Htsize] [Htlimit] [Htmapsto Htm]") as "H".
  { (* init_tabs *)
      by apply Heqs4. }
  6: { (* bringing up the mapsto assertion first to instantiate wts *)
    (* Note: "Htmapsto" itself does not provide all the tables -- it only 
       contains the ownership of tables generated from alloc_tab (i.e. the new
       ones allocated by the module. We also need the imported ones. 
       It's quite painful to express it in Iris, but the wts gmap we want here
       for applying the init_tabs spec is wts ∪ wtsalloc here. That's why
       we've done the painful disjointness proof previously. *)
    instantiate (1 := wts ∪ wtsalloc).
    iApply big_opM_union => //.
    unfold import_tab_resources.
    iFrame.

    { (* Alloc *)
      unfold tab_typecheck.
      iApply big_opM_map_to_list.
      rewrite Heqwtsalloc.
      rewrite Heqtablebase.
      rewrite map_to_list_to_map => /=; last first.
      { rewrite fst_zip; last first.
        { repeat rewrite fmap_length.
          by rewrite gen_index_length. }
        rewrite NoDup_fmap.
        unfold gen_index.
        rewrite NoDup_alt.
        move => i j x Hl1 Hl2.
        rewrite list_lookup_imap in Hl1.
        rewrite list_lookup_imap in Hl2.
        destruct (repeat _ _ !! i) eqn: Hri => //.
        destruct (repeat _ _ !! j) eqn: Hrj => //.
        apply elem_of_list_lookup_2, elem_of_list_In, repeat_spec in Hri.
        apply elem_of_list_lookup_2, elem_of_list_In, repeat_spec in Hrj.
        subst.
        simpl in *.
        inversion Hl1. inversion Hl2.
        by lias.
      }
      (* We still need to manipulate the existing big_sepL to the one in the goal. *)
      remember (length s_tables0) as off.
      destruct m => /=.
      clear.
      iRevert "Htmapsto".
      iRevert (off).
      iInduction (mod_tables) as [|?] "IH" => //=.
      iIntros (off) "Htm".
      iDestruct "Htm" as "(Htm0 & Htm)".
      iFrame.
      iDestruct ("IH" $! (off+1) with "[Htm]") as "H".
      { iApply (big_sepL_mono with "Htm").
        iIntros (???) "H".
        replace (off+1+k) with (off+S k) => //; last by lias.
      }
      replace (list_fmap nat N N.of_nat (imap ((fun i x => i+off+x) ∘ S) (repeat 0 (length mod_tables)))) with (N.of_nat <$> gen_index (off+1) (length (mod_tables))) => //.
      f_equal.
      unfold gen_index.
      apply list_eq.
      intros.
      repeat rewrite list_lookup_imap.
      destruct (repeat _ _ !! i) eqn:H => //=.
      f_equal.
      by lias.
    }
  }
  { (* bound check *)
    unfold wts_bound_check.
    apply all2_Forall2.
    unfold check_bounds_elem in Helemcb.
    destruct m => /=.
    destruct inst => /=.
    simpl in *.
    rewrite -> Heqwtsalloc in *.
    rewrite -> Heqtablebase in *.
    clear - Helemcb Htapp H1 Htindex Htdom Himpwasm Hwtsdisj Hvtlen.
    move/eqP in H1.
    subst.
    apply all2_Forall2 in Helemcb.
    rewrite map_length in Htindex.
    apply Forall2_lookup.
    rewrite -> Forall2_lookup in Helemcb.
    move => i.
    specialize (Helemcb i).
    rewrite list_lookup_fmap.
    destruct (mod_elem !! i) eqn:Helemi => /=; last first.
    - inversion Helemcb.
      symmetry in H0.
      rewrite H0 => /=.
      by apply None_Forall2.
    - inversion Helemcb; subst.
      symmetry in H.
      rewrite H.
      simpl.
      apply Some_Forall2.
      repeat rewrite nth_error_lookup in H1.
      rewrite map_fmap in H1.
      rewrite list_lookup_fmap in H1.
      rewrite map_fmap.
      rewrite list_lookup_fmap.
      destruct m, modelem_table => /=.
      simpl in *.
      destruct (_ !! n) eqn:Hexttabl => //.
      simpl in *.
      rewrite nth_error_lookup in H1.
      destruct t.
      rewrite lookup_app in H1.
      rewrite lookup_app in Hexttabl.

      destruct (ext_tabs _ !! n) eqn:Hexttabslookup => /=.
      { (* Imported *)
        inversion Hexttabl; subst; clear Hexttabl.
        apply ext_tabs_lookup_exist in Hexttabslookup.
        destruct Hexttabslookup as [k Hlookup].
        rewrite list_lookup_fmap in Hlookup.
        destruct (v_imps !! k) eqn:Hvlookup => //.
        simpl in Hlookup.
        destruct (t_imps !! k) eqn:Htlookup; last by apply lookup_ge_None in Htlookup; rewrite <- Hvtlen in Htlookup; apply lookup_lt_Some in Hvlookup; lias.
        specialize (Himpwasm k m e Hvlookup Htlookup) as Hmdesc.
        destruct m; inversion Hlookup; subst; clear Hlookup.
        simpl in *.
        destruct Hmdesc as [tab [tt [Hwslookup [Hwtslookup [-> Htt]]]]].
        erewrite -> lookup_union_Some_l => //.
        rewrite Hwslookup in H1.
        apply N.leb_le in H1.
        unfold N_of_int in H1.
        rewrite <- Z_nat_N in H1.
        apply PeanoNat.Nat.leb_le.
        by lias.
      }
      { (* Alloc *)
        assert (forall {X: Type} (f: _ -> X), (map f l0) !! (n - length (ext_tabs (modexp_desc <$> v_imps))) = Some (f (Mk_tableidx n0))) as Hlookup.
        { intros.
          rewrite map_fmap list_lookup_fmap.
          by rewrite Hexttabl.
        }
        clear Hexttabl.
        specialize (Hlookup _ (fun '(Mk_tableidx i) => i)).
        rewrite Htindex in Hlookup.
        unfold gen_index in Hlookup.
        rewrite list_lookup_imap in Hlookup.
        destruct (repeat 0 _ !! _) eqn:Hrlookup => //=.
        simpl in Hlookup.
        inversion Hlookup; subst; clear Hlookup.
        apply elem_of_list_lookup_2, elem_of_list_In, repeat_spec in Hrlookup.
        subst.

        apply lookup_ge_None in Hexttabslookup.
        destruct (s_tables0 !! _) eqn:Hwslookup => //.
        { apply lookup_lt_Some in Hwslookup; by lias. }
        rewrite map_fmap in H1.
        repeat rewrite list_lookup_fmap in H1.
        destruct (mod_tables !! _) eqn:Hmtlookup => //.
        simpl in H1.
        destruct m, modtab_type, tt_limits => /=.
        simpl in *.
        rewrite repeat_length in H1.
        
        erewrite lookup_union_Some_r => //; last first.
        {
          apply elem_of_list_to_map.
          { rewrite fst_zip; last first.
            { repeat rewrite fmap_length.
              rewrite gen_index_length.
              by lias.
            }
            apply NoDup_fmap.
            { move => ???; by apply Nat2N.inj. }
            by apply gen_index_NoDup.
          }
          apply elem_of_list_lookup.
          exists (n-length (ext_tabs (modexp_desc <$> v_imps))).
          apply zip_lookup_Some.
          { repeat rewrite fmap_length.
            rewrite gen_index_length.
            by lias.
          }
          { rewrite list_lookup_fmap.
            rewrite gen_index_lookup; last first.
            { apply lookup_lt_Some in Hmtlookup; by lias. }
            simpl.
            do 2 f_equal.
            by lias.
          }
          { rewrite map_fmap.
            do 2 rewrite list_lookup_fmap.
            replace (_+_+_-_) with (n-length (ext_tabs (modexp_desc <$> v_imps))) in Hmtlookup; last by lias.
            by rewrite Hmtlookup.
          }
        }
        { simpl.
          unfold N_of_int in H1.
          rewrite repeat_length.
          rewrite <- Z_nat_N in H1.
          apply N.leb_le in H1.
          apply PeanoNat.Nat.leb_le.
          by lias.
        }
      }
    }
  { (* wts update *)
    by [].
  }
  (* gen_heaps *)
  { by []. }
  { by []. }
  { by []. }

  iMod "H" as "(Hwt & Htsize & Htlimit & Htm)".

  destruct s4.
    
  specialize (init_tabs_preserve _ _ _ _ _ Heqs4) as [Hf4 [Hm4 Hg4]].
  simpl in Hf4, Hm4, Hg4.
  rewrite -> Hf4, Hm4, Hg4 in *.
  clear Hf4 Hm4 Hg4.
  simpl.

  (* Split wts' back to the original form *)
  iAssert ( ([∗ map] n ↦ tabinst ∈ wts', n↦[wtblock] tabinst) -∗ (import_tab_wasm_check v_imps t_imps (module_import_init_tabs m inst wts)) ∗ (module_inst_resources_tab (module_inst_build_tables m inst) (drop (get_import_table_count m) inst.(inst_tab))))%I as "Htabsplit".
  {
    apply update_wts_split in Hwtsupd => //.
    destruct (update_wts_partial wts _ _ _) as [wts1' |] eqn: Hwtsimpupdate => //=.
    destruct (update_wts_partial wtsalloc _ _ _) as [wts2'|] eqn: Hwtsallocupdate => //=.
    iIntros "Hwts'".
    rewrite Hwtsupd.
    iDestruct (big_sepM_union with "Hwts'") as "(Hm1 & Hm2)".
    { (* disjointness *)
      apply map_disjoint_dom.
      apply map_disjoint_dom in Hwtsdisj.
      apply update_wts_partial_dom_preserve in Hwtsimpupdate.
      apply update_wts_partial_dom_preserve in Hwtsallocupdate.
      rewrite <- Hwtsimpupdate.
      rewrite <- Hwtsallocupdate.
      by apply Hwtsdisj.
    }
    iSplitL "Hm1".
    (* imports *)
    { 
      unfold import_tab_wasm_check.
      replace (module_import_init_tabs m inst wts) with wts1'.
      { iFrame.
        iPureIntro.
        unfold tab_typecheck, tab_domcheck.
        split.
        - (* Typecheck *)
          apply Forall2_lookup.
          move => i.
          destruct (v_imps !! i) eqn:Hvl => //=.
          + destruct (t_imps !! i) eqn:Htl => //=; last by apply lookup_lt_Some in Hvl; apply lookup_ge_None in Htl; lias.
            specialize (Himpwasm _ _ _ Hvl Htl) as Hvtlookup.
            apply Some_Forall2.
            destruct m0, modexp_desc => //=.
            destruct t.
            simpl in Hvtlookup.
            destruct Hvtlookup as [tab [tt [Hwt [Hwts [-> Htt]]]]].
            eapply update_wts_partial_lookup_type in Hwts => //.
            destruct Hwts as [tab' [Hwtslookup Htt']].
            by exists tab', tt.
          + destruct (t_imps !! i) eqn: Htl => //=; first by apply lookup_lt_Some in Htl; apply lookup_ge_None in Hvl; lias.
            by apply None_Forall2.
        - (* Dom *)
          apply update_wts_partial_dom_preserve in Hwtsimpupdate.
          by rewrite <- Htdom.
      }
      (* replace *)
      {
        (* Extremely tricky proof: having to two ways of obtaining the 
           final table contents are equivalent. *)
        unfold module_import_init_tabs.
        destruct m; simpl in *.
        rewrite Httlen.
        rewrite Heqtablebase in Htapp.
        rewrite -> Htapp in *.
        move/eqP in H1.
        move: Helemcb Hinstelem Hebound Hwtsimpupdate Htdom.
        unfold check_bounds_elem, module_elem_bound_check_gmap => /=.
        clear - Htindex H1 Hexttype Hvttablen Hexttabelem.
        move: wts1' wts e_offs.
        induction mod_elem => /=; intros; destruct e_offs => //=.
        { simpl in Hwtsimpupdate.
          by inversion Hwtsimpupdate.
        }
        simpl in Hwtsimpupdate.
        destruct a, modelem_table; simpl in *.
        rewrite nth_error_lookup in Helemcb.
        destruct (inst_tab inst !! n) eqn: Hinstlookup => //=.
        move/andP in Helemcb.
        destruct Helemcb as [Helem Helemcb].
        destruct (nth_error _ t0) eqn: Hwtlookup => //=.
        rewrite nth_error_lookup in Hwtlookup.
        apply N.leb_le in Helem.
        inversion Hinstelem; subst; clear Hinstelem.
        simpl in H3.
        inversion Hebound; subst; clear Hebound.
        destruct (assert_const1_i32 modelem_offset) eqn:Hmeoff => //=.
        destruct (wts !! N.of_nat t0) eqn: Hwtslookup => //=.
        { destruct (update_tab _ _ _) eqn: Hupdtab => //=.
          (* The key is that updtab shouldn't change the size of table. *)
          apply IHmod_elem in Hwtsimpupdate => //.
          3: (* Dom *)
          { rewrite <- Htdom.
            by rewrite dom_insert_lookup => //.
          }
          2: (* modelem boundcheck *)
          { apply Forall_lookup.
            rewrite -> Forall_lookup in H4.
            move => i x Helemlookup.
            specialize (H4 i x Helemlookup).
            destruct x, modelem_table => /=.
            destruct (assert_const1_i32 modelem_offset0) eqn:Haci32 => //.
            destruct (ext_tabs _ !! n0) eqn:Hexttabslookup => //.
            destruct t4 => /=.
            destruct (wts !! N.of_nat n1) eqn:Hwtslookup2 => //.
            destruct (decide (t0 = n1)); subst.
            - rewrite lookup_insert.
              rewrite Hwtslookup in Hwtslookup2.
              inversion Hwtslookup2; subst; clear Hwtslookup2.
              replace (length (table_data t3)) with (length (table_data t4)) => //.
              by eapply update_tab_length.
            - rewrite lookup_insert_ne; last by lias.
              by rewrite Hwtslookup2.
          }
          rewrite Hwtsimpupdate.
          f_equal.
          clear IHmod_elem Hwtsimpupdate.
          rewrite nth_error_lookup.
          rewrite Hinstlookup.
          rewrite Hwtslookup.
          destruct inst; simpl in *; subst.
          (* We deduce that the table is one of the import only via the dom of wts. *)
          assert (N.of_nat t0 ∈ (dom (gset N) wts)) as Ht0dom; first by apply elem_of_dom.
          rewrite -> Htdom in Ht0dom.
          rewrite -> elem_of_list_to_set in Ht0dom.
          simplify_lookup.
          apply Nat2N.inj in Heq; subst.
          apply Hexttabelem in Helem1.
          destruct (n <? length (ext_t_tabs t_imps)) eqn:Hnbound => /=; last first.
          { exfalso.
            rewrite map_fmap in Hinstlookup.
            rewrite list_lookup_fmap in Hinstlookup.
            destruct (( _ ++ l0) !! n) eqn:Hn => //.
            simpl in Hinstlookup.
            rewrite -> lookup_app_r in Hn.
            { destruct t0.
              inversion Hinstlookup; subst; clear Hinstlookup.
              assert (gen_index (length s_tables0) (length (map modtab_type mod_tables)) !! (n-length (ext_tabs (modexp_desc <$> v_imps))) = Some x).
              { rewrite <- Htindex.
                rewrite map_fmap.
                rewrite list_lookup_fmap.
                by rewrite Hn.
              }
              apply gen_index_lookup_Some in H.
              destruct H as [-> ?].
              by lias.
            }
            { rewrite Hvttablen in Hnbound.
              move/Nat.ltb_spec0 in Hnbound.
              by lias.
            }
          }
          (* To the main goal, where the two methods of obtaining single table is the same *)
          { f_equal.
            unfold update_tab in Hupdtab.
            unfold table_init_replace_single.
            destruct (_+_<=? _) eqn:Hle => //=.
            inversion Hupdtab; subst; clear Hupdtab.
            simpl in *.
            unfold assert_const1_i32_to_nat.
            rewrite Hmeoff => /=.
            f_equal.
            unfold lookup_funcaddr => /=.
            rewrite map_length map_fmap.
            repeat rewrite cat_app.
            
            unfold assert_const1_i32 in Hmeoff.
            destruct modelem_offset => //=.
            destruct b => //=.
            destruct v => //=.
            destruct modelem_offset => //=.
            inversion Hmeoff; subst; clear Hmeoff.
            apply reduce_trans_const in H3.
            inversion H3; subst; clear H3.
            replace (Z.to_nat (Wasm_int.Int32.intval t)) with (nat_of_int t) => //.
            remember ((take (nat_of_int t) (table_data t2) ++
     ((λ '(Mk_funcidx fidx), inst_funcs !! fidx) <$> modelem_init) ++
     drop (nat_of_int t + length modelem_init) (table_data t2))) as l.
            replace (length (table_data t2)) with (length l); first by rewrite firstn_all.
            subst.
            repeat rewrite app_length.
            rewrite fmap_length take_length drop_length.
            apply PeanoNat.Nat.leb_le in Hle.
            assert (nat_of_int t <= length (table_data t2)) as Hlt.
            { unfold nat_of_int; by lias. }
            replace (nat_of_int t `min` length (table_data t2)) with (nat_of_int t); last by lias.
            rewrite map_length in Hle.
            fold (nat_of_int t) in Hle.
            by lias.
          }
        }
       (* When wts !! t0 is none. In this case the table is not one of the imports and wts should not get updated. *)
        { 
          apply IHmod_elem in Hwtsimpupdate => //.
          rewrite Hwtsimpupdate.
          f_equal.
          destruct (n <? length (ext_t_tabs t_imps)) eqn:Hnbound => //=.
          exfalso.
          apply not_elem_of_dom in Hwtslookup.
          rewrite -> Htdom in Hwtslookup.
          apply Hwtslookup.
          rewrite -> elem_of_list_to_set.
          apply elem_of_list_fmap.
          exists t0.
          split => //.
          destruct inst; simpl in *; subst.
          rewrite map_fmap in Hinstlookup.
          rewrite list_lookup_fmap in Hinstlookup.
          destruct ((_ ++ l0) !! n) eqn :Hnl => //=.
          simpl in Hinstlookup.
          destruct t2.
          inversion Hinstlookup; subst; clear Hinstlookup.
          rewrite ext_tab_addrs_aux.
          apply PeanoNat.Nat.leb_le in Hnbound.
          rewrite Hvttablen in Hnbound.
          rewrite lookup_app_l in Hnl => //.

          apply elem_of_list_lookup.
          exists n.
          rewrite list_lookup_fmap.
          by rewrite Hnl.
        }
      }
    }

    (* alloc *)
    {
      (* The spirit of this is similar to the above part, although now
         updating the allocated part of the state instead of the imported. *)      
      unfold module_inst_resources_tab.
      assert (length (gen_index (length s_tables0) (length (mod_tables m))) =
  length (module_inst_build_tables m inst)) as Htblen.
      { rewrite gen_index_length.
        unfold module_inst_build_tables.
        apply fold_left_preserve.
        { unfold module_inst_table_base.
          by rewrite fmap_length.
        }
        { move => x act Hlen.
          destruct act, modelem_table => /=.
          destruct (n <? _) eqn:Hle => //.
          rewrite nth_error_lookup.
          destruct (x !! _) eqn: Hxl => //.
          by rewrite insert_length.
        }
      }

      iApply big_sepL2_flip.
      replace (drop _ (inst_tab inst)) with (gen_index (length s_tables0) (length (mod_tables m))); last first.
      { rewrite Httlen Hvttablen.
        move/eqP in H1.
        rewrite H1.
        rewrite map_fmap fmap_app.
        rewrite drop_app_alt; last by rewrite fmap_length.
        rewrite map_fmap in Htindex.
        rewrite Htindex.
        by rewrite map_length.
      }      
      iApply big_sepL2_big_sepM => //.
      { by apply gen_index_NoDup. }
      unfold module_inst_build_tables.
      replace (module_inst_table_base (mod_tables m)) with tablebase; last first.
      { rewrite Heqtablebase.
        unfold module_inst_table_base, module_inst_table_base_create.
        repeat rewrite map_fmap.
        rewrite <- list_fmap_compose.
        destruct m => /=.
        clear.
        induction mod_tables => //=.
        f_equal; last by apply IHmod_tables.
        by destruct a, modtab_type => /=.
      }
      iApply big_sepM_l2m_zip_f.
      { rewrite gen_index_length.
        apply fold_left_preserve => //.
        { rewrite Heqtablebase.
          by rewrite fmap_length map_length.
        }
        move => x act Hlen.
        destruct act, modelem_table.
        destruct (n <? _) => //.
        rewrite nth_error_lookup.
        destruct (x !! _) eqn: Hxl => //.
        by rewrite insert_length.
      }
      { by apply gen_index_NoDup. }
      (* Get the iris assertion away *)
      replace (list_to_map _) with wts2' => //.
      rewrite -> Heqwtsalloc in *.
      destruct m; simpl in *.
      move/eqP in H1.
      rewrite Httlen.
      assert (Forall2 (fun tt t => N.of_nat (length (t.(table_data))) = tt.(modtab_type).(tt_limits).(lim_min)) mod_tables tablebase) as Htbprop.
      {
        apply Forall2_same_length_lookup.
        split.
        { rewrite Heqtablebase.
          by rewrite fmap_length map_length.
        }
        { move => i elem t Hle Hlt.
          rewrite Heqtablebase in Hlt.
          rewrite map_fmap in Hlt.
          repeat rewrite list_lookup_fmap in Hlt.
          rewrite Hle in Hlt.
          simpl in Hlt.
          destruct elem, modtab_type, tt_limits; simpl in *.
          inversion Hlt => /=.
          rewrite repeat_length.
          by rewrite <- N_nat_bin.
        }
      }
      destruct inst; simpl in *.
      rewrite map_fmap in H1.
      assert (inst_tab = ((fun '(Mk_tableidx i) => i) <$> (ext_tabs (modexp_desc <$> v_imps))) ++ gen_index (length s_tables0) (length (fmap modtab_type mod_tables))) as Hinsttab.
      { repeat rewrite map_fmap in Htindex.
        rewrite <- Htindex.
        by rewrite <- fmap_app.
      }
      rewrite fmap_length in Hinsttab.
      clear H1.
      rewrite -> Hinsttab in *.
      clear Heqtablebase.
      rewrite -> Htapp in *.
      unfold check_bounds_elem in Helemcb.
      simpl in Helemcb.

      unfold module_elem_bound_check_gmap in Hebound.
      simpl in Hebound.

      assert (e_offs = e_inits') as Heeq.
      { move : Hinstelem Hmodelem.
        clear.
        move : e_inits' e_offs.
        induction mod_elem; intros; destruct e_inits'; destruct e_offs => //=.
        { apply Forall2_length in Hinstelem; by lias. }
        { apply Forall2_length in Hinstelem; by lias. }
        { inversion Hinstelem; subst; clear Hinstelem.
          simpl in Hmodelem.
          inversion Hmodelem; subst; clear Hmodelem.
          f_equal; last by apply IHmod_elem.
          destruct a; simpl in *; subst.
          apply reduce_trans_const in H2.
          by inversion H2.
        }
      }
      rewrite <- Heeq in *.
      move: Helemcb Hmodelem Hebound Hwtsallocupdate Htbprop Hvttablen.
      unfold check_bounds_elem => /=.
      
      clear - Hexttabelem Σ wasmG0.

      move : tablebase wts2' e_offs.
      induction mod_elem; intros; destruct e_offs; simpl in * => //=.
      { (* base *)
        by inversion Hwtsallocupdate.
      }
      destruct a, modelem_table; simpl in *.
      inversion Hebound; subst; clear Hebound.
      destruct (assert_const1_i32 modelem_offset) eqn:Hmeoff => //.
      unfold assert_const1_i32 in Hmeoff.
      destruct modelem_offset => //=.
      destruct b => //=.
      destruct v => //=.
      destruct modelem_offset => //=.
      inversion Hmeoff; subst; clear Hmeoff.
      inversion Hmodelem; subst; clear Hmodelem.
      move/andP in Helemcb.
      destruct Helemcb as [Hcb Helemcb].
      rewrite nth_error_lookup in Hcb.
      unfold lookup_funcaddr, assert_const1_i32_to_nat => /=.
      destruct (_ !! n) eqn:Hnl => //=.
      repeat rewrite -> nth_error_lookup in *.
      destruct ((s_tables0 ++ tablebase) !! t0) eqn:Htl; rewrite Htl in Hcb => //=.
      eapply IHmod_elem => //.
      { apply all2_Forall2.
        apply all2_Forall2 in Helemcb.
        apply Forall2_same_length_lookup.
        split; first by apply Forall2_length in Helemcb.
        move => i off elem Hlo Hle.
        rewrite -> Forall2_lookup in Helemcb.
        specialize (Helemcb i).
        rewrite Hlo Hle in Helemcb.
        inversion Helemcb; subst; clear Helemcb.
        destruct (nth_error _ _) eqn:Hn => //=.
        repeat rewrite -> nth_error_lookup in *.
        rewrite lookup_app in H4.
        rewrite lookup_app.
        destruct (s_tables0 !! t2) eqn:Hstlookup => /=.
        { rewrite Hstlookup in H4.
          by rewrite Hstlookup.
        }
        { rewrite Hstlookup in H4.
          rewrite Hstlookup.
          destruct (n <? _) eqn:Hlt => //=.
          destruct (tablebase !! (n - _)) eqn:Htblookup => //=.
          destruct (decide ((n - length (ext_t_tabs t_imps)) = (t2 - length s_tables0))) eqn:Hd => //=.
          { rewrite e.
            rewrite -> Forall2_lookup in Htbprop.
            specialize (Htbprop (t2-length s_tables0)).
            destruct (tablebase !! _) eqn:Htblookup2 => //=.
            rewrite list_lookup_insert; last by apply lookup_lt_Some in Htblookup2.
            rewrite nth_error_lookup in Hn.
            destruct elem, modelem_table => /=.
            simpl in *.
            rewrite -> e in *.
            inversion Htbprop; subst; clear Htbprop.
            rewrite take_length.
            repeat rewrite app_length.
            rewrite take_length drop_length fmap_length.
            apply N.leb_le.
            rewrite Htblookup2 in Htblookup.
            inversion Htblookup; subst; clear Htblookup.
            destruct x, modtab_type, tt_limits => //=.
            simpl in *.
            apply N.leb_le in H4.
            by lias.
          }
          {
            by rewrite list_lookup_insert_ne => //.
          }
        }
      }
      2: {
        remember (if n<? length (_) then _ else _) as tablebase'.
        assert (length tablebase = length tablebase') as Htlen.
        { destruct (n <? _); first by subst.
          destruct (tablebase !! _); last by subst.
          rewrite Heqtablebase'.
          by rewrite insert_length.
        }
        apply Forall2_same_length_lookup.
        split => //; first by apply Forall2_length in Htbprop; lias.
        move => i mt ti Hmtl Htil.
        rewrite -> Forall2_lookup in Htbprop.
        specialize (Htbprop i).
        rewrite Hmtl in Htbprop.
        inversion Htbprop; subst; clear Htbprop.
        destruct (n <? _) eqn:Hlt.
        { rewrite Htil in H0.
          inversion H0; subst; by rewrite <- H4.
        }
        destruct (tablebase !! (n - length (ext_t_tabs t_imps))) eqn:Htblookup => //=; last first.
        { rewrite Htil in H0.
          inversion H0; subst; by rewrite <- H4.
        }
        rewrite <- H4; f_equal.
        destruct (decide (n-length (ext_t_tabs t_imps) = i)) => //=; last first.
        { rewrite list_lookup_insert_ne in Htil => //.
          rewrite Htil in H0.
          by inversion H0.
        }
        { subst.
          rewrite list_lookup_insert in Htil; last by eapply lookup_lt_Some.
          inversion Htil; subst; clear Htil.
          unfold table_init_replace_single => /=.
          rewrite take_length.
          repeat rewrite app_length.
          rewrite take_length drop_length fmap_length.
          rewrite Htblookup in H0.
          inversion H0; subst; clear H0.
          by lias.
        }
      }
      {
        remember (if n <? _ then tablebase else _) as tablebase'.
        rewrite -> Hvttablen in *.
        rewrite lookup_app in Hnl.
        destruct ((_ <$> _) !! n) eqn:Himplookup => //=.
        { (* Not updating the table since it's targeting at imports *)
          inversion Hnl; subst; clear Hnl.
          erewrite not_elem_of_list_to_map_1 in Hwtsallocupdate.
          2: {
               apply Hexttabelem in Himplookup.
               rewrite elem_of_list_lookup.
               move => [i HContra].
               rewrite fst_zip in HContra; last first.
               { rewrite fmap_length gen_index_length.
                 apply Forall2_length in Htbprop. by lias.
               }
               rewrite list_lookup_fmap in HContra.
                 
               destruct (gen_index _ _ !! i) eqn:Hgl => //=.
               apply gen_index_lookup_Some in Hgl as [-> Hlt].
               simpl in HContra.
               inversion HContra.
               by lias.
          }
          rewrite <- Hwtsallocupdate.
          do 3 f_equal.
          apply lookup_lt_Some in Himplookup.
          rewrite fmap_length in Himplookup.
          move/Nat.ltb_lt in Himplookup.
          by rewrite Himplookup.
        }
        { (* Updating the table *)
          apply gen_index_lookup_Some in Hnl as [-> Hnl].
          rewrite fmap_length in Hnl.
          destruct (tablebase !! (n-length (ext_tabs (modexp_desc <$> v_imps)))) eqn:Hmtlookup; last by apply lookup_ge_None in Hmtlookup; apply Forall2_length in Htbprop; lias => //.
          erewrite elem_of_list_to_map_1 in Hwtsallocupdate => //.
          2: { rewrite fst_zip; last first.
               { rewrite fmap_length gen_index_length.
                 apply Forall2_length in Htbprop. by lias.
               }
               apply NoDup_fmap; first by lias.
               by apply gen_index_NoDup.
          }
          2: { apply elem_of_list_lookup.
               rewrite fmap_length.
               exists (n-length (ext_tabs (modexp_desc <$> v_imps))).
               apply zip_lookup_Some.
               { rewrite fmap_length gen_index_length.
                  by apply Forall2_length in Htbprop.
               }
               { rewrite list_lookup_fmap.
                 by rewrite gen_index_lookup => //.
               }
               { by rewrite Hmtlookup => //.
               }
          }
          destruct (update_tab _ _ _) eqn:Hupdtab => //=.
          rewrite <- Hwtsallocupdate.
          f_equal.
          rewrite fmap_length.
          destruct (n<? length(ext_tabs (modexp_desc <$> v_imps))) eqn:Hlt; first by move/Nat.ltb_lt in Hlt; apply lookup_ge_None in Himplookup; rewrite fmap_length in Himplookup; lias.
          rewrite Heqtablebase'.
          replace (table_init_replace_single _ _ _) with t2; last first.
          { unfold update_tab in Hupdtab.
            unfold table_init_replace_single.
            destruct (_ <=? _) eqn:Hle => //=.
            inversion Hupdtab; subst; clear Hupdtab.
            f_equal.
            rewrite map_fmap.
            repeat rewrite fmap_length.
            replace (Z.to_nat (Wasm_int.Int32.intval t)) with (nat_of_int t) => //.
            assert (length (take (nat_of_int t) (table_data t0) ++
   ((λ '(Mk_funcidx j), inst_funcs !! j) <$> modelem_init) ++
   drop (nat_of_int t + length modelem_init) (table_data t0)) = length (table_data t0)) as Hlen.
            { repeat rewrite app_length.
              rewrite take_length drop_length fmap_length.
              move/Nat.leb_le in Hle.
              apply N.leb_le in Hcb.
              rewrite lookup_app_r in Htl; last by lias.
              rewrite fmap_length in Htl.
              replace (_+_-_) with (n-length (ext_tabs (modexp_desc <$> v_imps))) in Htl; last by lias.
              rewrite Hmtlookup in Htl.
              inversion Htl; subst; clear Htl.
              rewrite map_length in Hle.
              unfold nat_of_int.
              by lias.
            }
            rewrite <- Hlen.
            by rewrite firstn_all.
          }
          erewrite list_to_map_zip_insert => //.
          { apply NoDup_fmap; first by lias.
            by apply gen_index_NoDup.
          }
          { rewrite list_lookup_fmap.
            by rewrite gen_index_lookup => /=; last by lias.
          }
        }
      }
    }
  }
          
  iDestruct ("Htabsplit" with "Htm") as "(Htmimp & Htmalloc)".

  (* init_mems *)
  move/eqP in Hs'.
  symmetry in Hs'.
(*  iDestruct (init_mems_state_update $! Hs' with "[Htm] [$] [$] [$] [Hmmapsto]") as "H" => /=.
  { instantiate (1 := wgs).
    instantiate (1 := wms).
    instantiate (1 := (module_import_init_tabs m inst wts)).
    instantiate (1 := wfs).
    instantiate (1 := t_imps).
    instantiate (1 := v_imps).
    instantiate (1 := wts ∪ wtsalloc).
    admit. }
  {
    rewrite Hmapp.
    rewrite app_length fmap_length.
    iApply (big_sepL_mono with "Hmmapsto").
    move => k mem Hmem.
    iIntros "Hmm".
    replace (_+_+_-_) with (length s_mems1 + k) => //.
    clear.
    destruct m => /=.
    induction mod_mems => //=; lias. (* TODO: mysterious lias fail *)
  }
    
  iMod "H" as "(Hwimport & Hwm & Hmsize & Hmlimit & Hmmapsto)".*)

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

  iSplitL "Hirwtf Hirwtm Hirwtg".
  (* tmp case, won't exist after fixing *)
  { admit. }
  
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
  }*)
Admitted.
                     

End Iris_instantiation.

