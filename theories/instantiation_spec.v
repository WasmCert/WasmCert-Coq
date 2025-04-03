(** Relational instantiation in the spec **)
(* see https://webassembly.github.io/spec/core/exec/modules.html#exec-instantiation *)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import list_extra datatypes datatypes_properties
                        binary_format_parser operations
                         typing opsem type_checker memory memory_list.
From Coq Require Import BinNat.

(* TODO: Documentation *)

Section Instantiation_spec.
  
Context `{ho: host}.

Definition alloc_Xs {A B} f (s : store_record) (xs : list A) : store_record * list B :=
  let '(s', fas) :=
    List.fold_left
      (fun '(s, ys) x =>
        let '(s', y) := f s x in
        (s', y :: ys))
        xs
        (s, nil) in
  (s', List.rev fas).

Definition funcs_of_externals (evs : list extern_value) : list funcaddr :=
  seq.pmap (fun ev => match ev with | EV_func fa => Some fa | _ => None end) evs.

Definition tables_of_externals (evs : list extern_value) : list tableaddr :=
  seq.pmap (fun ev => match ev with | EV_table ta => Some ta | _ => None end) evs.

Definition mems_of_externals (evs : list extern_value) : list memaddr :=
  seq.pmap (fun ev => match ev with | EV_mem ta => Some ta | _ => None end) evs.

Definition globals_of_externals (evs : list extern_value) : list globaladdr :=
  seq.pmap (fun ev => match ev with | EV_global ta => Some ta | _ => None end) evs.

Definition add_func (s : store_record) funcinst := {|
  s_funcs := cat s.(s_funcs) [::funcinst];
  s_tables := s.(s_tables);
  s_mems := s.(s_mems);
  s_globals := s.(s_globals);
  s_elems := s.(s_elems);
  s_datas := s.(s_datas);
|}.

Definition gen_func_instance mf inst : funcinst :=
  match lookup_N inst.(inst_types) mf.(modfunc_type) with
  | Some ft =>
      FC_func_native ft inst mf
  | None =>
      (* Will not happen for well-typed modules *)
      FC_func_native (Tf nil nil) inst mf
  end.
                
Definition alloc_func (s : store_record) (m_f : module_func) (mi : moduleinst) : store_record * funcaddr :=
  let funcaddr := N.of_nat (List.length s.(s_funcs)) in
  (* Spec didn't say what if this is out of bound; but it cannot happen to valid modules *)
  let funcinst := gen_func_instance m_f mi in
  let S' := add_func s funcinst in
  (S', funcaddr).

Definition alloc_funcs (s : store_record) (m_fs : list module_func) (mi : moduleinst) : store_record * list funcaddr :=
  alloc_Xs (fun s m_f => alloc_func s m_f mi) s m_fs.

Definition add_table (s : store_record) (ti : tableinst) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := cat s.(s_tables) [::ti];
  s_mems := s.(s_mems);
  s_globals := s.(s_globals);
  s_elems := s.(s_elems);
  s_datas := s.(s_datas);
|}.

Definition gen_table_instance (mt: table_type) ref: tableinst :=
  let '{| tt_limits := {| lim_min := min; lim_max := maxo |} as lim; tt_elem_type := ety |} := mt in
  {| tableinst_elem := (List.repeat ref (N.to_nat min));
    tableinst_type := mt;
  |}.
  
Definition alloc_tab_ref (s : store_record) (tty : table_type) (ref: value_ref) : store_record * tableaddr :=
  let '{| tt_limits := {| lim_min := min; lim_max := maxo |} as lim; tt_elem_type := ety |} := tty in
  let tableaddr := N.of_nat (List.length s.(s_tables)) in
  let tableinst := gen_table_instance tty ref in
  (add_table s tableinst, tableaddr).

Definition alloc_tab s tty: store_record * tableaddr :=
  alloc_tab_ref s tty (VAL_ref_null tty.(tt_elem_type)).

Definition alloc_tabs (s : store_record) (ts : list table_type) : store_record * list tableaddr :=
  alloc_Xs alloc_tab s ts.

Definition gen_mem_instance (lim : limits) : meminst :=
  let len := BinNatDef.N.mul page_size lim.(lim_min) in
  {| meminst_data := mem_make Integers.Byte.zero len;
    meminst_type := lim;
  |}.

Definition add_mem (s : store_record) (m_m : meminst) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := cat s.(s_mems) [::m_m];
  s_globals := s.(s_globals);
  s_elems := s.(s_elems);
  s_datas := s.(s_datas);
|}.

Definition alloc_mem (s : store_record) (m_mt : memory_type) : store_record * memaddr :=
  let '{| lim_min := min; lim_max := maxo |} := m_mt in
  let memaddr := N.of_nat (List.length s.(s_mems)) in
  let meminst := gen_mem_instance m_mt in
  (add_mem s meminst, memaddr).

Definition alloc_mems (s : store_record) (m_mts : list memory_type) : store_record * list memaddr :=
  alloc_Xs alloc_mem s m_mts.

Definition add_glob (s : store_record) (m_g : globalinst) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := s.(s_mems);
  s_globals := cat s.(s_globals) [::m_g];
  s_elems := s.(s_elems);
  s_datas := s.(s_datas);
|}.

Definition gen_global_instance (gt: module_global) (v: value): globalinst :=
  {|
    g_type := gt.(modglob_type);
    g_val := v
  |}.
    
Definition alloc_glob (s : store_record) (m_g_v : module_global * value) : store_record * globaladdr :=
  let '(mg_type, v) := m_g_v in
  let globaddr := N.of_nat (List.length s.(s_globals)) in
  let globinst := gen_global_instance mg_type v in
  (add_glob s globinst, globaddr).

Definition alloc_globs s m_gs vs :=
  alloc_Xs alloc_glob s (List.combine m_gs vs).

Definition add_elem (s : store_record) (m_e : eleminst) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := s.(s_mems);
  s_globals := s.(s_globals);
  s_elems := cat s.(s_elems) [::m_e];
  s_datas := s.(s_datas);
|}.

Definition alloc_elem (s: store_record) (m_e_v: module_element * list value_ref) : store_record * elemaddr :=
  let '(m_e, refs) := m_e_v in
  let reftype := m_e.(modelem_type) in
  let elemaddr := N.of_nat (List.length s.(s_elems)) in
  let eleminst := Build_eleminst reftype refs in
  (add_elem s eleminst, elemaddr).

Definition alloc_elems (s : store_record) (m_es : list module_element) (elem_inits: list (list value_ref)) : store_record * list elemaddr :=
  alloc_Xs alloc_elem s (List.combine m_es elem_inits).

Definition add_data (s : store_record) (m_d : datainst) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := s.(s_mems);
  s_globals := s.(s_globals);
  s_elems := s.(s_elems);
  s_datas := cat s.(s_datas) [::m_d];
|}.

Definition alloc_data (s: store_record) (m_d: module_data) : store_record * dataaddr :=
  let dataaddr := N.of_nat (List.length s.(s_datas)) in
  let datainst := Build_datainst m_d.(moddata_init) in
  (add_data s datainst, dataaddr).

Definition alloc_datas (s : store_record) (m_d: list module_data) : store_record * list dataaddr :=
  alloc_Xs alloc_data s m_d.

Definition export_get_v_ext (inst : moduleinst) (exp : module_export_desc) : extern_value :=
  (* we circumvent partiality by providing 0 as a default. This is fine as the module_typing
     relation will validate of the export indices *)
  match exp with
  | MED_func i => EV_func ( (List.nth i inst.(inst_funcs) N0))
  | MED_table i => EV_table ( (List.nth i inst.(inst_tables) N0))
  | MED_mem i => EV_mem ( (List.nth i inst.(inst_mems) N0))
  | MED_global i => EV_global ( (List.nth i inst.(inst_globals) N0))
  end.

Definition ext_funcs :=
  seq.pmap
    (fun x =>
      match x with
      | EV_func i => Some i
      | _ => None
      end).

Definition ext_tables :=
  seq.pmap
    (fun x =>
      match x with
      | EV_table i => Some i
      | _ => None
      end).

Definition ext_mems :=
  seq.pmap
    (fun x =>
      match x with
      | EV_mem i => Some i
      | _ => None
      end).

Definition ext_globals :=
  seq.pmap
    (fun x =>
      match x with
      | EV_global i => Some i
      | _ => None
      end).

Definition ext_t_funcs :=
  seq.pmap
    (fun x =>
      match x with
      | ET_func tf => Some tf
      | _ => None
      end).

Definition ext_t_tables :=
  seq.pmap
    (fun x =>
      match x with
      | ET_table i => Some i
      | _ => None
      end).

Definition ext_t_mems :=
  seq.pmap
    (fun x =>
      match x with
      | ET_mem i => Some i
      | _ => None
      end).

Definition ext_t_globals :=
  seq.pmap
    (fun x =>
      match x with
      | ET_global i => Some i
      | _ => None
      end).

Definition get_exportinst (inst: moduleinst) (m_exp: module_export) : exportinst :=
  let extern_value := export_get_v_ext inst m_exp.(modexp_desc) in
  Build_exportinst m_exp.(modexp_name) extern_value.

Definition alloc_module (s : store_record) (m : module) (imps : list extern_value) (gvs : list value) (rvs: list (list value_ref))
    (s'_inst : store_record * moduleinst) : bool :=
  let '(s'_goal, inst) := s'_inst in
  let '(s1, i_fs) := alloc_funcs s m.(mod_funcs) inst in
  let '(s2, i_ts) := alloc_tabs s1 (map modtab_type m.(mod_tables)) in
  let '(s3, i_ms) := alloc_mems s2 (map modmem_type m.(mod_mems)) in
  let '(s4, i_gs) := alloc_globs s3 m.(mod_globals) gvs in
  let '(s5, i_es) := alloc_elems s4 m.(mod_elems) rvs in
  let '(s', i_ds) := alloc_datas s5 m.(mod_datas) in
  (s'_goal == s') &&
  (inst.(inst_types) == m.(mod_types)) &&
  (inst.(inst_funcs) == ((ext_funcs imps) ++ i_fs)) &&
  (inst.(inst_tables) == ((ext_tables imps) ++ i_ts)) &&
  (inst.(inst_mems) == ((ext_mems imps) ++ i_ms)) &&
  (inst.(inst_globals) == ((ext_globals imps) ++ i_gs)) &&
  (inst.(inst_elems) == i_es) &&
  (inst.(inst_datas) == i_ds) &&
  (inst.(inst_exports) == (map (get_exportinst inst) m.(mod_exports))).

Definition dummy_table : tableinst := {| tableinst_elem := nil; tableinst_type := Build_table_type (Build_limits N0 None) T_funcref |}.

Definition module_func_typing (c : t_context) (mf : module_func) (tf : function_type) : Prop :=
  let '{| modfunc_type := x; modfunc_locals := t_locs; modfunc_body := b_es |} := mf in
  let '(Tf tn tm) := tf in
  lookup_N c.(tc_types) x = Some (Tf tn tm) /\
  let c' := upd_local_label_return c (tn ++ t_locs) [::tm] (Some tm) in
  be_typing c' b_es (Tf [::] tm) /\
  (* Revise when non-defaultable types are added *)
  default_vals t_locs <> None.

Definition module_table_typing (c: t_context) (t : module_table) (tabt: table_type) : bool :=
  tabletype_valid t.(modtab_type) && (t.(modtab_type) == tabt).

Definition module_mem_typing (c: t_context) (m : module_mem) (mt: memory_type) : bool :=
  memtype_valid m.(modmem_type) && (m.(modmem_type) == mt).

Definition const_expr (c : t_context) (b_e : basic_instruction) : bool :=
  match b_e with
  | BI_const_num _ => true
  | BI_const_vec _ => true
  | BI_ref_null _ => true
  | BI_ref_func _ => true
  | BI_global_get k =>
      match lookup_N c.(tc_globals) k with
      | None => false
      | Some t => t.(tg_mut) == MUT_const
      end
  | _ => false
  end.

Definition const_exprs (c : t_context) (es : list basic_instruction) : bool :=
  seq.all (const_expr c) es.

Definition module_global_typing (c : t_context) (g : module_global) (tg : global_type) : Prop :=
  let '{| modglob_type := tg'; modglob_init := es |} := g in
  const_exprs c es /\
  tg = tg' /\
    typing.be_typing c es (Tf nil [::tg.(tg_t)]).

Definition elemmode_valid (c: t_context) (emode: module_elemmode) (t: reference_type) : Prop :=
  match emode with
  | ME_passive => True
  | ME_active tidx es =>
      exists tabtype,
      lookup_N c.(tc_tables) tidx = Some tabtype /\
      let '{| tt_limits := t_lim; tt_elem_type := rt |} := tabtype in
      rt = t /\
      typing.be_typing c es (Tf nil [::T_num T_i32]) /\
      const_exprs c es
  | ME_declarative => True
  end.

Definition module_elem_typing (c : t_context) (e : module_element) (t: reference_type) : Prop :=
  let '{| modelem_type := t'; modelem_init := e_inits; modelem_mode := emode |} := e in
  t = t' /\
  List.Forall (fun es => const_exprs c es /\ typing.be_typing c es (Tf nil [::T_ref t])) e_inits /\
  elemmode_valid c emode t.  

Definition datamode_valid (c: t_context) (dmode: module_datamode) : Prop :=
  match dmode with
  | MD_passive => True
  | MD_active midx es =>
      exists memtype,
      lookup_N c.(tc_mems) midx = Some memtype /\
      typing.be_typing c es (Tf nil [::T_num T_i32]) /\
      const_exprs c es
  end.

Definition module_data_typing (c : t_context) (m_d : module_data) (t: ok): Prop :=
  let '{| moddata_init := bs; moddata_mode := dmode |} := m_d in
  datamode_valid c dmode /\
  t = tt.

Definition module_start_typing (c : t_context) (ms : module_start) : bool :=
  let x := ms.(modstart_func) in
  match lookup_N c.(tc_funcs) x with
  | None => false
  | Some tf => tf == (Tf nil nil)
  end.

Definition module_import_desc_typing (c : t_context) (imp_desc : module_import_desc) (e : extern_type) : bool := 
  match imp_desc with
  | MID_func i => (option_map ET_func (lookup_N c.(tc_types) i) == Some e)
  | MID_table t_t =>
      tabletype_valid t_t && (e == ET_table t_t)
  | MID_mem mt =>
      memtype_valid mt && (e == ET_mem mt)
  | MID_global gt => ET_global gt == e
  end.

Definition module_import_typing (c: t_context) (imp: module_import) (e: extern_type) :=
  module_import_desc_typing c imp.(imp_desc) e.

Definition module_export_desc_typing (c : t_context) (d : module_export_desc) (e : extern_type) : bool :=
  match (d, e) with
  | (MED_func i, ET_func tf) =>
    match lookup_N c.(tc_funcs) i with
    | None => false
    | Some tf' => tf == tf'
    end
  | (MED_table i, ET_table t_t) =>
    match lookup_N c.(tc_tables) i with
    | None => false
    | Some lim' => t_t == lim'
    end
  | (MED_mem i, ET_mem t_m) =>
    match lookup_N c.(tc_mems) i with
    | None => false
    | Some lim' => t_m == lim' 
    end
  | (MED_global i, ET_global gt) =>
    match lookup_N c.(tc_globals) i with
    | None => false
    | Some gt' => gt == gt'
    end
  | (_, _) => false
  end.

Definition pred_option {A} (p : A -> bool) (a_opt : option A) : bool :=
  match a_opt with
  | None => true
  | Some a => p a
  end.

Definition module_export_typing (c: t_context) (exp: module_export) (e: extern_type) :=
  module_export_desc_typing c exp.(modexp_desc) e.

Definition nlist_nodup : list N -> list N := List.nodup N.eq_dec.

(* This filters duplicate using the most native method. The spec is ambiguous on what a 'set' is to be fair. *)
Fixpoint be_get_funcidx (be: basic_instruction) : list funcidx :=
  match be with
  | BI_ref_func x => [:: x]
  | BI_call x => [:: x]
  | BI_block _ bes => nlist_nodup (List.concat (List.map be_get_funcidx bes))
  | BI_if _ bes1 bes2 => nlist_nodup (List.concat (List.map be_get_funcidx bes1) ++ List.concat (List.map be_get_funcidx bes2))
  | BI_loop _ bes => nlist_nodup (List.concat (List.map be_get_funcidx bes))
  | _ => nil
  end.

Definition expr_get_funcidx (bes: expr) : list funcidx :=
  nlist_nodup (List.concat (List.map be_get_funcidx bes)).

Definition module_globals_get_funcidx (gs: list module_global) :=
  nlist_nodup (List.concat (List.map (fun x => expr_get_funcidx x.(modglob_init)) gs)).

Definition module_elem_get_funcidx (el: module_element) :=
  nlist_nodup (List.concat (List.map expr_get_funcidx el.(modelem_init)) ++
    match el.(modelem_mode) with
    | ME_active _ es => expr_get_funcidx es
    | _ => nil
    end).

Definition module_elems_get_funcidx (els: list module_element) :=
  nlist_nodup (List.concat (List.map module_elem_get_funcidx els)).

(** std-doc: the set of function indices occurring in the module, except in its
  functions or start function.

  Used in generating the refs components.
 **)
(* But then, what is left -- just the global initialisers and elems? *)
Definition module_filter_funcidx (m: module) : list funcidx :=
  nlist_nodup
    (module_globals_get_funcidx m.(mod_globals) ++
     module_elems_get_funcidx m.(mod_elems)).

Definition export_name_unique (exps: list module_export) : bool :=
  List.nodup name_eq_dec (map modexp_name exps) == (map modexp_name exps).

(* We deliberately omit the artificial restriction on the length of memory here. *)
Definition module_typing (m : module) (impts : list extern_type) (expts : list extern_type) : Prop :=
  exists fts tts mts gts rts dts,
  let '{|
    mod_types := tfs;
    mod_funcs := fs;
    mod_tables := ts;
    mod_mems := ms;
    mod_globals := gs;
    mod_elems := els;
    mod_datas := ds;
    mod_start := i_opt;
    mod_imports := imps;
    mod_exports := exps;
  |} := m in
  let ifts := ext_t_funcs impts in
  let its := ext_t_tables impts in
  let ims := ext_t_mems impts in
  let igs := ext_t_globals impts in
  let xs := module_filter_funcidx m in
  let c := {|
    tc_types := tfs;
    tc_funcs := ifts ++ fts;
    tc_tables := its ++ tts;
    tc_mems := ims ++ mts;
    tc_globals := igs ++ gts;
    tc_elems := rts;
    tc_datas := dts;
    tc_locals := nil;
    tc_labels := nil;
    tc_return := None;
    tc_refs := xs;
  |} in
  let c' := {|
    tc_types := nil;
    tc_funcs := c.(tc_funcs);
    tc_tables := c.(tc_tables);
    tc_mems := c.(tc_mems);
    tc_globals := igs;
    tc_elems := nil;
    tc_datas := nil;
    tc_locals := nil;
    tc_labels := nil;
    tc_return := None;
    tc_refs := xs;
  |} in
  List.Forall functype_valid tfs /\
  List.Forall2 (module_func_typing c) fs fts /\
  List.Forall2 (module_table_typing c') ts tts /\
  List.Forall2 (module_mem_typing c') ms mts /\
  List.Forall2 (module_global_typing c') gs gts /\
  List.Forall2 (module_elem_typing c') els rts /\
  List.Forall2 (module_data_typing c') ds dts /\
  pred_option (module_start_typing c) i_opt /\
  List.Forall2 (module_import_typing c) imps impts /\
  List.Forall2 (module_export_typing c) exps expts /\
  export_name_unique exps. 

(** std-doc:
For the purpose of checking external values against imports, such values are classified by external types. The following auxiliary typing rules specify this typing relation relative to a store S in which the referenced instances live.
*)
Definition external_typing (s: store_record) (e: extern_value) (t: extern_type) :=
  ext_typing s e = Some t.

Definition instantiate_globals f (hs : host_state) (s' : store_record) m (g_inits: list value) : Prop :=
  List.Forall2 (fun g v =>
      opsem.reduce_trans (hs, s', f, to_e_list g.(modglob_init))
                         (hs, s', f, [::v_to_e v]))
    m.(mod_globals) g_inits.

Definition instantiate_elems f (hs : host_state) (s' : store_record) m (r_inits: list (list value_ref)) : Prop :=
  List.Forall2
    (fun e rs => List.Forall2
                   (fun bes r =>
                      opsem.reduce_trans
                        (hs, s', f, to_e_list bes)
                        (hs, s', f, [::v_to_e (VAL_ref r)]))
                   e.(modelem_init) rs)
    m.(mod_elems)
    r_inits.

Definition get_init_expr_elem (i: nat) (elem: module_element) : list basic_instruction :=
  match elem.(modelem_mode) with
  | ME_passive => nil
  | ME_active tidx bes =>
      bes ++ [::BI_const_num (VAL_int32 (Wasm_int.int_of_Z i32m Z0)); BI_const_num (VAL_int32 (Wasm_int.int_of_Z i32m (BinInt.Z.of_nat (length elem.(modelem_init))))); BI_table_init tidx (N.of_nat i); BI_elem_drop (N.of_nat i)]
  | ME_declarative => [::BI_elem_drop (N.of_nat i)]
  end.

Definition get_init_expr_elems (elems: list module_element) : list basic_instruction :=
  List.concat (mapi (fun n => get_init_expr_elem n) elems).

Definition get_init_expr_data (i: nat) (data: module_data) : list basic_instruction :=
  match data.(moddata_mode) with
  | MD_passive => nil
  | MD_active midx bes =>
      bes ++ [::BI_const_num (VAL_int32 (Wasm_int.int_zero i32m)); BI_const_num (VAL_int32 (Wasm_int.int_of_Z i32m (BinInt.Z.of_nat (length data.(moddata_init))))); BI_memory_init (N.of_nat i); BI_data_drop (N.of_nat i)]
  end.

Definition get_init_expr_datas (datas: list module_data) : list basic_instruction :=
  List.concat (mapi (fun n => get_init_expr_data n) datas).

Definition get_init_expr_start (mstart: option module_start) : list basic_instruction :=
  match mstart with
  | Some (Build_module_start n) => [::BI_call n]
  | _ => nil
  end.

(* The following definitions needs a revisit when implementing the GC/funcref proposal *)
Definition limits_subtyping (l1 l2: limits) : bool :=
  (N.leb l2.(lim_min) l1.(lim_min)) &&
    match l1.(lim_max), l2.(lim_max) with
    | _, None => true
    | Some max1, Some max2 => N.leb max1 max2
    | _, _ => false
    end.

Definition import_func_subtyping (t1 t2: function_type) : bool :=
  t1 == t2.

Definition import_table_subtyping (t1 t2: table_type) : bool :=
  (t1.(tt_elem_type) == t2.(tt_elem_type)) &&
    limits_subtyping t1.(tt_limits) t2.(tt_limits).

Definition import_mem_subtyping (t1 t2: memory_type) : bool :=
  limits_subtyping t1 t2.

Definition import_global_subtyping (t1 t2: global_type) : bool :=
  t1 == t2.

Definition import_subtyping (t1 t2: extern_type) : bool :=
  match t1, t2 with
  | ET_func tf1, ET_func tf2 =>
      import_func_subtyping tf1 tf2
  | ET_table tt1, ET_table tt2 =>
      import_table_subtyping tt1 tt2
  | ET_mem tm1, ET_mem tm2 =>
      import_mem_subtyping tm1 tm2
  | ET_global tg1, ET_global tg2 =>
      import_global_subtyping tg1 tg2
  | _, _ => false
  end.

(* In Wasm 2.0, the module exports are now a part of the module instance. *)
Definition instantiate (s : store_record) (m : module) (v_imps : list extern_value)
                       (z : (store_record * frame * list basic_instruction)) : Prop :=
  let '(s_end, f, bes) := z in
  exists t_imps_mod t_imps t_exps hs' inst g_inits r_inits,
    module_typing m t_imps_mod t_exps /\
    List.Forall2 (external_typing s) v_imps t_imps /\
    List.Forall2 import_subtyping t_imps t_imps_mod /\
    alloc_module s m v_imps g_inits r_inits (s_end, inst) /\
    let inst_init := Build_moduleinst nil inst.(inst_funcs) nil nil (ext_globals v_imps) nil nil nil in
    let f_init := Build_frame nil inst_init in
    (* Init values *)
    instantiate_globals f_init hs' s_end m g_inits /\
    instantiate_elems f_init hs' s_end m r_inits /\
    f = Build_frame nil inst /\
      bes = get_init_expr_elems m.(mod_elems) ++ get_init_expr_datas m.(mod_datas) ++ get_init_expr_start m.(mod_start).

End Instantiation_spec.
