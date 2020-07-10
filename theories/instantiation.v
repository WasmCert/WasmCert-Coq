(* Instantiation *)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From ITree Require Import ITree.
From ITree Require ITreeFacts.
From Wasm Require Import list_extra datatypes datatypes_properties
                         interpreter binary_format_parser operations
                         typing opsem type_checker.

(* TODO: Documentation *)

(* TODO: separate algorithmic aspects from specification, incl. dependencies *)

(* TODO: get rid of old notation that doesn't follow standard *)

Section Host.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record_eq_dec := @store_record_eq_dec host_function.
Let store_record_eqType := @store_record_eqType host_function.

Local Canonical Structure name_eqType := Eval hnf in EqType name (seq_eqMixin _).

Let store_record := store_record host_function.
Let administrative_instruction := administrative_instruction host_function.
Let host_state := host_state host_instance.
Let executable_host := executable_host host_function.

Variable executable_host_instance : executable_host.

Let host_event := host_event executable_host_instance.
Context {eff : Type -> Type}.
Context {eff_has_host_event : host_event -< eff}.

Let run_v {eff' eff'_has_host_event} :=
  @interpreter.run_v host_function executable_host_instance eff' eff'_has_host_event.

Definition addr := nat.
Definition funaddr := addr.
Definition tableaddr := addr.
Definition memaddr := addr.
Definition globaladdr := addr.

Definition alloc_Xs {A B} f (s : store_record) (xs : list A) : store_record * list B :=
  let '(s', fas) :=
    List.fold_left
      (fun '(s, ys) x =>
        let '(s', y) := f s x in
        (s', cons y ys))
        xs
        (s, nil) in
  (s', List.rev fas).

Inductive externval : Type :=
| ev_func : funaddr -> externval
| ev_table : tableaddr -> externval
| ev_mem : memaddr -> externval
| ev_global : globaladdr -> externval.

Definition funcs_of_externals (evs : list externval) : list addr :=
  seq.pmap (fun ev => match ev with | ev_func fa => Some fa | _ => None end) evs.

Definition tables_of_externals (evs : list externval) : list addr :=
  seq.pmap (fun ev => match ev with | ev_table ta => Some ta | _ => None end) evs.

Definition mems_of_externals (evs : list externval) : list addr :=
  seq.pmap (fun ev => match ev with | ev_mem ta => Some ta | _ => None end) evs.

Definition globals_of_externals (evs : list externval) : list addr :=
  seq.pmap (fun ev => match ev with | ev_global ta => Some ta | _ => None end) evs.

Definition add_func (s : store_record) funcinst := {|
  s_funcs := List.app s.(s_funcs) (cons funcinst nil);
  s_tables := s.(s_tables);
  s_mems := s.(s_mems);
  s_globals := s.(s_globals);
|}.

Definition alloc_func (s : store_record) (m_f : module_func) (mi : instance) : store_record * funcidx :=
  let funcaddr := List.length s.(s_funcs) in
  let functype := List.nth (match m_f.(mf_type) with | Mk_typeidx n => n end) mi.(i_types) (Tf nil nil (* TODO: partiality problem *) ) in
  let funcinst := Func_native mi functype m_f.(mf_locals) m_f.(mf_body) in
  let S' := add_func s funcinst in
  (S', Mk_funcidx funcaddr).

Definition alloc_funcs (s : store_record) (m_fs : list module_func) (mi : instance) : store_record * list funcidx :=
  alloc_Xs (fun s m_f => alloc_func s m_f mi) s m_fs.

Definition add_table (s : store_record) (ti : tableinst) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := List.app s.(s_tables) (cons ti nil);
  s_mems := s.(s_mems);
  s_globals := s.(s_globals);
|}.

Definition alloc_tab (s : store_record) (tty : table_type) : store_record * tableidx :=
  let '{| tt_limits := {| lim_min := min; lim_max := maxo |} as lim; tt_elem_type := ety |} := tty in
  let tableaddr := Mk_tableidx (List.length s.(s_tables)) in
  let tableinst := {| table_data := (List.repeat None min); table_max_opt := maxo; |} in
  (add_table s tableinst, tableaddr).

Definition alloc_tabs (s : store_record) (ts : list table_type) : store_record * list tableidx :=
  alloc_Xs alloc_tab s ts.

Definition ki64 : nat := 65536.

Definition mem_mk (lim : limits) : memory :=
  Build_memory (bytes_replicate (lim.(lim_min) * ki64) #00) lim.

Definition add_mem (s : store_record) (m_m : memory) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := List.app s.(s_mems) (cons m_m nil);
  s_globals := s.(s_globals);
|}.

Definition alloc_mem (s : store_record) (m_m : mem_type) : store_record * memidx :=
  let 'Mk_mem_type lims := m_m in
  let '{| lim_min := min; lim_max := maxo |} := lims in
  let memaddr := Mk_memidx (List.length s.(s_mems)) in
  let meminst := mem_mk lims in
  (add_mem s meminst, memaddr).

Definition alloc_mems (s : store_record) (m_ms : list mem_type) : store_record * list memidx :=
  alloc_Xs alloc_mem s m_ms.

Definition add_glob (s : store_record) (m_g : global) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := s.(s_mems);
  s_globals := List.app s.(s_globals) (cons m_g nil);
|}.

Definition alloc_glob (s : store_record) (m_g_v : module_glob * value) : store_record * globalidx :=
  let '(m_g, v) := m_g_v in
  let globaddr := Mk_globalidx (List.length s.(s_globals)) in
  let globinst := Build_global m_g.(mg_type).(tg_mut) v in
  (add_glob s globinst, globaddr).

Definition alloc_globs s m_gs vs :=
  alloc_Xs alloc_glob s (List.combine m_gs vs).

(* TODO: lemmas *)

Definition v_ext := module_export_desc.

Definition export_get_v_ext (inst : instance) (exp : module_export_desc) : v_ext :=
  (* we circumvent partiality by providing 0 as a default *)
  match exp with
  | ED_func (Mk_funcidx i) => ED_func (Mk_funcidx (List.nth i inst.(i_funcs) 0))
  | ED_table (Mk_tableidx i) => ED_table (Mk_tableidx (List.nth i inst.(i_tab) 0))
  | ED_mem (Mk_memidx i) => ED_mem (Mk_memidx (List.nth i inst.(i_memory) 0))
  | ED_global (Mk_globalidx i) => ED_global (Mk_globalidx (List.nth i inst.(i_globs) 0))
  end.

Definition ext_funcs :=
  seq.pmap
    (fun x =>
      match x with
      | ED_func i => Some i
      | _ => None
      end).

Definition ext_tabs :=
  seq.pmap
    (fun x =>
      match x with
      | ED_table i => Some i
      | _ => None
      end).

Definition ext_mems :=
  seq.pmap
    (fun x =>
      match x with
      | ED_mem i => Some i
      | _ => None
      end).

Definition ext_globs :=
  seq.pmap
    (fun x =>
      match x with
      | ED_global i => Some i
      | _ => None
      end).

Definition ext_t_funcs :=
  seq.pmap
    (fun x =>
      match x with
      | ET_func tf => Some tf
      | _ => None
      end).

Definition ext_t_tabs :=
  seq.pmap
    (fun x =>
      match x with
      | ET_tab i => Some i
      | _ => None
      end).

Definition ext_t_mems :=
  seq.pmap
    (fun x =>
      match x with
      | ET_mem i => Some i
      | _ => None
      end).

Definition ext_t_globs :=
  seq.pmap
    (fun x =>
      match x with
      | ET_glob i => Some i
      | _ => None
      end).

Definition alloc_module (s : store_record) (m : module) (imps : list v_ext) (gvs : list value)
    (s'_inst_exps : store_record * instance * seq module_export) : bool :=
  let '(s, inst, exps) := s'_inst_exps in
  let '(s1, i_fs) := alloc_funcs s m.(mod_funcs) inst in
  let '(s2, i_ts) := alloc_tabs s1 (List.map (fun t => t.(t_type)) m.(mod_tables)) in
  let '(s3, i_ms) := alloc_mems s2 m.(mod_mems) in
  let '(s', i_gs) := alloc_globs s3 m.(mod_globals) gvs in
  (inst.(i_types) == m.(mod_types)) &&
  (inst.(i_funcs) == List.map (fun '(Mk_funcidx i) => i) (List.app (ext_funcs imps) i_fs)) &&
  (inst.(i_tab) == List.map (fun '(Mk_tableidx i) => i) (List.app (ext_tabs imps) i_ts)) &&
  (inst.(i_memory) == List.map (fun '(Mk_memidx i) => i) (List.app (ext_mems imps) i_ms)) &&
  (inst.(i_globs) == List.map (fun '(Mk_globalidx i) => i) (List.app (ext_globs imps) i_gs)) &&
  (exps == (List.map (fun m_exp => {| exp_name := m_exp.(exp_name); exp_desc := (export_get_v_ext inst m_exp.(exp_desc)) |}) m.(mod_exports) : seq module_export)).

Definition interp_alloc_module (s : store_record) (m : module) (imps : list v_ext) (gvs : list value) : (store_record * instance * list module_export) :=
  let i_fs := List.map (fun i => Mk_funcidx i) (seq.iota (List.length s.(s_funcs)) (List.length m.(mod_funcs))) in
  let i_ts := List.map (fun i => Mk_tableidx i) (seq.iota (List.length s.(s_tables)) (List.length m.(mod_tables))) in
  let i_ms := List.map (fun i => Mk_memidx i) (seq.iota (List.length s.(s_mems)) (List.length m.(mod_mems))) in
  let i_gs := List.map (fun i => Mk_globalidx i) (seq.iota (List.length s.(s_globals)) (min (List.length m.(mod_globals)) (List.length gvs))) in
  let inst := {|
    i_types := m.(mod_types);
    i_funcs := List.map (fun '(Mk_funcidx i) => i) (List.app (ext_funcs imps) i_fs);
    i_tab := List.map (fun '(Mk_tableidx i) => i) (List.app (ext_tabs imps) i_ts);
    i_memory := List.map (fun '(Mk_memidx i) => i) (List.app (ext_mems imps) i_ms);
    i_globs := List.map (fun '(Mk_globalidx i) => i) (List.app (ext_globs imps) i_gs);
  |} in
  let '(s1, _) := alloc_funcs s m.(mod_funcs) inst in
  let '(s2, _) := alloc_tabs s1 (List.map (fun t => t.(t_type)) m.(mod_tables)) in
  let '(s3, _) := alloc_mems s2 m.(mod_mems) in
  let '(s', _) := alloc_globs s3 m.(mod_globals) gvs in
  let exps := List.map (fun m_exp => {| exp_name := m_exp.(exp_name); exp_desc := export_get_v_ext inst m_exp.(exp_desc) |}) m.(mod_exports) in
  (s', inst, exps).

(* TODO: lemmas *)

Definition insert_at {A} (v : A) (n : nat) (l : list A) : list A :=
List.app (List.firstn n l) (List.app (cons v nil) (List.skipn (n + 1) l)).

Definition dummy_table := {| table_data := nil; table_max_opt := None; |}.

Definition init_tab (s : store_record) (inst : instance) (e_ind : nat) (e : module_element) : store_record :=
  let t_ind := List.nth (match e.(elem_table) with Mk_tableidx i => i end) inst.(i_tab) 0 in
  let '{|table_data := tab_e; table_max_opt := maxo |} := List.nth t_ind s.(s_tables) dummy_table in
  let e_pay := List.map (fun i => List.nth_error inst.(i_funcs) (match i with Mk_funcidx j => j end)) e.(elem_init) in
  let tab'_e := List.app (List.firstn e_ind tab_e) (List.app e_pay (List.skipn (e_ind + length e_pay) tab_e)) in
  {| s_funcs := s.(s_funcs);
     s_tables := insert_at {| table_data := tab'_e; table_max_opt := maxo |} e_ind s.(s_tables);
     s_mems := s.(s_mems);
     s_globals := s.(s_globals) |}.

Definition init_tabs (s : store_record) (inst : instance) (e_inds : list nat) (es : list module_element) : store_record :=
  List.fold_left (fun s' '(e_ind, e) => init_tab s' inst e_ind e) (List.combine e_inds es) s.

Definition dummy_mem := {| mem_data := nil; mem_limit := {| lim_min := 0; lim_max := None; |} |}.

Definition init_mem (s : store_record) (inst : instance) (d_ind : nat) (d : module_data) : store_record :=
  let m_ind := List.nth (match d.(dt_data) with Mk_memidx i => i end) inst.(i_memory) 0 in
  let mem := List.nth m_ind s.(s_mems) dummy_mem in
  let mem' := operations.write_bytes mem d_ind (List.map compcert_byte_of_byte d.(dt_init)) in
  {| s_funcs := s.(s_funcs);
     s_tables := s.(s_tables);
     s_mems := insert_at mem' m_ind s.(s_mems);
     s_globals := s.(s_globals); |}.

Definition init_mems (s : store_record) (inst : instance) (d_inds : list nat) (ds : list module_data) : store_record :=
  List.fold_left (fun s' '(d_ind, d) => init_mem s' inst d_ind d) (List.combine d_inds ds) s.

Definition module_func_typing (c : t_context) (m : module_func) (tf : function_type) : Prop :=
  let '{| mf_type := Mk_typeidx i; mf_locals := t_locs; mf_body := b_es |} := m in
  let '(Tf tn tm) := tf in
  i < List.length c.(tc_types_t) /\
  List.nth i c.(tc_types_t) (Tf nil nil) == tf /\
  let c' := {|
    tc_types_t := c.(tc_types_t);
    tc_func_t := c.(tc_func_t);
    tc_global := c.(tc_global);
    tc_table := c.(tc_table);
    tc_memory := c.(tc_memory);
    tc_local := c.(tc_local) ++ tn ++ t_locs;
    tc_label := cons tm c.(tc_label);
    tc_return := Some tm;
  |} in
  typing.be_typing c' b_es tf.

Definition limit_typing (lim : limits) (k : nat) : bool :=
  let '{| lim_min := min; lim_max := maxo |} := lim in
  (k <= expn_rec 2 32) &&
  (match maxo with None => true | Some max => max <= k end) &&
  (match maxo with None => true | Some max => min <= k end).

Definition module_tab_typing (t : module_table) : bool :=
  limit_typing t.(t_type).(tt_limits) (expn_rec 2 32).

Definition module_mem_typing (m : mem_type) : bool :=
  let '(Mk_mem_type lim) := m in
  limit_typing lim (expn_rec 2 32).

Definition const_expr (c : t_context) (b_e : basic_instruction) : bool :=
  match b_e with
  | EConst _ => true
  | Get_global k =>
    (k < length c.(tc_global)) &&
    match List.nth_error c.(tc_global) k with
    | None => false
    | Some t => t.(tg_mut) == MUT_immut
    end
  | _ => false
  end.

Definition const_exprs (c : t_context) (es : list basic_instruction) : bool :=
  seq.all (const_expr c) es.

Definition module_glob_typing (c : t_context) (g : module_glob) (tg : global_type) : Prop :=
  let '{| mg_type := tg'; mg_init := es |} := g in
  const_exprs c es /\
  typing.be_typing c es (Tf nil (cons tg.(tg_t) nil)).

Definition module_elem_typing (c : t_context) (e : module_element) : Prop :=
  let '{| elem_table := Mk_tableidx t; elem_offset := es; elem_init := is_ |} := e in
  const_exprs c es /\
  typing.be_typing c es (Tf nil (cons T_i32 nil)) /\
  t < List.length c.(tc_table) /\
  seq.all (fun '(Mk_funcidx i) => i < List.length c.(tc_func_t)) is_.

Definition module_data_typing (c : t_context) (m_d : module_data) : Prop :=
  let '{| dt_data := Mk_memidx d; dt_offset := es; dt_init := bs |} := m_d in
  const_exprs c es /\
  typing.be_typing c es (Tf nil (cons T_i32 nil)) /\
  d < List.length c.(tc_memory).

Definition module_start_typing (c : t_context) (ms : module_start) : bool :=
  let '(Mk_funcidx i) := ms.(start_func) in
  (i < length c.(tc_func_t)) &&
  match List.nth_error c.(tc_func_t) i with
  | None => false
  | Some tf => tf == (Tf nil nil)
  end.

Definition module_import_typing (c : t_context) (d : import_desc) (e : extern_t) : bool :=
  match (d, e) with
  | (ID_func i, ET_func tf) =>
    (i < List.length c.(tc_types_t)) &&
    match List.nth_error c.(tc_types_t) i with
    | None => false
    | Some tf' => tf == tf'
    end
  | (ID_table t_t, ET_tab t_t') =>
    (t_t == t_t') && module_tab_typing {| t_type := t_t |}
  | (ID_mem mt, ET_mem mt') =>
    (mt == mt') && module_mem_typing mt
  | (ID_global gt, ET_glob gt') => gt == gt'
  | _ => false
  end.

Definition module_export_typing (c : t_context) (d : module_export_desc) (e : extern_t) : bool :=
  match (d, e) with
  | (ED_func (Mk_funcidx i), ET_func tf) =>
    (i < List.length c.(tc_func_t)) &&
    match List.nth_error c.(tc_func_t) i with
    | None => false
    | Some tf' => tf == tf'
    end
  | (ED_table (Mk_tableidx i), ET_tab t_t) =>
    (i < List.length c.(tc_table)) &&
    match List.nth_error c.(tc_table) i with
    | None => false
    | Some t_t' => t_t == t_t'
    end
  | (ED_mem (Mk_memidx i), ET_mem (Mk_mem_type lim)) =>
    (i < List.length c.(tc_memory)) &&
    match List.nth_error c.(tc_memory) i with
    | None => false
    | Some lim' => lim == lim' (* TODO: should check for equality of `mem_type`s *)
    end
  | (ED_global (Mk_globalidx i), ET_glob gt) =>
    (i < List.length c.(tc_global)) &&
    match List.nth_error c.(tc_global) i with
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

Definition module_typing (m : module) (impts : list extern_t) (expts : list extern_t) : Prop :=
  exists fts gts,
  let '{| 
    mod_types := tfs;
    mod_funcs := fs;
    mod_tables := ts;
    mod_mems := ms;
    mod_globals := gs;
    mod_elem := els;
    mod_data := ds;
    mod_start := i_opt;
    mod_imports := imps;
    mod_exports := exps;
  |} := m in
  let ifts := ext_t_funcs impts in
  let its := ext_t_tabs impts in
  let ims := ext_t_mems impts in
  let igs := ext_t_globs impts in
  let c := {|
    tc_types_t := tfs;
    tc_func_t := List.app ifts fts;
    tc_global := List.app igs gts;
    tc_table := List.app its (List.map (fun t => t.(t_type)) ts);
    tc_memory := List.map (fun '(Mk_mem_type lim) => lim) (List.app ims ms); (* TODO: should use `mem_type`s *)
    tc_local := nil;
    tc_label := nil;
    tc_return := None;
  |} in
  let c' := {|
    tc_types_t := nil;
    tc_func_t := nil;
    tc_global := igs;
    tc_table := nil;
    tc_memory := nil;
    tc_local := nil;
    tc_label := nil;
    tc_return := None;
  |} in
  List.Forall2 (module_func_typing c) fs fts /\
  seq.all module_tab_typing ts /\
  seq.all module_mem_typing ms /\
  List.Forall2 (module_glob_typing c') gs gts /\
  List.Forall (module_elem_typing c) els /\
  List.Forall (module_data_typing c) ds /\
  pred_option (module_start_typing c) i_opt /\
  List.Forall2 (fun imp => module_import_typing c imp.(imp_desc)) imps impts /\
  List.Forall2 (fun exp => module_export_typing c exp.(exp_desc)) exps expts.

Inductive external_typing : store_record -> v_ext -> extern_t -> Prop :=
| ETY_func :
  forall (s : store_record) (i : nat) cl (tf : function_type),
  i < List.length s.(s_funcs) ->
  List.nth_error s.(s_funcs) i = Some cl ->
  tf = operations.cl_type cl ->
  external_typing s (ED_func (Mk_funcidx i)) (ET_func tf)
| ETY_tab :
  forall (s : store_record) (i : nat) (ti : tableinst) lim,
  i < List.length s.(s_tables) ->
  List.nth_error s.(s_tables) i = Some ti ->
  typing.tab_typing ti lim ->
  external_typing s (ED_table (Mk_tableidx i)) (ET_tab {| tt_limits := lim; tt_elem_type := ELT_funcref |})
| ETY_mem :
  forall (s : store_record) (i : nat) (m : memory) (mt : mem_type),
  i < List.length s.(s_mems) ->
  List.nth_error s.(s_mems) i = Some m ->
  typing.mem_typing m mt ->
  external_typing s (ED_mem (Mk_memidx i)) (ET_mem mt)
| ETY_glob :
  forall (s : store_record) (i : nat) (g : global) (gt : global_type),
  i < List.length s.(s_globals) ->
  List.nth_error s.(s_globals) i = Some g ->
  typing.global_agree g gt ->
  external_typing s (ED_global (Mk_globalidx i)) (ET_glob gt).

Definition instantiate_globals inst (hs' : host_state) (s' : store_record) m g_inits : Prop :=
  List.Forall2 (fun g v =>
      opsem.reduce_trans inst (hs', s', nil, operations.to_e_list g.(mg_init))
                              (hs', s', nil, cons (Basic (EConst v)) nil))
    m.(mod_globals) g_inits.

Definition instantiate_elem inst (hs' : host_state) (s' : store_record) m e_offs : Prop :=
  List.Forall2 (fun e c =>
      opsem.reduce_trans inst (hs', s', nil, operations.to_e_list e.(elem_offset))
                              (hs', s', nil, cons (Basic (EConst (ConstInt32 c))) nil))
    m.(mod_elem)
    e_offs.

Definition instantiate_data inst (hs' : host_state) (s' : store_record) m d_offs : Prop :=
  List.Forall2 (fun d c =>
      opsem.reduce_trans inst (hs', s', nil, operations.to_e_list d.(dt_offset))
                              (hs', s', nil, cons (Basic (EConst (ConstInt32 c))) nil))
    m.(mod_data)
    d_offs.

Definition nat_of_int (i : i32) : nat :=
  BinInt.Z.to_nat i.(Wasm_int.Int32.intval).

Definition check_bounds_elem (inst : instance) (s : store_record) (m : module) (e_offs : seq i32) : bool :=
  seq.all2
    (fun e_off e =>
      match List.nth_error inst.(i_tab) (match e.(elem_table) with Mk_tableidx i => i end) with
      | None => false
      | Some i =>
        match List.nth_error s.(s_tables) i with
        | None => false
        | Some ti =>
          nat_of_int e_off + List.length e.(elem_init) <= List.length ti.(table_data)
        end
      end)
      e_offs
      m.(mod_elem).

Definition mem_length (m : memory) :=
  List.length m.(mem_data).

Definition check_bounds_data (inst : instance) (s : store_record) (m : module) (d_offs : seq i32) : bool :=
  seq.all2
    (fun d_off d =>
      match List.nth_error inst.(i_memory) (match d.(dt_data) with Mk_memidx i => i end) with
      | None => false
      | Some i =>
        match List.nth_error s.(s_mems) i with
        | None => false
        | Some mem =>
          nat_of_int d_off + List.length d.(dt_init) <= mem_length mem
        end
      end)
      d_offs
      m.(mod_data).

Definition check_start m inst start : bool :=
  let start' :=
    operations.option_bind
    (fun i_s =>
      List.nth_error inst.(i_funcs) (match i_s.(start_func) with Mk_funcidx i => i end))
    m.(mod_start) in
  start' == start.

Definition instantiate (* FIXME: Do we need to use this: [(hs : host_state)] ? *)
                       (s : store_record) (m : module) (v_imps : list v_ext)
                       (z : (store_record * instance * list module_export) * option nat) : Prop :=
  let '((s_end, inst, v_exps), start) := z in
  exists t_imps t_exps hs' s' g_inits e_offs d_offs,
    module_typing m t_imps t_exps /\
    List.Forall2 (external_typing s) v_imps t_imps /\
    alloc_module s m v_imps g_inits (s', inst, v_exps) /\
    instantiate_globals inst hs' s' m g_inits /\
    instantiate_elem inst hs' s' m e_offs /\
    instantiate_data inst hs' s' m d_offs /\
    check_bounds_elem inst s m e_offs /\
    check_bounds_data inst s m e_offs /\
    check_start m inst start /\
    let s'' := init_tabs s' inst (map (fun o => BinInt.Z.to_nat o.(Wasm_int.Int32.intval)) e_offs) m.(mod_elem) in
    (s_end : store_record_eqType)
      == init_mems s'' inst (map (fun o => BinInt.Z.to_nat o.(Wasm_int.Int32.intval)) d_offs) m.(mod_data).

Definition gather_m_f_type (tfs : list function_type) (m_f : module_func) : option function_type :=
  let '(Mk_typeidx i) := m_f.(mf_type) in
  if i < List.length tfs then List.nth_error tfs i
  else None.

Definition gather_m_f_types (tfs : list function_type) (m_fs : list module_func) : option (list function_type) :=
  list_extra.those (List.map (gather_m_f_type tfs) m_fs).

Definition module_import_typer (tfs : list function_type) (imp : import_desc) : option extern_t :=
  match imp with
  | ID_func i =>
    if i < List.length tfs then
      match List.nth_error tfs i with
      | None => None
      | Some ft => Some (ET_func ft)
      end
    else None
  | ID_table t_t =>
    if module_tab_typing {| t_type := t_t |} then Some (ET_tab t_t) else None
  | ID_mem mt =>
    if module_mem_typing mt then Some (ET_mem mt) else None
  | ID_global gt => Some (ET_glob gt)
  end.

Definition module_imports_typer (tfs : list function_type) (imps : list module_import) : option (list extern_t) :=
  those (List.map (fun imp => module_import_typer tfs imp.(imp_desc)) imps).

Definition module_export_typer (c : t_context) (exp : module_export_desc) : option extern_t :=
  match exp with
  | ED_func (Mk_funcidx i) =>
    if i < List.length c.(tc_func_t) then
      match List.nth_error c.(tc_func_t) i with
      | None => None
      | Some ft => Some (ET_func ft)
      end
    else None
  | ED_table (Mk_tableidx i) =>
    if i < List.length c.(tc_table) then
      match List.nth_error c.(tc_table) i with
      | None => None
      | Some t_t => Some (ET_tab t_t)
      end
    else None
  | ED_mem (Mk_memidx i) =>
    if i < List.length c.(tc_memory) then
      match List.nth_error c.(tc_memory) i with
      | None => None
      | Some lim => Some (ET_mem (Mk_mem_type lim))
      end
    else None
  | ED_global (Mk_globalidx i) =>
    if i < List.length c.(tc_global) then
      match List.nth_error c.(tc_global) i with
      | None => None
      | Some g => Some (ET_glob g)
      end
    else None
  end.

Definition module_exports_typer (c : t_context) exps :=
  those (List.map (fun exp => module_export_typer c exp.(exp_desc)) exps).

Definition gather_m_g_types (mgs : list module_glob) : list global_type :=
  List.map (fun mg => mg.(mg_type)) mgs.

Definition module_func_type_checker (c : t_context) (m : module_func) : bool :=
  let '{| mf_type := Mk_typeidx i; mf_locals := t_locs; mf_body := b_es |} := m in
  (i < List.length c.(tc_types_t)) &&
  match List.nth_error c.(tc_types_t) i with
  | None => false
  | Some (Tf tn tm) =>
    let c' := {|
      tc_types_t := c.(tc_types_t);
      tc_func_t := c.(tc_func_t);
      tc_global := c.(tc_global);
      tc_table := c.(tc_table);
      tc_memory := c.(tc_memory);
      tc_local := List.app c.(tc_local) (List.app tn t_locs);
      tc_label := cons tm c.(tc_label);
      tc_return := Some tm;
    |} in
    type_checker.b_e_type_checker c' b_es (Tf tn tm)
  end.

Definition module_tab_type_checker := module_tab_typing.
Definition module_mem_type_checker := module_mem_typing.

Definition module_glob_type_checker (c : t_context) (mg : module_glob) : bool :=
  let '{| mg_type := tg; mg_init := es |} := mg in
  const_exprs c es &&
  type_checker.b_e_type_checker c es (Tf nil (cons tg.(tg_t) nil)).

Definition module_elem_type_checker (c : t_context) (e : module_element) : bool :=
  let '{| elem_table := Mk_tableidx t; elem_offset := es; elem_init := is_ |} := e in
  const_exprs c es &&
  type_checker.b_e_type_checker c es (Tf nil (cons T_i32 nil)) &&
  (t < List.length c.(tc_table)) &&
  seq.all (fun '(Mk_funcidx i) => i < List.length c.(tc_func_t)) is_.

Definition module_data_type_checker (c : t_context) (d : module_data) : bool :=
  let '{| dt_data := Mk_memidx d; dt_offset := es; dt_init := bs |} := d in
  const_exprs c es &&
  type_checker.b_e_type_checker c es (Tf nil (cons T_i32 nil)) &&
  (d < List.length c.(tc_memory)).

Definition module_start_type_checker (c : t_context) (ms : module_start) : bool :=
  module_start_typing c ms.

Definition module_type_checker (m : module) : option ((list extern_t) * (list extern_t)) :=
  let '{|
    mod_types := tfs;
    mod_funcs := fs;
    mod_tables := ts;
    mod_mems := ms;
    mod_globals := gs;
    mod_elem := els;
    mod_data := ds;
    mod_start := i_opt;
    mod_imports := imps;
    mod_exports := exps;
    |} := m in
  match (gather_m_f_types tfs fs, module_imports_typer tfs imps) with
  | (Some fts, Some impts) =>
    let ifts := ext_t_funcs impts in
    let its := ext_t_tabs impts in
    let ims := ext_t_mems impts in
    let igs := ext_t_globs impts in
    let gts := gather_m_g_types gs in
    let c := {|
      tc_types_t := tfs;
      tc_func_t := List.app ifts fts;
      tc_global := List.app igs gts;
      tc_table := List.app its (List.map (fun t => t.(t_type)) ts);
      tc_memory := List.map (fun '(Mk_mem_type lim) => lim) (List.app ims ms);
      tc_local := nil;
      tc_label := nil;
      tc_return := None |} in
    let c' := {|
      tc_types_t := nil;
      tc_func_t := nil;
      tc_global := igs;
      tc_table := nil;
      tc_memory := nil;
      tc_local := nil;
      tc_label := nil;
      tc_return := None
    |} in
    if seq.all (module_func_type_checker c) fs &&
       seq.all module_tab_type_checker ts &&
       seq.all module_mem_type_checker ms &&
       seq.all (module_glob_type_checker c') gs &&
       seq.all (module_elem_type_checker c) els &&
       seq.all (module_data_type_checker c) ds &&
       pred_option (module_start_type_checker c) i_opt then
       match module_exports_typer c exps with
       | Some expts => Some (impts, expts)
       | None => None
       end
    else None
  | (Some _, None) | (None, Some _) | (None, None) => None
  end.

Definition external_type_checker (s : store_record) (v : v_ext) (e : extern_t) : bool :=
  match (v, e) with
  | (ED_func (Mk_funcidx i), ET_func tf) =>
    (i < List.length s.(s_funcs)) &&
    match List.nth_error s.(s_funcs) i with
    | None => false
    | Some cl => tf == operations.cl_type cl
    end
  | (ED_table (Mk_tableidx i), ET_tab tf) =>
    let '{| tt_limits := lim; tt_elem_type := elem_type_tt |} := tf in
    (i < List.length s.(s_tables)) &&
    match List.nth_error s.(s_tables) i with
    | None => false
    | Some ti => typing.tab_typing ti lim
    end
  | (ED_mem (Mk_memidx i), ET_mem mt) =>
    (i < List.length s.(s_mems)) &&
    match List.nth_error s.(s_mems) i with
    | None => false
    | Some m => typing.mem_typing m mt
    end
  | (ED_global (Mk_globalidx i), ET_glob gt) =>
    (i < List.length s.(s_globals)) &&
    match List.nth_error s.(s_globals) i with
    | None => false
    | Some g => typing.global_agree g gt
    end
  | (_, _) => false
  end.

Import ITree ITreeFacts.

Import Monads.
Import MonadNotation.

(** The following type is returned as an event when the instantiation failed. **)
Inductive instantiation_error (T : Type) : Type :=
  | Instantiation_error : instantiation_error T.

Arguments Instantiation_error {T}.

Definition interp_get_v (s : store_record) (inst : instance) (b_es : list basic_instruction)
  : itree (instantiation_error +' eff) value (* FIXME: isa mismatch *) :=
  res <- burn 2 (run_v 0 inst (s, nil, operations.to_e_list b_es)) ;;
  match res with
  | (_, interpreter.R_value vs) =>
    match vs with
    | v :: nil => ret v
    | _ => trigger_inl1 Instantiation_error
    end
  | _ => trigger_inl1 Instantiation_error
  end.

Definition interp_get_i32 (s : store_record) (inst : instance) (b_es : list basic_instruction)
  : itree (instantiation_error +' eff) i32 (* FIXME: isa mismatch *) :=
  v <- interp_get_v s inst b_es ;;
  match v with
  | ConstInt32 c => ret c
  | _ => trigger_inl1 Instantiation_error
  end.

Definition interp_instantiate (s : store_record) (m : module) (v_imps : list v_ext)
  : itree (instantiation_error +' eff) ((store_record * instance * list module_export) * option nat) :=
  match module_type_checker m with
  | None => trigger_inl1 Instantiation_error
  | Some (t_imps, t_exps) =>
    if seq.all2 (external_type_checker s) v_imps t_imps then
      let inst_c := {|
            i_types := nil;
            i_funcs := nil;
            i_tab := nil;
            i_memory := nil;
            i_globs := List.map (fun '(Mk_globalidx i) => i) (ext_globs v_imps);
          |} in
      g_inits <- bind_list (fun g => interp_get_v s inst_c g.(mg_init)) m.(mod_globals) ;;
      let '(s', inst, v_exps) := interp_alloc_module s m v_imps g_inits in
      e_offs <- bind_list (fun e => interp_get_i32 s' inst e.(elem_offset)) m.(mod_elem) ;;
      d_offs <- bind_list (fun d => interp_get_i32 s' inst d.(dt_offset)) m.(mod_data) ;;
      if check_bounds_elem inst s m e_offs &&
         check_bounds_data inst s m d_offs then
        let start : option nat := operations.option_bind (fun i_s => List.nth_error inst.(i_funcs) (match i_s.(start_func) with Mk_funcidx i => i end)) m.(mod_start) in
        let s'' := init_tabs s' inst (List.map nat_of_int e_offs) m.(mod_elem) in
        let s_end := init_mems s' inst (List.map nat_of_int d_offs) m.(mod_data) in
        ret ((s_end, inst, v_exps), start)
      else trigger_inl1 Instantiation_error
    else trigger_inl1 Instantiation_error
  end.

Lemma interp_instantiate_imp_instantiate :
  forall s m v_imps s_end inst v_exps start,
  interp_instantiate s m v_imps ≈ ret ((s_end, inst, v_exps), start) ->
  instantiate s m v_imps ((s_end, inst, v_exps), start).
Proof.
Admitted. (* TODO *)

Definition empty_store_record : store_record := {|
    s_funcs := nil;
    s_tables := nil;
    s_mems := nil;
    s_globals := nil;
  |}.

Definition interp_instantiate_wrapper (m : module)
  : itree _ ((store_record * instance * list module_export) * option nat) :=
  interp_instantiate empty_store_record m nil.

Definition lookup_exported_function (n : name) (store_inst_exps : store_record * instance * list module_export)
    : option (config_tuple host_function) :=
  let '(s, inst, exps) := store_inst_exps in
  List.fold_left
    (fun acc e =>
      match acc with
      | Some cfg => Some cfg
      | None =>
        if e.(exp_name) == n then
          match e.(exp_desc) with
          | ED_func (Mk_funcidx fi) =>
            match List.nth_error s.(s_funcs) fi with
            | None => None
            | Some fc => Some (s, nil, cons (Invoke fc) nil)
            end
          | _ => None
          end
        else None
      end)
    exps
    None.

End Host.
