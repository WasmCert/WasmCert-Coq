From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
Require Import datatypes datatypes_properties.
Require binary_format_parser operations typing opsem.
(* TODO: separate algorithmic aspects from specification, incl. dependencies *)

(* TODO: get rid of old notation that doesn't follow standard *)

Definition addr := nat.
Definition funaddr := addr.
Definition tableaddr := addr.
Definition memaddr := addr.
Definition globaladdr := addr.

Definition alloc_Xs {A} f (s : store_record) (xs : list A) : store_record * list nat :=
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

Definition alloc_func (s : store_record) (m_f : module_func) (mi : instance) : store_record * nat :=
  let funcaddr := List.length s.(s_funcs) in
  let functype := List.nth (match m_f.(mf_type) with | Mk_typeidx n => n end) mi.(i_types) (Tf nil nil (* TODO: partiality problem *) ) in
  let funcinst := Func_native mi functype m_f.(mf_locals) m_f.(mf_body) in
  let S' := add_func s funcinst in
  (S', funcaddr).

Definition alloc_funcs (s : store_record) (m_fs : list module_func) (mi : instance) : store_record * list nat :=
  alloc_Xs (fun s m_f => alloc_func s m_f mi) s m_fs.

Definition add_table (s : store_record) (ti : tableinst) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := List.app s.(s_tables) (cons ti nil);
  s_mems := s.(s_mems);
  s_globals := s.(s_globals);
|}.

Definition alloc_tab (s : store_record) (tty : table_type) : store_record * nat :=
  let '{| tt_limits := {| lim_min := min; lim_max := maxo |} as lim; tt_elem_type := ety |} := tty in
  let tableaddr := List.length s.(s_tables) in
  let tableinst := {| table_data := (List.repeat None min); table_max_opt := maxo; |} in
  (add_table s tableinst, tableaddr).

Definition alloc_tabs (s : store_record) (ts : list table_type) : store_record * list nat :=
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

Definition alloc_mem (s : store_record) (m_m : mem_type) : store_record * nat :=
  let '{| lim_min := min; lim_max := maxo |} := m_m in
  let memaddr := List.length s.(s_mems) in
  let meminst := mem_mk m_m in
  (add_mem s meminst, memaddr).

Definition alloc_mems (s : store_record) (m_ms : list mem_type) : store_record * list nat :=
  alloc_Xs alloc_mem s m_ms.

Definition add_glob (s : store_record) (m_g : global) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := s.(s_mems);
  s_globals := List.app s.(s_globals) (cons m_g nil);
|}.

Definition alloc_glob (s : store_record) (m_g_v : module_glob * value) : store_record * nat :=
  let '(m_g, v) := m_g_v in
  let globaddr := List.length s.(s_globals) in
  let globinst := Build_global m_g.(mg_type).(tg_mut) v in
  (add_glob s globinst, globaddr).

Definition alloc_globs s m_gs vs :=
  alloc_Xs alloc_glob s (List.combine m_gs vs).

(* TODO: lemmas *)

Definition v_ext := module_export_desc.

Definition export_get_v_ext (inst : instance) (exp : module_export_desc) : v_ext :=
  (* we circumvent partiality by providing 0 as a default *)
  match exp with
  | ED_func i => ED_func (List.nth i inst.(i_funcs) 0)
  | ED_table i => ED_table (List.nth i inst.(i_tab) 0)
  | ED_mem i => ED_mem (List.nth i inst.(i_memory) 0)
  | ED_global i => ED_global (List.nth i inst.(i_globs) 0)
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

Definition alloc_module (s : store_record) (m : module) (imps : list v_ext) (gvs : list value) s'_inst_exps : bool :=
  let '(s, inst, exps) := s'_inst_exps in
  let '(s1, i_fs) := alloc_funcs s m.(mod_funcs) inst in
  let '(s2, i_ts) := alloc_tabs s1 (List.map (fun t => t.(t_type)) m.(mod_tables)) in
  let '(s3, i_ms) := alloc_mems s2 m.(mod_mems) in
  let '(s', i_gs) := alloc_globs s3 m.(mod_globals) gvs in
  (inst.(i_types) == m.(mod_types)) &&
  (inst.(i_funcs) == List.app (ext_funcs imps) i_fs) &&
  (inst.(i_tab) == List.app (ext_tabs imps) i_ts) &&
  (inst.(i_memory) == List.app (ext_mems imps) i_ms) &&
  (inst.(i_globs) == List.app (ext_globs imps) i_gs) &&
  (exps == List.map (fun m_exp => {| exp_name := m_exp.(exp_name); exp_desc := (export_get_v_ext inst m_exp.(exp_desc)) |}) m.(mod_exports)).

Definition interp_alloc_module (s : store_record) (m : module) (imps : list v_ext) (gvs : list value) : (store_record * instance * list module_export) :=
  let i_fs := seq.iota (List.length s.(s_funcs)) (List.length m.(mod_funcs)) in
  let i_ts := seq.iota (List.length s.(s_tables)) (List.length m.(mod_tables)) in
  let i_ms := seq.iota (List.length s.(s_mems)) (List.length m.(mod_mems)) in
  let i_gs := seq.iota (List.length s.(s_globals)) (min (List.length m.(mod_globals)) (List.length gvs)) in
  let inst := {|
    i_types := m.(mod_types);
    i_funcs := List.app (ext_funcs imps) i_fs;
    i_tab := List.app (ext_tabs imps) i_ts;
    i_memory := List.app (ext_mems imps) i_ms;
    i_globs := List.app (ext_globs imps) i_gs;
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
  let t_ind := List.nth e.(elem_table) inst.(i_tab) 0 in
  let '{|table_data := tab_e; table_max_opt := maxo |} := List.nth t_ind s.(s_tables) dummy_table in
  let e_pay := List.map (fun i => List.nth_error inst.(i_funcs) i) e.(elem_init) in
  let tab'_e := List.app (List.firstn e_ind tab_e) (List.app e_pay (List.skipn (e_ind + length e_pay) tab_e)) in
  {| s_funcs := s.(s_funcs);
     s_tables := insert_at {| table_data := tab'_e; table_max_opt := maxo |} e_ind s.(s_tables);
     s_mems := s.(s_mems);
     s_globals := s.(s_globals) |}.

Definition init_tabs (s : store_record) (inst : instance) (e_inds : list nat) (es : list module_element) : store_record :=
  List.fold_left (fun s' '(e_ind, e) => init_tab s' inst e_ind e) (List.combine e_inds es) s.

Definition compcert_byte_of_byte (b : Byte.byte) : byte :=
  (* TODO: this is not great *)
  encode (Byte.to_nat b).

Definition dummy_mem := {| mem_data := nil; mem_limit := {| lim_min := 0; lim_max := None; |} |}.

Definition init_mem (s : store_record) (inst : instance) (d_ind : nat) (d : module_data) : store_record :=
  let m_ind := List.nth d.(dt_data) inst.(i_memory) 0 in
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
  limit_typing m (expn_rec 2 32).

Definition const_expr (c : t_context) (b_e : basic_instruction) : bool :=
  match b_e with
  | EConst _ => true
  | Get_global k =>
    (k < length c.(tc_global)) &&
    match List.nth_error c.(tc_global) k with
    | None => false
    | Some t => t.(tg_mut) == T_immut
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
  let '{| elem_table := t; elem_offset := es; elem_init := is_ |} := e in
  const_exprs c es /\
  typing.be_typing c es (Tf nil (cons T_i32 nil)) /\
  t < List.length c.(tc_table) /\
  seq.all (fun i => i < List.length c.(tc_func_t)) is_.

Definition module_data_typing (c : t_context) (m_d : module_data) : Prop :=
  let '{| dt_data := d; dt_offset := es; dt_init := bs |} := m_d in
  const_exprs c es /\
  typing.be_typing c es (Tf nil (cons T_i32 nil)) /\
  d < List.length c.(tc_memory).

Definition module_start_typing (c : t_context) (i : nat) : bool :=
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
  | (ED_func i, ET_func tf) =>
    (i < List.length c.(tc_func_t)) &&
    match List.nth_error c.(tc_func_t) i with
    | None => false
    | Some tf' => tf == tf'
    end
  | (ED_table i, ET_tab t_t) =>
    (i < List.length c.(tc_table)) &&
    match List.nth_error c.(tc_table) i with
    | None => false
    | Some t_t' => t_t == t_t'
    end
  | (ED_mem i, ET_mem mt) =>
    (i < List.length c.(tc_memory)) &&
    match List.nth_error c.(tc_memory) i with
    | None => false
    | Some mt' => mt == mt'
    end
  | (ED_global i, ET_glob gt) =>
    (i < List.length c.(tc_global)) &&
    match List.nth_error c.(tc_global) i with
    | None => false
    | Some gt' => gt == gt'
    end
  | (_, _) => false
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
    tc_memory := List.app ims ms;
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
  match i_opt with None => true | Some i => module_start_typing c i.(start_func) end /\
  List.Forall2 (fun imp => module_import_typing c imp.(imp_desc)) imps impts /\
  List.Forall2 (fun exp => module_export_typing c exp.(exp_desc)) exps expts.

Inductive external_typing : store_record -> v_ext -> extern_t -> Prop :=
| ETY_func :
  forall (s : store_record) (i : nat) cl (tf : function_type),
  i < List.length s.(s_funcs) ->
  List.nth_error s.(s_funcs) i = Some cl ->
  tf = operations.cl_type cl ->
  external_typing s (ED_func i) (ET_func tf)
| ETY_tab :
  forall (s : store_record) (i : nat) (ti : tableinst) lim,
  i < List.length s.(s_tables) ->
  List.nth_error s.(s_tables) i = Some ti ->
  typing.tab_typing ti lim ->
  external_typing s (ED_table i) (ET_tab {| tt_limits := lim; tt_elem_type := elem_type_tt |})
| ETY_mem :
  forall (s : store_record) (i : nat) (m : memory) (mt : mem_type),
  i < List.length s.(s_mems) ->
  List.nth_error s.(s_mems) i = Some m ->
  typing.mem_typing m mt ->
  external_typing s (ED_mem i) (ET_mem mt)
| ETY_glob :
  forall (s : store_record) (i : nat) (g : global) (gt : global_type),
  i < List.length s.(s_globals) ->
  List.nth_error s.(s_globals) i = Some g ->
  typing.global_agree g gt ->
  external_typing s (ED_global i) (ET_glob gt).

Definition instantiate (s : store_record) (m : module) (v_imps : list v_ext) (z : (store_record * instance * list module_export) * option nat) : Prop :=
  let '((s_end, inst, v_exps), start) := z in
  exists t_imps t_exps s' g_inits,
  module_typing m t_imps t_exps /\
  List.Forall2 (external_typing s) v_imps t_imps /\
  alloc_module s m v_imps g_inits (s', inst, v_exps) /\
  List.Forall2 (fun g v => opsem.reduce_trans inst (s', nil, operations.to_e_list g.(mg_init) ) (s', nil, cons (Basic (EConst v)) nil)) m.(mod_globals) g_inits /\
  true (* TODO *).