From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
Require Import datatypes datatypes_properties.
Require binary_format_parser operations.

Definition addr := nat.
Definition funaddr := addr.
Definition tableaddr := addr.
Definition memaddr := addr.
Definition globaladdr := addr.

Definition alloc_Xs {A} f (S_ : store_record) (xs : list A) : store_record * list nat :=
  let '(S', fas) :=
    List.fold_left
      (fun '(S_, ys) x =>
        let '(S', y) := f S_ x in
        (S', cons y ys))
        xs
        (S_, nil) in
  (S', List.rev fas).

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

Definition add_func S_ funcinst :=
  Build_store_record (List.app S_.(s_funcs) (cons funcinst nil)) S_.(s_tab) S_.(s_memory) S_.(s_globs).

Definition alloc_func (S_ : store_record) (m_f : module_func) (mi : instance) : store_record * nat :=
  let funcaddr := List.length S_.(s_funcs) in
  let functype := List.nth (match m_f.(mf_type) with | Mk_typeidx n => n end) mi.(i_types) (Tf nil nil (* TODO: partiality problem *) ) in
  let funcinst := Func_native mi functype m_f.(mf_locals) m_f.(mf_body) in
  let S' := add_func S_ funcinst in
  (S', funcaddr).

Definition alloc_funcs (S_ : store_record) (m_fs : list module_func) (mi : instance) : store_record * list nat :=
  alloc_Xs (fun S_ m_f => alloc_func S_ m_f mi) S_ m_fs.

Definition add_table S_ ti :=
  Build_store_record S_.(s_funcs) (List.app S_.(s_tab) (cons ti nil)) S_.(s_memory) S_.(s_globs).

Definition alloc_tab (S_ : store_record) (tty : table_type) : store_record * nat :=
  let '{| tt_limits := {| lim_min := min; lim_max := maxo |} as lim; tt_elem_type := ety |} := tty in
  let tableaddr := List.length S_.(s_tab) in
  let tableinst := {| table_data := (List.repeat None min); table_limit := lim; |} in
  (add_table S_ tableinst, tableaddr).

Definition alloc_tabs (S_ : store_record) (ts : list table_type) : store_record * list nat :=
  alloc_Xs alloc_tab S_ ts.

Definition ki64 := 65536.

Definition mem_mk (lim : limits) : memory :=
  Build_memory (bytes_replicate (lim.(lim_min) * ki64) #00) lim.

Definition add_mem S_ m_m :=
  Build_store_record S_.(s_funcs) S_.(s_tab) (List.app S_.(s_memory) (cons m_m nil)) S_.(s_globs).

Definition alloc_mem (S_ : store_record) (m_m : mem_type) : store_record * nat :=
  let '{| lim_min := min; lim_max := maxo |} := m_m in
  let memaddr := List.length S_.(s_memory) in
  let meminst := mem_mk m_m in
  (add_mem S_ meminst, memaddr).

Definition alloc_mems (S_ : store_record) (m_ms : list mem_type) : store_record * list nat :=
  alloc_Xs alloc_mem S_ m_ms.

Definition add_glob S_ m_g :=
Build_store_record S_.(s_funcs) S_.(s_tab) S_.(s_memory) (List.app S_.(s_globs) (cons m_g nil)) .

Definition alloc_glob (S_ : store_record) (m_g_v : module_glob * value) : store_record * nat :=
  let '(m_g, v) := m_g_v in
  let globaddr := List.length S_.(s_globs) in
  let globinst := Build_global m_g.(mg_type).(tg_mut) v in
  (add_glob S_ globinst, globaddr).

Definition alloc_globs s m_gs vs :=
  alloc_Xs alloc_glob s (List.combine m_gs vs).

(* TODO: lemmas *)

Definition v_ext := export_desc.

Definition export_get_v_ext (inst : instance) (exp : export_desc) : v_ext :=
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

Definition interp_alloc_module (s : store_record) (m : module) (imps : list v_ext) (gvs : list value) : (store_record * instance * list export) :=
  let i_fs := seq.iota (List.length s.(s_funcs)) (List.length m.(mod_funcs)) in
  let i_ts := seq.iota (List.length s.(s_tab)) (List.length m.(mod_tables)) in
  let i_ms := seq.iota (List.length s.(s_memory)) (List.length m.(mod_mems)) in
  let i_gs := seq.iota (List.length s.(s_globs)) (min (List.length m.(mod_globals)) (List.length gvs)) in
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

Definition init_tab (s : store_record) (inst : instance) (e_ind : nat) (e : element) : store_record :=
  let t_ind := List.nth e.(elem_table) inst.(i_tab) 0 in
  let '{|table_data := tab_e; table_limit := lim |} :=
    (* TODO: mismatch *)
    let dummy := {| table_data := nil; table_limit := {| lim_min := 0; lim_max := None; |} |} in
    List.nth t_ind s.(s_tab) dummy in
  let e_pay := List.map (fun i => List.nth_error inst.(i_funcs) i) e.(elem_init) in
  let tab'_e := List.app (List.firstn e_ind tab_e) (List.app e_pay (List.skipn (e_ind + length e_pay) tab_e)) in
  {| s_funcs := s.(s_funcs);
     s_tab := insert_at {| table_data := tab'_e; table_limit := lim |} e_ind s.(s_tab);
     s_memory := s.(s_memory);
     s_globs := s.(s_globs) |}.

Definition init_tabs (s : store_record) (inst : instance) (e_inds : list nat) (es : list element) : store_record :=
  List.fold_left (fun s' '(e_ind, e) => init_tab s' inst e_ind e) (List.combine e_inds es) s.

Definition compcert_byte_of_byte (b : Byte.byte) : byte :=
  (* TODO: this is not great *)
  encode (Byte.to_nat b).

Definition init_mem (s : store_record) (inst : instance) (d_ind : nat) (d : data) : store_record :=
  let m_ind := List.nth d.(dt_data) inst.(i_memory) 0 in
  let mem :=
    let dummy_mem := {| mem_data := nil; mem_limit := {| lim_min := 0; lim_max := None; |} |} in
    List.nth m_ind s.(s_memory) dummy_mem in
  let mem' := operations.write_bytes mem d_ind (List.map compcert_byte_of_byte d.(dt_init)) in
  {| s_funcs := s.(s_funcs);
     s_tab := s.(s_tab);
     s_memory := insert_at mem' m_ind s.(s_memory);
     s_globs := s.(s_globs); |}.

Definition init_mems (s : store_record) (inst : instance) (d_inds : list nat) (ds : list data) : store_record :=
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
  be_typing c' b_es tf.


Definition module_typing (m : module) (impts : list extern_t) (expts : list extern_t) : Prop :=
  exists fts gts,
  let '{| 
    mod_types := tfs;
    mod_funcs := fs;
    mod_tables := ts;
    mod_mems := ms;
    mod_globals := gs;
    mod_elements := els;
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
    tc_table := List.app its ts;
    tc_memory := List.app ims ms;
    tc_local := nil;
    tc_label := nil;
    tc_return := None;
  |} in
  seq.all2 (module_func_typing c) fs fts &&
  true (* TODO*).

Definition instantiate (s : store_record) (m : module) (t_imps : list v_ext) (t_exps : (store_record * instance * list export) * option nat) : bool :=
  module_typing m t_imps t_exps &&
  seq.allb (external_typing c) v_imps t_imps &&
  ???.