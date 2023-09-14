From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import opsem interpreter_func instantiation_spec.
From Coq Require Import BinNat.

Section Instantiation_func.

Import EmptyHost.
Import Interpreter_func_extract.

Let alloc_funcs := alloc_funcs host_function_eqType.
Let alloc_tabs := alloc_tabs host_function_eqType.
Let alloc_mems := alloc_mems host_function_eqType.
Let alloc_globs := alloc_globs host_function_eqType.
Let check_bounds_elem := check_bounds_elem host_function_eqType.
Let check_bounds_data := check_bounds_data host_function_eqType.
Let init_tabs := init_tabs host_function_eqType.
Let init_mems := init_mems host_function_eqType.

Let instantiate := instantiate host_function_eqType host_instance.
Let interp_alloc_module := interp_alloc_module host_function_eqType.

Let run_v := run_v tt.


Definition gather_m_f_type (tfs : list function_type) (m_f : module_func) : option function_type :=
  let '(Mk_typeidx i) := m_f.(modfunc_type) in
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
    if module_tab_typing {| modtab_type := t_t |} then Some (ET_tab t_t) else None
  | ID_mem mt =>
    if module_mem_typing mt then Some (ET_mem mt) else None
  | ID_global gt => Some (ET_glob gt)
  end.

Definition module_imports_typer (tfs : list function_type) (imps : list module_import) : option (list extern_t) :=
  those (List.map (fun imp => module_import_typer tfs imp.(imp_desc)) imps).

Definition module_export_typer (c : t_context) (exp : module_export_desc) : option extern_t :=
  match exp with
  | MED_func (Mk_funcidx i) =>
    if i < List.length c.(tc_func_t) then
      match List.nth_error c.(tc_func_t) i with
      | None => None
      | Some ft => Some (ET_func ft)
      end
    else None
  | MED_table (Mk_tableidx i) =>
    if i < List.length c.(tc_table) then
      match List.nth_error c.(tc_table) i with
      | None => None
      | Some t_t => Some (ET_tab t_t)
      end
    else None
  | MED_mem (Mk_memidx i) =>
    if i < List.length c.(tc_memory) then
      match List.nth_error c.(tc_memory) i with
      | None => None
      | Some lim => Some (ET_mem lim)
      end
    else None
  | MED_global (Mk_globalidx i) =>
    if i < List.length c.(tc_global) then
      match List.nth_error c.(tc_global) i with
      | None => None
      | Some g => Some (ET_glob g)
      end
    else None
  end.

Definition module_exports_typer (c : t_context) exps :=
  those (List.map (fun exp => module_export_typer c exp.(modexp_desc)) exps).

Definition gather_m_g_types (mgs : list module_glob) : list global_type :=
  List.map (fun mg => mg.(modglob_type)) mgs.

Definition module_func_type_checker (c : t_context) (m : module_func) : bool :=
  let '{| modfunc_type := Mk_typeidx i; modfunc_locals := t_locs; modfunc_body := b_es |} := m in
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
      tc_label := tm :: c.(tc_label);
      tc_return := Some tm;
    |} in
    type_checker.b_e_type_checker c' b_es (Tf [::] tm)
  end.

Definition module_tab_type_checker := module_tab_typing.
Definition module_memory_type_checker := module_mem_typing.

Definition module_glob_type_checker (c : t_context) (mg : module_glob) : bool :=
  let '{| modglob_type := tg; modglob_init := es |} := mg in
  const_exprs c es &&
  type_checker.b_e_type_checker c es (Tf nil [::tg.(tg_t)]).

Definition module_elem_type_checker (c : t_context) (e : module_element) : bool :=
  let '{| modelem_table := Mk_tableidx t; modelem_offset := es; modelem_init := is_ |} := e in
  const_exprs c es &&
  type_checker.b_e_type_checker c es (Tf nil [::T_i32]) &&
  (t < List.length c.(tc_table)) &&
  seq.all (fun '(Mk_funcidx i) => i < List.length c.(tc_func_t)) is_.

Definition module_data_type_checker (c : t_context) (d : module_data) : bool :=
  let '{| moddata_data := Mk_memidx d; moddata_offset := es; moddata_init := bs |} := d in
  const_exprs c es &&
  type_checker.b_e_type_checker c es (Tf nil [::T_i32]) &&
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
      tc_table := List.app its (List.map (fun t => t.(modtab_type)) ts);
      tc_memory := List.app ims ms;
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
       seq.all module_memory_type_checker ms &&
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
  | (MED_func (Mk_funcidx i), ET_func tf) =>
    (i < List.length s.(s_funcs)) &&
    match List.nth_error s.(s_funcs) i with
    | None => false
    | Some cl => tf == operations.cl_type cl
    end
  | (MED_table (Mk_tableidx i), ET_tab tf) =>
    (i < List.length s.(s_tables)) &&
    match List.nth_error s.(s_tables) i with
    | None => false
    | Some ti => typing.tab_typing ti tf
    end
  | (MED_mem (Mk_memidx i), ET_mem mt) =>
    (i < List.length s.(s_mems)) &&
    match List.nth_error s.(s_mems) i with
    | None => false
    | Some m => typing.mem_typing m mt
    end
  | (MED_global (Mk_globalidx i), ET_glob gt) =>
    (i < List.length s.(s_globals)) &&
    match List.nth_error s.(s_globals) i with
    | None => false
    | Some g => typing.global_agree g gt
    end
  | (_, _) => false
  end.

Definition interp_get_v (s : store_record) (inst : instance) (b_es : list basic_instruction) : option value :=
  match run_v s (Build_frame [::] inst) (operations.to_e_list b_es) 2 with
  | (_, interpreter_func.R_value vs) =>
    match vs with
    | [:: v] => Some v
    | _ => None
    end
  | _ => None
  end.

Definition interp_get_i32 (s : store_record) (inst : instance) (b_es : list basic_instruction) : option i32 :=
  match interp_get_v s inst b_es with
  | Some (VAL_int32 c) => Some c
  | _ => None
  end.

(* Executable version of instantiation for extraction adapted from Isabelle; unverified yet *)
Definition interp_instantiate (s : store_record) (m : module) (v_imps : list v_ext) : option ((store_record * instance * list module_export) * option nat) :=
  match module_type_checker m with
  | None => None
  | Some (t_imps, t_exps) =>
    if seq.all2 (external_type_checker s) v_imps t_imps then
      let g_inits_opt :=
        let c := {|
          inst_types := nil;
          inst_funcs := nil;
          inst_tab := nil;
          inst_memory := nil;
          inst_globs := List.map (fun '(Mk_globalidx i) => i) (ext_globs v_imps);
        |} in
        those (map (fun g => interp_get_v s c g.(modglob_init)) m.(mod_globals)) in
      match g_inits_opt with
      | None => None
      | Some g_inits =>
        let '(s', inst, v_exps) := interp_alloc_module s m v_imps g_inits in
        let e_offs_opt := those (map (fun e => interp_get_i32 s' inst e.(modelem_offset)) m.(mod_elem)) in
        match e_offs_opt with
        | None => None
        | Some e_offs =>
          let d_offs_opt := those (map (fun d => interp_get_i32 s' inst d.(moddata_offset)) m.(mod_data)) in
          match d_offs_opt with
          | None => None
          | Some d_offs =>
            if check_bounds_elem inst s' m e_offs &&
               check_bounds_data inst s' m d_offs then
              let start : option nat := operations.option_bind (fun i_s => List.nth_error inst.(inst_funcs) (match i_s.(modstart_func) with Mk_funcidx i => i end)) m.(mod_start) in
              let s'' := init_tabs s' inst (List.map nat_of_int e_offs) m.(mod_elem) in
              let s_end := init_mems s'' inst (List.map N_of_int d_offs) m.(mod_data) in
              Some ((s_end, inst, v_exps), start)
            else None
          end
        end
      end
    else None
  end.

Definition empty_store_record : store_record := {|
    s_funcs := nil;
    s_tables := nil;
    s_mems := nil;
    s_globals := nil;
  |}.

(* Add an empty host and provide an initial empty store *)
Definition interp_instantiate_wrapper (m : module) : option ((host_state * store_record * instance * list module_export) * option nat) :=
  match interp_instantiate empty_store_record m nil with
  | Some ((s, i, es), on) => Some ((tt, s, i, es), on)
  | None => None
  end.

Definition lookup_exported_function (n : name) (store_inst_exps : host_state * store_record * instance * list module_export)
    : option (host_state * store_record * frame * seq administrative_instruction) :=
  let '(hs, s, inst, exps) := store_inst_exps in
  List.fold_left
    (fun acc e =>
      match acc with
      | Some cfg => Some cfg
      | None =>
        if e.(modexp_name) == n then
          match e.(modexp_desc) with
          | MED_func (Mk_funcidx fi) =>
            match List.nth_error s.(s_funcs) fi with
            | None => None
            | Some fc => Some (hs, s, (Build_frame nil inst), [::AI_invoke fi])
            end
          | _ => None
          end
        else None
      end)
    exps
    None.

End Instantiation_func.

(** Extraction **)

Module Instantiation_func_extract.

Import EmptyHost.

Definition lookup_exported_function :
    name -> host_state * store_record * instance * seq module_export ->
    option (host_state * store_record * frame * seq administrative_instruction) :=
  lookup_exported_function.

Definition interp_instantiate_wrapper :
  module ->
  option (host_state * store_record * instance * seq module_export * option nat) :=
  interp_instantiate_wrapper.

End Instantiation_func_extract.
