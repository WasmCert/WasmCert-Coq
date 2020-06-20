(* TODO: work in progress; let's wait for Conrad to finish his analysis of it *)
Require Import datatypes.
Require binary_format_parser.

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

Definition allocfuncs (S_ : store_record) (m_fs : list module_func) (mi : instance) : store_record * list nat :=
  alloc_Xs (fun S_ m_f => alloc_func S_ m_f mi) S_ m_fs.

Definition add_table S_ ti :=
  Build_store_record S_.(s_funcs) (List.app S_.(s_tab) (cons ti nil)) S_.(s_memory) S_.(s_globs).

Definition alloc_tab (S_ : store_record) (tty : table_type) : store_record * nat :=
  match tty with
  | Mk_table_type (Mk_limits min maxo) ety =>
    let tableaddr := List.length S_.(s_tab) in
    let tableinst := Build_tabinst (List.repeat None min) maxo in
    (add_table S_ tableinst, tableaddr)
  end.

Definition alloc_tabs (S_ : store_record) (ts : list table_type) : store_record * list nat :=
  alloc_Xs alloc_tab S_ ts.

Definition ki64 := 65536.

Definition mem_mk (lim : limits) : memory :=
  Build_memory (bytes_replicate (lim.(lim_min) * ki64) #00) (lim.(lim_max)).

  Definition add_mem S_ m_m :=
  Build_store_record S_.(s_funcs)S_.(s_tab)  (List.app S_.(s_memory) (cons m_m nil)) S_.(s_globs).

Definition alloc_mem (S_ : store_record) (m_m : mem_type) : store_record * nat :=
  match m_m with
  | Mk_limits min maxo =>
    let memaddr := List.length S_.(s_memory) in
    let meminst := mem_mk m_m in
    (add_mem S_ meminst, memaddr)
  end.

Definition alloc_mems (S_ : store_record) (ms : list mem_type) : store_record * list nat :=
  alloc_Xs alloc_mem S_ ms.

  (*
Definition allocate_module (S_ : store_record) (m : module) (evs : list externval) (vals : list value) : store_record * instance :=
  let moduleinst :=
    wasm.Build_instance
        m.(binary.mod_types) in
  let '(S1, funcaddrs) := allocfuncs S m.(binary.mod_funcs) moduleinst in
  let '(S2, tableaddrs) := alloctables S1 (List.map (fun x => x.(binary.t_type)) m.(binary.mod_tables)) in
  let '(S3, memaddrs) := allocmems S2 (List.map (fun x => x.(binary.m_type)) m.(binary.mod_mems)) in
  (S', moduleinst)
        .
        *)