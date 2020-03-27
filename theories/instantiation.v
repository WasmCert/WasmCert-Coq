(* TODO: work in progress; let's wait for Conrad to finish his analysis of it *)
Require Import datatypes.
Require binary_format_parser.

(*

Definition addr := nat.
Definition funaddr := addr.
Definition tableaddr := addr.
Definition memaddr := addr.
Definition globaladdr := addr.

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

Definition allocfunc (S_ : store_record) (f : func2) (mi : instance) : store_record * nat :=
  let funcaddr := List.length S_.(s_funcs) in
  let functype := List.nth (match f.(fc2_type) with | Mk_typeidx n => n end) mi.(i_types) (Tf nil nil) in (* TODO: partiality problem *)
  let funcinst := Func_native mi functype nil (* TODO: ? *) f.(fc2_body) in
  let S' := add_func S_ funcinst in
  (S', funcaddr).

Definition allocfuncs (S_ : store_record) (fs : list func2) (mi : instance) : store_record * list nat :=
  let '(S', fas) := List.fold_left (fun acc f => match acc with | (S_, fas) => let '(S', fa) := allocfunc S_ f mi in (S', cons fa fas) end) fs (S_, nil) in
  (S', List.rev fas).

Definition add_table S_ ti :=
  Build_store_record S_.(s_funcs) (List.app S_.(s_tab) (cons ti nil)) S_.(s_memory) S_.(s_globs).

Definition alloctable (S_ : store_record) (tty : table_type) : store_record * nat :=
  match tty with
  | Mk_table_type (Mk_limits min maxo) ety =>
    let tableaddr := List.length S_.(s_tab) in
    let tableinst := Build_tabinst (List.repeat None min) maxo (* TODO: is this what the spec says? *) in
    (add_table S_ tableinst, tableaddr)
  end.

Definition alloctables (S_ : store_record) (ts : list table_type) : store_record * list nat :=
  let '(S', tas) := List.fold_left (fun acc t => match acc with | (S_, tas) => let '(S', ta) := alloctable S_ t in (S', cons ta tas) end) ts (S_, nil) in
  (S', List.rev tas).
  *)

  (*
Definition allocmem (S_ : wasm.store_record) (m : binary.mem) : wasm.store_record * nat :=
  match m with
  | Mk_mem (Mk_limits min maxo) =>
    let memaddr := List.length S_.(wasm.s_mem) in
    let meminst :=  
  end.

Definition allocmems (S_ : wasm.store_record) (ms : list binary.mem) : wasm.store_record * list nat :=
  let '(S', mas) := List.fold_left (fun acc m => match acc with | (S_, mas) => let '(S', ma) := allocmem S_ m in (S', cons ma mas) end) ms (S_, nil) in
  (S', List.rev mas).

Definition allocate_module (S : wasm.store_record) (m : binary.module) (evs : list externval) (vals : list wasm.value) : wasm.store_record * wasm.instance :=
  let moduleinst :=
    wasm.Build_instance
        m.(binary.mod_types) in
  let '(S1, funcaddrs) := allocfuncs S m.(binary.mod_funcs) moduleinst in
  let '(S2, tableaddrs) := alloctables S1 (List.map (fun x => x.(binary.t_type)) m.(binary.mod_tables)) in
  let '(S3, memaddrs) := allocmems S2 (List.map (fun x => x.(binary.m_type)) m.(binary.mod_mems)) in
  (S', moduleinst)
        .
        *)