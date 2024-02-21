(** Basic operations over Wasm datatypes **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Wasm Require Import common memory_list.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From compcert Require lib.Floats.
From Wasm Require Export datatypes_properties list_extra.
From Coq Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Placeholder for better array lookup in the future *)
Definition lookup_N {T: Type} (l: list T) (n: N) : option T :=
  List.nth_error l (N.to_nat n).

Definition empty_t_context := Build_t_context nil nil nil nil nil nil nil nil nil None nil.

(** read `len` bytes from `m` starting at `start_idx` *)
Definition read_bytes (m : meminst) (start_idx : N) (len : nat) : option bytes :=
  those
    (List.map
      (fun off =>
        let idx := N.add start_idx (N.of_nat off) in
        mem_lookup idx m.(meminst_data))
    (iota 0 len)).

(** write bytes `bs` to `m` starting at `start_idx` *)
Definition write_bytes (m : meminst) (start_idx : N) (bs : bytes) : option meminst :=
  let x :=
    list_extra.fold_lefti
      (fun off dat_o b =>
        match dat_o with
        | None => None
        | Some dat =>
          let idx := N.add start_idx (N.of_nat off) in
          mem_update idx b dat
        end)
      bs
      (Some m.(meminst_data)) in
  match x with
  | Some dat => Some {| meminst_data := dat; meminst_type := m.(meminst_type); |}
  | None => None
  end.

Definition page_size : N := 65536%N.

Definition page_limit : N := 65536%N.

Definition ml_valid (m: memory_list) : Prop :=
  N.modulo (memory_list.mem_length m) page_size = 0%N.

Definition mem_length (m : meminst) : N :=
  mem_length m.(meminst_data).

Definition mem_size (m : meminst) : N :=
  N.div (mem_length m) page_size.

(** Grow the memory a given number of pages.
  * @param len_delta: the number of pages to grow the memory by
  *)

Definition mem_grow (m : meminst) (len_delta : N) : option meminst :=
  let new_size := N.add (mem_size m) len_delta in
  let new_mem_data := mem_grow (N.mul len_delta page_size) m.(meminst_data) in
  if N.leb new_size mem_limit_bound then
  match m.(meminst_type).(lim_max) with
  | Some maxlim =>
    if N.leb new_size maxlim then
        Some {|
          meminst_data := new_mem_data;
          meminst_type := m.(meminst_type);
          |}
    else None
  | None =>
    Some {|
      meminst_data := new_mem_data;
      meminst_type := m.(meminst_type);
      |}
  end
  else None.

(* TODO: We crucially need documentation here. *)

Definition load (m : meminst) (n : N) (off : static_offset) (l : nat) : option bytes :=
  if N.leb (N.add n (N.add off (N.of_nat l))) (mem_length m)
  then read_bytes m (N.add n off) l
  else None.

Definition sign_extend (s : sx) (l : nat) (bs : bytes) : bytes :=
  (* TODO: implement sign extension *) bs.
(* TODO
  let: msb := msb (msbyte bytes) in
  let: byte := (match sx with sx_U => O | sx_S => if msb then -1 else 0) in
  bytes_takefill byte l bytes
*)

Definition load_packed (s : sx) (m : meminst) (n : N) (off : static_offset) (lp : nat) (l : nat) : option bytes :=
  option_map (sign_extend s l) (load m n off lp).

Definition store (m : meminst) (n : N) (off : static_offset) (bs : bytes) (l : nat) : option meminst :=
  if N.leb (n + off + N.of_nat l) (mem_length m)
  then write_bytes m (n + off) (bytes_takefill #00 l bs)
  else None.

Definition store_packed := store.

Definition wasm_deserialise (bs : bytes) (vt : number_type) : value_num :=
  match vt with
  | T_i32 => VAL_int32 (Wasm_int.Int32.repr (common.Memdata.decode_int bs))
  | T_i64 => VAL_int64 (Wasm_int.Int64.repr (common.Memdata.decode_int bs))
  | T_f32 => VAL_float32 (Floats.Float32.of_bits (Integers.Int.repr (common.Memdata.decode_int bs)))
  | T_f64 => VAL_float64 (Floats.Float.of_bits (Integers.Int64.repr (common.Memdata.decode_int bs)))
  end.


Definition typeof_num (v : value_num) : number_type :=
  match v with
  | VAL_int32 _ => T_i32
  | VAL_int64 _ => T_i64
  | VAL_float32 _ => T_f32
  | VAL_float64 _ => T_f64
  end.

Definition typeof_vec (v: value_vec) : vector_type :=
  match v with
  | VAL_vec128 _ => T_v128
  end.

Definition typeof_ref (v: value_ref) : reference_type :=
  match v with
  | VAL_ref_null vt => vt
  | VAL_ref_func _ => T_funcref
  | VAL_ref_extern _ => T_externref
  end.

Definition typeof (v: value) : value_type :=
  match v with
  | VAL_num v' => T_num (typeof_num v')
  | VAL_vec v' => T_vec (typeof_vec v')
  | VAL_ref v' => T_ref (typeof_ref v')
  end.
    


Definition option_projl (A B : Type) (x : option (A * B)) : option A :=
  option_map fst x.

Definition option_projr (A B : Type) (x : option (A * B)) : option B :=
  option_map snd x.

Definition tnum_length (t : number_type) : N :=
  match t with
  | T_i32 => 4
  | T_i64 => 8
  | T_f32 => 4
  | T_f64 => 8
  end.

Definition tvec_length (t: vector_type) : N :=
  match t with
  | T_v128 => 16
  end.
    

Definition tp_length (tp : packed_type) : nat :=
  match tp with
  | Tp_i8 => 1
  | Tp_i16 => 2
  | Tp_i32 => 4
  end.

Definition is_int_t (t : number_type) : bool :=
  match t with
  | T_i32 => true
  | T_i64 => true
  | T_f32 => false
  | T_f64 => false
  end.

Definition is_float_t (t : number_type) : bool :=
  match t with
  | T_i32 => false
  | T_i64 => false
  | T_f32 => true
  | T_f64 => true
  end.

Definition is_mut (tg : global_type) : bool :=
  tg_mut tg == MUT_var.


Definition app_unop_i (e : Wasm_int.type) (iop : unop_i) : Wasm_int.sort e -> Wasm_int.sort e :=
  let: Wasm_int.Pack u (Wasm_int.Class eqmx intmx) as e' := e
    return Wasm_int.sort e' -> Wasm_int.sort e' in
  match iop with
  | UOI_ctz => Wasm_int.int_ctz intmx
  | UOI_clz => Wasm_int.int_clz intmx
  | UOI_popcnt => Wasm_int.int_popcnt intmx
  end.

Definition app_unop_f (e : Wasm_float.type) (fop : unop_f) : Wasm_float.sort e -> Wasm_float.sort e :=
  let: Wasm_float.Pack u (Wasm_float.Class eqmx mx) as e' := e
    return Wasm_float.sort e' -> Wasm_float.sort e' in
  match fop with
  | UOF_neg => Wasm_float.float_neg mx
  | UOF_abs => Wasm_float.float_abs mx
  | UOF_ceil => Wasm_float.float_ceil mx
  | UOF_floor => Wasm_float.float_floor mx
  | UOF_trunc => Wasm_float.float_trunc mx
  | UOF_nearest => Wasm_float.float_nearest mx
  | UOF_sqrt => Wasm_float.float_sqrt mx
  end.

Definition app_unop (op: unop) (v: value_num) :=
  match op with
  | Unop_i iop =>
    match v with
    | VAL_int32 c => VAL_int32 (@app_unop_i i32t iop c)
    | VAL_int64 c => VAL_int64 (@app_unop_i i64t iop c)
    | _ => v
    end
  | Unop_f fop =>
    match v with
    | VAL_float32 c => VAL_float32 (@app_unop_f f32t fop c)
    | VAL_float64 c => VAL_float64 (@app_unop_f f64t fop c)
    | _ => v
    end
  end.

Definition app_binop_i (e : Wasm_int.type) (iop : binop_i)
    : Wasm_int.sort e -> Wasm_int.sort e -> option (Wasm_int.sort e) :=
  let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e
    return Wasm_int.sort e' -> Wasm_int.sort e' -> option (Wasm_int.sort e') in
  let: add_some := fun f c1 c2 => Some (f c1 c2) in
  match iop with
  | BOI_add => add_some (Wasm_int.int_add mx)
  | BOI_sub => add_some (Wasm_int.int_sub mx)
  | BOI_mul => add_some (Wasm_int.int_mul mx)
  | BOI_div SX_U => Wasm_int.int_div_u mx
  | BOI_div SX_S => Wasm_int.int_div_s mx
  | BOI_rem SX_U => Wasm_int.int_rem_u mx
  | BOI_rem SX_S => Wasm_int.int_rem_s mx
  | BOI_and => add_some (Wasm_int.int_and mx)
  | BOI_or => add_some (Wasm_int.int_or mx)
  | BOI_xor => add_some (Wasm_int.int_xor mx)
  | BOI_shl => add_some (Wasm_int.int_shl mx)
  | BOI_shr SX_U => add_some (Wasm_int.int_shr_u mx)
  | BOI_shr SX_S => add_some (Wasm_int.int_shr_s mx)
  | BOI_rotl => add_some (Wasm_int.int_rotl mx)
  | BOI_rotr => add_some (Wasm_int.int_rotr mx)
  end.

Definition app_binop_f (e : Wasm_float.type) (fop : binop_f)
    : Wasm_float.sort e -> Wasm_float.sort e -> option (Wasm_float.sort e) :=
  let: Wasm_float.Pack u (Wasm_float.Class _ mx) as e' := e
    return Wasm_float.sort e' -> Wasm_float.sort e' -> option (Wasm_float.sort e') in
  let: add_some := fun f c1 c2 => Some (f c1 c2) in
  match fop with
  | BOF_add => add_some (Wasm_float.float_add mx)
  | BOF_sub => add_some (Wasm_float.float_sub mx)
  | BOF_mul => add_some (Wasm_float.float_mul mx)
  | BOF_div => add_some (Wasm_float.float_div mx)
  | BOF_min => add_some (Wasm_float.float_min mx)
  | BOF_max => add_some (Wasm_float.float_max mx)
  | BOF_copysign => add_some (Wasm_float.float_copysign mx)
  end.

Definition app_binop (op: binop) (v1: value_num) (v2: value_num) :=
  match op with
  | Binop_i iop =>
    match v1 with
    | VAL_int32 c1 =>
      match v2 with
      | VAL_int32 c2 => option_map (fun v => VAL_int32 v) (@app_binop_i i32t iop c1 c2)
      |  _ => None
      end                              
    | VAL_int64 c1 =>
      match v2 with
      | VAL_int64 c2 => option_map (fun v => VAL_int64 v) (@app_binop_i i64t iop c1 c2)
      |  _ => None
      end                              
    | _ => None
    end
  | Binop_f fop =>
    match v1 with
    | VAL_float32 c1 =>
      match v2 with
      | VAL_float32 c2 => option_map (fun v => VAL_float32 v) (@app_binop_f f32t fop c1 c2)
      |  _ => None
      end                              
    | VAL_float64 c1 =>
      match v2 with
      | VAL_float64 c2 => option_map (fun v => VAL_float64 v) (@app_binop_f f64t fop c1 c2)
      |  _ => None
      end                              
    | _ => None
    end
  end.

Definition app_testop_i (e : Wasm_int.type) (o : testop) : Wasm_int.sort e -> bool :=
  let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e return Wasm_int.sort e' -> bool in
  match o with
  | Eqz => Wasm_int.int_eqz mx
  end.

Definition app_relop_i (e : Wasm_int.type) (rop : relop_i)
    : Wasm_int.sort e -> Wasm_int.sort e -> bool :=
  let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e
    return Wasm_int.sort e' -> Wasm_int.sort e' -> bool in
  match rop with
  | ROI_eq => Wasm_int.int_eq mx
  | ROI_ne => @Wasm_int.int_ne _
  | ROI_lt SX_U => Wasm_int.int_lt_u mx
  | ROI_lt SX_S => Wasm_int.int_lt_s mx
  | ROI_gt SX_U => Wasm_int.int_gt_u mx
  | ROI_gt SX_S => Wasm_int.int_gt_s mx
  | ROI_le SX_U => Wasm_int.int_le_u mx
  | ROI_le SX_S => Wasm_int.int_le_s mx
  | ROI_ge SX_U => Wasm_int.int_ge_u mx
  | ROI_ge SX_S => Wasm_int.int_ge_s mx
  end.

Definition app_relop_f (e : Wasm_float.type) (rop : relop_f)
    : Wasm_float.sort e -> Wasm_float.sort e -> bool :=
  let: Wasm_float.Pack u (Wasm_float.Class _ mx) as e' := e
    return Wasm_float.sort e' -> Wasm_float.sort e' -> bool in
  match rop with
  | ROF_eq => Wasm_float.float_eq mx
  | ROF_ne => @Wasm_float.float_ne _
  | ROF_lt => Wasm_float.float_lt mx
  | ROF_gt => Wasm_float.float_gt mx
  | ROF_le => Wasm_float.float_le mx
  | ROF_ge => Wasm_float.float_ge mx
  end.

Definition app_relop (op: relop) (v1: value_num) (v2: value_num) :=
  match op with
  | Relop_i iop =>
    match v1 with
    | VAL_int32 c1 =>
      match v2 with
      | VAL_int32 c2 => @app_relop_i i32t iop c1 c2
      |  _ => false
      end                              
    | VAL_int64 c1 =>
      match v2 with
      | VAL_int64 c2 => @app_relop_i i64t iop c1 c2
      |  _ => false
      end                              
    | _ => false
    end
  | Relop_f fop =>
    match v1 with
    | VAL_float32 c1 =>
      match v2 with
      | VAL_float32 c2 => @app_relop_f f32t fop c1 c2
      |  _ => false
      end                              
    | VAL_float64 c1 =>
      match v2 with
      | VAL_float64 c2 => @app_relop_f f64t fop c1 c2
      |  _ => false
      end                              
    | _ => false
    end
  end.

Definition types_agree (t : value_type) (v : value) : bool :=
  (typeof v) == t.

Definition rglob_is_mut (g : module_global) : bool :=
  g.(modglob_type).(tg_mut) == MUT_var.

Definition option_bind (A B : Type) (f : A -> option B) (x : option A) :=
  match x with
  | None => None
  | Some y => f y
  end.

Section Host.

Variable host_function : eqType.

Let funcinst := funcinst host_function.
Let store_record := store_record host_function.

Definition cl_type (cl : funcinst) : function_type :=
  match cl with
  | FC_func_native tf _ _ => tf
  | FC_func_host tf _ => tf
  end.

Definition upd_s_mem (s : store_record) (m : list meminst) : store_record :=
  {|
    s_funcs := s.(s_funcs);
    s_tables := s.(s_tables);
    s_mems := m;
    s_globals := s.(s_globals);
    s_elems := s.(s_elems);
    s_datas := s.(s_datas);
  |}.

Definition stypes (s : store_record) (i : moduleinst) (j : typeidx) : option function_type :=
  lookup_N (inst_types i) j.


Definition sfunc_ind (s : store_record) (i : moduleinst) (j : funcidx) : option funcaddr :=
  lookup_N (inst_funcs i) j.

Definition sfunc (s : store_record) (i : moduleinst) (j : funcidx) : option funcinst :=
  match sfunc_ind s i j with
  | Some a => lookup_N (s_funcs s) a
  | None => None
  end.

Definition sglob_ind (s : store_record) (i : moduleinst) (j : globalidx) : option globaladdr :=
  lookup_N (inst_globals i) j.

Definition sglob (s : store_record) (i : moduleinst) (j : globalidx) : option globalinst :=
  match sglob_ind s i j with
  | Some a => lookup_N (s_globals s) a
  | None => None
  end.

Definition sglob_val (s : store_record) (i : moduleinst) (j : globalidx) : option value :=
  option_map g_val (sglob s i j).

Definition smem_ind (s : store_record) (i : moduleinst) : option memaddr :=
  match i.(inst_mems) with
  | nil => None
  | cons k _ => Some k
  end.

Definition smem (s: store_record) (inst: moduleinst) : option meminst :=
  match inst.(inst_mems) with
  | nil => None
  | k :: _ => lookup_N s.(s_mems) k
  end.

Definition tab_size (t: tableinst) : nat :=
  length (tableinst_elem t).

Definition stab_ind (s: store_record) (inst: moduleinst) (x: tableidx) : option tableaddr :=
  lookup_N inst.(inst_tables) x.

Definition stab (s: store_record) (inst: moduleinst) (x: tableidx): option tableinst :=
  match lookup_N inst.(inst_tables) x with
  | Some a => lookup_N s.(s_tables) a
  | None => None
  end.

Definition stab_elem (s: store_record) (inst: moduleinst) (x: tableidx) (i: elemidx) : option value_ref :=
  match lookup_N inst.(inst_tables) x with
  | Some tabaddr =>
      match lookup_N s.(s_tables) tabaddr with
      | Some tab => lookup_N tab.(tableinst_elem) i
      | _ => None
      end
  | _ => None
  end.

Definition stab_update (s: store_record) (inst: moduleinst) (x: tableidx) (i: elemidx) (tabv: value_ref) : option store_record :=
  match lookup_N inst.(inst_tables) x with
  | Some tabaddr =>
      match lookup_N s.(s_tables) tabaddr with
      | Some tab =>
          if i < tab_size tab then
            let: tab' := {| tableinst_type := tab.(tableinst_type);
                           tableinst_elem := set_nth tabv tab.(tableinst_elem) (N.to_nat i) tabv |} in
            let: tabs' := set_nth tab' s.(s_tables) x tab' in
            Some (Build_store_record (s_funcs s) tabs' (s_mems s) (s_globals s) (s_elems s) (s_datas s))
          else None
      | None => None
      end
  | None => None
  end.

Definition growtable (tab: tableinst) (n: N) (tabinit: value_ref) : option tableinst :=
  let len := (N.of_nat (tab_size tab) + n)%N in
  if N.leb u32_bound len then None
  else
    let: {| tt_limits := lim; tt_elem_type := tabtype |} := tab.(tableinst_type) in
    let lim' := {| lim_min := len; lim_max := lim.(lim_max) |} in
    if limit_valid_range lim' table_limit_bound then
      let elem' := tab.(tableinst_elem) ++ (List.repeat tabinit (N.to_nat n)) in
      let tab' := {| tableinst_type := {| tt_limits := lim'; tt_elem_type := tabtype |}; tableinst_elem := elem' |} in
      Some tab'
    else
      None.

Definition stab_grow (s: store_record) (inst: moduleinst) (x: tableidx) (n: N) (tabinit: value_ref) : option store_record :=
  match stab s inst x with
  | Some tab =>
      match growtable tab n tabinit with
      | Some tab' => 
          let tabs' := (set_nth tab' s.(s_tables) (N.to_nat x) tab') in
          Some (Build_store_record (s_funcs s) tabs' (s_mems s) (s_globals s) (s_elems s) (s_datas s))
      | None => None
      end
  | None => None
  end.

Definition elem_size (e: eleminst) : nat :=
  length (eleminst_elem e).

Definition selem (s: store_record) (inst: moduleinst) (x: elemaddr): option eleminst :=
  match lookup_N inst.(inst_elems) x with
  | Some eaddr => lookup_N s.(s_elems) eaddr
  | _ => None
  end.

Definition selem_drop (s: store_record) (inst: moduleinst) (x: elemaddr) : option store_record :=
  match selem s inst x with
  | Some elem =>
      let empty_elem := {| eleminst_type := elem.(eleminst_type); eleminst_elem := [::] |} in
      let: elems' := set_nth empty_elem s.(s_elems) (N.to_nat x) empty_elem in
      Some (Build_store_record (s_funcs s) (s_tables s) (s_mems s) (s_globals s) elems' (s_datas s))
  | None => None
  end.

Definition data_size (d: datainst) : nat :=
  length (datainst_data d).

Definition sdata (s: store_record) (inst: moduleinst) (x: dataaddr): option datainst :=
  match lookup_N inst.(inst_datas) x with
  | Some daddr => lookup_N s.(s_datas) daddr
  | _ => None
  end.

Definition sdata_drop (s: store_record) (inst: moduleinst) (x: dataaddr) : option store_record :=
  match sdata s inst x with
  | Some data =>
      let empty_data := {| datainst_data := [::] |} in
      let: datas' := set_nth empty_data s.(s_datas) (N.to_nat x) empty_data in
      Some (Build_store_record (s_funcs s) (s_tables s) (s_mems s) (s_globals s) (s_elems s) datas')
  | None => None
  end.   

Definition supdate_glob_s (s : store_record) (k : globaladdr) (v : value) : option store_record :=
  option_map
    (fun g =>
      let: g' := Build_globalinst (g_type g) v in
      let: gs' := set_nth g' (s_globals s) k g' in
      Build_store_record (s_funcs s) (s_tables s) (s_mems s) gs' (s_elems s) (s_datas s))
    (lookup_N (s_globals s) k).

Definition supdate_glob (s : store_record) (i : moduleinst) (j : globalidx) (v : value) : option store_record :=
  option_bind
    (fun k => supdate_glob_s s k v)
    (sglob_ind s i j).


Definition func_extension (f1 f2: funcinst) : bool :=
  f1 == f2.

Definition table_extension (t1 t2 : tableinst) :=
  (tableinst_type t1 == tableinst_type t2) &&
  (tab_size t1 <= tab_size t2).

Definition mem_extension (m1 m2 : meminst) :=
  (meminst_type m1 == meminst_type m2) &&
  (mem_length m1 <= mem_length m2).

Definition global_extension (g1 g2: globalinst) : bool :=
  (g_type g1 == g_type g2) &&
    let (mut, t) := g_type g1 in
    ((mut == MUT_var) || (g_val g1 == g_val g2)).

Definition elem_extension (e1 e2: eleminst) : bool :=
  (eleminst_elem e1 == eleminst_elem e2) || (eleminst_elem e2 == [::]).

Definition data_extension (d1 d2: datainst) : bool :=
  (datainst_data d1 == datainst_data d2) || (datainst_data d2 == [::]).

Definition component_extension {T: Type} (ext_rel: T -> T -> bool) (l1 l2: list T): bool :=
  (length l1 <= length l2) &&
  all2 ext_rel l1 (take (length l1) l2).

Definition store_extension (s s' : store_record) : bool :=
  component_extension func_extension s.(s_funcs) s'.(s_funcs) &&
  component_extension table_extension s.(s_tables) s'.(s_tables) &&
  component_extension mem_extension s.(s_mems) s'.(s_mems) &&
  component_extension global_extension s.(s_globals) s'.(s_globals) &&
  component_extension elem_extension s.(s_elems) s'.(s_elems) &&
  component_extension data_extension s.(s_datas) s'.(s_datas).


Definition vs_to_vts (vs : list value) : list value_type := map typeof vs.

Definition to_e_list (bes : list basic_instruction) : seq administrative_instruction :=
  map AI_basic bes.

(* Two versions of converting admin instructions back to basic *)
Definition to_b_single (e: administrative_instruction) : basic_instruction :=
  match e with
  | AI_basic x => x
  | _ => BI_const_num (VAL_int32 (Wasm_int.Int32.zero))
  end.

Definition to_b_list (es: seq administrative_instruction) : seq basic_instruction :=
  map to_b_single es.

Definition to_b_single_opt (e: administrative_instruction) : option basic_instruction :=
  match e with
  | AI_basic x => Some x
  | _ => None
  end.

Definition to_b_list_opt (es: seq administrative_instruction) : option (seq basic_instruction) :=
  those (map to_b_single_opt es).

Definition e_is_basic (e: administrative_instruction) : bool :=
  match e with
  | AI_basic _ => true
  | _ => false
  end.

Definition es_is_basic (es: list administrative_instruction): bool :=
  all e_is_basic es.

Definition vref_to_e (vref: value_ref) : administrative_instruction :=
  match vref with
  | VAL_ref_null t => AI_basic (BI_ref_null t)
  | VAL_ref_func addr => AI_ref addr
  | VAL_ref_extern eaddr => AI_ref_extern eaddr
  end.

Definition v_to_e (v: value) : administrative_instruction :=
  match v with
  | VAL_num v => AI_basic (BI_const_num v)
  | VAL_vec v => AI_basic (BI_const_vec v)
  | VAL_ref v => vref_to_e v
  end.                      

(** [v_to_e_list]: 
    takes a list of [v] and gives back a list where each [v] is mapped to the corresponding administrative instruction. **)
Definition v_to_e_list (ves : seq value) : seq administrative_instruction :=
  map v_to_e ves.

Definition e_to_vref (e: administrative_instruction) : value_ref :=
  match e with
  | AI_basic (BI_ref_null t) => VAL_ref_null t
  | AI_ref addr => VAL_ref_func addr
  | AI_ref_extern eaddr => VAL_ref_extern eaddr
  | _ => VAL_ref_null T_funcref
  end.

Definition e_to_vref_opt (e: administrative_instruction) : option value_ref :=
  match e with
  | AI_basic (BI_ref_null t) => Some (VAL_ref_null t)
  | AI_ref addr => Some (VAL_ref_func addr)
  | AI_ref_extern eaddr => Some (VAL_ref_extern eaddr)
  | _ => None
  end.

(* Two versions of converting admin instructions into values *)
Definition e_to_v (e: administrative_instruction) : value :=
  match e with
  | AI_basic (BI_const_num v) => VAL_num v
  | AI_basic (BI_const_vec v) => VAL_vec v
  | _ => (VAL_ref (e_to_vref e))
  end.

Definition e_to_v_list (es: seq administrative_instruction) : list value :=
  map e_to_v es.

Definition e_to_v_opt (e: administrative_instruction) : option value :=
  match e with
  | AI_basic (BI_const_num v) => Some (VAL_num v)
  | AI_basic (BI_const_vec v) => Some (VAL_vec v)
  | _ => option_map VAL_ref (e_to_vref_opt e)
  end.

Definition e_to_v_list_opt (es: list administrative_instruction) : option (list value) :=
  those (map e_to_v_opt es).

Definition is_const (e : administrative_instruction) : bool :=
  match e_to_v_opt e with
  | Some _ => true
  | None => false
  end.

Definition const_list (es : list administrative_instruction) : bool :=
  List.forallb is_const es.

(* The expected terminal instructions *)
Definition terminal_form (es: seq administrative_instruction) :=
  const_list es \/ es = [::AI_trap].

(* Filling label context hole *)
Fixpoint lfill {k} (lh : lholed k) (es : seq administrative_instruction) : seq administrative_instruction :=
  match lh with
  | LH_base vs es' => v_to_e_list vs ++ es ++ es'
  | LH_rec _ vs n es' lh' es'' => v_to_e_list vs ++ [:: AI_label n es' (lfill lh' es)] ++ es''
  end.

(* interpreter related *)

Fixpoint split_vals (es : seq basic_instruction) : seq value * seq basic_instruction :=
  match es with
  | e :: es' =>
      match e_to_v_opt (AI_basic e) with
        | Some v => 
            let: (vs', es'') := split_vals es' in
            (v :: vs', es'')
      | None => (nil, es)
      end
  | nil => (nil, nil)
  end.

(** [split_vals_e es]: takes the maximum initial segment of [es] whose elements
    are all of the form [Basic (EConst v)];
    returns a pair of lists [(ves, es')] where [ves] are those [v]'s in that initial
    segment and [es] is the remainder of the original [es]. **)
Fixpoint split_vals_e (es : seq administrative_instruction) : seq value * seq administrative_instruction :=
  match es with
  | e :: es' =>
      match e_to_v_opt e with
        | Some v => 
            let: (vs', es'') := split_vals_e es' in
            (v :: vs', es'')
      | None => (nil, es)
      end
  | nil => (nil, nil)
  end.

Fixpoint split_n (es : seq value) (n : nat) : seq value * seq value :=
  match (es, n) with
  | ([::], _) => ([::], [::])
  | (_, 0) => ([::], es)
  | (e :: esX, n.+1) =>
    let: (es', es'') := split_n esX n in
    (e :: es', es'')
  end.

(* TODO: eliminate the use of this *)
Definition expect {A B : Type} (ao : option A) (f : A -> B) (b : B) : B :=
  oapp f b ao.

Definition expect' {A B : Type} (ao : option A) (f : A -> B) (b : B) : B :=
  match ao as ao0 return (ao = ao0) -> B with
  | Some a => (fun _ => f a)
  | None => fun _ => b
  end (Logic.eq_refl ao).

Definition vs_to_es (vs : seq value) : seq administrative_instruction :=
  v_to_e_list (rev vs).

Definition e_is_trap (e : administrative_instruction) : bool :=
  (e == AI_trap).

Definition es_is_trap (es : seq administrative_instruction) : bool :=
  (es == [:: AI_trap]).


(** Converting a result into a stack. **)
Definition result_to_stack (r : result) :=
  match r with
  | result_values vs => v_to_e_list vs
  | result_trap => [:: AI_trap]
  end.

Definition result_types_agree (ts : result_type) r :=
  match r with
  | result_values vs => all2 types_agree ts vs
  | result_trap => true
  end.

(** std-doc:
https://www.w3.org/TR/wasm-core-2/exec/runtime.html#exec-expand
**)
Definition expand (inst: moduleinst) (tb: block_type) : option function_type :=
  match tb with
  | BT_id n => lookup_N inst.(inst_types) n
  | BT_valtype (Some t) => Some (Tf [::] [::t])
  | BT_valtype None => Some (Tf [::] [::])
  end.
  
Definition expand_t (C: t_context) (tb: block_type) : option function_type :=
  match tb with
  | BT_id n => lookup_N C.(tc_types) n
  | BT_valtype (Some t) => Some (Tf [::] [::t])
  | BT_valtype None => Some (Tf [::] [::])
  end.
  
Definition load_store_t_bounds (a : alignment_exponent) (tp : option packed_type) (t : number_type) : bool :=
  match tp with
  | None => Nat.pow 2 a <= tnum_length t
  | Some tp' => (Nat.pow 2 a <= tp_length tp') && (tp_length tp' < tnum_length t) && (is_int_t t)
  end.

Definition cvt_i32 (s : option sx) (v : value_num) : option i32 :=
  match v with
  | VAL_int32 _ => None
  | VAL_int64 c => Some (wasm_wrap c)
  | VAL_float32 c =>
    match s with
    | Some SX_U => Wasm_float.float_ui32_trunc f32m c
    | Some SX_S => Wasm_float.float_ui32_trunc f32m c
    | None => None
    end
  | VAL_float64 c =>
    match s with
    | Some SX_U => Wasm_float.float_ui32_trunc f64m c
    | Some SX_S => Wasm_float.float_ui32_trunc f64m c
    | None => None
    end
  end.

Definition cvt_i64 (s : option sx) (v : value_num) : option i64 :=
  match v with
  | VAL_int32 c =>
    match s with
    | Some SX_U => Some (wasm_extend_u c)
    | Some SX_S => Some (wasm_extend_s c)
    | None => None
    end
  | VAL_int64 c => None
  | VAL_float32 c =>
    match s with
    | Some SX_U => Wasm_float.float_ui64_trunc f32m c
    | Some SX_S => Wasm_float.float_si64_trunc f32m c
    | None => None
    end
  | VAL_float64 c =>
    match s with
    | Some SX_U => Wasm_float.float_ui64_trunc f64m c
    | Some SX_S => Wasm_float.float_si64_trunc f64m c
    | None => None
    end
  end.

Definition cvt_f32 (s : option sx) (v : value_num) : option f32 :=
  match v with
  | VAL_int32 c =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui32 f32m c)
    | Some SX_S => Some (Wasm_float.float_convert_si32 f32m c)
    | None => None
    end
  | VAL_int64 c =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui64 f32m c)
    | Some SX_S => Some (Wasm_float.float_convert_si64 f32m c)
    | None => None
    end
  | VAL_float32 c => None
  | VAL_float64 c => Some (wasm_demote c)
  end.

Definition cvt_f64 (s : option sx) (v : value_num) : option f64 :=
  match v with
  | VAL_int32 c =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui32 f64m c)
    | Some SX_S => Some (Wasm_float.float_convert_si32 f64m c)
    | None => None
    end
  | VAL_int64 c =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui64 f64m c)
    | Some SX_S => Some (Wasm_float.float_convert_si64 f64m c)
    | None => None
    end
  | VAL_float32 c => Some (wasm_promote c)
  | VAL_float64 c => None
  end.


Definition cvt (t : number_type) (s : option sx) (v : value_num) : option value_num :=
  match t with
  | T_i32 => option_map VAL_int32 (cvt_i32 s v)
  | T_i64 => option_map VAL_int64 (cvt_i64 s v)
  | T_f32 => option_map VAL_float32 (cvt_f32 s v)
  | T_f64 => option_map VAL_float64 (cvt_f64 s v)
  end.

Definition bits (v : value_num) : bytes :=
  match v with
  | VAL_int32 c => serialise_i32 c
  | VAL_int64 c => serialise_i64 c
  | VAL_float32 c => serialise_f32 c
  | VAL_float64 c => serialise_f64 c
  end.

Definition bitzero (t : number_type) : value_num :=
  match t with
  | T_i32 => VAL_int32 (Wasm_int.int_zero i32m)
  | T_i64 => VAL_int64 (Wasm_int.int_zero i64m)
  | T_f32 => VAL_float32 (Wasm_float.float_zero f32m)
  | T_f64 => VAL_float64 (Wasm_float.float_zero f64m)
  end.


(** std-doc:
Each value type has an associated default value; it is the respective value 0 for number types and
 null for reference types.

https://www.w3.org/TR/wasm-core-2/exec/runtime.html#default-val
**)
Definition default_val (t: value_type) : value :=
  match t with
  | T_num t => VAL_num (bitzero t)
  | T_vec t => VAL_vec (VAL_vec128 tt)
  | T_ref t => VAL_ref (VAL_ref_null t)
  end.

Definition n_zeros (ts : seq value_type) : seq value :=
  map default_val ts.

End Host.

Arguments cl_type {host_function}.

#[export]
Hint Unfold v_to_e: core.
