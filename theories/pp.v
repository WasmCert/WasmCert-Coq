(** Pretty-printer **)

Require Import Coq.Strings.String.
From compcert Require Import Floats.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import Coq.Init.Decimal.
Require Export bytes_pp datatypes interpreter_ctx.
Require Import BinNat.
Require Import ansi list_extra.

Open Scope string_scope.

Section Host.

Context `{ho: host}.
  
Variable show_host_function : host_function -> string.

Definition newline_char : Ascii.ascii := Ascii.ascii_of_byte Byte.x0a.

Definition newline : string := String newline_char EmptyString.

(** Describe an indentation level. **)
Definition indentation := nat.

Fixpoint indent (i : indentation) (s : string) : string :=
  match i with
  | 0 => s
  | S i' => "  " ++ indent i' s
  end.

Definition type_style := FG_cyan.

Definition pp_number_type (vt: number_type) : string :=
  let s :=
    match vt with
    | T_i32 => "i32"
    | T_i64 => "i64"
    | T_f32 => "f32"
    | T_f64 => "f64"
    end in
  with_fg type_style s.

Definition pp_vector_type (vt: vector_type) : string :=
  let s :=
    match vt with
    | T_i128 => "v128"
    end in
  with_fg type_style s.

Definition pp_reference_type (vt : reference_type) : string :=
  let s :=
    match vt with
    | T_funcref => "funcref"
    | T_externref => "externref"
    end in
  with_fg type_style s.

Definition pp_value_type (vt: value_type) : string :=
  match vt with
  | T_num t => pp_number_type t
  | T_vec t => pp_vector_type t
  | T_ref t => pp_reference_type t
  | T_bot => "Bot" (* Should not happen *)
  end.

Definition pp_value_types (vts : list value_type) : string :=
  "[" ++ String.concat ", " (List.map pp_value_type vts) ++ "]".

Definition pp_function_type (tf : function_type) : string :=
  let '(Tf ts1 ts2) := tf in
  pp_value_types ts1 ++ " -> " ++ pp_value_types ts2.

Fixpoint string_of_uint (i : uint) : string :=
  match i with
  | Nil => ""
  | D0 i' => "0" ++ string_of_uint i'
  | D1 i' => "1" ++ string_of_uint i'
  | D2 i' => "2" ++ string_of_uint i'
  | D3 i' => "3" ++ string_of_uint i'
  | D4 i' => "4" ++ string_of_uint i'
  | D5 i' => "5" ++ string_of_uint i'
  | D6 i' => "6" ++ string_of_uint i'
  | D7 i' => "7" ++ string_of_uint i'
  | D8 i' => "8" ++ string_of_uint i'
  | D9 i' => "9" ++ string_of_uint i'
  end.

Definition pp_N (n: N) : string :=
  string_of_uint (N.to_uint n).

Definition pp_positive (p: positive) : string :=
  string_of_uint (BinPos.Pos.to_uint p).

Definition pp_Z (z: Z) : string :=
  match z with
  | Z0 => "0"
  | Zpos p => pp_positive p
  | Zneg p => "-" ++ pp_positive p
  end.

Definition pp_id := pp_N.

Definition pp_addr := pp_N.

Definition pp_block_type (tf : block_type) : string :=
  match tf with
  | BT_valtype None => ""
  | BT_valtype (Some vt) => " " ++ pp_value_type vt
  | BT_id x => pp_id x
  end.

Definition pp_i32 i :=
  pp_Z (Wasm_int.Int32.signed i).

Definition pp_i64 i :=
  pp_Z (Wasm_int.Int64.signed i).

(* TODO: all this printing of floats business is highly dubious,
   and completely untested *)
Fixpoint bool_list_of_pos (acc : list bool) (p : BinNums.positive) :=
  match p with
  | BinNums.xI p' => bool_list_of_pos (true :: acc) p'
  | BinNums.xO p' => bool_list_of_pos (false :: acc) p'
  | BinNums.xH => true :: acc
  end.

Open Scope list.

Fixpoint pp_bools (acc : list Byte.byte) (bools : list bool) : list Byte.byte :=
  (* TODO: I am ashamed I wrote this *)
  match bools with
  | nil => acc
  | b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: bools' =>
    pp_bools (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, b8))))))) :: acc) bools'
  | b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::  nil =>
    Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, false))))))) :: acc
  | b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: nil =>
    Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, false))))))) :: acc
  | b1 :: b2 :: b3 :: b4 :: b5 :: nil =>
    Byte.of_bits (b1, (b2, (b3, (b4, (b5, (false, (false, false))))))) :: acc
  | b1 :: b2 :: b3 :: b4 :: nil =>
    Byte.of_bits (b1, (b2, (b3, (b4, (false, (false, (false, false))))))) :: acc
  | b1 :: b2 :: b3 :: nil =>
    Byte.of_bits (b1, (b2, (b3, (false, (false, (false, (false, false))))))) :: acc
  | b1 :: b2 :: nil =>
    Byte.of_bits (b1, (b2, (false, (false, (false, (false, (false, false))))))) :: acc
  | b1 :: nil =>
    Byte.of_bits (b1, (false, (false, (false, (false, (false, (false, false))))))) :: acc
  end.

Definition pp_f32 (f : float32) : string :=
  match BinIntDef.Z.to_N ((Float32.to_bits f).(Integers.Int.intval)) with
  | BinNums.N0 => "0"
  | BinNums.Npos p =>
    bytes_pp.hex_small_no_prefix_of_bytes_compact (pp_bools nil (List.rev (bool_list_of_pos nil p)))
  end.

Definition pp_f64 (f : float) : string :=
  match BinIntDef.Z.to_N ((Float.to_bits f).(Integers.Int64.intval)) with
  | BinNums.N0 => "0"
  | BinNums.Npos p =>
    bytes_pp.hex_small_no_prefix_of_bytes_compact (pp_bools nil (List.rev (bool_list_of_pos nil p)))
  end.

Definition pp_value_num (v : value_num) : string :=
  match v with
  | VAL_int32 i => pp_number_type T_i32 ++ ".const " ++ with_fg FG_green (pp_i32 i) ++ newline
  | VAL_int64 i => pp_number_type T_i64 ++ ".const " ++ with_fg FG_green (pp_i64 i) ++ newline
  | VAL_float32 f => pp_number_type T_f32 ++ ".const " ++ with_fg FG_green (pp_f32 f) ++ newline
  | VAL_float64 f => pp_number_type T_f64 ++ ".const " ++ with_fg FG_green (pp_f64 f) ++ newline
  end.

Definition pp_value_vec (v : value_vec) : string :=
  match v with
  | VAL_vec128 t => pp_vector_type T_v128 ++ ".const" ++ with_fg FG_yellow " (unimplemented)" ++ newline
  end.

Definition pp_value_ref (v : value_ref) : string :=
  match v with
  | VAL_ref_null t => pp_reference_type t ++ ".null" ++ newline
  | VAL_ref_func a => "funcref " ++ pp_addr a ++ newline
  | VAL_ref_extern a => "externref " ++ pp_addr a ++ newline
  end.

Definition pp_value (v: value) : string :=
  match v with
  | VAL_num v' => pp_value_num v'
  | VAL_vec v' => pp_value_vec v'
  | VAL_ref v' => pp_value_ref v'
  end.

Definition pp_values (vs : list value) : string :=
  String.concat "" (List.map pp_value vs).

Definition pp_values_hint_empty (vs : list value) : string :=
  match vs with
  | nil => "(empty)"
  | _ => pp_values vs
  end.

Definition pp_unary_op_i (uoi : unop_i) : string :=
  match uoi with
  | UOI_clz => "clz"
  | UOI_ctz => "ctz"
  | UOI_popcnt => "popcnt"
  end.

Definition pp_unary_op_f (uof : unop_f) : string :=
  match uof with
  | UOF_neg => "neg"
  | UOF_abs => "abs"
  | UOF_ceil => "ceil"
  | UOF_floor => "floor"
  | UOF_trunc => "trunc"
  | UOF_nearest => "nearest"
  | UOF_sqrt => "sqrt"
  end.

Definition pp_sx (s : sx) : string :=
  match s with
  | SX_U => "u"
  | SX_S => "s"
  end.

Definition pp_sx_o (sxo : option sx) : string :=
  match sxo with
  | Some s => "_" ++ pp_sx s
  | None => ""
  end.

Definition pp_binary_op_i (boi : binop_i) : string :=
  match boi with
  | BOI_add => "add"
  | BOI_sub => "sub"
  | BOI_mul => "mul"
  | BOI_div s => "div_" ++ pp_sx s
  | BOI_rem s => "rem_" ++ pp_sx s
  | BOI_and => "and"
  | BOI_or => "or"
  | BOI_xor => "xor"
  | BOI_shl => "shl"
  | BOI_shr s => "shr_" ++ pp_sx s
  | BOI_rotl => "rotl"
  | BOI_rotr => "rotr"
  end.

Definition pp_binary_op_f (bof : binop_f) : string :=
  match bof with
  | BOF_add => "add"
  | BOF_sub => "sub"
  | BOF_mul => "mul"
  | BOF_div => "div"
  | BOF_min => "min"
  | BOF_max => "max"
  | BOF_copysign => "copysign"
  end.

Definition pp_rel_op_i (roi : relop_i) : string :=
  match roi with
  | ROI_eq => "eq"
  | ROI_ne => "ne"
  | ROI_lt s => "lt_" ++ pp_sx s
  | ROI_gt s => "gt_" ++ pp_sx s
  | ROI_le s => "le_" ++ pp_sx s
  | ROI_ge s => "ge_" ++ pp_sx s
  end.

Definition pp_rel_op_f (rof : relop_f) : string :=
  match rof with
  | ROF_eq => "eq"
  | ROF_ne => "ne"
  | ROF_lt => "lt"
  | ROF_gt => "gt"
  | ROF_le => "ne"
  | ROF_ge => "ge"
  end.

(* The alignment exponent is the exponent in both the spec and the binary, but needs to be the power in the text format. *)
Definition pp_memarg (a: alignment_exponent) (o: static_offset) : string :=
  "offset=" ++ pp_N o ++ " " ++ "align=" ++ pp_N (N.shiftl 1 a).

Definition pp_packing (p : packed_type) :=
  match p with
  | Tp_i8 => "8"
  | Tp_i16 => "16"
  | Tp_i32 => "32"
  end.

Definition pp_ps (ps : packed_type * sx) : string :=
  let '(p, s) := ps in
  pp_packing p ++ "_" ++ pp_sx s.

Definition be_style := FG_magenta.

Definition pp_list {T: Type} (f: T -> string) (l: list T) : string :=
  String.concat " " (List.map f l).

Definition pp_cvtop (cvt: cvtop) : string :=
  match cvt with
  | CVO_wrap => "wrap"
  | CVO_trunc => "trunc"
  | CVO_extend => "extend"
  | CVO_convert => "convert"
  | CVO_demote => "demote"
  | CVO_promote => "promote"
  | CVO_reinterpret => "reinterpret"
  | CVO_trunc_sat => "trunc_sat"
  end.


Fixpoint pp_basic_instruction (i : indentation) (be : basic_instruction) : string :=
  let pp_basic_instructions bes i :=
    String.concat "" (List.map (pp_basic_instruction (S i)) bes) in
  match be with
  | BI_unreachable => indent i (with_fg be_style "unreachable" ++ newline)
  | BI_nop => indent i (with_fg be_style "nop" ++ newline)
  | BI_drop => indent i (with_fg be_style "drop" ++ newline)
  | BI_select None => indent i (with_fg be_style "select" ++ newline)
  | BI_select (Some ts) => indent i (with_fg be_style "select " ++ pp_list pp_value_type ts ++ newline)
  | BI_ref_null t => indent i (with_fg be_style "ref.null " ++ pp_reference_type t ++ newline)
  | BI_ref_is_null => indent i (with_fg be_style "ref.is_null " ++ newline)
  | BI_ref_func addr => indent i (with_fg be_style "ref.func " ++ pp_addr addr ++ newline)
  | BI_block tf bes =>
    indent i (with_fg be_style "block" ++ with_fg type_style (pp_block_type tf) ++ newline)
    ++ pp_basic_instructions bes (S i)
    ++ indent i (with_fg be_style "end" ++ newline)
  | BI_loop tf bes =>
    indent i (with_fg be_style "loop" ++ with_fg type_style (pp_block_type tf) ++ newline)
    ++ pp_basic_instructions bes (S i)
    ++ indent i (with_fg be_style "end" ++ newline)
  | BI_if tf bes nil =>
    indent i (with_fg be_style "if" ++ with_fg type_style (pp_block_type tf) ++ newline)
    ++ pp_basic_instructions bes (S i)
    ++ indent i (with_fg be_style "end" ++ newline)
  | BI_if tf bes1 bes2 =>
    indent i (with_fg be_style "if" ++ with_fg type_style (pp_block_type tf) ++ newline)
    ++ pp_basic_instructions bes1 (S i)
    ++ indent i (with_fg be_style "else" ++ newline)
    ++ pp_basic_instructions bes2 (S i)
    ++ indent i (with_fg be_style "end" ++ newline)
  | BI_br x =>
    indent i (with_fg be_style "br " ++ pp_id x ++ newline)
  | BI_br_if x =>
    indent i (with_fg be_style "br_if " ++ pp_id x ++ newline)
  | BI_br_table is_ i =>
    indent i (with_fg be_style "br_table " ++ String.concat " " (List.map pp_id is_) ++ " " ++ pp_id i ++ newline)
  | BI_return =>
    indent i (with_fg be_style "return" ++ newline)
  | BI_call x =>
    indent i (with_fg be_style "call " ++ pp_id x ++ newline)
  | BI_call_indirect x y =>
    indent i (with_fg be_style "call_indirect " ++ pp_id x ++ " " ++ pp_id y ++ newline)
  | BI_local_get x =>
    indent i (with_fg be_style "local.get " ++ pp_id x ++ newline)
  | BI_local_set x =>
    indent i (with_fg be_style "local.set " ++ pp_id x ++ newline)
  | BI_local_tee x =>
    indent i (with_fg be_style "local.tee " ++ pp_id x ++ newline)
  | BI_global_get x =>
    indent i (with_fg be_style "global.get " ++ pp_id x ++ newline)
  | BI_global_set x =>
    indent i (with_fg be_style "global.set " ++ pp_id x ++ newline)

  | BI_table_get x =>
    indent i (with_fg be_style "table.get " ++ pp_id x ++ newline)
  | BI_table_set x =>
    indent i (with_fg be_style "table.set " ++ pp_id x ++ newline)
  | BI_table_init x y =>
    indent i (with_fg be_style "table.init " ++ pp_id x ++ " " ++ pp_id y ++ newline)
  | BI_elem_drop x =>
    indent i (with_fg be_style "elem.drop " ++ pp_id x ++ newline)
  | BI_table_copy x y =>
    indent i (with_fg be_style "table.copy " ++ pp_id x ++ " " ++ pp_id y ++ newline)
  | BI_table_grow x =>
    indent i (with_fg be_style "table.grow " ++ pp_id x ++ newline)
  | BI_table_size x =>
    indent i (with_fg be_style "table.size " ++ pp_id x ++ newline)
  | BI_table_fill x =>
    indent i (with_fg be_style "table.fill " ++ pp_id x ++ newline)
             
  | BI_load vt None a o =>
    indent i (pp_number_type vt ++ ".load " ++ pp_memarg a o ++ newline)
  | BI_load vt (Some ps) a o =>
    indent i (pp_number_type vt ++ ".load" ++ pp_ps ps ++ " " ++ pp_memarg a o ++ newline)
  | BI_store vt None a o =>
    indent i (pp_number_type vt ++ ".store " ++ pp_memarg a o ++ newline)
  | BI_store vt (Some p) a o =>
    indent i (pp_number_type vt ++ ".store" ++ pp_packing p ++ " " ++ pp_memarg a o ++ newline)
  | BI_memory_size =>
    indent i (with_fg be_style "memory.size" ++ newline ++ newline)
  | BI_memory_grow =>
    indent i (with_fg be_style "memory.grow" ++ newline)
  | BI_memory_init x =>
    indent i (with_fg be_style "memory.init " ++ pp_id x ++ newline)
  | BI_data_drop x =>
    indent i (with_fg be_style "data.drop " ++ pp_id x ++ newline)
  | BI_memory_copy =>
    indent i (with_fg be_style "memory.copy" ++ newline)
  | BI_memory_fill =>
    indent i (with_fg be_style "memory.fill" ++ newline)
  | BI_const_num v =>
    indent i (pp_value_num v)
  | BI_const_vec v =>
    indent i (pp_value_vec v)
  | BI_unop vt (Unop_i uoi) =>
    indent i (pp_number_type vt ++ "." ++ pp_unary_op_i uoi ++ newline)
  | BI_unop vt (Unop_f uof) =>
    indent i (pp_number_type vt ++ "." ++ pp_unary_op_f uof ++ newline)
  | BI_unop vt (Unop_extend n) =>
    indent i (pp_number_type vt ++ ".extend" ++ pp_N n ++ "_" ++ pp_sx (SX_S) ++ newline)
  | BI_binop vt (Binop_i boi) =>
    indent i (pp_number_type vt ++ "." ++ pp_binary_op_i boi ++ newline)
  | BI_binop vt (Binop_f bof) =>
    indent i (pp_number_type vt ++ "." ++ pp_binary_op_f bof ++ newline)
  | BI_testop vt Eqz =>
    indent i (pp_number_type vt ++ ".eqz" ++ newline)
  | BI_relop vt (Relop_i roi) =>
    indent i (pp_number_type vt ++ "." ++ pp_rel_op_i roi ++ newline)
  | BI_relop vt (Relop_f rof) =>
    indent i (pp_number_type vt ++ "." ++ pp_rel_op_f rof ++ newline)
  | BI_cvtop vt1 cvtop vt2 sxo =>
      indent i (pp_number_type vt1 ++ "." ++ pp_cvtop cvtop ++ "_" ++ pp_number_type vt2 ++ pp_sx_o sxo ++ newline)
  end.

Definition pp_basic_instructions n bes :=
  String.concat "" (List.map (pp_basic_instruction n) bes).

Definition pp_funcinst (n : indentation) (fc : funcinst) : string :=
  match fc with
  | FC_func_native ft inst mfunc =>
    (* TODO: show instance? *)
    indent n ("native " ++ pp_function_type ft ++ newline) ++
    indent n ("value types " ++ pp_value_types mfunc.(modfunc_locals) ++ newline) ++
    indent n ("body" ++ newline) ++
    pp_basic_instructions (n.+1) mfunc.(modfunc_body) ++
    indent n ("end native" ++ newline)
  | FC_func_host ft h =>
    indent n ("host " ++ show_host_function h
              ++ " : " ++ pp_function_type ft ++ newline)
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_uint (Nat.to_uint (BinNatDef.N.of_nat n)).

Definition ae_style := FG_blue.

Fixpoint pp_administrative_instruction (n : indentation) (e : administrative_instruction) : string :=
  let pp_administrative_instructions (n : nat) (es : list administrative_instruction) : string :=
    String.concat "" (List.map (pp_administrative_instruction n) es) in
  match e with
  | AI_basic be => pp_basic_instruction n be
  | AI_trap => indent n (with_fg ae_style "trap" ++ newline)
  | AI_ref a =>
    indent n (with_fg ae_style "ref " ++ pp_addr a ++ newline)
  | AI_ref_extern a =>
    indent n (with_fg ae_style "ref_extern " ++ pp_addr a ++ newline)
  | AI_invoke a =>
    indent n (with_fg ae_style "invoke " ++ pp_addr a ++ newline)
  (*    pp_funcinst (n.+1) fc*)
           
  | AI_label k es1 es2 =>
    indent n (with_fg ae_style "label " ++ string_of_nat k ++ newline) ++
    String.concat "" (List.map (pp_administrative_instruction (n.+1)) es1) ++
    indent n (with_fg ae_style "label_cont" ++ newline) ++
    String.concat "" (List.map (pp_administrative_instruction (n.+1)) es2) ++
    indent n (with_fg ae_style "end label" ++ newline)
  | AI_frame n f es =>
    indent n (with_fg ae_style "frame " ++ string_of_nat n ++ newline) ++
    (* TODO: inst? *)
    indent n (with_fg ae_style "with values " ++ pp_values_hint_empty f.(f_locs) ++ newline) ++
    pp_administrative_instructions (n.+1) es ++
    indent n (with_fg ae_style "end frame" ++ newline)
  end.

Definition pp_administrative_instructions (n : nat) (es : list administrative_instruction) : string :=
  String.concat "" (List.map (pp_administrative_instruction n) es).

Definition pp_mutability (m : mutability) : string :=
  match m with
  | MUT_const => "const"
  | MUT_var => "var"
  end.

Definition pp_global_type (gt: global_type) : string :=
  pp_mutability gt.(tg_mut) ++ " " ++ pp_value_type gt.(tg_t).

Definition pp_global (g : globalinst) : string :=
  pp_global_type g.(g_type) ++ " " ++ pp_value g.(g_val).

Definition pp_globals (n : indentation) (gs : list globalinst) : string :=
  String.concat "" (mapi (fun i g => indent n (string_of_nat i ++ ": " ++ pp_global g ++ newline)) gs).

Definition pp_memories (n : indentation) (ms : list meminst) : string :=
  String.concat "" (mapi (fun i m => indent n (string_of_nat i ++ ": " ++ "TODO: memory" ++ newline)) ms).

Definition pp_table (n: indentation) (t : tableinst) : string :=
  String.concat "" (mapi (fun i elem => indent n (string_of_nat i ++ ": " ++ pp_value_ref elem ++ newline)) t.(tableinst_elem)).

Definition pp_tables (n : indentation) (ms : list tableinst) : string :=
  String.concat "" (mapi (fun i t => indent n (string_of_nat i ++ ": " ++ pp_table n t)) ms).

Definition pp_store (n : indentation) (s : store_record) : string :=
  indent n ("globals" ++ newline) ++
  pp_globals (n.+1) s.(s_globals) ++
  indent n ("memories" ++ newline) ++
  pp_memories (n.+1) s.(s_mems) ++
  indent n ("tables" ++ newline) ++
  pp_tables (n.+1) s.(s_tables).

(* XXX disambiguate between cfg/res tuple with/without hs? *)
Definition pp_config_tuple_except_store (cfg : store_record * frame * list administrative_instruction) : string :=
  let '(s, f, es) := cfg in
  pp_administrative_instructions 0 es ++
  "with values " ++ pp_values_hint_empty f.(f_locs) ++ newline.

Definition pp_cfg_tuple_ctx_except_store (cfg: cfg_tuple_ctx) : string :=
  let '(s, ccs, sc, oe) := cfg in
  pp_administrative_instructions 0 (ccs ⦃ sc ⦃ olist oe ⦄ ⦄).

Definition pp_res_cfg_except_store {hs: host_state} {cfg: cfg_tuple_ctx} (res: run_step_ctx_result hs cfg) : string :=
  match res with
  | RSC_normal hs' cfg' _ =>
      "Reduction to:" ++ newline ++ pp_cfg_tuple_ctx_except_store cfg' ++ newline
  | RSC_value _ _ vs _ _ _ =>
      "Value:" ++ newline ++ pp_values vs ++ newline
  | RSC_value_frame _ _ vs _ _ _ _ _ =>
      "Value (f):" ++ newline ++ pp_values vs ++ newline
  | RSC_invalid _ =>
      "Invalid context. This should not happen when executing a module start function. Please report a bug if this error arises during invocation of module start functions." ++ newline
  | RSC_error _ =>
      "Ill-typed input configuration"
  end.

End Host.

(** As-is, [eqType] tends not to extract well.
  This section provides alternative definitions for better extraction. **)
Module PP.

Import DummyHost.
  
Section Show.

Definition pp_values := pp_values.

Definition pp_store := pp_store.

Definition pp_cfg_tuple_ctx_except_store := pp_cfg_tuple_ctx_except_store.

Definition pp_res_cfg_except_store {hs: host_state} {cfg: cfg_tuple_ctx} (res: run_step_ctx_result hs cfg) := pp_res_cfg_except_store res.

Definition pp_administrative_instructions := pp_administrative_instructions.

End Show.

End PP.

