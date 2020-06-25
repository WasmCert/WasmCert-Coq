(* pretty-printer *)
Require Import Coq.Strings.String.
From compcert Require Import Floats.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import Coq.Init.Decimal.
Require Import bytes_pp datatypes interpreter.
Require BinNatDef.
Require Import ansi.

Open Scope string_scope.

Definition newline_char : Ascii.ascii := Ascii.ascii_of_byte Byte.x0a.

Definition newline : string := String newline_char EmptyString.

Fixpoint indent (i : nat) (s : string) : string :=
  match i with
  | 0 => s
  | S i' => "  " ++ indent i' s
  end.

Definition pp_value_type (vt : value_type) : string :=
  match vt with
  | T_i32 => "i32"
  | T_i64 => "i64"
  | T_f32 => "f32"
  | T_f64 => "f64"
  end.

Definition pp_block_tf tf : string :=
  match tf with
  | Tf nil nil => ""
  | Tf nil (cons vt nil) => " " ++ pp_value_type vt
  | Tf nil _ => " error!"
  | Tf _ _ => " error!"
  end.

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

Definition pp_immediate (i : immediate) : string :=
  (* TODO: it's not clear that's the right way to print it, but hey *)
  string_of_uint (Nat.to_uint i).

Definition pp_i32 i :=
  pp_immediate (BinIntDef.Z.to_nat (Wasm_int.Int32.unsigned i)).

Definition pp_i64 i :=
  pp_immediate (BinIntDef.Z.to_nat (Wasm_int.Int64.unsigned i)).

(* TODO: all this printing of floats business is highly dubious,
 * and completely untested *)
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
    pp_bools (Ascii.byte_of_ascii (Ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8) :: acc) bools'
  | b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::  nil =>
    Ascii.byte_of_ascii (Ascii.Ascii b1 b2 b3 b4 b5 b6 b7 false) :: acc
  | b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: nil =>
    Ascii.byte_of_ascii (Ascii.Ascii b1 b2 b3 b4 b5 b6 false false) :: acc
  | b1 :: b2 :: b3 :: b4 :: b5 :: nil =>
    Ascii.byte_of_ascii (Ascii.Ascii b1 b2 b3 b4 b5 false false false) :: acc
  | b1 :: b2 :: b3 :: b4 :: nil =>
    Ascii.byte_of_ascii (Ascii.Ascii b1 b2 b3 b4 false false false false) :: acc
  | b1 :: b2 :: b3 :: nil =>
    Ascii.byte_of_ascii (Ascii.Ascii b1 b2 b3 false false false false false) :: acc
  | b1 :: b2 :: nil =>
    Ascii.byte_of_ascii (Ascii.Ascii b1 b2 false false false false false false) :: acc
  | b1 :: nil =>
    Ascii.byte_of_ascii (Ascii.Ascii b1 false false false false false false false) :: acc
  end.

Definition pp_f32 (f : float32) : string :=
  match BinIntDef.Z.to_N ((Float32.to_bits f).(Integers.Int.intval)) with
  | BinNums.N0 => "0"
  | BinNums.Npos p =>
    bytes_pp.hex_small_no_prefix_of_bytes_compact (pp_bools nil (bool_list_of_pos nil p))
  end.

Definition pp_f64 (f : float) : string :=
  match BinIntDef.Z.to_N ((Float.to_bits f).(Integers.Int64.intval)) with
  | BinNums.N0 => "0"
  | BinNums.Npos p =>
    bytes_pp.hex_small_no_prefix_of_bytes_compact (pp_bools nil (bool_list_of_pos nil p))
  end.

Definition pp_const (v : value) : string :=
  match v with
  | ConstInt32 i => "i32.const " ++ pp_i32 i ++ newline
  | ConstInt64 i => "i64.const " ++ pp_i64 i ++ newline
  | ConstFloat32 f => "f32.const " ++ pp_f32 f ++ newline
  | ConstFloat64 f => "f64.const " ++ pp_f64 f ++ newline
  end.

Definition pp_unary_op_i (uoi : unop_i) : string :=
  match uoi with
  | Clz => "clz"
  | Ctz => "ctz"
  | Popcnt => "popcnt"
  end.

Definition pp_unary_op_f (uof : unop_f) : string :=
  match uof with
  | Neg => "neg"
  | Abs => "abs"
  | Ceil => "ceil"
  | Floor => "floor"
  | Trunc => "trunc"
  | Nearest => "nearest"
  | Sqrt => "sqrt"
  end.

Definition pp_sx (s : sx) : string :=
  match s with
  | SX_U => "u"
  | SX_S => "s"
  end.

Definition pp_binary_op_i (boi : binop_i) : string :=
  match boi with
  | Add => "add"
  | Sub => "sub"
  | Mul => "mul"
  | Div s => "div_" ++ pp_sx s
  | Rem s => "rem_" ++ pp_sx s
  | And => "and"
  | Or => "or"
  | Xor => "xor"
  | Shl => "shl"
  | Shr s => "shr_" ++ pp_sx s
  | Rotl => "rotl"
  | Rotr => "rotr"
  end.

Definition pp_binary_op_f (bof : binop_f) : string :=
  match bof with
  | Addf => "add"
  | Subf => "sub"
  | Mulf => "mul"
  | Divf => "div"
  | Min => "min"
  | Max => "max"
  | Copysign => "copysign"
  end.

Definition pp_rel_op_i (roi : relop_i) : string :=
  match roi with
  | Eq => "eq"
  | Ne => "ne"
  | Lt s => "lt_" ++ pp_sx s
  | Gt s => "gt_" ++ pp_sx s
  | Le s => "le_" ++ pp_sx s
  | Ge s => "ge_" ++ pp_sx s
  end.

Definition pp_rel_op_f (rof : relop_f) : string :=
  match rof with
  | Eqf => "eq"
  | Nef => "ne"
  | Ltf => "lt"
  | Gtf => "gt"
  | Lef => "ne"
  | Gef => "ge"
  end.

Definition pp_ao a o : string :=
  pp_immediate a ++ " " ++ pp_immediate o.

Definition pp_packing (p : packed_type) :=
  match p with
  | Tp_i8 => "8"
  | Tp_i16 => "16"
  | Tp_i32 => "32"
  end.

Definition pp_ps (ps : packed_type * sx) : string :=
  let '(p, s) := ps in
  pp_packing p ++ "_" ++ pp_sx s.

Fixpoint pp_basic_instruction (i : nat) (be : basic_instruction) : string :=
  let pp_basic_instructions bes i :=
    String.concat "" (List.map (pp_basic_instruction (S i)) bes) in
  match be with
  | Unreachable => indent i "unreachable" ++ newline
  | Nop => indent i "nop" ++ newline
  | Drop => indent i "drop" ++ newline
  | Select => indent i "select" ++ newline
  | Block tf bes =>
    indent i ("block" ++ pp_block_tf tf ++ newline)
    ++ pp_basic_instructions bes (S i)
    ++ indent i "end" ++ newline
  | Loop tf bes =>
    indent i ("loop" ++ pp_block_tf tf ++ newline)
    ++ pp_basic_instructions bes (S i)
    ++ indent i "end" ++ newline
  | If tf bes nil =>
    indent i ("if" ++ pp_block_tf tf ++ newline)
    ++ pp_basic_instructions bes (S i)
    ++ indent i "end" ++ newline
  | If tf bes1 bes2 =>
    indent i ("if" ++ pp_block_tf tf ++ newline)
    ++ pp_basic_instructions bes1 (S i)
    ++ indent i "else" ++ newline
    ++ pp_basic_instructions bes2 (S i)
    ++ indent i "end" ++ newline
  | Br x =>
    indent i ("br " ++ pp_immediate x ++ newline)
  | Br_if x =>
    indent i ("br_if " ++ pp_immediate x ++ newline)
  | Br_table is_ i =>
    indent i ("br_table " ++ String.concat " " (List.map pp_immediate is_) ++ " " ++ pp_immediate i ++ newline)
  | Return =>
    indent i "return" ++ newline
  | Call x =>
    indent i ("call " ++ pp_immediate x ++ newline)
  | Call_indirect x =>
    indent i ("call_indirect " ++ pp_immediate x ++ newline)
  | Get_local x =>
    indent i ("local.get " ++ pp_immediate x ++ newline)
  | Set_local x =>
    indent i ("local.set " ++ pp_immediate x ++ newline)
  | Tee_local x =>
    indent i ("local.tee " ++ pp_immediate x ++ newline)
  | Get_global x =>
    indent i ("global.get " ++ pp_immediate x ++ newline)
  | Set_global x =>
    indent i ("global.set " ++ pp_immediate x ++ newline)
  | Load vt None a o =>
    pp_value_type vt ++ ".load " ++ pp_ao a o
  | Load vt (Some ps) a o =>
    pp_value_type vt ++ ".load" ++ pp_ps ps ++ " " ++ pp_ao a o
  | Store vt None a o =>
    pp_value_type vt ++ ".store " ++ pp_ao a o
  | Store vt (Some p) a o =>
    pp_value_type vt ++ ".store" ++ pp_packing p ++ " " ++ pp_ao a o
  | Current_memory =>
    indent i "memory.size" ++ newline
  | Grow_memory =>
    indent i "memory.grow" ++ newline
  | EConst v =>
    indent i (pp_const v)
  | Unop_i vt uoi =>
    indent i (pp_value_type vt ++ "." ++ pp_unary_op_i uoi ++ newline)
  | Unop_f vt uof =>
    indent i (pp_value_type vt ++ "." ++ pp_unary_op_f uof ++ newline)
  | Binop_i vt boi =>
    indent i (pp_value_type vt ++ "." ++ pp_binary_op_i boi ++ newline)
  | Binop_f vt bof =>
    indent i (pp_value_type vt ++ "." ++ pp_binary_op_f bof ++ newline)
  | Testop vt Eqz =>
    indent i (pp_value_type vt ++ ".eqz" ++ newline)
  | Relop_i vt roi =>
    indent i (pp_value_type vt ++ "." ++ pp_rel_op_i roi ++ newline)
  | Relop_f vt rof =>
    indent i (pp_value_type vt ++ "." ++ pp_rel_op_f rof ++ newline)
  | Cvtop vt1 cvtop vt2 sxo => "?" ++ newline (* TODO: ??? *)
  end.

Definition pp_basic_instructions bes :=
  String.concat "" (List.map (pp_basic_instruction 0) bes).

Definition pp_function_closure (n : nat) (fc : function_closure) : string :=
  match fc with
  | Func_native i ft vs bes => indent n ("native" ++ newline) (* TODO: show *)
  | Func_host ft h => indent n ("host" ++ newline) (* TODO: show *)
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_uint (Nat.to_uint (BinNatDef.N.of_nat n)).

Fixpoint pp_administrative_instruction (n : nat) (e : administrative_instruction) : string :=
  match e with
  | Basic be => pp_basic_instruction n be
  | Trap => indent n ("trap" ++ newline)
  | Invoke fc =>
    indent n ("invoke" ++ newline) ++
    pp_function_closure (n.+1) fc
  | Label k es1 es2 =>
    indent n ("label " ++ string_of_nat k ++ newline) ++
    String.concat "" (List.map (pp_administrative_instruction (n.+1)) es1) ++
    indent n "label2" ++ newline ++ (* TODO: ??? *)
    String.concat "" (List.map (pp_administrative_instruction (n.+1)) es1) ++
    indent n ("end" ++ newline)
  | Local n i vs es =>
    indent n ("local" ++ newline) (* TODO: ??? *)
  end.

Definition pp_administrative_instructions (n : nat) (es : list administrative_instruction) : string :=
  String.concat "" (List.map (pp_administrative_instruction n) es).

Definition pp_values (vs : list value) : string :=
  String.concat " " (List.map pp_const vs).

Definition pp_values_hint_empty (vs : list value) : string :=
  match vs with
  | nil => "(empty)"
  | _ => pp_values vs
  end.

Definition pp_store (n : nat) (s : store_record) : string :=
  indent n ("TODO: store"). (* TODO *)

Definition pp_config_tuple (cfg : interpreter.config_tuple) : string :=
  let '(s, vs, es) := cfg in
  pp_administrative_instructions 0 es ++
  "with values " ++ pp_values_hint_empty vs ++ newline ++
  "and store" ++ newline ++
  pp_store 1 s.

Definition pp_res_tuple (res_cfg : interpreter.res_tuple) : string :=
  let '(s, vs, res) := res_cfg in
  match res with
  | RS_crash _ => "crash" ++ newline ++
    "with values " ++ pp_values_hint_empty vs ++ newline ++
    "and store" ++ newline ++
    pp_store 1 s
  | RS_break n vs => "break " ++ string_of_nat n ++ "  " ++ pp_values_hint_empty vs ++ newline ++
    "with values " ++ pp_values_hint_empty vs ++ newline ++
    "and store" ++ newline ++
    pp_store 1 s
  | RS_return vs_res => "return " ++ pp_values_hint_empty vs_res ++ newline ++
    "with values " ++ pp_values_hint_empty vs ++ newline ++
    "and store" ++ newline ++
    pp_store 1 s
  | RS_normal es =>
    "normal" ++ newline ++
    String.concat "" (List.map (pp_administrative_instruction 1) es) ++
    "with values " ++ pp_values_hint_empty vs ++ newline ++
    "and store" ++ newline ++
    pp_store 1 s
  end.
