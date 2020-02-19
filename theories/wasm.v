(** Wasm base definitions **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)
(* TODO: in serious need of cleaning up
 * - proofs have not been ported
 * - lots of axioms
 * - no validation
 * - variable order in inductive definitions is pretty much random
 *)

Require Export numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Variable host : eqType. (* TODO: Do the same as integers and floats. *)
Variable host_state : eqType.

Definition immediate := nat. (* i *)

Definition static_offset := nat. (* off *)

Definition alignment_exponent := nat. (* a *)

Definition uint8 := nat. (* TODO: What about [Byte.byte]? *)

Definition byte := uint8.
Variable byte_eqb : byte -> byte -> bool.

(* TODO: lots of stuff *)

Definition bytes := list byte.

Parameter serialise_i32 : i32 -> bytes.
Parameter serialise_i64 : i64 -> bytes.
Parameter serialise_f32 : f32 -> bytes.
Parameter serialise_f64 : f64 -> bytes.

Fixpoint bytes_takefill (a : byte) (n : nat) (aas : bytes) : bytes :=
  match n with
  | O => nil
  | S n' =>
    match aas with
    | nil => cons a (bytes_takefill a n' aas)
    | cons a' aas' => cons a' (bytes_takefill a n' aas')
    end
  end.

Fixpoint bytes_replicate (n : nat) (b : byte) : bytes :=
  match n with
  | 0 => [::]
  | n'.+1 => b :: bytes_replicate n' b
  end.

Fixpoint last {A} (l : list A) : option A :=
  match l with
  | [::] => None
  | [::x] => Some x
  | _ :: l' => last l'
  end.

Definition msbyte (bs : bytes) : option byte :=
  last bs.

Definition mem := list byte.

Definition read_bytes (m : mem) (n : nat) (l : nat) : bytes :=
  List.firstn l (List.skipn n m).

Definition write_bytes (m : mem) (n : nat) (bs : bytes) : mem :=
  app (List.firstn n m) (app bs (List.skipn (n + length bs) m)).

Definition mem_append (m : mem) (bs : bytes) := app m bs.

Inductive value_type : Type := (* t *)
| T_i32
| T_i64
| T_f32
| T_f64.

Scheme Equality for value_type.
Definition value_type_eqb v1 v2 := is_left (value_type_eq_dec v1 v2).
Definition eqvalue_typeP  : Equality.axiom value_type_eqb :=
  eq_dec_Equality_axiom value_type_eq_dec.

Canonical Structure value_type_eqMixin := EqMixin eqvalue_typeP.
Canonical Structure value_type_eqType := Eval hnf in EqType value_type value_type_eqMixin.

Inductive packed_type : Type := (* tp *)
| Tp_i8
| Tp_i16
| Tp_i32.

Inductive mutability : Type := (* mut *)
| T_immut
| T_mut.

Scheme Equality for mutability.
Definition mutability_eqb v1 v2 := is_left (mutability_eq_dec v1 v2).
Definition eqmutabilityP  : Equality.axiom mutability_eqb :=
  eq_dec_Equality_axiom mutability_eq_dec.

Canonical Structure mutability_eqMixin := EqMixin eqmutabilityP.
Canonical Structure mutability_eqType := Eval hnf in EqType mutability mutability_eqMixin.


Record global_type := (* tg *)
  { tg_mut : mutability; tg_t : value_type}.

Scheme Equality for global_type.
Definition global_type_eqb v1 v2 := is_left (global_type_eq_dec v1 v2).
Definition eqglobal_typeP  : Equality.axiom global_type_eqb :=
  eq_dec_Equality_axiom global_type_eq_dec.

Canonical Structure global_type_eqMixin := EqMixin eqglobal_typeP.
Canonical Structure global_type_eqType := Eval hnf in EqType global_type global_type_eqMixin.

Inductive function_type := (* tf *)
| Tf : list value_type -> list value_type -> function_type.

Definition function_type_eqb (tf1 tf2 : function_type) :=
  let: Tf vt11 vt12 := tf1 in
  let: Tf vt21 vt22 := tf2 in
  (vt11 == vt21) && (vt12 == vt22).

Lemma eqfunction_typeP : Equality.axiom function_type_eqb.
Proof.
  case=> tf11 tf12.
  case=> tf21 tf22.
  rewrite /function_type_eqb.
  case_eq (tf11 == tf21) => /= [/eqP-Hm|/eqP-Hm].
  {
    case_eq (tf12 == tf22) => /= [/eqP-Ht|/eqP-Ht].
    {
      apply/ReflectT.
      by subst.
    }
    {
      apply/ReflectF.
      move=> H.
      injection H => Ht2 Hm2.
      by subst.
    }
  }
  {
    apply/ReflectF.
    move=> H.
    injection H => _ Hm2.
    by subst.
  }
Qed.

Definition function_eq_dec := Equality_axiom_eq_dec eqfunction_typeP.

Canonical Structure function_type_eqMixin := EqMixin eqfunction_typeP.
Canonical Structure function_type_eqType :=
  Eval hnf in EqType function_type function_type_eqMixin.

Record t_context := {
  tc_types_t : list function_type;
  tc_func_t : list function_type;
  tc_global : list global_type;
  tc_table : option nat;
  tc_memory : option nat;
  tc_local : list value_type;
  tc_label : list (list value_type);
  tc_return : option (list value_type);
}.

Parameter t_context_eq_dec : forall x y : t_context, {x = y} + {x <> y}. (* TODO *)

Definition eqt_contextP := eq_dec_Equality_axiom t_context_eq_dec.

(*

Record s_context := {
  sc_inst : list t_context;
  sc_funcs : list function_type;
  sc_tab : list nat;
  sc_mem : list nat;
  sc_globs : list global_type;
}.

*)

Inductive sx : Type :=
| sx_S
| sx_U.

Scheme Equality for sx.
Definition sx_eqb v1 v2 := is_left (sx_eq_dec v1 v2).
Definition eqsxP  : Equality.axiom sx_eqb :=
  eq_dec_Equality_axiom sx_eq_dec.

Canonical Structure sx_eqMixin := EqMixin eqsxP.
Canonical Structure sx_eqType := Eval hnf in EqType sx sx_eqMixin.

Inductive unop_i : Type :=
| Clz
| Ctz
| Popcnt.

Inductive unop_f : Type :=
| Neg
| Abs
| Ceil
| Floor
| Trunc
| Nearest
| Sqrt.

Inductive binop_i : Type :=
| Add
| Sub
| Mul
| Div : sx -> binop_i
| Rem : sx -> binop_i
| And
| Or
| Xor
| Shl
| Shr : sx -> binop_i
| Rotl
| Rotr.

Inductive binop_f : Type :=
| Addf
| Subf
| Mulf
| Divf
| Min
| Max
| Copysign.

Inductive testop : Type :=
| Eqz.

Inductive relop_i : Type :=
| Eq
| Ne
| Lt : sx -> relop_i
| Gt : sx -> relop_i
| Le : sx -> relop_i
| Ge : sx -> relop_i.

Inductive relop_f : Type :=
| Eqf
| Nef
| Ltf
| Gtf
| Lef
| Gef.

Inductive cvtop : Type :=
| Convert
| Reinterpret.

Inductive value : Type := (* v *)
| ConstInt32 : i32 -> value
| ConstInt64 : i64 -> value
| ConstFloat32 : f32 -> value
| ConstFloat64 : f64 -> value.

Definition value_eqb (v1 v2 : value) : bool :=
  match v1, v2 with
  | ConstInt32 i1, ConstInt32 i2 => i1 == i2
  | ConstInt64 i1, ConstInt64 i2 => i1 == i2
  | ConstFloat32 f1, ConstFloat32 f2 => f1 == f2
  | ConstFloat64 f1, ConstFloat64 f2 => f1 == f2
  | _, _ => false
  end.

Lemma eqvalueP : Equality.axiom value_eqb.
Proof.
  do 2 case=> ?;
    by [ apply/ReflectF
       | apply/iffP; [ move=> /=; apply/eqP | move=> E; f_equal; exact: E | case ] ].
Qed.

Definition value_eq_dec := Equality_axiom_eq_dec eqvalueP.

Canonical Structure value_eqMixin := EqMixin eqvalueP.
Canonical Structure value_eqType := Eval hnf in EqType value value_eqMixin.

Inductive basic_instruction : Type := (* be *)
| Unreachable
| Nop
| Drop
| Select
| Block : function_type -> list basic_instruction -> basic_instruction
| Loop : function_type -> list basic_instruction -> basic_instruction
| If : function_type -> list basic_instruction -> list basic_instruction -> basic_instruction
| Br : immediate -> basic_instruction
| Br_if : immediate -> basic_instruction
| Br_table : list immediate -> immediate -> basic_instruction
| Return
| Call : immediate -> basic_instruction
| Call_indirect : immediate -> basic_instruction
| Get_local : immediate -> basic_instruction
| Set_local : immediate -> basic_instruction
| Tee_local : immediate -> basic_instruction
| Get_global : immediate -> basic_instruction
| Set_global : immediate -> basic_instruction
| Load : value_type -> option (packed_type * sx) -> alignment_exponent -> static_offset -> basic_instruction
| Store : value_type -> option packed_type -> alignment_exponent -> static_offset -> basic_instruction
| Current_memory
| Grow_memory
| EConst : value -> basic_instruction
| Unop_i : value_type -> unop_i -> basic_instruction
| Unop_f : value_type -> unop_f -> basic_instruction
| Binop_i : value_type -> binop_i -> basic_instruction
| Binop_f : value_type -> binop_f -> basic_instruction
| Testop : value_type -> testop -> basic_instruction
| Relop_i : value_type -> relop_i -> basic_instruction
| Relop_f : value_type -> relop_f -> basic_instruction
| Cvtop : value_type -> cvtop -> value_type -> option sx -> basic_instruction.

(* TODO:
Scheme Equality for basic_instruction.
Definition eqglobal_typeP := eq_dec_Equality_axiom global_type_eq_dec.
*)
Variable basic_instruction_eqb : basic_instruction -> basic_instruction -> bool.

Parameter eqbasic_instructionP : Equality.axiom basic_instruction_eqb.

Canonical Structure basic_instruction_eqMixin := EqMixin eqbasic_instructionP.
Canonical Structure basic_instruction_eqType :=
  Eval hnf in EqType basic_instruction basic_instruction_eqMixin.

Record instance : Type := (* inst *) {
  i_types : list function_type;
  i_funcs : list immediate;
  i_tab : option immediate;
  i_mem : option immediate;
  i_globs : list immediate;
}.

Definition instance_eqb (i1 i2 : instance) : bool :=
  (i_types i1 == i_types i2)
    &&
    (i_funcs i1 == i_funcs i2)
    &&
    (i_tab i1 == i_tab i2)
    &&
    (i_mem i1 == i_mem i2)
    &&
    (i_globs i1 == i_globs i2)
.

Lemma eqinstanceP : Equality.axiom instance_eqb.
Proof.
  move=> i1 i2. case: i1; case: i2; intros;
    by [ apply/ReflectF
       | move=> /=; apply/iffP;
         [ apply andP
         | repeat (case; move/andP); case; repeat move/eqP => ?; f_equal
         | inversion 1; subst; repeat (split=> //; apply/andP) ] ].
Qed.

Definition instance_eq_dec := Equality_axiom_eq_dec eqinstanceP.

Canonical Structure instance_eqMixin := EqMixin eqinstanceP.
Canonical Structure instance_eqType := Eval hnf in EqType instance instance_eqMixin.

Inductive function_closure : Type := (* cl *)
| Func_native : instance -> function_type -> list value_type -> list basic_instruction -> function_closure
| Func_host : function_type -> host -> function_closure.

Definition function_closure_eqb (cl1 cl2 : function_closure) : bool :=
  match (cl1, cl2) with
  | (Func_native i1 tf1 vs1 eis1, Func_native i2 tf2 vs2 eis2) =>
    (i1 == i2) && (tf1 == tf2) && (vs1 == vs2) && (eis1 == eis2)
  | (Func_host tf1 h1, Func_host tf2 h2) =>
    (tf1 == tf2) && (h1 == h2)
  | _ => false
  end.

Parameter eqfunction_closureP : Equality.axiom function_closure_eqb.
(* TODO *)
Canonical Structure function_closure_eqMixin := EqMixin eqfunction_closureP.
Canonical Structure function_closure_eqType := Eval hnf in EqType function_closure function_closure_eqMixin.


Definition tabinst := list (option function_closure).

Record global : Type := {
  g_mut : mutability;
  g_val : value;
}.

Definition global_eqb (g1 g2 : global) : bool :=
  (g_mut g1 == g_mut g2) && (g_val g1 == g_val g2).

Lemma eqglobalP : Equality.axiom global_eqb.
Proof.
  move=> g1 g2.
  case: g1 => m1 t1; case: g2 => m2 t2.
  case_eq (m1 == m2) => [Hm|Hm].
  {
    case_eq (t1 == t2) => [Ht|Ht].
    {
      rewrite /global_eqb /=.
      rewrite Hm Ht.
      apply ReflectT.
      move/eqP: Hm => Hm.
      move/eqP: Ht => Ht.
      by subst.
    }
    {
      rewrite /global_eqb /=.
      rewrite Hm Ht.
      apply ReflectF.
      move=> H.
      injection H => Ht2 Hm2.
      subst.
      by rewrite eqxx in Ht.
    }
  }
  {
    rewrite /global_eqb /=.
    rewrite Hm.
    apply/ReflectF.
    move=> H.
    injection H => _ Hm2.
    subst.
    by rewrite eqxx in Hm.
  }
Qed.

Definition global_eq_dec := Equality_axiom_eq_dec eqglobalP.

Canonical Structure global_eqMixin := EqMixin eqglobalP.
Canonical Structure global_eqType := Eval hnf in EqType global global_eqMixin.


Record store_record : Type := (* s *) {
  s_funcs : list function_closure;
  s_tab : list tabinst;
  s_mem : list mem;
  s_globs : list global;
}.

Definition store_record_eqb (s1 s2 : store_record) : bool :=
  (s_funcs s1 == s_funcs s2) && (s_tab s1 == s_tab s2) && (s_mem s1 == s_mem s2) && (s_globs s1 == s_globs s2).

Lemma eqstore_recordP : Equality.axiom store_record_eqb.
Proof.
  move=> s1 s2. case: s1; case: s2; intros;
    by [ apply/ReflectF
       | move=> /=; apply/iffP;
         [ apply andP
         | repeat (case; move/andP); case; repeat move/eqP => ?; f_equal
         | inversion 1; subst; repeat (split=> //; apply/andP) ] ].
Qed.

Definition store_record_eq_dec := Equality_axiom_eq_dec eqstore_recordP.

Canonical Structure store_record_eqMixin := EqMixin eqstore_recordP.
Canonical Structure store_record_eqType := Eval hnf in EqType store_record store_record_eqMixin.

Definition upd_s_mem (s : store_record) (m : list mem) : store_record :=
  Build_store_record
    (s_funcs s)
    (s_tab s)
    m
    (s_globs s).

Inductive administrative_instruction : Type := (* e *)
| Basic : basic_instruction -> administrative_instruction
| Trap
| Callcl : function_closure -> administrative_instruction
| Label : nat -> list administrative_instruction -> list administrative_instruction -> administrative_instruction
| Local : nat -> instance -> list value -> list administrative_instruction -> administrative_instruction.

Fixpoint administrative_instruction_eqb (e1 e2 : administrative_instruction) : bool :=
  let fff :=
      (fix f (l1 l2 : list administrative_instruction) :=
         match l1, l2 with
         | nil, nil => true
         | cons _ _, nil => false
         | nil, cons _ _ => false
         | cons x xs, cons y ys => (administrative_instruction_eqb x y) && (f xs ys)
         end
      ) in
  match e1, e2 with
  | Basic be1, Basic be2 => be1 == be2
  | Trap, Trap => true
  | Callcl cl1, Callcl cl2 => cl1 == cl2
  | Label n1 es11 es12, Label n2 es21 es22 =>
    (Nat.eqb n1 n2) &&
    (fff es11 es21) &&
    (fff es12 es22)
  | Local n1 i1 vs1 es1, Local n2 i2 vs2 es2 =>
    (Nat.eqb n1 n2) &&
    (instance_eqb i1 i2) &&
    (vs1 == vs2) &&
    (fff es1 es2)
  | _, _ => (* TODO *) false
  end.

Parameter eqadministrative_instructionP : Equality.axiom administrative_instruction_eqb.
(* TODO *)
Canonical Structure administrative_instruction_eqMixin := EqMixin eqadministrative_instructionP.
Canonical Structure administrative_instruction_eqType := Eval hnf in EqType administrative_instruction administrative_instruction_eqMixin.


Inductive lholed : Type :=
| LBase : list administrative_instruction -> list administrative_instruction -> lholed
| LRec : list administrative_instruction -> nat -> list administrative_instruction -> lholed -> list administrative_instruction -> lholed.


Definition mem_size (m : mem) :=
  length m.

Definition mem_grow (m : mem) (n : nat) :=
 m ++ bytes_replicate (n * 64000) 0.

Definition load (m : mem) (n : nat) (off : static_offset) (l : nat) : option bytes :=
  if mem_size m >= (n + off + l)
  then Some (read_bytes m (n + off) l)
  else None.

Definition sign_extend (s : sx) (l : nat) (bs : bytes) : bytes :=
  (* TODO *) bs.
(* TODO
  let msb := msb (msbyte bytes) in
  let byte := (match sx with sx_U => O | sx_S => if msb then -1 else 0) in
  bytes_takefill byte l bytes
*)

Definition load_packed (s : sx) (m : mem) (n : nat) (off : static_offset) (lp : nat) (l : nat) : option bytes :=
  option_map (sign_extend s l) (load m n off lp).

Definition store (m : mem) (n : nat) (off : static_offset) (bs : bytes) (l : nat) : option mem :=
  if (mem_size m) >= (n + off + l)
  then Some (write_bytes m (n + off) (bytes_takefill O l bs))
  else None.

Definition store_packed := store.

(* TODO: The whole host should be defined as a mixin in a separate file. *)
Parameter wasm_deserialise : bytes -> value_type -> value.

Parameter host_apply : store_record -> function_type -> host -> list value -> host_state -> option (store_record * list value).

Definition typeof (v : value) : value_type :=
  match v with
  | ConstInt32 _ => T_i32
  | ConstInt64 _ => T_i64
  | ConstFloat32 _ => T_f32
  | ConstFloat64 _ => T_f64
  end.

Definition option_projl (A B : Type) (x : option (A * B)) : option A :=
  option_map fst x.

Definition option_projr (A B : Type) (x : option (A * B)) : option B :=
  option_map snd x.

Definition t_length (t : value_type) : nat :=
  match t with
  | T_i32 => 4
  | T_i64 => 8
  | T_f32 => 4
  | T_f64 => 8
  end.

Definition tp_length (tp : packed_type) : nat :=
  match tp with
  | Tp_i8 => 1
  | Tp_i16 => 2
  | Tp_i32 => 4
  end.

Definition is_int_t (t : value_type) : bool :=
  match t with
  | T_i32 => true
  | T_i64 => true
  | T_f32 => false
  | T_f64 => false
  end.

Definition is_float_t (t : value_type) : bool :=
  match t with
  | T_i32 => false
  | T_i64 => false
  | T_f32 => true
  | T_f64 => true
  end.

Definition is_mut (tg : global_type) : bool :=
  tg_mut tg == T_mut.


Definition app_unop_i (e : Wasm_int.type) (iop : unop_i) (c : Wasm_int.sort e) : Wasm_int.sort e :=
  (let: Wasm_int.Pack u (Wasm_int.Class eqmx intmx) as e' := e return Wasm_int.sort e' -> Wasm_int.sort e' in
  match iop with
  | Ctz => Wasm_int.int_ctz intmx
  | Clz => Wasm_int.int_clz intmx
  | Popcnt => Wasm_int.int_popcnt intmx
  end) c.

Definition app_unop_f (e : Wasm_float.type) (fop : unop_f) (c : Wasm_float.sort e) : Wasm_float.sort e :=
  (let: Wasm_float.Pack u (Wasm_float.Class eqmx mx) as e' := e return Wasm_float.sort e' -> Wasm_float.sort e' in
  match fop with
  | Neg => Wasm_float.float_neg mx
  | Abs => Wasm_float.float_abs mx
  | Ceil => Wasm_float.float_ceil mx
  | Floor => Wasm_float.float_floor mx
  | Trunc => Wasm_float.float_trunc mx
  | Nearest => Wasm_float.float_nearest mx
  | Sqrt => Wasm_float.float_sqrt mx
  end) c.

(* TODO: can't be bothered to make this nicer *)
Definition app_binop_i (e : Wasm_int.type) (iop : binop_i) (c1 c2 : Wasm_int.sort e) : option (Wasm_int.sort e) :=
  (let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e return Wasm_int.sort e' -> Wasm_int.sort e' -> option (Wasm_int.sort e') in
  match iop with
  | Add => fun c1 c2 => Some (Wasm_int.int_add mx c1 c2)
  | Sub => fun c1 c2 => Some (Wasm_int.int_sub mx c1 c2)
  | Mul => fun c1 c2 => Some (Wasm_int.int_mul mx c1 c2)
  | Div sx_U => Wasm_int.int_div_u mx
  | Div sx_S => Wasm_int.int_div_s mx
  | Rem sx_U => Wasm_int.int_rem_u mx
  | Rem sx_S => Wasm_int.int_rem_s mx
  | And => fun c1 c2 => Some (Wasm_int.int_and mx c1 c2)
  | Or => fun c1 c2 => Some (Wasm_int.int_or mx c1 c2)
  | Xor => fun c1 c2 => Some (Wasm_int.int_xor mx c1 c2)
  | Shl => fun c1 c2 => Some (Wasm_int.int_shl mx c1 c2)
  | Shr sx_U => fun c1 c2 => Some (Wasm_int.int_shr_u mx c1 c2)
  | Shr sx_S => fun c1 c2 => Some (Wasm_int.int_shr_s mx c1 c2)
  | Rotl => fun c1 c2 => Some (Wasm_int.int_rotl mx c1 c2)
  | Rotr => fun c1 c2 => Some (Wasm_int.int_rotr mx c1 c2)
  end) c1 c2.

(* TODO: can't be bothered to make this nicer *)
Definition app_binop_f (e : Wasm_float.type) (fop : binop_f) (c1 c2 : Wasm_float.sort e) : option (Wasm_float.sort e) :=
    (let: Wasm_float.Pack u (Wasm_float.Class _ mx) as e' := e return Wasm_float.sort e' -> Wasm_float.sort e' -> option (Wasm_float.sort e') in
  match fop with
  | Addf => fun c1 c2 => Some (Wasm_float.float_add mx c1 c2)
  | Subf => fun c1 c2 => Some (Wasm_float.float_sub mx c1 c2)
  | Mulf => fun c1 c2 => Some (Wasm_float.float_mul mx c1 c2)
  | Divf => fun c1 c2 => Some (Wasm_float.float_div mx c1 c2)
  | Min => fun c1 c2 => Some (Wasm_float.float_min mx c1 c2)
  | Max => fun c1 c2 => Some (Wasm_float.float_max mx c1 c2)
  | Copysign => fun c1 c2 => Some (Wasm_float.float_copysign mx c1 c2)
  end) c1 c2.

Definition app_testop_i (e : Wasm_int.type) (o : testop) (c : Wasm_int.sort e) : bool :=
  (let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e return Wasm_int.sort e' -> bool in
  match o with
  | Eqz => fun c => Wasm_int.int_eqz mx c
  end) c.

Definition app_relop_i (e : Wasm_int.type) (rop : relop_i) (c1 c2 : Wasm_int.sort e) : bool :=
  (let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e return Wasm_int.sort e' -> Wasm_int.sort e' -> bool in
  match rop with
  | Eq => fun c1 c2 => Wasm_int.int_eq mx c1 c2
  | Ne => fun c1 c2 => Wasm_int.int_ne c1 c2
  | Lt sx_U => fun c1 c2 => Wasm_int.int_lt_u mx c1 c2
  | Lt sx_S => fun c1 c2 => Wasm_int.int_lt_s mx c1 c2
  | Gt sx_U => fun c1 c2 => Wasm_int.int_gt_u mx c1 c2
  | Gt sx_S => fun c1 c2 => Wasm_int.int_gt_s mx c1 c2
  | Le sx_U => fun c1 c2 => Wasm_int.int_le_u mx c1 c2
  | Le sx_S => fun c1 c2 => Wasm_int.int_le_s mx c1 c2
  | Ge sx_U => fun c1 c2 => Wasm_int.int_ge_u mx c1 c2
  | Ge sx_S => fun c1 c2 => Wasm_int.int_ge_s mx c1 c2
  end) c1 c2.

Definition app_relop_f (e : Wasm_float.type) (rop : relop_f) (c1 c2 : Wasm_float.sort e) : bool :=
  (let: Wasm_float.Pack u (Wasm_float.Class _ mx) as e' := e return Wasm_float.sort e' -> Wasm_float.sort e' -> bool in
  match rop with
  | Eqf => fun c1 c2 => Wasm_float.float_eq mx c1 c2
  | Nef => fun c1 c2 => Wasm_float.float_ne c1 c2
  | Ltf => fun c1 c2 => Wasm_float.float_lt mx c1 c2
  | Gtf => fun c1 c2 => Wasm_float.float_gt mx c1 c2
  | Lef => fun c1 c2 => Wasm_float.float_le mx c1 c2
  | Gef => fun c1 c2 => Wasm_float.float_ge mx c1 c2
  end) c1 c2.

Definition types_agree (t : value_type) (v : value) : bool :=
  (typeof v) == t.

Definition cl_type (cl : function_closure) : function_type :=
  match cl with
  | Func_native _ tf _ _ => tf
  | Func_host tf _ => tf
  end.

Definition rglob_is_mut (g : global) : bool :=
  g_mut g == T_mut.

Definition option_bind (A B : Type) (f : A -> option B) (x : option A) :=
  match x with
  | None => None
  | Some y => f y
  end.

Definition stypes (s : store_record) (i : instance) (j : nat) : option function_type :=
  (List.nth_error (i_types i) j).
(* TODO: optioned *)

Definition sfunc_ind (s : store_record) (i : instance) (j : nat) : option nat :=
  List.nth_error (i_funcs i) j.

Definition sfunc (s : store_record) (i : instance) (j : nat) : option function_closure :=
  option_bind (List.nth_error (s_funcs s)) (sfunc_ind s i j).

Definition sglob_ind (s : store_record) (i : instance) (j : nat) : option nat :=
  (List.nth_error (i_globs i) j).

Definition sglob (s : store_record) (i : instance) (j : nat) : option global :=
  option_bind (List.nth_error (s_globs s))
    (sglob_ind s i j).

Definition sglob_val (s : store_record) (i : instance) (j : nat) : option value :=
  option_map g_val (sglob s i j).

Definition smem_ind (s : store_record) (i : instance) : option nat :=
  i_mem i.

Definition stab_s (s : store_record) (i j : nat) : option function_closure :=
  let stabinst := List.nth_error (s_tab s) i in
  option_bind (fun x => x) (
  option_bind
    (fun stabinst => if length stabinst > j then List.nth_error stabinst j else None)
    stabinst).

Definition stab (s : store_record) (i : instance) (j : nat) : option function_closure :=
  if i_tab i is Some k then stab_s s k j else None.

Definition update_list_at {A : Type} (l : list A) (k : nat) (a : A) :=
  List.firstn k l ++ [::a] ++ List.skipn (k + 1) l.

Definition supdate_glob_s (s : store_record) (k : nat) (v : value) : option store_record :=
  option_map
    (fun g =>
      let g' := Build_global (g_mut g) v in
      let gs' := update_list_at (s_globs s) k g' in
      Build_store_record (s_funcs s) (s_tab s) (s_mem s) gs')
    (List.nth_error (s_globs s) k).

Definition supdate_glob (s : store_record) (i : instance) (j : nat) (v : value) : option store_record :=
  option_bind
    (fun k => supdate_glob_s s k v)
    (sglob_ind s i j).

Definition is_const (e : administrative_instruction) : bool :=
  if e is Basic _ then true else false.

Definition const_list (es : list administrative_instruction) : bool :=
  List.forallb is_const es.

Definition store_extension (s s' : store_record) : bool :=
  (s_funcs s == s_funcs s') &&
  (s_tab s == s_tab s') &&
  (all2 (fun bs bs' => mem_size bs <= mem_size bs') (s_mem s) (s_mem s')) &&
  (s_globs s == s_globs s').

Definition to_e_list (bes : list basic_instruction) : list administrative_instruction :=
  map Basic bes.

Definition v_to_e_list (ves : list value) : list administrative_instruction :=
  map (fun v => Basic (EConst v)) ves.

Fixpoint lfill (k : nat) (lh : lholed) (es : list administrative_instruction) : option (list administrative_instruction) :=
  match k with
  | 0 =>
    if lh is LBase vs es' then
      if const_list vs then Some (app vs (app es es')) else None
    else None
  | k'.+1 =>
    if lh is LRec vs n es' lh' es'' then
      if const_list vs then
        if lfill k' lh' es is Some lfilledk then
          Some (app vs (cons (Label n es' lfilledk) es''))
        else None
      else None
    else None
  end.

Definition lfilled (k : nat) (lh : lholed) (es : list administrative_instruction) (es' : list administrative_instruction) : bool :=
  if lfill k lh es is Some es'' then es' == es'' else false.

Inductive lfilledInd : nat -> lholed -> list administrative_instruction -> list administrative_instruction -> Prop :=
| LfilledBase: forall vs es es',
    const_list vs ->
    lfilledInd 0 (LBase vs es') es (vs ++ es ++ es')
| LfilledRec: forall k vs n es' lh' es'' es LI,
    const_list vs ->
    lfilledInd k lh' es LI ->
    lfilledInd (k.+1) (LRec vs n es' lh' es'') es (vs ++ [ :: (Label n es' LI) ] ++ es'').

Lemma lfilled_Ind_Equivalent: forall k lh es LI,
    lfilled k lh es LI <-> lfilledInd k lh es LI.
Proof.
  move => k. split.
  - move: lh es LI. induction k; move => lh es LI HFix.
    + unfold lfilled in HFix. simpl in HFix. destruct lh => //=.
      * destruct (const_list l) eqn:HConst => //=.
        { replace LI with (l++es++l0); first by apply LfilledBase.
          symmetry. move: HFix. by apply/eqseqP. }
    + unfold lfilled in HFix. simpl in HFix. destruct lh => //=.
      * destruct (const_list l) eqn:HConst => //=.
        { destruct (lfill k lh es) eqn:HLF => //=.
          { replace LI with (l ++ [ :: (Label n l0 l2)] ++ l1).
          apply LfilledRec; first by [].
          apply IHk. unfold lfilled; first by rewrite HLF.
          symmetry. move: HFix. by apply/eqseqP. }
        }
  - move => HLF. induction HLF.
    + unfold lfilled. unfold lfill. by rewrite H.
    + unfold lfilled. unfold lfill. rewrite H. fold lfill.
      unfold lfilled in IHHLF. destruct (lfill k lh' es) => //=.
      * replace LI with l => //=.
        symmetry. by apply/eqseqP.
Qed.

Lemma lfilledP: forall k lh es LI,
    reflect (lfilledInd k lh es LI) (lfilled k lh es LI).
Proof.
  move => k lh es LI. destruct (lfilled k lh es LI) eqn:HLFBool.
  - apply ReflectT. by apply lfilled_Ind_Equivalent.
  - apply ReflectF. move => HContra. apply lfilled_Ind_Equivalent in HContra. by rewrite HLFBool in HContra.
Qed.

Fixpoint lfill_exact (k : nat) (lh : lholed) (es : list administrative_instruction) : option (list administrative_instruction) :=
  match k with
  | 0 =>
    if lh is LBase nil nil then Some es else None
  | k'.+1 =>
    if lh is LRec vs n es' lh' es'' then
      if const_list vs then
        if lfill_exact k' lh' es is Some lfilledk then
          Some (app vs (cons (Label n es' lfilledk) es''))
        else None
      else None
    else None
  end.

Definition lfilled_exact (k : nat) (lh : lholed) (es : list administrative_instruction) (es' : list administrative_instruction) : bool :=
  if lfill_exact k lh es is Some es'' then es' == es'' else false.

Definition load_store_t_bounds (a : alignment_exponent) (tp : option packed_type) (t : value_type) : bool :=
  match tp with
  | None => Nat.pow 2 a <= t_length t
  | Some tp' => (Nat.pow 2 a <= tp_length tp') && (tp_length tp' < t_length t) && (is_int_t t)
  end.

Definition cvt_i32 (s : option sx) (v : value) : option i32 :=
  match v with
  | ConstInt32 _ => None
  | ConstInt64 c => Some (wasm_wrap c)
  | ConstFloat32 c =>
    match s with
    | Some sx_U => Wasm_float.float_ui32_trunc f32m c
    | Some sx_S => Wasm_float.float_ui32_trunc f32m c
    | None => None
    end
  | ConstFloat64 c =>
    match s with
    | Some sx_U => Wasm_float.float_ui32_trunc f64m c
    | Some sx_S => Wasm_float.float_ui32_trunc f64m c
    | None => None
    end
  end.

Definition cvt_i64 (s : option sx) (v : value) : option i64 :=
  match v with
  | ConstInt32 c =>
    match s with
    | Some sx_U => Some (wasm_extend_u c)
    | Some sx_S => Some (wasm_extend_s c)
    | None => None
    end
  | ConstInt64 c => None
  | ConstFloat32 c =>
    match s with
    | Some sx_U => Wasm_float.float_ui64_trunc f32m c
    | Some sx_S => Wasm_float.float_si64_trunc f32m c
    | None => None
    end
  | ConstFloat64 c =>
    match s with
    | Some sx_U => Wasm_float.float_ui64_trunc f64m c
    | Some sx_S => Wasm_float.float_si64_trunc f64m c
    | None => None
    end
  end.

Definition cvt_f32 (s : option sx) (v : value) : option f32 :=
  match v with
  | ConstInt32 c =>
    match s with
    | Some sx_U => Some (Wasm_float.float_convert_ui32 f32m c)
    | Some sx_S => Some (Wasm_float.float_convert_si32 f32m c)
    | None => None
    end
  | ConstInt64 c =>
    match s with
    | Some sx_U => Some (Wasm_float.float_convert_ui64 f32m c)
    | Some sx_S => Some (Wasm_float.float_convert_si64 f32m c)
    | None => None
    end
  | ConstFloat32 c => None
  | ConstFloat64 c => Some (wasm_demote c)
  end.

Definition cvt_f64 (s : option sx) (v : value) : option f64 :=
  match v with
  | ConstInt32 c =>
    match s with
    | Some sx_U => Some (Wasm_float.float_convert_ui32 f64m c)
    | Some sx_S => Some (Wasm_float.float_convert_si32 f64m c)
    | None => None
    end
  | ConstInt64 c =>
    match s with
    | Some sx_U => Some (Wasm_float.float_convert_ui64 f64m c)
    | Some sx_S => Some (Wasm_float.float_convert_si64 f64m c)
    | None => None
    end
  | ConstFloat32 c => Some (wasm_promote c)
  | ConstFloat64 c => None
  end.


Definition cvt (t : value_type) (s : option sx) (v : value) : option value :=
  match t with
  | T_i32 => option_map ConstInt32 (cvt_i32 s v)
  | T_i64 => option_map ConstInt64 (cvt_i64 s v)
  | T_f32 => option_map ConstFloat32 (cvt_f32 s v)
  | T_f64 => option_map ConstFloat64 (cvt_f64 s v)
  end.

Definition bits (v : value) : bytes :=
  match v with
  | ConstInt32 c => serialise_i32 c
  | ConstInt64 c => serialise_i64 c
  | ConstFloat32 c => serialise_f32 c
  | ConstFloat64 c => serialise_f64 c
  end.

Definition bitzero (t : value_type) : value :=
  match t with
  | T_i32 => ConstInt32 (Wasm_int.int_zero i32m)
  | T_i64 => ConstInt64 (Wasm_int.int_zero i64m)
  | T_f32 => ConstFloat32 (Wasm_float.float_zero f32m)
  | T_f64 => ConstFloat64 (Wasm_float.float_zero f64m)
  end.

Definition n_zeros (ts : list value_type) : list value :=
  map bitzero ts.

(* TODO: lots of lemmas *)

