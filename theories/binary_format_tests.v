(** Tests for the binary parser. **)
Require Import Byte.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_printer bytes_pp
                         datatypes_properties check_toks pp.

Open Scope string_scope.
Import Coq.Strings.String.StringSyntax.
Open Scope list_scope.

Lemma test_unreachable : check_toks (x00 :: nil) parse_be = Running.Singleton Unreachable.
Proof. vm_compute. reflexivity. Qed.

Lemma test_nop : check_toks (x01 :: nil) parse_be = Running.Singleton Nop.
Proof. vm_compute. reflexivity. Qed.

(** An example program. **)
Definition test :=
  If (Tf nil nil) (Testop T_i64 Eqz :: nil) (Testop T_i64 Eqz :: nil).

(** Its byte representation. **)
Definition test_bytes : list Byte.byte :=
  x04 :: x40
  :: x50
  :: x05
  :: x50
  :: x0b
  :: x0b
  :: nil.

(** It is possible to display lists of bytes in a nice way using the following command:
[[
Compute hex_small_no_prefix_of_bytes test_bytes.
]]
**)

Lemma text_binary_correct : binary_of_expr (test :: nil) = test_bytes.
Proof. vm_compute. reflexivity. Qed.

Lemma text_parse_correct : run_parse_expr test_bytes = Some (test :: nil).
Proof. vm_compute. reflexivity. Qed.

(** It is possible to display programs in a nice way using the following command:
[[
Compute option_map pp_basic_instructions (run_parse_expr test_bytes).
]]
**)

(** Example from Wikipedia: https://en.wikipedia.org/wiki/WebAssembly#Code_representation
  This is the representation of a factorial function. **)
Definition test_wikipedia_byte : list Byte.byte :=
  x20 :: x00
  :: x50
  :: x04 :: x7e
  :: x42 :: x01
  :: x05
  :: x20 :: x00
  :: x20 :: x00
  :: x42 :: x01
  :: x7d
  :: x10 :: x00
  :: x7e
  :: x0b
  :: nil.

Definition test_wikipedia :=
  (Get_local 0
   :: Testop T_i64 Eqz
   :: If (Tf nil (T_i64 :: nil))
        (EConst (ConstInt64 Wasm_int.Int64.one) :: nil)
        (Get_local 0
         :: Get_local 0
         :: EConst (ConstInt64 Wasm_int.Int64.one)
         :: Binop_i T_i64 Sub
         :: Call 0
         :: Binop_i T_i64 Mul :: nil) :: nil).

Lemma test_wikipedia_correct : run_parse_bes test_wikipedia_byte = Some test_wikipedia.
Proof. vm_compute. reflexivity. Qed.

Definition empty_module := {|
  mod_types := nil;
  mod_funcs := nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elem := nil;
  mod_data := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma empty_module_round_trip : run_parse_module (binary_of_module empty_module) = Some empty_module.
Proof. vm_compute. reflexivity. Qed.

Definition module_type := {|
  mod_types := cons (Tf nil (cons T_i32 nil)) nil;
  mod_funcs := nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elem := nil;
  mod_data := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma module_type_round_trip :
  run_parse_module (binary_of_module module_type) = Some module_type.
Proof. vm_compute. reflexivity. Qed.

Definition module_type_fun := {|
  mod_types := cons (Tf nil (cons T_i32 nil)) nil;
  mod_funcs :=
    cons {| mf_type := Mk_typeidx 0; mf_locals := nil; mf_body := nil |} nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elem := nil;
  mod_data := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma module_type_fun_round_trip :
  run_parse_module (binary_of_module module_type_fun) = Some module_type_fun.
Proof. vm_compute. reflexivity. Qed.

Definition module_42 := {|
  mod_types := cons (Tf nil (cons T_i32 nil)) nil;
  mod_funcs :=
    let e := EConst (ConstInt32 (Wasm_int.Int32.repr (BinInt.Z.of_nat 42))) in
    cons {| mf_type := Mk_typeidx 0; mf_locals := nil; mf_body := cons e nil |} nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elem := nil;
  mod_data := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma module_42_round_trip :
  run_parse_module (binary_of_module module_42) = Some module_42.
Proof. vm_compute. reflexivity. Qed.

Definition module_42_exported := {|
  mod_types := cons (Tf nil (cons T_i32 nil)) nil;
  mod_funcs :=
    let e := EConst (ConstInt32 (Wasm_int.Int32.repr (BinInt.Z.of_nat 42))) in
    cons {| mf_type := Mk_typeidx 0; mf_locals := nil; mf_body := cons e nil |} nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elem := nil;
  mod_data := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := cons {| exp_name := String.list_byte_of_string "hello"; exp_desc := ED_func (Mk_funcidx 0); |} nil;
|}.

Lemma module_42_exported_round_trip :
  run_parse_module (binary_of_module module_42_exported) = Some module_42_exported.
Proof. vm_compute. reflexivity. Qed.
