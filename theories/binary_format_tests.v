(** Tests for the binary parser. **)
Require Import Byte Ascii.
From parseque Require Import Parseque.
Require Import binary_format_parser binary_format_printer bytes_pp
  datatypes_properties check_toks pp.
Open Scope string_scope.
Import Coq.Strings.String.StringSyntax.

Lemma test_unreachable : check_toks (x00 :: nil) parse_be = Running.Singleton Unreachable.
Proof. reflexivity. Qed.

Lemma test_nop : check_toks (x01 :: nil) parse_be = Running.Singleton Nop.
Proof. reflexivity. Qed.

Compute hex_small_no_prefix_of_bytes (binary_of_be (If (Tf nil nil) (Testop T_i64 Eqz :: nil) (Testop T_i64 Eqz :: nil))).

Definition test2 : list Byte.byte :=
  x04 :: x40
  :: x50
  :: x05
  :: x50
  :: x0b
  :: x0b
  :: nil.

Compute run_parse_expr test2.
Compute option_map pp_basic_instructions (run_parse_expr test2).

(** Example from Wikipedia: https://en.wikipedia.org/wiki/WebAssembly#Code_representation
  This is the representation of a factorial function. **)
Definition test_wikipedia : list Byte.byte :=
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

Compute option_map pp_basic_instructions (run_parse_bes test_wikipedia).

(*
Definition test_factorial :=
  Block (
    Get_local 0
    :: Get_local 0
    :: Testop T_i64 Eqz
    (* TODO: continue the translation: I don’t know how to encode this. *)
if (result i64)
    i64.const 1
else
    local.get 0
    local.get 0
    i64.const 1
    i64.sub
    call 0
    i64.mul
end
*)

(* TODO: The parser fails here! So either Wikipedia is wrong (and we have to update the article),
  or the parser is (and we have to update it) ☺
Lemma test_wikipedia_correct : check_toks test_wikipedia be = Singleton test_factorial.
Proof.
  reflexivity.
Qed.
*)
