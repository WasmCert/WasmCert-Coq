(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Minimal subset of CompCert's common/Memdata.v.

    coq-wasm uses only [encode_int] and [decode_int] from this module
    (for Wasm memory load/store byte encoding). The rest of the original
    Memdata.v (memory chunks, byte-level value encoding for CompCert's
    [Values.val] discriminated union, and all related lemmas) is not
    used and has been removed, along with its transitive deps on AST.v,
    Values.v, and Errors.v. The four definitions kept below are unchanged
    from the upstream file. *)

From Coq Require Import List ZArith.
From compcert Require Import Integers.
From compcert Require Archi.

(** Reverse a byte list on big-endian hosts (no-op on little-endian).
    coq-wasm's vendored Archi.v hardcodes [big_endian = false], so in
    practice this is the identity, but we keep the conditional for
    semantic equivalence with the original CompCert function. *)
Definition rev_if_be (l: list byte) : list byte :=
  if Archi.big_endian then List.rev l else l.

(** Encode an integer [x] as a list of [n] little-endian bytes. *)
Fixpoint bytes_of_int (n: nat) (x: Z) {struct n}: list byte :=
  match n with
  | O => nil
  | S m => Byte.repr x :: bytes_of_int m (x / 256)
  end.

(** Decode a list of little-endian bytes into an integer. *)
Fixpoint int_of_bytes (l: list byte): Z :=
  match l with
  | nil => 0
  | b :: l' => Byte.unsigned b + int_of_bytes l' * 256
  end.

Definition encode_int (sz: nat) (x: Z) : list byte :=
  rev_if_be (bytes_of_int sz x).

Definition decode_int (b: list byte) : Z :=
  int_of_bytes (rev_if_be b).
