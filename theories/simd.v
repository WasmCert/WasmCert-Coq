From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat.
From Coq Require Import BinInt BinNat NArith Lia Uint63 String.
From Wasm Require Import numerics bytes memory common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type SIMD_Type.

  Parameter v128: Type.

  Parameter v128_default: v128.

  Parameter encode_v128 : v128 -> string.
  Parameter decode_v128 : string -> v128.

End SIMD_Type.

Module SIMD <: SIMD_Type.

  Definition v128 := bytes.

  Definition v128_default : v128 := nil.

Definition encode_v128 bs :=
  let coq_bytes :=
    List.map byte_of_compcert_byte bs in
  string_of_list_byte coq_bytes.

Definition decode_v128 s :=
  let bs := list_byte_of_string s in
    List.map compcert_byte_of_byte bs.

Lemma decode_encode_v128: forall v,
    decode_v128 (encode_v128 v) = v.
Proof.
  induction v => //=.
  unfold decode_v128, encode_v128 in *.
  rewrite list_byte_of_string_of_list_byte => /=.
  rewrite list_byte_of_string_of_list_byte in IHv => /=.
  rewrite IHv.
  f_equal.
  by rewrite compcert_byte_roundtrip.
Qed.

Lemma encode_decode_v128: forall s,
    encode_v128 (decode_v128 s) = s.
Proof.
  induction s => //=.
  unfold decode_v128, encode_v128 in * => /=.
  rewrite coq_byte_roundtrip => /=.
  cbn; f_equal.
  - by rewrite Ascii.ascii_of_byte_of_ascii.
  - by apply IHs. 
Qed.

End SIMD.

Module Export simd_export := SIMD.

