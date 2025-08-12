From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat.
From Coq Require Import BinInt BinNat NArith Lia Uint63.
From Wasm Require Import numerics bytes memory common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type SIMD_Type.

  Parameter v128: Type.

  Parameter v128_default: v128.

End SIMD_Type.

Module SIMD <: SIMD_Type.

  Definition v128 := bytes.

  Definition v128_default : v128 := nil.
  
End SIMD.
