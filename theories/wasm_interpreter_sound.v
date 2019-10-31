(* soundness of the Wasm interpreter *)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp
Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import wasm wasm_opsem wasm_interpreter.

Axiom run_step_soundness : forall d i s vs es s' vs' es',
    wasm_interpreter.run_step d i (s, vs, es) = (s', vs', RS_normal es') ->
    exists j,
      reduce s vs es j s' vs' es'.
(* TODO *)
