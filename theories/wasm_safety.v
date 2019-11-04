(* safety of Wasm *)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp
Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import wasm wasm_typing wasm_type_checker wasm_opsem.

Axiom progress :
  (* TODO *)
  forall i s vs es ts,
  config_typing i s vs es ts ->
  const_list es \/
  es = [::Trap] \/
  (exists s' vs' es', reduce s vs es i s' vs' es').

Axiom preservation :
  (* TODO *)
  forall i s vs es ts s' vs' es',
  config_typing i s vs es ts ->
  reduce s vs es i s' vs' es' ->
  config_typing i s' vs' es' ts.

Axiom safety : True.
  (* TODO *)
