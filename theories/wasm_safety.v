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

Inductive reduce_star : store_record -> list value -> list administrative_instruction -> nat -> store_record -> list value -> list administrative_instruction -> Prop :=
| reduce_refl : forall s vs es i, reduce_star s vs es i s vs es
| reduce_step : forall s vs es i s' vs' es' s'' vs'' es'',
    reduce s vs es i s' vs' es' ->
    reduce_star s' vs' es' i s'' vs'' es'' ->
    reduce_star s vs es i s'' vs'' es''.

Axiom safety :
  (* TODO *)
  forall i s vs es ts,
    config_typing i s vs es ts ->
    (exists s' vs' es', (const_list es' \/ es' = [::Trap]) /\ reduce_star s vs es i s' vs' es') \/
    (exists sn vsn esn, sn 0 = s /\ vsn 0 = vs /\ esn 0 = es /\
                        forall n, reduce (sn n) (vsn n) (esn n) i (sn n.+1) (vsn n.+1) (esn n.+1)).
