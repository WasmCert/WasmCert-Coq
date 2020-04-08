(** safety of Wasm **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp
Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import operations typing type_checker opsem.


Section Host.

Variable host_function : eqType.
Variable host_instance : host host_function.

Let host_state := host_state host_instance.
Let store_record := store_record host_function.
Let administrative_instruction := administrative_instruction host_function.
Let reduce := @reduce _ host_instance.

Lemma progress : forall i s vs es ts hs,
  config_typing i s vs es ts ->
  const_list es \/
  es = [::Trap] \/
  (exists s' vs' es' hs', reduce hs s vs es i hs' s' vs' es').
Admitted. (* TODO *)

Lemma preservation : forall i s vs es ts s' vs' es' hs hs',
  config_typing i s vs es ts ->
  reduce hs s vs es i hs' s' vs' es' ->
  config_typing i s' vs' es' ts.
Admitted. (* TODO *)

Inductive reduce_star : host_state -> store_record -> list value -> list administrative_instruction -> instance ->
                        host_state -> store_record -> list value -> list administrative_instruction -> Prop :=
  | reduce_refl : forall hs s vs es i, reduce_star hs s vs es i hs s vs es
  | reduce_step : forall hs s vs es i hs' s' vs' es' hs'' s'' vs'' es'',
    reduce hs s vs es i hs' s' vs' es' ->
    reduce_star hs' s' vs' es' i hs'' s'' vs'' es'' ->
    reduce_star hs s vs es i hs'' s'' vs'' es''
  .

Lemma safety : forall hs i s vs es ts,
    config_typing i s vs es ts ->
    (exists s' vs' es' hs',
      (const_list es' \/ es' = [::Trap]) /\ reduce_star hs s vs es i hs' s' vs' es') \/
    (exists hsn sn vsn esn, hsn 0 = hs /\ sn 0 = s /\ vsn 0 = vs /\ esn 0 = es /\
      forall n, reduce (hsn n) (sn n) (vsn n) (esn n) i (hsn n.+1) (sn n.+1) (vsn n.+1) (esn n.+1)).
Admitted. (* TODO *)

End Host.

