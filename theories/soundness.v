From Wasm Require Export type_preservation type_progress.
From mathcomp Require Import ssreflect ssrbool eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Context `{ho: host}.

(* The same host function well-formedness assumptions from the interpreter *)
Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> list value -> (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).

CoInductive sound_trace hs s f es ts (Htype: config_typing s (f, es) ts) : Type :=
| rt_terminal :
  terminal_form es ->
  sound_trace hs Htype
| rt_step hs' s' f' es' (Htype': config_typing s' (f', es') ts):
  reduce_tuple (hs, s, f, es) (hs', s', f', es') ->
  sound_trace hs' Htype' ->
  sound_trace hs Htype
.

CoFixpoint type_soundness hs s f es ts Htype: @sound_trace hs s f es ts Htype.
Proof.
  intros.
  destruct (t_progress_interp_ctx host_application_impl_correct hs Htype) as [Hterm | [hs' [s' [f' [es' Hreduce]]]]] eqn:Hprogress.
  - by apply rt_terminal.
  - eapply rt_step.
    + by apply Hreduce.
    + by refine (type_soundness hs' _ _ _ _ (t_preservation Hreduce Htype)).
Defined.
    
End Host.
