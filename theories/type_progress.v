From Wasm Require Export interpreter_ctx.
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

(* The progress property is derived from the interpreter. *)
Definition t_progress_interp_ctx: forall (hs: host_state) (s: store_record) (f: frame) es ts,
  config_typing s (f, es) ts ->
  terminal_form es \/
    (exists hs' s' f' es', reduce hs s f es hs' s' f' es').
Proof.
  move => hs s f es ts Htype.
  (* initialise an interpreter cfg tuple *)
  destruct (interp_cfg_of_wasm (s, (f, es))) as [[[[s0 ccs] sc] oe] [Hfill Hvalid]].
  (* run the interpreter *)
  remember (@run_one_step_ctx _ _ host_application_impl host_application_impl_correct hs (s0, ccs, sc, oe)) as res.
  destruct res as [hs' [[[s' ccs'] sc'] oe'] Hred Hvalid' | s' f' vs Hvalfill | s' f' Htrapfill | Hcontra | Hcontra]; clear Heqres.
  (* step *)
  - unfold reduce_ctx in Hred.
    rewrite Hfill in Hred.
    destruct (ctx_to_cfg (s', ccs', sc', oe')) as [[s'' [f'' es'']] | ] => //.
    right.
    by exists hs', s'', f'', es''.
  (* values *)
  - rewrite Hvalfill in Hfill; injection Hfill as <- <- <-.
    do 2 left.
    by apply v_to_e_const.
  (* trap *)
  - rewrite Htrapfill in Hfill; injection Hfill as <- <- <-.
    by left; right.
  (* invalid input -- impossible *)
  - by apply Hcontra in Hvalid.
  (* ill-typed -- impossible *)
  - unfold ctx_cfg_typing in Hcontra.
    rewrite Hfill in Hcontra.
    by apply Hcontra in Htype.
Qed.

End Host.
