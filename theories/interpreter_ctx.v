(** Proof-carrying interpreter for Wasm, optimised for contexts **)

From Wasm Require Import common properties opsem_properties tactic typing_inversion contexts.
From Coq Require Import ZArith.BinInt Program.Equality.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export operations host.
Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

Section Host.

Import EvalContext.
  
Variable host_function : eqType.
Let host := host host_function.
Let cfg_tuple_ctx := @cfg_tuple_ctx host_function.

Variable host_instance : host.

Let store_record := store_record host_function.
Let host_state := host_state host_instance.

Let e_typing := @e_typing host_function.
Let inst_typing := @inst_typing host_function.

Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                       (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).

Definition olist {T: Type} (ot: option T) : list T :=
  match ot with
  | Some t => [::t]
  | None => nil
  end.

Definition reduce_cfg (hs hs': host_state) (cfg cfg': cfg_tuple_ctx) : Prop :=
  match cfg with
  | (s, f, cc, e) =>
      match cfg' with
      | (s', f', cc', e') => reduce hs s f (cc [[ olist e ]]) hs' s' f' (cc' [[ olist e' ]])
      end
  end.

Definition run_one_step (hs: host_state) (cfg: cfg_tuple_ctx) : {hs' & {cfg' | reduce_cfg hs hs' cfg cfg'}}.
Proof.
  destruct cfg as [[[s f] cc] e].
  destruct e as [e | ]; last first.
Defined.

End Host.

Inductive res_crash : Type :=
| C_error : res_crash
| C_exhaustion : res_crash.

Scheme Equality for res_crash.
Definition res_crash_eqb c1 c2 := is_left (res_crash_eq_dec c1 c2).
Definition eqres_crashP : Equality.axiom res_crash_eqb :=
  eq_dec_Equality_axiom res_crash_eq_dec.

Canonical Structure res_crash_eqMixin := EqMixin eqres_crashP.
Canonical Structure res_crash_eqType := Eval hnf in EqType res_crash res_crash_eqMixin.

Inductive res : Type :=
| R_crash : res_crash -> res
| R_trap : res
| R_value : list value -> res.

Definition res_eq_dec : forall r1 r2 : res, {r1 = r2} + {r1 <> r2}.
Proof. decidable_equality. Defined.

Definition res_eqb (r1 r2 : res) : bool := res_eq_dec r1 r2.
Definition eqresP : Equality.axiom res_eqb :=
  eq_dec_Equality_axiom res_eq_dec.

Canonical Structure res_eqMixin := EqMixin eqresP.
Canonical Structure res_eqType := Eval hnf in EqType res res_eqMixin.

Section Host_func.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record := store_record host_function.
Let host_state := host_state host_instance.

Let e_typing := @e_typing host_function.
Let inst_typing := @inst_typing host_function.

Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                       (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).

(* Predicate for determining if a program fragment is typeable in some context, instead of a full program *)
Definition fragment_typeable s f ves es :=
  exists C C' ret lab t1s t2s t1s',
    C = upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab /\
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C' /\
    store_typing s /\
    e_typing s C es (Tf t1s t2s).

Inductive res_step'
  (hs : host_state) (s : store_record) (f : frame)
  (es : list administrative_instruction) : Type :=
| RS'_value :
    const_list es \/ es_is_trap es ->
    res_step' hs s f es
| RS'_error :
    (~ fragment_typeable s f [::] es) ->
    res_step' hs s f es
| RS'_break k bvs :
    (exists i j (lh: lholed i),
      i + k = j /\
      lfill lh (vs_to_es bvs ++ [::AI_basic (BI_br j)]) = es /\
      empty_vs_base lh) ->
    res_step' hs s f es
| RS'_return rvs :
    (exists i (lh: lholed i),
      lfill lh (vs_to_es rvs ++ [:: AI_basic BI_return]) = es /\
      empty_vs_base lh) ->
    res_step' hs s f es
| RS'_normal hs' s' f' es' :
    reduce hs s f es hs' s' f' es' ->
    res_step' hs s f es.
