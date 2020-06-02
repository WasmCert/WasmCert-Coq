Require Import common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import operations typing datatypes_properties typing opsem.

Definition b_to_a (bes: seq basic_instruction) : seq administrative_instruction :=
  map (fun x => (Basic x)) bes.

Definition a_to_b_single (e: administrative_instruction) : basic_instruction :=
  match e with
  | Basic x => x
  | _ => EConst (ConstInt32 (Wasm_int.Int32.zero))
  end.

Definition a_to_b (es: seq administrative_instruction) : seq basic_instruction :=
  map a_to_b_single es.

Lemma b_a_elim: forall bes es,
    es = b_to_a bes ->
    bes = a_to_b es.
Proof.
  induction bes; move => es H => //=.
  - by rewrite H.
  - simpl in H. assert (es = b_to_a (a :: bes)) as H1.
    + by rewrite H.
    + rewrite H1. simpl. f_equal. by apply IHbes.
Qed.   

Definition t_be_value (es: seq basic_instruction) : Prop :=
  const_list (b_to_a es).

Print tc_global.

(*
  It is less trivial than thought to state this theorem because typing and opsem used
    different parameters in their corresponding formulation.
 *)

Print value.

Print value_type.

Definition v_to_vt (v: value) :=
  match v with
  | ConstInt32 _ => T_i32
  | ConstInt64 _ => T_i64
  | ConstFloat32 _ => T_f32
  | ConstFloat64 _ => T_f64
  end.

Definition vs_to_vts (vs: list value) :=
  map v_to_vt vs.

(* Questionable formulation on b_e only. cl_typing seems to already include 
     be_typing and inst_typing?*)

Theorem t_be_progress: forall C i s vs bes tf,
    be_typing C bes tf ->
    inst_typing s i C ->
    vs_to_vts vs = tc_local C ->
    (t_be_value bes \/
     exists s' vs' es', reduce s vs (b_to_a bes) i s' vs' es').
Proof.
Admitted.

Ltac b_to_a_revert :=
  repeat lazymatch goal with
         | H: _ = b_to_a ?bes |- _ =>
           apply b_a_elim in H
         end.

(* This has a 0% chance of being the correct statement. I just wanted to see
     how the opsem condition works when we do inversion on it. *)
Theorem t_be_preservation: forall s vs bes i s' vs' bes' C C' tf,
    reduce s vs (b_to_a bes) i s' vs' (b_to_a bes') ->
    be_typing C bes tf ->
    inst_typing s i C ->
    vs_to_vts vs = tc_local C ->
    inst_typing s' i C' ->
    vs_to_vts vs' = tc_local C' ->
    be_typing C' bes' tf.
Proof.
  move => s vs bes i s' vs' bes' C C' tf HOpsem HBET HInstT HLocalT HInstT' HLocalT'.
  inversion HOpsem; subst.
  - (* reduce_simple *)
Admitted.
