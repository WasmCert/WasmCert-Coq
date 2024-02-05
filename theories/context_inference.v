From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From compcert Require lib.Floats.
From Wasm Require Export common typing operations.
From Coq Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Context_inference.

Variable host_function : eqType.

Let function_closure := function_closure host_function.
Let store_record := store_record host_function.

Definition func_typing_inf (fs: list function_closure) (n: nat) : option function_type :=
  option_map cl_type (List.nth_error fs n).

Definition funcs_typing_inf (s: store_record) (inst: instance) : option (list function_type) :=
  those (map (fun i => func_typing_inf s.(s_funcs) i) inst.(inst_funcs)).

(* Choosing the most lenient bound *)
Definition tab_typing_inf (ts: list tableinst) (n: nat) : option table_type :=
  match List.nth_error ts n with
  | Some _ => Some (Build_table_type (Build_limits 0%N None) ELT_funcref)
  | _ => None
  end.

Definition tabs_typing_inf (s: store_record) (inst: instance) : option (list table_type) :=
  those (map (fun i => tab_typing_inf s.(s_tables) i) inst.(inst_tab)).

(* Choosing the most lenient bound *)
Definition mem_typing_inf (ms: list memory) (n: nat) : option memory_type :=
  match List.nth_error ms n with
  | Some _ => Some (Build_limits 0%N None)
  | _ => None
  end.

Definition mems_typing_inf (s: store_record) (inst: instance) : option (list memory_type) :=
  those (map (fun i => mem_typing_inf s.(s_mems) i) inst.(inst_memory)).

Definition global_typing_inf (gs: list global) (n: nat) : option global_type :=
  match List.nth_error gs n with
  | Some g => Some (Build_global_type g.(g_mut) (typeof g.(g_val)))
  | _ => None
  end.

Definition globals_typing_inf (s: store_record) (inst: instance) : option (list global_type) :=
  those (map (fun i => global_typing_inf s.(s_globals) i) inst.(inst_globs)).

Definition inst_typing_inf (s: store_record) (inst: instance) : option t_context :=
  match funcs_typing_inf s inst with
  | Some fts =>
      match tabs_typing_inf s inst with
      | Some tts =>
          match mems_typing_inf s inst with
          | Some mts =>
              match globals_typing_inf s inst with
              | Some gts =>
                  Some (Build_t_context inst.(inst_types) fts gts tts mts nil nil None)
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition frame_typing_inf (s: store_record) (f: frame) : option t_context :=
  match inst_typing_inf s f.(f_inst) with
  | Some C => Some (upd_local C ((map typeof f.(f_locs)) ++ tc_local C))
  | None => None
  end.

Lemma func_typing_inf_agree: forall xs n x,
    (func_typing_inf xs n == Some x) = 
      functions_agree xs n x.
Proof.
  move => xs n x.
  unfold func_typing_inf, functions_agree.
  destruct (List.nth_error xs n) as [ x' | ] eqn:Hnth; rewrite Hnth => /=.
  - assert (n < length xs)%coq_nat as Hlen; first by apply List.nth_error_Some; rewrite Hnth.
    move/ltP in Hlen.
    by rewrite Hlen.
  - cbn.
    by lias.
Qed.

Lemma tab_typing_inf_agree: forall xs n x,
    tab_typing_inf xs n = Some x ->
    tabi_agree xs n x.
Proof.
  move => xs n x.
  unfold tab_typing_inf, tabi_agree, tab_typing, limit_match.
  destruct (List.nth_error xs n) as [ x' | ] eqn:Hnth => //=.
  assert (n < length xs)%coq_nat as Hlen; first by apply List.nth_error_Some; rewrite Hnth.
  move => Hinf.
  move/ltP in Hlen.
  rewrite Hlen => /=.
  injection Hinf as <-.
  cbn.
  rewrite Bool.andb_true_r.
  apply/N.leb_spec0.
  by lias.
Qed.


Lemma those_all2_agree {X Y Z: eqType}: forall (xs: list X) (ns: list Y) (ts: list Z) (f: list X -> Y -> option Z) (g: list X -> Y -> Z -> bool),
    (forall xs n x, (f xs n == Some x) = g xs n x) ->
    ((those (map (f xs) ns) == Some ts) = all2 (g xs) ns ts).
Proof.
  setoid_rewrite <- those_those0.
  move => xs.
  elim => //=.
  move => y ys IH ts f g Heq.
  destruct (f xs y) as [t | ] eqn:Hf => /=; move/eqP in Hf; destruct ts => //=; 
  destruct (those0 (map (f xs) ys)) as [ts' | ] eqn:Hthose => //=; cbn;
  try (erewrite <- IH; last by apply Heq);
  try (rewrite Hthose); cbn;
  try (move/eqP in Hf; rewrite -Heq Hf); cbn => //.
  by lias.
Qed.
  
Lemma funcs_typing_inf_agree: forall s inst fts,
  (funcs_typing_inf s inst == Some fts) =
  all2 (functions_agree s.(s_funcs)) inst.(inst_funcs) fts.
Proof.
  move => f inst fts.
  unfold funcs_typing_inf.
  apply those_all2_agree.
  by apply func_typing_inf_agree.
Qed.

Lemma inst_typing_inf_impl: forall s inst C,
    inst_typing_inf s inst = Some C ->
    inst_typing s inst C.
Proof.
  move => s inst C Hinf.
  unfold inst_typing_inf in Hinf.
  destruct inst.
  remove_bools_options => /=.
  apply/andP; split.
Admitted.
  
End Context_inference.
