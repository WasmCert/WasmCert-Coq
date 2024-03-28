From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From compcert Require lib.Floats.
From Wasm Require Export common typing operations.
From Coq Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
Section Context_inference.

Variable host_function : eqType.

Let funcinst := funcinst host_function.
Let store_record := store_record host_function.

Definition func_typing_inf (fs: list funcinst) (n: funcaddr) : option function_type :=
  option_map cl_type (lookup_N fs n).

Definition funcs_typing_inf (s: store_record) (inst: moduleinst) : option (list function_type) :=
  those (map (fun i => func_typing_inf s.(s_funcs) i) inst.(inst_funcs)).

(* Choosing the most lenient bound *)
Definition tab_typing_inf (ts: list tableinst) (n: tableaddr) : option table_type :=
  match lookup_N ts n with
  | Some _ => Some (Build_table_type (Build_limits 0%N None) T_funcref)
  | _ => None
  end.

Definition tabs_typing_inf (s: store_record) (inst: moduleinst) : option (list table_type) :=
  those (map (fun i => tab_typing_inf s.(s_tables) i) inst.(inst_tab)).

(* Choosing the most lenient bound *)
Definition mem_typing_inf (ms: list memory) (n: memoryaddr) : option memory_type :=
  match List.nth_error ms n with
  | Some _ => Some (Build_limits 0%N None)
  | _ => None
  end.

Definition mems_typing_inf (s: store_record) (inst: moduleinst) : option (list memory_type) :=
  those (map (fun i => mem_typing_inf s.(s_mems) i) inst.(inst_memory)).

Definition global_typing_inf (gs: list global) (n: nat) : option global_type :=
  match List.nth_error gs n with
  | Some g => Some (Build_global_type g.(g_mut) (typeof g.(g_val)))
  | _ => None
  end.

Definition globals_typing_inf (s: store_record) (inst: moduleinst) : option (list global_type) :=
  those (map (fun i => global_typing_inf s.(s_globals) i) inst.(inst_globs)).

Definition inst_typing_inf (s: store_record) (inst: moduleinst) : option t_context :=
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

Lemma mem_typing_inf_agree: forall xs n x,
    mem_typing_inf xs n = Some x ->
    memi_agree xs n x.
Proof.
  move => xs n x.
  unfold mem_typing_inf, memi_agree, mem_typing, limit_match.
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

Lemma global_typing_inf_agree: forall xs n x,
    (global_typing_inf xs n = Some x) ->
    globals_agree xs n x.
Proof.
  move => xs n x.
  unfold global_typing_inf, globals_agree, global_agree.
  destruct (List.nth_error xs n) as [ x' | ] eqn:Hnth => //=.
  assert (n < length xs)%coq_nat as Hlen; first by apply List.nth_error_Some; rewrite Hnth.
    move/ltP in Hlen.
    rewrite Hlen => /=.
    move => [<-] => /=.
    apply/eqP; f_equal.
    by lias.
Qed.

Lemma those_all2_impl {X Y Z: Type}: forall (xs: list X) (ns: list Y) (ts: list Z) (f: list X -> Y -> option Z) (g: list X -> Y -> Z -> bool),
    (forall xs n x, f xs n = Some x -> g xs n x) ->
    (those (map (f xs) ns) = Some ts) ->
    all2 (g xs) ns ts.
Proof.
  setoid_rewrite <- those_those0.
  move => xs.
  elim => //=; first by intros; destruct ts.
  move => y ys IH ts f g Heq Himpl.
  remove_bools_options.
  apply Heq in Hoption.
  eapply IH in Hoption0; last by apply Heq.
  by rewrite Hoption Hoption0.
Qed.
  
Lemma funcs_typing_inf_agree: forall s inst xts,
  (funcs_typing_inf s inst = Some xts) ->
  all2 (functions_agree s.(s_funcs)) inst.(inst_funcs) xts.
Proof.
  move => f inst xts Hinf.
  unfold funcs_typing_inf in Hinf.
  eapply those_all2_impl; eauto.
  intros.
  rewrite <- func_typing_inf_agree.
  by apply/eqP.
Qed.

Lemma tabs_typing_inf_agree: forall s inst xts,
  (tabs_typing_inf s inst = Some xts) ->
  all2 (tabi_agree s.(s_tables)) inst.(inst_tab) xts.
Proof.
  move => f inst fts Hinf.
  eapply those_all2_impl; eauto.
  intros.
  by apply tab_typing_inf_agree.
Qed.

Lemma mems_typing_inf_agree: forall s inst xts,
  (mems_typing_inf s inst = Some xts) ->
  all2 (memi_agree s.(s_mems)) inst.(inst_memory) xts.
Proof.
  move => f inst fts Hinf.
  eapply those_all2_impl; eauto.
  intros.
  by apply mem_typing_inf_agree.
Qed.

Lemma globals_typing_inf_agree: forall s inst xts,
  (globals_typing_inf s inst = Some xts) ->
  all2 (globals_agree s.(s_globals)) inst.(inst_globs) xts.
Proof.
  move => f inst fts Hinf.
  eapply those_all2_impl; eauto.
  intros.
  by apply global_typing_inf_agree.
Qed.

Lemma inst_typing_inf_impl: forall s inst C,
    inst_typing_inf s inst = Some C ->
    inst_typing s inst C.
Proof.
  move => s inst C Hinf.
  unfold inst_typing_inf in Hinf.
  destruct inst.
  remove_bools_options => /=.
  apply/andP; split; last by apply mems_typing_inf_agree in Hoption1.
  apply/andP; split; last by apply tabs_typing_inf_agree in Hoption0.
  apply/andP; split; last by apply globals_typing_inf_agree in Hoption2.
  apply/andP; split; last by apply funcs_typing_inf_agree in Hoption.
  by apply/eqP.
Defined.
  
End Context_inference.
*)
