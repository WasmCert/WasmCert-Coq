(** Typing inversion lemmas **)

From Wasm Require Export common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith ZArith_base.
From Wasm Require Export properties subtyping_properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Typing_inversion_be.
  
(* Some quality of life lemmas *)
(* Upd: these lemmas are deprecated; it is encouraged to directly use subtyping rule. *)
Lemma bet_weakening_empty_1: forall C es ts t2s,
    be_typing C es (Tf [::] t2s) ->
    be_typing C es (Tf ts (ts ++ t2s)).
Proof.
  move => C es ts t2s HType.
  eapply bet_subtyping; eauto.
  by resolve_subtyping.
Qed.

Lemma bet_weakening_empty_2: forall C es ts t1s,
    be_typing C es (Tf t1s [::]) ->
    be_typing C es (Tf (ts ++ t1s) ts).
Proof.
  move => C es ts t1s HType.
  eapply bet_subtyping; eauto.
  by resolve_subtyping.
Qed.

Lemma bet_weakening_empty_both: forall C es ts,
    be_typing C es (Tf [::] [::]) ->
    be_typing C es (Tf ts ts).
Proof.
  move => C es ts HType.
  eapply bet_subtyping; eauto.
  by resolve_subtyping.
Qed.


Hint Constructors be_typing : core.

(* Structural inversions *)
Lemma empty_typing: forall C t1s t2s,
    be_typing C [::] (Tf t1s t2s) ->
    t1s <ts: t2s.
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //; extract_premise.
  - by destruct es.
  - unfold instr_subtyping in *.
    by extract_premise; subst.
Qed.

Definition be_principal_typing (C: t_context) (be: basic_instruction) (tf: instr_type) : Prop :=
  match be with
  | BI_const_num c =>
      tf = (Tf nil [::T_num (typeof_num c)])
  | BI_const_vec c =>
      tf = (Tf nil [::T_vec (typeof_vec c)])
  | BI_ref_null t =>
      tf = (Tf nil [::T_ref t])
  | BI_ref_is_null =>
      exists t, tf = (Tf [::T_ref t] [::T_num T_i32])
  | BI_ref_func x =>
      exists t, tf = (Tf [::] [::T_ref T_funcref]) /\
             lookup_N (tc_funcs C) x = Some t /\
             List.In x (tc_refs C)
  | BI_unop t op =>
      tf = (Tf [::T_num t] [::T_num t]) /\
        unop_type_agree t op
  | BI_binop t op =>
      tf = (Tf [::T_num t; T_num t] [::T_num t]) /\
        binop_type_agree t op
  | BI_testop t op =>
      tf = (Tf [::T_num t] [::T_num T_i32]) /\
        is_int_t t
  | BI_relop t op =>
      tf = (Tf [::T_num t; T_num t] [::T_num T_i32]) /\
        relop_type_agree t op
  | BI_cvtop t2 op t1 sx =>
      tf = (Tf [::T_num t1] [::T_num t2]) /\
        cvtop_valid t2 op t1 sx
  | BI_unreachable =>
      True (* Equivalently, put existential quantifiers and trivial equalities *)
  | BI_nop =>
      tf = (Tf nil nil)
  | BI_drop =>
      exists t, tf = (Tf [::t] nil)
  | BI_select ot =>
      exists t, tf = (Tf [::t; t; T_num T_i32] [::t]) /\
             match ot with
             | Some [::t0] => t = t0
             | None => is_numeric_type t
             | _ => False
             end
  | BI_block tb es =>
      exists tn tm,
      tf = (Tf tn tm) /\
        expand_t C tb = Some (Tf tn tm) /\
        be_typing (upd_label C ([::tm] ++ (tc_labels C))) es (Tf tn tm)
  | BI_loop tb es =>
      exists tn tm,
      tf = (Tf tn tm) /\
        expand_t C tb = Some (Tf tn tm) /\
        be_typing (upd_label C ([::tn] ++ (tc_labels C))) es (Tf tn tm)
  | BI_if tb es1 es2 =>
      exists tn tm,
      tf = (Tf (tn ++ [::T_num T_i32]) tm) /\
        expand_t C tb = Some (Tf tn tm) /\
        be_typing (upd_label C ([::tm] ++ (tc_labels C))) es1 (Tf tn tm) /\
        be_typing (upd_label C ([::tm] ++ (tc_labels C))) es2 (Tf tn tm)
  | BI_br k =>
      exists tx ty ts,
      tf = (Tf (tx ++ ts) ty) /\
        lookup_N C.(tc_labels) k = Some ts
  | BI_br_if k =>
      exists ts,
      tf = (Tf (ts ++ [::T_num T_i32]) ts) /\
        lookup_N C.(tc_labels) k = Some ts
  | BI_br_table ins k =>
      exists tx ty ts,
      tf = (Tf (tx ++ (ts ++ [::T_num T_i32])) ty) /\
        List.Forall (fun i => (lookup_N C.(tc_labels) i) = Some ts) (ins ++ [::k])
  | BI_return =>
      exists tx ty ts,
      tf = (Tf (tx ++ ts) ty) /\
        tc_return C = Some ts
  | BI_call n =>
      exists tf0,
      tf = tf0 /\
        lookup_N (tc_funcs C) n = Some tf0
  | BI_call_indirect x y =>
      exists ts1 ts2 tabt,
      tf = (Tf (ts1 ++ [::T_num T_i32]) ts2)/\
        lookup_N (tc_tables C) x = Some tabt /\
        tabt.(tt_elem_type) = T_funcref /\
        lookup_N (tc_types C) y = Some (Tf ts1 ts2)
  | BI_local_get x =>
      exists t,
      tf = (Tf nil [::t]) /\
        lookup_N (tc_locals C) x = Some t
  | BI_local_set x =>
      exists t,
      tf = (Tf [::t] nil) /\
        lookup_N (tc_locals C) x = Some t
  | BI_local_tee x =>
      exists t,
      tf = (Tf [::t] [::t]) /\
        lookup_N (tc_locals C) x = Some t
  | BI_global_get x =>
      exists gt t,
      tf = (Tf nil [::t]) /\
        lookup_N (tc_globals C) x = Some gt /\
        tg_t gt = t
  | BI_global_set x =>
      exists gt t,
      tf = (Tf [::t] nil) /\
        lookup_N (tc_globals C) x = Some gt /\
        tg_t gt = t /\
        is_mut gt
  | BI_table_get x =>
      exists tabt t,
      tf = (Tf [::T_num T_i32] [::T_ref t]) /\
        lookup_N (tc_tables C) x = Some tabt /\
        tabt.(tt_elem_type) = t
  | BI_table_set x =>
      exists tabt t,
      tf = (Tf [::T_num T_i32; T_ref t] [::]) /\
        lookup_N (tc_tables C) x = Some tabt /\
        tabt.(tt_elem_type) = t
  | BI_table_size x =>
      exists tabt,
      tf = (Tf [::] [::T_num T_i32]) /\
        lookup_N (tc_tables C) x = Some tabt
  | BI_table_grow x =>
      exists tabt t,
      tf = (Tf [::T_ref t; T_num T_i32] [::T_num T_i32]) /\
        lookup_N (tc_tables C) x = Some tabt /\
        tabt.(tt_elem_type) = t
  | BI_table_fill x =>
      exists tabt t,
      tf = (Tf [::T_num T_i32; T_ref t; T_num T_i32] nil) /\
        lookup_N (tc_tables C) x = Some tabt /\
        tabt.(tt_elem_type) = t
  | BI_table_copy x y =>
      exists tabt1 tabt2 t,
      tf = (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::]) /\
        lookup_N (tc_tables C) x = Some tabt1 /\
        tabt1.(tt_elem_type) = t /\
        lookup_N (tc_tables C) y = Some tabt2 /\
        tabt2.(tt_elem_type) = t
  | BI_table_init x y =>
      exists tabt t,
      tf = (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::]) /\
        lookup_N (tc_tables C) x = Some tabt /\
        tabt.(tt_elem_type) = t /\
        lookup_N (tc_elems C) y = Some t
  | BI_elem_drop x =>
      exists t,
      tf = (Tf nil nil) /\
        lookup_N (tc_elems C) x = Some t
  | BI_load t tp_sx a off =>
      exists mt,
      tf = (Tf [::T_num T_i32] [::T_num t]) /\
        lookup_N (tc_mems C) 0%N = Some mt /\
        load_store_t_bounds a (option_projl tp_sx) t
  | BI_store t tp a off =>
      exists mt,
      tf = (Tf [::T_num T_i32; T_num t] [::]) /\
        lookup_N (tc_mems C) 0%N = Some mt /\
        load_store_t_bounds a tp t
  | BI_memory_size =>
      exists mt,
      tf = (Tf [::] [::T_num T_i32]) /\
        lookup_N (tc_mems C) 0%N = Some mt
  | BI_memory_grow =>
      exists mt,
      tf = (Tf [::T_num T_i32] [::T_num T_i32]) /\
        lookup_N (tc_mems C) 0%N = Some mt
  | BI_memory_fill =>
      exists mt,
      tf = (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::]) /\
        lookup_N (tc_mems C) 0%N = Some mt
  | BI_memory_copy =>
      exists mt,
      tf = (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::]) /\
        lookup_N (tc_mems C) 0%N = Some mt
  | BI_memory_init x =>
      exists mt dt,
      tf = (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::]) /\
        lookup_N (tc_mems C) 0%N = Some mt /\
        lookup_N (tc_datas C) x = Some dt
  | BI_data_drop x =>
      exists dt,
      tf = (Tf nil nil) /\
        lookup_N (tc_datas C) x = Some dt
  end.

Lemma be_typing_inversion: forall C be tf,
    be_typing C [::be] tf ->
    exists tf_principal,
      tf_principal <ti: tf /\
      be_principal_typing C be tf_principal.
Proof.
  move => C be tf HType.
  gen_ind_subst HType => //; try by (eexists; split; first (by apply instr_subtyping_eq); try by repeat eexists; eauto).
  (* Table copy -- needs a separate resolve since substitution simplified the premises by too much *)
  - eexists; split; first (by apply instr_subtyping_eq).
    by exists tabtype1, tabtype2, (tt_elem_type tabtype1).
  (* Composition *)
  - extract_listn; extract_premise.
    apply empty_typing in HType1.
    exists extr; split => //.
    destruct extr as [tx ty].
    unfold instr_subtyping in *.
    extract_premise; subst.
    apply values_subtyping_split1 in HType1; remove_bools_options.
    exists (take (size extr) t1s), extr0, (drop (size extr) t1s), extr2; repeat split => //; resolve_subtyping => //.
    by rewrite cat_take_drop.
  (* Subtyping *)
  - extract_premise.
    exists extr; split => //.
    by resolve_subtyping.
Qed.

(** A helper tactic for proving [composition_typing_single]. **)
Ltac auto_prove_bet:=
  repeat lazymatch goal with
  | H: _ |- exists t3s, be_typing _ [::] (Tf ?tx _) /\ _ =>
    try exists tx; split; try eauto
  | H: _ |- be_typing _ [::] (Tf ?es ?es) =>
    apply bet_weakening_empty_both; try by []
  end.

(* Note that this lemma is still true in the context of subtyping. *)
Lemma be_composition_typing_single: forall C es1 e t1s t2s,
    be_typing C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists t3s, be_typing C es1 (Tf t1s t3s) /\
           be_typing C [::e] (Tf t3s t2s).
Proof.
  move => C es1 e t1s t2s HType.
  gen_ind_subst HType; extract_listn; auto_prove_bet.
  - by destruct es1 => //=.
  - by exists t2s.
  - unfold instr_subtyping in H.
    extract_premise; subst.
    exists (extr0 ++ extr); split.
    + eapply bet_subtyping; eauto.
      unfold instr_subtyping.
      exists extr0, extr0, extr2, extr; by resolve_subtyping.
    + eapply bet_subtyping; eauto.
      unfold instr_subtyping.
      exists extr0, extr1, extr, extr3; by resolve_subtyping.
Qed.

Lemma be_composition_typing: forall C es1 es2 t1s t2s,
    be_typing C (es1 ++ es2) (Tf t1s t2s) ->
    exists t3s, be_typing C es1 (Tf t1s t3s) /\
           be_typing C es2 (Tf t3s t2s).
Proof.
  move => C es1 es2.
  move: es1.
  induction es2 using List.rev_ind; move => es1 t1s t2s HType.
  - rewrite cats0 in HType.
    exists t2s.
    repeat split => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite catA in HType.
    apply be_composition_typing_single in HType as [ts3 [Hbet1 Hbet2]].
    apply IHes2 in Hbet1 as [ts3' [Hbet3 Hbet4]].
    exists ts3'.
    repeat split => //.
    by eapply bet_composition; eauto.
Qed.

Lemma bet_composition': forall C es1 es2 t1s t2s t3s,
    be_typing C es1 (Tf t1s t2s) ->
    be_typing C es2 (Tf t2s t3s) ->
    be_typing C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => C es1 es2.
  move: es1.
  induction es2 using List.rev_ind; move => es1 t1s t2s t3s Hbet1 Hbet2.
  - apply empty_typing in Hbet2; rewrite cats0; subst.
    eapply bet_subtyping; eauto.
    unfold instr_subtyping.
    exists nil, nil, t1s, t3s.
    by resolve_subtyping.
  - apply be_composition_typing in Hbet2 as [ts3 [Hbet3 Hbet4]].
    rewrite catA. eapply bet_composition; last by eauto.
    by eapply IHes2; eauto.
Qed.

Lemma bet_composition_front: forall C e es t1s t2s t3s,
    be_typing C [::e] (Tf t1s t2s) ->
    be_typing C es (Tf t2s t3s) ->
    be_typing C (e :: es) (Tf t1s t3s).
Proof.
  intros.
  rewrite - cat1s.
  by eapply bet_composition'; eauto.
Qed.

End Typing_inversion_be.

Lemma upd_label_overwrite: forall C l1 l2,
    upd_label (upd_label C l1) l2 = upd_label C l2.
Proof.
  by [].
Qed.

Ltac resolve_list_eq :=
  repeat match goal with
  | H: _ ++ [::_] = _ ++ [::_] |- _ =>
    apply concat_cancel_last in H; destruct H; subst
  | H: _ ++ [::_] = _ ++ _ ++ [::_] |- _ =>
    rewrite catA in H; apply concat_cancel_last in H; destruct H; subst
  | H: _ ++ _ ++ [::_] = _ ++ [::_] |- _ =>
    rewrite catA in H; apply concat_cancel_last in H; destruct H; subst
  | H: _ ++ [::_; _] = (?l ++ [::?x]) ++ [::?y] |- _ =>
    rewrite -catA in H; simpl in H; apply concat_cancel_last_n in H; remove_bools_options
  | H: (?l ++ [::?x1; ?x2]) ++ [:: ?y] = _ ++ [::_; _; _] |- _ =>
    rewrite -catA in H; simpl in H; apply concat_cancel_last_n in H; remove_bools_options
  | H: [:: _; _] = [::_; _] |- _ =>
    inversion H; subst; clear H
  | H: [:: _; _; _] = [::_; _; _] |- _ =>
    inversion H; subst; clear H
  | H: Tf _ _ = Tf _ _ |- _ =>
    inversion H; subst; clear H
  | H: T_num _ = T_num _ |- _ =>
    inversion H; subst; clear H
    end.

Ltac invert_be_typing :=
  repeat match goal with
  | H: be_typing _ [::] _ |- _ =>
    apply empty_typing in H; subst
  | H: be_typing _ [::_] _ |- _ =>
    let tf_principal := fresh "tf_principal" in
    let Htisub := fresh "Htisub" in
    let Hinvgoal := fresh "Hinvgoal" in
    apply be_typing_inversion in H as [tf_principal [Htisub Hinvgoal]]; simpl in Hinvgoal; extract_premise
  | H: be_typing _ (_ ++ _) _ |- _ =>
    let ts3 := fresh "ts3_comp" in
    let H1 := fresh "H1_comp" in
    let H2 := fresh "H2_comp" in
    apply be_composition_typing in H; destruct H as [ts3 [H1 H2]]
  | H: be_typing _ [::_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: be_typing _ [::_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: be_typing _ [::_;_;_;_] _ |- _ =>
      rewrite -cat1s in H
  | _ => try by simpl; try resolve_list_eq
  end.

Ltac e_typing_ind HType :=
  match type of HType with
  | e_typing _ _ _ (Tf ?ts1 ?ts2) =>
      let tf := fresh "tf" in
      let Heqtf := fresh "Heqtf" in
      remember (Tf ts1 ts2: instr_type) as tr eqn:Heqtf;
      move: ts1 ts2 Heqtf;
      dependent induction HType; intros; subst
  end.

Section Typing_inversion_e.
             
Context {hfc: host_function_class}.

(** Typing lemmas **)

(* A reformulation of [ety_a] that is easier to be used. *)
Lemma ety_a': forall s C es ts,
    es_is_basic es ->
    be_typing C (to_b_list es) ts ->
    e_typing s C es ts.
Proof.
  move => s C es ts HBasic HType.
  replace es with (to_e_list (to_b_list es)).
  - by apply ety_a.
  - symmetry. by apply e_b_elim.
Qed.

Lemma et_weakening_empty_1: forall s C es ts t2s,
    e_typing s C es (Tf [::] t2s) ->
    e_typing s C es (Tf ts (ts ++ t2s)).
Proof.
  move => s C es ts t2s HType.
  eapply ety_subtyping; eauto.
  by resolve_subtyping.
Qed.

Lemma et_weakening_empty_2: forall s C es ts t2s,
    e_typing s C es (Tf t2s nil) ->
    e_typing s C es (Tf (ts ++ t2s) ts).
Proof.
  move => s C es ts t2s HType.
  eapply ety_subtyping; eauto.
  by resolve_subtyping.
Qed.

(* A convenient lemma to invert e_typing back to be_typing. *)
Lemma et_to_bet: forall s C es tf,
    es_is_basic es ->
    e_typing s C es tf ->
    be_typing C (to_b_list es) tf.
Proof.
  move => s C es tf HBasic HType.
  dependent induction HType; basic_inversion => //.
  + replace (to_b_list (to_e_list bes)) with bes => //.
    by apply b_e_elim.
  + rewrite to_b_list_concat.
    apply basic_concat in HBasic.
    move/andP in HBasic.
    destruct HBasic as [Hbes Hbe].
    eapply bet_composition.
    * by eapply IHHType1 => //.
    * by eapply IHHType2 => //.
  + apply IHHType in HBasic.
    by eapply bet_subtyping; eauto.
Qed.

Definition e_principal_typing (s: store_record) (C: t_context) (e: administrative_instruction) (tf: instr_type) : Prop :=
  match e with
  | AI_basic b =>
      be_principal_typing C b tf
  | AI_trap =>
      True (* Equivalently, add trivial equalities *)
  | AI_ref_extern a =>
      tf = (Tf nil [::T_ref T_externref])
  | AI_ref a =>
      exists t, tf = (Tf nil [::T_ref T_funcref]) /\
        ext_func_typing s a = Some t
  | AI_invoke a =>
      exists tf0, tf = tf0 /\
        ext_func_typing s a = Some tf0
  | AI_label n es0 es =>
      exists ts1 ts2,
      tf = (Tf nil ts2) /\
        e_typing s C es0 (Tf ts1 ts2) /\
        e_typing s (upd_label C ([::ts1] ++ tc_labels C)) es (Tf nil ts2) /\
        length ts1 = n
  | AI_frame n f es =>
      exists ts,
      tf = (Tf nil ts) /\
        thread_typing s (Some ts) (f, es) ts /\
        length ts = n
  end.
  
Lemma empty_e_typing: forall s C t1s t2s,
    e_typing s C [::] (Tf t1s t2s) ->
    t1s <ts: t2s.
Proof.
  move => s C t1s t2s HType.
  apply et_to_bet in HType => //.
  by apply empty_typing in HType.
Qed.

Lemma et_empty: forall s C ts1 ts2,
    ts1 <ts: ts2 ->
    e_typing s C nil (Tf ts1 ts2).
Proof.
  move => s C ts1 ts2 Hsub.
  apply ety_a' => //=.
  eapply bet_subtyping; first by apply bet_empty.
  unfold instr_subtyping.
  exists ts1, ts2, nil, nil.
  repeat rewrite cats0.
  by resolve_subtyping.
Qed.

Lemma e_typing_inversion: forall s C e tf,
    e_typing s C [::e] tf ->
    exists tf_principal,
      tf_principal <ti: tf /\
      e_principal_typing s C e tf_principal.
Proof.
  move => s C e tf HType.
  dependent induction HType; try by (eexists; split; first (by apply instr_subtyping_eq); try by eexists; eauto).
  (* bet *)
  - do 2 (try destruct bes => //).
    destruct e => //.
    simpl in x; inversion x; subst; clear x.
    by apply be_typing_inversion.
  (* Composition *)
  - extract_listn; extract_premise.
    apply empty_e_typing in HType1.
    exists extr; split => //.
    destruct extr as [tx ty].
    unfold instr_subtyping in *.
    extract_premise; subst.
    apply values_subtyping_split1 in HType1; remove_bools_options.
    exists (take (size extr) t1s), extr0, (drop (size extr) t1s), extr2; repeat split => //; resolve_subtyping => //.
    by rewrite cat_take_drop.
  (* Subtyping *)
  - extract_premise.
    exists extr; split => //.
    by resolve_subtyping.
Qed.
  
(** A helper tactic for proving [composition_typing_single]. **)
Ltac auto_prove_et:=
  repeat lazymatch goal with
  | H: _ |- exists t3s, e_typing _ _ [::] (Tf ?tx _) /\ _ =>
    try exists tx; split; try eauto
  | H: _ |- e_typing _ _ [::] (Tf ?es ?es) =>
    apply et_empty; try by resolve_subtyping
  end.

Lemma e_composition_typing_single: forall s C es1 e t1s t2s,
    e_typing s C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists t3s, e_typing s C es1 (Tf t1s t3s) /\
           e_typing s C [::e] (Tf t3s t2s).
Proof.
  move => s C es1 es2 t1s t2s HType.
  e_typing_ind HType; extract_listn; resolve_list_eq; auto_prove_et => //; try by econstructor; eauto.
  - (* basic *)
    apply b_e_elim in x. destruct x. subst.
    rewrite to_b_list_concat in H.
    invert_be_typing.
    apply basic_concat in H1. move/andP in H1. destruct H1.
    exists ts3_comp.
    by repeat split => //=; apply ety_a' => //=.
  - (* subtyping *)
    extract_premise.
    unfold instr_subtyping in *; extract_premise; subst.
    exists (extr0 ++ extr); split; eapply ety_subtyping; eauto; unfold instr_subtyping.
    + exists extr0, extr0, extr2, extr; by resolve_subtyping.
    + exists extr0, extr1, extr, extr3; by resolve_subtyping.
Qed.

Lemma e_composition_typing: forall s C es1 es2 t1s t2s,
    e_typing s C (es1 ++ es2) (Tf t1s t2s) ->
    exists t3s, e_typing s C es1 (Tf t1s t3s) /\
           e_typing s C es2 (Tf t3s t2s).
Proof.
  move => s C es1 es2.
  move: es1.
  induction es2 using List.rev_ind; move => es1 ts1 ts2 HType.
  - rewrite cats0 in HType.
    exists ts2.
    repeat split => //=.
    apply ety_a' => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite catA in HType.
    apply e_composition_typing_single in HType as [ts3 [Het1 Het2]].
    apply IHes2 in Het1 as [ts3' [Het3 Het4]].
    exists ts3'.
    repeat split => //.
    by eapply ety_composition; eauto.
Qed.

Lemma et_composition': forall s C es1 es2 t1s t2s t3s,
    e_typing s C es1 (Tf t1s t2s) ->
    e_typing s C es2 (Tf t2s t3s) ->
    e_typing s C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => s C es1 es2.
  move: es1.
  induction es2 using List.rev_ind; move => es1 ts1 ts2 ts3 Het1 Het2.
  - apply et_to_bet in Het2 => //. apply empty_typing in Het2.
    rewrite cats0.
    eapply ety_subtyping; eauto.
    unfold instr_subtyping.
    exists nil, nil, ts1, ts3.
    by resolve_subtyping.
  - apply e_composition_typing in Het2 as [ts3' [Het3 Het4]].
    rewrite catA. eapply ety_composition => //=.
    eapply IHes2; eauto.
    by eauto.
Qed.

Lemma Value_typing_inversion: forall s C v ts1 ts2,
    e_typing s C [::v_to_e v] (Tf ts1 ts2) ->
    exists t, (Tf nil [::t]) <ti: (Tf ts1 ts2) /\
           value_typing s v t.
Proof.
  move => s C v ts1 ts2 HType.
  Opaque instr_subtyping.
  destruct v; simpl in HType; try (apply et_to_bet in HType; last done); simpl in HType; invert_be_typing; simpl in *; subst.
  - exists (T_num (typeof_num v)); split => //.
    by destruct v.
  - exists (T_vec (typeof_vec v)); split => //.
    by destruct v.
  (* ref -- slightly annoying, since one is basic and the other ones are not *)
  - destruct v; simpl in *.
    (* ref_null *)
    + apply et_to_bet in HType; last done; simpl in *.
      invert_be_typing.
      exists (T_ref r); split => //.
      by destruct r.
    (* ref *)
    + apply e_typing_inversion in HType; simpl in *.
      extract_premise.
      eexists; split; eauto.
      unfold value_typing => /=.
      by rewrite Hconjr.
    (* ref_extern *)
    + apply e_typing_inversion in HType; simpl in *.
      extract_premise.
      exists (T_ref T_externref).
      by split => //.
  Transparent instr_subtyping.
Qed.

Lemma Values_typing_inversion: forall s C vs ts1 ts2,
    e_typing s C (v_to_e_list vs) (Tf ts1 ts2) ->
    exists ts, (Tf nil ts) <ti: (Tf ts1 ts2) /\
           values_typing s vs ts.
Proof.
  move => s C; elim => /=.
  - move => tx ty Htype.
    apply empty_e_typing in Htype; subst.
    exists nil; split => //.
    exists tx, ty, nil, nil; by repeat rewrite cats0.
  - move => v vs IH ts1 ts2 Htype.
    rewrite - cat1s in Htype.
    apply e_composition_typing in Htype as [ts3 [Het1 Het2]].
    apply Value_typing_inversion in Het1 as [t [Hsub Hvt]].
    apply IH in Het2; unfold instr_subtyping in *; extract_premise; resolve_subtyping.
    apply values_subtyping_split2 in Hconjl1; remove_bools_options.
    exists (t :: extr).
    split; last by lias.
    exists extr0, (take (size extr1) extr5), nil, ((drop (size extr1) extr5) ++ extr7); repeat split; resolve_subtyping => //.
    + by rewrite cats0.
    + by rewrite catA cat_take_drop.
    + rewrite -cat1s values_subtyping_cat; first by erewrite values_subtyping_trans; eauto.
      apply values_subtyping_size in H0, Hconjr2.
      by lias.
Qed.

(* In Wasm 2.0, values are no longer always well-typed, and typing needs to be done under e_typing. *)
Lemma et_value_typing: forall s C v t,
    value_typing s v t ->
    e_typing s C [::v_to_e v] (Tf nil [::t]).
Proof.
  move => s C v t Hvt.
  destruct v as [| | v]=> /=; unfold value_typing in Hvt; remove_bools_options; simpl in *; try injection Hoption as <-.
  - apply ety_a' => //=.
    econstructor; first by econstructor.
    apply instr_subtyping_weaken2 with (ty2 := [::T_num (typeof_num v)]); by resolve_subtyping.
  - apply ety_a' => //=.
    econstructor; first by econstructor.
    apply instr_subtyping_weaken2 with (ty2 := [::T_vec (typeof_vec v)]); by resolve_subtyping.
  - destruct v as [| f | e] => /=; simpl in *; try injection Hoption as <-; remove_bools_options.
    + apply ety_a' => //=.
      econstructor; first by econstructor.
      apply instr_subtyping_weaken2 with (ty2 := [::T_ref r]); by resolve_subtyping.
    + eapply ety_subtyping; first by eapply ety_ref; eauto.
      apply instr_subtyping_weaken2 with (ty2 := [::T_ref T_funcref]); by resolve_subtyping.
    + eapply ety_subtyping; first by eapply ety_ref_extern; eauto.
      apply instr_subtyping_weaken2 with (ty2 := [::T_ref T_externref]); by resolve_subtyping.
Qed.

Lemma et_values_typing: forall s C vs ts,
    values_typing s vs ts ->
    e_typing s C (v_to_e_list vs) (Tf nil ts).
Proof.
  move => s C; elim => /=.
  - move => ts Hvts; destruct ts => //.
    apply ety_a' => //=. by apply bet_empty.
  - move => v vs IH ts Hvts; remove_bools_options.
    rewrite -cat1s.
    apply et_composition' with (t2s := [::v0]); first by apply et_value_typing.
    rewrite <- (cat1s v0 cons_l).
    eapply ety_subtyping; first by eapply IH; eauto.
    by resolve_subtyping.
Qed.

(* Helpers for more efficiently dealing with these due to subtyping *)
Lemma et_value_typing': forall s C v t tf,
    value_typing s v t ->
    (Tf nil [::t]) <ti: tf ->
    e_typing s C [::v_to_e v] tf.
Proof.
  move => s C v t [tx ty] Hvaltype Hsub.
  eapply ety_subtyping; eauto; by apply et_value_typing; eauto.
Qed.

Lemma et_values_typing': forall s C vs ts tf,
    values_typing s vs ts ->
    (Tf nil ts) <ti: tf ->
    e_typing s C (v_to_e_list vs) tf.
Proof.
  move => s C v t [tx ty] Hvaltype Hsub.
  eapply ety_subtyping; eauto; by apply et_values_typing; eauto.
Qed.

End Typing_inversion_e.

Ltac invert_e_typing :=
  repeat match goal with
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    let ts3 := fresh "ts3_comp" in
    let H1 := fresh "H1_comp" in
    let H2 := fresh "H2_comp" in
    apply e_composition_typing in H as [ts3 [H1 H2]]; subst;
    try repeat rewrite -catA in H1;
    try repeat rewrite -catA in H2
  | H: e_typing _ _ [:: AI_basic _] _ |- _ =>
    apply et_to_bet in H => //; simpl in H; invert_be_typing; subst
  | H: e_typing _ _ [::$V _] _ |- _ =>
    let ts := fresh "ts_value" in
    let H1 := fresh "H1_value" in
    let H2 := fresh "H2_value" in
    eapply Value_typing_inversion in H => //; eauto => //;
    destruct H as [ts [H1 H2]]; subst
  | H: e_typing _ _ (v_to_e_list _) _ |- _ =>
    let ts := fresh "ts_values" in
    let H1 := fresh "H1_values" in
    let H2 := fresh "H2_values" in
    apply Values_typing_inversion in H as [ts [H1 H2]]; subst
  | H : e_typing _ _ [:: _] _ |- _ =>
    let tf_principal := fresh "tf_principal" in
    let Htisub := fresh "Htisub" in
    let Hinvgoal := fresh "Hinvgoal" in
    apply e_typing_inversion in H as [tf_principal [Htisub Hinvgoal]]; simpl in Hinvgoal; extract_premise
  | H: e_typing _ _ (cons ?x _) _ |- _ =>
    rewrite -(cat1s x) in H
  end; invert_be_typing; resolve_list_eq.

(* Some more complicated lemmas *)
Section Typing_inversion_e.

Context `{hfc: host_function_class}.
  
(* inst_typing inversion *)
Lemma inst_t_context_local_empty: forall s i C,
    inst_typing s i = Some C ->
    tc_locals C = [::].
Proof.
  move => s i C HInstType.
  unfold inst_typing, typing.inst_typing in HInstType.
  destruct i => //=.
  by remove_bools_options.
Qed.

Lemma inst_t_context_label_empty: forall s i C,
    inst_typing s i = Some C ->
    tc_labels C = [::].
Proof.
  move => s i C HInstType.
  unfold inst_typing, typing.inst_typing in HInstType.
  destruct i => //=.
  by remove_bools_options.
Qed.

Lemma global_type_reference: forall s i j C v t,
    store_typing s ->
    inst_typing s i = Some C ->
    sglob_val s i j = Some v ->
    option_map tg_t (lookup_N (tc_globals C) j) = Some t ->
    value_typing s v t.
Proof.
  move => s i j C v t Hst HInstType Hvref Htref.
  unfold sglob_val in Hvref.
  unfold sglob in Hvref.
  unfold sglob_ind in Hvref.
  remove_bools_options.
  unfold inst_typing, typing.inst_typing in HInstType.
  destruct i => //=.
  remove_bools_options; simpl in *.
  unfold store_typing in Hst.
  destruct s; remove_bools_options.
  destruct Hst as [? [? [? [Hglobtype ?]]]].
  eapply those_lookup_inv in Hoption5; eauto.
  eapply Forall_lookup with (n := (N.to_nat g1)) in Hglobtype as [gt Hglobtype]; eauto.
  {
    unfold globalinst_typing in Hglobtype.
    destruct g0.
    rewrite List.nth_error_map in Hoption5.
    unfold ext_global_typing in Hoption5.
    remove_bools_options; simpl in *.
    unfold lookup_N in *.
    rewrite Hoption1 in Hoption8.
    injection Hoption8 as <-.
    rewrite Hoption0 in Hoption5.
    by injection Hoption5 as <-.
  }
Qed.

Lemma func_context_store: forall s i C j x,
    inst_typing s i = Some C ->
    lookup_N (tc_funcs C) j = Some x ->
    exists a, lookup_N i.(inst_funcs) j = Some a.
Proof.
  move => s i C j x HIT HN.
  unfold sfunc. unfold operations.sfunc. unfold option_bind.
  unfold sfunc_ind.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=.
  remove_bools_options; simpl in *.
  eapply those_lookup_inv in Hoption; eauto.
  unfold lookup_N in *.
  rewrite List.nth_error_map in Hoption.
  remove_bools_options.
  by eexists.
Qed.

Lemma glob_context_store: forall s i C j g,
    inst_typing s i = Some C ->
    lookup_N (tc_globals C) j = Some g ->
    sglob s i j <> None.
Proof.
  move => s i C j g HIT HN.
  unfold sglob. unfold operations.sglob. unfold option_bind.
  unfold sglob_ind.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=.
  remove_bools_options; simpl in *.
  eapply those_lookup_inv in Hoption2; eauto.
  unfold lookup_N in *.
  rewrite List.nth_error_map in Hoption2.
  unfold ext_global_typing in Hoption2.
  remove_bools_options.
  unfold lookup_N in *.
  by rewrite Hoption2.
Qed.

Lemma mem_context_store: forall s i C,
    inst_typing s i = Some C ->
    tc_mems C <> [::] ->
    exists (n: memaddr), smem_ind s i = Some n /\
              lookup_N (s_mems s) n <> None.
Proof.
  move => s i C HIT HMemory.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=. 
  remove_bools_options; simpl in *.
  destruct l1 => //.
  eapply those_lookup_inv with (i := 0) in Hoption1; eauto; last by eauto.
  rewrite List.nth_error_map in Hoption1.
  unfold ext_mem_typing in Hoption1.
  remove_bools_options; simpl in *.
  exists m0; by rewrite Hoption1.
Qed.

Lemma Lfilled_break_typing: forall n m k (lh: lholed n) vs LI ts s C t2s tss,
    e_typing s (upd_label C (tss ++ [::ts] ++ tc_labels C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfill lh (vs ++ [::AI_basic (BI_br m)]) = LI ->
    length tss = k ->
    N.of_nat (n + k) = m ->
    e_typing s C vs (Tf [::] ts).
Proof.
  move => n m k lh vs LI ts s C ts2 tss HType HConst HLength HLF <- HSum.
  subst m.
  apply const_es_exists in HConst as [xs ->].
  generalize dependent ts.
  move: ts2.
  generalize dependent LI.
  move: lh tss.
  elim.
  - move => vs es tss LI /= <- ts2 ts HType HTSSLength.
    rewrite add0n in HType.
    repeat rewrite catA in HType.
    invert_e_typing.
    unfold lookup_N in *.
    rewrite Nat2N.id list_nth_prefix in Hconjr; injection Hconjr as <-.
    eapply ety_subtyping; first by apply et_values_typing; eauto.
    simplify_subtyping.
    exists nil, nil, nil, ts; repeat split => //.
    repeat rewrite length_is_size in HTSSLength.
    rewrite v_to_e_size in HTSSLength.
    apply values_typing_length in H2_values.
    repeat rewrite length_is_size in H2_values.
    eapply values_subtyping_cat_suffix; eauto.
    by lias.
  - move => k0 vs m es lh' IH es' tss LI /= <- ts2 ts HType HTSSLength.
    rewrite - (cat1s _ es') in HType.
    invert_e_typing.
    rewrite upd_label_overwrite -cat1s catA in Hconjl1.
    remember ([::extr] ++ tss) as tss'.
    eapply ety_subtyping; first eapply IH.
    + reflexivity.
    + subst tss'. uapply Hconjl1; repeat f_equal; by lias.
    + done.
    + by resolve_subtyping.
Qed.
  
Lemma Lfilled_return_typing {k}: forall (lh: lholed k) vs LI ts s C0 C t2s,
    e_typing s C0 LI (Tf [::] t2s) ->
    tc_return C = tc_return C0 ->
    const_list vs ->
    length ts = length vs ->
    lfill lh (vs ++ [::AI_basic BI_return]) = LI ->
    Some ts = tc_return C ->
    e_typing s C vs (Tf [::] ts).
Proof.
  induction lh; move => vs LI ts s C0 C t2s HType Heqret HConst HLength /=HLF HReturn; subst => //=; invert_e_typing.
  - apply const_es_exists in HConst as [vs0 ->].
    invert_e_typing.
    rewrite Hconjr in Heqret.
    rewrite - HReturn in Heqret.
    injection Heqret as <-.
    eapply ety_subtyping; first by apply et_values_typing; eauto.
    simplify_subtyping.
    exists nil, nil, nil, ts; repeat split => //.
    apply values_typing_length in H2_values0.
    rewrite v_to_e_length in HLength.
    repeat rewrite length_is_size in H2_values0.
    repeat rewrite length_is_size in HLength.
    eapply values_subtyping_cat_suffix; eauto.
    by lias.
  - by eapply IHlh; eauto.
Qed.

Lemma Frame_return_typing {k}: forall s C vs f LI tf (lh: lholed k),
    e_typing s C [:: AI_frame (length vs) f LI] tf ->
    const_list vs ->
    lfill lh (vs ++ [::AI_basic BI_return]) = LI ->
    e_typing s C vs tf.
Proof.
  move => s C vs f LI tf lh HType HConst Hlf.
  destruct tf as [t1s t2s].
  invert_e_typing.
  inversion Hconjl0; subst; clear Hconjl0.
  remove_bools_options.
  apply const_es_exists in HConst as [? ->].
  eapply Lfilled_return_typing in H6; eauto; last by apply v_to_e_const.
  invert_e_typing.
  eapply ety_subtyping; first apply et_values_typing; eauto.
  by resolve_subtyping.
Qed.

(* Auxiliary lemmas for the tactics resolving e_typing *)
Lemma value_cons_e_typing: forall s C v t es tx ty,
    value_typing s v t ->
    e_typing s C es (Tf (tx ++ [::t]) ty) ->
    e_typing s C (cons ($V v) es) (Tf tx ty).
Proof.
  move => s C v t es tx ty Hvt Het.
  rewrite -cat1s; eapply et_composition'; eauto.
  eapply et_value_typing'; eauto.
  by resolve_subtyping.
Qed.

Lemma values_cat_e_typing: forall s C vs ts es tx ty,
    values_typing s vs ts ->
    e_typing s C es (Tf (tx ++ ts) ty) ->
    e_typing s C (v_to_e_list vs ++ es) (Tf tx ty).
Proof.
  move => s C vs ts es tx ty Hvt Het.
  eapply et_composition'; eauto.
  eapply et_values_typing'; eauto.
  by resolve_subtyping.
Qed.

Lemma value_num_cons_e_typing: forall s C v es tx ty,
    e_typing s C es (Tf (tx ++ [::T_num (typeof_num v)]) ty) ->
    e_typing s C (cons ($VN v) es) (Tf tx ty).
Proof.
  intros.
  replace ($VN v) with ($V (VAL_num v)) => //.
  eapply value_cons_e_typing; eauto.
  by apply value_num_principal_typing.
Qed.

Lemma value_vec_cons_e_typing: forall s C v es tx ty,
    e_typing s C es (Tf (tx ++ [::T_vec (typeof_vec v)]) ty) ->
    e_typing s C (cons ($V (VAL_vec v)) es) (Tf tx ty).
Proof.
  intros.
  eapply value_cons_e_typing; eauto.
  by apply value_vec_principal_typing.
Qed.

End Typing_inversion_e.
