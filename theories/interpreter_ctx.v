(** Proof-carrying interpreter for Wasm, optimised for contexts **)

From Wasm Require Import common properties opsem_properties tactic typing_inversion interpreter_func contexts.
From Coq Require Import ZArith.BinInt Program.Equality.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export operations host.
Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

Section Host.

Variable host_function: eqType.

Let host := host host_function.

Variable host_instance : host.

Let store_record := store_record host_function.
Let host_state := host_state host_instance.

Let e_typing := @e_typing host_function.
Let inst_typing := @inst_typing host_function.
Let frame_typing := @frame_typing host_function.
 

Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                       (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).

Let ctx_fill := @ctx_fill host_function host_instance.
Notation "ctx ⦃ es ⦄" := (ctx_fill _ es ctx) (at level 1).

(* Slightly ugly *)
Let valid_cfg_ctx := @valid_cfg_ctx host_function.
Let cfg_tuple_ctx := @cfg_tuple_ctx host_function.
Let label_ctx_eval := @label_ctx_eval host_function host_instance.
Let frame_ctx_eval := @frame_ctx_eval host_function host_instance.
Let closure_ctx_eval := @closure_ctx_eval host_function host_instance.
Let list_label_ctx_eval := @list_label_ctx_eval host_function host_instance.
Let list_closure_ctx_eval := @list_closure_ctx_eval host_function host_instance.
Let lh_ctx_fill_aux := @lh_ctx_fill_aux host_function host_instance.

Lemma fc_typing: forall (fc: frame_ctx) es s C0 tf,
    e_typing s C0 (fc ⦃ es ⦄) tf ->
    exists C ret,
      frame_typing s fc.(FC_frame) C /\
        length ret = fc.(FC_arity) /\
        e_typing s (upd_return C (Some ret)) es (Tf nil ret).
Proof.
  move => fc es s C [ts1 ts2] /= Htype.
  apply e_composition_typing in Htype as [? [? [? [? [-> [-> [_ Htype]]]]]]].
  rewrite -cat1s in Htype.
  apply e_composition_typing in Htype as [? [? [? [? [-> [-> [Htype _]]]]]]].
  apply Local_typing in Htype as [? [-> [Htype Hlen]]].
  inversion Htype as [??????? Hftype ? Hetype]; subst; clear Htype.
  clear - Hftype Hetype Hlen.
  by do 2 eexists; repeat split; eauto.
Qed.

Lemma lc_typing: forall (lc: label_ctx) es s C0 tf,
    e_typing s C0 (lc ⦃ es ⦄) tf ->
    exists ts1 ts2,
      e_typing s C0 (lc.(LC_cont)) (Tf ts1 ts2) /\
      length ts1 = lc.(LC_arity) /\
      e_typing s (upd_label C0 ([::ts1] ++ C0.(tc_label))) es (Tf nil ts2).
Proof.
  move => lc es s C [ts1 ts2] /= Htype.
  apply e_composition_typing in Htype as [? [? [? [? [-> [-> [_ Htype]]]]]]].
  rewrite -cat1s in Htype.
  apply e_composition_typing in Htype as [? [? [? [? [-> [-> [Htype _]]]]]]].
  apply Label_typing in Htype as [? [? [-> [Hconttype [Htype Hlen]]]]].
  by do 2 eexists; split; eauto.
Qed.

Definition lab_lc_agree (lab: list value_type) (lc: label_ctx) : bool :=
  length lab == lc.(LC_arity).

Lemma lcs_typing_exists: forall (lcs: list label_ctx) es s C0 tf,
    e_typing s C0 (lcs ⦃ es ⦄) tf ->
    exists labs ts1 ts2,
      e_typing s (upd_label C0 (labs ++ C0.(tc_label))) es (Tf ts1 ts2) /\
      all2 lab_lc_agree labs lcs /\
      (lcs <> nil -> ts1 = nil).
Proof.
  induction lcs as [|lc' lcs']; move => es s C0 [ts1 ts2] Htype.
  - exists nil, ts1, ts2.
    by destruct C0.
  - apply IHlcs' in Htype as [labs [ts1' [ts2' [Htype [Hagree Hconsume]]]]].
    apply lc_typing in Htype as [? [? [Hctype [Hartiy Htype]]]].
    simpl in *.
    rewrite upd_label_overwrite in Htype.
    rewrite -cat1s catA in Htype.
    do 3 eexists; repeat split; eauto => /=.
    apply/andP; split => //.
    by apply/eqP.
Qed.

Lemma cc_typing_exists: forall (cc: closure_ctx) es s C0 tf,
    e_typing s C0 cc ⦃ es ⦄ tf ->
    exists C ret labs ts2,
      frame_typing s (cc.1).(FC_frame) C /\
        length ret = (cc.1).(FC_arity) /\
        e_typing s (upd_label (upd_return C (Some ret)) labs) es (Tf nil ts2).
Proof.
  move => [fc lcs] es s C0 tf Htype.
  apply fc_typing in Htype as [C [ret [? [? Htype]]]].
  destruct lcs; first by do 4 eexists; repeat split; eauto.
  apply lcs_typing_exists in Htype as [labs [ts1 [ts2 [Htype [Hagree Hconsume]]]]].
  do 4 eexists; repeat split; eauto.
  by rewrite Hconsume in Htype => //; eauto.
Qed.

Lemma ccs_typing_exists: forall cc ccs es s C0 tf,
    e_typing s C0 (cc :: ccs) ⦃ es ⦄ tf ->
    exists C ret labs ts2,
      frame_typing s (cc.1).(FC_frame) C /\
        length ret = (cc.1).(FC_arity) /\
        e_typing s (upd_label (upd_return C (Some ret)) labs) es (Tf nil ts2).
Proof.
  move => cc ccs.
  move: cc.
  induction ccs as [| cc' ccs']; move => [fc lcs] es s C0 tf Htype.
  - by eapply cc_typing_exists; eauto.
  - apply IHccs' in Htype as [? [? [? [? [? [??]]]]]].
    by eapply cc_typing_exists; eauto.
Qed.

Lemma ccs_typing_focus: forall cc ccs es s C0 tf,
    e_typing s C0 (cc :: ccs) ⦃ es ⦄ tf ->
    exists C ret labs tf,
     e_typing s (upd_label (upd_return C ret) labs) (cc ⦃ es ⦄) tf.
Proof.
  move => cc ccs.
  move: cc.
  induction ccs as [| cc' ccs']; move => [fc lcs] es s C0 tf Htype.
  - exists C0, (tc_return C0), (tc_label C0), tf.
    by destruct C0.
  - apply IHccs' in Htype as [? [? [? [? Htype]]]].
    apply cc_typing_exists in Htype as [C [ret [lab [ts2 [Hftype [Hlen Htype]]]]]].
    exists C, (Some ret), lab, (Tf nil ts2).
    by apply Htype.
Qed.

Lemma sc_typing_args: forall (sc: seq_ctx) es s C ts0,
    e_typing s C (sc ⦃ es ⦄) (Tf nil ts0) ->
    exists k ts2, e_typing s C es (Tf (map typeof (drop k (rev sc.1))) ts2).
Proof.
  move => [vs0 es0] es s C ts0 /=Htype.
  apply e_composition_typing in Htype as [ts1 [ts2 [ts3 [ts4 [Heq [? [Htype1 Htype2]]]]]]].
  destruct ts1, ts2 => //; subst; clear Heq.
  apply et_to_bet in Htype1; last by apply const_list_is_basic, v_to_e_const.
  apply Const_list_typing in Htype1 as ->.
  simpl in Htype2.
  apply e_composition_typing in Htype2 as [ts1 [ts2 [ts4 [ts5 [Heq [-> [Htype _]]]]]]].
  exists (size ts1), ts5.
  by rewrite map_drop Heq drop_size_cat.
Qed.

Lemma e_typing_ops: forall (ccs: list closure_ctx) (sc: seq_ctx) es s C0 ts0,
    e_typing s C0 (ccs ⦃ sc ⦃ es ⦄ ⦄) (Tf nil ts0) ->
    exists C' k ts, e_typing s C' es (Tf (map typeof (drop k (rev sc.1))) ts).
Proof.
  move => ccs [vs0 es0] es s C0 ts0.
  destruct ccs as [ | cc' ccs']; move => Htype.
  - apply sc_typing_args in Htype as [? [? Htype]].
    by do 3 eexists; eauto.
  - apply ccs_typing_exists in Htype as [? [? [? [? [? [? Htype]]]]]].
    apply sc_typing_args in Htype as [? [? Htype]].
    by do 3 eexists; eauto.
Qed.

Lemma e_typing_ops_local: forall cc (ccs: list closure_ctx) (sc: seq_ctx) es s C0 tf,
    e_typing s C0 ((cc :: ccs) ⦃ sc ⦃ es ⦄ ⦄) tf ->
    exists C C' ret labs k ts,
      frame_typing s (cc.1).(FC_frame) C /\
        length ret = (cc.1).(FC_arity) /\
        C' = (upd_label (upd_return C (Some ret)) labs) /\
        e_typing s C' es (Tf (map typeof (drop k (rev sc.1))) ts).
Proof.
  move => cc ccs [vs0 es0] es s C0 tf Htype.
  - apply ccs_typing_exists in Htype as [? [? [? [? [? [? Htype]]]]]].
    apply sc_typing_args in Htype as [? [? Htype]].
    by do 6 eexists; eauto.
Qed.

Definition empty_t_context := Build_t_context nil nil nil nil nil nil nil None.

Lemma config_typing_empty_inv: forall s es ts (C: t_context),
    config_typing s empty_frame es ts ->
    C = empty_t_context ->
    store_typing s /\ e_typing s C es (Tf [::] ts).
Proof.
  move => s es ts C Htype ?; subst.
  inversion Htype as [???? Hstype Htype']; subst; split => //; clear Hstype Htype.
  inversion Htype' as [?????? C0 Hftype ? Htype _]; subst; clear Htype'.
  inversion Hftype as [????? Hinsttype]; subst; clear Hftype.
  destruct C; simpl in *.
  by destruct tc_local, tc_label, tc_return => //; destruct tc_types_t, tc_func_t, tc_global, tc_table, tc_memory => //.
Qed.


Definition reduce_ctx (hs hs': host_state) (cfg cfg': cfg_tuple_ctx) : Prop :=
  match cfg with
  | (s, ccs, sc, oe) =>
      match cfg' with
      | (s', ccs', sc', oe') => reduce hs s empty_frame (ccs ⦃ sc ⦃ olist oe ⦄ ⦄) hs' s' empty_frame (ccs' ⦃ sc' ⦃ olist oe' ⦄ ⦄)
      end
  end.

Ltac red_ctx_simpl :=
  repeat lazymatch goal with
  | |- reduce _ _ _ (((_, ?lcs) :: ?ccs) ⦃ _ ⦃ _ ⦄ ⦄) _ _ _ (((_, ?lcs) :: ?ccs) ⦃ _ ⦃ _ ⦄ ⦄) =>
      apply reduce_focus_ctx_id
  | |- reduce _ _ _ (((_, _) :: ?ccs) ⦃ _ ⦃ _ ⦄ ⦄) _ _ _ (((_, _) :: ?ccs) ⦃ _ ⦃ _ ⦄ ⦄) =>
      apply reduce_focus_ctx
  | |- reduce _ _ _ (?ccs ⦃ _ ⦃ _ ⦄ ⦄) _ _ _ (?ccs ⦃ _ ⦃ _ ⦄ ⦄) =>
      apply (list_closure_ctx_eval.(ctx_reduce))
  | |- reduce _ _ _ (foldl (@closure_ctx_fill _ _) _ _) _ _ _ (foldl (@closure_ctx_fill _ _) _ _) =>
      apply (list_closure_ctx_eval.(ctx_reduce))
  | |- reduce _ _ _ (foldl label_ctx_fill _ _) _ _ _ (foldl label_ctx_fill _ _) =>
      apply (list_label_ctx_eval.(ctx_reduce))
  end.

Ltac infer_hole :=
  repeat lazymatch goal with
  | |- context C [vs_to_es _] =>
      rewrite /vs_to_es
  | |- ?l1 ++ ?l2 = ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?l2 =>
      try by instantiate (1 := [::x1; x2; x3; x4]) => //
  | |- ?l1 ++ ?l2 = ?x1 :: ?x2 :: ?x3 :: ?l2 =>
      try by instantiate (1 := [::x1; x2; x3]) => //
  | |- ?l1 ++ ?l2 = ?x1 :: ?x2 :: ?l2 =>
      try by instantiate (1 := [::x1; x2]) => //
  | |- ?l1 ++ ?l2 = ?x :: ?l2 =>
      try by instantiate (1 := [::x]) => //
  | |- ?l ++ ?les = ?les =>
      try by instantiate (1 := nil) => //
  | |- ?l1 ++ ?l2 = ?l3 ++ ?x :: ?l2 =>
      try instantiate (1 := l3 ++ [::x]); rewrite -catA => //
  | _: _ |- ?l ++ _ = ?l ++ _ =>
      f_equal => //
  | |- context C [ _ ++ [::] ] =>
      rewrite cats0
  | |- context C [v_to_e_list (rev (?x :: ?l2))] =>
      rewrite rev_cons -cats1 -v_to_e_cat => //
  | |- context C [v_to_e_list (rev (?l1 ++ ?l2))] =>
      rewrite rev_cat -v_to_e_cat => //
  | |- context C [v_to_e_list [:: ?x] ] =>
      unfold v_to_e_list, v_to_e => //=
  | |- context C [ ( _ ++ _) ++ _ ] =>
      rewrite -catA
  end.

Ltac resolve_reduce_ctx vs es :=
  (* Sometimes 1 infer_hole isn't enough, which supposedly shouldn't occur *)
  unfold reduce_ctx; red_ctx_simpl => //=; try (eapply r_label with (lh := LH_base (rev vs) es) => /=; do 2 infer_hole => /=).

Ltac resolve_valid_ccs :=
  repeat lazymatch goal with
    | |- _ /\ _ =>
        split => //
    | |- context C [valid_ccs _] =>
        unfold valid_ccs => /=
    | |- context C [ (_ || _) ] =>
        apply/orP; (try by left); (try by right)
    end.

Definition s_of_cfg (cfg: cfg_tuple_ctx) :=
  match cfg with
  | (s, _, _, _) => s
  end.

Definition es_of_cfg (cfg: cfg_tuple_ctx) :=
  match cfg with
  | (_, ccs, sc, oe) => ccs ⦃ sc ⦃ olist oe ⦄ ⦄
  end.

Inductive run_step_ctx_result (hs: host_state) (cfg: cfg_tuple_ctx): Type :=
| RSC_normal hs' cfg':
  reduce_ctx hs hs' cfg cfg' ->
  run_step_ctx_result hs cfg
| RSC_value vs:
  es_of_cfg cfg = v_to_e_list vs ->
  run_step_ctx_result hs cfg
| RSC_invalid :
  (valid_cfg_ctx cfg -> False) ->
  run_step_ctx_result hs cfg
| RSC_error:
  (forall ts, config_typing (s_of_cfg cfg) empty_frame (es_of_cfg cfg) ts -> False) ->
  run_step_ctx_result hs cfg
.


Ltac resolve_invalid_typing :=
  apply RSC_error;
  let ts := fresh "ts" in
  let ts' := fresh "ts'" in
  let Htype := fresh "Htype" in
  let Hftype := fresh "Hftype" in
  let Hstype := fresh "Hstype" in
  intros ts Htype; unfold s_of_cfg, es_of_cfg in Htype;
  eapply config_typing_empty_inv in Htype as [Hstype Htype]; eauto;
  match type of Htype with
  | e_typing _ _ ((_ :: _) ⦃ _ ⦃ _ ⦄ ⦄) _ =>
    apply e_typing_ops_local in Htype as [? [? [? [? [? [ts' [Hftype [? [? Htype]]]]]]]]]
  | e_typing _ _ (_ ⦃ _ ⦃ _ ⦄ ⦄) (Tf nil _) =>
    apply e_typing_ops in Htype as [? [? [ts' Htype]]]
  end;
  simpl in Htype;
  try (apply et_to_bet in Htype; last by auto_basic).

Ltac last_unequal H :=
  apply (f_equal rev) in H;
  repeat rewrite rev_cat in H;
  repeat rewrite -map_rev in H;
  repeat rewrite rev_drop in H;
  repeat rewrite revK in H;
  repeat rewrite size_rev in H;
  repeat rewrite map_take in H;
  simpl in H;
  match type of H with
  | context C [take ?n _] =>
      try by destruct n
  end.

Notation "<< hs , cfg >>" := (@RSC_normal _ _ hs cfg).

Ltac get_cc ccs :=
  let fc := fresh "fc" in 
  let lcs := fresh "lcs" in 
  let ccs' := fresh "ccs'" in 
  destruct ccs as [ | [fc lcs] ccs']; first by apply RSC_invalid => /=; unfold valid_ccs; move => [??].

Definition empty_label_ctx := Build_label_ctx nil 0 nil nil.

Lemma nth_nth_error {T: Type}: forall (l: list T) k x0 v,
    List.nth_error l k = Some v ->
    nth x0 l k = v.
Proof.
  elim; first by case => //.
  move => ???; case => //=.
  by move => ?? [<-].
Qed.

Definition run_ctx_br: forall hs s ccs sc j,
  run_step_ctx_result hs (s, ccs, sc, Some (AI_basic (BI_br j))).
Proof.
  intros hs s ccs [vs es] j.
  get_cc ccs.
  destruct (j < length lcs) eqn:Hlablen.
  - destruct (List.nth_error lcs j) as [lab | ] eqn:Htar; last by apply List.nth_error_None in Htar; move/ltP in Hlablen; lias.
    destruct lab as [lvs lk lces les].
    destruct (lk <= length vs) eqn:Hvslen.
    + apply <<hs, (s, ((fc, drop (S j) lcs) :: ccs'), (take lk vs ++ lvs, lces ++ les), None)>>.
      apply reduce_focus_ctx => //=.
      rewrite - (cat_take_drop (j.+1) lcs) drop_size_cat; last by rewrite size_takel => //.
      rewrite foldl_cat.
      apply list_label_ctx_eval.(ctx_reduce) => //=.
      rewrite /fmask0.
      rewrite (take_nth empty_label_ctx) => //.
      rewrite foldl_rcons.
      apply nth_nth_error with (x0 := empty_label_ctx) in Htar.
      rewrite Htar => /=.
      rewrite - (cat_take_drop lk vs) take_size_cat; last by rewrite size_takel => //.
      rewrite /vs_to_es rev_cat -v_to_e_cat rev_cat -v_to_e_cat -cat1s -catA.
      resolve_reduce_ctx lvs les; last rewrite catA; eauto => //=.
      simpl.
      apply r_simple; eapply rs_br.
      { by apply v_to_e_const. }
      { by rewrite v_to_e_length length_is_size size_rev size_takel. }
      { apply lh_ctx_fill_aux with (acc := (LH_base (rev (drop lk vs)) es)) (lcs := take j lcs) => /=.
        rewrite ctx_to_lh_aux_len => /=.
        repeat rewrite - catA => /=.
        rewrite add0n length_is_size size_takel; rewrite length_is_size in Hlablen; by lias => //=.
      }
      
    + (* Not enough values *)
      apply RSC_error.
      destruct lcs as [| lc lcs] => //.
      intros ts Htype; unfold s_of_cfg, es_of_cfg in Htype.
      eapply config_typing_empty_inv in Htype as [Hstype Htype]; eauto.
      apply ccs_typing_focus in Htype as [? [? [? [tf Htype]]]].
      apply fc_typing in Htype as [? [? [Hftype [Hlen Htype]]]].
      apply lcs_typing_exists in Htype as [labs [ts1 [ts2 [Htype [Hagree Hconsume]]]]].
      rewrite -> Hconsume in * => //; clear Hconsume.
      apply sc_typing_args in Htype as [k [ts3 Htype]]; simpl in Htype.
      apply et_to_bet in Htype; last by auto_basic.
      simpl in Htype; invert_be_typing.
      unfold plop2 in H2_br; move/eqP in H2_br.
      inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
      destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
      apply inst_t_context_label_empty in Hit; rewrite -> Hit, cats0 in *; simpl in *; clear Hit.
      eapply all2_projection in Hagree; eauto.
      move/eqP in Hagree; simpl in Hagree; subst.
      apply (f_equal size) in H3_br.
      rewrite size_map size_cat drop_rev size_rev size_takel in H3_br; last by lias.
      repeat rewrite length_is_size in Hvslen.
      by lias.
      
  - (* Not enough labels *)
    apply RSC_error.
    intros ts Htype; unfold s_of_cfg, es_of_cfg in Htype.
    eapply config_typing_empty_inv in Htype as [Hstype Htype]; eauto.
    apply ccs_typing_focus in Htype as [? [? [? [tf Htype]]]].
    apply fc_typing in Htype as [? [? [Hftype [Hlen Htype]]]].
    apply lcs_typing_exists in Htype as [labs [ts1 [ts2 [Htype [Hagree Hconsume]]]]].
    simpl in Htype.
    apply e_composition_typing in Htype as [? [? [? [? [? [? [Htype1 Htype2]]]]]]]; subst.
    rewrite -cat1s in Htype2.
    apply e_composition_typing in Htype2 as [? [? [? [? [? [? [Htype3 Htype4]]]]]]]; subst.
    apply et_to_bet in Htype3; last by auto_basic.
    simpl in Htype3; invert_be_typing.
    inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
    destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
    apply inst_t_context_label_empty in Hit; rewrite -> Hit in *; simpl in *.
    apply all2_size in Hagree.
    rewrite length_is_size in Hlablen.
    rewrite cats0 in H1_br.
    by rewrite Hagree in H1_br; lias.
Defined.
    
Definition run_ctx_return: forall hs s ccs sc,
  run_step_ctx_result hs (s, ccs, sc, Some (AI_basic BI_return)).
Proof.  
  intros hs s ccs [vs es].
  get_cc ccs.
  destruct fc as [lvs lk lf les].
  destruct (lk <= length vs) eqn:Hvslen.
  - apply <<hs, (s, ccs', (take lk vs ++ lvs, les), None)>> => /=.
    rewrite - (cat_take_drop lk vs) take_size_cat; last by rewrite size_takel => //.
    rewrite /vs_to_es rev_cat -v_to_e_cat rev_cat -v_to_e_cat -cat1s -catA.
    resolve_reduce_ctx lvs les; last rewrite catA; eauto => //=.
    apply r_simple; eapply rs_return.
    { by apply v_to_e_const. }
    { by rewrite v_to_e_length length_is_size size_rev size_takel. }
    { apply lh_ctx_fill_aux with (acc := (LH_base (rev (drop lk vs)) es)) (lcs := lcs) => /=.
      by repeat rewrite - catA => /=.
    }
  - (* Not enough values *)
    resolve_invalid_typing; simpl in Htype; invert_be_typing.
    simpl in *; subst.
    injection H2_return as ->.
    apply (f_equal size) in H1_return.
    rewrite size_map size_cat drop_rev size_rev size_takel in H1_return; last by lias.
    repeat rewrite length_is_size in Hvslen.
    by lias.
Defined.
    
(* Invoke does not need a frame context. This is useful for handling the starting invocation of a module *)
Definition run_ctx_invoke hs s ccs vs0 es0 a:
    run_step_ctx_result hs (s, ccs, (vs0, es0), Some (AI_invoke a)).
Proof.
  destruct (List.nth_error s.(s_funcs) a) as [cl|] eqn:?.
  - (* Some cl *)
    destruct cl as [i [t1s t2s] ts es | [t1s t2s] cl'] eqn:?.
    + (* FC_func_native i (Tf t1s t2s) ts es *)
      remember (length t1s) as n eqn:?.
      remember (length t2s) as m eqn:?.
      destruct (length vs0 >= n) eqn:Hlen.
      * (* true *)
        destruct (split_n vs0 n) as [vs' vs''] eqn:Hsplit.
        remember (n_zeros ts) as zs eqn:?.
        apply <<hs, (s, (Build_frame_ctx vs'' m (Build_frame (rev vs' ++ zs) i) es0, nil) :: ccs, (nil, nil), Some (AI_basic (BI_block (Tf [::] t2s) es)))>> => /=.
        red_ctx_simpl => //=.
        rewrite split_n_is_take_drop in Hsplit.
        injection Hsplit as ??.
        eapply r_label with (lh := LH_base (rev vs'') es0) => /=; subst; infer_hole.
        2: { instantiate (1 := (v_to_e_list (rev (take (length t1s) vs0)) ++ [::AI_invoke a])).
             by rewrite catA catA v_to_e_cat -rev_cat cat_take_drop -catA.
        }
        eapply r_invoke_native; eauto.
        repeat rewrite length_is_size.
        repeat rewrite length_is_size in Hlen.
        by rewrite size_rev size_takel => //.
      * (* not enough arguments *)
        resolve_invalid_typing.
        eapply Invoke_func_native_typing in Htype as [ts1 [C' [Hvstype [? [Hit Hbet]]]]]; eauto; subst.
        apply (f_equal size) in Hvstype.
        rewrite size_map size_cat drop_rev size_rev size_takel in Hvstype; last by lias.
        repeat rewrite length_is_size in Hlen.
        by lias.
    + (* FC_func_host (Tf t1s t2s) cl' *)
      remember (length t1s) as n eqn:?.
      remember (length t2s) as m eqn:?.
      destruct (length vs0 >= n) eqn:Hlen.
      * (* true *)
        destruct (split_n vs0 n) as [vs' vs''] eqn: Hsplit.
        destruct (host_application_impl hs s (Tf t1s t2s) cl' (rev vs')) as [hs' [[s' rves]|]] eqn:?.
        -- (* (hs', Some (s', rves)) *)
          destruct rves as [rvs | ].
          ++ apply <<hs', (s', ccs, (rev rvs ++ vs'', es0), None)>> => /=.
             red_ctx_simpl => //.
             rewrite split_n_is_take_drop in Hsplit.
             injection Hsplit as ??.
             eapply r_label with (lh := LH_base (rev vs'') es0) => /=; subst; infer_hole.
             2: { instantiate (1 := (v_to_e_list (rev (take (length t1s) vs0)) ++ [::AI_invoke a])).
                  by rewrite catA catA v_to_e_cat -rev_cat cat_take_drop -catA.
             }
             rewrite revK.
             unfold fmask0 => /=.
             fold (result_to_stack (result_values rvs)).
             eapply r_invoke_host_success; eauto.
             repeat rewrite length_is_size.
             by rewrite size_rev size_takel => //.
          ++ apply <<hs', (s', ccs, (vs'', es0), Some AI_trap)>> => /=.
             red_ctx_simpl => //.
             rewrite split_n_is_take_drop in Hsplit.
             injection Hsplit as ??.
             eapply r_label with (lh := LH_base (rev vs'') es0) => /=; subst; infer_hole.
             2: { instantiate (1 := (v_to_e_list (rev (take (length t1s) vs0)) ++ [::AI_invoke a])).
                  by rewrite catA catA v_to_e_cat -rev_cat cat_take_drop -catA.
             }
             unfold fmask0 => /=.
             fold (result_to_stack result_trap).
             eapply r_invoke_host_success; eauto.
             repeat rewrite length_is_size.
             by rewrite size_rev size_takel => //.
  - (* (hs', None) *)
    apply <<hs', (s, ccs, (vs'', es0), Some AI_trap)>> => /=.
    red_ctx_simpl => //.
    rewrite split_n_is_take_drop in Hsplit.
    injection Hsplit as ??.
    eapply r_label with (lh := LH_base (rev vs'') es0) => /=; subst; infer_hole.
    2: { instantiate (1 := (v_to_e_list (rev (take (length t1s) vs0)) ++ [::AI_invoke a])).
         by rewrite catA catA v_to_e_cat -rev_cat cat_take_drop -catA.
    }
    unfold fmask0 => /=.
    eapply r_invoke_host_diverge; eauto.
    repeat rewrite length_is_size.
    by rewrite size_rev size_takel => //.
    * (* false *)
      resolve_invalid_typing.
      eapply Invoke_func_host_typing in Htype as [ts1 [Hvstype ?]]; eauto; subst.
      apply (f_equal size) in Hvstype.
      rewrite size_map size_cat drop_rev size_rev size_takel in Hvstype; last by lias.
      repeat rewrite length_is_size in Hlen.
      by lias.
  - (* None *)
    resolve_invalid_typing.
    eapply Invoke_func_typing in Htype as [cl Hnth]; eauto.
    by rewrite Hnth in Heqo.
Defined.

(* One step of execution; does not perform the context update in the end to shift to the new instruction. *)
Definition run_one_step_ctx (hs: host_state) (cfg: cfg_tuple_ctx) : run_step_ctx_result hs cfg.
Proof.
  destruct cfg as [[[s ccs] sc] oe].
  destruct oe as [e | ]; last first.
  (* Exitting from contexts *)
  {
  (*  unfold valid_cfg_ctx in Hvalid; destruct sc as [vs es]; subst; simpl in Hvalid.
    destruct Hvalid as [? Heq]; move/eqP in Heq; subst es.*)
    destruct sc as [vs es]; subst.
    destruct es as [ | ??]; last by apply RSC_invalid => /=; move => [??].
    destruct ccs as [ | [fc lcs] ccs'].
    { (* entire instruction is const *)
      by apply (@RSC_value _ _ (rev vs)) => /=; rewrite cats0.
    }
    { destruct lcs as [ | lc lcs'].
      (* Exitting a local *)
      {
        destruct fc as [lvs lk lf les].
        destruct (length vs == lk) eqn:Hlen; move/eqP in Hlen.
        {
          destruct les as [ | e les'].
          { (* No instruction in the hole *)
            apply <<hs, (s, ccs', (vs ++ lvs, nil), None)>> => /=.
            resolve_reduce_ctx lvs (nil: list administrative_instruction).
            by apply r_simple, rs_local_const; [ by apply v_to_e_const | by rewrite length_is_size v_to_e_size size_rev ].
          }
          { (* e is in the hole *)
          (*  remember (ctx_update ccs' (vs ++ lvs, les') e) as cfg_new; symmetry in Heqcfg_new.
            destruct cfg_new as [[[ccs0 [vs0 es0]] oe] | ].
            - destruct (valid_ccs ccs0 oe) eqn:Hccsnil. *)
            apply <<hs, (s, ccs', (vs ++ lvs, les'), Some e)>> => /=.
            resolve_reduce_ctx lvs (e :: les').
            by apply r_simple, rs_local_const; [ by apply v_to_e_const | by rewrite length_is_size v_to_e_size size_rev ].
          }
        }
        (* length doesn't match -- ill-typed *)
        {
          apply RSC_error.
          intros ts Htype; unfold s_of_cfg, es_of_cfg in Htype.
          eapply config_typing_empty_inv in Htype as [Hstype Htype]; eauto.
          apply ccs_typing_focus in Htype as [C [? [? [[ts1 ts2] Htype]]]].
          rewrite /= cats0 in Htype.
          apply e_composition_typing in Htype as [ts' [ts1' [ts2' [ts3 [? [? [Htype1 Htype2]]]]]]]; subst.
          rewrite -cat1s in Htype2.
          apply e_composition_typing in Htype2 as [? [? [? [? [? [? [Htype3 Htype4]]]]]]]; subst.
          apply Local_typing in Htype3 as [? [? [Htype ?]]]; subst.
          inversion Htype as [????????? Hvstype]; subst; clear Htype.
          apply et_to_bet in Hvstype; last by apply const_list_is_basic, v_to_e_const.
          apply Const_list_typing in Hvstype; subst; simpl in *.
          by repeat rewrite length_is_size in Hlen; rewrite size_map size_rev in Hlen.
        }
      }
      (* Exitting a label *)
      { destruct lc as [lvs lk lces les].
        destruct les as [ | e les'].
        { (* No instruction in the hole still *)
          apply <<hs, (s, (fc, lcs') :: ccs', (vs ++ lvs, nil), None)>> => /=.
          resolve_reduce_ctx (FC_val fc) (FC_post fc).
          eapply r_local.
          red_ctx_simpl => //=.
          unfold fmask0, label_ctx_fill => /=.
          eapply r_label with (lh := LH_base (rev lvs) nil) => /=; infer_hole; eauto => /=.
          apply r_simple, rs_label_const; by apply v_to_e_const.
        }
        { (* e is in the hole *)
          apply <<hs, (s, (fc, lcs') :: ccs', (vs ++ lvs, les'), Some e)>> => /=.
          resolve_reduce_ctx (FC_val fc) (FC_post fc).
          apply r_local => /=.
          red_ctx_simpl => //=.
          unfold fmask0, label_ctx_fill => /=.
          eapply r_label with (lh := LH_base (rev lvs) (e :: les')) => /=; infer_hole.
          apply r_simple, rs_label_const; by apply v_to_e_const.
        }
      }
    }
  }
  (* Execute an instruction *)
  { destruct e as [
      (* AI_basic *) [
      (* BI_unreachable *) |
      (* BI_nop *) |
      (* BI_drop *) |
      (* BI_select *) |
      (* BI_block (Tf t1s t2s) es *) [t1s t2s] es |
      (* BI_loop (Tf t1s t2s) es *) [t1s t2s] es |
      (* BI_if tf es1 es2 *) [t1s t2s] es1 es2 |
      (* BI_br j *) j |
      (* BI_br_if j *) j |
      (* BI_br_table js j *) js j |
      (* BI_return *) |
      (* BI_call j *) j |
      (* BI_call_indirect j *) j |
      (* BI_get_local j *) j |
      (* BI_set_local j *) j |
      (* BI_tee_local j *) j |
      (* BI_get_global j *) j |
      (* BI_set_global j *) j |
      (* BI_load t [Some (tp, sx)|None] a off *) t ops(*[[tp sx]|]*) a off |
      (* BI_store t [Some tp|None] a off *) t op(*[tp|]*) a off |
      (* BI_current_memory *) |
      (* BI_grow_memory *) |
      (* BI_const _ *) |
      (* BI_unop t op *) t op |
      (* BI_binop t op *) t op |
      (* BI_testop [T_i32|T_i64|T_f32|T_f64] testop *) t(*[| | |]*) testop |
      (* BI_relop t op *) t op |
      (* BI_cvtop t2 [CVO_convert|CVO_reinterpret] t1 sx *) t2 cvtop (*[|]*) t1 sx ] |
      (* AI_trap *) |
      (* AI_invoke a *) a |
      (* AI_label ln les es *) ln les es |
      (* AI_local ln lf es *) ln lf es ]; destruct sc as [vs0 es0].

    - (* AI_basic BI_unreachable *)
      apply <<hs, (s, ccs, (vs0, es0), Some AI_trap)>> => /=.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_unreachable.

    - (* AI_basic BI_nop *)
      apply <<hs, (s, ccs, (vs0, es0), None)>> => /=.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_nop.

    - (* AI_basic BI_drop *)
      destruct vs0 as [ | v vs0].
      + (* [::] *)
        resolve_invalid_typing; simpl in Htype; invert_be_typing.
        by destruct ts'.
      + (* v :: vs0 *)
        apply <<hs, (s, ccs, (vs0, es0), None)>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_drop.
      
    - (* AI_basic BI_select *)
      destruct vs0 as [|v3 [|v2 [|v1 vs0]]].
      (* Not enough arguments *)
      1,2,3: resolve_invalid_typing; simpl in Htype; invert_be_typing; try by size_unequal H1_select.
      (* [:: v3, v2, v1 & vs0] *)
      destruct v3 as [c| | |] eqn:?.
      (* Conclude a contradiction by comparing the last element. However, `last` computes very badly *)
      2,3,4: resolve_invalid_typing; simpl in Htype; invert_be_typing; by last_unequal H1_select.
      (* VAL_int32 c *)
      destruct (c == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
      + (* true *)
        apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_const v2)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_select_false.
      + (* false *)
        apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_const v1)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_select_true.
      

    - (* AI_basic (BI_block (Tf t1s t2s) es) *)
      destruct (length vs0 >= length t1s) eqn:Hlen.
      + (* true *)
        destruct (split_n vs0 (length t1s)) as [ves' ves''] eqn:Hsplit.
        remember (AI_label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)) as e'.
        apply <<hs, (s, ccs, (ves'', es0), Some e')>> => /=.
        red_ctx_simpl => //.
        rewrite split_n_is_take_drop in Hsplit; injection Hsplit as ??; subst.
        eapply r_label with (lh := LH_base (rev (drop (length t1s) vs0)) es0) => /=; infer_hole => /=.
        2: { instantiate (1 := (v_to_e_list (rev (take (length t1s) vs0))) ++ [::AI_basic (BI_block (Tf t1s t2s) es)]).
             repeat rewrite catA.
             rewrite v_to_e_cat -rev_cat cat_take_drop.
             by infer_hole.
        }
        apply r_simple; eapply rs_block; eauto; first by apply v_to_e_const.
        rewrite v_to_e_length.
        repeat rewrite length_is_size.
        repeat rewrite length_is_size in Hlen.
        by rewrite size_rev size_takel.
      + (* false *)
        resolve_invalid_typing.
        simpl in Htype; invert_be_typing.
        apply (f_equal size) in H1_block.
        rewrite size_map size_cat drop_rev size_rev size_takel in H1_block; last by lias.
        repeat rewrite length_is_size in Hlen.
        by lias.

    - (* AI_basic (BI_loop (Tf t1s t2s) es) *)
      destruct (length vs0 >= length t1s) eqn:Hlen.
      + (* true *)
        destruct (split_n vs0 (length t1s)) as [ves' ves''] eqn:Hsplit.
        remember (AI_label (length t1s) [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs_to_es ves' ++ to_e_list es)) as e'.
        apply <<hs, (s, ccs, (ves'', es0), Some e')>> => /=.
        red_ctx_simpl => //.
        rewrite split_n_is_take_drop in Hsplit; injection Hsplit as ??; subst.
        eapply r_label with (lh := LH_base (rev (drop (length t1s) vs0)) es0) => /=; infer_hole => /=.
        2: { instantiate (1 := (v_to_e_list (rev (take (length t1s) vs0))) ++ [::AI_basic (BI_loop (Tf t1s t2s) es)]).
             repeat rewrite catA.
             rewrite v_to_e_cat -rev_cat cat_take_drop.
             by infer_hole.
        }
        apply r_simple; eapply rs_loop; eauto; first by apply v_to_e_const.
        rewrite v_to_e_length.
        repeat rewrite length_is_size.
        repeat rewrite length_is_size in Hlen.
        by rewrite size_rev size_takel.
      + (* false *)
        resolve_invalid_typing.
        simpl in Htype; invert_be_typing.
        apply (f_equal size) in H1_loop.
        rewrite size_map size_cat drop_rev size_rev size_takel in H1_loop; last by lias.
        repeat rewrite length_is_size in Hlen.
        by lias.

    - (* AI_basic (BI_if tf es1 es2) *)
      destruct vs0 as [|v vs0].
      resolve_invalid_typing; simpl in Htype; invert_be_typing; by size_unequal H1_if.
      (* v :: ves' *)
      destruct v as [c| | |].
      2,3,4: resolve_invalid_typing; simpl in Htype; invert_be_typing; by last_unequal H1_if.
      (* VAL_int32 c *)
      destruct (c == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
      + (* true *)
        apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_block (Tf t1s t2s) es2)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_if_false.
      + (* false *)
        apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_block (Tf t1s t2s) es1)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_if_true.

    - (* AI_basic (BI_br j) *)
      by apply run_ctx_br.

    - (* AI_basic (BI_br_if j) *)
      destruct vs0 as [|v vs0]; first by resolve_invalid_typing; simpl in Htype; invert_be_typing; size_unequal H2_brif.
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?.
      2,3,4: resolve_invalid_typing; simpl in Htype; invert_be_typing; by last_unequal H2_brif.
      (* VAL_int32 c *)
      destruct (c == Wasm_int.int_zero i32m) eqn:Heqc; move/eqP in Heqc.
      + (* 0 *)
        apply <<hs, (s, ccs, (vs0, es0), None)>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_br_if_false.
      + (* not 0 *)
        apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_br j)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_br_if_true.

    - (* AI_basic (BI_br_table js j) *)
      destruct vs0 as [|v vs0]; first by resolve_invalid_typing; simpl in Htype; invert_be_typing; size_unequal H1_brtable.
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?.
      2,3,4: resolve_invalid_typing; simpl in Htype; invert_be_typing; by last_unequal H1_brtable.
      remember (Wasm_int.nat_of_uint i32m c) as k.
      destruct (k < length js) eqn:Hlen.
      + (* true *)
        destruct (List.nth_error js k) as [js_at_k|] eqn: Hnth.
        * (* Some js_at_k *)
          apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_br js_at_k)))>> => /=.
          resolve_reduce_ctx vs0 es0.
          by apply r_simple; subst; apply rs_br_table.
        * (* None *)
          apply List.nth_error_None in Hnth.
          by lias.
      + (* false *)
        apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_br j)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; subst; apply rs_br_table_length; lias.
        
    - (* AI_basic BI_return *)
      by apply run_ctx_return.

    - (* AI_basic (BI_call j) *)
      get_cc ccs.
      destruct (List.nth_error fc.(FC_frame).(f_inst).(inst_funcs) j) as [a|] eqn: Hnth.
      + (* Some a *)
        apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_invoke a))>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_call.
      + (* None *)
        resolve_invalid_typing; simpl in Htype; invert_be_typing.
        inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
        destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
        eapply func_context_store in Hit as [? Hnth']; eauto.
        by rewrite Hnth in Hnth'.

    - (* AI_basic (BI_call_indirect j) *)
      get_cc ccs.    
      destruct vs0 as [|v vs0]; first by resolve_invalid_typing; simpl in Htype; invert_be_typing; size_unequal H4_callindirect.
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?.
      2,3,4: resolve_invalid_typing; simpl in Htype; invert_be_typing; by last_unequal H4_callindirect.
      (* VAL_int32 c *)
      remember (fc.(FC_frame)) as f.
      destruct (stab_addr s f (Wasm_int.nat_of_uint i32m c)) as [a|] eqn:?.
      + (* Some a *)
        destruct (List.nth_error s.(s_funcs) a) as [cl|] eqn:?.
        * (* Some cl *)
           destruct (stypes s f.(f_inst) j == Some (cl_type cl)) eqn:Hcl; move/eqP in Hcl.
           -- (* true *)
             apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_invoke a))>>.
             resolve_reduce_ctx vs0 es0.
             by eapply r_call_indirect_success; subst; eauto.
           -- (* false *)
             apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_trap))>>.
             resolve_reduce_ctx vs0 es0.
             by eapply r_call_indirect_failure1; subst; eauto.
        * (* None *)
          resolve_invalid_typing; simpl in Htype; invert_be_typing.
          inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
          destruct fc as [fvs fk ff fes]; simpl in *.
          eapply store_typing_stabaddr in Hit as [? Hnth']; eauto.
          by rewrite Heqo0 in Hnth'.
      + (* None *)
        apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_trap))>>.
        resolve_reduce_ctx vs0 es0.
        by eapply r_call_indirect_failure2; subst.

    - (* AI_basic (BI_get_local j) *)
      get_cc ccs.    
      remember (fc.(FC_frame)) as f.
      destruct (j < length f.(f_locs)) eqn:?.
      + (* true *)
        destruct (List.nth_error f.(f_locs) j) as [vs_at_j|] eqn:?.
        * (* Some vs_at_j *)
          apply <<hs, (s, (fc, lcs) :: ccs', (vs_at_j :: vs0, es0), None)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_get_local; subst.
        * (* None *)
          apply List.nth_error_None in Heqo; by lias.
      + (* false *)
        resolve_invalid_typing; simpl in Htype; invert_be_typing.
        inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
        destruct fc as [fvs fk ff fes]; simpl in *.
        apply inst_t_context_local_empty in Hit; rewrite -> Hit in *; simpl in *.
        rewrite length_is_size size_map -length_is_size in H3_getlocal; by lias.

    - (* AI_basic (BI_set_local j) *)
      get_cc ccs.    
      remember (fc.(FC_frame)) as f.
      destruct vs0 as [|v vs0].
      + (* [::] *)
        resolve_invalid_typing; simpl in Htype; invert_be_typing; by size_unequal H2_setlocal.
      + (* v :: ves' *)
        destruct (j < length f.(f_locs)) eqn:Hlen.
        * (* true *)
           apply <<hs, (s, ((Build_frame_ctx (fc.(FC_val)) fc.(FC_arity) (Build_frame (set_nth v f.(f_locs) j v) f.(f_inst)) fc.(FC_post)), lcs) :: ccs', (vs0, es0), None)>>.
           resolve_reduce_ctx vs0 es0.
           by eapply r_set_local; subst => //.
        * (* false *)
          resolve_invalid_typing; simpl in Htype; invert_be_typing.
          inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
          destruct fc as [fvs fk ff fes]; simpl in *.
          apply inst_t_context_local_empty in Hit; rewrite -> Hit in *; simpl in *.
          rewrite length_is_size size_map -length_is_size in H3_setlocal; by lias.

    - (* AI_basic (BI_tee_local j) *)
      destruct vs0 as [|v vs0].
      + (* [::] *)
        resolve_invalid_typing; simpl in Htype; invert_be_typing; by size_unequal H2_teelocal.
      + (* v :: ves' *)
        apply <<hs, (s, ccs, (v :: v :: vs0, es0), Some (AI_basic (BI_set_local j)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by eapply r_simple, rs_tee_local.

    - (* AI_basic (BI_get_global j) *)
      get_cc ccs.    
      remember (fc.(FC_frame)) as f.
      destruct (sglob_val s f.(f_inst) j) as [v|] eqn:Hsglob.
      + (* Some xx *)
        apply <<hs, (s, (fc, lcs) :: ccs', (v :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by eapply r_get_global; subst.
      + (* None *)
        resolve_invalid_typing; simpl in Htype; invert_be_typing.
        inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
        destruct fc as [fvs fk ff fes]; simpl in *.
        unfold sglob_val, sglob, sglob_ind in Hsglob.
        remove_bools_options.
        by eapply glob_context_store in Hoption; eauto.

    - (* AI_basic (BI_set_global j) *)
      get_cc ccs.    
      remember (fc.(FC_frame)) as f.
      destruct vs0 as [|v vs0].
      + (* [::] *)
        resolve_invalid_typing; simpl in Htype; invert_be_typing; by size_unequal H4_setglobal.
      + (* v :: ves' *)
        destruct (supdate_glob s f.(f_inst) j v) as [s'|] eqn:Hsupdate.
        * (* Some s' *)
          apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_set_global; subst.
        * (* None *)
          resolve_invalid_typing; simpl in Htype; invert_be_typing.
          inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
          destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
          unfold supdate_glob, supdate_glob_s in Hsupdate.
          eapply glob_context_store in H5_setglobal; eauto.
          unfold sglob in H5_setglobal.
          destruct (sglob_ind s fi j) as [sglobi|] eqn:Hsglobi => //; simpl in *.
          by destruct (List.nth_error (s_globals s) sglobi) => //.

    - (* AI_basic (BI_load t ops (Some (tp, sx)) a off) *)
      get_cc ccs.    
      remember (fc.(FC_frame)) as f.
      destruct vs0 as [|v vs0].
      + (* [::] *)
        resolve_invalid_typing; simpl in Htype; invert_be_typing; by size_unequal H1_load.
      + (* v :: ves' *)
        destruct v as [c| | |] eqn:?.
        2,3,4: resolve_invalid_typing; simpl in Htype; invert_be_typing; by last_unequal H1_load.
        (* VAL_int32 c *)
        destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
        * (* Some j *)
           destruct (List.nth_error s.(s_mems) j) as [mem_s_j|] eqn:?.
           { (* Some mem_s_j*)
             destruct ops as [[tp sx] | ].
             (* Some (tp, sx) *)
             - destruct (load_packed sx (mem_s_j) (Wasm_int.N_of_uint i32m c) off (tp_length tp) (t_length t)) as [bs|] eqn:Hload.
               + (* Some bs *)
                 apply <<hs, (s, (fc, lcs) :: ccs', (wasm_deserialise bs t :: vs0, es0), None)>>.
                 resolve_reduce_ctx vs0 es0.
                 by eapply r_load_packed_success; subst; eauto.
               + (* None *)
                 apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
                 resolve_reduce_ctx vs0 es0.
                 by eapply r_load_packed_failure; subst; eauto.
             - destruct (load (mem_s_j) (Wasm_int.N_of_uint i32m c) off (t_length t)) as [bs|] eqn:Hload.
               + (* Some bs *)
                 apply <<hs, (s, (fc, lcs) :: ccs', (wasm_deserialise bs t :: vs0, es0), None)>>.
                 resolve_reduce_ctx vs0 es0.
                 by eapply r_load_success; subst; eauto.
               + (* None *)
                 apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
                 resolve_reduce_ctx vs0 es0.
                 by eapply r_load_failure; subst; eauto.
           }
           { (* None *)
             resolve_invalid_typing; simpl in Htype; invert_be_typing.
             inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
             destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
             eapply mem_context_store in Hit as [? [Hsmemi Hnth]]; eauto.
             rewrite Heqo in Hsmemi; injection Hsmemi as ->.
             by rewrite Heqo0 in Hnth.
           }
        * (* None *)
          resolve_invalid_typing; simpl in Htype; invert_be_typing.
          inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
          destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
          eapply mem_context_store in Hit as [? [Hsmemi Hnth]]; eauto.
          by rewrite Heqo in Hsmemi.

    - (* AI_basic (BI_store t (Some tp) a off) *)
      get_cc ccs. 
      remember (fc.(FC_frame)) as f.
      destruct vs0 as [|v [|v' vs0]].
      1,2: resolve_invalid_typing; simpl in Htype; invert_be_typing; by size_unequal H1_store.
      (* v :: v' :: ves' *)
      destruct v' as [c| | |] eqn:?.
      2,3,4:
        resolve_invalid_typing; simpl in Htype; invert_be_typing;
        simpl in *;
        apply (f_equal rev) in H1_store;
        rewrite rev_cat -map_rev rev_drop revK size_rev map_take /= in H1_store;
        destruct ((size vs0).+2 - x3) => //=; by destruct n.
      (* VAL_int32 c *)
      destruct (types_agree t v) eqn:?.
      + (* true *)
        destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
        * (* Some j *)
           destruct (List.nth_error s.(s_mems) j) as [mem_s_j|] eqn:?.
           { (* Some mem_s_j *)
             destruct op as [tp | ].
              - (* Some tp*)
                destruct (store_packed mem_s_j (Wasm_int.N_of_uint i32m c) off (bits v) (tp_length tp)) as [mem'|] eqn:?.
                + (* Some mem' *)
                  apply <<hs, (upd_s_mem s (set_nth mem' s.(s_mems) j mem'), (fc, lcs) :: ccs', (vs0, es0), None)>>.
                  resolve_reduce_ctx vs0 es0.
                  by eapply r_store_packed_success; subst; eauto.
                + (* None *)
                  apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
                  resolve_reduce_ctx vs0 es0.
                  by eapply r_store_packed_failure; subst; eauto.
                  (* None *)
              - destruct (store mem_s_j (Wasm_int.N_of_uint i32m c) off (bits v) (t_length t)) as [mem'|] eqn:?.
                + (* Some mem' *)
                  apply <<hs, (upd_s_mem s (set_nth mem' s.(s_mems) j mem'), (fc, lcs) :: ccs', (vs0, es0), None)>>.
                  resolve_reduce_ctx vs0 es0.
                  by eapply r_store_success; subst; eauto.
                + (* None *)
                  apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
                  resolve_reduce_ctx vs0 es0.
                  by eapply r_store_failure; subst; eauto.
           }
           { (* None *)
             resolve_invalid_typing; simpl in Htype; invert_be_typing.
             inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
             destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
             eapply mem_context_store in Hit as [? [Hsmemi Hnth]]; eauto.
             rewrite Heqo in Hsmemi; injection Hsmemi as ->.
             by rewrite Heqo0 in Hnth.
           }
        * (* None *)
          resolve_invalid_typing; simpl in Htype; invert_be_typing.
          inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
          destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
          eapply mem_context_store in Hit as [? [Hsmemi Hnth]]; eauto.
          by rewrite Heqo in Hsmemi.
      + (* false *)
        resolve_invalid_typing; simpl in Htype; invert_be_typing.
        simpl in *.
        unfold types_agree in Heqb; move/eqP in Heqb.
        last_unequal H1_store.
        destruct ((size vs0).+2-x3) => //; simpl in *.
        by inversion H1_store.

    - (* AI_basic BI_current_memory *)
      get_cc ccs.    
      remember (fc.(FC_frame)) as f.
      destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
      + (* Some j *)
        destruct (List.nth_error s.(s_mems) j) as [s_mem_s_j|] eqn:?.
        * (* Some j *)
          remember (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j)))) as v' eqn:?.
          apply <<hs, (s, (fc, lcs) :: ccs', (v' :: vs0, es0), None)>>.
          resolve_reduce_ctx vs0 es0.
          by subst; eapply r_current_memory; eauto.
        * (* None *)
          resolve_invalid_typing; simpl in Htype; invert_be_typing.
          inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
          destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
          eapply mem_context_store in Hit as [? [Hsmemi Hnth]]; eauto.
          rewrite Heqo in Hsmemi; injection Hsmemi as ->.
          by rewrite Heqo0 in Hnth.
      + (* None *)
        resolve_invalid_typing; simpl in Htype; invert_be_typing.
        inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
        destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
        eapply mem_context_store in Hit as [? [Hsmemi Hnth]]; eauto.
        by rewrite Heqo in Hsmemi.

    - (* AI_basic BI_grow_memory *)
      get_cc ccs.    
      remember (fc.(FC_frame)) as f.
      destruct vs0 as [|v vs0]; first by resolve_invalid_typing; simpl in Htype; invert_be_typing; size_unequal H3_growmemory.
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?.
      2,3,4: resolve_invalid_typing; simpl in Htype; invert_be_typing; by last_unequal H3_growmemory.
      (* VAL_int32 c *)
      destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
      + (* Some j *)
        destruct (List.nth_error s.(s_mems) j) as [s_mem_s_j|] eqn:Heqsmem.
        * (* Some s_mem_s_j *)
           remember (mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m c)) as mem'.
           destruct mem' as [mem''|].
           -- (* Some mem'' *)
              remember (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j)))) as v'.
              remember (upd_s_mem s (set_nth mem'' s.(s_mems) j mem'')) as s'.
              apply <<hs, (s', (fc, lcs) :: ccs', (v' :: vs0, es0), None)>>.
              resolve_reduce_ctx vs0 es0.
              by subst; eapply r_grow_memory_success; eauto.
           -- (* None *)
              apply <<hs, (s, (fc, lcs) :: ccs', (VAL_int32 int32_minus_one :: vs0, es0), None)>>.
              resolve_reduce_ctx vs0 es0.
              by subst; eapply r_grow_memory_failure; eauto.
        * (* None *)
          resolve_invalid_typing; simpl in Htype; invert_be_typing.
          inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
          destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
          eapply mem_context_store in Hit as [? [Hsmemi Hnth]]; eauto.
          rewrite Heqo in Hsmemi; injection Hsmemi as ->.
          by rewrite Heqsmem in Hnth.
      + (* None *)
        resolve_invalid_typing; simpl in Htype; invert_be_typing.
        inversion Hftype as [s' i tvs C f Hit Hfi Hlocs]; subst.
        destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
        eapply mem_context_store in Hit as [? [Hsmemi Hnth]]; eauto.
        by rewrite Heqo in Hsmemi.

    - (* AI_basic (BI_const _) *)
      apply RSC_invalid => /=; by move => [??].

    - (* AI_basic (BI_unop t op) *)
      destruct vs0 as [|v vs0].
      + (* [::] *)
        by resolve_invalid_typing; simpl in Htype; invert_be_typing; size_unequal H2_unop.
      + (* v :: ves' *)
        apply <<hs, (s, ccs, (app_unop op v :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_unop.

    - (* AI_basic (BI_binop t op) *)
      destruct vs0 as [|v2 [|v1 vs0]].
      1,2: by resolve_invalid_typing; simpl in Htype; invert_be_typing; size_unequal H1_binop.
      (* [:: v2, v1 & ves'] *)
      destruct (app_binop op v1 v2) as [v|] eqn:?.
      + (* Some v *)
        apply <<hs, (s, ccs, (v :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_binop_success.
      + (* None *)
        apply <<hs, (s, ccs, (vs0, es0), Some AI_trap)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_binop_failure.

    - (* AI_basic (BI_testop t testop) *)
      destruct vs0 as [| v vs0].
      + (* [::] *)
        by resolve_invalid_typing; simpl in Htype; invert_be_typing; size_unequal H1_testop.
      + (* VAL_int32 c :: ves' *)
        destruct t as [| | |].
        3,4: resolve_invalid_typing; simpl in Htype; invert_be_typing; by last_unequal H1_testop.
        (* i32 *)
        * destruct v as [c| | |].
          2,3,4: resolve_invalid_typing; simpl in Htype; invert_be_typing; by last_unequal H1_testop.
          apply <<hs, (s, ccs, (VAL_int32 (wasm_bool (@app_testop_i i32t testop c)) :: vs0, es0), None)>>.
          resolve_reduce_ctx vs0 es0.
          by apply r_simple, rs_testop_i32.
        (* i64 *)
        * destruct v as [|c | |].
          1,3,4: resolve_invalid_typing; simpl in Htype; invert_be_typing; by last_unequal H1_testop.
          apply <<hs, (s, ccs, (VAL_int32 (wasm_bool (@app_testop_i i64t testop c)) :: vs0, es0), None)>>.
          resolve_reduce_ctx vs0 es0.
          by apply r_simple, rs_testop_i64.

    - (* AI_basic (BI_relop t op) *)
      destruct vs0 as [|v2 [|v1 vs0]].
      1,2: by resolve_invalid_typing; simpl in Htype; invert_be_typing; size_unequal H1_relop.
      (* [:: v2, v1 & ves'] *)
      apply <<hs, (s, ccs, (VAL_int32 (wasm_bool (@app_relop op v1 v2)) :: vs0, es0), None)>>.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_relop.

    - (* AI_basic (BI_cvtop t2 CVO_convert t1 sx) *)
      destruct vs0 as [|v vs0]; first by resolve_invalid_typing; simpl in Htype; invert_be_typing; size_unequal H1_cvtop.
      (* v :: ves' *)
      destruct (types_agree t1 v) eqn:Ht1.
      + (* true *)
        destruct cvtop.
        (* convert *)
        * destruct (cvt t2 sx v) as [v'|] eqn:Heqv'.
          { (* Some v' *)
            apply <<hs, (s, ccs, (v' :: vs0, es0), None)>>.
            resolve_reduce_ctx vs0 es0.
            by apply r_simple, rs_convert_success.
          }
          { (* None *)
            apply <<hs, (s, ccs, (vs0, es0), Some AI_trap)>>.
            resolve_reduce_ctx vs0 es0.
            by apply r_simple, rs_convert_failure.
          }
        (* Reinterpret *)
        * destruct sx eqn:Heqsx.
          { (* Some _ *)
            resolve_invalid_typing; simpl in Htype; invert_be_typing.
            by specialize (H3_cvtop erefl).
          }
          { (* None *)
            apply <<hs, (s, ccs, ((wasm_deserialise (bits v) t2) :: vs0, es0), None)>>.
            resolve_reduce_ctx vs0 es0.
            by apply r_simple, rs_reinterpret.
          }
      + (* false *)
        resolve_invalid_typing; simpl in Htype; invert_be_typing.
        unfold types_agree in Ht1; move/eqP in Ht1.
        last_unequal H1_cvtop.
        by destruct ((size vs0).+1 - x0) => //; inversion H1_cvtop.

    - (* AI_trap *)
      get_cc ccs.
      destruct ((vs0 == nil) && (es0 == nil)) eqn:Hscnil; move/andP in Hscnil.
      + destruct Hscnil as [Heq1 Heq2]; move/eqP in Heq1; move/eqP in Heq2; subst.
        destruct lcs as [ | lc lcs'].
        * destruct fc as [lvs ? ? les].
          apply <<hs, (s, ccs', (lvs, les), Some AI_trap)>> => /=.
          resolve_reduce_ctx lvs les.
          by apply r_simple, rs_local_trap.
        * destruct lc as [lvs ? ? les].
          apply <<hs, (s, (fc, lcs') :: ccs', (lvs, les), Some AI_trap)>>.
          unfold reduce_ctx.
          apply reduce_focus_ctx => //=.
          apply list_label_ctx_eval.(ctx_reduce) => //=.
          unfold label_ctx_fill => /=.
          resolve_reduce_ctx lvs les.
          by apply r_simple, rs_label_trap.
      + apply <<hs, (s, (fc, lcs) :: ccs', (nil, nil), Some AI_trap)>>.
        resolve_reduce_ctx lvs les.
        apply r_simple.
        apply rs_trap with (lh := LH_base (rev vs0) es0) => //.
        move => Hcontra; apply Hscnil.
        specialize (f_equal size Hcontra) as Hsize; rewrite size_cat v_to_e_size size_rev in Hsize.
        simpl in Hsize.
        clear - Hsize.
        assert (H: size vs0 = 0); first (by lias); destruct vs0 => //; clear H.
        assert (H: size es0 = 0); first (by lias); by destruct es0.

    - (* AI_invoke a *)
      by apply run_ctx_invoke.
        
    - (* AI_label ln les es *)
      by apply RSC_invalid => /=; move => [??].

    * (* AI_local ln lf es *)
      by apply RSC_invalid => /=; move => [??].
  }
Defined.

Definition hs_cfg_ctx : Type := host_state * cfg_tuple_ctx.

(* reformation to a valid configuration, if possible *)
Definition run_step_cfg_ctx_reform (cfg: cfg_tuple_ctx) : option cfg_tuple_ctx.
Proof.
  destruct cfg as [[[s ccs] sc] oe].
 (* destruct ccs as [ | cc ccs]; first by right. *)
  destruct (ctx_update ccs sc oe) as [[[ccs' sc'] oe'] | ] eqn:Hctxupdate; last by right.
  exact (Some (s, ccs', sc', oe')).
Defined.

Definition run_v_init (s: store_record) (es: list administrative_instruction) : option cfg_tuple_ctx :=
  match ctx_decompose es with
  | Some (ccs, sc, oe) => Some (s, ccs, sc, oe)
  | None => None
  end.


Section Interp_ctx_progress.
  
(* The only case where run_v_init produces an invalid cfg is when there is no call context (which is only possible
   in real Wasm execution at module entrance with a single Invoke *)
Lemma run_v_init_valid: forall (s s': store_record) es ccs sc oe,
    store_typing s ->
    run_v_init s es = Some (s', ccs, sc, oe) ->
    ccs <> nil ->
    valid_cfg_ctx (s', ccs, sc, oe).
Proof.
  move => s s' es ccs sc oe Hstype Hinit Hneq.
  unfold run_v_init in Hinit.
  destruct (ctx_decompose es) as [[[ccs' sc'] oe'] | ] eqn:Hdecomp => //; inversion Hinit; subst; clear Hinit.
  destruct ccs as [| cc ccs] => //.
  split => //.
  by apply ctx_decompose_valid_split in Hdecomp.
Qed.

Definition valid_wasm_instr (es: list administrative_instruction) : bool :=
  match es with
  | [::AI_invoke _]
  | [::AI_local _ _ _] => true
  | _ => false
  end.

Definition valid_init_Some s es:
  valid_wasm_instr es ->
  run_v_init s es <> None.
Proof.
  move => Hvalid.
  destruct es as [| e es] => //; destruct e, es => //.
  rewrite /run_v_init /ctx_decompose ctx_decompose_aux_equation /=.
  destruct (ctx_decompose_aux _) as [[[??]?]|] eqn:Hdecomp => //; by apply ctx_decompose_acc_some in Hdecomp.
Qed.

Definition t_progress_interp_ctx: forall (hs: host_state) (s: store_record) es ts,
  valid_wasm_instr es ->
  config_typing s empty_frame es ts ->
  terminal_form es \/
  exists hs' s' es', reduce hs s empty_frame es hs' s' empty_frame es'.
Proof.
  move => hs s es ts Hvalid Htype.
  destruct (run_v_init s es) as [[[[s0 ccs] sc] oe]|] eqn:Hinit; last by eapply valid_init_Some in Hvalid; apply Hvalid in Hinit.
  destruct es as [| e es] => //; destruct e, es => //.
  (* Invoke *)
  { unfold run_v_init in Hinit.
    rewrite /ctx_decompose ctx_decompose_aux_equation /= in Hinit.
    injection Hinit as <- <- <- <-.
    { remember (run_one_step_ctx hs (s, nil, (nil, nil), Some (AI_invoke f))) as res.
      destruct res as [hs' [[[s' ccs'] sc'] oe'] Hred | vs Heq | Hcontra | Hcontra]; clear Heqres.
      - right.
        unfold reduce_ctx in Hred.
        simpl in *.
        repeat eexists. by eauto.
      - left.
        simpl in *.
        subst; rewrite Heq.
        left; by apply v_to_e_const.
      - exfalso; by apply Hcontra.
      - simpl in Hcontra. by apply Hcontra in Htype.
    }
  }
  (* Label *)
  { remember Hinit as Hinit2; clear HeqHinit2.
    unfold run_v_init in Hinit.
    rewrite /ctx_decompose ctx_decompose_aux_equation /= in Hinit.
    destruct (ctx_decompose_aux _) as [[[ccs' sc'] oe'] | ] eqn:Hdecomp => //; injection Hinit as <- -> -> ->.
    { remember (run_one_step_ctx hs (s, ccs, sc, oe)) as res.
      destruct res as [hs' [[[s' ccs'] sc'] oe'] Hred | vs Heq | Hcontra | Hcontra]; clear Heqres.
      1,2,4:
      unfold run_v_init in Hinit2; destruct (ctx_decompose _) as [[[ccs2 sc2] oe2]|] eqn:Hdecomp' => //;
      apply (@ctx_decompose_fill_id host_function host_instance) in Hdecomp';
      simpl in Hdecomp';
      injection Hinit2 as -> -> ->.
      - right.
        unfold reduce_ctx in Hred.
        simpl in *.
        rewrite Hdecomp' in Hred.
        repeat eexists. by eauto.
      - exfalso.
        simpl in *.
        rewrite Hdecomp' in Heq.
        by destruct vs.
      - simpl in Hcontra. rewrite Hdecomp' in Hcontra. by apply Hcontra in Htype.
      - exfalso; apply Hcontra; clear Hcontra.
        split;
        by [apply ctx_decompose_valid_ccs_aux in Hdecomp
           | apply ctx_decompose_valid_aux in Hdecomp ].
    }
  }
Qed.

End Interp_ctx_progress.

End Host.


Module Interpreter_ctx_extract.

Import EmptyHost.

(* No host function exists *)
Definition host_application_impl : host_state -> store_record -> function_type -> host_function_eqType -> seq value ->
                                   (host_state * option (store_record * result)).
Proof.
  move => ??? hf; by inversion hf.
Defined.

Definition host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).
Proof.
  move => ??? hf; by inversion hf.
Defined.

Definition run_one_step_ctx := run_one_step_ctx host_application_impl_correct.

Definition run_step_cfg_ctx_reform := @run_step_cfg_ctx_reform host_function_eqType.

Definition run_v_init := @run_v_init host_function_eqType.

Definition es_of_cfg := @es_of_cfg host_function_eqType host_instance.

End Interpreter_ctx_extract.
