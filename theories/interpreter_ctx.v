(** Proof-carrying interpreter for Wasm, optimised for contexts **)

From Wasm Require Import common properties tactic typing_inversion contexts.
From Coq Require Import ZArith.BinInt Program.Equality.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export operations host.
Require Import BinNat NArith BinNums ZArith.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

Section Host.

Context `{ho: host}.
  
Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                       (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).

Notation "ctx ⦃ es ⦄" := (ctx_fill es ctx) (at level 1).

Lemma config_typing_empty_inv: forall s es ts (C: t_context),
    config_typing s (empty_frame, es) ts ->
    C = empty_t_context ->
    store_typing s /\ e_typing s C es (Tf [::] ts).
Proof.
  move => s es ts C Htype ?; subst.
  destruct Htype as [Hstoretype Hthtype].
  split => //.
  inversion Hthtype as [s' f es' ors rs C Hstype Hftype Hetype]; subst; clear Hthtype.
  move/eqP in Hftype.
  uapply H.
  unfold frame_typing in Hftype; remove_bools_options.
  unfold empty_frame.
  unfold inst_typing in Hoption; simpl in *; remove_bools_options =>/=.
  by inversion Hoption0; subst.
Qed.
  
(** Auxiliary definition for reductions between context tuples **)
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
  | |- reduce _ _ _ (foldl closure_ctx_fill _ _) _ _ _ (foldl closure_ctx_fill _ _) =>
      apply (list_closure_ctx_eval.(ctx_reduce))
  | |- reduce _ _ _ (foldl label_ctx_fill _ _) _ _ _ (foldl label_ctx_fill _ _) =>
      apply (list_label_ctx_eval.(ctx_reduce))
  end.

(** Automatically trying to infer what to put aside using the L0 context (r_label) **)
Ltac infer_hole :=
  repeat match goal with
  | |- context C [vs_to_es _] =>
      rewrite /vs_to_es => /=
  | |- context C [ _ ++ [::] ] =>
      rewrite cats0 => /=
  | |- context C [v_to_e_list (rev (?x :: ?l2))] =>
      rewrite rev_cons -cats1 -v_to_e_cat => //=
  | |- context C [v_to_e_list (rev (?l1 ++ ?l2))] =>
      rewrite rev_cat -v_to_e_cat => //=
  | |- context C [v_to_e_list [:: ?x] ] =>
      unfold v_to_e_list, v_to_e => //=
  | |- context C [ ( _ ++ _) ++ _ ] =>
      rewrite -catA => /=
  | |- ?l1 ++ ?l2 = ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?x7 :: ?x8 :: ?l2 =>
      try by instantiate (1 := [::x1; x2; x3; x4; x5; x6; x7; x8]) => //
  | |- ?l1 ++ ?l2 = ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?x7 :: ?l2 =>
      try by instantiate (1 := [::x1; x2; x3; x4; x5; x6; x7]) => //
  | |- ?l1 ++ ?l2 = ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?l2 =>
      try by instantiate (1 := [::x1; x2; x3; x4; x5; x6]) => //
  | |- ?l1 ++ ?l2 = ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?l2 =>
      try by instantiate (1 := [::x1; x2; x3; x4; x5]) => //
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
      try instantiate (1 := l3 ++ [::x]); rewrite -catA => //=
  | _: _ |- ?l ++ _ = ?l ++ _ =>
      f_equal => //=
  end.

Ltac resolve_reduce_ctx vs es :=
  unfold reduce_ctx; red_ctx_simpl => //=; try (eapply r_label with (lh := LH_base (rev vs) es) => /=; infer_hole).

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
  (forall ts, config_typing (s_of_cfg cfg) (empty_frame, (es_of_cfg cfg)) ts -> False) ->
  run_step_ctx_result hs cfg
.

Ltac invert_ctx_typing Hetype :=
  match type of Hetype with
  | e_typing _ _ ((_ :: _) ⦃ _ ⦃ _ ⦄ ⦄) _ =>
    apply e_typing_ops_local in Hetype as [? [? [? [? [vts [ts' [Hvtstype [Hftype [Harity [? Hetype]]]]]]]]]]
  | e_typing _ _ (_ ⦃ _ ⦃ _ ⦄ ⦄) (Tf nil _) =>
    apply e_typing_ops in Hetype as [? [vts [ts' [Hvtstype Hetype]]]]
  end;
  simpl in *; invert_e_typing.

(** The usual start of a crash certification **)
Ltac resolve_invalid_typing :=
  apply RSC_error;
  let ts := fresh "ts" in
  let ts' := fresh "ts'" in
  let Htype := fresh "Htype" in
  let Hetype := fresh "Hetype" in
  let Hftype := fresh "Hftype" in
  let Hstype := fresh "Hstype" in
  intros ts Htype; unfold s_of_cfg, es_of_cfg in Htype;
  eapply config_typing_empty_inv in Htype as [Hstype Hetype]; eauto;
  invert_ctx_typing Hetype.

Ltac last_unequal H :=
  apply (f_equal rev) in H;
  repeat rewrite rev_cat in H;
  repeat rewrite -map_rev in H;
  repeat rewrite rev_drop in H;
  repeat rewrite revK in H;
  repeat rewrite size_rev in H;
  repeat rewrite map_take in H;
  simpl in H;
  (try by inversion H);
  match type of H with
  | context C [take ?n _] =>
      try by destruct n
  | _ => fail "unable to obtain a contradiction"
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

Lemma values_typing_rev: forall s vs ts,
    values_typing s (rev vs) = Some ts ->
    values_typing s vs = Some (rev ts).
Proof.
  move => s vs ts Hvaltype.
  unfold values_typing in *.
  rewrite map_rev in Hvaltype.
  by apply those_rev.
Qed.

(** Br exits from one label context. **)
Definition run_ctx_br: forall hs s ccs sc j,
  run_step_ctx_result hs (s, ccs, sc, Some (AI_basic (BI_br j))).
Proof.
  intros hs s ccs [vs es] j.
  get_cc ccs.
  destruct ((N.to_nat j) < length lcs) eqn:Hlablen.
  - destruct (List.nth_error lcs (N.to_nat j)) as [lab | ] eqn:Htar; last by apply List.nth_error_None in Htar; move/ltP in Hlablen; lias.
    destruct lab as [lvs lk lces les].
    destruct (lk <= length vs) eqn:Hvslen.
    + apply <<hs, (s, ((fc, drop (S (N.to_nat j)) lcs) :: ccs'), (take lk vs ++ lvs, lces ++ les), None)>>.
      apply reduce_focus_ctx => //=.
      rewrite - (cat_take_drop ((N.to_nat j).+1) lcs) drop_size_cat; last by rewrite size_takel => //.
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
      { apply lh_ctx_fill_aux with (acc := (LH_base (rev (drop lk vs)) es)) (lcs := take (N.to_nat j) lcs) => /=.
        rewrite ctx_to_lh_aux_len => /=.
        repeat rewrite - catA => /=.
        rewrite length_is_size in Hlablen.
        rewrite add0n length_is_size size_takel; last by lias.
        by rewrite N2Nat.id. 
      }
      
    + (* Not enough values *)
      apply RSC_error.
      destruct lcs as [| lc lcs] => //.
      intros ts Htype; unfold s_of_cfg, es_of_cfg in Htype.
      eapply config_typing_empty_inv in Htype as [Hstype Htype]; eauto.
      apply ccs_typing_focus in Htype as [? [? [? [tf Htype]]]].
      apply fc_typing in Htype as [? [? [Hftype [Hlen Htype]]]] => //.
      apply lcs_typing_exists in Htype as [labs [ts1 [ts2 [Htype [Hagree Hconsume]]]]].
      rewrite -> Hconsume in * => //; clear Hconsume.
      eapply sc_typing_args in Htype as [ts3 [ts4 [Hvstype Htype]]]; simpl in Htype.
      apply et_to_bet in Htype => //.
      simpl in Htype; invert_be_typing.
      unfold frame_typing in Hftype.
      remove_bools_options.
      simpl in *.
      destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
      erewrite -> inst_t_context_label_empty in H1_br; eauto.
      rewrite cats0 in H1_br.
      eapply all2_projection in Hagree; eauto.
      move/eqP in Hagree; simpl in Hagree; subst.
      apply values_typing_length in Hvstype.
      repeat rewrite -> length_is_size in *.
      rewrite length_is_size in Hvstype.
      rewrite size_rev size_cat in Hvstype.
      by lias.
      
  - (* Not enough labels *)
    apply RSC_error.
    intros ts Htype; unfold s_of_cfg, es_of_cfg in Htype.
    eapply config_typing_empty_inv in Htype as [Hstype Htype]; eauto.
    apply ccs_typing_focus in Htype as [? [? [? [tf Htype]]]].
    apply fc_typing in Htype as [? [? [Hftype [Hlen Htype]]]] => //.
    apply lcs_typing_exists in Htype as [labs [ts1 [ts2 [Htype [Hagree Hconsume]]]]].
    simpl in Htype.
    rewrite -cat1s in Htype.
    unfold vs_to_es in Htype.
    invert_e_typing.
    unfold frame_typing in Hftype.
    remove_bools_options.
    destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
    erewrite -> inst_t_context_label_empty in *; eauto.
    rewrite -> cats0 in *.
    apply all2_size in Hagree.
    rewrite length_is_size in Hlablen.
    unfold lookup_N in H1_br.
    apply nth_error_Some_length in H1_br.
    rewrite length_is_size Hagree in H1_br.
    by lias.
Defined.

(** Return exits from the innermost frame and all label contexts **)
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
    resolve_invalid_typing.
    simpl in *; injection H2_return as ->.
    apply values_typing_length in Hvtstype.
    repeat rewrite length_is_size in Hvtstype.
    rewrite size_cat size_rev in Hvtstype.
    repeat rewrite length_is_size in Hvslen.
    by lias.
Defined.
    
(** Invoke does not need a frame context. 
    This is useful for handling the starting invocation of a module, as the execution otherwise always assumes
    the existence of one frame context, which is in fact true in the spec representation (due to the frame in the
    config tuple) **)
Definition run_ctx_invoke hs s ccs vs0 es0 a:
    run_step_ctx_result hs (s, ccs, (vs0, es0), Some (AI_invoke a)).
Proof.
  destruct (lookup_N s.(s_funcs) a) as [cl|] eqn:?.
  - (* Some cl *)
    destruct cl as [[t1s t2s] i [tidx ts es] | [t1s t2s] cl'] eqn:?.
    + (* FC_func_native i (Tf t1s t2s) ts es *)
      remember (length t1s) as n eqn:?.
      remember (length t2s) as m eqn:?.
      destruct (length vs0 >= n) eqn:Hlen.
      * (* true *)
        destruct (split_n vs0 n) as [vs' vs''] eqn:Hsplit.
        remember (n_zeros ts) as zs eqn:?.
        apply <<hs, (s, (Build_frame_ctx vs'' m (Build_frame (rev vs' ++ zs) i) es0, nil) :: ccs, (nil, nil), Some (AI_label m nil (to_e_list es)))>> => /=.
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
        unfold ext_func_typing in H3_invoke.
        remove_bools_options; simpl in *.
        inversion H0; subst; clear H0.
        apply values_typing_length in Hvtstype.
        repeat rewrite length_is_size in Hvtstype.
        rewrite size_cat size_rev in Hvtstype.
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
      unfold ext_func_typing in H3_invoke.
      remove_bools_options; simpl in *.
      inversion H0; subst; clear H0.
      apply values_typing_length in Hvtstype.
      repeat rewrite length_is_size in Hvtstype.
      rewrite size_cat size_rev in Hvtstype.
      repeat rewrite length_is_size in Hlen.
      by lias.
  - (* None *)
    resolve_invalid_typing.
    unfold ext_func_typing in H3_invoke.
    by remove_bools_options; simpl in *.
Defined.

Ltac resolve_invalid_value :=
  repeat match goal with
  | H: values_typing _ (rev (?v :: _)) = Some _ |- _ =>
    apply values_typing_rev in H
  | H: values_typing _ (_ :: _) = Some (rev (?l1 ++ ?l2 ++ [::?t])) |- _ =>
    rewrite (catA l1 l2 [::t]) in H
  | H: values_typing _ (_ :: _) = Some (rev (?l ++ [::?t])) |- _ =>
    rewrite cats1 rev_rcons in H
  | H: values_typing _ (_ :: _) = Some (_ :: _) |- _ =>
    apply values_typing_cons_impl in H as [??];
    simpl in *;
    remove_bools_options => //
  | H: values_typing _ (_ :: _ :: _) = Some (rev (?l ++ _)) |- _ =>
    rewrite rev_cat in H;
    apply values_typing_cons_impl in H as [??];
    simpl in *;
    remove_bools_options => //
end.

Ltac assert_value_type v :=
  move: v; case => v;
  try by resolve_invalid_typing; resolve_invalid_value.

Ltac no_args :=
  resolve_invalid_typing;
  repeat match goal with
    | Hvtstype : values_typing _ _ = Some _ |- _ =>
      by apply values_typing_length in Hvtstype; size_unequal Hvtstype
    end.

Notation "$u32oz v" := (Wasm_int.int_of_Z i32m v) (at level 90).
Notation "$zou32 v" := (Wasm_int.Z_of_uint i32m v) (at level 90).
Notation "$nou32 v" := (Wasm_int.N_of_uint i32m v) (at level 90).

(* One step of execution; does not perform the context update in the end to shift to the new instruction. *)
Definition run_one_step_ctx (hs: host_state) (cfg: cfg_tuple_ctx) : run_step_ctx_result hs cfg.
Proof.
  destruct cfg as [[[s ccs] sc] oe].
  destruct oe as [e | ]; last first.
  (* Exitting from contexts *)
  {
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
          rewrite -cat1s in Htype.
          unfold vs_to_es in Htype.
          invert_e_typing.
          inversion H2_frame as [??????? Hftype ? Hetype Hvstype]; subst; clear H2_frame.
          invert_e_typing.
          apply values_typing_length in H2_values0.
          rewrite - H2_values0 in Hlen.
          by repeat rewrite length_is_size in Hlen; rewrite size_rev in Hlen.
        }
      }
      (* Exitting a label *)
      { destruct lc as [lvs lk lces les].
        destruct les as [ | e les'].
        { (* No instruction in the hole still *)
          apply <<hs, (s, (fc, lcs') :: ccs', (vs ++ lvs, nil), None)>> => /=.
          resolve_reduce_ctx (FC_val fc) (FC_post fc).
          eapply r_frame.
          red_ctx_simpl => //=.
          unfold fmask0, label_ctx_fill => /=.
          eapply r_label with (lh := LH_base (rev lvs) nil) => /=; infer_hole; eauto => /=.
          apply r_simple, rs_label_const; by apply v_to_e_const.
        }
        { (* e is in the hole *)
          apply <<hs, (s, (fc, lcs') :: ccs', (vs ++ lvs, les'), Some e)>> => /=.
          resolve_reduce_ctx (FC_val fc) (FC_post fc).
          apply r_frame => /=.
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
      (* BI_const_num _ *) |
      (* BI_unop t op *) t op |
      (* BI_binop t op *) t op |
      (* BI_testop t testop *) t testop |
      (* BI_relop t op *) t op |
      (* BI_cvtop t2 cvtop t1 sx *) t2 cvtop t1 sx |
      (* BI_const_vec _ *) |
      (* BI_ref_null t *) t |
      (* BI_ref_is_null *) |
      (* BI_ref_func x *) x |
      (* BI_drop *) |
      (* BI_select ot *) ot |
      (* BI_local_get j *) j |
      (* BI_local_set j *) j |
      (* BI_local_tee j *) j |
      (* BI_global_get j *) j |
      (* BI_global_set j *) j |
      (* BI_table_get x *) x |
      (* BI_table_set x *) x |
      (* BI_table_size x *) x |
      (* BI_table_grow x *) x |
      (* BI_table_fill x *) x |
      (* BI_table_copy x y *) x y |
      (* BI_table_init x y *) x y |
      (* BI_elem_drop x *) x |
      (* BI_load t [Some (tp, sx)|None] a off *) t ops a off |
      (* BI_store t [Some tp|None] a off *) t op a off |
      (* BI_memory_size *) |
      (* BI_memory_grow *) |
      (* BI_memory_fill *) |
      (* BI_memory_copy *) |
      (* BI_memory_init x *) x |
      (* BI_data_drop x *) x |
      (* BI_unreachable *) |
      (* BI_nop *) |
      (* BI_block bt es *) bt es |
      (* BI_loop bt es *) bt es |
      (* BI_if bt es1 es2 *) bt es1 es2 |
      (* BI_br j *) j |
      (* BI_br_if j *) j |
      (* BI_br_table js j *) js j |
      (* BI_return *) |
      (* BI_call j *) x |
      (* BI_call_indirect j *) x y ] |
      (* AI_trap *) |
      (* AI_ref a *) a |
      (* AI_ref_extern a *) a |
      (* AI_invoke a *) a |
      (* AI_label ln les es *) ln les es |
      (* AI_frame ln lf es *) ln lf es ]; destruct sc as [vs0 es0].

    - (* AI_basic (BI_const _) *)
      (* This along with other value instructions are invalid, as it doesn't respect
the condition that all values should live in the operand stack. *)
      apply RSC_invalid => /=; by move => [??].

    - (* AI_basic (BI_unop t op) *)
      destruct vs0 as [|v vs0]; first by no_args.
      (* v :: ves' *)
      assert_value_type v.
      apply <<hs, (s, ccs, (VAL_num (app_unop op v) :: vs0, es0), None)>>.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_unop.

    - (* AI_basic (BI_binop t op) *)
      destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      assert_value_type v2.
      assert_value_type v1.
      (* [:: v2, v1 & ves'] *)
      destruct (app_binop op v1 v2) as [v|] eqn:?.
      + (* Some v *)
        apply <<hs, (s, ccs, (VAL_num v :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_binop_success.
      + (* None *)
        apply <<hs, (s, ccs, (vs0, es0), Some AI_trap)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_binop_failure.

    - (* AI_basic (BI_testop t testop) *)
      destruct vs0 as [| v vs0]; first by no_args.
      (* v :: ves' *)
      assert_value_type v.
      destruct t as [| | |].
      3,4: by resolve_invalid_typing; last_unequal H1_testop.
      (* i32 *)
      + destruct v as [c| | |].
        2,3,4: by resolve_invalid_typing; resolve_invalid_value. 
        apply <<hs, (s, ccs, (VAL_num (VAL_int32 (wasm_bool (@app_testop_i i32t testop c))) :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_testop_i32.
      (* i64 *)
      + destruct v as [|c | |].
        1,3,4: by resolve_invalid_typing; resolve_invalid_value.
        apply <<hs, (s, ccs, (VAL_num (VAL_int32 (wasm_bool (@app_testop_i i64t testop c))) :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_testop_i64.

    - (* AI_basic (BI_relop t op) *)
      destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      assert_value_type v2.
      assert_value_type v1.
      (* [:: v2, v1 & ves'] *)
      apply <<hs, (s, ccs, (VAL_num (VAL_int32 (wasm_bool (@app_relop op v1 v2))) :: vs0, es0), None)>>.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_relop.

    - (* AI_basic (BI_cvtop t2 CVO_convert t1 sx) *)
      destruct vs0 as [|v vs0]; first by no_args.
      assert_value_type v.
      (* v :: ves' *)
      destruct (types_agree (T_num t1) (VAL_num v)) eqn:Ht1.
      + (* true *)
        destruct (cvtop_valid t2 cvtop t1 sx) eqn:Hcvtvalid.
        * (* true *)
          destruct (eval_cvt t2 cvtop sx v) as [v'|] eqn:Heval.
          { (* Some v' *)
            apply <<hs, (s, ccs, (VAL_num v' :: vs0, es0), None)>>.
            resolve_reduce_ctx vs0 es0.
            by apply r_simple, rs_convert_success.
          }
          { (* None *)
            apply <<hs, (s, ccs, (vs0, es0), Some AI_trap)>>.
            resolve_reduce_ctx vs0 es0.
            by apply r_simple, rs_convert_failure.
          }
        * (* false *)
          by resolve_invalid_typing; lias.
      + (* false *)
        resolve_invalid_typing. resolve_invalid_value.
        unfold types_agree, value_num_typing in *; simpl in *.
        by move/eqP in Ht1.

    - (* AI_basic BI_const_vec v *)
      apply RSC_invalid => /=; by move => [??].
      
    - (* AI_basic BI_ref_null t *)
      apply RSC_invalid => /=; by move => [??].

    - (* AI_basic BI_ref_is_null *)
      destruct vs0 as [|v vs0]; first by no_args.
      assert_value_type v.
      destruct v as [ v | v | v ].
      (* ref_null *)
      + apply <<hs, (s, ccs, ((VAL_num (VAL_int32 Wasm_int.Int32.one)) :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_ref_is_null_true.
      (* ref_func *)
      + apply <<hs, (s, ccs, ((VAL_num (VAL_int32 Wasm_int.Int32.zero)) :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        replace (AI_ref v) with ($V (VAL_ref (VAL_ref_func v))) => //.
        by apply r_simple, rs_ref_is_null_false.
      (* ref_extern *)
      + apply <<hs, (s, ccs, ((VAL_num (VAL_int32 Wasm_int.Int32.zero)) :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        replace (AI_ref_extern v) with ($V (VAL_ref (VAL_ref_extern v))) => //.
        by apply r_simple, rs_ref_is_null_false.

    - (* AI_basic (BI_ref_func x) *)
      get_cc ccs.
      destruct (lookup_N (inst_funcs (f_inst fc.(FC_frame))) x) as [addr | ] eqn:Hnth.
      + apply <<hs, (s, (fc, lcs) :: ccs', ((VAL_ref (VAL_ref_func addr)) :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_ref_func.
      + resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options.
        simpl in *.
        eapply inst_typing_func_lookup_inv in H1_ref_func; eauto.
        destruct H1_ref_func as [f [Hext Hnthf]].
        by rewrite Hnthf in Hnth.
      
    - (* AI_basic BI_drop *)
      destruct vs0 as [ | v vs0]; first by no_args.
      (* v :: vs0 *)
      apply <<hs, (s, ccs, (vs0, es0), None)>> => /=.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_drop.
      
    - (* AI_basic BI_select *)
      destruct vs0 as [|v3 [|v2 [|v1 vs0]]]; try by no_args.

      (* v3 has to be i32, but the other two can be of any numeric type. Note that neitehr the spec nor the opsem checks for this during runtime *)
      assert_value_type v3.
      destruct v3 as [c| | |] eqn:?; subst.
      (* Conclude a contradiction by comparing the last element. However, `last` computes very badly *)
      2,3,4: resolve_invalid_typing; simpl in *; resolve_invalid_value. 
      (* VAL_int32 c *)
      destruct (c == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
      + (* true *)
        apply <<hs, (s, ccs, (vs0, es0), Some ($V v2))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_select_false.
      + (* false *)
        apply <<hs, (s, ccs, (vs0, es0), Some ($V v1))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_select_true.
        
    - (* AI_basic (BI_local_get j) *)
      get_cc ccs.
      destruct (lookup_N fc.(FC_frame).(f_locs) j) as [vs_at_j|] eqn:?.
      * (* Some vs_at_j *)
        apply <<hs, (s, (fc, lcs) :: ccs', (vs_at_j :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by eapply r_local_get; subst.
      + (* None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        erewrite inst_t_context_local_empty in H1_local_get; eauto.
        rewrite cats0 in H1_local_get.
        unfold lookup_N in *.
        apply nth_error_Some_length in H1_local_get.
        apply values_typing_length in Hoption0.
        rewrite List.nth_error_None in Heqo.
        by lias.
        
    - (* AI_basic (BI_local_set j) *)
      get_cc ccs.    
      destruct vs0 as [|v vs0]; first by no_args.
      (* v :: ves' *)
      destruct (N.to_nat j < length fc.(FC_frame).(f_locs)) eqn:Hlen.
      + (* true *)
        apply <<hs, (s, ((Build_frame_ctx (fc.(FC_val)) fc.(FC_arity) (Build_frame (set_nth v fc.(FC_frame).(f_locs) (N.to_nat j) v) fc.(FC_frame).(f_inst)) fc.(FC_post)), lcs) :: ccs', (vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by eapply r_local_set with (vd := v). 
      + (* false *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        erewrite inst_t_context_local_empty in H1_local_set; eauto.
        rewrite cats0 in H1_local_set.
        unfold lookup_N in *.
        apply nth_error_Some_length in H1_local_set.
        apply values_typing_length in Hoption0.
        by lias.

    - (* AI_basic (BI_local_tee j) *)
      destruct vs0 as [|v vs0]; first by no_args.
      (* v :: ves' *)
      apply <<hs, (s, ccs, (v :: v :: vs0, es0), Some (AI_basic (BI_local_set j)))>> => /=.
      resolve_reduce_ctx vs0 es0.
      by eapply r_simple, rs_local_tee.

    - (* AI_basic (BI_global_get j) *)
      get_cc ccs.
      destruct (sglob_val s fc.(FC_frame).(f_inst) j) as [v|] eqn:Hsglob.
      + (* Some xx *)
        apply <<hs, (s, (fc, lcs) :: ccs', (v :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_global_get.
      + (* None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        unfold_store_operations.
        * inst_typing_lookup.
          by rewrite Hoption2 in Hextgt.
        * eapply inst_typing_global_lookup_inv in Hoption; eauto.
          destruct Hoption as [? [? Hnthg]].
          by rewrite Hoption3 in Hnthg.

    - (* AI_basic (BI_global_set j) *)
      get_cc ccs.    
      destruct vs0 as [|v vs0]; first by no_args.
      (* v :: ves' *)
      destruct (supdate_glob s fc.(FC_frame).(f_inst) j v) as [s'|] eqn:Hsupdate.
      * (* Some s' *)
        apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by eapply r_global_set; subst.
      * (* None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        unfold_store_operations.
        * inst_typing_lookup.
          by rewrite Hoption2 in Hextgt.
        * eapply inst_typing_global_lookup_inv in H1_global_set; eauto.
          destruct H1_global_set as [? [? Hnthg]].
          by rewrite Hoption1 in Hnthg.

    - (* AI_basic (BI_table_get x) *)
      get_cc ccs.
      destruct vs0 as [|v vs0]; first by no_args.
      assert_value_type v.
      assert_value_type v.
      destruct (stab_elem s fc.(FC_frame).(f_inst) x ($nou32 v)) as [tabv|] eqn:Hstab.
      + (* Some xx *)
        apply <<hs, (s, (fc, lcs) :: ccs', ((VAL_ref tabv) :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_table_get_success.
      + (* None *)
        (* Note that the stab_elem specification in the opsem matches the spec for typed expressions only -- it produces traps in some untyped scenarios which is undefined in spec. But that is not a problem anyway *)
        apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_table_get_failure.

    - (* AI_basic (BI_table_set x) *)
      get_cc ccs.
      destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      (* v2 needs to be a ref and v1 needs to be a i32 num *)
      assert_value_type v2.
      assert_value_type v1; assert_value_type v1.
      destruct (stab_update s fc.(FC_frame).(f_inst) x ($nou32 v1) v2) as [s'|] eqn:Hsupdate.
      + (* Some xx *)
        apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_table_set_success.
      + (* None *)
        apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_table_set_failure.
        
    - (* AI_basic (BI_table_size x) *)
      get_cc ccs.
      destruct (stab s fc.(FC_frame).(f_inst) x) as [tab|] eqn:Hstab.
      + (* Some xx *)
        apply <<hs, (s, (fc, lcs) :: ccs', ((VAL_num (VAL_int32 ($u32oz (Z.of_nat (tab_size tab))))) :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by eapply r_table_size; eauto.
      + (* None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        unfold_store_operations.
        * inst_typing_lookup.
          by rewrite Hstab in Hexttabt.
        * eapply inst_typing_table_lookup_inv in H2_table_size; eauto.
          destruct H2_table_size as [? [? Hnthtab]].
          by rewrite Hoption1 in Hnthtab.

    - (* AI_basic (BI_table_grow x) *)
      get_cc ccs.
      destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      (* Takes an i32 and a reference value *)
      assert_value_type v2; assert_value_type v2.
      assert_value_type v1.
      destruct (stab s fc.(FC_frame).(f_inst) x) as [tab|] eqn:Hstab.
      + (* Some xx *)
        destruct (growtable tab (Wasm_int.N_of_uint i32m v2) v1) as [tab' | ] eqn:Htabgrow.
        * (* Some *)
          apply <<hs, (upd_s_table s (set_nth tab' (s_tables s) (N.to_nat x) tab'), (fc, lcs) :: ccs', ((VAL_num (VAL_int32 ($u32oz (Z.of_nat (tab_size tab))))) :: vs0, es0), None)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_table_grow_success; eauto.
        * (* None *)
          apply <<hs, (s, (fc, lcs) :: ccs', ((VAL_num (VAL_int32 int32_minus_one)) :: vs0, es0), None)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_table_grow_failure; eauto.
      + (* None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        unfold_store_operations.
        * inst_typing_lookup.
          by rewrite Hstab in Hexttabt.
        * eapply inst_typing_table_lookup_inv in H3_table_grow; eauto.
          destruct H3_table_grow as [? [? Hnthtab]].
          by rewrite Hoption1 in Hnthtab.

    - (* AI_basic (BI_table_fill x) *)
      get_cc ccs.
      destruct vs0 as [|v3 [|v2 [|v1 vs0]]]; try by no_args.
      (* Takes i32; val; i32 *)
      assert_value_type v3; assert_value_type v3.
      assert_value_type v2.
      assert_value_type v1; assert_value_type v1.
      destruct (stab s fc.(FC_frame).(f_inst) x) as [tab|] eqn:Hstab.
      + (* Some xx *)
        destruct (Z.ltb (Z.of_nat (tab_size tab)) (($zou32 v1) + ($zou32 v3))) eqn:Hbound; move/Z.ltb_spec0 in Hbound.
        * (* Out of bound *)
          apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_table_fill_bound; eauto; lias.
        * destruct (($zou32 v3) == 0)%Z eqn:Hn0; move/eqP in Hn0; simpl in *; subst.
          { (* Return *)
            apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None)>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_table_fill_return; eauto; simpl in *; lias.
          }
          {
            (* Step *)
            apply <<hs, (s, (fc, lcs) :: ccs',
                          ((VAL_ref v2) :: (VAL_num (VAL_int32 v1)) :: vs0,
                            [::($VN (VAL_int32 ($u32oz (Z.add ($zou32 v1) 1)))); ($V (VAL_ref v2)); ($VN (VAL_int32 ($u32oz (Z.sub ($zou32 v3) 1)))); (AI_basic (BI_table_fill x))] ++ es0),
                          Some (AI_basic (BI_table_set x)))>>.
            resolve_reduce_ctx vs0 es0; simpl in *.
            by eapply r_table_fill_step; eauto; lias.
          }
      + (* None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        unfold_store_operations.
        * inst_typing_lookup.
          by rewrite Hstab in Hexttabt.
        * eapply inst_typing_table_lookup_inv in H2_table_fill; eauto.
          destruct H2_table_fill as [? [? Hnthtab]].
          by rewrite Hoption1 in Hnthtab.
          
    - (* AI_basic (BI_table_copy x y) *)
      get_cc ccs.
      destruct vs0 as [|n [|src [|dst vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_value_type n; assert_value_type n.
      assert_value_type src; assert_value_type src.
      assert_value_type dst; assert_value_type dst.
      destruct (stab s fc.(FC_frame).(f_inst) x) as [tabx|] eqn:Hstabx.
      + (* Some xx *)
        destruct (stab s fc.(FC_frame).(f_inst) y) as [taby|] eqn:Hstaby.
        * (* Some xx *)
          destruct (Z.ltb (Z.of_nat (tab_size taby)) (($zou32 src) + ($zou32 n))) eqn:Hboundy; move/Z.ltb_spec0 in Hboundy.
          { (* taby Out of bound *)
            apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_table_copy_bound; eauto; lias.
          }
          destruct (Z.ltb (Z.of_nat (tab_size tabx)) (($zou32 dst) + ($zou32 n))) eqn:Hboundx; move/Z.ltb_spec0 in Hboundx.
          { (* tabx Out of bound *)
            apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_table_copy_bound; eauto; lias.
          }
          {
            (* In bound for both tables *)
            destruct (($zou32 n) == 0)%Z eqn:Hn0; move/eqP in Hn0; simpl in *; subst.
            { (* Return *)
              apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None)>>.
              resolve_reduce_ctx vs0 es0.
              by eapply r_table_copy_return; eauto; simpl in *; lias.
            }
            destruct (Z.leb ($zou32 dst) ($zou32 src)) eqn:Hdir; move/Z.leb_spec0 in Hdir.
            { (* copy -- forward *)
              apply <<hs, (s, (fc, lcs) :: ccs',
                            ((VAL_num (VAL_int32 src)) :: (VAL_num (VAL_int32 dst)) :: vs0,
                              [::(AI_basic (BI_table_set x)); $VN (VAL_int32 ($u32oz (Z.add ($zou32 dst) 1))); $VN (VAL_int32 ($u32oz (Z.add ($zou32 src) 1))); $VN (VAL_int32 ($u32oz (Z.sub ($zou32 n) 1))); AI_basic (BI_table_copy x y)] ++ es0),
                            Some (AI_basic (BI_table_get y)))>>.
              resolve_reduce_ctx vs0 es0.
              by eapply r_table_copy_forward; eauto; simpl in *; lias.
            }
            { (* copy -- backward *)
              apply <<hs, (s, (fc, lcs) :: ccs',
                            ((VAL_num (VAL_int32 ($u32oz (Z.sub (Z.add ($zou32 src) ($zou32 n)) 1)))) ::
                            (VAL_num (VAL_int32 ($u32oz (Z.sub (Z.add ($zou32 dst) ($zou32 n)) 1)))) ::
                            vs0,
                              [::(AI_basic (BI_table_set x)); $VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 ($u32oz (Z.sub ($zou32 n) 1))); AI_basic (BI_table_copy x y)] ++ es0),
                            Some (AI_basic (BI_table_get y)))>>.
              resolve_reduce_ctx vs0 es0.
              eapply r_table_copy_backward; eauto; simpl in *; try by lias.
            }
          }

        * (* staby = None *)
          resolve_invalid_typing.
          unfold frame_typing in Hftype; remove_bools_options; simpl in *.
          unfold_store_operations.
          {  inst_typing_lookup.
             by rewrite Hstaby in Hexttabt.
          }
          { eapply inst_typing_table_lookup_inv in H3_table_copy; eauto.
            destruct H3_table_copy as [? [? Hnthtab]].
            by rewrite Hoption1 in Hnthtab.
          }
          
      + (* stabx = None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        unfold_store_operations.
        {  inst_typing_lookup.
           by rewrite Hstabx in Hexttabt.
        }
        { eapply inst_typing_table_lookup_inv in H2_table_copy; eauto.
          destruct H2_table_copy as [? [? Hnthtab]].
          by rewrite Hoption1 in Hnthtab.
        }
        
    - (* AI_basic (BI_table_init x y) *)
      get_cc ccs.
      destruct vs0 as [|n [|src [|dst vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_value_type n; assert_value_type n.
      assert_value_type src; assert_value_type src.
      assert_value_type dst; assert_value_type dst.
      destruct (stab s fc.(FC_frame).(f_inst) x) as [tab|] eqn:Hstab.
      + (* Some xx *)
        destruct (selem s fc.(FC_frame).(f_inst) y) as [elem|] eqn:Hselem.
        * (* Some xx *)
          destruct (Z.ltb (Z.of_nat (elem_size elem)) (($zou32 src) + ($zou32 n))) eqn:Hboundy; move/Z.ltb_spec0 in Hboundy.
          { (* elem Out of bound *)
            apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_table_init_bound; eauto; lias.
          }
          destruct (Z.ltb (Z.of_nat (tab_size tab)) (($zou32 dst) + ($zou32 n))) eqn:Hboundx; move/Z.ltb_spec0 in Hboundx.
          { (* tab Out of bound *)
            apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_table_init_bound; eauto; lias.
          }
          {
            (* In bound for both table and elem *)
            destruct (($zou32 n) == 0)%Z eqn:Hn0; move/eqP in Hn0; simpl in *; subst.
            { (* Return *)
              apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None)>>.
              resolve_reduce_ctx vs0 es0.
              by eapply r_table_init_return; eauto; simpl in *; lias.
            }
            { (* Step -- but need to lookup first *)
              destruct (lookup_N elem.(eleminst_elem) ($nou32 src)) as [v | ] eqn:Hnthelem.
              { (* Step *)
                apply <<hs, (s, (fc, lcs) :: ccs',
                              ((VAL_ref v) :: (VAL_num (VAL_int32 dst)) :: vs0,
                                [::$VN (VAL_int32 ($u32oz (Z.add ($zou32 dst) 1)));
                                 $VN (VAL_int32 ($u32oz (Z.add ($zou32 src) 1)));
                                 $VN (VAL_int32 ($u32oz (Z.sub ($zou32 n) 1)));
                                 AI_basic (BI_table_init x y)
                                ] ++ es0),
                              Some (AI_basic (BI_table_set x)))>>.
                resolve_reduce_ctx vs0 es0.
                by eapply r_table_init_step; eauto; simpl in *; lias.
              }
              { (* lookup oob *)
                resolve_invalid_typing.
                destruct elem; unfold elem_size in Hboundy; simpl in *.
                unfold lookup_N in *; apply List.nth_error_None in Hnthelem.
                apply Hboundy.
                apply Z2Nat.inj_lt; try by lias.
                { specialize (Wasm_int.Int32.unsigned_range_2 src) as Ha1.
                  specialize (Wasm_int.Int32.unsigned_range_2 n) as Ha2.
                  by lias.
                }
                rewrite Nat2Z.id.
                assert (Wasm_int.Int32.unsigned n > 0)%Z as Hngt.
                { specialize (Wasm_int.Int32.unsigned_range_2 n) as Ha.
                  by lias.
                }
                rewrite Z_N_nat in Hnthelem.
                rewrite Z2Nat.inj_add; try by lias.
                by specialize (Wasm_int.Int32.unsigned_range_2 src) as ?; lias.
              }
            }
          }

        * (* selem = None *)
          resolve_invalid_typing.
          unfold frame_typing in Hftype; remove_bools_options; simpl in *.
          unfold_store_operations.
          { eapply inst_typing_elem_lookup_inv in H3_table_init; eauto.
            destruct H3_table_init as [? [? [Hinstelem [Hnthelem ?]]]].
            rewrite Hoption2 in Hinstelem; injection Hinstelem as <-.
            by rewrite Hselem in Hnthelem.
          }
          { eapply inst_typing_elem_lookup_inv in H3_table_init; eauto.
            destruct H3_table_init as [? [? [Hinstelem [Hnthelem ?]]]].
            by rewrite Hoption2 in Hinstelem.
          }
          
      + (* stab = None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        unfold_store_operations.
        {  inst_typing_lookup.
           by rewrite Hstab in Hexttabt.
        }
        { eapply inst_typing_table_lookup_inv in H2_table_init; eauto.
          destruct H2_table_init as [? [? Hnthtab]].
          by rewrite Hoption1 in Hnthtab.
        }
        
    - (* AI_basic BI_elem_drop x *)
      get_cc ccs.
      destruct (selem_drop s fc.(FC_frame).(f_inst) x) as [s'|] eqn:Hs'.
      + apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_elem_drop.
      + resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        unfold_store_operations.
        { eapply inst_typing_elem_lookup_inv in H2_elem_drop; eauto.
          destruct H2_elem_drop as [? [? [Hinstelem [Hnthelem ?]]]].
          rewrite Hoption2 in Hinstelem; injection Hinstelem as <-. 
          by rewrite Hoption1 in Hnthelem.
        }
        { eapply inst_typing_elem_lookup_inv in H2_elem_drop; eauto.
          destruct H2_elem_drop as [? [? [Hinstelem [Hnthelem ?]]]].
          by rewrite Hoption2 in Hinstelem.
        }

    - (* AI_basic (BI_load t ops (Some (tp, sx)) a off) *)
      get_cc ccs.    
      destruct vs0 as [|v vs0]; first by no_args.
      assert_value_type v; assert_value_type v.
      (* VAL_int32 v :: ves' *)
      destruct (smem s fc.(FC_frame).(f_inst)) as [mem_s_j|] eqn:?.
      { (* Some mem_s_j *)
        destruct ops as [[tp sx] | ].
        (* Some (tp, sx) *)
        - destruct (load_packed sx (mem_s_j) ($nou32 v) off (tp_length tp) (tnum_length t)) as [bs|] eqn:Hload.
          + (* Some bs *)
            apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num (wasm_deserialise bs t) :: vs0, es0), None)>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_load_packed_success; subst; eauto.
          + (* None *)
            apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_load_packed_failure; subst; eauto.
        - destruct (load (mem_s_j) ($nou32 v) off (tnum_length t)) as [bs|] eqn:Hload.
          + (* Some bs *)
            apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num (wasm_deserialise bs t) :: vs0, es0), None)>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_load_success; subst; eauto.
          + (* None *)
            apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_load_failure; subst; eauto.
      }
      { (* None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        unfold_store_operations.
        { inst_typing_lookup.
          by rewrite Heqo in Hextmt.
        }
        { eapply inst_typing_mem_lookup_inv in H3_load; eauto.
          destruct H3_load as [? [? Hnthmem]].
          by rewrite Hoption1 in Hnthmem.
        }
      }

    - (* AI_basic (BI_store t (Some tp) a off) *)
      get_cc ccs. 
      destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      assert_value_type v1; assert_value_type v1.
      assert_value_type v2.
      destruct (typeof_num v2 == t) eqn:Heq; move/eqP in Heq.
      + (* true *)
        destruct (smem_ind s fc.(FC_frame).(f_inst)) as [j|] eqn:?.
        * (* Some j *)
           destruct (lookup_N s.(s_mems) j) as [mem_s_j|] eqn:?.
           { (* Some mem_s_j *)
             destruct op as [tp | ].
              - (* Some tp *)
                destruct (store_packed mem_s_j ($nou32 v1) off (bits v2) (tp_length tp)) as [mem'|] eqn:?.
                + (* Some mem' *)
                  apply <<hs, (upd_s_mem s (set_nth mem' s.(s_mems) j mem'), (fc, lcs) :: ccs', (vs0, es0), None)>>.
                  resolve_reduce_ctx vs0 es0.
                  by eapply r_store_packed_success; subst; eauto.
                + (* None *)
                  apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
                  resolve_reduce_ctx vs0 es0.
                  by eapply r_store_packed_failure; subst; eauto.
                  (* None *)
              - destruct (store mem_s_j ($nou32 v1) off (bits v2) (tnum_length t)) as [mem'|] eqn:?.
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
             resolve_invalid_typing.
             unfold frame_typing in Hftype; remove_bools_options; simpl in *.
             unfold_store_operations.
             eapply inst_typing_mem_lookup_inv in H2_store; eauto.
             destruct H2_store as [? [Hextmt Hnthmem]].
             rewrite Heqo in Hnthmem; injection Hnthmem as <-.
             unfold ext_mem_typing in Hextmt.
             by rewrite Heqo0 in Hextmt.
           }
           
        * (* None *)
          resolve_invalid_typing.
          unfold frame_typing in Hftype; remove_bools_options; simpl in *.
          unfold_store_operations.
          eapply inst_typing_mem_lookup_inv in H2_store; eauto.
          destruct H2_store as [? [Hextmt Hnthmem]].
          by rewrite Heqo in Hnthmem.
          
      + (* false *)
        by resolve_invalid_typing; resolve_invalid_value.

    - (* AI_basic BI_memory_size *)
      get_cc ccs.    
      destruct (smem s fc.(FC_frame).(f_inst)) as [s_mem_s_j|] eqn:?.
      + (* Some j *)
        apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num (VAL_int32 ($u32oz (Z.of_N (mem_size (s_mem_s_j))))) :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by subst; eapply r_memory_size; eauto.
      + (* None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        unfold_store_operations.
        { eapply inst_typing_mem_lookup_inv in H1_memory_size; eauto.
          destruct H1_memory_size as [? [Hextmt Hnthmem]].
          rewrite Hoption1 in Hnthmem; injection Hnthmem as <-.
          unfold ext_mem_typing in Hextmt.
          by rewrite Heqo in Hextmt.
        }
        { eapply inst_typing_mem_lookup_inv in H1_memory_size; eauto.
          destruct H1_memory_size as [? [Hextmt Hnthmem]].
          by rewrite Hoption1 in Hnthmem.
        }

    - (* AI_basic BI_memory_grow *)
      get_cc ccs.
      destruct vs0 as [|v vs0]; first by no_args.
      assert_value_type v; assert_value_type v.
      (* VAL_int32 c *)
      destruct (smem_ind s fc.(FC_frame).(f_inst)) as [j|] eqn:?.
      + (* Some j *)
        destruct (lookup_N s.(s_mems) j) as [s_mem_s_j|] eqn:Heqsmem.
        * (* Some s_mem_s_j *)
           destruct (mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m v)) as [mem' | ] eqn:Hgrow.
           -- (* Some mem'' *)
              remember (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j)))) as v'.
              remember (upd_s_mem s (set_nth mem' s.(s_mems) j mem')) as s'.
              apply <<hs, (s', (fc, lcs) :: ccs', (VAL_num (VAL_int32 ($u32oz (Z.of_N (mem_size s_mem_s_j)))) :: vs0, es0), None)>>.
              resolve_reduce_ctx vs0 es0.
              by subst; eapply r_memory_grow_success; eauto.
           -- (* None *)
              apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num (VAL_int32 int32_minus_one) :: vs0, es0), None)>>.
              resolve_reduce_ctx vs0 es0.
              by subst; eapply r_memory_grow_failure; eauto.
        * (* None *)
          resolve_invalid_typing.
          unfold frame_typing in Hftype; remove_bools_options; simpl in *.
          unfold_store_operations.
          eapply inst_typing_mem_lookup_inv in H1_memory_grow; eauto.
          destruct H1_memory_grow as [? [Hextmt Hnthmem]].
          rewrite Heqo in Hnthmem; injection Hnthmem as <-.
          unfold ext_mem_typing in Hextmt.
          by rewrite Heqsmem in Hextmt.
      + (* None *)
          resolve_invalid_typing.
          unfold frame_typing in Hftype; remove_bools_options; simpl in *.
          unfold_store_operations.
          eapply inst_typing_mem_lookup_inv in H1_memory_grow; eauto.
          destruct H1_memory_grow as [? [Hextmt Hnthmem]].
          by rewrite Heqo in Hnthmem.

    - (* AI_basic BI_memory_fill *)
      get_cc ccs.
      destruct vs0 as [|v3 [|v2 [|v1 vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_value_type v3; assert_value_type v3.
      assert_value_type v2; assert_value_type v2.
      assert_value_type v1; assert_value_type v1.
      destruct (smem s fc.(FC_frame).(f_inst)) as [mem|] eqn:Hsmem.
      + (* Some *)
        destruct (Z.ltb (Z.of_nat (mem_length mem)) (Z.add ($zou32 v1) ($zou32 v3))) eqn:Hlt; move/Z.ltb_spec0 in Hlt.
        * (* true *)
          apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_memory_fill_bound; eauto; lias.
        * (* false *)
          destruct (($zou32 v3) == 0)%Z eqn:Heq0; move/eqP in Heq0.
          { (* Return *)
            apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None)>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_memory_fill_return; eauto; lias.
          }
          { (* Step *)
            apply <<hs, (s, (fc, lcs) :: ccs',
                          ((VAL_num (VAL_int32 v2)) :: (VAL_num (VAL_int32 v1)) :: vs0,
                            [::$VN (VAL_int32 ($u32oz (Z.add ($zou32 v1) 1)));
                             $VN (VAL_int32 v2);
                             $VN (VAL_int32 ($u32oz (Z.sub ($zou32 v3) 1)));
                            AI_basic (BI_memory_fill)] ++ es0),
                          Some (AI_basic (BI_store T_i32 (Some Tp_i8) 0%N 0%N)))>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_memory_fill_step; eauto; lias.
          }
      + (* None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        unfold_store_operations.
        { eapply inst_typing_mem_lookup_inv in H1_memory_fill; eauto.
          destruct H1_memory_fill as [? [Hextmt Hnthmem]].
          rewrite Hoption1 in Hnthmem; injection Hnthmem as <-.
          unfold ext_mem_typing in Hextmt.
          by rewrite Hsmem in Hextmt.
        }
        { eapply inst_typing_mem_lookup_inv in H1_memory_fill; eauto.
          destruct H1_memory_fill as [? [? Hnthmem]].
          by rewrite Hoption1 in Hnthmem.
        }
        
    - (* AI_basic BI_memory_copy *)
      get_cc ccs.
      destruct vs0 as [|n [|src [|dst vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_value_type n; assert_value_type n.
      assert_value_type src; assert_value_type src.
      assert_value_type dst; assert_value_type dst.
      destruct (smem s fc.(FC_frame).(f_inst)) as [mem|] eqn:Hsmem.
      + (* Some *)
        destruct (Z.ltb (Z.of_nat (mem_length mem)) (($zou32 src) + ($zou32 n))) eqn:Hboundy; move/Z.ltb_spec0 in Hboundy.
        { (* y Out of bound *)
          apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_memory_copy_bound; eauto; lias.
        }
        destruct (Z.ltb (Z.of_nat (mem_length mem)) (($zou32 dst) + ($zou32 n))) eqn:Hboundx; move/Z.ltb_spec0 in Hboundx.
        { (* x Out of bound *)
          apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_memory_copy_bound; eauto; lias.
        }
        {
          (* In bound for both memories *)
          destruct (($zou32 n) == 0)%Z eqn:Hn0; move/eqP in Hn0; simpl in *; subst.
          { (* Return *)
            apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None)>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_memory_copy_return; eauto; simpl in *; lias.
          }
          destruct (Z.leb ($zou32 dst) ($zou32 src)) eqn:Hdir; move/Z.leb_spec0 in Hdir.
          { (* copy -- forward *)
            apply <<hs, (s, (fc, lcs) :: ccs',
                          ((VAL_num (VAL_int32 src)) :: (VAL_num (VAL_int32 dst)) :: vs0,
                            [::(AI_basic (BI_store T_i32 (Some Tp_i8) 0%N 0%N)); $VN (VAL_int32 ($u32oz (Z.add ($zou32 dst) 1))); $VN (VAL_int32 ($u32oz (Z.add ($zou32 src) 1))); $VN (VAL_int32 ($u32oz (Z.sub ($zou32 n) 1))); AI_basic (BI_memory_copy)] ++ es0),
                          Some (AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) 0%N 0%N)))>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_memory_copy_forward; eauto; simpl in *; lias.
          }
          { (* copy -- backward *)
            apply <<hs, (s, (fc, lcs) :: ccs',
                          ((VAL_num (VAL_int32 ($u32oz (Z.add ($zou32 src) (Z.sub ($zou32 n) 1))))) ::
                             (VAL_num (VAL_int32 ($u32oz (Z.add ($zou32 dst) (Z.sub ($zou32 n) 1))))) ::
                             vs0,
                            [::(AI_basic (BI_store T_i32 (Some Tp_i8) 0%N 0%N)); $VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 ($u32oz (Z.sub ($zou32 n) 1))); AI_basic (BI_memory_copy)] ++ es0),
                          Some (AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) 0%N 0%N)))>>.
            resolve_reduce_ctx vs0 es0.
            eapply r_memory_copy_backward; eauto; simpl in *; try by lias.
          }
        }
      + (* None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        unfold_store_operations.
        { eapply inst_typing_mem_lookup_inv in H1_memory_copy; eauto.
          destruct H1_memory_copy as [? [Hextmt Hnthmem]].
          rewrite Hoption1 in Hnthmem; injection Hnthmem as <-.
          unfold ext_mem_typing in Hextmt.
          by rewrite Hsmem in Hextmt.
        }
        { eapply inst_typing_mem_lookup_inv in H1_memory_copy; eauto.
          destruct H1_memory_copy as [? [? Hnthmem]].
          by rewrite Hoption1 in Hnthmem.
        }
        
    - (* AI_basic BI_memory_init *)
      get_cc ccs.
      destruct vs0 as [|n [|src [|dst vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_value_type n; assert_value_type n.
      assert_value_type src; assert_value_type src.
      assert_value_type dst; assert_value_type dst.
      destruct (smem s fc.(FC_frame).(f_inst)) as [mem|] eqn:Hsmem.
      + (* Some *)
        destruct (sdata s fc.(FC_frame).(f_inst) x) as [data|] eqn:Hsdata.
        * (* Some *)
          destruct (Z.ltb (Z.of_nat (data_size data)) (($zou32 src) + ($zou32 n))) eqn:Hboundy; move/Z.ltb_spec0 in Hboundy.
          { (* y Out of bound *)
            apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_memory_init_bound; eauto; lias.
          }
          destruct (Z.ltb (Z.of_nat (mem_length mem)) (($zou32 dst) + ($zou32 n))) eqn:Hboundx; move/Z.ltb_spec0 in Hboundx.
          { (* x Out of bound *)
            apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
            resolve_reduce_ctx vs0 es0.
            by eapply r_memory_init_bound; eauto; lias.
          }
          {
            (* In bound for both table and elem *)
            destruct (($zou32 n) == 0)%Z eqn:Hn0; move/eqP in Hn0; simpl in *; subst.
            { (* Return *)
              apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None)>>.
              resolve_reduce_ctx vs0 es0.
              by eapply r_memory_init_return; eauto; simpl in *; lias.
            }
            { (* Step -- but need to lookup first *)
              destruct (lookup_N data.(datainst_data) ($nou32 src)) as [b | ] eqn:Hnthdata.
              { (* Step *)
                apply <<hs, (s, (fc, lcs) :: ccs',
                              ((VAL_num (wasm_deserialise [::b] T_i32)) :: (VAL_num (VAL_int32 dst)) :: vs0,
                                [::$VN (VAL_int32 ($u32oz (Z.add ($zou32 dst) 1)));
                                 $VN (VAL_int32 ($u32oz (Z.add ($zou32 src) 1)));
                                 $VN (VAL_int32 ($u32oz (Z.sub ($zou32 n) 1)));
                                 AI_basic (BI_memory_init x)
                                ] ++ es0),
                              Some (AI_basic (BI_store T_i32 (Some Tp_i8) 0%N 0%N)))>>.
                resolve_reduce_ctx vs0 es0.
                by eapply r_memory_init_step; eauto; simpl in *; lias.
              }
              { (* lookup oob *)
                resolve_invalid_typing.
                destruct data; unfold data_size in Hboundy; simpl in *.
                unfold lookup_N in *; apply List.nth_error_None in Hnthdata.
                apply Hboundy.
                apply Z2Nat.inj_lt; try by lias.
                { specialize (Wasm_int.Int32.unsigned_range_2 src) as Ha1.
                  specialize (Wasm_int.Int32.unsigned_range_2 n) as Ha2.
                  by lias.
                }
                rewrite Nat2Z.id.
                assert (Wasm_int.Int32.unsigned n > 0)%Z as Hngt.
                { specialize (Wasm_int.Int32.unsigned_range_2 n) as Ha.
                  by lias.
                }
                rewrite Z_N_nat in Hnthdata.
                rewrite Z2Nat.inj_add; try by lias.
                by specialize (Wasm_int.Int32.unsigned_range_2 src) as ?; lias.
              }
            }
          }

        * (* sdata = None *)
          resolve_invalid_typing.
          unfold frame_typing in Hftype; remove_bools_options; simpl in *.
          unfold_store_operations.
          { eapply inst_typing_data_lookup_inv in H2_memory_init; eauto.
            destruct H2_memory_init as [? [? [Hinstdata [Hnthdata ?]]]].
            rewrite Hoption2 in Hinstdata; injection Hinstdata as <-.
            by rewrite Hsdata in Hnthdata.
          }
          { eapply inst_typing_data_lookup_inv in H2_memory_init; eauto.
            destruct H2_memory_init as [? [? [Hinstdata [Hnthdata ?]]]].
            by rewrite Hoption2 in Hinstdata.
          }

      + (* None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        unfold_store_operations.
        { eapply inst_typing_mem_lookup_inv in H1_memory_init; eauto.
          destruct H1_memory_init as [? [Hextmt Hnthmem]].
          rewrite Hoption1 in Hnthmem; injection Hnthmem as <-.
          unfold ext_mem_typing in Hextmt.
          by rewrite Hsmem in Hextmt.
        }
        { eapply inst_typing_mem_lookup_inv in H1_memory_init; eauto.
          destruct H1_memory_init as [? [? Hnthmem]].
          by rewrite Hoption1 in Hnthmem.
        }
          
    - (* AI_basic BI_data_drop x *)
      get_cc ccs.
      destruct (sdata_drop s fc.(FC_frame).(f_inst) x) as [s'|] eqn:Hs'.
      + apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_data_drop.
      + resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        unfold_store_operations.
        { eapply inst_typing_data_lookup_inv in H1_data_drop; eauto.
          destruct H1_data_drop as [? [? [Hinstdata [Hnthdata ?]]]].
          rewrite Hoption2 in Hinstdata; injection Hinstdata as <-. 
          by rewrite Hoption1 in Hnthdata.
        }
        { eapply inst_typing_data_lookup_inv in H1_data_drop; eauto.
          destruct H1_data_drop as [? [? [Hinstdata [Hnthdata ?]]]].
          by rewrite Hoption2 in Hinstdata.
        }

    - (* AI_basic BI_nop *)
      apply <<hs, (s, ccs, (vs0, es0), None)>> => /=.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_nop.

    - (* AI_basic BI_unreachable *)
      apply <<hs, (s, ccs, (vs0, es0), Some AI_trap)>> => /=.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_unreachable.

    - (* AI_basic (BI_block bt es) *)
      get_cc ccs.
      destruct (expand fc.(FC_frame).(f_inst) bt) as [[t1s t2s] | ] eqn:Hexpand.
      + (* Some t1s t2s *)
        destruct (length vs0 >= length t1s) eqn:Hlen.
        * (* true *)
          destruct (split_n vs0 (length t1s)) as [ves' ves''] eqn:Hsplit.
          apply <<hs, (s, (fc, lcs) :: ccs', (ves'', es0), Some (AI_label (length t2s) nil (vs_to_es ves' ++ to_e_list es)))>>.
          rewrite split_n_is_take_drop in Hsplit; injection Hsplit as ??; subst.
          resolve_reduce_ctx ves'' es0.
          resolve_reduce_ctx (drop (length t1s) vs0) es0.
          2: {
            instantiate (1 := (v_to_e_list (rev (take (length t1s) vs0))) ++ [::AI_basic (BI_block bt es)]).
            repeat rewrite catA.
            rewrite v_to_e_cat -rev_cat cat_take_drop.
            by infer_hole.
          }
          eapply r_block; eauto; first by apply v_to_e_const.
          rewrite v_to_e_length.
          repeat rewrite length_is_size.
          repeat rewrite length_is_size in Hlen.
          by rewrite size_rev size_takel.
        * (* false *)
          resolve_invalid_typing.
          unfold frame_typing in Hftype; remove_bools_options; simpl in *.
          erewrite <- inst_typing_expand_eq in Hexpand_block; eauto; last by unfold inst_match; destruct t; lias.
          rewrite Hexpand_block in Hexpand; injection Hexpand as <- <-.
          apply values_typing_length in Hvtstype.
          move/leP in Hlen; apply Hlen.
          rewrite rev_length List.app_length in Hvtstype.
          by lias.
      + (* None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        erewrite <- inst_typing_expand_eq in Hexpand_block; eauto; last by unfold inst_match; destruct t; lias.
        by rewrite Hexpand_block in Hexpand.

    - (* AI_basic (BI_loop bt es) *)
      get_cc ccs.
      destruct (expand fc.(FC_frame).(f_inst) bt) as [[t1s t2s] | ] eqn:Hexpand.
      + (* Some t1s t2s *)
        destruct (length vs0 >= length t1s) eqn:Hlen.
        * (* true *)
          destruct (split_n vs0 (length t1s)) as [ves' ves''] eqn:Hsplit.
          apply <<hs, (s, (fc, lcs) :: ccs', (ves'', es0), Some (AI_label (length t1s) [::AI_basic (BI_loop bt es)] (vs_to_es ves' ++ to_e_list es)))>>.
          rewrite split_n_is_take_drop in Hsplit; injection Hsplit as ??; subst.
          resolve_reduce_ctx ves'' es0.
          resolve_reduce_ctx (drop (length t1s) vs0) es0.
          2: {
            instantiate (1 := (v_to_e_list (rev (take (length t1s) vs0))) ++ [::AI_basic (BI_loop bt es)]).
            repeat rewrite catA.
            rewrite v_to_e_cat -rev_cat cat_take_drop.
            by infer_hole.
          }
          eapply r_loop; eauto; first by apply v_to_e_const.
          rewrite v_to_e_length.
          repeat rewrite length_is_size.
          repeat rewrite length_is_size in Hlen.
          by rewrite size_rev size_takel.
        * (* false *)
          resolve_invalid_typing.
          unfold frame_typing in Hftype; remove_bools_options; simpl in *.
          erewrite <- inst_typing_expand_eq in Hexpand_block; eauto; last by unfold inst_match; destruct t; lias.
          rewrite Hexpand_block in Hexpand; injection Hexpand as <- <-.
          apply values_typing_length in Hvtstype.
          move/leP in Hlen; apply Hlen.
          rewrite rev_length List.app_length in Hvtstype.
          by lias.
      + (* None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        erewrite <- inst_typing_expand_eq in Hexpand_block; eauto; last by unfold inst_match; destruct t; lias.
        by rewrite Hexpand_block in Hexpand.
        
    - (* AI_basic (BI_if tb es1 es2) *)
      destruct vs0 as [|v vs0]; first by no_args.
      assert_value_type v;  assert_value_type v.
      destruct (v == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
      + (* true *)
        apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_block bt es2)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_if_false.
      + (* false *)
        apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_block bt es1)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_if_true.

    - (* AI_basic (BI_br j) *)
      by apply run_ctx_br.

    - (* AI_basic (BI_br_if j) *)
      destruct vs0 as [|v vs0]; first by no_args.
      assert_value_type v; assert_value_type v.
      destruct (v == Wasm_int.int_zero i32m) eqn:Heqc; move/eqP in Heqc.
      + (* 0 *)
        apply <<hs, (s, ccs, (vs0, es0), None)>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_br_if_false.
      + (* not 0 *)
        apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_br j)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_br_if_true.

    - (* AI_basic (BI_br_table js j) *)
      destruct vs0 as [|v vs0]; first by no_args.
      assert_value_type v; assert_value_type v.
      destruct (N.ltb ($nou32 v) (N.of_nat (length js))) eqn:Hlen; move/N.ltb_spec0 in Hlen.
      + (* true *)
        destruct (lookup_N js ($nou32 v)) as [js_at_k|] eqn: Hnth.
        * (* Some js_at_k *)
          apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_br js_at_k)))>> => /=.
          resolve_reduce_ctx vs0 es0.
          by apply r_simple; subst; apply rs_br_table.
        * (* None *)
          unfold lookup_N in Hnth.
          apply List.nth_error_None in Hnth.
          by lias.
      + (* false *)
        apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_br j)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; subst; apply rs_br_table_length; lias.
        
    - (* AI_basic BI_return *)
      by apply run_ctx_return.

    - (* AI_basic (BI_call x) *)
      get_cc ccs.
      destruct (lookup_N fc.(FC_frame).(f_inst).(inst_funcs) x) as [a|] eqn: Hnth.
      + (* Some a *)
        apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_invoke a))>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_call.
      + (* None *)
        resolve_invalid_typing.
        unfold frame_typing in Hftype; remove_bools_options; simpl in *.
        eapply inst_typing_func_lookup_inv in H1_call; eauto.
        destruct H1_call as [? [Hextft Hnthft]].
        by rewrite Hnthft in Hnth.

    - (* AI_basic (BI_call_indirect x y) *)
      get_cc ccs.
      destruct vs0 as [|v vs0]; first by no_args.
      assert_value_type v; assert_value_type v.
      destruct (stab_elem s fc.(FC_frame).(f_inst) x ($nou32 v)) as [vref|] eqn:?.
      + (* Some a *)
        destruct vref as [t | a | a].
        * (* ref_null *)
          apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_call_indirect_failure_null_ref; eauto.
        * (* funcref *)
          destruct (lookup_N s.(s_funcs) a) as [cl | ] eqn:Hnthcl.
          -- (* Some *)
            destruct (lookup_N (inst_types (f_inst (fc.(FC_frame)))) y == Some (cl_type cl)) eqn:Hcl; move/eqP in Hcl.
            ++ (* true *)
              apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_invoke a))>>.
              resolve_reduce_ctx vs0 es0.
              by eapply r_call_indirect_success; subst; eauto.
            ++ (* false *)
              apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_trap))>>.
              resolve_reduce_ctx vs0 es0.
              by eapply r_call_indirect_failure_mismatch; subst; eauto.
          -- (* None *)
          resolve_invalid_typing.
          unfold frame_typing in Hftype; remove_bools_options; simpl in *.
          unfold_store_operations.
          resolve_store_inst_lookup.
          destruct t1; remove_bools_options; simpl in *.
          unfold lookup_N in Hnthtabt.
          eapply all_projection in Hif1; eauto.
          move/eqP in Hif1; simpl in Hif1.
          unfold ext_func_typing in Hif1.
          by rewrite Hnthcl in Hif1.
        * (* externref *)
          resolve_invalid_typing.
          unfold frame_typing in Hftype; remove_bools_options; simpl in *.
          unfold_store_operations.
          resolve_store_inst_lookup.
          destruct t1; remove_bools_options; simpl in *.
          eapply all_projection in Hif1; eauto.
          move/eqP in Hif1; simpl in Hif1.
          rewrite Hnthtabt in H1_callindirect; injection H1_callindirect as <-.
          by rewrite H2_callindirect in Hif1.
      + (* None *)
        apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_trap))>>.
        resolve_reduce_ctx vs0 es0.
        by eapply r_call_indirect_failure_bound; subst.

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

    - (* AI_ref a *)
      by apply RSC_invalid => /=; move => [??].
      
    - (* AI_ref_extern a *)
      by apply RSC_invalid => /=; move => [??].
       
    - (* AI_invoke a *)
      by apply run_ctx_invoke.
        
    - (* AI_label ln les es *)
      by apply RSC_invalid => /=; move => [??].

    - (* AI_frame ln lf es *)
      by apply RSC_invalid => /=; move => [??].
  }
Defined.

(* reformation to a valid configuration, if possible *)
Definition run_step_cfg_ctx_reform (cfg: cfg_tuple_ctx) : option cfg_tuple_ctx.
Proof.
  destruct cfg as [[[s ccs] sc] oe].
  destruct (ctx_update ccs sc oe) as [[[ccs' sc'] oe'] | ] eqn:Hctxupdate; last by right.
  exact (Some (s, ccs', sc', oe')).
Defined.

Definition run_v_init (s: store_record) (es: list administrative_instruction) : option cfg_tuple_ctx :=
  match ctx_decompose es with
  | Some (ccs, sc, oe) => Some (s, ccs, sc, oe)
  | None => None
  end.

Definition hs_cfg_ctx : Type := host_state * cfg_tuple_ctx.

Fixpoint run_multi_step_ctx (fuel: nat) (hcfg: hs_cfg_ctx) : (option hs_cfg_ctx) + (list value) :=
  match fuel with
  | 0 => inl None
  | S n =>
      let (hs, cfg) := hcfg in
      match run_one_step_ctx hs cfg with
      | RSC_normal hs' cfg' HReduce =>
          run_multi_step_ctx n (hs', cfg')
      | RSC_value vs _ => inr vs
      | _ => inl None
      end
  end.

(** Auxiliary definition for running arbitrary expressions, not necessarily with a frame within the expression decomposition.
    Requires knowing about the number of return values beforehand (can be obtained from typing).
    Note that this definition should *never* be used in the extracted code due to the inefficient
    usage of fuel. It is only used internally during module instantiation.
 **)

Definition run_multi_step_raw (hs: host_state) (fuel: nat) (s: store_record) (f: frame) (es: list administrative_instruction) (arity: nat) : (option hs_cfg_ctx) + (list value) :=
  match run_v_init s [::AI_frame arity f es] with
  | Some cfg => run_multi_step_ctx fuel (hs, cfg)
  | None => inl None
  end.


Section Interp_ctx_progress.

(** A definition to what is considered a 'valid' tuple by the ctx interpreter.
    This constraint seems restrictive, but in fact all Wasm runtime configuration can be expressed in this form:
    the runtime configuration tuple (S; F; es) always has a frame F, which can be used to form the frame context
    [AI_frame n F es] (with the right choice of n).

    The only exception is at the start of a module invocation (in fact not an exception, since the Wasm spec uses
    an empty frame at the start), where the Invoke part comes to the rescue; but in principle it is not even needed.
 **)
Definition valid_wasm_instr (es: list administrative_instruction) : bool :=
  match es with
  | [::AI_invoke _]
  | [::AI_frame _ _ _] => true
  | _ => false
  end.

Lemma valid_instr_preserve (hs: host_state) s f es hs' s' f' es':
  reduce hs s f es hs' s' f' es' ->
  valid_wasm_instr es ->
  valid_wasm_instr es' \/ terminal_form es'.
Proof.
  move => Hred.
  induction Hred => //; subst; move => Hvalid; (try by left); (try by (right; (try by left); (try by right))).
  - destruct e as [ | e es] => //; destruct e, es => //.
    + inversion H; subst; clear H; try by destruct vs as [ | v vs] => //; destruct vs.
      by right; right.
    + inversion H; subst; clear H; (try by destruct vs as [ | v vs] => //; destruct vs); try by (right; (try by left); (try by right)).
  - by destruct vs as [| v vs] => //; destruct v => //.
  - by destruct vs as [| v vs] => //; destruct v => //.
  - right.
    destruct r => /=; by [left; apply v_to_e_const | right].
    (* Frame *)
  - destruct lh using lh_case; destruct k => //.
    + rewrite -> lh_cast_eq in *.
      simpl in *.
      destruct vs => //=; last destruct v as [v | v | v] => //=; try by destruct v => //.
      destruct es as [ | e es]; first by apply reduce_not_nil in Hred.
      destruct e, es, es0 => //; by apply IHHred in Hvalid; rewrite cats0.
    + inversion H; subst.
      rewrite -> lh_cast_eq in *; clear H.
      simpl in Hvalid.
      destruct vs as [| v vs] => //; destruct v as [v|v|v] => //=; by destruct v.
Qed.

Definition valid_init_Some s es:
  valid_wasm_instr es ->
  run_v_init s es <> None.
Proof.
  move => Hvalid.
  destruct es as [| e es] => //; destruct e, es => //.
  rewrite /run_v_init /ctx_decompose ctx_decompose_aux_equation /=.
  destruct (ctx_decompose_aux _) as [[[??]?]|] eqn:Hdecomp => //; by apply ctx_decompose_acc_some in Hdecomp.
Qed.

(* The only case where run_v_init produces an invalid cfg is when there is no call context (which is only possible
   in real Wasm execution at module entrance with a single Invoke *)
Lemma run_v_init_valid: forall (s: store_record) es,
    store_typing s ->
    valid_wasm_instr es ->
    exists s' ccs sc oe, run_v_init s es = Some (s', ccs, sc, oe) /\ valid_cfg_ctx (s', ccs, sc, oe).
Proof.
  move => s es Hstype Hvalid.
  destruct (run_v_init s es) as [[[[s' ccs] sc] oe]|] eqn:Hinit; last by eapply valid_init_Some in Hvalid; apply Hvalid in Hinit.
  exists s', ccs, sc, oe; split => //.
  unfold run_v_init in Hinit.
  destruct (ctx_decompose es) as [[[ccs' sc'] oe'] | ] eqn:Hdecomp => //; inversion Hinit; subst; clear Hinit.
  split; last by apply ctx_decompose_valid_split in Hdecomp.
  unfold ctx_decompose in Hdecomp.
  destruct es as [| e es'] => //; destruct e, es' => //;
  rewrite ctx_decompose_aux_equation in Hdecomp; simpl in Hdecomp.
  - apply/orP; right.
    injection Hdecomp as <- <-; by subst => /=.
  - by apply ctx_decompose_valid_ccs_aux in Hdecomp => //.
Qed.

(* The induced progress for this version looks slightly weaker, as it only applies to valid instructions directly.
   However, every function call starts with a valid instruction and continues to be one until the call is exited 
   (preservation of valid instructions).
*)
Definition t_progress_interp_ctx: forall (hs: host_state) (s: store_record) es ts,
  valid_wasm_instr es ->
  config_typing s (empty_frame, es) ts ->
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
  (* Frame *)
  { remember Hinit as Hinit2; clear HeqHinit2.
    unfold run_v_init in Hinit.
    rewrite /ctx_decompose ctx_decompose_aux_equation /= in Hinit.
    destruct (ctx_decompose_aux _) as [[[ccs' sc'] oe'] | ] eqn:Hdecomp => //; injection Hinit as <- -> -> ->.
    { remember (run_one_step_ctx hs (s, ccs, sc, oe)) as res.
      destruct res as [hs' [[[s' ccs'] sc'] oe'] Hred | vs Heq | Hcontra | Hcontra]; clear Heqres.
      1,2,4:
      unfold run_v_init in Hinit2; destruct (ctx_decompose _) as [[[ccs2 sc2] oe2]|] eqn:Hdecomp' => //;
      apply ctx_decompose_fill_id in Hdecomp';
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
        by destruct vs as [|v vs] => //; destruct v as [|v|] => //; by destruct v.
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

(** Extraction **)
Module Interpreter_ctx_extract.

Export DummyHost.

Definition run_one_step_ctx := run_one_step_ctx host_application_impl_correct.

Definition run_step_cfg_ctx_reform := run_step_cfg_ctx_reform.

Definition run_v_init := run_v_init.

Definition es_of_cfg := es_of_cfg.

Definition run_multi_step_raw := run_multi_step_raw host_application_impl_correct tt.

End Interpreter_ctx_extract.
