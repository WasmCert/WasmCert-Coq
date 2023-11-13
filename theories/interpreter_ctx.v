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

Import EvalContext.
  
Let host := host EvalContext.host_function.
Let cfg_tuple_ctx := @cfg_tuple_ctx EvalContext.host_function.

Let store_record := store_record EvalContext.host_function.
Let host_state := host_state EvalContext.host_instance.

Let e_typing := @e_typing EvalContext.host_function.
Let inst_typing := @inst_typing EvalContext.host_function.

Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                       (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).

Definition reduce_ctx (hs hs': host_state) (cfg cfg': cfg_tuple_ctx) : Prop :=
  match cfg with
  | (s, ccs, sc, oe) =>
      match cfg' with
      | (s', ccs', sc', oe') => reduce hs s empty_frame (ccs ⦃ sc ⦃ olist oe ⦄ ⦄) hs' s' empty_frame (ccs' ⦃ sc' ⦃ olist oe' ⦄ ⦄)
      end
  end.

(*
Lemma reduce_ctx_reduce (hs hs': host_state) s f s' f' es es':
  (forall ccs sc oe ccs' sc' oe', ccs ⦃ sc ⦃ olist oe ⦄ ⦄ = es ->
  ccs' ⦃ sc' ⦃ olist oe' ⦄ ⦄ = es' ->
  reduce_ctx hs hs' (s, f, ccs, sc, oe) (s', f', ccs', sc', oe')) <->
  reduce hs s f es hs' s' f' es'.
Proof.
  split; last by intros; subst.
  move => Hred.
  remember (ctx_decompose es) as de.
  destruct de as [[ccs sc] oe].
  symmetry in Heqde.
  remember (ctx_decompose es') as de'.
  destruct de' as [[ccs' sc'] oe'].
  symmetry in Heqde'.
  apply decompose_fill_id in Heqde.
  apply decompose_fill_id in Heqde'.
  specialize (Hred _ _ _ _ _ _ Heqde Heqde').
  unfold reduce_ctx in Hred.
  by rewrite Heqde Heqde' in Hred.
Qed.
*)

Ltac red_ctx_simpl :=
  repeat lazymatch goal with
  | _: _ |- reduce _ _ _ (foldl closure_ctx_fill _ _) _ _ _ (foldl closure_ctx_fill _ _) =>
      apply (list_closure_ctx_eval.(ctx_reduce))
  | _: _ |- reduce _ _ _ (foldl label_ctx_fill _ _) _ _ _ (foldl label_ctx_fill _ _) =>
      apply (list_label_ctx_eval.(ctx_reduce))
  end.

Ltac infer_hole :=
  repeat lazymatch goal with
  | |- context C [vs_to_es _] =>
      rewrite /vs_to_es
  | _: _ |- ?l ++ _ = ?l ++ _ =>
      f_equal => //
  | _: _ |- ?l1 ++ ?l2 = ?x :: ?l2 =>
      try instantiate (1 := [::x]) => //
  | _: _ |- ?l1 ++ ?l2 = ?x1 :: ?x2 :: ?l2 =>
      instantiate (1 := [::x1; x2]) => //
  | _: _ |- ?l1 ++ ?l2 = ?l3 ++ ?x :: ?l2 =>
      try instantiate (1 := l3 ++ [::x]); rewrite -catA => //
  | |- context C [ _ ++ [::] ] =>
      rewrite cats0
  | |- context C [v_to_e_list (rev (?l1 ++ ?l2))] =>
      rewrite rev_cat -v_to_e_cat => //
  | |- context C [ ( _ ++ _) ++ _ ] =>
      rewrite -catA
  end.

Definition run_one_step_ctx (hs: host_state) (cfg: cfg_tuple_ctx) : valid_cfg_ctx cfg -> {hs' & {cfg' | reduce_ctx hs hs' cfg cfg' /\ valid_cfg_ctx cfg'}} + False.
Proof.
  move => Hvalid.
  destruct cfg as [[[s ccs] sc] oe].
  destruct oe as [e | ]; last first.
  (* Exitting from contexts *)
  {
    unfold valid_cfg_ctx in Hvalid; destruct sc as [vs es]; subst; simpl in *.
    destruct Hvalid as [? Heq]; move/eqP in Heq; subst es.
    destruct ccs as [ | [fc lcs] ccs'].
    { (* entire instruction is const *)
      right. admit.
    }
    { destruct lcs as [ | lc lcs'].
      (* Exitting a local *)
      {
        destruct fc as [lvs lk lf les].
        destruct (length vs == lk) eqn:Hlen; move/eqP in Hlen.
        {
          destruct les as [ | e les'].
          { (* No instruction in the hole *)
            left; exists hs, (s, ccs', (vs ++ lvs, nil), None) => /=.
            split => //.
            red_ctx_simpl => //.
            repeat rewrite cats0.
            eapply r_label with (lh := LH_base (rev lvs) nil) => /=; infer_hole.
            by apply r_simple, rs_local_const; [ by apply v_to_e_const | by rewrite length_is_size v_to_e_size size_rev ].
          }
          { (* e is in the hole *)
            left; exists hs, (s, ccs', (vs ++ lvs, les'), Some e) => /=.
            split => //.
            red_ctx_simpl => //.
            rewrite cats0.
            eapply r_label with (lh := LH_base (rev lvs) (e :: les')) => /=; infer_hole.
            by apply r_simple, rs_local_const; [ by apply v_to_e_const | by rewrite length_is_size v_to_e_size size_rev ].
          }
        }
        (* length doesn't match *)
        { right. admit. }
      }
      (* Exitting a label *)
      { destruct lc as [lvs lk lces les].
        destruct les as [ | e les'].
        { (* No instruction in the hole still *)
          left; exists hs, (s, (fc, lcs') :: ccs', (vs ++ lvs, nil), None) => /=.
          split => //.
          red_ctx_simpl => //.
          repeat rewrite cats0.
          eapply r_label with (lh := LH_base (rev (FC_val fc)) (FC_post fc)) => /=; infer_hole.
          apply r_local => /=.
          red_ctx_simpl => //=.
          unfold fmask0, label_ctx_fill => /=.
          eapply r_label with (lh := LH_base (rev lvs) nil) => /=; infer_hole.
          apply r_simple, rs_label_const; by apply v_to_e_const.
        }
        { (* e is in the hole *)
          left; exists hs, (s, (fc, lcs') :: ccs', (vs ++ lvs, ), None) => /=.
          split => //.
          red_ctx_simpl => //.
          rewrite cats0.
          eapply r_label with (lh := LH_base (rev (FC_val fc)) (FC_post fc)) => /=; infer_hole.
          apply r_local => /=.
          red_ctx_simpl => //=.
          unfold fmask0, label_ctx_fill => /=.
          eapply r_label with (lh := LH_base (rev lvs) (e :: les')) => /=; infer_hole.
          apply r_simple, rs_label_const; by apply v_to_e_const.
        }
      }
  }
  { destruct cc as [ | cc ccs]; first exact None.
    destruct cc as [[fctx lctx] [vs es]].
    destruct e as [
      (* AI_basic *) [
      (* BI_unreachable *) |
      (* BI_nop *) |
      (* BI_drop *) |
      (* BI_select *) |
      (* BI_block (Tf t1s t2s) es *) [t1s t2s] es |
      (* BI_loop (Tf t1s t2s) es *) [t1s t2s] es |
      (* BI_if tf es1 es2 *) tf es1 es2 |
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
      (* BI_load t [Some (tp, sx)|None] a off *) t [[tp sx]|] a off |
      (* BI_store t [Some tp|None] a off *) t [tp|] a off |
      (* BI_current_memory *) |
      (* BI_grow_memory *) |
      (* BI_const _ *) |
      (* BI_unop t op *) t op |
      (* BI_binop t op *) t op |
      (* BI_testop [T_i32|T_i64|T_f32|T_f64] testop *) [| | |] testop |
      (* BI_relop t op *) t op |
      (* BI_cvtop t2 [CVO_convert|CVO_reinterpret] t1 sx *) t2 [|] t1 sx ] |
      (* AI_trap *) |
      (* AI_invoke a *) a |
      (* AI_label ln les es *) ln les es |
      (* AI_local ln lf es *) ln lf es ].

    * (* AI_basic BI_unreachable *)
      apply <<hs, s, f, vs_to_es ves ++ [:: AI_trap]>>'.
      by apply reduce_unreachable.

    * (* AI_basic BI_nop *)
      apply <<hs, s, f, vs_to_es ves>>'.
      by apply reduce_nop.

    * (* AI_basic BI_drop *)
      destruct ves as [|v ves'] eqn:Heqves.
      + (* [::] *)
        apply RS''_error. by apply drop_error.
      + (* v :: ves' *)
        apply <<hs, s, f, vs_to_es ves'>>'. by apply reduce_drop.

    * (* AI_basic BI_select *)
      destruct ves as [|v3 [|v2 [|v1 ves']]];
        try by (apply RS''_error; apply select_error_size).
      (* [:: v3, v2, v1 & ves'] *)
      destruct v3 as [c| | |] eqn:?;
        try by
          (apply RS''_error; eapply select_error_i32 with (v3 := v3); subst v3).
      (* VAL_int32 c *)
      destruct (c == Wasm_int.int_zero i32m) eqn:?.
      + (* true *)
        apply <<hs, s, f, vs_to_es (v2 :: ves')>>'.
        by apply reduce_select_false.
      + (* false *)
        apply <<hs, s, f, vs_to_es (v1 :: ves')>>'.
        by apply reduce_select_true; clear run_step_aux; lias.

    * (* AI_basic (BI_block (Tf t1s t2s) es) *)
      destruct (length ves >= length t1s) eqn:?.
      + (* true *)
        destruct (split_n ves (length t1s)) as [ves' ves''] eqn:?.
        remember (AI_label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)) as e'.
        apply <<hs, s, f, vs_to_es ves'' ++ [:: e']>>'.
        by subst e'; eapply reduce_block.
      + (* false *)
        apply RS''_error.
        (* TODO should use length in lemmas instead? *)
        repeat rewrite length_is_size in Heqb.
        by apply block_error; clear - Heqb; lias.

    * (* AI_basic (BI_loop (Tf t1s t2s) es) *)
      destruct (length ves >= length t1s) eqn:?.
      + (* true *)
        destruct (split_n ves (length t1s)) as [ves' ves''] eqn:?.
        apply <<hs, s, f, vs_to_es ves''
          ++ [:: AI_label (length t1s) [:: AI_basic (BI_loop (Tf t1s t2s) es)] (vs_to_es ves' ++ to_e_list es)]
        >>'.
        by apply reduce_loop.
      + (* false *)
        apply RS''_error.
        apply loop_error; repeat rewrite -length_is_size; clear run_step_aux; lias.

    * (* AI_basic (BI_if tf es1 es2) *)
      destruct ves as [|v ves'] eqn:?;
        try by (apply RS''_error; apply if_error_0).
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?;
        try by (apply RS''_error; eapply if_error_typeof => //).
      (* VAL_int32 c *)
      destruct (c == Wasm_int.int_zero i32m) eqn:?.
      + (* true *)
        apply <<hs, s, f, vs_to_es ves' ++ [:: AI_basic (BI_block tf es2)]>>'.
        by eapply reduce_if_false.
      + (* false *)
        apply <<hs, s, f, vs_to_es ves' ++ [:: AI_basic (BI_block tf es1)]>>'.
        by eapply reduce_if_true.

    * (* AI_basic (BI_br j) *)
      apply break(j, ves).
      by apply break_br.

    * (* AI_basic (BI_br_if j) *)
      destruct ves as [|v ves'];
        try by (apply RS''_error; apply br_if_error_0).
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?;
        try by (apply RS''_error; eapply br_if_error_i32 with (v := v); subst v).
      (* VAL_int32 c *)
      destruct (c == Wasm_int.int_zero i32m) eqn:?.
      ** (* true *)
         apply <<hs, s, f, vs_to_es ves'>>'.
         by eapply reduce_br_if_false.
      ** (* false *)
         apply <<hs, s, f, vs_to_es ves' ++ [:: AI_basic (BI_br j)]>>'.
         by eapply reduce_br_if_true; clear run_step_aux; lias.

    * (* AI_basic (BI_br_table js j) *)
      destruct ves as [|v ves'];
        try by (apply RS''_error; apply br_table_error_0).
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?;
        try by (apply RS''_error; eapply br_table_error_i32 with (v := v); subst v).
      remember (Wasm_int.nat_of_uint i32m c) as k.
      destruct (k < length js) eqn:?.
      + (* true *)
        destruct (List.nth_error js k) as [js_at_k|] eqn:?.
        -- (* Some js_at_k *)
           apply <<hs, s, f, vs_to_es ves' ++ [::AI_basic (BI_br js_at_k)]>>'.
           by apply reduce_br_table with (k := k).
        -- (* None *)
           apply RS''_error.
           by apply br_table_error_kth with (k := k) (c := c) (ves' := ves').
      + (* false *)
        apply <<hs, s, f, vs_to_es ves' ++ [::AI_basic (BI_br j)]>>'.
        by apply reduce_br_table_length with (k := k); clear run_step_aux; lias.

    * (* AI_basic BI_return *)
      apply RS''_return with (rvs := ves).
      by left => //.

    * (* AI_basic (BI_call j) *)
      destruct (List.nth_error f.(f_inst).(inst_funcs) j) as [a|] eqn:?.
      + (* Some a *)
        apply <<hs, s, f, vs_to_es ves ++ [:: AI_invoke a]>>'.
        by apply reduce_call.
      + (* None *)
        apply RS''_error.
        by apply call_error.

    * (* AI_basic (BI_call_indirect j) *)
      destruct ves as [|v ves'] eqn:?;
        try by (apply RS''_error; apply call_indirect_error_0).
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?;
        try by (apply RS''_error; eapply call_indirect_error_typeof => //).
      (* VAL_int32 c *)
      destruct (stab_addr s f (Wasm_int.nat_of_uint i32m c)) as [a|] eqn:?.
      + (* Some a *)
        destruct (List.nth_error s.(s_funcs) a) as [cl|] eqn:?.
        -- (* Some cl *)
           destruct (stypes s f.(f_inst) j == Some (cl_type cl)) eqn:?.
           ** (* true *)
              apply <<hs, s, f, vs_to_es ves' ++ [:: AI_invoke a]>>'.
              by eapply reduce_call_indirect_success with (cl := cl).
           ** (* false *)
              apply <<hs, s, f, vs_to_es ves' ++ [:: AI_trap]>>'.
              by eapply reduce_call_indirect_failure_1 with (cl := cl) (a := a).
        -- (* None *)
           apply RS''_error.
           by eapply call_indirect_error_ath with (a := a).
      + (* None *)
        apply <<hs, s, f, vs_to_es ves' ++ [:: AI_trap]>>'.
        by eapply reduce_call_indirect_failure_2.

    * (* AI_basic (BI_get_local j) *)
      destruct (j < length f.(f_locs)) eqn:?.
      + (* true *)
        destruct (List.nth_error f.(f_locs) j) as [vs_at_j|] eqn:?.
        -- (* Some vs_at_j *)
           apply <<hs, s, f, vs_to_es (vs_at_j :: ves)>>'.
           by apply reduce_get_local.
        -- (* None *)
           apply RS''_error. by apply get_local_error_jth_none.
      + (* false *)
        apply RS''_error. by apply get_local_error_length; clear run_step_aux; lias.

    * (* AI_basic (BI_set_local j) *)
      destruct ves as [|v ves'] eqn:?.
      + (* [::] *)
        apply RS''_error. by apply set_local_error_0.
      + (* v :: ves' *)
        destruct (j < length f.(f_locs)) eqn:?.
        -- (* true *)
           apply <<hs, s, Build_frame (set_nth v f.(f_locs) j v) f.(f_inst), vs_to_es ves'>>'.
           by eapply reduce_set_local.
        -- (* false *)
           apply RS''_error. by eapply set_local_error_length.

    * (* AI_basic (BI_tee_local j) *)
      destruct ves as [|v ves'] eqn:?.
      + (* [::] *)
        apply RS''_error. by apply tee_local_error_0.
      + (* v :: ves' *)
        apply <<hs, s, f, vs_to_es (v :: v :: ves') ++ [:: AI_basic (BI_set_local j)]>>'.
        by eapply reduce_tee_local.

    * (* AI_basic (BI_get_global j) *)
      destruct (sglob_val s f.(f_inst) j) as [xx|] eqn:?.
      + (* Some xx *)
        apply <<hs, s, f, vs_to_es (xx :: ves)>>'.
        by apply reduce_get_global.
      + (* None *)
        apply RS''_error. by apply get_global_error.

    * (* AI_basic (BI_set_global j) *)
      destruct ves as [|v ves'] eqn:?.
      + (* [::] *)
        apply RS''_error. by apply set_global_error_0.
      + (* v :: ves' *)
        destruct (supdate_glob s f.(f_inst) j v) as [s'|] eqn:?.
        -- (* Some s' *)
           apply <<hs, s', f, vs_to_es ves'>>'.
           by eapply reduce_set_global => //.
        -- (* None *)
           apply RS''_error. by eapply set_global_error_jth.

    * (* AI_basic (BI_load t (Some (tp, sx)) a off) *)
      (* TODO can this and the next branch be deduped? *)
      destruct ves as [|v ves'] eqn:?.
      + (* [::] *)
        apply RS''_error. by apply load_error_0.
      + (* v :: ves' *)
        destruct v as [c| | |] eqn:?;
          try by (apply RS''_error; eapply load_error_typeof => //).
        (* VAL_int32 c *)
        destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
        -- (* Some j *)
           destruct (List.nth_error s.(s_mems) j) as [mem_s_j|] eqn:?.
           ** (* Some mem_s_j*)
              destruct (load_packed sx (mem_s_j) (Wasm_int.N_of_uint i32m c) off (tp_length tp) (t_length t)) as [bs|] eqn:?.
              ++ (* Some bs *)
                 apply <<hs, s, f, vs_to_es (wasm_deserialise bs t :: ves')>>'.
                 by apply reduce_load_packed_success with (mem_s_j := mem_s_j) (j := j) (c := c).
              ++ (* None *)
                 apply <<hs, s, f, vs_to_es ves' ++ [:: AI_trap]>>'.
                 by apply reduce_load_packed_failure with (mem_s_j := mem_s_j) (j := j) (c := c).
           ** (* None*)
              apply RS''_error. by eapply load_error_jth with (j := j).
        -- (* None *)
           apply RS''_error. by eapply load_error_smem_ind.

    * (* AI_basic (BI_load t None a off) *)
      destruct ves as [|v ves'] eqn:?.
      + (* [::] *)
        apply RS''_error. by apply load_error_0.
      + (* v :: ves' *)
        destruct v as [c| | |] eqn:?;
          try by (apply RS''_error; eapply load_error_typeof => //).
        (* VAL_int32 c *)
        destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
        -- (* Some j *)
           destruct (List.nth_error s.(s_mems) j) as [mem_s_j|] eqn:?.
           ** (* Some mem_s_j*)
              destruct (load (mem_s_j) (Wasm_int.N_of_uint i32m c) off (t_length t)) as [bs|] eqn:?.
              ++ (* Some bs *)
                 apply <<hs, s, f, vs_to_es (wasm_deserialise bs t :: ves')>>'.
                 by apply reduce_load_success
                   with (c := c) (j := j) (mem_s_j := mem_s_j).
              ++ (* None *)
                 apply <<hs, s, f, vs_to_es ves' ++ [:: AI_trap]>>'.
                 by apply reduce_load_failure
                   with (c := c) (j := j) (mem_s_j := mem_s_j).
           ** (* None *)
              apply RS''_error. by eapply load_error_jth with (j := j).
        -- (* None *)
           apply RS''_error. by eapply load_error_smem_ind.

    * (* AI_basic (BI_store t (Some tp) a off) *)
      (* TODO dedupe with the branch below by matching tp later? *)
      destruct ves as [|v [|v' ves']] eqn:?;
        try by (apply RS''_error; apply store_error_size).
      (* v :: v' :: ves' *)
      destruct v' as [c| | |] eqn:?;
        try by (apply RS''_error; eapply store_error_typeof => //).
      (* VAL_int32 c *)
      destruct (types_agree t v) eqn:?.
      + (* true *)
        destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
        -- (* Some j *)
           destruct (List.nth_error s.(s_mems) j) as [mem_s_j|] eqn:?.
           ** (* Some mem_s_j *)
              destruct (store_packed mem_s_j (Wasm_int.N_of_uint i32m c) off (bits v) (tp_length tp)) as [mem'|] eqn:?.
              ++ (* Some mem' *)
                 apply <<hs, upd_s_mem s (set_nth mem' s.(s_mems) j mem'), f, vs_to_es ves'>>'.
                 by eapply reduce_store_packed_success with (mem_s_j := mem_s_j).
              ++ (* None *)
                 apply <<hs, s, f, vs_to_es ves' ++ [:: AI_trap]>>'.
                 by eapply reduce_store_packed_failure with (j := j) (mem_s_j := mem_s_j).
           ** (* None *)
              apply RS''_error. by eapply store_error_jth with (j := j).
        -- (* None *)
           apply RS''_error. by eapply store_error_smem.
      + (* false *)
        apply RS''_error. by apply store_error_types_disagree with (v := v) (c := c) (ves' := ves').

    * (* AI_basic (BI_store t None a off) *)
      destruct ves as [|v [|v' ves']] eqn:?;
        try by (apply RS''_error; apply store_error_size).
      (* v :: v' :: ves' *)
      destruct v' as [c| | |] eqn:?;
        try by (apply RS''_error; eapply store_error_typeof => //).
      (* VAL_int32 c *)
      destruct (types_agree t v) eqn:?.
      + (* true *)
        destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
        -- (* Some j *)
           destruct (List.nth_error s.(s_mems) j) as [mem_s_j|] eqn:?.
           ** (* Some mem_s_j *)
              destruct (store mem_s_j (Wasm_int.N_of_uint i32m c) off (bits v) (t_length t)) as [mem'|] eqn:?.
              ++ (* Some mem' *)
                 apply <<hs, upd_s_mem s (set_nth mem' s.(s_mems) j mem'), f, vs_to_es ves'>>'.
                 by eapply reduce_store_success with (mem_s_j := mem_s_j).
              ++ (* None *)
                 apply <<hs, s, f, vs_to_es ves' ++ [:: AI_trap]>>'.
                 by eapply reduce_store_failure with (j := j) (mem_s_j := mem_s_j).
           ** (* None *)
              apply RS''_error. by eapply store_error_jth with (j := j).
        -- (* None *)
           apply RS''_error. by eapply store_error_smem.
      + (* false *)
        apply RS''_error. by apply store_error_types_disagree with (v := v) (c := c) (ves' := ves').

    * (* AI_basic BI_current_memory *)
      destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
      + (* Some j *)
        destruct (List.nth_error s.(s_mems) j) as [s_mem_s_j|] eqn:?.
        -- (* Some j *)
           remember (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j)))) as v' eqn:?.
           apply <<hs, s, f, vs_to_es (v' :: ves)>>'.
           by apply reduce_current_memory with (j := j) (s_mem_s_j := s_mem_s_j).
        -- (* None *)
           apply RS''_error. by apply current_memory_error_jth with (j := j).
      + (* None *)
        apply RS''_error. by apply current_memory_error_smem => //.

    * (* AI_basic BI_grow_memory *)
      destruct ves as [|v ves'] eqn:?;
        try by (apply RS''_error; apply grow_memory_error_0).
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?;
        try by (apply RS''_error; by eapply grow_memory_error_typeof => //).
      (* VAL_int32 c *)
      destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
      + (* Some j *)
        destruct (List.nth_error s.(s_mems) j) as [s_mem_s_j|] eqn:Heqsmem.
        -- (* Some s_mem_s_j *)
           remember (mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m c)) as mem'.
           destruct mem' as [mem''|].
           ** (* Some mem'' *)
              remember (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j)))) as v'.
              remember (upd_s_mem s (set_nth mem'' s.(s_mems) j mem'')) as s'.
              apply <<hs, s', f, (vs_to_es (v' :: ves'))>>'.
              by eapply reduce_grow_memory with (j := j) (s_mem_s_j := s_mem_s_j) (mem'' := mem'') => //.
           ** (* None *)
              apply <<hs, s, f, vs_to_es (VAL_int32 int32_minus_one :: ves')>>'.
              by eapply reduce_grow_memory_failure with (j := j) (s_mem_s_j := s_mem_s_j).
        -- (* None *)
           apply RS''_error. by eapply grow_memory_error_jth with (j := j).
      + (* None *)
        apply RS''_error. by eapply grow_memory_error_smem => //.

    * (* AI_basic (BI_const _) *)
      by exfalso.

    * (* AI_basic (BI_unop t op) *)
      destruct ves as [|v ves'].
      + (* [::] *)
        apply RS''_error. by apply unop_error.
      + (* v :: ves' *)
        apply <<hs, s, f, vs_to_es (app_unop op v :: ves')>>'.
        by apply reduce_unop.

    * (* AI_basic (BI_binop t op) *)
      destruct ves as [|v2 [|v1 ves']];
        try by (apply RS''_error; apply binop_error_size).
      (* [:: v2, v1 & ves'] *)
      destruct (app_binop op v1 v2) as [v|] eqn:?.
      + (* Some v *)
        apply <<hs, s, f, vs_to_es (v :: ves')>>'.
        by apply reduce_binop.
      + (* None *)
        apply <<hs, s, f, (vs_to_es ves') ++ [:: AI_trap]>>'.
        by apply reduce_binop_trap.

    * (* AI_basic (BI_testop T_i32 testop) *)
      destruct ves as [|[c| | |] ves'] eqn:?;
        try by (apply RS''_error; by eapply testop_i32_error => //).
      + (* [::] *)
        apply RS''_error. by apply testop_error_0.
      + (* VAL_int32 c :: ves' *)
        apply <<hs, s, f, vs_to_es (VAL_int32 (wasm_bool (@app_testop_i i32t testop c)) :: ves')>>'.
        by apply reduce_testop_i32.

    * (* AI_basic (BI_testop T_i64 testop) *)
      (* TODO un-nest this destruct? could make the 'try by' clearer *)
      destruct ves as [|v ves'].
      + (* [::] *)
        apply RS''_error. by apply testop_error_0.
      + (* v :: ves' *)
        destruct v as [|c| |];
          try by (apply RS''_error; by eapply testop_i64_error => //).
        (* VAL_int64 c *)
        apply <<hs, s, f, vs_to_es (VAL_int32 (wasm_bool (@app_testop_i i64t testop c)) :: ves')>>'.
        by eapply reduce_testop_i64.

    * (* AI_basic (BI_testop T_f32 testop) *)
      apply RS''_error. by apply testop_f32_error.

    * (* AI_basic (BI_testop T_f64 testop) *)
      apply RS''_error. by apply testop_f64_error.

    * (* AI_basic (BI_relop t op) *)
      destruct ves as [|v2 [|v1 ves']];
          try by (apply RS''_error; apply relop_error_size).
      (* [:: v2, v1 & ves'] *)
      apply <<hs, s, f, vs_to_es (VAL_int32 (wasm_bool (app_relop op v1 v2)) :: ves')>>'.
      by apply reduce_relop.

    * (* AI_basic (BI_cvtop t2 CVO_convert t1 sx) *)
      destruct ves as [|v ves'];
        try by (apply RS''_error; apply cvtop_error_0).
      (* v :: ves' *)
      destruct (types_agree t1 v) eqn:Ht1.
      + (* true *)
        destruct (cvt t2 sx v) as [v'|] eqn:Heqv'.
        -- (* Some v' *)
           apply <<hs, s, f, vs_to_es (v' :: ves')>>'.
           by apply reduce_cvtop_success.
        -- (* None *)
           apply <<hs, s, f, vs_to_es ves' ++ [::AI_trap]>>'.
           by apply reduce_cvtop_trap.
      + (* false *)
        apply RS''_error. by eapply cvtop_error_types_disagree.

    * (* AI_basic (BI_cvtop t2 CVO_reinterpret t1 sx) *)
      destruct ves as [|v ves'];
        try by (apply RS''_error; apply cvtop_error_0).
      destruct (types_agree t1 v) eqn:?.
      + (* true *)
        destruct sx eqn:Heqsx.
        -- (* Some _ *)
           apply RS''_error. by eapply cvtop_error_reinterpret_sx.
        -- (* None *)
           apply <<hs, s, f, (vs_to_es (wasm_deserialise (bits v) t2 :: ves'))>>'.
           by apply reduce_reinterpret.
      + (* false *)
        apply RS''_error. by eapply cvtop_error_types_disagree.

    * (* AI_trap *)
      by exfalso.

    * (* AI_invoke a *)
      destruct (List.nth_error s.(s_funcs) a) as [cl|] eqn:?.
      + (* Some cl *)
        destruct cl as [i [t1s t2s] ts es | [t1s t2s] cl'] eqn:?.
        -- (* FC_func_native i (Tf t1s t2s) ts es *)
           remember (length t1s) as n eqn:?.
           remember (length t2s) as m eqn:?.
           destruct (length ves >= n) eqn:?.
           ** (* true *)
              destruct (split_n ves n) as [ves' ves''] eqn:?.
              remember (n_zeros ts) as zs eqn:?.
              apply <<hs, s, f, vs_to_es ves'' ++ [::
                AI_local
                m
                (Build_frame (rev ves' ++ zs) i)
                [::AI_basic (BI_block (Tf [::] t2s) es)]
              ]>>'.
              by eapply reduce_invoke_native with (n := n) (ts := ts) (t1s := t1s).
           ** (* false *)
              apply RS''_error.
              by eapply invoke_func_native_error_n with
                (n := n) (t1s := t1s) (t2s := t2s) (i := i) (ts := ts) (es := es).
        -- (* FC_func_host (Tf t1s t2s) cl' *)
           remember (length t1s) as n eqn:?.
           remember (length t2s) as m eqn:?.
           destruct (length ves >= n) eqn:?.
           ** (* true *)
              destruct (split_n ves n) as [ves' ves''] eqn:?.
              destruct (host_application_impl hs s (Tf t1s t2s) cl' (rev ves')) as [hs' [[s' rves]|]] eqn:?.
              ++ (* (hs', Some (s', rves)) *)
                 apply <<hs', s', f, vs_to_es ves'' ++ (result_to_stack rves)>>'.
                 by eapply reduce_invoke_host_success with
                   (n := n) (t1s := t1s) (t2s := t2s) (cl' := cl') (ves' := ves').
              ++ (* (hs', None) *)
                 apply <<hs', s, f, vs_to_es ves ++ [::AI_invoke a]>>'.
                 by eapply reduce_invoke_host_diverge with
                   (n := n) (t1s := t1s) (t2s := t2s) (cl' := cl') (ves' := ves') (ves'' := ves'') => //.
           ** (* false *)
              apply RS''_error.
              by eapply invoke_func_host_error_n with
                (n := n) (t1s := t1s) (t2s := t2s) (cl' := cl').
      + (* None *)
        apply RS''_error. by apply invoke_host_error_ath.

    * (* AI_label ln les es *)
      destruct (es_is_trap es) eqn:?.
      + (* true *)
        apply <<hs, s, f, vs_to_es ves ++ [::AI_trap]>>'.
        by apply reduce_label_trap.
      + (* false *)
        destruct (const_list es) eqn:?.
        -- (* true *)
           apply <<hs, s, f, vs_to_es ves ++ es>>'.
           by apply reduce_label_const.
        -- (* false *)
          assert (run_step_measure es < S (run_one_step_measure (AI_label ln les es)))%coq_nat as Hmeasure.
          { simpl. by rewrite run_step_measure_eq; lias. }
          specialize (run_step_aux hs s f es Hmeasure).
          destruct run_step_aux as
             [ Hv | Herr | n bvs H | rvs H | hs' s' f' es'] eqn:?.
           ** (* RS'_value hs s f Hv *)
              exfalso. by apply const_trap_contradiction with (es := es).
           ** (* RS'_error hs Herr *)
              apply RS''_error.
              by apply label_error_rec.
           ** (* RS'_break hs s f es n bvs *)
              destruct n as [|n].
              ++ (* 0 *)
                 destruct (length bvs >= ln) eqn:?.
                 --- (* true *)
                     apply <<hs, s, f, vs_to_es ((take ln bvs) ++ ves) ++ les>>'.
                     by apply reduce_label_break_rec.
                 --- (* false *)
                     apply RS''_error.
                     by apply label_error_break_rec with (bvs := bvs).
              ++ (* n.+1 *)
                 apply break(n, bvs).
                 by apply label_break_rec.
           ** (* RS'_return hs s f es rvs H *)
              apply RS''_return with (rvs := rvs).
              (* TODO move into a lemma? *)
              right. destruct H as [i [lh H]].
              by exists ln, les, es, i, lh => //.
           ** (* RS'_normal hs s f es hs' s' f' es' *)
              apply <<hs', s', f', vs_to_es ves ++ [:: AI_label ln les es']>>'.
              by apply reduce_label_rec.

    * (* AI_local ln lf es *)
      destruct (es_is_trap es) eqn:?.
      + (* true *)
        apply <<hs, s, f, vs_to_es ves ++ [::AI_trap]>>'.
        by apply reduce_local_trap.
      + (* false *)
        destruct (const_list es) eqn:?.
        -- (* true *)
           destruct (length es == ln) eqn:?.
           ** (* true *)
              apply <<hs, s, f, vs_to_es ves ++ es>>'.
              by apply reduce_local_const.
           ** (* false *)
              apply RS''_error.
              by apply local_error_const_len.
        -- (* false *)
           assert (run_step_measure es < S (run_one_step_measure (AI_local ln lf es)))%coq_nat as Hmeasure.
           { simpl. by rewrite run_step_measure_eq; lias. }
           specialize (run_step_aux hs s lf es Hmeasure).
           destruct run_step_aux as
             [ Hv | Herr | n bvs | rvs H | hs' s' f' es'] eqn:?; clear Hmeasure.
           ** (* RS'_value hs s f Hv *)
              exfalso. by apply const_trap_contradiction with (es := es).
           ** (* RS'_error hs Herr *)
              apply RS''_error.
              by apply local_error_rec.
           ** (* RS'_break hs s f es n bvs *)
              apply RS''_error.
              by apply local_error_break_rec with (n := n) (bvs := bvs).
           ** (* RS'_return hs s f es rvs H *)
              destruct (length rvs >= ln) eqn:?.
              ++ (* true *)
                 apply <<hs, s, f, vs_to_es (take ln rvs ++ ves)>>'.
                 by apply reduce_local_return_rec.
              ++ (* false *)
                 apply RS''_error.
                 apply local_return_error with (rvs := rvs) => //.
           ** (* RS'_normal hs s f es hs' s' f' es' *)
              apply <<hs', s', f, vs_to_es ves ++ [:: AI_local ln f' es']>>'.
              by apply reduce_local_rec.
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
