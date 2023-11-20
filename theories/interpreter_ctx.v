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

Ltac get_cc ccs Hvalid :=
  let fc := fresh "fc" in 
  let lcs := fresh "lcs" in 
  let ccs' := fresh "ccs'" in 
  destruct ccs as [ | [fc lcs] ccs']; first by unfold valid_cfg_ctx, valid_ccs in Hvalid; inversion Hvalid.

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
| RSC_value:
  const_list (es_of_cfg cfg) ->
  run_step_ctx_result hs cfg
| RSC_error:
  forall ts, (config_typing (s_of_cfg cfg) empty_frame (es_of_cfg cfg) ts -> False) ->
  run_step_ctx_result hs cfg
| RSC_admit:
  False ->
  run_step_ctx_result hs cfg
.

Definition rsc_admit_inhab : False.
Admitted.


Ltac admit_rsc :=
  by apply RSC_admit; apply rsc_admit_inhab.


Notation "<< hs , cfg >>" := (@RSC_normal _ _ hs cfg).

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
  valid_cfg_ctx (s, ccs, sc, Some (AI_basic (BI_br j))) ->
  run_step_ctx_result hs (s, ccs, sc, Some (AI_basic (BI_br j))).
Proof.
  intros hs s ccs [vs es] j Hvalid.
  get_cc ccs Hvalid.
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
      by admit_rsc.
  - (* Not enough labels *)
    by admit_rsc.
Qed.
    
Definition run_ctx_return: forall hs s ccs sc,
  valid_cfg_ctx (s, ccs, sc, Some (AI_basic BI_return)) ->
  run_step_ctx_result hs (s, ccs, sc, Some (AI_basic BI_return)).
Proof.  
  intros hs s ccs [vs es] Hvalid.
  get_cc ccs Hvalid.
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
    by admit_rsc.
Qed.
    
(* One step of execution; does not perform the context update in the end to shift to the new instruction. *)
Definition run_one_step_ctx (hs: host_state) (cfg: cfg_tuple_ctx) : valid_cfg_ctx cfg -> run_step_ctx_result hs cfg.
Proof.
  move => Hvalid.
  destruct cfg as [[[s ccs] sc] oe].
  destruct oe as [e | ]; last first.
  (* Exitting from contexts *)
  {
    unfold valid_cfg_ctx in Hvalid; destruct sc as [vs es]; subst; simpl in Hvalid.
    destruct Hvalid as [? Heq]; move/eqP in Heq; subst es.
    destruct ccs as [ | [fc lcs] ccs'].
    { (* entire instruction is const *)
      apply RSC_value => /=.
      by rewrite cats0; apply v_to_e_const.
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
        { by admit_rsc. }
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
        by admit_rsc.
      + (* v :: vs0 *)
        apply <<hs, (s, ccs, (vs0, es0), None)>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_drop.
      
    - (* AI_basic BI_select *)
      destruct vs0 as [|v3 [|v2 [|v1 vs0]]].
        (*  try by (apply RS''_error; apply select_error_size). *)
        1,2,3: by admit_rsc.
      (* [:: v3, v2, v1 & vs0] *)
        destruct v3 as [c| | |] eqn:?.
        2,3,4: by admit_rsc.
 (*       try by
          (apply RS''_error; eapply select_error_i32 with (v3 := v3); subst v3).*)
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
        by admit_rsc.
        (* apply RS''_error.
        (* TODO should use length in lemmas instead? *)
        repeat rewrite length_is_size in Heqb.
        by apply block_error; clear - Heqb; lias.*)

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
        by admit_rsc.
      (*destruct (length ves >= length t1s) eqn:?.
      + (* true *)
        destruct (split_n ves (length t1s)) as [ves' ves''] eqn:?.
        apply <<hs, s, f, vs_to_es ves''
          ++ [:: AI_label (length t1s) [:: AI_basic (BI_loop (Tf t1s t2s) es)] (vs_to_es ves' ++ to_e_list es)]
        >>'.
        by apply reduce_loop.
      + (* false *)
        apply RS''_error.
        apply loop_error; repeat rewrite -length_is_size; clear run_step_aux; lias.*)
        
    - (* AI_basic (BI_if tf es1 es2) *)
      destruct vs0 as [|v vs0]; first by admit_rsc.
 (*       try by (apply RS''_error; apply if_error_0). *)
      (* v :: ves' *)
      destruct v as [c| | |].
      2,3,4: by admit_rsc. 
      (* VAL_int32 c *)
      destruct (c == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
      + (* true *)
        apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_block tf es2)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_if_false.
      + (* false *)
        apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_block tf es1)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_if_true.

    - (* AI_basic (BI_br j) *)
      by apply run_ctx_br.

    - (* AI_basic (BI_br_if j) *)
      destruct vs0 as [|v vs0]; first by admit_rsc.
     (*   try by (apply RS''_error; apply br_if_error_0). *)
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?.
      2,3,4: by admit_rsc.
      (*  try by (apply RS''_error; eapply br_if_error_i32 with (v := v); subst v). *)
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
      destruct vs0 as [|v vs0]; first by admit_rsc.
       (* try by (apply RS''_error; apply br_table_error_0).*)
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?.
      2,3,4: by admit_rsc.
      (*  try by (apply RS''_error; eapply br_table_error_i32 with (v := v); subst v). *)
      remember (Wasm_int.nat_of_uint i32m c) as k.
      destruct (k < length js) eqn:Hlen.
      + (* true *)
        destruct (List.nth_error js k) as [js_at_k|] eqn: Hnth.
        * (* Some js_at_k *)
          apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_br js_at_k)))>> => /=.
          resolve_reduce_ctx vs0 es0.
          by apply r_simple; subst; apply rs_br_table.
        * (* None *)
          by admit_rsc.
          (* apply RS''_error.
           by apply br_table_error_kth with (k := k) (c := c) (ves' := ves'). *)
      + (* false *)
        apply <<hs, (s, ccs, (vs0, es0), Some (AI_basic (BI_br j)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; subst; apply rs_br_table_length; lias.
        
    - (* AI_basic BI_return *)
      by apply run_ctx_return.

    - (* AI_basic (BI_call j) *)
      get_cc ccs Hvalid.
      destruct (List.nth_error fc.(FC_frame).(f_inst).(inst_funcs) j) as [a|] eqn: Hnth.
      + (* Some a *)
        apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_invoke a))>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_call.
      + (* None *)
        by admit_rsc.
        (* apply RS''_error.
        by apply call_error. *)

    - (* AI_basic (BI_call_indirect j) *)
      get_cc ccs Hvalid.    
      destruct vs0 as [|v vs0]; first by admit_rsc.
      (*  try by (apply RS''_error; apply call_indirect_error_0). *)
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?.
      2,3,4: by admit_rsc.
       (* try by (apply RS''_error; eapply call_indirect_error_typeof => //). *)
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
              (*apply <<hs, s, f, vs_to_es ves' ++ [:: AI_trap]>>'.
              by eapply reduce_call_indirect_failure_1 with (cl := cl) (a := a).*)
        * (* None *)
          by admit_rsc.
          (*
           apply RS''_error.
           by eapply call_indirect_error_ath with (a := a). *)
      + (* None *)
        apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_trap))>>.
        resolve_reduce_ctx vs0 es0.
        by eapply r_call_indirect_failure2; subst.

    - (* AI_basic (BI_get_local j) *)
      get_cc ccs Hvalid.    
      remember (fc.(FC_frame)) as f.
      destruct (j < length f.(f_locs)) eqn:?.
      + (* true *)
        destruct (List.nth_error f.(f_locs) j) as [vs_at_j|] eqn:?.
        * (* Some vs_at_j *)
          apply <<hs, (s, (fc, lcs) :: ccs', (vs_at_j :: vs0, es0), None)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_get_local; subst.
        * (* None *)
          by admit_rsc.
           (* apply RS''_error. by apply get_local_error_jth_none. *)
      + (* false *)
        by admit_rsc.
        (* apply RS''_error. by apply get_local_error_length; clear run_step_aux; lias. *)

    - (* AI_basic (BI_set_local j) *)
      get_cc ccs Hvalid.    
      remember (fc.(FC_frame)) as f.
      destruct vs0 as [|v vs0].
      + (* [::] *)
        by admit_rsc.
        (*apply RS''_error. by apply set_local_error_0.*)
      + (* v :: ves' *)
        destruct (j < length f.(f_locs)) eqn:Hlen.
        * (* true *)
           apply <<hs, (s, ((Build_frame_ctx (fc.(FC_val)) fc.(FC_arity) (Build_frame (set_nth v f.(f_locs) j v) f.(f_inst)) fc.(FC_post)), lcs) :: ccs', (vs0, es0), None)>>.
           resolve_reduce_ctx vs0 es0.
           by eapply r_set_local; subst => //.
        * (* false *)
          by admit_rsc.
           (*apply RS''_error. by eapply set_local_error_length.*)

    - (* AI_basic (BI_tee_local j) *)
      destruct vs0 as [|v vs0].
      + (* [::] *)
        by admit_rsc.
        (*apply RS''_error. by apply tee_local_error_0.*)
      + (* v :: ves' *)
        apply <<hs, (s, ccs, (v :: v :: vs0, es0), Some (AI_basic (BI_set_local j)))>> => /=.
        resolve_reduce_ctx vs0 es0.
        by eapply r_simple, rs_tee_local.

    - (* AI_basic (BI_get_global j) *)
      get_cc ccs Hvalid.    
      remember (fc.(FC_frame)) as f.
      destruct (sglob_val s f.(f_inst) j) as [v|] eqn:Hsglob.
      + (* Some xx *)
        apply <<hs, (s, (fc, lcs) :: ccs', (v :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by eapply r_get_global; subst.
      + (* None *)
        by admit_rsc.
        (* apply RS''_error. by apply get_global_error. *)

    - (* AI_basic (BI_set_global j) *)
      get_cc ccs Hvalid.    
      remember (fc.(FC_frame)) as f.
      destruct vs0 as [|v vs0].
      + (* [::] *)
        by admit_rsc.
      + (* v :: ves' *)
        destruct (supdate_glob s f.(f_inst) j v) as [s'|] eqn:Hsupdate.
        * (* Some s' *)
          apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_set_global; subst.
        * (* None *)
          by admit_rsc.

    - (* AI_basic (BI_load t ops (Some (tp, sx)) a off) *)
      get_cc ccs Hvalid.    
      remember (fc.(FC_frame)) as f.
      destruct vs0 as [|v vs0].
      + (* [::] *)
        by admit_rsc.
      + (* v :: ves' *)
        destruct v as [c| | |] eqn:?.
        2,3,4: by admit_rsc.
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
             by admit_rsc.
           (*
            apply RS''_error. by eapply load_error_jth with (j := j). *)
           }
        * (* None *)
          by admit_rsc.
        (* apply RS''_error. by eapply load_error_smem_ind. *)

        (*
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
*)

    - (* AI_basic (BI_store t (Some tp) a off) *)
      (* TODO dedupe with the branch below by matching tp later? *)
      get_cc ccs Hvalid.    
      remember (fc.(FC_frame)) as f.
      destruct vs0 as [|v [|v' vs0]].
      1,2: by admit_rsc.
      (*  try by (apply RS''_error; apply store_error_size). *)
      (* v :: v' :: ves' *)
      destruct v' as [c| | |] eqn:?.
      2,3,4: by admit_rsc.
      (*  try by (apply RS''_error; eapply store_error_typeof => //). *)
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
             by admit_rsc.
             (* apply RS''_error. by eapply store_error_jth with (j := j). *)
           }
        * (* None *)
          by admit_rsc.
      (*   apply RS''_error. by eapply store_error_smem. *)
      + (* false *)
        by admit_rsc.
        (*apply RS''_error. by apply store_error_types_disagree with (v := v) (c := c) (ves' := ves'). *)

    - (* AI_basic BI_current_memory *)
      get_cc ccs Hvalid.    
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
          by admit_rsc.
          (* apply RS''_error. by apply current_memory_error_jth with (j := j). *)
      + (* None *)
        by admit_rsc.
        (* apply RS''_error. by apply current_memory_error_smem => //. *)

    - (* AI_basic BI_grow_memory *)
      get_cc ccs Hvalid.    
      remember (fc.(FC_frame)) as f.
      destruct vs0 as [|v vs0]; first by admit_rsc.
      (*  try by (apply RS''_error; apply grow_memory_error_0). *)
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?.
      2,3,4: by admit_rsc.
      (*  try by (apply RS''_error; by eapply grow_memory_error_typeof => //). *)
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
          by admit_rsc.
          (* apply RS''_error. by eapply grow_memory_error_jth with (j := j). *)
      + (* None *)
        by admit_rsc.
        (* apply RS''_error. by eapply grow_memory_error_smem => //. *)

    - (* AI_basic (BI_const _) *)
      unfold valid_cfg_ctx, valid_ccs, valid_split in Hvalid => /=.
      by inversion Hvalid.

    - (* AI_basic (BI_unop t op) *)
      destruct vs0 as [|v vs0].
      + (* [::] *)
        by admit_rsc.
        (* apply RS''_error. by apply unop_error. *)
      + (* v :: ves' *)
        apply <<hs, (s, ccs, (app_unop op v :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_unop.

    - (* AI_basic (BI_binop t op) *)
      destruct vs0 as [|v2 [|v1 vs0]].
      1,2: by admit_rsc.
      (*  try by (apply RS''_error; apply binop_error_size). *)
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
      (*  try by (apply RS''_error; by eapply testop_i32_error => //). *)
      + (* [::] *)
        by admit_rsc.
        (* apply RS''_error. by apply testop_error_0. *)
      + (* VAL_int32 c :: ves' *)
        destruct t as [| | |].
        3,4: by admit_rsc.
        (* i32 *)
        * destruct v as [c| | |].
          2,3,4: by admit_rsc.
          apply <<hs, (s, ccs, (VAL_int32 (wasm_bool (@app_testop_i i32t testop c)) :: vs0, es0), None)>>.
          resolve_reduce_ctx vs0 es0.
          by apply r_simple, rs_testop_i32.
        (* i64 *)
        * destruct v as [|c | |].
          1,3,4: by admit_rsc.
          apply <<hs, (s, ccs, (VAL_int32 (wasm_bool (@app_testop_i i64t testop c)) :: vs0, es0), None)>>.
          resolve_reduce_ctx vs0 es0.
          by apply r_simple, rs_testop_i64.

    - (* AI_basic (BI_relop t op) *)
      destruct vs0 as [|v2 [|v1 vs0]].
      1,2: by admit_rsc.
      (*    try by (apply RS''_error; apply relop_error_size). *)
      (* [:: v2, v1 & ves'] *)
      apply <<hs, (s, ccs, (VAL_int32 (wasm_bool (@app_relop op v1 v2)) :: vs0, es0), None)>>.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_relop.

    - (* AI_basic (BI_cvtop t2 CVO_convert t1 sx) *)
      destruct vs0 as [|v vs0]; first by admit_rsc.
       (* try by (apply RS''_error; apply cvtop_error_0). *)
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
            (* apply RS''_error. by eapply cvtop_error_reinterpret_sx. *)
            by admit_rsc.
          }
          { (* None *)
            apply <<hs, (s, ccs, ((wasm_deserialise (bits v) t2) :: vs0, es0), None)>>.
            resolve_reduce_ctx vs0 es0.
            by apply r_simple, rs_reinterpret.
          }
      + (* false *)
        by admit_rsc.
        (* apply RS''_error. by eapply cvtop_error_types_disagree. *)

    - (* AI_trap *)
      get_cc ccs Hvalid.
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
      get_cc ccs Hvalid.    
      destruct (List.nth_error s.(s_funcs) a) as [cl|] eqn:?.
      + (* Some cl *)
        destruct cl as [i [t1s t2s] ts es | [t1s t2s] cl'] eqn:?.
        * (* FC_func_native i (Tf t1s t2s) ts es *)
           remember (length t1s) as n eqn:?.
           remember (length t2s) as m eqn:?.
           destruct (length vs0 >= n) eqn:Hlen.
           -- (* true *)
             destruct (split_n vs0 n) as [vs' vs''] eqn:Hsplit.
             remember (n_zeros ts) as zs eqn:?.
             apply <<hs, (s, (Build_frame_ctx vs'' m (Build_frame (rev vs' ++ zs) i) es0, nil) :: (fc, lcs) :: ccs', (nil, nil), Some (AI_basic (BI_block (Tf [::] t2s) es)))>> => /=.
             red_ctx_simpl => //.
             eapply r_label with (lh := LH_base (rev (FC_val fc)) (FC_post fc)) => /=; infer_hole.
             apply r_local.
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
           -- (* false *)
             by admit_rsc.
             (* apply RS''_error.
              by eapply invoke_func_native_error_n with
                (n := n) (t1s := t1s) (t2s := t2s) (i := i) (ts := ts) (es := es). *)
        * (* FC_func_host (Tf t1s t2s) cl' *)
           remember (length t1s) as n eqn:?.
           remember (length t2s) as m eqn:?.
           destruct (length vs0 >= n) eqn:Hlen.
           -- (* true *)
              destruct (split_n vs0 n) as [vs' vs''] eqn: Hsplit.
              destruct (host_application_impl hs s (Tf t1s t2s) cl' (rev vs')) as [hs' [[s' rves]|]] eqn:?.
              ++ (* (hs', Some (s', rves)) *)
                destruct rves as [rvs | ].
                ** apply <<hs', (s', (fc, lcs) :: ccs', (rev rvs ++ vs'', es0), None)>> => /=.
                   red_ctx_simpl => //.
                   eapply r_label with (lh := LH_base (rev (FC_val fc)) (FC_post fc)) => /=; infer_hole.
                   apply r_local.
                   red_ctx_simpl => //=.
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
                ** apply <<hs', (s', (fc, lcs) :: ccs', (vs'', es0), Some AI_trap)>> => /=.
                   red_ctx_simpl => //.
                   eapply r_label with (lh := LH_base (rev (FC_val fc)) (FC_post fc)) => /=; infer_hole.
                   apply r_local.
                   red_ctx_simpl => //=.
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
              ++ (* (hs', None) *)
                   apply <<hs', (s, (fc, lcs) :: ccs', (vs'', es0), Some AI_trap)>> => /=.
                   red_ctx_simpl => //.
                   eapply r_label with (lh := LH_base (rev (FC_val fc)) (FC_post fc)) => /=; infer_hole.
                   apply r_local.
                   red_ctx_simpl => //=.
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
           -- (* false *)
             by admit_rsc.
             (*
              apply RS''_error.
              by eapply invoke_func_host_error_n with
                (n := n) (t1s := t1s) (t2s := t2s) (cl' := cl').
              *)
      + (* None *)
        by admit_rsc.
        (* apply RS''_error. by apply invoke_host_error_ath. *)

        
    - (* AI_label ln les es *)
      by inversion Hvalid.

    * (* AI_local ln lf es *)
      by inversion Hvalid.
  }
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
