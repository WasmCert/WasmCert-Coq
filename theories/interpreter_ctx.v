(** Proof-carrying interpreter for Wasm, optimised for contexts **)

From Wasm Require Export common properties tactic typing_inversion contexts.
From Coq Require Import ZArith.BinInt Program.Equality.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export operations host.
Require Import BinNat NArith BinNums ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
  
Context `{ho: host}.

(* This assumption on host function applications is required to establish the interpreter correctness result in the corresponding case *)
Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value -> (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).

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

(* Try to resolve a reduction goal between ctx configs to the `reduce`
   relation by focusing on the innermost closure and attempting to choose
   the right frame for applying `r_label`. *)
Ltac resolve_reduce_ctx vs es :=
  try apply reduce_focus_id => //; try (eapply r_label with (lh := LH_base (rev vs) es) => /=; infer_hole).

(* An interpreter config needs to always include an outermost frame.
This is the part of the validity of the full cfg validity (valid_cfg_ctx). 
 *)
Definition valid_ccs_cfg (cfg: cfg_tuple_ctx) :=
  let '(s, ccs, sc, oe) := cfg in
  ccs <> nil.

(**
Results for the one-step interpreter.
Normal = Normal step
Value = Input is a list of val
Trap = Input is Trap
Invalid = Shape of input is invalid (should not occur for the result of
a decomposition)
Error = Input is ill-typed
 **)
Inductive run_step_ctx_result (hs: host_state) (cfg: cfg_tuple_ctx) (depth: N): Type :=
| RSC_normal hs' cfg' (depth': N):
  reduce_ctx hs hs' cfg cfg' ->
  valid_ccs_cfg cfg' ->
  run_step_ctx_result hs cfg depth
| RSC_value s f vs:
  ctx_to_cfg cfg = Some (s, (f, v_to_e_list vs)) ->
  run_step_ctx_result hs cfg depth
| RSC_trap s f:
  ctx_to_cfg cfg = Some (s, (f, [::AI_trap])) ->
  run_step_ctx_result hs cfg depth
| RSC_invalid :
  (valid_cfg_ctx cfg -> False) ->
  run_step_ctx_result hs cfg depth
| RSC_error:
  (forall ts, ctx_cfg_typing cfg ts -> False) ->
  run_step_ctx_result hs cfg depth
.

(** The usual start of a crash certification.
  Given a goal of a ctx interpreter result, apply the RSC_error constructor
  which requires proving that the input config is cannot be ctx_cfg-typed.
  Apply the ctx_config typing inversion lemma and other typing inversion 
  lemmas (the usual tactic for inverting e_typing premises) to extract and
  simplify information from the typing premise, in the hope of reaching
  a contradiction.
**)
Ltac resolve_invalid_typing :=
  apply RSC_error;
  let ts := fresh "ts" in
  let C := fresh "C" in
  let ret := fresh "ret" in
  let labs := fresh "labs" in
  let ts' := fresh "ts'" in
  let Hstype := fresh "Hstype" in
  let Hftype := fresh "Hftype" in
  let Hagree := fresh "Hagree" in
  let Hretcons := fresh "Hretcons" in
  let Hretnil := fresh "Hretnil" in
  let Htype := fresh "Htype" in
  let Hetype := fresh "Hetype" in
  let ts_pre := fresh "ts_pre" in
  let ts_post := fresh "ts_post" in
  let Hvstype := fresh "Hvstype" in
  move => ts Htype;
  apply ctx_cfg_inv in Htype as [C [ret [labs [ts' [Hstype [Hftype [Hagree [Hretcons [Hretnil Hetype]]]]]]]]];
  eapply sc_typing_args in Hetype as [ts3 [ts4 [Hvstype Hetype]]]; simpl in Hetype;
  invert_e_typing.

Notation "<< hs , cfg , d >>" := (@RSC_normal _ _ _ hs cfg d).

(* Tactic to get the outermost closure context from the validity condition *)
Ltac get_cc ccs :=
  let fc := fresh "fc" in 
  let lcs := fresh "lcs" in 
  let ccs' := fresh "ccs'" in 
  destruct ccs as [ | [fc lcs] ccs']; first by apply RSC_invalid => /=; unfold valid_ccs; move => [??].

(* Trying to resolve the goal by finding a contradiction by list sizes from the premises in the context. 
  Note that this destroys the original premises, so should only be used as a terminal most of time. *)
Ltac discriminate_size :=
  repeat match goal with
  | H: is_true (values_typing _ _ _) |- _ =>
    apply values_typing_size in H
  | H: Tf _ _ <ti: Tf _ _ |- _ =>
    let Hsize_add := fresh "Hsize_add" in
    let Hsize_bound1 := fresh "Hsize_bound1" in
    let Hsize_bound2 := fresh "Hsize_bound2" in
    specialize (instr_subtyping_size_exact H) as Hsize_add;
    apply instr_subtyping_size_bound in H as [Hsize_bound1 Hsize_bound2]; clear H
  | H: context C [length _] |- _ =>
    rewrite length_is_size in H
  | H: context C [size (rev _)] |- _ =>
    rewrite size_rev in H
  | H: context C [size (cat _ _)] |- _ =>
    rewrite size_cat in H
  | H: is_true (all2 _ _ _) |- _ =>
    apply all2_size in H
  | H: List.nth_error _ _ = Some _ |- _ =>
    apply nth_error_Some_length in H
  | H: List.nth_error _ _ = None |- _ =>
    apply List.nth_error_None in H
  | _ => unfold lookup_N in *; simplify_lists; simpl in *; subst; try by lias
    end.

Definition empty_label_ctx := Build_label_ctx nil 0 nil nil.

Opaque instr_subtyping.

(** Br j exits from j labels and targets the continuation of the next. **)
Definition run_ctx_br: forall hs s ccs sc j d,
  run_step_ctx_result hs (s, ccs, sc, Some (AI_basic (BI_br j))) d.
Proof.
  intros hs s ccs [vs es] j d.
  get_cc ccs.
  destruct (lookup_N lcs j) as [lab | ] eqn:Htar.
  - destruct lab as [lvs lk lces les].
    specialize (nth_error_Some_length Htar) as Hlablen; move/ltP in Hlablen.
    destruct (lk <= length vs) eqn:Hvslen.
    + apply <<hs, (s, ((fc, drop (S (N.to_nat j)) lcs) :: ccs'), (take lk vs ++ lvs, lces ++ les), None), d>> => //.
      apply reduce_focus => //=.
      rewrite - (cat_take_drop ((N.to_nat j).+1) lcs) drop_size_cat; last by rewrite size_takel; apply nth_error_Some_length in Htar; lias => //.
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
        rewrite add0n length_is_size size_takel; last by rewrite length_is_size in Hlablen; lias.
        by rewrite N2Nat.id. 
      }
      
    (* Not enough values *)
    + resolve_invalid_typing.
      destruct fc as [fvs fk [flocs fi] fes]; simpl in *.
      unfold frame_typing in Hftype; remove_bools_options; simpl in *.
      destruct Hftype as [ts0 [-> Hvt]].
      eapply all2_projection in Hagree; eauto.
      move/eqP in Hagree; simpl in Hagree; subst.
      by discriminate_size.
      
  (* Not enough labels *)
  - resolve_invalid_typing.
    by discriminate_size.
Defined.

(** Return exits from the innermost frame and all label contexts.
    This can be implemented by exitting from one closure context.
 **)
Definition run_ctx_return: forall hs s ccs sc d,
  run_step_ctx_result hs (s, ccs, sc, Some (AI_basic BI_return)) d.
Proof.  
  intros hs s ccs [vs es] d.
  get_cc ccs.
  (* Return needs an additional frame to execute; otherwise it returns in a type error. *)
  destruct ccs' as [| ccs' cc0] using last_ind.
  (* Error *)
  - by resolve_invalid_typing.
  - clear IHccs'.
    destruct fc as [lvs lk lf les].
    destruct (lk <= length vs) eqn:Hvslen.
    + apply <<hs, (s, rcons ccs' cc0, (take lk vs ++ lvs, les), None), N.sub d 1>> => //=; last by destruct ccs'.
      unfold reduce_ctx => /=.
      rewrite rev_cons rev_rcons rcons_cons.
      destruct cc0 as [[fvs0 fk0 ff0 fes0] lcs0].
      rewrite revK rev_rcons revK.
      apply (list_label_ctx_eval.(ctx_reduce)) => //=.
      apply (list_closure_ctx_eval.(ctx_reduce)) => //.
      resolve_reduce_ctx lvs les.
      apply r_simple; eapply rs_return.
      { by apply v_to_e_const. }
      { by rewrite v_to_e_length length_is_size size_rev size_takel. }
      { apply lh_ctx_fill_aux with (acc := (LH_base (rev (drop lk vs)) es)) (lcs := lcs) => /=.
        repeat rewrite catA => /=.
        rewrite v_to_e_cat rev_drop rev_take cat_take_drop.
        by repeat rewrite - catA.
      }
    (* Not enough values *)
    + resolve_invalid_typing.
      assert (length extr1 = lk) as <-; first by injection Hretcons; destruct ccs'.
      by discriminate_size.
Defined.

Definition run_ctx_invoke hs s ccs vs0 es0 a d:
    run_step_ctx_result hs (s, ccs, (vs0, es0), Some (AI_invoke a)) d.
Proof.
  get_cc ccs.
  destruct (lookup_N s.(s_funcs) a) as [cl|] eqn:?.
  (* Some cl *)
  - destruct cl as [[t1s t2s] i [tidx ts es] | [t1s t2s] cl'] eqn:?.
    (* FC_func_native i (Tf t1s t2s) ts es *)
    + remember (length t1s) as n eqn:?.
      remember (length t2s) as m eqn:?.
      destruct (length vs0 >= n) eqn:Hlen.
      (* true *)
      * destruct (split_n vs0 n) as [vs' vs''] eqn:Hsplit.
        destruct (default_vals ts) as [zs |] eqn:Hdefault.
        (* All types are defaultable as of Wasm 2.0. This potentially needs a 
           small change in 3.0 where non-defaultable types are introduced. In particular,
           the `default_vals` function needs to be made partial, and there should be
           a case split on the failure case due to an attempt on using the default values
           of non-defaultable types *)
        { apply <<hs, (s, (Build_frame_ctx vs'' m (Build_frame (rev vs' ++ zs) i) es0, nil) :: (fc, lcs) :: ccs', (nil, nil), Some (AI_label m nil (to_e_list es))), N.add d 1>> => //=.
          apply (@reduce_focus_pivot _ _ _ nil ([::(Build_frame_ctx vs'' m _ es0, nil)])) => //=.
          apply (list_label_ctx_eval.(ctx_reduce)) => //=.
          rewrite split_n_is_take_drop in Hsplit; injection Hsplit as <- <-.
          eapply r_label with (lh := LH_base (rev (drop n vs0)) es0) => /=; subst; infer_hole.
          2: { instantiate (1 := (v_to_e_list (rev (take (length t1s) vs0)) ++ [::AI_invoke a])) => /=.
               repeat rewrite catA.
               by rewrite v_to_e_cat -rev_cat cat_take_drop -catA.
          }
          eapply r_invoke_native; eauto.
          repeat rewrite length_is_size.
          repeat rewrite length_is_size in Hlen.
          by rewrite size_rev size_takel => //.
        }
        (* Not defaultable *)
        { resolve_invalid_typing.
          specialize (store_typing_func_lookup Hstype Heqo) as [ft [<- [_ Hfunctype]]].
          simpl in *.
          remove_bools_options.
          destruct f.
          destruct Hfunctype as [Heqtf [Hetype Hdefault']].
          by apply Hdefault'.
        }
      * (* not enough arguments *)
        resolve_invalid_typing.
        unfold ext_func_typing in Hconjr.
        remove_bools_options; simpl in *.
        by discriminate_size.
    + (* FC_func_host (Tf t1s t2s) cl' *)
      remember (length t1s) as n eqn:?.
      remember (length t2s) as m eqn:?.
      destruct (length vs0 >= n) eqn:Hlen.
      * (* true *)
        destruct (split_n vs0 n) as [vs' vs''] eqn: Hsplit.
        destruct (host_application_impl hs s (Tf t1s t2s) cl' (rev vs')) as [hs' [[s' rves]|]] eqn:?.
        (* (hs', Some (s', rves)) *)
        { destruct rves as [rvs | ].
          - apply <<hs', (s', (fc, lcs) :: ccs', (rev rvs ++ vs'', es0), None), d>> => //=.
            apply reduce_focus_id => //.
            rewrite split_n_is_take_drop in Hsplit.
            injection Hsplit as ??.
            eapply r_label with (lh := LH_base (rev vs'') es0) => /=; subst; infer_hole.
            2: { instantiate (1 := (v_to_e_list (rev (take (length t1s) vs0)) ++ [::AI_invoke a])).
                 by rewrite catA catA v_to_e_cat -rev_cat cat_take_drop -catA.
            }
            rewrite revK.
            unfold fmask0 => /=.
            fold (result_to_stack (result_values rvs)).
            (* host application correctness is used here *)
            eapply r_invoke_host_success; try by eauto.
            repeat rewrite length_is_size.
            by rewrite size_rev size_takel => //.
          - apply <<hs', (s', (fc, lcs) :: ccs', (vs'', es0), Some AI_trap), d>> => //=.
            apply reduce_focus_id => //.
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
            by rewrite size_rev size_takel => //. }
        (* (hs', None) *)
        { apply <<hs', (s, (fc, lcs) :: ccs', (vs'', es0), Some AI_trap), d>> => //=.
          apply reduce_focus_id => //.
          rewrite split_n_is_take_drop in Hsplit.
          injection Hsplit as ??.
          eapply r_label with (lh := LH_base (rev vs'') es0) => /=; subst; infer_hole.
          2: { instantiate (1 := (v_to_e_list (rev (take (length t1s) vs0)) ++ [::AI_invoke a])).
              by rewrite catA catA v_to_e_cat -rev_cat cat_take_drop -catA.
          }
          unfold fmask0 => /=.
          eapply r_invoke_host_diverge; eauto.
          repeat rewrite length_is_size.
          by rewrite size_rev size_takel => //. }
      * (* false *)
        resolve_invalid_typing.
        unfold ext_func_typing in Hconjr.
        remove_bools_options; simpl in *.
        by discriminate_size.
  - (* None *)
    resolve_invalid_typing.
    unfold ext_func_typing in Hconjr.
    by remove_bools_options; simpl in *.
Defined.

Ltac resolve_invalid_value :=
  repeat match goal with
  | Hvaltype : is_true (values_typing _ (rev (_ :: _)) _),
    Hsub: (Tf [::_] _ <ti: _) |- _ =>
      specialize (operand_subtyping1 Hvaltype Hsub) as Hopsub; clear Hsub; simpl in * => //=
  | Hvaltype : is_true (values_typing _ (rev (_ :: _ :: _)) _),
    Hsub: (Tf [::_; _] _ <ti: _) |- _ =>
      specialize (operand_subtyping2 Hvaltype Hsub) as Hopsub; clear Hsub; simpl in * => //=
  | Hvaltype : is_true (values_typing _ (rev (_ :: _ :: _ :: _)) _),
    Hsub: (Tf [::_; _; _] _ <ti: _) |- _ =>
      specialize (operand_subtyping3 Hvaltype Hsub) as Hopsub; clear Hsub; simpl in * => //=
  | Hvaltype : is_true (values_typing _ (rev (_ :: _)) _),
    Hsub: (Tf (_ ++ [::_]) _ <ti: _) |- _ =>
      specialize (operand_subtyping_suffix1 Hvaltype Hsub) as Hopsub; clear Hsub; simpl in * => //=
  | Hvaltype : is_true (values_typing _ (rev (_ :: _)) _),
    Hsub: (Tf (_ ++ _ ++ [::_]) _ <ti: _) |- _ =>
      rewrite catA in Hsub; specialize (operand_subtyping_suffix1 Hvaltype Hsub) as Hopsub; clear Hsub; simpl in * => //=
  | Hvaltype : is_true (value_typing _ (VAL_ref _) (T_num _)) |- _ =>
      apply value_typing_ref_impl in Hvaltype as [? Hteq] => //
  | Hvaltype : is_true (value_typing _ (VAL_num _) (T_num _)) |- _ =>
      unfold value_typing in Hvaltype; simpl in Hvaltype; remove_bools_options => //
  | Hvaltype : is_true (value_typing _ (VAL_ref _) (T_vec _)) |- _ =>
      apply value_typing_ref_impl in Hvaltype as [? Hteq] => //
  | _ => simpl in *; remove_bools_options; subst => //
end.

Ltac discriminate_value_type :=
  resolve_invalid_typing; resolve_invalid_value.

(* Directly destructs the top value of stack and automatically resolve the ill-typed cases. *)
Ltac assert_value_num v :=
  destruct v as [v| |]; [ | by discriminate_value_type | by discriminate_value_type].

Ltac assert_value_vec v :=
  destruct v as [ |v|]; [ by discriminate_value_type | | by discriminate_value_type].

Ltac assert_value_ref v :=
  destruct v as [ | |v]; [ by discriminate_value_type | by discriminate_value_type |].

Ltac assert_i32 v :=
  assert_value_num v; destruct v as [v | | |]; [ | by discriminate_value_type | by discriminate_value_type | by discriminate_value_type].

Ltac no_args :=
  resolve_invalid_typing; discriminate_size.

Ltac unfold_frame_type Hftype :=
  unfold frame_typing in Hftype; remove_bools_options; simpl in *;
  let ts0 := fresh "ts0" in
  let Hvaltype := fresh "Hvaltype" in
  destruct Hftype as [ts0 [-> Hvaltype]]; simpl in *.

Notation "$u32oz v" := (Wasm_int.int_of_Z i32m v) (at level 90).
Notation "$zou32 v" := (Wasm_int.Z_of_uint i32m v) (at level 90).
Notation "$nou32 v" := (Wasm_int.N_of_uint i32m v) (at level 90).

(* One step of execution; does not perform the context update in the end to shift to the new instruction nor the validity check. *)
Definition run_one_step_ctx (hs: host_state) (cfg: cfg_tuple_ctx) (d: N): run_step_ctx_result hs cfg d.
Proof.
  destruct cfg as [[[s ccs] [vs0 es0]] oe].
  get_cc ccs.
  destruct oe as [e | ]; last first.
  (* Empty hole -- exiting from contexts *)
  {
    destruct es0 as [ | ??]; last by apply RSC_invalid => /=; move => [??].
    { destruct lcs as [ | lc lcs'].
      {
        (* Exiting from frame -- we need to check if this is the last frame first *)
        destruct ccs' as [| cc ccs'].
        (* No more frames -- terminate *)
        { apply (@RSC_value _ _ _ s fc.(FC_frame) (rev vs0)) => /=.
          by destruct fc; rewrite cats0.
        }
        (* At least a frame left -- in this case, determine if the length of values match the arity *)
        {
          destruct fc as [lvs lk lf les].
          destruct (length vs0 == lk) eqn:Hlen; move/eqP in Hlen.
          {
            (* Exiting the frame now. Note that this implementation does not 
               attempt to directly construct the next canonical cfg (les can be non-empty) *)
            apply <<hs, (s, cc :: ccs', (vs0 ++ lvs, les), None), N.sub d 1>> => //=.
            apply (@reduce_focus_pivot _ _ _ [:: (Build_frame_ctx lvs lk lf les, nil)] nil) => //=.
            apply (list_label_ctx_eval.(ctx_reduce)) => //=.
            repeat rewrite cats0.
            resolve_reduce_ctx lvs les.
            by apply r_simple, rs_local_const; [ by apply v_to_e_const | by rewrite length_is_size v_to_e_size size_rev ].
          }
          {
            apply RSC_error; move => ts Hetype.
            apply ctx_cfg_inv_lcs in Hetype as [C [ret [ts2 [Hstype [Hftype [Hretcons [_ Hetype]]]]]]]; simpl in *.
            specialize (Hretcons isT) as [-> Harity]; simpl in Harity; injection Harity as <-.
            rewrite cats0 in Hetype.
            unfold vs_to_es in Hetype.
            invert_e_typing.
            by discriminate_size.
          }
        }
      }
      (* Exitting a label *)
      (* It is futile to try to push the next instruction e from lvs into the hole,
         as that might be a value anyway. Instead, the entire context reformation is done in a separate function *)
      { destruct lc as [lvs lk lces les].
        apply <<hs, (s, (fc, lcs') :: ccs', (vs0 ++ lvs, les), None), d>> => //=.
        apply reduce_focus => //=.
        apply (list_label_ctx_eval.(ctx_reduce)) => //=.
        repeat rewrite cats0.
        unfold fmask0, label_ctx_fill => /=.
        resolve_reduce_ctx lvs les.
        apply r_simple, rs_label_const; by apply v_to_e_const.
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
      (* BI_unop_vec _ *) op |
      (* BI_binop_vec _ *) op |
      (* BI_ternop_vec _ *) op |
      (* BI_test_vec _ *) tv |
      (* BI_shift_vec _ *) sv |
      (* BI_splat_vec _ *) shape |
      (* BI_extract_vec shape_vec [Some sx | None] laneidx *) shape sx x |
      (* BI_replace_vec shape_vec laneidx *) shape x |
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
      (* BI_load t [Some (tp, sx)|None] marg *) t ops marg |
      (* BI_load_vec lvarg marg *) lvarg marg |
      (* BI_load_vec_lane width marg laneidx *) width marg x |
      (* BI_store t [Some tp|None] marg *) t op marg |
      (* BI_store_vec_lane width marg laneidx *) width marg x |
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
      (* AI_frame ln lf es *) ln lf es ].

    (* AI_basic (BI_const _) *)
    (* This along with other value instructions are invalid, as it doesn't respect
the condition that all values should live in the operand stack. *)
    - apply RSC_invalid => /=; by move => [??].

    (* AI_basic (BI_unop t op) *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_value_num v.
      (* v :: ves' *)
      (* typechecking the operation against the operands *)
      destruct (unop_typecheck v t op) eqn:Htc.
      + apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num (app_unop op v) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_unop.
      (* Ill-typed *)
      + resolve_invalid_typing; resolve_invalid_value.
        apply num_subtyping in H; injection H as ->.
        unfold unop_typecheck in Htc.
        by rewrite Hconjr eq_refl in Htc.

    (* AI_basic (BI_binop t op) *)
    - destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      assert_value_num v2.
      assert_value_num v1.
      (* [:: v2, v1 & ves'] *)
      (* typechecking the operation against the operands *)
      destruct (binop_typecheck v1 v2 t op) eqn:Htc.
      { destruct (app_binop op v1 v2) as [v|] eqn:?.
        (* Some v *)
        + apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num v :: vs0, es0), None), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by apply r_simple, rs_binop_success.
        (* None *)
        + apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by apply r_simple, rs_binop_failure.
      }
      (* Ill-typed *)
      {
        resolve_invalid_typing; resolve_invalid_value.
        apply num_subtyping in H; injection H as ->.
        apply num_subtyping in H0; injection H0 as Hteq.
        unfold binop_typecheck in Htc.
        by rewrite Hconjr Hteq eq_refl in Htc.
      }

    (* AI_basic (BI_testop t testop) *)
    - destruct vs0 as [| v vs0]; first by no_args.
      (* v :: ves' *)
      assert_value_num v.
      destruct t as [| | |].
      3,4: by resolve_invalid_typing.
      (* i32 *)
      + destruct v as [c| | |].
        2,3,4: by resolve_invalid_typing; resolve_invalid_value. 
        apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num (VAL_int32 (wasm_bool (app_testop_i i32m testop c))) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_testop_i32.
      (* i64 *)
      + destruct v as [|c | |].
        1,3,4: by resolve_invalid_typing; resolve_invalid_value.
        apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num (VAL_int32 (wasm_bool (app_testop_i i64m testop c))) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_testop_i64.

    (* AI_basic (BI_relop t op) *)
    - destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      assert_value_num v2.
      assert_value_num v1.
      (* [:: v2, v1 & ves'] *)
      (* typechecking the operation against the operands *)
      destruct (relop_typecheck v1 v2 t op) eqn:Htc.
      { apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num (VAL_int32 (wasm_bool (@app_relop op v1 v2))) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_relop.
      }
      (* Ill-typed *)
      {
        resolve_invalid_typing; resolve_invalid_value.
        apply num_subtyping in H; injection H as ->.
        apply num_subtyping in H0; injection H0 as Hteq.
        unfold relop_typecheck in Htc.
        by rewrite Hconjr Hteq eq_refl in Htc.
      }

    (* AI_basic (BI_cvtop t2 CVO_convert t1 sx) *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_value_num v.
      (* v :: ves' *)
      destruct (typeof_num v == t1) eqn:Ht1; move/eqP in Ht1.
      (* true *)
      + destruct (cvtop_valid t2 cvtop t1 sx) eqn:Hcvtvalid.
        (* true *)
        * destruct (eval_cvt t2 cvtop sx v) as [v'|] eqn:Heval.
          (* Some v' *)
          { apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num v' :: vs0, es0), None), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by apply r_simple, rs_convert_success.
          }
          (* None *)
          { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by apply r_simple, rs_convert_failure.
          }
        (* false *)
        * by resolve_invalid_typing; lias.
      (* false *)
      + discriminate_value_type.
        apply num_subtyping in H; by inversion H; subst.

    (* AI_basic BI_const_vec v *)
    - apply RSC_invalid => /=; by move => [??].
      
    (* AI_basic BI_unop_vec op *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_value_vec v.
      apply <<hs, (s, (fc, lcs) :: ccs', (VAL_vec (app_unop_vec op v) :: vs0, es0), None), d>> => //.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_unop_vec.
      
    (* AI_basic BI_binop_vec op *)
    - destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      assert_value_vec v1.
      assert_value_vec v2.
      apply <<hs, (s, (fc,lcs) :: ccs', (VAL_vec (app_binop_vec op v1 v2) :: vs0, es0), None), d>> => //.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_binop_vec.
      
    (* AI_basic BI_ternop_vec op *)
    - destruct vs0 as [|v3 [|v2 [|v1 vs0]]]; try by no_args.
      assert_value_vec v1.
      assert_value_vec v2.
      assert_value_vec v3.
      apply <<hs, (s, (fc,lcs) :: ccs', (VAL_vec (app_ternop_vec op v1 v2 v3) :: vs0, es0), None), d>> => //.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_ternop_vec.
      
    (* AI_basic BI_test_vec tv *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_value_vec v.
      apply <<hs, (s, (fc,lcs) :: ccs', (VAL_num (VAL_int32 (wasm_bool (app_test_vec tv v))) :: vs0, es0), None), d>> => //.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_test_vec.
      
    (* AI_basic BI_shift_vec sv *)
    - destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      assert_value_vec v1.
      assert_i32 v2.
      apply <<hs, (s, (fc,lcs) :: ccs', (VAL_vec (app_shift_vec sv v1 v2) :: vs0, es0), None), d>> => //.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_shift_vec.
      
    (* AI_basic BI_splat_vec shape *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_value_num v.
      apply <<hs, (s, (fc,lcs) :: ccs', (VAL_vec (app_splat_vec shape v) :: vs0, es0), None), d>> => //.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_splat_vec.
      
    (* AI_basic (BI_extract_vec shape sx x) *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_value_vec v.
      destruct (N.ltb x (shape_dim shape)) eqn:Hlanebound.
      (* in bound *)
      + apply <<hs, (s, (fc,lcs) :: ccs', (VAL_num (app_extract_vec shape sx x v) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_extract_vec.
      (* out of bound *)
      + by resolve_invalid_typing; lias.
        
    (* AI_basic (BI_replace_vec shape x) *)
    - destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      assert_value_vec v1.
      assert_value_num v2.
      destruct (N.ltb x (shape_dim shape)) eqn:Hlanebound.
      (* in bound *)
      + apply <<hs, (s, (fc,lcs) :: ccs', (VAL_vec (app_replace_vec shape x v1 v2) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_replace_vec.
      (* out of bound *)
      + by resolve_invalid_typing; lias.
      
    (* AI_basic BI_ref_null t *)
    - apply RSC_invalid => /=; by move => [??].

    (* AI_basic BI_ref_is_null *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_value_ref v.
      destruct v as [ v | v | v ].
      (* ref_null *)
      + apply <<hs, (s, (fc, lcs) :: ccs', ((VAL_num (VAL_int32 Wasm_int.Int32.one)) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple, rs_ref_is_null_true.
      (* ref_func *)
      + apply <<hs, (s, (fc, lcs) :: ccs', ((VAL_num (VAL_int32 Wasm_int.Int32.zero)) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        replace (AI_ref v) with ($V (VAL_ref (VAL_ref_func v))) => //.
        by apply r_simple, rs_ref_is_null_false.
      (* ref_extern *)
      + apply <<hs, (s, (fc, lcs) :: ccs', ((VAL_num (VAL_int32 Wasm_int.Int32.zero)) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        replace (AI_ref_extern v) with ($V (VAL_ref (VAL_ref_extern v))) => //.
        by apply r_simple, rs_ref_is_null_false.

    (* AI_basic (BI_ref_func x) *)
    - destruct (lookup_N (inst_funcs (f_inst fc.(FC_frame))) x) as [addr | ] eqn:Hnth.
      + apply <<hs, (s, (fc, lcs) :: ccs', ((VAL_ref (VAL_ref_func addr)) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_ref_func.
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        eapply inst_typing_func_lookup_inv in Hconjl0 as [f [Hext Hnthf]]; eauto.
        by rewrite Hnthf in Hnth.
      
    (* AI_basic BI_drop *)
    - destruct vs0 as [ | v vs0]; first by no_args.
      (* v :: vs0 *)
      apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None), d>> => //=.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_drop.
      
    (* AI_basic BI_select *)
    - destruct vs0 as [|v3 [|v2 [|v1 vs0]]]; try by no_args.

      (* v3 has to be i32, but the other two can be of any numeric type. Note that neitehr the spec nor the opsem checks for this during runtime *)
      assert_i32 v3.
      (* VAL_int32 c *)
      destruct (v3 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
      (* true *)
      + apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some ($V v2)), d>> => //=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_select_false.
      + (* false *)
        apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some ($V v1)), d>> => //=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_select_true.
        
    (* AI_basic (BI_local_get j) *)
    - destruct (lookup_N fc.(FC_frame).(f_locs) j) as [vs_at_j|] eqn:?.
      (* Some vs_at_j *)
      + apply <<hs, (s, (fc, lcs) :: ccs', (vs_at_j :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by eapply r_local_get; subst.
      (* None *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        erewrite inst_t_context_local_empty in Hconjr; eauto.
        by discriminate_size.
        
    (* AI_basic (BI_local_set j) *)
    - destruct vs0 as [|v vs0]; first by no_args.
      (* v :: ves' *)
      destruct (N.ltb j (N.of_nat (length fc.(FC_frame).(f_locs)))) eqn:Hlen.
      (* true *)
      + apply <<hs, (s, ((Build_frame_ctx (fc.(FC_val)) fc.(FC_arity) (Build_frame (set_nth v fc.(FC_frame).(f_locs) (N.to_nat j) v) fc.(FC_frame).(f_inst)) fc.(FC_post)), lcs) :: ccs', (vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        eapply r_local_set with (vd := v) => //=; by lias.
      (* false *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        erewrite inst_t_context_local_empty in Hconjr; eauto.
        move/N.ltb_spec0 in Hlen.
        by discriminate_size.

    (* AI_basic (BI_local_tee j) *)
    - destruct vs0 as [|v vs0]; first by no_args.
      (* v :: ves' *)
      apply <<hs, (s, (fc, lcs) :: ccs', (v :: v :: vs0, es0), Some (AI_basic (BI_local_set j))), d>> => //=.
      resolve_reduce_ctx vs0 es0.
      by eapply r_simple, rs_local_tee.

    (* AI_basic (BI_global_get j) *)
    - destruct (sglob_val s fc.(FC_frame).(f_inst) j) as [v|] eqn:Hsglob.
      (* Some xx *)
      + apply <<hs, (s, (fc, lcs) :: ccs', (v :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_global_get.
      (* None *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        * by inst_typing_lookup; remove_bools_options.
        * eapply inst_typing_global_lookup_inv in Hoption as [? [? Hnthg]]; eauto.
          by simplify_multieq.

    (* AI_basic (BI_global_set j) *)
    - destruct vs0 as [|v vs0]; first by no_args.
      (* v :: ves' *)
      destruct (supdate_glob s fc.(FC_frame).(f_inst) j v) as [s'|] eqn:Hsupdate.
      (* Some s' *)
      + apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by eapply r_global_set; subst.
      (* None *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        * by inst_typing_lookup; remove_bools_options.
        * eapply inst_typing_global_lookup_inv in Hconjl0 as [? [? Hnthg]]; eauto.
          by simplify_multieq.

    (* AI_basic (BI_table_get x) *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_i32 v.
      destruct (stab_elem s fc.(FC_frame).(f_inst) x ($nou32 v)) as [tabv|] eqn:Hstab.
      (* Some xx *)
      + apply <<hs, (s, (fc, lcs) :: ccs', ((VAL_ref tabv) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_table_get_success.
      (* None *)
      (* Note that the stab_elem specification in the opsem matches the spec for typed expressions only -- it produces traps in some untyped scenarios which is undefined in spec. But that is not a problem anyway for now. Maybe this should be changed in the future. *)
      + apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_table_get_failure.

    (* AI_basic (BI_table_set x) *)
    - destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      (* v2 needs to be a ref and v1 needs to be a i32 num *)
      assert_value_ref v2.
      assert_i32 v1.
      destruct (stab_update s fc.(FC_frame).(f_inst) x ($nou32 v1) v2) as [s'|] eqn:Hsupdate.
      (* Some xx *)
      + apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_table_set_success.
      (* None *)
      + apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_table_set_failure.
        
    (* AI_basic (BI_table_size x) *)
    - destruct (stab s fc.(FC_frame).(f_inst) x) as [tab|] eqn:Hstab.
      (* Some xx *)
      + apply <<hs, (s, (fc, lcs) :: ccs', ((VAL_num (VAL_int32 ($u32oz (Z.of_nat (tab_size tab))))) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by eapply r_table_size; eauto.
      (* None *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        * inst_typing_lookup.
          by rewrite Hstab in Hexttabt.
        * eapply inst_typing_table_lookup_inv in Hconjr as [? [? Hnthtab]]; eauto.
          by simplify_multieq.

    (* AI_basic (BI_table_grow x) *)
    - destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      (* Takes an i32 and a reference value *)
      assert_i32 v2.
      assert_value_ref v1.
      destruct (stab_grow s fc.(FC_frame).(f_inst) x ($nou32 v2) v1) as [[s' sz]|] eqn:Hstabgrow.
      + apply <<hs, (s', (fc, lcs) :: ccs', ((VAL_num (VAL_int32 ($u32oz (Z.of_nat sz)))) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by eapply r_table_grow_success; eauto.
      (* None *)
      + apply <<hs, (s, (fc, lcs) :: ccs', ((VAL_num (VAL_int32 int32_minus_one)) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by eapply r_table_grow_failure; eauto.

    (* AI_basic (BI_table_fill x) *)
    - destruct vs0 as [|v3 [|v2 [|v1 vs0]]]; try by no_args.
      (* Takes i32; ref; i32 *)
      assert_i32 v3.
      assert_value_ref v2.
      assert_i32 v1.
      destruct (stab s fc.(FC_frame).(f_inst) x) as [tab|] eqn:Hstab.
      (* Some xx *)
      + destruct (Z.ltb (Z.of_nat (tab_size tab)) (($zou32 v1) + ($zou32 v3))) eqn:Hbound; move/Z.ltb_spec0 in Hbound.
        (* Out of bound *)
        * apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by eapply r_table_fill_bound; eauto; lias.
        * destruct (($zou32 v3) == 0)%Z eqn:Hn0; move/eqP in Hn0; simpl in *; subst.
          (* Return *)
          { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_table_fill_return; eauto; simpl in *; lias.
          }
          (* Step *)
          { apply <<hs, (s, (fc, lcs) :: ccs',
                          ((VAL_ref v2) :: (VAL_num (VAL_int32 v1)) :: vs0,
                            [::($VN (VAL_int32 ($u32oz (Z.add ($zou32 v1) 1)))); ($V (VAL_ref v2)); ($VN (VAL_int32 ($u32oz (Z.sub ($zou32 v3) 1)))); (AI_basic (BI_table_fill x))] ++ es0),
                          Some (AI_basic (BI_table_set x))), d>> => //.
            resolve_reduce_ctx vs0 es0; simpl in *.
            by eapply r_table_fill_step; eauto; lias.
          }
      (* None *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        * inst_typing_lookup.
          by rewrite Hstab in Hexttabt.
        * eapply inst_typing_table_lookup_inv in Hconjl0 as [? [? Hnthtab]]; eauto.
          by simplify_multieq.
          
    (* AI_basic (BI_table_copy x y) *)
    - destruct vs0 as [|n [|src [|dst vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_i32 n.
      assert_i32 src.
      assert_i32 dst.
      destruct (stab s fc.(FC_frame).(f_inst) x) as [tabx|] eqn:Hstabx.
      (* Some xx *)
      + destruct (stab s fc.(FC_frame).(f_inst) y) as [taby|] eqn:Hstaby.
        (* Some xx *)
        * destruct (Z.ltb (Z.of_nat (tab_size taby)) (($zou32 src) + ($zou32 n))) eqn:Hboundy; move/Z.ltb_spec0 in Hboundy.
          (* taby Out of bound *)
          { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_table_copy_bound; eauto; lias.
          }
          destruct (Z.ltb (Z.of_nat (tab_size tabx)) (($zou32 dst) + ($zou32 n))) eqn:Hboundx; move/Z.ltb_spec0 in Hboundx.
          (* tabx Out of bound *)
          { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_table_copy_bound; eauto; lias.
          }
          (* In bound for both tables *)
          { destruct (($zou32 n) == 0)%Z eqn:Hn0; move/eqP in Hn0; simpl in *; subst.
            (* Return *)
            { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None), d>> => //.
              resolve_reduce_ctx vs0 es0.
              by eapply r_table_copy_return; eauto; simpl in *; lias.
            }
            destruct (Z.leb ($zou32 dst) ($zou32 src)) eqn:Hdir; move/Z.leb_spec0 in Hdir.
            (* copy -- forward *)
            { apply <<hs, (s, (fc, lcs) :: ccs',
                            ((VAL_num (VAL_int32 src)) :: (VAL_num (VAL_int32 dst)) :: vs0,
                              [::(AI_basic (BI_table_set x)); $VN (VAL_int32 ($u32oz (Z.add ($zou32 dst) 1))); $VN (VAL_int32 ($u32oz (Z.add ($zou32 src) 1))); $VN (VAL_int32 ($u32oz (Z.sub ($zou32 n) 1))); AI_basic (BI_table_copy x y)] ++ es0),
                            Some (AI_basic (BI_table_get y))), d>> => //.
              resolve_reduce_ctx vs0 es0.
              by eapply r_table_copy_forward; eauto; simpl in *; lias.
            }
            (* copy -- backward *)
            { apply <<hs, (s, (fc, lcs) :: ccs',
                            ((VAL_num (VAL_int32 ($u32oz (Z.sub (Z.add ($zou32 src) ($zou32 n)) 1)))) ::
                            (VAL_num (VAL_int32 ($u32oz (Z.sub (Z.add ($zou32 dst) ($zou32 n)) 1)))) ::
                            vs0,
                              [::(AI_basic (BI_table_set x)); $VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 ($u32oz (Z.sub ($zou32 n) 1))); AI_basic (BI_table_copy x y)] ++ es0),
                            Some (AI_basic (BI_table_get y))), d>> => //.
              resolve_reduce_ctx vs0 es0.
              eapply r_table_copy_backward; eauto; simpl in *; try by lias.
            }
          }

        (* staby = None *)
        * resolve_invalid_typing.
          unfold_frame_type Hftype.
          unfold_store_operations.
          {  inst_typing_lookup.
             by rewrite Hstaby in Hexttabt.
          }
          { eapply inst_typing_table_lookup_inv in Hconjl2 as [? [? Hnthtab]]; eauto.
            by simplify_multieq.
          }
          
      (* stabx = None *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        {  inst_typing_lookup.
           by rewrite Hstabx in Hexttabt.
        }
        { eapply inst_typing_table_lookup_inv in Hconjl0 as [? [? Hnthtab]]; eauto.
          by simplify_multieq.
        }
        
    (* AI_basic (BI_table_init x y) *)
    - destruct vs0 as [|n [|src [|dst vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_i32 n.
      assert_i32 src.
      assert_i32 dst.
      destruct (stab s fc.(FC_frame).(f_inst) x) as [tab|] eqn:Hstab.
      (* Some xx *)
      + destruct (selem s fc.(FC_frame).(f_inst) y) as [elem|] eqn:Hselem.
        (* Some xx *)
        * destruct (Z.ltb (Z.of_nat (elem_size elem)) (($zou32 src) + ($zou32 n))) eqn:Hboundy; move/Z.ltb_spec0 in Hboundy.
          (* elem Out of bound *)
          { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_table_init_bound; eauto; lias.
          }
          destruct (Z.ltb (Z.of_nat (tab_size tab)) (($zou32 dst) + ($zou32 n))) eqn:Hboundx; move/Z.ltb_spec0 in Hboundx.
          (* tab Out of bound *)
          { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_table_init_bound; eauto; lias.
          }
          (* In bound for both table and elem *)
          { destruct (($zou32 n) == 0)%Z eqn:Hn0; move/eqP in Hn0; simpl in *; subst.
            (* Return *)
            { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None), d>> => //.
              resolve_reduce_ctx vs0 es0.
              by eapply r_table_init_return; eauto; simpl in *; lias.
            }
            (* Step -- but need to lookup first *)
            { destruct (lookup_N elem.(eleminst_elem) ($nou32 src)) as [v | ] eqn:Hnthelem.
              (* Step *)
              { apply <<hs, (s, (fc, lcs) :: ccs',
                              ((VAL_ref v) :: (VAL_num (VAL_int32 dst)) :: vs0,
                                [::$VN (VAL_int32 ($u32oz (Z.add ($zou32 dst) 1)));
                                 $VN (VAL_int32 ($u32oz (Z.add ($zou32 src) 1)));
                                 $VN (VAL_int32 ($u32oz (Z.sub ($zou32 n) 1)));
                                 AI_basic (BI_table_init x y)
                                ] ++ es0),
                              Some (AI_basic (BI_table_set x))), d>> => //.
                resolve_reduce_ctx vs0 es0.
                by eapply r_table_init_step; eauto; simpl in *; lias.
              }
              (* lookup oob *)
              { resolve_invalid_typing.
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

        (* selem = None *)
        * resolve_invalid_typing.
          unfold_frame_type Hftype.
          unfold_store_operations; eapply inst_typing_elem_lookup_inv in Hconjr as [? [? [? [??]]]]; eauto; by simplify_multieq.
          
      (* stab = None *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        {  inst_typing_lookup.
           by rewrite Hstab in Hexttabt.
        }
        { eapply inst_typing_table_lookup_inv in Hconjl0 as [? [??]]; eauto.
          by simplify_multieq.
        }
        
    (* AI_basic BI_elem_drop x *)
    - destruct (selem_drop s fc.(FC_frame).(f_inst) x) as [s'|] eqn:Hs'.
      + apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_elem_drop.
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        { eapply inst_typing_elem_lookup_inv in Hconjr as [? [? [? [? ?]]]]; eauto.
          by simplify_multieq.
        }
        { eapply inst_typing_elem_lookup_inv in Hconjr as [? [? [? [? ?]]]]; eauto.
          by simplify_multieq.
        }

    (* AI_basic (BI_load t ops (Some (tp, sx)) marg) *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_i32 v.
      (* VAL_int32 v :: ves' *)
      destruct (smem s fc.(FC_frame).(f_inst)) as [mem_s_j|] eqn:?.
      (* Some mem_s_j *)
      { destruct ops as [[tp sx] | ].
        (* Some (tp, sx) *)
        - destruct (load_packed sx (mem_s_j) ($nou32 v) marg.(memarg_offset) (tp_length tp) (tnum_length t)) as [bs|] eqn:Hload.
          (* Some bs *)
          + apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num (wasm_deserialise bs t) :: vs0, es0), None), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_load_packed_success; subst; eauto.
          (* None *)
          + apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_load_packed_failure; subst; eauto.
        - destruct (load (mem_s_j) ($nou32 v) marg.(memarg_offset) (tnum_length t)) as [bs|] eqn:Hload.
          (* Some bs *)
          + apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num (wasm_deserialise bs t) :: vs0, es0), None), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_load_success; subst; eauto.
          (* None *)
          + apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_load_failure; subst; eauto.
      }
      (* None *)
      { resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        { inst_typing_lookup; by remove_bools_options. }
        { eapply inst_typing_mem_lookup_inv in Hconjl0 as [? [??]]; eauto.
          by simplify_multieq.
        }
      }

    (* AI_basic (BI_load_vec lvarg marg) *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_i32 v.
      (* VAL_int32 v :: ves' *)
      destruct (smem s fc.(FC_frame).(f_inst)) as [mem_s_j|] eqn:?.
      (* Some mem_s_j *)
      { destruct (load_vec mem_s_j ($nou32 v) lvarg marg) as [v' | ] eqn:Hload_vec.
        - apply <<hs, (s, (fc, lcs) :: ccs', (VAL_vec v' :: vs0, es0), None), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by eapply r_load_vec_success; subst; eauto.
        - apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by eapply r_load_vec_failure; subst; eauto.
      }
      (* None *)
      { resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        { inst_typing_lookup; by remove_bools_options. }
        { eapply inst_typing_mem_lookup_inv in Hconjl0 as [? [??]]; eauto.
          by simplify_multieq.
        }
      }

    (* AI_basic (BI_load_vec_lane width marg x) *)
    - destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      assert_i32 v1.
      assert_value_vec v2.
      (* VAL_int32 v :: ves' *)
      destruct (smem s fc.(FC_frame).(f_inst)) as [mem_s_j|] eqn:?.
      (* Some mem_s_j *)
      { destruct (load_vec_lane mem_s_j ($nou32 v1) v2 width marg x) as [v' | ] eqn:Hload_vec_lane.
        - apply <<hs, (s, (fc, lcs) :: ccs', (VAL_vec v' :: vs0, es0), None), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by eapply r_load_vec_lane_success; subst; eauto.
        - apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by eapply r_load_vec_lane_failure; subst; eauto.
      }
      (* None *)
      { resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        { inst_typing_lookup; by remove_bools_options. }
        { eapply inst_typing_mem_lookup_inv in Hconjl0 as [? [??]]; eauto.
          by simplify_multieq.
        }
      }

    (* AI_basic (BI_store t (Some tp) a off) *)
    - destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      assert_i32 v1.
      assert_value_num v2.
      destruct (typeof_num v2 == t) eqn:Heq; move/eqP in Heq; last by discriminate_value_type; apply num_subtyping in H; inversion H; subst.
      destruct op as [tp | ].
      (* packed *)
      + destruct (smem_store_packed s fc.(FC_frame).(f_inst) ($nou32 v1) marg.(memarg_offset) v2 tp) as [s' | ] eqn:Hsmem.
        * apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by eapply r_store_packed_success; subst; eauto.
        (* None *)
        * apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by eapply r_store_packed_failure; subst; eauto.
      (* None *)
      + destruct (smem_store s fc.(FC_frame).(f_inst) ($nou32 v1) marg.(memarg_offset) v2 t) as [s' | ] eqn:Hsmem.
        * apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by eapply r_store_success; subst; eauto.
        (* None *)
        * apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by eapply r_store_failure; subst; eauto.
          
    (* AI_basic (BI_store_vec_lane width marg x) *)
    - destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      assert_i32 v1.
      assert_value_vec v2.
      destruct (smem_store_vec_lane s fc.(FC_frame).(f_inst) ($nou32 v1) v2 width marg x) as [s' | ] eqn:Hstore_vec_lane.
      - apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by eapply r_store_vec_lane_success; subst; eauto.
      - apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by eapply r_store_vec_lane_failure; subst; eauto.
      
    (* AI_basic BI_memory_size *)
    - destruct (smem s fc.(FC_frame).(f_inst)) as [s_mem_s_j|] eqn:?.
      (* Some j *)
      + apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num (VAL_int32 ($u32oz (Z.of_N (mem_size (s_mem_s_j))))) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by subst; eapply r_memory_size; eauto.
      (* None *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        { eapply inst_typing_mem_lookup_inv in Hconjr as [? [Hextmt ?]]; eauto.
          unfold ext_mem_typing in Hextmt; remove_bools_options.
          by simplify_multieq.
        }
        { eapply inst_typing_mem_lookup_inv in Hconjr as [? [??]]; eauto.
          by simplify_multieq.
        }

    (* AI_basic BI_memory_grow *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_i32 v.
      destruct (smem_grow s fc.(FC_frame).(f_inst) ($nou32 v)) as [[s' sz] | ] eqn:Hsmem.
      (* Some mem'' *)
      + apply <<hs, (s', (fc, lcs) :: ccs', (VAL_num (VAL_int32 ($u32oz (Z.of_N sz))) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by subst; eapply r_memory_grow_success; eauto.
      (* None *)
      + apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num (VAL_int32 int32_minus_one) :: vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by subst; eapply r_memory_grow_failure; eauto.

    (* AI_basic BI_memory_fill *)
    - destruct vs0 as [|v3 [|v2 [|v1 vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_i32 v3.
      assert_i32 v2.
      assert_i32 v1.
      destruct (smem s fc.(FC_frame).(f_inst)) as [mem|] eqn:Hsmem.
      (* Some *)
      + destruct (Z.ltb (Z.of_N (mem_length mem)) (Z.add ($zou32 v1) ($zou32 v3))) eqn:Hlt; move/Z.ltb_spec0 in Hlt.
        (* true *)
        * apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by eapply r_memory_fill_bound; eauto; lias.
        (* false *)
        * destruct (Z.eqb ($zou32 v3) Z0) eqn:Heq0; move/Z.eqb_spec in Heq0.
          (* Return *)
          { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_memory_fill_return; eauto; lias.
          }
          (* Step *)
          { apply <<hs, (s, (fc, lcs) :: ccs',
                          ((VAL_num (VAL_int32 v2)) :: (VAL_num (VAL_int32 v1)) :: vs0,
                            [::$VN (VAL_int32 ($u32oz (Z.add ($zou32 v1) 1%Z)));
                             $VN (VAL_int32 v2);
                             $VN (VAL_int32 ($u32oz (Z.sub ($zou32 v3) 1%Z)));
                            AI_basic (BI_memory_fill)] ++ es0),
                          Some (AI_basic (BI_store T_i32 (Some Tp_i8) (Build_memarg 0%N 0%N)))), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_memory_fill_step; eauto; lias.
          }
      (* None *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        { eapply inst_typing_mem_lookup_inv in Hconjr as [? [Hextmt ?]]; eauto.
          unfold ext_mem_typing in Hextmt; remove_bools_options.
          by simplify_multieq.
        }
        { eapply inst_typing_mem_lookup_inv in Hconjr as [? [??]]; eauto.
          by simplify_multieq.
        }
        
    (* AI_basic BI_memory_copy *)
    - destruct vs0 as [|n [|src [|dst vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_i32 n.
      assert_i32 src.
      assert_i32 dst.
      destruct (smem s fc.(FC_frame).(f_inst)) as [mem|] eqn:Hsmem.
      (* Some *)
      + destruct (Z.ltb (Z.of_N (mem_length mem)) (($zou32 src) + ($zou32 n))) eqn:Hboundy; move/Z.ltb_spec0 in Hboundy.
        (* y Out of bound *)
        { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by eapply r_memory_copy_bound; eauto; lias.
        }
        destruct (Z.ltb (Z.of_N (mem_length mem)) (($zou32 dst) + ($zou32 n))) eqn:Hboundx; move/Z.ltb_spec0 in Hboundx.
        (* x Out of bound *)
        { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by eapply r_memory_copy_bound; eauto; lias.
        }
        (* In bound for both memories *)
        { destruct (Z.eqb ($zou32 n) Z0)%Z eqn:Hn0; move/Z.eqb_spec in Hn0; simpl in *; subst.
          (* Return *)
          { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_memory_copy_return; eauto; simpl in *; lias.
          }
          destruct (Z.leb ($zou32 dst) ($zou32 src)) eqn:Hdir; move/Z.leb_spec0 in Hdir.
          (* copy -- forward *)
          { apply <<hs, (s, (fc, lcs) :: ccs',
                          ((VAL_num (VAL_int32 src)) :: (VAL_num (VAL_int32 dst)) :: vs0,
                            [::(AI_basic (BI_store T_i32 (Some Tp_i8) (Build_memarg 0%N 0%N))); $VN (VAL_int32 ($u32oz (Z.add ($zou32 dst) 1))); $VN (VAL_int32 ($u32oz (Z.add ($zou32 src) 1%Z))); $VN (VAL_int32 ($u32oz (Z.sub ($zou32 n) 1))); AI_basic (BI_memory_copy)] ++ es0),
                          Some (AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N)))), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_memory_copy_forward; eauto; simpl in *; lias.
          }
          (* copy -- backward *)
          { apply <<hs, (s, (fc, lcs) :: ccs',
                          ((VAL_num (VAL_int32 ($u32oz (Z.add ($zou32 src) (Z.sub ($zou32 n) 1))))) ::
                             (VAL_num (VAL_int32 ($u32oz (Z.add ($zou32 dst) (Z.sub ($zou32 n) 1))))) ::
                             vs0,
                            [::(AI_basic (BI_store T_i32 (Some Tp_i8) (Build_memarg 0%N 0%N))); $VN (VAL_int32 dst); $VN (VAL_int32 src); $VN (VAL_int32 ($u32oz (Z.sub ($zou32 n) 1%Z))); AI_basic (BI_memory_copy)] ++ es0),
                          Some (AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg 0%N 0%N)))), d>> => //.
            resolve_reduce_ctx vs0 es0.
            eapply r_memory_copy_backward; eauto; simpl in *; try by lias.
          }
        }
      (* None *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        { eapply inst_typing_mem_lookup_inv in Hconjr as [? [Hextmt ?]]; eauto.
          unfold ext_mem_typing in Hextmt; remove_bools_options.
          by simplify_multieq.
        }
        { eapply inst_typing_mem_lookup_inv in Hconjr as [? [??]]; eauto.
          by simplify_multieq.
        }
        
    (* AI_basic BI_memory_init *)
    - destruct vs0 as [|n [|src [|dst vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_i32 n.
      assert_i32 src.
      assert_i32 dst.
      destruct (smem s fc.(FC_frame).(f_inst)) as [mem|] eqn:Hsmem.
      (* Some *)
      + destruct (sdata s fc.(FC_frame).(f_inst) x) as [data|] eqn:Hsdata.
        (* Some *)
        * destruct (Z.ltb (Z.of_nat (data_size data)) (($zou32 src) + ($zou32 n))) eqn:Hboundy; move/Z.ltb_spec0 in Hboundy.
          (* y Out of bound *)
          { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_memory_init_bound; eauto; lias.
          }
          destruct (Z.ltb (Z.of_N (mem_length mem)) (($zou32 dst) + ($zou32 n))) eqn:Hboundx; move/Z.ltb_spec0 in Hboundx.
          (* x Out of bound *)
          { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
            resolve_reduce_ctx vs0 es0.
            by eapply r_memory_init_bound; eauto; lias.
          }
          (* In bound for both table and elem *)
          { destruct (Z.eqb ($zou32 n) Z0) eqn:Hn0; move/Z.eqb_spec in Hn0; simpl in *; subst.
            (* Return *)
            { apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None), d>> => //.
              resolve_reduce_ctx vs0 es0.
              by eapply r_memory_init_return; eauto; simpl in *; lias.
            }
            (* Step -- but need to lookup first *)
            { destruct (lookup_N data.(datainst_data) ($nou32 src)) as [b | ] eqn:Hnthdata.
              (* Step *)
              { apply <<hs, (s, (fc, lcs) :: ccs',
                              ((VAL_num (wasm_deserialise [::b] T_i32)) :: (VAL_num (VAL_int32 dst)) :: vs0,
                                [::$VN (VAL_int32 ($u32oz (Z.add ($zou32 dst) 1)));
                                 $VN (VAL_int32 ($u32oz (Z.add ($zou32 src) 1)));
                                 $VN (VAL_int32 ($u32oz (Z.sub ($zou32 n) 1)));
                                 AI_basic (BI_memory_init x)
                                ] ++ es0),
                              Some (AI_basic (BI_store T_i32 (Some Tp_i8) (Build_memarg 0%N 0%N)))), d>> => //.
                resolve_reduce_ctx vs0 es0.
                by eapply r_memory_init_step; eauto; simpl in *; lias.
              }
              (* lookup oob *)
              { resolve_invalid_typing.
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

        (* sdata = None *)
        * resolve_invalid_typing.
          unfold_frame_type Hftype.
          unfold_store_operations.
          { eapply inst_typing_data_lookup_inv in Hconjr0 as [? [? [? [??]]]]; eauto.
            by simplify_multieq.
          }
          { eapply inst_typing_data_lookup_inv in Hconjr0 as [? [? [? [??]]]]; eauto.
            by simplify_multieq.
          }

      (* None *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        { eapply inst_typing_mem_lookup_inv in Hconjl0 as [? [Hextmt ?]]; eauto.
          unfold ext_mem_typing in Hextmt; remove_bools_options.
          by simplify_multieq.
        }
        { eapply inst_typing_mem_lookup_inv in Hconjl0 as [? [??]]; eauto.
          by simplify_multieq.
        }
          
    (* AI_basic BI_data_drop x *)
    - destruct (sdata_drop s fc.(FC_frame).(f_inst) x) as [s'|] eqn:Hs'.
      + apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_data_drop.
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        { eapply inst_typing_data_lookup_inv in Hconjr as [? [? [? [??]]]]; eauto.
          by simplify_multieq.
        }
        { eapply inst_typing_data_lookup_inv in Hconjr as [? [? [? [??]]]]; eauto.
          by simplify_multieq.
        }

    (* AI_basic BI_nop *)
    - apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None), d>> => //=.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_nop.

    (* AI_basic BI_unreachable *)
    - apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //=.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_unreachable.

    (* AI_basic (BI_block bt es) *)
    - destruct (expand fc.(FC_frame).(f_inst) bt) as [[t1s t2s] | ] eqn:Hexpand.
      (* Some t1s t2s *)
      + destruct (length vs0 >= length t1s) eqn:Hlen.
        (* true *)
        * destruct (split_n vs0 (length t1s)) as [ves' ves''] eqn:Hsplit.
          apply <<hs, (s, (fc, lcs) :: ccs', (ves'', es0), Some (AI_label (length t2s) nil (vs_to_es ves' ++ to_e_list es))), d>> => //.
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
        (* false *)
        * resolve_invalid_typing.
          unfold_frame_type Hftype.
          erewrite <- inst_typing_expand_eq in Hconjl0; eauto. 
          rewrite Hconjl0 in Hexpand; injection Hexpand as <- <-.
          by discriminate_size.
      (* None *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        erewrite <- inst_typing_expand_eq in Hconjl0; eauto.
        by rewrite Hconjl0 in Hexpand.

    (* AI_basic (BI_loop bt es) *)
    - destruct (expand fc.(FC_frame).(f_inst) bt) as [[t1s t2s] | ] eqn:Hexpand.
      (* Some t1s t2s *)
      + destruct (length vs0 >= length t1s) eqn:Hlen.
        (* true *)
        * destruct (split_n vs0 (length t1s)) as [ves' ves''] eqn:Hsplit.
          apply <<hs, (s, (fc, lcs) :: ccs', (ves'', es0), Some (AI_label (length t1s) [::AI_basic (BI_loop bt es)] (vs_to_es ves' ++ to_e_list es))), d>> => //.
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
        (* false *)
        * resolve_invalid_typing.
          unfold_frame_type Hftype.
          erewrite <- inst_typing_expand_eq in Hconjl0; eauto.
          rewrite Hconjl0 in Hexpand; injection Hexpand as <- <-.
          by discriminate_size.
      (* None *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        erewrite <- inst_typing_expand_eq in Hconjl0; eauto.
        by rewrite Hconjl0 in Hexpand.
        
    (* AI_basic (BI_if tb es1 es2) *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_i32 v.
      destruct (v == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
      (* true *)
      + apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_basic (BI_block bt es2))), d>> => //=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_if_false.
      (* false *)
      + apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_basic (BI_block bt es1))), d>> => //=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_if_true.

    (* AI_basic (BI_br j) *)
    - by apply run_ctx_br.

    (* AI_basic (BI_br_if j) *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_i32 v.
      destruct (v == Wasm_int.int_zero i32m) eqn:Heqc; move/eqP in Heqc.
      (* 0 *)
      + apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), None), d>> => //=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_br_if_false.
      (* not 0 *)
      + apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_basic (BI_br j))), d>> => //=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; apply rs_br_if_true.

    (* AI_basic (BI_br_table js j) *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_i32 v.
      destruct (N.ltb ($nou32 v) (N.of_nat (length js))) eqn:Hlen; move/N.ltb_spec0 in Hlen.
      (* true *)
      + destruct (lookup_N js ($nou32 v)) as [js_at_k|] eqn: Hnth.
        (* Some js_at_k *)
        * apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_basic (BI_br js_at_k))), d>> => //=.
          resolve_reduce_ctx vs0 es0.
          by apply r_simple; subst; apply rs_br_table.
        (* None *)
        * unfold lookup_N in Hnth.
          apply List.nth_error_None in Hnth.
          by lias.
      (* false *)
      + apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_basic (BI_br j))), d>> => //=.
        resolve_reduce_ctx vs0 es0.
        by apply r_simple; subst; apply rs_br_table_length; lias.
        
    (* AI_basic BI_return *)
    - by apply run_ctx_return.

    (* AI_basic (BI_call x) *)
    - destruct (lookup_N fc.(FC_frame).(f_inst).(inst_funcs) x) as [a|] eqn: Hnth.
      (* Some a *)
      + apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_invoke a)), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by apply r_call.
      (* None *)
      + resolve_invalid_typing.
        unfold_frame_type Hftype.
        eapply inst_typing_func_lookup_inv in Hconjr as [? [??]]; eauto.
        by simplify_multieq.

    (* AI_basic (BI_call_indirect x y) *)
    - destruct vs0 as [|v vs0]; first by no_args.
      assert_i32 v.
      destruct (stab_elem s fc.(FC_frame).(f_inst) x ($nou32 v)) as [vref|] eqn:?.
      (* Some a *)
      + destruct vref as [t | a | a].
        (* ref_null *)
        * apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap), d>> => //.
          resolve_reduce_ctx vs0 es0.
          by eapply r_call_indirect_failure_null_ref; eauto.
        (* funcref *)
        * destruct (lookup_N s.(s_funcs) a) as [cl | ] eqn:Hnthcl.
          (* Some *)
          -- destruct (lookup_N (inst_types (f_inst (fc.(FC_frame)))) y == Some (cl_type cl)) eqn:Hcl; move/eqP in Hcl.
            (* true *)
            ++ apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_invoke a)), d>> => //.
              resolve_reduce_ctx vs0 es0.
              by eapply r_call_indirect_success; subst; eauto.
            (* false *)
            ++ apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_trap)), d>> => //.
              resolve_reduce_ctx vs0 es0.
              by eapply r_call_indirect_failure_mismatch; subst; eauto.
          (* None *)
          -- resolve_invalid_typing.
             unfold_frame_type Hftype.
             unfold_store_operations.
             resolve_store_inst_lookup.
             destruct t1; remove_bools_options; simpl in *.
             eapply all_projection in Hif1; eauto.
             unfold value_typing in Hif1; simpl in Hif1.
             unfold ext_func_typing in Hif1.
             by remove_bools_options.
        (* externref *)
        * resolve_invalid_typing.
          unfold_frame_type Hftype.
          unfold_store_operations.
          resolve_store_inst_lookup.
          destruct t1; remove_bools_options; simpl in *.
          eapply all_projection in Hif1; eauto.
          unfold value_typing in Hif1; simpl in *.
          simplify_multieq.
          apply ref_subtyping in Hif1.
          by rewrite Hconjl1 in Hif1.
      (* None *)
      + apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some (AI_trap)), d>> => //.
        resolve_reduce_ctx vs0 es0.
        by eapply r_call_indirect_failure_bound; subst.

    (* AI_trap *)
    - destruct ((vs0 == nil) && (es0 == nil)) eqn:Hscnil; move/andP in Hscnil.
      + destruct Hscnil as [Heq1 Heq2]; move/eqP in Heq1; move/eqP in Heq2; subst.
        (* Checking if this is the last label ctx *)
        destruct lcs as [ | lc lcs'].
        (* If it is, then check if this is the last frame ctx.
           In the case where this is also true, we terminate. *)
        * destruct fc as [fvs ? ? fes].
          destruct ccs' as [ | cc0 ccs']; first by eapply RSC_trap; eauto.
          (* Otherwise, exit from the innermost frame. *)
          apply <<hs, (s, cc0 :: ccs', (fvs, fes), Some AI_trap), d>> => //=.
          (* pivot at cc0 *)
          replace (cc0 :: ccs') with (nil ++ cc0 :: ccs') at 2 => //.
          rewrite - cat1s.
          apply reduce_focus_pivot => //=.
          apply (list_label_ctx_eval).(ctx_reduce) => //.
          resolve_reduce_ctx fvs fes.
          by apply r_simple, rs_local_trap.
        * destruct lc as [lvs ? ? les].
          apply <<hs, (s, (fc, lcs') :: ccs', (lvs, les), Some AI_trap), d>> => //.
          apply reduce_focus => //=.
          apply list_label_ctx_eval.(ctx_reduce) => //=.
          unfold label_ctx_fill => /=.
          resolve_reduce_ctx lvs les.
          by apply r_simple, rs_label_trap.
      + apply <<hs, (s, (fc, lcs) :: ccs', (nil, nil), Some AI_trap), d>> => //.
        resolve_reduce_ctx lvs les.
        apply r_simple.
        apply rs_trap with (lh := LH_base (rev vs0) es0) => //.
        move => Hcontra; apply Hscnil.
        specialize (f_equal size Hcontra) as Hsize; rewrite size_cat v_to_e_size size_rev in Hsize.
        simpl in Hsize.
        clear - Hsize.
        assert (H: size vs0 = 0); first (by lias); destruct vs0 => //; clear H.
        assert (H: size es0 = 0); first (by lias); by destruct es0.

    (* AI_ref a *)
    - by apply RSC_invalid => /=; move => [??].
      
    (* AI_ref_extern a *)
    - by apply RSC_invalid => /=; move => [??].
       
    (* AI_invoke a *)
    - by apply run_ctx_invoke.
        
    (* AI_label ln les es *)
    - by apply RSC_invalid => /=; move => [??].

    (* AI_frame ln lf es *)
    - by apply RSC_invalid => /=; move => [??].
  }
Defined.

(* reformation to a valid configuration. *)
Definition run_step_cfg_ctx_reform (cfg: cfg_tuple_ctx) : option cfg_tuple_ctx :=
  let '(s, ccs, sc, oe) := cfg in
  match ctx_update ccs sc oe with
  | Some (ccs', sc', oe') => Some (s, ccs', sc', oe')
  | None => None
  end.

Lemma run_step_reform_valid s ccs sc oe :
  valid_ccs ccs ->
  {cfg | run_step_cfg_ctx_reform (s, ccs, sc, oe) = Some cfg /\
         ctx_to_cfg (s, ccs, sc, oe) = ctx_to_cfg cfg /\
         valid_cfg_ctx cfg}.
Proof.
  move => Hvalid.
  unfold run_step_cfg_ctx_reform.
  specialize (ctx_update_valid_ccs sc oe Hvalid) as [ccs' [sctx' [oe' [Hupdate Hvalid']]]].
  rewrite Hupdate.
  eexists; do 2 split => //; last by apply ctx_update_valid in Hupdate.
  apply ctx_update_fill in Hupdate.
  by apply ctx_fill_impl.
Qed.

Definition run_v_init (s: store_record) (es: list administrative_instruction) : option cfg_tuple_ctx :=
  match ctx_decompose es with
  | Some (ccs, sc, oe) => Some (s, ccs, sc, oe)
  | None => None
  end.

(* run_v_init with a frame always returns a valid cfg tuple.
   This function provides a conversion from a Wasm config tuple to an
   interpreter config tuple.
 *)
Definition interp_cfg_of_wasm (wasm_cfg: config_tuple) : { cfg : cfg_tuple_ctx | ctx_to_cfg cfg = Some wasm_cfg /\ valid_cfg_ctx cfg }.
Proof.
  destruct wasm_cfg as [s [f es]].
  (* Arity of outermost frame doesn't matter as it gets removed later *)
  destruct (run_v_init s [::AI_frame 0 f es]) as [ cfg | ] eqn:Hinit.
  - exists cfg.
    move: Hinit.
    rewrite /run_v_init /ctx_decompose ctx_decompose_aux_equation /=.
    destruct (ctx_decompose_aux _) as [[[??]?]|] eqn:Hdecomp => //.
    move => [<-].
    assert (valid_ccs l) as Hvalidccs; first by apply ctx_decompose_valid_ccs_aux in Hdecomp.
    repeat split => //.
    { unfold ctx_to_cfg.
      apply ctx_decompose_fill_aux in Hdecomp.
      destruct l using last_ind => //; clear IHl.
      rewrite rev_rcons.
      destruct x as [[fvs fk ff fes] lcs].
      simpl in *.
      rewrite foldl_rcons in Hdecomp; simpl in Hdecomp.
      unfold vs_to_es in Hdecomp.
      destruct (rev fvs) as [ | v vs] eqn:Hrevfvs => //; last by destruct v as [?|?|v] => //; destruct v.
      simpl in *.
      destruct fes => //.
      inversion Hdecomp; subst; clear Hdecomp.
      by rewrite revK.
    }
    { by apply ctx_decompose_valid_aux in Hdecomp. }
  (* Impossible case *)
  - exfalso.
    move: Hinit.
    rewrite /run_v_init /ctx_decompose ctx_decompose_aux_equation /=.
    destruct (ctx_decompose_aux _) as [[[??]?]|] eqn:Hdecomp => //; by apply ctx_decompose_acc_some in Hdecomp.
Defined.

(* One-step interpreter with cfg reformation. *)
Definition run_one_step (hs: host_state) (cfg: cfg_tuple_ctx) (d: N): run_step_ctx_result hs cfg d.
Proof.
  destruct (run_one_step_ctx hs cfg d) as [hs' cfg' d' Hreduce Hvalid | | | |].
  - destruct cfg' as [[[s ccs] sc] oe].
    assert (valid_ccs ccs) as Hvalid'; first by destruct ccs.
    apply (run_step_reform_valid s sc oe) in Hvalid' as [cfg' [Hreform [Heq Hvalid']]].
    apply (@RSC_normal hs cfg d hs' cfg' d').
    + unfold reduce_ctx in *.
      destruct (ctx_to_cfg cfg) as [[s0 [f0 es0]] | ] eqn:Hcfg => //.
      by rewrite Heq in Hreduce.
    + destruct cfg' as [[[??]?]?]; destruct Hvalid' as [??].
      unfold valid_ccs_cfg.
      by destruct l.
  all: by econstructor; eauto.
Defined.

Fixpoint run_multi_step_ctx (fuel: nat) (hs: host_state) (cfg: cfg_tuple_ctx) (d: N) : (option unit) + (list value) :=
  match fuel with
  | 0 => inl None
  | S n =>
      match run_one_step hs cfg d with
      | RSC_normal hs' cfg' d' Hvalid HReduce =>
         run_multi_step_ctx n hs' cfg' d'
      | RSC_value _ _ vs _ => inr vs
      | _ => inl None
      end
  end.

(** Note that this function should *never* be used in the extracted code due to the inefficient
    usage of fuel. It is only used internally during module instantiation.
 **)

Definition run_multi_step_raw (hs: host_state) (fuel: nat) (s: store_record) (f: frame) (es: list administrative_instruction): (option unit) + (list value) :=
  match interp_cfg_of_wasm (s, (f, es)) with
  | exist cfg _ => run_multi_step_ctx fuel hs cfg 0
  end.

End Host.
