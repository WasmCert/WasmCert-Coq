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
  
Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                       (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).

Notation "ctx ⦃ es ⦄" := (ctx_fill es ctx) (at level 1).

Definition ctx_to_cfg (cfg: cfg_tuple_ctx) : option config_tuple :=
  match cfg with
  | (s, ccs, sc, oe) =>
      match rev ccs with
      | nil => None
      | (Build_frame_ctx fvs fk ff fes, lcs) :: ccs' =>
          Some (s, (ff, lcs ⦃ (rev ccs') ⦃ sc ⦃ olist oe ⦄ ⦄ ⦄))
      end
  end.

Definition ctx_cfg_typing (cfg: cfg_tuple_ctx) (ts: result_type) : Prop :=
  match ctx_to_cfg cfg with
  | Some (s, th) =>
      config_typing s th ts
  | None => False
  end.

Lemma config_typing_inv: forall s (f: frame) es ts,
    config_typing s (f, es) ts ->
    exists C,
      store_typing s /\
      frame_typing s f C /\
      e_typing s C es (Tf [::] ts).
Proof.
  move => s f es ts Htype; subst.
  destruct Htype as [Hstoretype Hthtype].
  inversion Hthtype as [s' f' es' ors rs C' Hstype Hftype ? Hetype]; subst; clear Hthtype.
  replace (upd_return C' None) with C' in Hetype; first by exists C'.
  unfold frame_typing in Hftype.
  remove_bools_options.
  destruct Hftype as [ts' [-> Hvaltype]] => /=.
  by unfold inst_typing in Hoption; destruct f, f_inst, t; unfold upd_return, upd_local, upd_local_label_return in *; simpl in *; remove_bools_options.
Qed.

(* Context typing inversion lemma *)
Lemma ctx_cfg_inv: forall s cc ccs sc oe ts,
    ctx_cfg_typing (s, (cc :: ccs), sc, oe) ts ->
    exists C (ret: option result_type) labs ts2,
      store_typing s /\
      frame_typing s cc.1.(FC_frame) C /\
      all2 lab_lc_agree labs cc.2 /\ 
      (ccs != nil -> (option_map (@length _) ret = Some cc.1.(FC_arity))) /\
      (ccs = nil -> ret = None) /\
      e_typing s (upd_label (upd_return C ret) labs) (sc ⦃ olist oe ⦄) (Tf nil ts2).
Proof.
  move => s cc ccs sc oe ts Htype.
  unfold ctx_cfg_typing in Htype.
  destruct (ctx_to_cfg (s, cc::ccs, sc, oe)) as [[s0 [f es]]|] eqn:Hcfg => //; unfold ctx_to_cfg in Hcfg.
  destruct (rev (cc :: ccs)) as [ | [[? ? ff ?] lcs] ccs'] eqn:Hcc => //.
  injection Hcfg as <- <- <-.
  apply config_typing_inv in Htype as [C [Hstype [Hftype Hetype]]].
  apply lcs_typing_exists_nil in Hetype as [labs0 [ts2 [Hetype Hagree0]]].
  destruct ccs' using last_ind.
  + destruct ccs; simpl in * => //; last by apply (f_equal size) in Hcc; rewrite size_rev in Hcc.
    rewrite rev_cons in Hcc; simpl in *.
    injection Hcc as -> => /=.
    exists C, None, labs0, ts2 => /=.
    unfold upd_label, upd_return, upd_local_label_return => /=.
    repeat split; try by destruct C.
    unfold frame_typing in Hftype; remove_bools_options.
    destruct Hftype as [? [-> ?]].
    erewrite -> inst_t_context_local_empty, cats0 in Hetype; eauto.
    simpl in *.
    erewrite -> inst_t_context_local_empty, cats0; eauto.
    erewrite -> inst_t_context_label_empty, cats0 in Hetype; eauto.
    uapply Hetype => /=.
    by erewrite <- inst_t_context_return_None; eauto.
  + clear IHccs'.
    rewrite rev_rcons in Hetype.
    apply ccs_typing_exists in Hetype as [C0 [ret [labs [ts' [Hftype0 [Harity [Hagree Hetype]]]]]]].
    rewrite rev_cons -rcons_cons in Hcc.
    apply rcons_inj in Hcc.
    injection Hcc as Hcc <-.
    apply rev_move in Hcc; subst.
    exists C0, (Some ret), labs, ts'.
    repeat split => //; move => Hreveq => //=; last by apply (f_equal size) in Hreveq; rewrite size_rev in Hreveq.
    by rewrite Harity.
Qed.

(*
(** Auxiliary definition for reductions between context tuples.
    Technically there's an auxiliary empty frame added; but that allows precisely
    the same set of instructions.
 **)
Definition reduce_ctx (hs hs': host_state) (cfg cfg': cfg_tuple_ctx) : Prop :=
  match cfg with
  | (s, ccs, sc, oe) =>
      match cfg' with
      | (s', ccs', sc', oe') => reduce hs s empty_frame (ccs ⦃ sc ⦃ olist oe ⦄ ⦄) hs' s' empty_frame (ccs' ⦃ sc' ⦃ olist oe' ⦄ ⦄)
      end
  end.
*)

(** Auxiliary definition for reductions between context tuples. **)

Definition reduce_ctx (hs hs': host_state) (cfg cfg': cfg_tuple_ctx) : Prop :=
  match ctx_to_cfg cfg with
  | Some (s, (f, es)) =>
      match ctx_to_cfg cfg' with
      | Some (s', (f', es')) =>
          reduce hs s f es hs' s' f' es'
      | None => False
      end
  | None => False
  end.

(** ctx reduction lemmas **)
Lemma reduce_focus_pivot ccs0 ccs1: forall hs hs' s ccs sc oe s' sc' oe' cc0 cc0',
    cc0.1.(FC_val) = cc0'.1.(FC_val) ->
    cc0.1.(FC_post) = cc0'.1.(FC_post) ->
    cc0.1.(FC_arity) = cc0'.1.(FC_arity) ->
    reduce hs s cc0.1.(FC_frame) (cc0.2 ⦃ ccs0 ⦃ sc ⦃ olist oe ⦄ ⦄ ⦄) hs' s' cc0'.1.(FC_frame) (cc0'.2 ⦃ ccs1 ⦃ sc' ⦃ olist oe' ⦄ ⦄ ⦄) ->
    reduce_ctx hs hs' (s, ccs0 ++ cc0 :: ccs, sc, oe) (s', ccs1 ++ cc0' :: ccs, sc', oe').
Proof.
  destruct ccs as [|ccs' cc] using last_ind.
  - intros ????? [fc lcs] [fc' lcs'] ??? Hred => /=.
    unfold reduce_ctx, ctx_to_cfg => /=.
    destruct fc, fc'; simpl in *.
    do 2 rewrite rev_cat /= revK.
    exact Hred.
  - intros ????? [fc lcs] [fc' lcs'] Heqval Heqpost Heqarity Hred.
    unfold reduce_ctx, ctx_to_cfg in * => /=.
    destruct cc as [[fvs0 fk0 ff0 fes0] lcs0].
    rewrite rev_cat rev_cons rev_rcons /=.
    repeat rewrite rev_cat rev_rcons revK.
    rewrite rev_cat rev_cons rev_rcons revK /= rev_cat rev_rcons revK revK.
    apply (list_label_ctx_eval.(ctx_reduce)) => //.
    do 2 rewrite foldl_cat.
    simpl in *.
    apply (list_closure_ctx_eval.(ctx_reduce)) => //.
    rewrite -Heqval -Heqpost -Heqarity.
    eapply r_label with (lh := LH_base (rev (FC_val fc)) (FC_post fc)) => /=; try by (f_equal; rewrite -cat1s; eauto).
    by apply r_frame.
Qed.

Lemma reduce_focus: forall ccs hs s lcs sc oe hs' s' lcs' sc' oe' fc fc',
    fc.(FC_val) = fc'.(FC_val) ->
    fc.(FC_post) = fc'.(FC_post) ->
    fc.(FC_arity) = fc'.(FC_arity) ->
    reduce hs s fc.(FC_frame) (lcs ⦃ sc ⦃ olist oe ⦄ ⦄) hs' s' fc'.(FC_frame) (lcs' ⦃ sc' ⦃ olist oe' ⦄ ⦄) ->
    reduce_ctx hs hs' (s, (fc, lcs) :: ccs, sc, oe) (s', (fc', lcs') :: ccs, sc', oe').
Proof.
  intros; by apply (@reduce_focus_pivot nil nil).
Qed.

Lemma reduce_focus_id: forall ccs hs s lcs sc oe hs' s' sc' oe' fc fc',
    fc.(FC_val) = fc'.(FC_val) ->
    fc.(FC_post) = fc'.(FC_post) ->
    fc.(FC_arity) = fc'.(FC_arity) ->
    reduce hs s fc.(FC_frame) (sc ⦃ olist oe ⦄) hs' s' fc'.(FC_frame) (sc' ⦃ olist oe' ⦄) ->
    reduce_ctx hs hs' (s, (fc, lcs) :: ccs, sc, oe) (s', (fc', lcs) :: ccs, sc', oe').
Proof.
  intros ???????????? Heqval Heqpost Heqarity Hred => /=.
  apply reduce_focus => //.
  by apply (list_label_ctx_eval.(ctx_reduce)) with (hs := hs) => //.
Qed.

(*
(* The reduction of a combined frame and instructions projects back to a reduction 
   between the original thread setups. *)
Lemma reduce_fes_thread hs hs' s s' fes fes' f es f' es' f0 f0':
  reduce hs s f0 fes hs' s' f0' fes' ->
  fes_to_thread fes = Some (f, es) ->
  fes_to_thread fes' = Some (f', es') ->
  reduce hs s f es hs' s' f' es'.
Proof.
  move => Hred Hthread1 Hthred2.
  unfold fes_to_thread in *.
  destruct fes => //; destruct a => //; destruct fes => //.
  destruct fes' => //; destruct a => //; destruct fes' => //.
  remove_bools_options.
  remember [::AI_frame n f es] as les.
  remember [::AI_frame n0 f' es'] as les'.
  induction Hred; subst => //.
  - by inversion H; subst; clear H => //.
  - by repeat (destruct vs as [|? vs] => //).
  - by repeat (destruct vcs as [|? vcs] => //).
  - destruct lh; simpl in *.
    + destruct l as [ | ? l] => //; simpl in *; last by repeat destruct v => //.
      destruct es0 as [|e es0]; first by apply reduce_not_nil in Hred.
      destruct es0, l0 => //.
      rewrite cats0 in H0; simpl in H; inversion H; subst.
      by eapply IHHred; eauto.
    + by repeat destruct l => //.
  - by inversion Heqles; inversion Heqles'; subst.
Qed.

Lemma valid_ccs_thread ccs es:
  valid_ccs ccs ->
  exists f es', fes_to_thread (ccs ⦃ es ⦄) = Some (f, es').
Proof.
  unfold valid_ccs.
  destruct ccs as [|cc ccs] => //.
  move => Hvalid.
  destruct (cc :: ccs) eqn:Hlast using last_ind => //.
  rewrite last_rcons in Hvalid.
  simpl.
  rewrite foldl_rcons => /=.
  destruct x as [fc lcs]; destruct fc; simpl in *.
  remove_bools_options; subst.
  by repeat eexists.
Qed.
 *)

Ltac red_ctx_simpl :=
  repeat lazymatch goal with
  | |- reduce _ _ _ (((_, ?lcs) :: ?ccs) ⦃ _ ⦃ _ ⦄ ⦄) _ _ _ (((_, ?lcs) :: ?ccs) ⦃ _ ⦃ _ ⦄ ⦄) =>
      apply reduce_focus_id
  | |- reduce _ _ _ (((_, _) :: ?ccs) ⦃ _ ⦃ _ ⦄ ⦄) _ _ _ (((_, _) :: ?ccs) ⦃ _ ⦃ _ ⦄ ⦄) =>
      apply reduce_focus
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
  unfold reduce_ctx; try (eapply r_label with (lh := LH_base (rev vs) es) => /=; infer_hole).

Ltac resolve_valid_ccs :=
  repeat lazymatch goal with
    | |- _ /\ _ =>
        split => //
    | |- context C [valid_ccs _] =>
        unfold valid_ccs => /=
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
| RSC_value s f vs:
  ctx_to_cfg cfg = Some (s, (f, v_to_e_list vs)) ->
  run_step_ctx_result hs cfg
| RSC_invalid :
  (valid_cfg_ctx cfg -> False) ->
  run_step_ctx_result hs cfg
| RSC_error:
  (forall ts, ctx_cfg_typing cfg ts -> False) ->
  run_step_ctx_result hs cfg
.

Ltac invert_ctx_typing Hetype0 :=
  match type of Hetype0 with
  | e_typing _ _ ((_ :: _) ⦃ _ ⦃ _ ⦄ ⦄) _ =>
    let vts := fresh "vts" in
    let ts' := fresh "ts'" in
    let Hvtsype := fresh "Hvtsype" in
    let Hftype := fresh "Hftype" in
    let Hetype := fresh "Hetype" in
    let Harity := fresh "Harity" in
    apply e_typing_ops_local in Hetype0 as [? [? [? [? [vts [ts' [Hvtstype [Hftype [Harity [? Hetype]]]]]]]]]]
  | e_typing _ _ (_ ⦃ _ ⦃ _ ⦄ ⦄) (Tf nil _) =>
    let vts := fresh "vts" in
    let ts' := fresh "ts'" in
    let Hvtsype := fresh "Hvtsype" in
    let Hetype := fresh "Hetype" in
    apply e_typing_ops in Hetype0 as [? [vts [ts' [Hvtstype Hetype]]]]
  end;
  simpl in *; invert_e_typing; remove_bools_options.

(** The usual start of a crash certification **)
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
  invert_e_typing; simpl in *.

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

(* Note that this destroys the original premises, so should only be used as a terminal most of time. *)
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

(** Br exits from one label context. **)
Definition run_ctx_br: forall hs s ccs sc j,
  run_step_ctx_result hs (s, ccs, sc, Some (AI_basic (BI_br j))).
Proof.
  intros hs s ccs [vs es] j.
  get_cc ccs.
  destruct (lookup_N lcs j) as [lab | ] eqn:Htar.
  - destruct lab as [lvs lk lces les].
    specialize (nth_error_Some_length Htar) as Hlablen; move/ltP in Hlablen.
    destruct (lk <= length vs) eqn:Hvslen.
    + apply <<hs, (s, ((fc, drop (S (N.to_nat j)) lcs) :: ccs'), (take lk vs ++ lvs, lces ++ les), None)>> => //.
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

(** Return exits from the innermost frame and all label contexts. **)
Definition run_ctx_return: forall hs s ccs sc,
  run_step_ctx_result hs (s, ccs, sc, Some (AI_basic BI_return)).
Proof.  
  intros hs s ccs [vs es].
  get_cc ccs.
  (* Return needs an additional frame to execute; otherwise it returns in a type error. *)
  destruct ccs' as [| ccs' cc0] using last_ind.
  (* Error *)
  - by resolve_invalid_typing.
  - clear IHccs'.
    destruct fc as [lvs lk lf les].
    destruct (lk <= length vs) eqn:Hvslen.
    + apply <<hs, (s, rcons ccs' cc0, (take lk vs ++ lvs, les), None)>> => //=.
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

Definition run_ctx_invoke hs s ccs vs0 es0 a:
    run_step_ctx_result hs (s, ccs, (vs0, es0), Some (AI_invoke a)).
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
        (* types are all defaultable as of Wasm 2.0 *)
        { apply <<hs, (s, (Build_frame_ctx vs'' m (Build_frame (rev vs' ++ zs) i) es0, nil) :: (fc, lcs) :: ccs', (nil, nil), Some (AI_label m nil (to_e_list es)))>> => /=.
          apply (@reduce_focus_pivot nil ([::(Build_frame_ctx vs'' m _ es0, nil)])) => //=.
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
        -- (* (hs', Some (s', rves)) *)
          destruct rves as [rvs | ].
          ++ apply <<hs', (s', (fc, lcs) :: ccs', (rev rvs ++ vs'', es0), None)>> => /=.
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
             eapply r_invoke_host_success; eauto.
             repeat rewrite length_is_size.
             by rewrite size_rev size_takel => //.
          ++ apply <<hs', (s', (fc, lcs) :: ccs', (vs'', es0), Some AI_trap)>> => /=.
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
             by rewrite size_rev size_takel => //.
  - (* (hs', None) *)
    apply <<hs', (s, (fc, lcs) :: ccs', (vs'', es0), Some AI_trap)>> => /=.
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
    by rewrite size_rev size_takel => //.
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

(* Lemma for eliminating subtypes *)
Lemma operand_subtyping: forall s ops ops0 vts ts1 ts2 ts',
  values_typing s (rev (ops ++ ops0)) vts ->
  (Tf ts1 ts2 <ti: Tf vts ts') ->
  size ops = size ts1 ->
  values_typing s ops (rev ts1).
Proof.
  move => s ops ops0 vts ts1 ts2 ts' Hvt Hsub Hsize.
  apply values_typing_rev in Hvt.
  apply instr_subtyping_consumed_rev_prefix in Hsub as [ts_prefix [Heqrev Hsub]].
  rewrite Heqrev in Hvt.
  unfold values_typing in Hvt.
  rewrite all2_cat in Hvt; remove_bools_options; first by eapply values_typing_trans; eauto.
  apply values_subtyping_size in Hsub.
  by rewrite size_rev in Hsub; lias.
Qed.

(* Instances for tactic *)
Lemma operand_subtyping1: forall s v1 ops0 vts t1 ts2 ts',
  values_typing s (rev (v1 :: ops0)) vts ->
  (Tf [::t1] ts2 <ti: Tf vts ts') ->
  values_typing s [::v1] [::t1].
Proof.
  intros ??????? Hvt Hsub.
  rewrite -cat1s in Hvt.
  by eapply operand_subtyping in Hsub; eauto.
Qed.

Lemma operand_subtyping2: forall s v1 v2 ops0 vts t1 t2 ts2 ts',
  values_typing s (rev (v1 :: v2 :: ops0)) vts ->
  (Tf [::t1; t2] ts2 <ti: Tf vts ts') ->
  values_typing s [::v1; v2] [::t2; t1].
Proof.
  intros ????????? Hvt Hsub.
  rewrite -(cat1s v1) -(cat1s v2) catA in Hvt.
  by eapply operand_subtyping in Hsub; eauto.
Qed.

Lemma operand_subtyping3: forall s v1 v2 v3 ops0 vts t1 t2 t3 ts2 ts',
  values_typing s (rev (v1 :: v2 :: v3 :: ops0)) vts ->
  (Tf [::t1; t2; t3] ts2 <ti: Tf vts ts') ->
  values_typing s [::v1; v2; v3] [::t3; t2; t1].
Proof.
  intros ??????????? Hvt Hsub.
  rewrite -(cat1s v1) -(cat1s v2) -(cat1s v3) catA catA in Hvt.
  by eapply operand_subtyping in Hsub; eauto.
Qed.

Lemma operand_subtyping_suffix1: forall s v1 ops0 vts ts0 t1 ts2 ts',
  values_typing s (rev (v1 :: ops0)) vts ->
  (Tf (ts0 ++ [::t1]) ts2 <ti: Tf vts ts') ->
  values_typing s [::v1] [::t1].
Proof.
  intros ???????? Hvt Hsub.
  apply values_typing_rev in Hvt.
  apply instr_subtyping_consumed_rev_prefix in Hsub as [ts_prefix [Heqrev Hsub]].
  rewrite Heqrev in Hvt.
  unfold values_typing in Hvt.
  rewrite rev_cat in Hsub.
  destruct ts_prefix as [|t ?] => //.
  simpl in *; remove_bools_options.
  by erewrite value_typing_trans; eauto.
Qed.

Lemma value_typing_ref_impl: forall s v t,
  value_typing s (VAL_ref v) t ->
  exists tref, t = T_ref tref.
Proof.
  move => s v t Hvt.
  unfold value_typing in Hvt; remove_bools_options.
  simpl in *; remove_bools_options.
  apply ref_subtyping in Hvt; subst.
  by eexists.
Qed.

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
  | _ => simpl in *; remove_bools_options; subst => //
end.

Ltac discriminate_value_type :=
  resolve_invalid_typing; resolve_invalid_value.

Ltac assert_value_num v :=
  destruct v as [v | |]; [ | by discriminate_value_type | by discriminate_value_type].

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
Definition run_one_step_ctx (hs: host_state) (cfg: cfg_tuple_ctx) : run_step_ctx_result hs cfg.
Proof.
  destruct cfg as [[[s ccs] sc] oe].
  destruct oe as [e | ]; last first.
  (* Exitting from contexts *)
  {
    destruct sc as [vs es]; subst.
    destruct es as [ | ??]; last by apply RSC_invalid => /=; move => [??].
    destruct ccs as [ | [fc lcs] ccs'].
    { (* Only values left, with no context. This case should have been removed in the
         restructure function *)
      eapply RSC_value with (vs := rev vs) => //=.
      by rewrite cats0.
    }
    { destruct lcs as [ | lc lcs'].
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
        (* length doesn't match -- ill-typed. However, in this case we check if it's only a frame containing values *)
        {
          destruct ((ccs' == nil) && (lvs == nil) && (les == nil)) eqn:Hfv.
          { remove_bools_options; subst.
            apply (@RSC_value_frame _ _ hs s (rev vs) lk lf) => //=.
            by rewrite cats0.
          }
          {
            apply RSC_error.
            intros ts Htype; unfold s_of_cfg, es_of_cfg in Htype.
            eapply config_typing_inv in Htype as [C0 [Hstype [Hftype0 Hetype]]]; eauto.
            apply ccs_typing_focus in Hetype as [C [? [? [[ts1 ts2] Hetype]]]].
            rewrite /= cats0 in Hetype.
            rewrite -cat1s in Hetype.
            unfold vs_to_es in Hetype.
            invert_e_typing.
            inversion Hconjl0 as [??????? Hftype ? Hetype Hvstype]; subst; clear Hconjl0.
            invert_e_typing.
            by discriminate_size.
          }
        }
      }
      (* Exitting a label *)
      { destruct lc as [lvs lk lces les].
        destruct les as [ | e les'].
        { (* No instruction in the hole still *)
          apply <<hs, (s, (fc, lcs') :: ccs', (vs ++ lvs, nil), None)>> => /=.
          resolve_reduce_ctx (FC_val fc) (FC_post fc).
          eapply r_frame.
          apply reduce_focus_id => //=.
          unfold fmask0, label_ctx_fill => /=.
          eapply r_label with (lh := LH_base (rev lvs) nil) => /=; infer_hole; eauto => /=.
          apply r_simple, rs_label_const; by apply v_to_e_const.
        }
        { (* e is in the hole *)
          apply <<hs, (s, (fc, lcs') :: ccs', (vs ++ lvs, les'), Some e)>> => /=.
          resolve_reduce_ctx (FC_val fc) (FC_post fc).
          apply r_frame => /=.
          apply reduce_focus_id => //=.
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
      assert_value_num v.
      (* v :: ves' *)
      apply <<hs, (s, ccs, (VAL_num (app_unop op v) :: vs0, es0), None)>>.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_unop.

    - (* AI_basic (BI_binop t op) *)
      destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      assert_value_num v2.
      assert_value_num v1.
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
      assert_value_num v.
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
      assert_value_num v2.
      assert_value_num v1.
      (* [:: v2, v1 & ves'] *)
      apply <<hs, (s, ccs, (VAL_num (VAL_int32 (wasm_bool (@app_relop op v1 v2))) :: vs0, es0), None)>>.
      resolve_reduce_ctx vs0 es0.
      by apply r_simple, rs_relop.

    - (* AI_basic (BI_cvtop t2 CVO_convert t1 sx) *)
      destruct vs0 as [|v vs0]; first by no_args.
      assert_value_num v.
      (* v :: ves' *)
      destruct (typeof_num v == t1) eqn:Ht1; move/eqP in Ht1.
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
        discriminate_value_type.
        apply num_subtyping in H; by inversion H; subst.

    - (* AI_basic BI_const_vec v *)
      apply RSC_invalid => /=; by move => [??].
      
    - (* AI_basic BI_ref_null t *)
      apply RSC_invalid => /=; by move => [??].

    - (* AI_basic BI_ref_is_null *)
      destruct vs0 as [|v vs0]; first by no_args.
      assert_value_ref v.
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
        unfold_frame_type Hftype.
        eapply inst_typing_func_lookup_inv in Hconjl0 as [f [Hext Hnthf]]; eauto.
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
      assert_i32 v3.
      (* VAL_int32 c *)
      destruct (v3 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
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
        unfold_frame_type Hftype.
        erewrite inst_t_context_local_empty in Hconjr; eauto.
        by discriminate_size.
        
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
        unfold_frame_type Hftype.
        erewrite inst_t_context_local_empty in Hconjr; eauto.
        by discriminate_size.

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
        unfold_frame_type Hftype.
        unfold_store_operations.
        * by inst_typing_lookup; remove_bools_options.
        * eapply inst_typing_global_lookup_inv in Hoption as [? [? Hnthg]]; eauto.
          by simplify_multieq.

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
        unfold_frame_type Hftype.
        unfold_store_operations.
        * by inst_typing_lookup; remove_bools_options.
        * eapply inst_typing_global_lookup_inv in Hconjl0 as [? [? Hnthg]]; eauto.
          by simplify_multieq.

    - (* AI_basic (BI_table_get x) *)
      get_cc ccs.
      destruct vs0 as [|v vs0]; first by no_args.
      assert_i32 v.
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
      assert_value_ref v2.
      assert_i32 v1.
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
        unfold_frame_type Hftype.
        unfold_store_operations.
        * inst_typing_lookup.
          by rewrite Hstab in Hexttabt.
        * eapply inst_typing_table_lookup_inv in Hconjr as [? [? Hnthtab]]; eauto.
          by simplify_multieq.

    - (* AI_basic (BI_table_grow x) *)
      get_cc ccs.
      destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      (* Takes an i32 and a reference value *)
      assert_i32 v2.
      assert_value_ref v1.
      destruct (stab_grow s fc.(FC_frame).(f_inst) x ($nou32 v2) v1) as [[s' sz]|] eqn:Hstabgrow.
      + apply <<hs, (s', (fc, lcs) :: ccs', ((VAL_num (VAL_int32 ($u32oz (Z.of_nat sz)))) :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by eapply r_table_grow_success; eauto.
      + (* None *)
        apply <<hs, (s, (fc, lcs) :: ccs', ((VAL_num (VAL_int32 int32_minus_one)) :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by eapply r_table_grow_failure; eauto.

    - (* AI_basic (BI_table_fill x) *)
      get_cc ccs.
      destruct vs0 as [|v3 [|v2 [|v1 vs0]]]; try by no_args.
      (* Takes i32; ref; i32 *)
      assert_i32 v3.
      assert_value_ref v2.
      assert_i32 v1.
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
        unfold_frame_type Hftype.
        unfold_store_operations.
        * inst_typing_lookup.
          by rewrite Hstab in Hexttabt.
        * eapply inst_typing_table_lookup_inv in Hconjl0 as [? [? Hnthtab]]; eauto.
          by simplify_multieq.
          
    - (* AI_basic (BI_table_copy x y) *)
      get_cc ccs.
      destruct vs0 as [|n [|src [|dst vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_i32 n.
      assert_i32 src.
      assert_i32 dst.
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
          unfold_frame_type Hftype.
          unfold_store_operations.
          {  inst_typing_lookup.
             by rewrite Hstaby in Hexttabt.
          }
          { eapply inst_typing_table_lookup_inv in Hconjl2 as [? [? Hnthtab]]; eauto.
            by simplify_multieq.
          }
          
      + (* stabx = None *)
        resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        {  inst_typing_lookup.
           by rewrite Hstabx in Hexttabt.
        }
        { eapply inst_typing_table_lookup_inv in Hconjl0 as [? [? Hnthtab]]; eauto.
          by simplify_multieq.
        }
        
    - (* AI_basic (BI_table_init x y) *)
      get_cc ccs.
      destruct vs0 as [|n [|src [|dst vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_i32 n.
      assert_i32 src.
      assert_i32 dst.
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
          unfold_frame_type Hftype.
          unfold_store_operations; eapply inst_typing_elem_lookup_inv in Hconjr as [? [? [? [??]]]]; eauto; by simplify_multieq.
          
      + (* stab = None *)
        resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        {  inst_typing_lookup.
           by rewrite Hstab in Hexttabt.
        }
        { eapply inst_typing_table_lookup_inv in Hconjl0 as [? [??]]; eauto.
          by simplify_multieq.
        }
        
    - (* AI_basic BI_elem_drop x *)
      get_cc ccs.
      destruct (selem_drop s fc.(FC_frame).(f_inst) x) as [s'|] eqn:Hs'.
      + apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None)>>.
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

    - (* AI_basic (BI_load t ops (Some (tp, sx)) a off) *)
      get_cc ccs.    
      destruct vs0 as [|v vs0]; first by no_args.
      assert_i32 v.
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
        unfold_frame_type Hftype.
        unfold_store_operations.
        { inst_typing_lookup; by remove_bools_options. }
        { eapply inst_typing_mem_lookup_inv in Hconjl0 as [? [??]]; eauto.
          by simplify_multieq.
        }
      }

    - (* AI_basic (BI_store t (Some tp) a off) *)
      get_cc ccs. 
      destruct vs0 as [|v2 [|v1 vs0]]; try by no_args.
      assert_i32 v1.
      assert_value_num v2.
      destruct (typeof_num v2 == t) eqn:Heq; move/eqP in Heq; last by discriminate_value_type; apply num_subtyping in H; inversion H; subst.
      destruct op as [tp | ].
      (* packed *)
      + destruct (smem_store_packed s fc.(FC_frame).(f_inst) ($nou32 v1) off v2 tp) as [s' | ] eqn:Hsmem.
        * apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_store_packed_success; subst; eauto.
        * (* None *)
          apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_store_packed_failure; subst; eauto.
      (* None *)
      + destruct (smem_store s fc.(FC_frame).(f_inst) ($nou32 v1) off v2 t) as [s' | ] eqn:Hsmem.
        * apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_store_success; subst; eauto.
        * (* None *)
          apply <<hs, (s, (fc, lcs) :: ccs', (vs0, es0), Some AI_trap)>>.
          resolve_reduce_ctx vs0 es0.
          by eapply r_store_failure; subst; eauto.
          
    - (* AI_basic BI_memory_size *)
      get_cc ccs.    
      destruct (smem s fc.(FC_frame).(f_inst)) as [s_mem_s_j|] eqn:?.
      + (* Some j *)
        apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num (VAL_int32 ($u32oz (Z.of_N (mem_size (s_mem_s_j))))) :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by subst; eapply r_memory_size; eauto.
      + (* None *)
        resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        { eapply inst_typing_mem_lookup_inv in Hconjr as [? [Hextmt ?]]; eauto.
          unfold ext_mem_typing in Hextmt; remove_bools_options.
          by simplify_multieq.
        }
        { eapply inst_typing_mem_lookup_inv in Hconjr as [? [??]]; eauto.
          by simplify_multieq.
        }

    - (* AI_basic BI_memory_grow *)
      get_cc ccs.
      destruct vs0 as [|v vs0]; first by no_args.
      assert_i32 v.
      destruct (smem_grow s fc.(FC_frame).(f_inst) ($nou32 v)) as [[s' sz] | ] eqn:Hsmem.
      + (* Some mem'' *)
        apply <<hs, (s', (fc, lcs) :: ccs', (VAL_num (VAL_int32 ($u32oz (Z.of_N sz))) :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by subst; eapply r_memory_grow_success; eauto.
      + (* None *)
        apply <<hs, (s, (fc, lcs) :: ccs', (VAL_num (VAL_int32 int32_minus_one) :: vs0, es0), None)>>.
        resolve_reduce_ctx vs0 es0.
        by subst; eapply r_memory_grow_failure; eauto.

    - (* AI_basic BI_memory_fill *)
      get_cc ccs.
      destruct vs0 as [|v3 [|v2 [|v1 vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_i32 v3.
      assert_i32 v2.
      assert_i32 v1.
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
        unfold_frame_type Hftype.
        unfold_store_operations.
        { eapply inst_typing_mem_lookup_inv in Hconjr as [? [Hextmt ?]]; eauto.
          unfold ext_mem_typing in Hextmt; remove_bools_options.
          by simplify_multieq.
        }
        { eapply inst_typing_mem_lookup_inv in Hconjr as [? [??]]; eauto.
          by simplify_multieq.
        }
        
    - (* AI_basic BI_memory_copy *)
      get_cc ccs.
      destruct vs0 as [|n [|src [|dst vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_i32 n.
      assert_i32 src.
      assert_i32 dst.
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
        unfold_frame_type Hftype.
        unfold_store_operations.
        { eapply inst_typing_mem_lookup_inv in Hconjr as [? [Hextmt ?]]; eauto.
          unfold ext_mem_typing in Hextmt; remove_bools_options.
          by simplify_multieq.
        }
        { eapply inst_typing_mem_lookup_inv in Hconjr as [? [??]]; eauto.
          by simplify_multieq.
        }
        
    - (* AI_basic BI_memory_init *)
      get_cc ccs.
      destruct vs0 as [|n [|src [|dst vs0]]]; try by no_args.
      (* Takes i32; i32; i32 *)
      assert_i32 n.
      assert_i32 src.
      assert_i32 dst.
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
          unfold_frame_type Hftype.
          unfold_store_operations.
          { eapply inst_typing_data_lookup_inv in Hconjr0 as [? [? [? [??]]]]; eauto.
            by simplify_multieq.
          }
          { eapply inst_typing_data_lookup_inv in Hconjr0 as [? [? [? [??]]]]; eauto.
            by simplify_multieq.
          }

      + (* None *)
        resolve_invalid_typing.
        unfold_frame_type Hftype.
        unfold_store_operations.
        { eapply inst_typing_mem_lookup_inv in Hconjl0 as [? [Hextmt ?]]; eauto.
          unfold ext_mem_typing in Hextmt; remove_bools_options.
          by simplify_multieq.
        }
        { eapply inst_typing_mem_lookup_inv in Hconjl0 as [? [??]]; eauto.
          by simplify_multieq.
        }
          
    - (* AI_basic BI_data_drop x *)
      get_cc ccs.
      destruct (sdata_drop s fc.(FC_frame).(f_inst) x) as [s'|] eqn:Hs'.
      + apply <<hs, (s', (fc, lcs) :: ccs', (vs0, es0), None)>>.
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
          unfold_frame_type Hftype.
          erewrite <- inst_typing_expand_eq in Hconjl0; eauto. 
          rewrite Hconjl0 in Hexpand; injection Hexpand as <- <-.
          by discriminate_size.
      + (* None *)
        resolve_invalid_typing.
        unfold_frame_type Hftype.
        erewrite <- inst_typing_expand_eq in Hconjl0; eauto.
        by rewrite Hconjl0 in Hexpand.

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
          unfold_frame_type Hftype.
          erewrite <- inst_typing_expand_eq in Hconjl0; eauto.
          rewrite Hconjl0 in Hexpand; injection Hexpand as <- <-.
          by discriminate_size.
      + (* None *)
        resolve_invalid_typing.
        unfold_frame_type Hftype.
        erewrite <- inst_typing_expand_eq in Hconjl0; eauto.
        by rewrite Hconjl0 in Hexpand.
        
    - (* AI_basic (BI_if tb es1 es2) *)
      destruct vs0 as [|v vs0]; first by no_args.
      assert_i32 v.
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
      assert_i32 v.
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
      assert_i32 v.
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
        unfold_frame_type Hftype.
        eapply inst_typing_func_lookup_inv in Hconjr as [? [??]]; eauto.
        by simplify_multieq.

    - (* AI_basic (BI_call_indirect x y) *)
      get_cc ccs.
      destruct vs0 as [|v vs0]; first by no_args.
      assert_i32 v.
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
            unfold_frame_type Hftype.
            unfold_store_operations.
            resolve_store_inst_lookup.
            destruct t1; remove_bools_options; simpl in *.
            eapply all_projection in Hif1; eauto.
            unfold value_typing in Hif1; simpl in Hif1.
            unfold ext_func_typing in Hif1.
            by remove_bools_options.
        * (* externref *)
          resolve_invalid_typing.
          unfold_frame_type Hftype.
          unfold_store_operations.
          resolve_store_inst_lookup.
          destruct t1; remove_bools_options; simpl in *.
          eapply all_projection in Hif1; eauto.
          unfold value_typing in Hif1; simpl in *.
          simplify_multieq.
          apply ref_subtyping in Hif1.
          by rewrite Hconjl1 in Hif1.
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
          apply reduce_focus => //=.
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

(* reformation to a valid configuration, if possible.
   If the cfg is already a value, report that.
 *)
Definition run_step_cfg_ctx_reform (cfg: cfg_tuple_ctx) : option cfg_tuple_ctx.
Proof.
  destruct cfg as [[[s ccs] sc] oe].
  destruct (ctx_update ccs sc oe) as [[[ccs' sc'] oe'] | ] eqn:Hctxupdate; last by exact None.
  exact (Some (s, ccs', sc', oe')).
Defined.

Definition run_v_init (s: store_record) (es: list administrative_instruction) : option cfg_tuple_ctx :=
  match ctx_decompose es with
  | Some (ccs, sc, oe) => Some (s, ccs, sc, oe)
  | None => None
  end.

Definition run_v_init_with_frame (s: store_record) (f: frame) (n: nat) (es: list administrative_instruction) : option cfg_tuple_ctx :=
  run_v_init s [::AI_frame n f es].

Definition hs_cfg_ctx : Type := host_state * cfg_tuple_ctx.

Definition empty_store_record := Build_store_record nil nil nil nil nil nil.

(* TODO: include proofs *)
Fixpoint run_multi_step_ctx (fuel: nat) (hs: host_state) (cfg: cfg_tuple_ctx) : (option unit) + (list value) :=
  match fuel with
  | 0 => inl None
  | S n =>
      match run_one_step_ctx hs cfg with
      | RSC_normal hs' cfg' HReduce =>
          match run_step_cfg_ctx_reform cfg' with
          | Some cfg'' => run_multi_step_ctx n hs' cfg''
          | None => inl None
          end
      | RSC_value _ _ vs _ _ _ => inr vs
      | RSC_value_frame _ _ vs _ _ _ _ _ => inr vs
      | _ => inl None
      end
  end.

(** Auxiliary definition for running arbitrary expressions, not necessarily with a frame within the expression decomposition.
    Requires knowing about the number of return values beforehand (can be obtained from typing).
    Note that this function should *never* be used in the extracted code due to the inefficient
    usage of fuel. It is only used internally during module instantiation.
 **)

Definition run_multi_step_raw (hs: host_state) (fuel: nat) (s: store_record) (f: frame) (arity: nat) (es: list administrative_instruction): (option unit) + (list value) :=
  match run_v_init_with_frame s f arity es with
  | Some cfg => run_multi_step_ctx fuel hs cfg
  | None => inl None
  end.


Section Interp_ctx_progress.

(** A definition to what is considered a 'valid' tuple by the ctx interpreter.
    This constraint seems restrictive, but in fact all Wasm runtime configuration can be expressed in this form:
    the runtime configuration tuple (S; F; es) always has a frame F, which can be used to form the frame context
    [AI_frame n F es] (with the right choice of n).
 **)
Definition valid_wasm_instr (es: list administrative_instruction) : bool :=
  match es with
  | [::AI_frame _ _ _] => true
  | _ => false
  end.

(* Due to the representation of the outermost frame in the ctx interpreter, the
  terminal values are expanded to include an outermost frame  *)
Definition terminal_form_ctx (es: list administrative_instruction) : bool :=
  const_list es ||
  match es with
  | [:: AI_frame _ _ es'] => const_list es'
  | [:: AI_trap] => true
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
  destruct es as [| e es'] => //; destruct e, es' => //.
  rewrite ctx_decompose_aux_equation in Hdecomp; simpl in Hdecomp.
  by apply ctx_decompose_valid_ccs_aux in Hdecomp.
Qed.

(* Somewhat subsumed by the lemma below, although this might still be helpful
in places where typing term is not available *)
Lemma valid_instr_preserve (hs: host_state) s f es hs' s' f' es':
  reduce hs s f es hs' s' f' es' ->
  valid_wasm_instr es ->
  valid_wasm_instr es' \/ terminal_form_ctx es'.
Proof.
  move => Hred.
  induction Hred => //; subst; move => Hvalid; (try by left); (try by (right; (try by left); (try by right))).
  (* Simple *)
  - destruct e as [ | e es] => //; destruct e, es => //.
    + inversion H; subst; clear H; (try by destruct vs as [ | v vs] => //; destruct vs); (try by right => /=).
  - by right; unfold terminal_form_ctx; rewrite H4.
  - by right; unfold terminal_form_ctx; rewrite H3.
  (* Block *)
  - by destruct vs as [| v vs] => //; destruct v => //.
  (* Loop *)
  - by destruct vs as [| v vs] => //; destruct v => //.
  (* Host *)
  - right.
    destruct r => //=.
    unfold terminal_form_ctx; by rewrite v_to_e_const.
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

(* The induced progress for this version looks slightly weaker, as it only applies to valid instructions directly.
   However, every function call starts with a valid instruction and continues to be one until the call is exited 
   (preservation of valid instructions).
*)
Definition t_progress_interp_ctx: forall (hs: host_state) (s: store_record) es ts,
  valid_wasm_instr es ->
  config_typing s (empty_frame, es) ts ->
  terminal_form_ctx es \/
    (exists hs' s' es', reduce hs s empty_frame es hs' s' empty_frame es' /\
                     valid_wasm_instr es).
Proof.
  move => hs s es ts Hvalid Htype.
  destruct (run_v_init s es) as [[[[s0 ccs] sc] oe]|] eqn:Hinit; last by eapply valid_init_Some in Hvalid; apply Hvalid in Hinit.
  destruct es as [| e es] => //; destruct e, es => //.
  (* Frame *)
  { remember Hinit as Hinit2; clear HeqHinit2.
    unfold run_v_init in Hinit.
    rewrite /ctx_decompose ctx_decompose_aux_equation /= in Hinit.
    destruct (ctx_decompose_aux _) as [[[ccs' sc'] oe'] | ] eqn:Hdecomp => //; injection Hinit as <- -> -> ->.
    { remember (run_one_step_ctx hs (s, ccs, sc, oe)) as res.
      destruct res as [hs' [[[s' ccs'] sc'] oe'] Hred | hs0 s0 vs ? ? Heq | hs0 s0 vs n0 f0 ? ? Heq | Hcontra | Hcontra]; clear Heqres.
      1,2,3,5:
      unfold run_v_init in Hinit2; destruct (ctx_decompose _) as [[[ccs2 sc2] oe2]|] eqn:Hdecomp' => //;
      apply ctx_decompose_fill_id in Hdecomp';
      simpl in Hdecomp';
      injection Hinit2 as -> -> ->.
      - right.
        unfold reduce_ctx in Hred.
        simpl in *.
        rewrite Hdecomp' in Hred.
        repeat eexists. by eauto.
      - simpl in *.
        rewrite Hdecomp' in Heq.
        destruct vs as [ | v vs] => //; destruct v, vs => //; by destruct v.
      - simpl in *.
        rewrite Hdecomp' in Heq.
        injection Heq as -> -> ->.
        left; unfold terminal_form_ctx; by rewrite v_to_e_const.
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

#[export]
Instance host_instance : host.
Proof.
  by refine {|
      host_state := unit_eqType ;
      host_application _ _ _ _ _ _ _ := False
    |}.
Defined.

Definition host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                                   (host_state * option (store_record * result)).
Proof.
  move => ??? hf.
  by refine ((of_void _) hf).
Defined.

Definition host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).
Proof.
  move => ??? hf; by inversion hf.
Defined.

Definition cfg_tuple_ctx : Type := cfg_tuple_ctx.

Definition run_step_ctx_result : host_state -> cfg_tuple_ctx -> Type := run_step_ctx_result.

Definition run_one_step_ctx (hs: host_state) (cfg: cfg_tuple_ctx) : run_step_ctx_result hs cfg := run_one_step_ctx host_application_impl_correct hs cfg.

Definition run_step_cfg_ctx_reform : cfg_tuple_ctx -> option cfg_tuple_ctx := run_step_cfg_ctx_reform.

Definition run_v_init : store_record -> list administrative_instruction -> option cfg_tuple_ctx := run_v_init.

Definition run_v_init_with_frame : store_record -> frame -> nat -> list administrative_instruction -> option cfg_tuple_ctx := run_v_init_with_frame.

Definition run_multi_step_raw : host_state -> nat -> store_record -> frame -> nat -> list administrative_instruction -> (option unit) + (list value) := run_multi_step_raw host_application_impl_correct.

Definition es_of_cfg : cfg_tuple_ctx -> list administrative_instruction := es_of_cfg.

Definition s_of_cfg : cfg_tuple_ctx -> store_record := s_of_cfg.

End Interpreter_ctx_extract.

