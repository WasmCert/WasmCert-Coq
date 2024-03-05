(** Inductively defined contexts extract to code that run very poorly. This alternative defines an
    additional context stack to replace the inductive definition, since the evaluation context tree is
    always guaranteed to be linear. **)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program NArith ZArith Wf_nat.
From Wasm Require Export common operations datatypes_properties properties opsem typing_inversion tactic.
Require Import FunInd Recdef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section EvalContext.

Variable host_function: eqType.

Variable host_instance: host host_function.

#[local]
Definition reduce := @reduce host_function host_instance.

(* Typeclass for a Wasm evaluation context.
   ctx_frame_mask and ctx_frame_cond are auxiliary functions for defining
   the ctx_reduce relation, which instructs on how reductions of instructions
   within the hole could affect the configuration on the outer context (well, in
   principle they shouldn't do so in a normal language, but the frame reduction
   rule necessitates such a practice here).
*)
Class eval_ctx (ctx_t: Type): Type :=
  {
    ctx_fill: list administrative_instruction -> ctx_t -> list administrative_instruction;
    ctx_frame_mask: ctx_t -> frame -> frame;
    ctx_frame_cond: ctx_t -> frame -> frame -> Prop;
    ctx_reduce: forall (ctx: ctx_t) hs s f es hs' s' f' es',
      ctx_frame_cond ctx f f' ->
      reduce hs s (ctx_frame_mask ctx f) es hs' s' (ctx_frame_mask ctx f') es' ->
      reduce hs s f (ctx_fill es ctx) hs' s' f' (ctx_fill es' ctx);
  }.

End EvalContext.

Notation "ctx ⦃ es ⦄" := (ctx_fill es ctx) (at level 1).


Section Host.

Variable host_function: eqType.

Variable host_instance: host host_function.

Notation eval_ctx := (@eval_ctx host_function host_instance).


Definition fmask0 {T1 T2: Type} := (fun (_: T1) => @id T2).

Definition fcond0 {T1 T2 T3: Type} := (fun (_: T1) (_: T2) (_: T3) => True).

(* Sequence context: rev vs ++ [_] ++ es. This is only used in the base level *)
Definition seq_ctx : Type := (list value) * (list administrative_instruction).

#[refine, export]
Instance seq_ctx_eval : eval_ctx seq_ctx :=
  {| ctx_fill := (fun es ctx => (vs_to_es (fst ctx) ++ es ++ snd ctx)); ctx_frame_mask := fmask0; ctx_frame_cond := fcond0 |}.
Proof.
  move => ctx hs s f es hs' s' f' es' _ Hred.
  by eapply r_label with (lh := LH_base (rev (fst ctx)) (snd ctx)); eauto.
Defined.


(* Label context: rev LC_val ++ [::AI_label LC_arity LC_cont [_]) ++ LC_post; can be nested *)
Record label_ctx: Type :=
  { LC_val: list value;
    LC_arity: nat;
    LC_cont: list administrative_instruction;
    LC_post: list administrative_instruction;
  }.

Definition label_ctx_eq_dec (v1 v2 : label_ctx): {v1 = v2} + {v1 <> v2}.
Proof.
  by decidable_equality.
Qed.

Definition label_ctx_eqb (v1 v2: label_ctx) : bool := label_ctx_eq_dec v1 v2.
Definition eqlabel_ctx: Equality.axiom label_ctx_eqb :=
  eq_dec_Equality_axiom label_ctx_eq_dec.

Canonical Structure label_ctx_eqMixin := EqMixin eqlabel_ctx.
Canonical Structure label_ctx_eqType := Eval hnf in EqType label_ctx label_ctx_eqMixin.

Definition label_ctx_fill := (fun es ctx => (vs_to_es (LC_val ctx) ++ [::AI_label (LC_arity ctx) (LC_cont ctx) es] ++ (LC_post ctx))).

#[refine, export]
Instance label_ctx_eval: eval_ctx label_ctx :=
  {| ctx_fill := label_ctx_fill;
     ctx_frame_mask := fmask0; ctx_frame_cond := fcond0 |}.
Proof.
  move => [lvs lk lces les] hs s f es hs' s' f' es' _ Hred.
  eapply r_label with (lh := LH_rec (rev lvs) lk lces (LH_base nil nil) les); eauto => //; by rewrite /label_ctx_fill /= cats0.
Defined.


(* Frame context: rev FC_val ++ [::AI_local FC_arity FC_frame [_]) ++ FC_post *)
Record frame_ctx: Type :=
  { FC_val: list value;
    FC_arity: nat;
    FC_frame: frame;
    FC_post: list administrative_instruction;
  }.

Definition frame_ctx_eq_dec (v1 v2 : frame_ctx): {v1 = v2} + {v1 <> v2}.
Proof.
  by decidable_equality.
Qed.

Definition frame_ctx_eqb (v1 v2: frame_ctx) : bool := frame_ctx_eq_dec v1 v2.
Definition eqframe_ctx: Equality.axiom frame_ctx_eqb :=
  eq_dec_Equality_axiom frame_ctx_eq_dec.

Canonical Structure frame_ctx_eqMixin := EqMixin eqframe_ctx.
Canonical Structure frame_ctx_eqType := Eval hnf in EqType frame_ctx frame_ctx_eqMixin.

#[refine, export]
Instance frame_ctx_eval: eval_ctx frame_ctx :=
  {| ctx_fill := (fun es ctx => (vs_to_es (FC_val ctx) ++ [::AI_local (FC_arity ctx) (FC_frame ctx) es] ++ (FC_post ctx)));
    ctx_frame_mask := (fun ctx _ => ctx.(FC_frame));
    ctx_frame_cond := (fun _ f1 f2 => f1 = f2);
  |}.
Proof.
  move => [lvs lk lf les] hs s f es hs' s' f' es' /= <- Hred /=.
  eapply r_label with (lh := LH_base (rev lvs) les); eauto => //=; try by rewrite -cat1s.
  by apply r_local.
Defined.


(* A general instance for lists of evaluation contexts *)

Fixpoint ctx_frame_cond_list {T: Type} {ctx_p: eval_ctx T} (ctxs: list T) (f1 f2: frame): Prop :=
  match ctxs with
  | nil => True
  | ctx :: ctxs' =>
      ctx_p.(ctx_frame_cond) ctx (foldr ctx_p.(ctx_frame_mask) f1 ctxs') (foldr ctx_p.(ctx_frame_mask) f2 ctxs') /\
      ctx_frame_cond_list ctxs' f1 f2
  end.

#[refine, export]
Instance list_ctx_eval {T: Type} (ctx_p: eval_ctx T): eval_ctx (list T) :=
  {| ctx_fill := (fun es ctxs => foldl ctx_p.(ctx_fill) es ctxs);
    ctx_frame_mask := (fun ctxs f => foldr ctx_p.(ctx_frame_mask) f ctxs);
    ctx_frame_cond := ctx_frame_cond_list
  |}.
Proof.
  elim => //.
  move => ctx ctxs' IH hs s f es hs' s' f' es' /=[Hcond Hconds] /=Hred /=.
  apply ctx_p.(ctx_reduce) in Hred => //=.
  by apply IH in Hred => //=.
Defined.

  
Lemma ctx_frame_cond_list_label: forall (lcs: list label_ctx) f,
  ctx_frame_cond_list lcs f f.
Proof.
  by elim.
Qed.

Lemma ctx_frame_cond_list_frame: forall (lcs: list frame_ctx) f,
  ctx_frame_cond_list lcs f f.
Proof.
  by elim.
Qed.

Definition closure_ctx : Type := frame_ctx * list label_ctx.

Definition closure_ctx_fill es (cc: closure_ctx):=
  match cc with
  | (fc, lc) => fc ⦃ lc ⦃ es ⦄ ⦄
  end.

Lemma foldr_id {T1 T2: Type}: forall (l: list T1) (x: T2),
    foldr (fun _ => id) x l = x.
Proof.
  by elim.
Qed.
  
(* Simpler instances for label and frame contexts *)
#[refine, export]
Instance list_label_ctx_eval : eval_ctx (list label_ctx) :=
  {| ctx_fill := (@list_ctx_eval label_ctx _).(ctx_fill);
    ctx_frame_mask := fmask0;
    ctx_frame_cond := fcond0;
    |}.
Proof.
  elim => //.
  move => [lvs lk lces les] ctxs' IH hs s f es hs' s' f' es' _ Hred /=.
  rewrite /fmask0 in Hred.
  rewrite /label_ctx_fill /=.
  apply IH => //.
  rewrite /fmask0.
  eapply r_label with (lh := LH_rec (rev lvs) lk lces (LH_base nil nil) les); eauto => //; by rewrite /label_ctx_fill /= cats0.
Defined.

#[refine, export]
Instance list_frame_ctx_eval : eval_ctx (list frame_ctx) :=
  {| ctx_fill := (@list_ctx_eval frame_ctx _).(ctx_fill);
    ctx_frame_mask := (fun ctxs f0 =>
                         match ctxs with
                         | nil => f0
                         | ctx :: ctxs' => ctx.(FC_frame)
                         end);
    ctx_frame_cond := (fun _ f1 f2 => f1 = f2);
    |}.
Proof.
  case => //.
  move => ctx ctxs'; move: ctxs' ctx.
  elim => //.
  - move => [lvs lk lf les] hs s f es hs' s' f' es' <- /=Hred /=.
    eapply r_label with (lh := LH_base (rev lvs) les); eauto => //=; try by rewrite -cat1s.
    by apply r_local.
  - move => ctx ctxs' IH [lvs lk lf les] hs s f es hs' s' f' es' <- /=Hred.
    apply IH => //=.
    eapply r_label with (lh := LH_base (rev lvs) les); eauto => //=; try by rewrite -cat1s.
    by apply r_local.
Defined.

#[refine, export]
Instance closure_ctx_eval: eval_ctx closure_ctx :=
  {| ctx_fill := closure_ctx_fill;
     ctx_frame_mask := (fun '(fc, lc) _ => fc.(FC_frame));
     ctx_frame_cond := (fun _ f1 f2 => f1 = f2);
  |}.
Proof.
  move => [fc lcs] hs s f es hs' s' f' es' <- Hred.
  apply ctx_reduce => //.
  by apply list_label_ctx_eval.(ctx_reduce) => //. 
Defined.

#[refine, export]
Instance list_closure_ctx_eval : eval_ctx (list closure_ctx) :=
  {| ctx_fill := (@list_ctx_eval closure_ctx _).(ctx_fill);
    ctx_frame_mask := (fun ctxs f0 =>
                         match ctxs with
                         | nil => f0
                         | (fc, lcs) :: ctxs' => fc.(FC_frame)
                         end);
    ctx_frame_cond := (fun _ f1 f2 => f1 = f2);
    |}.
Proof.
  case => //.
  move => ctx ctxs'; move: ctxs' ctx.
  elim => //.
  - move => [[lvs lk lf les] lcs] hs s f es hs' s' f' es' <- /=Hred /=.
    eapply r_label with (lh := LH_base (rev lvs) les); eauto => //=; try by rewrite -cat1s.
    apply r_local.
    by apply (list_label_ctx_eval.(ctx_reduce)).
  - move => ctx ctxs' IH [[lvs lk lf les] lcs] hs s f es hs' s' f' es' <- /=Hred.
    apply IH => //=.
    eapply r_label with (lh := LH_base (rev lvs) les); eauto => //=; try by rewrite -cat1s.
    apply r_local.
    by apply (list_label_ctx_eval.(ctx_reduce)).
Defined.

(* A configuration is now represented as (S; ctxs ⦃ sc ⦃ option e ⦄ ⦄), with the hole holding at most one instruction which needs to be non-constant.
   Note that no frame is held in the tuple, since all frames should have been pushed into the local contexts.
   The contexts are represented in a reversed stack-like structure: the head of each list is the innermost context.
   The hole is allowed to be empty (in which case the inner context is then exitted on the next step). However, the sequence context sc should not hold any
   non-empty instruction in the continuation. *)
Definition cfg_tuple_ctx: Type := (store_record host_function) * list closure_ctx * seq_ctx * option administrative_instruction.

Definition valid_hole (e: administrative_instruction) : bool :=
  match e with
  | AI_label _ _ _ => false
  | AI_local _ _ _ => false
  | AI_basic (BI_const _) => false
  | _ => true
  end.

Definition valid_split (sc: seq_ctx) oe: bool :=
  match oe with
  | Some e => valid_hole e
  | None => snd sc == nil
  end.

Definition oe_noframe (oe: option administrative_instruction) :=
  match oe with
  | None
  | Some (AI_invoke _) => true
  | _ => false
  end.

Definition valid_ccs (ccs: list closure_ctx) (oe: option administrative_instruction): bool :=
  (ccs != nil) || (oe_noframe oe).

(* The canonical form of a context config tuple: 
   - The ves split has to be valid;
   - The closure can only be empty if the entire instruction is already a value.
*)
Definition valid_cfg_ctx (cfg: cfg_tuple_ctx) : Prop :=
  match cfg with
  | (_, cc, sc, oe) =>
      valid_ccs cc oe /\ valid_split sc oe
  end.

Definition olist {T: Type} (ot: option T) : list T :=
  match ot with
  | Some t => [::t]
  | None => nil
  end.

Fixpoint ai_measure (e: administrative_instruction) : nat :=
  match e with
  | AI_label _ _ es => 1 + List.list_sum (map ai_measure es)
  | AI_local _ _ es => 1 + List.list_sum (map ai_measure es)
  | _ => 1
  end.

Definition ais_measure (LI: list administrative_instruction) : nat :=
  List.list_sum (map ai_measure LI).

Lemma ais_measure_cat: forall l1 l2,
    ais_measure (l1 ++ l2) = ais_measure l1 + ais_measure l2.
Proof.
  move => l1 l2.
  unfold ais_measure.
  by rewrite map_cat cat_app List.list_sum_app.
Qed.

Lemma ais_measure_cons: forall x l,
    ais_measure (x :: l) = ai_measure x + ais_measure l.
Proof.
  done.
Qed.

Definition empty_instance := Build_instance nil nil nil nil nil.

Definition empty_frame := Build_frame nil empty_instance.

(* Placeholder so that ctx_decompose can be useful for instructions without the outer frame, although not the
   intended purpose *)
Definition empty_frame_ctx := Build_frame_ctx nil 0 empty_frame nil.

(* Tail recursive version of split_vals_e, also producing the reversed vs list used in the contexts *)
Fixpoint split_vals'_aux (ves: list administrative_instruction) (acc: list value) : (list value) * (list administrative_instruction) :=
  match ves with
  | nil => (acc, nil)
  | e :: ves' =>
      match e_to_v_opt e with
      | Some v => split_vals'_aux ves' (v :: acc)
      | None => (acc, ves)
      end
  end.

Definition split_vals' ves := split_vals'_aux ves nil.

Lemma split_vals'_aux_impl: forall ves acc vs es,
    split_vals'_aux ves acc = (vs, es) ->
    (exists vs0, split_vals_e ves = (vs0, es) /\ vs = rev vs0 ++ acc).
Proof.
  elim => /=.
  - move => acc vs es.
    + move => [<- <-]; by eexists; split.
  - move => e ves' IH acc vs es.
    destruct (e_to_v_opt e) as [v |] eqn:Hetov.
    + destruct e as [b | | | | |] => //; destruct b => //=.
      simpl in Hetov; injection Hetov as ->; move => /= Hsplit.
      apply IH in Hsplit as [vs0 [-> ->]].
      eexists; split => //=.
      by rewrite rev_cons -cats1 -catA cat1s.
    + move => [<- <-].
      exists nil.
      split => //.
      destruct e as [b | | | | |] => //; by destruct b.
Qed.

Lemma split_vals'_aux_spec: forall ves acc vs es vs0,
    split_vals_e ves = (vs0, es) ->
    vs = rev vs0 ++ acc ->
    split_vals'_aux ves acc = (vs, es).
Proof.
  elim => /=.
  - by move => acc vs es vs0 [<- <-] ->.
  - move => e ves' IH acc vs es vs0 Heq ->.
    destruct (split_vals_e ves') as [vs' es'] eqn:Hsplit.
    destruct (e_to_v_opt e) as [v | ] eqn:Hetov.
    + destruct e as [b | | | | |] => //; destruct b => //=.
      simpl in Hetov; injection Hetov as ->.
      injection Heq as <- <-.
      erewrite IH; eauto.
      by rewrite rev_cons -cats1 -catA cat1s.
    + destruct e as [b | | | | |]; first (destruct b); by injection Heq as <- <-.
Qed.

Lemma split_vals'_spec: forall ves vs es,
    split_vals' ves = (vs, es) <->
    split_vals_e ves = (rev vs, es).
Proof.
  move => ves vs es.
  split; move => Hsplit.
  - apply split_vals'_aux_impl in Hsplit as [vs0 [Hsplit ->]].
    by rewrite Hsplit cats0 revK.
  - eapply split_vals'_aux_spec; eauto.
    by rewrite cats0 revK.
Qed.

Function ctx_decompose_aux (ves_acc: (list administrative_instruction) * (list closure_ctx)) {measure (fun '(ves, acc) => ais_measure ves)} : option (list closure_ctx * seq_ctx * option administrative_instruction) :=
  let '(ves, acc) := ves_acc in
  match split_vals' ves with
  | (vs, es) =>
      match es with
      | nil => Some (acc, (vs, nil), None)
      | e :: es' =>
          match e with
          | AI_label k ces es =>
              match acc with
              | nil => None
              | (fc, lcs) :: ccs' => ctx_decompose_aux (es, (fc, (Build_label_ctx vs k ces es') :: lcs) :: ccs')
              end
          | AI_local k f es =>
              ctx_decompose_aux (es, (Build_frame_ctx vs k f es', nil) :: acc)
          | _ => (* In this case, we know that e cannot be const due to a lemma *)
              Some (acc, (vs, es'), Some e)
          end
      end
  end.
Proof.
  { move => [ves acc] ves' acc' vs ? e es' k ces es ?? Hsplit cc ccs fc lcs ?? [? ?]; subst.
    apply split_vals'_spec, split_vals_inv in Hsplit as ->.
    rewrite ais_measure_cat ais_measure_cons /ais_measure => /=.
    by lias.
  }
  { move => [ves acc] ves' acc' [? ?] vs ? e es' k f ??? Hsplit; subst.
    apply split_vals'_spec, split_vals_inv in Hsplit as ->.
    rewrite ais_measure_cat ais_measure_cons /ais_measure => /=.
    by lias.
  }
Defined.

Definition ctx_decompose ves := ctx_decompose_aux (ves, nil).

Definition e_is_label e :=
  match e with
  | AI_label _ _ _ => true
  | _ => false
  end.

Lemma ctx_decompose_aux_none_impl: forall ves acc,
    ctx_decompose_aux (ves, acc) = None ->
    acc = nil /\ exists vs e es, split_vals' ves = (vs, e :: es) /\ e_is_label e.
Proof.
  move => ves.
  remember (ais_measure ves) as m.
  move: Heqm.
  move: ves.
  induction m as [m' IH] using (lt_wf_ind).
  move => ves ? acc Hdecomp; subst m'.
  rewrite ctx_decompose_aux_equation in Hdecomp.
  destruct (split_vals' ves) as [vs es] eqn:Hsplit.
  apply split_vals'_spec, split_vals_inv in Hsplit as ->.
  destruct es as [ | e es'] => //.
  destruct e => //.
  (* Label *)
  - destruct acc as [ | [fc lcs] ccs'] => //.
    split => //.
    by repeat eexists.
  - eapply IH in Hdecomp as [Hcontra ?]; eauto; first by inversion Hcontra.
    by rewrite ais_measure_cat ais_measure_cons /ais_measure => /=; lias.
  - eapply IH in Hdecomp as [Hcontra ?]; eauto; first by inversion Hcontra.
    by rewrite ais_measure_cat ais_measure_cons /ais_measure => /=; lias.
Qed.

Lemma ctx_decompose_acc_some: forall ves acc,
    acc <> nil ->
    ctx_decompose_aux (ves, acc) <> None.
Proof.
  move => ves acc Hnil Hcontra.
  by apply ctx_decompose_aux_none_impl in Hcontra as [-> ?].
Qed.

(* Auxiliary definitions for maintaining the canonical decomposition during execution. These avoid the need to
   invoke split_vals again unless the hole itself is a const *)
Definition ctx_update_nconst (acc: list closure_ctx) (sctx: seq_ctx) e :=
  let '(vs, es0) := sctx in
  match e with
  | AI_label k ces es =>
      match acc with
      | nil => None 
      | (fc, lcs) :: ccs' => ctx_decompose_aux (es, (fc, (Build_label_ctx vs k ces es0) :: lcs) :: ccs')
      end
  | AI_local k f es =>
      ctx_decompose_aux (es, (Build_frame_ctx vs k f es0, nil) :: acc)
  | _ => Some (acc, (vs, es0), Some e)
  end.

Definition ctx_update (acc: list closure_ctx) (sctx: seq_ctx) (oe: option administrative_instruction) :=
  match oe with
  | Some e =>
      match e_to_v_opt e with
      | Some v =>
          let '(vs, es) := sctx in
          let '(vs', es') := split_vals' es in
          match es' with
          | nil => Some (acc, (vs' ++ [::v] ++ vs, nil), None)
          | e' :: es'' => ctx_update_nconst acc (vs' ++ [::v] ++ vs, es'') e'
          end
      | None => ctx_update_nconst acc sctx e
      end
  | None =>
      let '(vs, es) := sctx in
      let '(vs', es') := split_vals' es in
      match es' with
      | nil => Some (acc, (vs' ++ vs, nil), None)
      | e' :: es'' => ctx_update_nconst acc (vs' ++ vs, es'') e'
      end
  end.

Lemma ctx_decompose_valid_ccs_aux: forall ves acc ccs sctx oe,
    acc != nil ->
    ctx_decompose_aux (ves, acc) = Some (ccs, sctx, oe) ->
    valid_ccs ccs oe.
Proof.
  move => ves.
  remember (ais_measure ves) as m.
  move: Heqm.
  move: ves.
  induction m as [m' IH] using (lt_wf_ind).
  move => ves ? acc ccs sctx oe Hnil Hdecomp; subst m'.
  rewrite ctx_decompose_aux_equation in Hdecomp.
  destruct (split_vals' ves) as [vs es] eqn:Hsplit.
  apply split_vals'_spec in Hsplit.
  destruct es as [ | e es']; first by injection Hdecomp as <- <- <-; unfold valid_ccs; apply/orP; right.
  destruct e as
    [ b
    |
    |
    | addr
    | n ces es
    | n f es
    ]; simpl in *; try by (injection Hdecomp as <- <- <-; unfold valid_ccs; apply/orP; left).
  - destruct acc as [ | [fc lcs] ccs'] => //.
    eapply IH in Hdecomp; eauto; apply split_vals_inv in Hsplit as ->.
    by rewrite ais_measure_cat ais_measure_cons /ais_measure => /=; lias.
  - eapply IH in Hdecomp; eauto; apply split_vals_inv in Hsplit as ->.
    by rewrite ais_measure_cat ais_measure_cons /ais_measure => /=; lias.
Qed.

Lemma ctx_decompose_valid_aux: forall ves acc ccs sctx oe,
    ctx_decompose_aux (ves, acc) = Some (ccs, sctx, oe) ->
    valid_split sctx oe.
Proof.
  move => ves.
  remember (ais_measure ves) as m.
  move: Heqm.
  move: ves.
  induction m as [m' IH] using (lt_wf_ind).
  move => ves ? acc ccs sctx oe Hdecomp; subst m'.
  rewrite ctx_decompose_aux_equation in Hdecomp.
  destruct (split_vals' ves) as [vs es] eqn:Hsplit.
  apply split_vals'_spec in Hsplit.
  destruct es as [ | e es']; first by injection Hdecomp as <- <- <-.
  destruct e as
    [ b
    |
    |
    | addr
    | n ces es
    | n f es
    ]; simpl in *; try by injection Hdecomp as <- <- <-.
  - injection Hdecomp as <- <- <- => /=.
    apply split_vals_nconst in Hsplit.
    by destruct b.
  - destruct acc as [ | [fc lcs] ccs'] => //.
    eapply IH in Hdecomp; eauto; apply split_vals_inv in Hsplit as ->.
    by rewrite ais_measure_cat ais_measure_cons /ais_measure => /=; lias.
  - eapply IH in Hdecomp; eauto; apply split_vals_inv in Hsplit as ->.
    by rewrite ais_measure_cat ais_measure_cons /ais_measure => /=; lias.
Qed.

Lemma ctx_decompose_valid_split: forall ves ccs sctx oe,
    ctx_decompose ves = Some (ccs, sctx, oe) ->
    valid_split sctx oe.
Proof.
  intros.
  by eapply ctx_decompose_valid_aux; eauto.
Qed.

Lemma ctx_update_nconst_valid_ccs: forall sctx e ccs ccs' sctx' oe,
    ccs != nil ->
    ctx_update_nconst ccs sctx e = Some (ccs', sctx', oe) ->
    valid_ccs ccs' oe.
Proof.
  move => [vs es] e ccs ccs' [vs' es'] oe Hnil Hupdate.
  unfold ctx_update_nconst in Hupdate; unfold valid_ccs.
  destruct e; first destruct b; try (injection Hupdate as <- <- <-; subst => //); try (by apply/orP; left).
  (* Label *)
  - destruct ccs as [ | [fc lcs] ccs0] => //.
    by eapply ctx_decompose_valid_ccs_aux in Hupdate; eauto.
  - by eapply ctx_decompose_valid_ccs_aux in Hupdate; eauto.
Qed.
  
Lemma ctx_update_nconst_valid: forall sctx e ccs ccs' sctx' oe,
    ~ is_const e ->
    ctx_update_nconst ccs sctx e = Some (ccs', sctx', oe) ->
    valid_split sctx' oe.
Proof.
  move => [vs es] e ccs ccs' [vs' es'] oe Hnconst Hupdate.
  unfold ctx_update_nconst in Hupdate.
  destruct e; try injection Hupdate as <- <- <-; subst => //; try by destruct b.
  (* Label *)
  - destruct ccs as [ | [fc lcs] ccs0] => //.
    by apply ctx_decompose_valid_aux in Hupdate.
  (* Local *)
  -  by apply ctx_decompose_valid_aux in Hupdate.
Qed.

Lemma ctx_update_valid_ccs: forall sctx ccs ccs' sctx' oe oe',
    ccs != nil ->
    ctx_update ccs sctx oe = Some (ccs', sctx', oe') ->
    valid_ccs ccs' oe'.
Proof.
  move => [vs es] ccs ccs' [vs' es'] oe oe' Hnil Hupdate.
  unfold ctx_update in Hupdate; unfold valid_ccs.
  destruct oe as [e | ].
  - destruct (e_to_v_opt e) as [v | ] eqn:Hetov.
    + destruct (split_vals' es) as [vs'' es''] eqn:Hsplit.
      destruct es'' as [ | e0 es'']; try by injection Hupdate as <- <- <-; subst => //; apply/orP; left.
      apply split_vals'_spec, split_vals_nconst in Hsplit.
      by apply ctx_update_nconst_valid_ccs in Hupdate => //.
    + by apply ctx_update_nconst_valid_ccs in Hupdate => //.
  - destruct (split_vals' es) as [vs'' es''] eqn:Hsplit.
    destruct es'' as [ | e0 es'']; try by injection Hupdate as <- <- <-; subst => //; apply/orP; left.
    apply split_vals'_spec, split_vals_nconst in Hsplit.
    by apply ctx_update_nconst_valid_ccs in Hupdate => //.
Qed.

Lemma ctx_update_valid: forall sctx ccs ccs' sctx' oe oe',
    ctx_update ccs sctx oe = Some (ccs', sctx', oe') ->
    valid_split sctx' oe'.
Proof.
  move => [vs es] ccs ccs' [vs' es'] oe oe' Hupdate.
  unfold ctx_update in Hupdate.
  destruct oe as [e | ].
  - destruct (e_to_v_opt e) as [v | ] eqn:Hetov.
    + destruct (split_vals' es) as [vs'' es''] eqn:Hsplit.
      destruct es'' as [ | e0 es'']; try by injection Hupdate as <- <- <-; subst => //.
      apply split_vals'_spec, split_vals_nconst in Hsplit.
      by apply ctx_update_nconst_valid in Hupdate => //.
    + apply ctx_update_nconst_valid in Hupdate => //.
      by destruct e => //; destruct b.
  - destruct (split_vals' es) as [vs'' es''] eqn:Hsplit.
    destruct es'' as [ | e0 es'']; try by injection Hupdate as <- <- <-; subst => //.
    apply split_vals'_spec, split_vals_nconst in Hsplit.
    by apply ctx_update_nconst_valid in Hupdate => //.
Qed.

Lemma ctx_decompose_fill_aux: forall ves acc ccs sctx oe,
    ctx_decompose_aux (ves, acc) = Some (ccs, sctx, oe) ->
    ccs ⦃ sctx ⦃ olist oe ⦄ ⦄ = acc ⦃ ves ⦄.
Proof.
  move => ves.
  remember (ais_measure ves) as m.
  move: Heqm.
  move: ves.
  induction m as [m' IH] using (lt_wf_ind).
  move => ves ? acc ccs sctx oe Hdecomp; subst m'.
  rewrite ctx_decompose_aux_equation in Hdecomp.
  destruct (split_vals' ves) as [vs es] eqn:Hsplit.
  apply split_vals'_spec in Hsplit.
  destruct es as [ | e es'].
  - injection Hdecomp as <- <- <- => //=.
    by apply split_vals_inv in Hsplit as ->.
  - destruct e as
      [ b
      |
      |
      | addr
      | n ces es
      | n f es
      ]; simpl in *; try by injection Hdecomp as <- <- <- => /=; apply split_vals_inv in Hsplit as ->.
    (* Label *)
    + destruct acc as [ | [fc lcs] ccs']; first by inversion Hdecomp => /=.
      eapply IH in Hdecomp; eauto; apply split_vals_inv in Hsplit as ->; first by rewrite Hdecomp.
      by rewrite ais_measure_cat ais_measure_cons /ais_measure => /=; lias.
    (* Local *)
    + eapply IH in Hdecomp; eauto; apply split_vals_inv in Hsplit as ->; first by rewrite Hdecomp.
      by rewrite ais_measure_cat ais_measure_cons /ais_measure => /=; lias.
Qed.

Lemma ctx_decompose_fill_id: forall ves ccs sctx oe,
    ctx_decompose ves = Some (ccs, sctx, oe) ->
    ccs ⦃ sctx ⦃ olist oe ⦄ ⦄ = ves.
Proof.
  move => ves ccs sctx oe Hdecomp.
  by apply ctx_decompose_fill_aux in Hdecomp.
Qed.

Lemma ctx_update_nconst_fill: forall sctx e ccs ccs' sctx' oe,
    ctx_update_nconst ccs sctx e = Some (ccs', sctx', oe) ->
    ccs ⦃ sctx ⦃ [::e] ⦄ ⦄ = ccs' ⦃ sctx' ⦃ olist oe ⦄ ⦄.
Proof.
  move => [vs es] e ccs ccs' [vs' es'] oe Hupdate.
  unfold ctx_update_nconst in Hupdate.
  destruct e => //; try by injection Hupdate as <- <- <-; subst.
  (* Local *)
  - destruct ccs as [ | [fc lcs] ccs0] => //.
    by apply ctx_decompose_fill_aux in Hupdate.
  - by apply ctx_decompose_fill_aux in Hupdate.
Qed.
  
Lemma ctx_update_fill: forall sctx ccs ccs' sctx' oe oe',
    ctx_update ccs sctx oe = Some (ccs', sctx', oe') ->
    ccs ⦃ sctx ⦃ olist oe ⦄ ⦄ = ccs' ⦃ sctx' ⦃ olist oe' ⦄ ⦄.
Proof.
  move => [vs es] ccs ccs' [vs' es'] oe oe' Hupdate.
  unfold ctx_update in Hupdate.
  destruct oe as [e | ].
  { destruct (e_to_v_opt e) as [v | ] eqn:Hetov; last by apply ctx_update_nconst_fill in Hupdate.
    destruct (split_vals' es) as [vs0 es0] eqn:Hsplit.
    apply split_vals'_spec, split_vals_inv in Hsplit as ->.
    destruct es0.
    - injection Hupdate as <- <- <-; subst; rewrite cats0 => //.
      destruct e => //; destruct b => //; simpl in Hetov; injection Hetov as -> => /=.
      f_equal.
      rewrite cats0 /vs_to_es rev_cat rev_cons -cats1 -catA.
      by repeat rewrite -v_to_e_cat.
    - destruct e => //; destruct b => //; simpl in Hetov; injection Hetov as ->.
      apply ctx_update_nconst_fill in Hupdate.
      rewrite - Hupdate => /=.
      f_equal.
      rewrite /vs_to_es rev_cat rev_cons -cats1 -catA.
      repeat rewrite -v_to_e_cat.
      by rewrite -catA.
  }
  {
    destruct (split_vals' es) as [vs0 es0] eqn:Hsplit.
    apply split_vals'_spec, split_vals_inv in Hsplit as ->.
    destruct es0 as [ | e es0].
    - injection Hupdate as <- <- <-; subst; rewrite cats0 => //=.
      f_equal.
      by rewrite cats0 /vs_to_es rev_cat -v_to_e_cat.
    - apply ctx_update_nconst_fill in Hupdate.
      rewrite - Hupdate => /=.
      f_equal.
      by rewrite /vs_to_es rev_cat -v_to_e_cat -catA.
  }
Qed.

(** conversion between lholed and contexts **)

Fixpoint lh_to_ctx_aux {k} (lh: lholed k) (acc: list label_ctx): seq_ctx * (list label_ctx) :=
  match lh with
  | LH_base vs es => ((rev vs, es), acc)
  | @LH_rec _ vs k ces lh' es => lh_to_ctx_aux lh' ((Build_label_ctx (rev vs) k ces es) :: acc)
  end.

Definition lh_to_ctx {k} (lh: lholed k) :=
  lh_to_ctx_aux lh nil.

(* It's better to express the result as a sigma type for better computation. *)
Fixpoint ctx_to_lh_aux {k} (lcs: list label_ctx) (acc: lholed k): {j & lholed j}.
Proof.
  destruct lcs as [ | [lvs lk lces les]].
  - exists k; by exact acc.
  - exact (ctx_to_lh_aux (S k) lcs (LH_rec (rev lvs) lk lces acc les)).
Defined.

Definition ctx_to_lh (sc: seq_ctx) (lcs: list label_ctx) : {j & lholed j} :=
  ctx_to_lh_aux lcs (LH_base (rev sc.1) sc.2).

Lemma ctx_to_lh_aux_len: forall lcs k (acc: lholed k),
    projT1 (ctx_to_lh_aux lcs acc) = k + length lcs.
Proof.
  induction lcs as [ | [lvs lk lces les]]; move => k acc => //=; first by rewrite addn0.
  by rewrite IHlcs; lias.
Qed.

Lemma ctx_to_lh_len: forall sc lcs,
    projT1 (ctx_to_lh sc lcs) = length lcs.
Proof.
  move => sc lcs.
  by apply ctx_to_lh_aux_len.
Qed.

Lemma lh_ctx_fill_aux: forall lcs k (acc: lholed k) es lf,
    lcs ⦃ (lfill acc es) ⦄ = lf ->
    lfill (projT2 (ctx_to_lh_aux lcs acc)) es = lf.
Proof.
  induction lcs as [ | [lvs lk lces les]]; move => k acc es lf Hctxfill => /=; first done.
  apply IHlcs; simpl in *.
  by apply Hctxfill.
Qed.

Lemma lh_ctx_fill: forall lcs es lf,
    lcs ⦃ es ⦄ = lf ->
    lfill (projT2 (ctx_to_lh (nil, nil) lcs)) es = lf.
Proof.
  intros lcs es lf Hctx.
  by apply lh_ctx_fill_aux with (acc := LH_base nil nil) => /=; rewrite cats0.
Qed.

(** context reduction lemmas **)

Let reduce := @reduce host_function host_instance.

Lemma reduce_focus_ctx: forall hs s lcs ccs es hs' s' lcs' es' f0 fc fc',
    fc.(FC_val) = fc'.(FC_val) ->
    fc.(FC_post) = fc'.(FC_post) ->
    fc.(FC_arity) = fc'.(FC_arity) ->
    reduce hs s fc.(FC_frame) (lcs ⦃ es ⦄) hs' s' fc'.(FC_frame) (lcs' ⦃ es' ⦄) ->
    reduce hs s f0 (((fc, lcs) :: ccs) ⦃ es ⦄) hs' s' f0 (((fc', lcs') :: ccs) ⦃ es' ⦄).
Proof.
  intros ???????????? Heqval Heqpost Heqarity => /=.
  rewrite - Heqpost -Heqval -Heqarity.
  move => Hred.
  apply (list_closure_ctx_eval.(ctx_reduce)) with (hs := hs) => //.
  eapply r_label with (lh := LH_base (rev (FC_val fc)) (FC_post fc)) => /=; try by (f_equal; rewrite -cat1s; eauto).
  by apply r_local.
Qed.

Lemma reduce_focus_ctx_id: forall hs s lcs ccs es hs' s' es' f0 fc fc',
    fc.(FC_val) = fc'.(FC_val) ->
    fc.(FC_post) = fc'.(FC_post) ->
    fc.(FC_arity) = fc'.(FC_arity) ->
    reduce hs s fc.(FC_frame) es hs' s' fc'.(FC_frame) es' ->
    reduce hs s f0 (((fc, lcs) :: ccs) ⦃ es ⦄) hs' s' f0 (((fc', lcs) :: ccs) ⦃ es' ⦄).
Proof.
  intros ??????????? Heqval Heqpost Heqarity Hred.
  apply reduce_focus_ctx => //.
  by apply (list_label_ctx_eval.(ctx_reduce)).
Qed.


(** Typing propagations for contexts **)
Section Typing.

Let e_typing := @e_typing host_function.
Let inst_typing := @inst_typing host_function.
Let frame_typing := @frame_typing host_function.

Ltac invert_e_typing' :=
  unfold e_typing in *; invert_e_typing.

Lemma fc_typing: forall (fc: frame_ctx) es s C0 tf,
    e_typing s C0 (fc ⦃ es ⦄) tf ->
    exists C ret,
      frame_typing s fc.(FC_frame) C /\
        length ret = fc.(FC_arity) /\
        e_typing s (upd_return C (Some ret)) es (Tf nil ret).
Proof.
  move => fc es s C [ts1 ts2] /= Htype.
  rewrite - cat1s in Htype.
  invert_e_typing'.
  inversion H2_local as [??????? Hftype ? Hetype]; subst; clear H2_local.
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
  unfold label_ctx_fill in Htype.
  invert_e_typing'.
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
    exists ts2, e_typing s C es (Tf (map typeof (rev sc.1)) ts2).
Proof.
  move => [vs0 es0] es s C ts0 /=Htype.
  invert_e_typing'.
  apply et_to_bet in H1_comp; last by apply const_list_is_basic, v_to_e_const.
  apply Const_list_typing in H1_comp as ->.
  simpl in *.
  by exists ts3_comp0.
Qed.

Lemma e_typing_ops: forall (ccs: list closure_ctx) (sc: seq_ctx) es s C0 ts0,
    e_typing s C0 (ccs ⦃ sc ⦃ es ⦄ ⦄) (Tf nil ts0) ->
    exists C' ts, e_typing s C' es (Tf (map typeof (rev sc.1)) ts).
Proof.
  move => ccs [vs0 es0] es s C0 ts0.
  destruct ccs as [ | cc' ccs']; move => Htype.
  - apply sc_typing_args in Htype as [? Htype].
    by do 2 eexists; eauto.
  - apply ccs_typing_exists in Htype as [? [? [? [? [? [? Htype]]]]]].
    apply sc_typing_args in Htype as [? Htype].
    by do 2 eexists; eauto.
Qed.

Lemma e_typing_ops_local: forall cc (ccs: list closure_ctx) (sc: seq_ctx) es s C0 tf,
    e_typing s C0 ((cc :: ccs) ⦃ sc ⦃ es ⦄ ⦄) tf ->
    exists C C' ret labs ts,
      frame_typing s (cc.1).(FC_frame) C /\
        length ret = (cc.1).(FC_arity) /\
        C' = (upd_label (upd_return C (Some ret)) labs) /\
        e_typing s C' es (Tf (map typeof (rev sc.1)) ts).
Proof.
  move => cc ccs [vs0 es0] es s C0 tf Htype.
  - apply ccs_typing_exists in Htype as [? [? [? [? [? [? Htype]]]]]].
    apply sc_typing_args in Htype as [? Htype].
    by do 6 eexists; eauto.
Qed.

End Typing.

End Host.
