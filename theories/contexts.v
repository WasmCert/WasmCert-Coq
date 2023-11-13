(** Inductively defined contexts extract to code that run very poorly. This alternative defines an
    additional context stack to replace the inductive definition, since the evaluation context tree is
    always guaranteed to be linear. **)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program NArith ZArith Wf_nat.
From Wasm Require Export common operations datatypes_properties properties opsem.
Require Import FunInd Recdef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module EvalContext.

Parameter host_function: eqType.

Parameter host_instance: host host_function.

#[local]
Definition reduce := @reduce host_function host_instance.

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

Notation "ctx ⦃ es ⦄" := (ctx_fill es ctx) (at level 1).

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

Definition label_ctx_fill := (fun es ctx => (vs_to_es (LC_val ctx) ++ [::AI_label (LC_arity ctx) (LC_cont ctx) es] ++ (LC_post ctx))).

#[refine, export]
Instance label_ctx_eval: eval_ctx label_ctx :=
  {| ctx_fill := label_ctx_fill; ctx_frame_mask := fmask0; ctx_frame_cond := fcond0 |}.
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

Fixpoint ctx_frame_cond_list {T: Type} {ctx_p: eval_ctx T} (ctxs: list T) (f1 f2: frame): Prop :=
  match ctxs with
  | nil => True
  | ctx :: ctxs' =>
      ctx_p.(ctx_frame_cond) ctx (foldr ctx_p.(ctx_frame_mask) f1 ctxs') (foldr ctx_p.(ctx_frame_mask) f2 ctxs') /\
      ctx_frame_cond_list ctxs' f1 f2
  end.

(* A general instance for lists of evaluation contexts *)
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
  apply (@ctx_reduce _ _ fc) => //.
  apply (@ctx_reduce _ _ lcs) => /=; first by apply ctx_frame_cond_list_label.
  by rewrite foldr_id.
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
   The hole is allowed to be empty (in which case the inner context is then exitted on the next step). *)
Definition cfg_tuple_ctx {host_function: eqType}: Type := (store_record host_function) * list closure_ctx * seq_ctx * option administrative_instruction.

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

(* The canonical form of a context config tuple: 
   - The ves split has to be valid;
   - The closure can only be empty if the entire instruction is already a value. 
*)
Definition valid_cfg_ctx {host_function: eqType} (cfg: @cfg_tuple_ctx host_function) : Prop :=
  match cfg with
  | (_, cc, sc, oe) =>
      (cc = nil -> oe = None /\ snd sc = nil) /\ valid_split sc oe
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

(*
Definition ai_rect' (P: administrative_instruction -> Type)
  (e : administrative_instruction)
  (f_basic : forall b : basic_instruction, P (AI_basic b)) 
  (f_trap : P AI_trap)
  (f_invoke : forall addr : funcaddr, P (AI_invoke addr))
  (f_label : forall (n : nat) (ces es : seq administrative_instruction), ais_measure es < ai_measure e -> P (AI_label n ces es))
  (f_local : forall (n : nat) (f : frame) (es : seq administrative_instruction), ais_measure es < ai_measure e -> P (AI_local n f es))
  : (P e).
Proof.
  destruct e as
    [ b
    |
    | addr
    | n ces es
    | n f es
    ].
  - exact (f_basic b).
  - exact (f_trap).
  - exact (f_invoke addr).
  - by apply f_label.
  - by apply f_local.
Defined.
*)

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
    + destruct e as [b | | | |] => //; destruct b => //=.
      simpl in Hetov; injection Hetov as ->; move => /= Hsplit.
      apply IH in Hsplit as [vs0 [-> ->]].
      eexists; split => //=.
      by rewrite rev_cons -cats1 -catA cat1s.
    + move => [<- <-].
      exists nil.
      split => //.
      destruct e as [b | | | |] => //; by destruct b.
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
    + destruct e as [b | | | |] => //; destruct b => //=.
      simpl in Hetov; injection Hetov as ->.
      injection Heq as <- <-.
      erewrite IH; eauto.
      by rewrite rev_cons -cats1 -catA cat1s.
    + destruct e as [b | | | |]; first (destruct b); by injection Heq as <- <-.
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
              | nil => None (* ctx_decompose_aux (es, [:: (empty_frame_ctx, [::Build_label_ctx vs k ces es'])]) *)
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
 (* { move => [ves acc] ves' acc' vs ? e es' k ces es ?? Hsplit ? [? ?]; subst.
    apply split_vals'_spec, split_vals_inv in Hsplit as ->.
    rewrite ais_measure_cat ais_measure_cons /ais_measure => /=.
    by lias.
  }*)
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

Definition ctx_update (acc: list closure_ctx) (sctx: seq_ctx) e :=
  match e_to_v_opt e with
  | Some v =>
      let '(vs, es) := sctx in
      let '(vs', es') := split_vals' es in
      match es' with
      | nil => Some (acc, (vs' ++ [::v] ++ vs, nil), None)
      | e' :: es'' => ctx_update_nconst acc (vs' ++ [::v] ++ vs, es'') e'
      end
  | None => ctx_update_nconst acc sctx e
  end.

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

Lemma ctx_decompose_valid: forall ves ccs sctx oe,
    ctx_decompose ves = Some (ccs, sctx, oe) ->
    valid_split sctx oe.
Proof.
  intros.
  by eapply ctx_decompose_valid_aux; eauto.
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

Lemma ctx_update_valid: forall sctx e ccs ccs' sctx' oe,
    ctx_update ccs sctx e = Some (ccs', sctx', oe) ->
    valid_split sctx' oe.
Proof.
  move => [vs es] e ccs ccs' [vs' es'] oe Hupdate.
  unfold ctx_update in Hupdate.
  destruct (e_to_v_opt e) as [v | ] eqn:Hetov.
  - destruct (split_vals' es) as [vs'' es''] eqn:Hsplit.
    destruct es'' as [ | e0 es'']; try by injection Hupdate as <- <- <-; subst => //.
    apply split_vals'_spec, split_vals_nconst in Hsplit.
    by apply ctx_update_nconst_valid in Hupdate => //.
  - apply ctx_update_nconst_valid in Hupdate => //.
    by destruct e => //; destruct b.
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
  
Lemma ctx_update_fill: forall sctx e ccs ccs' sctx' oe,
    ctx_update ccs sctx e = Some (ccs', sctx', oe) ->
    ccs ⦃ sctx ⦃ [::e] ⦄ ⦄ = ccs' ⦃ sctx' ⦃ olist oe ⦄ ⦄.
Proof.
  move => [vs es] e ccs ccs' [vs' es'] oe Hupdate.
  unfold ctx_update in Hupdate.
  destruct (e_to_v_opt e) as [v | ] eqn:Hetov; last by apply ctx_update_nconst_fill in Hupdate.
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
Qed.

End EvalContext.
