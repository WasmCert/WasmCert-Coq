(** Inductively defined contexts extract to code that run very poorly. This alternative defines an
    additional context stack to replace the inductive definition, since the evaluation context tree is
    guaranteed to be linear. **)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From HB Require Import structures.
From Coq Require Import Program NArith ZArith Wf_nat.
From Wasm Require Export common operations datatypes_properties properties opsem typing_inversion tactic.
Require Import FunInd Recdef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section EvalContext.

Context `{ho: host}.

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

Context `{ho: host}.

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
Definition eqlabel_ctxP: Equality.axiom label_ctx_eqb :=
  eq_dec_Equality_axiom label_ctx_eq_dec.

HB.instance Definition label_ctx_eqMixin := hasDecEq.Build label_ctx eqlabel_ctxP.

Definition label_ctx_fill := (fun es ctx => (vs_to_es (LC_val ctx) ++ [::AI_label (LC_arity ctx) (LC_cont ctx) es] ++ (LC_post ctx))).

#[refine, export]
Instance label_ctx_eval: eval_ctx label_ctx :=
  {| ctx_fill := label_ctx_fill;
     ctx_frame_mask := fmask0; ctx_frame_cond := fcond0 |}.
Proof.
  move => [lvs lk lces les] hs s f es hs' s' f' es' _ Hred.
  eapply r_label with (lh := LH_rec (rev lvs) lk lces (LH_base nil nil) les); eauto => //; by rewrite /label_ctx_fill /= cats0.
Defined.


(* Frame context: rev FC_val ++ [::AI_frame FC_arity FC_frame [_]) ++ FC_post 
   Note that the outermost frame  is technically only a framestate as stated in the 2.0 spec.
*)
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
Definition eqframe_ctxP: Equality.axiom frame_ctx_eqb :=
  eq_dec_Equality_axiom frame_ctx_eq_dec.

HB.instance Definition frame_ctx_eqMixin := hasDecEq.Build frame_ctx eqframe_ctxP.

#[refine, export]
Instance frame_ctx_eval: eval_ctx frame_ctx :=
  {| ctx_fill := (fun es ctx => (vs_to_es (FC_val ctx) ++ [::AI_frame (FC_arity ctx) (FC_frame ctx) es] ++ (FC_post ctx)));
    ctx_frame_mask := (fun ctx _ => ctx.(FC_frame));
    ctx_frame_cond := (fun _ f1 f2 => f1 = f2);
  |}.
Proof.
  move => [lvs lk lf les] hs s f es hs' s' f' es' /= <- Hred /=.
  eapply r_label with (lh := LH_base (rev lvs) les); eauto => //=; try by rewrite -cat1s.
  by apply r_frame.
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
    by apply r_frame.
  - move => ctx ctxs' IH [lvs lk lf les] hs s f es hs' s' f' es' <- /=Hred.
    apply IH => //=.
    eapply r_label with (lh := LH_base (rev lvs) les); eauto => //=; try by rewrite -cat1s.
    by apply r_frame.
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
    apply r_frame.
    by apply (list_label_ctx_eval.(ctx_reduce)).
  - move => ctx ctxs' IH [[lvs lk lf les] lcs] hs s f es hs' s' f' es' <- /=Hred.
    apply IH => //=.
    eapply r_label with (lh := LH_base (rev lvs) les); eauto => //=; try by rewrite -cat1s.
    apply r_frame.
    by apply (list_label_ctx_eval.(ctx_reduce)).
Defined.

(* A configuration is now represented as (S; ⦃ ctxs ⦃ sc ⦃ option e ⦄ ⦄), with the hole holding at most one instruction which needs to be non-constant.
   Note that no frame is held in the tuple, since all frames should been pushed into the local contexts. The validity predicate later asserts that the length of the closure contexts stack must be at least one, and the outermost context must not have any continuations or operands.
   The contexts are represented in a reversed stack-like structure: the head of each list is the innermost context.
   The hole is allowed to be empty (in which case the inner context is then exitted on the next step). However, the sequence context sc should not hold any
   non-empty instruction in the continuation. *)
Definition cfg_tuple_ctx: Type := store_record * (list closure_ctx) * seq_ctx * option administrative_instruction.

Definition valid_hole (e: administrative_instruction) : bool :=
  (negb (is_const e)) &&
    match e with
    | AI_label _ _ _ => false
    | AI_frame _ _ _ => false
    | _ => true
    end.

Definition valid_split (sc: seq_ctx) oe: bool :=
  match oe with
  | Some e => valid_hole e
  | None => snd sc == nil
  end.

Definition valid_ccs (ccs: list closure_ctx): bool :=
  ccs != nil.

Lemma valid_ccs_change_labs fc labs labs' ccs:
  valid_ccs ((fc, labs) :: ccs) ->
  valid_ccs ((fc, labs') :: ccs).
Proof.
  by destruct ccs => /=.
Qed.

(* The canonical form of a context config tuple: 
   - The ves split has to be valid;
   - The closure can only be empty if the entire instruction is already a value.
*)
Definition valid_cfg_ctx (cfg: cfg_tuple_ctx) : Prop :=
  match cfg with
  | (_, cc, sc, oe) =>
      valid_ccs cc /\ valid_split sc oe
  end.

Definition olist {T: Type} (ot: option T) : list T :=
  match ot with
  | Some t => [::t]
  | None => nil
  end.

Fixpoint ai_measure (e: administrative_instruction) : nat :=
  match e with
  | AI_label _ _ es => 1 + List.list_sum (map ai_measure es)
  | AI_frame _ _ es => 1 + List.list_sum (map ai_measure es)
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

(* Convert frame state to frame context *)
Definition to_frame_ctx (f: frame) (n: nat) :=
  Build_frame_ctx nil n f nil.

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
    + move => Hsplit.
      apply IH in Hsplit as [vs' [Hsplit ->]].
      rewrite Hsplit.
      eexists; split => //=.
      by rewrite rev_cons -cats1 -catA cat1s.
    + move => [<- <-].
      by exists nil.
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
    + injection Heq as <- <-.
      erewrite IH; eauto.
      by rewrite rev_cons -cats1 -catA cat1s.
    + by injection Heq as <- <-.
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

(* Suppressing these two warnings locally *)
Set Warnings "-funind-cannot-define-graph".
Set Warnings "-funind-cannot-build-inversion".
Function ctx_decompose_aux (ves_acc: (list administrative_instruction) * (list closure_ctx)) {measure (fun '(ves, ccs) => ais_measure ves)} : option (list closure_ctx * seq_ctx * option administrative_instruction) :=
  let '(ves, ccs) := ves_acc in
  match split_vals' ves with
  | (vs, es) =>
      match es with
      | nil => Some (ccs, (vs, nil), None)
      | e :: es' =>
          match e with
          | AI_label k ces es =>
              match ccs with
              | nil => None
              | (fc, lcs) :: ccs' =>
                  ctx_decompose_aux (es, (fc, (Build_label_ctx vs k ces es') :: lcs) :: ccs')
              end
          | AI_frame k f es =>
              ctx_decompose_aux (es, (Build_frame_ctx vs k f es', nil) :: ccs)
          | _ => (* In this case, we know that e cannot be const due to how split_vals' works *)
              Some (ccs, (vs, es'), Some e)
          end
      end
  end.
Proof.
  { move => [ves acc] ves' ccs' vs ? e es' k ces es ?? Hsplit cc ccs fc lcs ?? [? ?]; subst.
    apply split_vals'_spec, split_vals_inv in Hsplit as ->.
    rewrite ais_measure_cat ais_measure_cons /ais_measure => /=.
    by lias.
  }
  { move => [ves acc] ves' ccs' [? ?] vs ? e es' k f ??? Hsplit; subst.
    apply split_vals'_spec, split_vals_inv in Hsplit as ->.
    rewrite ais_measure_cat ais_measure_cons /ais_measure => /=.
    by lias.
  }
Defined.
Set Warnings "+funind-cannot-define-graph".
Set Warnings "+funind-cannot-build-inversion".

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
  | AI_frame k f es =>
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
    valid_ccs acc ->
    ctx_decompose_aux (ves, acc) = Some (ccs, sctx, oe) ->
    valid_ccs ccs.
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
  destruct es as [ | e es']; first by injection Hdecomp as <- <- <-; unfold valid_ccs.
  destruct e as
    [ b
    |
    | faddr
    | eaddr
    | addr
    | n ces es
    | n f es
    ]; simpl in *; try by (injection Hdecomp as <- <- <-; unfold valid_ccs).
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
    | faddr
    | eaddr
    | addr
    | n ces es
    | n f es
    ]; simpl in *; try by injection Hdecomp as <- <- <-.
  - injection Hdecomp as <- <- <- => /=.
    apply split_vals_nconst in Hsplit.
    by destruct b.
  - injection Hdecomp as <- <- <- => /=.
    by apply split_vals_nconst in Hsplit.
  - injection Hdecomp as <- <- <- => /=.
    by apply split_vals_nconst in Hsplit.
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
    valid_ccs ccs ->
    ctx_update_nconst ccs sctx e = Some (ccs', sctx', oe) ->
    valid_ccs ccs'.
Proof.
  move => [vs es] e ccs ccs' [vs' es'] oe Hnil Hupdate.
  unfold ctx_update_nconst in Hupdate; unfold valid_ccs.
  destruct e; first destruct b; try (injection Hupdate as <- <- <-; subst => //); try (by apply/orP; left).
  (* Label *)
  - destruct ccs as [ | [fc lcs] ccs0] => //.
    eapply ctx_decompose_valid_ccs_aux in Hupdate; eauto.
  - eapply ctx_decompose_valid_ccs_aux in Hupdate; eauto.
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
  (* Frame *)
  - by apply ctx_decompose_valid_aux in Hupdate.
Qed.

Lemma ctx_update_nconst_none_impl: forall ccs sctx e,
    ctx_update_nconst ccs sctx e = None ->
    ccs = nil.
Proof.
  move => ccs [vs es] e Hupdate.
  unfold ctx_update_nconst in Hupdate.
  destruct e, ccs as [ | [fc lcs] ccs'] => //; simpl in *; by apply ctx_decompose_aux_none_impl in Hupdate as [??].
Qed.

Lemma ctx_update_none_impl: forall acc sctx e,
    ctx_update acc sctx e = None ->
    acc = nil.
Proof.
  move => acc [vs es] e Hupdate.
  unfold ctx_update in Hupdate.
  remove_bools_options.
  - destruct (split_vals' es) as [vs' es'] eqn:Hsplit => //.
    destruct es' => //.
    by apply ctx_update_nconst_none_impl in Hupdate.
  - by apply ctx_update_nconst_none_impl in Hupdate.
  - destruct (split_vals' es) as [vs' es'] eqn:Hsplit => //.
    destruct es' => //.
    by apply ctx_update_nconst_none_impl in Hupdate.
Qed.

Lemma ctx_update_valid_ccs: forall sctx ccs oe,
    valid_ccs ccs ->
    { ccs' & {sctx' & { oe' |
      ctx_update ccs sctx oe = Some (ccs', sctx', oe') /\
      valid_ccs ccs'}}}.
Proof.
  move => [vs es] ccs oe Hvalid.
  destruct (ctx_update ccs (vs, es) oe) as [cfg' | ] eqn:Hupdate; last by apply ctx_update_none_impl in Hupdate; unfold valid_ccs in Hvalid; subst.
  unfold ctx_update in Hupdate; unfold valid_ccs.
  destruct cfg' as [[ccs' sctx'] oe'].
  destruct oe as [e | ].
  - destruct (e_to_v_opt e) as [v | ] eqn:Hetov.
    + destruct (split_vals' es) as [vs'' es''] eqn:Hsplit.
      destruct es'' as [ | e0 es''].
      * injection Hupdate as <- <- <-; subst => //.
        repeat eexists; by eauto.
      * apply split_vals'_spec, split_vals_nconst in Hsplit.
        repeat eexists; eauto.
        by apply ctx_update_nconst_valid_ccs in Hupdate => //.
    + apply ctx_update_nconst_valid_ccs in Hupdate => //.
      by repeat eexists; eauto.
  - destruct (split_vals' es) as [vs'' es''] eqn:Hsplit.
    destruct es'' as [ | e0 es''].
    + injection Hupdate as <- <- <-; subst => //.
      repeat eexists; by eauto.
    + apply split_vals'_spec, split_vals_nconst in Hsplit.
      apply ctx_update_nconst_valid_ccs in Hupdate => //.
      repeat eexists; by eauto.
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
      | faddr
      | eaddr
      | addr
      | n ces es
      | n f es
      ]; simpl in *; try by injection Hdecomp as <- <- <- => /=; apply split_vals_inv in Hsplit as ->.
    (* Label *)
    + destruct acc as [ | [fc lcs] ccs']; first by inversion Hdecomp => /=.
      eapply IH in Hdecomp; eauto; apply split_vals_inv in Hsplit as ->; first by rewrite Hdecomp.
      by rewrite ais_measure_cat ais_measure_cons /ais_measure => /=; lias.
    (* Frame *)
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
      apply ve_inv in Hetov; subst e.
      f_equal => /=.
      rewrite cats0 /vs_to_es rev_cat rev_cons -cats1 -catA.
      by repeat rewrite -v_to_e_cat.
    - apply ve_inv in Hetov; subst e.
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


(** Typing propagations for contexts **)
Section Typing.

Lemma fc_typing: forall (fc: frame_ctx) es s C0 tf,
    e_typing s C0 (fc ⦃ es ⦄) tf ->
    exists C ret,
      frame_typing s fc.(FC_frame) C /\
        fc.(FC_arity) = (length ret) /\
        e_typing s (upd_return C (Some ret)) es (Tf nil ret).
Proof.
  move => fc es s C [ts1 ts2] /= Htype.
  rewrite - cat1s in Htype.
  unfold vs_to_es in Htype.
  invert_e_typing.
  inversion Hconjl0 as [??????? Hftype ? Hetype]; subst; clear Hconjl0.
  by do 2 eexists; repeat split; eauto.
Qed.

Lemma lc_typing: forall (lc: label_ctx) es s C0 tf,
    e_typing s C0 (lc ⦃ es ⦄) tf ->
    exists ts1 ts2,
      e_typing s C0 (lc.(LC_cont)) (Tf ts1 ts2) /\
      length ts1 = lc.(LC_arity) /\
      e_typing s (upd_label C0 ([::ts1] ++ C0.(tc_labels))) es (Tf nil ts2).
Proof.
  move => lc es s C [ts1 ts2] /= Htype.
  unfold label_ctx_fill in Htype.
  invert_e_typing.
  by do 2 eexists; split; eauto.
Qed.

Definition lab_lc_agree (lab: list value_type) (lc: label_ctx) : bool :=
  length lab == lc.(LC_arity).

Lemma lcs_typing_exists: forall (lcs: list label_ctx) es s C0 tf,
    e_typing s C0 (lcs ⦃ es ⦄) tf ->
    exists labs ts1 ts2,
      e_typing s (upd_label C0 (labs ++ C0.(tc_labels))) es (Tf ts1 ts2) /\
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

Lemma lcs_typing_exists_nil: forall (lcs: list label_ctx) es s C0 ts,
    e_typing s C0 (lcs ⦃ es ⦄) (Tf nil ts) ->
    exists labs ts2,
      e_typing s (upd_label C0 (labs ++ C0.(tc_labels))) es (Tf nil ts2) /\
      all2 lab_lc_agree labs lcs.
Proof.
  move => lcs es s C0 ts Hetype.
  destruct lcs.
  - simpl in Hetype.
    exists nil, ts.
    split => //=.
    by destruct C0.
  - apply lcs_typing_exists in Hetype as [? [? [? [Hetype [? Hconsume]]]]].
    rewrite Hconsume in Hetype => //.
    by repeat eexists; eauto.
Qed.

Lemma cc_typing_exists: forall (cc: closure_ctx) es s C0 tf,
    e_typing s C0 cc ⦃ es ⦄ tf ->
    exists C ret labs ts2,
      frame_typing s (cc.1).(FC_frame) C /\
        (cc.1).(FC_arity) = (length ret) /\
        (all2 lab_lc_agree labs cc.2) /\
        e_typing s (upd_label (upd_return C (Some ret)) labs) es (Tf nil ts2).
Proof.
  move => [fc lcs] es s C0 tf Htype.
  apply fc_typing in Htype as [C [ret [? [? Htype]]]].
  apply lcs_typing_exists_nil in Htype as [labs [ts2 [Htype Hagree]]].
  simpl in Htype.
  do 3 eexists; exists ts2; repeat split; eauto.
  uapply Htype.
  f_equal.
  by erewrite frame_typing_label_empty, cats0; eauto.
Qed.

Lemma ccs_typing_exists: forall cc ccs es s C0 tf,
    e_typing s C0 (cc :: ccs) ⦃ es ⦄ tf ->
    exists C ret labs ts2,
      frame_typing s (cc.1).(FC_frame) C /\
        (cc.1).(FC_arity) = length ret /\
        (all2 lab_lc_agree labs cc.2) /\
        e_typing s (upd_label (upd_return C (Some ret)) labs) es (Tf nil ts2).
Proof.
  move => cc ccs.
  move: cc.
  induction ccs as [| cc' ccs']; move => [fc lcs] es s C0 tf Htype.
  - by eapply cc_typing_exists; eauto.
  - apply IHccs' in Htype as [? [? [? [? [? [? [??]]]]]]].
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
  - exists C0, (tc_return C0), (tc_labels C0), tf.
    by destruct C0.
  - apply IHccs' in Htype as [? [? [? [? Htype]]]].
    apply cc_typing_exists in Htype as [C [ret [lab [ts2 [Hftype [Hlen Htype]]]]]].
    exists C, (Some ret), lab, (Tf nil ts2).
    by apply Htype.
Qed.

Lemma sc_typing_args: forall (sc: seq_ctx) es s C ts0,
    e_typing s C (sc ⦃ es ⦄) (Tf nil ts0) ->
    exists vts ts2,
      values_typing s (rev sc.1) vts /\
      e_typing s C es (Tf vts ts2).
Proof.
  move => [vs0 es0] es s C ts0 /=Htype.
  unfold vs_to_es in Htype.
  invert_e_typing.
  exists ts_values, ts3_comp0; split => //.
  eapply ety_subtyping; eauto.
  resolve_subtyping.
  simplify_subtyping.
  exists nil, nil, ts_values, ts3_comp0; by resolve_subtyping.
Qed.

Lemma e_typing_ops: forall (ccs: list closure_ctx) (sc: seq_ctx) es s C0 ts0,
    e_typing s C0 (ccs ⦃ sc ⦃ es ⦄ ⦄) (Tf nil ts0) ->
    exists C' vts ts,
      values_typing s (rev sc.1) vts /\
      e_typing s C' es (Tf vts ts).
Proof.
  move => ccs [vs0 es0] es s C0 ts0.
  destruct ccs as [ | cc' ccs']; move => Htype.
  - by eapply sc_typing_args in Htype as [? Htype]; eauto.
  - apply ccs_typing_exists in Htype as [? [? [? [? [? [? [? Htype]]]]]]].
    by eapply sc_typing_args in Htype as [? Htype]; eauto.
Qed.

Lemma e_typing_ops_local: forall cc (ccs: list closure_ctx) (sc: seq_ctx) es s C0 tf,
    e_typing s C0 ((cc :: ccs) ⦃ sc ⦃ es ⦄ ⦄) tf ->
    exists C C' ret labs vts ts,
      values_typing s (rev sc.1) vts /\
      frame_typing s (cc.1).(FC_frame) C /\
        (cc.1).(FC_arity) = length ret /\
        C' = (upd_label (upd_return C (Some ret)) labs) /\
        e_typing s C' es (Tf vts ts).
Proof.
  move => cc ccs [vs0 es0] es s C0 tf Htype.
  - apply ccs_typing_exists in Htype as [? [? [? [? [? [? [? Htype]]]]]]].
    eapply sc_typing_args in Htype as [? [? [Hvstype Htype]]]; eauto.
    by do 7 eexists; eauto.
Qed.

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

(* Context typing inversion lemma. The first version preserves the original
   type label context, where as the second version focuses on the innermost label. *)
Lemma ctx_cfg_inv_lcs: forall s cc ccs sc oe ts,
    ctx_cfg_typing (s, (cc :: ccs), sc, oe) ts ->
    exists C (ret: option result_type) ts2,
      store_typing s /\
      frame_typing s cc.1.(FC_frame) C /\
      (ccs != nil -> (ret = Some ts2 /\ (option_map (@length _) ret = Some cc.1.(FC_arity)))) /\
      (ccs = nil -> ret = None) /\
      e_typing s (upd_return C ret) (cc.2 ⦃ sc ⦃ olist oe ⦄ ⦄) (Tf nil ts2).
Proof.
  move => s cc ccs sc oe ts Htype.
  unfold ctx_cfg_typing in Htype.
  destruct (ctx_to_cfg (s, cc::ccs, sc, oe)) as [[s0 [f es]]|] eqn:Hcfg => //; unfold ctx_to_cfg in Hcfg.
  destruct (rev (cc :: ccs)) as [ | [[? ? ff ?] lcs] ccs'] eqn:Hcc => //.
  injection Hcfg as <- <- <-.
  apply config_typing_inv in Htype as [C [Hstype [Hftype Hetype]]].
  destruct ccs' using last_ind.
  + destruct ccs; simpl in * => //; last by apply (f_equal size) in Hcc; rewrite size_rev in Hcc.
    rewrite rev_cons in Hcc; simpl in *.
    injection Hcc as -> => /=.
    exists C, None, ts => /=.
    repeat split => //.
    by erewrite <- frame_typing_return_None; eauto; destruct C.
  + clear IHccs'.
    rewrite rev_rcons in Hetype.
    apply lcs_typing_exists in Hetype as [labs0 [ts1 [ts2 [Hetype [Hagree0 Hconsume0]]]]].
    rewrite rev_cons -rcons_cons in Hcc.
    apply rcons_inj in Hcc.
    injection Hcc as Hcc <-.
    simpl in Hetype.
    apply rev_move in Hcc; subst.
    apply ccs_typing_focus in Hetype as [C' [ret [labs [[ts1' ts2'] Hetype]]]].
    destruct cc as [fc lcs']; simpl in *.
    invert_e_typing.
    inversion Hconjl0; subst; clear Hconjl0.
    exists C0, (Some extr), extr.
    repeat split => //=; last by move => Hreveq => //=; apply (f_equal size) in Hreveq; rewrite size_rev in Hreveq.
    by rewrite Hconjr0.
Qed.

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
  apply ctx_cfg_inv_lcs in Htype as [C [ret [ts' [Hstype [Hftype [Hretcons [Hretnil Hetype]]]]]]].
  apply lcs_typing_exists_nil in Hetype as [labs0 [ts2 [Hetype Hagree0]]].
  exists C, ret, labs0, ts2.
  repeat split => //.
  - move => H; by apply Hretcons in H as [??].
  - uapply Hetype => /=.
    f_equal.
    by erewrite frame_typing_label_empty, cats0; eauto.
Qed.

End Typing.

Section Reduction.

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
(* ctxs reduction can be focused in any partial initial fragments with a pivot cc. *)
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

Lemma v_to_e_split_eq: forall vs1 vs2 e1 e2 es1 es2,
    ~ is_const e1 ->
    ~ is_const e2 ->
    v_to_e_list vs1 ++ e1 :: es1 = v_to_e_list vs2 ++ e2 :: es2 ->
    vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
Proof.
  induction vs1; destruct vs2; intros ???? Hnc1 Hnc2 Heq => //=; simpl in *; try inversion Heq; subst => //.
  - unfold is_const in Hnc1; by rewrite v2e2v in Hnc1.
  - unfold is_const in Hnc2; by rewrite v2e2v in Hnc2.
  - apply ve_inj in H0; subst.
    apply IHvs1 in H1 as [? [??]] => //.
    by subst.
Qed.

(* Fill implication *)
Lemma ctx_fill_impl: forall s ccs1 sctx1 oe1 ccs2 sctx2 oe2,
    ccs1 != nil -> ccs2 != nil ->
    ccs1 ⦃ sctx1 ⦃ olist oe1 ⦄ ⦄ = ccs2 ⦃ sctx2 ⦃ olist oe2 ⦄ ⦄ ->
    ctx_to_cfg (s, ccs1, sctx1, oe1) = ctx_to_cfg (s, ccs2, sctx2, oe2).
Proof.
  intros ??????? Hn1 Hn2 Heq => //.
  unfold ctx_to_cfg.
  destruct ccs1 as [| [fc1 lcs1] ccs1'] eqn:Hccs1 using List.rev_ind => //=.
  destruct ccs2 as [| [fc2 lcs2] ccs2'] eqn:Hccs2 using List.rev_ind => //=.
  repeat rewrite rev_cat => //=.
  destruct fc1, fc2 => /=.
  subst.
  simpl in *.
  repeat rewrite foldl_cat in Heq.
  simpl in Heq.
  apply v_to_e_split_eq in Heq as [Heq1 [Heq2 Heq3]] => //.
  repeat rewrite revK.
  do 3 f_equal; by inversion Heq2.
Qed.

End Reduction.

End Host.
