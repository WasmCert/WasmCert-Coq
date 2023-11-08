(** Properties of Wasm label/evaluation contexts *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith ZArith.
From Wasm Require Export common operations datatypes_properties properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Decidable equality of lholed without pulling in unnecessary 
    equality axioms **)
Section lholed_eqdec.

Definition lholed_cast {k k'} (lh: lholed k) (Heq: k = k'): lholed k' :=
  eq_rect k lholed lh k' Heq.

(* Some combinations of theorem from standard library should give these as well,
   but it's not clear which ones are axiom free *)
Theorem nat_eqdec_refl: forall k, Nat.eq_dec k k = left (erefl k).
Proof.
  elim => //=.
  move => k IH.
  by rewrite IH.
Defined.

Definition nat_eqdec_canon k k' (H: k = k') : k = k' :=
  match (Nat.eq_dec k k') with
  | left e => e
  | right ne => False_ind _ (ne H)
  end.

Theorem nat_eqdec_aux: forall (k: nat) (H: k = k), H = nat_eqdec_canon H.
Proof.
  move => k H.
  case H.
  unfold nat_eqdec_canon.
  by rewrite nat_eqdec_refl.
Defined.

Theorem nat_eqdec_unique: forall (k: nat) (H: k = k), H = erefl k.
Proof.
  move => k H.
  rewrite (nat_eqdec_aux H).
  unfold nat_eqdec_canon.
  by rewrite nat_eqdec_refl.
Defined.

Theorem lh_cast_eq {k} (lh: lholed k) (Heq: k = k):
  @lholed_cast k k lh Heq = lh.
Proof.
  by rewrite (nat_eqdec_unique Heq).
Qed.

Ltac decide_eq_arg x y :=
  let Heq := fresh "Heq" in
  let Hcontra := fresh "Hcontra" in
  destruct (x == y) eqn:Heq; move/eqP in Heq; subst; last by right; move => Hcontra; injection Hcontra.

Definition lh_case: forall n (P: lholed n -> Type),
    (forall (H: 0 = n) vs es, P (lholed_cast (LH_base vs es) H)) ->
    (forall n' (H: S n' = n) vs k es (lh: lholed n') es', P (lholed_cast (LH_rec vs k es lh es') H)) ->
    (forall (lh: lholed n), P lh).
Proof.
  move => n P H0 Hrec lh.
  destruct lh as [lvs les | n lvs k les lh les'].
  - by specialize (H0 (erefl 0) lvs les).
  - by specialize (Hrec _ (erefl (S n)) lvs k les lh les'). 
Defined.

(* Decidable equality of lholed without eq_rect_eq *)
Definition lholed_eq_dec : forall k (lh1 lh2 : lholed k), {lh1 = lh2} + {lh1 <> lh2}.
Proof.
  elim.
  {
    move => lh1.
    eapply lh_case; last done.
    move => H vs es; rewrite lh_cast_eq.
    move: lh1.
    eapply lh_case; last done.
    move => H' vs' es'; rewrite lh_cast_eq.
    decide_eq_arg vs' vs.
    decide_eq_arg es' es.
    by left.
  }
  {
    move => n IH lh.
    eapply lh_case; first done.
    move => n1 H1 vs1 k1 es1 lh1 es1'; injection H1 as ->; rewrite lh_cast_eq.
    move: lh.
    eapply lh_case; first done.
    move => n2 H2 vs2 k2 es2 lh2 es2'; injection H2 as ->; rewrite lh_cast_eq.
    decide_eq_arg vs2 vs1.
    decide_eq_arg k2 k1.
    decide_eq_arg es2 es1.
    decide_eq_arg es2' es1'.
    destruct (IH lh1 lh2) as [ | Hneq]; subst; first by left.
    right. move => Hcontra; apply Hneq.
    clear - Hcontra.
    inversion Hcontra.
    (* This one is axiom free *)
    apply Eqdep_dec.inj_pair2_eq_dec in H0 => //.
    decide equality.
  }
Defined.

Definition lholed_eqb {k} (v1 v2: lholed k) : bool := lholed_eq_dec v1 v2.

Definition eqlholedP {k} :=
  eq_dec_Equality_axiom (@lholed_eq_dec k).

Canonical Structure lholed_eqMixin {k} := EqMixin (@eqlholedP k).
Canonical Structure lholed_eqType {k} := Eval hnf in EqType (@lholed k) (@lholed_eqMixin k).

End lholed_eqdec.

Lemma lfilled_not_nil {k}: forall (lh: lholed k) es es', lfill lh es = es' -> es <> [::] -> es' <> [::].
Proof.
  elim => /=.
  { move => vs ? es ? <- ?.
    by destruct es, vs => //.
  }
  { move => k' vs n es lh' IH vs' ?? <- ?.
    by destruct vs.
  }
Qed.

(** label context arithmetics **)
Fixpoint empty_vs_base {k} (lh: lholed k) : bool :=
  match lh with
  | LH_base [::] _ => true
  | LH_rec _ _ _ _ lh _ => empty_vs_base lh
  | _ => false
  end.

Fixpoint lh_push_base_vs {k} (lh: lholed k) rvs: lholed k :=
  match lh with
  | LH_base vs es => LH_base (vs ++ rvs) es
  | LH_rec _ vs n es lh' es' =>
      let lh_pushed := lh_push_base_vs lh' rvs in
      LH_rec vs n es lh_pushed es'
  end.

Definition lh_push_front_vs {k} vcs (lh: lholed k): lholed k :=
  match lh with
  | LH_base vs es => LH_base (vcs ++ vs) es
  | LH_rec _ vs n es lh' es' => LH_rec (vcs ++ vs) n es lh' es'
  end.

Definition lh_drop_vs {k} l (lh: lholed k): lholed k :=
  match lh with
  | LH_base vs es => LH_base (drop l vs) es
  | LH_rec _ vs n es lh' es' => LH_rec (drop l vs) n es lh' es'
  end.

Definition lh_drop_vs_o {k} l (lh: lholed k): option (lholed k) :=
  match lh with
  | LH_base vs es =>
      if l <= length vs then Some (LH_base (drop l vs) es)
      else None
  | LH_rec _ vs n es lh' es' =>
      if l <= length vs then Some (LH_rec (drop l vs) n es lh' es')
      else None
  end.

Definition lh_push_back_es {k} es0 (lh: lholed k): lholed k :=
  match lh with
  | LH_base vs es => LH_base vs (es ++ es0)
  | LH_rec _ vs n es lh' es' => LH_rec vs n es lh' (es' ++ es0)
  end.

Lemma lfill_push_base_vs {k} : forall (lh: lholed k) vs ves es,
  ves = v_to_e_list vs ->
  lfill lh (ves ++ es) = lfill (lh_push_base_vs lh vs) es.
Proof.
  induction lh as [vs es | ? vs n es lh' IH es'']; intros rvs vcs e ->; simpl in *.
  - by rewrite/v_to_e_list map_cat -catA -catA.
  - do 3 f_equal.
    by eapply IH; eauto.
Qed.

Lemma lfill_push_base_vs' {k}: forall (lh: lholed k) vs ves es l,
    ves = v_to_e_list vs ->
    length ves >= l ->
    lfill lh (ves ++ es) = lfill (lh_push_base_vs lh (take (length ves - l) vs)) ((drop (length ves - l) ves) ++ es).
Proof.
  move => lh vs ves es l Hves Hlen.
  rewrite -(cat_take_drop (length ves - l) ves) -catA.
  erewrite <-lfill_push_base_vs; eauto.
  subst.
  repeat rewrite catA cat_take_drop v_to_e_take.
  by rewrite length_is_size v_to_e_size catA cat_take_drop.
Qed.

Lemma lfill_push_front_vs {k} : forall (lh: lholed k) vs es LI,
    lfill lh es = LI ->
    lfill (lh_push_front_vs vs lh) es = v_to_e_list vs ++ LI.
Proof.
  move => lh vs es LI <-.
  by destruct lh => //=; rewrite - v_to_e_cat -catA.
Qed.

Lemma lfill_drop_impl {k}: forall (lh: lholed k) ves e es LI,
    const_list ves ->
    is_const e = false ->
    lfill lh (e :: es) = ves ++ LI ->
    lh_drop_vs_o (length ves) lh = Some (lh_drop_vs (length ves) lh).
Proof.
  move => lh ves e es LI Hconst Hnconst Heq.
  destruct lh; simpl in * => //.
  all: apply es_split_by_non_const in Heq; eauto; (try by apply v_to_e_const); destruct Heq as [? Heq].
  all: replace (length ves <= length l) with true; (apply f_equal with (f := @size administrative_instruction) in Heq; rewrite size_cat v_to_e_size in Heq; simpl in Heq; repeat rewrite length_is_size; by lias).
Qed.
  
Lemma lfill_drop_vs {k}: forall (lh: lholed k) ves e es LI,
    const_list ves ->
    is_const e = false ->
    lfill lh (e :: es) = ves ++ LI ->
    lfill (lh_drop_vs (length ves) lh) (e :: es) = LI.
Proof.
  move => lh ves e es LI Hconst Hnconst Heq.
  destruct lh; simpl in * => //.
  all: specialize (es_split_by_non_const Heq) as Heq2; destruct Heq2 as [xs Heq2]; eauto; (try by apply v_to_e_const).
  all: rewrite -(cat_take_drop (length ves) l) -v_to_e_cat -catA in Heq.
  all: apply concat_cancel_first_n in Heq; last by rewrite v_to_e_size size_take; apply f_equal with (f := size) in Heq2; rewrite v_to_e_size size_cat in Heq2; rewrite length_is_size; destruct (size ves < size l) eqn:?; lias.
  all: move/andP in Heq; destruct Heq as [Heqves HeqLI]; move/eqP in Heqves; by move/eqP in HeqLI.
Qed.

Lemma lfill_push_back_es {k}: forall (lh: lholed k) es es0,
    lfill (lh_push_back_es es0 lh) es = lfill lh es ++ es0.
Proof.
  move => lh es es0.
  destruct lh; simpl in * => //; by repeat rewrite -catA => //.
Qed.


Fixpoint ai_gen_measure (e: administrative_instruction) : nat :=
  match e with
  | AI_label _ _ es => 1 + List.list_max (map ai_gen_measure es)
  | _ => 0
  end.

Definition ais_gen_measure (LI: list administrative_instruction) : nat :=
  List.list_max (map ai_gen_measure LI).

Lemma lfill_const: forall k (lh: lholed k) e lf,
    const_list lf ->
    lfill lh [::e] = lf ->
    {vs & {es & {Heq: k = 0 & lholed_cast lh Heq = (LH_base vs es) /\ lf = v_to_e_list vs ++ [::e] ++ es}}}.
Proof.
  move => k lh.
  destruct lh as [lvs les | k lvs j lces lh les] => //.
  - move => e lf /=Hconst Hlf.
    subst.
    apply const_list_split in Hconst as [_ Hconst].
    simpl in Hconst.
    move/andP in Hconst; destruct Hconst as [? Hconst].
    destruct e as [b | | | |] => //; destruct b => //.
    exists lvs, les, (Logic.eq_refl 0).
    by split => //.
  - move => e lf Hconst Hlf. subst.
    exfalso.
    apply const_list_split in Hconst as [_ Hconst].
    by simpl in Hconst.
Qed.

Lemma const_seq_factorise (fe: nat -> administrative_instruction) (ves: list administrative_instruction):
  {vs & {es & ves = v_to_e_list vs ++ [::fe 0] ++ es}} + {forall vs es, ves <> v_to_e_list vs ++ [::fe 0] ++ es}.
Proof.
  move: fe.
  induction ves as [ | e ves']; move => fe; first by right; destruct vs => //.
  destruct (e == fe 0) eqn:H; move/eqP in H.
  - subst.
    left; by exists nil, ves'.
  - destruct (is_const e) eqn:Hconst.
    { destruct e as [ b | | | |] => //; destruct b => //.
      destruct (IHves' fe) as [[vs [es ->]] | Hcontra]; first by left; exists (v :: vs), es.
      right; move => vs es Heq.
      destruct vs as [| v0 vs'] => //; simpl in *; first by inversion Heq.
      apply (Hcontra vs' es) => /=; by inversion Heq.
    }
    { right; move => vs es Heq.
      destruct vs as [| v0 vs'] => //; simpl in *; by inversion Heq; subst.
    }
Qed.
    
Definition lf_decide fe es: Type := {n & {lh: lholed n | lfill lh [::fe n] = es}} + {forall n (lh: lholed n), lfill lh [::fe n] <> es}.

Definition lfill_factorise_aux (fe: nat -> administrative_instruction) (es: list administrative_instruction) (Hrec: forall fe es', (ais_gen_measure es' < ais_gen_measure es)%coq_nat -> lf_decide fe es'):
    lf_decide fe es.
Proof.
  (* First, decide if lfill0 hold *)
  destruct (const_seq_factorise fe es) as [[vs' [es'' Heq]] | Hcontra]; first by left; exists 0, (LH_base vs' es'').
  (* If not, then look at the top of instruction stack *)
  destruct (split_vals_e es) as [vs es'] eqn:Hsplit.
  destruct es' as [| e es'].
  (* Instruction stack is empty *)
  - right. move => n lh Hlf.
    apply split_vals_inv in Hsplit as ->; rewrite cats0 in Hlf.
    rewrite cats0 in Hcontra.
    apply lfill_const in Hlf; last by apply v_to_e_const.
    destruct Hlf as [vs' [es [-> [? Heq]]]]; simpl in *; subst.
    by apply Hcontra in Heq.
  - specialize (split_vals_nconst Hsplit) as Hnconst.
    apply split_vals_inv in Hsplit as ->.
    destruct e as [ | | | j lvs les |].
    4: {
      destruct (Hrec (fun n => fe (S n)) les) as [IH | IH] => /=.
      (* measure *)
      {
        unfold ais_gen_measure.
        rewrite - cat1s map_cat map_cat cat_app cat_app.
        repeat rewrite List.list_max_app => /=.
        destruct (List.list_max (map ai_gen_measure es')); by lias.
      }
      { destruct IH as [n' [lh' Hlf]].
        left.
        exists (S n'), (LH_rec vs j lvs lh' es') => /=.
        by rewrite Hlf.
      }
      { right. move => n lh Hlf.
        destruct lh as [lvs' les' | n' lvs' les' lh' les'']; simpl in *; first by apply (Hcontra lvs' les').
        apply const_list_concat_inv in Hlf as [Heq [Heqlab <-]] => //; try by apply v_to_e_const.
        apply v_to_e_inj in Heq as ->.
        injection Heqlab as <- <- <-.
        by eapply IH.
      }
    }
    all: right; move => n' lh Hlf; destruct lh as [lvs' les' | n' lvs' les' lh' les'']; simpl in *; (try by apply (Hcontra lvs' les')); apply const_list_concat_inv in Hlf as [Heq [Heqlab <-]] => //; by apply v_to_e_const.
Defined.

Program Fixpoint lfill_factorise fe es {measure (ais_gen_measure es)} :=
  @lfill_factorise_aux fe es lfill_factorise.


(** Inductively defined contexts extract to code that run very poorly. This alternative defines an
    additional context stack to replace the inductive definition, since the evaluation context tree is
    always guaranteed to be linear. **)
Module EvalContext.

Class eval_ctx (ctx_t: Type): Type :=
  {
    ctx_fill: ctx_t -> list administrative_instruction -> list administrative_instruction;
  }.

Notation "ctx [[ es ]]" := (ctx_fill ctx es) (at level 5).

(* Sequence context: vs ++ [_] ++ es. This is only used in the base level *)
Definition seq_ctx : Type := (list value) * (list administrative_instruction).

#[export]
Instance seq_ctx_eval : eval_ctx seq_ctx :=
  {| ctx_fill := (fun ctx es => (v_to_e_list (fst ctx) ++ es ++ (snd ctx))) |}.

(* Label context: LC_val ++ [::AI_label LC_arity LC_cont [_]) ++ LC_post; can be nested *)
Record label_ctx: Type :=
  { LC_val: list value;
    LC_arity: nat;
    LC_cont: list administrative_instruction;
    LC_post: list administrative_instruction;
  }.

Definition label_ctx_fill := (fun ctx es => (v_to_e_list (LC_val ctx) ++ [::AI_label (LC_arity ctx) (LC_cont ctx) es] ++ LC_post ctx)).

#[export]
Instance label_ctx_eval: eval_ctx label_ctx :=
  {| ctx_fill := label_ctx_fill |}.

Canonical label_ctx_eval.

#[export]
Instance list_ctx_eval {T: Type} (f: eval_ctx T): eval_ctx (list T) :=
  {| ctx_fill := (fun ctxs es => foldr f.(ctx_fill) es ctxs) |}.

Definition label_list_ctx: Type := list label_ctx.

(* Frame context: FC_val ++ [::AI_local FC_arity FC_frame [_]) ++ FC_post *)
Record frame_ctx: Type :=
  { FC_val: list value;
    FC_arity: nat;
    FC_frame: frame;
    FC_post: list administrative_instruction;
  }.

#[export]
Instance frame_ctx_eval: eval_ctx frame_ctx :=
  {| ctx_fill := (fun ctx es => (v_to_e_list (FC_val ctx) ++ [::AI_local (FC_arity ctx) (FC_frame ctx) es] ++ FC_post ctx)) |}.

Definition closure_ctx : Type := (option frame_ctx) * label_ctx * seq_ctx.

Definition closure_ctx_fill (cc: closure_ctx) es :=
  match cc with
  | (Some fc, lc, sc) => fc [[ lc [[ sc [[ es ]] ]] ]]
  | (None, lc, sc) => lc [[ sc [[ es ]] ]]
  end.

#[export]
Instance closure_ctx_eval: eval_ctx closure_ctx :=
  {| ctx_fill := closure_ctx_fill |}.

(* A configuration is now represented as (S; F; ctx [[ e ]]), with the hole holding at most one instruction.
   The hole is allowed to be empty (in which case the inner context is then exitted. *)
Definition cfg_tuple_ctx {host_function: eqType}: Type := (store_record host_function) * frame * list closure_ctx * option administrative_instruction.

End EvalContext.
