From mathcomp Require Import ssreflect ssrbool eqtype seq.
From iris.program_logic Require Import language.
From Coq Require Import Eqdep_dec.
Require Export lfill_prelude.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition expr := list administrative_instruction.

(* A value can be an immediate, a trap, a [br i] if it is in a context shallow enough,
   i.e. a [valid_holed i] ; or a return, in any context. *)
(* We use VH and SH instead of LH so that the fill operations are always total functions *)
Inductive val : Type :=
| immV : (list value) -> val
| trapV : val
| brV (i : nat) (lh : valid_holed i) : val
| retV : simple_valid_holed -> val
| callHostV : function_type -> hostfuncidx -> seq.seq value -> llholed -> val.

Definition val_eq_dec : forall v1 v2: val, {v1 = v2} + {v1 <> v2}.
Proof.
  intros v1 v2;destruct v1,v2;auto.
  - destruct (decide (l = l0));[subst;by left|right;intros Hcontr;congruence].
  - destruct (decide (i = i0)). subst.
    destruct (valid_holed_eq_dec lh lh0) as [-> | H].
    by left.
    right. intro. inversion H0.
    apply Eqdep.EqdepTheory.inj_pair2 in H2.
    done.
    right.
    intro.
    inversion H.
    apply eq_sigT_fst in H2.
    done.
  - destruct (simple_valid_holed_eq_dec s s0);subst;[by left|right;congruence..].
  - destruct (function_type_eq_dec f f0), (llholed_eq_dec l0 l2),
      (hostfuncidx_eq_dec h h0), (decide (l = l1)) ;subst; try by right;congruence.
    by left.
Defined.

Definition val_eqb (v1 v2: val) : bool := val_eq_dec v1 v2.
Definition eqvalP : Equality.axiom val_eqb :=
  eq_dec_Equality_axiom val_eq_dec.

Canonical Structure val_eqMixin := EqMixin eqvalP.
Canonical Structure val_eqType := Eval hnf in EqType val val_eqMixin.


Definition state : Type := store_record * (list value) * instance.

Definition observation := unit.

Definition of_val (v : val) : expr :=
  match v with
  | immV l => v_to_e_list l
  | trapV => [::AI_trap]
  | brV i vh => vfill vh [AI_basic (BI_br i)]
  | retV sh => sfill sh [AI_basic BI_return]
  | callHostV tf h vcs sh => llfill sh [AI_call_host tf h vcs]
  end.

Lemma of_val_imm (vs : list value) :
  v_to_e_list vs = of_val (immV vs).
Proof. done. Qed.

(* The following operation mirrors the opsem of AI_trap *)
(* in which a trap value swallows all other stack values *)
(* and the opsem of br and return, which skips over all subsequent expressions *)
Definition val_combine (v1 v2 : val) :=
  match v1 with
  | immV l => match v2 with
             | immV l' => immV (l ++ l')
             | trapV => trapV
             | brV i vh => brV (vh_push_const vh l)
             | retV lh => retV (sh_push_const lh l)
             | callHostV tf h cvs sh => callHostV tf h cvs (llh_push_const sh l)
             end
  | trapV => trapV
  | brV i vh => brV (vh_append vh (of_val v2))
  | retV lh => retV (sh_append lh (of_val v2))
  | callHostV tf h vcs sh => callHostV tf h vcs (llh_append sh (of_val v2))
  end.

(* Intuitively, when writing [NotVal e], we intend to mean e is not a value.
   This is however not enforced by the syntax *)
Inductive ValNotVal :=
  Val : val -> ValNotVal
| NotVal : expr -> ValNotVal.

Definition expr_of_val_not_val x :=
  match x with
  | Val v => of_val v
  | NotVal e => e end.

Lemma expr_of_val_of_val_not_val v :
  of_val v = expr_of_val_not_val (Val v).
Proof. done. Qed.

Definition val_of_val_not_val x :=
  match x with
  | Val v => Some v
  | NotVal _ => None end.

(* Combining a val and a ValNotVal. It is intended that combining will yield a ValNotVal 
   representinig the concatenation of the function arguments, and verifies our
   invariant that [NotVal e] is used only when e is not a value *)
Definition val_not_val_combine (v1 : val) (v2 : ValNotVal) : ValNotVal :=
  match v1 with
  | immV l => match v2 with
             | Val (immV l') => Val (immV (l ++ l'))
             | Val trapV => match l with
                           | [] => Val trapV
                           | _ => NotVal (v_to_e_list l ++ [AI_trap])
                           end
             | Val (brV i vh) => Val (brV (vh_push_const vh l))
             | Val (retV lh) => Val (retV (sh_push_const lh l))
             | Val (callHostV tf h vcs lh) => Val (callHostV tf h vcs (llh_push_const lh l))
             | NotVal e => NotVal (v_to_e_list l ++ e)
             end
  | trapV => match expr_of_val_not_val v2 with
              [] => Val trapV
            | _ => NotVal (AI_trap :: expr_of_val_not_val v2)
            end
  | brV i vh =>
      Val (brV (vh_append vh (expr_of_val_not_val v2)))
  | retV lh =>
      Val (retV (sh_append lh (expr_of_val_not_val v2)))
  | callHostV tf h vcs lh =>
      Val (callHostV tf h vcs (llh_append lh (expr_of_val_not_val v2)))
  end.

(* performs a fold_left on a list of ValNotVals. Aborts if a NotVal is reached *)
Fixpoint merge_values (v : val) (vs : list ValNotVal) : ValNotVal  :=
  match vs with
  | [] => Val v
  | a :: vs => match val_not_val_combine v a with
             | Val v => merge_values v vs
             | NotVal e => NotVal (e ++ flatten (map expr_of_val_not_val vs))  end
  end.

Definition merge_values_list vs :=
  match vs with
  | Val v :: vs => merge_values v vs
  | [] => Val (immV [])
  | _ => NotVal (flatten (map expr_of_val_not_val vs))
  end.

Fixpoint to_val_instr (instr : administrative_instruction) : ValNotVal :=
  match instr with
  | AI_trap => Val trapV
  | AI_basic (BI_br i) => Val (brV (VH_base i [] []))
  | AI_basic BI_return => Val (retV (SH_base [] []))
  | AI_basic (BI_const v) => Val (immV [v])
  | AI_label n labe es =>
      match merge_values_list (map to_val_instr es) with
      | Val (brV i vh) => 
          match vh_decrease (VH_rec [] n labe vh []) with
          | Some vh' => Val (brV vh')
          | None => NotVal [instr]
          end 
      | Val (retV lh) => Val (retV (SH_rec [] n labe lh []))
      | Val (callHostV tf h cvs lh) => Val (callHostV tf h cvs (LL_label [] n labe lh []))
      | _ => NotVal [instr]
      end
 | AI_local n f es =>
      match merge_values_list (map to_val_instr es) with
      | Val (callHostV tf h cvs sh) =>
          Val (callHostV tf h cvs (LL_local [] n f sh []))
      | _ => NotVal [instr]
      end 
  | AI_call_host tf h cvs => Val (callHostV tf h cvs (LL_base [] []))
  | _ => NotVal [instr]
  end.

Definition to_val (e : expr) : option val :=
  match merge_values_list (map to_val_instr e) with
  | Val v => Some v
  | _ => None
  end.

Definition prim_step (e : expr) (s : state) (os : list observation) (e' : expr) (s' : state) (fork_es' : list expr) : Prop :=
  let '(σ, locs, inst) := s in
  let '(σ', locs', inst') := s' in
    reduce σ (Build_frame locs inst) e σ' (Build_frame locs' inst') e' /\ os = [] /\ fork_es' = [].

  
Lemma val_not_val_combine_app v1 v2 :
  expr_of_val_not_val (val_not_val_combine v1 v2) = of_val v1 ++ expr_of_val_not_val v2.
Proof.
  intros.
  destruct v1, v2 => //=.
  destruct v => //=.
  by rewrite - v_to_e_cat.
  destruct l => //=.
  destruct lh => //= ; rewrite - v_to_e_cat ; by rewrite app_assoc.
  all : try by destruct s => //= ; rewrite - v_to_e_cat ; by rewrite app_assoc.
  all : try by destruct (of_val v) => //=.
  all : try by destruct e => //=.
  all : try by destruct lh => //= ; rewrite app_comm_cons ; rewrite app_assoc.
  all : try by destruct s => //= ; rewrite app_comm_cons ; rewrite app_assoc.
  all : try by destruct l0 => //= ; rewrite app_comm_cons ; rewrite app_assoc.
  all : try by destruct l1 => //= ; rewrite - v_to_e_cat ; rewrite app_assoc.
Qed.

(* if we write val_not_val_combine_assoc v1 v2 as v1 + v2, this lemma is just plain
   associativity : v1 + (v2 + x) = (v1 + v2) + x. Because of typing, the phrasing is
   a little more complicated *)
Lemma val_not_val_combine_assoc v1 v2 x :
  val_not_val_combine v1 (val_not_val_combine v2 x) = 
    match val_not_val_combine v1 (Val v2) with
    | Val v3 => val_not_val_combine v3 x
    | NotVal es => NotVal (es ++ expr_of_val_not_val x)  end.
Proof.
  
  destruct v1 as [ vs1 | | n1 vh1 | sh1 | tf1 h1 vcs1 llh1 ],
      v2 as [ vs2 | | n2 vh2 | sh2 | tf2 h2 vcs2 llh2 ],
        x as [[ vs0 | | n0 vh0 | sh0 | tf0 h0 vcs0 llh0 ] | es0 ].

  all: simpl ; try done.

  all: (try destruct vs1).
  all: (try destruct vs2).
  all: (try destruct vs0).
  all: try destruct es0.

  all: simpl ; try done.
  
  all: (try rewrite - vh_push_const_app) ;
    (try rewrite - sh_push_const_app) ;
    (try rewrite - llh_push_const_app) ;
    (try rewrite - vh_append_app) ;
    (try rewrite - sh_append_app) ;
    (try rewrite - llh_append_app) ;
    (try rewrite - v_to_e_cat) ; 
    (try rewrite vh_append_nil) ;
    (try rewrite sh_append_nil) ;
    (try rewrite llh_append_nil) ;
    (try rewrite vh_push_const_nil) ;
    (try rewrite sh_push_const_nil) ;
    (try rewrite llh_push_const_nil) ;
    (try rewrite vh_append_nil) ;
    (try rewrite sh_append_nil) ;
    (try rewrite llh_append_nil) ;
    (try rewrite vh_push_const_nil) ;
    (try rewrite sh_push_const_nil) ;
    (try rewrite llh_push_const_nil) ;
    (try rewrite vh_push_const_append) ;
    (try rewrite sh_push_const_append) ;
    (try rewrite llh_push_const_append)
     .

     
  all : simpl ; try done.
  
  all:
    (try destruct (vfill _ _) eqn:Habs ; try by apply vfill_is_nil in Habs as [? _]) ;
    (try rewrite - Habs) ;
    (try destruct (sfill _ _) eqn:Habs' ; try by apply sfill_is_nil in Habs' as [? _]) ;
    (try rewrite - Habs') ;
    (try destruct (llfill _ _) eqn:Habs'' ; try by apply llfill_is_nil in Habs'' as [? _]) ;
    (try rewrite - Habs'') .

  
  all : simpl ; try done.


  all : try by repeat rewrite cats0.
  all : try by repeat rewrite app_comm_cons ; rewrite app_assoc.
  all : try by rewrite app_nil_r.
  all : try by rewrite - app_assoc.
  all : try by destruct vh0 => //= ; rewrite - v_to_e_cat - app_assoc.
  all : try by destruct sh0 => //= ; rewrite - v_to_e_cat - app_assoc.
  all : try by destruct llh0 => //= ; rewrite - v_to_e_cat - app_assoc.
  all : try by destruct (vfill vh2 _) eqn:Habs2 ;
    (try by apply vfill_is_nil in Habs2 as [? _]) ;
    rewrite - Habs2 ;
    destruct vh2 => //= ; rewrite - app_assoc.
  all : try by destruct (sfill sh2 _) eqn:Habs2 ;
    (try by apply sfill_is_nil in Habs2 as [? _]) ;
    rewrite - Habs2 ;
    destruct sh2 => //= ; rewrite - app_assoc.
  all : try by destruct (llfill llh2 _) eqn:Habs2 ;
    (try by apply llfill_is_nil in Habs2 as [? _]) ;
    rewrite - Habs2 ;
    destruct llh2 => //= ; rewrite - app_assoc.
  all : try by destruct vh2 => //= ; rewrite app_comm_cons app_assoc.
  all : try by destruct sh2 => //= ; rewrite app_comm_cons app_assoc.
  all : try by destruct llh2 => //= ; rewrite app_comm_cons app_assoc.
Qed.


Lemma merge_br i (vh : valid_holed i) es :
  merge_values (brV vh) es =
    Val (brV (vh_append vh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent vh.
  induction es => //=.
  intros. destruct vh ; simpl ; by rewrite cats0.
  intros.
  rewrite vh_append_app.
  rewrite - IHes.
  done.
Qed.

Lemma merge_return sh es :
  merge_values (retV sh) es =
    Val (retV (sh_append sh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent sh.
  induction es => //=.
  intros. destruct sh ; simpl ; by rewrite cats0.
  intros.
  rewrite sh_append_app.
  rewrite - IHes.
  done.
Qed.

Lemma merge_call_host tf h cvs sh es :
  merge_values (callHostV tf h cvs sh) es =
    Val (callHostV tf h cvs (llh_append sh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent sh.
  induction es => //=.
  intros. destruct sh ; simpl ; by rewrite cats0.
  intros.
  rewrite llh_append_app.
  rewrite - IHes.
  done.
Qed.

Lemma merge_trap es :
  merge_values trapV es =
    val_not_val_combine trapV (NotVal (flatten (map expr_of_val_not_val es))).
Proof.
  induction es => //=.
  destruct (expr_of_val_not_val a) eqn:Ha => //=.
Qed.


(* This next lemma proves two identities that had to be proven mutually recursively *)
Lemma merge_prepend_flatten vs :
  (forall v0, merge_values v0 vs = val_not_val_combine v0 (merge_values_list vs)) /\
    flatten (map expr_of_val_not_val vs) = expr_of_val_not_val (merge_values_list vs).
Proof.
  induction vs => //=. 
  - split => //. destruct v0 => //=.
    + by rewrite cats0.
    + by rewrite vh_append_nil.
    + by rewrite sh_append_nil.
    + by rewrite llh_append_nil.
  - destruct a => //=.
    + destruct IHvs as [IHvs1 IHvs2].
      rewrite (IHvs1 v).
      split.
      * intro v0 ; rewrite val_not_val_combine_assoc.
        destruct (val_not_val_combine v0 (Val v)) eqn:Hv0a.
        -- done.
        -- by rewrite IHvs2.
      * rewrite IHvs2.
        by rewrite val_not_val_combine_app.
    + split ; last done.
      destruct v0 => //=.
      * by rewrite app_assoc.
      * destruct e => //=.
        by rewrite merge_trap.
      * rewrite merge_br.
        by rewrite vh_append_app.
      * rewrite merge_return.
        by rewrite sh_append_app. 
      * rewrite merge_call_host.
        by rewrite llh_append_app.
Qed.

(* For convenience, we provide lemmas for usage of each identity separately *)
Lemma merge_prepend v0 vs :
  merge_values v0 vs = val_not_val_combine v0 (merge_values_list vs).
Proof. by edestruct merge_prepend_flatten as [? _]. Qed.

Lemma merge_flatten vs :
  flatten (map expr_of_val_not_val vs) = expr_of_val_not_val (merge_values_list vs).
Proof. by edestruct merge_prepend_flatten as [_ ?]. Qed.

Lemma of_to_val_instr e : expr_of_val_not_val (to_val_instr e) = [e].
Proof.
  cut (forall n, size_of_instruction e < n -> expr_of_val_not_val (to_val_instr e) = [e]).
  intro H ; apply (H (S (size_of_instruction e))) ; try lia.
  intro n.
  generalize dependent e. 
  induction n ; first lia.
  intros e Hsize.
  destruct e => //=.
  - destruct b => //=. 
  - { destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge => //.
      destruct v => //.
      { destruct i => //.
        destruct (vh_decrease _) eqn:Hvh => //=.
        replace (vfill v [AI_basic (BI_br (S i))]) with l0 ; first done.
        remember (length_rec l0) as m'.
        assert (length_rec l0 < S m') ; first lia.
        remember (S m') as m.
        clear Heqm Heqm' m'.
        generalize dependent l0.
        generalize dependent lh ; generalize dependent v ; generalize dependent i.
        induction m => //= ; first by intros ; lia.
        intros.
        destruct l0 => //=.
        destruct a ; try by inversion Hmerge.
        destruct b ; try by inversion Hmerge.
        + simpl in Hmerge.
          rewrite merge_br in Hmerge.
          inversion Hmerge.
          apply Eqdep.EqdepTheory.inj_pair2 in H2 ; subst lh ; clear Hmerge.
          simpl in Hvh.
          inversion Hvh ; subst ; clear Hvh => //=.
          rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
          with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.
      + simpl in Hmerge.
        rewrite merge_return in Hmerge.
        inversion Hmerge.
      + simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          last by inversion Hmerge.
        destruct v1 ; inversion Hmerge.
        assert (existT i0 (vh_push_const lh0 [v0]) =
                  existT (S i) (vh_push_const (match H1 in (_ = w) return (valid_holed w)
                                               with Logic.eq_refl => lh0 end) [v0])).
        by destruct H1.
        rewrite H0 in H2.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        rewrite <- H2 in Hvh.
        apply vh_decrease_push_const_inv in Hvh as (vh'' & Hvh & Hpush).
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm i vh'' match H1 in _ = w return valid_holed w with
                          | Logic.eq_refl => lh0 end Hvh l0) => //.
        rewrite H1.
        destruct vh'' ; simpl in Hpush ; subst v => //=.
        destruct i0 => //.
        pose proof (eq_add_S _ _ H1) as Hi.
        assert (H1 = f_equal S Hi) as Hproof.
        apply Eqdep.EqdepTheory.UIP.
        by rewrite Hproof ; destruct Hi.
        specialize (cons_length_rec (AI_basic (BI_const v0)) l0).
        lia.
      + simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      + rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v0 => // ; (try by rewrite merge_return in Hmerge) ;
                      try by rewrite merge_call_host in Hmerge.
        destruct (vh_decrease (VH_rec _ _ _ _ _)) eqn:Hdecr => //.
        rewrite merge_br in Hmerge.
        replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
        inversion Hmerge.
        assert (existT i0 (vh_append v0 l0) =
                  existT (S i) (vh_append match H1 in _ = w return valid_holed w with
                                            Logic.eq_refl => v0 end l0)) ;
          first by destruct H1.
        rewrite H0 in H2 ; clear H0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        unfold vh_decrease in Hdecr ; fold vh_decrease in Hdecr.
        destruct i0 => //.
        destruct (vh_decrease lh0) eqn:Hdecr0 => //.
        inversion Hdecr.
        rewrite - H3 in H2.
        pose proof (eq_add_S _ _ H1) as Hi.
        assert (H1 = f_equal S Hi) as Hproof.
        apply Eqdep.EqdepTheory.UIP.
        replace match H1 in (_ = w) return (valid_holed w) with
         | Logic.eq_refl => VH_rec [] n1 l1 v1 []
                end with (VH_rec [] n1 l1 match Hi in _ = w return valid_holed w with
                                          | Logic.eq_refl => v1 end []) in H2 ;
          last by rewrite Hproof ; destruct Hi.
        simpl in H2.
        rewrite - H2 in Hvh.
        unfold vh_decrease in Hvh ; fold vh_decrease in Hvh.
        destruct i => //.
        destruct (vh_decrease match Hi in _ = w return valid_holed w
                              with Logic.eq_refl => v1 end) eqn:Hdecr1 => //.
        inversion Hvh => //=.
        rewrite (IHm i0 v1 lh0 Hdecr0 l2).
        clear - Hdecr1.
        apply (vfill_decrease [AI_basic (BI_br (S i0))]) in Hdecr1.
        rewrite - Hdecr1.
        clear.
        destruct Hi.
        done.
        simpl in Hsize. simpl. lia.
        done.
        unfold length_rec in H.
        rewrite map_cons in H.
        simpl in H. unfold length_rec. lia.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.
      + simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hl1 => //.
        destruct v0 => //.
        rewrite merge_call_host in Hmerge.
        inversion Hmerge.
      + simpl in Hmerge. rewrite merge_call_host in Hmerge.
        simpl in Hmerge.
        destruct (flatten _) => //=.
    }
    { simpl. 
    replace (sfill s [AI_basic BI_return]) with l0 ; first done.
    remember (length_rec l0) as m'.
    assert (length_rec l0 < S m') ; first lia.
    remember (S m') as m.
    clear Heqm Heqm' m'.
    generalize dependent l0.
    generalize dependent s.
    induction m => //= ; first by intros ; lia.
    intros.
    destruct l0 => //=.
    destruct a ; try by inversion Hmerge.
    destruct b ; try by inversion Hmerge.
    + simpl in Hmerge.
      rewrite merge_br in Hmerge.
      inversion Hmerge.
    + simpl in Hmerge.
      rewrite merge_return in Hmerge.
      inversion Hmerge => /=.
      rewrite map_map.
      replace (flatten
                 (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
        with l0 ; first done.
      clear - IHn Hsize.
      induction l0 => //=.
      rewrite IHn ; last by simpl in Hsize ; lia.
      simpl.
      rewrite -> IHl0 at 1 => //=.
      simpl in Hsize.
      lia.
    + simpl in Hmerge.
      rewrite merge_prepend in Hmerge.
      destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
        last by inversion Hmerge.
      destruct v0 ; inversion Hmerge.
      assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
      rewrite (IHm s0 l0) => //=.
      destruct s0 => //=.
      specialize (cons_length_rec (AI_basic (BI_const v)) l0).
      lia.
    + simpl in Hmerge.
      rewrite merge_trap in Hmerge.
      destruct (flatten _) => //=.
    + rewrite map_cons in Hmerge.
      unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
      destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
      destruct v => //.
      destruct (vh_decrease _) => //.
      by rewrite merge_br in Hmerge.
      rewrite merge_return in Hmerge.
      replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
      inversion Hmerge.
      simpl.
      rewrite (IHm s0 l2) => //.
      simpl in Hsize. simpl. lia.
      unfold length_rec in H.
      rewrite map_cons in H.
      simpl in H. unfold length_rec. lia.
      clear - IHn Hsize.
      induction l0 => //=.
      rewrite IHn ; last by simpl in Hsize ; lia.
      simpl.
      rewrite -> IHl0 at 1 => //=.
      simpl in Hsize.
      lia.
    + simpl in Hmerge.
      destruct (merge_values_list _) => //=.
      destruct v => //=.
      rewrite merge_call_host in Hmerge. done.
    + simpl in Hmerge.
      destruct (merge_values_list _) => //=.
      destruct v => //=.
      rewrite merge_call_host in Hmerge => //.
    + simpl in Hmerge.
      rewrite merge_call_host in Hmerge.
      simpl in Hmerge.
      destruct (flatten _) => //=. } 
    simpl. replace (llfill l2 [AI_call_host f h l1]) with l0 ; first done.
      remember (length_rec l0) as m'. 
      assert (length_rec l0 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l0.
      generalize dependent l2.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l0 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      + simpl in Hmerge.
        rewrite merge_br in Hmerge.
        inversion Hmerge.
      + simpl in Hmerge.
        rewrite merge_return in Hmerge.
        inversion Hmerge => //. 
    + simpl in Hmerge.
      rewrite merge_prepend in Hmerge.
      destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
        last by inversion Hmerge.
      destruct v0 ; inversion Hmerge. subst.
      assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
      erewrite (IHm _ l0) => //=.
      destruct l4 => //=. 
      specialize (cons_length_rec (AI_basic (BI_const v)) l0).
      lia.
    + simpl in Hmerge.
      rewrite merge_trap in Hmerge.
      destruct (flatten _) => //=.
    + rewrite map_cons in Hmerge.
      unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
      destruct (merge_values_list (map to_val_instr l4)) eqn:Hmerge2 => //.
      destruct v => //.
      destruct (vh_decrease _) => //.
      by rewrite merge_br in Hmerge.
      by rewrite merge_return in Hmerge.
      rewrite merge_call_host in Hmerge.
      replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
      inversion Hmerge. subst.
      simpl.
      erewrite (IHm _ l4) => //.
      simpl in Hsize. simpl. lia.
      unfold length_rec in H.
      rewrite map_cons in H.
      simpl in H. unfold length_rec. lia.
      clear - IHn Hsize.
      induction l0 => //=.
      rewrite IHn ; last by simpl in Hsize ; lia.
      simpl.
      rewrite -> IHl0 at 1 => //=.
      simpl in Hsize.
      lia.
    + simpl in Hmerge.
      destruct (merge_values_list _) eqn:Hmerge2 => //.
      destruct v => //.
      rewrite merge_call_host in Hmerge.
      inversion Hmerge ; subst.
      simpl.
      erewrite (IHm _ l3) => //=.
      replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 ; first done.
      clear - IHn Hsize.
      induction l0 => //=.
      rewrite IHn ; last by simpl in Hsize ; lia.
      simpl.
      rewrite -> IHl0 at 1 => //=.
      simpl in Hsize.
      lia.
      simpl in Hsize.
      lia.
      unfold length_rec in H.
      simpl in H.
      unfold length_rec. lia.
    + simpl in Hmerge.
      rewrite merge_call_host in Hmerge.
      inversion Hmerge => /=.
      rewrite map_map.
      replace (flatten
                 (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
        with l0 ; first done.
      clear - IHn Hsize.
      induction l0 => //=.
      rewrite IHn ; last by simpl in Hsize ; lia.
      simpl.
      rewrite -> IHl0 at 1 => //=.
      simpl in Hsize.
      lia.  }
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //=.
    replace l with (llfill l1 [AI_call_host f0 h l0]) ; first done.
    remember (length_rec l) as m'. 
    assert (length_rec l < S m') ; first lia.
    remember (S m') as m.
    clear Heqm Heqm' m'.
    generalize dependent l.
    generalize dependent l1.
    induction m => //= ; first by intros ; lia.
    intros.
    destruct l => //=.
    destruct a ; try by inversion Hmerge.
    destruct b ; try by inversion Hmerge.
    + simpl in Hmerge.
      rewrite merge_br in Hmerge.
      inversion Hmerge.
    + simpl in Hmerge.
      rewrite merge_return in Hmerge.
      inversion Hmerge => //. 
    + simpl in Hmerge.
      rewrite merge_prepend in Hmerge.
      destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
        last by inversion Hmerge.
      destruct v0 ; inversion Hmerge. subst.
      assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
      erewrite <- (IHm _ l) => //=.
      destruct l3 => //=. 
      specialize (cons_length_rec (AI_basic (BI_const v)) l).
      lia.
    + simpl in Hmerge.
      rewrite merge_trap in Hmerge.
      destruct (flatten _) => //=.
    + rewrite map_cons in Hmerge.
      unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
      destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
      destruct v => //.
      destruct (vh_decrease _) => //.
      by rewrite merge_br in Hmerge.
      by rewrite merge_return in Hmerge.
      rewrite merge_call_host in Hmerge.
      inversion Hmerge ; subst. simpl.
      replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l.
      erewrite <- (IHm _ l3) => //.
      simpl in Hsize. simpl. lia.
      unfold length_rec in H.
      rewrite map_cons in H.
      simpl in H. unfold length_rec. lia.
      clear - IHn Hsize.
      induction l => //=.
      rewrite IHn ; last by simpl in Hsize ; lia.
      simpl.
      rewrite -> IHl at 1 => //=.
      simpl in Hsize.
      lia.
    + simpl in Hmerge.
      destruct (merge_values_list _) eqn:Hmerge2 => //.
      destruct v => //.
      rewrite merge_call_host in Hmerge.
      inversion Hmerge ; subst.
      simpl.
      erewrite (IHm _ l2) => //=.
      replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l ; first done.
      clear - IHn Hsize.
      induction l => //=.
      rewrite IHn ; last by simpl in Hsize ; lia.
      simpl.
      rewrite -> IHl at 1 => //=.
      simpl in Hsize.
      lia.
      simpl in Hsize.
      lia.
      unfold length_rec in H.
      simpl in H.
      unfold length_rec. lia.
    + simpl in Hmerge.
      rewrite merge_call_host in Hmerge.
      inversion Hmerge => /=.
      rewrite map_map.
      replace (flatten
                 (map (λ x, expr_of_val_not_val (to_val_instr x)) l))
        with l ; first done.
      clear - IHn Hsize.
      induction l => //=.
      rewrite IHn ; last by simpl in Hsize ; lia.
      simpl.
      rewrite -> IHl at 1 => //=.
      simpl in Hsize.
      lia.
Qed.

Lemma flatten_simplify es :
  flatten (map expr_of_val_not_val (map to_val_instr es)) = es.
Proof.
  induction es => //=.
  rewrite of_to_val_instr IHes => //=.
Qed.
  

Lemma merge_to_val es :
  expr_of_val_not_val (merge_values_list (map to_val_instr es)) = es.
Proof.
  induction es => //=.
  specialize (of_to_val_instr a) ; intro Ha'.
  destruct (to_val_instr a) eqn:Ha => /= ; simpl in Ha'.
  - rewrite merge_prepend.
    remember (merge_values_list _) as vnv.
    specialize (val_not_val_combine_app v vnv) ; intro H.
    destruct (val_not_val_combine v vnv) eqn:Hv ; simpl in H ; simpl ; 
      rewrite H Ha' IHes ; subst ; done.
  - rewrite Ha'.
    rewrite flatten_simplify => //=.
Qed.


Lemma of_to_val es v : to_val es = Some v -> of_val v = es.
Proof. unfold to_val. specialize (merge_to_val es) ; intro H.
       destruct (merge_values_list _) => //.
       simpl in H. intro H' ; inversion H' ; by subst. Qed.


Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  destruct v.
  - induction l => //=.
    unfold to_val.
    unfold merge_values_list.
    rewrite map_cons.
    unfold to_val_instr.
    fold to_val_instr.
    unfold to_val in IHl.
    unfold of_val in IHl.    
    destruct (map to_val_instr _) eqn:Hmap ; try by inversion IHl.
    destruct (merge_values_list (v :: l0)) eqn:Hmerge ; try by inversion IHl.
    rewrite merge_prepend.
    rewrite Hmerge.
    inversion IHl ; subst => //=.
  - done.
  - unfold of_val, to_val. 
    cut (forall i (vh : valid_holed i) j, merge_values_list (map to_val_instr (vfill vh [AI_basic (BI_br (j + i))])) = Val (brV (vh_increase_repeat vh j))).
    intro H. specialize (H i lh 0).
    unfold vh_increase_repeat in H. simpl in H.
    by rewrite H.
    clear i lh.
    induction vh as [i bef aft | i bef n es vh Hvh aft ] => //= ; intro j.
    { induction bef => //=.
      { rewrite merge_br => //= ; rewrite flatten_simplify.
        assert (VH_base (j + i) [] aft = vh_increase_repeat (VH_base i [] aft) j) as H ;
          last by rewrite H.
        induction j ; unfold vh_increase_repeat => //=.
        fold vh_increase_repeat.
        rewrite - IHj => //=.
      } 
      rewrite merge_prepend.
      destruct (merge_values_list _) eqn:Hmerge => //.
      inversion IHbef ; subst v => //=.
      by rewrite - vh_increase_repeat_push_const. } 
    induction bef.
    { simpl. specialize (Hvh (S j)).
      replace (BI_br (S j + i)) with (BI_br (j + S i)) in Hvh ; last by rewrite - S_plus.
      rewrite Hvh => /=.
      
      rewrite vh_decrease_increase.
      rewrite merge_br.
      rewrite flatten_simplify => //=.
      rewrite vh_increase_repeat_rec.
      destruct (S_plus j i) => //.
    }
    simpl.
    rewrite merge_prepend.
    destruct (merge_values_list _) eqn:Hmerge => //.
    inversion IHbef ; subst v => //.
    simpl.
    by rewrite - vh_increase_repeat_push_const.
  - unfold of_val, to_val.
    induction s.
    + induction l => //=.
      * rewrite merge_return.
        rewrite flatten_simplify.
        done.
      * rewrite merge_prepend.
        destruct (merge_values_list _) => //=.
        inversion IHl ; subst => //=.
    + induction l => /=.
      * destruct (merge_values_list _) => //.
        inversion IHs ; subst => /=.
        rewrite merge_return.
        rewrite flatten_simplify.
        done.
      * rewrite merge_prepend.
        clear IHs.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //=.
  - unfold of_val, to_val => //=.
    induction l0 => //=.
    + induction l0 => //=.
      * rewrite merge_call_host.
        rewrite flatten_simplify => //.
      * rewrite merge_prepend.
        destruct (merge_values_list _) => //=.
        inversion IHl0 ; subst => //.
    + induction l0 => //=.
      * destruct (merge_values_list _) => //.
        inversion IHl0 ; subst => /=.
        rewrite merge_call_host.
        rewrite flatten_simplify => //.
      * rewrite merge_prepend.
        clear IHl0.
        destruct (merge_values_list _) => //.
        inversion IHl1 ; subst => //.
    +  induction l0 => //=.
      * destruct (merge_values_list _) => //.
        inversion IHl0 ; subst => /=.
        rewrite merge_call_host.
        rewrite flatten_simplify => //.
      * rewrite merge_prepend.
        clear IHl0.
        destruct (merge_values_list _) => //.
        inversion IHl1 ; subst => //.
Qed.


Lemma to_val_cons_is_none_or_cons : forall e0 e r,
  to_val (e0 :: e)%SEQ = r -> is_none_or (fun l => match l with | immV v => v != [] | _ => true end) r.
Proof.
  intros e0 e r H ; subst r.
  cut (forall n e0 e, length_rec (e0 :: e) < n ->  is_none_or (λ l : val, match l with
                         | immV v => v != []
                         | _ => true
                                                              end) (to_val (e0 :: e)%SEQ)).
  intro H ; apply (H (S (length_rec (e0 :: e)))) ; try lia.
  clear e e0.
  induction n => //= ; first lia.
  intros e0 e Hlen.
  destruct e0 => //.
  destruct b => //= ; unfold to_val => /=.
  - rewrite merge_br => //.
  - rewrite merge_return => //.
  - rewrite merge_prepend => /=.
    destruct e => //.
    assert (length_rec (a :: e) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec => //=. lia.
    apply IHn in H.
    unfold to_val in H.
    destruct (merge_values_list _) => //.
    destruct v0 => //.
  - unfold to_val => //=.
    rewrite merge_trap => /=.
    rewrite flatten_simplify => /=.
    destruct e => //=.
  - unfold to_val.
    unfold merge_values_list, map, to_val_instr.
    fold to_val_instr.
    destruct l0 ; first done.
    assert (length_rec (a :: l0) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec.
    rewrite map_cons.
    simpl.
    lia.
    apply IHn in H.
    unfold is_none_or in H.
    unfold to_val in H.
    destruct (merge_values_list _) => //.
    destruct v => //.
    + destruct (vh_decrease _) eqn:Hdecr => //=.
      rewrite merge_br => //=.
    + rewrite merge_return => //=.
    + rewrite merge_call_host => //=.
  - unfold to_val => //=.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //.
    rewrite merge_call_host => //.
  - unfold to_val => //=. rewrite merge_call_host => //=.
Qed.
    
Lemma to_val_trap_is_singleton : ∀ e,
    to_val e = Some trapV -> e = [::AI_trap].
Proof.
  intro e.
  destruct e => //=.
  destruct a => //=.
  destruct b => //= ; unfold to_val => /=.
  - by rewrite merge_br.
  - by rewrite merge_return.
  - rewrite merge_prepend.
    destruct (merge_values_list _) => //=.
    destruct v0 => //=.
  - unfold to_val => /=.
    destruct e => //=.
    rewrite of_to_val_instr.
    done.
  - unfold to_val => /=.
    destruct (merge_values_list _) => //=.
    destruct v => //=.
    destruct i => //=.
    destruct (vh_decrease _) => //=.
    rewrite merge_br => //=.
    rewrite merge_return => //=.
    rewrite merge_call_host => //=.
  - unfold to_val => //=.
    destruct (merge_values_list _) => //.
    destruct v => //.
    rewrite merge_call_host => //.
  - unfold to_val => //= ; rewrite merge_call_host => /=.
    destruct (flatten _) => //=.
Qed. 


Lemma flatten_map_expr_of_val_not_val vs :
  flatten (map expr_of_val_not_val vs) =
    expr_of_val_not_val (merge_values_list vs).
Proof.
  induction vs => //=.
  destruct a => //=.
  rewrite IHvs.
  rewrite merge_prepend.
  by rewrite val_not_val_combine_app.
Qed.

Lemma merge_app vs1 vs2:
  merge_values_list (vs1 ++ vs2) =
    match (merge_values_list vs1) with
    | Val v1 => val_not_val_combine v1 (merge_values_list vs2)
    | NotVal e1 => NotVal (e1 ++ expr_of_val_not_val (merge_values_list vs2)) end.
Proof.
  induction vs1 => //=.
  { destruct (merge_values_list vs2) => //.
    destruct v => //.
    by rewrite vh_push_const_nil.
    by rewrite sh_push_const_nil.
    by rewrite llh_push_const_nil.
  }
  destruct a => //.
  { do 2 rewrite merge_prepend.
    rewrite IHvs1.  
    destruct (merge_values_list vs1) eqn:Hvs1 => //=.
    by rewrite val_not_val_combine_assoc.
    destruct v => //=.
    by rewrite app_assoc. 
    destruct e => //=.
    destruct (merge_values_list vs2) ;
      by rewrite vh_append_app.
    destruct (merge_values_list vs2) ;
      by rewrite sh_append_app.
    destruct (merge_values_list vs2) ;
      by rewrite llh_append_app.
    } 
  rewrite map_app.
  rewrite flatten_cat.
  rewrite (flatten_map_expr_of_val_not_val vs2).
  by rewrite catA.
Qed.

Lemma to_val_is_immV es vs :
  to_val es = Some (immV vs) -> es = map (λ x, AI_basic (BI_const x)) vs.
Proof.
  generalize dependent vs.
  induction es => //=.
  intros.
  unfold to_val in H.
  simpl in H.
  inversion H => //=.

  intros.
  unfold to_val in H ; simpl in H.
  destruct (to_val_instr a) eqn:Ha => //.
  rewrite merge_prepend in H.
  unfold to_val in IHes.
  destruct (merge_values_list _) => //.
  destruct v, v0 => //.
  simpl in H.
  inversion H ; subst.
  erewrite IHes => //.
  destruct a => //.
  destruct b => //.
  inversion Ha => //.
  simpl in Ha.
  destruct (merge_values_list _) => //.
  destruct v => //.
  destruct i => //.
  destruct (vh_decrease _) => //.
  simpl in Ha.
  destruct (merge_values_list _) => //.
  destruct v => //.
  simpl in H.
  destruct l => //.
  simpl in H.
  destruct l => //.
  simpl in H.
  destruct (vfill lh _) => //.
  simpl in H.
  destruct (sfill _ _) => //.
  simpl in H.
  destruct (llfill _ _) => //. 
  destruct v => //.
  destruct e => //.
Qed.

Lemma merge_is_not_val es es' :
  merge_values_list (map to_val_instr es) = NotVal es' -> es = es'.
Proof.
  generalize dependent es'.
  induction es => //= ; intro es'.
  destruct (to_val_instr a) eqn:Ha => //=.
  { destruct a => //= ; simpl in Ha.
    { destruct b => //= ; inversion Ha ; subst.
      by rewrite merge_br.
      by rewrite merge_return.
      rewrite merge_prepend.
      destruct (merge_values_list _) eqn:Hmerge => //=.
      destruct v => //=.
      intro H ; inversion H ; subst.
      rewrite (to_val_trap_is_singleton (e := es)) => //.
      unfold to_val ; by rewrite Hmerge.
      
      intro H ; inversion H.
      by erewrite IHes. }
    { inversion Ha.
      rewrite merge_prepend.
      destruct (merge_values_list _) eqn:Hmerge => //=.
      assert (to_val es = Some v0) ; first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H.
      rewrite H.
      destruct es => //.
      by intro H' ; inversion H'.
      erewrite IHes => //.
      destruct e => //.
      by intro H ; inversion H. }
    destruct (merge_values_list (map _ l0)) eqn:Hmerge => //.
    destruct v0 => //.
    destruct i => //.
    destruct (vh_decrease _) => //.
    inversion Ha.

    rewrite merge_br => //.
    inversion Ha.
    rewrite merge_return => //.
    inversion Ha.
    inversion Ha ; subst.
    rewrite merge_call_host => //.
    destruct (merge_values_list (map to_val_instr l)) eqn:Hl => //.
    destruct v0 => //.
    inversion Ha => //.
    rewrite merge_call_host => //.
    inversion Ha.
    rewrite merge_call_host => //.
  }
  rewrite flatten_simplify.
  intro H ; inversion H.
  destruct a => // ; try by inversion Ha. 
  destruct b => // ; try by inversion Ha.
  simpl in Ha.
  destruct (merge_values_list (map _ l0)) => // ; try by inversion Ha. 
  destruct v => // ; try by inversion Ha.
  destruct i => // ; try by inversion Ha.
  destruct (vh_decrease lh) ; try by inversion Ha.
  simpl in Ha.
  destruct (merge_values_list (map _ l)) => // ; try by inversion Ha.
  destruct v => // ; by inversion Ha.
  
Qed. 

Lemma extend_retV sh es :
  to_val (of_val (retV sh) ++ es) = Some (retV (sh_append sh es)).
Proof.
  unfold to_val.
  rewrite map_app.
  rewrite merge_app.
  specialize (to_of_val (retV sh)) as H.
  unfold to_val in H.
  destruct (merge_values_list _) => //.
  inversion H => /=.
  destruct (merge_values_list _) eqn:Hmerge => //=.
  erewrite of_to_val.
  done.
  unfold to_val.
  by rewrite Hmerge.
  by apply merge_is_not_val in Hmerge ; subst.
Qed.


Lemma splits_vals_e_to_val_hd : forall e1 e es vs,
    split_vals_e e1 = (vs, e :: es) ->
    to_val e1 = None
    ∨ (vs = [] ∧ to_val e1 = Some trapV)
    ∨ (∃ i, e = AI_basic (BI_br i) ∧ to_val e1 = Some (brV (VH_base i vs es)))
    ∨ (e = AI_basic BI_return ∧ to_val e1 = Some (retV (SH_base vs es)))
    \/ (∃ tf h vcs, e = AI_call_host tf h vcs /\ to_val e1 = Some (callHostV tf h vcs ((LL_base vs es))))
    \/ (∃ i n es' LI (vh : valid_holed i),
          e = AI_label n es' LI /\ to_val e1 = Some (brV (VH_rec vs n es' vh es))
          /\ vfill vh [AI_basic (BI_br (S i))] = LI)
    \/ (∃ n es' LI sh, e = AI_label n es' LI /\ to_val e1 = Some (retV (SH_rec vs n es' sh es))
                      /\ sfill sh [AI_basic BI_return] = LI)
    \/ (∃ tf h vcs n es' LI sh, e = AI_label n es' LI /\ to_val e1 = Some (callHostV tf h vcs ((LL_label vs n es' sh es)))
                               /\ llfill sh [AI_call_host tf h vcs] = LI)
    \/ (∃ tf h vcs n f LI sh, e = AI_local n f LI /\ to_val e1 = Some (callHostV tf h vcs ((LL_local vs n f sh es)))
                             /\ llfill sh [AI_call_host tf h vcs] = LI)
.
Proof.
  intros e1.
  induction e1 ; intros e es vs Hsplit.
  { destruct vs => //. } 
  { destruct vs => //.
    { simpl in Hsplit.
      destruct a => // ; try by left.
      destruct b => // ; simplify_eq;try by left.
      - unfold to_val => /=.
        rewrite merge_br flatten_simplify.
        right. right. left. eexists. eauto.
      - unfold to_val => /=.
        rewrite merge_return flatten_simplify.
        right. right. right. left. auto.
      - destruct (split_vals_e e1). simplify_eq.
      - destruct e1. right;left;auto.
      - left.
        unfold to_val => /=. destruct a => //.
        destruct b => //. rewrite of_to_val_instr => //.
      - simpl.
        destruct (merge_values_list _) eqn:Hmerge => //.
        destruct v => //.
      - inversion Hsplit ; subst.
        destruct (to_val (_ :: _)) eqn:Htv ; try by left.
        right. right. right. right.
        unfold to_val in Htv => /=.
        simpl in Htv. destruct (merge_values_list _) eqn:Hmerge => //.
        destruct v0 => //.
        + destruct i => //.
          destruct (vh_decrease _) eqn:Hdecr => //.
          rewrite merge_br flatten_simplify in Htv.
          inversion Htv ; subst.
          right ; left. repeat eexists _.
          repeat split => //.
          assert (to_val l0 = Some (brV lh)).
          unfold to_val ; by rewrite Hmerge.
          apply of_to_val in H.
          unfold of_val in H.
          unfold vfill ; fold vfill.
          rewrite - (vfill_decrease _ Hdecr) => //.
        + rewrite merge_return flatten_simplify in Htv.
          inversion Htv ; subst.
          right ; right ; left. repeat eexists _.
          repeat split => //.
          assert (to_val l0 = Some (retV s)).
          unfold to_val ; by rewrite Hmerge.
          apply of_to_val in H.
          unfold of_val in H => //.
        + rewrite merge_call_host flatten_simplify in Htv.
          inversion Htv ; subst.
          right ; right ; right. left. repeat eexists _.
          repeat split => //.
          assert (to_val l0 = Some (callHostV f h l1 l2)).
          unfold to_val ; by rewrite Hmerge.
          apply of_to_val in H.
          unfold of_val in H => //.
      - inversion Hsplit ; subst.
        destruct (to_val (_ :: _)) eqn:Htv ; try by left.
        right. right. right. right.
        unfold to_val in Htv => /=.
        simpl in Htv.
        destruct (merge_values_list _) eqn:Hmerge => //.
        destruct v0 => //.
        rewrite merge_call_host flatten_simplify in Htv.
        inversion Htv ; subst.
        do 4 right. repeat eexists _.
        repeat split => //.
        fold (of_val (callHostV f0 h l0 l1)).
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
      - unfold to_val => /=.
        rewrite merge_call_host flatten_simplify.
        inversion Hsplit.
        right. right. right. right. left. repeat eexists.
    }
    { simpl in Hsplit.
      destruct a => //.
      destruct b => //.
      destruct (split_vals_e e1) eqn:Hsome.
      assert ((l, l0) = (vs, (e :: es)%SEQ)) as Heq%IHe1.
      { simplify_eq. auto. }
      destruct Heq as [?|[[??]|[[?[??]]|[[??]|[(?&?&?&?&?)|[(?&?&?&?&?&?&?&?)|[(?&?&?&?&?&?&?)|[(?&?&?&?&?&?&?&?&?&?)|(?&?&?&?&?&?&?&?&?&?)]]]]]]]] ;
        unfold to_val => /= ; rewrite merge_prepend.
      { left. unfold to_val in H. destruct (merge_values_list _) => //. } 
      { left. unfold to_val in H0. destruct (merge_values_list _) => //. by inversion H0. }
      { unfold to_val in H0. destruct (merge_values_list _) => //.
        inversion H0 => /=. right. right. left. eexists _.
        split => //=. inversion Hsplit ; subst => //. }
      { unfold to_val in H0. destruct (merge_values_list _) => //.
        inversion H0 => /=. right. right. right. left.
        split;auto. by inversion Hsplit. }
      { unfold to_val in H0. destruct (merge_values_list _) => //.
        inversion H0 => /=. right. right. right. right. left. repeat eexists.
        by inversion Hsplit. by inversion Hsplit. } 
      { unfold to_val in H0. destruct (merge_values_list _) => //.
        inversion H0 => /=. right. right. right. right. right. left.
        repeat eexists _. repeat split => //. by inversion Hsplit. }
      { unfold to_val in H0. destruct (merge_values_list _) => //.
        inversion H0 => /=. do 6 right.  left. repeat eexists _. repeat split => //.
        by inversion Hsplit. }
      { unfold to_val in H0. destruct (merge_values_list _) => //. 
        inversion H0 => /=. do 7 right. left. repeat eexists _. repeat split => //.
        by inversion Hsplit. }
      { unfold to_val in H0. destruct (merge_values_list _) => //.
        inversion H0 => /=. do 8 right. repeat eexists _. repeat split => //.
        by inversion Hsplit. } 
    }  }
Qed.

Lemma to_val_None_prepend: forall es1 es2,
  to_val es2 = None ->
  to_val (es1 ++ es2) = None
  ∨ (∃ i (vh : valid_holed i), to_val es1 = Some (brV vh))
  ∨ (∃ sh, to_val es1 = Some (retV sh))
  \/ (∃ tf h cvs sh, to_val es1 = Some (callHostV tf h cvs sh)).
Proof.
  move => es1 es2 H.
  induction es1;try by left.
  destruct a;try by left.
  destruct b; try by left.
  - right ; left.
    unfold to_val => /=.
    rewrite merge_br flatten_simplify.
    eauto.
  - right ; right.
    unfold to_val => /=.
    rewrite merge_return flatten_simplify.
    eauto.
  - destruct IHes1 as [?|[[?[??]]|[[??]|(?&?&?&?&?)]]].
    { simpl. unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //=.
      by left. }
    { right;left. eexists _, (vh_push_const _ _). unfold to_val => /=.
      rewrite merge_prepend. unfold to_val in H0.
      destruct (merge_values_list _) ; last done. inversion H0 => //=. } 
    { right;right. left. unfold to_val => /=. rewrite merge_prepend.  unfold to_val in H0.
      destruct (merge_values_list _) => //.  inversion H0 => //=. by repeat eexists. }
    { right;right; right. unfold to_val => /=. rewrite merge_prepend. unfold to_val in H0.
      destruct (merge_values_list _) => //. inversion H0 => //=.  by repeat eexists. }
  - unfold to_val => /=. rewrite merge_trap => /=. rewrite flatten_simplify.
    destruct (es1 ++ es2) eqn:Habs => //.
    apply app_eq_nil in Habs as [-> ->].
    destruct IHes1 as [Habs | [ (? & ? & Habs) | [ [ ? Habs ] | (?&?&?&?& Habs)]]] ; by inversion Habs.
    by left.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => // ; try by left.
    destruct v => // ; try by left.
    + destruct i => // ; try by left.
      destruct (vh_decrease _) ; try by left.
      rewrite merge_br flatten_simplify.
      right ; left.
      rewrite merge_br flatten_simplify.
      by repeat eexists.
    + rewrite merge_return flatten_simplify.
      right ; right. left.
      rewrite merge_return flatten_simplify.
      by eexists.
    + rewrite merge_call_host flatten_simplify.
      right ; right ; right.
      rewrite merge_call_host flatten_simplify.
      by repeat eexists.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hl ; try by left.
    destruct v ; try by left.
    repeat right ; repeat eexists.
    rewrite merge_call_host flatten_simplify.
    done.
  - unfold to_val => /=.
    repeat right ; repeat eexists.
    rewrite merge_call_host flatten_simplify.
    done.
Qed.

Lemma to_val_None_prepend_const : forall es1 es2,
    const_list es1 ->
  to_val es2 = None ->
  to_val (es1 ++ es2) = None.
Proof.
  move => es1 es2 H H'.
  eapply to_val_None_prepend in H' as [ ? | [(i & vh & Hes1) | [[sh Hes1] | (?&?&?&sh&Hes1)]]] ; first done.
  - exfalso.
    generalize dependent i. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    unfold to_val in Hes1 ; simpl in Hes1.
    rewrite merge_prepend in Hes1.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v0 => //.
    apply (IHes1 H i0 lh) => //.
    unfold to_val.
    by rewrite Hmerge.
  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    unfold to_val in Hes1 ; simpl in Hes1.
    rewrite merge_prepend in Hes1.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v0 => //.
    apply (IHes1 H s) => //.
    unfold to_val.
    by rewrite Hmerge.
  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    unfold to_val in Hes1 ; simpl in Hes1.
    rewrite merge_prepend in Hes1.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v0 => //.
    simpl in Hes1.
    inversion Hes1 ; subst.
    apply (IHes1 H l0) => //.
    unfold to_val.
    rewrite Hmerge.
    done.
Qed.
  
Lemma to_val_None_append: forall es1 es2,
  to_val es1 = None ->
  to_val (es1 ++ es2) = None.
Proof.
  move => es1 es2.
  induction es1 => //=.
  destruct a => //=.
  destruct b => //= ; unfold to_val => /=.
  - by rewrite merge_br flatten_simplify.
  - by rewrite merge_return flatten_simplify.
  - rewrite merge_prepend.
    unfold to_val in IHes1.
    destruct (merge_values_list _) eqn:Hmerge => //=.
    + destruct v0 => //=.
      assert (to_val es1 = Some trapV) ; first by unfold to_val ; rewrite Hmerge.
      apply to_val_trap_is_singleton in H as -> => //=.
    + rewrite merge_prepend.
      destruct (merge_values_list (map to_val_instr (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
  - unfold to_val => /=.
    rewrite merge_trap => /=.
    rewrite flatten_simplify.
    destruct es1 => //=.
    rewrite of_to_val_instr => //.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //.
    + destruct i => //.
      destruct (vh_decrease _) eqn:Hdecr => //.
      repeat rewrite merge_br => //.
    + repeat rewrite merge_return => //.
    + repeat rewrite merge_call_host => //.
  - unfold to_val => /=.
    destruct (merge_values_list _) => //.
    destruct v => //.
    rewrite merge_call_host flatten_simplify => //.
  - unfold to_val => /=. by rewrite merge_call_host flatten_simplify.
Qed.
  
Lemma to_val_not_trap_interweave : ∀ es es',
    const_list es -> es != [] ∨ es' != [] -> to_val (es ++ [AI_trap] ++ es')%SEQ = None.
Proof.
  intros es.
  induction es;intros es1 Hconst [Hnil | Hnil];try done.
  { destruct es1 => //=. unfold to_val => /=. rewrite of_to_val_instr => //. }
  { simpl in Hconst. apply andb_true_iff in Hconst as [Ha Hconst].
    destruct a => //.
    destruct b => //.
    simpl.
    unfold to_val => /=.
    rewrite merge_prepend.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct es,es1 ; first simpl in Hmerge.
    inversion Hmerge => //.
    assert (to_val ([] ++ [AI_trap] ++ s :: es1) = None).
    apply IHes => //=. by right.
    unfold to_val in H.
    rewrite Hmerge in H => //.
    assert (to_val ((a :: es) ++ [AI_trap] ++ []) = None).
    apply IHes => //=. by left.
    rewrite app_nil_r in H.
    unfold to_val in H.
    rewrite Hmerge in H => //.
    assert (to_val (a :: es ++ [AI_trap] ++ s :: es1) = None).
    apply IHes => //=. by right.
    unfold to_val in H.
    rewrite Hmerge in H => //.
  }
  { simpl in Hconst. apply andb_true_iff in Hconst as [Ha Hconst].
    destruct a => //.
    destruct b => //.
    simpl.
    unfold to_val => /=.
    rewrite merge_prepend.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct es,es1 ; first simpl in Hmerge.
    inversion Hmerge => //.
    assert (to_val ([] ++ [AI_trap] ++ s :: es1) = None).
    apply IHes => //=. by right.
    unfold to_val in H.
    rewrite Hmerge in H => //.
    assert (to_val ((a :: es) ++ [AI_trap] ++ []) = None).
    apply IHes => //=. 
    rewrite app_nil_r in H.
    unfold to_val in H.
    rewrite Hmerge in H => //.
    assert (to_val (a :: es ++ [AI_trap] ++ s :: es1) = None).
    apply IHes => //=. by right.
    unfold to_val in H.
    rewrite Hmerge in H => //. }
  Qed.

Lemma const_list_to_val es :
  const_list es -> exists vs, to_val es = Some (immV vs).
Proof.
  induction es => //= ; intros.
  by exists [].
       destruct a => //=.
       destruct b => //=.
       unfold to_val => /=.
       rewrite merge_prepend.
       apply IHes in H as [vs Htv].
       unfold to_val in Htv.
       destruct (merge_values_list _) => //=.
       inversion Htv => //=.
       by eexists.
Qed.

Lemma to_val_const_list: forall es vs,
  to_val es = Some (immV vs) ->
  const_list es.
Proof.
  move => es. 
  elim: es => [|e es'] //=.
  move => IH vs.
  destruct e => //=.
  destruct b => //= ; unfold to_val => /=. 
  - rewrite merge_br flatten_simplify => //.
  - rewrite merge_return flatten_simplify => //.
  - rewrite merge_prepend.
    unfold to_val in IH.
    destruct (merge_values_list _) => //.
    destruct v0 => //=.
    intro H ; inversion H ; subst.
    by eapply IH.
  - unfold to_val => /=.
    rewrite merge_trap flatten_simplify => /=.
    destruct es' => //=.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //.
    + destruct i => //.
      destruct (vh_decrease lh) => //.
      rewrite merge_br flatten_simplify => //.
    + rewrite merge_return flatten_simplify => //.
    + rewrite merge_call_host flatten_simplify => //.
  - unfold to_val => /=.
    destruct (merge_values_list _) => //.
    destruct v => //.
    rewrite merge_call_host flatten_simplify => //.
  - unfold to_val => /= ; by rewrite merge_call_host flatten_simplify.
Qed.

Lemma val_head_stuck_reduce : ∀ locs1 s1 e1 locs2 s2 e2,
    reduce locs1 s1 e1 locs2 s2 e2 ->
    to_val e1 = None.
Proof.
  move => locs1 s1 e1 locs2 s2 e2 HRed;try by to_val_None_prepend_const.
  induction HRed => //= ; subst; try by to_val_None_prepend_const.
  - inversion H; subst => //=;try by apply to_val_None_prepend_const;auto.
    + unfold to_val => /=.
      apply const_list_to_val in H0 as [vs Htv].
      unfold to_val in Htv.
      destruct (merge_values_list _) => //.
      inversion Htv => //.
    + unfold to_val => /=.
      destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v => //.
      destruct i0 => //.
      destruct (vh_decrease lh0) eqn:Hdecr => //.
      assert (to_val LI = Some (brV lh0)) ; first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H1.
      unfold of_val in H1.
      rewrite (vfill_decrease _ Hdecr) in H1.
      destruct (vfill_to_lfilled v [AI_basic (BI_br (S i0))]) as (Hk & Hfill).
      rewrite H1 in Hfill.
      edestruct lfilled_first_values as (Habs1 & Habs2 & _).
      exact H2.
      rewrite - (app_nil_l [_]) in Hfill.
      rewrite - cat_app in Hfill.
      exact Hfill.
      all : try done.
      inversion Habs1.
      subst.
      lia.
      assert (to_val LI = Some (retV s0)) ; first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H1. unfold of_val in H1. 
      specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfill.
      rewrite H1 in Hfill.
      edestruct lfilled_first_values as (Habs & _ & _).
      exact H2.
      rewrite - (app_nil_l [_]) in Hfill.
      rewrite - cat_app in Hfill.
      exact Hfill.
      all : try done.
      assert (to_val LI = Some (callHostV f0 h l l0)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H1. unfold of_val in H1.
      edestruct lfilled_llfill_first_values as [Habs _].
      exact H2.
      rewrite - (cat0s [_]) in H1.
      exact H1.
      all : try done.
    + unfold to_val => /=.
      apply const_list_to_val in H0 as [vs Htv].
      unfold to_val in Htv.
      destruct (merge_values_list _) => //.
      inversion Htv => //.
    + unfold to_val => /=.
      destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v => //.
      assert (to_val es = Some (callHostV f1 h l l0)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H1. unfold of_val in H1.
      edestruct lfilled_llfill_first_values as [Habs _].
      exact H2.
      rewrite - (cat0s [_]) in H1.
      exact H1.
      all : try done.
    + destruct v => //.
      by destruct b => //=.
    + move/lfilledP in H1.
      inversion H1. subst es e.
      apply to_val_not_trap_interweave;auto.
      case: vs {H H1 H2 H4} H0 => //=.
      case: es' => //=.
      move => a l H. by right.
      move => a l H. by left.
  - apply to_val_None_prepend_const;auto.
    apply v_to_e_is_const_list.
  - apply to_val_None_prepend_const ; auto.
    apply v_to_e_is_const_list.
  - destruct k, lh ; unfold lfilled, lfill in H ; fold lfill in H => //.
    + destruct (const_list l) eqn:Hl => //.
      apply b2p in H ; subst.
      apply to_val_None_prepend_const, to_val_None_append => //.
    + destruct (const_list l) eqn:Hl => //.
      destruct (lfill _ _ _) eqn:Hfill => //.
      apply b2p in H ; subst.
      generalize dependent les'.
      induction l ; intros ;  unfold to_val => /=.
      * destruct (merge_values_list _) eqn:Hmerge => //.
        destruct v => //.
        -- destruct i => //.
           destruct (vh_decrease lh0) eqn:Hdecr => //.
           exfalso.
           assert (to_val l2 = Some (brV lh0)) ; first by unfold to_val ; rewrite Hmerge.
           apply of_to_val in H.
           unfold of_val in H.
           destruct (vfill_to_lfilled lh0 [AI_basic (BI_br (S i))]) as (Hk & Hfilled).
           rewrite H in Hfilled.
           assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
           rewrite - (app_nil_l [_]) in Hfilled.
           rewrite - cat_app in Hfilled.
           eapply lfilled_br_and_reduce ; first (exact HRed) ; (try exact Hfilled) => //=.
        -- exfalso.
           assert (to_val l2 = Some (retV s0)) ; first by unfold to_val ; rewrite Hmerge.
           apply of_to_val in H. unfold of_val in H.
           specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfilled.
           rewrite H in Hfilled.
           assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
           rewrite - (app_nil_l [_]) in Hfilled.
           rewrite - cat_app in Hfilled.
           eapply lfilled_return_and_reduce ; first (exact HRed) ;
             (try exact Hfilled) => //=.
        -- exfalso.
           assert (to_val l2 = Some (callHostV f0 h l l3)) ;
             first by unfold to_val ; rewrite Hmerge.
           apply of_to_val in H. unfold of_val in H.
           assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
           destruct (lfilled_implies_llfill H1) as [llh Hfilled].
           eapply llfill_call_host_and_reduce ; first (exact HRed) ; (try exact Hfilled) => //=.
      * destruct a => //.
        destruct b => //=.
        rewrite merge_prepend.
        unfold lfilled, lfill in H0 ; fold lfill in H0.
        rewrite Hl in H0.
        destruct (lfill _ _ es') eqn:Hfill' => //.
        apply b2p in H0.
        destruct les' => //.
        assert (lfilled (S k) (LH_rec l n l0 lh l1) es' les').
        unfold lfilled, lfill ; fold lfill.
        apply andb_true_iff in Hl as [? Hl]. unfold const_list, forallb ; rewrite Hl.
        rewrite Hfill'. by inversion H0.
        apply IHl in H => //.
        unfold to_val in H.
        destruct (merge_values_list _) => //.
      * unfold to_val => /=.
        unfold to_val in IHHRed.
        destruct (merge_values_list _) => //.
Qed.

Lemma val_head_stuck : forall e1 s1 κ e2 s2 efs,
  prim_step e1 s1 κ e2 s2 efs →
  to_val e1 = None.
Proof.
  rewrite /prim_step => e1 [[locs1 σ1] inst] κ e2 [[ locs2 σ2] inst'] efs.
  move => [HRed _].
  eapply val_head_stuck_reduce;eauto.
Qed.

Lemma wasm_mixin : LanguageMixin of_val to_val prim_step.
Proof. split; eauto using to_of_val, of_to_val, val_head_stuck. Qed.

Definition wasm_lang := Language wasm_mixin.

