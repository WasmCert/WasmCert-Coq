(** Miscellaneous properties about Wasm operations **)

From Wasm Require Export datatypes_properties operations typing opsem common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Bool Program.Equality Wf_nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Basic Lemmas **)

(** List operations **)

Lemma cat_app {A} (l1 : list A) l2 :
  cat l1 l2 = app l1 l2.
Proof. done. Qed.

Lemma app_eq_singleton: forall T (l1 l2 : list T) (a : T),
    l1 ++ l2 = [::a] ->
    (l1 = [::a] /\ l2 = [::]) \/ (l1 = [::] /\ l2 = [::a]).
Proof.
  intros.
  apply List.app_eq_unit in H as [?|?]; by [ right | left ].
Qed.

Lemma combine_app {T1 T2: Type} (l1 l3: list T1) (l2 l4: list T2):
  length l1 = length l2 ->
  List.combine (l1 ++ l3) (l2 ++ l4) = List.combine l1 l2 ++ List.combine l3 l4.
Proof.
  move: l2 l3 l4.
  induction l1; move => l2 l3 l4 Hlen => /=; first by destruct l2 => //.
  - destruct l2 => //=.
    simpl in Hlen.
    inversion Hlen; subst; clear Hlen.
    f_equal.
    by apply IHl1.
Qed.

Lemma length_is_size: forall {X:Type} (l: list X),
    length l = size l.
Proof.
  move => X l. by elim: l.
Qed.

Lemma const_list_concat: forall vs1 vs2,
    const_list vs1 ->
    const_list vs2 ->
    const_list (vs1 ++ vs2).
Proof.
  move => vs1 vs2. elim vs1 => {vs1} //=.
  - move => a vs1' IHvs1 H1 H2. simpl in H1. simpl.
    apply andb_true_iff in H1. destruct H1. rewrite IHvs1 //=. by rewrite andbT.
Qed.

Lemma const_list_split: forall vs1 vs2,
    const_list (vs1 ++ vs2) ->
    const_list vs1 /\
    const_list vs2.
Proof.
  induction vs1 => //=; move => vs2 HConst.
  move/andP in HConst. destruct HConst.
  apply IHvs1 in H0. destruct H0.
  split => //.
  by apply/andP.
Qed.    

(** This lemma justifies the computation “to the first non-[const_list]”. **)
Lemma const_list_concat_inv : forall vs1 vs2 e1 e2 es1 es2,
  const_list vs1 ->
  const_list vs2 ->
  ~ is_const e1 ->
  ~ is_const e2 ->
  vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 ->
  vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
Proof.
  induction vs1 => vs2 e1 e2 es1 es2 C1 C2 N1 N2; destruct vs2 => /=; inversion 1; subst;
    try move: C1 => /= /andP [? ?] //;
    try move: C2 => /= /andP [? ?] //.
  - done.
  - apply IHvs1 in H2 => //. move: H2 => [? [? ?]]. by subst.
Qed.

Lemma const_list_take: forall vs l,
    const_list vs ->
    const_list (take l vs).
Proof.
  move => vs. induction vs => //=.
  - move => l HConst. destruct l => //=.
    + simpl. simpl in HConst. apply andb_true_iff in HConst. destruct HConst.
      apply andb_true_iff. split => //. by apply IHvs.
Qed.

Lemma v_to_e_is_const_list: forall vs,
    const_list (v_to_e_list vs).
Proof.
  move => vs. by elim: vs.
Qed.

Lemma v_to_e_cat: forall vs1 vs2,
    v_to_e_list vs1 ++ v_to_e_list vs2 = v_to_e_list (vs1 ++ vs2).
Proof.
  move => vs1. elim: vs1 => //=.
  - move => a l IH vs2. by rewrite IH.
Qed.

Lemma split_vals_e_v_to_e_duality: forall es vs es',
    split_vals_e es = (vs, es') ->
    es = (v_to_e_list vs) ++ es'.
Proof.
  move => es vs. move: es. elim: vs => //.
  - move=> es es'. destruct es => //=.
    + by inversion 1.
    + case a; try by inversion 1; [idtac].
      move => b. case b; try by inversion 1.
      move => v H.  by destruct (split_vals_e es).
  - move => a l H es es' HSplit. unfold split_vals_e in HSplit.
    destruct es => //. destruct a0 => //. destruct b => //.
    fold split_vals_e in HSplit.
    destruct (split_vals_e es) eqn:Heqn. inversion HSplit; subst.
    simpl. f_equal. by apply: H.
Qed.

Lemma const_list_cons : forall a l,
  const_list (a :: l) = is_const a && const_list l.
Proof. by []. Qed.

Lemma v_to_e_list0 : v_to_e_list [::] = [::].
Proof. reflexivity. Qed.

Lemma v_to_e_list1 : forall v, v_to_e_list [:: v] = [:: AI_basic (BI_const v)].
Proof. reflexivity. Qed.

Lemma e_is_trapP : forall e, reflect (e = AI_trap) (e_is_trap e).
Proof.
  case => //= >; by [ apply: ReflectF | apply: ReflectT ].
Qed.

Lemma es_is_trapP : forall l, reflect (l = [::AI_trap]) (es_is_trap l).
Proof.
  case; first by apply: ReflectF.
  move=> // a l. case l => //=.
  - apply: (iffP (e_is_trapP _)); first by elim.
    by inversion 1.
  - move=> >. by apply: ReflectF.
Qed.

Lemma split_n_is_take_drop: forall es n,
    split_n es n = (take n es, drop n es).
Proof.
  move => es n. move: es. elim:n => //=.
  - move => es. by destruct es.
  - move => n IH es'. destruct es' => //=.
    + by rewrite IH.
Qed.

Lemma fold_left_preserve {A B: Type} (P: A -> Prop) (f: A -> B -> A) (l: list B) (acc: A) :
  P acc ->
  (forall (x:A) (act: B), P x -> P (f x act)) ->
  P (List.fold_left f l acc).
Proof.
  rewrite -List.fold_left_rev_right.
  revert acc.
  induction l;simpl;auto.
  intros acc Ha Hnext.
  rewrite List.fold_right_app => /=. apply IHl =>//.
  by apply Hnext.
Qed.    

Lemma v_to_e_take_exchange: forall vs n,
    v_to_e_list (take n vs) = take n (v_to_e_list vs).
Proof.
  move => vs n. move: vs. elim:n => //=.
  - move => vs. by destruct vs.
  - move => n IH vs'. destruct vs' => //=.
    + by rewrite IH.
Qed.

Lemma v_to_e_drop_exchange: forall vs n,
    v_to_e_list (drop n vs) = drop n (v_to_e_list vs).
Proof.
  move => vs n. move: vs. elim:n => //=.
  - move => vs. by destruct vs.
  - move => n IH vs'. by destruct vs' => //=.
Qed.

Lemma v_to_e_size: forall vs,
    size (v_to_e_list vs) = size vs.
Proof.
  move => vs. elim: vs => //=.
  - move => a l IH. by f_equal.
Qed.      
      
(** This lemma is useful when an instruction consumes some expressions on the stack:
  we usually have to split a list of expressions by the expressions effectively
  consumed by the instructions and the one left. **)
Lemma v_to_e_take_drop_split: forall l n,
  v_to_e_list l = v_to_e_list (take n l) ++ v_to_e_list (drop n l).
Proof.
  move => l n. rewrite v_to_e_cat. by rewrite cat_take_drop.
Qed.

Lemma v_to_e_take: forall l n,
  v_to_e_list (take n l) = take n (v_to_e_list l).
Proof.
  move => + n. induction n => //.
  - move => l. by repeat rewrite take0.
  - move => l. destruct l => //. simpl. f_equal. by apply IHn.
Qed.

Lemma v_to_e_drop: forall l n,
  v_to_e_list (drop n l) = drop n (v_to_e_list l).
Proof.
  move => + n. induction n => //.
  - move => l. by repeat rewrite drop0.
  - move => l. destruct l => //. simpl. f_equal. by apply IHn.
Qed.

Lemma v_to_e_rev: forall l,
  v_to_e_list (rev l) = rev (v_to_e_list l).
Proof.
  elim => //=.
  move => a l IH. rewrite rev_cons. rewrite -cats1. rewrite -v_to_e_cat.
  rewrite rev_cons. rewrite -cats1. by rewrite -IH.
Qed.

Lemma to_b_list_concat: forall es1 es2 : seq administrative_instruction,
    to_b_list (es1 ++ es2) = to_b_list es1 ++ to_b_list es2.
Proof.
  induction es1 => //=.
  move => es2. by f_equal.
Qed.

Lemma to_e_list_basic: forall bes,
    es_is_basic (to_e_list bes).
Proof.
  induction bes => //=.
  split => //=.
  unfold e_is_basic. by eauto.
Qed.

Lemma basic_concat: forall es1 es2,
    es_is_basic (es1 ++ es2) ->
    es_is_basic es1 /\ es_is_basic es2.
Proof.
  induction es1 => //=.
  move => es2 H. destruct H.
  apply IHes1 in H0. destruct H0.
  by repeat split => //=.
Qed.

Lemma basic_split: forall es1 es2,
    es_is_basic es1 ->
    es_is_basic es2 ->
    es_is_basic (es1 ++ es2).
Proof.
  induction es1 => //=.
  move => es2 H1 H2.
  destruct H1.
  split => //=.
  by apply IHes1.
Qed.

Lemma const_list_is_basic: forall es,
    const_list es ->
    es_is_basic es.
Proof.
  induction es => //=.
  move => H. move/andP in H. destruct H.
  split.
  - destruct a => //.
    unfold e_is_basic. by eauto.
  - by apply IHes.                                 
Qed.

Lemma to_b_list_rev: forall es : seq administrative_instruction,
    rev (to_b_list es) = to_b_list (rev es).
Proof.
  induction es => //=.
  repeat rewrite rev_cons.
  rewrite IHes.
  repeat rewrite -cats1.
  by rewrite to_b_list_concat.
Qed.

Lemma vs_to_vts_cat: forall vs1 vs2,
    vs_to_vts (vs1 ++ vs2) = vs_to_vts vs1 ++ vs_to_vts vs2.
Proof.
  induction vs1 => //=.
  move => vs2. by rewrite IHvs1.
Qed.
  
Lemma vs_to_vts_rev: forall vs,
    vs_to_vts (rev vs) = rev (vs_to_vts vs).
Proof.
  induction vs => //=.
  repeat rewrite rev_cons.
  repeat rewrite -cats1.
  rewrite vs_to_vts_cat.
  by rewrite IHvs.
Qed.
  
Lemma const_es_exists: forall es,
    const_list es ->
    exists vs, es = v_to_e_list vs.
Proof.
  induction es => //=.
  - by exists [::].
  - move => HConst.
    move/andP in HConst. destruct HConst.
    destruct a => //=. destruct b => //=.
    edestruct IHes => //=.
    exists (v :: x). simpl. by rewrite H1.
Qed.

Lemma b_e_elim: forall bes es,
    to_e_list bes = es ->
    bes = to_b_list es /\ es_is_basic es.
Proof.
  induction bes; move => es H => //=.
  - by rewrite -H.
  - simpl in H. assert (es = to_e_list (a :: bes)) as H1.
    + by rewrite -H.
    + rewrite H1. split.
      -- simpl. f_equal. by apply IHbes.
      -- by apply to_e_list_basic.
Qed.

Lemma e_b_elim: forall bes es,
    bes = to_b_list es ->
    es_is_basic es ->
    es = to_e_list bes.
Proof.
  induction bes; move => es H1 H2 => //=.
  - by destruct es => //=.
  - destruct es => //=. simpl in H1. simpl in H2. destruct H2.
    inversion H1; subst.
    inversion H; subst => //=.
    f_equal. apply IHbes => //=.
Qed.
    
Lemma to_e_list_injective: forall bes bes',
    to_e_list bes = to_e_list bes' ->
    bes = bes'.
Proof.
  move => bes bes' H.
  apply b_e_elim in H; destruct H; subst => //=.
  induction bes' => //=.
  f_equal. apply IHbes'. by apply to_e_list_basic.
Qed.

Lemma to_e_list_cat: forall bes1 bes2,
    to_e_list (bes1 ++ bes2) = to_e_list bes1 ++ to_e_list bes2.
Proof.
  induction bes1 => //.
  move => bes2. simpl. by f_equal.
Qed.

Lemma concat_cancel_last: forall {X:Type} (l1 l2: seq X) (e1 e2:X),
    l1 ++ [::e1] = l2 ++ [::e2] ->
    l1 = l2 /\ e1 = e2.
Proof.
  move => X l1 l2 e1 e2 H.
  assert (rev (l1 ++ [::e1]) = rev (l2 ++ [::e2])); first by rewrite H.
  repeat rewrite rev_cat in H0. inversion H0.
  rewrite - (revK l1). rewrite H3. split => //. by apply revK.
Qed.

Lemma concat_cancel_last_n: forall (l1 l2 l3 l4: seq value_type),
    l1 ++ l2 = l3 ++ l4 ->
    size l2 = size l4 ->
    (l1 == l3) && (l2 == l4).
Proof.
  move => l1 l2 l3 l4 HCat HSize.
  rewrite -eqseq_cat; first by apply/eqP.
  assert (size (l1 ++ l2) = size (l3 ++ l4)); first by rewrite HCat.
  repeat rewrite size_cat in H.
  rewrite HSize in H. by lias.
Qed.

Lemma extract_list1 : forall {X:Type} (es: seq X) (e1 e2:X),
    es ++ [::e1] = [::e2] ->
    es = [::] /\ e1 = e2.
Proof.
  move => X es e1 e2 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma extract_list2 : forall {X:Type} (es: seq X) (e1 e2 e3:X),
    es ++ [::e1] = [::e2; e3] ->
    es = [::e2] /\ e1 = e3.
Proof.
  move => X es e1 e2 e3 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma extract_list3 : forall {X:Type} (es: seq X) (e1 e2 e3 e4:X),
    es ++ [::e1] = [::e2; e3; e4] ->
    es = [::e2; e3] /\ e1 = e4.
Proof.
  move => X es e1 e2 e3 e4 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma extract_list4 : forall {X:Type} (es: seq X) (e1 e2 e3 e4 e5:X),
    es ++ [::e1] = [::e2; e3; e4; e5] ->
    es = [::e2; e3; e4] /\ e1 = e5.
Proof.
  move => X es e1 e2 e3 e4 e5 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma list_nth_prefix: forall {X:Type} (l1 l2: seq X) x,
    List.nth_error (l1 ++ [::x] ++ l2) (length l1) = Some x.
Proof.
  move => X. induction l1 => //=.
Qed.

(** Numerics **)

Lemma N_nat_bin n:
  n = N.of_nat (ssrnat.nat_of_bin n).
Proof.
  destruct n => //=.
  replace (ssrnat.nat_of_pos p) with (Pos.to_nat p); first by rewrite positive_nat_N.
  induction p => //=.
  - rewrite Pos2Nat.inj_xI.
    f_equal.
    rewrite IHp.
    rewrite ssrnat.NatTrec.doubleE.
    rewrite - ssrnat.mul2n.
    by lias.
  - rewrite Pos2Nat.inj_xO.
    rewrite IHp.
    rewrite ssrnat.NatTrec.doubleE.
    rewrite - ssrnat.mul2n.
    by lias.
Qed.

Lemma nat_bin n:
  ssrnat.nat_of_bin n = N.to_nat n.
Proof.
  rewrite -> (N_nat_bin n).
  rewrite Nat2N.id.
  by rewrite <- N_nat_bin.
Qed.
  

(** * Tactics **)

(** [gen_ind] perform an induction over predicates like [be_typing], generalising its parameters,
  but not generalising any section variables such as [host_function].
  The reason for this tactic is that [dependent induction] is far too aggressive
  in its generalisation, and prevents the use of some lemmas. **)

(** The first step is to name each parameter of the predicate. **)
Ltac gen_ind_pre H :=
  let rec aux v :=
    lazymatch v with
    | ?f ?x =>
      let only_do_if_ok_direct t cont :=
        lazymatch t with
        | Type => idtac
        | host _ => idtac
        | _ => cont tt
        end in
      let t := type of x in
      only_do_if_ok_direct t ltac:(fun _ =>
        let t :=
          match t with
          | _ _ => t
          | ?t => eval unfold t in t
          | _ => t
          end in
        only_do_if_ok_direct t ltac:(fun _ =>
          let x' :=
            let rec get_name x :=
              match x with
              | ?f _ => get_name f
              | _ => fresh x
              | _ => fresh "x"
              end in
            get_name x in
          move: H;
          set_eq x' x;
          let E := fresh "E" x' in
          move=> E H));
      aux f
    | _ => idtac
    end in
  let Ht := type of H in
  aux Ht.

(** Then, each of the associated parameters can be generalised. **)
Ltac gen_ind_gen H :=
  let rec try_generalize t :=
    lazymatch t with
    | ?f ?x => try_generalize f; try_generalize x
    | ?x => is_variable x ltac:(generalize dependent x) ltac:(idtac)
    | _ => fail "unable to generalize" t
    end in
  let rec aux v :=
    lazymatch v with
    | ?f ?x => 
    lazymatch goal with
      | _ : x = ?y |- _ => try_generalize y
      | _ => fail "unexpected term" v
      end;
      aux f
    | _ => idtac
    end in
  let Ht := type of H in
  aux Ht.

(** After the induction, one can inverse them again (and do some cleaning). **)
Ltac gen_ind_post :=
  repeat lazymatch goal with
  | |- _ = _ -> _ => inversion 1
  | |- _ -> _ => intro
  end;
  repeat lazymatch goal with
  | H: True |- _ => clear H
  | H: ?x = ?x |- _ => clear H
  end.

(** Wrapping every part of the generalised induction together. **)
Ltac gen_ind H :=
  gen_ind_pre H;
  gen_ind_gen H;
  induction H;
  gen_ind_post.

(** Similar to [gen_ind H; subst], but cleaning just a little bit more. **)
Ltac gen_ind_subst H :=
  gen_ind H;
  subst;
  gen_ind_post.

(** Calls the continuation on [v] or, if it failed, on [v] whose root has been unfolded.
  This is useful for tactics with pattern mtaching recognising a predicate which is
  frequently folded in a section, like [be_typing]. **)
Ltac call_unfold v cont :=
  let rec unfold_root :=
    lazymatch v with
    | ?f ?x =>
      let f := unfold_root f in
      constr:(f x)
    | ?x => eval unfold x in x
    end in
  first [
      cont v
    | let v := unfold_root v in
      cont v ].

(** Perform basic simplifications of [es_is_basic]. **)
Ltac basic_inversion :=
   repeat lazymatch goal with
         | H: True |- _ =>
           clear H
         | H: es_is_basic (_ ++ _) |- _ =>
           let Ha := fresh H in
           let Hb := fresh H in
           apply basic_concat in H; destruct H as [Ha Hb]
         | H: es_is_basic [::] |- _ =>
           clear H
         | H: es_is_basic [::_] |- _ =>
           let H1 := fresh H in
           let H2 := fresh H in
           try by (unfold es_is_basic in H; destruct H as [H1 H2]; inversion H1)
         | H: e_is_basic _ |- _ =>
           inversion H; try by []
         end.

(** Rewrite hypotheses on the form [_ ++ [:: _] = _] as some easier to use equalities. **)
Ltac extract_listn :=
  repeat lazymatch goal with
  | H: (?es ++ [::?e])%list = [::_] |- _ =>
    apply extract_list1 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_] |- _ =>
    apply extract_list1 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _] |- _ =>
    apply extract_list2 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _] |- _ =>
    apply extract_list2 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _; _] |- _ =>
    apply extract_list3 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _; _] |- _ =>
    apply extract_list3 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _; _; _] |- _ =>
    apply extract_list4 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _; _; _] |- _ =>
    apply extract_list4 in H; destruct H; subst
  | H: _ :: _ = (_ ++ _)%list |- _ => symmetry in H
  | H: _ :: _ = _ ++ _ |- _ => symmetry in H
         end.

Ltac fold_upd_context :=
  lazymatch goal with
  | |- context [upd_local (upd_return ?C ?ret) ?loc] =>
    replace (upd_local (upd_return C ret) loc) with
        (upd_local_return C ret loc); try by destruct C
  | |- context [upd_return (upd_local ?C ?ret) ?loc] =>
    replace (upd_return (upd_local C ret) loc) with
        (upd_local_return C ret loc); try by destruct C
  end.



(** * More Advanced Lemmas **)

Section Host.

Variable host_function : eqType.

Let store_record := store_record host_function.
Let function_closure := function_closure host_function.
Let e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
  @e_typing _.

Lemma lfilled_collapse1: forall n lh vs es LI l,
    lfilledInd n lh (vs++es) LI ->
    const_list vs ->
    length vs >= l ->
    exists lh', lfilledInd n lh' ((drop (length vs-l) vs) ++ es) LI.
Proof.
  move => n lh vs es LI l HLF HConst HLen.
  remember (vs++es) as es'. induction HLF; subst.
  - exists (LH_base (vs0 ++ (take (length vs - l) vs)) es').
    replace (vs0++(vs++es)++es') with ((vs0++take (length vs - l) vs) ++ (drop (length vs - l) vs ++ es) ++ es').
    { apply LfilledBase. apply const_list_concat => //=.
      by apply const_list_take. }
    repeat rewrite -catA. f_equal.
    repeat rewrite catA. do 2 f_equal.
    by apply cat_take_drop. 
  - destruct IHHLF => //. eexists (LH_rec _ _ _ _ _). apply LfilledRec => //. by apply H0.
Qed.

Lemma lfilled_collapse2: forall n lh es es' LI,
    lfilledInd n lh (es++es') LI ->
    exists lh', lfilledInd n lh' es LI.
Proof.
  move => n lh es es' LI HLF. remember (es ++ es') as Ees. induction HLF; subst.
  - eexists (LH_base _ _). rewrite <- catA. by apply LfilledBase.
  - destruct IHHLF => //. eexists (LH_rec _ _ _ _ _). apply LfilledRec => //. by apply H0.
Qed.

Lemma lfilled_collapse3: forall k lh n les es LI,
    lfilledInd k lh [:: AI_label n les es] LI ->
    exists lh', lfilledInd (k+1) lh' es LI.
Proof.
  move => k lh n les es LI HLF. remember [:: AI_label n les es] as E.  induction HLF; subst.
  - eexists (LH_rec _ _ _ _ _). apply LfilledRec. auto.
    assert (lfilledInd 0 (LH_base nil nil) es ([::] ++ es ++ [::])). { by apply LfilledBase. }
    simpl in H0. rewrite cats0 in H0. by apply H0.
  - destruct IHHLF => //. eexists (LH_rec _ _ _ _ _). apply LfilledRec => //. by apply H0.
Qed.

Lemma lfilled_deterministic: forall k lh es les les',
    lfilledInd k lh es les ->
    lfilledInd k lh es les' ->
    les = les'.
Proof.
  move => k lh es les les' HLF HLF'.
  apply lfilled_Ind_Equivalent in HLF. unfold operations.lfilled in HLF.
  apply lfilled_Ind_Equivalent in HLF'. unfold operations.lfilled in HLF'.
  destruct (lfill k lh es) => //.
  replace les' with l.
  { move: HLF. by apply/eqseqP. }
  symmetry. move: HLF'. by apply/eqseqP. 
Qed.  


(** Additional List properties **)

Lemma nth_error_Some_length:
  forall A (l : seq.seq A) (i : nat) (m : A),
  List.nth_error l i = Some m -> 
  (i < length l)%coq_nat.
Proof.
  move => A l i m H1.
  assert (H2 : List.nth_error l i <> None) by rewrite H1 => //.
  by apply List.nth_error_Some in H2.
Qed.

Lemma all_projection: forall {X:Type} f (l:seq X) n x,
    all f l ->
    List.nth_error l n = Some x ->
    f x.
Proof.
  move => X f l n x.
  generalize dependent l.
  induction n => //; destruct l => //=; move => HF HS; remove_bools_options => //.
  eapply IHn; by eauto.
Qed.

Lemma all2_projection: forall {X Y:Type} f (l1:seq X) (l2:seq Y) n x1 x2,
    all2 f l1 l2 ->
    List.nth_error l1 n = Some x1 ->
    List.nth_error l2 n = Some x2 ->
    f x1 x2.
Proof.
  move => X Y f l1 l2 n.
  generalize dependent l1.
  generalize dependent l2.
  induction n => //=; move => l2 l1 x1 x2 HALL HN1 HN2.
  - destruct l1 => //=. destruct l2 => //=.
    inversion HN1. inversion HN2. subst. clear HN1. clear HN2.
    simpl in HALL. move/andP in HALL. by destruct HALL.
  - destruct l1 => //=. destruct l2 => //=.
    simpl in HALL. move/andP in HALL. destruct HALL.
    eapply IHn; by eauto.
Qed.

Lemma all2_element {T1 T2: Type} (l1: list T1) (l2: list T2) f n x:
  all2 f l1 l2 ->
  List.nth_error l1 n = Some x ->
  exists y, List.nth_error l2 n = Some y.
Proof.
  move => Hall2 Hnth.
  destruct (List.nth_error l2 n) eqn:Hnth'; first by eauto.
  exfalso.
  apply List.nth_error_None in Hnth'.
  apply all2_size in Hall2.
  repeat rewrite - length_is_size in Hall2.
  rewrite -Hall2 in Hnth'.
  apply nth_error_Some_length in Hnth.
  by lias.
Qed.

Lemma all2_spec: forall {X Y:Type} (f: X -> Y -> bool) (l1:seq X) (l2:seq Y),
    size l1 = size l2 ->
    (forall n x y, List.nth_error l1 n = Some x ->
          List.nth_error l2 n = Some y ->
          f x y) ->
    all2 f l1 l2.
Proof.
  move => X Y f l1.
  induction l1; move => l2; destruct l2 => //=.
  move => Hsize Hf.
  apply/andP; split.
  { specialize (Hf 0 a y); simpl in *; by apply Hf. }
  { apply IHl1; first by lias.
    move => n x1 y1 Hnl1 Hnl2.
    specialize (Hf (n.+1) x1 y1).
    by apply Hf.
  }
Qed.

Lemma all2_weaken {T1 T2: Type} (l1: list T1) (l2: list T2) (f1 f2: T1 -> T2 -> bool):
  (forall x y, f1 x y -> f2 x y) ->
  all2 f1 l1 l2 ->
  all2 f2 l1 l2.
Proof.
  move => Himpl Hall2.
  apply all2_spec; first by apply all2_size in Hall2.
  move => n x y Hn1 Hn2.
  apply Himpl.
  by apply (all2_projection Hall2 Hn1 Hn2).
Qed.

Lemma nth_error_take {T: Type} (l: list T) (x: T) (k n: nat):
  List.nth_error l n = Some x ->
  n < k ->
  List.nth_error (take k l) n = Some x.
Proof.
  move: x k n.
  induction l; move => x k n Hnth Hlt; destruct n, k => //=.
  by apply IHl.
Qed.
 
Definition function {X Y:Type} (f: X -> Y -> Prop) : Prop :=
  forall x y1 y2, ((f x y1 /\ f x y2) -> y1 = y2).

Lemma all2_function_unique: forall {X Y:Type} f (l1:seq X) (l2 l3:seq Y),
    all2 f l1 l2 ->
    all2 f l1 l3 ->
    function f ->
    l2 = l3.
Proof.
  move => X Y f l1.
  induction l1 => //=; move => l2 l3 HA1 HA2 HF.
  - destruct l2 => //. by destruct l3 => //.
  - destruct l2 => //=; destruct l3 => //=.
    simpl in HA1. simpl in HA2.
    move/andP in HA1. move/andP in HA2.
    destruct HA1. destruct HA2.
    unfold function in HF.
    assert (y = y0); first by eapply HF; eauto.
    rewrite H3. f_equal.
    by apply IHl1.
Qed.

Fixpoint ai_gen_measure (e: administrative_instruction) : nat :=
  match e with
  | AI_label _ _ es => 1 + List.list_max (map ai_gen_measure es)
  | _ => 0
  end.

Definition lfilled_pickable_rec_gen_measure (LI: list administrative_instruction) : nat :=
  List.list_max (map ai_gen_measure LI).

(*
(** The decreasing measure used in the definition of [lfilled_pickable_rec_gen]. **)
Definition lfilled_pickable_rec_gen_measure (LI : seq administrative_instruction) :=
  TProp.max
    (seq_administrative_instruction_rect'
       (fun _ => 0)
       0
       (fun _ => 0)
       (fun _ LI1 LI2 m1 m2 => 1 + TProp.max m2)
       (fun _ _ LI' m => 0)
       LI).
 *)

Lemma lfilled_pickable_rec_gen_measure_cons : forall I LI,
  lfilled_pickable_rec_gen_measure LI <= lfilled_pickable_rec_gen_measure (I :: LI).
Proof.
  move=> I LI.
  unfold lfilled_pickable_rec_gen_measure => /=.
  by lias.
Qed.

Lemma lfilled_pickable_rec_gen_measure_concat_l : forall LI1 LI2,
  lfilled_pickable_rec_gen_measure LI1 <= lfilled_pickable_rec_gen_measure (LI1 ++ LI2).
Proof.
  unfold lfilled_pickable_rec_gen_measure => /=.
  move => LI1 LI2. rewrite map_cat List.list_max_app.
  by lias.
Qed.

Lemma lfilled_pickable_rec_gen_measure_concat_r : forall LI1 LI2,
  lfilled_pickable_rec_gen_measure LI2 <= lfilled_pickable_rec_gen_measure (LI1 ++ LI2).
Proof.
  unfold lfilled_pickable_rec_gen_measure => /=.
  move => LI1 LI2. rewrite map_cat List.list_max_app.
  by lias.
Qed.

Lemma lfilled_pickable_rec_gen_measure_label_r : forall n es LI LI',
  lfilled_pickable_rec_gen_measure LI < lfilled_pickable_rec_gen_measure (AI_label n es LI :: LI').
Proof.
  move=> n es LI LI'. rewrite /lfilled_pickable_rec_gen_measure /=.
  destruct (List.list_max (map ai_gen_measure LI')); by lias.
Qed.

(** A helper definition for [lfilled_decidable_rec]. **)
Definition lfilledInd_pickable_rec_gen : forall fes,
  (forall es' lh lh' n0, decidable (lfilledInd 0 lh (fes n0 lh') es')) ->
  forall es', pickable2 (fun n lh => lfilledInd n lh (fes n lh) es').
Proof.
  move=> fes D0 es'.
  apply: (@pickable2_equiv _ _ (fun n lh => lfilledInd n lh (fes (0+n) lh) es')); first by [].
  move: 0 => k.
  have [m E]: { m | lfilled_pickable_rec_gen_measure es' = m }; first by eexists.
  move: fes D0 es' E k. induction (lt_wf m) as [m _ IH]. move=> fes D0 es' E k.
  have Dcl: forall vs, decidable (const_list vs).
  { move=> vs. by apply: is_true_decidable. }
  (** First, we check whether we can set [n = 0]. **)
  have P0: pickable2 (fun vs es'' =>
                       let lh := LH_base vs es'' in
                       let es := fes k lh in
                       es' = vs ++ es ++ es'' /\ const_list vs /\ lfilledInd 0 lh es es').
  {
    have: pickable3 (fun vs es es'' =>
      es' = vs ++ es ++ es'' /\ let lh := LH_base vs es'' in
      es = fes k lh /\ const_list vs /\ lfilledInd 0 lh es es').
    {
      apply: list_split_pickable3_gen. move=> vs es es'' Ees /=.
      case E': (es == fes k (LH_base vs es'')); move/eqP: E' => E'.
      - rewrite E'. repeat apply: decidable_and => //. by apply: eq_comparable.
      - right. by move=> [Ees2 [Cl I]].
    }
    case.
    - move=> [[[vs es] es''] [E1 [E2 [Cl I]]]]. left. exists (vs, es''). by subst.
    - move=> Ex. right. move=> [vs [es'' [E' [Cl I]]]]. apply: Ex.
      by repeat eexists; eassumption.
  }
  case P0.
  {
    move=> [[vs es''] [E' [Cvs I]]]. left. exists (0, LH_base vs es'').
    subst. rewrite_by (k + 0 = k). by apply: LfilledBase.
  }
  move=> nE.
  (** Otherwise, we have to apply [LfilledRec]. **)
  have Dparse: forall es' : seq administrative_instruction,
    decidable (exists n es1 LI es2, es' = [:: AI_label n es1 LI] ++ es2).
  {
    clear. move=> es'.
    have Pparse: pickable4 (fun n es1 LI es2 => es' = [:: AI_label n es1 LI] ++ es2).
    {
      let no := by intros; right; intros (?&?&?&?&?) in
      (case es'; first by no); case; try by no.
      move=> n l1 l2 l3. left. by exists (n, l1, l2, l3).
    }
    convert_pickable Pparse.
  }
  case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse es)) es').
  - move=> [[vs es''] [E1 [C Ex]]].
    destruct es'' as [| [| | | n es1 LI |] es2];
      try solve [ exfalso; move: Ex => [? [? [? [? E']]]]; inversion E' ].
    clear Ex. rewrite E1.
    have I_LI: (lfilled_pickable_rec_gen_measure LI < m)%coq_nat.
    {
      rewrite -E E1. apply/leP. eapply leq_trans.
      - by eapply lfilled_pickable_rec_gen_measure_label_r.
      - by apply: lfilled_pickable_rec_gen_measure_concat_r.
    }
    set fes' := fun k lh => fes (k + 1) (LH_rec vs n es1 lh es2).
    have D1: forall es' lh lh' n0, decidable (lfilledInd 0 lh (fes' n0 lh') es').
    { move=> ? ? ? ?. by apply: D0. }
    move: (IH _ I_LI fes' D1 LI (erefl _) k) => [[[n' lh] LF]|NP].
    - eapply LfilledRec with (vs := vs) in LF => //.
      left. exists (n'.+1, LH_rec vs n es1 lh es2).
      move: LF. rewrite /fes'. rewrite_by (k + n' + 1 = k + n'.+1) => /= LF. by apply: LF.
    - right. move=> [n' [lh FI]]. apply: NP. inversion FI; subst.
      + exfalso. apply: nE. exists vs0. exists es'0. repeat split => //.
        * rewrite -H. by rewrite_by (k + 0 = k).
        * by rewrite_by (k = k + 0).
      + apply const_list_concat_inv in H => //. move: H => [? [E ?]]. inversion E; subst.
        exists k0. eexists. rewrite /fes'. rewrite_by (k + k0 + 1 = k + k0.+1). by apply: H4.
  - move=> nE'. right. move=> [n [lh I]]. inversion I; subst.
    + apply: nE. do 2 eexists. rewrite_by (k + 0 = k). repeat split; try eassumption.
      by apply: LfilledBase.
    + apply: nE'. by repeat eexists.
Defined.

Definition lfilled_pickable_rec_gen : forall fes,
  (forall es' lh lh' n0, decidable (lfilled 0 lh (fes n0 lh') es')) ->
  forall es', pickable2 (fun n lh => lfilled n lh (fes n lh) es').
Proof.
  move=> fes D0 es'.
  apply: (@pickable2_equiv _ _ (fun n lh => lfilledInd n lh (fes (0+n) lh) es')).
  { move=> n lh. by split; apply lfilled_Ind_Equivalent. }
  apply: lfilledInd_pickable_rec_gen => es'' lh lh' n0.
  by apply: decidable_equiv; first by apply: lfilled_Ind_Equivalent.
Defined.

(** We can always decide [lfilled 0]. **)
Lemma lfilled_decidable_base : forall es es' lh,
  decidable (lfilled 0 lh es es').
Proof.
  move=> es es' lh. apply: (@decidable_equiv (lfilledInd 0 lh es es')).
  { by split; apply lfilled_Ind_Equivalent. }
  case lh.
  - move=> vsh esh.
    have: pickable2 (fun vs es'' => es' = vs ++ es ++ es'' /\ const_list vs /\ vs = vsh /\ es'' = esh).
    {
      apply: list_search_split_pickable2.
      - by apply: administrative_instruction_eq_dec.
      - move=> ? ?. by repeat apply: decidable_and; apply: eq_comparable.
    }
    case.
    + move=> [[vs es''] [E [C [E1 E2]]]]. left. subst. by constructor.
    + move=> nE. right. move=> I. apply: nE. inversion I. subst. by repeat eexists.
  - move=> vs n es'' lh' es'''. right. move=> I. by inversion I.
Defined.

(** We can furthermore rebuild the stack [lh] for any [lfilled 0] predicate. **)
Lemma lfilled_pickable_base : forall es es',
  pickable (fun lh => lfilled 0 lh es es').
Proof.
  move=> es es'. apply: (@pickable_equiv _ (fun lh => lfilledInd 0 lh es es')).
  { move=> lh. by split; apply lfilled_Ind_Equivalent. }
  have: pickable2 (fun vs es'' => es' = vs ++ es ++ es'' /\ const_list vs /\ True).
  {
    apply: list_search_split_pickable2.
    - by apply: administrative_instruction_eq_dec.
    - move=> ? ?. apply: decidable_and.
      + by apply: is_true_decidable.
      + by left.
  }
  case.
  - move=> [[vs es''] [E [C _]]]. left. eexists. subst. by constructor.
  - move=> nE. right. move=> [lh I]. apply: nE. inversion I. subst. by repeat eexists.
Defined.

(** A helper definition for the decidability of [br_reduce] and [return_reduce]
  (see type_soundness.v). **)
Definition lfilled_pickable_rec : forall es,
  (forall es' lh, decidable (lfilled 0 lh es es')) ->
  forall es', pickable2 (fun n lh => lfilled n lh es es').
Proof.
  move=> es D. by apply: lfilled_pickable_rec_gen.
Defined.

(** Typing lemmas **)

(* A reformulation of [ety_a] that is easier to be used. *)
Lemma ety_a': forall s C es ts,
    es_is_basic es ->
    be_typing C (to_b_list es) ts ->
    e_typing s C es ts.
Proof.
  move => s C es ts HBasic HType.
  replace es with (to_e_list (to_b_list es)).
  - by apply ety_a.
  - symmetry. by apply e_b_elim.
Qed.

(* Some quality of life lemmas *)
Lemma bet_weakening_empty_1: forall C es ts t2s,
    be_typing C es (Tf [::] t2s) ->
    be_typing C es (Tf ts (ts ++ t2s)).
Proof.
  move => C es ts t2s HType.
  assert (be_typing C es (Tf (ts ++ [::]) (ts ++ t2s))); first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma et_weakening_empty_1: forall s C es ts t2s,
    e_typing s C es (Tf [::] t2s) ->
    e_typing s C es (Tf ts (ts ++ t2s)).
Proof.
  move => s C es ts t2s HType.
  assert (e_typing s C es (Tf (ts ++ [::]) (ts ++ t2s))); first by apply ety_weakening.
  by rewrite cats0 in H.
Qed.

Lemma bet_weakening_empty_2: forall C es ts t1s,
    be_typing C es (Tf t1s [::]) ->
    be_typing C es (Tf (ts ++ t1s) ts).
Proof.
  move => C es ts t1s HType.
  assert (be_typing C es (Tf (ts ++ t1s) (ts ++ [::]))); first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma bet_weakening_empty_both: forall C es ts,
    be_typing C es (Tf [::] [::]) ->
    be_typing C es (Tf ts ts).
Proof.
  move => C es ts HType.
  assert (be_typing C es (Tf (ts ++ [::]) (ts ++ [::]))); first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma empty_typing: forall C t1s t2s,
    be_typing C [::] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - by destruct es.
  - f_equal. by eapply IHHType.
Qed.

(* A convenient lemma to invert e_typing back to be_typing. *)
Lemma et_to_bet: forall s C es ts,
    es_is_basic es ->
    e_typing s C es ts ->
    be_typing C (to_b_list es) ts.
Proof.
  move => s C es ts HBasic HType.
  dependent induction HType; basic_inversion.
  + replace (to_b_list (to_e_list bes)) with bes => //.
    by apply b_e_elim.
  + rewrite to_b_list_concat.
    eapply bet_composition.
    * by eapply IHHType1 => //.
    * by eapply IHHType2 => //.
  + apply bet_weakening. by eapply IHHType => //.
Qed.

Lemma empty_e_typing: forall s C t1s t2s,
    e_typing s C [::] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => s C t1s t2s HType.
  apply et_to_bet in HType => //.
  by apply empty_typing in HType.
Qed.

Section composition_typing_proofs.

Hint Constructors be_typing : core.

(** A helper tactic for proving [composition_typing_single]. **)
Ltac auto_prove_bet:=
  repeat lazymatch goal with
  | H: _ |- exists ts t1s t2s t3s, ?tn = ts ++ t1s /\ ?tm = ts ++ t2s /\
                                   be_typing _ [::] (Tf _ _) /\ _ =>
    try exists [::], tn, tm, tn; try eauto
  | H: _ |- _ /\ _ =>
    split => //=; try eauto
  | H: _ |- be_typing _ [::] (Tf ?es ?es) =>
    apply bet_weakening_empty_both; try by []
  end.

Lemma composition_typing_single: forall C es1 e t1s t2s,
    be_typing C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             be_typing C es1 (Tf t1s' t3s) /\
                             be_typing C [::e] (Tf t3s t2s').
Proof.
  move => C es1 e t1s t2s HType.
  gen_ind_subst HType; extract_listn; auto_prove_bet.
  + by apply bet_block.
  + by destruct es1 => //=.
  + apply concat_cancel_last in H1. destruct H1. subst.
    by exists [::], t1s0, t2s0, t2s.
  + edestruct IHHType; eauto.
    destruct H as [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]. subst.
    exists (ts ++ x), t1s', t2s', t3s'.
    by repeat split => //=; rewrite -catA.
Qed.

Lemma composition_typing: forall C es1 es2 t1s t2s,
    be_typing C (es1 ++ es2) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             be_typing C es1 (Tf t1s' t3s) /\
                             be_typing C es2 (Tf t3s t2s').
Proof.
  move => C es1 es2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1.
  clear Heqes2'. subst.
  induction es2' => //=; move => es1 t1s t2s HType.
  - unfold rev in HType; simpl in HType. subst.
    rewrite cats0 in HType.
    exists [::], t1s, t2s, t2s.
    repeat split => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite rev_cons in HType.
    rewrite -cats1 in HType. subst.
    rewrite catA in HType.
    apply composition_typing_single in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]]. subst.
    apply IHes2' in H3.
    destruct H3 as [ts2 [t1s2 [t2s2 [t3s2 [H5 [H6 [H7 H8]]]]]]]. subst.
    exists ts', (ts2 ++ t1s2), t2s', (ts2 ++ t3s2).
    repeat split => //.
    + by apply bet_weakening.
    + rewrite rev_cons. rewrite -cats1.
      eapply bet_composition; eauto.
      by apply bet_weakening.
Qed.

Lemma e_composition_typing_single: forall s C es1 e t1s t2s,
    e_typing s C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             e_typing s C es1 (Tf t1s' t3s) /\
                             e_typing s C [::e] (Tf t3s t2s').
Proof.
  move => s C es1 es2 t1s t2s HType.
  gen_ind_subst HType; extract_listn.
  - (* basic *)
    apply b_e_elim in H3. destruct H3. subst.
    rewrite to_b_list_concat in H.
    apply composition_typing in H.
    apply basic_concat in H1. destruct H1.
    destruct H as [ts' [t1s' [t2s' [t3s' [H2 [H3 [H4 H5]]]]]]]. subst.
    exists ts', t1s', t2s', t3s'.
    by repeat split => //=; apply ety_a' => //=.
  - (* composition *)
    apply concat_cancel_last in H2. destruct H2. subst.
    by exists [::], t1s0, t2s0, t2s.
  - (* weakening *)
    edestruct IHHType; eauto.
    destruct H as [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]. subst.
    exists (ts ++ x), t1s', t2s', t3s'.
    by repeat split => //; rewrite catA.
  - (* Trap *)
    exists [::], t1s, t2s, t1s.
    repeat split => //=.
    + apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
    + by apply ety_trap.
  - (* Local *)
    exists [::], [::], t2s, [::]. repeat split => //=.
    + by apply ety_a' => //.
    + by apply ety_local.
  - (* Invoke *)
    exists [::], t1s, t2s, t1s. repeat split => //=.
    + apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
    + by eapply ety_invoke; eauto.
  - (* Label *)
    exists [::], [::], t2s0, [::]. repeat split => //=.
    + by apply ety_a' => //.
    + by eapply ety_label; eauto.
Qed.

Lemma e_composition_typing: forall s C es1 es2 t1s t2s,
    e_typing s C (es1 ++ es2) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             e_typing s C es1 (Tf t1s' t3s) /\
                             e_typing s C es2 (Tf t3s t2s').
Proof.
  move => s C es1 es2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1.
  clear Heqes2'. subst.
  induction es2' => //=; move => es1 t1s t2s HType.
  - unfold rev in HType; simpl in HType. subst.
    rewrite cats0 in HType.
    exists [::], t1s, t2s, t2s.
    repeat split => //=.
    apply ety_a' => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite rev_cons in HType.
    rewrite -cats1 in HType. subst.
    rewrite catA in HType.
    apply e_composition_typing_single in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]]. subst.
    apply IHes2' in H3.
    destruct H3 as [ts2 [t1s2 [t2s2 [t3s2 [H5 [H6 [H7 H8]]]]]]]. subst.
    exists ts', (ts2 ++ t1s2), t2s', (ts2 ++ t3s2).
    repeat split => //.
    + by apply ety_weakening.
    + rewrite rev_cons. rewrite -cats1.
      eapply ety_composition; eauto.
      by apply ety_weakening.
Qed.

Lemma bet_composition': forall C es1 es2 t1s t2s t3s,
    be_typing C es1 (Tf t1s t2s) ->
    be_typing C es2 (Tf t2s t3s) ->
    be_typing C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => C es1 es2 t1s t2s t3s HType1 HType2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1. generalize dependent es2.
  generalize dependent t1s. generalize dependent t2s.
  generalize dependent t3s.
  induction es2' => //=.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1. destruct es2 => //=. rewrite cats0.
    apply empty_typing in HType2. by subst.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1.
    rewrite rev_cons in H2. rewrite -cats1 in H2.
    rewrite H2 in HType2.
    apply composition_typing in HType2.
    destruct HType2 as [ts [t1s' [t2s' [t3s' [H3 [H4 [H5 H6]]]]]]]. subst.
    rewrite catA. eapply bet_composition => //=.
    instantiate (1 := (ts ++ t3s')).
    eapply IHes2' => //.
    instantiate (1 := (ts ++ t1s')); first by apply bet_weakening.
    symmetry. by apply revK.
    by apply HType1.
    by apply bet_weakening.
Qed.

Lemma bet_composition_front: forall C e es t1s t2s t3s,
    be_typing C [::e] (Tf t1s t2s) ->
    be_typing C es (Tf t2s t3s) ->
    be_typing C (e :: es) (Tf t1s t3s).
Proof.
  intros.
  rewrite - cat1s.
  by eapply bet_composition'; eauto.
Qed.

Lemma et_composition': forall s C es1 es2 t1s t2s t3s,
    e_typing s C es1 (Tf t1s t2s) ->
    e_typing s C es2 (Tf t2s t3s) ->
    e_typing s C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => s C es1 es2 t1s t2s t3s HType1 HType2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1. generalize dependent es2.
  generalize dependent t1s. generalize dependent t2s.
  generalize dependent t3s.
  induction es2' => //=.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1. destruct es2 => //=. rewrite cats0.
    apply et_to_bet in HType2. apply empty_typing in HType2. by subst.
  - by [].
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1.
    rewrite rev_cons in H2. rewrite -cats1 in H2.
    rewrite H2 in HType2.
    apply e_composition_typing in HType2.
    destruct HType2 as [ts [t1s' [t2s' [t3s' [H3 [H4 [H5 H6]]]]]]]. subst.
    rewrite catA. eapply ety_composition => //=.
    instantiate (1 := (ts ++ t3s')).
    eapply IHes2' => //.
    instantiate (1 := (ts ++ t1s')); first by apply ety_weakening.
    symmetry. by apply revK.
    by apply HType1.
    by apply ety_weakening.
Qed.

End composition_typing_proofs.

(************ these come from the certified itp *************)

(* XXX does this exist elsewhere? *)
Lemma bet_const' : forall C vs,
  be_typing C (map BI_const vs) (Tf [::] (map typeof vs)).
Proof.
  intros C vs. induction vs as [|vs' v IHvs] using last_ind.
  - apply bet_empty.
  - rewrite <- cats1. rewrite map_cat.
    apply bet_composition with (t2s := map typeof vs') => //.
    rewrite map_cat.
    replace (map typeof vs') with ((map typeof vs') ++ [::]) at 1;
      last by rewrite cats0.
    by apply bet_weakening; apply bet_const.
Qed.

Lemma to_b_v_to_e_is_bi_const : forall vs,
  to_b_list (v_to_e_list vs) = map BI_const vs.
Proof.
  induction vs as [|v vs' IH] => //.
  rewrite <- cat1s.
  unfold v_to_e_list. unfold to_b_list.
  unfold v_to_e_list in IH. unfold to_b_list in IH.
  repeat rewrite map_cat.
  f_equal => //.
Qed.

Lemma cats_injective : forall T (s1 : seq T),
  injective (fun s2 => s1 ++ s2).
Proof.
  intros T s1 s2 s2' Heq.
  induction s1 => //.
  by injection Heq => //.
Qed.

Lemma seq_split_predicate : forall (T : eqType) (xs xs' ys ys' : seq T) (y : T) (P : pred T),
  xs ++ [:: y] ++ ys = xs' ++ ys' ->
  all P xs ->
  all P xs' ->
  ~ P y ->
  size xs >= size xs'.
Proof.
  intros T xs xs' ys ys' y P H HPxs HPxs' HnPy.
  destruct (size xs < size xs') eqn:Hsize => //; last by lias.
  exfalso; apply HnPy.
  apply f_equal with (f := drop (size xs)) in H.
  rewrite drop_size_cat in H => //.
  rewrite drop_cat in H.
  rewrite Hsize in H.
  assert (size (drop (size xs) xs') > 0). { by rewrite size_drop; lias. }
  destruct (drop (size xs) xs') as [|x xs''] eqn:Heqdrop => //.
  assert (List.In x xs').
  {
    rewrite <- cat_take_drop with (n0 := size xs).
    apply List.in_or_app; right.
    by rewrite Heqdrop; apply List.in_eq.
  }
  inversion H; subst x.
  by apply list_all_forall with (l := xs').
Qed.

Lemma concat_cancel_first_n: forall (T : eqType) (l1 l2 l3 l4: seq T),
    l1 ++ l2 = l3 ++ l4 ->
    size l1 = size l3 ->
    (l1 == l3) && (l2 == l4).
Proof.
  move => T l1 l2 l3 l4 HCat HSize.
  rewrite -eqseq_cat; first by apply/eqP.
  assert (size (l1 ++ l2) = size (l3 ++ l4)); first by rewrite HCat.
  repeat rewrite size_cat in H.
  rewrite HSize in H. by lias.
Qed.

Lemma ves_cat_e_split : forall vs vs' e e' es',
  vs ++ [:: e] ++ es' = vs' ++ [:: e'] ->
  const_list vs ->
  const_list vs' ->
  ~ is_const e ->
  vs = vs' /\ e = e' /\ es' = [::].
Proof.
  intros vs vs' e e' es' H Hconst Hconst' Hnconst.
  assert (H' : vs ++ [:: e] ++ es' = vs' ++ [:: e']) => //.
  apply seq_split_predicate with (P := is_const) in H => //.
  destruct (size vs' == size vs) eqn:Heqb; move/eqP in Heqb.
  - apply concat_cancel_first_n in H' => //.
    move/andP in H'; destruct H' as [Heqvs Heqe'].
    move/eqP in Heqvs. move/eqP in Heqe'.
    by inversion Heqe'; split => //.
  - move/leP in H. apply Lt.le_lt_or_eq in H as [H|] => //.
    assert (size vs' < size vs). { by lias. }
    apply f_equal with (f := size) in H'.
    repeat rewrite size_cat in H'.
    simpl in H'.
    by lias.
Qed.

Lemma es_split_by_non_const : forall vs vs' e es es',
  vs ++ [:: e] ++ es = vs' ++ es' ->
  const_list vs ->
  const_list vs' ->
  ~ is_const e ->
  exists vs'', vs = vs' ++ vs''.
Proof.
  intros vs vs' e es es' H Hconstvs Hconstvs' Hnconste.
  assert (Hsize : size vs >= size vs').
  { by apply (seq_split_predicate H Hconstvs Hconstvs' Hnconste). }
  exists (drop (size vs') vs).
  assert (H' : vs ++ e :: es = vs' ++ es') => //.
  apply f_equal with (f := take (size vs')) in H.
  rewrite take_cat in H.
  destruct (size vs' < size vs) eqn:?.
  - rewrite take_cat ltnn subnn take0 cats0 in H.
    remember (size vs') as n eqn:Heqn.
    clear Heqn.
    subst vs'.
    by rewrite cat_take_drop.
  - assert (Heqsize : size vs' = size vs). { by lias. }
    rewrite Heqsize.
    rewrite drop_size.
    rewrite cats0.
    apply concat_cancel_first_n in H' => //.
    move/andP in H'.
    destruct H'.
    by apply/eqP.
Qed.

Fixpoint empty_vs_base lh : bool :=
  match lh with
  | LH_base [::] _ => true
  | LH_rec _ _ _ lh _ => empty_vs_base lh
  | _ => false
  end.

Lemma lfilled_collapse_empty_vs_base : forall i lh rvs vcs e es,
  lfilledInd i lh (vs_to_es rvs ++ [:: e]) (v_to_e_list vcs ++ es) ->
  ~ is_const e ->
  empty_vs_base lh ->
  exists lh', lfilledInd i lh' [:: e] es.
Proof.
  (* XXX fragile names *)
  induction i as [|i]; intros lh rvs vcs e es Hlf He Hbase.
  - inversion Hlf; subst.
    destruct vs => //. simpl in *.
    rewrite <- catA in H.
    assert (Heqrvs : exists vcs', vs_to_es rvs = v_to_e_list vcs ++ vcs').
    { by apply (es_split_by_non_const H) => //; try by apply v_to_e_is_const_list. }
    destruct Heqrvs as [vcs' Heqrvs]; rewrite Heqrvs in H, Hlf.
    rewrite <- catA in H.
    apply cats_injective in H; subst es.
    exists (LH_base vcs' es').
    apply LfilledBase.
    eapply const_list_split.
    rewrite <- Heqrvs.
    by apply v_to_e_is_const_list.
  - inversion Hlf; subst.
    destruct (split_vals_e LI) as [LIvs LIes] eqn:HsplitLI.
    apply split_vals_e_v_to_e_duality in HsplitLI. subst LI.
    destruct (IHi lh' rvs LIvs e LIes H4 He Hbase) as [lh'' Hlf''].
    assert (Heqvs : exists vcs', vs = v_to_e_list vcs ++ vcs').
    { by apply (es_split_by_non_const H0) => //; last by apply v_to_e_is_const_list. }
    destruct Heqvs as [vcs' ->].
    rewrite <- catA in H0.
    apply cats_injective in H0; subst es.
    apply lfilled_collapse1 with (l := 0) in H4 as [lh''' H4] => //;
      last by apply v_to_e_is_const_list.
    rewrite subn0 drop_size in H4 => //.
    eexists.
    apply LfilledRec; first by apply const_list_split in H1 as [??].
    by apply H4.
Qed.

(************ certified itp properties *************)
Lemma cat_cons_not_nil : forall T (xs : list T) y ys,
  xs ++ (y :: ys) <> [::].
Proof. move => T xs y ys E. by move: (List.app_eq_nil _ _ E) => [? ?]. Qed.

Lemma not_reduce_simple_nil : forall es', ~ reduce_simple [::] es'.
Proof.
  assert (forall es es', reduce_simple es es' -> es = [::] -> False) as H.
  { move => es es' H.
    elim: {es es'} H => //=.
    { move => vs es _ _ t1s t2s _ _ _ _ H.
      apply: cat_cons_not_nil. exact H. }
    { move => vs es _ _ t1s t2s _ _ _ _ H.
      apply: cat_cons_not_nil. exact H. }
    { move => es lh _ H Hes.
      rewrite Hes {es Hes} /lfilled /operations.lfilled /= in H.
      case: lh H => //=.
      { move => es es2.
        case_eq (const_list es) => //=.
        move=> _ /eqP H.
        symmetry in H.
        by move: (List.app_eq_nil _ _ H) => [? ?]. } } }
  { move => es' H2.
    apply: H. exact H2. done. }
Qed.


Lemma lfill_cons_not_Some_nil : forall i lh es es' e es0,
  lfill i lh es = es' -> es = e :: es0 -> es' <> Some [::].
Proof.
  elim.
  { elim; last by intros; subst.
    move=> l l0 es es' /=.
    case: (const_list l).
    { move => Hfill H1 H2 H3 H4.
      rewrite H4 in H2.
      injection H2 => H5 {H2}.
      rewrite H3 in H5.
      apply: cat_cons_not_nil.
      exact H5.
       }
    { intros; subst; discriminate. } }
  { move=> n IH.
    elim; first by intros; subst.
    intros.
    rewrite /= in H0.
    move: H0.
    case: (const_list l).
    { rewrite H1 {H1}.
      case_eq (lfill n l1 (e :: es0)).
      { move=> l3 H1 H2 H3.
        rewrite H3 in H2.
        injection H2.
        move=> {} H2.
        apply: cat_cons_not_nil.
        exact H2. }
      { intros; subst; discriminate. } }
    { intros; subst; discriminate. } }
Qed.

Lemma lfilled_not_nil : forall i lh es es', lfilled i lh es es' -> es <> [::] -> es' <> [::].
Proof.
  move => i lh es es' H Hes Hes'.
  move: (List.exists_last Hes) => [e [e0 H']].
  rewrite H' in H.
  move: H.
  rewrite /lfilled /operations.lfilled.
  case_eq (operations.lfill i lh es).
  { intros; subst.
    rewrite H in H0.
    assert ([::] = l) as H0'.
    { apply/eqP.
      apply H0. }
    { rewrite H0' in H.
      rewrite /= in H.
      case E: (e ++ (e0 :: l)%SEQ)%list; first by move: (List.app_eq_nil _ _ E) => [? ?].
      apply: lfill_cons_not_Some_nil.
      apply: H.
      apply: E.
      by rewrite H0'. } }
  { intros; subst.
    rewrite H in H0.
    done. }
Qed.

Variable host_instance: host host_function.

Local Definition reduce := @reduce host_function host_instance.

Lemma reduce_not_nil : forall hs hs' σ1 f es σ2 f' es',
  reduce hs σ1 f es hs' σ2 f' es' -> es <> [::].
Proof.
  move => hs hs' σ1 f es σ2 f' es' Hred.
  elim: {σ1 f es f' σ2} Hred => //;
    try solve [ repeat intro;
                match goal with
                | H : (_ ++ _)%SEQ = [::] |- _ =>
                  by move: (app_eq_nil _ _ H) => [? ?]
                end ].
  { move => e e' _ _ _ Hreds He.
    rewrite He in Hreds.
    apply: not_reduce_simple_nil.
    apply: Hreds. }
  { intros. destruct ves => //. }
  { intros. destruct ves => //. }
  { intros. by destruct ves => //. }
  { intros. apply: lfilled_not_nil. exact H1. exact H0. }
Qed.

(** Store extension properties **)

Let func_extension: function_closure -> function_closure -> bool := @func_extension _.
Let store_extension: store_record -> store_record -> Prop := @store_extension _.

Lemma reflexive_all2_same: forall {X:Type} f (l: seq X),
    reflexive f ->
    all2 f l l.
Proof.
  move => X f l.
  induction l; move => H; unfold reflexive in H => //=.
  apply/andP. split => //=.
  by apply IHl.
Qed.

Lemma func_extension_refl: forall f,
    func_extension f f.
Proof.
  move => f. by unfold func_extension, operations.func_extension.
Qed.

Lemma all2_func_extension_same: forall f,
    all2 func_extension f f.
Proof.
  move => f.
  apply reflexive_all2_same. unfold reflexive.
  by apply func_extension_refl.
Qed.

Lemma tab_extension_refl: forall t,
    tab_extension t t.
Proof.
  move => t. unfold tab_extension.
  by apply/andP.
Qed.

Lemma all2_tab_extension_same: forall t,
    all2 tab_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive.
  by apply tab_extension_refl.
Qed.

Lemma mem_extension_refl: forall m,
    mem_extension m m.
Proof.
  move => m.
  unfold mem_extension.
  apply/andP; split => //.
  by apply N.leb_le; lias.
Qed.

Lemma all2_mem_extension_same: forall t,
    all2 mem_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive.
  by apply mem_extension_refl.
Qed.

Lemma glob_extension_refl: forall t,
    glob_extension t t.
Proof.
  move => t.
  unfold glob_extension.
  do 2 (apply/andP; split => //).
  apply/orP.
  by right.
Qed.

Lemma all2_glob_extension_same: forall t,
    all2 glob_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. by apply glob_extension_refl.
Qed.

Lemma comp_extension_same_refl {T: Type} (l: list T) f:
    reflexive f ->
    comp_extension l l f.
Proof.
  move => Hrefl.
  unfold comp_extension.
  apply/andP; split; first by lias.
  rewrite length_is_size take_size.
  by apply reflexive_all2_same.
Qed.

Lemma func_extension_trans:
  transitive func_extension.
Proof.
  move => x1 x2 x3 Hext1 Hext2.
  unfold func_extension, operations.func_extension in *.
  remove_bools_options.
  by apply/eqP; subst.
Qed.
  
Lemma tab_extension_trans:
  transitive tab_extension.
Proof.
  move => x1 x2 x3 Hext1 Hext2.
  unfold tab_extension in *.
  remove_bools_options.
  apply/andP; split; last apply/eqP.
  - by lias.
  - by destruct x2; simpl in *; subst.
Qed.
    
Lemma mem_extension_trans:
  transitive mem_extension.
Proof.
  move => x1 x2 x3 Hext1 Hext2.
  unfold mem_extension in *.
  remove_bools_options.
  apply/andP; split; last apply/eqP.
  - move/N.leb_spec0 in H.
    move/N.leb_spec0 in H1.
    apply/N.leb_spec0.
    by lias.
  - by destruct x2; simpl in *; subst.
Qed.
    
Lemma glob_extension_trans:
  transitive glob_extension.
Proof.
  move => x1 x2 x3 Hext1 Hext2.
  unfold glob_extension in *.
  destruct x1, x2, x3 => /=; simpl in *.
  remove_bools_options; rewrite - H3 in H0; subst => /=; try by apply/eqP.
  repeat (apply/andP; split => //).
  apply/orP; by right.
Qed.

Lemma nth_error_take_longer {T: Type} (l: list T) n k:
  n < k ->
  List.nth_error l n = List.nth_error (take k l) n.
Proof.
  move: k l.
  induction n; move => k l Hlt; destruct l, k => //=.
  apply IHn; by lias.
Qed.

Lemma comp_extension_trans {T: Type} (l1 l2 l3: list T) f:
  comp_extension l1 l2 f ->
  comp_extension l2 l3 f ->
  transitive f ->
  comp_extension l1 l3 f.
Proof.
  move => Hext1 Hext2 Htrans.
  unfold comp_extension in *.
  remove_bools_options.
  apply/andP; split; first by lias.
  apply all2_spec.
  - rewrite size_take.
    repeat rewrite length_is_size in H H0 H1 H2.
    rewrite length_is_size.
    assert (size l1 <= size l3); first lias.
    destruct (size l1 < size l3) eqn: Hlt => //; last by lias.
  - move => n x y Hnth1 Hnth2.
    specialize (all2_element H2 Hnth1) as [z Hnth3].
    assert (f x z) as Htrans1; first by eapply all2_projection; eauto.
    assert (f z y) as Htrans2; last eauto.
    apply nth_error_Some_length in Hnth1.
    rewrite - nth_error_take_longer in Hnth2; last by lias.
    rewrite - nth_error_take_longer in Hnth3; last by lias.
    eapply all2_projection; [by apply H0 | eauto | ].
    rewrite - nth_error_take_longer => //.
    by lias.
Qed.
    
Lemma store_extension_trans (s1 s2 s3: store_record):
  store_extension s1 s2 ->
  store_extension s2 s3 ->
  store_extension s1 s3.
Proof.
  move => Hext1 Hext2.
  unfold store_extension, operations.store_extension in *.
  remove_bools_options.
  apply/andP; split; last by eapply comp_extension_trans; eauto; apply glob_extension_trans.
  apply/andP; split; last by eapply comp_extension_trans; eauto; apply mem_extension_trans.
  apply/andP; split; last by eapply comp_extension_trans; eauto; apply tab_extension_trans.
  by eapply comp_extension_trans; eauto; apply func_extension_trans.
Qed.
  
Lemma store_extension_same: forall s,
    store_extension s s.
Proof.
  move => s. unfold store_extension.
  repeat (apply/andP; split => //); rewrite length_is_size take_size.
  + by apply all2_func_extension_same.
  + by apply all2_tab_extension_same.
  + by apply all2_mem_extension_same.
  + by apply all2_glob_extension_same.
Qed.

Lemma comp_extension_lookup {T: Type} (l1 l2: list T) f n x:
  comp_extension l1 l2 f ->
  List.nth_error l1 n = Some x ->
  exists y, (List.nth_error l2 n = Some y /\ f x y).
Proof.
  move => Hext Hnth.
  unfold comp_extension in Hext.
  remove_bools_options.
  assert (lt n (length l1)) as Hlen; first by apply List.nth_error_Some; rewrite Hnth.
  destruct (List.nth_error l2 n) as [y |] eqn:Hnth'; last by apply List.nth_error_None in Hnth'; lias.
  apply (nth_error_take (k := length l1)) in Hnth'; last by lias.
  specialize (all2_projection H0 Hnth Hnth') as Hproj.
  by exists y.
Qed.

Lemma store_extension_lookup_func: forall s s' n cl,
    store_extension s s' ->
    List.nth_error (s_funcs s) n = Some cl ->
    List.nth_error (s_funcs s') n = Some cl.
Proof.
  move => s s' n cl Hext Hnth.
  unfold store_extension, operations.store_extension in Hext.
  remove_bools_options.
  eapply comp_extension_lookup in Hnth; eauto.
  unfold operations.func_extension in Hnth.
  destruct Hnth as [? [Hnth Heq]].
  by move/eqP in Heq; subst.
Qed.

Lemma store_extension_lookup_tab: forall s s' n x,
    store_extension s s' ->
    List.nth_error (s_tables s) n = Some x ->
    exists x', List.nth_error (s_tables s') n = Some x' /\ tab_extension x x'.
Proof.
  move => s s' n cl Hext Hnth.
  unfold store_extension, operations.store_extension in Hext.
  remove_bools_options.
  by eapply comp_extension_lookup in Hnth; eauto.
Qed.

Lemma store_extension_lookup_mem: forall s s' n x,
    store_extension s s' ->
    List.nth_error (s_mems s) n = Some x ->
    exists x', List.nth_error (s_mems s') n = Some x' /\ mem_extension x x'.
Proof.
  move => s s' n cl Hext Hnth.
  unfold store_extension, operations.store_extension in Hext.
  remove_bools_options.
  by eapply comp_extension_lookup in Hnth; eauto.
Qed.

Lemma store_extension_lookup_glob: forall s s' n x,
    store_extension s s' ->
    List.nth_error (s_globals s) n = Some x ->
    exists x', List.nth_error (s_globals s') n = Some x' /\ glob_extension x x'.
Proof.
  move => s s' n cl Hext Hnth.
  unfold store_extension, operations.store_extension in Hext.
  remove_bools_options.
  by eapply comp_extension_lookup in Hnth; eauto.
Qed.

End Host.
