(** Miscellaneous properties about Wasm operations **)

From Wasm Require Export datatypes_properties operations typing opsem common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Bool Program NArith ZArith Wf_nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Basic Lemmas **)

(** List operations **)

(* Friction between seq and List *)
Lemma cat_app {A} (l1 : list A) l2 :
  cat l1 l2 = app l1 l2.
Proof. done. Qed.

Lemma length_is_size: forall {X:Type} (l: list X),
  length l = size l.
Proof.
  move => X l. by elim: l.
Qed.

Lemma rev_length {T} (l: list T):
  length (rev l) = length l.
Proof.
  by repeat rewrite length_is_size; rewrite size_rev.
Qed.

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

Lemma those_length {T: Type} (l1: list (option T)) l2:
  those l1 = Some l2 ->
  length l1 = length l2.
Proof.
  move: l2.
  rewrite - those_those0.
  induction l1 as [|x l1]; destruct l2 as [|y l2] => //=; destruct x => //=; move => Hthose.
  - by destruct (those0 l1) => //.
  - f_equal.
    destruct (those0 l1) eqn:Hthose0 => //=.
    apply IHl1.
    simpl in Hthose.
    injection Hthose as ->.
    by f_equal.
Qed.

Lemma those_lookup_inv {T: Type} (l1: list (option T)) l2:
  those l1 = Some l2 ->
  (forall i x, List.nth_error l2 i = Some x ->
          List.nth_error l1 i = Some (Some x)).
Proof.
  rewrite -those_those0.
  move: l2. induction l1 as [|x l1]; destruct l2 as [|y l2] => //=; move => Heq i z; destruct i => //=; move => Hnth; destruct x => //.
  - injection Hnth as ->.
    destruct (those0 l1) eqn:Hthose => //.
    simpl in Heq.
    by injection Heq as ->.
  - destruct (those0 l1) eqn:Hthose => //.
    simpl in Heq.
    injection Heq as ->->.
    eapply IHl1; by eauto.
Qed.

Lemma those_lookup {T: Type} (l1: list (option T)) l2:
  those l1 = Some l2 ->
  (forall i x, List.nth_error l1 i = Some (Some x) ->
          List.nth_error l2 i = Some x).
Proof.
  rewrite -those_those0.
  move: l2. induction l1 as [|x l1]; destruct l2 as [|y l2] => //=; intros; remove_bools_options; destruct i; simpl in * => //=; first by injection H0 as <-.
  by apply IHl1.
Qed.

Lemma those_spec_None {T: Type} (l1: list (option T)) n:
  those l1 <> None ->
  n < length l1 ->
  exists y, List.nth_error l1 n = Some (Some y).
Proof.
  rewrite -those_those0.
  move: n.
  induction l1 as [| x l1] => //=.
  move => n Hx Hlen; destruct n => //=; destruct x => //=; first by eexists.
  apply IHl1 => //.
  move => Hcontra; by rewrite Hcontra in Hx.
Qed.

Lemma those_map_lookup {T T': Type}: forall f (l: list T) (l': list T') n x,
    those (map f l) = Some l' ->
    List.nth_error l n = Some x ->
    exists y, f x = Some y /\ List.nth_error l' n = Some y.
Proof.
  setoid_rewrite <- those_those0.
  move => f. elim => //=.
  - case => //; by case.
  - move => x l IH.
    case => y l' => //; intros; remove_bools_options.
    destruct n as [ | n']; simpl in *.
    + injection H0 as <-.
      by exists y.
    + by apply IH.
Qed.

Lemma those_cons_impl {T: Type}: forall (l: list (option T)) l' x y,
    those (x :: l) = Some (y :: l') ->
    x = Some y /\
    those l = Some l'.
Proof.
  setoid_rewrite <- those_those0.
  move => k k' x y /=Hthose.
  by remove_bools_options.
Qed.
  
Lemma those_cat {T: Type}: forall (l1 l2: list (option T)) l1' l2',
    those l1 = Some l1' ->
    those l2 = Some l2' ->
    those (l1 ++ l2) = Some (l1' ++ l2').
Proof.
  setoid_rewrite <- those_those0.
  elim.
  - move => l2; by case => //=.
  - move => x l1 IH l2 l1' l2' /= Hthose1 Hthose2 => /=.
    remove_bools_options.
    by erewrite IH; eauto.
Qed.

Lemma those_spec {T: Type}: forall (l1: list (option T)) l2,
    length l1 = length l2 ->
    (forall n x, List.nth_error l2 n = Some x ->
            List.nth_error l1 n = Some (Some x)) ->
    those l1 = Some l2.
Proof.
  setoid_rewrite <- those_those0.
  induction l1; move => l2 Hlen Hspec => /=.
  - by destruct l2.
  - specialize (Hspec 0) as Hspec0; destruct l2 => //; simpl in *.
    specialize (Hspec0 t erefl) as Heq.
    inversion Heq; subst; clear Heq.
    unfold option_map.
    erewrite IHl1; eauto.
    move => n x Hnth.
    specialize (Hspec (S n) x); simpl in *.
    by apply Hspec.
Qed.

Lemma const_list_cat: forall vs1 vs2,
    const_list (vs1 ++ vs2) = const_list vs1 && const_list vs2.
Proof.
  move => vs1 vs2.
  repeat rewrite cat_app.
  unfold const_list.
  by rewrite List.forallb_app.
Qed.

Lemma const_list_concat: forall vs1 vs2,
    const_list vs1 ->
    const_list vs2 ->
    const_list (vs1 ++ vs2).
Proof.
  move => vs1 vs2.
  rewrite const_list_cat; by lias.
Qed.

Lemma const_list_split: forall vs1 vs2,
    const_list (vs1 ++ vs2) ->
    const_list vs1 /\
    const_list vs2.
Proof.
  move => vs1 vs2 Hconst.
  rewrite const_list_cat in Hconst.
  by move/andP in Hconst.
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

Lemma const_list_cons : forall a l,
  const_list (a :: l) = is_const a && const_list l.
Proof. by []. Qed.

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

Lemma v_to_e_cat: forall vs1 vs2,
    v_to_e_list vs1 ++ v_to_e_list vs2 = v_to_e_list (vs1 ++ vs2).
Proof.
  intros; by rewrite - map_cat.
Qed.

Lemma v_to_e_size: forall vs,
    size (v_to_e_list vs) = size vs.
Proof.
  intros; by rewrite size_map.
Qed.

(* Technically the same as above, but this pattern occurs very frequently *)
Lemma v_to_e_length: forall vs,
    length (v_to_e_list vs) = length vs.
Proof.
  intros; by rewrite length_is_size v_to_e_size.
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
  intros; by apply map_take.
Qed.

Lemma v_to_e_drop: forall l n,
  v_to_e_list (drop n l) = drop n (v_to_e_list l).
Proof.
  intros; by apply map_drop.
Qed.

Lemma v_to_e_rev: forall l,
  v_to_e_list (rev l) = rev (v_to_e_list l).
Proof.
  intros; by apply map_rev.
Qed.

Lemma ve_inv: forall v e,
    (v_to_e v) = e <->
    e_to_v_opt e = Some v.
Proof.
  split.
  - case v => //=; move => v' <- => //=.
    by case v' => //=.
  - case e => //=; move => e'. 2,3: by move => [<-].
    case e' => //=; by move => ? [<-] => //.
Qed.

Lemma v2e2v: forall v,
    e_to_v_opt (v_to_e v) = Some v.
Proof.
  move => v.
  remember (v_to_e v) as e.
  by apply ve_inv.
Qed.

Lemma ve_inj: forall v1 v2,
    v_to_e v1 = v_to_e v2 ->
    v1 = v2.
Proof.
  move => v1 v2.
  destruct v1 as [ | | [| |]]; destruct v2 as [ | | [| |]] => //=; by move => [<-].
Qed.

Lemma v_to_e_inj: forall l1 l2,
    v_to_e_list l1 = v_to_e_list l2 ->
    l1 = l2.
Proof.
  apply inj_map.
  unfold injective.
  by apply ve_inj.
Qed.

Lemma to_b_list_concat: forall es1 es2,
    to_b_list (es1 ++ es2) = to_b_list es1 ++ to_b_list es2.
Proof.
  intros; by rewrite/to_b_list map_cat.
Qed.
    
Lemma to_b_list_rev: forall es : seq administrative_instruction,
    rev (to_b_list es) = to_b_list (rev es).
Proof.
  intros; by rewrite/to_b_list map_rev.
Qed.
    
Lemma to_e_list_basic: forall bes,
    es_is_basic (to_e_list bes).
Proof.
  by induction bes => //=.
Qed.

Lemma basic_concat: forall es1 es2,
    es_is_basic (es1 ++ es2) ->
    es_is_basic es1 && es_is_basic es2.
Proof.
  induction es1 => //=.
  move => es2 H; move/andP in H. destruct H.
  apply IHes1 in H0; move/andP in H0; destruct H0.
  apply/andP; split => //=.
  by apply/andP; split => //=.
Qed.

Lemma basic_split: forall es1 es2,
    es_is_basic es1 ->
    es_is_basic es2 ->
    es_is_basic (es1 ++ es2).
Proof.
  induction es1 => //=.
  move => es2 H1 H2.
  move/andP in H1.
  destruct H1.
  apply/andP.
  split => //=.
  by apply IHes1.
Qed.

Lemma is_const_exists: forall e,
    is_const e ->
    {v | e = v_to_e v}.
Proof.
  move => e HConst.
  unfold is_const in HConst.
  destruct (e_to_v_opt e) as [v | ] eqn:Hetov => //.
  apply ve_inv in Hetov; by exists v.
Qed.

Lemma const_es_exists: forall es,
    const_list es ->
    {vs | es = v_to_e_list vs}.
Proof.
  induction es => //=.
  - by exists [::].
  - move => HConst.
    move/andP in HConst. destruct HConst as [Ha HConst].
    apply IHes in HConst as [vs Heq].
    apply is_const_exists in Ha as [v Heqv]; subst.
    by exists (v :: vs) => //=.
Qed.

Lemma const_those_const: forall vs vcs,
    vs = v_to_e_list vcs ->
    e_to_v_list_opt vs = Some vcs.
Proof.
  setoid_rewrite <- those_those0.
  move => ? vcs ->.
  induction vcs => //=.
  rewrite v2e2v.
  by rewrite IHvcs.
Qed.

Lemma v_to_e_const: forall vs,
    const_list (v_to_e_list vs).
Proof.
  elim => //=.
  move => v vs Hconst.
  unfold is_const.
  by rewrite v2e2v.
Qed.
  
Lemma split_vals_inv: forall es vs es',
    split_vals_e es = (vs, es') ->
    es = (v_to_e_list vs) ++ es'.
Proof.
  move => es vs. move: es. elim: vs => //.
  - move=> es es'. destruct es => //=.
    + by inversion 1.
    + destruct (e_to_v_opt a) as [v | ] eqn:Hconst => //.
      destruct (split_vals_e es) eqn:IH => //.
      by inversion 1.
  - move => a l H es es' HSplit.
    destruct es => //.
    simpl in HSplit.
    destruct (e_to_v_opt a0) as [v | ] eqn:Hconst => //.
    destruct (split_vals_e es) eqn:IH => //.
    injection HSplit as -> -> ->.
    apply H in IH; subst => /=.
    f_equal.
    by apply ve_inv in Hconst.
Qed.

Lemma split_vals_nconst: forall es vs e es',
    split_vals_e es = (vs, e :: es') ->
    ~ is_const e.
Proof.
  elim; first by move => ??? /=? => //.
  move => e es IH vs0 e0 es' Hsplit.
  simpl in *.
  destruct (e_to_v_opt e) as [v | ] eqn:Hconst => //.
  - destruct (split_vals_e es) eqn: IHes => //.
    injection Hsplit as <- ->.
    by eapply IH; eauto.
  - injection Hsplit as <- <- <-.
    unfold is_const.
    by rewrite Hconst.
Qed.

Lemma value_split_0 : forall es ves,
  split_vals_e es = (ves, [::]) ->
  const_list es \/ es_is_trap es.
Proof.
  intros es ves Hsplit. left.
  apply split_vals_inv in Hsplit. subst es.
  rewrite cats0. by apply v_to_e_const.
Qed.

Lemma value_trap : forall e es es'' ves,
  split_vals_e es = (ves, e :: es'') ->
  e_is_trap e ->
  ((es'' != [::]) || (ves != [::])) = false ->
  const_list es \/ es_is_trap es.
Proof.
  intros e es es'' ves Hsplit Htrap Hesves. right.
  apply split_vals_inv in Hsplit. subst es.
  rewrite <- negb_and in Hesves. move/andP in Hesves. destruct Hesves as [Hes Hves].
  move/eqP in Hes. move/eqP in Hves. subst es'' ves.
  by destruct e.
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
      * simpl. f_equal. by apply IHbes.
      * by apply to_e_list_basic.
Qed.

Lemma e_b_elim: forall bes es,
    bes = to_b_list es ->
    es_is_basic es ->
    es = to_e_list bes.
Proof.
  induction bes; move => es H1 H2 => //=.
  - by destruct es => //=.
  - destruct es => //=. simpl in H1. simpl in H2.
    move/andP in H2.
    destruct H2.
    inversion H1; subst.
    destruct a0 => //=.
    f_equal. by apply IHbes => //=.
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

Lemma nth_error_app_Some {T: Type} (l1 l2 : list T) n x:
  List.nth_error l1 n = Some x ->
  List.nth_error (l1 ++ l2) n = Some x.
Proof.
  move => Hnth.
  rewrite List.nth_error_app1 => //.
  by eapply nth_error_Some_length; eauto.
Qed.

Lemma Forall_lookup: forall {X:Type} f (l:seq X) n x,
    List.Forall f l ->
    List.nth_error l n = Some x ->
    f x.
Proof.
  move => X f l n x.
  generalize dependent l.
  induction n => //; destruct l => //=; move => HF HS; remove_bools_options => //; inversion HF; subst => //.
  eapply IHn; by eauto.
Qed.

Lemma all_repeat: forall {X: Type} (f: X -> bool) v n,
    f v = true ->
    all f (List.repeat v n).
Proof.
  move => X f v. elim => //=.
  move => n IH Hf.
  rewrite Hf => /=; by apply IH.
Qed.

Lemma all_projection: forall {X:Type} f (l:seq X) n x,
    all f l ->
    List.nth_error l n = Some x ->
    f x.
Proof.
  move => X f l n x Hall Hnth.
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

Lemma all2_nth_impl {T1 T2: Type} (l1: list T1) (l2: list T2) f n x:
  all2 f l1 l2 ->
  List.nth_error l1 n = Some x ->
  exists y, List.nth_error l2 n = Some y /\ f x y.
Proof.
  move => Hall2 Hnth.
  destruct (List.nth_error l2 n) eqn:Hnth'.
  - exists t; split => //.
    by eapply all2_projection; eauto.
  - exfalso.
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

Lemma all2_cat {T1 T2: Type} (l1 l3: list T1) (l2 l4: list T2) (f: T1 -> T2 -> bool):
  size l1 = size l2 ->
  all2 f (l1 ++ l3) (l2 ++ l4) = all2 f l1 l2 && all2 f l3 l4.
Proof.
  move : l2 l3 l4.
  induction l1 as [ | x l1] => //=; destruct l2 as [ | y l2]; move => l3 l4 Hsize => //; simpl in *.
  erewrite IHl1; by lias.
Qed.

Lemma all2_split1 {T1 T2: Type} (l1: list T1) (l2 l3: list T2) (f: T1 -> T2 -> bool):
  all2 f l1 (l2 ++ l3) ->
  all2 f (take (size l2) l1) l2 && all2 f (drop (size l2) l1) l3.
Proof.
  move => Hall.
  assert (size l1 = size l2 + size l3) as Hsize; first by apply all2_size in Hall; rewrite size_cat in Hall.
  rewrite <- (cat_take_drop (size l2) l1) in Hall.
  by rewrite all2_cat in Hall; last by rewrite size_takel; lias.
Qed.

Lemma all2_split2 {T1 T2: Type} (l1 l2: list T1) (l3: list T2) (f: T1 -> T2 -> bool):
  all2 f (l1 ++ l2) l3 ->
  all2 f l1 (take (size l1) l3) && all2 f l2 (drop (size l1) l3).
Proof.
  move => Hall.
  assert (size l3 = size l1 + size l2) as Hsize; first by apply all2_size in Hall; rewrite size_cat in Hall.
  rewrite <- (cat_take_drop (size l1) l3) in Hall.
  by rewrite all2_cat in Hall; last by rewrite size_takel; lias.
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
 
Lemma nth_error_rev {T} (l: list T) n x:
  List.nth_error l n = Some x ->
  List.nth_error (rev l) (length l - (S n)) = Some x.
Proof.
  move: x n; induction l; first by destruct n.
  move => x n; destruct n => //=.
  - move => [->] => /=.
    rewrite rev_cons -cats1.
    replace (S (length l) - 1) with (length l); last by lias.
    rewrite List.nth_error_app2; last by rewrite rev_length.
    by rewrite rev_length Nat.sub_diag.
  - move => Hnth.
    rewrite subSS.
    rewrite rev_cons -cats1.
    apply IHl in Hnth.
    by apply nth_error_app_Some.
Qed. 

Lemma those_rev {T: Type}: forall (l1: list (option T)) l2,
    those (rev l1) = Some l2 ->
    those l1 = Some (rev l2).
Proof.
  move => l1 l2; move => Hthose.
  apply those_spec; first by (apply those_length in Hthose; rewrite (rev_length l2); rewrite (rev_length l1) in Hthose).
  move => n x Hnth.
  assert (n < length l2) as Hlen; first by apply nth_error_Some_length in Hnth; rewrite rev_length in Hnth; lias.
  apply nth_error_rev in Hnth.
  rewrite revK in Hnth.
  eapply those_lookup_inv in Hnth; eauto.
  apply nth_error_rev in Hnth.
  rewrite revK in Hnth.
  rewrite <- Hnth.
  f_equal.
  apply those_length in Hthose.
  rewrite rev_length in Hthose.
  repeat rewrite rev_length.
  rewrite Hthose.
  by lias.
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
        | host_function_class => idtac
        | host => idtac
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
           apply basic_concat in H; move/andP in H; destruct H as [Ha Hb]
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
  | H: ?es ++ [::?e] = [::_] |- _ =>
    apply extract_list1 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _] |- _ =>
    apply extract_list2 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _; _] |- _ =>
    apply extract_list3 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _; _; _] |- _ =>
    apply extract_list4 in H; destruct H; subst
  | H: ?es ++ [::?e] = ?es' ++ [::?e'] |- _ =>
    apply concat_cancel_last in H as [??]; subst
  | H: _ :: _ = _ ++ _ |- _ => symmetry in H
         end.

Lemma value_subtyping_eq: forall t,
    t <t: t.
Proof.
  move => t.
  unfold value_subtyping => /=.
  rewrite eq_refl.
  by lias.
Qed.

Lemma value_subtyping_trans: forall t1 t2 t3,
    t1 <t: t2 ->
    t2 <t: t3 ->
    t1 <t: t3.
Proof.
  unfold value_subtyping.
  move => t1 t2 t3 Hs1 Hs2; remove_bools_options; subst; rewrite eq_refl; by lias.
Qed.

Lemma values_subtyping_eq: forall ts,
    ts <ts: ts.
Proof.
  induction ts => //=.
  by rewrite value_subtyping_eq.
Qed.

Lemma values_subtyping_size: forall ts1 ts2,
    ts1 <ts: ts2 ->
    size ts1 = size ts2.
Proof.
  move => ts1 ts2 Hsub.
  by apply all2_size in Hsub.
Qed.

Lemma values_subtyping_trans: forall ts1 ts2 ts3,
    ts1 <ts: ts2 ->
    ts2 <ts: ts3 ->
    ts1 <ts: ts3.
Proof.
  induction ts1 as [ | x ts1]; destruct ts2 as [ | y ts2] => //; destruct ts3 as [ | z ts3] => //=; move => Hs1 Hs2; remove_bools_options.
  by erewrite value_subtyping_trans; eauto.
Qed.

Lemma values_subtyping_cat_trans: forall ts1 ts2 ts3 ts4,
    ts1 <ts: ts2 ->
    (ts2 ++ ts3) <ts: ts4 ->
    (ts1 ++ ts3) <ts: ts4.                        
Proof.
  induction ts1 as [ | x ts1]; destruct ts2 as [ | y ts2]; destruct ts4 as [ | z ts4] => //=.
  move => Hsub1 Hsub2; remove_bools_options.
  by erewrite value_subtyping_trans; eauto.
Qed.

Lemma values_subtyping_cat: forall tx1 tx2 ty1 ty2,
  size tx1 = size ty1 ->  
  (tx1 ++ tx2) <ts: (ty1 ++ ty2) = (tx1 <ts: ty1) && (tx2 <ts: ty2).
Proof.
  move => tx1 tx2 ty1 ty2 Hsize.
  unfold values_subtyping.
  by rewrite all2_cat => //.
Qed.

Lemma values_subtyping_split1: forall ts ts1 ts2,
    ts <ts: (ts1 ++ ts2) ->
    ((take (size ts1) ts) <ts: ts1) && ((drop (size ts1) ts) <ts: ts2).
Proof.
  move => ts ts1 ts2; unfold values_subtyping.
  by apply all2_split1.
Qed.

Lemma values_subtyping_split2: forall ts ts1 ts2,
    (ts1 ++ ts2) <ts: ts ->
    (ts1 <ts: (take (size ts1) ts)) && (ts2 <ts: (drop (size ts1) ts)).
Proof.
  move => ts ts1 ts2; unfold values_subtyping.
  by apply all2_split2.
Qed.

Lemma values_subtyping_split: forall ts1 ts2 n,
    n <= size ts1 ->
    (ts1 <ts: ts2) ->
    ((take n ts1) <ts: (take n ts2)) /\
    ((drop n ts1) <ts: (drop n ts2)).
Proof.
  move => ts1 ts2 n Hbound Hsub.
  rewrite - (cat_take_drop n ts1) in Hsub.
  apply values_subtyping_split2 in Hsub; remove_bools_options.
  rewrite size_takel in H => //.
  by rewrite size_takel in H0.
Qed.
  
Lemma func_subtyping_eq: forall tf,
    tf <tf: tf.
Proof.
  move => [ts1 ts2].
  unfold func_subtyping.
  repeat split => //; by apply values_subtyping_eq.
Qed.

Lemma func_subtyping_trans: forall tf1 tf2 tf3,
    tf1 <tf: tf2 ->
    tf2 <tf: tf3 ->
    tf1 <tf: tf3.
Proof.
  move => [tx1 ty1] [tx2 ty2] [tx3 ty3].
  unfold func_subtyping.
  move => [??] [??].
  split; by eapply values_subtyping_trans; eauto.
Qed.

Lemma instr_subtyping_eq: forall tf,
    tf <ti: tf.
Proof.
  move => [ts1 ts2].
  unfold instr_subtyping.
  exists nil, nil, ts1, ts2; repeat split => //; by apply values_subtyping_eq.
Qed.

Lemma instr_subtyping_trans: forall tf1 tf2 tf3,
    tf1 <ti: tf2 ->
    tf2 <ti: tf3 ->
    tf1 <ti: tf3.
Proof.
  move => [tx1 ty1] [tx2 ty2] [tx3 ty3].
  unfold instr_subtyping.
  move => [ts1 [ts1' [tsubx12 [tsuby12 [-> [-> [Hsub1 [Hsubx1 Hsuby1]]]]]]]].
  move => [ts2 [ts2' [tsubx23 [tsuby23 [-> [-> [Hsub2 [Hsubx2 Hsuby2]]]]]]]].
  apply values_subtyping_split1 in Hsubx2.
  apply values_subtyping_split2 in Hsuby2.
  remove_bools_options.
  (* Slightly difficult -- draw it out on paper *)
  exists (ts2 ++ (take (size ts1) tsubx23)), (ts2' ++ (take (size ts1') tsuby23)), (drop (size ts1) tsubx23), (drop (size ts1') tsuby23); repeat rewrite -catA cat_take_drop.
  repeat split => //; try by eapply values_subtyping_trans; eauto.
  rewrite values_subtyping_cat => //; last by apply values_subtyping_size.
  rewrite Hsub2 => /=.
  by (do 2 (eapply values_subtyping_trans; eauto)).
Qed.

(* Trying to resolve subtyping goals in a non-breaking way. A different tactic is provided below that performs more destructive unfolds on instr and func subtyping relations. *)
Ltac resolve_subtyping :=
  repeat match goal with
  | H: is_true ?b |-
      context [ ?b ] =>
      rewrite H => /=
                    
  | |- context [ ?t <t: ?t ] =>
      rewrite value_subtyping_eq => //
                                     
  | |- context [ ?ts <ts: ?ts ] =>
    rewrite values_subtyping_eq => //
  | _: is_true (?ts1 <ts: ?ts1') |-
      context [(?ts1 ++ ?ts2) <ts: (?ts1' ++ ?ts2')] =>
      erewrite values_subtyping_cat; eauto; last by apply values_subtyping_size
  | _: is_true (?ts1 <ts: ?ts2),
    _: is_true ((?ts2 ++ ?ts3) <ts: ?ts4) |-
       context [ (?ts1 ++ ?ts3) <ts: ?ts4 ] =>
      erewrite values_subtyping_cat_trans; try by eauto
                                                    
  | |- context [ ?tf <tf: ?tf ] =>
      rewrite func_subtyping_eq => //
                                    
  | |- context [ ?tf <ti: ?tf ] =>
    try by apply instr_subtyping_eq => //
                                     
  | |- (Tf nil nil) <ti: (Tf ?ts0 ?ts0) =>
    exists ts0, ts0, nil, nil; repeat split; repeat rewrite cats0 => //
  | |- (Tf nil ?ts) <ti: (Tf ?ts0 (?ts0 ++ ?ts)) =>
    exists ts0, ts0, nil, ts; repeat split; repeat rewrite cats0 => //
  | |- (Tf ?ts nil) <ti: (Tf (?ts0 ++ ?ts) ?ts0) =>
    exists ts0, ts0, ts, nil; repeat split; repeat rewrite cats0 => //
  | |- (Tf ?ts1 ?ts2) <ti: (Tf (?ts0 ++ ?ts1) (?ts0 ++ ?ts2)) =>
    exists ts0, ts0, ts1, ts2; repeat split; repeat rewrite cats0 => //

  (* transitivities, up to a chain of length 3 *)
  | H1: is_true (?a <t: ?b),
    H2: is_true (?b <t: ?c) |-
      context [ ?a <t: ?c ] =>
      rewrite (value_subtyping_trans H1 H2) => /=
  | H1: is_true (?a <t: ?b),
    H2: is_true (?b <t: ?c),
    H3: is_true (?c <t: ?d) |-
      context [ ?a <t: ?d ] =>
      rewrite (value_subtyping_trans (values_subtyping_trans H1 H2) H3) => /=
                                                                             
  | H1: is_true (?a <ts: ?b),
    H2: is_true (?b <ts: ?c) |-
      context [ ?a <ts: ?c ] =>
      rewrite (values_subtyping_trans H1 H2) => /=
  | H1: is_true (?a <ts: ?b),
    H2: is_true (?b <ts: ?c),
    H3: is_true (?c <ts: ?d) |-
      context [ ?a <ts: ?d ] =>
      rewrite (values_subtyping_trans (values_subtyping_trans H1 H2) H3) => /=
                                                                             
  | H1: (?a <ti: ?b),
    H2: (?b <ti: ?c) |-
      context [ ?a <ti: ?c ] =>
      apply (instr_subtyping_trans H1 H2) => /=
  | H1: (?a <ti: ?b),
    H2: (?b <ti: ?c),
    H3: (?c <ti: ?d) |-
      context [ ?a <ti: ?d ] =>
      apply (instr_subtyping_trans (instr_subtyping_trans H1 H2) H3) => /=

  (* subtyping of empty *)
  | H: is_true (?ts <ts: nil) |- _ =>
      destruct ts => //; clear H
  | H: is_true (nil <ts: ?ts) |- _ =>
      destruct ts => //; clear H
  end.

Ltac extract_premise :=
  repeat match goal with
  | H: ?x = ?x -> _ |- _ =>
    specialize (H erefl)
  | H: forall x, ?x0 = x -> _ |- _ =>
    try specialize (H _ erefl)
  | H: forall x, [::?x0] = [::x] -> _ |- _ =>
    try specialize (H _ erefl)
  | H: forall x, [:: ?c ?x0] = [:: ?c x] -> _ |- _ =>
    try specialize (H _ erefl)
  | H: forall x y, [:: ?c ?x0 ?y0] = [:: ?c y x] -> _ |- _ =>
    try specialize (H _ _ erefl)
  | H: forall x y, [:: ?c ?x0 ?y0] = [:: ?c x y] -> _ |- _ =>
    try specialize (H _ _ erefl)
  | H: forall t ts, ?ts0 ++ [::?t0] = ts ++ [::t] -> _ |- _ =>
    try specialize (H _ _ erefl)
  | H: forall x y z, [:: ?c ?x0 ?y0 ?z0] = [:: ?c z y x] -> _ |- _ =>
    try specialize (H _ _ _ erefl)
  | H: forall x y, (Tf ?x0 ?y0) = (Tf y x) -> _ |- _ =>
    try specialize (H _ _ erefl)
  | H: forall x y, (Tf ?x0 ?y0) = (Tf x y) -> _ |- _ =>
    try specialize (H _ _ erefl)
  | H: exists t, ?P |- _ =>
    let extr := fresh "extr" in
    let Hextr := fresh "Hextr" in  
    destruct H as [extr Hextr]
  | H: ?P /\ ?Q |- _ =>
    let Hconjl := fresh "Hconjl" in  
    let Hconjr := fresh "Hconjr" in  
    destruct H as [Hconjl Hconjr]
  | _ => (repeat rewrite -> cats0 in * ); (repeat rewrite -> cat0s in * ); resolve_subtyping; subst
    end.

Lemma instr_subtyping_strengthen1: forall tx1 ty1 tx2 ty2 ts,
    ((Tf tx1 ty1) <ti: (Tf tx2 ty2)) ->
    (tx1 <ts: ts) ->
    ((Tf ts ty1) <ti: (Tf tx2 ty2)).
Proof.
  intros.
  unfold instr_subtyping in *; extract_premise.
  exists extr, extr0, extr1, extr2.
  by resolve_subtyping.
Qed.

Lemma instr_subtyping_strengthen2: forall tx1 ty1 tx2 ty2 ts,
    ((Tf tx1 ty1) <ti: (Tf tx2 ty2)) ->
    (ty2 <ts: ts) ->
    ((Tf tx1 ty1) <ti: (Tf tx2 ts)).
Proof.
  intros ?????? Hsub.
  unfold instr_subtyping in *; extract_premise.
  apply values_subtyping_split2 in Hsub; remove_bools_options.
  exists extr, (take (size extr0) ts), extr1, (drop (size extr0) ts); rewrite cat_take_drop.
  by resolve_subtyping.
Qed.

Lemma instr_subtyping_weaken1: forall tx1 ty1 tx2 ty2 ts,
    ((Tf tx1 ty1) <ti: (Tf tx2 ty2)) ->
    (ts <ts: ty1) ->
    ((Tf tx1 ts) <ti: (Tf tx2 ty2)).
Proof.
  intros.
  unfold instr_subtyping in *; extract_premise.
  exists extr, extr0, extr1, extr2.
  by resolve_subtyping.
Qed.

Lemma instr_subtyping_weaken2: forall tx1 ty1 tx2 ty2 ts,
    ((Tf tx1 ty1) <ti: (Tf tx2 ty2)) ->
    (ts <ts: tx2) ->
    ((Tf tx1 ty1) <ti: (Tf ts ty2)).
Proof.
  intros ?????? Hsub.
  unfold instr_subtyping in *; extract_premise.
  apply values_subtyping_split1 in Hsub; remove_bools_options.
  exists (take (size extr) ts), extr0, (drop (size extr) ts), extr2; rewrite cat_take_drop.
  by resolve_subtyping.
Qed.

Lemma num_subtyping: forall tn t,
    (T_num tn <t: t) ->
    t = T_num tn.
Proof.
  by intros; unfold value_subtyping in *; remove_bools_options.
Qed.

Lemma vec_subtyping: forall tn t,
    (T_vec tn <t: t) ->
    t = T_vec tn.
Proof.
  by intros; unfold value_subtyping in *; remove_bools_options.
Qed.

Lemma ref_subtyping: forall tn t,
    (T_ref tn <t: t) ->
    t = T_ref tn.
Proof.
  by intros; unfold value_subtyping in *; remove_bools_options.
Qed.

(* Only use this tactic if desperate *)
Ltac simplify_subtyping :=
  repeat match goal with
  | H: is_true true |- _ => clear H
  | H: ?x = ?x |- _ => clear H
                              
  | H: is_true (T_num ?t <t: ?t') |- _ =>
    apply num_subtyping in H => //
  | H: is_true (T_vec ?t <t: ?t') |- _ =>
    apply vec_subtyping in H => //
  | H: is_true (T_ref ?t <t: ?t') |- _ =>
    apply ref_subtyping in H => //

  | H: T_num ?t1 = T_num ?t2 |- _ =>
    inversion H; subst; clear H
                                
  | H: T_vec ?t1 = T_vec ?t2 |- _ =>
    inversion H; subst; clear H
                                
  | H: T_ref ?t1 = T_ref ?t2 |- _ =>
    inversion H; subst; clear H
      
  (* Structural splits of values_typing *)
  | H: is_true (?ts <ts: (?ts1 ++ ?ts2)) |- _ =>
    let Hsubs1 := fresh "Hsubs1" in
    let Hsubs2 := fresh "Hsubs2" in
    apply values_subtyping_split1 in H; move/andP in H; destruct H as [Hsubs1 Hsubs2] => //
  | H: is_true ((?ts1 ++ ?ts2) <ts: ?ts) |- _ =>
    let Hsubs1 := fresh "Hsubs1" in
    let Hsubs2 := fresh "Hsubs2" in
    apply values_subtyping_split2 in H; move/andP in H; destruct H as [Hsubs1 Hsubs2] => //
  | _ => (* real desperation mode *)
        unfold instr_subtyping, func_subtyping in *; resolve_subtyping => //; remove_bools_options => //; extract_premise; subst => //; extract_listn; subst => //; simpl in *; remove_bools_options; subst => //
  end.

(* Auxiliary lemmas for composing types only knowing a principal type. In 1.0 the subtypings are simple concatenations, which made things a lot easier. *)
Lemma instr_subtyping_compose_le: forall tx0 ty0 ty0' tz0 tx ty tz,
    ((Tf tx0 ty0) <ti: (Tf tx ty)) ->
    ((Tf ty0' tz0) <ti: (Tf ty tz)) ->
    size ty0 <= size ty0' ->
    ((Tf ((take (size ty0' - size ty0) ty0') ++ tx0) tz0) <ti: (Tf tx tz)) /\ (ty0 <ts: drop (size ty0' - size ty0) ty0').
Proof.
  intros ??????? Hsubi1 Hsubi2 Hsize.
  simplify_subtyping.
  specialize (values_subtyping_size Hconjl2) as Hsize'.
  apply values_subtyping_split with (n := size ty0' - size ty0) in Hconjl2 as [Hsubs1 Hsubs2]; last by lias.
  rewrite - (cat_take_drop (size ty0' - size ty0) extr1) catA in Hconjl.
  specialize (values_subtyping_size Hconjr1) as Hsize''.
  apply concat_cancel_last_n in Hconjl => //; remove_bools_options; subst; last by rewrite size_drop; lias.
  simplify_subtyping; split => //.
  exists (take (size extr) extr3), extr0, (drop (size extr) extr3 ++ extr5), extr2.
  repeat split; resolve_subtyping => //.
  - by rewrite catA cat_take_drop.
  - rewrite values_subtyping_cat; first by resolve_subtyping.
    apply values_subtyping_size in Hsubs3.
    rewrite Hsubs3.
    repeat rewrite size_takel; by lias.
Qed.

Lemma instr_subtyping_compose_ge: forall tx0 ty0 ty0' tz0 tx ty tz,
    ((Tf tx0 ty0) <ti: (Tf tx ty)) ->
    ((Tf ty0' tz0) <ti: (Tf ty tz)) ->
    size ty0' <= size ty0 ->
    ((Tf tx0 ((take (size ty0 - size ty0') ty0) ++ tz0)) <ti: (Tf tx tz)) /\ (drop (size ty0 - size ty0') ty0 <ts: ty0').
Proof.
  intros ??????? Hsubi1 Hsubi2 Hsize.
  simplify_subtyping.
  specialize (values_subtyping_size Hconjr1) as Hsize'.
  apply values_subtyping_split with (n := size ty0 - size ty0') in Hconjr1 as [Hsubs1 Hsubs2]; last by lias.
  rewrite - (cat_take_drop (size ty0 - size ty0') extr6) catA in Hconjl.
  specialize (values_subtyping_size Hconjl2) as Hsize''.
  apply concat_cancel_last_n in Hconjl => //; remove_bools_options; subst; last by rewrite size_drop; lias.
  simplify_subtyping; split => //.
  exists extr3, (take (size extr4) extr0), extr5, (drop (size extr4) extr0 ++ extr2).
  repeat split; resolve_subtyping => //.
  - by rewrite catA cat_take_drop.
  - rewrite values_subtyping_cat; first by resolve_subtyping.
    apply values_subtyping_size in Hsubs3.
    rewrite - Hsubs3.
    repeat rewrite size_takel; by lias.
Qed.

(* A few special cases *)
Lemma instr_subtyping_compose_eq: forall tx0 ty0 ty0' tz0 tx ty tz,
    ((Tf tx0 ty0) <ti: (Tf tx ty)) ->
    ((Tf ty0' tz0) <ti: (Tf ty tz)) ->
    size ty0 = size ty0' ->
    ((Tf tx0 tz0) <ti: (Tf tx tz)) /\ (ty0 <ts: ty0').
Proof.
  intros ??????? Hsubi1 Hsubi2 Hsize.
  specialize (instr_subtyping_compose_le Hsubi1 Hsubi2) as Hsub.
  rewrite Hsize subnn take0 drop0 in Hsub.
  apply Hsub; by lias.
Qed.

Lemma instr_subtyping_compose_nil1: forall tx0 ty0 tz0 tx ty tz,
    ((Tf tx0 nil) <ti: (Tf tx ty)) ->
    ((Tf ty0 tz0) <ti: (Tf ty tz)) ->
    (Tf (ty0 ++ tx0) tz0) <ti: (Tf tx tz).
Proof.
  intros ?????? Hsubi1 Hsubi2.
  specialize (instr_subtyping_compose_le Hsubi1 Hsubi2) as Hsub.
  destruct Hsub as [Hsub _] => //.
  uapply Hsub; do 2 f_equal => /=.
  by rewrite subn0 take_size.
Qed.

Lemma instr_subtyping_compose_nil2: forall tx0 ty0 tz0 tx ty tz,
    ((Tf tx0 ty0) <ti: (Tf tx ty)) ->
    ((Tf nil tz0) <ti: (Tf ty tz)) ->
    (Tf tx0 (ty0 ++ tz0)) <ti: (Tf tx tz).
Proof.
  intros ?????? Hsubi1 Hsubi2.
  specialize (instr_subtyping_compose_ge Hsubi1 Hsubi2) as Hsub.
  destruct Hsub as [Hsub _] => //.
  uapply Hsub; do 2 f_equal => /=.
  by rewrite subn0 take_size.
Qed.

Ltac unify_principal :=
  repeat match goal with
  | H1: (Tf ?ts1 ?ts2) <ti: (Tf ?tx ?ty),
    H2: (Tf ?ts3 ?ts4) <ti: (Tf ?ty ?tz) |- _ =>
    let Hprincipal := fresh "Hprincipal" in  
    let Hsubs := fresh "Hsubs" in
    (* syntactic sugar for matching 2 variables doesn't work in Ltac *)
    match ts2 with
    | nil => specialize (instr_subtyping_compose_nil1 H1 H2) as Hprincipal; clear H1 H2
    | [::_] =>
        match ts3 with
        | nil => specialize (instr_subtyping_compose_nil2 H1 H2) as Hprincipal
        | [::_] => specialize (instr_subtyping_compose_eq H1 H2) as [Hprincipal Hsubs] => //
        | _ => specialize (instr_subtyping_compose_le H1 H2) as [Hprincipal Hsubs] => //
        end; clear H1 H2
    | [::_; _] =>
        match ts3 with
        | nil => specialize (instr_subtyping_compose_nil2 H1 H2) as Hprincipal
        | [::_] => specialize (instr_subtyping_compose_ge H1 H2) as [Hprincipal Hsubs] => //
        | [::_; _] => specialize (instr_subtyping_compose_eq H1 H2) as [Hprincipal Hsubs] => //
        | _ => specialize (instr_subtyping_compose_le H1 H2) as [Hprincipal Hsubs] => //
        end; clear H1 H2
    | [::_; _; _] =>
        match ts3 with
        | nil => specialize (instr_subtyping_compose_nil2 H1 H2) as Hprincipal
        | [::_; _] => specialize (instr_subtyping_compose_ge H1 H2) as [Hprincipal Hsubs] => //
        | [::_; _] => specialize (instr_subtyping_compose_ge H1 H2) as [Hprincipal Hsubs] => //
        | [::_; _; _] => specialize (instr_subtyping_compose_eq H1 H2) as [Hprincipal Hsubs] => //
        | _ => specialize (instr_subtyping_compose_le H1 H2) as [Hprincipal Hsubs] => //
        end; clear H1 H2
    | _ => idtac "unification is too complicated"
    end; try (move: Hprincipal; rewrite (lock instr_subtyping) /= -lock; move => Hprincipal)
  | |- is_true (size _ <= size _) =>
    try by repeat rewrite size_cat; lias
  end.
(* Some quality of life lemmas *)
(* Upd: these lemmas are deprecated; it is encouraged to directly use subtyping rule. *)
Lemma bet_weakening_empty_1: forall C es ts t2s,
    be_typing C es (Tf [::] t2s) ->
    be_typing C es (Tf ts (ts ++ t2s)).
Proof.
  move => C es ts t2s HType.
  eapply bet_subtyping; eauto.
  by resolve_subtyping.
Qed.

Lemma bet_weakening_empty_2: forall C es ts t1s,
    be_typing C es (Tf t1s [::]) ->
    be_typing C es (Tf (ts ++ t1s) ts).
Proof.
  move => C es ts t1s HType.
  eapply bet_subtyping; eauto.
  by resolve_subtyping.
Qed.

Lemma bet_weakening_empty_both: forall C es ts,
    be_typing C es (Tf [::] [::]) ->
    be_typing C es (Tf ts ts).
Proof.
  move => C es ts HType.
  eapply bet_subtyping; eauto.
  by resolve_subtyping.
Qed.

(** * More Advanced Lemmas **)

Section Host.

Context `{hfc: host_function_class}.

Lemma values_typing_length: forall s vs ts,
    values_typing s vs = Some ts ->
    length vs = length ts.
Proof.
  move => s vs ts Hvts.
  apply those_length in Hvts.
  by rewrite length_is_size size_map -length_is_size in Hvts.
Qed.

Lemma values_typing_cons_impl: forall s v t vs ts,
    values_typing s (v :: vs) = Some (t :: ts) ->
    value_typing s v = Some t /\
    values_typing s vs = Some ts.
Proof.
  move => s v t vs ts Hvaltype.
  by apply those_cons_impl in Hvaltype as [??].
Qed.

Lemma values_typing_cat: forall s vs1 vs2 ts1 ts2,
    values_typing s vs1 = Some ts1 ->
    values_typing s vs2 = Some ts2 ->
    values_typing s (vs1 ++ vs2) = Some (ts1 ++ ts2).
Proof.
  move => s vs1 vs2 ts1 ts2.
  unfold values_typing.
  intros.
  by rewrite map_cat; erewrite those_cat.
Qed.

Lemma default_value_typing: forall s t v,
    default_val t = Some v ->
    value_typing s v = Some t.
Proof.
  move => s t v Hval.
  destruct t, v => //; simpl in *; try inversion Hval; subst => //=.
  - by destruct n.
  - by destruct v0.
Qed.

Lemma default_values_typing: forall s ts vs,
    default_vals ts = Some vs ->
    values_typing s vs = Some ts.
Proof.
  unfold default_vals, values_typing.
  setoid_rewrite <- those_those0.
  move => s; elim => /=; first by case.
  move => t ts IH vs Hdefaults; destruct vs => //; remove_bools_options => /=.
  erewrite default_value_typing; eauto.
  by erewrite IH; eauto.
Qed.

(* Avoid changing everything to type or making other large-scale changes *)
Lemma vcs_exist_constructive: forall vs P,
  (exists vcs, vs = v_to_e_list vcs /\ P vcs) ->
  { vcs | vs = v_to_e_list vcs /\ P vcs }.
Proof.
  move => vs P Hexist.
  assert (const_list vs) as Hconst; first by destruct Hexist as [? [-> ?]]; apply v_to_e_const.
  apply const_es_exists in Hconst as [vcs Heq].
  assert (P vcs) as HP; first by (destruct Hexist as [? [-> HP]]; subst; apply v_to_e_inj in Heq; subst).
  by exists vcs.
Qed.

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

Lemma et_weakening_empty_1: forall s C es ts t2s,
    e_typing s C es (Tf [::] t2s) ->
    e_typing s C es (Tf ts (ts ++ t2s)).
Proof.
  move => s C es ts t2s HType.
  eapply ety_subtyping; eauto.
  by resolve_subtyping.
Qed.

Lemma et_weakening_empty_2: forall s C es ts t2s,
    e_typing s C es (Tf t2s nil) ->
    e_typing s C es (Tf (ts ++ t2s) ts).
Proof.
  move => s C es ts t2s HType.
  eapply ety_subtyping; eauto.
  by resolve_subtyping.
Qed.

(* A convenient lemma to invert e_typing back to be_typing. *)
Lemma et_to_bet: forall s C es tf,
    es_is_basic es ->
    e_typing s C es tf ->
    be_typing C (to_b_list es) tf.
Proof.
  move => s C es tf HBasic HType.
  dependent induction HType; basic_inversion => //.
  + replace (to_b_list (to_e_list bes)) with bes => //.
    by apply b_e_elim.
  + rewrite to_b_list_concat.
    apply basic_concat in HBasic.
    move/andP in HBasic.
    destruct HBasic as [Hbes Hbe].
    eapply bet_composition.
    * by eapply IHHType1 => //.
    * by eapply IHHType2 => //.
  + apply IHHType in HBasic.
    by eapply bet_subtyping; eauto.
Qed.

(************ these come from the certified itp *************)
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
  - move/leP in H. apply Nat.lt_eq_cases in H as [H|] => //.
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

(************ certified itp properties *************)
Lemma cat_cons_not_nil : forall T (xs : list T) y ys,
  xs ++ (y :: ys) <> [::].
Proof. move => T xs y ys E. by move: (List.app_eq_nil _ _ E) => [? ?]. Qed.

Lemma not_reduce_simple_nil : forall es', ~ reduce_simple [::] es'.
Proof.
  move => ? Hcontra.
  inversion Hcontra; subst.
  destruct lh as [vs | ? vs] => //; by destruct vs => //.
Qed.

(* further list operations *)
Lemma nth_error_map: forall {X Y:Type} l n (f: X -> Y) fv,
    List.nth_error (map f l) n = Some fv ->
    exists v,
      List.nth_error l n = Some v /\
      f v = fv.
Proof.
  move => X Y l n.
  move: l.
  induction n => //=; move => l f fv HNth; destruct l => //=.
  - destruct (map f (x::l)) eqn:HMap => //=.
    inversion HNth; subst.
    simpl in HMap. inversion HMap. subst.
    by eexists.
  - destruct (map f (x::l)) eqn:HMap => //=.
    simpl in HMap. inversion HMap. subst.
    by apply IHn.
Qed.

Lemma nth_error_nth: forall {X: Type} l n {x:X},
  n < length l ->
  List.nth_error l n = Some (nth x l n).
Proof.
  induction l; destruct n => //=.
  by apply IHl.
Qed.

Lemma nth_error_nth': forall {T: Type} (l: list T) n (x x0:T),
  List.nth_error l n = Some x -> nth x0 l n = x.
Proof.
  induction l => //=; destruct n => //=; intros; first by inversion H.
  by apply IHl.
Qed.

Lemma set_nth_length: forall {X: Type} l n {x xd: X},
    n < length l ->
    length (set_nth xd l n x) = length l.
Proof.
  move => X l n x xd Hnth.
  repeat rewrite length_is_size.
  rewrite size_set_nth -length_is_size.
  unfold maxn.
  destruct (n.+1 < _) eqn:Hlt => //.
  by lias.
Qed.

Lemma nth_error_set_nth_length: forall {X: Type} l n {x0 x xd: X},
  List.nth_error l n = Some x0 ->
  length (set_nth xd l n x) = length l.
Proof.
  move => X l n x0 x xd Hnth.
  apply nth_error_Some_length in Hnth.
  by eapply set_nth_length; lias.
Qed.

Lemma nth_error_set_eq: forall {X:Type} l n {x xd:X},
    List.nth_error (set_nth xd l n x) n = Some x.
Proof.
  move => X l n x xd.
  rewrite set_nthE.
  destruct (n < size l) eqn:Hsize.
  - replace (n.+1) with (n+1)%coq_nat; last by lias.
    apply memory_list.lookup_split; by lias.
  - rewrite List.nth_error_app2; last by rewrite length_is_size; lias.
    rewrite - cat_nseq.
    rewrite List.nth_error_app2; last by repeat rewrite length_is_size; rewrite size_nseq.
    repeat rewrite length_is_size; rewrite size_nseq.
    by replace (_ - _) with 0; last by lias.
Qed.

Lemma nth_error_set_neq: forall {X:Type} l n m {x xd:X},
    n <> m ->
    n < length l ->
    List.nth_error (set_nth xd l n x) m = List.nth_error l m.
Proof.
  move => X l n. move: l.
  induction n => //=; move => l m x Hne HLength.
  - destruct m => //=.
    by destruct l => //=.
  - destruct m => //=.
    + by destruct l => //=.
    + destruct l => //=.
      simpl in HLength.
      by apply IHn; lias.
Qed.

Lemma set_nth_In: forall {X: Type} y l n {x xd: X},
    n < length l ->
    List.In y (set_nth xd l n x) ->
    y = x \/ (exists m, n <> m /\ List.nth_error l m = Some y).
Proof.
  move => X y l n x xd Hlen Hin.
  apply List.In_nth_error in Hin as [m Hnth].
  destruct (n == m) eqn:Heq; move/eqP in Heq; subst.
  - by left; rewrite nth_error_set_eq in Hnth; injection Hnth.
  - right; exists m; split => //.
    by erewrite <- nth_error_set_neq; eauto => //.
Qed.

Lemma Forall_set: forall {X:Type} f l n {x xd:X},
    List.Forall f l ->
    f x ->
    n < length l ->
    List.Forall f (set_nth xd l n x).
Proof.
  move => X f l. induction l; destruct n; move => x xd Hall Hf Hlen => //; constructor => //=; try by inversion Hall.
  apply IHl => //.
  by inversion Hall.
Qed.

(** Store extension properties **)

Lemma reflexive_all2_same: forall {X:Type} f (l: seq X),
    reflexive f ->
    all2 f l l.
Proof.
  move => X f l.
  induction l; move => H; unfold reflexive in H => //=.
  apply/andP. split => //=.
  by apply IHl.
Qed.

Lemma func_extension_refl:
    reflexive func_extension.
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

Lemma table_extension_refl:
    reflexive table_extension.
Proof.
  move => t. unfold table_extension, limits_extension.
  do 3 (apply/andP; split => //).
  apply/N.leb_spec0; by lias.
Qed.

Lemma all2_table_extension_same: forall t,
    all2 table_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive.
  by apply table_extension_refl.
Qed.

Lemma mem_extension_refl:
    reflexive mem_extension.
Proof.
  move => m. unfold table_extension, limits_extension.
  do 2 (apply/andP; split => //).
  apply/N.leb_spec0; by lias.
Qed.

Lemma all2_mem_extension_same: forall t,
    all2 mem_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive.
  by apply mem_extension_refl.
Qed.

Lemma global_extension_refl:
    reflexive global_extension.
Proof.
  move => [[??]?] => /=.
  unfold global_extension => /=.
  (apply/andP; split => //).
  apply/orP.
  by right.
Qed.

Lemma all2_global_extension_same: forall t,
    all2 global_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive.
  by apply global_extension_refl.
Qed.

Lemma elem_extension_refl:
    reflexive elem_extension.
Proof.
  move => ? => /=.
  unfold elem_extension => /=.
  by repeat rewrite eq_refl.
Qed.

Lemma all2_elem_extension_same: forall t,
    all2 elem_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive.
  by apply elem_extension_refl.
Qed.

Lemma data_extension_refl:
    reflexive data_extension.
Proof.
  move => ? => /=.
  unfold data_extension => /=.
  by rewrite eq_refl.
Qed.

Lemma all2_data_extension_same: forall t,
    all2 data_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive.
  by apply data_extension_refl.
Qed.

Lemma component_extension_same_refl {T: Type} (l: list T) f:
    reflexive f ->
    component_extension f l l.
Proof.
  move => Hrefl.
  unfold component_extension.
  apply/andP; split; first by lias.
  rewrite take_size.
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
  
Lemma table_extension_trans:
  transitive table_extension.
Proof.
  move => x1 x2 x3 Hext1 Hext2.
  destruct x1, x2, x3.
  unfold table_extension, table_type_extension, limits_extension in *; simpl in *.
  remove_bools_options; simpl in *; subst.
  do 3 (try (apply/andP; split)); try by lias.
  - rewrite - H; by lias.
  - rewrite - H2; by lias.
Qed.
    
Lemma mem_extension_trans:
  transitive mem_extension.
Proof.
  move => x1 x2 x3 Hext1 Hext2.
  destruct x1, x2, x3.
  unfold mem_extension, limits_extension in *; simpl in *.
  remove_bools_options; simpl in *; subst.
  do 2 (try (apply/andP; split)); try by lias.
  rewrite - H1; by lias.
Qed.
    
Lemma global_extension_trans:
  transitive global_extension.
Proof.
  move => [[??]?] [[??]?] [[??]?] Hext1 Hext2.
  unfold global_extension in *; simpl in *.
  remove_bools_options; subst; inversion H; inversion H1; subst; apply/andP; split => //.
  apply/orP; by right.
Qed.

Lemma elem_extension_trans:
  transitive elem_extension.
Proof.
  move => x1 x2 x3 Hext1 Hext2.
  destruct x1, x2, x3.
  unfold elem_extension in *; simpl in *.
  remove_bools_options; subst => //; try repeat rewrite eq_refl; by lias.
Qed.
    
Lemma data_extension_trans:
  transitive data_extension.
Proof.
  move => x1 x2 x3 Hext1 Hext2.
  destruct x1, x2, x3.
  unfold data_extension in *; simpl in *.
  remove_bools_options; subst => //; try by apply/orP; right.
  by rewrite eq_refl.
Qed.
    
Lemma nth_error_take_longer {T: Type} (l: list T) n k:
  n < k ->
  List.nth_error l n = List.nth_error (take k l) n.
Proof.
  move: k l.
  induction n; move => k l Hlt; destruct l, k => //=.
  apply IHn; by lias.
Qed.

Lemma component_extension_update {T: Type} (l: list T) n x y y0 f:
  reflexive f ->
  List.nth_error l n = Some x ->
  f x y ->
  component_extension f l (set_nth y0 l n y).
Proof.
  move => Hrefl Hnth Hf.
  assert (length l = length (set_nth y0 l n y)) as Hlen; first by erewrite <- nth_error_set_nth_length; eauto.
  
  unfold component_extension; apply/andP; split; first by lias.
  rewrite Hlen length_is_size take_size.
  apply all2_spec => //.
  move => i x' y' Hnth' Hnth2.
  destruct (i == n) eqn:Heqn.
  - move/eqP in Heqn; subst.
    rewrite Hnth' in Hnth.
    injection Hnth as ->.
    rewrite nth_error_set_eq in Hnth2.
    by injection Hnth2 as <-.
  - move/eqP in Heqn.
    rewrite nth_error_set_neq in Hnth2; eauto; last by apply nth_error_Some_length in Hnth; lias.
    rewrite Hnth' in Hnth2; injection Hnth2 as <-.
    by apply Hrefl.
Qed.

Lemma component_extension_trans {T: Type} (l1 l2 l3: list T) f:
  component_extension f l1 l2 ->
  component_extension f l2 l3 ->
  transitive f ->
  component_extension f l1 l3.
Proof.
  move => Hext1 Hext2 Htrans.
  unfold component_extension in *.
  remove_bools_options.
  apply/andP; split; first by lias.
  apply all2_spec.
  - rewrite size_take.
    repeat rewrite length_is_size in H H0 H1 H2.
    rewrite length_is_size.
    assert (size l1 <= size l3); first lias.
    destruct (size l1 < size l3) eqn: Hlt => //; last by lias.
  - move => n x y Hnth1 Hnth2.
    specialize (all2_nth_impl H2 Hnth1) as [z [Hnth3 Hf]].
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
  apply/andP; split; last by eapply component_extension_trans; eauto; apply data_extension_trans.
  apply/andP; split; last by eapply component_extension_trans; eauto; apply elem_extension_trans.
  apply/andP; split; last by eapply component_extension_trans; eauto; apply global_extension_trans.
  apply/andP; split; last by eapply component_extension_trans; eauto; apply mem_extension_trans.
  apply/andP; split; last by eapply component_extension_trans; eauto; apply table_extension_trans.
  by eapply component_extension_trans; eauto; apply func_extension_trans.
Qed.
  
Lemma store_extension_same: forall s,
    store_extension s s.
Proof.
  move => s. unfold store_extension.
  repeat (apply/andP; split => //); rewrite length_is_size take_size.
  + by apply all2_func_extension_same.
  + by apply all2_table_extension_same.
  + by apply all2_mem_extension_same.
  + by apply all2_global_extension_same.
  + by apply all2_elem_extension_same.
  + by apply all2_data_extension_same.
Qed.

Lemma component_extension_lookup {T: Type} (l1 l2: list T) f n x:
  component_extension f l1 l2 ->
  lookup_N l1 n = Some x ->
  exists y, (lookup_N l2 n = Some y /\ f x y).
Proof.
  move => Hext Hnth.
  unfold component_extension in Hext.
  remove_bools_options.
  unfold lookup_N in *.
  assert (lt (N.to_nat n) (length l1)) as Hlen; first by apply List.nth_error_Some; rewrite Hnth.
  destruct (List.nth_error l2 (N.to_nat n)) as [y |] eqn:Hnth'; last by apply List.nth_error_None in Hnth'; lias.
  apply (nth_error_take (k := length l1)) in Hnth'; last by lias.
  specialize (all2_projection H0 Hnth Hnth') as Hproj.
  by exists y.
Qed.

Lemma store_extension_lookup_func: forall s s' n cl,
    store_extension s s' ->
    lookup_N (s_funcs s) n = Some cl ->
    lookup_N (s_funcs s') n = Some cl.
Proof.
  move => s s' n cl Hext Hnth.
  unfold store_extension, operations.store_extension in Hext.
  remove_bools_options.
  eapply component_extension_lookup in Hnth; eauto.
  unfold operations.func_extension in Hnth.
  destruct Hnth as [? [Hnth Heq]].
  by move/eqP in Heq; subst.
Qed.

Lemma store_extension_lookup_table: forall s s' n x,
    store_extension s s' ->
    lookup_N (s_tables s) n = Some x ->
    exists x', lookup_N (s_tables s') n = Some x' /\ table_extension x x'.
Proof.
  move => s s' n cl Hext Hnth.
  unfold store_extension, operations.store_extension in Hext.
  remove_bools_options.
  by eapply component_extension_lookup in Hnth; eauto.
Qed.

Lemma store_extension_lookup_mem: forall s s' n x,
    store_extension s s' ->
    lookup_N (s_mems s) n = Some x ->
    exists x', lookup_N (s_mems s') n = Some x' /\ mem_extension x x'.
Proof.
  move => s s' n cl Hext Hnth.
  unfold store_extension, operations.store_extension in Hext.
  remove_bools_options.
  by eapply component_extension_lookup in Hnth; eauto.
Qed.

Lemma store_extension_lookup_global: forall s s' n x,
    store_extension s s' ->
    lookup_N (s_globals s) n = Some x ->
    exists x', lookup_N (s_globals s') n = Some x' /\ global_extension x x'.
Proof.
  move => s s' n cl Hext Hnth.
  unfold store_extension, operations.store_extension in Hext.
  remove_bools_options.
  by eapply component_extension_lookup in Hnth; eauto.
Qed.

Lemma store_extension_lookup_elem: forall s s' n x,
    store_extension s s' ->
    lookup_N (s_elems s) n = Some x ->
    exists x', lookup_N (s_elems s') n = Some x' /\ elem_extension x x'.
Proof.
  move => s s' n cl Hext Hnth.
  unfold store_extension, operations.store_extension in Hext.
  remove_bools_options.
  by eapply component_extension_lookup in Hnth; eauto.
Qed.

Lemma store_extension_lookup_data: forall s s' n x,
    store_extension s s' ->
    lookup_N (s_datas s) n = Some x ->
    exists x', lookup_N (s_datas s') n = Some x' /\ data_extension x x'.
Proof.
  move => s s' n cl Hext Hnth.
  unfold store_extension, operations.store_extension in Hext.
  remove_bools_options.
  by eapply component_extension_lookup in Hnth; eauto.
Qed.

(** Lookups connecting module instance, store, and typing context *)
Lemma inst_typing_type_lookup: forall s inst C n,
    inst_typing s inst = Some C ->
    lookup_N inst.(inst_types) n = lookup_N C.(tc_types) n.
Proof.
  move => s inst C n Hit.
  unfold inst_typing in Hit.
  destruct inst; remove_bools_options; simpl in *.
  by eauto.
Qed.

Lemma inst_typing_func_lookup: forall s inst C n x,
    inst_typing s inst = Some C ->
    lookup_N inst.(inst_funcs) n = Some x ->
    exists t, ext_func_typing s x = Some t /\
         lookup_N C.(tc_funcs) n = Some t.
Proof.
  move => s inst C n x Hit Hnth.
  unfold inst_typing in Hit.
  destruct inst; remove_bools_options; simpl in *.
  by eapply those_map_lookup in Hoption; eauto.
Qed.

Lemma inst_typing_table_lookup: forall s inst C n x,
    inst_typing s inst = Some C ->
    lookup_N inst.(inst_tables) n = Some x ->
    exists t, ext_table_typing s x = Some t /\
         lookup_N C.(tc_tables) n = Some t.
Proof.
  move => s inst C n x Hit Hnth.
  unfold inst_typing in Hit.
  destruct inst; remove_bools_options; simpl in *.
  by eapply those_map_lookup in Hoption0; eauto.
Qed.
  
Lemma inst_typing_mem_lookup: forall s inst C n x,
    inst_typing s inst = Some C ->
    lookup_N inst.(inst_mems) n = Some x ->
    exists t, ext_mem_typing s x = Some t /\
         lookup_N C.(tc_mems) n = Some t.
Proof.
  move => s inst C n x Hit Hnth.
  unfold inst_typing in Hit.
  destruct inst; remove_bools_options; simpl in *.
  by eapply those_map_lookup in Hoption1; eauto.
Qed.
  
Lemma inst_typing_global_lookup: forall s inst C n x,
    inst_typing s inst = Some C ->
    lookup_N inst.(inst_globals) n = Some x ->
    exists t, ext_global_typing s x = Some t /\
         lookup_N C.(tc_globals) n = Some t.
Proof.
  move => s inst C n x Hit Hnth.
  unfold inst_typing in Hit.
  destruct inst; remove_bools_options; simpl in *.
  by eapply those_map_lookup in Hoption2; eauto.
Qed.

Lemma inst_typing_elem_lookup: forall s inst C n x,
    inst_typing s inst = Some C ->
    lookup_N inst.(inst_elems) n = Some x ->
    exists t ei, lookup_N (s_elems s) x = Some ei /\
            eleminst_typing s ei = Some t /\
            lookup_N C.(tc_elems) n = Some t.
Proof.
  move => s inst C n x Hit Hnth.
  unfold inst_typing in Hit.
  destruct inst; remove_bools_options; simpl in *.
  eapply those_map_lookup in Hoption3; eauto.
  destruct Hoption3 as [t [Hnthelem Hnthl]].
  remove_bools_options.
  by exists t, e.
Qed.

Lemma inst_typing_data_lookup: forall s inst C n x,
    inst_typing s inst = Some C ->
    lookup_N inst.(inst_datas) n = Some x ->
    exists t di, lookup_N (s_datas s) x = Some di /\
            datainst_typing s di = Some t /\
            lookup_N C.(tc_datas) n = Some t.
Proof.
  move => s inst C n x Hit Hnth.
  unfold inst_typing in Hit.
  destruct inst; remove_bools_options; simpl in *.
  eapply those_map_lookup in Hoption4; eauto.
  destruct Hoption4 as [t [Hnthdata Hnthl]].
  remove_bools_options.
  by exists t, d.
Qed.

Lemma inst_typing_expand_eq: forall s inst C C' tb,
    inst_typing s inst = Some C ->
    tc_types C = tc_types C' ->
    expand inst tb = expand_t C' tb.
Proof.
  move => s inst C C' tb Hit Hteq.
  destruct tb => //=.
  rewrite -Hteq.
  by eapply inst_typing_type_lookup; eauto.
Qed.

Lemma inst_typing_func_lookup_inv: forall s inst C n t,
    inst_typing s inst = Some C ->
    lookup_N C.(tc_funcs) n = Some t ->
    exists x, ext_func_typing s x = Some t /\
         lookup_N inst.(inst_funcs) n = Some x.
Proof.
  move => s inst C n t Hit Hnth.
  unfold inst_typing in Hit.
  destruct inst; remove_bools_options; simpl in *.
  unfold lookup_N in *.
  eapply those_lookup_inv in Hoption; eauto.
  apply nth_error_map in Hoption as [a [??]].
  by exists a.
Qed.

Lemma inst_typing_table_lookup_inv: forall s inst C n t,
    inst_typing s inst = Some C ->
    lookup_N C.(tc_tables) n = Some t ->
    exists x, ext_table_typing s x = Some t /\
         lookup_N inst.(inst_tables) n = Some x.
Proof.
  move => s inst C n t Hit Hnth.
  unfold inst_typing in Hit.
  destruct inst; remove_bools_options; simpl in *.
  unfold lookup_N in *.
  eapply those_lookup_inv in Hoption0; eauto.
  apply nth_error_map in Hoption0 as [a [??]].
  by exists a.
Qed.

Lemma inst_typing_mem_lookup_inv: forall s inst C n t,
    inst_typing s inst = Some C ->
    lookup_N C.(tc_mems) n = Some t ->
    exists x, ext_mem_typing s x = Some t /\
         lookup_N inst.(inst_mems) n = Some x.
Proof.
  move => s inst C n t Hit Hnth.
  unfold inst_typing in Hit.
  destruct inst; remove_bools_options; simpl in *.
  unfold lookup_N in *.
  eapply those_lookup_inv in Hoption1; eauto.
  apply nth_error_map in Hoption1 as [a [??]].
  by exists a.
Qed.

Lemma inst_typing_global_lookup_inv: forall s inst C n t,
    inst_typing s inst = Some C ->
    lookup_N C.(tc_globals) n = Some t ->
    exists x, ext_global_typing s x = Some t /\
         lookup_N inst.(inst_globals) n = Some x.
Proof.
  move => s inst C n t Hit Hnth.
  unfold inst_typing in Hit.
  destruct inst; remove_bools_options; simpl in *.
  unfold lookup_N in *.
  eapply those_lookup_inv in Hoption2; eauto.
  apply nth_error_map in Hoption2 as [a [??]].
  by exists a.
Qed.

Lemma inst_typing_elem_lookup_inv: forall s inst C n t,
    inst_typing s inst = Some C ->
    lookup_N C.(tc_elems) n = Some t ->
    exists a ei, lookup_N inst.(inst_elems) n = Some a /\
           lookup_N s.(s_elems) a = Some ei /\
           eleminst_typing s ei = Some t.
Proof.
  move => s inst C n t Hit Hnth.
  unfold inst_typing in Hit.
  destruct inst; remove_bools_options; simpl in *.
  unfold lookup_N in *.
  eapply those_lookup_inv in Hoption3; eauto.
  apply nth_error_map in Hoption3 as [a [??]].
  remove_bools_options.
  by exists a, e.
Qed.
  
Lemma inst_typing_data_lookup_inv: forall s inst C n t,
    inst_typing s inst = Some C ->
    lookup_N C.(tc_datas) n = Some t ->
    exists a ei, lookup_N inst.(inst_datas) n = Some a /\
           lookup_N s.(s_datas) a = Some ei /\
           datainst_typing s ei = Some t.
Proof.
  move => s inst C n t Hit Hnth.
  unfold inst_typing in Hit.
  destruct inst; remove_bools_options; simpl in *.
  unfold lookup_N in *.
  eapply those_lookup_inv in Hoption4; eauto.
  apply nth_error_map in Hoption4 as [a [??]].
  remove_bools_options.
  by exists a, d.
Qed.
  
Lemma store_typing_func_lookup: forall s n x,
    store_typing s ->
    lookup_N s.(s_funcs) n = Some x ->
    exists t, funcinst_typing s x t.
Proof.
  move => s n x Hst Hnth.
  unfold store_typing in Hst; destruct s.
  destruct Hst as [Hf _]; simpl in *.
  by eapply Forall_lookup in Hf; eauto.
Qed.

Lemma store_typing_table_lookup: forall s n x,
    store_typing s ->
    lookup_N s.(s_tables) n = Some x ->
    exists t, tableinst_typing s x = Some t.
Proof.
  move => s n x Hst Hnth.
  unfold store_typing in Hst; destruct s.
  destruct Hst as [Hf [Ht _]]; simpl in *.
  by eapply Forall_lookup in Ht; eauto.
Qed.

Lemma store_typing_mem_lookup: forall s n x,
    store_typing s ->
    lookup_N s.(s_mems) n = Some x ->
    exists t, meminst_typing s x = Some t.
Proof.
  move => s n x Hst Hnth.
  unfold store_typing in Hst; destruct s.
  destruct Hst as [Hf [Ht [Hm _]]]; simpl in *.
  by eapply Forall_lookup in Hm; eauto.
Qed.

Lemma store_typing_global_lookup: forall s n x,
    store_typing s ->
    lookup_N s.(s_globals) n = Some x ->
    exists t, globalinst_typing s x = Some t.
Proof.
  move => s n x Hst Hnth.
  unfold store_typing in Hst; destruct s.
  destruct Hst as [_ [_ [_ [Hg _]]]]; simpl in *.
  by eapply Forall_lookup in Hg; eauto.
Qed.

Lemma store_typing_elem_lookup: forall s n x,
    store_typing s ->
    lookup_N s.(s_elems) n = Some x ->
    exists t, eleminst_typing s x = Some t.
Proof.
  move => s n x Hst Hnth.
  unfold store_typing in Hst; destruct s.
  destruct Hst as [_ [_ [_ [_ [He _]]]]]; simpl in *.
  by eapply Forall_lookup in He; eauto.
Qed.

Lemma store_typing_data_lookup: forall s n x,
    store_typing s ->
    lookup_N s.(s_datas) n = Some x ->
    exists t, datainst_typing s x = Some t.
Proof.
  move => s n x Hst Hnth.
  unfold store_typing in Hst; destruct s.
  destruct Hst as [_ [_ [_ [_ [_ Hd]]]]]; simpl in *.
  by eapply Forall_lookup in Hd; eauto.
Qed.

End Host.

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
    destruct e as [b | | | | | | ] => //; try destruct b => //;
    exists lvs, les, (Logic.eq_refl 0); by split => //.
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
  - destruct (e_to_v_opt e) as [v | ] eqn:Hconst.
    { destruct e as [ b | | | | | |] => //; first destruct b => //.
      all: apply ve_inv in Hconst; destruct (IHves' fe) as [[vs [es ->]] | Hcontra]; first by (left; exists (v :: vs), es); rewrite - Hconst.
      all: right; move => vs es Heq;
      destruct vs as [| v' vs'] => //; simpl in *; first by inversion Heq.
      all: apply (Hcontra vs' es) => /=; by inversion Heq.
    }
    { right; move => vs es Heq.
      destruct vs as [| v0 vs'] => //; simpl in *; first by inversion Heq; subst.
      inversion Heq; subst.
      by rewrite v2e2v in Hconst.
    }
Qed.

(* lfill decidability *)
Fixpoint ai_gen_measure (e: administrative_instruction) : nat :=
  match e with
  | AI_label _ _ es => 1 + List.list_max (map ai_gen_measure es)
  | _ => 0
  end.

Definition ais_gen_measure es: nat :=
  1 + List.list_max (map ai_gen_measure es).

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
    destruct e as [ | | | | | j lvs les |].
    6: {
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


Section Host.

Context `{ho: host}.

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
  all: try by destruct vs.
  all: try by destruct ves.
  { intros. apply: lfilled_not_nil. exact H1. exact H0. }
Qed.

End Host.
