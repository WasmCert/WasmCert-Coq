(** Miscellaneous properties about Wasm operations **)

From Wasm Require Export datatypes_properties operations typing opsem common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Bool Program NArith ZArith Wf_nat.

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

(*
Ltac fold_upd_context :=
  lazymatch goal with
  | |- context [upd_local (upd_return ?C ?ret) ?loc] =>
    replace (upd_local (upd_return C ret) loc) with
        (upd_local_return C ret loc); try by destruct C
  | |- context [upd_return (upd_local ?C ?ret) ?loc] =>
    replace (upd_return (upd_local C ret) loc) with
        (upd_local_return C ret loc); try by destruct C
  end.
*)


(** * More Advanced Lemmas **)

Section Host.

Variable host_function : eqType.

Let store_record := store_record host_function.
Let funcinst := funcinst host_function.
Let e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
  @e_typing _.

Lemma values_typing_length: forall s vs ts,
    @values_typing host_function s vs = Some ts ->
    length vs = length ts.
Proof.
  move => s vs ts Hvts.
  apply those_length in Hvts.
  by rewrite length_is_size size_map -length_is_size in Hvts.
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

Lemma bet_value_typing: forall C bv v,
    $V v = AI_basic bv ->
    be_typing C [::bv] (Tf nil [::typeof v]).
Proof.
  move => C bv v HConst.
  destruct v; inversion HConst; subst; clear HConst; try by constructor.
  destruct v; inversion H0; subst; clear H0.
  by constructor.
Qed.

(************ these come from the certified itp *************)
(*
Lemma bet_const' : forall C vs,
  be_typing C (map BI_const_num vs) (Tf [::] (map (fun v => T_num (typeof_num v)) vs)).
Proof.
  intros C vs. induction vs as [|vs' v IHvs] using last_ind.
  - apply bet_empty.
  - rewrite <- cats1. rewrite map_cat.
    eapply bet_composition; eauto => //.
    rewrite map_cat.
    apply bet_weakening_empty_1.
    by apply bet_const_num.
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
*)
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

(** Store extension properties **)

Let func_extension: funcinst -> funcinst -> bool := @func_extension _.
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

Lemma table_extension_refl: forall t,
    table_extension t t.
Proof.
  move => t. unfold table_extension.
  by apply/andP.
Qed.

Lemma all2_table_extension_same: forall t,
    all2 table_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive.
  by apply table_extension_refl.
Qed.

Lemma mem_extension_refl: forall m,
    mem_extension m m.
Proof.
  move => m.
  unfold mem_extension.
  by apply/andP; split => //.
Qed.

Lemma all2_mem_extension_same: forall t,
    all2 mem_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive.
  by apply mem_extension_refl.
Qed.

Lemma global_extension_refl: forall t,
    global_extension t t.
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

Lemma elem_extension_refl: forall t,
    elem_extension t t.
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

Lemma data_extension_refl: forall t,
    data_extension t t.
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
  unfold table_extension in *; simpl in *.
  remove_bools_options.
  apply/andP; split; last apply/eqP.
  - apply/eqP. by rewrite H1.
  - simpl in *; subst.
    by lias.
Qed.
    
Lemma mem_extension_trans:
  transitive mem_extension.
Proof.
  move => x1 x2 x3 Hext1 Hext2.
  destruct x1, x2, x3.
  unfold mem_extension in *; simpl in *.
  remove_bools_options.
  apply/andP; split; last apply/eqP.
  - apply/eqP; by rewrite H1.
  - simpl in *; subst.
    by lias.
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

Variable host_function: eqType.
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
  all: try by destruct vs.
  all: try by destruct ves.
  { intros. apply: lfilled_not_nil. exact H1. exact H0. }
Qed.

End Host.
