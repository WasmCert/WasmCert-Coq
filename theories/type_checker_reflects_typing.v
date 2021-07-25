(** The Wasm type checker reflects typing (soundness and completeness) **)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Require Import Coq.Program.Equality.

Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Wasm Require Import common operations typing type_checker properties.

Section Host.

Variable host_function : eqType.

Lemma result_typingP : forall r ts,
  reflect (result_typing r ts) (result_types_agree ts r).
Proof.
  move=> + ts. case.
  - move=> l /=. apply: iffP.
    + rewrite all2_swap. by apply: all2_mapP.
    + move=> ?. subst. by constructor.
    + move=> T. by inversion_clear T.
  - apply: Bool.ReflectT. by constructor.
Qed.

Lemma nth_error_ssr: forall {T: Type} (l: list T) n (x x0:T),
  List.nth_error l n = Some x -> nth x0 l n = x.
Proof.
  induction l => //=; destruct n => //=; intros; first by inversion H.
  by apply IHl.
Qed.

Lemma ssr_nth_error: forall {T: Type} (l: list T) n (x x0:T),
  nth x0 l n = x ->
  n < size l ->
  List.nth_error l n = Some x.
Proof.
  induction l; destruct n => //=; intros; subst => //=.
  eapply IHl; eauto; by lias.
Qed.

Lemma ct_compat_symmetry: forall c1 c2,
  ct_compat c1 c2 ->
  ct_compat c2 c1.
Proof.
  intros.
  destruct c1, c2 => //=.
  simpl in H.
  move/eqP in H.
  subst.
  by apply/eqP.
Qed.

Lemma ct_list_compat_rcons_bool: forall l1 l2 x1 x2,
  ct_list_compat (rcons l1 x1) (rcons l2 x2) =
  ct_compat x1 x2 && ct_list_compat l1 l2.
Proof.
  induction l1; intros; destruct l2 => //=.
  - destruct l2 => //=; by lias.
  - destruct l1 => //=; by lias.
  - rewrite IHl1. by lias.
Qed.
    
Lemma ct_list_compat_rcons: forall l1 l2 x1 x2,
  ct_list_compat (rcons l1 x1) (rcons l2 x2) <->
  ct_compat x1 x2 /\ ct_list_compat l1 l2.
Proof.
  split; intros.
  - rewrite ct_list_compat_rcons_bool in H.
    by move/andP in H.
  - move/andP in H.
    by rewrite ct_list_compat_rcons_bool.
Qed.

Lemma ct_suffix_rcons: forall l1 l2 x1 x2,
  ct_suffix (rcons l1 x1) (rcons l2 x2) <->
  ct_compat x1 x2 /\ ct_suffix l1 l2.
Proof.
  unfold ct_suffix.
  intros.
  split; move => H.
  - move/andP in H; destruct H.
    repeat rewrite size_rcons in H.
    rewrite drop_rcons in H0; last by repeat rewrite size_rcons; lias.
    apply ct_list_compat_rcons in H0.
    destruct H0.
    split => //; first by apply ct_compat_symmetry.
    apply/andP; split; first by lias.
    repeat rewrite size_rcons in H1.
    by replace (_-_) with (size l2 - size l1) in H1; last by lias.
  - destruct H.
    move/andP in H0; destruct H0.
    repeat rewrite size_rcons.
    apply/andP; split; first by lias.
    rewrite drop_rcons; last by lias.
    replace (_-_) with (size l2 - size l1); last by lias.
    apply ct_list_compat_rcons.
    split => //.
    by apply ct_compat_symmetry.
Qed.
    
Lemma ct_suffix_empty: forall l,
  ct_suffix [::] l.
Proof.
  move => l. unfold ct_suffix => /=.
  rewrite subn0. apply/eqP.
  by rewrite drop_size.
Qed.

Lemma ct_suffix_any_grow: forall l1 l2,
  ct_suffix l1 l2 ->
  size l1 < size l2 ->
  ct_suffix [::CTA_any & l1] l2.
Proof.
  unfold ct_suffix => /=.
  move => l1 l2 Hsuf Hsize.
  move/andP in Hsuf; destruct Hsuf as [_ Hcompat].
  apply/andP; split => //=.
  move: l1 l2 Hsize Hcompat.
  induction l1 using last_ind => //=; move => l2; case/lastP: l2 => [|l2 x']; intros => //.
  - rewrite -> size_rcons in *.
    replace (_-_) with (size l2); last by lias.
    remember (drop (size l2) _) as tail.
    assert (size tail = 1).
    { subst. rewrite size_drop size_rcons. by lias. }
    do 2 destruct tail => //=.
    by destruct c.
  - repeat rewrite size_rcons in Hsize.
    rewrite drop_rcons in Hcompat; last by repeat rewrite size_rcons; lias.
    rewrite drop_rcons; last by repeat rewrite size_rcons; lias.
    apply ct_list_compat_rcons in Hcompat.
    destruct Hcompat.
    repeat rewrite size_rcons in H0.
    replace (_-_) with (size l2 - size l1) in H0; last by lias.
    apply IHl1 in H0; eauto.
    repeat rewrite size_rcons.
    rewrite - rcons_cons.
    by apply ct_list_compat_rcons.
Qed.
    
Lemma ct_suffix_any_1: forall l,
  size l > 0 ->
  ct_suffix [::CTA_any] l.
Proof.
  move => l H.
  destruct l => //=.
  unfold ct_suffix, ct_list_compat => /=.
  destruct (_ -1) eqn: Hsize => //.
  - destruct l => //=. apply/andP.
    split => //. by destruct c.
  - assert (size (drop n l) = 1).
    { rewrite size_drop. by lias. }
    remember (drop n l) as l'.
    do 2 destruct l' => //=.
    by destruct c0.
Qed.

Lemma ct_list_compat_self: forall l,
  ct_list_compat l l.
Proof.
  induction l => //.
  unfold all2.
  apply/andP; split => //.
  by destruct a => //=.
Qed.

Lemma ct_suffix_self: forall l,
  ct_suffix l l.
Proof.
  move => l.
  unfold ct_suffix => /=.
  apply/andP; split => //.
  rewrite subnn.
  rewrite drop0.
  by apply ct_list_compat_self.
Qed.

Lemma ct_suffix_suffix: forall l1 l2,
  ct_suffix (to_ct_list l2) (to_ct_list (l1 ++ l2)).
Proof.
  move => l1 l2.
  unfold ct_suffix.
  apply/andP; split => //; repeat rewrite size_map; rewrite size_cat => //.
  - by lias.
  - unfold to_ct_list. rewrite map_cat.
    replace (size l1 + size l2 - size l2) with (size l1); last by lias.
    rewrite drop_size_cat; last by rewrite size_map.
    by apply ct_list_compat_self.
Qed.

Lemma ct_suffix_prefix: forall l1 l2 l3,
  ct_suffix (l1 ++ l2) l3 ->
  ct_suffix l2 l3.
Proof.
  unfold ct_suffix; intros.
  move/andP in H; rewrite size_cat in H; destruct H.
  apply/andP; split; first by lias.
  unfold ct_list_compat in *.
  move : l2 l3 H H0.
  induction l1 => //; intros.
  destruct l3 => //.
  simpl in H.
  apply IHl1; first by lias.
  rewrite -> drop_nth with (x0 := a) in H0; last by lias.
  simpl in H0.
  move/andP in H0; destruct H0.
  replace (_-_) with (size l3 - (size l1 + size l2)) in H1; last by lias.
  simpl.
  by replace (_-_) with ((size l3 - (size l1 + size l2)).+1); last by lias.
Qed.
  
Lemma ct_suffix_extend: forall l1 l2 l3,
  ct_suffix l1 l2 ->
  ct_suffix l1 (l3 ++ l2).
Proof.
  unfold ct_suffix.
  move => l1 l2 l3 H.
  move/andP in H; destruct H as [H1 H2].
  apply/andP; split; first by rewrite size_cat; lias.
  rewrite size_cat.
  rewrite drop_cat.
  replace (size l3 + size l2 - size l1 < size l3) with false; last by lias.
  replace (size l3 + size l2 - size l1 - size l3) with (size l2 - size l1); last by lias.
  assumption.
Qed.

Lemma ct_suffix_size: forall ct1 ct2,
  ct_suffix ct1 ct2 ->
  size ct1 <= size ct2.
Proof.
  move => ct1 ct2.
  unfold ct_suffix.
  move => H.
  move/andP in H; destruct H as [H _].
  by repeat rewrite size_map in H.
Qed.

Lemma upd_label_overwrite: forall C loc lab ret lab',
  upd_label (upd_local_label_return C loc lab ret) lab'
  = upd_local_label_return C loc lab' ret.
Proof.
  move => C loc lab ret lab'.
  unfold upd_label.
  unfold upd_local_label_return. by auto.
Qed.

(*???*)
Ltac bool_to_prop_and:=
  repeat match goal with
         | H: _ && _ = true |- _ =>
           move/andP in H; destruct H
         | H: _ && _ |- _ =>
           move/andP in H; destruct H
         end.

Lemma consume_empty: forall l,
  consume l [::] = l.
Proof.
  move => l.
  by destruct l => //=; rewrite ct_suffix_empty; rewrite subn0; rewrite take_size.
Qed.

Lemma produce_empty: forall l,
  produce l (CT_type [::]) = l.
Proof.
  move => l.
  unfold produce.
  by destruct l => //=; rewrite cats0.
Qed.

Lemma type_update_empty_cons: forall l ct,
  type_update l [::] ct = produce l ct.
Proof.
  move => l.
  unfold type_update. by rewrite consume_empty.
Qed.

Lemma type_update_empty_prod: forall l ts,
  type_update l ts (CT_type [::]) = consume l ts.
Proof.
  move => l ts.
  unfold type_update. by rewrite produce_empty.
Qed.
  

Ltac simplify_hypothesis Hb :=
  repeat match type of Hb with
  | is_true (es_is_trap _) => move/es_is_trapP: Hb => Hb
  | ?b = true => fold (is_true b) in Hb
  | (_ == _) = false => move/eqP in Hb
  | context C [size (rev _)] => rewrite size_rev in Hb
  | context C [take _ (rev _)] => rewrite take_rev in Hb
  | context C [rev (rev _)] => rewrite revK in Hb
  | context C [true && _] => rewrite Bool.andb_true_l in Hb
  | context C [_ && true] => rewrite Bool.andb_true_r in Hb
  | context C [false || _] => rewrite Bool.orb_false_l in Hb
  | context C [_ || false] => rewrite Bool.orb_false_r in Hb
  (* It looks really like a bad idea to unfold type_update in general. *)
(*  | context C [type_update _ _] => unfold type_update in Hb; try simpl in Hb*)
  | context C [ct_suffix [::] _] => rewrite ct_suffix_empty in Hb; try simpl in Hb
  | context C [ct_suffix [::CTA_any] (_::_)] => rewrite ct_suffix_any_1 in Hb => //; try simpl in Hb
  | context C [ct_suffix ?l ?l] => rewrite ct_suffix_self in Hb => //; try simpl in Hb
  | context C [size (map _ _)] => rewrite size_map in Hb
  | context C [?x - 0] => rewrite subn0 in Hb; simpl in Hb
  | context C [?x - ?x] => rewrite subnn in Hb; simpl in Hb
  | context C [take (size ?x) ?x] => rewrite take_size in Hb; simpl in Hb
  | context C [drop (size ?x) ?x] => rewrite drop_size in Hb; simpl in Hb
  | context C [take 0 ?x] => rewrite take0 in Hb; simpl in Hb
  | context C [drop 0 ?x] => rewrite drop0 in Hb; simpl in Hb
  | context C [produce _ _] => unfold produce in Hb; simpl in Hb
  | context C [ if ?expr then _ else _ ] => let if_expr := fresh "if_expr" in destruct expr eqn:if_expr => //=; simpl in Hb => //=
  | context C [ match ?expr with | Some _ => _ | None => _ end ] => let match_expr := fresh "match_expr" in destruct expr eqn:match_expr => //=; simpl in Hb => //=
  | exists _, _ /\ _ => let tx := fresh "tx" in
                        let Hsuffix := fresh "Hsuffix" in
                        let Hbet := fresh "Hbet" in
                        destruct Hb as [tx [Hsuffix Hbet]]
  | is_true true => clear Hb
  | is_true false => exfalso; apply: notF; apply: Hb
  | is_true (_ == _) => move/eqP in Hb
  | is_true (_ && _) => move/andP in Hb; destruct Hb
  | is_true (_ || _) => move/orP in Hb; destruct Hb
  | ?x = ?x => clear Hb
  | _ = _ => rewrite Hb in *; subst => //=
  | _ => simpl in Hb => /=
         end.

Ltac simplify_goal :=
  repeat match goal with H: _ |- _ => progress simplify_hypothesis H end.

Lemma CT_top_empty_consume: forall tf,
  consume (CT_top_type [::]) tf = CT_top_type [::].
Proof.
  move => tf. unfold consume.
  destruct tf => //=.
  by rewrite ct_suffix_empty.
Qed.

Definition populate_ct_aux_single (cta: checker_type_aux): value_type :=
  match cta with
  | CTA_any => T_i32
  | CTA_some vt => vt
  end.

Definition populate_ct_aux (l: list checker_type_aux): list value_type :=
  map populate_ct_aux_single l.

Definition populate_ct (ct: checker_type) : list value_type :=
  match ct with
  | CT_type tn => tn
  | CT_top_type tn => populate_ct_aux tn
  | CT_bot => [::]
  end.

Ltac resolve_bet:=
  repeat match goal with
         | |- be_typing _ [::] (Tf ?tx ?tx) =>
           apply bet_weakening_empty_both; apply bet_empty => //
         | H: be_typing ?C ?bes (Tf ?tn ?tm) |- be_typing ?C (_ :: ?bes) (Tf _ ?tm) =>
           eapply bet_composition_front; last by apply H
         | H: is_true ?expr |- context C [ if ?expr then _ else _ ] =>
           idtac H; rewrite H => //=
         end.

Ltac auto_rewrite_cond:=
  repeat match goal with
         | H: is_true ?expr |- context C [ ?expr ] =>
           rewrite H => //=
         | H: ?x <> ?y |- context C [?x != ?y ] =>
           move/eqP in H; rewrite H => //=
         | H: is_true (Nat.eqb ?x ?y) |- _ =>
           move/eqP in H; rewrite H => //=
         | H: is_true (b_e_type_checker _ _ _) |- _ => simpl in H => //=
         | |- context C [ ?x == ?x ] =>
           rewrite eq_refl => //=
         | |- context C [ true && true ] =>
           unfold andb => //=
         | |- context C [ct_suffix [::] _] => rewrite ct_suffix_empty => //=
         | |- context C [ct_suffix [::CTA_any] (_::_)] => rewrite ct_suffix_any_1 => //=
         | |- context C [ct_suffix ?l ?l] => rewrite ct_suffix_self => //=
         | |- context C [ct_suffix ?l (?l)%list] => rewrite ct_suffix_self => //=
         | |- context C [size (to_ct_list _)] => unfold to_ct_list; rewrite size_map => //=
         | |- context C [?x - ?x] => rewrite subnn => //=
         | |- context C [?x - 0] => rewrite subn0 => //=
         | |- context C [take 0 _] => rewrite take0 => //=
         | |- context C [take (size ?x) ?x] => rewrite take_size => //=
         | |- context C [drop 0 _] => rewrite drop0 => //=
         | |- context C [take (drop ?x) ?x] => rewrite drop_size => //=
         | |- context C [_ :: (tc_label _)] => rewrite - cat1s => //=
         | |- context C [_ ++ [::]] => rewrite cats0 => //=
         | |- context C [size (_ ++ _)] => rewrite size_cat => //=
         | |- context C [size (_ ++ _)%list] => rewrite size_cat => //=
         | |- context C [?x + ?n - ?n] => replace (x + n - n) with x; last by lias => //=
         | |- context C [match ?f with | (Tf _ _) => _ end ] => destruct f => //=
(*         | |- context C [type_update _ _] => unfold type_update => //=*)
         | H: match ?expr with | _ => _ end = CT_type _ |- _ => let Hexpr := fresh "Hexpr" in destruct expr eqn: Hexpr => //=
         | H: match ?expr with | _ => _ end = CT_top_type _ |- _ => let Hexpr := fresh "Hexpr" in destruct expr eqn: Hexpr => //=
         | H: option_map _ _ = _ |- _ => unfold option_map in H
         | H: Some _ = Some _ |- _ => inversion H; subst; clear H => //=
         | H: CT_type _ = CT_type _ |- _ => inversion H; subst; clear H => //=
         | H: is_true (plop2 _ _ _) |- _ => unfold plop2 in H => //=
         | H: is_true (List.nth_error _ _ == _) |- _ => move/eqP in H; rewrite H => //=
         | H: is_true (_ == _) |- _ => move/eqP in H
         | H: ?x = ?x |- _ => clear H
         | H: _ = _ |- _=> progress (rewrite H; subst => //=)
         | _ => simplify_goal => //=; (try rewrite ct_suffix_suffix => //=); (try rewrite ct_suffix_self => //=); (try subst => //=)
         end.

Lemma populate_ct_aux_suffix: forall l,
  ct_suffix l (to_ct_list (populate_ct_aux l)).
Proof with auto_rewrite_cond.
  induction l => //=.
  unfold ct_suffix => /=.
  apply/andP; split.
  - repeat rewrite size_map. by lias.
  - unfold ct_list_compat.
    unfold ct_suffix, ct_list_compat, to_ct_list, populate_ct_aux in IHl...
    repeat rewrite size_map.
    rewrite subnn.
    simpl.
    destruct a => //=.
    by apply/andP.
Qed.

Lemma populate_ct_agree: forall l,
  l <> CT_bot ->
  c_types_agree l (populate_ct l).
Proof.
  intros.
  destruct l => //=.
  by apply populate_ct_aux_suffix.
Qed.

Lemma type_update_prefix: forall l1 l2 l3 cons prod,
  type_update (CT_type l1) cons prod = CT_type l2 ->
  type_update (CT_type (l3 ++ l1)) cons prod = CT_type (l3 ++ l2).
Proof.
  unfold type_update, produce, consume.
  move => l1 l2 l3 cons prod H.
  auto_rewrite_cond.
  unfold to_ct_list.
  rewrite map_cat.
  rewrite ct_suffix_extend => //.
  rewrite take_cat.
  assert (size cons <= size l1); first by apply ct_suffix_size in Hexpr1; rewrite size_map in Hexpr1.
  replace (_ < _) with false; last by lias.
  replace (_ + _ - _ - _) with (size l1 - size cons); last by lias.
  by rewrite catA.
Qed.

Lemma type_update_prefix_top: forall l1 l2 l3 cons prod,
  type_update (CT_type l1) cons prod = CT_top_type l2 ->
  type_update (CT_type (l3 ++ l1)) cons prod = CT_top_type l2.
Proof.
  unfold type_update, produce, consume.
  move => l1 l2 l3 cons prod H.
  auto_rewrite_cond.
  unfold to_ct_list.
  rewrite map_cat.
  by rewrite ct_suffix_extend => //.
Qed.

Ltac simplify_type_update :=
  repeat (try (rewrite -> type_update_empty_cons in * )); (try (rewrite -> type_update_empty_prod in * )).

Lemma check_rcons: forall es e C ts,
  check C (es ++ [::e]) ts = check_single C (check C es ts) e.
Proof.
  by induction es => //=.
Qed.
    
Lemma check_single_notop: forall C ct ts e,
  check_single C ct e = CT_type ts ->
  exists ts', ct = CT_type ts'.
Proof with auto_rewrite_cond.
  move => C ct ts e.
  move : C ct ts.
  induction e; move => C ct ts Htc; destruct ct; auto_rewrite_cond; try (unfold type_update in Htc); try by eexists...
Qed.
  
Lemma check_single_bot: forall C e,
  check_single C CT_bot e = CT_bot.
Proof.
  move => C e.
  by destruct e => //=.
Qed.
  
Lemma check_single_weaken: forall C e ts ts2 ts0,
  check_single C (CT_type ts) e = CT_type ts0 ->
  check_single C (CT_type (ts2 ++ ts)) e = CT_type (ts2 ++ ts0).
Proof with auto_rewrite_cond.
  move => C e.
  move : C.
  induction e; move => C ts ts2 ts0 Htc; simpl in Htc => //=; simplify_goal; auto_rewrite_cond; simplify_goal; subst => //=; try by apply type_update_prefix...
  - do 3 destruct ts => //=; clear H.
    (* Numerical disaster *)
    rewrite length_is_size; rewrite size_cat.
    replace (_ < _) with true => /=; last by lias.
    repeat (rewrite List.nth_error_app2; last by rewrite length_is_size; lias).
    repeat rewrite length_is_size.
    replace (_ + _ - 2 - _) with (size ts + 1); last by lias.
    replace (_ + _ - 3 - _) with (size ts); last by lias.
    replace (_ - 2) with (length ts + 1) in H0; last by lias.
    replace (_ - 3) with (length ts) in H0; last by lias.
    rewrite length_is_size in H0.
    rewrite H0.
    rewrite eq_refl.
    unfold to_ct_list.
    rewrite map_cat.
    rewrite ct_suffix_extend => //.
    rewrite take_cat.
    replace (_ < _) with false; last by lias.
    replace (_ + _ - _ - _) with (size ts + 1); last by lias.
    repeat f_equal => //=.
    replace (size ts + 1) with (1 + size ts); last by lias.
    simpl.
    by f_equal.
  - destruct f => //=.
    simplify_goal.
    by apply type_update_prefix.
Qed.
    
Lemma check_single_weaken_top: forall C e ts ts2 ts0,
  check_single C (CT_type ts) e = CT_top_type ts0 ->
  check_single C (CT_type (ts2 ++ ts)) e = CT_top_type ts0.
Proof with auto_rewrite_cond.
  move => C e.
  move : C.
  induction e; move => C ts ts2 ts0 Htc; simpl in Htc => //=; simplify_goal; auto_rewrite_cond => //=; try (destruct f); simplify_goal; by erewrite type_update_prefix_top; eauto...
Qed.
    
Lemma check_weaken: forall C es ts ts2 ts0,
  check C es (CT_type ts) = CT_type ts0 ->
  check C es (CT_type (ts2 ++ ts)) = CT_type (ts2 ++ ts0).
Proof.
  move => C es.
  move: C.
  (* It's much easier to do induction from the right side due to how check works. *)
  induction es using List.rev_ind => //=; move => C ts ts2 ts0 Htc; first by inversion Htc.
  rewrite check_rcons in Htc.
  rewrite check_rcons.
  assert (exists ts', (check C es (CT_type ts)) = CT_type ts') as [ts3 Htc2]; first by eapply check_single_notop; eauto.
  rewrite Htc2 in Htc.
  erewrite IHes; eauto.
  by apply check_single_weaken.
Qed.
  
Lemma check_weaken_top: forall C es ts ts2 ts0,
  check C es (CT_type ts) = CT_top_type ts0 ->
  check C es (CT_type (ts2 ++ ts)) = CT_top_type ts0.
Proof.
  move => C es.
  move: C.
  induction es using List.rev_ind => //=; move => C ts ts2 ts0 Htc.
  rewrite check_rcons in Htc.
  rewrite check_rcons.
  destruct (check C es (CT_type ts)) eqn:Htc2; simpl in Htc => //=.
  - by erewrite IHes; eauto.
  - erewrite check_weaken; eauto.
    by erewrite check_single_weaken_top; eauto.
  - by rewrite check_single_bot in Htc.
Qed.
    
Lemma same_lab_h_condition: forall C ts l,
  all (fun i: nat => (i < length (tc_label C)) && plop2 C i ts) l ->
  same_lab_h l (tc_label C) ts = Some ts.
Proof.
  move => C ts l.
  move: C ts.
  induction l => //=.
  move => C ts H.
  move/andP in H; destruct H as [H1 H2].
  move/andP in H1; destruct H1 as [H1 H3].
  replace (length (tc_label C) <= a) with false; last by lias.
  move/ltP in H1.
  unfold plop2 in H3.
  move/eqP in H3.
  rewrite H3.
  rewrite eq_refl.
  by apply IHl.
Qed.

Lemma same_lab_h_rec: forall x l C ts,
  same_lab_h (x :: l) (tc_label C) ts = Some ts ->
  same_lab_h l (tc_label C) ts = Some ts.
Proof.
  move => x l C ts H.
  simpl in H.
  destruct (length (tc_label C) <= x) => //=.
  destruct (List.nth_error (tc_label C) x) => //=.
  destruct (l0 == ts) eqn:Heq => //=.
  move/eqP in Heq. by subst.
Qed.

Lemma ct_list_compat_trans: forall ts1 ts2 ts,
  ct_list_compat (to_ct_list ts) ts1 ->
  ct_list_compat (to_ct_list ts) ts2 ->
  ct_list_compat ts1 ts2.
Proof.
  move => ts1.
  induction ts1; move => ts2 ts H1 H2; destruct ts2, ts => //=.
  simpl in *.
  move/andP in H1; destruct H1.
  move/andP in H2; destruct H2.
  apply/andP; split.
  - destruct c, a => //=.
    move/eqP in H; move/eqP in H1.
    subst.
    by apply/eqP.
  by eapply IHts1; eauto.
Qed.

Lemma ct_suffix_take: forall l1 l2 n,
  ct_suffix l1 l2 ->
  n <= size l1 ->
  ct_suffix (take (size l1 - n) l1) (take (size l2 - n) l2).
Proof with auto_rewrite_cond.
  induction l1 using last_ind; case/lastP => [|l2' x'] => //=; intros.
  - by apply ct_suffix_empty.
  - by destruct l1 => //=.
  - rewrite size_rcons in H0.
    destruct n => //=.
    + repeat rewrite subn0.
      by repeat rewrite take_size.
    + repeat rewrite size_rcons.
      repeat rewrite subSS.
      apply ct_suffix_rcons in H; destruct H.
      repeat rewrite - cats1.
      repeat rewrite take_cat.
      destruct n => //=...
      * by destruct (size l1 < size l1), (size l2' < size l2') => //=.
      * assert (size l1 - n.+1 < size l1); first by lias...
        assert (size l1 <= size l2'); first by unfold ct_suffix in H1; move/andP in H1; destruct H1.
        assert (size l2' - n.+1 < size l2'); first by lias...
        by apply IHl1.
Qed.
        
Lemma ct_compat_extend: forall l1 l2 l3,
  ct_list_compat l1 l2 ->
  ct_list_compat (l1 ++ l3) (l2 ++ l3).
Proof.
  move => l1.
  induction l1 => //=; move => l2 l3 H; destruct l2 => //=; first by apply ct_list_compat_self.
  move/andP in H; destruct H.
  apply/andP; split => //.
  by apply IHl1.
Qed.
  
Lemma ct_compat_take: forall l1 l2 n,
  ct_list_compat l1 l2 ->
  ct_list_compat (take n l1) (take n l2).
Proof.
  move => l1.
  induction l1 => //=; move => l2 n H; destruct l2 => //=.
  move/andP in H; destruct H as [H1 H2].
  destruct n => //=.
  apply/andP; split => //.
  by apply IHl1.
Qed.

Lemma ct_compat_drop: forall l1 l2 n,
  ct_list_compat l1 l2 ->
  ct_list_compat (drop n l1) (drop n l2).
Proof.
  move => l1.
  induction l1 => //=; move => l2 n H; destruct l2 => //=.
  move/andP in H; destruct H as [H1 H2].
  destruct n => //=.
  apply/andP; split => //.
  by apply IHl1.
Qed.

Lemma ct_compat_drop_shift: forall l1 l2 n a b c1 c2,
  ct_list_compat (drop n l1) l2 ->
  a < size l1 ->
  b < size l2 ->
  a = b + n ->
  ct_compat (nth c1 l1 a) (nth c2 l2 b).
Proof.
  induction l1 as [| x l1'] => //=; move => l2 n a b c1 c2 Hcompat Hs1 Hs2 Hsum; destruct l2, a, b => //=.
  - destruct n => //. simpl in Hcompat.
    move/andP in Hcompat. by destruct Hcompat.
  - rewrite add0n in Hsum.
    subst.
    replace c with (nth c1 (c :: l2) 0) => //.
    by eapply IHl1'; eauto.
  - eapply IHl1'; eauto.
    destruct n => //=.
    + simpl in Hcompat.
      move/andP in Hcompat.
      destruct Hcompat.
      by rewrite drop0.
    + rewrite -> drop_nth with (x0 := CTA_any) in Hcompat; last by lias.
      simpl in Hcompat.
      move/andP in Hcompat.
      by destruct Hcompat.
Qed.

Lemma ct_list_nth_type: forall l c n,
  n < size l ->
  exists t, nth c (to_ct_list l) n = CTA_some t.
Proof.
  induction l; destruct n => //=; move => Hsize.
  - by eexists.
  - by eapply IHl; eauto.
Qed.

(*
  We need the mutual ct type to be from ct_list, since CTA_any destroys transitivity. 
*)
Lemma ct_compat_mutual: forall ts1 ts2 ts_mutual ts,
  ts_mutual = to_ct_list ts ->
  size ts1 <= size ts_mutual ->
  size ts2 <= size ts_mutual ->
  ct_list_compat (drop (size ts_mutual - size ts1) ts_mutual) ts1 ->
  ct_list_compat (drop (size ts_mutual - size ts2) ts_mutual) ts2 ->
  size ts1 <= size ts2 ->
  ct_list_compat (drop (size ts2 - size ts1) ts2) ts1.
Proof.
  move => ts1.
  induction ts1; move => ts2 ts_mutual ts Hnany Hs1 Hs2 Hct1 Hct2 Hsize => //=.
  - rewrite subn0. by rewrite drop_size.
  - destruct ts2 => //=.
    destruct ts_mutual, ts => //=.
    simpl in *.
    inversion Hnany; subst; clear Hnany.
    destruct (size ts2 == size ts1) eqn: Heq1 => //=; move/eqP in Heq1.
    + rewrite Heq1.
      rewrite Heq1 in Hct2.
      rewrite subnn.
      destruct (size (to_ct_list ts) == size ts1) eqn: Heq2 => //=; move/eqP in Heq2.
      * rewrite Heq2 in Hct1, Hct2.
        rewrite subnn in Hct1, Hct2.
        replace (CTA_some v :: to_ct_list ts) with (to_ct_list (v :: ts)) in * => //=.
        eapply ct_list_compat_trans in Hct1; eauto.
        by simpl in Hct1.
      * destruct (_-_) eqn:Hsub.
        -- assert ((size (to_ct_list ts)).+1 <= (size ts1).+1); first by lias.
           simpl in *. by lias.
        -- unfold to_ct_list in Hct1, Hct2.
           rewrite - map_drop in Hct1, Hct2.
           eapply ct_list_compat_trans in Hct1; eauto.
           by simpl in Hct1.
    + destruct ((size ts2).+1-(size ts1).+1) eqn:Hsub.
      * assert ((size ts2).+1 <= (size ts1).+1); first by lias.
        simpl in *. by lias.
      * assert (size ts1 < size (to_ct_list ts)); first by lias.
        destruct (_ - _) eqn:Hsub2; first by lias.
        destruct (size (to_ct_list ts) == size ts2) eqn: Heq3 => //=; move/eqP in Heq3.
        -- rewrite Heq3 in Hct2.
           rewrite subnn in Hct2.
           rewrite Heq3 in Hsub2.
           assert (n0 = n); first by lias.
           subst.
           simpl in Hct2.
           move/andP in Hct2; destruct Hct2 as [_ Hct2].
           eapply ct_compat_drop in Hct2.
           unfold to_ct_list in Hct1, Hct2.
           rewrite - map_drop in Hct1.
           rewrite - map_drop in Hct2.
           by eapply ct_list_compat_trans in Hct1; eauto.
        -- destruct ((size (to_ct_list ts)).+1 - (size ts2).+1) eqn:Hsub4.
           ++ assert ((size (to_ct_list ts)).+1 <= (size ts2).+1); first by lias.
              simpl in *. by lias.
           ++ assert (n < size ts2); first by lias.
              assert (n0 < size (to_ct_list ts)); first by lias.
              assert (n1 < size (to_ct_list ts)); first by lias.
              eapply drop_nth with (x0 := CTA_any) in H0.
              eapply drop_nth with (x0 := CTA_any) in H1.
              eapply drop_nth with (x0 := CTA_any) in H2.
              rewrite - Hsub in H0.
              rewrite - Hsub2 in H1.
              rewrite - Hsub4 in H2.
              rewrite H0.
              rewrite H1 in Hct1.
              rewrite H2 in Hct2.
              simpl in *.
              rewrite -> subSS in *.
              move/andP in Hct1; destruct Hct1 as [Hcs1 Hct1].
              move/andP in Hct2; destruct Hct2 as [Hcs2 Hct2].
              apply/andP; split.
              ** assert (ct_compat (nth CTA_any (to_ct_list ts) n0) (nth CTA_any ts2 n)) as Hcs3.
                 eapply ct_compat_drop_shift; eauto; by lias.
                 destruct (nth CTA_any ts2 n), a => //=.
                 assert (exists v, nth CTA_any (to_ct_list ts) n0 = CTA_some v) as Hv; first eapply ct_list_nth_type; eauto; first by unfold to_ct_list in Hsub2; rewrite size_map in Hsub2; lias.
                 destruct Hv as [vt Hv].
                 rewrite -> Hv in *.
                 simpl in *.
                 move/eqP in Hcs1.
                 move/eqP in Hcs3.
                 subst.
                 by apply/eqP.
              (* Finally the IH applies here... *)
              ** eapply IHts1; by eauto.
Qed.

Lemma ct_suffix_mutual_compat: forall ts1 ts2 ts_mutual ts,
  ts_mutual = to_ct_list ts ->
  ct_suffix ts1 ts_mutual ->
  ct_suffix ts2 ts_mutual ->
  size ts1 <= size ts2 ->
  ct_list_compat (drop (size ts2 - size ts1) ts2) ts1.
Proof with auto_rewrite_cond.
  move => ts1 ts2 ts_mutual ts Hnany Hsuffix1 Hsuffix2 Hsize.
  subst.
  unfold ct_suffix in *...
  by eapply ct_compat_mutual; eauto.
Qed.

Lemma ct_suffix_mutual_suffix: forall ts1 ts2 ts_mutual ts,
  ts_mutual = to_ct_list ts ->
  ct_suffix ts1 ts_mutual ->
  ct_suffix ts2 ts_mutual ->
  size ts1 <= size ts2 ->
  ct_suffix ts1 ts2.
Proof with auto_rewrite_cond.
  move => ts1 ts2 ts_mutual ts Hnany Hsuffix1 Hsuffix2 Hsize.
  subst.
  unfold ct_suffix in *...
  by eapply ct_compat_mutual; eauto.
Qed.

Lemma sub_if: forall a b,
  (if (a-b<a) then a-b else a) = a-b.
Proof.
  move => a b.
  destruct (a-b<a) eqn:H; by lias.
Qed.

Lemma le_neq_lt: forall a b,
    a <= b ->
    a <> b ->
    a < b.
Proof.
  by lias.
Qed.
    
Lemma type_update_agree_suffix: forall ts cons prod ts2 topt,
  c_types_agree (type_update (CT_type ts) cons prod) ts2 ->
  ct_suffix topt (to_ct_list ts) ->
  c_types_agree (type_update (CT_top_type topt) cons prod) ts2.
Proof with auto_rewrite_cond.
  move => ts cons prod ts2 topt Hct Hsuffix.
  unfold type_update, c_types_agree, produce, consume, ct_suffix, to_ct_list in * => /=...
  destruct (size cons <= size topt) eqn:Hsize => //=.
  - remember Hsize as Hsize_ct; clear HeqHsize_ct.
    apply ct_compat_mutual with (ts := ts) (ts_mutual := to_ct_list ts) in Hsize; eauto...
    rewrite size_map.
    destruct prod => //=...
    apply/andP; split.
    + repeat rewrite size_take.
      rewrite size_map.
      repeat rewrite sub_if.
      by lias.
    + repeat rewrite size_take.
      repeat rewrite size_map.
      repeat rewrite sub_if.
      rewrite - map_drop.
      rewrite drop_cat.
      rewrite size_take.
      rewrite sub_if.
      replace (_ - _ + _ - _) with (size ts - size topt); last by lias.
      move/leP in Hsize_ct.
      destruct (size ts - size topt == size ts - size cons) eqn:Heq.
      * replace (_ - _ < _ - _) with false => //=; last by lias.
        replace (_ - _ - _) with 0; last by lias.
        rewrite drop0.
        assert (size topt = size cons); first by lias.
        rewrite -> H3 in *.
        rewrite subnn.
        rewrite take0 => //=.
        by apply ct_list_compat_self.
      * assert (size ts - size topt <= size ts - size cons); first by lias.
        move/eqP in Heq.
        apply le_neq_lt in H3 => //.
        rewrite H3.
        rewrite map_cat.
        apply ct_compat_extend.
        replace (size ts - size cons) with ((size topt - size cons) + (size ts - size topt)); last by lias.
        rewrite - take_drop.
        rewrite map_take.
        apply ct_compat_take.
        by rewrite map_drop.
  - assert (size topt <= size cons) as Hsize2; first by lias.
    rewrite Hsize2.
    apply ct_compat_mutual with (ts := ts) (ts_mutual := to_ct_list ts) in Hsize2 => //...
    rewrite size_map.
    destruct prod => //=...
    repeat rewrite size_map.
    rewrite size_take.
    rewrite sub_if.
    apply/andP; split; first by lias.
    rewrite map_cat map_take.
    replace (_ - _ + _ - _) with (size ts - size cons); last by lias.
    rewrite drop_cat.
    rewrite size_take size_map.
    rewrite sub_if => /=.
    replace (_ < _) with false; last by lias.
    rewrite subnn drop0.
    by apply ct_list_compat_self.
Qed.

Lemma ct_suffix_any_take_2: forall ts,
  2 < size ts ->
  ct_suffix [::CTA_any] (to_ct_list (take (size ts - 2) ts)).
Proof.
  move => ts H.
  apply ct_suffix_any_1.
  unfold to_ct_list.
  repeat rewrite size_map size_take.
  rewrite sub_if.
  by lias.
Qed.

Lemma ct_suffix_compat_index: forall l1 l2 n t1 t2,
  ct_suffix l1 l2 ->
  n >= 1 ->
  n <= size l1 ->
  List.nth_error l1 (length l1 - n) = Some t1 ->
  List.nth_error l2 (length l2 - n) = Some t2 ->
  ct_compat t1 t2.
Proof.
  move => l1 l2 n t1 t2 Hsuf Hn Hsize Hn1 Hn2.
  unfold ct_suffix in Hsuf.
  move/andP in Hsuf; destruct Hsuf as [Hsize2 Hcompat].
  rewrite length_is_size in Hn1.
  rewrite length_is_size in Hn2.
  apply nth_error_ssr with (x0 := t1) in Hn1.
  apply nth_error_ssr with (x0 := t2) in Hn2.
  apply ct_compat_drop_shift with (a := size l2 - n) (b := size l1 - n) (c1 := t2) (c2 := t1) in Hcompat; by [rewrite Hn1 Hn2 in Hcompat; apply ct_compat_symmetry | lias | lias | lias].
Qed.

Lemma nth_to_ct_list: forall ts n x,
  List.nth_error ts n = Some x ->
  List.nth_error (to_ct_list ts) n = Some (CTA_some x).
Proof.
  intros.
  assert (n < length ts)%coq_nat as Hsize; first by rewrite - List.nth_error_Some; rewrite H.
  apply nth_error_ssr with (x1 := x) in H.
  assert (nth (CTA_some x) (to_ct_list ts) n = CTA_some x) as Hssr.
  { unfold to_ct_list. rewrite -> nth_map with (x1 := x); last by lias. by rewrite H. }
  by apply ssr_nth_error in Hssr; last by unfold to_ct_list; rewrite size_map; lias.
Qed.

Lemma select_return_top_suffix: forall c2 c3 ts topt topts,
  select_return_top topt c2 c3 = CT_top_type topts ->
  ct_suffix topt (to_ct_list ts) ->  
  List.nth_error topt (length topt - 2) = Some c2 ->
  List.nth_error topt (length topt - 3) = Some c3 ->
  List.nth_error ts (length ts - 2) = List.nth_error ts (length ts - 3) ->
  2 < length topt ->
  2 < size ts ->
  ct_suffix topts (to_ct_list (take (size ts - 2) ts)).
Proof with auto_rewrite_cond.
  move => c2 c3 ts topt topts Hselect Hsuffix Hn2 Hn3 Hts3 Hsize1 Hsize2.
  unfold select_return_top in Hselect.
  destruct (List.nth_error ts (length ts-2)) eqn:Hts2; last by apply List.nth_error_None in Hts2; rewrite length_is_size in Hts2; lias.
  symmetry in Hts3.
  remember Hts3 as Hts3'; clear HeqHts3'.
  apply nth_error_ssr with (x0 := v) in Hts3'.
  apply nth_to_ct_list in Hts2.
  apply nth_to_ct_list in Hts3.
  replace (length ts) with (length (to_ct_list ts)) in Hts2; last by repeat rewrite length_is_size; unfold to_ct_list; rewrite size_map.
  replace (length ts) with (length (to_ct_list ts)) in Hts3; last by repeat rewrite length_is_size; unfold to_ct_list; rewrite size_map.
  eapply ct_suffix_compat_index in Hts2; eauto.
  eapply ct_suffix_compat_index in Hts3; eauto.
  assert (ct_suffix (take (size topt - 3) topt) (take (size (to_ct_list ts) - 3) (to_ct_list ts)))as Hsuffixm3; first by apply ct_suffix_take.
  replace (size ts - 2) with ((size ts - 3).+1); last by lias.
  rewrite -> take_nth with (x0 := v); last by lias.
  replace (size (to_ct_list ts)) with (size ts) in Hsuffixm3; last by unfold to_ct_list; rewrite size_map.
  destruct c2, c3 => //=; auto_rewrite_cond; inversion Hselect; subst; clear Hselect; repeat rewrite length_is_size; unfold to_ct_list; rewrite map_rcons; rewrite cats1; rewrite ct_suffix_rcons; rewrite map_take; split => //; by unfold ct_compat.
Qed.
  
(*
  This seems to be a rather tedious single case.
*)
Lemma type_update_select_agree: forall topt ts,
  ct_suffix [::CTA_any; CTA_some T_i32] (to_ct_list ts) ->
  ct_suffix topt (to_ct_list ts) ->
  2 < length ts ->
  List.nth_error ts (length ts-2) = List.nth_error ts (length ts-3) ->
  c_types_agree (type_update_select (CT_top_type topt)) (take (size ts-2) ts).
Proof with auto_rewrite_cond.
  move => topt ts Hs1 Hs2 Hsize Htype.
  rewrite length_is_size in Hsize.
  destruct topt => //=; first by apply ct_suffix_any_take_2...
  destruct topt => //=...
  - (* 1 *)
    eapply ct_suffix_mutual_compat with (ts1 := [::c]) in Hs1...
    destruct c => //=; auto_rewrite_cond; by apply ct_suffix_any_take_2...
  - destruct topt => //=...
    + (* 2 *)
      eapply ct_suffix_mutual_compat with (ts1 := [::c; c0]) in Hs1...
      assert (ct_suffix [::CTA_some T_i32] [::c; c0] = true) as H; first destruct c0 => //=...
      unfold ct_suffix.
      assert (ts = take (size ts - 3) ts ++ drop (size ts - 3) ts) as H2; first by rewrite cat_take_drop.
      remember (drop (size ts-3) ts) as tail.
      assert (size tail = 3) as Hsizetail.
      { subst. rewrite size_drop. by lias. }
      repeat destruct tail as [|? tail] => //=. clear Hsizetail.
      apply/andP; split => //=.
      * unfold to_ct_list.
        rewrite size_map size_take sub_if.
        by lias.
      * rewrite -> H2 in *.
        unfold to_ct_list.
        rewrite size_map size_take sub_if size_cat size_take sub_if => //=.
        rewrite map_take.
        replace (size ts - 3 + 3 - 2 - 1) with (size ts - 3); last by lias.
        replace (size ts - 3 + 3 - 2) with (1 + (size ts - 3)); last by lias.
        rewrite - take_drop.
        rewrite map_cat.
        assert (size ts - 3 = size (to_ct_list (take (size ts - 3) ts))) as Hsize2.
        { unfold to_ct_list. by rewrite size_map size_take sub_if. }
        rewrite drop_size_cat => //.
        simpl.
        apply/andP; split => //.
        destruct c => //=.
        repeat rewrite length_is_size size_cat size_take sub_if in Htype.
        simpl in Htype.
        repeat (rewrite List.nth_error_app2 in Htype; last by (rewrite length_is_size size_take sub_if; lias)).
        repeat rewrite length_is_size size_take sub_if in Htype.
        replace (size ts - 3 + 3 - 2 - (size ts - 3))%coq_nat with 1 in Htype; last by lias.
        replace (size ts - 3 + 3 - 3 - (size ts - 3))%coq_nat with 0 in Htype; last by lias.
        simpl in Htype.
        inversion Htype; subst; clear Htype.
        unfold ct_suffix, to_ct_list in Hs2...
        rewrite size_cat size_take sub_if in H1...
        replace (size ts - 3 + 3 - 2) with (1 + (size ts - 3)) in H1; last by lias.
        rewrite map_cat map_take in H1. simpl in H1.
        rewrite drop_cat in H1.
        repeat rewrite size_take size_map sub_if in H1.
        replace (_ < _) with false in H1; last by lias.
        replace (1+_-_) with 1 in H1; last by lias.
        simpl in H1.
        by auto_rewrite_cond.
    + (* 3 *)
      replace ((length topt).+3-3) with (length topt); last by lias.
      destruct (List.nth_error [::c0, c1 & topt] (length topt)) eqn: Hl2; last by apply List.nth_error_None in Hl2; simpl in Hl2; lias.
      destruct (List.nth_error [::c, c0, c1 & topt] (length topt)) eqn: Hl3; last by apply List.nth_error_None in Hl3; simpl in Hl3; lias.
      assert (exists topts, select_return_top [::c, c0, c1 & topt] c2 c3 = CT_top_type topts) as Htopts.
      { unfold select_return_top.
        destruct c2, c3 => //=; try by eexists.
        replace v with v0 => //=; first by rewrite eq_refl; eexists.
        
        destruct (List.nth_error ts (length ts-2)) eqn:Hts1; last by apply List.nth_error_None in Hts1; rewrite length_is_size in Hts1; lias.
        symmetry in Htype.
        
        replace (length topt) with (length [::c, c0, c1 & topt] - 3) in Hl3; last by lias.
        apply nth_error_ssr with (x0 := v1) in Htype.
        repeat rewrite length_is_size in Htype.
        assert (nth (CTA_some v1) (to_ct_list ts) (size ts - 3) = CTA_some v1) as Hts3ssr.
        { unfold to_ct_list. rewrite -> nth_map with (x1 := v1); last by lias. by rewrite Htype. }
        apply ssr_nth_error in Hts3ssr; last by unfold to_ct_list; rewrite size_map; lias.
        eapply ct_suffix_compat_index with (l2 := to_ct_list ts) in Hl3; eauto; last by rewrite length_is_size; unfold to_ct_list; rewrite size_map; apply Hts3ssr.

        replace (length topt) with (length [::c0, c1 & topt] - 2) in Hl2; last by lias.
        apply nth_error_ssr with (x0 := v1) in Hts1.
        repeat rewrite length_is_size in Hts1.
        assert (nth (CTA_some v1) (to_ct_list ts) (size ts - 2) = CTA_some v1) as Hts2ssr.
        { unfold to_ct_list. rewrite -> nth_map with (x1 := v1); last by lias. by rewrite Hts1. }
        apply ssr_nth_error in Hts2ssr; last by unfold to_ct_list; rewrite size_map; lias.
        eapply ct_suffix_compat_index with (l2 := to_ct_list ts) in Hl2; eauto.
        2: { by apply ct_suffix_prefix with (l1 := [::c]). }
        2: { rewrite length_is_size; unfold to_ct_list; rewrite size_map; apply Hts2ssr. }
        simpl in *.

        by auto_rewrite_cond.
        }
      destruct Htopts as [topts Htopts].
      rewrite Htopts.
      unfold type_update, produce...
      replace (ct_suffix _ _) with true...
      * eapply select_return_top_suffix; eauto.
        simpl.
        by replace (_-_) with (length topt); last by lias.
      * eapply ct_suffix_mutual_suffix with (ts2 := [::c, c0, c1 & topt]) in Hs1; eauto.
        by rewrite ct_suffix_any_grow => //.
Qed.

Lemma c_types_agree_suffix_single: forall l C ts ts2 e,
  c_types_agree (check_single C (CT_type ts) e) ts2 ->
  ct_suffix l (to_ct_list ts) ->
  c_types_agree (check_single C (CT_top_type l) e) ts2.
Proof with auto_rewrite_cond.
  move => l C ts ts2 e.
  move: l C ts ts2.
  induction e; move => topt C ts ts2 H Hsuffix; simpl in H => //=; auto_rewrite_cond; simplify_goal; (try destruct f); (try destruct c); (try by eapply type_update_agree_suffix; eauto) => //=...
  - by apply type_update_select_agree.
  - simplify_goal.
    by eapply type_update_agree_suffix; eauto.
Qed.
    
Lemma c_types_agree_weakening: forall C es ts ts' ts2,
  c_types_agree (check C es (CT_type ts)) ts2 ->
  c_types_agree (check C es (CT_type (ts' ++ ts))) (ts' ++ ts2).
Proof.
  unfold c_types_agree.
  move => C es ts ts' ts2.
  destruct (check C es (CT_type ts)) eqn:Htc => //=; move => H.
  - erewrite check_weaken_top; eauto.
    unfold to_ct_list.
    rewrite map_cat.
    by rewrite ct_suffix_extend.
  - move/eqP in H. subst.
    erewrite check_weaken; by eauto.
Qed.
    
Lemma tc_to_bet_generalized: forall C bes tm ct,
  (match List.fold_left (check_single C) bes ct with
        | CT_top_type ts => ct_suffix ts (to_ct_list tm)
        | CT_type ts => ts == tm
        | CT_bot => false end) = true -> 
  match ct with 
  | CT_type tn => be_typing C bes (Tf tn tm)
  | CT_top_type tn => exists tn', c_types_agree (CT_top_type tn) tn' /\ be_typing C bes (Tf tn' tm)
  | CT_bot => true
  end.
Proof.
  move => C bes. move: C.
  elim: bes => //=.
  - move => C tm ct.
    destruct ct => //=.
    + move => Hsuffix.
      exists tm.
      split => //=.
      by resolve_bet.
    + move => Heq.
      move/eqP in Heq. subst.
      by resolve_bet.
  - move => be bes IH C tm ct Htc.
    apply IH in Htc.
Admitted.
  
Lemma b_e_type_checker_reflects_typing:
  forall C bes tf,
    reflect (be_typing C bes tf) (b_e_type_checker C bes tf).
Proof with auto_rewrite_cond.
  move => C bes tf.
  destruct tf as [tn tm].
  destruct (b_e_type_checker C bes (Tf tn tm)) eqn: Htc_bool.
  - apply ReflectT.
    unfold b_e_type_checker, c_types_agree in Htc_bool.
    by apply tc_to_bet_generalized in Htc_bool.
  - apply ReflectF.
    move => Hbet.
    assert (b_e_type_checker C bes (Tf tn tm)) as H; (try by rewrite H in Htc_bool); clear Htc_bool.
    induction Hbet; subst => //=; unfold type_update => //=...
    + unfold convert_cond...
    + unfold same_lab => //=.
      remember (ins ++ [::i]) as l.
      rewrite - Heql.
      destruct l => //=; first by destruct ins.
      remember H as H2; clear HeqH2.
      move/allP in H2.
      assert (n \in (ins ++ [::i])) as Hn; first by rewrite - Heql; rewrite mem_head.
      apply H2 in Hn.
      move/andP in Hn; destruct Hn as [H3 H4].
      unfold plop2 in H4.
      replace (length (tc_label C) <= n) with false; last by lias.
      move/eqP in H4.
      rewrite H4.
      apply same_lab_h_condition in H.
      replace (ins ++ [::i])%list with (ins ++ [::i]) in H; last by lias.
      rewrite - Heql in H.
      apply same_lab_h_rec in H.
      rewrite H.
      rewrite ct_suffix_suffix...
    + destruct tf as [t1 t2] => //=...
    + destruct (List.nth_error (tc_global C) i) => //=...
    + unfold type_update => //=...
    + unfold type_update => //=...
    + simplify_goal...
    + rewrite List.fold_left_app => //=.
      unfold c_types_agree in IHHbet1.
      destruct (List.fold_left _ es _) eqn:Htc => //=.
      * by eapply c_types_agree_suffix_single; eauto.
      * move/eqP in IHHbet1. by subst.
    + by apply c_types_agree_weakening.
Qed.
      
(*
Lemma wasm_type_checker_reflects_typing:
  forall C cl,
    reflect (cl_typing_self C cl) (cl_type_check C cl).
Proof.
  move => C cl. destruct (cl_type_check C cl) eqn:tc_bool.
  - apply ReflectT. move: tc_bool.
    unfold cl_type_check.
    destruct cl.
    + destruct f.
      unfold b_e_type_checker.
      unfold c_types_agree.
      move: l l0 l1 l2.
      induction l0 => //=.
      -- move => l1 l2 H.
         move/eqP in H; subst.
         unfold cl_typing_self.
         eapply cl_typing_native => //=.
         ++ apply/inst_typeP. by eauto.
         ++ apply bet_empty.
      -- move => l1 l2.
         match goal with
         | |- context C [match ?exp with
                         | CT_top_type _ => _
                         | CT_type _ => _
                         | CT_bot => _ end]
           => destruct exp eqn:HDestruct
                                 end.
      
         admit.
      -- admit.
      -- by [].
    + move => _. by apply cl_typing_host.
  - apply ReflectF. move => tc_prop.
    assert (cl_type_check C cl = true) as HTest; last by rewrite tc_bool in HTest.
    clear tc_bool. 
    
    unfold cl_typing_self in tc_prop.
    inversion tc_prop; subst => //.
    clear H5.
    clear tc_prop.
    
    dependent induction H2; try (inversion Heqtf; subst; clear Heqtf) => //.
    + by apply/eqP.
    + simpl. by rewrite ct_suffix_empty.
    + simpl. by apply/eqP.
    + rewrite upd_label_overwrite in H2. simpl in H2.
      rewrite upd_label_overwrite in IHbe_typing. simpl in IHbe_typing.
      simpl. rewrite upd_label_overwrite.
      
      
      

    
Admitted.
*)
End Host.

