(* Lemmas and Tactics for dealing with subtypings *)

From Wasm Require Export operations subtyping properties.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Lemma values_subtyping_cat': forall tx1 tx2 ty1 ty2,
  (tx1 <ts: ty1) ->
  (tx2 <ts: ty2) ->
  (tx1 ++ tx2) <ts: (ty1 ++ ty2).
Proof.
  intros.
  unfold values_subtyping in *.
  rewrite all2_cat => //; first by lias.
  by apply all2_size in H.
Qed.

Lemma values_subtyping_rev: forall ts1 ts2,
    ts1 <ts: ts2 ->
    rev ts1 <ts: rev ts2.
Proof.
  move => ts1 ts2 Hsub.
  by apply all2_rev.
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
  move => [??] => /=; by repeat rewrite values_subtyping_eq.
Qed.

Lemma func_subtyping_trans: forall tf1 tf2 tf3,
    tf1 <tf: tf2 ->
    tf2 <tf: tf3 ->
    tf1 <tf: tf3.
Proof.
  move => [tx1 ty1] [tx2 ty2] [tx3 ty3] => /= /andP [Hsubx21 Hsuby21] /andP [Hsubx32 Hsuby32].
  rewrite (@values_subtyping_trans _ tx2); eauto.
  by rewrite (@values_subtyping_trans _ ty2); eauto.
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

(* All the subtyping relations are preorders *)
#[global]
Instance value_sub_preorder: RelationClasses.PreOrder value_subtyping.
Proof.
  constructor.
  - move => x. by apply value_subtyping_eq.
  - move => ???. by apply value_subtyping_trans.
Qed.

#[global]
Instance values_sub_preorder: RelationClasses.PreOrder values_subtyping.
Proof.
  constructor.
  - move => x. by apply values_subtyping_eq.
  - move => ???. by apply values_subtyping_trans.
Qed.

#[global]
Instance func_sub_preorder: RelationClasses.PreOrder func_subtyping.
Proof.
  constructor.
  - move => x. by apply func_subtyping_eq.
  - move => ???. by apply func_subtyping_trans.
Qed.

#[global]
Instance instr_sub_preorder: RelationClasses.PreOrder instr_subtyping.
Proof.
  constructor.
  - move => x. by apply instr_subtyping_eq.
  - move => x y z. by apply instr_subtyping_trans.
Qed.

Lemma values_subtyping_cat_suffix: forall ts1 ts2 ts3 ts4 tx ty n,
    ts1 ++ ts2 = ts3 ++ ts4 ->
    (tx <ts: ts2) ->
    (drop n ts4 <ts: ty) ->
    size tx = size ty ->
    tx <ts: ty.
Proof.
  intros ??????? Hcat Hsubs1 Hsubs2 Hsize.
  rewrite - (cat_take_drop n ts4) catA in Hcat.
  apply concat_cancel_last_n in Hcat; last first.
  { apply values_subtyping_size in Hsubs1, Hsubs2.
    by lias.
  }
  remove_bools_options; subst.
  by eapply values_subtyping_trans; eauto.
Qed.

(* Any subtyping relation with a non-bot type on the LHS reduces to an equality
as of Wasm 2.0.
*)
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

Lemma value_values_subtyping: forall t1 t2,
    t1 <t: t2 = [::t1] <ts: [::t2].
Proof.
  intros.
  by unfold values_subtyping => /=; lias.
Qed.

(* It is generally a really bad idea to unfold instruction subtyping definition due to its complexity. Instead, it is much better to prove lemmas for any use cases. *)
Lemma instr_subtyping_empty_impl: forall ts1 ts2,
    ts1 <ts: ts2 ->
    (Tf nil nil <ti: Tf ts1 ts2).
Proof.
  intros.
  exists ts1, ts2, nil, nil.
  by repeat rewrite cats0.
Qed.

Lemma instr_subtyping_empty_impl': forall ts1 ts2,
    (Tf nil nil <ti: Tf ts1 ts2) -> 
    ts1 <ts: ts2.
Proof.
  intros.
  unfold instr_subtyping in H.
  destruct H as [ts [ts' [sub1 [sub2 [-> [-> [Hsub1 [Hsub2 Hsub3]]]]]]]].
  destruct sub1, sub2 => //.
  by repeat rewrite cats0.
Qed.

Lemma instr_subtyping_empty1_impl: forall ts ts1 ts2,
    ((ts1 ++ ts) <ts: ts2) ->
    (Tf nil ts <ti: Tf ts1 ts2).
Proof.
  intros.
  apply values_subtyping_split2 in H; remove_bools_options.
  exists ts1, (take (size ts1) ts2), nil, (drop (size ts1) ts2).
  rewrite cats0.
  repeat split => //.
  by rewrite cat_take_drop.
Qed.

Lemma instr_subtyping_empty1_impl': forall ts ts1 ts2,
    (Tf nil ts <ti: Tf ts1 ts2) ->
    ((ts1 ++ ts) <ts: ts2).
Proof.
  intros.
  unfold instr_subtyping in H.
  destruct H as [ts0 [ts' [sub1 [sub2 [-> [-> [Hsub1 [Hsub2 Hsub3]]]]]]]].
  destruct sub1 => //.
  rewrite cats0.
  rewrite values_subtyping_cat; first by lias.
  by apply all2_size in Hsub1.
Qed.

Lemma values_subtyping_weaken: forall ts1 ts2 ts,
    (ts1 <ts: ts2) ->
    ((ts ++ ts1) <ts: (ts ++ ts2)).
Proof.
  intros.
  rewrite values_subtyping_cat => //.
  rewrite H.
  by rewrite values_subtyping_eq.
Qed.

Lemma values_subtyping_take: forall ts1 ts2 n,
    (ts1 <ts: ts2) ->
    (take n ts1 <ts: take n ts2).
Proof.
  intros.
  unfold values_subtyping.
  by rewrite all2_take.
Qed.

Lemma values_subtyping_drop: forall ts1 ts2 n,
    (ts1 <ts: ts2) ->
    (drop n ts1 <ts: drop n ts2).
Proof.
  intros.
  unfold values_subtyping.
  by rewrite all2_drop.
Qed.

Lemma instr_subtyping_weaken: forall ts1 ts2 ts3 ts4 ts,
    (Tf ts1 ts2 <ti: Tf ts3 ts4) ->
    (Tf ts1 ts2 <ti: Tf (ts ++ ts3) (ts ++ ts4)).
Proof.
  intros; unfold instr_subtyping in *.
  destruct H as [ts0 [ts' [sub1 [sub2 [-> [-> [Hsub1 [Hsub2 Hsub3]]]]]]]].
  exists (ts ++ ts0), (ts ++ ts'), sub1, sub2; repeat split => //; try by rewrite catA.
  by apply values_subtyping_weaken.
Qed.

Lemma instr_subtyping_weaken1: forall tx1 ty1 tx2 ty2 ts,
    ((Tf tx1 ty1) <ti: (Tf tx2 ty2)) ->
    (tx1 <ts: ts) ->
    ((Tf ts ty1) <ti: (Tf tx2 ty2)).
Proof.
  intros.
  unfold instr_subtyping in *.
  destruct H as [ts0 [ts' [ts1_s [ts2_s [-> [-> [Hsub1 [Hsub2 Hsub3]]]]]]]].
  exists ts0, ts', ts1_s, ts2_s.
  repeat split => //; by eapply values_subtyping_trans; eauto.
Qed.

Lemma instr_subtyping_weaken2: forall tx1 ty1 tx2 ty2 ts,
    ((Tf tx1 ty1) <ti: (Tf tx2 ty2)) ->
    (ty2 <ts: ts) ->
    ((Tf tx1 ty1) <ti: (Tf tx2 ts)).
Proof.
  intros ?????? Hsub.
  unfold instr_subtyping in *.
  destruct H as [ts0 [ts' [ts1_s [ts2_s [-> [-> [Hsub1 [Hsub2 Hsub3]]]]]]]].
  apply values_subtyping_split2 in Hsub; remove_bools_options.
  exists ts0, (take (size ts') ts), ts1_s, (drop (size ts') ts); rewrite cat_take_drop.
  repeat split => //; by eapply values_subtyping_trans; eauto.
Qed.

Lemma instr_subtyping_strengthen1: forall tx1 ty1 tx2 ty2 ts,
    ((Tf tx1 ty1) <ti: (Tf tx2 ty2)) ->
    (ts <ts: ty1) ->
    ((Tf tx1 ts) <ti: (Tf tx2 ty2)).
Proof.
  intros.
  unfold instr_subtyping in *.
  destruct H as [ts0 [ts' [ts1_s [ts2_s [-> [-> [Hsub1 [Hsub2 Hsub3]]]]]]]].
  exists ts0, ts', ts1_s, ts2_s.
  repeat split => //; by eapply values_subtyping_trans; eauto.
Qed.

Lemma instr_subtyping_strengthen2: forall tx1 ty1 tx2 ty2 ts,
    ((Tf tx1 ty1) <ti: (Tf tx2 ty2)) ->
    (ts <ts: tx2) ->
    ((Tf tx1 ty1) <ti: (Tf ts ty2)).
Proof.
  intros ?????? Hsub.
  unfold instr_subtyping in *.
  destruct H as [ts0 [ts' [ts1_s [ts2_s [-> [-> [Hsub1 [Hsub2 Hsub3]]]]]]]].
  apply values_subtyping_split1 in Hsub; remove_bools_options.
  exists (take (size ts0) ts), ts', (drop (size ts0) ts), ts2_s; rewrite cat_take_drop.
  repeat split => //; by eapply values_subtyping_trans; eauto.
Qed.

  
(* Trying to resolve subtyping goals in a non-breaking way. A different tactic is provided below that performs more destructive unfolds on instr and func subtyping relations. *)
Ltac resolve_subtyping :=
  repeat match goal with
  (* Simple cleaning and rewriting *)
  | H: is_true ?b |-
      context [ ?b ] =>
      rewrite H => /=
  | H: is_true true |- _ => clear H
  | H: ?x = ?x |- _ => clear H
  | H: is_true (_ && true) |- _ => move/andP in H; destruct H as [H _]
  | |- context [_ && true] => rewrite Bool.andb_true_r

  (* Instruction subtyping with nils *)
  | |- (Tf nil nil <ti: Tf ?ts1 ?ts2) =>
    apply instr_subtyping_empty_impl
  | H: Tf nil nil <ti: Tf ?ts1 ?ts2 |- _ =>
    apply instr_subtyping_empty_impl' in H

  (* Resolving top-level types. Need to be changed when a supremum type is introduced in future proposals *)
  | H: is_true (T_num ?t <t: ?t') |- _ =>
    apply num_subtyping in H => //; subst
  | H: is_true (T_vec ?t <t: ?t') |- _ =>
    apply vec_subtyping in H => //; subst
  | H: is_true (T_ref ?t <t: ?t') |- _ =>
    apply ref_subtyping in H => //; subst

  | H: T_num ?t1 = T_num ?t2 |- _ =>
    inversion H; subst; clear H
                                
  | H: T_vec ?t1 = T_vec ?t2 |- _ =>
    inversion H; subst; clear H
                                
  | H: T_ref ?t1 = T_ref ?t2 |- _ =>
    inversion H; subst; clear H

  (* subtyping of empty *)
  | H: is_true (?ts <ts: nil) |- _ =>
      destruct ts => //; clear H
  | H: is_true (nil <ts: ?ts) |- _ =>
      destruct ts => //; clear H

  (* subtyping of take/drop *)
  | H: is_true (?ts1 <ts: ?t2) |-
      context [ take ?n ?ts1 <ts: take ?n ?ts2 ] =>
      rewrite (values_subtyping_take n H) => //
                                              
  | H: is_true (?ts1 <ts: ?t2) |-
      context [ drop ?n ?ts1 <ts: drop ?n ?ts2 ] =>
      rewrite (values_subtyping_drop n H) => //
                        
  (* singleton list subtyping *)
  | H: is_true ([::?t1] <ts: [::?t2]) |- _ =>
      rewrite - value_values_subtyping in H
      
  (* Reflexivity *)
  | |- context [ ?t <t: ?t ] =>
      rewrite value_subtyping_eq => //
                                     
  | |- context [ ?ts <ts: ?ts ] =>
    rewrite values_subtyping_eq => //
  | |- context [(?ts1 ++ ?ts2) <ts: (?ts1 ++ ?ts2')] =>
      erewrite values_subtyping_cat; (try reflexivity); eauto => //
  | _: is_true (?ts1 <ts: ?ts1') |-
      context [(?ts1 ++ ?ts2) <ts: (?ts1' ++ ?ts2')] =>
      erewrite values_subtyping_cat; eauto => //; last by apply values_subtyping_size
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

  (* Certain composite implications *)
  | H1: is_true (?ts1 <ts: take ?n ?ts2),
    H2: is_true (?ts2 <ts: ?ts3) |-
        context [?ts1 <ts: take ?n ?ts3] =>
    rewrite (values_subtyping_trans H1 (values_subtyping_take n H2))
  | H1: is_true (?ts1 <ts: drop ?n ?ts2),
    H2: is_true (?ts2 <ts: ?ts3) |-
        context [?ts1 <ts: drop ?n ?ts3] =>
    rewrite (values_subtyping_trans H1 (values_subtyping_drop n H2))
      
  (* proving singleton list subtyping *)
  | H: is_true (?t1 <t: ?t2) |-
      context [[::?t1] <ts: [::?t2]] =>
      rewrite - (value_values_subtyping t1 t2)
              
  | H: is_true (?t1 <t: ?t2) |-
      context [is_true ([::?t1] <ts: [::?t2])] =>
      rewrite - (value_values_subtyping t1 t2)

  (* Strengthening and weakening *)
  | H: is_true (?t1 <t: ?t2) |-
      (Tf [::?t2] _ <ti: Tf [::?t1] _) =>
      apply instr_subtyping_weaken1 with (tx1 := [::t1]) => //
  | H: is_true (?t1 <t: ?t2) |-
      (Tf _ [::?t1] <ti: Tf _ [::?t2]) =>
      apply instr_subtyping_strengthen1 with (ty1 := [::t2]) => //
                                                            
  | H: is_true (?ts1 <ts: ?ts2) |-
      (Tf ?ts2 _ <ti: Tf ?ts1 _) =>
      apply instr_subtyping_weaken1 with (tx1 := ts1) => // 
  | H: is_true (?ts1 <ts: ?ts2) |-
      (Tf _ ?ts1 <ti: Tf _ ?ts2) =>
      apply instr_subtyping_strengthen1 with (ty1 := ts2) => //

  (* cat *)
  | H1: is_true (?ts1 <ts: ?ts2),
    H2: is_true (?ts1' <ts: ?ts2') |-
      context [(?ts1 ++ ?ts1') <ts: (?ts2 ++ ?ts2')] =>
      rewrite (values_subtyping_cat' H1 H2)
              
  (* reverse *)
  | H: is_true (?ts1 <ts: ?ts2) |-
      context [(rev ?ts1) <ts: (rev ?ts2)] =>
      rewrite (values_subtyping_rev H)
              
  | _ => try by []
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

(* Only use this tactic if desperate *)
Ltac simplify_subtyping :=
  repeat match goal with
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

Lemma instr_subtyping_size_bound: forall ts1 ts2 ts3 ts4,
    (Tf ts1 ts2 <ti: Tf ts3 ts4) ->
    size ts1 <= size ts3 /\ size ts2 <= size ts4.
Proof.
  intros.
  simplify_subtyping.
  apply values_subtyping_size in Hconjl2.
  apply values_subtyping_size in Hconjr0.
  repeat rewrite size_cat.
  by lias.
Qed.

Lemma instr_subtyping_size_exact: forall ts1 ts2 ts3 ts4,
    (Tf ts1 ts2 <ti: Tf ts3 ts4) ->
    size ts1 + size ts4 = size ts2 + size ts3.
Proof.
  intros.
  simplify_subtyping.
  apply values_subtyping_size in Hconjl1.
  apply values_subtyping_size in Hconjl2.
  apply values_subtyping_size in Hconjr0.
  repeat rewrite size_cat.
  by lias.
Qed.

Lemma instr_subtyping_consumed_rev_prefix: forall ts1 ts2 ts3 ts4,
    (Tf ts1 ts2 <ti: Tf ts3 ts4) ->
    exists ts_prefix, rev ts3 = (ts_prefix ++ (drop (size ts1) (rev ts3))) /\
              (ts_prefix <ts: rev ts1).
Proof.
  move => ts1 ts2 ts3 ts4 Htisub.
  exists (take (size ts1) (rev ts3)); split; first by rewrite cat_take_drop.
  simplify_subtyping.
  rewrite rev_cat.
  rewrite take_size_cat; last by rewrite size_rev; apply values_subtyping_size in Hconjl2.
  by apply all2_rev.
Qed.

Lemma instr_subtyping_produced_suffix: forall ts1 ts2 ts3 ts4,
    (Tf ts1 ts2 <ti: Tf ts3 ts4) ->
    exists ts_suffix, ts4 = ((take (size ts4 - size ts2) ts4) ++ ts_suffix) /\
              (ts2 <ts: ts_suffix).
Proof.
  move => ts1 ts2 ts3 ts4 Htisub.
  exists (drop (size ts4 - size ts2) ts4); split; first by rewrite cat_take_drop.
  simplify_subtyping.
  rewrite drop_size_cat => //.
  rewrite size_cat.
  rewrite (values_subtyping_size Hconjr0).
  by lias.
Qed.

Lemma instr_subtyping_suffix_prod_cons: forall ts1 ts2 ts3 ts4 ts5 ts6 ts ts',
    Tf ts1 ts <ti: Tf ts2 ts3 ->
    Tf (ts4 ++ ts') ts5 <ti: Tf ts3 ts6 ->
    size ts = size ts' ->
    ts <ts: ts'.                     
Proof.
  intros ???????? Hsub1 Hsub2 Hlen.
  simplify_subtyping.
  by eapply values_subtyping_cat_suffix; eauto.
Qed.
  
(*
Given a subtype of (tx -> ty) and a subtype of (ty -> tz),
try to figure out the relations that have to be satisfied by the subtypes and
simplify for premises.
*)
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
    | _ => idtac
    end; try (move: Hprincipal; rewrite (lock instr_subtyping) /= -lock; move => Hprincipal)
  | |- is_true (size _ <= size _) =>
    try by repeat rewrite size_cat; lias
  end.


Section Host.

Context {hfc: host_function_class} `{memory: Memory}.
  
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

Lemma value_num_principal_typing: forall s v,
    value_typing s (VAL_num v) (T_num (typeof_num v)).
Proof.
  move => s v.
  unfold value_typing => /=.
  by resolve_subtyping.
Qed.

Lemma value_vec_principal_typing: forall s v,
    value_typing s (VAL_vec v) (T_vec (typeof_vec v)).
Proof.
  move => s v.
  unfold value_typing => /=.
  by resolve_subtyping.
Qed.

Lemma value_ref_principal_typing: forall s v t,
    typeof_ref s v = Some t ->
    value_typing s (VAL_ref v) (T_ref t).
Proof.
  move => s v t.
  unfold typeof_ref, value_typing; destruct v => /=; move => H; remove_bools_options => /=; by resolve_subtyping.
Qed.

Lemma value_typing_trans: forall s v t t',
    value_typing s v t ->
    t <t: t' ->
    value_typing s v t'.
Proof.
  unfold value_typing.
  move => s v t t' Hvaltype Hsub; remove_bools_options.
  by resolve_subtyping.
Qed.

Lemma values_typing_trans: forall s vs ts1 ts2,
    values_typing s vs ts1 ->
    ts1 <ts: ts2 ->
    values_typing s vs ts2.
Proof.
  intros s vs ts1 ts2 Hvt Hsub.
  unfold values_typing in *.
  apply all2_spec; first by apply values_subtyping_size in Hsub; apply all2_size in Hvt; lias.
  move => n v vt Hnth1 Hnth2.
  eapply all2_nth_impl in Hvt; eauto.
  destruct Hvt as [vt' [Hnth3 Hvt']].
  eapply all2_projection in Hsub; eauto.
  by eapply value_typing_trans; eauto.
Qed.

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

(* Instances for value elimination tactic used in interpreter *)
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

End Host.

Ltac resolve_value_principal_typing :=
  repeat match goal with
  | |- is_true (value_typing ?s (VAL_num ?v) ?t) =>
      try by apply value_num_principal_typing
  | |- is_true (value_typing ?s (VAL_vec ?v) ?t) =>
      try by apply value_vec_principal_typing
  | H: typeof_ref ?s ?v = Some ?tref
    |- is_true (value_typing ?s (VAL_ref ?v) ?t) =>
      try by apply (value_ref_principal_typing H)
  | H: is_true (value_typing ?s ?v ?t),
      Hsub: is_true (?t <t: ?t') |-
      context [value_typing ?s ?v ?t'] =>
      erewrite (value_typing_trans H Hsub); eauto => //=
  end.

(* Given a value type, destruct it and the subcases as well. *)
Ltac destruct_value_type t :=
  destruct t as [ [ | | | ] | [] | [ | ] | ].

(* DESTRUCT ALL VALUE TYPES TO THE OBLIVION *)
Ltac total_destruction :=
  repeat match goal with
    | v: value_type |- _ =>
        destruct_value_type v => //=
    end.

Section Lattice_properties.
  
  (* Properties of inf and sup *)
  Lemma t_inf_comm t1 t2:
    t_inf t1 t2 = t_inf t2 t1.
  Proof.
    by total_destruction.
  Qed.
  
  Lemma t_inf_sub t1 t2 tinf:
    tinf = t_inf t1 t2 ->
    tinf <t: t1.
  Proof.
    by total_destruction.
  Qed.

  Lemma t_inf_strict t1 t2 t3:
    t3 <t: t1 ->
    t3 <t: t2 ->
    t3 <t: t_inf t1 t2.
  Proof.
    by total_destruction.
  Qed.
  
  Lemma t_sup_comm t1 t2:
    t_sup t1 t2 = t_sup t2 t1.
  Proof.
    by total_destruction.
  Qed.
  
  Lemma t_sup_sub t1 t2 tsup:
    t_sup t1 t2 = Some tsup ->
    t1 <t: tsup.
  Proof.
    by total_destruction.
  Qed.

  Lemma t_sup_strict t1 t2 t3:
    t1 <t: t3 ->
    t2 <t: t3 ->
    exists tsup, t_sup t1 t2 = Some tsup /\
    tsup <t: t3.
  Proof.
    total_destruction; by eexists.
  Qed.

  Lemma ts_inf_length ts1 ts2 tsinf:
    ts_inf ts1 ts2 = Some tsinf ->
    length ts1 = length ts2.
  Proof.
    move: ts2; induction ts1; destruct ts2 => //=.
    move => Hlen.
    unfold ts_inf in *.
    remove_bools_options.
    by lias.
  Qed.
  
  Lemma ts_inf_comm ts1 ts2:
    ts_inf ts1 ts2 = ts_inf ts2 ts1.
  Proof.
    move: ts2; induction ts1; destruct ts2 => //=.
    unfold ts_inf.
    unfold ts_inf in IHts1.
    specialize (IHts1 ts2).
    rewrite eq_sym.
    rewrite eq_sym in IHts1.
    destruct (length _ == length _) eqn:Hlen => //=.
    rewrite t_inf_comm.
    do 2 f_equal.
    by injection IHts1.
  Qed.
  
  Lemma ts_inf_sub ts1 ts2 tsinf:
    ts_inf ts1 ts2 = Some tsinf ->
    tsinf <ts: ts1.
  Proof.
    unfold ts_inf.
    destruct (length _ == length _) eqn:Hlen => //=.
    move => [Hmap]; subst.
    move: ts2 Hlen.
    induction ts1; destruct ts2 => //=.
    move => Hlen.
    move/eqP in Hlen; injection Hlen as Hlen.
    specialize (IHts1 ts2).
    rewrite Hlen eq_refl in IHts1.
    specialize (IHts1 Logic.eq_refl).
    apply/andP; split => //.
    by eapply t_inf_sub; eauto.
  Qed.

  Lemma ts_inf_exists ts1 ts2 ts3:
    ts3 <ts: ts1 ->
    ts3 <ts: ts2 ->
    exists tsinf, ts_inf ts1 ts2 = Some tsinf.
  Proof.
    move : ts2 ts3.
    induction ts1; destruct ts2, ts3 => //=; intros; remove_bools_options.
    - by exists nil => //.
    - specialize (IHts1 ts2 ts3 H2 H1) as [tsinf Hinfeq].
      exists ((t_inf a v) :: tsinf) => /=.
      unfold ts_inf in * => /=.
      remove_bools_options.
      move/eqP in Hif.
      by rewrite Hif eq_refl.
  Qed.

  Lemma ts_inf_strict ts1 ts2 ts3 tsinf:
    ts3 <ts: ts1 ->
    ts3 <ts: ts2 ->
    ts_inf ts1 ts2 = Some tsinf ->
    ts3 <ts: tsinf.
  Proof.
    move : ts2 ts3 tsinf.
    induction ts1; destruct ts2, ts3, tsinf => //=; intros; unfold ts_inf in *; remove_bools_options.
    move/eqP in Hif; simpl in Hif; injection Hif as Hif.
    apply/andP; split; first by apply t_inf_strict.
    eapply (IHts1 ts2 ts3); eauto.
    by rewrite Hif eq_refl.
  Qed.
    
End Lattice_properties.
