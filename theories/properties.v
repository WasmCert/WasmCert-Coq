(** Miscellaneous properties about Wasm operations **)
(* (C) Rao Xiaojia - see LICENSE.txt *)

Require Export operations typing opsem interpreter.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import Bool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

(* Check with Martin for split_vals *)
Lemma split_vals_e_v_to_e_duality: forall es vs es',
    split_vals_e es = (vs, es') ->
    es = (v_to_e_list vs) ++ es'.
Proof.
  move => es vs. move: es. elim: vs => //.
  - unfold split_vals_e. destruct es => //=.
    + move => es' H. by inversion H.
    + move => es'.
      case a; try by inversion 1; [idtac]. move => b. case b; try by inversion 1.
      (* ask *)
      fold split_vals_e. move => v H.
      by destruct (split_vals_e es).
  - move => a l H es es' HSplit. unfold split_vals_e in HSplit.
    destruct es => //. destruct a0 => //. destruct b => //. fold split_vals_e in HSplit.
    destruct (split_vals_e es) eqn:Heqn. inversion HSplit; subst.
    simpl. f_equal. by auto.
Qed.

(* Check with Martin for split_n: it's just take+drop *)
Lemma split_n_is_take_drop: forall es n,
    split_n es n = (take n es, drop n es).
Proof.
  move => es n. move: es. elim:n => //=.
  - move => es. by destruct es.
  - move => n IH es'. destruct es' => //=.
    + by rewrite IH.
Qed.

(* Ask Martin *)
Lemma update_list_at_is_set_nth: forall {X:Type} (l:list X) n x,
    n < size l ->
    set_nth x l n x = update_list_at l n x.
Proof.
  move => X l n x. move: n. elim: l => //=.
  move => a l IH n HLen. destruct n => //=.
  unfold update_list_at. simpl. f_equal. by apply IH.
Qed.

(* Check with Martin: size is the standard function used in ssreflect.seq; should we
   change all occurrences of length to size instead? *)
Lemma length_is_size: forall {X:Type} (l: list X),
    length l = size l.
Proof.
  move => X l. by elim: l.
Qed.

(* Very interestingly, the following lemma has EXACTLY the same proof as the
   lemma split_n_is_take_drop, although they are not related at all! *)
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

Lemma to_b_list_concat: forall es1 es2,
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

Lemma to_b_list_rev: forall es,
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

Lemma lfilled_collapse1: forall n lh vs es LI l,
    lfilledInd n lh (vs++es) LI ->
    const_list vs ->
    length vs >= l ->
    exists lh', lfilledInd n lh' ((drop (length vs-l) vs) ++ es) LI.
Proof.
  move => n lh vs es LI l HLF HConst HLen.
  (* Comparing this proof to the original proof in Isabelle, it seems that (induction X rule: Y) in Isabelle means induction on proposition Y remembering X (in Coq). *)
  remember (vs++es) as es'. induction HLF; subst.
  - exists (LBase (vs0 ++ (take (length vs - l) vs)) es').
    (* The proof to this case should really have finished here; the below is just rearranging brackets and applying cat_take_drop and assumptions. *)
    replace (vs0++(vs++es)++es') with ((vs0++take (length vs - l) vs) ++ (drop (length vs - l) vs ++ es) ++ es').
    { apply LfilledBase. apply const_list_concat => //=.
      by apply const_list_take. }
    repeat rewrite -catA. f_equal.
    repeat rewrite catA. do 2 f_equal.
    by apply cat_take_drop. 
  - destruct IHHLF => //. eexists (LRec _ _ _ _ _). apply LfilledRec => //. by apply H0.
Qed.

Lemma lfilled_collapse2: forall n lh es es' LI,
    lfilledInd n lh (es++es') LI ->
    exists lh', lfilledInd n lh' es LI.
Proof.
  move => n lh es es' LI HLF. remember (es ++ es') as Ees. induction HLF; subst.
  - eexists (LBase _ _). rewrite <- catA. by apply LfilledBase.
  - destruct IHHLF => //. eexists (LRec _ _ _ _ _). apply LfilledRec => //. by apply H0.
Qed.

Lemma lfilled_collapse3: forall k lh n les es LI,
    lfilledInd k lh [:: Label n les es] LI ->
    exists lh', lfilledInd (k+1) lh' es LI.
Proof.
  move => k lh n les es LI HLF. remember [:: Label n les es] as E.  induction HLF; subst.
  - eexists (LRec _ _ _ _ _). apply LfilledRec. auto.
    assert (lfilledInd 0 (LBase nil nil) es ([::] ++ es ++ [::])). { by apply LfilledBase. }
    simpl in H0. rewrite cats0 in H0. by apply H0.
  - destruct IHHLF => //. eexists (LRec _ _ _ _ _). apply LfilledRec => //. by apply H0.
Qed.

Lemma lfilled_deterministic: forall k lh es les les',
    lfilledInd k lh es les ->
    lfilledInd k lh es les' ->
    les = les'.
Proof.
  move => k lh es les les' HLF HLF'.
  apply lfilled_Ind_Equivalent in HLF. unfold lfilled in HLF.
  apply lfilled_Ind_Equivalent in HLF'. unfold lfilled in HLF'.
  destruct (lfill k lh es) => //.
  replace les' with l.
  { move: HLF. by apply/eqseqP. }
  symmetry. move: HLF'. by apply/eqseqP. 
Qed.  
