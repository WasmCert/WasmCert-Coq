Require Export wasm wasm_common wasm_numerics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import Bool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive lfilledInd : nat -> lholed -> list administrative_instruction -> list administrative_instruction -> Prop :=
| LfilledBase: forall vs es es',
    const_list vs ->
    lfilledInd 0 (LBase vs es') es (vs ++ es ++ es')
| LfilledRec: forall k vs n es' lh' es'' es LI,
    const_list vs ->
    lfilledInd k lh' es LI ->
    lfilledInd (k.+1) (LRec vs n es' lh' es'') es (vs ++ [ :: (Label n es' LI) ] ++ es'').

Lemma lfilled_Ind_Equivalent: forall k lh es LI,
    lfilled k lh es LI <-> lfilledInd k lh es LI.
Proof.
  move => k. split.
  - move: lh es LI. induction k; move => lh es LI HFix.
    + unfold lfilled in HFix. simpl in HFix. destruct lh.
      * destruct (const_list l) eqn:HConst.
        { replace LI with (l++es++l0). by apply LfilledBase.
          (* TODO: some trivial equalities that should be solvable in one step *)
          admit. }
        { discriminate HFix. }
      * discriminate HFix.
    + unfold lfilled in HFix. simpl in HFix. destruct lh.
      * discriminate HFix.
      * destruct (const_list l) eqn:HConst.
        { destruct (lfill k lh es) eqn:HLF.
          { replace LI with (l ++ [ :: (Label n l0 l2)] ++ l1).
          apply LfilledRec. by [].
          apply IHk. unfold lfilled. rewrite HLF. by [].
          (* TODO: same *)
          admit. }
          discriminate HFix. }
        { discriminate HFix. }
  - move => HLF. induction HLF.
    + unfold lfilled. unfold lfill. rewrite H. by [].
    + unfold lfilled. unfold lfill. rewrite H. fold lfill.
      unfold lfilled in IHHLF. destruct (lfill k lh' es).
      * replace LI with l.
        { by []. }
        (* TODO: same *)
        admit.
      * by [].  
Admitted.  

Lemma const_list_concat: forall vs1 vs2,
    const_list vs1 ->
    const_list vs2 ->
    const_list (vs1 ++ vs2).
Proof.
  move => vs1 vs2. induction vs1.
  - by [].
  - move => H1 H2. simpl in H1. simpl. apply andb_true_iff in H1. destruct H1. rewrite IHvs1. rewrite andbT. by []. by []. by [].
Qed.      

Lemma const_list_take: forall vs l,
    const_list vs ->
    const_list (take l vs).
Proof.
Admitted.
    
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
    { apply LfilledBase. apply const_list_concat.
      - by [].
      - by apply const_list_take. }
    rewrite <- catA. rewrite <- catA. rewrite catA. rewrite catA. replace ((vs0 ++ take (length vs - l) vs) ++ drop (length vs - l) vs) with (vs0 ++ vs).
    { rewrite <- catA. rewrite <- catA. reflexivity. }
    rewrite <- catA. rewrite cat_take_drop. reflexivity.
  - destruct IHHLF as [e He]. auto. eexists (LRec _ _ _ _ _). apply LfilledRec. auto. by eauto.
Qed.

Lemma lfilled_collapse2: forall n lh es es' LI,
    lfilledInd n lh (es++es') LI ->
    exists lh', lfilledInd n lh' es LI.
Proof.
  move => n lh es es' LI HLF. remember (es ++ es') as Ees. induction HLF; subst.
  - eexists (LBase _ _). rewrite <- catA. apply LfilledBase. by [].
  - destruct IHHLF as [x E]. auto. eexists (LRec _ _ _ _ _). apply LfilledRec. by []. by eauto.
Qed.

Lemma lfilled_collapse3: forall k lh n les es LI,
    lfilledInd k lh [:: Label n les es] LI ->
    exists lh', lfilledInd (k+1) lh' es LI.
Proof.
  move => k lh n les es LI HLF. remember [:: Label n les es] as E.  induction HLF; subst.
  - eexists (LRec _ _ _ _ _). apply LfilledRec. auto.
    assert (lfilledInd 0 (LBase nil nil) es ([::] ++ es ++ [::])). apply LfilledBase. by [].
    simpl in H0. rewrite cats0 in H0. by apply H0.
  - destruct IHHLF as [x E]. auto. eexists (LRec _ _ _ _ _). apply LfilledRec. auto. by eauto.
Qed.

Lemma lfilled_deterministic: forall k lh es les les',
    lfilledInd k lh es les ->
    lfilledInd k lh es les' ->
    les = les'.
Proof.
  move => k lh es les les' HLF. move: les'. induction HLF; subst; move => les' HLF'.
  - by inversion HLF'.
  - inversion HLF'; subst.
    replace LI0 with LI. { by []. }
    by apply IHHLF.
Qed.
