Require Export wasm typing.
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

Lemma const_list_take: forall vs l,
    const_list vs ->
    const_list (take l vs).
Proof.
  move => vs. induction vs => //=.
  - move => l HConst. destruct l => //=.
    + simpl. simpl in HConst. apply andb_true_iff in HConst. destruct HConst.
      apply andb_true_iff. split => //. by apply IHvs.
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
