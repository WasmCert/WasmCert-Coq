From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap proph_map.
Require Export iris iris_locations stdpp_aux.
Require Export datatypes operations properties opsem.

Ltac false_assumption := exfalso ; apply ssrbool.not_false_is_true ; assumption.

Lemma found_intruse l1 l2 (x : administrative_instruction) :
  l1 = l2 -> (In x l1 -> False) -> In x l2 -> False.
Proof.
  intros. rewrite H in H0. apply H0 ; exact H1.
Qed.

(* If H is a hypothesis that states the equality between 2 lists, attempts to prove
   False by showing object x is in the rhs of H, but not in the lhs.
   If attempt fails, user is given a hypothesis Hxl1 to end proof manually *)
Ltac found_intruse x H Hxl1 :=
  exfalso ; 
  apply (found_intruse _ _ x H) ;
  [intro Hxl1 ; repeat ((destruct Hxl1 as [Hxl1 | Hxl1] ; [ inversion Hxl1 |]) +
                          assumption  ) |
    try by (apply in_or_app ; right ; left ; trivial) ].



(* Attempts to prove False from hypothesis H, which states that an lholed is filled
   with AI_trap. If attempt fails, user is given a hypothesis Hxl1 to end proof manually *)
Ltac filled_trap H Hxl1 :=
  exfalso ;
  unfold lfilled, lfill in H ;
  destruct (_:lholed) in H ; [|false_assumption] ;
  destruct (const_list _) in H ; [|false_assumption] ;
  move/eqP in H ; found_intruse AI_trap H Hxl1.

(* Given hypothesis H, which states that an lholed lh is filled at level k, 
   unfolds the definition of lfilled. Attempts to prove a contradiction when k > 0.
   If attempts fail, user is given that filled expression is 
   vs ++ (AI_label n l1 l3) :: l0 *)
Ltac simple_filled H k lh vs l0 n l1 l3 :=
  let l2 := fresh "l" in
  let lh' := fresh "lh" in
  let Hxl1 := fresh "Hxl1" in
  let les := fresh "les" in
  let Hvs := fresh "Hvs" in
  unfold lfilled, lfill in H ;
  destruct k ;
  [ destruct lh as [vs l0|] ; [| false_assumption] ;
    destruct (const_list vs) eqn:Hvs ; [| false_assumption] ; move/eqP in H |
    fold lfill in H ; destruct lh as [|vs n l1 lh' l2] ; [false_assumption |] ;
    destruct (const_list vs) eqn:Hvs ; [| false_assumption ] ;
    remember (lfill k lh' _) as les ;
    destruct les as [l3|] ; [| false_assumption ] ;
    move/eqP in H ; found_intruse (AI_label n l1 l3) H Hxl1].

(* Like simple_filled, but does not attempt to solve case k > 0 *)
Ltac simple_filled2 H k lh vs l0 n l1 l3 :=
  let l2 := fresh "l" in
  let lh' := fresh "lh" in
  let Hxl1 := fresh "Hxl1" in
  let les := fresh "les" in
  let Hvs := fresh "Hvs" in
  unfold lfilled, lfill in H ;
  destruct k ;
  [ destruct lh as [vs l0|] ; [| false_assumption] ;
    destruct (const_list vs) eqn:Hvs ; [| false_assumption] ; move/eqP in H |
    fold lfill in H ; destruct lh as [|vs n l1 lh' l2] ; [false_assumption |] ;
    destruct (const_list vs) eqn:Hvs ; [| false_assumption ] ;
    remember (lfill k lh' _) as les ;
    destruct les as [l3|] ; [| false_assumption ] ;
    move/eqP in H ; try by found_intruse (AI_label n l1 l3) H Hxl1].

Global Instance ai_list_eq_dec: EqDecision (seq.seq administrative_instruction).
Proof.
  apply list_eq_dec.
Defined.
Global Instance ai_eq_dec: EqDecision (administrative_instruction).
Proof.
  pose proof administrative_instruction_eq_dec. eauto.
Defined.

Lemma ai_eq_true a a0 : administrative_instruction_eqb a a0 = true <-> a = a0.
Proof.
  split; by move/eqP.
Qed.

Lemma ai_eqseq_true (l1 l2 : seq.seq administrative_instruction) :
  l1 = l2 <-> (l1 == l2) = true.
Proof.
  split; by move/eqP.
Qed.


Section lfilled_properties.

  Fixpoint base_is_empty lh :=
    match lh with
    | LH_base bef aft => bef = [] /\ aft = []
    | LH_rec _ _ _ lh _ => base_is_empty lh
    end.

  Fixpoint empty_base lh :=
    match lh with
    | LH_base bef aft => (LH_base [] [], LH_base bef aft)
    | LH_rec a b c lh d => let '( lh', lh0) := empty_base lh in
                          (LH_rec a b c lh' d, lh0)
    end.

  Fixpoint get_layer lh i :=
    match lh,i with
    | LH_base vs es, _ => None
    | LH_rec vs' n es lh' es', 0 => Some (vs',n,es,lh',es')
    | LH_rec _ _ _ lh' _, S n => get_layer lh' n
    end.

  Definition delete_outer lh :=
    match lh with
    | LH_base _ _ => lh
    | LH_rec vs n es lh es' => lh
    end.

  Definition lh_delete_inner lh :=
    let '(lh',_) := empty_base lh in lh'.

  Fixpoint sh_pull_const_r sh vs :=
    match sh with
    | SH_base bef aft  => SH_base (bef ++ vs) aft 
    | SH_rec bef n es sh aft => SH_rec bef n es (sh_pull_const_r sh vs) aft
    end.

  Fixpoint lh_pull_const_r lh vs :=
    match lh with
    | LH_base bef aft  => LH_base (bef ++ vs) aft 
    | LH_rec bef n es sh aft => LH_rec bef n es (lh_pull_const_r sh vs) aft
    end.
  
  Inductive lh_minus_Ind : lholed -> lholed -> lholed -> Prop :=
  | lh_minus_base lh : lh_minus_Ind lh (LH_base [] []) lh
  | lh_minus_ind lh lh' lh'' vs n es es' :
    lh_minus_Ind lh lh' lh'' ->
    lh_minus_Ind (LH_rec vs n es lh es') (LH_rec vs n es lh' es') lh''.

  Lemma to_e_list_fmap l :
    fmap (fun v => AI_basic (BI_const v)) l = v_to_e_list l.
  Proof.
    induction l;auto.
  Qed.

  Lemma can_empty_base k lh es LI lh' lh0 :
    empty_base lh = (lh', lh0) -> 
    lfilled k lh es LI ->
    exists es', lfilled 0 lh0 es es' /\ lfilled k lh' es' LI /\ base_is_empty lh'.
  Proof.
    generalize dependent lh. generalize dependent LI. generalize dependent lh'.
    generalize dependent lh0.
    induction k ; intros lh0 lh' LI lh Hempty Hfill.
    - unfold lfilled, lfill in Hfill.
      destruct lh as [bef aft |] ; last by false_assumption.
      destruct (const_list bef) eqn:Hbef ; last by false_assumption.
      inversion Hempty.
      subst.    
      move/eqP in Hfill.
      exists (bef ++ es ++ aft).
      repeat split => //=.
      unfold lfilled, lfill ; rewrite Hbef => //=.
      unfold lfilled, lfill ; rewrite app_nil_r Hfill => //=. 
    - unfold lfilled, lfill in Hfill.
      fold lfill in Hfill.
      destruct lh ; first by false_assumption.
      destruct (empty_base lh) eqn:Hlh.
      simpl in Hempty.
      rewrite Hlh in Hempty.
      inversion Hempty ; subst ; clear Hempty.
      destruct (const_list l) eqn:Hl ; last by false_assumption.
      destruct (lfill k lh es) eqn:Hfill' ; last by false_assumption.
      move/eqP in Hfill.
      assert (lfilled k lh es l3) ; first by unfold lfilled ; rewrite Hfill'.
      eapply IHk in H ; last done.
      destruct H as (es' & Hfill0 & Hfill1 & Hempty).
      exists es'.
      repeat split => //=.
      unfold lfilled, lfill ; fold lfill.
      rewrite Hl.
      unfold lfilled in Hfill1.
      destruct (lfill _ l2 _) eqn:Hl2 ; last by false_assumption.
      move/eqP in Hfill1.
      by subst.
  Qed.
  

  Lemma can_fill_base k lh es es' LI lh' lh0 :
    empty_base lh = (lh', lh0) ->
    lfilled 0 lh0 es es' -> lfilled k lh' es' LI -> lfilled k lh es LI.
  Proof.
    generalize dependent LI ; generalize dependent k.
    generalize dependent lh' ; generalize dependent lh0.
    induction lh ; intros lh0 lh' k LI Hempty ; simpl.
    { inversion Hempty ; subst.
      intros Hfill0 Hfill.
      unfold lfilled, lfill in Hfill.
      destruct k ; last by false_assumption.
      simpl in Hfill.
      move/eqP in Hfill.
      unfold lfilled, lfill in Hfill0.
      unfold lfilled, lfill.
      destruct (const_list l) ; last by false_assumption.
      move/eqP in Hfill0.
      subst.
      by rewrite app_nil_r. }
    destruct (empty_base lh) eqn:Hlh.
    simpl in Hempty.
    rewrite Hlh in Hempty.
    inversion Hempty ; subst.
    intros Hfill0 Hfill.
    unfold lfilled, lfill.
    unfold lfilled, lfill in Hfill.
    destruct k ; first by false_assumption.
    fold lfill.
    fold lfill in Hfill.
    destruct (const_list l) ; last by false_assumption.
    destruct (lfill k l2 es') eqn:Hfill' ; last by false_assumption.
    move/eqP in Hfill.
    assert (lfilled k l2 es' l3) ; first by unfold lfilled; rewrite Hfill'.
    eapply IHlh in H => //=.
    unfold lfilled in H.
    destruct (lfill k lh es) ; last by false_assumption.
    move/eqP in H.
    by subst.
  Qed.


  Fixpoint lh_minus lh1 lh2 :=
    match lh2 with
    | LH_base [] [] => Some lh1
    | LH_base _ _ => None
    | LH_rec bef2 n2 es2 lh2 aft2 =>
        match lh1 with
        | LH_base _ _ => None
        | LH_rec bef1 n1 es1 lh1 aft1 =>
            if (bef1 == bef2) && (n1 =? n2) && (es1 == es2) && (aft1 == aft2)
            then lh_minus lh1 lh2
            else None
        end
    end.


  Lemma lh_minus_plus k0 k1 lh0 lh1 lh2 es0 es1 es2 :
    lh_minus lh0 lh1 = Some lh2 ->
    k0 >= k1 -> 
    lfilled (k0 - k1) lh2 es0 es1 ->
    lfilled k1 lh1 es1 es2 ->
    lfilled k0 lh0 es0 es2.
  Proof.
    generalize dependent lh1 ; generalize dependent es2 ;
      generalize dependent lh0 ; generalize dependent k0.
    induction k1 ; intros k0 lh0 es2 lh1 Hminus Hk Hfill2 Hfill1.
    { unfold lfilled, lfill in Hfill1.
      destruct lh1 as [bef1 aft1 |] ; last by false_assumption.
      unfold lh_minus in Hminus.
      destruct bef1 ; destruct aft1 ; try by destruct lh0 ; inversion Hminus.
      simpl in Hfill1.
      assert (lh0 = lh2) as -> ; first by destruct lh0 ; inversion Hminus.
      move/eqP in Hfill1.
      rewrite Hfill1 app_nil_r.
      rewrite - minus_n_O in Hfill2.
      done. }
    unfold lfilled, lfill in Hfill1 ; fold lfill in Hfill1.
    destruct lh1 as [ | bef1 n1 nes1 lh1 aft1] ; first by false_assumption.
    destruct (const_list bef1) eqn:Hbef1 ; last by false_assumption.
    destruct (lfill k1 _ _) eqn:Hfill1' ; last by false_assumption.
    move/eqP in Hfill1.
    unfold lh_minus in Hminus.
    destruct lh0 ; first by inversion Hminus.
    destruct (_ && _) eqn:Heq ; last by inversion Hminus.
    fold lh_minus in Hminus.
    destruct k0 ; first lia.
    unfold lfilled, lfill ; fold lfill.
    repeat apply andb_true_iff in Heq as [Heq ?].
    move/eqP in H.
    move/eqP in H0.
    move/eqP in Heq.
    subst.
    apply beq_nat_true in H1 as ->.
    rewrite Hbef1.
    assert (lfilled k1 lh1 es1 l) ; first by unfold lfilled ; rewrite Hfill1'.
    assert (lfilled k0 lh0 es0 l) ; first by eapply IHk1 ; try lia.
    unfold lfilled in H0.
    destruct (lfill k0 lh0 es0) ; last by false_assumption.
    by move/eqP in H0; subst.
  Qed.

  Lemma lh_minus_minus k0 k1 lh0 lh1 lh2 es0 es1 es2 :
    lh_minus lh0 lh1 = Some lh2 ->
    lfilled k0 lh0 es0 es2 ->
    lfilled k1 lh1 es1 es2 ->
    lfilled (k0 - k1) lh2 es0 es1.
  Proof.
    generalize dependent lh1 ; generalize dependent es2 ;
      generalize dependent lh0 ; generalize dependent k0.
    induction k1 ; intros k0 lh0 es2 lh1 Hminus Hfill0 Hfill1.
    { unfold lfilled, lfill in Hfill1.
      destruct lh1 as [bef1 aft1 |] ; last by false_assumption.
      unfold lh_minus in Hminus.
      destruct bef1 ; destruct aft1 ; try by destruct lh0 ; inversion Hminus.
      simpl in Hfill1.
      assert (lh0 = lh2) as -> ; first by destruct lh0 ; inversion Hminus.
      move/eqP in Hfill1.
      rewrite Hfill1 app_nil_r in Hfill0.
      rewrite - minus_n_O.
      done. }
    unfold lfilled, lfill in Hfill1 ; fold lfill in Hfill1.
    destruct lh1 as [| bef1 n1 nes1 lh1 aft1] ; first by false_assumption.
    destruct (const_list bef1) eqn:Hbef1 ; last by false_assumption.
    destruct (lfill k1 _ _) eqn:Hfill'1 ; last by false_assumption.
    move/eqP in Hfill1.
    unfold lh_minus in Hminus.
    destruct lh0 ; first by inversion Hminus.
    destruct (_ && _) eqn:Heq ; last by inversion Hminus.
    fold lh_minus in Hminus.
    unfold lfilled, lfill in Hfill0.
    destruct k0 ; first by false_assumption.
    fold lfill in Hfill0.
    repeat apply andb_true_iff in Heq as [Heq _].
    move/eqP in Heq; subst.
    rewrite Hbef1 in Hfill0.
    assert (lfilled k1 lh1 es1 l) ; first by unfold lfilled ; rewrite Hfill'1.
    replace (S k0 - S k1) with (k0 - k1) ; last lia.
    destruct (lfill k0 _ _ ) eqn:Hfill'0 ; last by false_assumption.
    move/eqP in Hfill0.
    assert (lfilled k0 lh0 es0 l0) ; first by unfold lfilled ; rewrite Hfill'0.
    eapply IHk1 => //=.
    apply first_values in Hfill0 as (_ & Hlab & _) => //= ; try by left.
    by inversion Hlab ; subst. all: by intros [? ?].
  Qed.

  Lemma lfilled_same_index k0 k1 lh es0 es1 LI0 LI1 :
    lfilled k0 lh es0 LI0 ->
    lfilled k1 lh es1 LI1 ->
    k0 = k1.
  Proof.
    generalize dependent k1 ; generalize dependent lh ; generalize dependent LI0 ;
      generalize dependent LI1.
    induction k0 ; intros LI1 LI0 lh k1 Hfill0 Hfill1.
    { unfold lfilled, lfill in Hfill0.
      destruct lh ; last by false_assumption.
      unfold lfilled, lfill in Hfill1.
      destruct k1 ; last by false_assumption.
      done. }
    unfold lfilled, lfill in Hfill0 ; fold lfill in Hfill0.
    destruct lh ; first by false_assumption.
    unfold lfilled, lfill in Hfill1.
    destruct k1 ; first by false_assumption.
    fold lfill in Hfill1.
    destruct (const_list l) ; last by false_assumption.
    destruct (lfill k0 lh es0) eqn:Hfill'0 ; last by false_assumption.
    destruct (lfill k1 lh es1) eqn:Hfill'1 ; last by false_assumption.
    assert (lfilled k0 lh es0 l2) ; first by unfold lfilled ; rewrite Hfill'0.
    assert (lfilled k1 lh es1 l3) ; first by unfold lfilled ; rewrite Hfill'1.
    eapply IHk0 in H0 => //=.
    lia.
  Qed.

  Lemma lfilled_depth k lh es LI :
    lfilled k lh es LI ->
    lh_depth lh = k.
  Proof.
    generalize dependent k ; generalize dependent LI.
    induction lh ; intros LI k Hfill ;
      unfold lh_depth ;
      unfold lfilled, lfill in Hfill ;
      destruct k => //= ; try by false_assumption.
    fold lfill in Hfill.
    fold lh_depth.
    destruct (const_list l) ; last by false_assumption.
    destruct (lfill k lh es) eqn:Hfill' ; last by false_assumption.
    assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill'.
    apply IHlh in H.
    lia.
  Qed.
  
  Lemma lh_minus_depth lh0 lh1 lh2 :
    lh_minus lh0 lh1 = Some lh2 ->
    lh_depth lh2 = lh_depth lh0 - lh_depth lh1.
  Proof.
    generalize dependent lh0.
    induction lh1 ; intros lh0 Hminus.
    { unfold lh_minus in Hminus.
      destruct l ; destruct l0 ; try by destruct lh0 ; inversion Hminus. }
    unfold lh_minus in Hminus.
    destruct lh0 ; first by inversion Hminus.
    destruct (_ && _) eqn:Heq ; last by inversion Hminus.
    fold lh_minus in Hminus.
    apply IHlh1 in Hminus.
    unfold lh_depth ; fold lh_depth.
    lia.
  Qed.

  

  Lemma lh_minus_minus2 k0 k1 lh0 lh1 lh2 es0 es1 es2 :
    lh_minus lh0 lh1 = Some lh2 ->
    k0 >= k1 ->
    lfilled k0 lh0 es0 es2 ->
    lfilled (k0 - k1) lh2 es0 es1 ->
    lfilled k1 lh1 es1 es2.
  Proof.
    generalize dependent lh0. generalize dependent es2.
    generalize dependent k0. generalize dependent k1.
    induction lh1 ; intros k1 k0 es2 lh0 Hminus Hk Hfill0 Hfill2.
    { unfold lh_minus in Hminus.
      destruct l ; last by destruct lh0 ; inversion Hminus.
      destruct l0 ; last by destruct lh0 ; inversion Hminus.
      assert (lh2 = lh0) as -> ; first by destruct lh0 ; inversion Hminus.
      specialize (lfilled_same_index _ _ _ _ _ _ _  Hfill0 Hfill2) ; intro.
      rewrite H in Hfill0.
      eapply lfilled_inj in Hfill0 ; last exact Hfill2.
      rewrite Hfill0.
      assert (k1 = 0) ; first lia.
      rewrite H0.
      by unfold lfilled, lfill => //= ; rewrite app_nil_r. }
    destruct k1.
    { replace (k0 - 0) with k0 in Hfill2 ; last lia.
      destruct k0.
      { unfold lfilled, lfill in Hfill0.
        destruct lh0 ; last by false_assumption.
        inversion Hminus. } 
      apply lfilled_depth in Hfill0, Hfill2.
      apply lh_minus_depth in Hminus.
      rewrite Hfill0 Hfill2 in Hminus.
      unfold lh_depth in Hminus.
      lia. }     
    unfold lh_minus in Hminus.
    destruct lh0 ; first by inversion Hminus.
    fold lh_minus in Hminus.
    destruct (_ && _) eqn:Heq ; last by inversion Hminus.
    unfold lfilled, lfill in Hfill0.
    destruct k0 ; first by false_assumption.
    fold lfill in Hfill0.
    destruct (const_list l2) eqn:Hl2 ; last by false_assumption.
    destruct (lfill k0 lh0 es0) eqn:Hfill0' ; last by false_assumption.
    move/eqP in Hfill0.
    unfold lfilled, lfill ; fold lfill.
    repeat apply andb_true_iff in Heq as [Heq ?].
    move/eqP in Heq; subst.
    rewrite Hl2.
    replace (S k0 - S k1) with (k0 - k1) in Hfill2 ; last lia.
    assert (lfilled k0 lh0 es0 l5) ; first by unfold lfilled ; rewrite Hfill0'.
    eapply IHlh1 in Hfill2 => //= ; last lia.
    unfold lfilled in Hfill2.
    destruct (lfill k1 lh1 es1) ; last by false_assumption.
    move/eqP in H.
    move/eqP in H0.
    apply beq_nat_true in H1.
    by move/eqP in Hfill2; subst.
  Qed.
  


  Lemma filled_twice k0 k1 lh0 lh1 es0 es1 LI :
    lfilled k0 lh0 es0 LI ->
    lfilled k1 lh1 es1 LI ->
    k0 >= k1 ->
    base_is_empty lh1 ->
    exists lh2, lh_minus lh0 lh1 = Some lh2.
  Proof.
    generalize dependent lh1 ; generalize dependent LI ;
      generalize dependent lh0 ; generalize dependent k0.
    induction k1 ; intros k0 lh0 LI lh1 Hfill0 Hfill1 Hk Hempty.
    { unfold lfilled, lfill in Hfill1.
      destruct lh1 as [bef1 aft1 |] ; last by false_assumption.
      inversion Hempty ; subst bef1 aft1.
      unfold lh_minus.
      destruct lh0 ; by eexists. }
    unfold lfilled, lfill in Hfill1 ; fold lfill in Hfill1.
    destruct lh1 as [| bef1 n1 nes1 lh1 aft1 ] ; first by false_assumption.
    destruct (const_list bef1) eqn:Hbef1 ; last by false_assumption.
    destruct (lfill k1 lh1 es1) eqn:Hfill'1 ; last by false_assumption.
    move/eqP in Hfill1.
    destruct k0 ; first lia.
    unfold lfilled, lfill in Hfill0 ; fold lfill in Hfill0.
    destruct lh0 as [| bef0 n0 nes0 lh0 aft0 ] ; first by false_assumption.
    destruct (const_list bef0) eqn:Hbef0 ; last by false_assumption.
    destruct (lfill k0 lh0 es0) eqn:Hfill'0 ; last by false_assumption.
    move/eqP in Hfill0.
    unfold lh_minus.
    rewrite Hfill1 in Hfill0.
    apply first_values in Hfill0 as (-> & Hlab & ->) => //= ; try by left.
    inversion Hlab ; subst.
    repeat rewrite eq_refl.
    rewrite Nat.eqb_refl.
    simpl.
    fold lh_minus.
    unfold base_is_empty in Hempty.
    fold base_is_empty in Hempty.
    assert (lfilled k0 lh0 es0 l0) ; first by unfold lfilled ; rewrite Hfill'0.
    assert (lfilled k1 lh1 es1 l0) ; first by unfold lfilled ; rewrite Hfill'1.
    eapply IHk1 => //=.
    lia. all: intros [? ?];done.
  Qed.                                 

  Lemma lfilled_length_rec_or_same k lh es LI :
    lfilled k lh es LI -> length_rec es < length_rec LI \/ es = LI.
  Proof.
    generalize dependent k ; generalize dependent LI.
    induction lh ; intros LI k Hfill.
    unfold lfilled, lfill in Hfill.
    destruct k ; last by false_assumption.
    destruct (const_list l) ; last by false_assumption.
    move/eqP in Hfill; subst.
    destruct l.
    destruct l0.
    right.
    by rewrite app_nil_r.
    left.
    simpl.
    rewrite app_length_rec.
    specialize (cons_length_rec a l0) ; intro ; lia.
    repeat rewrite app_length_rec.
    left.
    specialize (cons_length_rec a l) ; intro ; lia.
    unfold lfilled, lfill in Hfill.
    destruct k ; first by false_assumption.
    fold lfill in Hfill.
    destruct (const_list l) ; last by false_assumption.
    destruct (lfill k lh es) eqn:Hfill' ; last by false_assumption.
    move/eqP in Hfill; subst.
    rewrite list_extra.cons_app.
    repeat rewrite app_length_rec.
    unfold length_rec at 3.
    simpl.
    fold (length_rec l2).
    assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill'.
    apply IHlh in H as [Hlen | ->] ; lia.
  Qed.
  
  
  Lemma filled_trivial k lh es :
    lfilled k lh es es -> k = 0 /\ lh = LH_base [] [].
  Proof.
    intros Hfill.
    unfold lfilled, lfill in Hfill.
    destruct k.
    split => //=.
    destruct lh ; last by false_assumption.
    destruct (const_list l) ; last by false_assumption.
    move/eqP in Hfill. 
    assert (length es = length (l ++ es ++ l0)%list) ; first by rewrite - Hfill.
    repeat rewrite app_length in H.
    destruct l ; last by simpl in H ; lia.
    destruct l0 ; last by simpl in H ; lia.
    done.
    fold lfill in Hfill.
    destruct lh ; first by false_assumption.
    destruct (const_list l) ; last by false_assumption.
    destruct (lfill k lh es) eqn:Hfill' ; last by false_assumption.
    move/eqP in Hfill.
    assert (length_rec es = length_rec (l ++ (AI_label n l0 l2 :: l1)%SEQ)) ;
      first by rewrite Hfill.
    rewrite list_extra.cons_app in H.
    repeat rewrite app_length_rec in H.
    unfold length_rec at 3 in H.
    simpl in H.
    fold (length_rec l2) in H.
    assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill'.
    apply lfilled_length_rec in H0.
    lia.
  Qed.

  Lemma lfilled_const k lh es LI :
    lfilled k lh es LI ->
    const_list LI ->
    k = 0 /\ const_list es.
  Proof.
    intros.
    unfold lfilled, lfill in H.
    destruct k.
    { destruct lh ; last by false_assumption.
      destruct (const_list l) ; last by false_assumption.
      move/eqP in H; subst.
      unfold const_list in H0.
      repeat rewrite forallb_app in H0.
      repeat apply andb_true_iff in H0 as [? H0].
      by split. }
    fold lfill in H.
    destruct lh ; first by false_assumption.
    destruct (const_list l) ; last by false_assumption.
    destruct (lfill _ _ _ ) ; last by false_assumption.
    move/eqP in H; subst.
    unfold const_list in H0.
    rewrite forallb_app in H0.
    simpl in H0.
    rewrite andb_false_r in H0.
    false_assumption.
  Qed.

  Lemma filled_singleton k lh es e :
    lfilled k lh es [e] ->
    (forall a b c, e = AI_label a b c -> False) ->
    es <> [] ->
    k = 0 /\ lh = LH_base [] [] /\ es = [e].
  Proof.
    intros.
    simple_filled H k lh bef aft nn ll ll'.
    apply Logic.eq_sym, app_eq_unit in H as [[ -> Htrap] | [ _ Hnil]].
    apply app_eq_unit in Htrap as [[ -> _ ] | [-> ->]] => //=.
    apply app_eq_nil in Hnil as [-> ->] => //=.
    by eapply H0.
  Qed.

  Definition lh_prepend lh v :=
    match lh with
    | LH_base bef aft => LH_base (AI_basic (BI_const v) :: bef) aft
    | LH_rec bef n es lh aft => LH_rec (AI_basic (BI_const v) :: bef) n es lh aft end.

  Lemma lfilled_prepend i lh es v LI :
    lfilled i lh es LI -> lfilled i (lh_prepend lh v) es (AI_basic (BI_const v) :: LI).
  Proof.
    destruct i, lh ; unfold lfilled, lfill ; destruct (const_list l) eqn:Hl => //=.
    - intros H ; apply b2p in H ; subst ; rewrite Hl => //=.
    - fold lfill. destruct (lfill _ _ _) eqn:Hfill => //=.
      intros H ; apply b2p in H ; subst ; rewrite Hl => //=.
  Qed.
  
  Lemma lfilled_vLI i lh e es v LI :
    lfilled i lh (e :: es) (AI_basic (BI_const v) :: LI) ->
    (exists lh', lh_prepend lh' v = lh /\ lfilled i lh' (e :: es) LI) \/
      i = 0 /\ e = AI_basic (BI_const v) /\ exists aft, lh = LH_base [] aft /\ es ++ aft = LI.
  Proof.
    intros Hfilled.
    unfold lfilled, lfill in Hfilled ; destruct i, lh ; destruct (const_list l) eqn:Hl => //.
    - apply b2p in Hfilled.
      destruct l.
      + inversion Hfilled ; subst.
        right. repeat split => //=.
        exists l0 => //.
      + inversion Hfilled ; subst.
        left. exists (LH_base l l0).
        split => //=.
        unfold lfilled, lfill => //=.
        unfold const_list in Hl. simpl in Hl. 
        unfold const_list ; rewrite Hl. done.
    - fold lfill in Hfilled.
      destruct (lfill i lh (e :: es)) eqn:Hfill => //.
      apply b2p in Hfilled.
      destruct l ; inversion Hfilled.
      subst.
      left. exists (LH_rec l n l0 lh l1).
      split => //.
      unfold lfilled, lfill ; fold lfill.
      unfold const_list in Hl ; simpl in Hl ; unfold const_list ; rewrite Hl.
      rewrite Hfill.
      done.
  Qed.

  Lemma lh_minus_Ind_Equivalent lh lh' lh'' :
    lh_minus lh lh' = Some lh'' <->
      lh_minus_Ind lh lh' lh''.
  Proof.
    revert lh lh''.
    induction lh';intros lh lh''.
    { split; intros Hlh.
      { unfold lh_minus in Hlh.
        destruct lh. destruct l,l0 =>//.
        simplify_eq. constructor.
        destruct l,l0 =>//.
        inversion Hlh;subst.
        constructor. }
      { inversion Hlh;simplify_eq.
        unfold lh_minus.
        destruct lh'';auto. }
    }
    { split;intros Hlh.
      { unfold lh_minus in Hlh.
        destruct lh. done.
        destruct (l2 == l) eqn:Hl1; [|cbn in Hlh;done].
        apply ai_eqseq_true in Hl1 as ->.
        destruct (decide (n0 = n));subst.
        2: { apply PeanoNat.Nat.eqb_neq in n1.
             rewrite n1 in Hlh. cbn in Hlh;done. }
        rewrite PeanoNat.Nat.eqb_refl /= in Hlh.
        destruct (l3 == l0) eqn:Hl2;[simpl in Hlh;apply ai_eqseq_true in Hl2 as ->|cbn in Hlh;done].
        destruct (l4 == l1) eqn:Hl3;[simpl in Hlh;apply ai_eqseq_true in Hl3 as ->|cbn in Hlh;done].
        constructor. apply IHlh'. auto.
      }
      { inversion Hlh. simpl. 
        rewrite !eq_refl PeanoNat.Nat.eqb_refl. cbn.
        apply IHlh';auto.
      }
    }
  Qed.

  Lemma lh_delete_inner_eq lh :
    base_is_empty lh ->
    lh_delete_inner lh = lh.
  Proof.
    intros Hbase.
    induction lh.
    { inversion Hbase; subst; auto. }
    { simpl in Hbase. apply IHlh in Hbase.
      unfold lh_delete_inner in Hbase.
      destruct (empty_base lh) eqn:Hlh. simplify_eq.
      unfold lh_delete_inner. rewrite /= Hlh. auto. }
  Qed.

  Lemma base_is_empty_delete_inner lh :
    base_is_empty (lh_delete_inner lh).
  Proof.
    induction lh.
    { simpl. auto. }
    { unfold lh_delete_inner.
      destruct (empty_base (LH_rec l n l0 lh l1)) eqn:Hl.
      inversion Hl. destruct (empty_base lh) eqn:Hlh. simplify_eq.
      simpl. unfold lh_delete_inner in IHlh.
      rewrite Hlh in IHlh. auto. }
  Qed.

  Lemma lh_minus_eq lh :
    lh_minus lh (LH_base [] []) = Some lh.
  Proof.
    induction lh;simpl;auto.
  Qed.
  
  Lemma get_layer_lh_minus lh i vs' n es lh' es' :
    get_layer lh i = Some (vs', n, es, lh', es') -> ∃ lh'', lh_minus lh lh'' = Some lh'.
  Proof.
    revert i vs' n es lh' es'.
    induction lh;intros i vs' m es lh' es' Hl;[done|].
    destruct i.  
    { inversion Hl;simplify_eq.
      exists (LH_rec vs' m es (LH_base [] []) es'). simpl.
      cbn. rewrite !eqseqE !eq_refl PeanoNat.Nat.eqb_refl. cbn.
      apply lh_minus_eq. }
    { inversion Hl.
      apply IHlh in H0. destruct H0 as [hl'' Hlh''].
      exists (LH_rec l n l0 hl'' l1).
      simpl. rewrite Hlh''.
      cbn. rewrite !eqseqE !eq_refl PeanoNat.Nat.eqb_refl. cbn. auto. }
  Qed.

  Lemma LH_rec_circular vs' m es lh es' : LH_rec vs' m es lh es' = lh -> False.
  Proof.
    revert vs' m es es'.
    induction lh;intros vs' m es es' Hcontr;[done|].
    inversion Hcontr;subst.
    apply IHlh in H3. auto.
  Qed.

  Lemma lminus_base_inv lh lh' : lh_minus_Ind lh lh' lh -> lh' = LH_base [] [].
  Proof.
    intros Hlh.
    inversion Hlh;auto.
    exfalso. simplify_eq.
    apply lh_minus_Ind_Equivalent in H.
    apply lh_minus_depth in H. simpl in H. lia.
  Qed.
  
  Lemma lminus_rec_inv vs' m es lh es' lh'' :
    lh_minus (LH_rec vs' m es lh es') lh'' = Some lh ->
    lh'' = LH_rec vs' m es (LH_base [] []) es'.
  Proof.
    intros Hmin%lh_minus_Ind_Equivalent.
    inversion Hmin;subst.
    exfalso. eapply LH_rec_circular. eauto.
    f_equiv. eapply lminus_base_inv;eauto.
  Qed.

  Lemma get_layer_depth i lh x :
    get_layer lh i = Some x ->
    i < lh_depth lh.
  Proof.
    revert i x;induction lh;intros i x Hlayer;[done|].
    destruct x,p,p,p.
    cbn in Hlayer.
    destruct i;simplify_eq.
    { simpl. lia. }
    { apply IHlh in Hlayer.
      simpl. lia. }
  Qed.

  Lemma get_layer_depth_lt i lh vs' n es lh' es' :
    get_layer lh i = Some (vs',n,es,lh',es') ->
    lh_depth lh' < lh_depth lh.
  Proof.
    revert i vs' n es lh' es';induction lh;intros i vs' m es lh' es' Hlayer;[done|].
    cbn in Hlayer.
    destruct i;simplify_eq.
    { simpl. lia. }
    { apply IHlh in Hlayer.
      simpl. lia. }
  Qed.

  Lemma get_layer_circular lh i vs' m es es' :
    get_layer lh i = Some (vs', m, es, lh, es') ->
    False.
  Proof.
    revert lh vs' m es es'.
    induction i;intros lh vs' m es es' Hlayer;auto.
    destruct lh;try done.
    simpl in Hlayer.
    simplify_eq.
    symmetry in H0.
    by apply LH_rec_circular in H0.
    apply get_layer_depth_lt in Hlayer. lia.
  Qed.

  Lemma get_layer_find i lh' :
    S i < (lh_depth lh') ->
    ∃ vs0' n0 es0 vs' n es lh es' es0' lh'',
      get_layer lh' (lh_depth lh' - (S (S i))) = Some (vs0', n0, es0, (LH_rec vs' n es lh es'), es0') ∧
        lh_minus lh' lh'' = Some (LH_rec vs' n es lh es') ∧ lh_depth lh = i.
  Proof.
    revert i.
    induction lh';intros i Hlt.
    { simpl in Hlt. lia. }
    { destruct lh';[simpl in Hlt;lia|].
      destruct lh'.
      { simpl in Hlt. destruct i;[|lia]. simpl.
        do 9 eexists.
        eexists (LH_rec l n l0 (LH_base [] []) l1).
        split;eauto. rewrite !eq_refl PeanoNat.Nat.eqb_refl.
        cbn. auto. }
      { simpl. simpl in Hlt.
        destruct (decide (i = S (lh_depth lh'))).
        { subst i.
          rewrite PeanoNat.Nat.sub_diag.
          clear IHlh'.
          do 9 eexists.
          eexists (LH_rec l n l0 (LH_base [] []) l1).
          split;eauto.
          rewrite !eq_refl PeanoNat.Nat.eqb_refl. cbn. auto. }
        { assert (S i < S (S (lh_depth lh'))) as Hlt';[lia|].
          apply IHlh' in Hlt'.
          destruct Hlt' as [vs0' [n3 [es0 [vs' [m [es [lh [es' [es0' [lh'' [Heq Hmin]]]]]]]]]]].
          simpl in Heq.
          destruct (lh_depth lh' - i) eqn:Hi1.
          { rewrite Nat.sub_succ_l;[|lia]. rewrite Hi1.
            do 9 eexists.
            eexists (LH_rec l n l0 lh'' l1).
            split;[eauto|].
            rewrite !eq_refl PeanoNat.Nat.eqb_refl. cbn.
            auto. }
          { rewrite Nat.sub_succ_l;[|lia]. rewrite Hi1.
            destruct n4.
            { inversion Heq;subst. do 9 eexists.
              eexists (LH_rec l n l0 lh'' l1).
              split;eauto.
              rewrite !eq_refl !PeanoNat.Nat.eqb_refl. cbn. auto. }
            { do 9 eexists. eexists (LH_rec l n l0 lh'' l1).
              split;eauto.
              rewrite !eq_refl !PeanoNat.Nat.eqb_refl. cbn. auto. }
          }
        }      
      }
    }
  Qed.
  
  Lemma lfilled_minus lh' i vs' n es lh es' e LI j lh'' :
    lh_minus lh' lh'' = Some lh ->
    i < lh_depth lh' ->
    get_layer lh' (lh_depth lh' - S i) = Some (vs', n, es, lh, es') ->
    lfilled j lh' e LI ->
    ∃ LI', lfilled i lh e LI' ∧ lfilled (j - i) lh'' LI' LI.
  Proof.
    intros Hlh%lh_minus_Ind_Equivalent.
    revert vs' n es es' i j e LI.
    induction Hlh;intros vs' m es2 es2' i j e LI Hle Hlayer Hfill.
    { apply get_layer_circular in Hlayer. done. }
    { simpl in *.
      destruct (lh_depth lh - i) eqn:Hi.
      { simplify_eq.
        assert (lh_depth lh'' = i);[lia|simplify_eq].
        apply lfilled_depth in Hfill as Heq. simpl in *;subst.
        apply lfilled_Ind_Equivalent in Hfill.
        inversion Hfill;simplify_eq.
        apply lfilled_Ind_Equivalent in H8.
        eexists. split;eauto.
        apply lfilled_Ind_Equivalent.
        assert (S (lh_depth lh'') - (lh_depth lh'') = S 0) as ->;[lia|].
        constructor;auto.
        apply lminus_base_inv in Hlh as ->.
        apply lfilled_Ind_Equivalent. cbn.
        erewrite app_nil_r. by apply/eqP.
      }
      { assert (lh_depth lh - S i = n0);[lia|simplify_eq].
        apply lfilled_Ind_Equivalent in Hfill.
        inversion Hfill;simplify_eq.
        apply lfilled_Ind_Equivalent in H8.
        eapply IHHlh in Hlayer as HLI';[|lia|eauto].
        destruct HLI' as [LI' [Hfill1 Hfill2]].
        assert (i <= k) as Hlei.
        { apply lh_minus_Ind_Equivalent in Hlh.
          apply lh_minus_depth in Hlh as Hd.
          apply lfilled_depth in Hfill1 as Hieq.
          apply lfilled_depth in Hfill2 as Hkeq.
          rewrite Hieq in Hd.
          rewrite Hkeq in Hd.
          simpl in *. lia. }
        exists LI'.
        split;auto. rewrite Nat.sub_succ_l;auto.
        apply lfilled_Ind_Equivalent. constructor;auto.
        apply lfilled_Ind_Equivalent. auto.
      }
    }
  Qed.

  Lemma lfilled_split i j lh e LI :
    i <= j ->
    lfilled j lh e LI ->
    ∃ lh' lh'' LI',
      lfilled i lh' e LI' ∧ lfilled (j - i) lh'' LI' LI.
  Proof.
    revert i lh e LI.
    induction j;intros i lh e LI Hle Hfill%lfilled_Ind_Equivalent.
    { inversion Hfill;simplify_eq. destruct i;[|lia].
      simpl.
      eexists; eexists; eexists.
      split.
      { apply lfilled_Ind_Equivalent. constructor. eauto. }
      { instantiate (2:=LH_base [] []). cbn. apply/eqP.
        rewrite app_nil_r. eauto. }
    }
    { inversion Hfill;simplify_eq.
      destruct (decide (i = S j)).
      { simplify_eq. rewrite PeanoNat.Nat.sub_diag.
        eexists; eexists; eexists.
        split.
        { apply lfilled_Ind_Equivalent.
          constructor;eauto. }
        { instantiate (4:=LH_base [] []). cbn. apply/eqP.
          rewrite app_nil_r. eauto. }
      }
      { assert (i <= j) as Hle';[lia|].
        apply lfilled_Ind_Equivalent in H1.
        eapply IHj in Hle' as Hres;eauto.
        destruct Hres as [lh2 [lh'' [LI' [Hfill1 Hfill2]]]].
        repeat eexists;eauto.
        apply lfilled_Ind_Equivalent.
        rewrite -minus_Sn_m;eauto.
        constructor;auto. apply lfilled_Ind_Equivalent. eauto.
      }
    }
  Qed.

  Lemma lfilled_to_sfill i lh es LI :
    lfilled i lh es LI ->
    ∃ sh, LI = sfill sh es.
  Proof.
    revert i es LI.
    induction lh;intros i es LI Hfill%lfilled_Ind_Equivalent.
    { inversion Hfill;simplify_eq.
      apply const_es_exists in H4 as [vs Hvs].
      exists (SH_base vs l0);rewrite Hvs;simpl;auto. }
    { inversion Hfill;simplify_eq.
      apply lfilled_Ind_Equivalent in H8.
      apply IHlh in H8 as [sh Hsh]. simplify_eq.
      apply const_es_exists in H7 as [vs Hvs].
      exists (SH_rec vs n l0 sh l1).
      rewrite Hvs;simpl;auto. }
  Qed.

  Lemma sfill_sh_pull_const_r sh :
    ∀ e x, sfill (sh_pull_const_r sh x) e = sfill sh (v_to_e_list x ++ e).
  Proof.
    induction sh;intros e x.
    { cbn. rewrite -to_e_list_fmap. rewrite !fmap_app. repeat rewrite app_assoc. repeat f_equiv. }
    { cbn. rewrite IHsh. auto. }
  Qed.

  Lemma const_list_app v1 v2 :
    const_list (v1 ++ v2) <-> const_list v1 ∧ const_list v2.
  Proof.
    split; intros; [ by apply const_list_split | apply const_list_concat; by inversion H ].
  Qed.
  
  Lemma lh_pull_const_r_app i lh x es es1 :
    lfilled i lh (v_to_e_list x ++ es) es1 ->
    ∃ lh', lfilled i lh' es es1.
  Proof.
    revert i es1.
    induction lh;intros i es1 Hfill%lfilled_Ind_Equivalent.
    { inversion Hfill;simplify_eq.
      exists (LH_base (l ++ (v_to_e_list) x) l0).
      apply lfilled_Ind_Equivalent. repeat erewrite app_assoc.
      erewrite <- (app_assoc _ _ l0). constructor.
      apply const_list_app. split;auto. apply v_to_e_is_const_list. }
    { inversion Hfill;simplify_eq. apply lfilled_Ind_Equivalent in H8.
      apply IHlh in H8 as [lh' Hlh'%lfilled_Ind_Equivalent].
      eexists. apply lfilled_Ind_Equivalent.
      constructor;eauto. }
  Qed.

  Lemma lfilled_flatten i lh e LI l1 n es l2 :
    lfilled (S i) (LH_rec l1 n es lh l2) e LI ->
    ∃ LI', lfilled i lh e LI' ∧ lfilled 1 (LH_rec l1 n es (LH_base [] []) l2) LI' LI.
  Proof.
    revert i e LI l1 n es l2.
    induction lh;intros i e LI l1' m es l2' Hfill%lfilled_Ind_Equivalent.
    { inversion Hfill;simplify_eq.
      inversion H8;simplify_eq.
      eexists. split;apply lfilled_Ind_Equivalent.
      constructor;auto. constructor;auto.
      apply lfilled_Ind_Equivalent. cbn. rewrite app_nil_r;by apply/eqP. }
    { inversion Hfill;simplify_eq.
      inversion H8;simplify_eq.
      apply lfilled_Ind_Equivalent in H8.
      apply IHlh in H8 as HLI'.
      eexists.
      split;apply lfilled_Ind_Equivalent.
      constructor;eauto.
      constructor;auto.
      apply lfilled_Ind_Equivalent. cbn. rewrite app_nil_r;by apply/eqP. }
  Qed.

  
End lfilled_properties.
