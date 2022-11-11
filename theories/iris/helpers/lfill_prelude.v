From mathcomp Require Import ssreflect ssrbool eqtype seq.
From Coq Require Import Eqdep_dec.
From stdpp Require Import base list.
Require Export common operations opsem properties list_extra stdpp_aux.
Require Export lfill_extension.
Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma cons_length_rec a es :
  length_rec (a :: es) > length_rec es.
Proof.
  unfold length_rec => //=. destruct a => //= ; lia.
Qed. 

Lemma app_length_rec l1 l2 :
  length_rec (app l1 l2) = length_rec l1 + length_rec l2.
Proof.
  unfold length_rec. rewrite map_app. rewrite list_sum_app. done.  
Qed. 

Lemma lfilled_length_rec k lh es les :
  lfilled k lh es les -> length_rec es <= length_rec les.
Proof.
  move => Hlf; move/lfilledP in Hlf.
  induction Hlf; repeat rewrite app_length_rec => /=; first lia.
  unfold length_rec in * => /=; by lias.
Qed.

Lemma lfill_cons_not_Some_nil : forall i lh es es' e es0,
  lfill i lh es = es' -> es = e :: es0 -> es' <> Some [::].
Proof.
  move => i lh es es' e es0 Hlf Hes Hcontra.
  destruct es' => //; inversion Hcontra; subst; clear Hcontra.
  assert (lfilled i lh (e :: es0) []) as Hlf'; first by unfold lfilled; rewrite Hlf.
  move/lfilledP in Hlf'.
  inversion Hlf'; subst; by destruct vs => //.
Qed.

Lemma lfilled_not_nil : forall i lh es es', lfilled i lh es es' -> es <> [::] -> es' <> [::].
Proof.
  move => i lh es es' H Hes Hes'.
  move/lfilledP in H.
  inversion H; subst; clear H; by destruct vs, es => //.
Qed.

Lemma lfilled_first_values i lh vs e i' lh' vs' e' LI :
  lfilled i lh (vs ++ [::e]) LI ->
  lfilled i' lh' (vs' ++ [::e']) LI ->
  const_list vs -> const_list vs' ->
  (is_const e = false) -> (is_const e' = false) ->
  (forall n es LI, e <> AI_label n es LI) -> (forall n es LI, e' <> AI_label n es LI) ->
  e = e' /\ i = i' /\ (length vs = length vs' -> (vs = vs' /\ lh = lh')).
Proof.
  cut (forall n,
          length_rec LI < n ->
          lfilled i lh (vs ++ [::e]) LI ->
          lfilled i' lh' (vs' ++ [::e']) LI ->
          const_list vs -> const_list vs' ->
          (is_const e = false) -> (is_const e' = false) ->
          (forall n es LI, e <> AI_label n es LI) -> (forall n es LI, e' <> AI_label n es LI) ->
          e = e' /\ i = i' /\ (length vs = length vs' -> (vs = vs' /\ lh = lh'))).
  { intro Hn ; apply (Hn (S (length_rec LI))) ; lia. }
  intro n. generalize dependent LI. generalize dependent e'.
  generalize dependent vs'. generalize dependent lh'. generalize dependent i'.
  generalize dependent e. generalize dependent vs. generalize dependent lh.
  generalize dependent i.
  induction n ;
    intros i lh vs e i' lh' vs' e' LI Hlab Hfill Hfill' Hvs Hvs' He He' Hlabe Hlabe' ;
    first by inversion Hlab.
  unfold lfilled, lfill in Hfill. destruct i.
  { destruct lh as [bef aft|] => //. 
    remember (const_list bef) as b eqn:Hbef ; destruct b => //. 
    move/eqP in Hfill.
    unfold lfilled, lfill in Hfill' ; destruct i'.
    { destruct lh' as [bef' aft'|] => //. 
      remember (const_list bef') as b0 eqn:Hbef' ; destruct b0 => //. 
      move/eqP in Hfill'.
      rewrite Hfill in Hfill'. do 2 rewrite <- app_assoc in Hfill'.
      rewrite app_assoc in Hfill'. rewrite (app_assoc bef' _ _) in Hfill'.
      
      apply first_values in Hfill' as (Hvvs & Hee & ?) ; (try done) ; (try by left);
        try by unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      repeat split => //=. apply (app_inj_2 _ _ _ _ H0 Hvvs).
      apply app_inj_2 in Hvvs as [-> _] => //. by subst.
    }
    fold lfill in Hfill'. destruct lh' => //. 
    remember (const_list l) as b ; destruct b => //. 
    destruct (lfill i' lh' _) => //. 
    move/eqP in Hfill'. rewrite Hfill in Hfill'.
    rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
    apply first_values in Hfill' as ( _ & Habs & _ ) ; (try done) ; try by intros [? ?].
    by exfalso ; apply (Hlabe n0 l0 l2).
    unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
  fold lfill in Hfill. 
  destruct lh as [| bef n' l lh aft] => //. 
  remember (const_list bef) as b ; destruct b => //. 
  remember (lfill i lh (vs ++ [e])) as les ; destruct les => //. 
  move/eqP in Hfill.
  unfold lfilled, lfill in Hfill' ; destruct i'.
  { destruct lh' as [bef' aft' |] => //.  
    remember (const_list bef') as b ; destruct b => //. 
    move/eqP in Hfill'. rewrite Hfill in Hfill'.
    rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
    apply first_values in Hfill' as ( _ & Habs & _ ) => //= ; try by intros [? ?].
    by exfalso ; apply (Hlabe' n' l l0).
    unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
  fold lfill in Hfill'.
  destruct lh' as [| bef' n'' l' lh' aft'] => //. 
  remember (const_list bef') as b ; destruct b => //. 
  remember (lfill i' lh' (vs' ++ [e'])) as les0 ; destruct les0 => //. 
  move/eqP in Hfill'. rewrite Hfill in Hfill'.
  apply first_values in Hfill' as ( Hl & Hlab' & -> ) => //= ; try by intros [? ?].
  inversion Hlab' ; subst.
  assert (e = e' /\ i = i' /\ (length vs = length vs' -> vs = vs' /\ lh = lh')) as (? & ? & ?).
  apply (IHn i lh vs e i' lh' vs' e' l1) => //=.
  rewrite app_length_rec in Hlab.
  replace (AI_label n'' l' l1 :: aft') with ([AI_label n'' l' l1] ++ aft') in Hlab => //=.
  rewrite app_length_rec in Hlab. simpl in Hlab.
  rewrite Nat.add_0_r in Hlab. rewrite <- Nat.add_succ_l in Hlab.
  fold (length_rec l1) in Hlab. lia.
  unfold lfilled ; rewrite <- Heqles ; done.
  unfold lfilled ; rewrite <- Heqles0 ; done.
  repeat split => //=. lia.
  apply H1 in H2 as [??] => //.
  apply H1 in H2 as [-> ->] => //.
Qed.

Lemma lfilled_trans : forall k lh es1 es2 k' lh' es3,
    lfilled k lh es1 es2 -> lfilled k' lh' es2 es3 -> exists lh'', lfilled (k+k') lh'' es1 es3.
Proof.
  intros k lh es1 es2 k' ; generalize dependent es2 ; generalize dependent es1 ;
    generalize dependent lh ; generalize dependent k ; induction k' ;
    intros k lh es1 es2 lh' es3 Hfill2 Hfill3.
  { unfold lfilled, lfill in Hfill3.
    destruct lh' as [ bef' aft' |] => //. 
    remember (const_list bef') as b eqn:Hbef' ; destruct b => //. 
    move/eqP in Hfill3.
    unfold lfilled, lfill in Hfill2.
    destruct k. { destruct lh as [bef aft |] => //. 
                  remember (const_list bef) as b eqn:Hbef ; destruct b => //. 
                  move/eqP in Hfill2 ; subst.
                  exists (LH_base (bef' ++ bef) (aft ++ aft')). simpl.
                  unfold lfilled, lfill, const_list. simpl.
                  rewrite List.forallb_app. unfold const_list in Hbef ; rewrite <- Hbef.
                  unfold const_list in Hbef' ; rewrite <- Hbef' => //=.
                  by repeat rewrite List.app_assoc. }
    fold lfill in Hfill2. destruct lh as [| bef n es lh aft ] => //.  
    remember (const_list bef) as b eqn:Hbef ; destruct b => //. 
    remember (lfill k lh es1) as fill ; destruct fill => //. 
    move/eqP in Hfill2 ; subst.
    exists (LH_rec (bef' ++ bef) n es lh (aft ++ aft')). rewrite <- plus_n_O.
    unfold lfilled, lfill ; fold lfill ; unfold const_list.
    rewrite List.forallb_app. unfold const_list in Hbef ; rewrite <- Hbef.
    unfold const_list in Hbef' ; rewrite <- Hbef' => //=.
    rewrite <- Heqfill. repeat rewrite app_assoc. repeat rewrite <- List.app_assoc. done. }
  unfold lfilled, lfill in Hfill3 ; fold lfill in Hfill3.
  destruct lh' as [| bef' n' es' lh' aft' ] => //. 
  remember (const_list bef') as b eqn:Hbef' ; destruct b => //. 
  remember (lfill k' lh' es2) as fill' ; destruct fill' => //. 
  move/eqP in Hfill3. assert (lfilled k' lh' es2 l) as Hfill.
  by unfold lfilled ; rewrite <- Heqfill'.
  destruct (IHk' _ _ _ _ _ _ Hfill2 Hfill) as (lh'' & Hfill').
  exists (LH_rec bef' n' es' lh'' aft').
  rewrite plus_comm => //=. rewrite plus_comm.
  unfold lfilled, lfill ; fold lfill. rewrite <- Hbef'. unfold lfilled in Hfill'.
  destruct (lfill (k + k') lh'' es1) => //. 
  move/eqP in Hfill' ; by subst.
Qed.

Lemma vfill_is_nil n (vh : valid_holed n) es :
  vfill vh es = [] -> es = [] /\ vh = VH_base n [] [].
Proof.
  destruct vh => //= ; intros.
  repeat apply app_eq_nil in H as [? H].
  apply map_eq_nil in H0.
  by subst.
  apply app_eq_nil in H as [_ H] ; inversion H.
Qed.

Lemma sfill_is_nil sh es :
  sfill sh es = [] -> es = [] /\ sh = SH_base [] [].
Proof.
  destruct sh => //= ; intros.
  repeat apply app_eq_nil in H as [? H].
  apply map_eq_nil in H0.
  by subst.
  apply app_eq_nil in H as [_ H] ; inversion H.
Qed.

Lemma llfill_is_nil lh es :
  llfill lh es = [] -> es = [] /\ lh = LL_base [] [].
Proof.
  destruct lh => //= ; intros.
  repeat apply app_eq_nil in H as [? H].
  apply map_eq_nil in H0.
  by subst.
  all : apply app_eq_nil in H as [_ H] ; inversion H.
Qed.
  
Lemma vh_push_const_inj n (vh : valid_holed n) vh' vs :
  vh_push_const vh vs = vh_push_const vh' vs -> vh = vh'.
Proof.
  destruct vh => //=.
  destruct vh' => //=.
  intro H ; inversion H.
  apply app_inv_head in H1.
  by subst.
  set (m := S n) in vh'.
  pose (Logic.eq_refl : m = S n) as Hm.
  change vh' with match Hm in _ = w return valid_holed w with
                  | Logic.eq_refl => vh' end.
  clearbody m Hm.
  replace (vh_push_const match Hm in _ = w return valid_holed w with
                         | Logic.eq_refl => vh' end vs)
    with match Hm in _ = w return valid_holed w with
         | Logic.eq_refl => vh_push_const vh' vs end ;
    last by destruct Hm.
  destruct vh' => //=.
  replace match Hm in (_ = w) return (valid_holed w) with
          | Logic.eq_refl => VH_base n1 (vs ++ l2) l3
          end with (VH_base (S n) (vs ++ l2) l3) ;
    last by destruct Hm.
  done.
  pose proof (eq_add_S _ _ Hm) as Hn.
  assert (Hm = f_equal S Hn) as Hproof.
  apply Eqdep.EqdepTheory.UIP.
  replace match Hm in (_ = w) return (valid_holed w) with
          | Logic.eq_refl => VH_rec (vs ++ l2) n2 l3 vh' l4
          end with (VH_rec (vs ++ l2) n2 l3 match Hn in _ = w return valid_holed w
                                            with Logic.eq_refl => vh' end l4) ;
    last by rewrite Hproof ; destruct Hn.
  intro H ; inversion H.
  apply app_inv_head in H1.
  apply Eqdep.EqdepTheory.inj_pair2 in H4.
  rewrite H1 H4.
  by rewrite Hproof ; destruct Hn.
Qed.
  
Lemma vfill_decrease n (vh1:valid_holed (S n)) vh2 es :
  vh_decrease vh1 = Some vh2 -> vfill vh1 es = vfill vh2 es.
Proof.
  set (m := S n) in vh1.
  pose (Logic.eq_refl : m = S n) as Hm.
  change vh1 with match Hm in _ = w return valid_holed w with
                  | Logic.eq_refl => vh1 end.
  clearbody m Hm.
  generalize dependent n.
  induction vh1 ; intros m vh2 Hm.
  - destruct n => //.
    pose proof (eq_add_S _ _ Hm) as Hn.
    assert (Hm = f_equal S Hn) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease match Hm in _ = w return valid_holed w with
                         | Logic.eq_refl => VH_base (S n) l l0 end) with
      match Hn in _ = w return option (valid_holed w) with
      | Logic.eq_refl => vh_decrease (VH_base (S n) l l0) end ;
      last by rewrite Hproof ; destruct Hn.
    simpl.
    rewrite Hproof.
    destruct Hn. simpl.
    intro H ; inversion H ; subst => //=.
  - pose proof (eq_add_S _ _ Hm) as Hn.
    assert (Hm = f_equal S Hn) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease match Hm in _ = w return valid_holed w with
                         | Logic.eq_refl => VH_rec l n0 l0 vh1 l1 end) with
      match Hn in _ = w return option (valid_holed w) with
      | Logic.eq_refl => vh_decrease (VH_rec l n0 l0 vh1 l1) end ;
      last by rewrite Hproof ; destruct Hn.
    simpl.
    destruct n ; first by destruct Hn.
    destruct m => //.
    pose proof (eq_add_S _ _ Hn) as Hp.
    assert (Hn = f_equal S Hp) as Hproof'.
    apply Eqdep.EqdepTheory.UIP.
    replace  match Hn in (_ = w) return (option (valid_holed w)) with
             | Logic.eq_refl =>
                 match vh_decrease vh1 with
                 | Some vh' => Some (VH_rec l n0 l0 vh' l1)
                 | None => None
                 end
             end with match vh_decrease match Hn in (_ = w) return valid_holed w with
                                        | Logic.eq_refl => vh1 end with
                      | Some vh' => Some (VH_rec l n0 l0 vh' l1)
                      | None => None end ;
      last by rewrite Hproof' ; destruct Hp.
    destruct (vh_decrease _) eqn:Hdecr1 => //.
    apply IHvh1 in Hdecr1.
    intro H ; inversion H ; subst  => /=.
    simpl in Hdecr1.
    by rewrite Hdecr1.
Qed.    

Lemma vh_decrease_push_const m (vh : valid_holed (S m)) vs vh' :
  vh_decrease vh = Some vh' ->
  vh_decrease (vh_push_const vh vs) = Some (vh_push_const vh' vs).
Proof.
  set (n := S m) in vh.
  pose (Logic.eq_refl : n = S m) as Hn.
  change vh with (match Hn in _ = w return valid_holed w with
                  | Logic.eq_refl => vh end).
  clearbody n Hn.
  destruct vh.
  - destruct n => //.
    pose proof (eq_add_S _ _ Hn) as Hm.
    assert (Hn = f_equal S Hm) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease (match Hn in _ = w return (valid_holed w) with
                          | Logic.eq_refl => VH_base (S n) l l0 end)) with
      (match Hm in _ = w return (option (valid_holed w)) with
       | Logic.eq_refl => vh_decrease (VH_base (S n) l l0) end) ;
      last by rewrite Hproof ; destruct Hm.
    replace (vh_decrease (vh_push_const (match Hn in (_ = w) return (valid_holed w) with
                                         | Logic.eq_refl => VH_base (S n) l l0 end) vs))
      with (match Hm in _ = w return option (valid_holed w) with
            | Logic.eq_refl => vh_decrease (VH_base (S n) (vs ++ l) l0) end) ;
      last by rewrite Hproof ; destruct Hm.
    destruct Hm => //=.
    intro H ; inversion H => //=.
  - pose proof (eq_add_S _ _ Hn) as Hm.
    assert (Hn = f_equal S Hm) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease (match Hn in _ = w return (valid_holed w) with
                          | Logic.eq_refl => VH_rec l n0 l0 vh l1 end)) with
      (match Hm in _ = w return (option (valid_holed w)) with
       | Logic.eq_refl => vh_decrease (VH_rec l n0 l0 vh l1) end) ;
      last by rewrite Hproof ; destruct Hm.
    replace (vh_decrease (vh_push_const (match Hn in (_ = w) return (valid_holed w) with
                                         | Logic.eq_refl => VH_rec l n0 l0 vh l1 end) vs))
      with (match Hm in _ = w return option (valid_holed w) with
            | Logic.eq_refl => vh_decrease (VH_rec (vs ++ l) n0 l0 vh l1) end) ;
      last by rewrite Hproof ; destruct Hm.
    destruct Hm => //=.
    destruct n => //=.
    destruct (vh_decrease vh) => //=.
    intro H ; inversion H => //=.
Qed.

Lemma vh_decrease_push_const_inv m (vh : valid_holed (S m)) vs vh' :
  vh_decrease (vh_push_const vh vs) = Some vh' ->
  exists vh'', vh_decrease vh = Some vh'' /\ vh_push_const vh'' vs = vh'.
Proof.
  set (n := S m) in vh.
  pose (Logic.eq_refl : n = S m) as Hn.
  change vh with (match Hn in _ = w return valid_holed w with
                  | Logic.eq_refl => vh end) in *.
  clearbody n Hn.
  generalize dependent m.
  induction vh ; intros m vh' Hn.
  - destruct n => //.
    pose proof (eq_add_S _ _ Hn) as Hm.
    assert (Hn = f_equal S Hm) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease (match Hn in _ = w return (valid_holed w) with
                          | Logic.eq_refl => VH_base (S n) l l0 end)) with
      (match Hm in _ = w return (option (valid_holed w)) with
       | Logic.eq_refl => vh_decrease (VH_base (S n) l l0) end) ;
      last by rewrite Hproof ; destruct Hm.
    replace (vh_decrease (vh_push_const (match Hn in (_ = w) return (valid_holed w) with
                                         | Logic.eq_refl => VH_base (S n) l l0 end) vs))
      with (match Hm in _ = w return option (valid_holed w) with
            | Logic.eq_refl => vh_decrease (VH_base (S n) (vs ++ l) l0) end) ;
      last by rewrite Hproof ; destruct Hm.
    exists (VH_base m l l0).
    split.
    destruct Hm => //=.
    simpl in H. destruct Hm => //=.
    by inversion H.
  - pose proof (eq_add_S _ _ Hn) as Hm.
    assert (Hn = f_equal S Hm) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease (vh_push_const (match Hn in (_ = w) return (valid_holed w) with
                                         | Logic.eq_refl => VH_rec l n0 l0 vh l1 end) vs))
      with 
      (vh_decrease (vh_push_const (VH_rec l n0 l0 (match Hm in _ = w return valid_holed w
                                                   with Logic.eq_refl => vh end) l1) vs)) ;
      last by rewrite Hproof ; destruct Hm.
    simpl. destruct m => //.
    destruct (vh_decrease _) eqn:Hdecr => //.
    intro Hvh'.

    destruct n => //.
    pose proof (eq_add_S _ _ Hm) as Hp.
    assert (Hm = f_equal S Hp) as Hproof'.
    apply Eqdep.EqdepTheory.UIP.
    destruct (IHvh m (vh_push_const v vs) Hm) as (vh'' & Hdecr' & Hpush).    
    erewrite vh_decrease_push_const => //.
    exists (VH_rec l n0 l0 vh'' l1).
    split.
    replace ( vh_decrease
                match Hn in (_ = w) return (valid_holed w) with
                | Logic.eq_refl => VH_rec l n0 l0 vh l1
                end )
      with  ( match Hm in _ = w return option (valid_holed w) with
              | Logic.eq_refl => vh_decrease (VH_rec l n0 l0 vh l1) end) ;
      last by rewrite Hproof Hproof' ; destruct Hp.
    simpl.
    replace (  match Hm in (_ = w) return (option (valid_holed w)) with
               | Logic.eq_refl =>
                   match vh_decrease vh with
                   | Some vh'0 => Some (VH_rec l n0 l0 vh'0 l1)
                   | None => None
                   end
               end) with
      (match vh_decrease (match Hm in (_ = w) return (valid_holed w) with
                          | Logic.eq_refl => vh end) with
       | Some vh'0 => Some (VH_rec l n0 l0 vh'0 l1)
       | None => None end) ;
      last by rewrite Hproof' ; destruct Hp.
    by rewrite Hdecr'.
    simpl.
    inversion Hvh'.
    apply vh_push_const_inj in Hpush.
    by rewrite Hpush.
Qed.
    
Lemma sh_push_const_app sh vs1 vs2 :
  sh_push_const sh (vs1 ++ vs2) =
    sh_push_const (sh_push_const sh vs2) vs1.
Proof.
  destruct sh => //= ; rewrite catA => //.
Qed.

Lemma vh_push_const_app n (vh : valid_holed n) vs1 vs2 :
  vh_push_const vh (vs1 ++ vs2) =
    vh_push_const (vh_push_const vh vs2) vs1.
Proof.
  destruct vh => //= ; rewrite catA => //.
Qed.

Lemma llh_push_const_app lh vs1 vs2 :
  llh_push_const lh (vs1 ++ vs2) =
    llh_push_const (llh_push_const lh vs2) vs1.
Proof.
  destruct lh => //= ; rewrite catA => //.
Qed.

Lemma sh_push_const_nil sh :
  sh_push_const sh [] = sh.
Proof. destruct sh => //=. Qed.

Lemma vh_push_const_nil n (vh : valid_holed n) :
  vh_push_const vh [] = vh.
Proof. destruct vh => //=. Qed.

Lemma llh_push_const_nil lh :
  llh_push_const lh [] = lh.
Proof. destruct lh => //=. Qed. 

Lemma sh_append_app sh es1 es2 :
  sh_append sh (es1 ++ es2) =
    sh_append (sh_append sh es1) es2.
Proof.
  destruct sh => //= ; rewrite catA => //.
Qed.

Lemma vh_append_app n (vh : valid_holed n) es1 es2 :
  vh_append vh (es1 ++ es2) =
    vh_append (vh_append vh es1) es2.
Proof.
  destruct vh => //= ; rewrite catA => //.
Qed.

Lemma llh_append_app lh es1 es2 :
  llh_append lh (es1 ++ es2) =
    llh_append (llh_append lh es1) es2.
Proof.
  destruct lh => //= ; rewrite catA => //. 
Qed.

Lemma sh_append_nil sh :
  sh_append sh [] = sh.
Proof. destruct sh => /= ; rewrite cats0 => //. Qed.

Lemma vh_append_nil n (vh : valid_holed n) :
  vh_append vh [] = vh.
Proof. destruct vh => /= ; rewrite cats0 => //. Qed.

Lemma llh_append_nil lh :
  llh_append lh [] = lh.
Proof. destruct lh => /= ; rewrite cats0 => //. Qed. 

Lemma sh_push_const_append sh vs es :
  sh_push_const (sh_append sh es) vs =
    sh_append (sh_push_const sh vs) es.
Proof.
  destruct sh => //=.
Qed.

Lemma vh_push_const_append n (vh : valid_holed n) vs es :
  vh_push_const (vh_append vh es) vs =
    vh_append (vh_push_const vh vs) es.
Proof.
  destruct vh => //=.
Qed.

Lemma llh_push_const_append lh vs es :
  llh_push_const (llh_append lh es) vs =
    llh_append (llh_push_const lh vs) es.
Proof.
  destruct lh => //=. 
Qed.

Lemma vfill_increase m (vh : valid_holed m) es :
  vfill (vh_increase vh ) es = vfill vh es.
Proof.
  induction vh => //=.
  by rewrite IHvh.
Qed.

Lemma vh_decrease_increase m (vh : valid_holed m) :
  vh_decrease (vh_increase vh) = Some vh.
Proof.
  induction vh => //=.
  by rewrite IHvh.
Qed.  

Lemma vh_increase_push_const m (vh : valid_holed m) vs :
  vh_increase (vh_push_const vh vs) = vh_push_const (vh_increase vh) vs.
Proof. destruct vh => //=. Qed.

Lemma vh_increase_repeat_push_const m (vh : valid_holed m) vs j :
  vh_increase_repeat (vh_push_const vh vs) j = vh_push_const (vh_increase_repeat vh j) vs.
Proof. induction j => //=. rewrite IHj. by rewrite vh_increase_push_const. Qed.

Lemma S_plus m n : S (m + n) = m + S n. Proof. induction m => //=. by rewrite IHm. Defined.

Lemma vh_increase_repeat_rec m (vh : valid_holed m) bef n es aft j :
  vh_increase_repeat (VH_rec bef n es vh aft) j =
    match S_plus j m in _ = w return valid_holed w with
    | Logic.eq_refl => VH_rec bef n es (vh_increase_repeat vh j) aft end.
Proof.
  induction j ; first done.
  unfold vh_increase_repeat ; fold vh_increase_repeat.
  unfold S_plus ; simpl.
  assert (S_plus j m = S_plus j m) ; first done.
  unfold S_plus in H at 1.
  rewrite H.
  rewrite IHj.
  unfold eq_ind_r, eq_ind.
  set (Hp := S_plus j m).
  clearbody Hp.
  destruct Hp => //=.
Qed.

Lemma vfill_to_lfilled i (vh : valid_holed i) es:
  i >= (lh_depth (lh_of_vh vh)) /\
    lfilled (lh_depth (lh_of_vh vh)) (lh_of_vh vh) es (vfill vh es).
Proof.
  induction vh => //=.
  - split ; first lia.
    unfold lfilled, lfill.
    induction l => //=.
    destruct (const_list _) => //.
  - destruct IHvh as (Hk & Hfill).
    split ; first lia.
    unfold lfilled, lfill => /=.
    fold lfill.
    unfold lfilled in Hfill.
    destruct (lfill _ _ _) => //.
    move/eqP in Hfill; subst.
    induction l => //=.
    destruct (const_list _) => //.
Qed.

Lemma sfill_to_lfilled sh es :
  lfilled (lh_depth (lh_of_sh sh)) (lh_of_sh sh) es (sfill sh es).
Proof.
  induction sh => //=.
  - unfold lfilled, lfill.
    induction l => //=.
    destruct (const_list _) => //.
  - unfold lfilled, lfill => /= ; fold lfill.
    unfold lfilled in IHsh.
    destruct (lfill _ _ _) => //.
    move/eqP in IHsh; subst.
    induction l => //=.
    destruct (const_list _) => //.
Qed.
  
Lemma lfilled_to_vfill k lh es LI i :
  lfilled k lh es LI -> i >= k -> exists vh, vh_of_lh lh i = Some vh /\ vfill vh es = LI.
Proof.
  generalize dependent lh ; generalize dependent LI ; generalize dependent i.
  induction k ; intros i LI lh.
  - unfold lfilled, lfill.
    destruct lh => //.
    destruct (const_list l) eqn:Hl => //.
    intros HLI _ ; move/eqP in HLI; subst.
    unfold vh_of_lh.
    induction l => /=.
    + exists (VH_base i [] l0) => //=.
    + destruct a => //=.
      destruct b => //=.
      rewrite list_extra.cons_app.
      rewrite - cat_app.
      apply IHl in Hl as (vh & ? & ?).
      destruct (those _) eqn:Hthose => //.
      erewrite those_app => //=.
      eexists ; split => //=.
      replace (v_to_e_list l1) with l ; first done.
      clear - Hthose.
      generalize dependent l1.
      induction l => //= ; intros.
      * unfold those in Hthose.
        simpl in Hthose.
        inversion Hthose => //.
      * destruct a => //=.
        destruct b => //=.
        rewrite list_extra.cons_app in Hthose.
        rewrite - cat_app in Hthose.
        apply those_app_inv in Hthose as (tl1 & tl2 & Hv0 & Hthose & Htl) => //.
        unfold those in Hv0.
        inversion Hv0 ; subst.
        erewrite IHl => //=.
  - unfold lfilled, lfill ; fold lfill.
    destruct lh => //.
    destruct (const_list l) eqn:Hl => //.
    destruct (lfill _ _ _) eqn:Hfill => //.
    intros HLI Hi ; move/eqP in HLI ; subst.
    destruct i ; first lia.
    assert (i >= k) ; first lia.
    apply (IHk i l2 lh) in H as (vh & Hvh & Hvfill) ;
      last by unfold lfilled ; rewrite Hfill.
    simpl.
    rewrite Hvh.
    induction l => //=.
    + eexists ; split => //=.
      by rewrite Hvfill.
    + destruct a => //=.
      destruct b => //=.
      rewrite list_extra.cons_app.
      rewrite - cat_app.
      specialize (IHl Hl) as (vh0 & Hvh0 & Hvfill0).
      destruct (those (map _ l)) eqn:Hthose => //.
      erewrite those_app => //.
      eexists ; split => //=.
      inversion Hvh0 ; subst.
      simpl in Hvfill0.
      by rewrite Hvfill0.
Qed.      

Lemma lfilled_implies_llfill k lh es LI :
  lfilled k lh es LI ->
  exists llh, llfill llh es = LI.
Proof.
  intro Hfill.
  unfold lfilled, lfill in Hfill.
  generalize dependent lh ; generalize dependent LI ;
    induction k ; intros ; destruct lh => //.
  destruct (const_list l) eqn:Hl => //.
  move/eqP in Hfill; subst LI.
  induction l.
  exists (LL_base [] l0) => //=.
  destruct a => //. destruct b => //.
  simpl in Hl.
  destruct (IHl Hl) as [llh Hfill].
  exists (llh_push_const llh [v]) => /=.
  rewrite - Hfill.
  by destruct llh => //=.
  fold lfill in Hfill.
  destruct (const_list l) eqn:Hl => //.
  destruct (lfill _ _ _) eqn:Hfill' => //.
  fold lfill in IHk.
  move/eqP in Hfill; subst LI.
  specialize (IHk l2 lh).
  rewrite Hfill' in IHk.
  destruct IHk as [llh <-] => //.
  induction l.
  exists (LL_label [] n l0 llh l1) => //=.
  destruct a => //. destruct b => //.
  simpl in Hl.
  destruct (IHl Hl) as [llh0 Hfill].
  exists (llh_push_const llh0 [v]) => /=.
  rewrite - Hfill.
  by destruct llh0 => //=. 
Qed.

Lemma llfill_all_values' lh vs e lh' n0 es vs' LI :
  llfill lh (vs ++ [e]) = LI ->
  llfill lh' [AI_label n0 es vs'] = LI ->
  const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
  (is_const e = false ) ->
  (e <> AI_trap) ->
  (forall n es LI, e <> AI_label n es LI) ->
  (forall n f LI, e <> AI_local n f LI) ->
  False.
Proof.
  cut (forall n,
          length_rec LI < n ->
          llfill lh (vs ++ [e]) = LI ->
          llfill lh' [AI_label n0 es vs'] = LI ->
          const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
          (is_const e = false ) ->
          e <> AI_trap ->
          (forall n es LI, e <> AI_label n es LI) ->
          (forall n f LI, e <> AI_local n f LI) ->
          False).
  { intro Hn ; apply (Hn (S (length_rec LI))) ; lia. }
  intro n. generalize dependent LI. generalize dependent es. generalize dependent n0.
  generalize dependent vs'. generalize dependent lh'. 
  generalize dependent e. generalize dependent vs. generalize dependent lh.
  induction n ;
    intros lh vs e lh' vs' n0 es LI Hlab Hfill Hfill' Hvs Hvs' He He' Hlabe Hloce ;
    first by inversion Hlab.
  destruct lh as [bef aft | bef n' l lh aft | bef n' l lh aft].
  { simpl in Hfill.
    destruct lh' as [bef' aft' | | ]. 
    { simpl in Hfill'.
      rewrite - Hfill in Hfill'. rewrite <- app_assoc in Hfill'.
      rewrite app_assoc in Hfill'.
      apply first_values in Hfill' as (? & Hee & ?) => //. 
      apply (Hlabe _ _ _ (Logic.eq_sym Hee)).
      apply v_to_e_is_const_list.
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff ; split => //.
      apply v_to_e_is_const_list. 
    } 
    { simpl in Hfill'. rewrite - Hfill in Hfill'.
      rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
      apply first_values in Hfill' as ( _ & Habs & _ ) ; (try done) ; try by intros [? ?].
      apply (Hlabe _ _ _ (Logic.eq_sym Habs)).
      apply v_to_e_is_const_list.
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      split => //. apply v_to_e_is_const_list. }
     { simpl in Hfill'. rewrite - Hfill in Hfill'.
      rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
      apply first_values in Hfill' as ( _ & Habs & _ ) ; (try done) ; try by intros [? ?].
      apply (Hloce _ _ _ (Logic.eq_sym Habs)).
      apply v_to_e_is_const_list.
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      split => //. apply v_to_e_is_const_list. }

  }
  { simpl in Hfill.
    destruct lh' as [bef' aft' | bef' n'' l' lh' aft' | bef' n'' l' lh' aft' ].
    { simpl in Hfill'. rewrite - Hfill in Hfill'.
      apply first_values in Hfill' as ( _ & Habs & _ ) => //= ; try by apply v_to_e_is_const_list.
      inversion Habs ; subst ; clear Habs.
      destruct lh. { simpl in Hvs'.
                     destruct Hvs' as [Hvs' | Hvs'].
                     { apply const_list_split in Hvs' as [? [[? ?]%const_list_split ?]%const_list_split].
                       destruct e;try done. destruct b;try done. }
                     { erewrite !app_assoc in Hvs'. rewrite -app_assoc in Hvs'.
                       rewrite -(app_nil_l [AI_trap]) in Hvs'.
                       apply first_values in Hvs' as [? [? ?]];auto;try by intros [? ?].
                       simplify_eq. apply const_list_concat;auto.
                       apply v_to_e_is_const_list.
                  } }
      simpl in Hvs'.
      destruct Hvs' as [Hvs' | Hvs'].
      { apply const_list_split in Hvs' as [? [? _]%andb_true_iff]. done. }
      { do 2 destruct l0 => //. }
      simpl in Hvs'.
       destruct Hvs' as [Hvs' | Hvs'].
      { apply const_list_split in Hvs' as [? [? _]%andb_true_iff]. done. }
      { do 2 destruct l0 => //. }
    }
  simpl in Hfill'. rewrite - Hfill in Hfill'.
  apply first_values in Hfill' as ( Hl & Hlab' & _ ) => //= ; try by left.
  inversion Hlab' ; subst.
  eapply (IHn lh vs e lh' vs' n0 es _) => //=.
  rewrite app_length_rec in Hlab.
  rewrite list_extra.cons_app in Hlab. 
  rewrite app_length_rec in Hlab. simpl in Hlab.
  rewrite Nat.add_0_r in Hlab. rewrite <- Nat.add_succ_l in Hlab.
  fold (length_rec (llfill lh (vs ++ [e]))) in Hlab.
  rewrite - H2 in Hlab. lia.
  apply v_to_e_is_const_list. apply v_to_e_is_const_list.

  simpl in Hfill'. rewrite - Hfill in Hfill'.
  apply first_values in Hfill' as ( Hl & Hlab' & _ ) => //= ; try by left.
  apply v_to_e_is_const_list. apply v_to_e_is_const_list.
  }
  simpl in Hfill.
  destruct lh'. 
  simpl in Hfill' ; rewrite - Hfill' in Hfill.
  apply first_values in Hfill as (_ & ? & _) => //.
  apply v_to_e_is_const_list.
  apply v_to_e_is_const_list.
  simpl in Hfill' ; rewrite - Hfill' in Hfill.
  apply first_values in Hfill as (_ & ? & _) => //.
  all:try apply v_to_e_is_const_list.
  simpl in Hfill' ; rewrite - Hfill' in Hfill.
  apply first_values in Hfill as (Hl & Hloc & _) => //.
  all:try apply v_to_e_is_const_list.
  inversion Hloc ; subst.
  eapply (IHn lh vs e lh' vs' n0 es _) => //=.
  rewrite app_length_rec in Hlab.
  rewrite list_extra.cons_app in Hlab. 
  rewrite app_length_rec in Hlab. simpl in Hlab.
  rewrite Nat.add_0_r in Hlab. rewrite <- Nat.add_succ_l in Hlab.
  fold (length_rec (llfill lh' [AI_label n0 es vs'])) in Hlab.
  lia.
Qed.

Lemma lfilled_all_values' i lh vs e i' lh' n0 es vs' LI :
  lfilled i lh (vs ++ [e]) LI ->
  lfilled i' lh' [AI_label n0 es vs'] LI ->
  const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
  (is_const e = false ) ->
  e <> AI_trap ->
  (forall n es LI, e <> AI_label n es LI) ->
  False.
Proof.
  cut (forall n,
          length_rec LI < n ->
          lfilled i lh (vs ++ [e]) LI ->
          lfilled i' lh' [AI_label n0 es vs'] LI ->
          const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
          (is_const e = false ) ->
          e <> AI_trap ->
          (forall n es LI, e <> AI_label n es LI) ->
          False).
  { intro Hn ; apply (Hn (S (length_rec LI))) ; lia. }
  intro n. generalize dependent LI. generalize dependent es. generalize dependent n0.
  generalize dependent vs'. generalize dependent lh'. generalize dependent i'.
  generalize dependent e. generalize dependent vs. generalize dependent lh.
  generalize dependent i.
  induction n ;
    intros i lh vs e i' lh' vs' n0 es LI Hlab Hfill Hfill' Hvs Hvs' He He' Hlabe ;
    first by inversion Hlab.
  unfold lfilled, lfill in Hfill. destruct i.
  { destruct lh as [bef aft|] => //. 
    remember (const_list bef) as b eqn:Hbef ; destruct b => //. 
    move/eqP in Hfill.
    unfold lfilled, lfill in Hfill' ; destruct i'.
    { destruct lh' as [bef' aft'|] => //. 
      remember (const_list bef') as b0 eqn:Hbef' ; destruct b0 => //. 
      move/eqP in Hfill'.
      rewrite Hfill in Hfill'. rewrite <- app_assoc in Hfill'.
      rewrite app_assoc in Hfill'. 
      apply first_values in Hfill' as (? & Hee & ?) ; (try done) ; (try by intros [? ?]) ;
        try by unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      apply (Hlabe _ _ _ Hee).
    } 
    fold lfill in Hfill'. destruct lh' => //. 
    remember (const_list l) as b ; destruct b => //. 
    destruct (lfill i' lh' _) => //. 
    move/eqP in Hfill'. rewrite Hfill in Hfill'.
    rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
    apply first_values in Hfill' as ( _ & Habs & _ ) ; (try done) ; try by intros [? ?].
    apply (Hlabe _ _ _ Habs).
    unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
  fold lfill in Hfill. 
  destruct lh as [| bef n' l lh aft] => //. 
  remember (const_list bef) as b ; destruct b => //. 
  remember (lfill i lh (vs ++ [e])) as les ; destruct les => //. 
  move/eqP in Hfill.
  unfold lfilled, lfill in Hfill' ; destruct i'.
  { destruct lh' as [bef' aft' |] => //. 
    remember (const_list bef') as b ; destruct b => //. 
    move/eqP in Hfill'. rewrite Hfill in Hfill'.
    apply first_values in Hfill' as ( _ & Habs & _ ) => //= ; try by intros [? ?].
    inversion Habs ; subst ; clear Habs.
    destruct i. { unfold lfill in Heqles. destruct lh ; last by inversion Heqles.
                  destruct (const_list l) eqn:Hconst; inversion Heqles. rewrite H0 in Hvs'.
                  simplify_eq. destruct Hvs' as [Hvs' | Hvs'].
                  { apply const_list_split in Hvs' as [? [[? ?]%const_list_split ?]%const_list_split].
                    destruct e;try done. destruct b;try done. (* apply He;eauto. *) }
                  { erewrite !app_assoc in Hvs'. rewrite -app_assoc in Hvs'.
                    rewrite -(app_nil_l [AI_trap]) in Hvs'.
                    apply first_values in Hvs' as [? [? ?]];auto;try by intros [? ?].
                    simplify_eq. apply const_list_concat;auto.
                  } }
    unfold lfill in Heqles ; fold lfill in Heqles.
    destruct lh ; first by inversion Heqles.
    destruct (const_list l) eqn:Hconst; last by inversion Heqles.
    destruct (lfill i _ _) ; inversion Heqles.
    rewrite H0 in Hvs'. destruct Hvs' as [Hvs' | Hvs'].
    { apply const_list_split in Hvs' as [? [? _]%andb_true_iff]. done. }
    { do 2 destruct l =>//. }
  }
  fold lfill in Hfill'.
  destruct lh' as [| bef' n'' l' lh' aft'] => //. 
  remember (const_list bef') as b ; destruct b => //.  
  remember (lfill i' lh' _) as les0 ; destruct les0  => //. 
  move/eqP in Hfill'. rewrite Hfill in Hfill'.
  apply first_values in Hfill' as ( Hl & Hlab' & _ ) => //= ; try by left.
  inversion Hlab' ; subst.
  apply (IHn i lh vs e i' lh' vs' n0 es l1) => //=.
  rewrite app_length_rec in Hlab.
  replace (AI_label n'' l' l1 :: aft) with ([AI_label n'' l' l1] ++ aft) in Hlab => //=.
  rewrite app_length_rec in Hlab. simpl in Hlab.
  rewrite Nat.add_0_r in Hlab. rewrite <- Nat.add_succ_l in Hlab.
  fold (length_rec l1) in Hlab. lia.
  unfold lfilled ; rewrite <- Heqles ; done.
  unfold lfilled ; rewrite <- Heqles0 ; done.
Qed.

Lemma llfill_all_values'' lh vs e lh' n0 es vs' LI :
  llfill lh (vs ++ [e]) = LI ->
  llfill lh' [AI_local n0 es vs'] = LI ->
  const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
  (is_const e = false ) ->
  e <> AI_trap ->
  (forall n es LI, e <> AI_label n es LI) ->
  (forall n f LI, e <> AI_local n f LI) ->
  False.
Proof.
   cut (forall n,
          length_rec LI < n ->
          llfill lh (vs ++ [e]) = LI ->
          llfill lh' [AI_local n0 es vs'] = LI ->
          const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
          (is_const e = false  ) ->
          e <> AI_trap ->
          (forall n es LI, e <> AI_label n es LI) ->
          (forall n f LI, e <> AI_local n f LI) ->
          False).
  { intro Hn ; apply (Hn (S (length_rec LI))) ; lia. }
  intro n. generalize dependent LI. generalize dependent es. generalize dependent n0.
  generalize dependent vs'. generalize dependent lh'. 
  generalize dependent e. generalize dependent vs. generalize dependent lh.
  induction n ;
    intros lh vs e lh' vs' n0 es LI Hlab Hfill Hfill' Hvs Hvs' He He' Hlabe Hloce ;
    first by inversion Hlab.
  destruct lh as [bef aft | bef n' l lh aft | bef n' l lh aft].
  { simpl in Hfill.
    destruct lh' as [bef' aft' | | ]. 
    { simpl in Hfill'.
      rewrite - Hfill in Hfill'. rewrite <- app_assoc in Hfill'.
      rewrite app_assoc in Hfill'. 
      apply first_values in Hfill' as (? & Hee & ?) => //. 
      apply (Hloce _ _ _ (Logic.eq_sym Hee)).
      apply v_to_e_is_const_list.
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff ; split => //.
      apply v_to_e_is_const_list. 
    } 
    { simpl in Hfill'. rewrite - Hfill in Hfill'.
      rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
      apply first_values in Hfill' as ( _ & Habs & _ ) ; (try done) ; try by intros [? ?].
      apply (Hlabe _ _ _ (Logic.eq_sym Habs)).
      apply v_to_e_is_const_list.
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      split => //. apply v_to_e_is_const_list. }
     { simpl in Hfill'. rewrite - Hfill in Hfill'.
      rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
      apply first_values in Hfill' as ( _ & Habs & _ ) ; (try done) ; try by intros [? ?].
      apply (Hloce _ _ _ (Logic.eq_sym Habs)).
      apply v_to_e_is_const_list.
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      split => //. apply v_to_e_is_const_list. }

  }
  { simpl in Hfill.
    destruct lh' as [bef' aft' | bef' n'' l' lh' aft' | bef' n'' l' lh' aft' ].
    { simpl in Hfill'. rewrite - Hfill in Hfill'.
      apply first_values in Hfill' as ( _ & Habs & _ ) => //= ; try by apply v_to_e_is_const_list.
    }
  simpl in Hfill'. rewrite - Hfill in Hfill'.
  apply first_values in Hfill' as ( Hl & Hlab' & _ ) => //= ; try by left.
  inversion Hlab' ; subst.
  eapply (IHn lh vs e lh' vs' n0 es _) => //=.
  rewrite app_length_rec in Hlab.
  rewrite list_extra.cons_app in Hlab. 
  rewrite app_length_rec in Hlab. simpl in Hlab.
  rewrite Nat.add_0_r in Hlab. rewrite <- Nat.add_succ_l in Hlab.
  fold (length_rec (llfill lh (vs ++ [e]))) in Hlab.
  rewrite - H2 in Hlab. lia.
  apply v_to_e_is_const_list. apply v_to_e_is_const_list.

  simpl in Hfill'. rewrite - Hfill in Hfill'.
  apply first_values in Hfill' as ( Hl & Hlab' & _ ) => //= ; try by left.
  apply v_to_e_is_const_list. apply v_to_e_is_const_list.
  }
  simpl in Hfill.
  destruct lh'. 
  simpl in Hfill' ; rewrite - Hfill' in Hfill.
  apply first_values in Hfill as (_ & Habs & _) => //.
   inversion Habs ; subst ; clear Habs.
      destruct lh. { simpl in Hvs'.
                     destruct Hvs' as [Hvs' | Hvs'].
                     { apply const_list_split in Hvs' as [? [[? ?]%const_list_split ?]%const_list_split].
                       destruct e;try done. destruct b;try done. }
                     { erewrite !app_assoc in Hvs'. rewrite -app_assoc in Hvs'.
                       rewrite -(app_nil_l [AI_trap]) in Hvs'.
                       apply first_values in Hvs' as [? [? ?]];auto;try by intros [? ?].
                       simplify_eq. apply const_list_concat;auto.
                       apply v_to_e_is_const_list.
                  } }
      simpl in Hvs'.
      destruct Hvs' as [Hvs' | Hvs'].
      { apply const_list_split in Hvs' as [? [? _]%andb_true_iff]. done. }
      { do 2 destruct l => //. }
      simpl in Hvs'.
       destruct Hvs' as [Hvs' | Hvs'].
      { apply const_list_split in Hvs' as [? [? _]%andb_true_iff]. done. }
      { do 2 destruct l => //. } 
  apply v_to_e_is_const_list.
  apply v_to_e_is_const_list.
  simpl in Hfill' ; rewrite - Hfill' in Hfill.
  apply first_values in Hfill as (_ & ? & _) => //.
  all:try apply v_to_e_is_const_list.
  simpl in Hfill' ; rewrite - Hfill' in Hfill.
  apply first_values in Hfill as (Hl & Hloc & _) => //.
  all:try apply v_to_e_is_const_list.
  inversion Hloc ; subst.
  eapply (IHn lh vs e lh' vs' n0 es _) => //=.
  rewrite app_length_rec in Hlab.
  rewrite list_extra.cons_app in Hlab. 
  rewrite app_length_rec in Hlab. simpl in Hlab.
  rewrite Nat.add_0_r in Hlab. rewrite <- Nat.add_succ_l in Hlab.
  fold (length_rec (llfill lh' [AI_local n0 es vs'])) in Hlab.
  lia.
Qed.

Lemma lfilled_br_and_reduce s f es LI s' f' es' i j lh vs k lh' :
  reduce s f es s' f' es' ->
  const_list vs ->
  i <= j ->
  lfilled i lh (vs ++ [AI_basic (BI_br j)]) LI ->
  lfilled k lh' es LI ->
  False.
Proof.
  intros Hred Hvs Hi H1 Hes.
  cut (forall n, length_rec es < n -> False).
  { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
  intro n0. 
  generalize dependent es. generalize dependent es'.  generalize dependent k.
  generalize dependent lh'.
  induction n0 ; intros lh1 k es' es1 Hred2 Hfill Hlab ; first by lia.
  induction Hred2 ; try by (rewrite_cats1_list; specialize (lfilled_first_values H1 Hfill) as [Hcontra _] => //; inversion Hcontra).
  (* reduce_simple *)
  { destruct H; try by (rewrite_cats1_list; specialize (lfilled_first_values H1 Hfill) as [Hcontra _] => //; inversion Hcontra).
    (* const *)
    - apply (lfilled_all_values' H1 Hfill) => //=.
      by left. 
    - apply (lfilled_all_values' H1 Hfill) => //=. by right.
    (* br itself *)
    - assert (lfilled (S i0) (LH_rec [] n es lh0 []) (vs0 ++ [AI_basic (BI_br i0)])
                      [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i0 _ _) => //. 
      move/eqP in H2 ; by subst.
      destruct (lfilled_trans Hfill' Hfill) as [lh' Hfillbr].
      specialize (lfilled_first_values H1 Hfillbr) as (? & ? & ?) => //=.
      inversion H3 ; subst. lia.
    (* tee_local *)
    - replace [v ; AI_basic (BI_tee_local i0)] with
        ([v] ++ [AI_basic (BI_tee_local i0)])%SEQ in Hfill => //=.
      assert (AI_basic (BI_br j) = AI_basic (BI_tee_local i0)) => //=.
      apply (lfilled_first_values H1 Hfill) => //=.
      by rewrite H.
    (* trap *)
    - destruct (lfilled_trans H0 Hfill) as [lh' Hfill'].
      replace [AI_trap] with ([] ++ [AI_trap])%SEQ in Hfill' => //=.
      assert (AI_basic (BI_br j) = AI_trap) => //=.
      apply (lfilled_first_values H1 Hfill') => //=.
  }
  (* invoke *)
  specialize (lfilled_first_values H1 Hfill) as [Hcontra _] => //.
  subst.
  by apply v_to_e_is_const_list.
  specialize (lfilled_first_values H1 Hfill) as [Habs _] => //.
  subst.
  by apply v_to_e_is_const_list.
  (* label *)
  * destruct (lfilled_trans H Hfill) as [lh' Hfill'].
    apply (IHn0 _ _ _ _ Hred2 Hfill').
    unfold lfilled, lfill in H ; destruct k0.
    { destruct lh0 => //. 
      destruct (const_list l) => //. 
      move/eqP in H.
      destruct l. { destruct l0. { unfold lfilled, lfill in H0 ; simpl in H0.
                                    move/eqP in H0. simpl in H.
                                    rewrite app_nil_r in H.
                                    rewrite app_nil_r in H0. subst.
                                    exfalso ; apply IHHred2 => //=. }
        simpl in H. rewrite H in Hlab.
                     rewrite app_length_rec in Hlab.
                     assert (length_rec (a :: l0) > 0) ;
                       first by (specialize (cons_length_rec a l0)) ; lia.
                     lia. }
      rewrite H in Hlab. do 2 rewrite app_length_rec in Hlab.
      assert (length_rec (a :: l) > 0) ; first by specialize (cons_length_rec a l) ; lia.
      lia. }
    fold lfill in H. destruct lh0 => //. 
    destruct (const_list l) => //. 
    remember (lfill _ _ _) as fill ; destruct fill => //. 
    move/eqP in H. rewrite H in Hlab.
    replace (AI_label n l0 l2 :: l1) with ([AI_label n l0 l2] ++ l1) in Hlab => //=.
    do 2 rewrite app_length_rec in Hlab.
    unfold length_rec in Hlab. simpl in Hlab.
    rewrite <- (Nat.add_0_r (S n0)) in Hlab. rewrite plus_comm in Hlab.
    apply Nat.le_lt_add_lt in Hlab ; try lia. 
    apply lt_S_n in Hlab. rewrite Nat.add_0_r in Hlab.
    assert (lfilled k0 lh0 es l2) as Hfill''.
    { unfold lfilled ; by rewrite <- Heqfill. }
    apply lfilled_length_rec in Hfill''. unfold length_rec.
    unfold length_rec in Hfill''. lia.
Qed.

Lemma lfilled_return_and_reduce s f es LI s' f' es' i lh vs k lh' :
  reduce s f es s' f' es' ->
  const_list vs ->
  lfilled i lh (vs ++ [AI_basic BI_return]) LI ->
  lfilled k lh' es LI ->
  False.
Proof.
  intros Hred Hvs H1 Hes.
  cut (forall n, length_rec es < n -> False).
  { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
  intro n0. 
  generalize dependent es. generalize dependent es'. generalize dependent k.
  generalize dependent lh'.
  induction n0 ; intros lh1 k es' es1 Hred2 Hfill Hlab ; first by lia.
  induction Hred2; try by (rewrite_cats1_list; specialize (lfilled_first_values H1 Hfill) as [Hcontra _] => //; inversion Hcontra).
  (* r_simple *)
  { destruct H; try by (rewrite_cats1_list; specialize (lfilled_first_values H1 Hfill) as [Hcontra _] => //; inversion Hcontra).

    - apply (lfilled_all_values' H1 Hfill) => //=;try by intros [? ?].
      by left.
    - apply (lfilled_all_values' H1 Hfill) => //=. by right. (* by intros [? ?]. *)
    - assert (lfilled (S i0) (LH_rec [] n es lh0 []) (vs0 ++ [AI_basic (BI_br i0)])
                      [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i0 _ _) => //. 
      move/eqP in H2 ; by subst.
      destruct (lfilled_trans Hfill' Hfill) as [lh' Hfillbr].
      specialize (lfilled_first_values H1 Hfillbr) as (? & ? & ?) => //=.
    - replace [v ; AI_basic (BI_tee_local i0)] with
        ([v] ++ [AI_basic (BI_tee_local i0)])%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_tee_local i0)) => //=.
      apply (lfilled_first_values H1 Hfill) => //=.
      by rewrite H.
    - destruct (lfilled_trans H0 Hfill) as [lh' Hfill'].
      replace [AI_trap] with ([] ++ [AI_trap])%SEQ in Hfill' => //=.
      assert (AI_basic BI_return = AI_trap) => //=.
      apply (lfilled_first_values H1 Hfill') => //=. }
  * specialize (lfilled_first_values H1 Hfill) as [Hcontra _ ]=> //=.
    subst; by apply v_to_e_is_const_list.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //=.
    subst ; by apply v_to_e_is_const_list.
  * destruct (lfilled_trans H Hfill) as [lh' Hfill'].
    apply (IHn0 _ _ _ _ Hred2 Hfill').
    unfold lfilled, lfill in H ; destruct k0.
    { destruct lh0 => //.  
      destruct (const_list l) => //. 
      move/eqP in H.
      destruct l. { destruct l0. { unfold lfilled, lfill in H0 ; simpl in H0.
                                   move/eqP in H0. simpl in H.
                                   rewrite app_nil_r in H0.
                                   rewrite app_nil_r in H. subst.
                                   exfalso ; apply IHHred2 => //=. }
        simpl in H. rewrite H in Hlab.
                    rewrite app_length_rec in Hlab.
                    destruct (cons_length_rec a l0) as [ | ? ]; lia. }
      rewrite H in Hlab. do 2 rewrite app_length_rec in Hlab.
      destruct (cons_length_rec a l) as [ | ?] ; lia. }
    fold lfill in H. destruct lh0 => //. 
    destruct (const_list l) => //. 
    remember (lfill _ _ _) as fill ; destruct fill => //. 
    move/eqP in H. rewrite H in Hlab.
    replace (AI_label n l0 l2 :: l1) with ([AI_label n l0 l2] ++ l1) in Hlab => //=.
    do 2 rewrite app_length_rec in Hlab.
    unfold length_rec in Hlab. simpl in Hlab.
    rewrite <- (Nat.add_0_r (S n0)) in Hlab. rewrite plus_comm in Hlab.
    apply Nat.le_lt_add_lt in Hlab ; try lia. 
    apply lt_S_n in Hlab. rewrite Nat.add_0_r in Hlab.
    assert (lfilled k0 lh0 es l2) as Hfill''.
    { unfold lfilled ; by rewrite <- Heqfill. }
    apply lfilled_length_rec in Hfill''. unfold length_rec.
    unfold length_rec in Hfill''. lia.
Qed.

Lemma llfill_first_values lh vs e lh' vs' e' LI :
  llfill lh (vs ++ [::e]) = LI ->
  llfill lh' (vs' ++ [::e']) = LI ->
  const_list vs -> const_list vs' ->
  (is_const e = false) -> (is_const e' = false) ->
  (forall n es LI, e <> AI_label n es LI) ->
  (forall n es LI, e' <> AI_label n es LI) ->
  (forall n f LI, e <> AI_local n f LI) ->
  (forall n f LI, e' <> AI_local n f LI) ->
  e = e' /\ (length vs = length vs' -> (vs = vs' /\ lh = lh')).
Proof.
   cut (forall n,
          length_rec LI < n ->
          llfill lh (vs ++ [::e]) = LI ->
          llfill lh' (vs' ++ [::e']) = LI ->
          const_list vs -> const_list vs' ->
          (is_const e = false) -> (is_const e' = false) ->
          (forall n es LI, e <> AI_label n es LI) -> (forall n es LI, e' <> AI_label n es LI) ->
          (forall n f LI, e <> AI_local n f LI) ->
          (forall n f LI, e' <> AI_local n f LI) ->
          e = e' /\ (length vs = length vs' -> (vs = vs' /\ lh = lh'))).
  { intro Hn ; apply (Hn (S (length_rec LI))) ; lia. }
  intro n. generalize dependent LI. generalize dependent e'.
  generalize dependent vs'. generalize dependent lh'. 
  generalize dependent e. generalize dependent vs. generalize dependent lh.
  induction n ;
    intros lh vs e lh' vs' e' LI Hlab Hfill Hfill' Hvs Hvs' He He' Hlabe Hlabe' Hloce Hloce' ;
    first by inversion Hlab.
  destruct lh as [ bef aft | bef n' l lh aft | bef n' l lh aft ].
  { simpl in Hfill.
    destruct lh' as [bef' aft' | | ].
    { rewrite - Hfill in Hfill'.
      simpl in Hfill'.
      repeat rewrite app_assoc in Hfill'.
      rewrite - (app_assoc (_ ++ vs')) in Hfill'.
      rewrite - (app_assoc (v_to_e_list bef ++ _)) in Hfill'.
      apply first_values in Hfill' as (Hvvs & Hee & ?) => //=.
      split => //. intro H0.
      repeat rewrite cat_app in Hvvs.
      apply Logic.eq_sym in Hvvs.
      apply app_inj_2 in Hvvs as [Hbef ->] => //.
      apply v_to_e_inj in Hbef as ->. by subst. 
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      repeat split => //=. apply v_to_e_is_const_list.
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff => //. split => //. apply v_to_e_is_const_list. } 
    { simpl in Hfill'.
      rewrite - Hfill in Hfill'.
      repeat rewrite app_assoc in Hfill'.
      rewrite - (app_assoc (v_to_e_list bef ++ vs)) in Hfill'. 
      apply first_values in Hfill' as ( _ & Habs & _ ) => //=.
      exfalso ; by eapply Hlabe.
      apply v_to_e_is_const_list.
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      split => //. apply v_to_e_is_const_list.
    }
    { simpl in Hfill'.
      rewrite - Hfill in Hfill'.
      repeat rewrite app_assoc in Hfill'.
      rewrite - (app_assoc (v_to_e_list bef ++ vs)) in Hfill'. 
      apply first_values in Hfill' as ( _ & Habs & _ ) => //=.
      exfalso ; by eapply Hloce.
      apply v_to_e_is_const_list.
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      split => //. apply v_to_e_is_const_list.
    }
  }
    
  { simpl in Hfill.
    destruct lh' as [ bef' aft' | bef' n'' l' lh' aft' | bef' n'' l' lh' aft' ].
    { simpl in Hfill'. rewrite - Hfill in Hfill'.
      rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
      apply first_values in Hfill' as ( _ & Habs & _ ) => //=.
      by exfalso ; eapply Hlabe'. 
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      split => //. all: apply v_to_e_is_const_list. }
    { simpl in Hfill'. rewrite - Hfill in Hfill'.
      apply first_values in Hfill' as ( Hl & Hlab' & -> ) => //=. 
      apply v_to_e_inj in Hl as ->. inversion Hlab' ; subst.
      assert (e = e' /\ (length vs = length vs' -> vs = vs' /\ lh = lh')) as (? & ?).
      eapply (IHn lh vs e lh' vs' e' _) => //=.
      rewrite app_length_rec in Hlab.
      rewrite list_extra.cons_app in Hlab.
      rewrite app_length_rec in Hlab. simpl in Hlab.
      rewrite Nat.add_0_r in Hlab. rewrite <- Nat.add_succ_l in Hlab.
      
      fold (length_rec (llfill lh (vs ++ [e]))) in Hlab.
      rewrite - H2 in Hlab. lia.
      repeat split => //=.
      by destruct (H0 H1).
      destruct (H0 H1) ; subst => //. 
      all: apply v_to_e_is_const_list. }
    { simpl in Hfill'.
      rewrite - Hfill in Hfill'.
      apply first_values in Hfill' as (_ & Habs & _) => //=.
      all: apply v_to_e_is_const_list. }  } 
 { simpl in Hfill.
    destruct lh' as [ bef' aft' | bef' n'' l' lh' aft' | bef' n'' l' lh' aft' ].
    { simpl in Hfill'. rewrite - Hfill in Hfill'.
      rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
      apply first_values in Hfill' as ( _ & Habs & _ ) => //=.
      by exfalso ; eapply Hloce'. 
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      split => //. all: apply v_to_e_is_const_list. }
      { simpl in Hfill'.
      rewrite - Hfill in Hfill'.
      apply first_values in Hfill' as (_ & Habs & _) => //=.
      all: apply v_to_e_is_const_list. }
    { simpl in Hfill'. rewrite - Hfill in Hfill'.
      apply first_values in Hfill' as ( Hl & Hlab' & -> ) => //=. 
      apply v_to_e_inj in Hl as ->. inversion Hlab' ; subst.
      assert (e = e' /\ (length vs = length vs' -> vs = vs' /\ lh = lh')) as (? & ?).
      eapply (IHn lh vs e lh' vs' e' _) => //=.
      rewrite app_length_rec in Hlab.
      rewrite list_extra.cons_app in Hlab.
      rewrite app_length_rec in Hlab. simpl in Hlab.
      rewrite Nat.add_0_r in Hlab. rewrite <- Nat.add_succ_l in Hlab.
      
      fold (length_rec (llfill lh (vs ++ [e]))) in Hlab.
      rewrite - H2 in Hlab. lia.
      repeat split => //= ; by destruct (H0 H1) ; subst. 
      all: apply v_to_e_is_const_list. }
    } 
Qed.

Lemma lfilled_llfill_first_values i lh vs e lh' vs' e' LI :
  lfilled i lh (vs ++ [::e]) LI ->
  llfill lh' (vs' ++ [::e']) = LI ->
  const_list vs -> const_list vs' ->
  (is_const e = false) -> (is_const e' = false) ->
  (forall n es LI, e <> AI_label n es LI) ->
  (forall n es LI, e' <> AI_label n es LI) ->
  (forall n f LI, e <> AI_local n f LI) ->
  e = e' /\ (length vs = length vs' -> (vs = vs')).
Proof.
  cut (forall n,
          length_rec LI < n ->
          lfilled i lh (vs ++ [::e]) LI ->
          llfill lh' (vs' ++ [::e']) = LI ->
          const_list vs -> const_list vs' ->
          (is_const e = false) -> (is_const e' = false) ->
          (forall n es LI, e <> AI_label n es LI) -> (forall n es LI, e' <> AI_label n es LI) ->
          (forall n f LI, e <> AI_local n f LI) ->
          e = e' /\ (length vs = length vs' -> (vs = vs'))).
  { intro Hn ; apply (Hn (S (length_rec LI))) ; lia. }
  intro n. generalize dependent LI. generalize dependent e'.
  generalize dependent vs'. generalize dependent lh'. 
  generalize dependent e. generalize dependent vs. generalize dependent lh.
  generalize dependent i.
  induction n ;
    intros i lh vs e lh' vs' e' LI Hlab Hfill Hfill' Hvs Hvs' He He' Hlabe Hlabe' Hloce ;
    first by inversion Hlab.
  unfold lfilled, lfill in Hfill. destruct i.
  { destruct lh as [bef aft|] => //. 
    remember (const_list bef) as b eqn:Hbef ; destruct b => //. 
    move/eqP in Hfill.
    destruct lh' as [bef' aft' | | ].
    { rewrite Hfill in Hfill'.
      simpl in Hfill'.
      repeat rewrite app_assoc in Hfill'.
      rewrite - (app_assoc (_ ++ vs')) in Hfill'.
      rewrite - (app_assoc (bef ++ _)) in Hfill'.
      apply first_values in Hfill' as (Hvvs & Hee & ?) => //=.
      split => //. intro H0.
      repeat rewrite cat_app in Hvvs.
      apply Logic.eq_sym in Hvvs.
      apply (app_inj_2 _ _ _ _ H0 Hvvs).
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      repeat split => //=. apply v_to_e_is_const_list.
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff => //. } 
    { simpl in Hfill'.
      rewrite Hfill in Hfill'.
      repeat rewrite app_assoc in Hfill'.
      rewrite - (app_assoc (bef ++ vs)) in Hfill'. 
      apply first_values in Hfill' as ( _ & Habs & _ ) => //=.
      exfalso ; by eapply Hlabe.
      apply v_to_e_is_const_list.
      unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
    { simpl in Hfill'.
      rewrite Hfill in Hfill'.
      repeat rewrite app_assoc in Hfill'.
      rewrite - (app_assoc (bef ++ vs)) in Hfill'. 
      apply first_values in Hfill' as ( _ & Habs & _ ) => //=.
      exfalso ; by eapply Hloce.
      apply v_to_e_is_const_list.
      unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
  }
    
  fold lfill in Hfill. 
  destruct lh as [| bef n' l lh aft] => //. 
  remember (const_list bef) as b ; destruct b => //. 
  remember (lfill i lh (vs ++ [e])) as les ; destruct les => //. 
  move/eqP in Hfill.
  destruct lh' as [ bef' aft' | bef' n'' l' lh' aft' | bef' n'' l' lh' aft' ].
  { simpl in Hfill'. rewrite Hfill in Hfill'.
    rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
    apply first_values in Hfill' as ( _ & Habs & _ ) => //=.
    by exfalso ; apply (Hlabe' n' l l0).
    unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
    split => //. apply v_to_e_is_const_list. }
  { simpl in Hfill'. rewrite Hfill in Hfill'.
    apply first_values in Hfill' as ( Hl & Hlab' & -> ) => //=. 
    inversion Hlab' ; subst.
    assert (e = e' /\ (length vs = length vs' -> vs = vs')) as (? & ?).
    eapply (IHn i lh vs e lh' vs' e' _) => //=.
    rewrite app_length_rec in Hlab.
    rewrite list_extra.cons_app in Hlab.
    rewrite app_length_rec in Hlab. simpl in Hlab.
    rewrite Nat.add_0_r in Hlab. rewrite <- Nat.add_succ_l in Hlab.
    
    fold (length_rec (llfill lh' (vs' ++ [e']))) in Hlab. lia.
    unfold lfilled ; rewrite <- Heqles ; done.
    repeat split => //=.
    apply v_to_e_is_const_list. }
  { simpl in Hfill'.
    rewrite Hfill in Hfill'.
    apply first_values in Hfill' as (_ & Habs & _) => //=.
    apply v_to_e_is_const_list. } 

Qed.

Lemma llfill_trans llh1 llh2 es0 es1 es2 :
  llfill llh1 es0 = es1 ->
  llfill llh2 es1 = es2 ->
  exists llh0, llfill llh0 es0 = es2.
Proof.
  intros ; subst.
  generalize dependent es0.
  induction llh2 => /=.
  exists (llh_push_const (llh_append llh1 l0) l) => /=.
  destruct llh1 ; simpl ; 
    rewrite - v_to_e_cat ; repeat rewrite app_assoc ;
    by rewrite - app_assoc.
  intro es0.
  destruct (IHllh2 es0) as [llh0 <-].
  exists (LL_label l n l0 llh0 l1) => //=.
  intro es0.
  destruct (IHllh2 es0) as [llh0 <-].
  exists (LL_local l n f llh0 l0) => //=. 
Qed.

Lemma lfilled_in_llfill k lh es LI llh LI' :
  lfilled k lh es LI ->
  llfill llh LI = LI' ->
  exists llh', llfill llh' es = LI'.
Proof.
  intros H1 H2.
  apply lfilled_implies_llfill in H1 as [? H1].
  by specialize (llfill_trans H1 H2). 
Qed. 

Lemma llfill_call_host_and_reduce s f es LI s' f' es' lh lh' tf h cvs vs :
  reduce s f es s' f' es' ->
  const_list vs ->
  llfill lh (vs ++ [AI_call_host tf h cvs]) = LI ->
  llfill lh' es = LI ->
  False.
Proof.
  intros Hred Hvs H1 Hes.
  cut (forall n, length_rec es < n -> False).
  { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
  intro n0. 
  generalize dependent es. generalize dependent es'. 
  generalize dependent lh'. generalize dependent f.
  generalize dependent f'.
  induction n0 ; intros f' f lh1 es' es1 Hred2 Hfill Hlab ; first by lia.
  induction Hred2 ; try by (rewrite_cats1_list; specialize (llfill_first_values Hfill H1) as [Hcontra _] => //; inversion Hcontra).
  (* r_simple *) 
  { destruct H;
      try by (rewrite_cats1_list;
              specialize (llfill_first_values Hfill H1) as [Hcontra _] ; (try done) ; inversion Hcontra).
    - apply (llfill_all_values' H1 Hfill) => //=. 
      by left.
    - apply (llfill_all_values' H1 Hfill) => //=. by right. 
    - assert (lfilled (S i) (LH_rec [] n es lh0 []) (vs0 ++ [AI_basic (BI_br i)])
                                                                                      [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i _ _) => //. 
      move/eqP in H2 ; by subst.
      destruct (lfilled_in_llfill Hfill' Hfill) as [lh' Hfillbr].
      specialize (llfill_first_values Hfillbr H1) as (? & ?) => //=.
    - apply (llfill_all_values'' H1 Hfill) => //=.
      by left.
    - apply (llfill_all_values'' H1 Hfill) => //=.
      by right. 
    - apply lfilled_implies_llfill in H2 as [llh H2].
      assert (llfill (LL_local [] n f0 llh []) (vs0 ++ [AI_basic BI_return]) = [AI_local n f0 es]) => //=.
      by rewrite H2.
      destruct (llfill_trans H3 Hfill) as [llh' Hfill'].
      edestruct llfill_first_values as [? _].
      exact H1.
      exact Hfill'.
      all : try done.
    - replace [v ; AI_basic (BI_tee_local i)] with
        ([v] ++ [AI_basic (BI_tee_local i)])%SEQ in Hfill => //=.

      destruct (llfill_first_values Hfill H1) as [??] => //=.
      by rewrite H.
    - destruct (lfilled_in_llfill H0 Hfill) as [lh' Hfill'].
      replace [AI_trap] with ([] ++ [AI_trap])%SEQ in Hfill' => //=.
      destruct (llfill_first_values Hfill' H1) as [??] => //=. }
  * specialize (llfill_first_values Hfill H1) as [Hcontra _ ]=> //=.
    subst; by apply v_to_e_is_const_list.
  * specialize (llfill_first_values Hfill H1) as [Habs _] => //=.
    subst ; by apply v_to_e_is_const_list.
  * destruct (lfilled_in_llfill H Hfill) as [lh' Hfill'].
    apply (IHn0 _ _ _ _ _ Hred2 Hfill').
    unfold lfilled, lfill in H ; destruct k.
    { destruct lh0 => //.  
      destruct (const_list l) => //. 
      move/eqP in H.
      destruct l. { destruct l0. { unfold lfilled, lfill in H0 ; simpl in H0.
                                   move/eqP in H0. simpl in H.
                                   rewrite app_nil_r in H0.
                                   rewrite app_nil_r in H. subst.
                                   exfalso ; apply IHHred2 => //=. }
        simpl in H. rewrite H in Hlab.
                    rewrite app_length_rec in Hlab.
                    destruct (cons_length_rec a l0) as [ | ? ]; lia. }
      rewrite H in Hlab. do 2 rewrite app_length_rec in Hlab.
      destruct (cons_length_rec a l) as [ | ?] ; lia. }
    fold lfill in H. destruct lh0 => //. 
    destruct (const_list l) => //. 
    remember (lfill _ _ _) as fill ; destruct fill => //. 
    move/eqP in H. rewrite H in Hlab.
    replace (AI_label n l0 l2 :: l1) with ([AI_label n l0 l2] ++ l1) in Hlab => //=.
    do 2 rewrite app_length_rec in Hlab.
    unfold length_rec in Hlab. simpl in Hlab.
    rewrite <- (Nat.add_0_r (S n0)) in Hlab. rewrite plus_comm in Hlab.
    apply Nat.le_lt_add_lt in Hlab ; try lia. 
    apply lt_S_n in Hlab. rewrite Nat.add_0_r in Hlab.
    assert (lfilled k lh0 es l2) as Hfill''.
    { unfold lfilled ; by rewrite <- Heqfill. }
    apply lfilled_length_rec in Hfill''. unfold length_rec.
    unfold length_rec in Hfill''. lia.
  * assert (llfill (LL_local [] n f (LL_base [] []) []) es = [AI_local n f es]).
    simpl. by rewrite app_nil_r.
    destruct (llfill_trans H Hfill) as [llh Hfill'].
    apply (IHn0 _ _ _ _ _ Hred2 Hfill').
    unfold length_rec in Hlab ; simpl in Hlab.
    rewrite Nat.add_0_r in Hlab.
    unfold length_rec. lia.
Qed. 

Lemma lfilled_call_host_and_reduce s f es LI s' f' es' i lh vs k lh' tf h cvs:
  reduce s f es s' f' es' ->
  const_list vs ->
  lfilled i lh (vs ++ [AI_call_host tf h cvs]) LI ->
  lfilled k lh' es LI ->
  False.
Proof.
  intros Hred Hvs H1 Hes.
  cut (forall n, length_rec es < n -> False).
  { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
  intro n0. 
  generalize dependent es. generalize dependent es'. generalize dependent k.
  generalize dependent lh'.
  induction n0 ; intros lh1 k es' es1 Hred2 Hfill Hlab ; first by lia.
  induction Hred2; try by (rewrite_cats1_list; specialize (lfilled_first_values H1 Hfill) as [Hcontra _] => //; inversion Hcontra).
  (* r_simple *)
  { destruct H; try by (rewrite_cats1_list; specialize (lfilled_first_values H1 Hfill) as [Hcontra _] => //; inversion Hcontra).

    - apply (lfilled_all_values' H1 Hfill) => //=;try by intros [? ?].
      by left.
    - apply (lfilled_all_values' H1 Hfill) => //=. by right. (* by intros [? ?]. *)
    - assert (lfilled (S i0) (LH_rec [] n es lh0 []) (vs0 ++ [AI_basic (BI_br i0)])
                      [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i0 _ _) => //. 
      move/eqP in H2 ; by subst.
      destruct (lfilled_trans Hfill' Hfill) as [lh' Hfillbr].
      specialize (lfilled_first_values H1 Hfillbr) as (? & ? & ?) => //=.
    - replace [v ; AI_basic (BI_tee_local i0)] with
        ([v] ++ [AI_basic (BI_tee_local i0)])%SEQ in Hfill => //=.
      assert (AI_call_host tf h cvs = AI_basic (BI_tee_local i0)) => //=.
      apply (lfilled_first_values H1 Hfill) => //=.
      by rewrite H.
    - destruct (lfilled_trans H0 Hfill) as [lh' Hfill'].
      replace [AI_trap] with ([] ++ [AI_trap])%SEQ in Hfill' => //=.
      assert (AI_call_host tf h cvs = AI_trap) => //=.
      apply (lfilled_first_values H1 Hfill') => //=. }
  * specialize (lfilled_first_values H1 Hfill) as [Hcontra _ ]=> //=.
    subst; by apply v_to_e_is_const_list.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //=.
    subst ; by apply v_to_e_is_const_list.
  * destruct (lfilled_trans H Hfill) as [lh' Hfill'].
    apply (IHn0 _ _ _ _ Hred2 Hfill').
    unfold lfilled, lfill in H ; destruct k0.
    { destruct lh0 => //.  
      destruct (const_list l) => //. 
      move/eqP in H.
      destruct l. { destruct l0. { unfold lfilled, lfill in H0 ; simpl in H0.
                                   move/eqP in H0. simpl in H.
                                   rewrite app_nil_r in H0.
                                   rewrite app_nil_r in H. subst.
                                   exfalso ; apply IHHred2 => //=. }
        simpl in H. rewrite H in Hlab.
                    rewrite app_length_rec in Hlab.
                    destruct (cons_length_rec a l0) as [ | ? ]; lia. }
      rewrite H in Hlab. do 2 rewrite app_length_rec in Hlab.
      destruct (cons_length_rec a l) as [ | ?] ; lia. }
    fold lfill in H. destruct lh0 => //. 
    destruct (const_list l) => //. 
    remember (lfill _ _ _) as fill ; destruct fill => //. 
    move/eqP in H. rewrite H in Hlab.
    replace (AI_label n l0 l2 :: l1) with ([AI_label n l0 l2] ++ l1) in Hlab => //=.
    do 2 rewrite app_length_rec in Hlab.
    unfold length_rec in Hlab. simpl in Hlab.
    rewrite <- (Nat.add_0_r (S n0)) in Hlab. rewrite plus_comm in Hlab.
    apply Nat.le_lt_add_lt in Hlab ; try lia. 
    apply lt_S_n in Hlab. rewrite Nat.add_0_r in Hlab.
    assert (lfilled k0 lh0 es l2) as Hfill''.
    { unfold lfilled ; by rewrite <- Heqfill. }
    apply lfilled_length_rec in Hfill''. unfold length_rec.
    unfold length_rec in Hfill''. lia.
Qed.

Lemma sfill_nested vh wh e :
  ∃ vh', sfill vh (sfill wh e) = sfill vh' e.
Proof.
  induction vh.
  { destruct wh.
    { exists (SH_base (l ++ l1) (l2 ++ l0)).
      cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc. auto. }
    { exists (SH_rec (l ++ l1) n l2 wh (l3 ++ l0)).
      cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc.
      rewrite app_comm_cons. rewrite (separate1 _ l3).
      repeat erewrite app_assoc. auto. } }
  { destruct IHvh as [vh' Heq].
    cbn. rewrite Heq.
    exists (SH_rec l n l0 vh' l1). cbn. auto. }
Qed.

Lemma llfill_nested vh wh e :
  ∃ vh', llfill vh (llfill wh e) = llfill vh' e.
Proof.
  induction vh.
  { destruct wh.
    { exists (LL_base (l ++ l1) (l2 ++ l0)).
      cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc. auto. }
    { exists (LL_label (l ++ l1) n l2 wh (l3 ++ l0)).
      cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc.
      rewrite app_comm_cons. rewrite (separate1 _ l3).
      repeat erewrite app_assoc. auto. }
    { exists (LL_local (l ++ l1) n f wh (l2 ++ l0)).
      cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc.
      rewrite app_comm_cons.
      repeat erewrite app_assoc. auto. }
  }
  { destruct IHvh as [vh' Heq].
    cbn. rewrite Heq.
    exists (LL_label l n l0 vh' l1). cbn. auto. }
  { destruct IHvh as [vh' Heq].
    cbn. rewrite Heq.
    exists (LL_local l n f vh' l0). cbn. auto. }
Qed.
