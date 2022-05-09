From mathcomp Require Import ssreflect ssrbool eqtype seq.
From iris.program_logic Require Import language.
From Coq Require Import Eqdep_dec.
Require Import common operations opsem interpreter properties list_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Section Host.
  
Import DummyHosts.
  
Let host_state := host_state host_instance.
Let reduce : host_state -> store_record -> frame -> list administrative_instruction ->
             host_state -> store_record -> frame -> list administrative_instruction -> Prop :=
  @reduce _ _.

Definition expr := list administrative_instruction.

Fixpoint lh_depth lh :=
  match lh with
  | LH_base _ _ => 0
  | LH_rec _ _ _ lh _ => S (lh_depth lh)
  end.

Global Instance ai_list_eq_dec: EqDecision (seq.seq administrative_instruction).
Proof.
  eapply list_eq_dec.
  Unshelve.
  pose proof administrative_instruction_eq_dec. eauto.
Defined.
Global Instance ai_eq_dec: EqDecision (administrative_instruction).
Proof.
  pose proof administrative_instruction_eq_dec. eauto.
Defined.
Global Instance value_list_eq_dec: EqDecision (seq.seq value).
Proof.
  decidable_equality.
Defined.
Global Instance lholed_eq_dec : EqDecision (lholed).
Proof.
  decidable_equality.
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

(* An object of [valid_holed n] is an lholed in shallow enough for a [br n] to 
   be placed inside and be stuck *)
(* We also enforce the constance of all the left-hand-sides *)
Inductive valid_holed : nat -> Type :=
| VH_base (n : nat) : list value -> list administrative_instruction -> valid_holed n
| VH_rec (n : nat) : list value -> nat -> list administrative_instruction ->
                   valid_holed n -> list administrative_instruction -> valid_holed (S n).

Definition valid_holed_eq_dec :
  forall i (lh1 lh2 : valid_holed i), { lh1 = lh2 } + { lh1 <> lh2 }.
Proof.
  clear.
  induction lh1 ; intros.
  - destruct lh2 ; last by right.
    destruct (decide (l = l1)), (decide (l0 = l2)) ; solve [ by right ; intro H ; inversion H | by subst ; left].
  - set (k := S n) in lh2.
(*    change (valid_holed k) in lh2. *)
    pose (Logic.eq_refl : k = S n) as Hk.
    change lh2 with (match Hk in _ = w return valid_holed w with
                      | Logic.eq_refl => lh2 end).
    clearbody Hk k.
    destruct lh2.
    { right. intro Habs.
      assert ( match Hk in (_ = w) return (valid_holed w) with
               | Logic.eq_refl => VH_base n1 l2 l3
               end = VH_base (S n) l2 l3) as Hdone ; last by rewrite Hdone in Habs.
      rewrite -> Hk. done. }

    pose proof (eq_add_S _ _ Hk) as Hn.

    assert (Hk = f_equal S Hn) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    
    replace (match Hk in _ = w return (valid_holed w) with
            | Logic.eq_refl => VH_rec l2 n2 l3 lh2 l4
             end) with
      ( VH_rec l2 n2 l3 (match Hn in _ = w return valid_holed w with
                         | Logic.eq_refl => lh2 end ) l4) ; last first.

    rewrite Hproof.
    destruct Hn. done.

    
    destruct (decide ( l = l2)), (decide (n0 = n2)), (decide (l0 = l3)),
      (decide ( l1 = l4)), (IHlh1 (match Hn in (_ = w) return (valid_holed w) with
     | Logic.eq_refl => lh2
                                   end)) ; try by right ; intro H ; inversion H.
    left ; by subst.
    right. intro H. inversion H.
    apply Eqdep.EqdepTheory.inj_pair2 in H4.
    done. 
Defined.    

(* Here, we only enforce the constance of the left-hand-sides, no constraint on depth *)
Inductive simple_valid_holed : Type :=
| SH_base : list value -> list administrative_instruction -> simple_valid_holed
| SH_rec : list value -> nat -> list administrative_instruction -> simple_valid_holed
           -> list administrative_instruction -> simple_valid_holed.

Definition simple_valid_holed_eq_dec :
  forall lh1 lh2 : simple_valid_holed, { lh1 = lh2 } + { lh1 <> lh2 }.
Proof.
  intros.
  generalize dependent lh2.
  induction lh1, lh2 ; auto.
  destruct (decide (l = l1)), (decide (l0 = l2)).
  subst ; by left.
  all : try by right ; intro H ; inversion H.
  destruct (decide (l = l2)), (decide (n = n0)), (decide (l0 = l3)),
    (decide (l1 = l4)) ; destruct (IHlh1 lh2) as [H0 | H0] ;
    try by right ; intro H ; inversion H.
  subst ; by left.
Defined.
    


(* A value can be an immediate, a trap, a [br i] if it is in a context shallow enough,
   i.e. a [valid_holed i] ; or a return, in any context. *)
(* We use VH and SH instead of LH so that the fill operations are always total functions *)
Inductive val : Type :=
| immV : (list value) -> val
| trapV : val
| brV (i : nat) (lh : valid_holed i) : val
| retV : simple_valid_holed -> val.



Definition val_eq_dec : forall v1 v2: val, {v1 = v2} + {v1 <> v2}.
Proof.
  intros v1 v2;destruct v1,v2;auto.
  - destruct (decide (l = l0));[subst;by left|right;intros Hcontr;congruence].
  - destruct (decide (i = i0)). subst.
    destruct (valid_holed_eq_dec lh lh0) as [-> | H].
    by left.
    right. intro. inversion H0.
    apply Eqdep.EqdepTheory.inj_pair2 in H2.
    done.
    right.
    intro.
    inversion H.
    apply eq_sigT_fst in H2.
    done.
  - destruct (simple_valid_holed_eq_dec s s0);subst;[by left|right;congruence..].
Defined.
Definition val_eqb (v1 v2: val) : bool := val_eq_dec v1 v2.
Definition eqvalP : Equality.axiom val_eqb :=
  eq_dec_Equality_axiom val_eq_dec.

Canonical Structure val_eqMixin := EqMixin eqvalP.
Canonical Structure val_eqType := Eval hnf in EqType val val_eqMixin.

Definition state : Type := host_state * store_record * (list value) * instance.

Definition observation := unit. (* TODO: maybe change? *)


(* Since we enforced constance of the left-hand-sides, the fill operations are total
   functions *)
Fixpoint vfill n (vh : valid_holed n) es  :=
  match vh with
  | VH_base m bef aft => ((λ x, AI_basic (BI_const x)) <$> bef) ++ es ++ aft
  | VH_rec m bef n es0 vh aft =>
      ((λ x, AI_basic (BI_const x)) <$> bef) ++ AI_label n es0 (vfill vh es) :: aft
  end.
                                             
Fixpoint sfill sh es :=
  match sh with
  | SH_base bef aft => ((λ x, AI_basic (BI_const x)) <$> bef) ++ es ++ aft
  | SH_rec bef n es0 sh aft =>
      ((λ x, AI_basic (BI_const x)) <$> bef) ++ AI_label n es0 (sfill sh es) :: aft
  end.

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
  


Definition of_val (v : val) : expr :=
  match v with
  | immV l => fmap (fun v => AI_basic (BI_const v)) l
  | trapV => [::AI_trap]
  | brV i vh => vfill vh [AI_basic (BI_br i)]
  | retV sh => sfill sh [AI_basic BI_return]
  end.

Lemma of_val_imm (vs : list value) :
  ((λ v : value, AI_basic (BI_const v)) <$> vs) = of_val (immV vs).
Proof. done. Qed.




Definition sh_push_const sh vs :=
  match sh with
  | SH_base bef aft  => SH_base (vs ++ bef) aft 
  | SH_rec bef n es sh aft => SH_rec (vs ++ bef) n es sh aft 
  end.

Definition sh_append sh expr :=
  match sh with
  | SH_base bef aft => SH_base bef (aft ++ expr)
  | SH_rec bef n es lh aft => SH_rec bef n es lh (aft ++ expr)
  end.



Definition vh_push_const n (vh : valid_holed n) vs :=
  match vh with
  | VH_base n bef aft => VH_base n (vs ++ bef) aft
  | VH_rec n bef m es vh aft => VH_rec (n := n) (vs ++ bef) m es vh aft end.

Definition vh_append n (vh : valid_holed n) expr :=
  match vh with
  | VH_base n bef aft => VH_base n bef (aft ++ expr)
  | VH_rec n bef m es vh aft => VH_rec bef m es vh (aft ++ expr) end.


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
  
  



(* The following operation mirrors the opsem of AI_trap *)
(* in which a trap value swallows all other stack values *)
(* and the opsem of br and return, which skips over all subsequent expressions *)
Definition val_combine (v1 v2 : val) :=
  match v1 with
  | immV l => match v2 with
             | immV l' => immV (l ++ l')
             | trapV => trapV
             | brV i vh => brV (vh_push_const vh l)
             | retV lh => retV (sh_push_const lh l)
             end
  | trapV => trapV
  | brV i vh => brV (vh_append vh (of_val v2))
  | retV lh => retV (sh_append lh (of_val v2))
  end.

(* Intuitively, when writing [NotVal e], we intend to mean e is not a value.
   This is however not enforced by the syntax *)
Inductive ValNotVal :=
  Val : val -> ValNotVal
| NotVal : expr -> ValNotVal.

Definition expr_of_val_not_val x :=
  match x with
  | Val v => of_val v
  | NotVal e => e end.

Lemma expr_of_val_of_val_not_val v :
  of_val v = expr_of_val_not_val (Val v).
Proof. done. Qed.

Definition val_of_val_not_val x :=
  match x with
  | Val v => Some v
  | NotVal _ => None end.

(* Combining a val and a ValNotVal. It is intended that combining will yield a ValNotVal 
   representinig the concatenation of the function arguments, and verifies our
   invariant that [NotVal e] is used only when e is not a value *)
Definition val_not_val_combine (v1 : val) (v2 : ValNotVal) : ValNotVal :=
  match v1 with
  | immV l => match v2 with
             | Val (immV l') => Val (immV (l ++ l'))
             | Val trapV => match l with
                           | [] => Val trapV
                           | _ => NotVal (((λ v, AI_basic (BI_const v)) <$> l) ++ [AI_trap])
                           end
             | Val (brV i vh) => Val (brV (vh_push_const vh l))
             | Val (retV lh) => Val (retV (sh_push_const lh l))
             | NotVal e => NotVal (((λ v, AI_basic (BI_const v)) <$> l) ++ e)
             end
  | trapV => match expr_of_val_not_val v2 with
              [] => Val trapV
            | _ => NotVal (AI_trap :: expr_of_val_not_val v2)
            end
  | brV i vh =>
      match v2 with
      | Val v2 => Val (brV (vh_append vh (of_val v2)))
      | NotVal e => Val (brV (vh_append vh e))
      end
  | retV lh =>
      match v2 with
      | Val v2 => Val (retV (sh_append lh (of_val v2)))
      | NotVal e => Val (retV (sh_append lh e))
      end
  end.


(* performs a fold_left on a list of ValNotVals. Aborts if a NotVal is reached *)
Fixpoint merge_values (v : val) (vs : list ValNotVal) : ValNotVal  :=
  match vs with
  | [] => Val v
  | a :: vs => match val_not_val_combine v a with
             | Val v => merge_values v vs
             | NotVal e => NotVal (e ++ flatten (map expr_of_val_not_val vs))  end
  end.

Definition merge_values_list vs :=
  match vs with
  | Val v :: vs => merge_values v vs
  | [] => Val (immV [])
  | _ => NotVal (flatten (map expr_of_val_not_val vs))
  end.




(* given a [valid_holed (S m)], attemps to give back an « equal » [valid_holed m] *)
Fixpoint vh_decrease m (vh : valid_holed (S m)) : option (valid_holed m) :=
  match vh with
  | VH_base (S n) bef aft => Some (VH_base n bef aft)
  | VH_rec (S _) bef m es vh aft =>
      match vh_decrease vh with
      | Some vh' => Some (VH_rec bef m es vh' aft)
      | None => None
      end
  | VH_base m _ _ | VH_rec m _ _ _ _ _ =>
                      (None : option (valid_holed m))
  end.


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
    
    
      


    



Fixpoint to_val_instr (instr : administrative_instruction) : ValNotVal :=
  match instr with
  | AI_trap => Val trapV
  | AI_basic (BI_br i) => Val (brV (VH_base i [] []))
  | AI_basic BI_return => Val (retV (SH_base [] []))
  | AI_basic (BI_const v) => Val (immV [v])
  | AI_label n labe es =>
      match merge_values_list (map to_val_instr es) with
      | Val (brV i vh) => 
          match vh_decrease (VH_rec [] n labe vh []) with
          | Some vh' => Val (brV vh')
          | None => NotVal [instr]
          end 
      | Val (retV lh) => Val (retV (SH_rec [] n labe lh []))
      | _ => NotVal [instr]
      end
  | _ => NotVal [instr]
  end.

Definition to_val (e : expr) : option val :=
  match merge_values_list (map to_val_instr e) with
  | Val v => Some v
  | _ => None
  end.



Definition prim_step (e : expr) (s : state) (os : list observation) (e' : expr) (s' : state) (fork_es' : list expr) : Prop :=
  let '(hs, σ, locs, inst) := s in
  let '(hs', σ', locs', inst') := s' in
    reduce hs σ (Build_frame locs inst) e hs' σ' (Build_frame locs' inst') e' /\ os = [] /\ fork_es' = [].
                          

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


Lemma sh_push_const_nil sh :
  sh_push_const sh [] = sh.
Proof. destruct sh => //=. Qed.

Lemma vh_push_const_nil n (vh : valid_holed n) :
  vh_push_const vh [] = vh.
Proof. destruct vh => //=. Qed.


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

Lemma sh_append_nil sh :
  sh_append sh [] = sh.
Proof. destruct sh => /= ; rewrite cats0 => //. Qed.

Lemma vh_append_nil n (vh : valid_holed n) :
  vh_append vh [] = vh.
Proof. destruct vh => /= ; rewrite cats0 => //. Qed.

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
  
Lemma val_not_val_combine_app v1 v2 :
  expr_of_val_not_val (val_not_val_combine v1 v2) = of_val v1 ++ expr_of_val_not_val v2.
Proof.
  intros.
  destruct v1, v2 => //=.
  destruct v => //=.
  by rewrite fmap_app.
  destruct l => //=.
  destruct lh => //= ; rewrite fmap_app ; by rewrite app_assoc.
  destruct s => //= ; rewrite fmap_app ; by rewrite app_assoc.
  all : try by destruct lh => //= ; rewrite app_comm_cons ; rewrite app_assoc.
  all : try by destruct s => //= ; rewrite app_comm_cons ; rewrite app_assoc.
  destruct v => //=.
  destruct l => //=.
  destruct (vfill _ _) eqn:Habs => //=.
  destruct (sfill _ _) => //=.
  destruct e => //=.  
Qed.

Lemma list_fmap_app a b c d e :
  list_fmap a b c (d ++ e) = list_fmap a b c d ++ list_fmap a b c e.
Proof.
  fold (fmap c (d ++ e)).
  rewrite fmap_app.
  done.
Qed.


(* if we write val_not_val_combine_assoc v1 v2 as v1 + v2, this lemma is just plain
   associativity : v1 + (v2 + x) = (v1 + v2) + x. Because of typing, the phrasing is
   a little more complicated *)
Lemma val_not_val_combine_assoc v1 v2 x :
  val_not_val_combine v1 (val_not_val_combine v2 x) = 
    match val_not_val_combine v1 (Val v2) with
    | Val v3 => val_not_val_combine v3 x
    | NotVal es => NotVal (es ++ expr_of_val_not_val x)  end.
Proof.
  destruct v1, v2, x as [v0 | v0], v0 ;
    (try destruct l0) ;  
    (try destruct l) ; 
    simpl ; 
    (try rewrite - vh_push_const_app) ; 
    (try rewrite - sh_push_const_app) ;
    (try rewrite - vh_append_app) ;
    (try rewrite - sh_append_app) ;
    (try rewrite list_fmap_app) ; 
    (try rewrite vh_append_nil) ;
    (try rewrite sh_append_nil) ;
    (try rewrite vh_push_const_nil) ;
    (try rewrite sh_push_const_nil) ;
    (try rewrite vh_append_nil) ;
    (try rewrite sh_append_nil) ;
    (try rewrite vh_push_const_nil) ;
    (try rewrite sh_push_const_nil) ;
    (try destruct (vfill _ _) eqn:Habs ; try by apply vfill_is_nil in Habs as [? _]) ;
    (try destruct (sfill _ _) eqn:Habs ; try by apply sfill_is_nil in Habs as [? _]) ;
    (try rewrite - Habs) ;
    (try done) ;
    simpl ;
    (try by rewrite - catA) ;
    (try by rewrite - app_assoc) ;
    (try by repeat rewrite cats0) ;
    (try by repeat rewrite app_nil_r) ;
    (try by rewrite vh_push_const_app) ;
    (try by rewrite sh_push_const_app) ;
    (try by rewrite vh_push_const_append) ;
    (try by rewrite sh_push_const_append) ;
    (try by rewrite app_comm_cons app_comm_cons app_assoc ) ;
    (try by destruct lh0 => //= ; rewrite list_fmap_app app_comm_cons catA) ;
    (try by destruct lh => //= ; rewrite list_fmap_app app_comm_cons catA) ;
    (try by destruct lh => //= ; rewrite list_fmap_app app_assoc) ; 
    (try by destruct s => //= ; rewrite list_fmap_app app_comm_cons catA) ;
    (try by destruct s0 => //= ; rewrite list_fmap_app app_comm_cons catA) ;
    (try by destruct s => //= ; rewrite list_fmap_app app_assoc) ; 
    (try by destruct lh0 => //= ; rewrite app_comm_cons app_assoc) ;
    (try by destruct lh => //= ; rewrite app_comm_cons app_assoc) ;
    (try by destruct s => //= ; rewrite app_comm_cons app_assoc) ;
    (try by destruct s0 => //= ; rewrite app_comm_cons app_assoc) ;
    (try by destruct (vfill lh _) eqn:Habs' ;
     (try by apply vfill_is_nil in Habs' as [? _]) ;
     rewrite - Habs' ;
     destruct lh => //= ; by rewrite - app_assoc) ;
    (try by destruct (sfill s _) eqn:Habs' ;
     (try by apply sfill_is_nil in Habs' as [? _]) ;
     rewrite - Habs' ;
     destruct s => //= ; by rewrite - app_assoc).
  destruct (sfill (sh_append _ _) _) eqn:Habs' ;
    try by apply sfill_is_nil in Habs' as [? _].
  destruct (sfill s _) eqn:Habs'' ; try by apply sfill_is_nil in Habs'' as [? _].
  rewrite - Habs' - Habs''.
  destruct s => //= ; by rewrite - app_assoc.
Qed.




Lemma merge_br i (vh : valid_holed i) es :
  merge_values (brV vh) es =
    Val (brV (vh_append vh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent vh.
  induction es => //=.
  intros. destruct vh ; simpl ; by rewrite cats0.
  intros.
  rewrite vh_append_app.
  rewrite - IHes.
  destruct a => //=.
Qed.


Lemma merge_return sh es :
  merge_values (retV sh) es =
    Val (retV (sh_append sh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent sh.
  induction es => //=.
  intros. destruct sh ; simpl ; by rewrite cats0.
  intros.
  rewrite sh_append_app.
  rewrite - IHes.
  destruct a => //=.
Qed.


Lemma merge_trap es :
  merge_values trapV es =
    val_not_val_combine trapV (NotVal (flatten (map expr_of_val_not_val es))).
Proof.
  induction es => //=.
  destruct (expr_of_val_not_val a) eqn:Ha => //=.
Qed.


(* This next lemma proves two identities that had to be proven mutually recursively *)
Lemma merge_prepend_flatten vs :
  (forall v0, merge_values v0 vs = val_not_val_combine v0 (merge_values_list vs)) /\
    flatten (map expr_of_val_not_val vs) = expr_of_val_not_val (merge_values_list vs).
Proof.
  induction vs => //=. 
  - split => //. destruct v0 => //=.
    + by rewrite cats0.
    + by rewrite vh_append_nil.
    + by rewrite sh_append_nil.
  - destruct a => //=.
    + destruct IHvs as [IHvs1 IHvs2].
      rewrite (IHvs1 v).
      split.
      * intro v0 ; rewrite val_not_val_combine_assoc.
        destruct (val_not_val_combine v0 (Val v)) eqn:Hv0a.
        -- done.
        -- by rewrite IHvs2.
      * rewrite IHvs2.
        by rewrite val_not_val_combine_app.
    + split ; last done.
      destruct v0 => //=.
      * by rewrite app_assoc.
      * destruct e => //=.
        by rewrite merge_trap.
      * rewrite merge_br.
        by rewrite vh_append_app.
      * rewrite merge_return.
        by rewrite sh_append_app.
Qed.

(* For convenience, we provide lemmas for usage of each identity separately *)
Lemma merge_prepend v0 vs :
  merge_values v0 vs = val_not_val_combine v0 (merge_values_list vs).
Proof. by edestruct merge_prepend_flatten as [? _]. Qed.

Lemma merge_flatten vs :
  flatten (map expr_of_val_not_val vs) = expr_of_val_not_val (merge_values_list vs).
Proof. by edestruct merge_prepend_flatten as [_ ?]. Qed.
                    

      
 


  

Fixpoint size_of_instruction e :=
  match e with
  | AI_label _ _ LI => S (list_sum (map size_of_instruction LI))
  | AI_local _ _ LI => S (list_sum (map size_of_instruction LI))
  | _ => 1
  end .
Definition length_rec es := list_sum (map size_of_instruction es).

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
  generalize dependent lh ; generalize dependent les.
  induction k ; intros les lh Hfill ; unfold lfilled, lfill in Hfill.
  { destruct lh => //. 
    destruct (const_list l) => //. 
    move/eqP in Hfill. rewrite Hfill. do 2 rewrite app_length_rec. lia. }
  fold lfill in Hfill. destruct lh => //. 
  destruct (const_list l) => //. 
  remember (lfill _ _ _ ) as fill ; destruct fill => //. 
  move/eqP in Hfill. assert (lfilled k lh es l2) as Hfill'.
  { unfold lfilled ; by rewrite <- Heqfill. }
  apply IHk in Hfill'.
  replace (AI_label n l0 l2 :: l1) with ([AI_label n l0 l2] ++ l1) in Hfill => //=.
  rewrite Hfill. do 2 rewrite app_length_rec.
  assert (length_rec l2 <= length_rec [AI_label n l0 l2]) ; last lia.
  unfold length_rec => //=. lia.
Qed.




Lemma of_to_val_instr e : expr_of_val_not_val (to_val_instr e) = [e].
Proof.
  cut (forall n, size_of_instruction e < n -> expr_of_val_not_val (to_val_instr e) = [e]).
  intro H ; apply (H (S (size_of_instruction e))) ; try lia.
  intro n.
  generalize dependent e. 
  induction n ; first lia.
  intros e Hsize.
  destruct e => //=.
  - destruct b => //=. 
  - destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge => //.
    destruct v => //.
    { destruct i => //.
      destruct (vh_decrease _) eqn:Hvh => //=.
      replace (vfill v [AI_basic (BI_br (S i))]) with l0 ; first done.
      remember (length_rec l0) as m'.
      assert (length_rec l0 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l0.
      generalize dependent lh ; generalize dependent v ; generalize dependent i.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l0 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      + simpl in Hmerge.
        rewrite merge_br in Hmerge.
        inversion Hmerge.
        apply Eqdep.EqdepTheory.inj_pair2 in H2 ; subst lh ; clear Hmerge.
        simpl in Hvh.
        inversion Hvh ; subst ; clear Hvh => //=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
          with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.
      + simpl in Hmerge.
        rewrite merge_return in Hmerge.
        inversion Hmerge.
      + simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          last by inversion Hmerge.
        destruct v1 ; inversion Hmerge.
        assert (existT i0 (vh_push_const lh0 [v0]) =
                  existT (S i) (vh_push_const (match H1 in (_ = w) return (valid_holed w)
                                               with Logic.eq_refl => lh0 end) [v0])).
        by destruct H1.
        rewrite H0 in H2.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        rewrite <- H2 in Hvh.
        apply vh_decrease_push_const_inv in Hvh as (vh'' & Hvh & Hpush).
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm i vh'' match H1 in _ = w return valid_holed w with
                          | Logic.eq_refl => lh0 end Hvh l0) => //.
(*        rewrite (IHl0 H2 vh'' match H0 in _ = w return valid_holed w with
                              | Logic.eq_refl => lh0 end) => // ; last first.        *)
        rewrite H1.
        destruct vh'' ; simpl in Hpush ; subst v => //=.
        destruct i0 => //.
        pose proof (eq_add_S _ _ H1) as Hi.
        assert (H1 = f_equal S Hi) as Hproof.
        apply Eqdep.EqdepTheory.UIP.
        by rewrite Hproof ; destruct Hi.
        specialize (cons_length_rec (AI_basic (BI_const v0)) l0).
        lia.
      + simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      + rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v0 => // ; last by rewrite merge_return in Hmerge.
        destruct (vh_decrease (VH_rec _ _ _ _ _)) eqn:Hdecr => //.
        rewrite merge_br in Hmerge.
        replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
        inversion Hmerge.
        assert (existT i0 (vh_append v0 l0) =
                  existT (S i) (vh_append match H1 in _ = w return valid_holed w with
                                            Logic.eq_refl => v0 end l0)) ;
          first by destruct H1.
        rewrite H0 in H2 ; clear H0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        unfold vh_decrease in Hdecr ; fold vh_decrease in Hdecr.
        destruct i0 => //.
        destruct (vh_decrease lh0) eqn:Hdecr0 => //.
        inversion Hdecr.
        rewrite - H3 in H2.
        pose proof (eq_add_S _ _ H1) as Hi.
        assert (H1 = f_equal S Hi) as Hproof.
        apply Eqdep.EqdepTheory.UIP.
        replace match H1 in (_ = w) return (valid_holed w) with
         | Logic.eq_refl => VH_rec [] n1 l1 v1 []
                end with (VH_rec [] n1 l1 match Hi in _ = w return valid_holed w with
                                          | Logic.eq_refl => v1 end []) in H2 ;
          last by rewrite Hproof ; destruct Hi.
        simpl in H2.
        rewrite - H2 in Hvh.
        unfold vh_decrease in Hvh ; fold vh_decrease in Hvh.
        destruct i => //.
        destruct (vh_decrease match Hi in _ = w return valid_holed w
                              with Logic.eq_refl => v1 end) eqn:Hdecr1 => //.
        inversion Hvh => //=.
        rewrite (IHm i0 v1 lh0 Hdecr0 l2).
        clear - Hdecr1.
        apply (vfill_decrease [AI_basic (BI_br (S i0))]) in Hdecr1.
        rewrite - Hdecr1.
        clear.
        destruct Hi.
        done.
        simpl in Hsize. simpl. lia.
        done.
        unfold length_rec in H.
        rewrite map_cons in H.
        simpl in H. unfold length_rec. lia.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia. }
    simpl. 
    replace (sfill s [AI_basic BI_return]) with l0 ; first done.
    remember (length_rec l0) as m'.
    assert (length_rec l0 < S m') ; first lia.
    remember (S m') as m.
    clear Heqm Heqm' m'.
    generalize dependent l0.
    generalize dependent s.
    induction m => //= ; first by intros ; lia.
    intros.
    destruct l0 => //=.
    destruct a ; try by inversion Hmerge.
    destruct b ; try by inversion Hmerge.
    + simpl in Hmerge.
      rewrite merge_br in Hmerge.
      inversion Hmerge.
    + simpl in Hmerge.
      rewrite merge_return in Hmerge.
      inversion Hmerge => /=.
      rewrite map_map.
      replace (flatten
                 (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
        with l0 ; first done.
      clear - IHn Hsize.
      induction l0 => //=.
      rewrite IHn ; last by simpl in Hsize ; lia.
      simpl.
      rewrite -> IHl0 at 1 => //=.
      simpl in Hsize.
      lia.
    + simpl in Hmerge.
      rewrite merge_prepend in Hmerge.
      destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
        last by inversion Hmerge.
      destruct v0 ; inversion Hmerge.
      assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
      rewrite (IHm s0 l0) => //=.
      destruct s0 => //=.
      specialize (cons_length_rec (AI_basic (BI_const v)) l0).
      lia.
    + simpl in Hmerge.
      rewrite merge_trap in Hmerge.
      destruct (flatten _) => //=.
    + rewrite map_cons in Hmerge.
      unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
      destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
      destruct v => //.
      destruct (vh_decrease _) => //.
      by rewrite merge_br in Hmerge.
      rewrite merge_return in Hmerge.
      replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
      inversion Hmerge.
      simpl.
      rewrite (IHm s0 l2) => //.
      simpl in Hsize. simpl. lia.
      unfold length_rec in H.
      rewrite map_cons in H.
      simpl in H. unfold length_rec. lia.
      clear - IHn Hsize.
      induction l0 => //=.
      rewrite IHn ; last by simpl in Hsize ; lia.
      simpl.
      rewrite -> IHl0 at 1 => //=.
      simpl in Hsize.
      lia.
Qed.

Lemma flatten_simplify es :
  flatten (map expr_of_val_not_val (map to_val_instr es)) = es.
Proof.
  induction es => //=.
  rewrite of_to_val_instr IHes => //=.
Qed.
  
        


Lemma merge_to_val es :
  expr_of_val_not_val (merge_values_list (map to_val_instr es)) = es.
Proof.
  induction es => //=.
  specialize (of_to_val_instr a) ; intro Ha'.
  destruct (to_val_instr a) eqn:Ha => /= ; simpl in Ha'.
  - rewrite merge_prepend.
    remember (merge_values_list _) as vnv.
    specialize (val_not_val_combine_app v vnv) ; intro H.
    destruct (val_not_val_combine v vnv) eqn:Hv ; simpl in H ; simpl ; 
      rewrite H Ha' IHes ; subst ; done.
  - rewrite Ha'.
    rewrite flatten_simplify => //=.
Qed.


Lemma of_to_val es v : to_val es = Some v -> of_val v = es.
Proof. unfold to_val. specialize (merge_to_val es) ; intro H.
       destruct (merge_values_list _) => //.
       simpl in H. intro H' ; inversion H' ; by subst. Qed.
       

Fixpoint vh_increase m (vh : valid_holed m) :=
  match vh with
  | VH_base m bef aft => VH_base (S m) bef aft
  | VH_rec m bef n es vh aft => VH_rec bef n es (vh_increase vh) aft end.


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

Lemma S_plus m n : S (m + n) = m + S n. Proof. induction m => //=. by rewrite IHm. Defined.

Fixpoint vh_increase_repeat m (vh : valid_holed m) n : valid_holed (n + m) :=
  match n with 0 => vh
          | S n => vh_increase (vh_increase_repeat vh n) end.


Lemma vh_increase_push_const m (vh : valid_holed m) vs :
  vh_increase (vh_push_const vh vs) = vh_push_const (vh_increase vh) vs.
Proof. destruct vh => //=. Qed.

Lemma vh_increase_repeat_push_const m (vh : valid_holed m) vs j :
  vh_increase_repeat (vh_push_const vh vs) j = vh_push_const (vh_increase_repeat vh j) vs.
Proof. induction j => //=. rewrite IHj. by rewrite vh_increase_push_const. Qed.



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





Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  destruct v.
  - induction l => //=.
    unfold to_val.
    unfold merge_values_list.
    rewrite map_cons.
    unfold to_val_instr.
    fold to_val_instr.
    unfold to_val in IHl.
    unfold of_val in IHl.    
    destruct (map to_val_instr _) eqn:Hmap ; try by inversion IHl.
    destruct (merge_values_list (v :: l0)) eqn:Hmerge ; try by inversion IHl.
    rewrite merge_prepend.
    rewrite Hmerge.
    inversion IHl ; subst => //=.
  - done.
  - unfold of_val, to_val. 
    cut (forall i (vh : valid_holed i) j, merge_values_list (map to_val_instr (vfill vh [AI_basic (BI_br (j + i))])) = Val (brV (vh_increase_repeat vh j))).
    intro H. specialize (H i lh 0).
    unfold vh_increase_repeat in H. simpl in H.
    by rewrite H.
    clear i lh.
    induction vh as [i bef aft | i bef n es vh Hvh aft ] => //= ; intro j.
    { induction bef => //=.
      { rewrite merge_br => //= ; rewrite flatten_simplify.
        assert (VH_base (j + i) [] aft = vh_increase_repeat (VH_base i [] aft) j) as H ;
          last by rewrite H.
        induction j ; unfold vh_increase_repeat => //=.
        fold vh_increase_repeat.
        rewrite - IHj => //=.
      } 
      rewrite merge_prepend.
      destruct (merge_values_list _) eqn:Hmerge => //.
      inversion IHbef ; subst v => //=.
      by rewrite - vh_increase_repeat_push_const. } 
    induction bef.
    { simpl. specialize (Hvh (S j)).
      replace (BI_br (S j + i)) with (BI_br (j + S i)) in Hvh ; last by rewrite - S_plus.
      rewrite Hvh => /=.
      
      rewrite vh_decrease_increase.
      rewrite merge_br.
      rewrite flatten_simplify => //=.
      rewrite vh_increase_repeat_rec.
      destruct (S_plus j i) => //.
    }
    simpl.
    rewrite merge_prepend.
    destruct (merge_values_list _) eqn:Hmerge => //.
    inversion IHbef ; subst v => //.
    simpl.
    by rewrite - vh_increase_repeat_push_const.
  - unfold of_val, to_val.
    induction s.
    + induction l => //=.
      * rewrite merge_return.
        rewrite flatten_simplify.
        done.
      * rewrite merge_prepend.
        destruct (merge_values_list _) => //=.
        inversion IHl ; subst => //=.
    + induction l => /=.
      * destruct (merge_values_list _) => //.
        inversion IHs ; subst => /=.
        rewrite merge_return.
        rewrite flatten_simplify.
        done.
      * rewrite merge_prepend.
        clear IHs.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //=.
Qed.



Definition is_none_or {A : Type} (p : A -> bool) (x : option A) : bool :=
  match x with
  | None => true
  | Some y => p y
  end.

Lemma to_val_cons_is_none_or_cons : forall e0 e r,
  to_val (e0 :: e)%SEQ = r -> is_none_or (fun l => match l with | immV v => v != [] | _ => true end) r.
Proof.
  intros e0 e r H ; subst r.
  cut (forall n e0 e, length_rec (e0 :: e) < n ->  is_none_or (λ l : val, match l with
                         | immV v => v != []
                         | _ => true
                                                              end) (to_val (e0 :: e)%SEQ)).
  intro H ; apply (H (S (length_rec (e0 :: e)))) ; try lia.
  clear e e0.
  induction n => //= ; first lia.
  intros e0 e Hlen.
  destruct e0 => //.
  destruct b => //= ; unfold to_val => /=.
  - rewrite merge_br => //.
  - rewrite merge_return => //.
  - rewrite merge_prepend => /=.
    destruct e => //.
    assert (length_rec (a :: e) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec => //=. lia.
    apply IHn in H.
    unfold to_val in H.
    destruct (merge_values_list _) => //.
    destruct v0 => //.
  - unfold to_val => //=.
    rewrite merge_trap => /=.
    rewrite flatten_simplify => /=.
    destruct e => //=.
  - unfold to_val.
    unfold merge_values_list, map, to_val_instr.
    fold to_val_instr.
    destruct l0 ; first done.
    assert (length_rec (a :: l0) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec.
    rewrite map_cons.
    simpl.
    lia.
    apply IHn in H.
    unfold is_none_or in H.
    unfold to_val in H.
    destruct (merge_values_list _) => //.
    destruct v => //.
    + destruct (vh_decrease _) eqn:Hdecr => //=.
      rewrite merge_br => //=.
    + rewrite merge_return => //=.
Qed.
    
Lemma to_val_trap_is_singleton : ∀ e,
    to_val e = Some trapV -> e = [::AI_trap].
Proof.
  intro e.
  destruct e => //=.
  destruct a => //=.
  destruct b => //= ; unfold to_val => /=.
  - by rewrite merge_br.
  - by rewrite merge_return.
  - rewrite merge_prepend.
    destruct (merge_values_list _) => //=.
    destruct v0 => //=.
  - unfold to_val => /=.
    destruct e => //=.
    rewrite of_to_val_instr.
    done.
  - unfold to_val => /=.
    destruct (merge_values_list _) => //=.
    destruct v => //=.
    destruct i => //=.
    destruct (vh_decrease _) => //=.
    rewrite merge_br => //=.
    rewrite merge_return => //=.
Qed.


Lemma split_vals_not_empty_res : forall es v vs es',
  split_vals_e es = (v :: vs, es') -> es <> [].
Proof. by case. Qed.


Fixpoint vh_of_lh lh i :=
  match lh with
  | LH_base bef aft => match those (map (λ x, match x with AI_basic (BI_const v) => Some v
                                                     |  _ => None end) bef) with
                      | Some bef => Some (VH_base i bef aft)
                      |  _ => None end
  | LH_rec bef n es lh aft =>
      match i with
      | 0 => None
      | S i => 
          match those (map (λ x, match x with AI_basic (BI_const v) => Some v
                                         |  _ => None end) bef) with
          |  Some bef => match vh_of_lh lh i with
                        | Some vh => Some (VH_rec bef n es vh aft)
                        | None => None end
          |  _ => None end
      end
  end. 

Fixpoint lh_of_vh i (vh : valid_holed i) :=
  match vh with
  | VH_base _ bef aft => LH_base (map (λ x, AI_basic (BI_const x)) bef) aft
  | VH_rec _ bef n es vh aft => LH_rec (map (λ x, AI_basic (BI_const x)) bef) n es
                                      (lh_of_vh vh) aft end.

Fixpoint lh_of_sh sh :=
  match sh with
  | SH_base bef aft => LH_base (map (λ x, AI_basic (BI_const x)) bef) aft
  | SH_rec bef n es sh aft => LH_rec (map (λ x, AI_basic (BI_const x)) bef) n es
                                    (lh_of_sh sh) aft end. 


Lemma b2p: forall {T:eqType} (a b:T), a==b -> a=b.
Proof. move => T a b Hb. by move/eqP in Hb. Qed.


Lemma cat_app {A} (l1 : list A) l2 :
  cat l1 l2 = app l1 l2.
Proof. done. Qed.




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
    apply b2p in Hfill ; subst.
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
  - (* destruct IHsh as [k Hfill]. *)
    unfold lfilled, lfill => /= ; fold lfill.
    unfold lfilled in IHsh.
    destruct (lfill _ _ _) => //.
    apply b2p in IHsh ; subst.
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
    intros HLI _ ; apply b2p in HLI ; subst.
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
      replace (list_fmap value administrative_instruction (λ x, AI_basic (BI_const x))
                         l1) with l ; first done.
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
    intros HLI Hi ; apply b2p in HLI ; subst.
    destruct i ; first lia.
    assert (i >= k) ; first lia.
    apply (IHk i l2 lh) in H as (vh & Hvh & Hvfill) ;
      last by unfold lfilled ; rewrite Hfill.
    simpl.
    rewrite Hvh.
    induction l => //=.
    + (*rewrite Hvh => //=.
      destruct i ; try lia. *)
      eexists ; split => //=.
      by rewrite Hvfill.
    + destruct a => //=.
      destruct b => //=.
      rewrite list_extra.cons_app.
      rewrite - cat_app.
      specialize (IHl Hl) as (vh0 & Hvh0 & Hvfill0).
      destruct (those (map _ l)) eqn:Hthose => //.
      erewrite those_app => //.
(*      destruct (vh_of_lh lh i) eqn:Hlh => //.
      destruct i ; try lia. *)
      eexists ; split => //=.
      inversion Hvh0 ; subst.
      simpl in Hvfill0.
      by rewrite Hvfill0.
Qed.      
    
Lemma flatten_map_expr_of_val_not_val vs :
  flatten (map expr_of_val_not_val vs) =
    expr_of_val_not_val (merge_values_list vs).
Proof.
  induction vs => //=.
  destruct a => //=.
  rewrite IHvs.
  rewrite merge_prepend.
  by rewrite val_not_val_combine_app.
Qed.

Lemma merge_app vs1 vs2:
  merge_values_list (vs1 ++ vs2) =
    match (merge_values_list vs1) with
    | Val v1 => val_not_val_combine v1 (merge_values_list vs2)
    | NotVal e1 => NotVal (e1 ++ expr_of_val_not_val (merge_values_list vs2)) end.
Proof.
  induction vs1 => //=.
  { destruct (merge_values_list vs2) => //.
    destruct v => //.
    by rewrite vh_push_const_nil.
    by rewrite sh_push_const_nil. }
  destruct a => //.
  { do 2 rewrite merge_prepend.
    rewrite IHvs1.  
    destruct (merge_values_list vs1) eqn:Hvs1 => //=.
    by rewrite val_not_val_combine_assoc.
    destruct v => //=.
    by rewrite app_assoc. 
    destruct e => //=.
    destruct (merge_values_list vs2) ;
      by rewrite vh_append_app.
    destruct (merge_values_list vs2) ;
      by rewrite sh_append_app. }
  rewrite map_app.
  rewrite flatten_cat.
  rewrite (flatten_map_expr_of_val_not_val vs2).
  by rewrite catA.
Qed.


Lemma to_val_is_immV es vs :
  to_val es = Some (immV vs) -> es = map (λ x, AI_basic (BI_const x)) vs.
Proof.
  generalize dependent vs.
  induction es => //=.
  intros.
  unfold to_val in H.
  simpl in H.
  inversion H => //=.

  intros.
  unfold to_val in H ; simpl in H.
  destruct (to_val_instr a) eqn:Ha => //.
  rewrite merge_prepend in H.
  unfold to_val in IHes.
  destruct (merge_values_list _) => //.
  destruct v, v0 => //.
  inversion H ; subst.
  erewrite IHes => //.
  destruct a => //.
  destruct b => //.
  inversion Ha => //.
  simpl in Ha.
  destruct (merge_values_list _) => //.
  destruct v => //.
  destruct i => //.
  destruct (vh_decrease _) => //.
  destruct l => //.
  destruct l => //.
  simpl in H.
  destruct (vfill lh _) => //.
  simpl in H.
  destruct (sfill _ _) => //.
  destruct v => //.
  destruct e => //.
Qed.
  
  

Lemma merge_is_not_val es es' :
  merge_values_list (map to_val_instr es) = NotVal es' -> es = es'.
Proof.
  generalize dependent es'.
  induction es => //= ; intro es'.
  destruct (to_val_instr a) eqn:Ha => //=.
  { destruct a => //= ; simpl in Ha.
    { destruct b => //= ; inversion Ha ; subst.
      by rewrite merge_br.
      by rewrite merge_return.
      rewrite merge_prepend.
      destruct (merge_values_list _) eqn:Hmerge => //=.
      destruct v => //=.
      intro H ; inversion H ; subst.
      rewrite (to_val_trap_is_singleton (e := es)) => //.
      unfold to_val ; by rewrite Hmerge.
      intro H ; inversion H.
      by erewrite IHes. }
    { inversion Ha.
      rewrite merge_prepend.
      destruct (merge_values_list _) eqn:Hmerge => //=.
      assert (to_val es = Some v0) ; first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H.
      rewrite H.
      destruct es => //.
      by intro H' ; inversion H'.
      erewrite IHes => //.
      destruct e => //.
      by intro H ; inversion H. }
    destruct (merge_values_list (map _ l0)) eqn:Hmerge => //.
    destruct v0 => //.
    destruct i => //.
    destruct (vh_decrease _) => //.
    inversion Ha.

    rewrite merge_br => //.
    inversion Ha.
    rewrite merge_return => //. }
  rewrite flatten_simplify.
  intro H ; inversion H.
  destruct a => // ; try by inversion Ha. 
  destruct b => // ; try by inversion Ha.
  simpl in Ha.
  destruct (merge_values_list (map _ l0)) => // ; try by inversion Ha. 
  destruct v => // ; try by inversion Ha.
  destruct i => // ; try by inversion Ha.
  destruct (vh_decrease lh) ; try by inversion Ha.
Qed. 


Lemma extend_retV sh es :
  to_val (of_val (retV sh) ++ es) = Some (retV (sh_append sh es)).
Proof.
  unfold to_val.
  rewrite map_app.
  rewrite merge_app.
  specialize (to_of_val (retV sh)) as H.
  unfold to_val in H.
  destruct (merge_values_list _) => //.
  inversion H => /=.
  destruct (merge_values_list _) eqn:Hmerge => //.
  erewrite of_to_val.
  done.
  unfold to_val.
  by rewrite Hmerge.
  by apply merge_is_not_val in Hmerge ; subst.
Qed.



Lemma splits_vals_e_to_val_hd : forall e1 e es vs,
    split_vals_e e1 = (vs, e :: es) ->
    to_val e1 = None
    ∨ (vs = [] ∧ to_val e1 = Some trapV)
    ∨ (∃ i, e = AI_basic (BI_br i) ∧ to_val e1 = Some (brV (VH_base i vs es)))
    ∨ (e = AI_basic BI_return ∧ to_val e1 = Some (retV (SH_base vs es)))
    \/ (∃ i n es' LI (vh : valid_holed i),
          e = AI_label n es' LI /\ to_val e1 = Some (brV (VH_rec vs n es' vh es))
          /\ vfill vh [AI_basic (BI_br (S i))] = LI)
    \/ (∃ n es' LI sh, e = AI_label n es' LI /\ to_val e1 = Some (retV (SH_rec vs n es' sh es))
                     /\ sfill sh [AI_basic BI_return] = LI).
Proof.
  intros e1.
  induction e1 ; intros e es vs Hsplit.
  { destruct vs => //. } 
  { destruct vs => //.
    { simpl in Hsplit.
      destruct a => // ; try by left.
      destruct b => // ; simplify_eq;try by left.
      - unfold to_val => /=.
        rewrite merge_br flatten_simplify.
        right. right. left. eexists. eauto.
      - unfold to_val => /=.
        rewrite merge_return flatten_simplify.
        right. right. right. left. auto.
      - destruct (split_vals_e e1). simplify_eq.
      - destruct e1. right;left;auto.
      - left.
        unfold to_val => /=. destruct a => //.
        destruct b => //. rewrite of_to_val_instr => //.
      - inversion Hsplit ; subst.
        destruct (to_val (_ :: _)) eqn:Htv ; try by left.
        right. right. right. right.
        unfold to_val in Htv => /=.
        simpl in Htv. destruct (merge_values_list _) eqn:Hmerge => //.
        destruct v0 => //.
        + destruct i => //.
          destruct (vh_decrease _) eqn:Hdecr => //.
          rewrite merge_br flatten_simplify in Htv.
          inversion Htv ; subst.
          left. repeat eexists _.
          repeat split => //.
          assert (to_val l0 = Some (brV lh)).
          unfold to_val ; by rewrite Hmerge.
          apply of_to_val in H.
          unfold of_val in H.
          unfold vfill ; fold vfill.
          rewrite - (vfill_decrease _ Hdecr) => //.
        + rewrite merge_return flatten_simplify in Htv.
          inversion Htv ; subst.
          right. repeat eexists _.
          repeat split => //.
          assert (to_val l0 = Some (retV s)).
          unfold to_val ; by rewrite Hmerge.
          apply of_to_val in H.
          unfold of_val in H => //.
    }
    { simpl in Hsplit.
      destruct a => //.
      destruct b => //.
      destruct (split_vals_e e1) eqn:Hsome.
      assert ((l, l0) = (vs, (e :: es)%SEQ)) as Heq%IHe1.
      { simplify_eq. auto. }
      destruct Heq as [?|[[??]|[[?[??]]|[[??]|[(?&?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]]]]] ;
        unfold to_val => /= ; rewrite merge_prepend.
      { left. unfold to_val in H. destruct (merge_values_list _) => //. } 
      { left. unfold to_val in H0. destruct (merge_values_list _) => //. by inversion H0. }
      { unfold to_val in H0. destruct (merge_values_list _) => //.
        inversion H0 => /=. right. right. left. eexists _.
        split => //=. inversion Hsplit ; subst => //. }
      { unfold to_val in H0. destruct (merge_values_list _) => //.
        inversion H0 => /=. right. right. right. left.
        split;auto. by inversion Hsplit. }
      { unfold to_val in H0. destruct (merge_values_list _) => //.
        inversion H0 => /=. right. right. right. right. left.
        repeat eexists _. repeat split => //. by inversion Hsplit. }
      { unfold to_val in H0. destruct (merge_values_list _) => //.
        inversion H0 => /=. repeat right. repeat eexists _. repeat split => //.
        by inversion Hsplit. }
        
    }  }
Qed.

Lemma to_val_None_prepend: forall es1 es2,
  to_val es2 = None ->
  to_val (es1 ++ es2) = None
  ∨ (∃ i (vh : valid_holed i), to_val es1 = Some (brV vh))
  ∨ (∃ sh, to_val es1 = Some (retV sh)).
Proof.
  move => es1 es2 H.
  induction es1;try by left.
  destruct a;try by left.
  destruct b; try by left.
  - right ; left.
    unfold to_val => /=.
    rewrite merge_br flatten_simplify.
    eauto.
  - right ; right.
    unfold to_val => /=.
    rewrite merge_return flatten_simplify.
    eauto.
  - destruct IHes1 as [?|[[?[??]]|[??]]].
    { simpl. unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //=.
      by left. }
    { right;left. eexists _, (vh_push_const _ _). unfold to_val => /=.
      rewrite merge_prepend. unfold to_val in H0.
      destruct (merge_values_list _) ; last done. inversion H0 => //=. } 
    { right;right. unfold to_val => /=. rewrite merge_prepend.  unfold to_val in H0.
      destruct (merge_values_list _) => //.  inversion H0 => //=. by repeat eexists. } 
  - unfold to_val => /=. rewrite merge_trap => /=. rewrite flatten_simplify.
    destruct (es1 ++ es2) eqn:Habs => //.
    apply app_eq_nil in Habs as [-> ->].
    destruct IHes1 as [Habs | [ (? & ? & Habs) | [ ? Habs ]]] ; by inversion Habs.
    by left.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => // ; try by left.
    destruct v => // ; try by left.
    + destruct i => // ; try by left.
      destruct (vh_decrease _) ; try by left.
      rewrite merge_br flatten_simplify.
      right ; left.
      rewrite merge_br flatten_simplify.
      by repeat eexists.
    + rewrite merge_return flatten_simplify.
      right ; right.
      rewrite merge_return flatten_simplify.
      by eexists.
Qed.

Lemma to_val_None_prepend_const : forall es1 es2,
    const_list es1 ->
  to_val es2 = None ->
  to_val (es1 ++ es2) = None.
Proof.
  move => es1 es2 H H'.
  eapply to_val_None_prepend in H' as [ ? | [(i & vh & Hes1) | [sh Hes1]]] ; first done.
  - exfalso.
    generalize dependent i. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    unfold to_val in Hes1 ; simpl in Hes1.
    rewrite merge_prepend in Hes1.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v0 => //.
    apply (IHes1 H i0 lh) => //.
    unfold to_val.
    by rewrite Hmerge.
  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    unfold to_val in Hes1 ; simpl in Hes1.
    rewrite merge_prepend in Hes1.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v0 => //.
    apply (IHes1 H s) => //.
    unfold to_val.
    by rewrite Hmerge.
Qed.
  
Lemma to_val_None_append: forall es1 es2,
  to_val es1 = None ->
  to_val (es1 ++ es2) = None.
Proof.
  move => es1 es2.
  induction es1 => //=.
  destruct a => //=.
  destruct b => //= ; unfold to_val => /=.
  - by rewrite merge_br flatten_simplify.
  - by rewrite merge_return flatten_simplify.
  - rewrite merge_prepend.
    unfold to_val in IHes1.
    destruct (merge_values_list _) eqn:Hmerge => //=.
    + destruct v0 => //=.
      assert (to_val es1 = Some trapV) ; first by unfold to_val ; rewrite Hmerge.
      apply to_val_trap_is_singleton in H as -> => //=.
    + rewrite merge_prepend.
      destruct (merge_values_list (map to_val_instr (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
  - unfold to_val => /=.
    rewrite merge_trap => /=.
    rewrite flatten_simplify.
    destruct es1 => //=.
    rewrite of_to_val_instr => //.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //.
    + destruct i => //.
      destruct (vh_decrease _) eqn:Hdecr => //.
      repeat rewrite merge_br => //.
    + repeat rewrite merge_return => //.
Qed.

  
Lemma cat_cons_not_nil : forall T (xs : list T) y ys,
  xs ++ (y :: ys) <> [].
Proof. move => T xs y ys E. by move: (app_eq_nil _ _ E) => [? ?]. Qed.

Lemma not_reduce_simple_nil : forall es', ~ reduce_simple [] es'.
Proof.
  assert (forall es es', reduce_simple es es' -> es = [] -> False) as H.
  { move => es es' H.
    elim: {es es'} H => //=.
    { move => vs es _ _ t1s t2s _ _ _ _ H.
      by apply: cat_cons_not_nil. }
    { move => vs es _ _ t1s t2s _ _ _ _ H.
      by apply: cat_cons_not_nil. }
    { move => es lh _ H Hes.
      rewrite Hes {es Hes} /lfilled /operations.lfilled /= in H.
      case: lh H => //=.
      { move => es es2.
        case_eq (const_list es) => //=.
        move=> _ /eqP H.
        symmetry in H.
        by move: (app_eq_nil _ _ H) => [? ?]. } } }
  { move => es' H2.
    by apply: H. }
Qed.

Lemma lfill_cons_not_Some_nil : forall i lh es es' e es0,
  lfill i lh es = es' -> es = e :: es0 -> es' <> Some [].
Proof.
  elim.
  { elim; last by intros; subst.
    move=> l l0 es es' /=.
    case: (const_list l).
    { move => Hfill H1 H2 H3 H4.
      rewrite H4 in H2.
      injection H2 => H5 {H2}.
      rewrite H3 in H5.
      by apply: cat_cons_not_nil. }
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
        done. }
      { intros; subst; discriminate. } }
    { intros; subst; discriminate. } }
Qed.

Lemma lfilled_not_nil : forall i lh es es', lfilled i lh es es' -> es <> [] -> es' <> [].
Proof.
  move => i lh es es' H Hes Hes'.
  move: (exists_last Hes) => [e [e0 H']].
  rewrite H' in H.
  move: H.
  rewrite /lfilled /operations.lfilled.
  case_eq (operations.lfill i lh es).
  { intros; subst.
    rewrite H in H0.
    assert ([] = l) as H0'.
    { apply/eqP.
      apply H0. }
    { rewrite H0' in H.
      rewrite /= in H.
      case E: (e ++ (e0 :: l)%SEQ)%list; first by move: (app_eq_nil _ _ E) => [? ?].
      apply: lfill_cons_not_Some_nil.
      apply: H.
      apply: E.
      by rewrite H0'. } }
  { intros; subst.
    rewrite H in H0.
    done. }
Qed.

Lemma reduce_not_nil : forall hs1 σ1 f es hs2 σ2 f' es',
  reduce hs1 σ1 f es hs2 σ2 f' es' -> es <> [].
Proof.
  move => hs1 σ1 f es hs2 σ2 f' es' Hred.
  elim: {hs1 σ1 f es hs2 f' σ2} Hred => //;
    try solve [ repeat intro;
                match goal with
                | H : (_ ++ _)%SEQ = [] |- _ =>
                  by move: (app_eq_nil _ _ H) => [? ?]
                end ].
  { move => e e' _ _ _ Hreds He.
    rewrite He in Hreds.
    apply: not_reduce_simple_nil.
    apply: Hreds. }
  { intros. by apply: lfilled_not_nil. }
Qed.

Lemma to_val_not_trap_interweave : ∀ es es',
    const_list es -> es != [] ∨ es' != [] -> to_val (es ++ [AI_trap] ++ es')%SEQ = None.
Proof.
  intros es.
  induction es;intros es1 Hconst [Hnil | Hnil];try done.
  { destruct es1 => //=. unfold to_val => /=. rewrite of_to_val_instr => //. }
  { simpl in Hconst. apply andb_true_iff in Hconst as [Ha Hconst].
    destruct a => //.
    destruct b => //.
    simpl.
    unfold to_val => /=.
    rewrite merge_prepend.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct es,es1 ; first simpl in Hmerge.
    inversion Hmerge => //.
    assert (to_val ([] ++ [AI_trap] ++ s :: es1) = None).
    apply IHes => //=. by right.
    unfold to_val in H.
    rewrite Hmerge in H => //.
    assert (to_val ((a :: es) ++ [AI_trap] ++ []) = None).
    apply IHes => //=. by left.
    rewrite app_nil_r in H.
    unfold to_val in H.
    rewrite Hmerge in H => //.
    assert (to_val (a :: es ++ [AI_trap] ++ s :: es1) = None).
    apply IHes => //=. by right.
    unfold to_val in H.
    rewrite Hmerge in H => //.
  }
  { simpl in Hconst. apply andb_true_iff in Hconst as [Ha Hconst].
    destruct a => //.
    destruct b => //.
    simpl.
    unfold to_val => /=.
    rewrite merge_prepend.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct es,es1 ; first simpl in Hmerge.
    inversion Hmerge => //.
    assert (to_val ([] ++ [AI_trap] ++ s :: es1) = None).
    apply IHes => //=. by right.
    unfold to_val in H.
    rewrite Hmerge in H => //.
    assert (to_val ((a :: es) ++ [AI_trap] ++ []) = None).
    apply IHes => //=. 
    rewrite app_nil_r in H.
    unfold to_val in H.
    rewrite Hmerge in H => //.
    assert (to_val (a :: es ++ [AI_trap] ++ s :: es1) = None).
    apply IHes => //=. by right.
    unfold to_val in H.
    rewrite Hmerge in H => //. }
  Qed.


Lemma const_list_to_val es :
  const_list es -> exists vs, to_val es = Some (immV vs).
Proof.
  induction es => //= ; intros.
  by exists [].
       destruct a => //=.
       destruct b => //=.
       unfold to_val => /=.
       rewrite merge_prepend.
       apply IHes in H as [vs Htv].
       unfold to_val in Htv.
       destruct (merge_values_list _) => //=.
       inversion Htv => //=.
       by eexists.
Qed.


Lemma to_val_const_list: forall es vs,
  to_val es = Some (immV vs) ->
  const_list es.
Proof.
  move => es. 
  elim: es => [|e es'] //=.
  move => IH vs.
  destruct e => //=.
  destruct b => //= ; unfold to_val => /=. 
  - rewrite merge_br flatten_simplify => //.
  - rewrite merge_return flatten_simplify => //.
  - rewrite merge_prepend.
    unfold to_val in IH.
    destruct (merge_values_list _) => //.
    destruct v0 => //=.
    intro H ; inversion H ; subst.
    by eapply IH.
  - unfold to_val => /=.
    rewrite merge_trap flatten_simplify => /=.
    destruct es' => //=.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //.
    + destruct i => //.
      destruct (vh_decrease lh) => //.
      rewrite merge_br flatten_simplify => //.
    + rewrite merge_return flatten_simplify => //.
Qed.


(* TODO: remove duplicated iris_properties lemmas *)
(* helper lemmas copy-pasted from iris_properties *)
Lemma first_values vs1 e1 es1 vs2 e2 es2 :
  (is_const e1 -> False) ->
  (is_const e2 -> False) ->
  const_list vs1 ->
  const_list vs2 ->
  vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 ->
  vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
Proof.
  intros He1 He2 Hvs1 Hvs2 Heq.
  generalize dependent vs2; induction vs1 ; intros.
  { destruct vs2 ; inversion Heq => //=. rewrite <- H0 in Hvs2.
    simpl in Hvs2. apply andb_true_iff in Hvs2 as [ Habs _ ].
    assert (const_list [e1]) ; first by apply andb_true_iff.
    done. }
  destruct vs2 ; inversion Heq.
  { rewrite H0 in Hvs1.
    simpl in Hvs1. apply andb_true_iff in Hvs1 as [ Habs _ ].
    assert (const_list [e2]) ; first by apply andb_true_iff.
    done. }
  assert (vs1 = vs2 /\ e1 = e2 /\ es1 = es2) as H ; last by destruct H ; subst.
  apply IHvs1 => //=.
  - by apply andb_true_iff in Hvs1 as [ _ Hvs1 ].
  - by apply andb_true_iff in Hvs2 as [ _ Hvs2 ].  
Qed.

Lemma lfilled_first_values i lh vs e i' lh' vs' e' LI :
  lfilled i lh (vs ++ [e]) LI ->
  lfilled i' lh' (vs' ++ [e']) LI ->
  const_list vs -> const_list vs' ->
  (is_const e -> False) -> (is_const e' -> False) ->
  (forall n es LI, e <> AI_label n es LI) -> (forall n es LI, e' <> AI_label n es LI) ->
  e = e' /\ i = i' /\ (length vs = length vs' -> vs = vs').
Proof.
  cut (forall n,
          length_rec LI < n ->
          lfilled i lh (vs ++ [e]) LI ->
          lfilled i' lh' (vs' ++ [e']) LI ->
          const_list vs -> const_list vs' ->
          (is_const e -> False) -> (is_const e' -> False) ->
          (forall n es LI, e <> AI_label n es LI) -> (forall n es LI, e' <> AI_label n es LI) ->
          e = e' /\ i = i' /\ (length vs = length vs' -> vs = vs')).
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
      repeat split => //=. intro Hlen. apply (app_inj_2 _ _ _ _ Hlen Hvvs). }
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
    unfold to_val => /=.
    unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
  fold lfill in Hfill'.
  destruct lh' as [| bef' n'' l' lh' aft'] => //. 
  remember (const_list bef') as b ; destruct b => //. 
  remember (lfill i' lh' (vs' ++ [e'])) as les0 ; destruct les0 => //. 
  move/eqP in Hfill'. rewrite Hfill in Hfill'.
  apply first_values in Hfill' as ( Hl & Hlab' & _ ) => //= ; try by intros [? ?].
  inversion Hlab' ; subst.
  assert (e = e' /\ i = i' /\ (length vs = length vs' -> vs = vs')) as (? & ? & ?).
  apply (IHn i lh vs e i' lh' vs' e' l1) => //=.
  rewrite app_length_rec in Hlab.
  replace (AI_label n'' l' l1 :: aft) with ([AI_label n'' l' l1] ++ aft) in Hlab => //=.
  rewrite app_length_rec in Hlab. simpl in Hlab.
  rewrite Nat.add_0_r in Hlab. rewrite <- Nat.add_succ_l in Hlab.
  fold (length_rec l1) in Hlab. lia.
  unfold lfilled ; rewrite <- Heqles ; done.
  unfold lfilled ; rewrite <- Heqles0 ; done.
  repeat split => //=. lia.
Qed.

Lemma lfilled_all_values' i lh vs e i' lh' n0 es vs' LI :
  lfilled i lh (vs ++ [e]) LI ->
  lfilled i' lh' [AI_label n0 es vs'] LI ->
  const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
  (is_const e -> False ) ->
  (to_val [e] = Some trapV -> False) ->
  (forall n es LI, e <> AI_label n es LI) ->
  False.
Proof.
  cut (forall n,
          length_rec LI < n ->
          lfilled i lh (vs ++ [e]) LI ->
          lfilled i' lh' [AI_label n0 es vs'] LI ->
          const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
          (is_const e -> False ) ->
          (to_val [e] = Some trapV -> False) ->
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
    unfold to_val => /=.
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
                  unfold lfilled, lfill, const_list.
                  rewrite forallb_app. unfold const_list in Hbef ; rewrite <- Hbef.
                  unfold const_list in Hbef' ; rewrite <- Hbef' => //=.
                  by repeat rewrite app_assoc. }
    fold lfill in Hfill2. destruct lh as [| bef n es lh aft ] => //.  
    remember (const_list bef) as b eqn:Hbef ; destruct b => //. 
    remember (lfill k lh es1) as fill ; destruct fill => //. 
    move/eqP in Hfill2 ; subst.
    exists (LH_rec (bef' ++ bef) n es lh (aft ++ aft')). rewrite <- plus_n_O.
    unfold lfilled, lfill ; fold lfill ; unfold const_list.
    rewrite forallb_app. unfold const_list in Hbef ; rewrite <- Hbef.
    unfold const_list in Hbef' ; rewrite <- Hbef' => //=.
    rewrite <- Heqfill. repeat rewrite app_assoc. by rewrite <- app_assoc. }
  unfold lfilled, lfill in Hfill3 ; fold lfill in Hfill3.
  destruct lh' as [| bef' n' es' lh' aft' ] => //. 
  remember (const_list bef') as b eqn:Hbef' ; destruct b => //. 
  remember (lfill k' lh' es2) as fill' ; destruct fill' => //. 
  move/eqP in Hfill3. assert (lfilled k' lh' es2 l) as Hfill.
  by unfold lfilled ; rewrite <- Heqfill'.
  destruct (IHk' _ _ _ _ _ _ Hfill2 Hfill) as (lh'' & Hfill').
  exists (LH_rec bef' n' es' lh'' aft'). rewrite plus_comm => //=. rewrite plus_comm.
  unfold lfilled, lfill ; fold lfill. rewrite <- Hbef'. unfold lfilled in Hfill'.
  destruct (lfill (k + k') lh'' es1) => //. 
  move/eqP in Hfill' ; by subst.
Qed.

Ltac rewrite_cats1_list :=
  match goal with
    | H: context [lfilled _ _ [?e1; ?e2; ?e3; ?e4] _] |- _  =>
      replace [e1; e2; e3; e4] with ([e1; e2; e3] ++ [e4])%SEQ in H => //
    | H: context [lfilled _ _ [?e1; ?e2; ?e3] _] |- _  =>
      replace [e1; e2; e3] with ([e1; e2] ++ [e3])%SEQ in H => //
    | H: context [lfilled _ _ [?e1; ?e2] _] |- _  =>
      rewrite - cat1s in H
    | H: context [lfilled _ _ [?e] _] |- _ =>
      replace [e] with ([] ++ [e])%SEQ in H => //
    | _ => idtac
  end.

Lemma lfilled_br_and_reduce hs s f es LI hs' s' f' es' i j lh vs k lh' :
  reduce hs s f es hs' s' f' es' ->
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
      by left. (* intros [? ?];done. *)
    (* unreachable? *)
    - apply (lfilled_all_values' H1 Hfill) => //=. by right.
(*      intros [? ?];done. *)
    (* br itself *)
    - assert (lfilled (S i0) (LH_rec [] n es lh0 []) (vs0 ++ [AI_basic (BI_br i0)])
                      [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i0 _ _) => //. 
      move/eqP in H2 ; by subst.
      destruct (lfilled_trans Hfill' Hfill) as [lh' Hfillbr].
      assert (AI_basic (BI_br j) = AI_basic (BI_br i0) /\ (i = S i0 + k)
              /\ (length vs = length vs0 -> vs = vs0)) as (? & ? & ?).
      apply (lfilled_first_values H1 Hfillbr) => //=.
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


Lemma lfilled_return_and_reduce hs s f es LI hs' s' f' es' i lh vs k lh' :
  reduce hs s f es hs' s' f' es' ->
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
      left.
      destruct (const_list_to_val (es:=vs0)) as [v Hv] => //= ; by exists (immV v).
    - apply (lfilled_all_values' H1 Hfill) => //=. by right. (* by intros [? ?]. *)
    - assert (lfilled (S i0) (LH_rec [] n es lh0 []) (vs0 ++ [AI_basic (BI_br i0)])
                      [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i0 _ _) => //. 
      move/eqP in H2 ; by subst.
      destruct (lfilled_trans Hfill' Hfill) as [lh' Hfillbr].
      assert (AI_basic BI_return = AI_basic (BI_br i0) /\ (i = S i0 + k)
              /\ (length vs = length vs0 -> vs = vs0)) as (? & ? & ?).
      apply (lfilled_first_values H1 Hfillbr) => //=.
      inversion H3.
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




Lemma val_head_stuck_reduce : ∀ hs1 locs1 s1 e1 hs2 locs2 s2 e2,
    reduce hs1 locs1 s1 e1 hs2 locs2 s2 e2 ->
    to_val e1 = None.
Proof.
  move => hs1 locs1 s1 e1 hs2 locs2 s2 e2 HRed;try by to_val_None_prepend_const.
  induction HRed => //= ; subst; try by to_val_None_prepend_const.
  - inversion H; subst => //=;try by apply to_val_None_prepend_const;auto.
    + unfold to_val => /=.
      apply const_list_to_val in H0 as [vs Htv].
      unfold to_val in Htv.
      destruct (merge_values_list _) => //.
      inversion Htv => //.
    + unfold to_val => /=.
      destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v => //.
      destruct i0 => //.
      destruct (vh_decrease lh0) eqn:Hdecr => //.
      assert (to_val LI = Some (brV lh0)) ; first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H1.
      unfold of_val in H1.
      rewrite (vfill_decrease _ Hdecr) in H1.
      destruct (vfill_to_lfilled v [AI_basic (BI_br (S i0))]) as (Hk & Hfill).
      rewrite H1 in Hfill.
      edestruct lfilled_first_values as (Habs1 & Habs2 & _).
      exact H2.
      rewrite - (app_nil_l [_]) in Hfill.
      rewrite - cat_app in Hfill.
      exact Hfill.
      all : try done.
      inversion Habs1.
      subst.
      lia.
      assert (to_val LI = Some (retV s0)) ; first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H1. unfold of_val in H1. 
      specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfill.
      rewrite H1 in Hfill.
      edestruct lfilled_first_values as (Habs & _ & _).
      exact H2.
      rewrite - (app_nil_l [_]) in Hfill.
      rewrite - cat_app in Hfill.
      exact Hfill.
      all : try done. 
    + destruct v => //.
      by destruct b => //=.
    + move/lfilledP in H1.
      inversion H1. subst es e.
      apply to_val_not_trap_interweave;auto.
      case: vs {H H1 H2 H4} H0 => //=.
      case: es' => //=.
      move => a l H. by right.
      move => a l H. by left.
  - apply to_val_None_prepend_const;auto.
    apply v_to_e_is_const_list.
  - destruct k, lh ; unfold lfilled, lfill in H ; fold lfill in H => //.
    + destruct (const_list l) eqn:Hl => //.
      apply b2p in H ; subst.
      apply to_val_None_prepend_const, to_val_None_append => //.
    + destruct (const_list l) eqn:Hl => //.
      destruct (lfill _ _ _) eqn:Hfill => //.
      apply b2p in H ; subst.
      generalize dependent les'.
      induction l ; intros ;  unfold to_val => /=.
      * destruct (merge_values_list _) eqn:Hmerge => //.
        destruct v => //.
        -- destruct i => //.
           destruct (vh_decrease lh0) eqn:Hdecr => //.
           exfalso.
           assert (to_val l2 = Some (brV lh0)) ; first by unfold to_val ; rewrite Hmerge.
           apply of_to_val in H.
           unfold of_val in H.
           destruct (vfill_to_lfilled lh0 [AI_basic (BI_br (S i))]) as (Hk & Hfilled).
           rewrite H in Hfilled.
           assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
           rewrite - (app_nil_l [_]) in Hfilled.
           rewrite - cat_app in Hfilled.
           eapply lfilled_br_and_reduce ; first (exact HRed) ; (try exact Hfilled) => //=.
        -- exfalso.
           assert (to_val l2 = Some (retV s0)) ; first by unfold to_val ; rewrite Hmerge.
           apply of_to_val in H. unfold of_val in H.
           specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfilled.
           rewrite H in Hfilled.
           assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
           rewrite - (app_nil_l [_]) in Hfilled.
           rewrite - cat_app in Hfilled.
           eapply lfilled_return_and_reduce ; first (exact HRed) ;
             (try exact Hfilled) => //=.
      * destruct a => //.
        destruct b => //=.
        rewrite merge_prepend.
        unfold lfilled, lfill in H0 ; fold lfill in H0.
        rewrite Hl in H0.
        destruct (lfill _ _ es') eqn:Hfill' => //.
        apply b2p in H0.
        destruct les' => //.
        assert (lfilled (S k) (LH_rec l n l0 lh l1) es' les').
        unfold lfilled, lfill ; fold lfill.
        apply andb_true_iff in Hl as [? Hl]. unfold const_list, forallb ; rewrite Hl.
        rewrite Hfill'. by inversion H0.
        apply IHl in H => //.
        unfold to_val in H.
        destruct (merge_values_list _) => //. 
Qed.

Lemma val_head_stuck : forall e1 s1 κ e2 s2 efs,
  prim_step e1 s1 κ e2 s2 efs →
  to_val e1 = None.
Proof.
  rewrite /prim_step => e1 [[[hs1 locs1] σ1] inst] κ e2 [[[hs2 locs2] σ2] inst'] efs.
  move => [HRed _].
  eapply val_head_stuck_reduce;eauto.
Qed.

Lemma wasm_mixin : LanguageMixin of_val to_val prim_step.
Proof. split; eauto using to_of_val, of_to_val, val_head_stuck. Qed.

Definition wasm_lang := Language wasm_mixin.

End Host.
