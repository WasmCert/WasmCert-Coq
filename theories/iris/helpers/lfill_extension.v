From mathcomp Require Import ssreflect ssrbool eqtype seq.
From Coq Require Import Eqdep_dec.
From stdpp Require Import base list.
Require Export common operations opsem properties list_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


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


Fixpoint size_of_instruction e :=
  match e with
  | AI_label _ _ LI => S (List.list_sum (map size_of_instruction LI))
  | AI_local _ _ LI => S (List.list_sum (map size_of_instruction LI))
  | _ => 1
  end.

Definition length_rec es := List.list_sum (map size_of_instruction es).


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

Inductive llholed : Type :=
| LL_base : list value -> list administrative_instruction -> llholed
| LL_label : list value -> nat -> list administrative_instruction -> llholed -> list administrative_instruction -> llholed
| LL_local : list value -> nat -> frame -> llholed -> list administrative_instruction -> llholed.

Definition llholed_eq_dec :
  forall lh1 lh2 : llholed, { lh1 = lh2 } + { lh1 <> lh2 }.
Proof.
  intros.
  decidable_equality.
Qed.

(* Since we enforced constance of the left-hand-sides, the fill operations are total
   functions *)
Fixpoint vfill n (vh : valid_holed n) es  :=
  match vh with
  | VH_base m bef aft => v_to_e_list bef ++ es ++ aft
  | VH_rec m bef n es0 vh aft =>
      v_to_e_list bef ++ AI_label n es0 (vfill vh es) :: aft
  end.
                                             
Fixpoint sfill sh es :=
  match sh with
  | SH_base bef aft => v_to_e_list bef ++ es ++ aft
  | SH_rec bef n es0 sh aft =>
      v_to_e_list bef ++ AI_label n es0 (sfill sh es) :: aft
  end.

Fixpoint llfill lh es :=
  match lh with
  | LL_base bef aft => v_to_e_list bef ++ es ++ aft
  | LL_label bef n es0 lh aft =>
      v_to_e_list bef ++ AI_label n es0 (llfill lh es) :: aft  
  | LL_local bef n f lh aft =>
      v_to_e_list bef ++ AI_local n f (llfill lh es) :: aft
  end.

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


Definition llh_push_const lh vs :=
  match lh with
  | LL_base bef aft => LL_base (vs ++ bef) aft
  | LL_label bef m es lh aft => LL_label (vs ++ bef) m es lh aft 
  | LL_local bef n f lh aft => LL_local (vs ++ bef) n f lh aft
  end.

Definition llh_append lh expr :=
  match lh with
  | LL_base bef aft => LL_base bef (aft ++ expr)
  | LL_label bef m es lh aft => LL_label bef m es lh (aft ++ expr)
  | LL_local bef n f lh aft => LL_local bef n f lh (aft ++ expr)
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

Fixpoint vh_increase m (vh : valid_holed m) :=
  match vh with
  | VH_base m bef aft => VH_base (S m) bef aft
  | VH_rec m bef n es vh aft => VH_rec bef n es (vh_increase vh) aft end.

Fixpoint vh_increase_repeat m (vh : valid_holed m) n : valid_holed (n + m) :=
  match n with 0 => vh
          | S n => vh_increase (vh_increase_repeat vh n) end.

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

Fixpoint llh_of_lh lh :=
  match lh with
  | LH_base bef aft =>
      match those (map (λ x, match x with
                             | AI_basic (BI_const v) => Some v
                             | _ => None end) bef) with
      | Some bef => Some (LL_base bef aft)
      | None => None end 
  | LH_rec bef n es lh aft =>
      match those (map (λ x, match x with
                             | AI_basic (BI_const v) => Some v
                             | _ => None end) bef) with
      | Some bef =>
          match llh_of_lh lh with
          | Some lh' => Some (LL_label bef n es lh' aft)
          | None => None
          end
      | None => None end
  end.



(* Tactics *)

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
  | H: context [llfill _ [?e1; ?e2; ?e3; ?e4] = _] |- _  =>
      replace [e1; e2; e3; e4] with ([e1; e2; e3] ++ [e4])%SEQ in H => //
  | H: context [llfill _ [?e1; ?e2; ?e3] = _] |- _  =>
      replace [e1; e2; e3] with ([e1; e2] ++ [e3])%SEQ in H => //
  | H: context [llfill _ [?e1; ?e2] = _] |- _  =>
      rewrite - cat1s in H
  | H: context [llfill _ [?e] = _] |- _ =>
      replace [e] with ([] ++ [e])%SEQ in H => //
  | _ => idtac
  end.
