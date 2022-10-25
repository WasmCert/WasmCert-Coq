From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_rules.
Require Export datatypes operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.


Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50). 
   
Notation "{{{ P }}} es @ E {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗ (WP (es : iris.expr) @ NotStuck ; E {{ v, Φ v }}))%I (at level 50).

Definition i32const (n:Z) := BI_const (VAL_int32 (Wasm_int.int_of_Z i32m n)).
Definition value_of_int (n:Z) := VAL_int32 (Wasm_int.int_of_Z i32m n).


Definition two14 := 16384%Z.
Definition two16 := 65536%Z.
Definition two32 := 4294967296%Z.


Definition points_to_i32 `{!wasmG Σ} n i v :=
  (∃ a b c d, n ↦[wm][ i ] a ∗ n ↦[wm][N.add i 1] b ∗
                n ↦[wm][N.add i 2] c ∗ n ↦[wm][N.add i 3] d ∗
                ⌜ serialise_i32 v = [a ; b ; c ; d] ⌝)%I.
Notation "n ↦[i32][ k ] v" := (points_to_i32 n k v) (at level 50).


Lemma of_nat_to_nat_plus a b :
  N.of_nat (N.to_nat a + b) = (a + N.of_nat b)%N.
Proof. lia. Qed.

Section Stack.

  Context `{!wasmG Σ}.


Lemma i32_wms n i v :
  n ↦[i32][ i ] v ⊣⊢ n ↦[wms][ i ]serialise_i32 v.
Proof.
  iSplit ; iIntros "H" ; unfold mem_block_at_pos, points_to_i32.
  - iDestruct "H" as (a b c d) "(? & ? & ? & ? & ->)".
    iSimpl.
    repeat rewrite of_nat_to_nat_plus.
    rewrite N.add_0_r.
    by iFrame.
  - remember (serialise_i32 v) as bs.
    repeat destruct bs => //=.
    repeat rewrite of_nat_to_nat_plus.
    rewrite N.add_0_r.
    iDestruct "H" as "(? & ? & ? & ? & _)".
    iExists _,_,_,_.
    iFrame.
    done.
Qed.
    
  



Definition isStack v (l : seq.seq i32) n :=
  (let st_p := (v + 4 + length l * 4)%Z in
    ⌜ (two16 | v)%Z ⌝ ∗ ⌜ (length l < two14)%Z ⌝ ∗
   N.of_nat n ↦[i32][ Z.to_N v ]
            (Wasm_int.Int32.repr st_p) ∗
            ([∗ list] i ↦ w ∈ l,
              N.of_nat n ↦[i32][ Z.to_N (st_p - 4 - 4 * i)%Z ] w) ∗
            ∃ bs, ⌜ (Z.of_nat (length bs) = two16 - 4 - length l * 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N st_p] bs
  )%I.

Definition stk : string := "STACK".
Definition stkN : namespace := nroot .@ stk.

(* stack module invariant *)
        
Definition stackModuleInv (isStack : Z -> seq.seq i32 -> iPropI Σ) (nextStackAddrIs : nat -> iPropI Σ) : iProp Σ :=
  ∃ (nextStack : nat), ⌜(Wasm_int.Int32.modulus - 1)%Z <> Wasm_int.Int32.Z_mod_modulus (ssrnat.nat_of_bin (N.of_nat nextStack `div` page_size))⌝ ∗
                     ⌜(N.of_nat nextStack + 4 < Z.to_N (two_power_nat 32))%N⌝ ∗
                     ⌜(page_size | N.of_nat nextStack)%N⌝ ∗ nextStackAddrIs nextStack ∗
                       ∀ (s : nat), ⌜(0 <= s < nextStack)%Z ∧ (page_size | N.of_nat s)%N⌝ -∗ ∃ l, isStack s l.


Lemma separate1 {A} (a : A) l :
  a :: l = [a] ++ l.
Proof. done. Qed.

Lemma separate2 {A} (a : A) b l :
  a :: b :: l = [a ; b] ++ l.
Proof. done. Qed.

Lemma separate3 {A} (a : A) b c l :
  a :: b :: c :: l = [a ; b ; c] ++ l.
Proof. done. Qed.

Lemma separate4 {A} (a : A) b c d l :
  a :: b :: c :: d :: l  = [a ; b ; c ; d ] ++ l.
Proof. done. Qed.

Lemma separate5 {A} (a : A) b c d e l :
  a :: b :: c :: d :: e :: l = [a ; b ; c ; d ; e] ++ l.
Proof. done. Qed.

Lemma separate6 {A} (a : A) b c d e f l :
  a :: b :: c :: d :: e :: f :: l = [a ; b ; c ; d ; e ; f] ++ l.
Proof. done. Qed.

Lemma separate7 {A} (a : A) b c d e f g l :
  a :: b :: c :: d :: e :: f :: g :: l = [a ; b ; c ; d ; e ; f ; g] ++ l.
Proof. done. Qed.

Lemma separate8 {A} (a : A) b c d e f g h l :
  a :: b :: c :: d :: e :: f :: g :: h :: l = [a ; b ; c ; d ; e ; f ; g ; h] ++ l.
Proof. done. Qed.
                                                              
Lemma separate9 {A} (a : A) b c d e f g h i l :
  a :: b :: c :: d :: e :: f :: g :: h :: i :: l = [a ; b ; c ; d ; e ; f ; g ; h ; i] ++ l.
Proof. done. Qed.

Definition validate_stack (x: immediate) :=
  [
    BI_get_local x ;
    i32const 65536 ;
    BI_binop T_i32 (Binop_i (BOI_rem SX_U)) ;
    BI_if (Tf [] []) [BI_unreachable] []
  ].
  
Lemma is_stack_divide (v : Z) s n:
  isStack v s n ⊢
  ⌜ Z.divide 65536 v ⌝.
Proof.
  iIntros "Hstack".
  unfold isStack.
  by iDestruct "Hstack" as "(%Hdiv & _)".
Qed.

Lemma is_stack_valid (v : Z) s n f E x:
    ⌜ (f_locs f) !! x = Some (value_of_int v) ⌝ ∗ 
    isStack v s n ∗ ↪[frame] f ⊢ 
    WP to_e_list (validate_stack x) @ E
    {{ w, ⌜ w = immV [] ⌝ ∗ isStack v s n ∗ ↪[frame] f }}.
Proof.
  iIntros "(%Hlocs & Hstack & Hf)".
  simpl.
  rewrite separate1.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame] f)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hf"; first by iApply wp_get_local.
  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int 0] ⌝ ∗ isStack v s n ∗ ↪[frame] f)%I).
  iSplitR; first by iIntros "(%H & _)".
  iDestruct (is_stack_divide with "Hstack") as "%Hdiv".
  iFrame "Hstack".
  iSplitL; first iApply (wp_binop with "Hf") => //.
  { iIntros "!>".
    iPureIntro => /=.
    unfold value_of_int.
    unfold Wasm_int.Int32.modu.
    simpl.
    repeat f_equal.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    unfold Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
    apply Znumtheory.Zdivide_mod in Hdiv.
    rewrite <- Znumtheory.Zmod_div_mod => //.
    by apply Znumtheory.Zmod_divide => //.
  }
  iIntros (w) "(-> & Hstack & Hf)".
  iFrame "Hstack".
  iApply (wp_if_false with "Hf") => //.
  iIntros "!> Hf".
  replace ([AI_basic (BI_block (Tf [] []) [])]) with ([] ++ [AI_basic (BI_block (Tf [] []) [])]) => //.
  iApply (wp_block with "Hf") => //.
  iIntros "!> Hf".
  by iApply (wp_label_value with "Hf").
Qed.
  
Lemma positive_add a b :
  a + b = ssrnat.NatTrec.add a b.
Proof.
  by rewrite ssrnat.NatTrec.addE.
Qed.

Lemma nat_of_bin_to_N x :
  Z.to_N (ssrnat.nat_of_bin x) = x.
Proof.
  rewrite nat_bin.
  remember (N.to_nat x) as x'.
  assert (N.of_nat x' = x); first by rewrite Heqx'; rewrite N2Nat.id.
  subst x.
  rewrite - Z_nat_N.
  f_equal.
  by rewrite Nat2Z.id.
Qed.

Lemma divide_and_multiply a b :
  (b > 0)%N -> N.divide b a -> (a `div` b * b = a)%N.
Proof.
  intros ? [c ->].
  rewrite N.div_mul => //.
  lia.
Qed.
  

Lemma div_lt a b c :
  (a < b)%N -> (c > 0)%N -> N.divide c a -> N.divide c b -> (a `div` c < b `div` c)%N.
Proof.
  intros.
  apply divide_and_multiply in H1, H2 => //=.
  rewrite - H1 in H.
  rewrite - H2 in H.
  apply N.mul_lt_mono_pos_r in H => //=.
  lia.
Qed.
      
Fixpoint stackAll {A} (s : seq.seq A) (Φ : A -> iPropI Σ) : iPropI Σ :=
  match s with
  | [] => (True)%I
  | a :: s => (Φ a ∗ stackAll s Φ)%I
  end.


Fixpoint stackAll2 {A} s1 s2 (Ψ : A -> A -> iPropI Σ) :=
  match s1, s2 with
  | [], [] => True%I
  | a1 :: s1, a2 :: s2 => (Ψ a1 a2 ∗ stackAll2 s1 s2 Ψ)%I
  | _, _ => False%I
  end.


Lemma stackAll_app {A} (s : seq.seq A) s' Φ :
  ⊢ stackAll (s ++ s') Φ ∗-∗ stackAll s Φ ∗ stackAll s' Φ.
Proof.
  iSplit.
  - iIntros "H".
    induction s => //=.
    by iFrame.
    iDestruct "H" as "[? H]".
    iFrame.
    exact IHs.
  - iIntros "[Hs Hs']".
    induction s => //=.
    iDestruct "Hs" as "[? Hs]".
    iFrame.
    exact IHs.
Qed.

Lemma drop_is_nil {A} n (s : seq.seq A) :
  drop n s = [] -> n >= length s.
Proof.
  move => Hdrop.
  assert (length s - n = 0) as Hdroplen; first by rewrite - drop_length; rewrite Hdrop.
  by lias.
Qed.

Lemma in_take {A} n s (x : A) :
  In x (take n s) -> In x s.
Proof.
  move => Hin.
  apply elem_of_list_In, elem_of_take in Hin as [i [? ?]].
  apply elem_of_list_In, elem_of_list_lookup.
  by eexists.
Qed.


End Stack.
