From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_rules proofmode.
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


(* Some useful constants *)
Definition two14 := 16384%Z.
Definition two16 := 65536%Z.
Definition two32 := 4294967296%Z.
Definition ffff0000 := 4294901760%Z.


Definition points_to_i32 `{!wasmG Σ} n i v :=
  (∃ a b c d, n ↦[wm][ i ] a ∗ n ↦[wm][N.add i 1] b ∗
                n ↦[wm][N.add i 2] c ∗ n ↦[wm][N.add i 3] d ∗
                ⌜ serialise_i32 v = [a ; b ; c ; d] ⌝)%I.
Notation "n ↦[i32][ k ] v" := (points_to_i32 n k v) (at level 50).


Lemma of_nat_to_nat_plus a b :
  N.of_nat (N.to_nat a + b) = (a + N.of_nat b)%N.
Proof. lia. Qed.

Section Stack.
  Set Bullet Behavior "Strict Subproofs".
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

(* The isStack v l n predicate describe a stack starting at location v, containing
   the mathematical stack (l: list i32), at memory n, of size 1 page.
   The first cell v points to the current top cell of the stack, so the maximum 
   number of elements the stack could contain is 16383.
*)  
Definition isStack v (l : seq.seq i32) n :=
  (let st_p := (v + length l * 4)%Z in
    ⌜ (two16 | v)%Z ⌝ ∗ ⌜(0 ≤ v ≤ ffff0000)%Z⌝ ∗ ⌜ (length l < two14)%Z ⌝ ∗
   N.of_nat n ↦[i32][ Z.to_N v ]
            (Wasm_int.Int32.repr st_p) ∗
            ([∗ list] i ↦ w ∈ l,
              N.of_nat n ↦[i32][ Z.to_N (st_p - 4 * i)%Z ] w) ∗
            ∃ bs, ⌜ (Z.of_nat (length bs) = two16 - 4 - length l * 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N st_p + 4%N] bs
  )%I.


Definition stk : string := "STACK".
Definition stkN : namespace := nroot .@ stk.

(* stack module invariant *)

Lemma N_divide_dec: ∀ a b : N, {(a | b)%N} + {¬ (a | b)%N}.
Proof.
  intros. destruct (decide ((N.to_nat a) | (N.to_nat b))).
  - left. destruct d. exists (N.of_nat x). lia.
  - right. intros Hcontr. apply n.
    destruct Hcontr. exists (N.to_nat x). lia.
Qed.

(* Lemma Z_divide_dec: ∀ a b : Z, {(a | b)%Z} + {¬ (a | b)%Z}. *)
(* Proof. *)
(*   intros. destruct (decide ((Z.to_nat a) | (Z.to_nat b))). *)
(*   - left. destruct d. exists (Z.of_nat x). lia. *)
(*   - right. intros Hcontr. apply n. *)
(*     destruct Hcontr. exists (N.to_nat x). lia. *)
(* Qed. *)

Inductive multiples_upto: N -> N -> list N -> Prop :=
| mu_base_nil n: (n > 0)%N -> multiples_upto n 0 []
| mu_ind n m l: multiples_upto n m l ->
                multiples_upto n (m + n) (m :: l).

Lemma multiples_upto_nil n m l :
  multiples_upto n m l -> (n > 0)%N.
Proof.
  intros. induction H;auto.
Qed.

Lemma multiples_upto_le n m l :
  (m > 0)%N ->
  multiples_upto n m l ->
  (n <= m)%N.
Proof.
  intros Hm.
  induction 1; by lias.
Qed.

Lemma le_mul x n :
  (2 <= x)%N ->
  (0 < n)%N ->
  (n < x * n)%N.
Proof.
  by lias.
Qed.

Lemma lt_mul x n :
  (x * n < n)%N ->
  x = 0%N.
Proof.
  by lias.
Qed.

Lemma multiples_upto_div :
  forall n m l,
    multiples_upto n m l ->
    (n | m)%N.
Proof.
  induction 1.
  - apply N.divide_0_r.
  - apply N.divide_add_r;auto.
    apply N.divide_refl.
Qed.

Lemma multiples_upto_in_lt :
  forall n m l i,
    multiples_upto n m l ->
    i ∈ l -> (i < m)%N.
Proof.
  induction 1;intros Hin.
  inversion Hin.
  inversion Hin;subst.
  { apply multiples_upto_nil in H. lia. }
  apply IHmultiples_upto in H2.
  lia.
Qed.

Lemma multiples_upto_in_div :
  forall n m l i,
    multiples_upto n m l ->
    i ∈ l -> (n | i)%N.
Proof.
  induction 1;intros Hin.
  inversion Hin.
  inversion Hin;subst.
  { apply multiples_upto_div in H. auto. }
  apply IHmultiples_upto in H2.
  auto.
Qed.
  
Lemma times_lt n1 n2 n3 :
  n1 * n3 < n2 * n3 ->
  n1 < n2.
Proof.
  by lias.
Qed.
  
Lemma times_lt_plus x x0 n :
  n > 0 ->
  (x * n < x0 * n + n) ->
  (x <= x0).
Proof.
  by lias.
Qed.

Lemma Nat2N_le_inj n1 n2 :
  n1 <= n2 <-> (N.of_nat n1 <= N.of_nat n2)%N.
Proof. lia. Qed.
Lemma Nat2N_lt_inj n1 n2 :
  n1 < n2 <-> (N.of_nat n1 < N.of_nat n2)%N.
Proof. lia. Qed.
Lemma N2Nat_le_inj n1 n2 :
  N.to_nat n1 <= N.to_nat n2 <-> (n1 <= n2)%N.
Proof. lia. Qed.
Lemma N2Nat_lt_inj n1 n2 :
  N.to_nat n1 < N.to_nat n2 <-> (n1 < n2)%N.
Proof. lia. Qed.

Lemma multiples_upto_in :
  forall n m l i, multiples_upto n m l ->
  (i < m)%N ->
  (n | i)%N ->
  i ∈ l.
Proof.
  intros n m l i H lt.
  assert (0 < m)%N as lm. lia.
  revert H lm lt.
  generalize dependent i.
  generalize dependent l.
  generalize dependent m.
  generalize dependent n.
  induction 1.
  - lia.
  - intros lm lt div.
    apply multiples_upto_div in H as div'.
    destruct (decide (i = m));subst.
    + constructor.
    + constructor.
      apply IHmultiples_upto;auto.
      { destruct m;[|lia].
        rewrite N.add_0_l in lt.
        rewrite N.add_0_l in lm.
        destruct div. subst i.
        apply lt_mul in lt;subst.
        rewrite N.mul_0_l in n0. lia. }
      destruct div,div';subst.
      apply N2Nat_lt_inj in lt.
      rewrite !N2Nat.inj_add !N2Nat.inj_mul in lt.
      apply times_lt_plus in lt;[|lia].
      apply N2Nat_le_inj in lt.
      apply N.mul_le_mono_r with _ _ n in lt.
      lia.
Qed.

Definition stackModuleInv (isStack : Z -> seq.seq i32 -> iPropI Σ) (nextStackAddrIs : nat -> iPropI Σ) : iProp Σ :=
  ∃ (nextStack : nat), ⌜(page_size | N.of_nat nextStack)%N⌝ ∗ nextStackAddrIs nextStack ∗
                     ∃ l, ⌜multiples_upto page_size (N.of_nat nextStack) l⌝ ∗
                          [∗ list] s ∈ l, ∃ stk, isStack (Z.of_N s) stk.


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

Lemma check_stack_valid (v : Z) (* s *) (* n *) f E x:
    ⌜ (f_locs f) !! x = Some (value_of_int v) ⌝ ∗ 
     ↪[frame] f ⊢ 
    WP to_e_list (validate_stack x) @ E
    {{ w, (⌜ w = trapV ⌝ ∨ ⌜ w = immV [] ⌝ ∗ ⌜ (65536 | v)%Z ⌝) ∗ ↪[frame] f }}.
Proof.
  iIntros "(%Hlocs & Hf)".
  simpl.
  rewrite separate1.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame] f)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hf"; first by iApply wp_get_local.
  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate3.

  (* case splitting *)
  destruct (decide ((v `mod` 65536)%Z = 0%Z)).
  - iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [value_of_int 0] ⌝ ∗ ↪[frame] f)%I).
    iSplitR; first by iIntros "(%H & _)".
    iSplitL. iApply (wp_binop with "Hf") => //.
    { iIntros "!>".
      iPureIntro => /=.
      unfold value_of_int.
      unfold Wasm_int.Int32.modu.
      simpl.
      repeat f_equal.
      rewrite Wasm_int.Int32.Z_mod_modulus_eq.
      unfold Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
      rewrite <- Znumtheory.Zmod_div_mod => //.
      by apply Znumtheory.Zmod_divide => //.
    }
    iIntros (w) "(-> & Hf)".
    iApply (wp_if_false with "Hf") => //.
    iIntros "!> Hf".
    replace ([AI_basic (BI_block (Tf [] []) [])]) with ([] ++ [AI_basic (BI_block (Tf [] []) [])]) => //.
    iApply (wp_block with "Hf") => //.
    iIntros "!> Hf".
    iApply (wp_label_value with "Hf");eauto.
    iNext. iRight. iSplit;auto. iPureIntro.
    apply Z.mod_divide;[unfold page_size;lia|]. auto.
  - iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [value_of_int _] ⌝ ∗ ↪[frame] f)%I).
    iSplitR; first by (iIntros "[%H _]").
    iSplitL. iApply (wp_binop with "Hf") => //.
    iIntros (w) "[-> Hf]".
    iApply (wp_if_true with "Hf") => //.
    { simpl.
      repeat f_equal.
      rewrite Wasm_int.Int32.Z_mod_modulus_eq.
      unfold Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
      rewrite <- Znumtheory.Zmod_div_mod => //.
      2: by apply Znumtheory.Zmod_divide => //.
      intros Hcontr. inversion Hcontr.
      rewrite Wasm_int.Int32.Z_mod_modulus_id in H0; [lia|].
      unfold Wasm_int.Int32.modulus.
      unfold two_power_nat. simpl.
      pose proof (Z_mod_lt v 65536). lia. }
    iNext. iIntros "Hf".
    take_drop_app_rewrite 0. iApply (wp_block with "Hf") => //.
    iIntros "!> Hf /=".
    build_ctx [AI_basic BI_unreachable].
    iApply wp_label_bind.
    iApply (wp_wand _ _ _ (λ v, ⌜v = trapV⌝ ∗ _)%I with "[Hf]").
    iApply (wp_unreachable with "Hf");eauto.
    iIntros (w) "[-> Hf]".
    deconstruct_ctx.
    iApply (wp_label_trap with "Hf");auto.
Qed.



Definition validate_stack_bound (x: immediate) :=
  [
    BI_get_local x ;
    BI_load T_i32 None N.zero N.zero ;
    BI_drop
  ].

Lemma is_stack_bound_valid (v : Z) s n f E x:
   ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
   ⌜ (f_locs f) !! x = Some (value_of_int v) ⌝ ∗
    isStack v s n ∗ ↪[frame] f ⊢ 
    WP to_e_list (validate_stack_bound x) @ E
    {{ w, ⌜ w = immV [] ⌝ ∗ isStack v s n ∗ ↪[frame] f }}.
Proof.
  iIntros "(%Hinst & %Hlocs & Hstack & Hf)".
  simpl.
  rewrite separate1.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame] f)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hf"; first by iApply wp_get_local.
  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  iDestruct "Hstack" as "(%Hdiv & %Hvub & %Hlen & Hv & Hs & Hrest)".
  iSplitR; last iSplitL "Hv Hf".
  2: { iApply wp_load => //; last first.
       iFrame "Hf".
       iDestruct (i32_wms with "Hv") as "Hv" => //=.
       rewrite Wasm_int.Int32.Z_mod_modulus_eq.
       iSplitR "Hv"; last first.
       { rewrite Z.mod_small.
         unfold N.zero.
         rewrite N.add_0_r.
         instantiate (1 := VAL_int32 _) => /=.
         by iFrame "Hv".
         split; try by lias.
         unfold ffff0000 in Hvub.
         replace Wasm_int.Int32.modulus with 4294967296%Z; by lias.
       }
       { by instantiate (1 := λ v, ⌜ v = immV [_] ⌝%I ). }
       { done. }
  }
  { iIntros "((%Habs & _) & _)"; by inversion Habs. }
  iIntros (w) "((-> & Hv) & Hf)".
  simpl.
  unfold N.zero.
  rewrite N.add_0_r.
  iDestruct (i32_wms with "Hv") as "Hv" => //=.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq Z.mod_small; last first.
  { unfold ffff0000 in Hvub.
    replace Wasm_int.Int32.modulus with 4294967296%Z; by lias.
  }
  iFrame "Hs Hrest Hv".
  iApply (wp_wand with "[Hf]"); first by iApply (wp_drop with "Hf"); instantiate (1 := λ v, ⌜ v = immV _ ⌝%I).
  iIntros (w) "(-> & Hf)".
  by repeat iSplit => //.
Qed.

Lemma u32_modulus: Wasm_int.Int32.modulus = 4294967296%Z.
Proof.
  by lias.
Qed.

Lemma stack_pure v s n:
  isStack v s n -∗
  ⌜(two16 | v)%Z⌝ ∗ ⌜(0 <= v <= ffff0000)%Z⌝ ∗ ⌜(length s < two14)%Z⌝ ∗ isStack v s n.
Proof.
  iIntros "Hs".
  repeat iSplit => //; by iDestruct "Hs" as "(% & (% & %) & % & ?)".
Qed.

Lemma stack_load_0 v s n f E:
  ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ -∗
  isStack v s n -∗
  ↪[frame] f -∗
  WP [AI_basic (BI_const (value_of_int v)); AI_basic (BI_load T_i32 None N.zero N.zero)] @ E
  {{ w, ⌜ w = immV [value_of_int (v + length s * 4)] ⌝ ∗ isStack v s n ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hinstmem Hs Hf" => /=.
  
  iDestruct (stack_pure with "Hs") as "(%Hdiv & %Hvb & %Hlens & Hs)".
  
  iApply (wp_wand with "[Hs Hf]").
  iApply wp_load => //; last first.
  { unfold isStack.
    iDestruct "Hs" as "(% & % & % & Hn & Hrest)".
    iDestruct (i32_wms with "Hn") as "Hn".
    rewrite N.add_0_r.
    simpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small; last by unfold ffff0000 in Hvb; rewrite u32_modulus; lia.
    unfold bits.
    instantiate (1 := VAL_int32 _) => /=.
    iFrame.
    iNext.
    instantiate (1 := λ w, (⌜ w = immV _ ⌝ ∗ _)%I) => /=.
    iSplit => //.
    by iApply "Hrest".
  }
  { done. }
  { iIntros (w) "(((-> & Hrest) & Hn) & Hf)".
    iSplit => //.
    iFrame.
    repeat iSplit => //=.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small; last by unfold ffff0000 in Hvb; rewrite u32_modulus; lia.
    rewrite N.add_0_r.
    by iApply i32_wms.
  }
Qed.

Lemma stack_load_0_alt v s n f E k:
  ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ -∗
  ⌜ k = (v + length s * 4)%Z ⌝ -∗
  isStack v s n -∗
  ↪[frame] f -∗
  WP [AI_basic (BI_const (value_of_int v)); AI_basic (BI_load T_i32 None N.zero N.zero)] @ E
  {{ w, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s n ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hinstmem %Hk Hs Hf" => /=.
  subst k.
  by iApply (stack_load_0 with "[] [$] [$]").
Qed.

Lemma stack_load_j v s n f E j sv:
  ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ -∗
  ⌜ s !! (Z.to_nat j) = Some sv ⌝ -∗
  ⌜ (0 <= j < length s)%Z ⌝ -∗
  isStack v s n -∗
  ↪[frame] f -∗
  WP [AI_basic (BI_const (value_of_int (v + length s * 4 - 4 * j))); AI_basic (BI_load T_i32 None N.zero N.zero)] @ E
  {{ w, ⌜ w = immV [VAL_int32 sv] ⌝ ∗ isStack v s n ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hinstmem %Hsv %Hjbound Hs Hf" => /=.

  iDestruct (stack_pure with "Hs") as "(%Hdiv & %Hvb & %Hlens & Hs)".
  
  assert (0 <= j < 16383)%Z as Hjb; first by unfold two14 in Hlens; lia.
  
  iApply (wp_wand with "[Hs Hf]").
  iApply wp_load => //; last first.
  { unfold isStack.
    iDestruct "Hs" as "(_ & _ & _ & Hn & Hcontent & Hrest)".
    iDestruct (big_sepL_lookup_acc with "Hcontent") as "(Hj & Hcrest)" => //=.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small; last first.
    { unfold ffff0000 in Hvb; unfold two14 in Hlens; rewrite u32_modulus.
      remember (length s) as x.
      rewrite - Heqx.
      lia.
    }
    rewrite N.add_0_r.
    iDestruct (i32_wms with "Hj") as "Hj".
    unfold bits.
    instantiate (1 := VAL_int32 sv) => /=.
    iSplitR "Hf Hj"; last first.
    iFrame "Hf".
    replace (4*Z.to_nat j)%Z with (4*j)%Z => //.
    lia.
    instantiate (1 := λ w, (⌜ w = immV [VAL_int32 sv] ⌝ ∗ _)%I).
    iIntros "!>" => /=.
    iSplit => //.
    iCombine "Hn Hrest Hcrest" as "H".
    by iApply "H".
  }
  { done. }

  iIntros (w) "(((-> & Hn & Hrest & Hcrest) & Hj) & Hf)".
  iSplit => //.
  iFrame.
  repeat iSplit => //=.
  iApply "Hcrest".
  iDestruct (i32_wms with "Hj") as "Hj".
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small; last first.
  { unfold ffff0000 in Hvb; unfold two14 in Hlens; rewrite u32_modulus.
    remember (length s) as x.
    rewrite - Heqx.
    lia.
  }
  rewrite N.add_0_r.
  replace (4*Z.to_nat j)%Z with (4*j)%Z => //.
  lia.  
Qed.

Lemma stack_load_j_alt v s n f E j k sv:
  ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ -∗
  ⌜ k = (v + length s * 4 - 4 * j)%Z ⌝ -∗
  ⌜ s !! (Z.to_nat j) = Some sv ⌝ -∗
  ⌜ (0 <= j < length s)%Z ⌝ -∗
  isStack v s n -∗
  ↪[frame] f -∗
  WP [AI_basic (BI_const (value_of_int k)); AI_basic (BI_load T_i32 None N.zero N.zero)] @ E
  {{ w, ⌜ w = immV [VAL_int32 sv] ⌝ ∗ isStack v s n ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hinstmem %Hk %Hsv %Hjbound Hs Hf" => /=.
  subst k.
  by iApply (stack_load_j with "[] [] [] [$] [$]").
Qed.

Lemma stack_store_j v (s: list i32) n f E j sv (v0: i32):
  ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ -∗
  ⌜ s !! (Z.to_nat j) = Some sv ⌝ -∗
  ⌜ (0 <= j < length s)%Z ⌝ -∗
  isStack v s n -∗
  ↪[frame] f -∗
  WP [AI_basic (BI_const (value_of_int (v + length s * 4 - 4 * j))); AI_basic (BI_const (VAL_int32 v0)); AI_basic (BI_store T_i32 None N.zero N.zero)] @ E
  {{ w, ⌜ w = immV [] ⌝ ∗ isStack v (<[ Z.to_nat j := v0 ]> s) n ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hinstmem %Hsv %Hjbound Hs Hf" => /=.

  iDestruct (stack_pure with "Hs") as "(%Hdiv & %Hvb & %Hlens & Hs)".
  
  assert (0 <= j < 16383)%Z as Hjb; first by unfold two14 in Hlens; lia.
  
  iApply (wp_wand with "[Hs Hf]").
  iApply wp_store => //; last first.
  { unfold isStack.
    iDestruct "Hs" as "(_ & _ & _ & Hn & Hcontent & Hrest)".
    iDestruct (big_sepL_insert_acc with "Hcontent") as "(Hj & Hcrest)" => //=.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small; last first.
    { unfold ffff0000 in Hvb; unfold two14 in Hlens; rewrite u32_modulus.
      remember (length s) as x.
      rewrite - Heqx.
      lia.
    }
    rewrite N.add_0_r.
    iDestruct (i32_wms with "Hj") as "Hj".
    iSplitR "Hf Hj"; last first.
    iFrame "Hf".
    replace (4*Z.to_nat j)%Z with (4*j)%Z => //.
    lia.
    instantiate (1 := λ w, (⌜ w = immV [] ⌝ ∗ _)%I).
    iIntros "!>" => /=.
    iSplit => //.
    iCombine "Hn Hrest Hcrest" as "H".
    by iApply "H".
  }
  { done. }

  iIntros (w) "(((-> & Hn & Hrest & Hcrest) & Hj) & Hf)".
  iSplit => //.
  iFrame "Hf".
  repeat iSplit => //=.
  { by rewrite insert_length. }
  repeat rewrite insert_length.
  iFrame.
  iApply "Hcrest".
  iDestruct (i32_wms with "Hj") as "Hj".
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small; last first.
  { unfold ffff0000 in Hvb; unfold two14 in Hlens; rewrite u32_modulus.
    remember (length s) as x.
    rewrite - Heqx.
    lia.
  }
  rewrite N.add_0_r.
  replace (4*Z.to_nat j)%Z with (4*j)%Z => //.
  lia.  
Qed.

Lemma stack_store_j_alt v (s: list i32) n f E j k sv (v0: i32):
  ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ -∗
  ⌜ k = (v + length s * 4 - 4 * j)%Z ⌝ -∗
  ⌜ s !! (Z.to_nat j) = Some sv ⌝ -∗
  ⌜ (0 <= j < length s)%Z ⌝ -∗
  isStack v s n -∗
  ↪[frame] f -∗
  WP [AI_basic (BI_const (value_of_int k)); AI_basic (BI_const (VAL_int32 v0)); AI_basic (BI_store T_i32 None N.zero N.zero)] @ E
  {{ w, ⌜ w = immV [] ⌝ ∗ isStack v (<[ Z.to_nat j := v0 ]> s) n ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hinstmem %Hsv %Hjbound Hs Hf" => /=.
  subst k.
  by iApply (stack_store_j with "[] [] [$] [$]").
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

Lemma two16_div_i32 :
  (two16 | Wasm_int.Int32.modulus)%Z.
Proof.
  rewrite u32_modulus.
  unfold two16. exists 65536%Z. lia.
Qed.

Lemma wasm_int_signed x:
  (-2147483648 <= x <= 2147483647)%Z ->
  Wasm_int.Int32.signed (Wasm_int.Int32.repr x) = x.
Proof.
  move => Hbound.
  rewrite Wasm_int.Int32.signed_repr; first by lias.
  unfold Wasm_int.Int32.min_signed.
  unfold Wasm_int.Int32.max_signed.
  unfold Wasm_int.Int32.half_modulus.
  rewrite u32_modulus.
  replace (4294967296 `div` 2)%Z with (2147483648)%Z; by lias.
Qed.

Lemma wasm_int_unsigned x:
  (0 <= x <= 4294967295)%Z ->
  Wasm_int.Int32.unsigned (Wasm_int.Int32.repr x) = x.
Proof.
  move => Hbound.
  rewrite Wasm_int.Int32.unsigned_repr; first by lias.
  unfold Wasm_int.Int32.max_unsigned.
  rewrite u32_modulus.
  by lias.
Qed.


End Stack.
