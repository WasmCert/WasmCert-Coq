From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_fundamental_helpers.
Require Export datatypes host operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.


Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50). 
   
Notation "{{{ P }}} es @ E {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗ (WP (es : iris.expr) @ NotStuck ; E {{ v, Φ v }}))%I (at level 50).


Section stack.


 Context `{!wasmG Σ}. 


 
Section code.

Definition i32const (n:Z) := BI_const (VAL_int32 (Wasm_int.int_of_Z i32m n)).
Definition value_of_int (n:Z) := VAL_int32 (Wasm_int.int_of_Z i32m n).


Definition two14 := 16384%Z.
Definition two16 := 65536%Z.
Definition two32 := 4294967296%Z.





Definition new_stack :=
  [
    i32const 1 ;
    BI_grow_memory ;
    BI_tee_local 0 ;
    i32const (-1) ;
    BI_relop T_i32 (Relop_i ROI_eq) ;  
    BI_if (Tf [] [T_i32]) [
        i32const (-1)
      ] [
        BI_get_local 0 ;
        i32const 65536 ;
        BI_binop T_i32 (Binop_i BOI_mul) ;
        BI_tee_local 0 ;
        BI_get_local 0 ;
        i32const 4 ;
        BI_binop T_i32 (Binop_i BOI_add) ;
        BI_store T_i32 None N.zero N.zero ;
        BI_get_local 0 
      ]                             
  ].

Definition is_empty :=
  [
    BI_get_local 0 ;
    i32const 4 ;
    BI_binop T_i32 (Binop_i BOI_add) ;
    BI_get_local 0 ;
    BI_load T_i32 None N.zero N.zero ;
    BI_relop T_i32 (Relop_i ROI_eq)
  ].

Definition is_full :=
  [
    i32const 0 ;
    i32const 1 ;
    BI_get_local 0 ;
    BI_load T_i32 None N.zero N.zero ;
    i32const 65536 ;
    BI_binop T_i32 (Binop_i (BOI_rem SX_U)) ;
    BI_select
  ].




Definition pop :=
  [
    BI_get_local 0 ;
    BI_load T_i32 None N.zero N.zero ;
    i32const 4 ;
    BI_binop T_i32 (Binop_i BOI_sub) ;
    BI_tee_local 1 ;
    BI_load T_i32 None N.zero N.zero ;
    BI_get_local 0 ;
    BI_get_local 1 ;
    BI_store T_i32 None N.zero N.zero
  ].

Definition push :=
  [
    BI_get_local 1 ;
    BI_load T_i32 None N.zero N.zero ;
    BI_tee_local 2 ;
    BI_get_local 0 ;
    BI_store T_i32 None N.zero N.zero ;
    BI_get_local 1 ;
    BI_get_local 2 ;
    i32const 4 ;
    BI_binop T_i32 (Binop_i BOI_add) ;
    BI_store T_i32 None N.zero N.zero
  ].


Definition stack_map :=
  [
    BI_get_local 1 ;
    BI_load T_i32 None N.zero N.zero ;
    BI_set_local 3 ;
    BI_get_local 1 ;
    i32const 4 ;
    BI_binop T_i32 (Binop_i BOI_add) ;
    BI_set_local 2 ;
    BI_block (Tf [] [])
             [BI_loop (Tf [] [])
                      [BI_get_local 2 ;
                       BI_get_local 3 ;
                       BI_relop T_i32 (Relop_i (ROI_ge SX_U)) ;
                       BI_br_if 1 ;
                       BI_get_local 2 ;
                       BI_get_local 2 ;
                       BI_get_local 2 ;
                       BI_load T_i32 None N.zero N.zero ;
                       BI_get_local 0 ;
                       BI_call_indirect 1 ;
                       BI_store T_i32 None N.zero N.zero ;
                       i32const 4 ;
                       BI_binop T_i32 (Binop_i BOI_add) ;
                       BI_set_local 2 ;
                       BI_br 0]
             ]
  ].



End code.


 
Section specs.


   (* Context `{!wasmG Σ}.  *)


Definition points_to_i32 n i v :=
  (∃ a b c d, n ↦[wm][ i ] a ∗ n ↦[wm][N.add i 1] b ∗
                n ↦[wm][N.add i 2] c ∗ n ↦[wm][N.add i 3] d ∗
                ⌜ serialise_i32 v = [a ; b ; c ; d] ⌝)%I.
Notation "n ↦[i32][ k ] v" := (points_to_i32 n k v) (at level 50).



Lemma of_nat_to_nat_plus a b :
  N.of_nat (N.to_nat a + b) = (a + N.of_nat b)%N.
Proof. lia. Qed.

Lemma i32_wms n i v :
  n ↦[i32][ i ] v ⊣⊢ n ↦[wms][ i ]serialise_i32 v.
Proof.
  iSplit ; iIntros "H" ; unfold mem_block_at_pos, points_to_i32.
  - iDestruct "H" as (a b c d) "(? & ? & ? & ? & ->)".
    iSimpl.
    repeat rewrite of_nat_to_nat_plus.
    rewrite N.add_0_r.
    iFrame.
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

Lemma positive_add a b :
  a + b = ssrnat.NatTrec.add a b.
Proof.
  unfold ssrnat.NatTrec.add.
  generalize dependent b.
  induction a.
  lia.
  fold ssrnat.NatTrec.add.
  fold ssrnat.NatTrec.add in IHa.
  intro b.
  rewrite - IHa.
  lia.
Qed.


Lemma nat_of_bin_to_N x :
  Z.to_N (ssrnat.nat_of_bin x) = x.
Proof.
  unfold Z.to_N. 
  unfold ssrnat.nat_of_bin.
  destruct x => //=.
  unfold Z.of_nat.
  induction p => //=.
  - unfold ssrnat.NatTrec.double.
    destruct (ssrnat.nat_of_pos p) eqn:Hp => //=.
    rewrite - positive_add.
    lia.
  - unfold ssrnat.NatTrec.double.
    destruct (ssrnat.nat_of_pos p) eqn:Hp => //=.
    rewrite - positive_add.
    destruct (n + S (S n)) eqn:Habs ; lia.
Qed.

Lemma divide_and_multiply a b :
  (b > 0)%N -> N.divide b a -> (a `div` b * b = a)%N.
Proof.
  intros ? [c ->].
  rewrite N.div_mul.
  done.
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

Lemma spec_new_stack f0 n len E: 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ length (f_locs f0) >= 1 ⌝ ∗
        ⌜ (Wasm_int.Int32.modulus - 1)%Z <>
         Wasm_int.Int32.Z_mod_modulus (ssrnat.nat_of_bin (len `div` page_size)) ⌝ ∗
        ⌜ (len + 4 < Z.to_N (two_power_nat 32))%N ⌝ ∗
        ⌜ (page_size | len)%N ⌝ ∗
        ↪[frame] f0 ∗
        N.of_nat n ↦[wmlength] len }}}
    to_e_list new_stack @ E
    {{{ v , (∃ (k : Z), ⌜ v = immV [value_of_int k] ⌝ ∗
                                   (⌜ (k = -1)%Z ⌝ ∗
                                      N.of_nat n↦[wmlength] len ∨
                                      ⌜ (0 <= k)%Z /\ (k + Z.of_N page_size <= two32)%Z ⌝ ∗
                                     isStack k [] n ∗
                                     N.of_nat n ↦[wmlength] (len + page_size)%N) ∗
            ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f1 = f_inst f0 ⌝)%I }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hflocs & %Hmod & %Hlenoverflow4 & %Hlendiv & Hframe & Hlen) HΦ".
  assert (page_size | len)%N as Hlenmod => //=.
  apply divide_and_multiply in Hlenmod => //=.
  assert (len < Z.to_N (two_power_nat 32))%N as Hlenoverflow ; first lia.
  assert (len `div` page_size < Z.to_N (two_power_nat 32))%N.
  { destruct len ; first done.
    remember (N.pos p) as len.
    assert (len `div`page_size < len)%N.
    apply N.div_lt.
    subst. lia.
    unfold page_size. lia.
    lia. }
  unfold new_stack.
  rewrite separate2.
  iApply wp_seq => /=.
  iSplitR.
  - instantiate (1 := λ x,
                   (((⌜ x = immV [VAL_int32 (Wasm_int.int_of_Z
                                            i32m (ssrnat.nat_of_bin
                                                    (len `div` page_size)))] ⌝ ∗
                               (N.of_nat n ↦[wms][ len ]
                                              repeat #00%byte (N.to_nat page_size)) ∗
                              N.of_nat n↦[wmlength] (len + page_size)%N)
                              
                   ∨ (⌜ x = immV [VAL_int32 int32_minus_one] ⌝%I ∗
                N.of_nat n↦[wmlength] len)) ∗ ↪[frame] f0)%I).
    iIntros "[[(%Habs & _ & _) | (%Habs & _)] Hf]" ; inversion Habs.
  - iSplitR "HΦ".
    unfold i32const.
    iApply (wp_grow_memory
              NotStuck E n f0 len
              (λ x, ⌜ x = immV [VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin
                                                                     (len `div`
                                                                          page_size)))] ⌝%I)
              (λ x, ⌜ x = immV [VAL_int32 int32_minus_one] ⌝%I) (Wasm_int.int_of_Z i32m 1)).
    + exact Hinst.
    + iFrame. 
      iSplit ; by iPureIntro.
  - iIntros (w) "H".
    unfold of_val.
    destruct w ; try by iDestruct "H" as "[[[%Habs _ ]| [%Habs _]] _]" ; inversion Habs.
    destruct l ; try by iDestruct "H" as "[[[%Habs _ ]| [%Habs _]] _]" ; inversion Habs.
    destruct l ; try by iDestruct "H" as "[[[%Habs _ ]| [%Habs _]] _]" ; inversion Habs.
    unfold fmap, list_fmap.
    rewrite - separate1.
    rewrite separate2.
    iApply (wp_seq _ E _ (λ x, (⌜ x = immV [v] ⌝
                                      ∗ ↪[frame] {|
                                            f_locs := set_nth v (f_locs f0) 0 v;
                                            f_inst := f_inst f0
                                          |} )%I) ).
    iDestruct "H" as "[H Hf]".
    iSplitR.
  - iIntros "[%Habs _]" ; done.
  - iSplitL "Hf". 
    iApply (wp_tee_local with "Hf").
    iIntros "!> Hf".
    rewrite list_extra.cons_app.
    iApply wp_val_app => //=.
    iSplitR => //=.
    iIntros "!> [%Habs _]" ; done.
    iApply (wp_set_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    rewrite - separate1.
    rewrite separate3.
    iApply wp_seq.
    iSplitR.
  - instantiate (1 := (λ x, (⌜ if v == value_of_int (-1) then
                                 x = immV [value_of_int 1]
                               else x = immV [value_of_int 0] ⌝ ∗
                                             ↪[frame] {| f_locs := set_nth v
                                                                           (f_locs f0) 0 v ;
                                                        f_inst := f_inst f0 |})%I)).
    iIntros "[%Habs _]".
    by destruct (v == value_of_int (-1)).
  - iSplitL "Hf".
    iApply (wp_relop with "Hf") => //=.
    iPureIntro.
    destruct (v == value_of_int (-1)) eqn:Hv.
    move/eqP in Hv.
    by rewrite Hv.
    destruct v => //=.
    unfold value_of_int in Hv.
    unfold value_of_int.
    unfold wasm_bool.
    destruct (Wasm_int.Int32.eq s (Wasm_int.Int32.repr (-1))) eqn:Hv' => //=.
    apply Wasm_int.Int32.same_if_eq in Hv'.
    rewrite Hv' in Hv.
    rewrite eq_refl in Hv.
    inversion Hv.
  - iIntros (w) "[%Hw Hf]".
    destruct w ; try by destruct (v == value_of_int (-1)).
    destruct l ; first by destruct (v == value_of_int (-1)).
    destruct l ; last by destruct (v == value_of_int (-1)).
    unfold of_val, fmap, list_fmap.
    iSimpl.
    destruct (v == value_of_int (-1)) eqn:Hv.
    + (* grow_memory failed *)
      move/eqP in Hv ; subst v.
      inversion Hw ; subst v0.
      iApply (wp_if_true with "Hf").
      intro.
      done.
      iIntros "!> Hf".
      rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
      iApply wp_wand_r. 
      iSplitL "Hf".
      iApply (wp_block with "Hf") => //=.
      iIntros "!> Hf".
      iApply (wp_label_value with "Hf") => //=.
      instantiate (1 := λ x, ⌜ x = immV [VAL_int32 (Wasm_int.Int32.repr (-1))] ⌝%I ).
      done.
      iIntros (v) "[%Hv Hf]".
      iApply "HΦ".
      iExists _.
      iSplit.
      done.
      iDestruct "H" as "[(%Hm1 & Hb & Hlen) | [_ Hlen]]".
      inversion Hm1.
      exfalso. done.
      iSplitR "Hf".
      iLeft.
      by iSplit.
      iExists _ ; by iFrame.
    + (* grow_memory succeeded *)
      inversion Hw ; subst v0.
      iApply (wp_if_false with "Hf").
      done.
      iIntros "!> Hf".
      rewrite - (app_nil_l [AI_basic (BI_block _ _)]).

      iDestruct "H" as "[ (%Hvv & Hb & Hlen) | [%Hvv Hlen]]" ; inversion Hvv ; subst ;
        last by rewrite eq_refl in Hv ; inversion Hv.
      unfold page_size at 2.
      replace (N.to_nat (64 * 1024)) with (4 + N.to_nat (65532)) ; last done.
      rewrite repeat_app.
      unfold repeat at 1.
      rewrite - separate4.
      iDestruct (wms_append with "Hb") as "[H1 Hb]".
      iDestruct (wms_append with "Hb") as "[H2 Hb]".
      iDestruct (wms_append with "Hb") as "[H3 Hb]".
      iDestruct (wms_append with "Hb") as "[H4 Hb]".
      iAssert (N.of_nat n↦[wms][ len ] [(#00%byte) ; (#00%byte) ; (#00%byte) ; (#00%byte)])%I with "[H1 H2 H3 H4]" as "Hbs".
      { unfold mem_block_at_pos, big_opL.
        repeat rewrite of_nat_to_nat_plus ; rewrite N.add_0_r.
        replace (len + 1 + 1)%N with (len + 2)%N ; last lia.
        replace ( len + 2+ 1)%N with (len + 3)%N ; last lia.
        iFrame. }
      remember (Wasm_int.Int32.repr (ssrnat.nat_of_bin (len `div` page_size))) as c.
      iApply wp_wand_r.        
      instantiate (1 := λ x, ((⌜ x = immV [value_of_int (N.to_nat len)] ⌝ ∗ N.of_nat n↦[i32][ len ] (Wasm_int.Int32.repr (N.to_nat len + 4))) ∗ ↪[frame] {| f_locs := set_nth (VAL_int32 c) (f_locs f0) 0
                                                                                                                                                                       (VAL_int32 (Wasm_int.Int32.imul c (Wasm_int.Int32.repr 65536))); f_inst := f_inst f0 |} )%I).
      iSplitL "Hf Hbs".
      * { iApply wp_wasm_empty_ctx.
          iApply (wp_block_ctx with "Hf") => //=.
          iIntros "!> Hf".
          iApply (wp_label_push_nil _ _ _ _ 0 (LH_base [] []) with "[Hf Hbs]") ;
            last unfold lfilled, lfill => //=.
          simpl.
          rewrite (separate1 (AI_basic (BI_get_local 0))).
          iApply wp_seq_ctx; eauto.
          iSplitL ""; last first.
          - iSplitL "Hf".
            iApply (wp_get_local with "[] [$Hf]") => /=; first by rewrite set_nth_read.
            instantiate (1 := (λ x, ( ⌜x = immV [VAL_int32 c] ⌝)%I)) => //=.
          - 2: { simpl. by iIntros "(%HContra & _ )". }
            iIntros (w) "[-> Hf]".
            unfold of_val, fmap, list_fmap.
            rewrite - separate1.
            rewrite (separate3 (AI_basic _)).
            iApply wp_seq_ctx.
            iSplitL ""; last first.
          - iSplitL "Hf".
            iApply (wp_binop with "Hf").
            unfold app_binop, app_binop_i. done.
            instantiate (1 := λ x,
                           ⌜ x = immV [VAL_int32 (Wasm_int.int_mul Wasm_int.Int32.Tmixin
                                                                   c (Wasm_int.int_of_Z i32m
                                                                                        65536))
                                   ] ⌝%I ) => //=.
          - 2: { simpl. by iIntros "(%HContra & _ )". }
            iIntros (w) "[-> Hf]".
            unfold of_val, fmap, list_fmap.
            rewrite - separate1.
            rewrite (separate2 (AI_basic _)).
            iApply wp_seq_ctx.
            iSplitL ""; last first.
            iSplitL "Hf".
            iApply (wp_tee_local with "Hf").
            iIntros "!> Hf".
            rewrite separate1.
        instantiate (1 :=  ( λ x,  (⌜ x = immV [(VAL_int32 (
                                                    Wasm_int.int_mul
                                                      Wasm_int.Int32.Tmixin
                                                      c (Wasm_int.int_of_Z
                                                           i32m 65536))
                                           )] ⌝
                                              ∗ ↪[frame]
                                              {| f_locs := set_nth
                                                             (VAL_int32 (
                                                                  Wasm_int.int_mul
                                                                    Wasm_int.Int32.Tmixin
                                                                    c (Wasm_int.int_of_Z
                                                                         i32m 65536)))
                                                            (set_nth
                                                               (VAL_int32 c)
                                                               (f_locs f0) 0
                                                               (VAL_int32 c))
                                                            0
                                                             (VAL_int32 (
                                                                  Wasm_int.int_mul
                                                                    Wasm_int.Int32.Tmixin
                                                                    c (Wasm_int.int_of_Z
                                                                         i32m 65536)))
                                              |})%I)).
        iApply wp_val_app => //=.
        iSplit; first by iIntros "!> (%HContra & _)" => //.
        iApply (wp_set_local with "[] [$Hf]") => //=.
        rewrite length_is_size size_set_nth.
        unfold ssrnat.maxn.
        rewrite length_is_size in Hflocs.
        destruct (ssrnat.leq 2 (seq.size (f_locs f0))) ; lia.
        rewrite set_nth_write.
        simpl.
        iIntros (w) "[-> Hf]".
        unfold of_val, fmap, list_fmap.
        rewrite - separate1.
        rewrite (separate2 (AI_basic _)).
        iApply wp_seq_ctx.
        iSplitL ""; last first.
        iSplitL "Hf".
        rewrite separate1.
        iApply wp_val_app => //=.
        instantiate (1 := (λ x, (⌜ x = immV [VAL_int32 (Wasm_int.int_mul
                                                          Wasm_int.Int32.Tmixin
                                                          c (Wasm_int.int_of_Z
                                                               i32m 65536)) ;
                                             VAL_int32 (Wasm_int.int_mul
                                                          Wasm_int.Int32.Tmixin
                                                          c (Wasm_int.int_of_Z
                                                               i32m 65536))] ⌝ 
                                            ∗ ↪[frame]
                                            {| f_locs := set_nth (VAL_int32 c)
                                                                 (f_locs f0) 0
                                                                 (VAL_int32
                                                                    (Wasm_int.Int32.imul
                                                                       c (Wasm_int.int_of_Z
                                                                            i32m 65536))) ;
                                              f_inst := f_inst f0
                                            |})%I )).
        iSplitL ""; first by iIntros "!> (%HContra & _)" => //.
        iApply (wp_get_local with "[] [$Hf]") => //=.
        rewrite set_nth_read => //=.
        iIntros (w) "[-> Hf]".
        unfold of_val, fmap, list_fmap.
        rewrite - separate2.
        rewrite (separate4 (AI_basic _)).
        iApply wp_seq_ctx.
        iSplitL ""; last first.
        iSplitL "Hf".
        rewrite separate1.
        iApply wp_val_app => //=.
        instantiate (1 := (λ x, (⌜ x = immV [VAL_int32 (Wasm_int.Int32.imul
                                                          c (Wasm_int.Int32.repr 65536)) ;
                                             VAL_int32 (Wasm_int.Int32.iadd
                                                          (Wasm_int.Int32.imul
                                                             c (Wasm_int.int_of_Z
                                                                  i32m 65536))
                                                          (Wasm_int.int_of_Z i32m 4))] ⌝
                                            ∗ ↪[frame]
                                            {| f_locs := set_nth
                                                           (VAL_int32 c)
                                                           (f_locs f0)
                                                           0 (VAL_int32 (
                                                                  Wasm_int.Int32.imul
                                                                    c (Wasm_int.Int32.repr
                                                                         65536))) ;
                                              f_inst := f_inst f0 |})%I )).
        iSplitL ""; first by iIntros "!> (%HContra & _)" => //.
        iApply (wp_binop with "Hf") => //=.
        iIntros (w) "[-> Hf]".
        unfold of_val, fmap, list_fmap.
        rewrite - separate2.
        rewrite (separate3 (AI_basic _)).
        iApply wp_seq_ctx.
        iSplitL ""; last first.
        iSplitL.
        iApply (wp_store with "[Hf Hbs]").
        done.
        instantiate (1 := [(#00%byte); (#00%byte); (#00%byte); (#00%byte)]).
        done.
        instantiate (2 := {| f_locs := set_nth (VAL_int32 c) (f_locs f0) 0
                                               (VAL_int32 (Wasm_int.Int32.imul
                                                             c (Wasm_int.Int32.repr
                                                                  65536))) ;
                            f_inst := f_inst f0 |}) => //=.
        instantiate (1 := λ x, ⌜x = immV []⌝%I ) => //=.
        iSplitL "" => //.
        iFrame.
        replace len with (Z.to_N (Wasm_int.Int32.Z_mod_modulus (Wasm_int.Int32.unsigned c * 65536)) + N.zero)%N => //.
        rewrite Heqc.
        unfold Wasm_int.Int32.unsigned.
        rewrite N.add_0_r => /=.
        do 2 rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        rewrite (Z.mod_small (ssrnat.nat_of_bin (len `div` page_size)) (two_power_nat 32)).
        replace (ssrnat.nat_of_bin (len `div` page_size) * 65536)%Z with (Z.of_N len).
        rewrite Z.mod_small.
        lia.
        lia.
        rewrite <- Hlenmod at 1.
        unfold page_size.
        replace (64 * 1024)%N with 65536%N ; last done.
        rewrite - (Z2N.id (_ * _)%Z) ; last lia.
        rewrite Z2N.inj_mul ; try lia.
        rewrite nat_of_bin_to_N.
        lia.
        split.
        lia.
        rewrite - (Z2N.id (ssrnat.nat_of_bin _)) ; last lia.
        rewrite nat_of_bin_to_N.
        lia.
        iIntros (w) "((-> & Hwm) & Hf)".
        unfold of_val, fmap, list_fmap.
        iSimpl.
        rewrite - (app_nil_r ([AI_basic _])).
        iApply wp_seq_ctx.
        iSplitL ""; last first.
        iSplitL "Hf".
        iApply (wp_get_local with "[] [$Hf]").
        simpl.
        rewrite set_nth_read.
        done.
        iModIntro.
        instantiate (1 := λ x, ⌜x = immV [ value_of_int (N.to_nat len) ]⌝%I).
        iPureIntro.
        simpl.
        unfold value_of_int.
        rewrite Heqc.
        unfold Wasm_int.Int32.imul.
        rewrite Wasm_int.Int32.mul_signed => /=.
        repeat f_equal.
        rewrite Wasm_int.Int32.signed_repr.
        rewrite Wasm_int.Int32.signed_repr.
        rewrite <- Hlenmod at 2.
        unfold page_size.
        replace (64 * 1024)%N with 65536%N ; last done.
        rewrite - (Z2N.id (ssrnat.nat_of_bin _)) ; last lia.
        rewrite nat_of_bin_to_N.
        lia.
        unfold Wasm_int.Int32.min_signed.
        unfold Wasm_int.Int32.max_signed.
        unfold Wasm_int.Int32.half_modulus.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        done.
        unfold Wasm_int.Int32.min_signed.
        unfold Wasm_int.Int32.max_signed.
        unfold Wasm_int.Int32.half_modulus.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        rewrite - (Z2N.id (ssrnat.nat_of_bin _)) ; last lia.
        rewrite nat_of_bin_to_N.
        split.
        assert (len >= 0)%N ; first lia.
        assert (page_size > 0)%N ; first by unfold page_size ; lia.
        assert (len `div` page_size >= 0)%N ; first lia.
        assert (two_power_nat 32 >= 2)%Z.
        unfold two_power_nat.
        unfold shift_nat.
        simpl.
        lia.
        assert ( 2 > 0 )%Z ; first lia.
        assert (0 < two_power_nat 32 `div` 2)%Z.
        apply Z.div_str_pos.
        lia.
        lia.
        assert (len `div` 2 < Z.to_N (two_power_nat 32) `div` 2)%N.
        apply div_lt => //=.
        assert (2 | page_size)%N.
        unfold page_size.
        replace (64*1024)%N with 65536%N ; last done.
        unfold N.divide.
        exists 32768%N.
        done.
        eapply N.divide_trans => //=.
        unfold N.divide.
        exists 2147483648%N.
        done.
        assert ( 2 < page_size )%N .
        unfold page_size ; lia.
        assert (len `div` page_size <= len `div` 2)%N.
        apply N.div_le_compat_l.
        done.
        eapply Z.le_trans.
        instantiate (1 := Z.of_N (len `div` 2)).
        lia.
        assert (len `div`2 <= Z.to_N (two_power_nat 32) `div` 2 - 1)%N ; first lia.
        apply N2Z.inj_le in H3.
        rewrite N2Z.inj_sub in H3.
        rewrite (N2Z.inj_div (Z.to_N _)) in H3.
        rewrite Z2N.id in H3.
        lia.
        lia.
        unfold two_power_nat.
        simpl.
        replace (4294967296 `div` 2)%N with 2147483648%N ; last done.
        lia.
        iIntros (w) "[-> Hf]".
        unfold of_val, fmap, list_fmap.
        rewrite app_nil_r.
        iApply (wp_val_return with "Hf").
        done.
        iIntros "Hf".
        rewrite app_nil_r app_nil_l.
        iApply wp_value.
        unfold IntoVal.
        apply language.of_to_val.
        done.
        iFrame.
        iSplit => //=.
        replace (Z.to_N (Wasm_int.Int32.Z_mod_modulus
                           (Wasm_int.Int32.unsigned c * 65536)) + N.zero)%N
          with len.
        subst c.
        unfold Wasm_int.Int32.imul.
        unfold Wasm_int.Int32.mul.
        rewrite - (Z2N.id (ssrnat.nat_of_bin _)) ; last lia.
        rewrite nat_of_bin_to_N.
        rewrite Wasm_int.Int32.unsigned_repr.
        rewrite Wasm_int.Int32.unsigned_repr.
        replace (Z.of_N (len `div` page_size) * 65536)%Z with (Z.of_N len).
        unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
        rewrite Wasm_int.Int32.unsigned_repr.
        rewrite Wasm_int.Int32.unsigned_repr.
        unfold serialise_i32.
        rewrite Wasm_int.Int32.unsigned_repr.
        unfold value_of_int.
        iApply i32_wms => //.
        unfold bits, serialise_i32.
        simpl.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small.
        replace (Z.of_N len + 4)%Z with (N.to_nat len + 4)%Z ; last lia.
        done.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        lia.
        unfold Wasm_int.Int32.max_unsigned.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        lia.
        unfold Wasm_int.Int32.max_unsigned.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        lia.
        unfold Wasm_int.Int32.max_unsigned.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        lia.
        rewrite <- Hlenmod at 1.
        unfold page_size.
        lia.
        unfold Wasm_int.Int32.max_unsigned.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        unfold two_power_nat => //=.
        unfold Wasm_int.Int32.max_unsigned.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        split ; last lia.
        assert (len >= 0)%N ; first lia.
        assert (page_size > 0)%N ; first by unfold page_size.
        lia.
        subst c.
        rewrite Wasm_int.Int32.unsigned_repr.
        rewrite - (Z2N.id (ssrnat.nat_of_bin _)).
        rewrite nat_of_bin_to_N.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small.
        rewrite <- Hlenmod at 1.
        unfold page_size.
        replace (64 * 1024)%N with 65536%N ; last done.
        rewrite - (Z2N.id 65536%Z).
        rewrite - N2Z.inj_mul.
        rewrite N2Z.id.
        unfold N.zero.
        lia.
        lia.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        rewrite - (Z2N.id 65536).
        rewrite - N2Z.inj_mul.
        unfold page_size.
        unfold page_size in Hlenmod.
        replace (64 * 1024)%N with 65536%N ; last done.
        replace (64 * 1024)%N with 65536%N in Hlenmod ; last done.
        rewrite Hlenmod.
        lia.
        lia.
        lia.
        unfold Wasm_int.Int32.max_unsigned.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        rewrite - (Z2N.id (ssrnat.nat_of_bin _)).
        rewrite nat_of_bin_to_N.
        split ; last lia.
        assert (len >= 0)%N ; first lia.
        assert (page_size > 0)%N ; first by unfold page_size ; lia.
        lia.
        lia.
      * (* clears some of the non-trap subgoals at this point. TODO: restructure this so that we don't get all of these at the end *)
        all: try by iIntros "(%HContra & _)".
        by iIntros "((%HContra & _) & _)". } 
      * iIntros (w) "[[-> Hn] Hf]".
        iApply "HΦ".
        iExists _.
        iSplit ; first done.
        iSplitR "Hf".
        iRight.
        iSplit.
        iPureIntro.
        split ; first lia.
        { destruct Hlendiv as [k ->].
          unfold page_size.
          unfold two32.
          replace (Z.to_N (two_power_nat 32)) with 4294967296%N in Hlenoverflow ; last done.
          unfold page_size in Hlenoverflow.
          assert (k < 65536)%N.
          lia.
          assert (k + 1 <= 65536)%N ; first lia.
          replace (N.to_nat (k * (64 * 1024)) + Z.pos (64 * 1024))%Z
            with (N.to_nat (k + 1)%N * (64 * 1024))%Z ; last lia.
          lia. }
        iSplitR "Hlen". 
        unfold isStack.
        replace (Z.to_N (N.to_nat len)) with len ; last lia.
        iSimpl.
        replace (N.to_nat len + 4 + 0%nat * 4)%Z with (N.to_nat len + 4)%Z ; last lia.
        iSplitR.
        iPureIntro.
        unfold page_size in Hlendiv.
        replace (64 * 1024)%N with 65536%N in Hlendiv ; last done.
        unfold Z.divide.
        unfold N.divide in Hlendiv.
        destruct Hlendiv as [r ->].
        exists (Z.of_N r).
        unfold two16 ; lia.
        iSplitR.
        iPureIntro.
        unfold two14 ; lia.
        iSplitL "Hn" ; first done.
        iSplit ; first done.
        iExists (repeat #00%byte ( N.to_nat 65532)).
        iSplit ; first by rewrite repeat_length.
        replace (Z.to_N (N.to_nat len + 4)) with (len + 1 + 1 + 1 + 1)%N ; last lia.
        done.
        done.
        iExists _ ; iFrame.
        done.
Qed.



Lemma spec_is_empty f0 n v s E: 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ (f_locs f0) !! 0 = Some (value_of_int v) ⌝ ∗ 
        ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - length s * 4)%Z ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s n }}}
    to_e_list is_empty @  E
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s n ∗
                           ⌜ (k = 1 /\ s = []) \/
                  (k = 0 /\ s <> []) ⌝ ∗
           ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝}}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hv & Hf & Hstack) HΦ" => /=.
  unfold is_empty.
  rewrite separate1.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR.
  by iIntros "[%Habs _]".
  iSplitL "Hf".
  - iApply (wp_get_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap .
    rewrite - separate1.
    rewrite separate3.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [value_of_int (v + 4)%Z] ⌝ ∗ ↪[frame] f0)%I).
    iSplitR.
    by iIntros "[%Habs _]".
    iSplitL "Hf".
  - iApply (wp_binop with "Hf") => //=.
    unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
    rewrite Wasm_int.Int32.unsigned_repr.
    rewrite Wasm_int.Int32.unsigned_repr.
    done.
    unfold Wasm_int.Int32.max_unsigned.
    unfold Wasm_int.Int32.modulus.
    unfold Wasm_int.Int32.wordsize.
    unfold Integers.Wordsize_32.wordsize.
    replace (two_power_nat 32) with 4294967296%Z ; last done.
    lia.
    lia.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    rewrite - separate1.
    rewrite separate2.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [value_of_int (v + 4)%Z ; value_of_int v] ⌝
                                       ∗ ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate1.
    iApply wp_val_app => //=.
    iSplitR.
    by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    rewrite - separate2.
    rewrite separate3.
    iApply wp_seq.
    instantiate ( 1 := λ x, ((((⌜ x = immV [value_of_int (v + 4)%Z ;
                                            value_of_int (v + 4 + length s * 4)%Z] ⌝
                                          ∗ [∗ list] i↦w ∈ s,
                                N.of_nat n ↦[i32][ Z.to_N (v + 4 + length s * 4 - 4 - 4 * i)] w) ∗

                                                                                                 (∃ bs, ⌜ (Z.of_nat (length bs) = two16 - 4 - length s * 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N (v + 4 + length s * 4)]bs))
                                           ∗  N.of_nat n↦[wms][(Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m v) + N.zero)%N]bits (value_of_int (v + 4 + length s * 4)) )
                                           ∗ ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[[[[%Habs _ ]_ ] _] _]".
    iDestruct "Hstack" as "(%Hdiv & %Hlen & Hv & Hs & Hrest)". 
    iSplitR "HΦ".
  - rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [[[[%Habs _ ] _ ] _ ] _ ]".
    unfold value_of_int.
    iApply wp_load => //=.
    iSplitL "Hs Hrest".
    iFrame.
    done.
    iFrame.
    rewrite N.add_0_r.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    iDestruct (i32_wms with "Hv") as "Hv" => //.
  - iIntros (w) "[[[[->  Hs] Hrest] Hp] Hf]".
    iAssert (isStack v s n)%I with "[Hrest Hp Hs]" as "Hstack".
    unfold isStack.
    iFrame.
    rewrite N.add_0_r.
    simpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    repeat iSplit => //=.
    iApply i32_wms => //.
  - unfold of_val, fmap, list_fmap.
    rewrite - separate2.
    iApply wp_wand_r.
    iSplitL "Hf".
    iApply (wp_relop with "Hf") => //=.
    instantiate (1 := λ x, ⌜ x = immV [VAL_int32 (wasm_bool (Wasm_int.Int32.eq (Wasm_int.Int32.repr (v + 4)) (Wasm_int.Int32.repr (v + 4 + length s * 4))))] ⌝%I).
    done.
  - iIntros (w) "[-> Hf]".
    iApply "HΦ".
    iExists _.
    iSplitR.
    iPureIntro.
    unfold value_of_int.
    unfold wasm_bool.
    instantiate (1 := if Wasm_int.Int32.eq (Wasm_int.Int32.repr (v + 4))
                                           (Wasm_int.Int32.repr (v + 4 + length s * 4))
                      then 1%Z else 0%Z).
    destruct (Wasm_int.Int32.eq (Wasm_int.Int32.repr (v + 4))
                                (Wasm_int.Int32.repr (v + 4 + length s * 4))) => //=.
  - iFrame.
    iSplit.
    iPureIntro.
    destruct s.
    left.
    split => //=.
    replace (v + 4 + 0%nat * 4)%Z with (v + 4)%Z ; last lia.
    by rewrite Wasm_int.Int32.eq_true.
    right.
    split => //=.
    rewrite Wasm_int.Int32.eq_false => //=.
    intro.
    simpl in Hv.
    apply Wasm_int.Int32.repr_inv in H ; unfold Wasm_int.Int32.max_unsigned in Hv ; try lia.
    iExists _ ; by iFrame.
Qed.
    
    
Lemma spec_is_full f0 n (v : Z) (s : seq.seq i32) E: 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ (f_locs f0) !! 0 = Some (value_of_int v) ⌝ ∗ 
        ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - length s * 4 )%Z ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s n }}}
    to_e_list is_full @ E
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s n ∗
                           ⌜ k = 1 \/ (length s < two14 - 1)%Z ⌝ ∗
          ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1⌝ }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hv & Hf & Hstack) HΦ" => /=.
  unfold is_full.
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int 0 ; value_of_int 1 ;
                                      value_of_int v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  - rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply wp_get_local => //.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate4.
    iApply wp_seq.
    instantiate ( 1 := λ x, ((((⌜ x = immV [value_of_int 0 ; value_of_int 1 ;
                                            value_of_int (v + 4 + length s * 4)%Z] ⌝
                                          ∗ [∗ list] i↦w ∈ s,
                                N.of_nat n ↦[i32][ Z.to_N (v + 4 + length s * 4 - 4 - 4 * i)] w) ∗

                                                                                                 (∃ bs, ⌜ (Z.of_nat (length bs) = two16 - 4 - length s * 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N (v + 4 + length s * 4)] bs)
                              )
                                           ∗  N.of_nat n↦[wms][(Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m v) + N.zero)%N]bits (value_of_int (v + 4 + length s * 4)) )
                               ∗ ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[[[[%Habs _] _] _] _]".
    iDestruct "Hstack" as "(%Hdiv & %Hlen & Hv & Hs & Hrest)".
    iSplitR "HΦ".
  - rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [[[[%Habs _] _] _] _]".
    iApply wp_load => //.
    iSplitL "Hs Hrest".
    iFrame.
    done.
    iFrame.
    rewrite N.add_0_r.
    iSimpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    iDestruct (i32_wms with "Hv") as "Hv" => //.
  - iIntros (w) "[[[[->  Hs] Hrest] Hp] Hf]".
    iAssert (isStack v s n)%I with "[Hrest Hp Hs]" as "Hstack".
    unfold isStack.
    iFrame.
    rewrite N.add_0_r.
    simpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    repeat iSplit => //.
    iApply i32_wms => //.
  - unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate5.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [value_of_int 0 ; value_of_int 1 ;
                                        value_of_int ((v + 4 + length s * 4) `mod` 65536)%Z
                                    ]⌝ ∗ ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
    rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_binop with "Hf") => //.
    iPureIntro => //=.
    unfold Wasm_int.Int32.modu.
    rewrite Wasm_int.Int32.unsigned_repr.
    rewrite Wasm_int.Int32.unsigned_repr.
    done.
    unfold Wasm_int.Int32.max_unsigned.
    unfold Wasm_int.Int32.modulus.
    unfold Wasm_int.Int32.wordsize.
    unfold Integers.Wordsize_32.wordsize.
    replace (two_power_nat 32) with 4294967296%Z ; last done.
    lia.
    split ; try lia.
    destruct Hv.
    apply (Z.add_le_mono v (Wasm_int.Int32.max_unsigned - 4 - length s * 4) (4 + length s * 4) (4 + length s * 4)) in H0.
    replace (Wasm_int.Int32.max_unsigned - 4 - length s * 4)%Z with (Wasm_int.Int32.max_unsigned - (4 + length s * 4))%Z in H0 ; last lia.
    rewrite Z.sub_add in H0.
    rewrite Z.add_assoc in H0.
    exact H0.
    lia.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    destruct ((v + 4 + length s * 4) `mod` 65536)%Z eqn:Hmod.
  - iApply wp_wand_r.
    iSplitL "Hf".
    iApply (wp_select_false with "Hf") => //.
    rewrite Hmod.
    done.
    instantiate (1 := λ x, ⌜ x = immV [value_of_int 1] ⌝%I).
    done.
    iIntros (w) "[-> Hf]".
    iApply "HΦ".
    iExists _.
    iSplitR => //=.
    iFrame.
    iSplitR.
    iLeft.
    done.
    iExists _ ; by iFrame.
  - iApply wp_wand_r.
    iSplitL "Hf".
    iApply (wp_select_true with "Hf") => //.
    unfold Wasm_int.int_of_Z => //=.
    unfold Wasm_int.Int32.zero.
    intro Habs.
    apply Wasm_int.Int32.repr_inv in Habs => //=.
    rewrite Hmod in Habs. done.
    rewrite Hmod.
    unfold Wasm_int.Int32.modulus.
    unfold Wasm_int.Int32.wordsize.
    unfold Integers.Wordsize_32.wordsize.
    replace (two_power_nat 32) with 4294967296%Z ; last done.
    split ; try lia.
    assert (( v + 4 + length s * 4) `mod` 65536 < 65536)%Z ; last lia.
    apply Z.mod_bound_pos ; lia.
    instantiate (1 := λ x, ⌜ x = immV [value_of_int 0] ⌝%I).
    done.
    iIntros (w) "[-> Hf]".
    iApply "HΦ".
    iExists _.
    iSplitR => //=.
    iFrame.
    iSplitR.
    iRight.
    iPureIntro.
    edestruct (Z.lt_total) as [ H | [ H | H]] => //=.     
    rewrite H in Hmod.
    replace (v + 4 + (two14 - 1) * 4 )%Z with (v + 1 * 65536)%Z in Hmod ;
      last by unfold two14 ; lia.
    rewrite Z.mod_add in Hmod.
    replace (v `mod` 65536)%Z with 0%Z in Hmod.
    done.
    unfold Z.divide in Hdiv.
    destruct Hdiv as [z ->].
    rewrite Z.mod_mul.
    done.
    unfold two16 ; lia.
    lia.
    remember (length s) as x in *.
    rewrite - Heqx in H.
    clear - Hlen H.
    lia.
    iExists _ ; by iFrame.
  - assert ( 0 <= v + 4 + length s * 4 )%Z ; first lia.
    assert (0 <65536)%Z ; first lia.
    apply (Z.mod_bound_pos _ _ H) in H0 as [Habs _].
    rewrite Hmod in Habs.
    lia.
Qed.    



Lemma spec_pop f0 n v (a : i32) s E:
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
         ∗ ⌜ f0.(f_locs) !! 0 = Some (value_of_int v) ⌝
         ∗ ⌜ length f0.(f_locs) >= 2 ⌝
         ∗ ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - S (length s) * 4 )%Z ⌝
         ∗ isStack v (a :: s) n
         ∗ ↪[frame] f0 }}}
    to_e_list pop @ E
    {{{ w, ⌜ w = immV [VAL_int32 a] ⌝ ∗
                      isStack v s n ∗
                      ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝ }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hlocs & %Hv & Hstack & Hf) HΦ" => /=.
  unfold pop.
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  - iApply (wp_get_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate2.
    iApply wp_seq.
    iSplitR ; last first.
    iDestruct "Hstack" as "(%Hdiv & %Hlen & Hv & Hs & Hrest)".
    iSplitR "HΦ".
  - iApply wp_load ; last first.
    iSplitL "Hs Hrest" ; last first.
    iFrame.
    iDestruct (i32_wms with "Hv") as "Hv" => //=.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    instantiate (1 := VAL_int32 _) => /=.
    rewrite N.add_0_r.
    done.
    iNext.
   
    by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ( [∗ list] i↦w ∈ (a :: s)%SEQ, N.of_nat n
                                      ↦[i32][ Z.to_N
                                                (v + 4 + length (a :: s) * 4 - 4 - 4 * i)] w) ∗ ( ∃ bs : seq.seq byte, ⌜Z.of_nat (length bs) = (two16 - 4 - length (a :: s) * 4)%Z⌝ ∗
              N.of_nat n↦[wms][Z.to_N (v + 4 + length (a :: s) * 4)]bs))%I) ; iFrame.
    done.
    done.
  - iIntros (w) "[[(-> & Hs & Hrest) Hp] Hf]". 
    iAssert (isStack v (a :: s) n)%I with "[Hrest Hp Hs]" as "Hstack".
    unfold isStack.
    iFrame.
    rewrite N.add_0_r.
    simpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    repeat iSplit => //=.
    iApply i32_wms => //.
  - unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate3.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [value_of_int (v + S (length s) * 4)] ⌝ ∗
                                       ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - iApply (wp_binop with "Hf") => //=.
    iPureIntro.
    unfold Wasm_int.Int32.isub, Wasm_int.Int32.sub.
    rewrite Wasm_int.Int32.unsigned_repr.
    rewrite Wasm_int.Int32.unsigned_repr.
    unfold value_of_int.
    unfold Wasm_int.int_of_Z => //=.
    remember (length s) as x.
    rewrite - Heqx.
    clear Heqx Hlen s.
    replace (v + 4 + S x * 4 - 4)%Z with (v + S x * 4)%Z ; first done.
    lia.
    unfold Wasm_int.Int32.max_unsigned.
    unfold Wasm_int.Int32.modulus.
    unfold Wasm_int.Int32.wordsize.
    unfold Integers.Wordsize_32.wordsize.
    replace (two_power_nat 32) with 4294967296%Z ; last done.
    lia.
    remember (length s) as x.
    rewrite - Heqx.
    clear Heqx Hlen s.
    lia.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate2.
    iApply (wp_seq _ _ _ (λ x, (⌜ x = immV [value_of_int (v + S (length s) * 4)] ⌝
                                           ∗ ↪[frame] _)%I)).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - iApply (wp_tee_local with "Hf").
    iIntros "!> Hf".
    rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_set_local with "[]Hf") => //.
  - iIntros (w) "[-> Hf]".
    remember {| f_locs := set_nth (value_of_int (v + S (length s) * 4)) (f_locs f0) 1
                                  (value_of_int (v + S (length s) * 4)) ;
               f_inst := f_inst f0 |} as f1.
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate2.
    iApply wp_seq.
    iDestruct "Hstack" as "(_ & _ & Hp & Hs & Hrest)".
    iSplitR ; last first.
    iSplitR "HΦ".
  - iApply wp_load ; last first.
    iFrame.
    rewrite separate1.
    iDestruct (big_sepL_app with "Hs") as "[Ha Hs]".
    iSplitR "Ha" ; last first.
    instantiate (1 := VAL_int32 _) => /=.
    iApply i32_wms.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq Z.mod_small.
    rewrite N.add_0_r Z.mul_0_r Z.sub_0_r.
    iDestruct "Ha" as "[Ha _]".
    remember (length s) as x.
    rewrite - Heqx.
    clear Heqx Hlen s.
    replace (v + 4 + S x * 4 - 4)%Z with (v + S x * 4)%Z.
    done.
    lia.
    unfold Wasm_int.Int32.max_unsigned in Hv. 
    remember (length s) as x.
    rewrite - Heqx.
    clear Heqx Hlen s.
    lia.
    by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ N.of_nat n
                                          ↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v + 4 + length ([a] ++ s)%list * 4) ∗
                                          ( ∃ bs : seq.seq byte,
                                              ⌜Z.of_nat (length bs) = (two16 - 4 - length ([a] ++ s)%list * 4)%Z⌝ ∗
                                                                                                              N.of_nat n↦[wms][Z.to_N (v + 4 + length ([a] ++ s)%list * 4)]bs) ∗
                                          ([∗ list] k↦y ∈ s, N.of_nat n
                           ↦[i32][ Z.to_N
                                     (v + 4 + length ([a] ++ s)%list * 4 - 4 -
                                        4 * (length [a] + k)%nat)] y))%I) ; iFrame.
    done.
    done.
  - iIntros (w) "[[(-> & Hp & Hrest & Hs) Ha] Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate2.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [VAL_int32 a ; value_of_int v] ⌝ ∗ ↪[frame] f1)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    subst.
    iApply (wp_get_local with "[] [$Hf]") => //=.
    unfold set_nth.
    destruct (f_locs f0) => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate3.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [VAL_int32 a ; value_of_int v ;
                                        value_of_int (v + S (length s) * 4)] ⌝ ∗
                                       ↪[frame] f1)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "[] [$Hf]") => //=.
    subst f1 => //=.
    by rewrite set_nth_read.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    iApply wp_wand_r.
    iSplitL "Hp Hf".
  - rewrite (separate1 (AI_basic _)).
    iApply wp_val_app => //.
    instantiate (1 := λ x, ((⌜ x = immV [VAL_int32 a] ⌝ ∗
                                       N.of_nat n↦[wms][Wasm_int.N_of_uint i32m
                                                                           (Wasm_int.int_of_Z i32m v) + N.zero]bits (value_of_int (v + S (length s) * 4))) ∗
                                                                                                                                                           ↪[frame] f1)%I).
    iSplit ; first by iIntros "!> [[%Habs _] _]".
    iApply wp_store => //.
    instantiate (1 := bits (value_of_int (v + 4 + length (a :: s) * 4))) => //=.
    subst f1 => //=.
    iSimpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    rewrite N.add_0_r.
    iFrame.
    iSplitR => //=.
    iDestruct (i32_wms with "Hp") as "Hp" => //.
  - iIntros (w) "[[-> Hp] Hf]".
    iApply "HΦ".
    iSplitR => //.
    unfold isStack.
    simpl in Hlen.
    iSplitR "Hf".
    repeat iSplit => //.
    iPureIntro.
    remember (length s) as x. rewrite - Heqx in Hlen ; clear Heqx s ; lia.
    iFrame.
    iSplitL "Hp".
  - simpl. rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    rewrite N.add_0_r.
    iApply i32_wms => //.
    unfold value_of_int => /=.
    remember (length s) as x. rewrite - Heqx ; clear Heqx Hlen s.
    replace (v + S (x) * 4)%Z with (v + 4 + x * 4)%Z ; last lia.
    done.
  - iDestruct "Hrest" as (bs) "[%Hbs Hrest]".
    iSplitL "Hs".
    iApply (big_sepL_impl with "Hs").
    iIntros "!>" (k y) "% H".
    simpl.
    remember (length s) as x ; rewrite - Heqx ; clear Heqx Hbs H Hlen s.
    replace ( v + 4 + S x * 4 - 4 - 4 * S k)%Z with
      (v + 4 + x * 4 - 4 - 4 * k)%Z.
    done.
    lia.
    iExists (serialise_i32 a ++ bs).
    iFrame.
    iSplitR.
    iPureIntro.
    rewrite app_length.
    simpl in Hbs.
    rewrite - (Nat2Z.id (length bs)).
    rewrite Hbs.
    remember (serialise_i32 a) as l.
    repeat (destruct l ; first done).
    destruct l ; last done.
    simpl.
    lia.
    unfold mem_block_at_pos.
    rewrite big_sepL_app.
    iSplitL "Ha".
    iApply (big_sepL_impl with "Ha").
    iIntros "!>" (k x) "%Hbits H".
    rewrite of_nat_to_nat_plus.
    rewrite N.add_0_r.
    rewrite of_nat_to_nat_plus.
    unfold Wasm_int.N_of_uint => //=.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; remember (length s) as y ; rewrite - Heqy ; clear Heqy Hbs Hlen s ; lia.
    remember (length s) as y ; rewrite - Heqy ; clear Heqy Hbs Hlen s.
    replace (v + S (y) * 4)%Z with (v + 4 + y * 4)%Z ; last lia.
    done.
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (k x) "%Hbits H".
    repeat rewrite of_nat_to_nat_plus.
    remember (serialise_i32 a) as l.
    repeat (destruct l => //).
    simpl.
    remember (length s) as y ; rewrite - Heqy ; clear Heqy Hbs Hlen s.
    replace (Z.to_N (v + 4 + S y * 4) + N.of_nat k)%N
      with (Z.to_N (v + 4 + y * 4) + N.of_nat (4+k))%N ; first done.
    simpl.
    lia.
    iExists _ ; by subst ; iFrame.
    all : try by iIntros "[[[% _] _] _]".
Qed.    
    
    

    
                                                                         
                                                                        
    
Lemma spec_push f0 n v (a : i32) s E :
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
         ∗ ⌜ f0.(f_locs) !! 0 = Some (VAL_int32 a) ⌝ 
         ∗ ⌜ f0.(f_locs) !! 1 = Some (value_of_int v) ⌝
         ∗ ⌜ length f0.(f_locs) >= 3 ⌝
         ∗ ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - S (length s) * 4 )%Z ⌝
         ∗ ⌜ (length s < two14 - 1)%Z ⌝
         ∗ isStack v s n
         ∗ ↪[frame] f0 }}}
    to_e_list push @ E
    {{{ w, ⌜ w = immV [] ⌝ ∗
           isStack v (a :: s) n ∗
           ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝ }}}. 
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hloca & %Hlocv & %Hlocs & %Hv & %Hlens & Hstack & Hf) HΦ" => /=.
  unfold push.
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  - iApply (wp_get_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate2.
    iApply wp_seq.
    instantiate ( 1 := λ x, ((((⌜ x = immV [ value_of_int (v + 4 + length (s) * 4)%Z] ⌝
                                           ∗ [∗ list] i↦w ∈  s,
                                 N.of_nat n ↦[i32][ Z.to_N (v + 4 + length (s) * 4 - 4 - 4 * i)] w) ∗

                                                                                                    (∃ bs, ⌜ Z.of_nat (length bs) = (two16 - 4 - length s * 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N (v + 4 + length s * 4)]bs)
                                                                                            )
                                ∗  N.of_nat n↦[wms][(Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m v) + N.zero)%N]bits (value_of_int (v + 4 + length (s) * 4)) )
                               ∗ ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[[[[%Habs _] _] _] _]".
    iDestruct "Hstack" as "(%Hdiv & %Hlen & Hv & Hs & Hrest)".
    iSplitR "HΦ".
  - iApply wp_load => //.
    iSplitL "Hs Hrest".
    iFrame.
    done.
    iFrame.
    rewrite N.add_0_r.
    iSimpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    iDestruct (i32_wms with "Hv") as "Hv" => //.
  - iIntros (w) "[[[[->  Hs] Hrest] Hp] Hf]".
    iAssert (isStack v (s) n)%I with "[Hrest Hp Hs]" as "Hstack".
    unfold isStack.
    iFrame.
    rewrite N.add_0_r.
    simpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    repeat iSplit => //=.
    iApply i32_wms => //.
  - unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate2.
    iApply (wp_seq _ _ _ (λ x, (⌜ x = immV [value_of_int (v + 4 + length s * 4)] ⌝
                                           ∗ ↪[frame] _)%I)).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - iApply (wp_tee_local with "Hf").
    iIntros "!> Hf".
    rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_set_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    remember {| f_locs := set_nth (value_of_int (v + 4 + length s * 4))
                                  (f_locs f0) 2 (value_of_int (v + 4 + length s * 4)) ;
               f_inst := f_inst f0 |} as f1.
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate2.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [value_of_int (v + 4 + length s * 4) ;
                                        VAL_int32 a] ⌝ ∗ ↪[frame] f1)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    subst f1 ; iApply (wp_get_local with "[] [$Hf]") => //.
    unfold set_nth.
    destruct (f_locs f0) => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate3.
    iApply wp_seq.
   instantiate
      (1 := λ x, (((⌜ x = immV [] ⌝ ∗ N.of_nat n↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v+4+length s * 4) ∗ ([∗ list] i↦w ∈ s, N.of_nat n↦[i32][Z.to_N (v + 4 + length s * 4 - 4 - 4 * i)] w) ∗ (∃ bs, ⌜ Z.of_nat (length bs) = (two16 - 4 - length (s) * 4 - 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N (v + 4 + S (length s) * 4)]bs) )
                     ∗ N.of_nat n ↦[wms][Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m (v + 4 + length s * 4)%Z) + N.zero]bits (VAL_int32 a)) ∗ ↪[frame] f1)%I).
    iSplitR ; first by iIntros "[[[ %Habs _ ] _] _]". 
    iDestruct "Hstack" as "(_ & _ & Hp & Hs & Hrest)".
    iDestruct "Hrest" as (bs) "[%Hbs Hrest]".
    unfold two16 in Hbs.
    unfold two14 in Hlens.
    remember (length s) as x.
    do 4 (destruct bs ; first by exfalso ; clear Heqx s ; simpl in Hbs ; lia).
    rewrite separate4.
    unfold mem_block_at_pos at 1.
    rewrite big_sepL_app.
    iDestruct "Hrest" as "[Ha Hrest]".
    iSplitR "HΦ".
  - iApply wp_wand_r. iSplitL. iApply wp_store ; last first.
    iFrame.
    iSplitR "Ha".
    iNext.
    simpl.
    subst x.
    by instantiate (1 := λ x, (⌜ x = immV [] ⌝ ∗ N.of_nat n ↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v + 4 + length s * 4) ∗ ([∗ list] i↦w ∈ s, N.of_nat n
                           ↦[i32][ Z.to_N (v + 4 + length s * 4 - 4 - 4 * i)] w) ∗ ([∗ list] k↦y ∈ bs, N.of_nat n↦[wm][N.of_nat
                                                 (N.to_nat
                                                    (Z.to_N (v + 4 + length s * 4)) +
                                                  S (S (S (S k))))]y))%I);
    iFrame.
    3: instantiate (1 := [b ; b0 ; b1 ; b2]) => //=. 
    3: done.
    2: subst f1 => //=.
    iApply (big_sepL_impl with "Ha").
    iIntros "!>" (k y) "% H".
    rewrite of_nat_to_nat_plus.
    simpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq Z.mod_small.
    rewrite of_nat_to_nat_plus.
    rewrite N.add_0_r.
    by subst x.
    unfold Wasm_int.Int32.max_unsigned in Hv.
    rewrite - Heqx.
    lia.
    iIntros (w) "[[(-> & Hp & Hs & Hrest) Ha] Hf]".
    iFrame.
    iSplitR "Ha".
    iSplit ; first done.
    subst x ; iFrame.
    iExists bs.
    iSplit ; first iPureIntro.
    simpl in Hbs.
    remember (length s) as x.
    rewrite - Heqx in Hbs.
    unfold two16. lia.
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (k x) "% H".
    do 2 rewrite of_nat_to_nat_plus.
    remember (length s) as y.
    clear Heqy s.
    replace (Z.to_N (v + 4 + y * 4) + N.of_nat (S (S (S (S k)))))%N with
      (Z.to_N (v + 4 + S y * 4) + N.of_nat k)%N.
    done.
    lia.
    by subst x.
  - iIntros (w) "[[(-> & Hp & Hs & Hrest) Ha] Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite (separate1 (AI_basic _)).
    iApply wp_seq.
    instantiate (1 := λ x, ( ⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame]f1)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - iApply (wp_get_local with "[] [$Hf]") => //.
    subst f1 => //=.
    unfold set_nth.
    destruct (f_locs f0) => //=.
    destruct l => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate2.
    iApply wp_seq.
    instantiate (1 := λ x, ( ⌜ x = immV [value_of_int v ;
                                         value_of_int ( v + 4 + length s * 4 ) ] ⌝
                                        ∗ ↪[frame] f1)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "[] [$Hf]") => //.
    subst f1 => //=.
    rewrite set_nth_read => //=.
    by subst x.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate4.
    iApply wp_seq.
    instantiate (1 := λ x, ( ⌜ x = immV [value_of_int v ;
                                         value_of_int ( v + 4 + S (length s) * 4 )] ⌝
                                        ∗ ↪[frame] f1)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_binop with "Hf") => //=.
    iPureIntro.
    unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
    rewrite Wasm_int.Int32.unsigned_repr.
    rewrite Wasm_int.Int32.unsigned_repr.
    unfold value_of_int => //=.
    rewrite - Heqx.
    replace (v + 4 + x * 4 + 4)%Z with (v + 4 + S x * 4)%Z => //=.
    lia.
    unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
    unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
    replace (two_power_nat 32) with two32 ; last done.
    unfold two32 ; lia.
    rewrite - Heqx. lia.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    iApply wp_wand_r.
    iSplitL "Hf Hp".
  - iApply wp_store.
    done.
    instantiate (1 := bits (value_of_int (v + 4 + length s * 4))) => //=.
    instantiate (2 := f1).
    subst f1 => //=.
    instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
    iFrame.
    iSplit => //=.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    iDestruct (i32_wms with "Hp") as "Hp" => //.
    rewrite N.add_0_r.
    by subst x.
  - iIntros (w) "[[-> Hp] Hf]".
    iApply "HΦ".
    iSplit => //=.
    unfold isStack.
    iSplitR "Hf".
    repeat iSplit => //=.
    iPureIntro ; rewrite - Heqx ; clear Heqx s ; unfold two14 ; lia.
    iSplitL "Hp".
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    iApply i32_wms => //.
    rewrite N.add_0_r.
    unfold value_of_int => //=.
    iSplitR "Hrest".
    iSplitL "Ha".
    iApply i32_wms => //.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    rewrite N.add_0_r.
    rewrite - Heqx.
    replace (v + 4 + S x * 4 - 4 - 4 * 0%nat)%Z
      with (v + 4 + x * 4)%Z ; last lia.
    done.
    iApply (big_sepL_impl with "Hs").
    iIntros "!>" (k y) "%Hbits H".
    rewrite - Heqx.
    replace (v + 4 + S x * 4 - 4 - 4 * S k)%Z
      with  (v + 4 + x * 4 - 4 - 4 * k)%Z ; last lia.
    done.
    iDestruct "Hrest" as (bs0) "[%Hbs0 Hrest]".
    iExists bs0.
    iSplit => //=.
    iPureIntro.
    rewrite - Heqx.
    lia.
    by subst x.
    iExists _ ; by subst ; iFrame.
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
  generalize dependent n.
  induction s ; intros => //=.
  lia.
  destruct n => //=.
  simpl in H.
  apply IHs in H.
  lia.
Qed.

Lemma in_take {A} n s (x : A) :
  In x (take n s) -> In x s.
Proof.
  generalize dependent s.
  induction n ; intro s => //=.
  destruct s => //=.
  intros [H | H] ; first (by left) ; apply IHn in H ; by right.
Qed.
  
  


Lemma spec_stack_map (f0 : frame) (n : immediate) (f : i32) (v : Z) (s : seq.seq i32) E
      j0 a cl 
      (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) :
  ⊢ {{{  ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝  ∗
            ⌜ f0.(f_locs) !! 0 = Some (VAL_int32 f) ⌝  ∗
            ⌜ f0.(f_locs) !! 1 = Some (value_of_int v) ⌝ ∗
            ⌜ length f0.(f_locs) >= 4 ⌝ ∗
            ⌜ (0 <= v)%Z ⌝ ∗                                   
            ⌜ (v + 4 + length s * 4 ≤ Wasm_int.Int32.max_unsigned)%Z ⌝ ∗
            isStack v s n ∗
            stackAll s Φ ∗
            ⌜ f0.(f_inst).(inst_types) !! 1 = Some (Tf [T_i32] [T_i32]) ⌝ ∗

            ⌜ f0.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
            (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
            (N.of_nat a) ↦[wf] cl ∗
            ⌜ match cl with FC_func_native _ t _ _ => t | FC_func_host t _ => t end
         = Tf [T_i32] [T_i32] ⌝ ∗ 
            (∀ (u : i32) (fc : frame),
                {{{ Φ u ∗
                      ⌜ f_inst f0 = f_inst fc ⌝ ∗
                       ↪[frame] fc ∗
                       (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
                       (N.of_nat a) ↦[wf] cl
                  }}}
                  [ AI_basic (BI_const (VAL_int32 u)) ;
                    AI_invoke a ] @ E
                  {{{ w, (∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)
                           ∗ ↪[frame] fc
                           ∗ (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) 
                           ∗ (N.of_nat a) ↦[wf] cl }}}) ∗   
            ↪[frame] f0 }}}
    to_e_list stack_map @ E
    {{{ w, ⌜ w = immV [] ⌝ ∗
           (∃ s', isStack v s' n ∗ stackAll2 s s' Ψ) ∗
           (∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝) ∗
            (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
            (N.of_nat a) ↦[wf] cl
    }}}.
Proof.
  iIntros "!>" (Ξ) "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs & %Hvb & %Hv & Hs & HΦ & %Htypes & %Htab & Htab & Hcl & %Hclt & #Hspec & Hf) HΞ" => /=.
  unfold stack_map.
  rewrite (separate1 (AI_basic (BI_get_local 1))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply wp_get_local => //.
  instantiate (1 := λ x, ⌜x = immV [value_of_int v]⌝%I) => //.
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (i32const v))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf Hs".
  iApply wp_load => // ; last first.
  unfold isStack.
  iDestruct "Hs" as "(% & % & Hn & ?)".
  iDestruct (i32_wms with "Hn") as "Hn".
  rewrite N.add_0_r.
  simpl.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  unfold bits.
  instantiate (1 := VAL_int32 _) => /=.
  iFrame.
  iNext.
  instantiate ( 1 := λ x, (⌜ x = immV [value_of_int (v + 4 + length s * 4)] ⌝ ∗
                                     ⌜(two16 | v)%Z⌝ ∗
                                     ⌜(length s < two14)%Z⌝ ∗
                                     ([∗ list] i↦w ∈ s, N.of_nat n ↦[i32][ Z.to_N (v + 4 + length s * 4 - 4 - 4 * i)] w) ∗
      (∃ bs : seq.seq byte, ⌜Z.of_nat (length bs) = (two16 - 4 - length s * 4)%Z⌝ ∗
                                                                              N.of_nat n↦[wms][Z.to_N (v + 4 + length s * 4)]bs))%I).
  iFrame.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  done.
  iIntros (w) "[[[-> Hs] Hn] Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (i32const (v + _ + _)))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply wp_set_local => //.
  by instantiate (1 := λ x, ⌜x = immV []⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate1 (AI_basic (BI_get_local 1))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]") => //=.
  unfold set_nth.
  destruct (f_locs f0) ; first by inversion Hlocs0.
  destruct l ; first by inversion Hlocs1.
  simpl in Hlocs1.
  inversion Hlocs1 ; subst.
  done.
  by instantiate (1 := λ x, ⌜x = immV [value_of_int v]⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite separate3.
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_binop with "Hf") => //.
  by instantiate (1 := λ x, ⌜ x = immV [_] ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 _ (AI_basic (BI_set_local 2))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply wp_set_local => //=.
  simpl.
  rewrite length_is_size size_set_nth.
  rewrite length_is_size in Hlocs.
  unfold ssrnat.maxn.
  destruct (ssrnat.leq _ _) ; lia.
  by instantiate (1 := λ x, ⌜x = immV []⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
  iApply (wp_block with "Hf") => //.
  iIntros "!> Hf".
  iSimpl.
  iApply wp_wasm_empty_ctx.
  rewrite - (cat0s [AI_basic (BI_loop _ _)]) - (cats0 [AI_basic (BI_loop _ _)]).
  iApply wp_label_push ; first done.
  rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).
  iApply (wp_loop_ctx with "Hf") => //.
  iIntros "!> Hf".
  simpl.
  rewrite - (cat0s (AI_basic (BI_get_local 2) :: _)).
  rewrite - (cats0 [AI_basic _;_;_;_;_;_;_;_;_;_;_;_;_;_;_]). 
  iApply wp_label_push ; first done.
  unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
  rewrite Wasm_int.Int32.unsigned_repr ; last lia.
  rewrite Wasm_int.Int32.unsigned_repr ; last by unfold Wasm_int.Int32.max_unsigned,
      Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
  iAssert (∀ (j :nat) s', ⌜ j <= length s ⌝ -∗ ⌜ length s' = length s - j ⌝ -∗ ↪[frame] {|
                    f_locs :=
                      set_nth (VAL_int32 (Wasm_int.Int32.repr (v + 4 )))
                        (set_nth
                           (VAL_int32 (Wasm_int.Int32.repr (v + 4 + length s * 4)))
                           (f_locs f0) 3
                           (VAL_int32 (Wasm_int.Int32.repr (v + 4 + length s * 4)))) 2
                        (VAL_int32 (Wasm_int.Int32.repr (v + 4 + (length s - j%Z) * 4)));
                    f_inst := f_inst f0
                    |} -∗
                    isStack v (take j s ++ s') n -∗ 
                    stackAll (take j s) Φ -∗
                    stackAll2 (drop j s) s' Ψ -∗
                    N.of_nat j0 ↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]Some a -∗
                    N.of_nat a↦[wf] cl -∗
                    (∀ w : val,
                        ⌜w = immV []⌝ ∗ (∃ s' : seq.seq i32, isStack v s' n ∗ stackAll2 s s' Ψ) ∗
                                  (∃ f1 : frame,  ↪[frame]f1 ∗ ⌜f_inst f0 = f_inst f1⌝) ∗
              N.of_nat j0↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]
              Some a ∗ N.of_nat a↦[wf]cl -∗ 
                                  Ξ w) -∗
                    WP [AI_basic (BI_get_local 2); AI_basic (BI_get_local 3);
     AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_U))); AI_basic (BI_br_if 1);
     AI_basic (BI_get_local 2); AI_basic (BI_get_local 2); AI_basic (BI_get_local 2);
     AI_basic (BI_load T_i32 None N.zero N.zero); AI_basic (BI_get_local 0);
     AI_basic (BI_call_indirect 1); AI_basic (BI_store T_i32 None N.zero N.zero);
     AI_basic (i32const 4); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_set_local 2); AI_basic (BI_br 0)] @  E
  CTX
  2;
  push_base (LH_rec [] 0 [] (LH_base [] []) []) 0
    [AI_basic
       (BI_loop (Tf [] [])
          [BI_get_local 2; BI_get_local 3; BI_relop T_i32 (Relop_i (ROI_ge SX_U));
          BI_br_if 1; BI_get_local 2; BI_get_local 2; BI_get_local 2;
          BI_load T_i32 None N.zero N.zero; BI_get_local 0; 
          BI_call_indirect 1; BI_store T_i32 None N.zero N.zero; 
          i32const 4; BI_binop T_i32 (Binop_i BOI_add); BI_set_local 2; 
          BI_br 0])] [] []
    {{ v0, Ξ v0 }})%I as "H".
  { iIntros (j).
    iInduction j as [|j] "IHj".
  { iIntros (s') "%Hj %Hs' Hf Hs HΦ HΨ Htab Hcl HΞ".
    rewrite (separate1 (AI_basic (BI_get_local 2))).
    iApply wp_seq_ctx.
    iSplitR ; last first.
    iSplitL "Hf".
    iApply (wp_get_local with "[] [$Hf]").
    simpl. by rewrite set_nth_read.
    by instantiate ( 1 := λ x, ⌜x = immV _⌝%I).
    iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite (separate2 _ (AI_basic (BI_get_local 3))).
    iApply wp_seq_ctx.
    iSplitR ; last first.
    iSplitL "Hf".
    rewrite (separate1 _ [AI_basic (BI_get_local 3)]).
    iApply wp_val_app => //.
    iSplitR ; last first.
    iApply wp_wand_r.
    iSplitL.
    iApply (wp_get_local with "[] [$Hf]").
    simpl.
    destruct (f_locs f0) ; first by inversion Hlocs.
    destruct l ; first by inversion Hlocs1.
    destruct l ; first by simpl in Hlocs ; lia.
    simpl.
    by rewrite set_nth_read.
    by instantiate (1 := λ x, ⌜x = immV _⌝%I).
    iIntros (w) "[-> Hf]".
    rewrite Z.sub_0_r.
    iSimpl.
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
    iFrame.
    done.
    by iIntros "!> [% _]".
    iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite (separate3 _ _ (AI_basic (BI_relop _ _))).
    iApply wp_seq_ctx.
    iSplitR ; last first.
    iSplitL "Hf".
    iApply (wp_relop with "Hf").
    simpl.
    unfold Wasm_int.Int32.ltu.
    rewrite Wasm_int.Int32.unsigned_repr.
    rewrite Coqlib.zlt_false.
    simpl.
    done.
    lia.
    split ; try lia.
    exact Hv.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite - (app_nil_l (AI_basic (i32const 1) :: _)).
    rewrite (separate2 _ (AI_basic (BI_br_if 1))).
    iApply wp_base_push ; first done.
    iApply (wp_br_if_true_ctx with "Hf").
    done.
    iIntros "!> Hf".
    rewrite - (app_nil_l [AI_basic (BI_br 1)]).
    iApply (wp_br_ctx with "Hf") => //.
    iIntros "!> Hf".
    iApply wp_value.
    unfold IntoVal.
    by apply of_to_val.
    iApply "HΞ".
    iSplit ; first done.
    iFrame. iSplitR "Hf".
    iExists s'.
    unfold take.
    unfold drop.
    iFrame.
    iExists _.
    iFrame.
    done.
    all : try by iIntros "[% _]". }
  iIntros (s') "%Hj %Hs' Hf Hs HΦ HΨ Htab Hcl HΞ".
  destruct s as [|v0 s]; first by inversion Hj.
  cut (exists ys y, v0 :: take j s = ys ++ [y]) ;
  [ intro Htail ; destruct Htail as (ys & y & Htail) |
    exists (removelast (v0 :: take j s)) ;
    exists (List.last (v0 :: take j s) (Wasm_int.Int32.repr 1)) ;
    apply app_removelast_last ;
    apply not_eq_sym ; apply nil_cons ].
  simpl in Hv.
  simpl in Hj.
  assert (j `min` length s = j) as Hjmin.
  { remember (length s) as x. rewrite - Heqx in Hj.
    lia. } 
  rewrite (separate1 (AI_basic (BI_get_local 2))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]").
  simpl. by rewrite set_nth_read.
  by instantiate ( 1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 _ (AI_basic (BI_get_local 3))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate1 _ [AI_basic (BI_get_local 3)]).
  iApply wp_val_app => //.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]").
  simpl.
  destruct (f_locs f0) ; first by inversion Hlocs.
  destruct l ; first by inversion Hlocs1.
  destruct l ; first by simpl in Hlocs ; lia.
  simpl.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
  iFrame.
  done.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate3 _ _ (AI_basic (BI_relop _ _))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_relop with "Hf").
  simpl.
  unfold Wasm_int.Int32.ltu.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Coqlib.zlt_true.
  simpl.
  done.
  lia.
  lia.
  lia.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (BI_const (VAL_int32 _)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_br_if_false with "Hf").
  done.
  iNext.
  by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate1 (AI_basic (BI_get_local 2)) [_;_;_;_;_;_;_;_;_;_]).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate1 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app. done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate3 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf Hs".
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
 
  iApply wp_wand_r.
  iSplitL.

  iApply wp_load ; last first.
  iFrame.
  unfold isStack.
  iDestruct "Hs" as "(Hdiv & Hlen & Hn & Hl & Hbs)".
  rewrite cat_app.
  iDestruct (big_sepL_app with "Hl") as "[Hs Hs']".
  rewrite app_length.
  rewrite Hs'.
  rewrite take_length.
  replace (S j `min` length (v0 :: s)) with (S j) ; last by simpl ; lia.
  unfold take ; fold (take (A := value)).
  rewrite Htail.
  iDestruct (big_sepL_app with "Hs") as "[Hs H]".
  iDestruct "H" as "[H _]".
  iDestruct (i32_wms with "H") as "H" => //.
  rewrite Nat.add_0_r.
  rewrite N.add_0_r.
  replace (Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr (v + 4 + (S (length s) - S j) * 4)))
    with (Z.to_N (v + 4 + (S (length s) - S j) * 4)).
  replace (S j + (length (v0 :: s) - S j)) with (length (v0 :: s)) ; last by simpl ; lia.
  replace (v + 4 + length (v0 :: s) * 4 - 4 - 4 * length ys)%Z
    with (v + 4 + length (v0 :: s) * 4 - S (length ys) * 4)%Z ; last lia.
  replace (S (length ys)) with (length (ys ++ [y])) ;
    last by rewrite app_length ; simpl ; lia.
  rewrite (cat_app ys [y]).
  rewrite - Htail.
  simpl.
  rewrite firstn_length.
  rewrite Hjmin.
  rewrite (Z.mul_sub_distr_r (S (length s)) (S j) 4).
  simpl in Hj.
  remember (length s) as x.
  rewrite - Heqx.
  replace (v + 4 + S x * 4 - S j * 4)%Z
    with (v + 4 + (S x * 4 - S j * 4))%Z ;
    last lia.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq Z.mod_small.
  instantiate (1 := VAL_int32 _).
  iSplitR "H" ; last iExact "H".
  iNext.
  subst x.
  instantiate ( 1 := λ x, (⌜ x = immV [VAL_int32 y] ⌝ ∗ ⌜ (two16 | v)%Z ⌝ ∗ ⌜ (S (length s) < two14)%Z ⌝ ∗ N.of_nat n ↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v + 4 + S (length s) * 4) ∗  (∃ bs : seq.seq byte, ⌜ Z.of_nat (length bs) = (two16 - 4 - S (length s) * 4)%Z⌝ ∗
            N.of_nat n↦[wms][Z.to_N (v + 4 + S (length s) * 4)]bs) ∗ ([∗ list] k↦y0 ∈ s', N.of_nat n
                              ↦[i32][ Z.to_N
                                        (v + 4 + S (length s) * 4 - 4 - 4 * S (j + k))] y0) ∗ [∗ list] k↦y0 ∈ ys, N.of_nat n
                             ↦[i32][ Z.to_N (v + 4 + S (length s) * 4 - 4 - 4 * k)] y0)%I).
  iFrame.
  done.
  simpl.
  unfold Wasm_int.Int32.max_unsigned in Hv ; rewrite - Heqx in Hv ; lia.
  simpl.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  done.
  done.
  iIntros (w) "[[[-> H1] H2] Hf]".
  iSimpl.
  instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗
                                     ( ⌜(two16 | v)%Z⌝ ∗ ⌜(S (length s) < two14)%Z⌝ ∗ N.of_nat n ↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v + 4 + S (length s) * 4) ∗
         (∃ bs : seq.seq byte, ⌜Z.of_nat (length bs) = (two16 - 4 - S (length s) * 4)%Z⌝ ∗
            N.of_nat n↦[wms][Z.to_N (v + 4 + S (length s) * 4)]bs) ∗
         ([∗ list] k↦y0 ∈ s', N.of_nat n
                              ↦[i32][ Z.to_N
                                        (v + 4 + S (length s) * 4 - 4 - 4 * S (j + k))] y0) ∗
         ([∗ list] k↦y0 ∈ ys, N.of_nat n
                                       ↦[i32][ Z.to_N (v + 4 + S (length s) * 4 - 4 - 4 * k)] y0))
                                     ∗ N.of_nat n↦[wms][Wasm_int.N_of_uint i32m
                            (Wasm_int.Int32.repr (v + 4 + (length (v0 :: s) - S j) * 4)) +
                                                          N.zero]bits (VAL_int32 y)
                                     ∗ ↪[frame] {|
                    f_locs :=
                      set_nth
                        (VAL_int32
                           (Wasm_int.Int32.repr (v + 4)))
                        (set_nth
                           (VAL_int32
                              (Wasm_int.Int32.repr (v + 4 + length (v0 :: s) * 4)))
                           (f_locs f0) 3
                           (VAL_int32
                              (Wasm_int.Int32.repr (v + 4 + length (v0 :: s) * 4)))) 2
                        (VAL_int32
                           (Wasm_int.Int32.repr (v + 4 + (length (v0 :: s) - S j) * 4)));
                    f_inst := f_inst f0
                                     |})%I).
  iFrame.
  done.
  by iIntros "!> [% _]".
  iIntros (w) "(-> & (Hdiv & Hlen & Hv & Hbs & Hs' & Hs) & H & Hf)".
  iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate3 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]") => /=.
  destruct (f_locs f0) ; inversion Hlocs0.
  simpl. done.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate5 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "HΦ Hf Htab Hcl".
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r ; iSplitL.
  unfold take ; fold (take (A := value)).
  rewrite Htail.
  iDestruct (stackAll_app with "HΦ") as "(HΦ & Hy & _)".
  rewrite (separate1 _ [_;AI_basic (BI_call_indirect 1)]).
  rewrite - (app_nil_r [_ ; AI_basic (BI_call_indirect 1)]).
  iApply wp_wasm_empty_ctx.
  iApply wp_base_push ; first done.
  iApply (wp_call_indirect_success_ctx with "Htab Hcl Hf").
  simpl.
  unfold cl_type.
  rewrite Hclt.
  done.
  simpl.
  done.
  iIntros "!> (Htab & Hcl & Hf)".
  iApply wp_base_pull.
  iApply wp_wasm_empty_ctx.
  simpl.
  iApply ("Hspec" with "[Hy Hf Htab Hcl]").
  iFrame.
  iPureIntro => //=.
  iIntros (w) "(H & Hf & ?)".
  iDestruct "H" as (v1) "[-> Hv1]".
  instantiate (1 := λ x, ((∃ v1, ⌜ x = immV _ ⌝ ∗ stackAll ys Φ ∗ Ψ y v1 ∗
                         N.of_nat j0↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]
                         Some a ∗
                         N.of_nat a↦[wf]cl)∗ ↪[frame] _)%I) ;
    iFrame.
  iExists  _; by iFrame.
  iIntros (w) "[H Hf]".
  iDestruct "H" as (v1) "[-> H]".
  iSimpl.
  instantiate (1 := λ x, (∃ v1, ⌜ x = immV _ ⌝ ∗ stackAll ys Φ ∗ Ψ y v1 ∗
                                           N.of_nat j0↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]
                                            Some a ∗ N.of_nat a↦[wf]cl
                                           ∗ ↪[frame] _)%I).
  iExists _ ; by iFrame.
  iIntros "!> H".
  by iDestruct "H" as (v1) "[% _]".
  iIntros (w) "Hf".
  iDestruct "Hf" as (v1) "(-> & HΦ & Hv1 & Htab & Hcl & Hf)".
  iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf H".
  rewrite (separate1 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply wp_store ; last first.
  simpl.
  iFrame.
  iNext.
  by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  done.
  done.
  done.
  iIntros (w) "[[-> H] Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ N.of_nat n↦[wms][ _ ] _ ∗ ↪[frame] _)%I) ;
  iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "(-> & H & Hf)".
  iSimpl.
  rewrite (separate3 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_binop with "Hf").
  done.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (BI_const (VAL_int32 (Wasm_int.Int32.iadd _ _))))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_set_local with "[] [$Hf]") => /=.
  destruct (f_locs f0) ; first done.
  destruct l ; first done.
  destruct l ; first by simpl in Hlocs ; lia.
  destruct l ; first by simpl in Hlocs ; lia.
  simpl.
  lia.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  simpl.
  rewrite set_nth_write.
  all : try by iIntros "[% _]".
  all : try by iIntros "Habs" ; iDestruct "Habs" as (?) "[% _]".
  rewrite - (app_nil_l [AI_basic (BI_br 0)]).
  iApply (wp_br_ctx_nested with "Hf").
  lia.
  done.
  instantiate (1 := LH_rec [] 0 [] (LH_base [] []) []) => //=.
  done.
  done.
  iIntros "!> Hf".
  iSimpl.
  rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).
  iApply (wp_loop_ctx with "Hf") => //.
  iIntros "!> Hf".
  simpl.
  rewrite - (cat0s (AI_basic (BI_get_local 2) :: _)).
  rewrite - (cats0 [AI_basic _;_;_;_;_;_;_;_;_;_;_;_;_;_;_]). 
  iApply wp_label_push ; first done.
  iApply ("IHj" with "[] [] [Hf] [Hv Hbs Hs' Hs H Hlen Hdiv] [HΦ] [HΨ Hv1] Htab Hcl").
  iPureIntro.
  lia.
  instantiate (1 := v1 :: s').
  iPureIntro.
  simpl.
  rewrite Hs' => //=.
  lia.
  unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Wasm_int.Int32.unsigned_repr.
  remember (length s) as x. rewrite - Heqx.
  replace (v + 4 + (S x - S j) * 4 + 4)%Z
    with (v + 4 + (S x - j) * 4)%Z.
  iExact "Hf".
  lia.
  lia.
  lia.
  unfold isStack.
  iFrame.
  iDestruct "Hlen" as "%".
  iSplit ; first iPureIntro.
  rewrite app_length.
  rewrite firstn_length.
  replace (j `min` length (v0 :: s)) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  lia.
  iSplitL "Hv".
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x. rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S (x)) ; last lia.
  iExact "Hv".
  iSplitR "Hbs".
  iApply big_sepL_app.
  iSplitL "Hs".
  replace j with (j `min` S j) ; last lia.
  rewrite - take_take.
  simpl.
  rewrite Htail.
  replace j with (length ys).
  rewrite take_app.
  iApply (big_sepL_impl with "Hs").
  iIntros "!>" (k x) "% H".
  remember (length s) as z ; rewrite - Heqz.
  replace (S z) with (length (ys ++ v1 :: s')) ; first done.
  rewrite app_length.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqz.
  remember (length ys) as zz ; rewrite - Heqzz.
  replace zz with j ; first lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  subst z. rewrite Hjmin in Hl. rewrite - Heqzz in Hl. lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite Hjmin in Hl.
  remember (length ys) as zz.
  rewrite - Heqzz in Hl.
  lia.
  iSplitL "H".
  iApply i32_wms.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  rewrite N.add_0_r.
  rewrite Nat.add_0_r.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S (x)) ; last lia.
  replace (v + 4 + S x *4 - 4 -4 * j)%Z
    with  (v + 4 + ( S x - S j) * 4)%Z ; last lia.
  iExact "H".
  unfold Wasm_int.Int32.max_unsigned in Hv.
  lia.
  iApply (big_sepL_impl with "Hs'").
  iIntros "!>" (k x) "% H".
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as z ; rewrite - Heqz.
  replace (j `min` S z) with j ; last by simpl ; lia.  
  rewrite Hs'.
  simpl.
  rewrite - Heqz.
  replace (j + S (z - j)) with (S z) ; last lia.
  replace (S ( j + k)) with (j + S k) ; last lia.
  iExact "H".
  iDestruct "Hbs" as (bs) "[% H]".
  iExists bs.
  iSplit ; first iPureIntro.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  lia.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S x) ; last lia.
  iExact "H".
  replace j with (j `min` S j) ; last lia.
  rewrite - take_take.
  simpl.
  rewrite Htail.
  replace j with (length ys).
  rewrite take_app.
  done.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite Hjmin in Hl.
  remember (length ys) as zz ; rewrite - Heqzz in Hl ;
    lia.
  rewrite - (take_drop j s).
  rewrite app_comm_cons.
  rewrite Htail.
  rewrite take_drop.
  rewrite drop_app_le.
  replace j with (length ys).
  rewrite drop_app.
  simpl.
  iFrame.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
   rewrite Hjmin in Hl.
  remember (length ys) as zz ; rewrite - Heqzz in Hl ;
    lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite app_length.
  rewrite - Hl.
  lia.
  iExact "HΞ". }
  iApply ("H" with "[] [] [Hf] [Hn Hs] [HΦ] [] Htab Hcl").
  instantiate (1 := length s).
  iPureIntro ; lia.
  instantiate (1 := []).
  iPureIntro ; simpl ; lia.
  rewrite Z.sub_diag.
  rewrite Z.mul_0_l.
  rewrite Z.add_0_r.
  done.
  iDestruct "Hs" as "(% & % & Hs & Hbs)".
  iSplit ; first done.
  iSplit ; first iPureIntro.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  exact H0.
  iSplitL "Hn".
  iApply i32_wms.
  rewrite N.add_0_r.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  iSplitL "Hs".
  rewrite cats0 firstn_length.
  rewrite firstn_all.
  rewrite Nat.min_id.
  done.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  done.
  rewrite firstn_all.
  done.
  rewrite drop_all.
  done.
  done.
  all : try by iIntros "[% _]".
  by iIntros "[[[% _] _] _]".
Qed.

   
Lemma spec_stack_map_trap `{!logrel_na_invs Σ}(f0 : frame) (n : immediate) (f : i32) (v : Z) (s : seq.seq i32) E
      j0 a cl 
      (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) :
  ⊢ {{{  ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝  ∗
            ⌜ f0.(f_locs) !! 0 = Some (VAL_int32 f) ⌝  ∗
            ⌜ f0.(f_locs) !! 1 = Some (value_of_int v) ⌝ ∗
            ⌜ length f0.(f_locs) >= 4 ⌝ ∗
            ⌜ (0 <= v)%Z ⌝ ∗                                   
            ⌜ (v + 4 + length s * 4 ≤ Wasm_int.Int32.max_unsigned)%Z ⌝ ∗
            isStack v s n ∗
            stackAll s Φ ∗
            ⌜ f0.(f_inst).(inst_types) !! 1 = Some (Tf [T_i32] [T_i32]) ⌝ ∗

            ⌜ f0.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
            (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
             (N.of_nat a) ↦[wf] cl ∗ 
             ⌜ match cl with FC_func_native _ t _ _ => t | FC_func_host t _ => t end 
          = Tf [T_i32] [T_i32] ⌝ ∗  
            (∀ (u : i32) (fc : frame),
                {{{ Φ u ∗
                      ⌜ f_inst f0 = f_inst fc ⌝ ∗
                       ↪[frame] fc ∗
                       (* (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗ *)
                       (* (N.of_nat a) ↦[wf] cl *)
                       na_own logrel_nais ⊤
                  }}}
                  [ AI_basic (BI_const (VAL_int32 u)) ;
                    AI_invoke a ] @ E
                  {{{ w, (⌜ w = trapV ⌝ ∨ ((∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)
                                             (* ∗ (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a)  *)
                                             (* ∗ (N.of_nat a) ↦[wf] cl *)))
                           ∗ na_own logrel_nais ⊤ ∗ ↪[frame] fc}}}) ∗
            na_own logrel_nais ⊤ ∗ ↪[frame] f0 }}}
    to_e_list stack_map @ E
    {{{ w, (⌜ w = trapV ⌝ ∨ (⌜ w = immV [] ⌝ ∗
                                        (∃ s', isStack v s' n ∗ stackAll2 s s' Ψ)))
             ∗ (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a)
             ∗ (N.of_nat a) ↦[wf] cl 
             ∗ (∃ f1, ↪[frame] f1 ∗ na_own logrel_nais ⊤ ∗ ⌜ f_inst f0 = f_inst f1 ⌝ )
    }}}.
Proof.
  iIntros "!>" (Ξ) "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs & %Hvb & %Hv & Hs & HΦ & %Htypes & %Htab & Htab & Hcl & %Hcl & #Hspec & Hinv & Hf) HΞ" => /=.
  iApply wp_wand_r.
  iSplitR "HΞ" ; last first.
  iIntros (w) "H".
  iApply "HΞ".
  iExact "H".
  iApply wp_wasm_empty_ctx.
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq_can_trap_ctx.
  iSplitR; last first.
  iFrame "Hf".
  iSplitR; last first.
  (* Be very careful -- cherry-pick the resources required to mix into Φf. *)
  iSplitR "Hs HΦ".
  iIntros "Hf".
  iApply wp_wand_r. iSplitL "Hf". iApply wp_get_local => //.
  instantiate (1 := λ x, ⌜x = immV [value_of_int v]⌝%I) => //.
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExists f0 ; iFrame.
  iCombine "Htab Hcl Hinv" as "H".
  instantiate (1 := fun x => (⌜ x = f0 ⌝%I ∗ N.of_nat j0 ↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))] Some a ∗ N.of_nat a ↦[wf] cl ∗ na_own logrel_nais ⊤)%I).
  by iFrame.
  2:{ (* This is impossible to prove !!!! *)
    iIntros (f1) "(Hf1 & HΦf)".
    iDestruct "HΦf" as "(-> & Htab & Hcl & Hinv)".
    iSplitL ""; first by iLeft.
    iFrame.
    iExists f0.
    by iSplit. }
  (* We now have the required resources from Φf. *)
  iIntros (w f2) "(-> & Hf & HΦf)".

  (* Rest to be done, but the resources are here *)
  iSimpl.
  rewrite (separate2 (AI_basic _)).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first. 
  iFrame "Hf".
  iSplitR ; last first.
  iSplitL "Hs".
  iIntros "Hf". iApply wp_wand_r. iSplitL. iApply wp_load => // ; last first.
  unfold isStack.
  iDestruct "Hs" as "(% & % & Hn & ?)".
  iDestruct (i32_wms with "Hn") as "Hn".
  rewrite N.add_0_r.
  simpl.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  unfold bits.
  instantiate (1 := VAL_int32 _) => /=.
  iFrame.
  iNext.
  instantiate ( 1 := λ x, (⌜ x = immV [value_of_int (v + 4 + length s * 4)] ⌝ ∗
                                     ⌜(two16 | v)%Z⌝ ∗
                                     ⌜(length s < two14)%Z⌝ ∗
                                     ([∗ list] i↦w ∈ s, N.of_nat n ↦[i32][ Z.to_N (v + 4 + length s * 4 - 4 - 4 * i)] w) ∗
      (∃ bs : seq.seq byte, ⌜Z.of_nat (length bs) = (two16 - 4 - length s * 4)%Z⌝ ∗
                                                                              N.of_nat n↦[wms][Z.to_N (v + 4 + length s * 4)]bs))%I).
  iFrame.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  done.
  iIntros (w) "[[[-> Hs] Hn] Hf]".
  iSplitR "Hf". iRight. instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _ ∗ _)%I).
  iSplitR ; first done. iSplitL "Hs". iExact "Hs". iExact "Hn".
  iExists _ ; iFrame. by instantiate (1 := λ x, ⌜ x = f0 ⌝%I).
  iIntros (w f1) "((-> & H & Hn) & Hf & ->)".
  iSimpl. rewrite (separate2 (AI_basic _)).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitR.
  iIntros "Hf".
  iApply wp_wand_r ; iSplitL. iApply wp_set_local => //.
  by instantiate (1 := λ x, ⌜x = immV []⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  iExists _ ; iFrame. by instantiate (1 := λ x, ⌜ x = {| f_locs := _ ; f_inst := f_inst f0 |} ⌝%I).
  iIntros (w f1) "(-> & Hf & ->)". iSimpl.
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitR. 
  iIntros "Hf". iApply wp_wand_r. iSplitL. iApply (wp_get_local with "[] [$Hf]") => //=.
  unfold set_nth.
  destruct (f_locs f0) ; first by inversion Hlocs0.
  destruct l ; first by inversion Hlocs1.
  simpl in Hlocs1.
  inversion Hlocs1 ; subst.
  done.
  by instantiate (1 := λ x, ⌜x = immV [value_of_int v]⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExists _ ; iFrame. by instantiate (1 := λ x, ⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝%I).
  iIntros (w f1) "(-> & Hf & ->)". iSimpl.
  rewrite (separate3 (AI_basic _)).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf".
  iSplitR ; last first.
  iSplitR.
  iIntros "Hf". iApply wp_wand_r ; iSplitL.
  iApply (wp_binop with "Hf") => //.
  by instantiate (1 := λ x, ⌜ x = immV [_] ⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExists _ ; iFrame. by instantiate (1 := λ x, ⌜ x = {| f_locs := _ ; f_inst := _ |}⌝%I).
  iIntros (w f1) "(-> & Hf & ->)". iSimpl.
  rewrite (separate2 (AI_basic _)).
  iApply wp_seq_can_trap_ctx. 
  iSplitR ; last first.
  iFrame "Hf".
  iSplitR ; last first.
  iSplitR.
  iIntros "Hf". iApply wp_wand_r ; iSplitL.
  iApply wp_set_local => //=.
  simpl.
  rewrite length_is_size size_set_nth.
  rewrite length_is_size in Hlocs.
  unfold ssrnat.maxn.
  destruct (ssrnat.leq _ _) ; lia.
  by instantiate (1 := λ x, ⌜x = immV []⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  iExists _ ; iFrame. by instantiate (1 := λ x, ⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝%I).
  iIntros (w f1) "(-> & Hf & ->)". simpl.
  rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
  iApply (wp_block_ctx with "Hf") => //.
  iIntros "!> Hf".
  iSimpl.
  rewrite - (cat0s [AI_basic (BI_loop _ _)]) - (cats0 [AI_basic (BI_loop _ _)]).
  iApply wp_label_push ; first done.
  rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).
  iApply (wp_loop_ctx with "Hf") => //.
  iIntros "!> Hf".
  simpl.
  rewrite - (cat0s (AI_basic (BI_get_local 2) :: _)).
  rewrite - (cats0 [AI_basic _;_;_;_;_;_;_;_;_;_;_;_;_;_;_]). 
  iApply wp_label_push ; first done.
  unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
  rewrite Wasm_int.Int32.unsigned_repr ; last lia.
  rewrite Wasm_int.Int32.unsigned_repr ; last by unfold Wasm_int.Int32.max_unsigned,
      Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
  iAssert (∀ (j :nat) s', ⌜ j <= length s ⌝ -∗ ⌜ length s' = length s - j ⌝ -∗ ↪[frame] {|
                    f_locs :=
                      set_nth (VAL_int32 (Wasm_int.Int32.repr (v + 4 )))
                        (set_nth
                           (VAL_int32 (Wasm_int.Int32.repr (v + 4 + length s * 4)))
                           (f_locs f0) 3
                           (VAL_int32 (Wasm_int.Int32.repr (v + 4 + length s * 4)))) 2
                        (VAL_int32 (Wasm_int.Int32.repr (v + 4 + (length s - j%Z) * 4)));
                    f_inst := f_inst f0
                    |} -∗
                    isStack v (take j s ++ s') n -∗ 
                    stackAll (take j s) Φ -∗
                    stackAll2 (drop j s) s' Ψ -∗
                    na_own logrel_nais ⊤ -∗
                    N.of_nat a ↦[wf] cl -∗
                    N.of_nat j0 ↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]Some a -∗
                   (∀ w : iris.val,
           (⌜w = trapV⌝ ∨ ⌜w = immV []⌝ ∗
            (∃ s' : seq.seq Wasm_int.Int32.T, isStack v s' n ∗ stackAll2 s s' Ψ)) ∗
           N.of_nat j0↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]
           Some a ∗ N.of_nat a ↦[wf] cl ∗
           (∃ f1 : frame,  ↪[frame]f1 ∗ na_own logrel_nais ⊤ ∗ ⌜f_inst f0 = f_inst f1⌝) -∗
           Ξ w) -∗
                    WP [AI_basic (BI_get_local 2); AI_basic (BI_get_local 3);
     AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_U))); AI_basic (BI_br_if 1);
     AI_basic (BI_get_local 2); AI_basic (BI_get_local 2); AI_basic (BI_get_local 2);
     AI_basic (BI_load T_i32 None N.zero N.zero); AI_basic (BI_get_local 0);
     AI_basic (BI_call_indirect 1); AI_basic (BI_store T_i32 None N.zero N.zero);
     AI_basic (i32const 4); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_set_local 2); AI_basic (BI_br 0)] @  E
  CTX
  2;
  push_base (LH_rec [] 0 [] (LH_base [] []) []) 0
    [AI_basic
       (BI_loop (Tf [] [])
          [BI_get_local 2; BI_get_local 3; BI_relop T_i32 (Relop_i (ROI_ge SX_U));
          BI_br_if 1; BI_get_local 2; BI_get_local 2; BI_get_local 2;
          BI_load T_i32 None N.zero N.zero; BI_get_local 0; 
          BI_call_indirect 1; BI_store T_i32 None N.zero N.zero; 
          i32const 4; BI_binop T_i32 (Binop_i BOI_add); BI_set_local 2; 
          BI_br 0])] [] []
    {{ v0, Ξ v0 }})%I as "Hloop".
  { iIntros (j).
    iInduction j as [|j] "IHj".
    { iIntros (s') "%Hj %Hs' Hf Hs HΦ HΨ Hown Hcl Htab HΞ".
      rewrite (separate1 (AI_basic (BI_get_local 2))).
      iApply wp_seq_can_trap_ctx. 
      iSplitR ; last first.
      iFrame "Hf".
      iSplitR ; last first.
      iSplitR.
      iIntros "Hf".
      iApply wp_wand_r ; iSplitL.
      iApply (wp_get_local with "[] [$Hf]").
      simpl. by rewrite set_nth_read.
      by instantiate ( 1 := λ x, ⌜x = immV _⌝%I).
      iIntros (w) "[-> Hf]".
      iSplitR. iRight.
      by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      iExists _ ; iFrame. by instantiate (1 := λ x, ⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝%I).
      iIntros (w f1) "(-> & Hf & ->)". iSimpl.
      rewrite (separate2 _ (AI_basic (BI_get_local 3))).
      iApply wp_seq_can_trap_ctx.
      iSplitR ; last first.
      iFrame "Hf".
      iSplitR ; last first.
      iSplitR.
      iIntros "Hf". rewrite (separate1 _ [AI_basic (BI_get_local 3)]).
      iApply wp_val_can_trap => //.
      iSplitR ; last first.
      iFrame "Hf". iIntros "Hf".
      iApply wp_wand_r.
      iSplitL.
      iApply (wp_get_local with "[] [$Hf]").
      simpl.
      destruct (f_locs f0) ; first by inversion Hlocs.
      destruct l ; first by inversion Hlocs1.
      destruct l ; first by simpl in Hlocs ; lia.
      simpl.
      by rewrite set_nth_read.
      by instantiate (1 := λ x, ⌜x = immV _⌝%I).
      iIntros (w) "[-> Hf]".
      iSplitR. iRight.
      by instantiate (1 := λ x, ⌜ x = immV _⌝%I).
      iExists _ ; iFrame. by instantiate (1 := λ x, ⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝%I).
      by iIntros "%".
      iIntros (w f1) "(-> & Hf & ->)". rewrite Z.sub_0_r.
      iSimpl.
(*      instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
    iFrame.
    done.
    by iIntros "!> [% _]".
    iIntros (w) "[-> Hf]".
    iSimpl. *)
      rewrite (separate3 _ _ (AI_basic (BI_relop _ _))).
      iApply wp_seq_can_trap_ctx.
      iSplitR ; last first.
      iFrame "Hf". iSplitR ; last first.
      iSplitR.
      iIntros "Hf".
      iApply wp_wand_r ; iSplitL.
      iApply (wp_relop with "Hf").
      simpl.
      unfold Wasm_int.Int32.ltu.
      rewrite Wasm_int.Int32.unsigned_repr.
      rewrite Coqlib.zlt_false.
      simpl.
      done.
      lia.
      split ; try lia.
      exact Hv.
      by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      iIntros (w) "[-> Hf]".
      iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      iExists _ ; iFrame. by instantiate (1 := λ x, ⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝%I).
      iIntros (w f1) "(-> & Hf & ->)". iSimpl.
      rewrite - (app_nil_l (AI_basic (i32const 1) :: _)).
      rewrite (separate2 _ (AI_basic (BI_br_if 1))).
      iApply wp_base_push ; first done.
      iApply (wp_br_if_true_ctx with "Hf").
      done.
      iIntros "!> Hf".
      rewrite - (app_nil_l [AI_basic (BI_br 1)]).
      iApply (wp_br_ctx with "Hf") => //.
      iIntros "!> Hf".
      iApply wp_value.
      unfold IntoVal.
      by apply of_to_val.
      iApply "HΞ".
      iFrame. iSplitR "Hf". iRight. iSplit ; first done.
      iExists s'.
      unfold take.
      unfold drop.
      iFrame.
      iExists _.
      iFrame.
      done.
      iIntros (f1) "[Hf ->]".
      iApply "HΞ".
      all : try by iIntros "%".
      all : try by iIntros (f1) }
  iIntros (s') "%Hj %Hs' Hf Hs HΦ HΨ Hown Hcl Htab HΞ".
  destruct s as [|v0 s]; first by inversion Hj.
  cut (exists ys y, v0 :: take j s = ys ++ [y]) ;
  [ intro Htail ; destruct Htail as (ys & y & Htail) |
    exists (removelast (v0 :: take j s)) ;
    exists (List.last (v0 :: take j s) (Wasm_int.Int32.repr 1)) ;
    apply app_removelast_last ;
    apply not_eq_sym ; apply nil_cons ].
  simpl in Hv.
  simpl in Hj.
  assert (j `min` length s = j) as Hjmin.
  { remember (length s) as x. rewrite - Heqx in Hj.
    lia. } 
  rewrite (separate1 (AI_basic (BI_get_local 2))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]").
  simpl. by rewrite set_nth_read.
  by instantiate ( 1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 _ (AI_basic (BI_get_local 3))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate1 _ [AI_basic (BI_get_local 3)]).
  iApply wp_val_app => //.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]").
  simpl.
  destruct (f_locs f0) ; first by inversion Hlocs.
  destruct l ; first by inversion Hlocs1.
  destruct l ; first by simpl in Hlocs ; lia.
  simpl.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
  iFrame.
  done.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate3 _ _ (AI_basic (BI_relop _ _))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_relop with "Hf").
  simpl.
  unfold Wasm_int.Int32.ltu.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Coqlib.zlt_true.
  simpl.
  done.
  lia.
  lia.
  lia.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (BI_const (VAL_int32 _)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_br_if_false with "Hf").
  done.
  iNext.
  by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate1 (AI_basic (BI_get_local 2)) [_;_;_;_;_;_;_;_;_;_]).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate1 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app. done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate3 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf Hs".
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
 
  iApply wp_wand_r.
  iSplitL.

  iApply wp_load ; last first.
  iFrame.
  unfold isStack.
  iDestruct "Hs" as "(Hdiv & Hlen & Hn & Hl & Hbs)".
  rewrite cat_app.
  iDestruct (big_sepL_app with "Hl") as "[Hs Hs']".
  rewrite app_length.
  rewrite Hs'.
  rewrite take_length.
  replace (S j `min` length (v0 :: s)) with (S j) ; last by simpl ; lia.
  unfold take ; fold (take (A := value)).
  rewrite Htail.
  iDestruct (big_sepL_app with "Hs") as "[Hs H]".
  iDestruct "H" as "[H _]".
  iDestruct (i32_wms with "H") as "H" => //.
  rewrite Nat.add_0_r.
  rewrite N.add_0_r.
  replace (Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr (v + 4 + (S (length s) - S j) * 4)))
    with (Z.to_N (v + 4 + (S (length s) - S j) * 4)).
  replace (S j + (length (v0 :: s) - S j)) with (length (v0 :: s)) ; last by simpl ; lia.
  replace (v + 4 + length (v0 :: s) * 4 - 4 - 4 * length ys)%Z
    with (v + 4 + length (v0 :: s) * 4 - S (length ys) * 4)%Z ; last lia.
  replace (S (length ys)) with (length (ys ++ [y])) ;
    last by rewrite app_length ; simpl ; lia.
  rewrite (cat_app ys [y]).
  rewrite - Htail.
  simpl.
  rewrite firstn_length.
  rewrite Hjmin.
  rewrite (Z.mul_sub_distr_r (S (length s)) (S j) 4).
  simpl in Hj.
  remember (length s) as x.
  rewrite - Heqx.
  replace (v + 4 + S x * 4 - S j * 4)%Z
    with (v + 4 + (S x * 4 - S j * 4))%Z ;
    last lia.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq Z.mod_small.
  instantiate (1 := VAL_int32 _).
  iSplitR "H" ; last iExact "H".
  iNext.
  subst x.
  instantiate ( 1 := λ x, (⌜ x = immV [VAL_int32 y] ⌝ ∗ ⌜ (two16 | v)%Z ⌝ ∗ ⌜ (S (length s) < two14)%Z ⌝ ∗ N.of_nat n ↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v + 4 + S (length s) * 4) ∗  (∃ bs : seq.seq byte, ⌜ Z.of_nat (length bs) = (two16 - 4 - S (length s) * 4)%Z⌝ ∗
            N.of_nat n↦[wms][Z.to_N (v + 4 + S (length s) * 4)]bs) ∗ ([∗ list] k↦y0 ∈ s', N.of_nat n
                              ↦[i32][ Z.to_N
                                        (v + 4 + S (length s) * 4 - 4 - 4 * S (j + k))] y0) ∗ [∗ list] k↦y0 ∈ ys, N.of_nat n
                             ↦[i32][ Z.to_N (v + 4 + S (length s) * 4 - 4 - 4 * k)] y0)%I).
  iFrame.
  done.
  simpl.
  unfold Wasm_int.Int32.max_unsigned in Hv ; rewrite - Heqx in Hv ; lia.
  simpl.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  done.
  done.
  iIntros (w) "[[[-> H1] H2] Hf]".
  iSimpl.
  instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗
                                     ( ⌜(two16 | v)%Z⌝ ∗ ⌜(S (length s) < two14)%Z⌝ ∗ N.of_nat n ↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v + 4 + S (length s) * 4) ∗
         (∃ bs : seq.seq byte, ⌜Z.of_nat (length bs) = (two16 - 4 - S (length s) * 4)%Z⌝ ∗
            N.of_nat n↦[wms][Z.to_N (v + 4 + S (length s) * 4)]bs) ∗
         ([∗ list] k↦y0 ∈ s', N.of_nat n
                              ↦[i32][ Z.to_N
                                        (v + 4 + S (length s) * 4 - 4 - 4 * S (j + k))] y0) ∗
         ([∗ list] k↦y0 ∈ ys, N.of_nat n
                                       ↦[i32][ Z.to_N (v + 4 + S (length s) * 4 - 4 - 4 * k)] y0))
                                     ∗ N.of_nat n↦[wms][Wasm_int.N_of_uint i32m
                            (Wasm_int.Int32.repr (v + 4 + (length (v0 :: s) - S j) * 4)) +
                                                          N.zero]bits (VAL_int32 y)
                                     ∗ ↪[frame] {|
                    f_locs :=
                      set_nth
                        (VAL_int32
                           (Wasm_int.Int32.repr (v + 4)))
                        (set_nth
                           (VAL_int32
                              (Wasm_int.Int32.repr (v + 4 + length (v0 :: s) * 4)))
                           (f_locs f0) 3
                           (VAL_int32
                              (Wasm_int.Int32.repr (v + 4 + length (v0 :: s) * 4)))) 2
                        (VAL_int32
                           (Wasm_int.Int32.repr (v + 4 + (length (v0 :: s) - S j) * 4)));
                    f_inst := f_inst f0
                                     |})%I).
  iFrame.
  done.
  by iIntros "!> [% _]".
  iIntros (w) "(-> & (Hdiv & Hlen & Hv & Hbs & Hs' & Hs) & H & Hf)".
  iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate3 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]") => /=.
  destruct (f_locs f0) ; inversion Hlocs0.
  simpl. done.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate5 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "HΦ Hf Htab Hcl Hown".
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r ; iSplitL.
  unfold take ; fold (take (A := value)).
  rewrite Htail.
  iDestruct (stackAll_app with "HΦ") as "(HΦ & Hy & _)".
  rewrite (separate1 _ [_;AI_basic (BI_call_indirect 1)]).
  rewrite - (app_nil_r [_ ; AI_basic (BI_call_indirect 1)]).
  iApply wp_wasm_empty_ctx.
  iApply wp_base_push ; first done.
  iApply (wp_call_indirect_success_ctx with "Htab Hcl Hf").
  simpl.
  unfold cl_type.
  rewrite Hcl.
  done.
  simpl.
  done.
  iIntros "!> (Htab & Hcl & Hf)".
  iApply wp_base_pull.
  iApply wp_wasm_empty_ctx.
  simpl.
  iApply ("Hspec" with "[Hy Hf Hown]").
  iFrame.
  iPureIntro => //=.
  iIntros (w) "H".
  iCombine "HΦ H" as "H".
  iExact "H".
  (*iDestruct "H" as (v1) "[-> Hv1]".
  instantiate (1 := λ x, ((∃ v1, ⌜ x = immV _ ⌝ ∗ stackAll ys Φ ∗ Ψ y v1 ∗
                         N.of_nat j0↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]
                         Some a ∗
                         N.of_nat a↦[wf]cl)∗ ↪[frame] _)%I) ;
    iFrame. 
  iExists  _; by iFrame. *)
  iIntros (w) "(HΦ & H & Hown & Hf)".
  iDestruct "H" as "[-> | H]".
  iSimpl.
  instantiate (1 := λ x, (⌜ x = trapV ⌝ ∨ (∃ v1, ⌜ x = immV _ ⌝ ∗ stackAll ys Φ ∗ Ψ y v1 ∗
                                          na_own logrel_nais ⊤
                                           ∗ ↪[frame] _))%I).
  by iLeft.
  iDestruct "H" as (v1) "[-> H]".
  iSimpl.
  iRight. iExists _ ; by iFrame.
  iIntros "!> H".
  by iDestruct "H" as (v1) "[% _]".
  iIntros (w) "Hf".
  iDestruct "Hf" as (v1) "(-> & HΦ & Hv1 & Htab & Hcl & Hf)".
  iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf H".
  rewrite (separate1 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply wp_store ; last first.
  simpl.
  iFrame.
  iNext.
  by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  done.
  done.
  done.
  iIntros (w) "[[-> H] Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ N.of_nat n↦[wms][ _ ] _ ∗ ↪[frame] _)%I) ;
  iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "(-> & H & Hf)".
  iSimpl.
  rewrite (separate3 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_binop with "Hf").
  done.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (BI_const (VAL_int32 (Wasm_int.Int32.iadd _ _))))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_set_local with "[] [$Hf]") => /=.
  destruct (f_locs f0) ; first done.
  destruct l ; first done.
  destruct l ; first by simpl in Hlocs ; lia.
  destruct l ; first by simpl in Hlocs ; lia.
  simpl.
  lia.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  simpl.
  rewrite set_nth_write.
  all : try by iIntros "[% _]".
  all : try by iIntros "Habs" ; iDestruct "Habs" as (?) "[% _]".
  rewrite - (app_nil_l [AI_basic (BI_br 0)]).
  iApply (wp_br_ctx_nested with "Hf").
  lia.
  done.
  instantiate (1 := LH_rec [] 0 [] (LH_base [] []) []) => //=.
  done.
  done.
  iIntros "!> Hf".
  iSimpl.
  rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).
  iApply (wp_loop_ctx with "Hf") => //.
  iIntros "!> Hf".
  simpl.
  rewrite - (cat0s (AI_basic (BI_get_local 2) :: _)).
  rewrite - (cats0 [AI_basic _;_;_;_;_;_;_;_;_;_;_;_;_;_;_]). 
  iApply wp_label_push ; first done.
  iApply ("IHj" with "[] [] [Hf] [Hv Hbs Hs' Hs H Hlen Hdiv] [HΦ] [HΨ Hv1] Htab Hcl").
  iPureIntro.
  lia.
  instantiate (1 := v1 :: s').
  iPureIntro.
  simpl.
  rewrite Hs' => //=.
  lia.
  unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Wasm_int.Int32.unsigned_repr.
  remember (length s) as x. rewrite - Heqx.
  replace (v + 4 + (S x - S j) * 4 + 4)%Z
    with (v + 4 + (S x - j) * 4)%Z.
  iExact "Hf".
  lia.
  lia.
  lia.
  unfold isStack.
  iFrame.
  iDestruct "Hlen" as "%".
  iSplit ; first iPureIntro.
  rewrite app_length.
  rewrite firstn_length.
  replace (j `min` length (v0 :: s)) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  lia.
  iSplitL "Hv".
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x. rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S (x)) ; last lia.
  iExact "Hv".
  iSplitR "Hbs".
  iApply big_sepL_app.
  iSplitL "Hs".
  replace j with (j `min` S j) ; last lia.
  rewrite - take_take.
  simpl.
  rewrite Htail.
  replace j with (length ys).
  rewrite take_app.
  iApply (big_sepL_impl with "Hs").
  iIntros "!>" (k x) "% H".
  remember (length s) as z ; rewrite - Heqz.
  replace (S z) with (length (ys ++ v1 :: s')) ; first done.
  rewrite app_length.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqz.
  remember (length ys) as zz ; rewrite - Heqzz.
  replace zz with j ; first lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  subst z. rewrite Hjmin in Hl. rewrite - Heqzz in Hl. lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite Hjmin in Hl.
  remember (length ys) as zz.
  rewrite - Heqzz in Hl.
  lia.
  iSplitL "H".
  iApply i32_wms.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  rewrite N.add_0_r.
  rewrite Nat.add_0_r.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S (x)) ; last lia.
  replace (v + 4 + S x *4 - 4 -4 * j)%Z
    with  (v + 4 + ( S x - S j) * 4)%Z ; last lia.
  iExact "H".
  unfold Wasm_int.Int32.max_unsigned in Hv.
  lia.
  iApply (big_sepL_impl with "Hs'").
  iIntros "!>" (k x) "% H".
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as z ; rewrite - Heqz.
  replace (j `min` S z) with j ; last by simpl ; lia.  
  rewrite Hs'.
  simpl.
  rewrite - Heqz.
  replace (j + S (z - j)) with (S z) ; last lia.
  replace (S ( j + k)) with (j + S k) ; last lia.
  iExact "H".
  iDestruct "Hbs" as (bs) "[% H]".
  iExists bs.
  iSplit ; first iPureIntro.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  lia.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S x) ; last lia.
  iExact "H".
  replace j with (j `min` S j) ; last lia.
  rewrite - take_take.
  simpl.
  rewrite Htail.
  replace j with (length ys).
  rewrite take_app.
  done.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite Hjmin in Hl.
  remember (length ys) as zz ; rewrite - Heqzz in Hl ;
    lia.
  rewrite - (take_drop j s).
  rewrite app_comm_cons.
  rewrite Htail.
  rewrite take_drop.
  rewrite drop_app_le.
  replace j with (length ys).
  rewrite drop_app.
  simpl.
  iFrame.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
   rewrite Hjmin in Hl.
  remember (length ys) as zz ; rewrite - Heqzz in Hl ;
    lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite app_length.
  rewrite - Hl.
  lia.
  iExact "HΞ". }
  iApply ("H" with "[] [] [Hf] [Hn Hs] [HΦ] [] Htab Hcl").
  instantiate (1 := length s).
  iPureIntro ; lia.
  instantiate (1 := []).
  iPureIntro ; simpl ; lia.
  rewrite Z.sub_diag.
  rewrite Z.mul_0_l.
  rewrite Z.add_0_r.
  done.
  iDestruct "Hs" as "(% & % & Hs & Hbs)".
  iSplit ; first done.
  iSplit ; first iPureIntro.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  exact H0.
  iSplitL "Hn".
  iApply i32_wms.
  rewrite N.add_0_r.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  iSplitL "Hs".
  rewrite cats0 firstn_length.
  rewrite firstn_all.
  rewrite Nat.min_id.
  done.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  done.
  rewrite firstn_all.
  done.
  rewrite drop_all.
  done.
  done.
  all : try by iIntros "[% _]".
  by iIntros "[[[% _] _] _]".
Qed. 

(*
  iIntros "!>" (Ξ) "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs & %Hvb & %Hv & Hs & HΦ & %Htypes & %Htab & Htab & #Hspec & Hinv & Hf) HΞ" => /=.
  rewrite (separate1 (AI_basic (BI_get_local 1))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply wp_get_local => //.
  instantiate (1 := λ x, ⌜ x = immV [value_of_int v] ⌝%I) => //.
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (i32const v))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf Hs".
  iApply wp_load => // ; last first.
  unfold isStack.
  iDestruct "Hs" as "(% & % & Hn & ?)".
  iDestruct (i32_wms with "Hn") as "Hn".
  rewrite N.add_0_r.
  simpl.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  unfold bits.
  instantiate (1 := VAL_int32 _) => /=.
  iFrame.
  iNext.
  instantiate ( 1 := λ x, (⌜ x = immV [value_of_int (v + 4 + length s * 4)] ⌝ ∗
                                     ⌜(two16 | v)%Z⌝ ∗
                                     ⌜(length s < two14)%Z⌝ ∗
                                     ([∗ list] i↦w ∈ s, N.of_nat n ↦[i32][ Z.to_N (v + 4 + length s * 4 - 4 - 4 * i)] w) ∗
      (∃ bs : seq.seq byte, ⌜Z.of_nat (length bs) = (two16 - 4 - length s * 4)%Z⌝ ∗
                                                                              N.of_nat n↦[wms][Z.to_N (v + 4 + length s * 4)]bs))%I).
  iFrame.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  done.
  iIntros (w) "[[[-> Hs] Hn] Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (i32const (v + _ + _)))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply wp_set_local => //.
  by instantiate (1 := λ x, x = immV []).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate1 (AI_basic (BI_get_local 1))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]") => //=.
  unfold set_nth.
  destruct (f_locs f0) ; first by inversion Hlocs0.
  destruct l ; first by inversion Hlocs1.
  simpl in Hlocs1.
  inversion Hlocs1 ; subst.
  done.
  by instantiate (1 := λ x, x = immV [value_of_int v]).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite separate3.
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_binop with "Hf") => //.
  by instantiate (1 := λ x, ⌜ x = immV [_] ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 _ (AI_basic (BI_set_local 2))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply wp_set_local => //=.
  simpl.
  rewrite length_is_size size_set_nth.
  rewrite length_is_size in Hlocs.
  unfold ssrnat.maxn.
  destruct (ssrnat.leq _ _) ; lia.
  by instantiate (1 := λ x, x = immV []).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
  iApply (wp_block with "Hf") => //.
  iIntros "!> Hf".
  iSimpl.
  iApply wp_wasm_empty_ctx.
  rewrite - (cat0s [AI_basic (BI_loop _ _)]) - (cats0 [AI_basic (BI_loop _ _)]).
  iApply wp_label_push ; first done.
  rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).
  iApply (wp_loop_ctx with "Hf") => //.
  iIntros "!> Hf".
  simpl.
  rewrite - (cat0s (AI_basic (BI_get_local 2) :: _)).
  rewrite - (cats0 [AI_basic _;_;_;_;_;_;_;_;_;_;_;_;_;_;_]). 
  iApply wp_label_push ; first done.
  unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
  rewrite Wasm_int.Int32.unsigned_repr ; last lia.
  rewrite Wasm_int.Int32.unsigned_repr ; last by unfold Wasm_int.Int32.max_unsigned,
      Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
  iAssert (∀ (j :nat) s', ⌜ j <= length s ⌝ -∗ ⌜ length s' = length s - j ⌝ -∗ ↪[frame] {|
                    f_locs :=
                      set_nth (VAL_int32 (Wasm_int.Int32.repr (v + 4 )))
                        (set_nth
                           (VAL_int32 (Wasm_int.Int32.repr (v + 4 + length s * 4)))
                           (f_locs f0) 3
                           (VAL_int32 (Wasm_int.Int32.repr (v + 4 + length s * 4)))) 2
                        (VAL_int32 (Wasm_int.Int32.repr (v + 4 + (length s - j%Z) * 4)));
                    f_inst := f_inst f0
                    |} -∗
                    isStack v (take j s ++ s') n -∗ 
                    stackAll (take j s) Φ -∗
                    stackAll2 (drop j s) s' Ψ -∗
                    N.of_nat j0 ↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]Some a -∗
                    N.of_nat a↦[wf] cl -∗
                    (∀ w : val,
                        ⌜w = immV []⌝ ∗ (∃ s' : seq.seq i32, isStack v s' n ∗ stackAll2 s s' Ψ) ∗
                                  (∃ f1 : frame,  ↪[frame]f1 ∗ ⌜f_inst f0 = f_inst f1⌝) -∗ 
                                  Ξ w) -∗
                    WP [AI_basic (BI_get_local 2); AI_basic (BI_get_local 3);
     AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_U))); AI_basic (BI_br_if 1);
     AI_basic (BI_get_local 2); AI_basic (BI_get_local 2); AI_basic (BI_get_local 2);
     AI_basic (BI_load T_i32 None N.zero N.zero); AI_basic (BI_get_local 0);
     AI_basic (BI_call_indirect 1); AI_basic (BI_store T_i32 None N.zero N.zero);
     AI_basic (i32const 4); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_set_local 2); AI_basic (BI_br 0)]
  CTX
  2;
  push_base (LH_rec [] 0 [] (LH_base [] []) []) 0
    [AI_basic
       (BI_loop (Tf [] [])
          [BI_get_local 2; BI_get_local 3; BI_relop T_i32 (Relop_i (ROI_ge SX_U));
          BI_br_if 1; BI_get_local 2; BI_get_local 2; BI_get_local 2;
          BI_load T_i32 None N.zero N.zero; BI_get_local 0; 
          BI_call_indirect 1; BI_store T_i32 None N.zero N.zero; 
          i32const 4; BI_binop T_i32 (Binop_i BOI_add); BI_set_local 2; 
          BI_br 0])] [] []
    {{ v0, Ξ v0 }})%I as "H".
  { iIntros (j).
  iInduction j as [|j] "IHj".
  { iIntros (s') "%Hj %Hs' Hf Hs HΦ HΨ Htab Hcl HΞ".
    rewrite (separate1 (AI_basic (BI_get_local 2))).
    iApply wp_seq_ctx.
    iSplitR ; last first.
    iSplitL "Hf".
    iApply (wp_get_local with "[] [$Hf]").
    simpl. by rewrite set_nth_read.
    by instantiate ( 1 := λ x, x = immV _).
    iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite (separate2 _ (AI_basic (BI_get_local 3))).
    iApply wp_seq_ctx.
    iSplitR ; last first.
    iSplitL "Hf".
    rewrite (separate1 _ [AI_basic (BI_get_local 3)]).
    iApply wp_val_app => //.
    iSplitR ; last first.
    iApply wp_wand_r.
    iSplitL.
    iApply (wp_get_local with "[] [$Hf]").
    simpl.
    destruct (f_locs f0) ; first by inversion Hlocs.
    destruct l ; first by inversion Hlocs1.
    destruct l ; first by simpl in Hlocs ; lia.
    simpl.
    by rewrite set_nth_read.
    by instantiate (1 := λ x, x = immV _).
    iIntros (w) "[-> Hf]".
    rewrite Z.sub_0_r.
    iSimpl.
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
    iFrame.
    done.
    by iIntros "!> [% _]".
    iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite (separate3 _ _ (AI_basic (BI_relop _ _))).
    iApply wp_seq_ctx.
    iSplitR ; last first.
    iSplitL "Hf".
    iApply (wp_relop with "Hf").
    simpl.
    unfold Wasm_int.Int32.ltu.
    rewrite Wasm_int.Int32.unsigned_repr.
    rewrite Coqlib.zlt_false.
    simpl.
    done.
    lia.
    split ; try lia.
    exact Hv.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite - (app_nil_l (AI_basic (i32const 1) :: _)).
    rewrite (separate2 _ (AI_basic (BI_br_if 1))).
    iApply wp_base_push ; first done.
    iApply (wp_br_if_true_ctx with "Hf").
    done.
    iIntros "!> Hf".
    rewrite - (app_nil_l [AI_basic (BI_br 1)]).
    iApply (wp_br_ctx with "Hf") => //.
    iIntros "!> Hf".
    iApply wp_value.
    unfold IntoVal.
    by apply of_to_val.
    iApply "HΞ".
    iSplit ; first done.
    iSplitR "Hf".
    iExists s'.
    unfold take.
    unfold drop.
    iFrame.
    iExists _.
    iFrame.
    done.
    all : try by iIntros "[% _]". }
  iIntros (s') "%Hj %Hs' Hf Hs HΦ HΨ Htab Hcl HΞ".
  destruct s as [|v0 s]; first by inversion Hj.
  cut (exists ys y, v0 :: take j s = ys ++ [y]) ;
  [ intro Htail ; destruct Htail as (ys & y & Htail) |
    exists (removelast (v0 :: take j s)) ;
    exists (List.last (v0 :: take j s) (Wasm_int.Int32.repr 1)) ;
    apply app_removelast_last ;
    apply not_eq_sym ; apply nil_cons ].
  simpl in Hv.
  simpl in Hj.
  assert (j `min` length s = j) as Hjmin.
  { remember (length s) as x. rewrite - Heqx in Hj.
    lia. } 
  rewrite (separate1 (AI_basic (BI_get_local 2))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]").
  simpl. by rewrite set_nth_read.
  by instantiate ( 1 := λ x, x = immV _).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 _ (AI_basic (BI_get_local 3))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate1 _ [AI_basic (BI_get_local 3)]).
  iApply wp_val_app => //.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]").
  simpl.
  destruct (f_locs f0) ; first by inversion Hlocs.
  destruct l ; first by inversion Hlocs1.
  destruct l ; first by simpl in Hlocs ; lia.
  simpl.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, x = immV _).
  iIntros (w) "[-> Hf]".
  iSimpl.
  instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
  iFrame.
  done.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate3 _ _ (AI_basic (BI_relop _ _))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_relop with "Hf").
  simpl.
  unfold Wasm_int.Int32.ltu.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Coqlib.zlt_true.
  simpl.
  done.
  lia.
  lia.
  lia.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (BI_const (VAL_int32 _)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_br_if_false with "Hf").
  done.
  iNext.
  by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate1 (AI_basic (BI_get_local 2)) [_;_;_;_;_;_;_;_;_;_]).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, x = immV _).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate1 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app. done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, x = immV _).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate3 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, x = immV _).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf Hs".
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
 
  iApply wp_wand_r.
  iSplitL.

  iApply wp_load ; last first.
  iFrame.
  unfold isStack.
  iDestruct "Hs" as "(Hdiv & Hlen & Hn & Hl & Hbs)".
  rewrite cat_app.
  iDestruct (big_sepL_app with "Hl") as "[Hs Hs']".
  rewrite app_length.
  rewrite Hs'.
  rewrite take_length.
  replace (S j `min` length (v0 :: s)) with (S j) ; last by simpl ; lia.
  unfold take ; fold (take (A := value)).
  rewrite Htail.
  iDestruct (big_sepL_app with "Hs") as "[Hs H]".
  iDestruct "H" as "[H _]".
  iDestruct (i32_wms with "H") as "H" => //.
  rewrite Nat.add_0_r.
  rewrite N.add_0_r.
  replace (Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr (v + 4 + (S (length s) - S j) * 4)))
    with (Z.to_N (v + 4 + (S (length s) - S j) * 4)).
  replace (S j + (length (v0 :: s) - S j)) with (length (v0 :: s)) ; last by simpl ; lia.
  replace (v + 4 + length (v0 :: s) * 4 - 4 - 4 * length ys)%Z
    with (v + 4 + length (v0 :: s) * 4 - S (length ys) * 4)%Z ; last lia.
  replace (S (length ys)) with (length (ys ++ [y])) ;
    last by rewrite app_length ; simpl ; lia.
  rewrite (cat_app ys [y]).
  rewrite - Htail.
  simpl.
  rewrite firstn_length.
  rewrite Hjmin.
  rewrite (Z.mul_sub_distr_r (S (length s)) (S j) 4).
  simpl in Hj.
  remember (length s) as x.
  rewrite - Heqx.
  replace (v + 4 + S x * 4 - S j * 4)%Z
    with (v + 4 + (S x * 4 - S j * 4))%Z ;
    last lia.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq Z.mod_small.
  instantiate (1 := VAL_int32 _).
  iSplitR "H" ; last iExact "H".
  iNext.
  subst x.
  instantiate ( 1 := λ x, (⌜ x = immV [VAL_int32 y] ⌝ ∗ ⌜ (two16 | v)%Z ⌝ ∗ ⌜ (S (length s) < two14)%Z ⌝ ∗ N.of_nat n ↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v + 4 + S (length s) * 4) ∗  (∃ bs : seq.seq byte, ⌜ Z.of_nat (length bs) = (two16 - 4 - S (length s) * 4)%Z⌝ ∗
            N.of_nat n↦[wms][Z.to_N (v + 4 + S (length s) * 4)]bs) ∗ ([∗ list] k↦y0 ∈ s', N.of_nat n
                              ↦[i32][ Z.to_N
                                        (v + 4 + S (length s) * 4 - 4 - 4 * S (j + k))] y0) ∗ [∗ list] k↦y0 ∈ ys, N.of_nat n
                             ↦[i32][ Z.to_N (v + 4 + S (length s) * 4 - 4 - 4 * k)] y0)%I).
  iFrame.
  done.
  simpl.
  unfold Wasm_int.Int32.max_unsigned in Hv ; rewrite - Heqx in Hv ; lia.
  simpl.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  done.
  done.
  iIntros (w) "[[[-> H1] H2] Hf]".
  iSimpl.
  instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗
                                     ( ⌜(two16 | v)%Z⌝ ∗ ⌜(S (length s) < two14)%Z⌝ ∗ N.of_nat n ↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v + 4 + S (length s) * 4) ∗
         (∃ bs : seq.seq byte, ⌜Z.of_nat (length bs) = (two16 - 4 - S (length s) * 4)%Z⌝ ∗
            N.of_nat n↦[wms][Z.to_N (v + 4 + S (length s) * 4)]bs) ∗
         ([∗ list] k↦y0 ∈ s', N.of_nat n
                              ↦[i32][ Z.to_N
                                        (v + 4 + S (length s) * 4 - 4 - 4 * S (j + k))] y0) ∗
         ([∗ list] k↦y0 ∈ ys, N.of_nat n
                                       ↦[i32][ Z.to_N (v + 4 + S (length s) * 4 - 4 - 4 * k)] y0))
                                     ∗ N.of_nat n↦[wms][Wasm_int.N_of_uint i32m
                            (Wasm_int.Int32.repr (v + 4 + (length (v0 :: s) - S j) * 4)) +
                                                          N.zero]bits (VAL_int32 y)
                                     ∗ ↪[frame] {|
                    f_locs :=
                      set_nth
                        (VAL_int32
                           (Wasm_int.Int32.repr (v + 4)))
                        (set_nth
                           (VAL_int32
                              (Wasm_int.Int32.repr (v + 4 + length (v0 :: s) * 4)))
                           (f_locs f0) 3
                           (VAL_int32
                              (Wasm_int.Int32.repr (v + 4 + length (v0 :: s) * 4)))) 2
                        (VAL_int32
                           (Wasm_int.Int32.repr (v + 4 + (length (v0 :: s) - S j) * 4)));
                    f_inst := f_inst f0
                                     |})%I).
  iFrame.
  done.
  by iIntros "!> [% _]".
  iIntros (w) "(-> & (Hdiv & Hlen & Hv & Hbs & Hs' & Hs) & H & Hf)".
  iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate3 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]") => /=.
  destruct (f_locs f0) ; inversion Hlocs0.
  simpl. done.
  by instantiate (1 := λ x, x = immV _).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate5 (AI_basic (i32const (v + 4 + _ * 4)))).
    
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iSplitL "HΦ Hf Htab Hcl".
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r ; iSplitL.
  unfold take ; fold (take (A := value)).
  rewrite Htail.
  iDestruct (stackAll_app with "HΦ") as "(HΦ & Hy & _)".
  rewrite (separate1 _ [_;AI_basic (BI_call_indirect 1)]).
  rewrite - (app_nil_r [_ ; AI_basic (BI_call_indirect 1)]).
  iApply wp_wasm_empty_ctx.
  iApply wp_base_push ; first done.
  iApply (wp_call_indirect_success_ctx with "Htab Hcl Hf").
  simpl.
  unfold cl_type.
  rewrite Hclt.
  done.
  simpl.
  done.
  iIntros "!> (Htab & Hcl & Hf)".
  iApply wp_base_pull.
  iApply wp_wasm_empty_ctx.
  simpl.
  iApply ("Hspec" with "[Hy Hf Htab Hcl]").
  iFrame.
  iPureIntro => //=.
  iIntros (w) "(H & Hf)".
    (* iDestruct "H" as (v1) "[-> Hv1]". *)
    instantiate (1 := λ x, (⌜ x = trapV ⌝ ∨ ∃ v1, ⌜ x = immV _ ⌝ ∗ stackAll ys Φ ∗ Ψ y v1 ∗
                         N.of_nat j0↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]
                         Some a ∗
                         N.of_nat a↦[wf]cl )%I) ;
      iFrame.
    iDestruct "H" as "[?|H]";[by iLeft|iRight].
    iDestruct "H" as "[H ?]"; iDestruct "H" as (v1) "[-> Hv1]".
  iExists  _; by iFrame.
  iIntros (w) "[H Hf]".
    (* iDestruct "H" as (v1) "[-> H]". *)
  iSimpl.
  instantiate (1 := λ x, ((⌜ x = trapV ⌝ ∨ (∃ v1, ⌜ x = immV _ ⌝ ∗ stackAll ys Φ ∗ Ψ y v1 ∗
                                           N.of_nat j0↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]
                                            Some a ∗ N.of_nat a↦[wf]cl))
                                           ∗ ↪[frame] _)%I).
    iDestruct "H" as "[-> | H]";[iFrame;by iLeft|iFrame;iRight].
    iDestruct "H" as (v1) "[-> Hv1]".
    iExists _ . by iFrame.
  iIntros "!> H".
  by iDestruct "H" as (v1) "[% _]".
  iIntros (w) "Hf".
  iDestruct "Hf" as (v1) "(-> & HΦ & Hv1 & Htab & Hcl & Hf)".
  iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf H".
  rewrite (separate1 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply wp_store ; last first.
  simpl.
  iFrame.
  iNext.
  by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  done.
  done.
  done.
  iIntros (w) "[[-> H] Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ N.of_nat n↦[wms][ _ ] _ ∗ ↪[frame] _)%I) ;
  iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "(-> & H & Hf)".
  iSimpl.
  rewrite (separate3 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_binop with "Hf").
  done.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (BI_const (VAL_int32 (Wasm_int.Int32.iadd _ _))))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_set_local with "[] [$Hf]") => /=.
  destruct (f_locs f0) ; first done.
  destruct l ; first done.
  destruct l ; first by simpl in Hlocs ; lia.
  destruct l ; first by simpl in Hlocs ; lia.
  simpl.
  lia.
  by instantiate (1 := λ x, x = immV _).
  iIntros (w) "[-> Hf]".
  simpl.
  rewrite set_nth_write.
  all : try by iIntros "[% _]".
  all : try by iIntros "Habs" ; iDestruct "Habs" as (?) "[% _]".
  rewrite - (app_nil_l [AI_basic (BI_br 0)]).
  iApply (wp_br_ctx_nested with "Hf").
  lia.
  done.
  instantiate (1 := LH_rec [] 0 [] (LH_base [] []) []) => //=.
  done.
  done.
  iIntros "!> Hf".
  iSimpl.
  rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).
  iApply (wp_loop_ctx with "Hf") => //.
  iIntros "!> Hf".
  simpl.
  rewrite - (cat0s (AI_basic (BI_get_local 2) :: _)).
  rewrite - (cats0 [AI_basic _;_;_;_;_;_;_;_;_;_;_;_;_;_;_]). 
  iApply wp_label_push ; first done.
  iApply ("IHj" with "[] [] [Hf] [Hv Hbs Hs' Hs H Hlen Hdiv] [HΦ] [HΨ Hv1] Htab Hcl").
  iPureIntro.
  lia.
  instantiate (1 := v1 :: s').
  iPureIntro.
  simpl.
  rewrite Hs' => //=.
  lia.
  unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Wasm_int.Int32.unsigned_repr.
  remember (length s) as x. rewrite - Heqx.
  replace (v + 4 + (S x - S j) * 4 + 4)%Z
    with (v + 4 + (S x - j) * 4)%Z.
  iExact "Hf".
  lia.
  lia.
  lia.
  unfold isStack.
  iFrame.
  iDestruct "Hlen" as "%".
  iSplit ; first iPureIntro.
  rewrite app_length.
  rewrite firstn_length.
  replace (j `min` length (v0 :: s)) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  lia.
  iSplitL "Hv".
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x. rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S (x)) ; last lia.
  iExact "Hv".
  iSplitR "Hbs".
  iApply big_sepL_app.
  iSplitL "Hs".
  replace j with (j `min` S j) ; last lia.
  rewrite - take_take.
  simpl.
  rewrite Htail.
  replace j with (length ys).
  rewrite take_app.
  iApply (big_sepL_impl with "Hs").
  iIntros "!>" (k x) "% H".
  remember (length s) as z ; rewrite - Heqz.
  replace (S z) with (length (ys ++ v1 :: s')) ; first done.
  rewrite app_length.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqz.
  remember (length ys) as zz ; rewrite - Heqzz.
  replace zz with j ; first lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  subst z. rewrite Hjmin in Hl. rewrite - Heqzz in Hl. lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite Hjmin in Hl.
  remember (length ys) as zz.
  rewrite - Heqzz in Hl.
  lia.
  iSplitL "H".
  iApply i32_wms.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  rewrite N.add_0_r.
  rewrite Nat.add_0_r.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S (x)) ; last lia.
  replace (v + 4 + S x *4 - 4 -4 * j)%Z
    with  (v + 4 + ( S x - S j) * 4)%Z ; last lia.
  iExact "H".
  unfold Wasm_int.Int32.max_unsigned in Hv.
  lia.
  iApply (big_sepL_impl with "Hs'").
  iIntros "!>" (k x) "% H".
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as z ; rewrite - Heqz.
  replace (j `min` S z) with j ; last by simpl ; lia.  
  rewrite Hs'.
  simpl.
  rewrite - Heqz.
  replace (j + S (z - j)) with (S z) ; last lia.
  replace (S ( j + k)) with (j + S k) ; last lia.
  iExact "H".
  iDestruct "Hbs" as (bs) "[% H]".
  iExists bs.
  iSplit ; first iPureIntro.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  lia.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S x) ; last lia.
  iExact "H".
  replace j with (j `min` S j) ; last lia.
  rewrite - take_take.
  simpl.
  rewrite Htail.
  replace j with (length ys).
  rewrite take_app.
  done.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite Hjmin in Hl.
  remember (length ys) as zz ; rewrite - Heqzz in Hl ;
    lia.
  rewrite - (take_drop j s).
  rewrite app_comm_cons.
  rewrite Htail.
  rewrite take_drop.
  rewrite drop_app_le.
  replace j with (length ys).
  rewrite drop_app.
  simpl.
  iFrame.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
   rewrite Hjmin in Hl.
  remember (length ys) as zz ; rewrite - Heqzz in Hl ;
    lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite app_length.
  rewrite - Hl.
  lia.
  iExact "HΞ". }
  iApply ("H" with "[] [] [Hf] [Hn Hs] [HΦ] [] Htab Hcl").
  instantiate (1 := length s).
  iPureIntro ; lia.
  instantiate (1 := []).
  iPureIntro ; simpl ; lia.
  rewrite Z.sub_diag.
  rewrite Z.mul_0_l.
  rewrite Z.add_0_r.
  done.
  iDestruct "Hs" as "(% & % & Hs & Hbs)".
  iSplit ; first done.
  iSplit ; first iPureIntro.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  exact H0.
  iSplitL "Hn".
  iApply i32_wms.
  rewrite N.add_0_r.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  iSplitL "Hs".
  rewrite cats0 firstn_length.
  rewrite firstn_all.
  rewrite Nat.min_id.
  done.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  done.
  rewrite firstn_all.
  done.
  rewrite drop_all.
  done.
  done.
  all : try by iIntros "[% _]".
  by iIntros "[[[% _] _] _]".
Qed.*)
          
                                        
    
    
End specs.


End stack.    
      
