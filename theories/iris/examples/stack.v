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
   


Section stack.


Canonical Structure wasm_lang := Language wasm_mixin.

 Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !wtablimitG Σ, !wmemlimitG Σ}. 

Section code.

Definition i32const (n:Z) := AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m n))).
Definition bi32const (n:Z) := BI_const (VAL_int32 (Wasm_int.int_of_Z i32m n)).
Definition value_of_int (n:Z) := VAL_int32 (Wasm_int.int_of_Z i32m n).

Definition two14 := 16384%Z.
Definition two16 := 65536%Z.
Definition two32 := 4294967296%Z.


Definition new_stack :=
  [
    i32const 1 ;
    AI_basic BI_grow_memory ;
    AI_basic (BI_tee_local 0) ;
    i32const (-1) ;
    AI_basic (BI_relop T_i32 (Relop_i ROI_eq)) ;  
    AI_basic (BI_if (Tf [] [T_i32]) [
                   bi32const (-1)
                 ] [
                   BI_get_local 0 ;
                   bi32const 65536 ;
                   BI_binop T_i32 (Binop_i BOI_mul) ;
                   BI_tee_local 0 ;
                   BI_get_local 0 ;
                   bi32const 4 ;
                   BI_binop T_i32 (Binop_i BOI_add) ;
                   BI_store T_i32 None N.zero N.zero ;
                   BI_get_local 0 
             ])                             
  ].

Definition is_empty :=
  [
    AI_basic (BI_get_local 0) ;
    i32const 4 ;
    AI_basic (BI_binop T_i32 (Binop_i BOI_add)) ;
    AI_basic (BI_get_local 0) ;
    AI_basic (BI_load T_i32 None N.zero N.zero) ;
    AI_basic (BI_relop T_i32 (Relop_i ROI_eq))
  ].

Definition is_full :=
  [
    i32const 0 ;
    i32const 1 ;
    AI_basic (BI_get_local 0) ;
    AI_basic (BI_load T_i32 None N.zero N.zero) ;
    i32const 65536 ;
    AI_basic (BI_binop T_i32 (Binop_i (BOI_rem SX_U))) ;
    AI_basic BI_select
  ].


(* Couldn't remember, do the arguments come first and then the local variables, or
   is it the other way around ? This is coded with local variables 0, 1, … n being the 
   n arguments, and then local variables n+1, n+2, … n+m be the m local variables.
   Will need to be changed if it was actually the other way around. *)

Definition pop :=
  [
    AI_basic (BI_get_local 0) ;
    AI_basic (BI_load T_i32 None N.zero N.zero) ;
    i32const 4 ;
    AI_basic (BI_binop T_i32 (Binop_i BOI_sub)) ;
    AI_basic (BI_tee_local 1) ;
    AI_basic (BI_load T_i32 None N.zero N.zero) ;
    AI_basic (BI_get_local 0) ;
    AI_basic (BI_get_local 1) ;
    AI_basic (BI_store T_i32 None N.zero N.zero)
  ].

Definition push :=
  [
    AI_basic (BI_get_local 1) ;
    AI_basic (BI_load T_i32 None N.zero N.zero) ;
    AI_basic (BI_tee_local 2) ;
    AI_basic (BI_get_local 0) ;
    AI_basic (BI_store T_i32 None N.zero N.zero) ;
    AI_basic (BI_get_local 1) ;
    AI_basic (BI_get_local 2) ;
    i32const 4 ;
    AI_basic (BI_binop T_i32 (Binop_i BOI_add)) ;
    AI_basic (BI_store T_i32 None N.zero N.zero)
  ].


Definition stack_map :=
  [
    AI_basic (BI_get_local 1) ;
    AI_basic (BI_load T_i32 None N.zero N.zero) ;
    AI_basic (BI_set_local 3) ;
    AI_basic (BI_get_local 1) ;
    i32const 4 ;
    AI_basic (BI_binop T_i32 (Binop_i BOI_add)) ;
    AI_basic (BI_set_local 2) ;
    AI_basic (BI_block (Tf [] [])
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
                                 bi32const 4 ;
                                 BI_binop T_i32 (Binop_i BOI_add) ;
                                 BI_set_local 2 ;
                                 BI_br 0]
             ])
  ].



End code.


 
Section specs.


   Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wftablimitsG Σ, !wmemlimitG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ, !logrel_na_invs Σ }. 





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

  



Lemma spec_new_stack f0 n len : 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ length (f_locs f0) >= 1 ⌝ ∗
        ⌜ (Wasm_int.Int32.modulus - 1)%Z <>
         Wasm_int.Int32.Z_mod_modulus (ssrnat.nat_of_bin (len `div` page_size)) ⌝ ∗
        ⌜ (len + 4 < Z.to_N (two_power_nat 32))%N ⌝ ∗
        ⌜ (page_size | len)%N ⌝ ∗
        ↪[frame] f0 ∗
        N.of_nat n ↦[wmlength] len }}}
    new_stack
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
                               (∃ b, N.of_nat n ↦[wms][ len ]
                                              repeat b (N.to_nat page_size)) ∗
                              N.of_nat n↦[wmlength] (len + page_size)%N)
                              
                   ∨ (⌜ x = immV [VAL_int32 int32_minus_one] ⌝%I ∗
                N.of_nat n↦[wmlength] len)) ∗ ↪[frame] f0)%I).
    iIntros "[[(%Habs & _ & _) | (%Habs & _)] Hf]" ; inversion Habs.
  - iSplitR "HΦ".
    unfold i32const.
    iApply (wp_grow_memory
              NotStuck ⊤ n f0 len
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
    iApply (wp_seq NotStuck ⊤ _ (λ x, (⌜ x = immV [v] ⌝
                                      ∗ ↪[frame] {|
                                            f_locs := set_nth v (f_locs f0) 0 v;
                                            f_inst := f_inst f0
                                          |} )%I) ).
    (* rewrite (assoc _ (∃ b, _)%I ). *)
    (* rewrite (assoc _ (⌜ immV [v] = _ ⌝)%I). *)
    (* rewrite (assoc _ (⌜ immV [v] = immV [VAL_int32 int32_minus_one] ⌝)%I). *)
    (* iDestruct (bi.sep_or_r with "H") as "[H Hf]".  *)
    iDestruct "H" as "[H Hf]".
    iSplitR.
  - iIntros "[%Habs _]" ; done.
  - iSplitL "Hf". 
    iApply (wp_tee_local with "Hf").
    iIntros "Hf".
    rewrite list_extra.cons_app.
    iApply wp_val_app => //=.
    iSplitR => //=.
    iIntros "!> [%Habs _]" ; done.
    iApply (wp_set_local with "Hf") => //=.
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
      iDestruct "Hb" as (b) "Hb".
      unfold page_size at 2.
      replace (N.to_nat (64 * 1024)) with (4 + N.to_nat (65532)) ; last done.
      rewrite repeat_app.
      unfold repeat at 1.
      rewrite - separate4.
      iDestruct (wms_append with "Hb") as "[H1 Hb]".
      iDestruct (wms_append with "Hb") as "[H2 Hb]".
      iDestruct (wms_append with "Hb") as "[H3 Hb]".
      iDestruct (wms_append with "Hb") as "[H4 Hb]".
      iAssert (N.of_nat n↦[wms][ len ] [b;b;b;b])%I with "[H1 H2 H3 H4]" as "Hbs".
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
            iApply (wp_get_local with "Hf") => /=; first by rewrite set_nth_read.
            instantiate (1 := (λ x, ( x = immV [VAL_int32 c]))) => //=.
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
            iIntros "Hf".
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
 (*       iSplitR => //=.
        iIntros "!> [%Habs _]" ; done.*)
        iApply (wp_set_local with "Hf") => //=.
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
        iApply (wp_get_local with "Hf") => //=.
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
        instantiate (1 := [b ; b ; b ; b]).
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
        iApply (wp_get_local with "Hf").
        simpl.
        rewrite set_nth_read.
        done.
        instantiate (1 := λ x, x = immV [ value_of_int (N.to_nat len) ]).
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
    (*    rewrite Wasm_int.Int32.signed_repr => //.
        rewrite Wasm_int.Int32.signed_repr => //.
        repeat f_equal.
        replace 65536%Z with (Z.of_nat (N.to_nat page_size)) ; last done.
        replace (Z.mul (Z.of_nat (ssrnat.nat_of_bin (len `div` page_size))) (Z.of_nat (N.to_nat page_size)))
          with (Z.of_nat (ssrnat.muln (ssrnat.nat_of_bin (len `div` page_size))
                                      (N.to_nat page_size))) ;
          last by unfold ssrnat.muln, ssrnat.muln_rec ; lia.
        rewrite - (ssrnat.bin_of_natK (N.to_nat page_size)).
        rewrite - ssrnat.nat_of_mul_bin.
        replace (ssrnat.bin_of_nat (N.to_nat page_size)) with page_size ; last done.
        replace (len `div` page_size * page_size)%N with len.
        admit.
        admit.
        done.
        admit.*)
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
        (*
        unfold points_to_i32.
        unfold mem_block_at_pos.
        destruct (Memdata.encode_int 4 (Z.of_N len + 4)) eqn:Hcode.
        assert (0 = 4) => //=.
        destruct l.
        assert (1 = 4) => //=.
        destruct l.
        assert (2 = 4) => //=.
        destruct l.
        assert (3 = 4) => //=.
        destruct l ; last by assert (4 < length [:: i, i0, i1, i2, i3 & l]) => //=.
        iExists i, i0, i1, i2.
        iSimpl in "Hwm".
        iDestruct "Hwm" as "(H1 & H2 & H3 & H4 & _)".
        repeat rewrite of_nat_to_nat_plus ; rewrite N.add_0_r.
        iFrame.
        iPureIntro.
        unfold bits.
        unfold serialise_i32.
        unfold Wasm_int.int_of_Z.
        simpl.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small.
        replace (N.to_nat len + 4)%Z with (Z.of_N len + 4)%Z ; last lia.
        done. *)
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
        iExists (repeat b ( N.to_nat 65532)).
        iSplit ; first by rewrite repeat_length.
        replace (Z.to_N (N.to_nat len + 4)) with (len + 1 + 1 + 1 + 1)%N ; last lia.
        done.
        done.
        iExists _ ; iFrame.
        done.
Qed.



Lemma spec_is_empty f0 n v s : 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ (f_locs f0) !! 0 = Some (value_of_int v) ⌝ ∗ 
        ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - length s * 4)%Z ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s n }}}
    is_empty
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s n ∗
                           ⌜ (k = 1 /\ s = []) \/
                  (k = 0 /\ s <> []) ⌝ ∗
           ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝}}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hv & Hf & Hstack) HΦ".
  unfold is_empty.
  rewrite separate1.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR.
  by iIntros "[%Habs _]".
  iSplitL "Hf".
  - iApply (wp_get_local with "Hf") => //=.
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
    iApply (wp_get_local with "Hf") => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    rewrite - separate2.
    rewrite separate3.
    iApply wp_seq.
    instantiate ( 1 := λ x, ((((⌜ x = immV [value_of_int (v + 4)%Z ;
                                            value_of_int (v + 4 + length s * 4)%Z] ⌝
                                          ∗ [∗ list] i↦w ∈ s,
                                N.of_nat n ↦[i32][ Z.to_N (v + 4 + length s * 4 - 4 - 4 * i)] w) ∗

                                                                                                 (∃ bs, ⌜ (Z.of_nat (length bs) = two16 - 4 - length s * 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N (v + 4 + length s * 4)]bs)
                              (* (∀ k, ⌜(k >= v + 4 + length s * 4)%Z⌝ -∗
                                                                                                 ⌜(k < v + 16384)%Z⌝ -∗ ∃ bk, N.of_nat n ↦[wm][Z.to_N k] bk) *))
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
    (* exact f0.(f_inst).    *)
    iSplitL "Hs Hrest".
    iFrame.
    done.
    iFrame.
    rewrite N.add_0_r.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    iDestruct (i32_wms with "Hv") as "Hv" => //.
(*    Print bits.
    replace (serialise_i32 (Wasm_int.Int32.repr (v + 4 + length s * 4)))
      with  (bits (VAL_int32 (Wasm_int.Int32.repr (v + 4 + length s * 4)))).
    iApply i32_wms.
    unfold mem_block_at_pos.
    unfold points_to_i32.
    remember (bits (value_of_int (v + 4 + length s * 4))) as bs.
    repeat (destruct bs => //=).
    unfold bits in Heqbs.
    unfold value_of_int in Heqbs.
    replace (Wasm_int.Int32.repr (v + 4 + length s * 4)) with
      (Wasm_int.int_of_Z i32m (v + 4 + length s * 4)) ; last done.
    rewrite <- Heqbs.
    iSimpl.
    iDestruct "Hv" as (a b3 c d) "(? & ? & ? & ? & %Hl)".
    inversion Hl ; subst.
    repeat rewrite of_nat_to_nat_plus ; rewrite N.add_0_r.
    iFrame. *)
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
(*     unfold mem_block_at_pos.
    unfold points_to_i32.
    remember (bits (value_of_int (v + 4 + length s * 4))) as bs.
    repeat destruct bs => //=.
    unfold bits in Heqbs.
    unfold value_of_int in Heqbs.
    replace (Wasm_int.Int32.repr (v + 4 + length s * 4)) with
      (Wasm_int.int_of_Z i32m (v + 4 + length s * 4)) ; last done.
    rewrite <- Heqbs.
    simpl.
    repeat rewrite of_nat_to_nat_plus ; rewrite N.add_0_r.
    repeat iSplit => //=.
    iExists _, _, _, _.
    iDestruct "Hp" as "(? & ? & ? & ? & ?)".
    iFrame.
    done. *)
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
    
    
Lemma spec_is_full f0 n (v : Z) (s : seq.seq i32) : 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ (f_locs f0) !! 0 = Some (value_of_int v) ⌝ ∗ 
        ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - length s * 4 )%Z ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s n }}}
    is_full
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s n ∗
                           ⌜ k = 1 \/ (length s < two14 - 1)%Z ⌝ ∗
          ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1⌝ }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hv & Hf & Hstack) HΦ".
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
                              (*(∀ k, ⌜(k >= v + 4 + length s * 4)%Z⌝ -∗
                                                                                                 ⌜(k < v + 16384)%Z⌝ -∗ ∃ bk, N.of_nat n ↦[wm][Z.to_N k] bk)*))
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
(*    unfold mem_block_at_pos.
    unfold points_to_i32.
    remember (bits (value_of_int (v + 4 + length s * 4))) as bs.
    repeat (destruct bs => //=).
    unfold bits in Heqbs.
    unfold value_of_int in Heqbs.
    replace (Wasm_int.Int32.repr (v + 4 + length s * 4)) with
      (Wasm_int.int_of_Z i32m (v + 4 + length s * 4)) ; last done.
    rewrite <- Heqbs.
    iSimpl.
    iDestruct "Hv" as (a b3 c d) "(? & ? & ? & ? & %Hl)".
    inversion Hl ; subst.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 0)) with (Z.to_N v) ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 1)) with (Z.to_N v + 1)%N ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 2)) with (Z.to_N v + 2)%N ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 3)) with (Z.to_N v + 3)%N ; last lia.
    iFrame. *)
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
(*    unfold mem_block_at_pos.
    unfold points_to_i32.
    remember (bits (value_of_int (v + 4 + length s * 4))) as bs.
    repeat destruct bs => //=.
    unfold bits in Heqbs.
    unfold value_of_int in Heqbs.
    replace (Wasm_int.Int32.repr (v + 4 + length s * 4)) with
      (Wasm_int.int_of_Z i32m (v + 4 + length s * 4)) ; last done.
    rewrite <- Heqbs.
    simpl.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 0)) with (Z.to_N v) ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 1)) with (Z.to_N v + 1)%N ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 2)) with (Z.to_N v + 2)%N ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 3)) with (Z.to_N v + 3)%N ; last lia.
    repeat iSplit => //=.
    iExists _, _, _, _.
    iDestruct "Hp" as "(? & ? & ? & ? & ?)".
    iFrame.
    done. *)
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
(*    unfold two14.
    replace (16384 - 1)%Z with 16383%Z ; last done. *)
    edestruct (Z.lt_total) as [ H | [ H | H]] => //=.     
    rewrite H in Hmod.
    (* replace (Init.Nat.of_uint (Decimal.D1 (Decimal.D6 (Decimal.D3 (Decimal.D8 (Decimal.D3 Decimal.Nil))))) * 4)%Z with 65532%Z in Hmod ; last done. *)
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
(*     replace ( Init.Nat.of_uint
                (Decimal.D1 (Decimal.D6 (Decimal.D3 (Decimal.D8 (Decimal.D3 Decimal.Nil))))) )
            with ( Init.Nat.of_num_uint
             (Number.UIntDecimal
                (Decimal.D1
                   (Decimal.D6 (Decimal.D3 (Decimal.D8 (Decimal.D3 Decimal.Nil))))))) in H ;
      last done. *)
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



Lemma spec_pop f0 n v (a : i32) s :
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
         ∗ ⌜ f0.(f_locs) !! 0 = Some (value_of_int v) ⌝
         ∗ ⌜ length f0.(f_locs) >= 2 ⌝
         ∗ ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - S (length s) * 4 )%Z ⌝
         ∗ isStack v (a :: s) n
         ∗ ↪[frame] f0 }}}
    pop
    {{{ w, ⌜ w = immV [VAL_int32 a] ⌝ ∗
                      isStack v s n ∗
                      ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝ }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hlocs & %Hv & Hstack & Hf) HΦ".
  unfold pop.
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  - iApply (wp_get_local with "Hf") => //=.
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
    (* done.
    iFrame.
    rewrite N.add_0_r.
    iSimpl. *)
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
(*    unfold mem_block_at_pos.
    unfold points_to_i32.
    remember (bits (value_of_int (v + 4 + length (a :: s) * 4))) as bs.
    repeat (destruct bs => //=).
    unfold bits in Heqbs.
    unfold value_of_int in Heqbs.
    replace (Wasm_int.Int32.repr (v + 4 + S (length s) * 4)) with
      (Wasm_int.int_of_Z i32m (v + 4 + length (a :: s) * 4)) ; last done.
    rewrite <- Heqbs.
    iSimpl.
    iDestruct "Hv" as (a0 b3 c d) "(? & ? & ? & ? & %Hl)".
    inversion Hl ; subst.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 0)) with (Z.to_N v) ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 1)) with (Z.to_N v + 1)%N ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 2)) with (Z.to_N v + 2)%N ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 3)) with (Z.to_N v + 3)%N ; last lia.
    iFrame. *)
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
(*    unfold mem_block_at_pos.
    unfold points_to_i32.
    remember (bits (value_of_int (v + 4 + length (a :: s) * 4))) as bs.
    repeat destruct bs => //=.
    unfold bits in Heqbs.
    unfold value_of_int in Heqbs.
    replace (Wasm_int.Int32.repr (v + 4 + S (length s) * 4)) with
      (Wasm_int.int_of_Z i32m (v + 4 + length (a :: s) * 4)) ; last done.
    rewrite <- Heqbs.
    simpl.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 0)) with (Z.to_N v) ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 1)) with (Z.to_N v + 1)%N ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 2)) with (Z.to_N v + 2)%N ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 3)) with (Z.to_N v + 3)%N ; last lia.
    repeat iSplit => //=.
    iExists _, _, _, _.
    iDestruct "Hp" as "(? & ? & ? & ? & ?)".
    iFrame.
    done. *)
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
    iIntros "Hf".
    rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_set_local with "Hf") => //.
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
 (*   iSplitR => //=.
    iApply (big_sepL_impl with "Hs").
    iNext. iIntros "!>" (k x) "%Hlookup Hp".
    replace (v + 4 + S (length s) * 4 - 4 - 4 * S k)%Z
      with (v + 4 + length s * 4 - 4 - 4 * k)%Z ; first done.
    lia.
    simpl.
    iDestruct "Ha" as "[Ha _]".
    iApply i32_wms => //.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    rewrite N.add_0_r.
    rewrite Z.mul_0_r.
    rewrite Z.sub_0_r.
    replace (v + 4 + S (length s) * 4 - 4)%Z with (v + S (length s) * 4)%Z ; last lia.
    done. *)
(*    replace (N.of_nat (N.to_nat (Z.to_N (v + S (length s) * 4)) + 0))
      with (Z.to_N (v + S (length s) * 4)) ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N (v + S (length s) * 4)) + 1))
      with (Z.to_N (v + S (length s) * 4) + 1)%N ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N (v + S (length s) * 4)) + 2))
      with (Z.to_N (v + S (length s) * 4) + 2)%N ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N (v + S (length s) * 4)) + 3))
      with (Z.to_N (v + S (length s) * 4) + 3)%N ; last lia.
    iFrame.
    unfold Wasm_int.Int32.max_unsigned in Hv.
    lia. *)
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
    iApply (wp_get_local with "Hf") => //=.
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
    iApply (wp_get_local with "Hf") => //=.
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
(*    unfold mem_block_at_pos.
    unfold points_to_i32.
    iDestruct "Hp" as (a0 b c d) "(? & ? & ? & ? & %Hbits)".
    unfold bits in Hbits.
    unfold value_of_int in Hbits.
    rewrite Hbits.
    iSimpl.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 0)) with (Z.to_N v) ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 1)) with (Z.to_N v + 1)%N ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 2)) with (Z.to_N v + 2)%N ; last lia.
    replace (N.of_nat (N.to_nat (Z.to_N v) + 3)) with (Z.to_N v + 3)%N ; last lia.
    iFrame. *)
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
(*    unfold mem_block_at_pos.
    unfold points_to_i32.
    remember (bits (value_of_int (v + 4 + length s * 4))) as bs.
    repeat destruct bs => //=.
    unfold bits, value_of_int in Heqbs.
    replace (v + S (length s) * 4)%Z with (v + 4 + length s * 4)%Z ; last lia.
    rewrite - Heqbs.
    simpl.
    iDestruct "Hp" as "(? & ? & ? & ? & _)".
    repeat rewrite of_nat_to_nat_plus.
    rewrite N.add_0_r.
    iExists _,_,_,_.
    iFrame.
    done. *)
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
    
    

    
                                                                         
                                                                        
    
Lemma spec_push f0 n v (a : i32) s :
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
         ∗ ⌜ f0.(f_locs) !! 0 = Some (VAL_int32 a) ⌝ 
         ∗ ⌜ f0.(f_locs) !! 1 = Some (value_of_int v) ⌝
         ∗ ⌜ length f0.(f_locs) >= 3 ⌝
         ∗ ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - S (length s) * 4 )%Z ⌝
         ∗ ⌜ (length s < two14 - 1)%Z ⌝
         ∗ isStack v s n
         ∗ ↪[frame] f0 }}}
    push
    {{{ w, ⌜ w = immV [] ⌝ ∗
           isStack v (a :: s) n ∗
           ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝ }}}. 
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hloca & %Hlocv & %Hlocs & %Hv & %Hlens & Hstack & Hf) HΦ".
  unfold push.
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  - iApply (wp_get_local with "Hf") => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate2.
    iApply wp_seq.
    instantiate ( 1 := λ x, ((((⌜ x = immV [ value_of_int (v + 4 + length (s) * 4)%Z] ⌝
                                           ∗ [∗ list] i↦w ∈  s,
                                 N.of_nat n ↦[i32][ Z.to_N (v + 4 + length (s) * 4 - 4 - 4 * i)] w) ∗

                                                                                                    (∃ bs, ⌜ Z.of_nat (length bs) = (two16 - 4 - length s * 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N (v + 4 + length s * 4)]bs)
                                                                                                  (* (∀ k, ⌜(k >= v + 4 + length (s) * 4)%Z⌝ -∗
                                                                                                         ⌜(k < v + 16384)%Z⌝ -∗ ∃ bk, N.of_nat n ↦[wm][Z.to_N k] bk) *))
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
(*    unfold mem_block_at_pos.
    unfold points_to_i32.
    remember (bits (value_of_int (v + 4 + length (s) * 4))) as bs.
    repeat (destruct bs => //=).
    unfold bits in Heqbs.
    unfold value_of_int in Heqbs.
    replace (Wasm_int.Int32.repr (v + 4 + (length s) * 4)) with
      (Wasm_int.int_of_Z i32m (v + 4 + length (s) * 4)) ; last done.
    rewrite <- Heqbs.
    iSimpl.
    iDestruct "Hv" as (a0 b3 c d) "(? & ? & ? & ? & %Hl)".
    inversion Hl ; subst.
    repeat rewrite of_nat_to_nat_plus.
    rewrite N.add_0_r.
    iFrame. *)
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
(*    unfold mem_block_at_pos.
    unfold points_to_i32.
    remember (bits (value_of_int (v + 4 + length (s) * 4))) as bs.
    repeat destruct bs => //=.
    unfold bits in Heqbs.
    unfold value_of_int in Heqbs.
    replace (Wasm_int.Int32.repr (v + 4 + (length s) * 4)) with
      (Wasm_int.int_of_Z i32m (v + 4 + length (s) * 4)) ; last done.
    rewrite <- Heqbs.
    simpl.
    repeat rewrite of_nat_to_nat_plus.
    rewrite N.add_0_r.
    repeat iSplit => //=.
    iExists _, _, _, _.
    iDestruct "Hp" as "(? & ? & ? & ? & ?)".
    iFrame.
    done. *)
  - unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate2.
    iApply (wp_seq _ _ _ (λ x, (⌜ x = immV [value_of_int (v + 4 + length s * 4)] ⌝
                                           ∗ ↪[frame] _)%I)).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - iApply (wp_tee_local with "Hf").
    iIntros "Hf".
    rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_set_local with "Hf") => //=.
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
    subst f1 ; iApply (wp_get_local with "Hf") => //.
    unfold set_nth.
    destruct (f_locs f0) => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate3.
    iApply wp_seq.
   instantiate
      (1 := λ x, (((⌜ x = immV [] ⌝ ∗ N.of_nat n↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v+4+length s * 4) ∗ ([∗ list] i↦w ∈ s, N.of_nat n↦[i32][Z.to_N (v + 4 + length s * 4 - 4 - 4 * i)] w) ∗ (∃ bs, ⌜ Z.of_nat (length bs) = (two16 - 4 - length (s) * 4 - 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N (v + 4 + S (length s) * 4)]bs) (* (∀ k, ⌜ (k >= v + 4 + S (length s) * 4)%Z ⌝ -∗ ⌜ (k < v + 16384)%Z ⌝ -∗ ∃ bk, N.of_nat n↦[wm][Z.to_N k]bk) *))
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
    
(*    rewrite N2Nat.id.
    iSplitR "Ha".
    iSplit => //=.
    iExists bs.
    iSplit.
    iPureIntro.
    simpl in Hbs.
    unfold two16.
    lia.
    unfold mem_block_at_pos.
    iApply (big_sepL_impl with "Hrest").
    iNext. iIntros "!>" (k x) "%Hbits H".
    repeat rewrite of_nat_to_nat_plus.
    replace (Z.to_N (v + 4 + length s * 4) + N.of_nat (S (S (S (S k)))))%N
      with (Z.to_N (v + 4 + S (length s) * 4) + N.of_nat k)%N ; last lia.
    done.
    unfold mem_block_at_pos.
    iApply (big_sepL_impl with "Ha").
    iIntros "!>" (k x) "%Hbits H".
    repeat rewrite of_nat_to_nat_plus.
    simpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    rewrite N.add_0_r.
    done. *)
  - iIntros (w) "[[(-> & Hp & Hs & Hrest) Ha] Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite (separate1 (AI_basic _)).
    iApply wp_seq.
    instantiate (1 := λ x, ( ⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame]f1)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - iApply (wp_get_local with "Hf") => //.
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
    iApply (wp_get_local with "Hf") => //.
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
  
  


Lemma spec_stack_map (f0 : frame) (n : immediate) (f : i32) (v : Z) (s : seq.seq i32)
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
                    AI_invoke a ]
                  {{{ w, (∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)
                           ∗ ↪[frame] fc
                           ∗ (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) 
                           ∗ (N.of_nat a) ↦[wf] cl }}}) ∗   
            ↪[frame] f0 }}}
    stack_map
    {{{ w, ⌜ w = immV [] ⌝ ∗
           (∃ s', isStack v s' n ∗ stackAll2 s s' Ψ) ∗
           (∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝ )
    }}}.
Proof.
  iIntros "!>" (Ξ) "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs & %Hvb & %Hv & Hs & HΦ & %Htypes & %Htab & Htab & Hcl & %Hclt & #Hspec & Hf) HΞ".
  unfold stack_map.
  rewrite (separate1 (AI_basic (BI_get_local 1))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply wp_get_local => //.
  instantiate (1 := λ x, x = immV [value_of_int v]) => //.
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (i32const v)).
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
(*  unfold Wasm_int.N_of_uint, Wasm_int.int_of_Z.
  destruct i32m.  
  replace (N_of_uint (int_of_Z v)) with (Z.to_N v). *)
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
  rewrite (separate2 (i32const (v + _ + _))).
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
  iApply (wp_get_local with "Hf") => //=.
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
  (*rewrite - (cats0 [AI_basic (BI_loop _ _)]).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iApply (wp_label_bind with "[Hf Hs Hn]") ; last first. 
  iPureIntro.
  unfold lfilled, lfill.
  instantiate (4 := []) => /=.
  by rewrite app_nil_r. *)
  rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).
  iApply (wp_loop_ctx with "Hf") => //.
  iIntros "!> Hf".
  simpl.
  rewrite - (cat0s (AI_basic (BI_get_local 2) :: _)).
  rewrite - (cats0 [AI_basic _;_;_;_;_;_;_;_;_;_;_;_;_;_;_]). 
  iApply wp_label_push ; first done.
(*  iApply (wp_label_bind with "[Hf Hs Hn]") ; last first.
  iPureIntro.
  unfold lfilled, lfill.
  instantiate (4 := []) => /=.
  by rewrite app_nil_r.  *)
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
                    isStack v (take j s ++ s') n -∗ (*  ++ drop (length s - j) s) n -∗ *)
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
     AI_basic (bi32const 4); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
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
          bi32const 4; BI_binop T_i32 (Binop_i BOI_add); BI_set_local 2; 
          BI_br 0])] [] []
    {{ v0, Ξ v0 }})%I as "H".
  { iIntros (j).
  iInduction j as [|j] "IHj".
  { iIntros (s') "%Hj %Hs' Hf Hs HΦ HΨ Htab Hcl HΞ".
    rewrite (separate1 (AI_basic (BI_get_local 2))).
    iApply wp_seq_ctx.
    iSplitR ; last first.
    iSplitL "Hf".
    iApply (wp_get_local with "Hf").
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
    iApply (wp_get_local with "Hf").
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
(*  
  iInduction s as [|a s] "IHs".
  { *)
    rewrite (separate3 _ _ (AI_basic (BI_relop _ _))).
    iApply wp_seq_ctx.
    iSplitR ; last first.
    iSplitL "Hf".
    iApply (wp_relop with "Hf").
(*    rewrite Z.mul_0_l.
    rewrite Z.add_0_r.
    unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
    rewrite Wasm_int.Int32.unsigned_repr.
    rewrite Wasm_int.Int32.unsigned_repr. *)
    simpl.
    unfold Wasm_int.Int32.ltu.
    rewrite Wasm_int.Int32.unsigned_repr.
    rewrite Coqlib.zlt_false.
    simpl.
    done.
    lia.
    split ; try lia.
    exact Hv.
    (*    unfold Wasm_int.Int32.max_unsigned.
    unfold Wasm_int.Int32.modulus.
    unfold Wasm_int.Int32.wordsize.
    unfold Integers.Wordsize_32.wordsize.
    done.
    lia. *)
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite - (app_nil_l (i32const _ :: _)).
    rewrite (separate2 _ (AI_basic (BI_br_if 1))).
    iApply wp_base_push ; first done.
(*    iApply wp_seq_ctx.
    iSplitR ; last first.
    iSplitL "Hf". *)
    iApply (wp_br_if_true_ctx with "Hf").
    done.
    iIntros "!> Hf".
(*    iApply wp_value.
    unfold IntoVal.
    by apply of_to_val.
    by instantiate (1 := λ x, (⌜ x = brV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
    iIntros (w) "[-> Hf]".
    iSimpl. *)
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
(*    iSplitL ; last done.
    unfold isStack.
    iDestruct "Hs" as "(% & % & Hl & Hbs)".
    iSplitR ; first done.
    iSplitR ; first done.
    iSplitL "Hn".
    iApply i32_wms => //.
    rewrite N.add_0_r.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small.
    iExact "Hn".
    unfold Wasm_int.Int32.max_unsigned in Hv.
    lia.
    iFrame. 
    iExists _. *)
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
  iApply (wp_get_local with "Hf").
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
  iApply (wp_get_local with "Hf").
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
  iApply (wp_get_local with "Hf") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, x = immV _).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (i32const (v + 4 + _ * 4))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate1 (i32const (v + 4 + _ * 4))).
  iApply wp_val_app. done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "Hf") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, x = immV _).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate3 (i32const (v + 4 + _ * 4))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate2 (i32const (v + 4 + _ * 4))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "Hf") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, x = immV _).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate4 (i32const (v + 4 + _ * 4))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf Hs".
  rewrite (separate2 (i32const (v + 4 + _ * 4))).
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
  rewrite (separate4 (i32const (v + 4 + _ * 4))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate3 (i32const (v + 4 + _ * 4))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "Hf") => /=.
  destruct (f_locs f0) ; inversion Hlocs0.
  simpl. done.
  by instantiate (1 := λ x, x = immV _).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate5 (i32const (v + 4 + _ * 4))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "HΦ Hf Htab Hcl".
  rewrite (separate2 (i32const (v + 4 + _ * 4))).
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
  instantiate (1 := λ x, (∃ v1, ⌜ x = immV _ ⌝ ∗ stackAll ys Φ ∗ Ψ y v1 ∗
                         N.of_nat j0↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]
                         Some a ∗
                         N.of_nat a↦[wf]cl )%I) ;
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
  rewrite (separate4 (i32const (v + 4 + _ * 4))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf H".
  rewrite (separate1 (i32const (v + 4 + _ * 4))).
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
  rewrite (separate3 (i32const (v + 4 + _ * 4))).
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
  iApply (wp_set_local with "Hf") => /=.
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
Qed.
          
                                        
    
    
End specs.


Section Client.

  (* Functions from the stack module are : 
     0 - new_stack
     1 - is_empty
     2 - is_full
     3 - pop
     4 - push 
     5 - map *)
  Definition main :=
    [ AI_basic (BI_call 0) ;
      AI_basic (BI_tee_local 0) ;
      i32const (-1) ;
      AI_basic (BI_relop T_i32 (Relop_i ROI_eq)) ;
      (* If new_stack failed, set global v0 to -1 and return *)
      AI_basic (BI_if (Tf [] []) [bi32const (-1) ; BI_set_global 0 ; BI_return] []) ;
      i32const 4 ;
      AI_basic (BI_get_local 0) ;
      AI_basic (BI_call 4) ;
      i32const 6 ;
      AI_basic (BI_get_local 0) ;
      AI_basic (BI_call 4) ;
      i32const 0 ;
      AI_basic (BI_get_local 0) ;
      AI_basic (BI_call 5) ;
      AI_basic (BI_get_local 0) ;
      AI_basic (BI_call 3) ;
      AI_basic (BI_get_local 0) ;
      AI_basic (BI_call 3) ;
      AI_basic (BI_binop T_i32 (Binop_i BOI_sub)) ;
      AI_basic (BI_set_global 0)
    ].

  Definition square :=
    [ AI_basic (BI_get_local 0) ;
      AI_basic (BI_get_local 0) ;
      AI_basic (BI_binop T_i32 (Binop_i BOI_mul)) ].

  Fixpoint basic_expr_of_expr es :=
    match es with
    | [] => Some []
    | AI_basic b :: q =>
        match basic_expr_of_expr q with
        | Some q' => Some (b :: q')
        | None => None
        end
    | _ :: q => None end.

  Fixpoint mk_basic_expr es :=
    match es with
    | [] => []
    | AI_basic b :: q => b :: mk_basic_expr q
    |  _ => [] end.


  Definition stack_module :=
    {|
      mod_types := [
        Tf [] [T_i32] ;
        Tf [T_i32] [T_i32] ;
        Tf [T_i32 ; T_i32] [] 
      ] ;
      mod_funcs := [
        {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [T_i32] ;
          modfunc_body := mk_basic_expr new_stack
        |} ;
        {|
          modfunc_type := Mk_typeidx 1 ;
          modfunc_locals := [] ;
          modfunc_body := mk_basic_expr is_empty
        |} ;
        {|
          modfunc_type := Mk_typeidx 1 ;
          modfunc_locals := [] ;
          modfunc_body := mk_basic_expr is_full
        |} ;
        {|
          modfunc_type := Mk_typeidx 1 ;
          modfunc_locals := [T_i32] ;
          modfunc_body := mk_basic_expr pop
        |} ;
        {|
          modfunc_type := Mk_typeidx 2 ;
          modfunc_locals := [T_i32] ;
          modfunc_body := mk_basic_expr push
        |} ;
        {|
          modfunc_type := Mk_typeidx 2 ;
          modfunc_locals := [T_i32 ; T_i32] ;
          modfunc_body := mk_basic_expr stack_map
        |}
      ] ;
      mod_tables := [ {| modtab_type := {| tt_limits := {| lim_min := 2%N ; lim_max := None |} ;
                                        tt_elem_type := ELT_funcref |} |} ] ;
      mod_mems := [
        {| lim_min := 0%N ; lim_max := None |}
      ] ;
      mod_globals := [] ;
      mod_elem := [] ;
      mod_data := [] ;
      mod_start := None ;
      mod_imports := [] ;
      mod_exports := [
        {|
          modexp_name := list_byte_of_string "new_stack" ;
          modexp_desc := MED_func (Mk_funcidx 0)
        |} ;
        {|
          modexp_name := list_byte_of_string "is_empty" ;
          modexp_desc := MED_func (Mk_funcidx 1)
        |} ;
        {|
          modexp_name := list_byte_of_string "is_full" ;
          modexp_desc := MED_func (Mk_funcidx 2)
        |} ;
        {|
          modexp_name := list_byte_of_string "pop" ;
          modexp_desc := MED_func (Mk_funcidx 3)
        |} ;
        {|
          modexp_name := list_byte_of_string "push" ;
          modexp_desc := MED_func (Mk_funcidx 4)
        |} ;
        {|
          modexp_name := list_byte_of_string "stack_map" ;
          modexp_desc := MED_func (Mk_funcidx 5)
        |} ;
        {|
          modexp_name := list_byte_of_string "table" ;
          modexp_desc := MED_table (Mk_tableidx 0)
        |}
      ]
    |}.

  Definition client_module :=
    {|
      mod_types := [ Tf [] [] ; Tf [] [T_i32] ; Tf [T_i32] [T_i32] ;
                     Tf [T_i32 ; T_i32] [] ] ;
      mod_funcs := [ {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [T_i32] ;
          modfunc_body := mk_basic_expr main
        |} ;
                     {|
                       modfunc_type := Mk_typeidx 2 ;
                       modfunc_locals := [] ;
                       modfunc_body := mk_basic_expr square
                     |} ] ;
      mod_tables := [] ; (* {| modtab_type := {| tt_limits := {| lim_min := 0%N ; lim_max := None |} ;
                                        tt_elem_type := ELT_funcref |} |} ] ; *)
      mod_mems := [] ;
      mod_globals := [ {| modglob_type := {| tg_t := T_i32 ;
                                            tg_mut := MUT_mut |} ;
                         modglob_init := [bi32const 0] |} ] ;
      mod_elem := [ {| modelem_table := Mk_tableidx 0 ;
                      modelem_offset := [bi32const 0] ;
                      modelem_init := [Mk_funcidx 7] |} ] ;
      mod_data := [] ;
      mod_start := Some {| modstart_func := Mk_funcidx 6 |} ;
      mod_imports := [
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "new_stack" ;
          imp_desc := ID_func 1
        |} ;
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "is_empty" ;
          imp_desc := ID_func 2
        |} ;
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "is_full" ;
          imp_desc := ID_func 2
        |} ;
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "pop" ;
          imp_desc := ID_func 2
        |} ;
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "push" ;
          imp_desc := ID_func 3
        |} ;
        {| imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "stack_map" ;
          imp_desc := ID_func 3
        |} ;
        {| imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "table" ;
          imp_desc := ID_table {| tt_limits := {| lim_min := 2%N ; lim_max := None |} ;
                                 tt_elem_type := ELT_funcref |} |}
      ] ;
      mod_exports := [
        {|
          modexp_name := list_byte_of_string "answer" ;
          modexp_desc := MED_global (Mk_globalidx 0)
        |}
      ]
    |}.


  Definition expts := [ET_func (Tf [] [T_i32]) ; ET_func (Tf [T_i32] [T_i32]);
                   ET_func (Tf [T_i32] [T_i32]) ; ET_func (Tf [T_i32] [T_i32]);
                       ET_func (Tf [T_i32 ; T_i32] []) ; ET_func (Tf [T_i32 ; T_i32] []) ;
                       ET_tab {| tt_limits := {| lim_min := 2%N ; lim_max := None |} ;
                                tt_elem_type := ELT_funcref |} ].

  Ltac bet_first f :=
    eapply bet_composition_front ; first eapply f => //=.
  
  Lemma module_typing_stack :
    module_typing stack_module [] expts.
  Proof.
    unfold module_typing => /=. 
    exists [Tf [] [T_i32] ; Tf [T_i32] [T_i32] ; Tf [T_i32] [T_i32] ;
       Tf [T_i32] [T_i32] ; Tf [T_i32 ; T_i32] [] ; Tf [T_i32 ; T_i32] [] ], [].
    repeat split => //.
    repeat (apply Forall2_cons ; repeat split => //) => /=.
    - bet_first bet_const.
      bet_first bet_grow_memory.
      bet_first bet_tee_local.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      by apply bet_const.
      bet_first bet_relop.
      by apply Relop_i32_agree.
      apply bet_if_wasm => /=.
      apply bet_const.
      bet_first bet_get_local.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      apply bet_const.
      bet_first bet_binop.
      apply Binop_i32_agree.
      bet_first bet_tee_local.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32]).
      apply bet_weakening.
      apply bet_get_local => //.
      simpl.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32 ; _]).
      apply bet_weakening.
      apply bet_const.
      simpl.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 [_ ; _]). 
      apply bet_weakening.
      apply bet_binop.
      apply Binop_i32_agree.
      bet_first bet_store. 
      apply bet_get_local => //.
    - bet_first bet_get_local.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32]).
      apply bet_weakening.
      apply bet_const.
      bet_first bet_binop.
      apply Binop_i32_agree.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32]).
      apply bet_weakening.
      apply bet_get_local => //.
      eapply bet_composition_front.
      apply bet_weakening.
      apply bet_load => //.
      apply bet_relop.
      apply Relop_i32_agree.
    - bet_first bet_const.
      unfold typeof.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32]).
      apply bet_weakening.
      apply bet_const.
      unfold typeof => /=.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32 ; T_i32]).
      apply bet_weakening.
      apply bet_get_local => //.
      eapply bet_composition_front.
      apply bet_weakening.
      apply bet_load => //.
      simpl.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32;_;_]).
      apply bet_weakening.
      apply bet_const.
      simpl.
      eapply bet_composition_front.
      rewrite (separate2 T_i32 T_i32 [_;_]).
      apply bet_weakening.
      apply bet_binop.
      apply Binop_i32_agree.
      apply bet_select.
    - bet_first bet_get_local. 
      bet_first bet_load.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32]).
      apply bet_weakening.
      apply bet_const.
      bet_first bet_binop.
      apply Binop_i32_agree.
      bet_first bet_tee_local. 
      bet_first bet_load.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32]).
      apply bet_weakening.
      apply bet_get_local => //.
      simpl.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32 ; _]).
      apply bet_weakening.
      apply bet_get_local => //.
      simpl.
      rewrite (separate1 T_i32 [_;_]).
      rewrite - (app_nil_r [T_i32]).
      apply bet_weakening.
      apply bet_store => //.
    - bet_first bet_get_local. 
      bet_first bet_load.
      bet_first bet_tee_local.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32]).
      apply bet_weakening.
      apply bet_get_local => //.
      bet_first bet_store.
      bet_first bet_get_local.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32]).
      apply bet_weakening.
      apply bet_get_local => //.
      simpl.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32 ; _]).
      apply bet_weakening.
      apply bet_const.
      unfold typeof => /=.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 [_;_]).
      apply bet_weakening.
      apply bet_binop.
      apply Binop_i32_agree.
      apply bet_store => //.
    - bet_first bet_get_local.
      bet_first bet_load.
      bet_first bet_set_local.
      bet_first bet_get_local.
      eapply bet_composition_front.
      rewrite (separate1 T_i32).
      apply bet_weakening.
      apply bet_const.
      bet_first bet_binop.
      apply Binop_i32_agree.
      bet_first bet_set_local.
      apply bet_block.
      apply bet_loop => /=.
      bet_first bet_get_local.
      eapply bet_composition_front.
      rewrite (separate1 T_i32).
      apply bet_weakening.
      apply bet_get_local => //.
      bet_first bet_relop.
      apply Relop_i32_agree.
      rewrite - (app_nil_l [T_i32]).
      bet_first bet_br_if.
      bet_first bet_get_local.
      eapply bet_composition_front.
      rewrite (separate1 T_i32).
      apply bet_weakening.
      apply bet_get_local => //.
      eapply bet_composition_front.
      simpl ; rewrite (separate2 T_i32).
      apply bet_weakening.
      apply bet_get_local => //.
      eapply bet_composition_front.
      simpl ; rewrite (separate2 T_i32 _ [_]).
      apply bet_weakening.
      apply bet_load => //.
      eapply bet_composition_front.
      simpl ; rewrite (separate3 T_i32 T_i32 T_i32 []).
      apply bet_weakening.
      apply bet_get_local => //.
      eapply bet_composition_front.
      simpl ; rewrite (separate2 T_i32 T_i32 [_;_]).
      apply bet_weakening.
      rewrite (separate1 T_i32 [_]).
      apply bet_call_indirect => //=.
      eapply bet_composition_front.
      simpl ; rewrite (separate1 T_i32 [_;_]).
      apply bet_weakening.
      apply bet_store => //.
      eapply bet_composition_front.
      apply bet_weakening.
      apply bet_const.
      bet_first bet_binop.
      apply Binop_i32_agree.
      bet_first bet_set_local.
      rewrite - (app_nil_l []).
      apply bet_br => //. 
    - unfold module_export_typing.
      repeat (apply Forall2_cons ; repeat split => //) => //=.
  Qed.


  Lemma module_typing_client :
    module_typing client_module expts [ET_glob {| tg_t := T_i32 ; tg_mut := MUT_mut |} ].
  Proof.
    unfold module_typing => /=.
    exists [ Tf [] [] ; Tf [T_i32] [T_i32] ],
      [ {| tg_t := T_i32 ; tg_mut := MUT_mut |} ].
    repeat split => //.
    repeat (apply Forall2_cons ; repeat split => //) => /=.
    - bet_first bet_call.
      bet_first bet_tee_local.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      apply bet_const.
      bet_first bet_relop.
      apply Relop_i32_agree.
      bet_first bet_if_wasm.
      bet_first bet_const.
      bet_first bet_set_global.
      replace (Tf [] []) with (Tf (app ([] : list value_type) []) []) ; last done.
      eapply bet_return => //.
      apply bet_empty.
      bet_first bet_const.
      unfold typeof.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      by apply bet_get_local.
      bet_first bet_call.
      bet_first bet_const.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      by apply bet_get_local.
      bet_first bet_call.
      bet_first bet_const.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      by apply bet_get_local.
      bet_first bet_call.
      bet_first bet_get_local.
      bet_first bet_call.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      by apply bet_get_local.
      eapply bet_composition_front.
      apply bet_weakening.
      by apply bet_call.
      bet_first bet_binop.
      apply Binop_i32_agree.
      by eapply bet_set_global.
    - bet_first bet_get_local.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      by apply bet_get_local.
      apply bet_binop.
      apply Binop_i32_agree.
    - apply Forall2_cons.
      repeat split => //.
      by apply bet_const.
    - unfold module_elem_typing.
      apply Forall_cons.
      repeat split => //.
      apply bet_const.
    - unfold module_import_typing.
      repeat (apply Forall2_cons ; repeat split => //) => //=.
    - apply Forall2_cons.
      repeat split => //.
  Qed.

  Definition module_decls := [ stack_module ; client_module ].
  Definition stack_instantiate :=
    [ ID_instantiate [0%N ; 1%N ; 2%N ; 3%N ; 4%N ; 5%N ; 6%N] 0 [] ;
      ID_instantiate [7%N] 1 [0%N ; 1%N ; 2%N ; 3%N ; 4%N ; 5%N ; 6%N] ].

  Notation " n ↪[vis]{ q } v" := (ghost_map_elem (V := module_export) visGName n q v%V)
                           (at level 20, q at level 5, format " n ↪[vis]{ q } v") .
  Notation " n ↪[vis] v" := (ghost_map_elem (V := module_export) visGName n (DfracOwn 1) v%V)
                          (at level 20, format " n ↪[vis] v").
  
  Notation " n ↪[mods]{ q } v" := (ghost_map_elem (V := module) msGName n q v%V)
                           (at level 20, q at level 5, format " n ↪[mods]{ q } v") .
  Notation " n ↪[mods] v" := (ghost_map_elem (V := module) msGName n (DfracOwn 1) v%V)
                               (at level 20, format " n ↪[mods] v").

(*  Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP es @ NotStuck ; ⊤ (*CTX_EMPTY*) {{ v, Φ v }})%I (at level 50). *)

 Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ,  !logrel_na_invs Σ}.

  Definition stack_instance idfs m t :=
    {|
      inst_types := [Tf [] [T_i32] ; Tf [T_i32] [T_i32] ; Tf [T_i32 ; T_i32] []] ;
      inst_funcs := idfs ;
      inst_tab := [t] ;
      inst_memory := [m] ;
      inst_globs := []
    |}.


(*   Definition finst (f : function_closure) :=
    match f with
    | FC_func_native inst _ _ _ => Some inst
    | _ => None end. *)

(*  Class logrel_na_invs Σ :=
  {
    logrel_na_invG :> na_invG Σ;
    logrel_nais : na_inv_pool_name;
  }. *)
(*
Definition wf : string := "wfN".
Definition wf0 : string := "wf0N".
Definition wf1 : string := "wf1N".
Definition wf2 : string := "wf2N".
Definition wf3 : string := "wf3N".
Definition wlen : string := "wlenN".
Definition wfN : namespace := nroot .@ wf.
Definition wf0N : namespace := nroot .@ wf0. 
Definition wf1N : namespace := nroot .@ wf1.
Definition wf2N : namespace := nroot .@ wf2.
Definition wf3N : namespace := nroot .@ wf3.
Definition wlenN : namespace := nroot .@ wlen. *)

Definition spec0 idf0 i0 l0 f0 (isStack : Z -> seq.seq i32 -> iPropI Σ)  nextStackAddrIs :=
  (∀ f addr, {{{ ↪[frame] f ∗
                  N.of_nat idf0 ↦[wf] FC_func_native i0 (Tf [] [T_i32]) l0 f0 ∗
                  nextStackAddrIs addr ∗
                  ⌜ (Wasm_int.Int32.modulus - 1)%Z <> Wasm_int.Int32.Z_mod_modulus (ssrnat.nat_of_bin (N.of_nat addr `div` page_size)) ⌝ ∗
                                                                                  ⌜ (N.of_nat addr + 4 < Z.to_N (two_power_nat 32))%N ⌝ ∗
                                                                                  ⌜ (page_size | N.of_nat addr)%N ⌝  }}}
               [AI_invoke idf0]
               {{{  v, (∃ (k : Z), ⌜ v = immV [value_of_int k] ⌝ ∗
                                              (⌜ (k = -1)%Z ⌝  ∗
                                                 nextStackAddrIs addr ∨
                                                 ⌜ (0 <= k)%Z /\ (k + Z.of_N page_size <= two32)%Z ⌝ ∗
                                                                                             isStack k []  ∗
                                                                                             nextStackAddrIs (addr + N.to_nat page_size) ))  ∗
                                                                                                                                             N.of_nat idf0 ↦[wf] FC_func_native i0 (Tf [] [T_i32]) l0 f0 ∗
                                                                                                                                             ↪[frame] f }}} )%I.

Definition spec1 idf1 i1 l1 f1 (isStack : Z -> seq.seq i32 -> iPropI Σ) :=
  (∀ v s f, {{{ ↪[frame] f  ∗
                 N.of_nat idf1 ↦[wf] FC_func_native i1 (Tf [T_i32] [T_i32]) l1 f1 ∗
                 ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - length s * 4)%Z ⌝ ∗ 
                 isStack v s }}}
              [i32const v ; AI_invoke idf1]
              {{{ w, (∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s ∗
                                      ⌜ (k = 1 /\ s = []) \/
                             (k = 0 /\ s <> []) ⌝) ∗
                                                 N.of_nat idf1 ↦[wf] FC_func_native i1 (Tf [T_i32] [T_i32]) l1 f1 ∗ 
                                                 ↪[frame] f}}})%I.

Definition spec2 idf2 i2 l2 f2 (isStack : Z -> seq.seq i32 -> iPropI Σ) :=
  (∀ v s f, {{{ ↪[frame] f ∗
                 N.of_nat idf2 ↦[wf] FC_func_native i2 (Tf [T_i32] [T_i32]) l2 f2 ∗
                 ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - length s * 4 )%Z ⌝ ∗ 
                 isStack v s }}}
              [i32const v ; AI_invoke idf2]
              {{{ w, (∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗
                                      isStack v s ∗
                                      ⌜ k = 1 \/ (length s < two14 - 1)%Z ⌝) ∗
                                                                            N.of_nat idf2 ↦[wf] FC_func_native i2 (Tf [T_i32] [T_i32]) l2 f2 ∗ 
                                                                            ↪[frame] f }}})%I.

Definition spec3 idf3 i3 l3 f3 (isStack : Z -> seq.seq i32 -> iPropI Σ) :=
  (∀ a v s f, {{{ ↪[frame] f ∗
                   N.of_nat idf3 ↦[wf] FC_func_native i3 (Tf [T_i32] [T_i32]) l3 f3
                   ∗ ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - S (length s) * 4 )%Z ⌝
                   ∗ isStack v (a :: s) }}}
                [i32const v ; AI_invoke idf3]
                {{{ w, ⌜ w = immV [VAL_int32 a] ⌝ ∗
                                  isStack v s ∗
                                  N.of_nat idf3 ↦[wf] FC_func_native i3 (Tf [T_i32] [T_i32]) l3 f3 ∗
                                  ↪[frame] f }}})%I.

Definition spec4 idf4 i4 l4 f4 isStack :=
  (∀ a v s f, {{{ ↪[frame] f ∗
                   N.of_nat idf4 ↦[wf] FC_func_native i4 (Tf [T_i32 ; T_i32] []) l4 f4 
                   ∗ ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - S (length s) * 4 )%Z ⌝
                   ∗ ⌜ (length s < two14 - 1)%Z ⌝
                   ∗ isStack v s }}}
                [ AI_basic (BI_const (VAL_int32 a)) ; i32const v ; AI_invoke idf4 ]
                {{{ w, ⌜ w = immV [] ⌝ ∗
                                  isStack v (a :: s) ∗
                                  N.of_nat idf4 ↦[wf] FC_func_native i4 (Tf [T_i32 ; T_i32] []) l4 f4 ∗
                                  ↪[frame] f }}})%I.

Definition spec5 idf5 i5 l5 f5 (isStack : Z -> seq.seq i32 -> iPropI Σ) j0 :=
  (∀ (f0 : frame) (f : i32) (v : Z) (s : seq.seq i32) a cl
      (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) ,
      {{{  ↪[frame] f0 ∗
            N.of_nat idf5 ↦[wf] FC_func_native i5 (Tf [T_i32 ; T_i32] []) l5 f5 ∗
            ⌜ (0 <= v)%Z ⌝ ∗
            ⌜ (v + 4 + length s * 4 ≤ Wasm_int.Int32.max_unsigned)%Z ⌝ ∗
            isStack v s ∗
            stackAll s Φ ∗
            N.of_nat j0 ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
            (N.of_nat a) ↦[wf] cl ∗
            ⌜ match cl with FC_func_native _ t _ _ => t | FC_func_host t _ => t end
         = Tf [T_i32] [T_i32] ⌝ ∗ 
              (∀ (u : i32) (fc : frame),
                   {{{ Φ u ∗
                      ⌜ i5 = f_inst fc ⌝ ∗
                       ↪[frame] fc ∗
                       N.of_nat j0 ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
                       (N.of_nat a) ↦[wf] cl
                  }}}
                  [ AI_basic (BI_const (VAL_int32 u)) ;
                    AI_invoke a ]
                  {{{ w, (∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)
                           ∗ ↪[frame] fc
                           ∗ N.of_nat j0 ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) 
                           ∗ (N.of_nat a) ↦[wf] cl }}}
                  )  }}}
    [ AI_basic (BI_const (VAL_int32 f)) ; i32const v ; AI_invoke idf5 ]
    {{{ w, ⌜ w = immV [] ⌝ ∗
           (∃ s', isStack v s' ∗ stackAll2 s s' Ψ) ∗
           N.of_nat idf5 ↦[wf] FC_func_native i5 (Tf [T_i32 ; T_i32] []) l5 f5 ∗
           ↪[frame] f0
    }}})%I.


Lemma instantiate_stack_spec (s : stuckness) E (hv0 hv1 hv2 hv3 hv4 hv5 hv6 : module_export) :
  (* Knowing 0%N holds the stack module… *)
  0%N ↪[mods] stack_module -∗
     (* … and we own the vis 0%N thru 4%N … *)
     ([∗ list] k↦hvk ∈ [hv0 ; hv1 ; hv2 ; hv3 ; hv4 ; hv5 ; hv6], N.of_nat k ↪[vis] hvk) -∗
     (* … instantiating the stack-module (by lazyness, this is expressed here with
        a take 1 in order to avoir rewriting the instantiation), yields the following : *)
     WP ((take 1 stack_instantiate, []) : host_expr)
     @ s ; E
             {{ v,
                    
                 (* 0%N still owns the stack_module *)
                 0%N ↪[mods] stack_module ∗ 
                  ∃ (idf0 idf1 idf2 idf3 idf4 idf5 idt : nat)
                    (name0 name1 name2 name3 name4 name5 name6 : name)
                    (f0 f1 f2 f3 f4 f5 : list basic_instruction)
                    (i0 i1 i2 i3 i4 i5 : instance)
                    (l0 l1 l2 l3 l4 l5 : list value_type)
                    tab 
                    (isStack : Z -> seq.seq i32 -> iPropI Σ)
                    (nextStackAddrIs : nat -> iPropI Σ), 
                    (* Our exports are in the vis 0%N thru 4%N. Note that everything is 
                       existantially quantified. In fact, all the f_i, i_i and l_i 
                       could be given explicitely, but we quantify them existantially 
                       to show modularity : we do not care what the functions are, 
                       we only care about their spec (see next comment). This also
                       makes this lemma more readable than if we stated explicitely all
                       the codes of the functions *)
                    let inst_vis := (map (λ '(name, idf),
                                                 {| modexp_name := name ;
                                                   modexp_desc := MED_func (Mk_funcidx idf)
                                                 |}) [(name0, idf0) ; (name1, idf1) ;
                                                      (name2, idf2) ; (name3, idf3) ;
                                                      (name4, idf4) ; (name5, idf5) ])
                                        ++ [ {| modexp_name := name6 ;
                                               modexp_desc := MED_table (Mk_tableidx idt) |} ]
                    in 
                    let inst_map := fold_left (λ fs '(idf,i,t,l,f),
                                                <[ N.of_nat idf := FC_func_native i t l f ]> fs)
                                              (rev [(idf0, i0, Tf [] [T_i32], l0, f0) ;
                                               (idf1, i1, Tf [T_i32] [T_i32], l1, f1) ;
                                                    (idf2, i2, Tf [T_i32] [T_i32], l2, f2) ;
                                                    (idf3, i3, Tf [T_i32] [T_i32], l3, f3) ;
                                                    (idf4, i4, Tf [T_i32 ; T_i32] [], l4, f4) ;
                                              (idf5, i5, Tf [T_i32 ; T_i32] [], l5, f5)])
                                              ∅ in 
                    (* These two import functions state that all [vis] and [wf] point 
                       to the correct exports/functions, i.e. a client will be able 
                       to successfully import them *)
                    import_resources_host [0%N; 1%N; 2%N; 3%N; 4%N ; 5%N ; 6%N] inst_vis ∗
                    import_resources_wasm_typecheck inst_vis expts inst_map
                    (<[ N.of_nat idt := tab ]> ∅) 
                    ∅ ∅ ∗
                    ⌜ length tab.(table_data) > 1 ⌝ ∗ 
                    (* We own a token that hides ressources needed for the new_stack function *)
                    nextStackAddrIs 0 ∗
                    (* And finally we have specs for all our exports : *)
                    (* Spec for new_stack (call 0) *)
                    spec0 idf0 i0 l0 f0 isStack nextStackAddrIs ∗
                    (* Spec for is_empty (call 1) *)
                    spec1 idf1 i1 l1 f1 isStack ∗
                    (* Spec for is_full (call 2) *)
                    spec2 idf2 i2 l2 f2 isStack ∗
                    (* Spec for pop (call 3) *)
                    spec3 idf3 i3 l3 f3 isStack ∗
                    (* Spec for push (call 4) *)
                    spec4 idf4 i4 l4 f4 isStack ∗
                    (* Spec of stack_map (call 5) *)
                    spec5 idf5 i5 l5 f5 isStack idt
                                          
             }}.
  Proof.
    iIntros "Hmod (Hhv0 & Hhv1 & Hhv2 & Hhv3 & Hhv4 & Hhv5 & Hhv6 & _)".
    iApply (weakestpre.wp_strong_mono s _ E
             with "[Hmod Hhv0 Hhv1 Hhv2 Hhv3 Hhv4 Hhv5 Hhv6]") => //.
    iApply (instantiation_spec_operational_no_start
             with "[Hmod Hhv0 Hhv1 Hhv2 Hhv3 Hhv4 Hhv5 Hhv6]") ;
      try exact module_typing_stack => //.
    - by unfold stack_module.
    - unfold module_restrictions => /=.
      repeat split => //=.
      exists [] => //.
      exists [] => //.
      exists [] => //.
    - unfold instantiation_resources_pre.
      iSplitL "Hmod" ; first done.
      repeat iSplit.
    - by unfold import_resources_host.
    - iPureIntro. apply dom_empty.
    - iPureIntro. apply dom_empty.
    - iPureIntro. apply dom_empty.
    - iPureIntro. apply dom_empty.
(*    - do 4 instantiate (1 := gmap_empty).
      by unfold import_resources_wasm_typecheck. *)
    - done.
    - unfold export_ownership_host.
      iSplitL "Hhv0".
      by iExists _.
      iSplitL "Hhv1".
      by iExists _.
      iSplitL "Hhv2".
      by iExists _.
      iSplitL "Hhv3".
      by iExists _.
      iSplitL "Hhv4".
      by iExists _.
      iSplitL "Hhv5".
      by iExists _.
      iSplitL "Hhv6".
      by iExists _.
      done.
      done.
      iPureIntro.
      unfold module_elem_bound_check_gmap.
      simpl.
      done.
      iPureIntro.
      unfold module_data_bound_check_gmap.
      simpl.
      done.
    - iIntros (v) "(Hmod & Himphost & Himpwasm & Hinst)".
      iDestruct "Hinst" as (inst g_inits t_inits m_inits) "(%Hinst & %Hival & Hexpwasm & Hexphost)".
      destruct Hinst as (Hinsttype & Hinstfunc & Hinsttab & Hinstmem & Hinstglob).
      unfold module_inst_resources_wasm, module_export_resources_host => /=.
      destruct inst => /=.
      iDestruct "Hexpwasm" as "(Hexpwf & Hexpwt & Hexpwm & Hexpwg)".
      unfold module_inst_resources_func, module_inst_resources_glob,
        module_inst_resources_tab, module_inst_resources_mem => /=.
      unfold big_sepL2 => /=.
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf Hexpwf]".
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf0 Hexpwf]".
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf1 Hexpwf]".
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf2 Hexpwf]".
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf3 Hexpwf]".
      destruct inst_funcs as [| ? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf4 Hexpwf]".
      destruct inst_funcs ; last done.
      destruct inst_tab ; first done.
      iDestruct "Hexpwt" as "[Htab Hexpwt]".
      destruct inst_tab ; last done.
      destruct inst_memory as [|m inst_memory] ; first done.
      iDestruct "Hexpwm" as "[Hexpwm ?]".
      destruct inst_memory ; last done.
      iDestruct "Hexpwm" as "(Hexpwm & Hmemlength & Hmemlim)".
      destruct inst_globs ; last done.
      iDestruct "Hexphost" as "(Hexp0 & Hexp1 & Hexp2 & Hexp3 & Hexp4 & Hexp5 & Hexp6 & _)".
      iDestruct "Hexp0" as (name0) "Hexp0".
      iDestruct "Hexp1" as (name1) "Hexp1".
      iDestruct "Hexp2" as (name2) "Hexp2".
      iDestruct "Hexp3" as (name3) "Hexp3".
      iDestruct "Hexp4" as (name4) "Hexp4".
      iDestruct "Hexp5" as (name5) "Hexp5".
      iDestruct "Hexp6" as (name6) "Hexp6".
      simpl in * ; subst.
      iSplitL "Hmod" ; first done.
      iExists f, f0, f1, f2, f3, f4, t.
      iExists name0, name1, name2, name3, name4, name5, name6.
      do 3 iExists _, _, _, _, _, _.
      iExists _.
      iExists (λ a b, isStack a b m).
      iExists (λ n, (N.of_nat m↦[wmlength] N.of_nat n)%I).
      iDestruct (mapsto_frac_ne with "Hf Hf0") as "%H01" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf Hf1") as "%H02" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf Hf2") as "%H03" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf Hf3") as "%H04" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf Hf4") as "%H05" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf0 Hf1") as "%H12" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf0 Hf2") as "%H13" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf0 Hf3") as "%H14" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf0 Hf4") as "%H15" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf1 Hf2") as "%H23" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf1 Hf3") as "%H24" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf1 Hf4") as "%H25" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf2 Hf3") as "%H34" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf2 Hf4") as "%H35" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf3 Hf4") as "%H45" ; first by eauto.
      (*  assert (forall a b, N.of_nat a <> N.of_nat b -> a <> b) as Hneq.
      { intros ; intro. by subst. }
      apply Hneq in H01, H02, H03, H04, H05, H12, H13, H14, H15, H23, H24, H25, H34, H35, H45. *)
(*      iMod (na_inv_alloc logrel_nais _ wfN with "[Hf]") as "#Hinvf".
      by iApply (later_intro with "Hf").
      iMod (na_inv_alloc logrel_nais _ wf0N with "[Hf0]") as "#Hinvf0".
      by iApply (later_intro with "Hf0").
      iMod (na_inv_alloc logrel_nais _ wf1N with "[Hf1]") as "#Hinvf1".
      by iApply (later_intro with "Hf1").
      iMod (na_inv_alloc logrel_nais _ wf2N with "[Hf2]") as "#Hinvf2".
      by iApply (later_intro with "Hf2").
      iMod (na_inv_alloc logrel_nais _ wf3N with "[Hf3]") as "#Hinvf3".
      by iApply (later_intro with "Hf3"). *)
(*      iMod (na_inv_alloc logrel_nais _ wlenN with "[Hmemlength]") as "#Hinvlen".
      instantiate (1 := ∃ len, N.of_nat m↦[wmlength] len ∗ ⌜  
                                        
      by iApply (later_intro with "Hmemlength"). *)
      iSplitL "Hexp0 Hexp1 Hexp2 Hexp3 Hexp4 Hexp5 Hexp6".
      unfold import_resources_host.
      iFrame. by iModIntro.
      iSplitL "Hf Hf0 Hf1 Hf2 Hf3 Hf4 Htab".
      unfold import_resources_wasm_typecheck => /=.
(*      iMod (na_inv_acc with "Hinvf Hown") as "(Hf & Hown & Hclosef)".
      admit. done.
      iMod (na_inv_acc with "Hinvf0 Hown") as "(Hf0 & Hown & Hclosef0)".
      admit. admit.
      iMod (na_inv_acc with "Hinvf1 Hown") as "(Hf1 & Hown & Hclosef1)".
      admit. admit.
      iMod (na_inv_acc with "Hinvf2 Hown") as "(Hf2 & Hown & Hclosef2)".
      admit. admit.
      iMod (na_inv_acc with "Hinvf3 Hown") as "(Hf3 & Hown & Hclosef3)".
      admit. admit. *)
     
      iSplitR.
    - iPureIntro.
      simpl.
      repeat rewrite dom_insert.
      done.
    - iSplitL "Hf".
      iExists _.
      iFrame.
      iPureIntro.
      rewrite lookup_insert.
      split => //.
      iSplitL "Hf0".
      iExists _ ; iFrame.
      iPureIntro.
      rewrite lookup_insert_ne ; last assumption.
      rewrite lookup_insert.
      split => //.
      iSplitL "Hf1".
      iExists _ ; iFrame.
      iPureIntro.
      do 2 (rewrite lookup_insert_ne ; last assumption).
      rewrite lookup_insert.
      split => //.
      iSplitL "Hf2".
      iExists _ ; iFrame.
      iPureIntro.
      do 3 (rewrite lookup_insert_ne ; last assumption).
      rewrite lookup_insert.
      split => //.
      iSplitL "Hf3".
      iExists _ ; iFrame.
      iPureIntro.
      do 4 (rewrite lookup_insert_ne ; last assumption).
      rewrite lookup_insert.
      split => //.
      iSplitL "Hf4".
      iExists _ ; iFrame.
      iPureIntro.
      do 5 (rewrite lookup_insert_ne ; last assumption).
      rewrite lookup_insert.
      split => //.
      iSplitL ; last done.
      iExists _, _ ; iFrame.
      iPureIntro.
      rewrite lookup_insert.
      split => //.
      iSplitR.
      iPureIntro.
      simpl.
      lia.
      iSplitL "Hmemlength" ; first done.
    - iSplitR. iIntros "!>" (fr addr Φ) "!> (Hf & Hwf & Hlen & % & % & %) HΦ".
      iApply wp_wand_r.
      iSplitR "HΦ".
      { (*iApply (wp_call with "Hf") => //=.
        iIntros "!> Hf". *)
        (* iApply wp_fupd. Search "wp_fup".
        iMod (na_inv_acc with "Hinvf Hown") as "(Hf & Hown & Hclosef)".
        admit. done. *)
        rewrite - (app_nil_l [AI_invoke f]).
        iApply (wp_invoke_native with "Hf Hwf") => //.
        iIntros "!> [Hf Hf0]".
        iSimpl.
        iApply (wp_frame_bind with "Hf").
        iIntros "Hf".
        rewrite - (app_nil_l [AI_basic _]).
        iApply (wp_block with "Hf") => //.
        iIntros "!> Hf".
        iApply (wp_label_bind with "[Hlen Hf Hf0]") ; last first.
        iPureIntro.
        unfold lfilled, lfill => /=.
        instantiate (5 := []) => /=.
        rewrite app_nil_r.
        done.
(*      iDestruct spec_new_stack as "#Hsp".
       unfold new_stack.
        replace (i32const 1) with (AI_basic (BI_const (VAL_int32 (Wasm_int.Int32.repr 1)))) ;
          last done.
        replace (i32const (-1)) with (AI_basic (BI_const (VAL_int32 (Wasm_int.Int32.repr (-1))))) ; last done. *)
        iApply (spec_new_stack with "[Hlen Hf]").
        iFrame.
        repeat iSplit ; iPureIntro => //=.
        lia.
        iIntros (w) "H".
        iDestruct "H" as (k) "(-> & H & Hf)" => /=.
        iDestruct "Hf" as (f5) "[Hf %Hf4]".
        iApply (wp_wand_ctx with "[H Hf Hf0]").
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        rewrite app_nil_r app_nil_l.
        iApply wp_value => //=.
        unfold IntoVal.
        apply of_to_val => //.
        iFrame.
        instantiate (1 := λ v, (⌜ v = immV [value_of_int k] ⌝ ∗
                                           (⌜k = (-1)%Z⌝ ∗N.of_nat m↦[wmlength]N.of_nat addr ∨  ⌜ (0 ≤ k)%Z ∧ (k + Z.pos (64 * 1024) ≤ two32)%Z⌝ ∗ isStack k [] m ∗
                                                                                             N.of_nat m↦[wmlength](N.of_nat addr + page_size)%N) ∗
                                                                                             N.of_nat f↦[wf]FC_func_native
                           {|
                             inst_types :=
                               [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
                             inst_funcs := [f; f0; f1; f2; f3;f4];
                             inst_tab := [t];
                             inst_memory := [m];
                             inst_globs := []
                           |} (Tf [] [T_i32]) [T_i32]
                           [BI_const (VAL_int32 (Wasm_int.Int32.repr 1));
                           BI_grow_memory; BI_tee_local 0;
                           BI_const (VAL_int32 (Wasm_int.Int32.repr (-1)));
                           BI_relop T_i32 (Relop_i ROI_eq);
                           BI_if (Tf [] [T_i32]) [bi32const (-1)]
                             [BI_get_local 0; bi32const 65536;
                             BI_binop T_i32 (Binop_i BOI_mul); 
                             BI_tee_local 0; BI_get_local 0; 
                             bi32const 4; BI_binop T_i32 (Binop_i BOI_add);
                             BI_store T_i32 None N.zero N.zero; 
                              BI_get_local 0]])%I).
        iSimpl.
        iFrame.
        done.
        iIntros (w) "[(-> & H &  Hf0) Hf]".
        iExists _.
        iFrame.
        iIntros "Hf".
        iSimpl.         
        iApply (wp_frame_value with "Hf") => //.
        iNext.
        instantiate (1 := λ v, ((∃ k, ⌜ v = immV [value_of_int k] ⌝ ∗
                                           (⌜k = (-1)%Z⌝ ∗ N.of_nat m↦[wmlength]N.of_nat addr ∨  ⌜ (0 ≤ k)%Z ∧ (k + Z.pos (64 * 1024) ≤ two32)%Z⌝ ∗ isStack k [] m ∗
                                                                                             N.of_nat m↦[wmlength](N.of_nat addr + page_size)%N)) ∗
                                                                                             N.of_nat f↦[wf]FC_func_native
                           {|
                             inst_types :=
                               [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
                             inst_funcs := [f; f0; f1; f2; f3; f4];
                             inst_tab := [t];
                             inst_memory := [m];
                             inst_globs := []
                           |} (Tf [] [T_i32]) [T_i32]
                           [BI_const (VAL_int32 (Wasm_int.Int32.repr 1));
                           BI_grow_memory; BI_tee_local 0;
                           BI_const (VAL_int32 (Wasm_int.Int32.repr (-1)));
                           BI_relop T_i32 (Relop_i ROI_eq);
                           BI_if (Tf [] [T_i32]) [bi32const (-1)]
                             [BI_get_local 0; bi32const 65536;
                             BI_binop T_i32 (Binop_i BOI_mul); 
                             BI_tee_local 0; BI_get_local 0; 
                             bi32const 4; BI_binop T_i32 (Binop_i BOI_add);
                             BI_store T_i32 None N.zero N.zero; 
                              BI_get_local 0]])%I).
        iSimpl.
        iFrame.
        iExists k.
        iFrame.
        done. }
      iIntros (w) "[[H Hf0] Hf]".
      iApply "HΦ".
      iFrame.
      iDestruct "H" as (k) "[-> [[-> Hlen] | (% & Hs & Hlen)]]".
      iExists (-1)%Z.
      iSplit ; first done.
      iLeft.
      by iFrame.
      iExists k.
      iSplit ; first done.
      iRight.
      unfold page_size.
      replace (N.of_nat addr + 64 * 1024)%N with
        (N.of_nat (addr + Pos.to_nat (64 * 1024))) ;
        last lia.
      by iFrame.
    - iSplitR.
      iIntros "!>" (v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Hlen & %Hdiv & Hlen) HΦ".
      iApply wp_wand_r.
      iSplitR "HΦ".
      { rewrite (separate1 (i32const _) _).
        rewrite - (app_nil_r [AI_basic _]).
(*        iApply wp_wasm_empty_ctx.
        iApply wp_base_push => //.
        iApply (wp_call_ctx with "Hf") => //=.
        iIntros "!> Hf".
        iApply wp_base_pull.
        rewrite app_nil_r.
        iApply wp_wasm_empty_ctx. *)
        iApply (wp_invoke_native with "Hf Hf0") => //.
        iIntros "!> [Hf Hf0]".
        iSimpl.
        iApply (wp_frame_bind with "Hf").
        iIntros "Hf".
        rewrite - (app_nil_l [AI_basic _]).
        iApply (wp_block with "Hf") => //.
        iIntros "!> Hf".
        iApply (wp_label_bind with "[Hlen Hf Hf0]") ; last first.
        iPureIntro.
        unfold lfilled, lfill => /=.
        instantiate (5 := []) => /=.
        rewrite app_nil_r.
        done.
        iApply (spec_is_empty with "[Hlen Hf]").
        iFrame.
        repeat iSplit ; iPureIntro => //=.
        lia.
        by destruct H.
        iIntros (w) "H".
        iDestruct "H" as (k) "(-> & H & %Hk & Hf)" => /=.
        iDestruct "Hf" as (f5) "[Hf %Hf4]".
        iApply (wp_wand_ctx with "[H Hf Hf0]").
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        rewrite app_nil_r app_nil_l.
        iApply wp_value => //=.
        unfold IntoVal.
        apply of_to_val => //.
        iFrame.
        instantiate (1 := λ v, (⌜ v = immV [value_of_int k] ⌝ ∗
                                           isStack v0 s0 m ∗
                                            N.of_nat f0↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3 ; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32] [T_i32]) []
                            [BI_get_local 0;
                            BI_const (VAL_int32 (Wasm_int.Int32.repr 4));
                            BI_binop T_i32 (Binop_i BOI_add); 
                            BI_get_local 0; BI_load T_i32 None N.zero N.zero;
                            BI_relop T_i32 (Relop_i ROI_eq)])%I).
        iSimpl.
        iFrame.
        done.
        iIntros (w) "[(-> & H &  Hf0) Hf]".
        iExists _.
        iFrame.
        iIntros "Hf".
        iSimpl.         
        iApply (wp_frame_value with "Hf") => //.
        iNext.
        instantiate (1 := λ v, ((∃ k, ⌜ v = immV [value_of_int k] ⌝ ∗
                                                 ⌜ k = 1 /\ s0 = [] \/ k = 0 /\ s0 <> [] ⌝) ∗
                                                                                        isStack v0 s0 m ∗
                                                                                        N.of_nat f0↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32] [T_i32]) []
                            [BI_get_local 0;
                            BI_const (VAL_int32 (Wasm_int.Int32.repr 4));
                            BI_binop T_i32 (Binop_i BOI_add); 
                            BI_get_local 0; BI_load T_i32 None N.zero N.zero;
                            BI_relop T_i32 (Relop_i ROI_eq)])%I).                            
        iSimpl.
        iFrame.
        iExists k.
        iFrame.
        done. }
      iIntros (w) "[(H & Hs & Hf0) Hf]".
      iDestruct "H" as (k) "%Hk".
      iApply "HΦ".
      iFrame.
      by iExists _.
    - iSplitR.
      iIntros "!>" (v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Hlen & %Hdiv & Hlen) HΦ".
      iApply wp_wand_r.
      iSplitR "HΦ".
      { rewrite (separate1 (i32const _) _).
        rewrite - (app_nil_r [AI_basic _]).
        (* iApply wp_wasm_empty_ctx.
        iApply wp_base_push => //.
        iApply (wp_call_ctx with "Hf") => //=.
        iIntros "!> Hf".
        iApply wp_base_pull.
        rewrite app_nil_r.
        iApply wp_wasm_empty_ctx. *)
        iApply (wp_invoke_native with "Hf Hf0") => //.
        iIntros "!> [Hf Hf0]".
        iSimpl.
        iApply (wp_frame_bind with "Hf").
        iIntros "Hf".
        rewrite - (app_nil_l [AI_basic _]).
        iApply (wp_block with "Hf") => //.
        iIntros "!> Hf".
        iApply (wp_label_bind with "[Hlen Hf Hf0]") ; last first.
        iPureIntro.
        unfold lfilled, lfill => /=.
        instantiate (5 := []) => /=.
        rewrite app_nil_r.
        done.
        iApply (spec_is_full with "[Hlen Hf]").
        iFrame.
        repeat iSplit ; iPureIntro => //=.
        lia.
        by destruct H.
        iIntros (w) "H".
        iDestruct "H" as (k) "(-> & H & %Hk & Hf)" => /=.
        iDestruct "Hf" as (f5) "[Hf %Hf4]".
        iApply (wp_wand_ctx with "[H Hf Hf0]").
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        rewrite app_nil_r app_nil_l.
        iApply wp_value => //=.
        unfold IntoVal.
        apply of_to_val => //.
        iFrame.
        instantiate (1 := λ v, (⌜ v = immV [value_of_int k] ⌝ ∗
                                           isStack v0 s0 m ∗
                                           N.of_nat f1↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3 ; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32] [T_i32]) []
                            [BI_const (VAL_int32 (Wasm_int.Int32.repr 0));
                            BI_const (VAL_int32 (Wasm_int.Int32.repr 1));
                            BI_get_local 0; BI_load T_i32 None N.zero N.zero;
                            BI_const (VAL_int32 (Wasm_int.Int32.repr 65536));
                            BI_binop T_i32 (Binop_i (BOI_rem SX_U)); BI_select])%I).
        iSimpl.
        iFrame.
        done.
        iIntros (w) "[(-> & H &  Hf0) Hf]".
        iExists _.
        iFrame.
        iIntros "Hf".
        iSimpl.         
        iApply (wp_frame_value with "Hf") => //.
        iNext.
        instantiate (1 := λ v, ((∃ k, ⌜ v = immV [value_of_int k] ⌝ ∗
                                                 ⌜ k = 1 \/ (length s0 < two14 - 1)%Z ⌝) ∗
                                                                                        isStack v0 s0 m ∗
                                                                                        N.of_nat f1↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3 ; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32] [T_i32]) []
                            [BI_const (VAL_int32 (Wasm_int.Int32.repr 0));
                            BI_const (VAL_int32 (Wasm_int.Int32.repr 1));
                            BI_get_local 0; BI_load T_i32 None N.zero N.zero;
                            BI_const (VAL_int32 (Wasm_int.Int32.repr 65536));
                            BI_binop T_i32 (Binop_i (BOI_rem SX_U)); BI_select])%I).                            
        iSimpl.
        iFrame.
        iExists k.
        iFrame.
        done. }
      iIntros (w) "[(H & Hs & Hf0) Hf]".
      iDestruct "H" as (k) "%Hk".
      iApply "HΦ".
      iFrame.
      by iExists _.
    - iSplitR.
      iIntros "!>" (a v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Ha & Hs) HΦ". 
      iApply wp_wand_r.
      iSplitR "HΦ".
      { rewrite (separate1 (i32const _) _).
        rewrite - (app_nil_r [AI_basic _]).
        (* iApply wp_wasm_empty_ctx.
        iApply wp_base_push => //.
        iApply (wp_call_ctx with "Hf") => //=.
        iIntros "!> Hf".
        iApply wp_base_pull.
        rewrite app_nil_r.
        iApply wp_wasm_empty_ctx. *)
        iApply (wp_invoke_native with "Hf Hf0") => //.
        iIntros "!> [Hf Hf0]".
        iSimpl.
        iApply (wp_frame_bind with "Hf").
        iIntros "Hf".
        rewrite - (app_nil_l [AI_basic _]).
        iApply (wp_block with "Hf") => //.
        iIntros "!> Hf".
        iApply (wp_label_bind with "[Hs Hf Hf0]") ; last first.
        iPureIntro.
        unfold lfilled, lfill => /=.
        instantiate (5 := []) => /=.
        rewrite app_nil_r.
        done.
        iApply (spec_pop with "[Hs Hf]").
        iFrame.
        repeat iSplit ; iPureIntro => //=.
        lia.
        lia.
        by destruct H.
        iIntros (w) "H".
        iDestruct "H" as "(-> & Hs & Hf)" => /=.
        iDestruct "Hf" as (f5) "[Hf %Hf4]".
        iApply (wp_wand_ctx with "[Hs Hf Hf0]").
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        rewrite app_nil_r app_nil_l.
        iApply wp_value => //=.
        unfold IntoVal.
        apply of_to_val => //.
        iFrame.
        instantiate (1 := λ v, (⌜ v = immV [_] ⌝ ∗
                                           isStack v0 s0 m ∗
                                            N.of_nat f2↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3 ; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32] [T_i32]) [T_i32]
                            [BI_get_local 0; BI_load T_i32 None N.zero N.zero;
                            BI_const (VAL_int32 (Wasm_int.Int32.repr 4));
                            BI_binop T_i32 (Binop_i BOI_sub); 
                            BI_tee_local 1; BI_load T_i32 None N.zero N.zero;
                            BI_get_local 0; BI_get_local 1;
                            BI_store T_i32 None N.zero N.zero])%I).
        iSimpl.
        iFrame.
        done.
        iIntros (w) "[(-> & H &  Hf0) Hf]".
        iExists _.
        iFrame.
        iIntros "Hf".
        iSimpl.         
        iApply (wp_frame_value with "Hf") => //.
        iNext.
        instantiate (1 := λ v,  (⌜ v = immV [_] ⌝ ∗
                                            isStack v0 s0 m ∗
                                            N.of_nat f2↦[wf]FC_func_native
                                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3 ; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32] [T_i32]) [T_i32]
                            [BI_get_local 0; BI_load T_i32 None N.zero N.zero;
                            BI_const (VAL_int32 (Wasm_int.Int32.repr 4));
                            BI_binop T_i32 (Binop_i BOI_sub); 
                            BI_tee_local 1; BI_load T_i32 None N.zero N.zero;
                            BI_get_local 0; BI_get_local 1;
                             BI_store T_i32 None N.zero N.zero])%I).
        iSimpl.
        iFrame.
        done. }
      iIntros (w) "[(-> & Hs & Hf0) Hf]".
      iApply "HΦ".
      by iFrame.
    - iSplitR. iIntros "!>" (a v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Ha & %Hlen & Hs) HΦ".
      iApply wp_wand_r.
      iSplitR "HΦ".
      { rewrite (separate2 _ (i32const _) _).
        rewrite - (app_nil_r [AI_basic _]).
        (* iApply wp_wasm_empty_ctx.
        iApply wp_base_push => //.
        iApply (wp_call_ctx with "Hf") => //=.
        iIntros "!> Hf".
        iApply wp_base_pull.
        rewrite app_nil_r.
        iApply wp_wasm_empty_ctx. *)
        iApply (wp_invoke_native with "Hf Hf0") => //.
        iIntros "!> [Hf Hf0]".
        iSimpl.
        iApply (wp_frame_bind with "Hf").
        iIntros "Hf".
        rewrite - (app_nil_l [AI_basic _]).
        iApply (wp_block with "Hf") => //.
        iIntros "!> Hf".
        iApply (wp_label_bind with "[Hs Hf Hf0]") ; last first.
        iPureIntro.
        unfold lfilled, lfill => /=.
        instantiate (5 := []) => /=.
        rewrite app_nil_r.
        done.
        iApply (spec_push with "[Hs Hf]").
        iFrame.
        repeat iSplit ; iPureIntro => //=.
        lia.
        lia.
        by destruct H.
        iIntros (w) "(-> & Hs & Hf)".
        iDestruct "Hf" as (f5) "[Hf %Hf4]".
        iApply (wp_wand_ctx with "[Hs Hf Hf0]").
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        iSimpl.
        iApply wp_value => //=.
        unfold IntoVal.
        apply of_to_val => //.
        iFrame.
        instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                           isStack v0 (a :: s0) m ∗
                                          N.of_nat f3↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3;f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32; T_i32] []) [T_i32]
                            [BI_get_local 1; BI_load T_i32 None N.zero N.zero;
                            BI_tee_local 2; BI_get_local 0;
                            BI_store T_i32 None N.zero N.zero; 
                            BI_get_local 1; BI_get_local 2;
                            BI_const (VAL_int32 (Wasm_int.Int32.repr 4));
                            BI_binop T_i32 (Binop_i BOI_add);
                            BI_store T_i32 None N.zero N.zero])%I).
        iSimpl.
        iFrame.
        done.
        iIntros (w) "[(-> & H &  Hf0) Hf]".
        iExists _.
        iFrame.
        iIntros "Hf".
        iSimpl.         
        iApply (wp_frame_value with "Hf") => //.
        iNext.
         instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                           isStack v0 (a :: s0) m ∗
                                          N.of_nat f3↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3 ; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32; T_i32] []) [T_i32]
                            [BI_get_local 1; BI_load T_i32 None N.zero N.zero;
                            BI_tee_local 2; BI_get_local 0;
                            BI_store T_i32 None N.zero N.zero; 
                            BI_get_local 1; BI_get_local 2;
                            BI_const (VAL_int32 (Wasm_int.Int32.repr 4));
                            BI_binop T_i32 (Binop_i BOI_add);
                            BI_store T_i32 None N.zero N.zero])%I).
        iSimpl.
        iFrame.
        iFrame.
        done. }
      iIntros (w) "[(-> & Hs & Hf0) Hf]".
      iApply "HΦ".
      by iFrame.
    - iIntros "!>" (f5 fi v0 s0 a cl Φ Ψ Ξ)
              "!> (Hf & Hf0 & % & %Hs & Hs & HΦ & Htab & Hcl & %Hclt & #Hspec) HΞ".
      iApply wp_wand_r.
      iSplitR "HΞ".
      { rewrite (separate2 _ (i32const _) _).
        rewrite - (app_nil_r [AI_basic _]).
        (* iApply wp_wasm_empty_ctx.
        iApply wp_base_push => //.
        iApply (wp_call_ctx with "Hf") => //=.
        iIntros "!> Hf".
        iApply wp_base_pull.
        rewrite app_nil_r.
        iApply wp_wasm_empty_ctx. *)
        iApply (wp_invoke_native with "Hf Hf0") => //.
        iIntros "!> [Hf Hf0]".
        iSimpl.
        iApply (wp_frame_bind with "Hf").
        iIntros "Hf".
        rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
        iApply (wp_block with "Hf") => //.
        iIntros "!> Hf".
        iApply (wp_label_bind with "[Hs Hf Hf0 HΦ Htab Hcl]") ; last first.
        iPureIntro.
        unfold lfilled, lfill => /=.
        instantiate (5 := []) => /=.
        rewrite app_nil_r.
        done.
        iApply (spec_stack_map with "[Hs Hf HΦ Hcl Htab]").        
        iFrame.
        repeat iSplit ; try iPureIntro => //=.
        lia.
 (*       iIntros (u fc) "!>". iIntros (Φ0) "(Hu & % & H)".
        iApply "Hspec".
        iFrame. *)
        iExact "Hspec".
        iIntros (w) "(-> & Hs & Hf)".
        iDestruct "Hf" as (f6) "[Hf %Hf4]".
        iApply (wp_wand_ctx with "[Hs Hf Hf0]").
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        iSimpl.
        iApply wp_value => //=.
        unfold IntoVal.
        apply of_to_val => //.
        iFrame.
        instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                           ( ∃ s', isStack v0 s' m ∗ stackAll2 s0 s' Ψ) ∗
                                           N.of_nat f4↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3;f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32; T_i32] []) [T_i32 ; T_i32 ]
                           [BI_get_local 1; BI_load T_i32 None N.zero N.zero;
                            BI_set_local 3; BI_get_local 1;
                            BI_const (VAL_int32 (Wasm_int.Int32.repr 4));
                            BI_binop T_i32 (Binop_i BOI_add); 
                            BI_set_local 2;
                            BI_block (Tf [] [])
                              [BI_loop (Tf [] [])
                                 [BI_get_local 2; BI_get_local 3;
                                 BI_relop T_i32 (Relop_i (ROI_ge SX_U)); 
                                 BI_br_if 1; BI_get_local 2; 
                                 BI_get_local 2; BI_get_local 2;
                                 BI_load T_i32 None N.zero N.zero; 
                                 BI_get_local 0; BI_call_indirect 1;
                                 BI_store T_i32 None N.zero N.zero; 
                                 bi32const 4; BI_binop T_i32 (Binop_i BOI_add);
                                 BI_set_local 2; BI_br 0]]])%I).
        iSimpl.
        iFrame.
        done.
        iIntros (w) "[(-> & H &  Hf0) Hf]".
        iExists _.
        iFrame.
        iIntros "Hf".
        iSimpl.         
        iApply (wp_frame_value with "Hf") => //.
        iNext.
         instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                            ( ∃ s', isStack v0 s' m ∗ stackAll2 s0 s' Ψ) ∗
                                 N.of_nat f4↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32; T_i32] []) [T_i32; T_i32]
                            [BI_get_local 1; BI_load T_i32 None N.zero N.zero;
                            BI_set_local 3; BI_get_local 1;
                            BI_const (VAL_int32 (Wasm_int.Int32.repr 4));
                            BI_binop T_i32 (Binop_i BOI_add); 
                            BI_set_local 2;
                            BI_block (Tf [] [])
                              [BI_loop (Tf [] [])
                                 [BI_get_local 2; BI_get_local 3;
                                 BI_relop T_i32 (Relop_i (ROI_ge SX_U)); 
                                 BI_br_if 1; BI_get_local 2; 
                                 BI_get_local 2; BI_get_local 2;
                                 BI_load T_i32 None N.zero N.zero; 
                                 BI_get_local 0; BI_call_indirect 1;
                                 BI_store T_i32 None N.zero N.zero; 
                                 bi32const 4; BI_binop T_i32 (Binop_i BOI_add);
                                 BI_set_local 2; BI_br 0]]])%I).
        iSimpl.
        iFrame.
        iFrame.
        done. }
      iIntros (w) "[(-> & Hs & Hf0) Hf]".
      iApply "HΞ".
      by iFrame.
  Qed. 

  

  Lemma instantiate_stack_client_spec (s: stuckness) E hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 :
    0%N ↪[mods] stack_module -∗
     1%N ↪[mods] client_module -∗
     ( [∗ list] k↦hvk ∈ [hv0 ; hv1 ; hv2 ; hv3 ; hv4 ; hv5 ; hv6 ; hv7], N.of_nat k↪[vis] hvk) -∗
     WP ((stack_instantiate , []) : host_expr)
     @ s; E
            {{ v,
                0%N ↪[mods] stack_module ∗
                 1%N ↪[mods] client_module ∗
                 ∃ idg name,
                   7%N ↪[vis] {| modexp_name := name ;
                                modexp_desc := MED_global (Mk_globalidx idg) |} ∗
                    (N.of_nat idg ↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int 20%Z |} ∨
                       N.of_nat idg ↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int (-1)%Z |}) }}.
  Proof.
    iIntros "Hmod0 Hmod1 (Hvis0 & Hvis1 & Hvis2 & Hvis3 & Hvis4 & Hvis5 & Hvis6 & Hvis7 &  _)".
    iApply (wp_seq_host_nostart
             with "[$Hmod0] [Hvis0 Hvis1 Hvis2 Hvis3 Hvis4 Hvis5 Hvis6]") => //.
    - iIntros "Hmod0".
      iApply weakestpre.wp_mono ;
        last iApply (instantiate_stack_spec
                      with "Hmod0 [Hvis0 Hvis1 Hvis2 Hvis3 Hvis4 Hvis5 Hvis6]").
      2:{ iSplitL "Hvis0" ; first done.
          iSplitL "Hvis1" ; first done.
          iSplitL "Hvis2" ; first done.
          iSplitL "Hvis3" ; first done.
          iSplitL "Hvis4" ; first done.
          iSplitL "Hvis5" ; first done.
          by iSplitL. }
      iIntros (v) "[? H]".
      iFrame.
      by iApply "H".
    - iIntros (w) "Hes1 Hmod0".
      iDestruct "Hes1" as (idf0 idf1 idf2 idf3 idf4 idf5 idt) "Hes1".
      iDestruct "Hes1" as (name0 name1 name2 name3 name4 name5 name6) "Hes1".
      iDestruct "Hes1" as (f0 f1 f2 f3 f4 f5) "Hes1".
      iDestruct "Hes1" as (i0 i1 i2 i3 i4 i5) "Hes1".  
      iDestruct "Hes1" as (l0 l1 l2 l3 l4 l5) "Hes1".
      iDestruct "Hes1" as (tab isStack nextStackAddrIs)
                            "(Himport & Himp_type & %Htab & Hnextaddr & #Hspec0 & #Hspec1 & #Hspec2 & #Hspec3 & #Hspec4 & #Hspec5)".
      iFrame "Hmod0".
      iApply (instantiation_spec_operational_start with "[Hmod1 Himport Himp_type Hvis7]") ; try exact module_typing_client.
    - by unfold client_module.
    - unfold instantiation_resources_pre.
      iFrame.
(*      iSplitL "Hmod1" => //.
      iSplitL "Hvis0 Hvis1 Hvis2 Hvis3 Hvis4".
      unfold import_resources_host.
      unfold big_sepL2.
      instantiate
        (1 := [ {| modexp_name := name0 ; modexp_desc := MED_func (Mk_funcidx idf0) |} ;
                {| modexp_name := name1 ; modexp_desc := MED_func (Mk_funcidx idf1) |} ;
                {| modexp_name := name2 ; modexp_desc := MED_func (Mk_funcidx idf2) |} ;
                {| modexp_name := name3 ; modexp_desc := MED_func (Mk_funcidx idf3) |} ;
                {| modexp_name := name4 ; modexp_desc := MED_func (Mk_funcidx idf4) |} ]
        ).
      iFrame.
    - iSplitR "Hvis5".
      do 3 instantiate (1 := ∅).
      instantiate (1 := <[ idf0 := _ ]> (<[ idf1 := _ ]> (<[idf2 := _]>
                                                            (<[ idf3 := _ ]> (<[ idf4 := _]> ∅))))).
      unfold import_resources_wasm_typecheck => /=.
(*      iDestruct (mapsto_frac_ne with "Hwf0 Hwf1") as "%H01" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hwf0 Hwf2") as "%H02" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hwf0 Hwf3") as "%H03" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hwf0 Hwf4") as "%H04" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hwf1 Hwf2") as "%H12" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hwf1 Hwf3") as "%H13" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hwf1 Hwf4") as "%H14" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hwf2 Hwf3") as "%H23" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hwf2 Hwf4") as "%H24" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hwf3 Hwf4") as "%H34" ; first by eauto. *)
      iSplit.
    - iPureIntro.
      simpl.
      repeat rewrite dom_insert.
      done.
    - iSplitL "Hwf0".
      iExists _.
      iFrame.
      iPureIntro.
      rewrite lookup_insert.
      split => //.
      iSplitL "Hwf1".
      iExists _ ; iFrame.
      iPureIntro.
      rewrite lookup_insert_ne ; last lia.
      rewrite lookup_insert.
      split => //.
      iSplitL "Hwf2".
      iExists _ ; iFrame.
      iPureIntro.
      do 2 (rewrite lookup_insert_ne ; last lia).
      rewrite lookup_insert.
      split => //.
      iSplitL "Hwf3".
      iExists _ ; iFrame.
      iPureIntro.
      do 3 (rewrite lookup_insert_ne ; last lia).
      rewrite lookup_insert.
      split => //.
      iSplitL => //.
      iExists _ ; iFrame.
      iPureIntro.
      do 4 (rewrite lookup_insert_ne ; last lia).
      rewrite lookup_insert.
      split => //. *)
      
    - unfold export_ownership_host => /=.
      repeat iSplit.
      by iExists _.
      done.
      done.
      iPureIntro ; unfold module_elem_bound_check_gmap ; simpl.
      apply Forall_cons.
      split ; last done.
      simpl.
      rewrite lookup_insert.
      done.
      iPureIntro ; unfold module_data_bound_check_gmap ; simpl ; done.
    - iIntros (idnstart) "Hf Hres".
      unfold instantiation_resources_post.
      iDestruct "Hres" as "(Hmod1 & Himphost & Himpwasm & Hinst)".
      iDestruct "Hinst" as (inst g_inits t_inits m_inits) "(%Hinst & %Hival & Hexpwasm & Hexphost)".
      destruct Hinst as (Hinsttype & Hinstfunc & Hinsttab & Hinstmem & Hinstglob & Hstart).
      unfold module_inst_resources_wasm, module_export_resources_host => /=.
      destruct inst => /=.
      iDestruct "Hexpwasm" as "(Hexpwf & Hexpwt & Hexpwm & Hexpwg)".
      unfold module_inst_resources_func, module_inst_resources_tab,
        module_inst_resources_mem, module_inst_resources_glob => /=.
      unfold big_sepL2 => /=.
      do 7 (destruct inst_funcs as [| ? inst_funcs] ; first by iExFalso ; iExact "Hexpwf").
      simpl.
      iDestruct "Hexpwf" as "[Hwfcl Hexpwf]".
      destruct inst_funcs ; first by iExFalso ; iExact "Hexpwf".
      iDestruct "Hexpwf" as "[Hwfsq Hexpwf]".
      destruct inst_funcs ; last by iExFalso ; iExact "Hexpwf".
(*      destruct inst_tab ; first by iExFalso ; iExact "Hexpwt".
      iDestruct "Hexpwt" as "[Hwt Hexpwt]".
      destruct inst_tab ; last by iExFalso ; iExact "Hexpwt". *)
      destruct inst_memory ; last by iExFalso ; iExact "Hexpwm".
      destruct inst_globs as [| g inst_globs] ; first by iExFalso ; iExact "Hexpwg". 
      iDestruct "Hexpwg" as "[Hwg Hexpwg]".
      destruct g_inits eqn:Hg ; try by iExFalso ; iExact "Hwg".
      destruct inst_globs ; last by iExFalso ; iExact "Hexpwg". 
      iDestruct "Hexphost" as "[Hexphost _]".
      iDestruct "Hexphost" as (name) "Hexphost" => /=.
      unfold import_resources_wasm_typecheck => /=.
(*      iDestruct "Himpwasm" as "[%Hdom Himpwasm]".
      destruct name0 ; first done ; iDestruct "Himpwasm" as "[Himpw0 Himpwasm]".
      destruct name0 ; first done ; iDestruct "Himpwasm" as "[Himpw1 Himpwasm]".
      destruct name0 ; first done ; iDestruct "Himpwasm" as "[Himpw2 Himpwasm]".
      destruct name0 ; first done ; iDestruct "Himpwasm" as "[Himpw3 Himpwasm]".
      destruct name0 ; first done ; iDestruct "Himpwasm" as "[Himpw4 _]". *) 
      iDestruct "Himpwasm" as "(%Hdom & Himpw0 & Himpw1 & Himpw2 & Himpw3 & Himpw4 & Himpw5 & Htab & _)". 
      iDestruct "Himpw0" as (cl0) "[Himpfcl0 %Hcltype0]".
      iDestruct "Himpw1" as (cl1) "[Himpfcl1 %Hcltype1]".
      iDestruct "Himpw2" as (cl2) "[Himpfcl2 %Hcltype2]".
      iDestruct "Himpw3" as (cl3) "[Himpfcl3 %Hcltype3]".
      iDestruct "Himpw4" as (cl4) "[Himpfcl4 %Hcltype4]".
      iDestruct "Himpw5" as (cl5) "[Himpfcl5 %Hcltype5]".
      iDestruct "Htab" as (tab0 tt) "[Htab %Htab0]".
      iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl1") as "%H01" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl2") as "%H02" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl3") as "%H03" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl4") as "%H04" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl5") as "%H05" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl2") as "%H12" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl3") as "%H13" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl4") as "%H14" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl5") as "%H15" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Himpfcl2 Himpfcl3") as "%H23" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Himpfcl2 Himpfcl4") as "%H24" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Himpfcl2 Himpfcl5") as "%H25" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Himpfcl3 Himpfcl4") as "%H34" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Himpfcl3 Himpfcl5") as "%H35" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Himpfcl4 Himpfcl5") as "%H45" ; first by eauto.
(*      assert (forall a b, N.of_nat a <> N.of_nat b -> a <> b) as Hneq.
      { intros ; intro. by subst. }
      apply Hneq in H01, H02, H03, H04, H05, H12, H13, H14, H15, H23, H24, H25, H34, H35, H45. *)
      rewrite lookup_insert in Hcltype0.
      destruct Hcltype0 as [Hcl _] ; inversion Hcl ; subst ; clear Hcl.
      rewrite lookup_insert_ne in Hcltype1 ; last assumption.
      rewrite lookup_insert in Hcltype1.
      destruct Hcltype1 as [Hcl _] ; inversion Hcl ; subst ; clear Hcl.
      do 2 (rewrite lookup_insert_ne in Hcltype2 ; last assumption).
      rewrite lookup_insert in Hcltype2.
      destruct Hcltype2 as [Hcl _] ; inversion Hcl ; subst ; clear Hcl.
      do 3 (rewrite lookup_insert_ne in Hcltype3 ; last assumption).
      rewrite lookup_insert in Hcltype3.
      destruct Hcltype3 as [Hcl _] ; inversion Hcl ; subst ; clear Hcl.
      do 4 (rewrite lookup_insert_ne in Hcltype4 ; last assumption).
      rewrite lookup_insert in Hcltype4.
      destruct Hcltype4 as [Hcl _] ; inversion Hcl ; subst ; clear Hcl.
      do 5 (rewrite lookup_insert_ne in Hcltype5 ; last assumption).
      rewrite lookup_insert in Hcltype5.
      destruct Hcltype5 as [Hcl _] ; inversion Hcl ; subst ; clear Hcl.
      rewrite lookup_insert in Htab0.
      destruct Htab0 as [Htab0 _] ; inversion Htab0 ; subst ; clear Htab0.
      simpl in * ; subst. 
      unfold ext_func_addrs in Hinstfunc ; simpl in Hinstfunc.
      unfold prefix in Hinstfunc.
      destruct Hinstfunc as [ll Hinstfunc].
      inversion Hinstfunc ; subst ; clear Hinstfunc.
      unfold check_start in Hstart.
      simpl in Hstart.
      apply b2p in Hstart.
      inversion Hstart ; subst ; clear Hstart.
      iApply wp_host_wasm.
      by apply HWEV_invoke.
      iApply wp_wand_r.
      iSplitR "Hmod1".
      rewrite - (app_nil_l [AI_invoke idnstart]).
      iApply (wp_invoke_native with "Hf Hwfcl").
      done. done. done.
      iIntros "!> [Hf Hwfcl]".
      iApply (wp_frame_bind with "Hf").
      iIntros "Hf".
      rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
      iApply (wp_block with "Hf").
      done. done. done. done.
      iIntros "!> Hf".
      iApply (wp_label_bind with
               "[Hwg Htab Hwfsq Hf Himpfcl0 Himpfcl1 Himpfcl2 Himpfcl3 Himpfcl4 Himpfcl5 Hexphost Hnextaddr]") ; last first.
      iPureIntro.
      unfold lfilled, lfill => /=.
      instantiate (5 := []) => /=.
      rewrite app_nil_r.
      done.
       
      { rewrite (separate1 (AI_basic (BI_call 0)) (_ :: _)).
        iApply wp_seq.
        iSplitR ; last first.
        iSplitL "Hnextaddr Hf Himpfcl0".
        { iApply (wp_call with "Hf").
          done.
          iIntros "!> Hf".
          iApply ("Hspec0" with "[Hf Hnextaddr Himpfcl0]").
          iFrame.
          repeat iSplit ; iPureIntro => //.
          unfold page_size. unfold N.divide.
          exists 0%N. 
          done.
          iIntros (v0) "(H & Himpfcl0 & Hf)".
          iFrame.
          instantiate (1 := λ v0, (( ∃ k : Z, ⌜v0 = immV [value_of_int k]⌝ ∗
                                                         (⌜k = (-1)%Z⌝ ∗ nextStackAddrIs 0 ∨  ⌜ (0 ≤ k)%Z ∧ (k + Z.pos (64 * 1024) ≤ two32)%Z⌝ ∗ isStack k [] ∗ nextStackAddrIs (0 + Pos.to_nat (64 * 1024)))) ∗ 
                                     N.of_nat idf0↦[wf]FC_func_native i0 (Tf [] [T_i32]) l0 f0)%I). 
          iFrame. }
        iIntros (w0) "[[H Himpfcl0] Hf]". 
        iDestruct "H" as (k) "[-> H]".
        iSimpl.
        rewrite (separate2 (i32const _)).
        iApply wp_seq.
        iSplitR ; last first.
        iSplitL "Hf".
        iApply (wp_tee_local with "Hf").
        iIntros "Hf".
        rewrite (separate1 (i32const _)).
        iApply wp_val_app => //.
        iSplitR ; last first.
        iApply wp_wand_r.
        iSplitL "Hf".
        iApply (wp_set_local with "Hf").
        simpl.
        lia.
        instantiate (1 := λ v, v = immV []) => //.
        iIntros (v0) "[-> Hf]".
        iSimpl.
        iSimpl in "Hf".
        instantiate (1 := λ v, (⌜ v = immV [VAL_int32 (Wasm_int.Int32.repr k)] ⌝
                                           ∗ ↪[frame] _)%I). 
        by iFrame.
        by iIntros "!> [%H _]".
        iIntros (w0) "[-> Hf]".
        iSimpl.
        rewrite (separate3 (i32const _)).
        iApply wp_seq.
        iSplitR ; last first.
        iSplitL "Hf".
        iApply (wp_relop with "Hf") => //.
        instantiate (1 := λ v, ⌜ v = immV
                                       [VAL_int32
                                          (wasm_bool
                                             (app_relop (Relop_i ROI_eq) (VAL_int32 (Wasm_int.int_of_Z i32m k))
                                                        (VAL_int32 (Wasm_int.Int32.repr (-1)))))]⌝%I ).
        done.
        iIntros (w0) "[-> Hf]".
        iSimpl.
        rewrite (separate2 _ (AI_basic (BI_if _ _ _))).
        iApply wp_seq.
        iSplitR ; last first.
        iAssert (⌜ (-1 <= k < two32 - 1)%Z ⌝%I) with "[H]" as "%Hk".
        { iDestruct "H" as "[[%Hk _] | (%Hk & _)]" ; iPureIntro.
          subst. done.
          destruct Hk.
          lia. }
        iSplitL "Hf Hwg". 
        instantiate (1:= λ v1, (( ⌜ v1 = immV [] ⌝ ∗
                                              ⌜ (k <> -1)%Z ⌝ ∗
                                              N.of_nat g↦[wg] {| g_mut := MUT_mut ; g_val := v |} ∨
                                    ⌜ exists sh, v1 = retV sh ⌝ ∗
                                                      N.of_nat g↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int (-1)%Z |}) ∗
                                                                                                                             ↪[frame] _)%I ).         
        destruct ( decide ( k = (* Wasm_int.Int32.modulus *) - 1)%Z ).
        + { subst. iSimpl.
            iApply (wp_if_true with "Hf") => //.
            iIntros "!> Hf".
            rewrite - (app_nil_l [AI_basic _]).
            iApply (wp_block with "Hf") => //.
            iIntros "!> Hf".
            iSimpl.
            iApply (wp_label_bind with "[Hf Hwg]") ; last first.
            iPureIntro.
            unfold lfilled, lfill.
            instantiate (4 := []) => /=.
            rewrite app_nil_r.
            done.
            rewrite (separate2 (i32const _)).
            iApply wp_seq.
            iSplitR ; last first.
            iSplitL.
            iApply (wp_set_global with "[] Hf Hwg").
            done.
            instantiate (1 := λ v, ⌜ v = immV [] ⌝%I ).
            done.
            iIntros (w0) "[[-> Hwg] Hf]".
            iSimpl.
            iApply wp_value.
            unfold IntoVal.
            by apply of_to_val.
            iIntros (lh) "%Hfill".
            unfold lfilled, lfill in Hfill ; simpl in Hfill.
            apply b2p in Hfill ; subst.
            iApply wp_value.
            unfold IntoVal.
            by apply of_to_val.
            iFrame.
            iRight.
            iFrame.
            iPureIntro ; by eexists _.
            by iIntros "[[%H _] _]". }
        + { rewrite Wasm_int.Int32.eq_false.
            2:{ intro Habs ; inversion Habs.
                rewrite Wasm_int.Int32.Z_mod_modulus_eq in H0.
                rewrite Z.mod_small in H0.
                subst.
                unfold Wasm_int.Int32.modulus in Hk.
                unfold Wasm_int.Int32.wordsize in Hk.
                unfold Integers.Wordsize_32.wordsize in Hk.
                replace (two_power_nat 32) with two32 in Hk ; last done.
                lia.
                unfold Wasm_int.Int32.modulus.
                unfold Wasm_int.Int32.wordsize.
                unfold Integers.Wordsize_32.wordsize.
                replace (two_power_nat 32) with two32 ; last done.
                lia. }
            iApply (wp_if_false with "Hf").
            done.
            iIntros "!> Hf".
            rewrite - (app_nil_l [AI_basic _]).
            iApply (wp_block with "Hf").
            done. done. done. done.
            iIntros "!> Hf".
            iApply (wp_label_bind with "[Hf Hwg]") ; last first.
            iPureIntro ; unfold lfilled, lfill.
            instantiate (4 := []) => /=.
            rewrite app_nil_r.
            done.
            iApply wp_value.
            unfold IntoVal ; by apply of_to_val.
            iSimpl.
            iIntros (lh) "%Hfill".
            unfold lfilled, lfill in Hfill ; simpl in Hfill.
            apply b2p in Hfill ; subst. 
            iApply (wp_label_value with "Hf").
            done.
            iLeft.
            repeat (iSplit ; try by iPureIntro).
            done. }
         
            iIntros (w0) "[[(-> & %Hk1 & Hwg) | [%Hret Hwg]] Hf]".
          { iDestruct "H" as "[[-> Haddr] | (%Hk2 & Hs & Haddr)]".
            done.
            iSimpl.
            rewrite (separate2 (i32const _)).
            iApply wp_seq.
            iSplitR ; last first.
            iSplitL "Hf".
            rewrite (separate1 (i32const _)).
            iApply wp_val_app.
            done.
            iSplitR ; last first.
            iApply wp_wand_r.
            iSplitL.
            iApply (wp_get_local with "Hf").
            done.
            instantiate (1 := λ v, v = immV [VAL_int32 (Wasm_int.Int32.repr k)]).
            done.
            iIntros (w0) "[-> Hf]".
            iSimpl.
            instantiate (1 := λ v, (⌜ v = immV [value_of_int 4%Z ; value_of_int k] ⌝ ∗
                                               ↪[frame] _)%I ). 
            by iFrame.
          by iIntros "!> [%H _]".
          iIntros (w0) "[-> Hf]".
          iSimpl.
          rewrite (separate3 (i32const _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Himpfcl4 Hf Hs".
          rewrite (separate2 (i32const _)).
          rewrite - (app_nil_r [AI_basic (BI_call 4)]).
          iApply wp_wasm_empty_ctx.
          iApply wp_base_push => //.
          iApply (wp_call_ctx with "Hf") => //=.
          iIntros "!> Hf".
          iApply wp_base_pull.
          rewrite app_nil_r.
          iApply wp_wasm_empty_ctx.
          iApply ("Hspec4" with "[Hf Himpfcl4 Hs]").
          iFrame.
          iSimpl.
          repeat iSplit ; iPureIntro => //.
          by destruct Hk2.
          unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
          unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          replace (two_power_nat 32) with two32 ; last done.
          by destruct Hk2 ; lia.
          iIntros (w0) "(-> & Hs & Himpfcl4 & Hf)".
          iFrame.
          instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                             isStack k [ (Wasm_int.int_of_Z i32m 4)] ∗
                                             N.of_nat idf4↦[wf]FC_func_native i4 (Tf [T_i32 ; T_i32] []) l4 f4)%I).
          by iFrame.
          iIntros (w0) "[(-> & Hs & Himpfcl4) Hf]".
          iSimpl.
          rewrite (separate2 (i32const _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf".
          rewrite (separate1 (i32const _)).
          iApply wp_val_app.
          done.
          iSplitR ; last first.
          iApply wp_wand_r.
          iSplitL.
          iApply (wp_get_local with "Hf").
          done.
          instantiate (1 := λ v, v = immV [value_of_int k]).
          done.
          iIntros (v0) "[-> Hf]".
          iSimpl.
          instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗
                                             ↪[frame] _)%I).  
          by iFrame.
          by iIntros "!> [%H _]".
          iIntros (w0) "[-> Hf]".
          iSimpl.
          rewrite (separate3 (i32const _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Himpfcl4 Hf Hs".
          rewrite (separate2 (i32const _)).
          rewrite - (app_nil_r [AI_basic (BI_call 4)]).
          iApply wp_wasm_empty_ctx.
          iApply wp_base_push => //.
          iApply (wp_call_ctx with "Hf") => //=.
          iIntros "!> Hf".
          iApply wp_base_pull.
          rewrite app_nil_r.
          iApply wp_wasm_empty_ctx.
          iApply ("Hspec4" with "[Hf Himpfcl4 Hs]").
          iFrame.
          iSimpl.
          repeat iSplit ; iPureIntro => //.
          by destruct Hk2.
          unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
          unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          replace (two_power_nat 32) with two32 ; last done.
          by destruct Hk2 ; lia.
          iIntros (w0) "(-> & Hs & Himpfcl4 & Hf)".
          iFrame.
          instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                             isStack k [_;_] ∗
                                             N.of_nat idf4↦[wf]FC_func_native i4 (Tf [T_i32 ; T_i32] []) l4 f4)%I).
          by iFrame.
          iIntros (w0) "[(-> & Hs & Himpfcl4) Hf]".
          iSimpl.
          rewrite (separate2 (AI_basic _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf".
          rewrite (separate1 (AI_basic _)).
          iApply wp_val_app ; first done.
          iSplitR ; last first.
          iApply wp_wand_r ; iSplitL.
          iApply (wp_get_local with "Hf").
          done.
          by instantiate (1 := λ v, v = immV _).
          iIntros (v0) "[-> Hf]".
          by instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
          by iIntros "!> [% _]".
          iIntros (v0) "[-> Hf]".
          iSimpl.
          rewrite (separate3 (i32const 0)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf Himpfcl5 Hs Htab Hwfsq".
          rewrite (separate2 (i32const _)).
          rewrite - (app_nil_r [AI_basic (BI_call 5)]).
          iApply wp_wasm_empty_ctx.
          iApply wp_base_push => //.
          iApply (wp_call_ctx with "Hf") => //=.
          iIntros "!> Hf".
          iApply wp_base_pull.
          rewrite app_nil_r.
          iApply wp_wasm_empty_ctx.
          iApply ("Hspec5" with "[Hf Himpfcl5 Hs Htab Hwfsq]").
          iFrame.
          iSimpl.
          repeat iSplit ; try iPureIntro.
          by destruct Hk2.
          unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
          unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          replace (two_power_nat 32) with two32 ; last done.
          by destruct Hk2 ; lia.
          instantiate (2 := λ x, True%I).
          iSplit ; first done.
          iSplitL "Htab".
          admit.
          iSplit ; first done.
          instantiate (1 := λ x y, ⌜ y = Wasm_int.Int32.imul x x ⌝%I ).
          iIntros (u fc) "!>". iIntros (Λ) "(_ & -> & Hf & Htab & Hcl) HΛ".
          rewrite (separate1 _ [AI_invoke _]).
          iApply wp_wand_r.
          iSplitL "Hf Hcl".
          iApply (wp_invoke_native with "Hf Hcl").
          done.
          done.
          done.
          iIntros "!> [Hf Hcl]".
          iApply (wp_frame_bind with "Hf").
          iIntros "Hf".
          rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
          iApply (wp_block with "Hf").
          done.
          done.
          done.
          done.
          iIntros "!> Hf".
          iApply (wp_label_bind with "[Hf Hcl]") ; last first.
          iPureIntro.
          unfold lfilled, lfill.
          instantiate (4 := []) => /=.
          by rewrite app_nil_r.
          rewrite (separate1 (AI_basic _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf".
          iApply (wp_get_local with "Hf").
          done.
          by instantiate (1 := λ x, x = immV _).
          iIntros (w0) "[-> Hf]".
          iSimpl.
          rewrite (separate2 (AI_basic _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf".
          rewrite (separate1 (AI_basic _)).
          iApply wp_val_app ; first done.
          iSplitR ; last first.
          iApply wp_wand_r.
          iSplitL.
          iApply (wp_get_local with "Hf").
          done.
          by instantiate (1 := λ x, x = immV _).
          iIntros (v0) "[-> Hf]".
          by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
          by iIntros "!> [% _]".
          iIntros (w0) "[-> Hf]".
          iSimpl.
          iApply wp_wand_r.
          iSplitL "Hf".
          iApply (wp_binop with "Hf").
          done.
          by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
          iIntros (v0) "[-> Hf]".
          iSimpl.
          iIntros (lh) "%Hlh".
          unfold lfilled, lfill in Hlh ; simpl in Hlh.
          apply b2p in Hlh as ->.
          iApply wp_wand_r.
          iSplitL "Hf".
          iApply (wp_label_value with "Hf") ; first done.
          by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
          iIntros (v0) "[-> Hf]".
          iExists _.
          iFrame.
          iIntros "Hf".
          iSimpl.
          iApply (wp_frame_value with "Hf") ; first done.
          done.
          iNext.
          by instantiate (1 := λ x, (⌜ x = immV _⌝ ∗ N.of_nat f12 ↦[wf] _)%I) ; iFrame.
          all : try by iIntros "[% _]".
          iIntros (v0) "[[-> Hcl] Hf]".
          iApply "HΛ".
          iFrame.
          by iExists _.
          iIntros (w0) "(-> & H & Hwimpcl5 & Hf)".
          iDestruct "H" as (s') "[Hs Hs']".
          destruct s' ; first by iExFalso ; iExact "Hs'".
          iDestruct "Hs'" as "[-> Hs']".
          destruct s' ; first by iExFalso ; iExact "Hs'".
          iDestruct "Hs'" as "[-> Hs']".
          destruct s' ; last by iExFalso ; iExact "Hs'".
          iFrame.
          by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ isStack _ _ ∗ N.of_nat idf5 ↦[wf] _)%I) ; iFrame.
          iIntros (w0) "[(-> & Hs & Himpfcl5) Hf]".
          iSimpl.
          rewrite (separate1 (AI_basic _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf".
          iApply (wp_get_local with "Hf").
          done.
          instantiate (1 := λ v, v = immV [value_of_int k]).
          done.
          iIntros (v0) "[-> Hf]".
          iSimpl.
          rewrite (separate2 (i32const _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Himpfcl3 Hf Hs".
          rewrite (separate1 (i32const _)).
          rewrite - (app_nil_r [AI_basic (BI_call 3)]).
          iApply wp_wasm_empty_ctx.
          iApply wp_base_push => //.
          iApply (wp_call_ctx with "Hf") => //.
          iIntros "!> Hf".
          iApply wp_base_pull.
          rewrite app_nil_r.
          iApply wp_wasm_empty_ctx.
          iApply ("Hspec3"  with "[Hs Hf Himpfcl3]").
          iFrame.
          iSimpl.
          repeat iSplit ; iPureIntro => //.
          by destruct Hk2.
          unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
          unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          replace (two_power_nat 32) with two32 ; last done.
          by destruct Hk2 ; lia.
          iIntros (w0) "(-> & Hs & Himpfcl3 & Hf)".
          iFrame.
          instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗
                                             isStack k _ ∗
                                             N.of_nat idf3 ↦[wf] FC_func_native i3 (Tf [T_i32] [T_i32]) l3 f3)%I).
          by iFrame.
          iIntros (w0) "[(-> & Hs & Himpfcl3) Hf]".
          iSimpl.
          rewrite (separate2 (i32const _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf".
          rewrite (separate1 (i32const _)).
          iApply wp_val_app.
          done.
          iSplitR ; last first.
          iApply wp_wand_r.
          iSplitL.
          iApply (wp_get_local with "Hf").
          done.
          instantiate (1 := λ v, v = immV [value_of_int k]).
          done.
          iIntros (v0) "[-> Hf]".
          iSimpl.
          instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗
                                             ↪[frame] _)%I). 
          by iFrame.
          by iIntros "!> [%H _]".
          iIntros (w0) "[-> Hf]".
          iSimpl.
          rewrite (separate3 (i32const _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf Hs Himpfcl3".
          rewrite (separate1 (i32const _)).
          iApply wp_val_app.
          done.
          iSplitR ; last first.
          rewrite (separate1 (i32const _)).
          rewrite - (app_nil_r [AI_basic (BI_call 3)]).
          iApply wp_wasm_empty_ctx.
          iApply wp_base_push => //.
          iApply (wp_wand_ctx with "[Hf Hs Himpfcl3]").
          iApply (wp_call_ctx with "Hf") => //.
          iIntros "!> Hf".
          iApply wp_base_pull.
          rewrite app_nil_r.
          iApply wp_wasm_empty_ctx.
          iApply ("Hspec3"  with "[Hs Hf Himpfcl3]").
          iFrame.
          iSimpl.
          repeat iSplit ; iPureIntro => //.
          by destruct Hk2.
          unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
          unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          replace (two_power_nat 32) with two32 ; last done.
          by destruct Hk2 ; lia.
          iIntros (w0) "(-> & Hs & Himpfcl3 & Hf)".
          iFrame.
          instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗
                                             isStack k [] ∗
                                             N.of_nat idf3 ↦[wf] FC_func_native i3 (Tf [T_i32] [T_i32]) l3 f3)%I).
          by iFrame.
          iIntros (w0) "[(-> & Hs & Himpfcl3) Hf]".
          iSimpl.
          instantiate (1:= λ v, (⌜ v = immV _ ⌝ ∗
                                            isStack k [] ∗
                                            N.of_nat idf3 ↦[wf] FC_func_native i3 (Tf [T_i32] [T_i32]) l3 f3 ∗
                                            ↪[frame] _)%I ). 
          by iFrame.
          by iIntros "!> [%H _]".
          iIntros (w0) "(-> & Hs & Himpfcl3 & Hf)".
          iSimpl.
          rewrite (separate3 (i32const _) (i32const _)).
          iSimpl.
          rewrite (separate3 (i32const _) (i32const _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf".
          iApply (wp_binop with "Hf").
          done.
          iSimpl.
          unfold Wasm_int.Int32.isub, Wasm_int.Int32.sub.
          rewrite Wasm_int.Int32.unsigned_repr.
          rewrite Wasm_int.Int32.unsigned_repr.
          instantiate (1 := λ v, ⌜ v = immV _ ⌝%I).
          done.
          unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
          unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          replace (two_power_nat 32) with two32 ; last done.
          unfold two32.
          lia.
          unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
          unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          replace (two_power_nat 32) with two32 ; last done.
          unfold two32.
          lia.
          iIntros (w0) "[-> Hf]".
          iSimpl.
          iApply wp_wand_r.
          iSplitL "Hf Hwg".
          iApply (wp_set_global with "[] Hf Hwg").
          done.
          instantiate (1 := λ v, ⌜ v = immV [] ⌝%I).
          by iNext.
          iIntros (v0) "[[ -> Hwg] Hf]".
          iSimpl.
          iIntros (lh) "%Hfill".
          unfold lfilled, lfill in Hfill ; simpl in Hfill.
          apply b2p in Hfill ; subst.
          iApply wp_wand_r.
          iSplitL "Hf".
          iApply (wp_label_value with "Hf").
          done.
          instantiate (1 := λ v, ⌜ v = immV [] ⌝%I).
          done.
          iIntros (v0) "[-> Hf]".
          iExists _.
          iFrame.
          iIntros "Hf".
          iSimpl.
          iApply (wp_frame_value with "Hf").
          done.
          done.
          all: try by iIntros "[% _]".
          all: try by iIntros "[[% _] _]".
          instantiate ( 1 := λ v, (⌜ v = immV [] ⌝ ∗ ∃ g, (N.of_nat g↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int 20 |} ∨ N.of_nat g↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int (-1) |}) ∗ 7%N ↪[vis] {|
                                                                                                                                                                                                     modexp_name := name;
                           modexp_desc :=
                             MED_global (Mk_globalidx g)
                         |} )%I ).
(*          instantiate (1 := λ v1, ( ⌜ v1 = immV [] ⌝  ∗
                                                (* N.of_nat idf1↦[wf]FC_func_native i1 (Tf [T_i32] [T_i32]) l1 f1 ∗
                                            N.of_nat idf2↦[wf]FC_func_native i2 (Tf [T_i32] [T_i32]) l2 f2 ∗
                                            N.of_nat n↦[wmlength](0 + page_size)%N ∗
                                            N.of_nat idf0↦[wf]FC_func_native i0 (Tf [] [T_i32]) l0 f0 ∗
                                            isStack k [] n ∗
                                            N.of_nat idf3↦[wf]FC_func_native i3 (Tf [T_i32] [T_i32]) l3 f3 ∗ *)
                                                N.of_nat g↦[wg] {|
                                                  g_mut := MUT_mut ;
                                                  g_val := value_of_int 2
                                                |})%I). *)
          iNext.
          iSplit ; first done.
          iExists g.
          iFrame. }
          destruct Hret as [sh ->].
          iApply wp_value.
          unfold IntoVal.
          apply of_to_val.
          rewrite extend_retV.
          done.
          iIntros (lh) "%Hfill".
          unfold lfilled, lfill in Hfill.
          simpl in Hfill.
          apply b2p in Hfill ; subst.
          iApply wp_value.
          unfold IntoVal.
          apply of_to_val.
          unfold iris.to_val => /=.
          specialize (to_of_val (retV (sh_append sh [AI_basic
                      (BI_const
                         (VAL_int32 (Wasm_int.Int32.repr 4)));
                   AI_basic (BI_get_local 0);
                   AI_basic (BI_call 4);
                   AI_basic
                     (BI_const (VAL_int32 (Wasm_int.Int32.repr 6)));
                   AI_basic (BI_get_local 0);
                   AI_basic (BI_call 4);
                   i32const 0 ; AI_basic (BI_get_local 0) ; AI_basic (BI_call 5) ;                                  
                   AI_basic (BI_get_local 0);
                   AI_basic (BI_call 3);
                   AI_basic (BI_get_local 0);
                   AI_basic (BI_call 3);
                   AI_basic (BI_binop T_i32 (Binop_i BOI_sub));
                                                     AI_basic (BI_set_global 0)]))) as H.
          unfold to_val, iris.to_val, of_val in H.
          rewrite app_nil_r.
          destruct (merge_values_list _).
          inversion H.
          done.
          done.
          iExists _.
          iFrame.
          iIntros "Hf".
          iApply wp_return.
          3:{ unfold of_val.
              instantiate (1 := []).
              apply sfill_to_lfilled. } 
          done.
          done.
          iApply wp_value.
          unfold IntoVal.
          by apply of_to_val.
          iFrame.
          iSplit ; first done.
          iExists g.
          iFrame.
          by iIntros "[[[%H _] | [%H _]] _]" ; first done ;
            destruct H.
          all : try by iIntros "[%H _]".
          iIntros "[[H _] _]".
          iDestruct "H" as (k) "[%H _]".
          done. }
      iIntros (w0) "[[-> Hwg] Hf]".
      iFrame.
      iDestruct "Hwg" as (g') "[Hwg Hvis7]".
      iExists g', _.
      iFrame.
  Admitted.

  End Client.
End stack.    
      
