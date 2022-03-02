From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_use.
Require Export datatypes host operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Let expr := iris_use.expr.
Let val := iris_use.val.
Let to_val := iris_use.to_val.


Section Stack.
  
Import DummyHosts.
  (*
Variable host_function : eqType.


Let host := host.host host_function.
Let function_closure := function_closure host_function.
Let store_record := store_record host_function.


Variable host_instance : host.
*)

Let reduce := @reduce host_function host_instance.

(*
Let wasm_mixin : LanguageMixin _ _ _ := wasm_mixin host_instance.
 *)
Canonical Structure wasm_lang := Language wasm_mixin.

Let reducible := @reducible wasm_lang.

Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.
(*
(* TODO: Resolve duplicated notations *)
Notation "n ↦[wf]{ q } v" := (mapsto (L:=N) (V:=function_closure) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wf]{ q } v") : bi_scope.
Notation "n ↦[wf] v" := (mapsto (L:=N) (V:=function_closure) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wf] v") : bi_scope.
Notation "n ↦[wt]{ q } [ i ] v" := (mapsto (L:=N*N) (V:=funcelem) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wt]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wt][ i ] v" := (mapsto (L:=N*N) (V:=funcelem) (n, i) (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wt][ i ] v") : bi_scope.
Notation "n ↦[wm]{ q } [ i ] v" := (mapsto (L:=N*N) (V:=byte) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wm]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wm][ i ] v" := (mapsto (L:=N*N) (V:=byte) (n, i) (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wm][ i ] v") : bi_scope.
Notation "n ↦[wmlength] v" := (mapsto (L:=N) (V:=N) n (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wmlength] v") : bi_scope.
Notation "n ↦[wg]{ q } v" := (mapsto (L:=N) (V:=global) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wg]{ q } v").
Notation "n ↦[wg] v" := (mapsto (L:=N) (V:=global) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wg] v") .
Notation " ↪[frame]{ q } v" := (ghost_map_elem frameGName tt q v%V)
                           (at level 20, q at level 5, format " ↪[frame]{ q } v") .
Notation " ↪[frame] v" := (ghost_map_elem frameGName tt (DfracOwn 1) v%V)
                            (at level 20, format " ↪[frame] v").
Notation "n ↦[wms][ i ] l" := (mem_block_at_pos n l i)
                                (at level 20, format "n ↦[wms][ i ] l"): bi_scope.



Notation "'WP' e @ s ; E 'CTX' i ; lh {{ Φ } }" := (wp_wasm_ctx s E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh {{ Φ } }" := (wp_wasm_ctx NotStuck E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh ? {{ Φ } }" := (wp_wasm_ctx MaybeStuck E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e 'CTX' i ; lh {{ Φ } }" := (wp_wasm_ctx NotStuck ⊤ e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e 'CTX' i ; lh ? {{ Φ } }" := (wp_wasm_ctx MaybeStuck ⊤ e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ s ; E 'CTX_EMPTY' {{ Φ } }" := (wp_wasm_ctx s E e%E Φ 0 (LH_base [] []))
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.


Notation "'WP' e @ s ; E 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx s E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ s ; E 'CTX_EMPTY' {{ v , Q } }" := (wp_wasm_ctx s E e%E (λ v, Q) 0 (LH_base [] []))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'CTX_EMPTY'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx NotStuck E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @ '[' E  '/' ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx MaybeStuck E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' E  '/' ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx NotStuck ⊤ e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx MaybeStuck ⊤ e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.


Notation "'WP' e @ s ; E 'FRAME' n ; f {{ Φ } }" := (wp_wasm_frame s E e%E Φ n f)
  (at level 20, only parsing) : bi_scope.

Notation "'WP' e @ s ; E 'FRAME' n ; f {{ v , Q } }" := (wp_wasm_frame s E e%E (λ v, Q) n f)
  (at level 20, e, Q, n, f at level 200,
    format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ; f ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
*)
Section code.

Definition i32const (n:Z) := AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m n))).
Definition bi32const (n:Z) := BI_const (VAL_int32 (Wasm_int.int_of_Z i32m n)).
Definition value_of_int (n:Z) := VAL_int32 (Wasm_int.int_of_Z i32m n).


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


Section specs.

Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, (*!wstackG Σ*)!wlocsG Σ, !winstG Σ}.


(*Notation "m :: l ↦ v" := (load m l N.zero 4 = Some (bits v))%I (at level 50).*)
Definition points_to_i32 n i v :=
  (∃ a b c d, n ↦[wm][ i ] a ∗ n ↦[wm][N.add i 1] b ∗
                n ↦[wm][N.add i 2] c ∗ n ↦[wm][N.add i 3] d ∗
                ⌜ bits v = [a ; b ; c ; d] ⌝)%I.
Notation "n ↦[i32][ k ] v" := (points_to_i32 n k v) (at level 50).




Definition isStack v l f0 :=
  (∃ n, ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
                                                ∃ st_p, N.of_nat n ↦[i32][ Z.to_N v ]
                                                                 (value_of_int st_p) ∗
                                                                 ⌜ ((st_p - v - 4)/4)%Z =
                                                          length l ⌝ ∗
                                                                 ([∗ list] i ↦ w ∈ l,
                                                                   N.of_nat n ↦[i32][ Z.to_N (st_p - 4 - 4 * i)%Z ] w) ∗
                                                                 ∀ k, ⌜ (k >= st_p)%Z ⌝ -∗ ⌜ (k < v + 16384)%Z ⌝ -∗ ∃ bk, N.of_nat n ↦[wm][ Z.to_N k ] bk)%I.

Notation "{{{ P }}} es {{{ v, 'RET' v ; Q }}}" :=
  (∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP es @ NotStuck ; ⊤ (*CTX_EMPTY*) {{ v, Φ v }}) (at level 50).
   
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
  



Lemma spec_new_stack f0 n len : 
  {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
                                              ⌜ length (f_locs f0) >= 1 ⌝ ∗
                                              ↪[frame] f0 ∗
                                              N.of_nat n ↦[wmlength] len }}}
    new_stack
    {{{ v, RET v ; (∃ (k : Z), ⌜ v = immV [value_of_int k] ⌝ ∗
                                         (⌜ (k = -1)%Z ⌝ ∗
                                          N.of_nat n↦[wmlength] len ∨
                                            isStack k [] f0 ∗
                                          N.of_nat n ↦[wmlength] (len + page_size)%N)%I) }}}.
Proof.
  iIntros (Φ) "(%Hinst & %Hflocs & Hframe & Hlen) HΦ".
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
    destruct w ; last by iDestruct "H" as "[[[%Habs _ ]| [%Habs _]] _]" ; inversion Habs.
    destruct l ; first by iDestruct "H" as "[[[%Habs _ ]| [%Habs _]] _]" ; inversion Habs.
    destruct l ; last by iDestruct "H" as "[[[%Habs _ ]| [%Habs _]] _]" ; inversion Habs.
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
    destruct w ; last by destruct (v == value_of_int (-1)).
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
      admit.
      iLeft.
      by iSplit.
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
        replace (N.of_nat (N.to_nat len + 0)) with len ; last lia.
        replace (N.of_nat (N.to_nat len + 1)) with (len + 1)%N ; last lia.
        replace (N.of_nat (N.to_nat len + 2)) with (len + 1 + 1)%N ; last lia.
        replace (N.of_nat (N.to_nat len + 3)) with (len + 1 + 1 + 1)%N ; last lia.
        iFrame. }
      remember (Wasm_int.Int32.repr (ssrnat.nat_of_bin (len `div` page_size))) as c.
      iApply wp_wand_r.        
      instantiate (1 := λ x, ((⌜ x = immV [value_of_int (N.to_nat len)] ⌝ ∗ N.of_nat n↦[i32][ len ] (value_of_int (N.to_nat len + 4))) ∗ ↪[frame] {| f_locs := set_nth (VAL_int32 c) (f_locs f0) 0
                        (VAL_int32 (Wasm_int.Int32.imul c (Wasm_int.Int32.repr 65536))); f_inst := f_inst f0 |} )%I).
      iSplitL "Hf Hbs".
      * iApply wp_wasm_empty_ctx.
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
        (* Left to find some lemmas to take care of modding by 2^32 here. *)
        admit.
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
        (* Numerical goal to be resolved *)
        admit.
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
        admit.
      * (* clears some of the non-trap subgoals at this point. TODO: restructure this so that we don't get all of these at the end *)
        all: try by iIntros "(%HContra & _)".
        by iIntros "((%HContra & _) & _)".
      * iIntros (w) "[[-> Hn] Hf]".
        iApply "HΦ".
        iExists _.
        iSplit ; first done.
        iRight.
        iSplitR "Hlen" ; last done.
        unfold isStack.
        iExists _.
        iSplit ; first done.
        replace (Z.to_N (N.to_nat len)) with len ; last lia.
        iExists _.
        iSplitL "Hn" ; first done.
        iSplit.
        iPureIntro. unfold length.
        rewrite Z.add_simpl_l.
        rewrite Z.sub_diag.
        by rewrite Z.div_0_l.
        unfold big_opL.
        iSplit ; first done.
        iIntros (k) "%Hk1 %Hk2".
        iExists b.
        
Admitted.
        
                                                                           
        
