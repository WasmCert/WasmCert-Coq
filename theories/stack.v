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


Section stack.
  
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
             



Section specs.

Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, (*!wstackG Σ*)!wlocsG Σ, !winstG Σ}.


(*Notation "m :: l ↦ v" := (load m l N.zero 4 = Some (bits v))%I (at level 50).*)
Definition points_to_i32 n i v :=
  (∃ a b c d, n ↦[wm][ i ] a ∗ n ↦[wm][N.add i 1] b ∗
                n ↦[wm][N.add i 2] c ∗ n ↦[wm][N.add i 3] d ∗
                ⌜ bits v = [a ; b ; c ; d] ⌝)%I.
Notation "n ↦[i32][ k ] v" := (points_to_i32 n k v) (at level 50).



Lemma of_nat_to_nat_plus a b :
  N.of_nat (N.to_nat a + b) = (a + N.of_nat b)%N.
Proof. lia. Qed.

Lemma i32_wms n i v :
  types_agree T_i32 v -> 
  n ↦[i32][ i ] v ⊣⊢ n ↦[wms][ i ]bits v.
Proof.
  intros Htype.
  iSplit ; iIntros "H" ; unfold mem_block_at_pos, points_to_i32.
  - iDestruct "H" as (a b c d) "(? & ? & ? & ? & ->)".
    iSimpl.
    repeat rewrite of_nat_to_nat_plus.
    rewrite N.add_0_r.
    iFrame.
  - remember (bits v) as bs.
    assert (length bs = length (bits v)) ; first by rewrite Heqbs.
    erewrite length_bits in H => //.
    simpl in H.
    repeat destruct bs => //=.
    repeat rewrite of_nat_to_nat_plus.
    rewrite N.add_0_r.
    iDestruct "H" as "(? & ? & ? & ? & _)".
    iExists _,_,_,_.
    iFrame.
    done.
Qed.
    
  



Definition isStack v l n :=
  (let st_p := (v + 4 + length l * 4)%Z in
    ⌜ (two16 | v)%Z ⌝ ∗ ⌜ (length l < two14)%Z ⌝ ∗
   N.of_nat n ↦[i32][ Z.to_N v ]
            (value_of_int st_p) ∗
            ([∗ list] i ↦ w ∈ l,
              N.of_nat n ↦[i32][ Z.to_N (st_p - 4 - 4 * i)%Z ] w) ∗
  (*            ∀ k, ⌜ (k >= st_p)%Z ⌝ -∗ ⌜ (k < v + 16384)%Z ⌝ -∗ ∃ bk, N.of_nat n ↦[wm][ Z.to_N k ] bk *)
            ∃ bs, ⌜ (Z.of_nat (length bs) = two16 - 4 - length l * 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N st_p] bs
                                                        
                                                         
 )%I.

(*
Definition isStack v l n :=
  (∃ st_p, N.of_nat n ↦[i32][ Z.to_N v ]
                    (value_of_int st_p) ∗
                    ⌜ ((st_p - v - 4)/4)%Z =
             length l ⌝ ∗
                    ([∗ list] i ↦ w ∈ l,
                      N.of_nat n ↦[i32][ Z.to_N (st_p - 4 - 4 * i)%Z ] w) ∗
                    ∀ k, ⌜ (k >= st_p)%Z ⌝ -∗ ⌜ (k < v + 16384)%Z ⌝ -∗ ∃ bk, N.of_nat n ↦[wm][ Z.to_N k ] bk)%I. *)

Notation "{{{ P }}} es {{{ v , Q }}}" :=
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

Lemma separate5 {A} (a : A) b c d e l :
  a :: b :: c :: d :: e :: l = [a ; b ; c ; d ; e] ++ l.
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
  {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
                                              ⌜ length (f_locs f0) >= 1 ⌝ ∗
                                                                       ⌜ (Wasm_int.Int32.modulus - 1)%Z <>
                                           Wasm_int.Int32.Z_mod_modulus (ssrnat.nat_of_bin (len `div` page_size)) ⌝ ∗
                                                                        ⌜ (len + 4 < Z.to_N (two_power_nat 32))%N ⌝ ∗
                                                                        ⌜ (page_size | len)%N ⌝ ∗
                                                                                              
                                                                        
                                                                        ↪[frame] f0 ∗
                                                                        N.of_nat n ↦[wmlength] len }}}
    new_stack
    {{{ v, (∃ (k : Z), ⌜ v = immV [value_of_int k] ⌝ ∗
                                         (⌜ (k = -1)%Z ⌝ ∗
                                          N.of_nat n↦[wmlength] len ∨
                                            isStack k [] n ∗
                                          N.of_nat n ↦[wmlength] (len + page_size)%N)%I) }}}.
Proof.
  iIntros (Φ) "(%Hinst & %Hflocs & %Hmod & %Hlenoverflow4 & %Hlendiv & Hframe & Hlen) HΦ".
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
        repeat rewrite of_nat_to_nat_plus ; rewrite N.add_0_r.
        replace (len + 1 + 1)%N with (len + 2)%N ; last lia.
        replace ( len + 2+ 1)%N with (len + 3)%N ; last lia.
        iFrame. }
      remember (Wasm_int.Int32.repr (ssrnat.nat_of_bin (len `div` page_size))) as c.
      iApply wp_wand_r.        
      instantiate (1 := λ x, ((⌜ x = immV [value_of_int (N.to_nat len)] ⌝ ∗ N.of_nat n↦[i32][ len ] (value_of_int (N.to_nat len + 4))) ∗ ↪[frame] {| f_locs := set_nth (VAL_int32 c) (f_locs f0) 0
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
        iRight.
        iSplitR "Hlen" ; last done.
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
Qed.
(*        iIntros (k) "%Hk1 %Hk2".
        iExists b.
        unfold mem_block_at_pos.
        iDestruct (big_sepL_delete with "Hb") as "[Hb _]".
        instantiate (1 := b).
        instantiate (1 := N.to_nat (Z.to_N k - len - 4)%N).
        apply repeat_lookup.
        lia.
        rewrite - N2Nat.inj_add.
        rewrite N2Nat.id.
        replace (len + 1 + 1 + 1 + 1)%N with (len + 4)%N ; last lia.
        replace (len + 4 + (Z.to_N k - len - 4))%N with (Z.to_N k) ; last lia.
        iFrame.
Qed. *)


Lemma spec_is_empty f0 n v s : 
  {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
                                              ⌜ (f_locs f0) !! 0 = Some (value_of_int v) ⌝ ∗ 
                                              ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - length s * 4)%Z ⌝ ∗ 
                                                                        ↪[frame] f0 ∗
                                                                        isStack v s n }}}
    is_empty
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s n ∗
                                   ⌜ (k = 1 /\ s = []) \/
                          (k = 0 /\ s <> []) ⌝ }}}.
Proof.
  iIntros (Φ) "(%Hinst & %Hlocv & %Hv & Hf & Hstack) HΦ".
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
    exact f0.(f_inst).   
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
Qed.
    
    
Lemma spec_is_full f0 n v s : 
  {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
                                              ⌜ (f_locs f0) !! 0 = Some (value_of_int v) ⌝ ∗ 
                                              ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - length s * 4 )%Z ⌝ ∗ 
                                                                        ↪[frame] f0 ∗
                                                                        isStack v s n }}}
    is_full
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s n ∗
                           ⌜ k = 1 \/ (length s < two14 - 1)%Z ⌝ }}}.
Proof.
  iIntros (Φ) "(%Hinst & %Hlocv & %Hv & Hf & Hstack) HΦ".
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
    exact f0.(f_inst).
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
    lia.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    destruct ((v + 4 + length s * 4) `mod` 65536)%Z eqn:Hmod.
  - iApply wp_wand_r.
    iSplitL "Hf".
    iApply (wp_select_false with "Hf") => //.
    instantiate (1 := λ x, ⌜ x = immV [value_of_int 1] ⌝%I).
    done.
    iIntros (w) "[-> Hf]".
    iApply "HΦ".
    iExists _.
    iSplitR => //=.
    iFrame.
    iLeft.
    done.
  - iApply wp_wand_r.
    iSplitL "Hf".
    iApply (wp_select_true with "Hf") => //.
    unfold Wasm_int.int_of_Z => //=.
    unfold Wasm_int.Int32.zero.
    intro Habs.
    apply Wasm_int.Int32.repr_inv in Habs => //=.
    rewrite <- Hmod.
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
    lia.
  - assert ( 0 <= v + 4 + length s * 4 )%Z ; first lia.
    assert (0 <65536)%Z ; first lia.
    apply (Z.mod_bound_pos _ _ H) in H0 as [Habs _].
    rewrite Hmod in Habs.
    lia.
Qed.    



Lemma spec_pop f0 n v a s :
  {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
                                              ∗ ⌜ f0.(f_locs) !! 0 = Some (value_of_int v) ⌝
                                                                          ∗ ⌜ length f0.(f_locs) >= 2 ⌝
                                                                                                     ∗ ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - S (length s) * 4 )%Z ⌝
                                                                                                     ∗ ⌜ types_agree T_i32 a ⌝
                                                                                                     ∗ isStack v (a :: s) n
                                                                                                     ∗ ↪[frame] f0 }}}
    pop
    {{{ w, ⌜ w = immV [a] ⌝ ∗ isStack v s n }}}.
Proof.
  iIntros (Φ) "(%Hinst & %Hlocv & %Hlocs & %Hv & %Ha & Hstack & Hf) HΦ".
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
    instantiate ( 1 := λ x, ((((⌜ x = immV [ value_of_int (v + 4 + length (a :: s) * 4)%Z] ⌝
                                           ∗ [∗ list] i↦w ∈  (a :: s),
                                 N.of_nat n ↦[i32][ Z.to_N (v + 4 + length (a :: s) * 4 - 4 - 4 * i)] w) ∗

                                                                                                        (∃ bs, ⌜ (Z.of_nat (length bs) = two16 - 4 - length (a :: s) * 4)%Z ⌝ ∗ N.of_nat n ↦[wms][Z.to_N (v + 4 + length (a :: s) * 4)]bs)
                              (*(∀ k, ⌜(k >= v + 4 + length (a :: s) * 4)%Z⌝ -∗
                                                                                                         ⌜(k < v + 16384)%Z⌝ -∗ ∃ bk, N.of_nat n ↦[wm][Z.to_N k] bk) *))
                                ∗  N.of_nat n↦[wms][(Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m v) + N.zero)%N]bits (value_of_int (v + 4 + length (a :: s) * 4)) )
                               ∗ ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[[[[%Habs _] _] _] _]".
    iDestruct "Hstack" as "(%Hdiv & %Hlen & Hv & Hs & Hrest)".
    iSplitR "HΦ".
  - iApply wp_load => //.
    exact f0.(f_inst).
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
  - iIntros (w) "[[[[->  Hs] Hrest] Hp] Hf]".
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
    replace (v + 4 + S (length s) * 4 - 4)%Z with (v + S (length s) * 4)%Z ; first done.
    lia.
    unfold Wasm_int.Int32.max_unsigned.
    unfold Wasm_int.Int32.modulus.
    unfold Wasm_int.Int32.wordsize.
    unfold Integers.Wordsize_32.wordsize.
    replace (two_power_nat 32) with 4294967296%Z ; last done.
    lia.
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
    iApply (wp_seq _ _ _ (λ x, (((⌜ x = immV [a] ⌝ ∗ N.of_nat n ↦[i32][Z.to_N v] value_of_int (v + 4 + length (a :: s) * 4) ∗ ([∗ list] i↦w ∈ s, N.of_nat n ↦[i32][ Z.to_N (v + 4 + (length s) * 4 - 4 - 4 * i)] w) ∗ (∃ bs, ⌜ (Z.of_nat (length bs) = two16 - 4 - length (a :: s) * 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N (v + 4 + length (a :: s) * 4)] bs) (* (∀ k, ⌜ (k >= v + 4 + length (a :: s) * 4)%Z⌝ -∗ ⌜ (k < v + 16384)%Z⌝ -∗ ∃ bk, N.of_nat n↦[wm][Z.to_N k]bk) *)) ∗
                                                                                                                                                                                                                                                                                                                                  N.of_nat n ↦[wms][Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m (v + S (length s) * 4)) + N.zero] bits a )∗ ↪[frame] f1 )%I)).
    iDestruct "Hstack" as "(_ & _ & Hp & Hs & Hrest)".
    iSplitR ; first by iIntros "[[[%Habs _] _] _]".
    iSplitR "HΦ".
  - iApply wp_load => //.
    exact f1.(f_inst).
    by subst f1 => //=.
    iFrame.
    rewrite separate1.
    iDestruct (big_sepL_app with "Hs") as "[Ha Hs]".
    iSplitR "Ha".
    iSplitR => //=.
    iApply (big_sepL_impl with "Hs").
    iIntros "!>" (k x) "%Hlookup Hp".
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
    done.
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
  - iIntros (w) "[[(-> & Hp & Hs & Hrest) Ha] Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate2.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [a ; value_of_int v] ⌝ ∗ ↪[frame] f1)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "Hf") => //=.
    subst f1 => //=.
    unfold set_nth.
    destruct (f_locs f0) => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate3.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [a ; value_of_int v ;
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
    instantiate (1 := λ x, ((⌜ x = immV [a] ⌝ ∗
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
    repeat iSplit => //.
    iPureIntro. lia.
    iFrame.
    iSplitL "Hp".
  - simpl. rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    rewrite N.add_0_r.
    iApply i32_wms => //.
    unfold value_of_int => /=.
    replace (v + S (length s) * 4)%Z with (v + 4 + length s * 4)%Z ; last lia.
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
    iExists (bits a ++ bs).
    iSplitR.
    iPureIntro.
    rewrite app_length.
    simpl in Hbs.
    rewrite - (Nat2Z.id (length bs)).
    rewrite Hbs.
    erewrite length_bits => //.
    unfold t_length.
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
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    replace (v + S (length s) * 4)%Z with (v + 4 + length s * 4)%Z ; last lia.
    done.
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (k x) "%Hbits H".
    repeat rewrite of_nat_to_nat_plus.
    erewrite length_bits => //.
    unfold t_length.
    replace (Z.to_N (v + 4 + length (a :: s) * 4) + N.of_nat k)%N
      with (Z.to_N (v + 4 + length s * 4) + N.of_nat (4+k))%N ; first done.
    simpl.
    lia.
Qed.    
    

(* 


    iIntros (k) "%Hkm %HkM".
    destruct (decide (k >= v + 4 + S (length s) * 4)%Z).
    iApply "Hrest" => //=.
    unfold mem_block_at_pos.
    remember (bits a) as bs.
    assert (length bs = length (bits a)) ; first by rewrite Heqbs.
    erewrite length_bits in H => //=.
    simpl in H.
    repeat destruct bs => //=.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv; lia.
    rewrite N.add_0_r.
    repeat rewrite of_nat_to_nat_plus.
    rewrite N.add_0_r.
    iDestruct "Ha" as "(? & ? & ? & ? & _)".
    destruct (Z.to_nat (k - v - 4 - length s * 4)%Z) eqn:Hk.
    assert (Z.to_N k = Z.to_N (v + S (length s) * 4)) ; first lia.
    iExists _.
    by rewrite H0.
    destruct n1.
    assert ( Z.to_N k = Z.to_N (v + S (length s) * 4) + 1)%N ; first lia.
    iExists _.
    by rewrite H0.
    destruct n1.
    assert ( Z.to_N k = Z.to_N (v + S (length s) * 4) + 2)%N ; first lia.
    iExists _.
    by rewrite H0.
    destruct n1.
    assert ( Z.to_N k = Z.to_N (v + S (length s) * 4) + 3)%N ; first lia.
    iExists _.
    by rewrite H0.
    lia.
Qed. *)
    
    

    
                                                                         
                                                                        
    
Lemma spec_push f0 n v a s :
  {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
                                              ∗ ⌜ f0.(f_locs) !! 0 = Some a ⌝ 
                                              ∗ ⌜ f0.(f_locs) !! 1 = Some (value_of_int v) ⌝
                                                                          ∗ ⌜ length f0.(f_locs) >= 3 ⌝
                                                                                                     ∗ ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - S (length s) * 4 )%Z ⌝
                                                                                                     ∗ ⌜ types_agree T_i32 a ⌝
                                                                                                     ∗ ⌜ (length s < two14 - 1)%Z ⌝
                                                                                                     ∗ isStack v s n
                                                                                                     ∗ ↪[frame] f0 }}}
    push
    {{{ w, ⌜ w = immV [] ⌝ ∗ isStack v (a :: s) n }}}.
Proof.
  iIntros (Φ) "(%Hinst & %Hloca & %Hlocv & %Hlocs & %Hv & %Ha & %Hlens & Hstack & Hf) HΦ".
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
    exact f0.(f_inst).
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
                                        a] ⌝ ∗ ↪[frame] f1)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "Hf") => //.
    subst f1 => /=.
    unfold set_nth.
    destruct (f_locs f0) => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate3.
    iApply wp_seq.
    instantiate
      (1 := λ x, (((⌜ x = immV [] ⌝ ∗ N.of_nat n↦[i32][ Z.to_N v] value_of_int (v+4+length s * 4) ∗ ([∗ list] i↦w ∈ s, N.of_nat n↦[i32][Z.to_N (v + 4 + length s * 4 - 4 - 4 * i)] w) ∗ (∃ bs, ⌜ Z.of_nat (length bs) = (two16 - 4 - length (s) * 4 - 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N (v + 4 + S (length s) * 4)]bs) (* (∀ k, ⌜ (k >= v + 4 + S (length s) * 4)%Z ⌝ -∗ ⌜ (k < v + 16384)%Z ⌝ -∗ ∃ bk, N.of_nat n↦[wm][Z.to_N k]bk) *))
                     ∗ N.of_nat n ↦[wms][Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m (v + 4 + length s * 4)%Z) + N.zero]bits a) ∗ ↪[frame] f1)%I).
    iSplitR ; first by iIntros "[[[ %Habs _ ] _] _]".
    iDestruct "Hstack" as "(_ & _ & Hp & Hs & Hrest)".
    iDestruct "Hrest" as (bs) "[%Hbs Hrest]".
    unfold two16 in Hbs.
    unfold two14 in Hlens.
    do 4 (destruct bs ; first by simpl in Hbs ; lia).
    rewrite separate4.
    unfold mem_block_at_pos at 1.
    rewrite big_sepL_app.
    iDestruct "Hrest" as "[Ha Hrest]".
    iSplitR "HΦ".
  - iApply wp_store => //.
    instantiate (1 := [b ; b0 ; b1 ; b2]) => //=.
    subst f1 => //=.
    iFrame.
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
    iIntros "!>" (k x) "%Hbits H".
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
    done.
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
    rewrite Wasm_int.Int32.unsigned_repr ; last lia.
    rewrite Wasm_int.Int32.unsigned_repr.
    unfold value_of_int => //=.
    replace (v + 4 + length s * 4 + 4)%Z with (v + 4 + S (length s) * 4)%Z => //=.
    lia.
    unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
    unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
    replace (two_power_nat 32) with two32 ; last done.
    unfold two32 ; lia.
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
    unfold value_of_int => //=.
  - iIntros (w) "[[-> Hp] Hf]".
    iApply "HΦ".
    iSplit => //=.
    unfold isStack.
    repeat iSplit => //=.
    iPureIntro ; unfold two14 ; lia.
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
    replace (v + 4 + S (length s) * 4 - 4 - 4 * 0%nat)%Z
      with (v + 4 + length s * 4)%Z ; last lia.
    done.
    iApply (big_sepL_impl with "Hs").
    iIntros "!>" (k x) "%Hbits H".
    replace (v + 4 + S (length s) * 4 - 4 - 4 * S k)%Z
      with  (v + 4 + length s * 4 - 4 - 4 * k)%Z ; last lia.
    done.
    iDestruct "Hrest" as (bs0) "[%Hbs0 Hrest]".
    iExists bs0.
    iSplit => //=.
    iPureIntro.
    lia.
Qed.
                                        
    
    
    
    
    
                                                           
                   
    
    

