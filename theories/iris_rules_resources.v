From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export datatypes host operations properties opsem.
Require Import Coq.Program.Equality.
Require Export iris iris_locations iris_properties iris_atomicity iris_wp_def stdpp_aux.

Import uPred.

Set Default Proof Using "Type". (* what is this? *)

Close Scope byte_scope.

Definition mem_block `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ} (n: N) (m: memory) :=
  (([∗ list] i ↦ b ∈ (m.(mem_data).(ml_data)), n ↦[wm][ (N.of_nat i) ] b ) ∗
     n ↦[wmlength] mem_length m)%I.
(* mem_size_exact (N.succ_pos n) (mem_size m))%I*)

Definition mem_block_at_pos `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ} (n: N) (l:bytes) k :=
  ([∗ list] i ↦ b ∈ l, n ↦[wm][ (N.of_nat (N.to_nat k+i)) ] b)%I.


Notation "n ↦[wmblock] m" := (mem_block n m)
                           (at level 20, format "n ↦[wmblock] m"): bi_scope.
Notation "n ↦[wms][ i ] l" := (mem_block_at_pos n l i)
                                (at level 20, format "n ↦[wms][ i ] l"): bi_scope.

(* Predicate for memory blocks *)

Section iris_rules_resources.

Import DummyHosts.

Let reduce := @reduce host_function host_instance.

Let reducible := @reducible wasm_lang.

Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.
(* TODO: switch to monotone implementation of mem_size once we have that? *)


Definition mem_block_equiv (m1 m2: memory) :=
  m1.(mem_data).(ml_data) = m2.(mem_data).(ml_data).

Notation "m1 ≡ₘ m2" := (mem_block_equiv m1 m2)
                        (at level 70, format "m1 ≡ₘ m2").


(* Instance related *)

Lemma wp_get_local (s : stuckness) (E : coPset) (v: value) (i: nat) (ϕ: iris.val -> Prop) f0 :
  (f_locs f0) !! i = Some v -> 
  ϕ (immV [v]) ->
  ↪[frame] f0 -∗
  WP ([AI_basic (BI_get_local i)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hlook Hϕ) "Hli".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] inst].
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ?)".
  iDestruct (ghost_map_lookup with "Hl Hli") as "%Hli".
  simplify_map_eq.
  (* rewrite gmap_of_list_lookup Nat2N.id in Hli. *)
  rewrite - nth_error_lookup in Hlook.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    exists [], [AI_basic (BI_const v)], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    by apply r_get_local.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
    iFrame "# ∗ %".
Qed.

Lemma wp_set_local (s : stuckness) (E : coPset) (v : value) (i: nat) (ϕ: iris.val -> Prop) f0 :
  i < length (f_locs f0) ->
  ϕ (immV []) ->
  ↪[frame] f0 -∗
  WP ([AI_basic (BI_const v); AI_basic (BI_set_local i)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ ↪[frame] (Build_frame (set_nth v (f_locs f0) i v) (f_inst f0)) }}.
Proof.
  iIntros (Hlen Hϕ) "Hli".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] inst].
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ?)".
  iDestruct (ghost_map_lookup with "Hl Hli") as "%Hli".
  simplify_map_eq.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    exists [], [], (hs, ws, set_nth v locs i v, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_set_local => //=.
    rewrite -(rwP ssrnat.leP). lia.
  - iIntros "!>" (es σ2 efs HStep).
    (* modify locs[i]. This has to be done before the update modality is used. *)
    iMod (ghost_map_update (Build_frame (set_nth v locs i v) inst) with "Hl Hli") as "(Hl & Hli)".
    iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H as [H | [ [? Hstart] | [[ a [cl [tf [h [Hstart [Hnth Hcl]]]]] ] | (?&?&?&Hstart & Hstart1 & Hstart2
                                                               & Hσ)]]] ;
      last (eapply r_set_local with (f' := {| f_locs := set_nth v locs i v; f_inst := inst |}); eauto) ;
    try by unfold first_instr in Hstart ; simpl in Hstart ; inversion Hstart.
    inversion H; subst; clear H. simpl.
    iFrame "# ∗ %". rewrite insert_insert. iFrame. auto.
    rewrite -(rwP ssrnat.leP) /=. lia.
Qed.

Lemma wp_tee_local (s : stuckness) (E : coPset) (v : value) (i : nat) (Φ : iris.val -> iProp Σ) f :
  ⊢ ↪[frame] f -∗
    (↪[frame] f -∗ WP [AI_basic (BI_const v) ; AI_basic (BI_const v) ;
                       AI_basic (BI_set_local i)]
     @ s ; E {{ Φ }}) -∗
             WP [AI_basic (BI_const v) ; AI_basic (BI_tee_local i)] @ s ; E {{ Φ }}.
Proof.
  iIntros "Hf Hwp".
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  destruct σ as [[[ hs ws ] locs ] inst ].
  iApply fupd_mask_intro ; first by solve_ndisj.
  iIntros "Hfupd".
  iDestruct "Hσ" as "(? & ? & ? & ? & ? & ?)".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => //=.
    eexists _,_,(_,_,_,_),_.
    repeat split => //=.
    by apply r_simple, rs_tee_local.
  - iIntros "!>" (es σ2 efs HStep).
    iMod "Hfupd".
    iModIntro.
    destruct σ2 as [[[ hs' ws'] locs' ] inst' ] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
    iApply bi.sep_exist_l. iExists _. iFrame.
Qed.


(*
(* tee_local is not atomic in the Iris sense, since it requires 2 steps to be reduced to a value. *)
Lemma wp_tee_local (s : stuckness) (E : coPset) (v v0: value) (n: nat) (ϕ: val -> Prop):
  (not (ϕ trapV)) ->
  ϕ (immV [v]) ->
  N.of_nat n ↦[wl] v0 ⊢
  WP ([AI_basic (BI_const v); AI_basic (BI_tee_local n)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ N.of_nat n ↦[wl] v }}.
Proof.
  iIntros (Hntrap Hϕ) "Hli".
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  destruct σ as [[[hs ws] locs] inst].
  iApply fupd_mask_intro; first by solve_ndisj.
  iIntros "Hfupd".
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ? & ?)".
  iDestruct (gen_heap_valid with "Hl Hli") as "%Hli".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v); AI_basic (BI_const v); AI_basic (BI_set_local n)], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_tee_local => //.
  - iIntros "!>" (es σ2 efs HStep).
    iMod "Hfupd".
    iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
    inversion H; subst; clear H.
    iFrame.
    repeat iSplit => //.
    iApply wp_val => //=.
    iSplitR => //; first by iIntros "(%HContra & _)". 
    iApply wp_mono; last iApply wp_set_local; eauto => //.
Qed.

(* r_get_global involves finding the reference index to the global store via
   the instance first. *)

(* TODO: Weaken the ownership of instance (and global) *)
Lemma wp_get_global (s : stuckness) (E : coPset) (v: value) (inst: instance) (n: nat) (ϕ: val -> Prop) (g: global) (k: nat):
  inst.(inst_globs) !! n = Some k ->
  g.(g_val) = v ->
  ϕ (immV [v]) ->
  (↦[wi] inst ∗
  N.of_nat k ↦[wg] g) ⊢
                      WP ([AI_basic (BI_get_global n)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ ↦[wi] inst ∗ N.of_nat k ↦[wg] g }}.
Proof.
  iIntros (Hinstg Hgval Hϕ) "(Hinst & Hglob)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hg & ? & Hi & ?)".
  iDestruct (gen_heap_valid with "Hg Hglob") as "%Hglob".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  rewrite gmap_of_list_lookup Nat2N.id in Hglob.
  rewrite - nth_error_lookup in Hglob.
  rewrite - nth_error_lookup in Hinstg.
  rewrite lookup_insert in Hinst.
  inversion Hinst; subst; clear Hinst.
  assert ( sglob_val (host_function:=host_function) ws
                     (f_inst {| f_locs := locs; f_inst := inst |}) n =
           Some (g_val g) ) as Hsglob.
  { unfold sglob_val, option_map, sglob, option_bind, sglob_ind => /=.
    by rewrite Hinstg Hglob.
  }
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (g_val g))], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    by apply r_get_global.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] winst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
Qed.
(*
Print  sglob_val.
Print supdate_glob.
*)
Lemma wp_set_global (s : stuckness) (E : coPset) (v:value) (inst :instance) (n:nat)
      (Φ : val -> Prop) (g: global) (k:nat):
  inst.(inst_globs) !! n = Some k ->
  Φ (immV []) ->
  ( ↦[wi] inst ∗
    N.of_nat k ↦[wg] g) ⊢
                        WP [AI_basic (BI_const v) ; AI_basic (BI_set_global n)] @ s ; E {{ w,  ⌜ Φ w ⌝ ∗ ↦[wi] inst ∗ N.of_nat k ↦[wg] {| g_mut := g_mut g ; g_val := v |} }}.
Proof.
  iIntros (Hinstg HΦ) "[Hinst Hglob]".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[ hs ws] locs ] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hg & ? & Hi & ?)". 
  iDestruct (gen_heap_valid with "Hg Hglob") as "%Hglob".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  rewrite gmap_of_list_lookup Nat2N.id in Hglob.
  rewrite - nth_error_lookup in Hglob.
  rewrite - nth_error_lookup in Hinstg.
  rewrite lookup_insert in Hinst.
  inversion Hinst ; subst ; clear Hinst.
  iDestruct (gen_heap_update with "Hg Hglob") as "H".
  remember {|
      s_funcs := datatypes.s_funcs ws;
      s_tables := datatypes.s_tables ws;
      s_mems := datatypes.s_mems ws;
      s_globals :=
        update_list_at (datatypes.s_globals ws) k
          {| g_mut := g_mut g; g_val := v |}
    |} as ws'.
  assert ( supdate_glob (host_function := host_function) ws
                     (f_inst {| f_locs := locs ; f_inst := inst |}) n v =
             Some ws') as Hsglob.
  { unfold supdate_glob, option_bind, sglob_ind, supdate_glob_s, option_map => /=.
    by rewrite Hinstg Hglob Heqws'. }
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], (hs, ws', locs, inst), [].
    unfold language.prim_step => /=. repeat split => /=.
    by apply r_set_global.
  - iIntros "!>" (es σ2 efs Hstep). iMod "H". iModIntro. 
    destruct σ2 as [[[ hs2 ws2 ] locs' ] inst'].
    destruct Hstep as (H & -> & ->).
    eapply reduce_det in H as [H | [Hstart | [[a Hstart] | (Hstart & Hstart1 & Hstart2
                                                            & Hσ)]]] ;
      last (by econstructor) ; try by unfold first_instr in Hstart ; inversion Hstart.
    inversion H ; subst ; clear H.
    iDestruct "H" as "[Hg Hk]". iFrame.
    destruct ws => //=. simpl in Hsglob.
    assert (N.to_nat (N.of_nat k) < length s_globals) as Hlen.
    { rewrite Nat2N.id. simpl in Hglob. apply nth_error_Some.
      rewrite Hglob ; done. }
    rewrite <- (gmap_of_list_insert (l:= s_globals) {| g_mut := g_mut g ;
                                                     g_val := v |} (n := N.of_nat k) Hlen).
    rewrite Nat2N.id.
    cut (<[k:={| g_mut := g_mut g ; g_val := v |}]> s_globals =
           update_list_at s_globals k {| g_mut := g_mut g ; g_val := v |}).
    intro Heq ; rewrite Heq. repeat iSplit => //=.
    rewrite Nat2N.id in Hlen. unfold update_list_at.
    clear - Hlen. 
    generalize dependent s_globals. 
    induction k ; intros s_globals Hlen. 
    { destruct s_globals.
      { exfalso. simpl in Hlen. lia. }
      simpl. unfold drop. done. }
    destruct s_globals. { exfalso ; simpl in Hlen ; lia. }
    simpl. simpl in IHk. assert (k < (length s_globals)). { simpl in Hlen. lia. }
    rewrite (IHk s_globals H). done.
Qed.


Lemma update_list_same_dom (l : seq.seq global) k v :
  k < length l -> 
  dom (gset N) (gmap_of_list l) = dom (gset N) (gmap_of_list (update_list_at l k v)).
Proof.
  induction k ; unfold update_list_at. 
  destruct l. simpl. intro ; exfalso ; lia.
  intro ; simpl. destruct l. simpl. unfold gmap_of_list. simpl.
  unfold dom, gset_dom, mapset.mapset_dom, mapset.mapset_dom_with, merge, gmap_merge.
  unfold merge, pmap.Pmerge. Search (gmap_of_list _).
  
Admitted. *)

(* Auxiliary lemmas for load/store *)

Lemma mem_update_length dat dat' k b:
  mem_update k b dat = Some dat' -> length (ml_data dat) = length (ml_data dat').
Proof.
  intros Hupd.
  unfold mem_update in Hupd.
  destruct ( _ <? _)%N eqn:Hl ; inversion Hupd.
  destruct (length (ml_data dat)) eqn:Hdat => //=.
  ** by exfalso ; apply N.ltb_lt in Hl ; apply N.nlt_0_r in Hl.
  ** (*apply N.leb_le in Hlen.
                 replace (mem_length m) with (N.of_nat (S n)) in Hlen ;
                   last by rewrite H1 ; apply N2Nat.id.
                 rewrite length_is_size in Hlen. *)
    apply N.ltb_lt in Hl.
    rewrite app_length => //=.
    repeat rewrite length_is_size.
    rewrite size_takel.
    rewrite size_drop.
    unfold ssrnat.subn, ssrnat.subn_rec.
    rewrite length_is_size in Hdat ; rewrite Hdat.
    rewrite Nat.sub_add_distr.
    replace (S n - N.to_nat k - 1) with (n - N.to_nat k) ; last lia.
    rewrite minus_Sn_m.
    rewrite le_plus_minus_r. 
    done.
    lia. lia. 
    rewrite length_is_size in Hdat.
    rewrite Hdat.
    unfold ssrnat.leq, ssrnat.subn, ssrnat.subn_rec.
    assert (N.to_nat k - S n = 0) ; first lia.
    by rewrite H.
Qed.




Lemma store_length (m m': memory) (n: N) (off: static_offset) (bs: bytes) : (* (l: nat) : *)
  store m n off bs (length bs) = Some m' -> (* is this lemma even true with any l as length ? *)
  length m.(mem_data).(ml_data) = length m'.(mem_data).(ml_data).
Proof.
  intros.
  unfold store, write_bytes, fold_lefti in H.
  destruct (_ <=? _)%N eqn:Hlen ; try by inversion H.
  cut (forall j dat dat',
          j <= length bs ->
          let i := length bs - j in
          (let '(_,acc_end) :=
            fold_left
              (λ '(k, acc) x,
                (k + 1,
                  match acc with
                  | Some dat => mem_update (n + off + N.of_nat k)%N x dat
                  | None => None
                  end)) (bytes_takefill #00%byte j (drop i bs))
              (i, Some dat) in acc_end) = Some dat' ->
                               length (ml_data dat) = length (ml_data (mem_data m)) ->
                               length (ml_data dat') = length (ml_data (mem_data m))).
  - intros Hi.
    assert (length bs <= length bs) ; first lia.
    destruct (let '(_, acc_end) := fold_left _ _ _ in acc_end) eqn:Hfl ; try by inversion H.
    apply (Hi _ (mem_data m) m0) in H0 => //=.
    + destruct m' ; inversion H ; by subst.
    + rewrite PeanoNat.Nat.sub_diag.
      unfold drop.
      exact Hfl.
  - induction j ; intros ; subst i.
    + rewrite Nat.sub_0_r in H1.
      rewrite drop_all in H1.
      simpl in H1. inversion H1. by rewrite - H4.
    + assert (j <= length bs) ; first lia.
      destruct (drop (length bs - S j) bs) eqn:Hdrop.
      * assert (length (drop (length bs - S j) bs) = 0) ; first by rewrite Hdrop.
        rewrite drop_length in H4. lia.
      * assert (exists dat0, mem_update (n + off + N.of_nat (length bs - S j))%N
                                   b dat = Some dat0) as [dat0 Hdat0].
         { unfold mem_update. apply N.leb_le in Hlen.
           assert (n + off + N.of_nat (length bs - S j) <
                     N.of_nat (length (ml_data dat)))%N.
           rewrite H2.
           unfold mem_length, memory_list.mem_length in Hlen.
           lia.
           apply N.ltb_lt in H4.
           rewrite H4.
           by eexists _. } 
        apply (IHj dat0 dat') in H3.
        ++ done.
        ++ simpl in H1.
           rewrite Hdat0 in H1.
           replace (length bs - j) with (length bs - S j + 1) ; last lia.
           rewrite - drop_drop.
           rewrite Hdrop.
           unfold drop => //=.
        ++ erewrite <- mem_update_length => //=.
Qed.


Lemma store_mem_max_opt (m m' : memory) n off bs l :
  store m n off bs l = Some m' ->
  mem_max_opt m = mem_max_opt m'.
Proof.
  intros.
  unfold store in H.
  destruct ( _ <=? _)%N ; try by inversion H.
  unfold write_bytes in H.
  destruct (fold_lefti _ _ _) ; try by inversion H.
Qed.

  
Lemma mem_equiv_length (m m': memory):
  m ≡ₘ m' ->
  mem_length m = mem_length m'.
Proof.
  move => Hm.
  unfold mem_length, memory_list.mem_length.
  by rewrite Hm.
Qed.

(* Lemma store_data_inj (m1 m2 m1': memory) (n: N) (off: static_offset) (bs: bytes) (l: nat) : *)
(*   m1 ≡ₘ m2 -> *)
(*   store m1 n off bs l = Some m1' -> *)
(*   exists m2', store m2 n off bs l = Some m2' /\ m1' ≡ₘ m2'. *)
(* Proof. *)
(*   move => Hmequiv Hstore. *)
(*   Print memory_list. *)
(*   exists (Build_memory (Build_memory_list (ml_init (mem_data m2)) (ml_data (mem_data m1'))) (mem_max_opt m2)). *)
(*   unfold store in Hstore. *)
(*   unfold store. *)
(* Admitted. *)

Lemma update_list_at_insert {T: Type} (l: list T) (x: T) (n: nat):
  n < length l ->
  update_list_at l n x = <[n := x]> l.
Proof.
  move => Hlen.
  unfold update_list_at.
  move: n x Hlen.
  elim: l => //=.
  - move => n.
    by destruct n; lia.
  - move => a l IH n x Hlen.
    destruct n => //=.
    f_equal.
    apply IH.
    lia.
Qed.


Lemma update_trivial {A} l i (x : A) :
  l !! i = Some x -> update_list_at l i x = l.
Proof.
  generalize dependent l.
  induction i ; intros ;
    destruct l ; inversion H => //=.
  unfold update_list_at. simpl.
  unfold update_list_at in IHi.
  by rewrite IHi.
Qed.

Lemma update_twice {A} l i (x : A) y :
  i < length l ->
  update_list_at (update_list_at l i x) i y = update_list_at l i y.
Proof.
  generalize dependent l.
  induction i ; intros.
  destruct l ; inversion H => //=.
  unfold update_list_at. simpl.
  rewrite seq.take_cat.
  rewrite size_take.
  assert (ssrnat.leq (S (S i)) (seq.size l)).
  { unfold ssrnat.leq, ssrnat.subn, ssrnat.subn_rec.
    rewrite length_is_size in H.
    replace (S (S i) - seq.size l) with 0 ; last lia.
    done. }
  rewrite H0.
  rewrite ssrnat.ltnn.
  rewrite ssrnat.subnn.
  rewrite take0.
  rewrite cats0.
  rewrite - drop_drop.
  replace (S i) with (length (seq.take (S i) l)) at 2.
  rewrite drop_app.
  unfold drop at 1. done.
  rewrite length_is_size.
  rewrite size_take.
  by rewrite H0.
Qed.


Lemma update_length {A} l i (x : A) :
  i < length l ->
  length (update_list_at l i x) = length l.
Proof.
  intros.
  unfold update_list_at.
  rewrite app_length => //=.
  rewrite length_is_size.
  rewrite size_take.
  unfold ssrnat.leq, ssrnat.subn, ssrnat.subn_rec.
  rewrite length_is_size in H.
  replace (S i - seq.size l) with 0 ; last lia.
  simpl.
  rewrite drop_length.
  unfold ssrnat.addn, ssrnat.addn_rec.
  rewrite length_is_size.
  lia.
Qed.


Lemma lookup_seq_nth {A} (l : seq.seq A) k :
  l !! k = seq.nth None (fmap (λ x, Some x) l) k.
Proof.
  generalize dependent l. 
  induction k ; intros ; destruct l => //=.
Qed.

Lemma take_fmap {A B} (l : seq.seq A) (f : A -> B) k :
  f <$> seq.take k l = seq.take k (f <$> l).
Proof.
  generalize dependent l.
  induction k ; intros ; destruct l => //=.
  unfold fmap in IHk.
  by rewrite IHk.
Qed.

Lemma ncons_fmap {A B} l (f : A -> B) i x :
  f <$> ncons i x l = ncons i (f x) (f <$> l).
Proof.
  induction i ; intros ; destruct l => //=.
  by rewrite - IHi.
  by rewrite - IHi.
Qed.

Lemma set_nth_read {A} (l : seq.seq A) x0 i x :
  set_nth x0 l i x !! i = Some x.
Proof.
  generalize dependent l.
  induction i ; intros ; destruct l => //=.
  rewrite lookup_seq_nth.
  rewrite ncons_fmap.
  rewrite nth_ncons.
  rewrite ssrnat.ltnn.
  rewrite ssrnat.subnn => //=.
Qed.


Lemma set_nth_ncons {A} x0 y0 i (x : A) y :
  set_nth x0 (ncons i y0 [y]) i x = ncons i y0 [x].
Proof.
  induction i => //=.
  by rewrite IHi.
Qed.


Lemma set_nth_write {A} (l : seq.seq A) x0 y0 i x y :
  set_nth x0 (set_nth y0 l i y) i x = set_nth y0 l i x.
Proof.
  generalize dependent l.
  induction i ; intros ; destruct l => //=.
  by rewrite set_nth_ncons.
  by rewrite IHi.
Qed.

  


Lemma set_nth_fmap {A B} (l : seq.seq A) (f : A -> B) x0 i x :
  f <$> set_nth x0 l i x = set_nth (f x0) (f <$> l) i (f x).
Proof.
  generalize dependent l.
  induction i ; intros ; destruct l => //=.
  specialize (ncons_fmap [x] f i x0) ; unfold fmap ; intros.
  rewrite H. done.
  unfold fmap in IHi.
  by rewrite IHi.
Qed.



Lemma update_ne {A} l i k (x : A) :
  i < length l -> i <> k -> (update_list_at l i x) !! k = l !! k.
Proof.
  intros.
  unfold update_list_at.
  destruct (decide (k < i)).
  rewrite lookup_app_l.
  rewrite lookup_seq_nth.
  rewrite take_fmap.
  rewrite nth_take.
  by rewrite lookup_seq_nth.
  unfold ssrnat.leq, ssrnat.subn, ssrnat.subn_rec.
  replace (S k - i) with 0 => //= ; last lia.
  rewrite length_is_size size_takel ; first done.
  unfold ssrnat.leq, ssrnat.subn, ssrnat.subn_rec.
  rewrite - length_is_size.
  replace (i - length l) with 0 => //= ; last lia.
  rewrite lookup_app_r.
  rewrite length_is_size size_takel.
  destruct (k - i) eqn:Hki ; first by exfalso ; lia.
  simpl.
  rewrite lookup_drop.
  unfold ssrnat.addn, ssrnat.addn_rec.
  replace (i + 1 + n0) with k => //= ; last lia.
  unfold ssrnat.leq, ssrnat.subn, ssrnat.subn_rec.
  rewrite - length_is_size.
  replace (i - length l) with 0 => //= ; last lia.
  rewrite length_is_size size_takel.
  lia.
  unfold ssrnat.leq, ssrnat.subn, ssrnat.subn_rec.
  rewrite - length_is_size.
  replace (i - length l) with 0 => //= ; last lia.
Qed.

  
Lemma those_app {A} (l1 : list (option A)) l2 tl1 tl2 :
  those l1 = Some tl1 -> those l2 = Some tl2 -> those (l1 ++ l2) = Some (tl1 ++ tl2).
Proof.
  generalize dependent tl1. induction l1 ; intros.
  unfold those in H ; inversion H. by rewrite app_nil_l.
  rewrite <- those_those0 in H. 
  unfold those0 in H. destruct a ; try by inversion H.
  fold (those0 l1) in H. rewrite those_those0 in H.
  destruct tl1 ; destruct (those l1) ; inversion H.
  assert (those (l1 ++ l2) = Some (l ++ tl2)) ; first by eapply IHl1.
  rewrite <- those_those0. unfold those0 => //=.
  fold (those0 (l1 ++ l2)). rewrite those_those0 H1. simpl. by subst.
Qed.


Lemma those_app_inv {A} (l1 : list (option A)) l2 tl :
  those (l1 ++ l2) = Some tl ->
  exists tl1 tl2, those l1 = Some tl1 /\ those l2 = Some tl2 /\ tl1 ++ tl2 = tl.
Proof.
  generalize dependent tl ; induction l1 ; intros.
  eexists _, _ ; repeat split => //=.
  rewrite <- app_comm_cons in H.
  rewrite <- those_those0 in H.
  unfold those0 in H. destruct a eqn:Ha ; try by inversion H.
  destruct (those0 (l1 ++ l2)) eqn:Hth ; unfold those0 in Hth ; rewrite Hth in H ;
    try by inversion H.
  fold (those0 (l1 ++ l2)) in Hth.
  rewrite those_those0 in Hth.
  rewrite Hth in IHl1.
  assert (Some l = Some l) ; first done.
  destruct (IHl1 l H0) as (tl1 & tl2 & Hth1 & Hth2 & Htl).
  rewrite <- those_those0.
  unfold those0. fold (those0 l1).
  unfold option_map. rewrite those_those0 Hth1.
  eexists _,_ ; repeat split => //=. rewrite Htl.
  unfold option_map in H. by inversion H.
Qed.


Lemma wms_append n k b bs :
  ⊢ (n ↦[wms][k] (b :: bs) ∗-∗ ( n↦[wm][k] b ∗ n↦[wms][N.add k 1%N] bs))%I.
Proof.
  iSplit.
  - iIntros "Hwms". unfold mem_block_at_pos, big_opL. rewrite Nat.add_0_r.
    rewrite N2Nat.id.
    fold (big_opL (M := iPropI Σ)).
    iDestruct "Hwms" as "[Hwm Hwms]".
    iSplitL "Hwm" => //=.
    iApply (big_sepL_impl with "Hwms").
    iIntros (k0 x) "!> %Hx Hwm".
    replace (N.to_nat k + S k0) with (N.to_nat (k+1) + k0) => //=.
    lia.
  - iIntros "[Hwm Hwms]". unfold mem_block_at_pos, big_opL.
    rewrite Nat.add_0_r N2Nat.id.
    fold (big_opL (M := iPropI Σ)).
    iSplitL "Hwm" => //=.
    iApply (big_sepL_impl with "Hwms").
    iIntros (k0 x) "!> %Hx Hwm".
    replace (N.to_nat (k+1) + k0) with (N.to_nat k + S k0) => //=.
    lia.
Qed.

Lemma map_iota_lift {A} (f : nat -> A) g n len :
  (forall x, f (x + 1) = g x) -> map f (iota (n+1) len) = map g (iota n len).
Proof.
  intros Hfg.
  generalize dependent n.
  induction len ; intros => //=.
  rewrite Hfg. replace (S (n+1)) with (S n + 1) ; last lia.
  rewrite IHlen. done.
Qed. 

Lemma load_append m k off b bs :
  load m k off (length (b :: bs)) = Some (b :: bs) ->
  load m k (off + 1)%N (length bs) = Some bs.
Proof.
  unfold load ; intros Hm.
  replace (off + N.of_nat (length (b :: bs)))%N with
    (off + 1 + N.of_nat (length bs))%N in Hm ; last by simpl ; lia.
  destruct (k + (off + 1 + N.of_nat (length bs)) <=? mem_length m)%N ; try by inversion Hm.
  unfold read_bytes. unfold read_bytes in Hm. simpl in Hm.
  destruct (mem_lookup (k + off + 0)%N (mem_data m)) ; inversion Hm.
  rewrite list_extra.cons_app in H0.
  destruct (those_app_inv [Some b0] _ _ H0) as (tl1 & tl2 & Htl1 & Htl2 & Htl).
  unfold those in Htl1. simpl in Htl1. inversion Htl1 ; subst ; clear Htl1.
  inversion Htl ; subst ; clear Htl.
  erewrite <- map_iota_lift => //=.
  intros. replace (k + off + N.of_nat (x+1))%N with
    (k + (off + 1) + N.of_nat x)%N => //=.
  lia.
Qed.

Lemma list_trivial_replace {A} l (x : A) k :
  l !! k = Some x ->
  cat (seq.take k l) (cat [x] (seq.drop (k+1) l)) = l.
Proof.
  generalize dependent k.
  induction l ; intros ; destruct k ; inversion H.
  - simpl. by rewrite drop0. 
  - apply IHl in H1. simpl. rewrite H1. done.
Qed.

Lemma trivial_update m k b :
  read_bytes m k 1 = Some [b] ->
  mem_update k b (mem_data m) = Some (mem_data m).
Proof.
  intro Hread.
  unfold mem_update.
  unfold read_bytes in Hread.
  unfold those in Hread.
  simpl in Hread.
  rewrite N.add_0_r in Hread.
  destruct (mem_lookup k (mem_data m)) eqn:Hlookup ; inversion Hread ; subst ; clear Hread.
  unfold mem_lookup in Hlookup.
  rewrite nth_error_lookup in Hlookup.
  assert (k < N.of_nat (length (ml_data (mem_data m))))%N.
  { apply lookup_lt_Some in Hlookup. lia. } 
  apply N.ltb_lt in H.
  rewrite H.
  rewrite list_trivial_replace => //=.
  by destruct (mem_data m).
Qed.


Definition incr_fst {A} (a : nat * A) := (fst a + 1,snd a).

Lemma incr_fst_equals {A} x n (o : A) :
  incr_fst x = (n,o) -> x = (n-1,o).
Proof.
  intros ; destruct x. unfold incr_fst in H. simpl in H.
  assert (n > 0). { inversion H ; lia. }
  rewrite Nat.sub_1_r.
  inversion H.
  replace (n0 + 1) with (S n0) ; last lia.
  rewrite Nat.pred_succ. done.
Qed.

Lemma fold_left_lift {A B} (f : (nat * A) -> B -> (nat * A)) g l i acc :
  (forall i acc x, f (i+1,acc) x = incr_fst (g (i,acc) x)) ->
  fold_left f l (i+1,acc) = incr_fst (fold_left g l (i,acc)).
Proof. 
  intros Hfg.
  generalize dependent i.
  generalize dependent acc.
  induction l ; intros => //=.
  rewrite Hfg.
  destruct (g (i, acc) a).
  unfold incr_fst => //=.
  rewrite IHl.
  unfold incr_fst => //=.
Qed.



Lemma store_append1 m k off b bs m':
  store m k off (b :: bs) (length (b :: bs)) = Some m' ->
  exists m'', store m'' k (off + 1)%N bs (length bs) = Some m' /\
           store m k off [b] 1 = Some m''.
Proof.
  intro Hstore.
  unfold store.
  unfold store in Hstore.
  destruct (k + off + N.of_nat (length (b :: bs)) <=? mem_length m)%N eqn:Hlen ;
    try by inversion Hstore.
  apply N.leb_le in Hlen.
  simpl in Hlen.
  assert (k + off + N.of_nat 1 <= mem_length m)%N ; first lia.
  apply N.leb_le in H.
  rewrite H.
  unfold write_bytes, fold_lefti => //=.
  rewrite N.add_0_r.
  unfold mem_update.
  unfold mem_length, memory_list.mem_length in H.
  apply N.leb_le in H.
  assert (k + off < N.of_nat (length (ml_data (mem_data m))))%N ; first lia.
  apply N.ltb_lt in H0.
  rewrite H0.
  eexists _ ; split => //=.
  remember {| mem_data := _ ; mem_max_opt := _ |} as m''.
  assert (store m k off [b] 1 = Some m'').
  { subst. unfold store. apply N.leb_le in H. rewrite H.
    unfold write_bytes, fold_lefti => //=.
    unfold mem_update. rewrite N.add_0_r.
    rewrite H0. done. }
  assert (mem_length m'' = mem_length m).
  { unfold mem_length, memory_list.mem_length. erewrite <- store_length => //=.
    by instantiate (1 := [b]) => //=. }
  assert (mem_max_opt m'' = mem_max_opt m) as Hmax; first by 
    eapply Logic.eq_sym, store_mem_max_opt.  
  rewrite H2.
  assert (k + (off + 1) + N.of_nat (length bs) <= mem_length m)%N ; first lia.
  apply N.leb_le in H3. rewrite H3.
  unfold write_bytes, fold_lefti in Hstore.
  simpl in Hstore.
  rewrite N.add_0_r in Hstore.
  replace (mem_update (k + off)%N b (mem_data m)) with (Some (mem_data m'')) in Hstore.
  rewrite <- (plus_O_n 1) in Hstore.
  destruct (fold_left _ _ (0 + 1, _)) eqn:Hfl ; try by inversion Hstore.
  rewrite (fold_left_lift _ (λ '(k0, acc) x,
                              (k0 + 1,
                                match acc with
                                | Some dat =>
                                    if (k + (off + 1) + N.of_nat k0 <?
                                          N.of_nat (length (ml_data dat)))%N
                                    then
                                      Some {| ml_init := ml_init dat ;
                                             ml_data :=
                                             seq.take (N.to_nat (k + (off + 1) +
                                                                   N.of_nat k0))
                                                      (ml_data dat) ++
                                                      x :: seq.drop (N.to_nat (k + (off + 1) + N.of_nat k0) + 1)
                                                      (ml_data dat)
                                           |}
                                    else None
                                | None => None
                                end)))
    in Hfl.
  apply incr_fst_equals in Hfl.
  rewrite Hfl.
  rewrite Hmax.
  done.
  intros. unfold incr_fst => //=.
  unfold mem_update.
  replace (k + off + N.of_nat (i+1))%N with (k + (off + 1) + N.of_nat i)%N ; last lia.
  done.
  unfold store in H1.
  apply N.leb_le in H.
  rewrite H in H1.
  unfold write_bytes, fold_lefti in H1.
  simpl in H1.
  rewrite N.add_0_r in H1.
  destruct (mem_update (k + off)%N b (mem_data m)) eqn:Hupd ; try by inversion H1.
Qed.

(*
Lemma store_append_inv m m'' k off b bs m':
  store m k off [b] 1 = Some m'' ->
  store m'' k (off + 1)%N bs (length bs) = Some m' ->
  store m k off (b :: bs) (length (b :: bs)) = Some m'.
Proof.
Admitted.
*)






Lemma enough_space_to_store m k off bs :
  (k + off + N.of_nat (length bs) <= mem_length m)%N ->
  exists mf, store m k off bs (length bs) = Some mf.
Proof.
  intros Hmlen.
  unfold store.
  apply N.leb_le in Hmlen.
  rewrite Hmlen.
  unfold write_bytes, fold_lefti. 
  cut (forall i dat,
          i <= length bs ->
          length (ml_data dat) = N.to_nat (mem_length m) ->
          let j := length bs - i in
          exists datf, (let '(_, acc_end) :=
                      fold_left (λ '(k0,acc) x,
                                  (k0 + 1,
                                    match acc with
                                    | Some dat => mem_update (k + off + N.of_nat k0)%N x dat
                                    | None => None
                                    end)) (bytes_takefill #00%byte (length (drop j bs))
                                                          (drop j bs))
                                (j, Some dat) in acc_end) = Some datf).
  - intros H.
    assert (length bs <= length bs) ; first lia.
    apply (H _ (mem_data m)) in H0 as [datf' Hdatf'].
    + rewrite PeanoNat.Nat.sub_diag in Hdatf'.
      unfold drop in Hdatf'.
      rewrite Hdatf'.
      by eexists _.
    + unfold mem_length, memory_list.mem_length.
      by rewrite Nat2N.id.
  - induction i ; intros ; subst j.
    + rewrite <- minus_n_O.
      rewrite drop_all => //=.
      by eexists _.
    + assert (i <= length bs) ; first lia.
      destruct (drop (length bs - S i) bs) eqn:Hdrop.
      * assert (length (drop (length bs - S i) bs) = 0) ; first by rewrite Hdrop.
        rewrite drop_length in H2. lia.
      * assert (exists datupd,
                   mem_update (k + off + N.of_nat (length bs - S i))%N b dat =
                     Some datupd ) as [datupd Hdatupd].
        { unfold mem_update.
           apply N.leb_le in Hmlen.
           assert ( k + off + N.of_nat (length bs - S i) <
                      N.of_nat (length (ml_data dat)))%N ;
             first lia.
           apply N.ltb_lt in H2 ; rewrite H2.
           by eexists _. }
        eapply (IHi datupd) in H1 as [datf Hdatf].
        ++ rewrite - Hdrop. rewrite drop_length.
           rewrite <- (take_drop 1 (drop (length bs - S i) bs)).
           rewrite drop_drop.
           rewrite Hdrop.
           unfold take.
           replace (length bs - S i + 1) with (length bs - i) ; last lia.
           replace (length bs - (length bs - S i)) with (S i) ; last lia.
           simpl.
           replace (length bs - S i + 1) with (length bs - i) ; last lia.
           rewrite drop_length in Hdatf.
           replace (length bs - (length bs - i)) with i in Hdatf ; last lia.
           rewrite Hdatupd.
           rewrite Hdatf.
           by eexists _.
        ++ rewrite <- H0.
           by erewrite <- mem_update_length.
Qed.


(* This lemma is true (and proven), but perhaps uninteresting (especially given
   lemma enough_space_to_store) *)
(*

Lemma store_in_same_memory_length m m' mf k off bs :
  mem_length m = mem_length m' ->
  store m k off bs (length bs) = Some mf -> 
  exists mf', store m' k off bs (length bs) = Some mf'.
Proof.
  intros Hmlen Hstore.
  unfold store. unfold store in Hstore.
  rewrite <- Hmlen.
  destruct (k + off + N.of_nat (length bs) <=? mem_length m )%N eqn:Hlen
  ; try by inversion Hstore.
  unfold write_bytes, fold_lefti. unfold write_bytes, fold_lefti in Hstore.
  cut (forall i dat datf dat',
          i <= length bs ->
          length (ml_data dat') = N.to_nat (mem_length m) ->
          length (ml_data dat) = N.to_nat (mem_length m) ->
          let j := length bs - i in
          (let '(_, acc_end) :=
             fold_left (λ '(k0, acc) x,
                         (k0 + 1,
                           match acc with
                           | Some dat => mem_update (k + off + N.of_nat k0)%N x dat
                           | None => None
                           end)) (bytes_takefill #00%byte (length (drop j bs))
                                                 (drop j bs))
                       (j, Some dat) in acc_end) = Some datf ->
          exists datf', (let '(_, acc_end) :=
                      fold_left (λ '(k0,acc) x,
                                  (k0 + 1,
                                    match acc with
                                    | Some dat => mem_update (k + off + N.of_nat k0)%N x dat
                                    | None => None
                                    end)) (bytes_takefill #00%byte (length (drop j bs))
                                                          (drop j bs))
                                (j, Some dat') in acc_end) = Some datf').
  - intros H.
    assert (length bs <= length bs) ; first lia.
    apply (H _ (mem_data m) (mem_data mf) (mem_data m')) in H0 as [datf' Hdatf'].
    + rewrite PeanoNat.Nat.sub_diag in Hdatf'.
      unfold drop in Hdatf'.
      rewrite Hdatf'.
      by eexists _.
    + rewrite Hmlen.
      unfold mem_length, memory_list.mem_length.
      by rewrite Nat2N.id.
    + unfold mem_length, memory_list.mem_length.
      by rewrite Nat2N.id.
    + rewrite PeanoNat.Nat.sub_diag.
      unfold drop.
      destruct (let '(_, acc_end) := fold_left _ _ _ in acc_end) eqn : H1 ;
        try by inversion Hstore.
  - induction i ; intros ; subst j.
    + rewrite <- minus_n_O.
      rewrite drop_all => //=.
      by eexists _.
    + assert (i <= length bs) ; first lia.
      destruct (drop (length bs - S i) bs) eqn:Hdrop.
      * assert (length (drop (length bs - S i) bs) = 0) ; first by rewrite Hdrop.
        rewrite drop_length in H4. lia.
      * assert (exists datupd datupd',
                   mem_update (k + off + N.of_nat (length bs - S i))%N b dat =
                     Some datupd /\
                   mem_update (k + off + N.of_nat (length bs - S i))%N b dat' =
                            Some datupd') as (datupd & datupd' & Hdatupd & Hdatupd').
        -- unfold mem_update.
           apply N.leb_le in Hlen.
           assert ( k + off + N.of_nat (length bs - S i) <
                      N.of_nat (length (ml_data dat')))%N ;
             first lia.
           apply N.ltb_lt in H4 ; rewrite H4.
           assert ( k + off + N.of_nat (length bs - S i) <
                      N.of_nat (length (ml_data dat)))%N ;
             first lia.
           apply N.ltb_lt in H5 ; rewrite H5.
           by eexists _, _.
        -- eapply (IHi datupd _ datupd') in H3 as [datf' Hdatf'].
           ++ rewrite - Hdrop. rewrite drop_length.
              rewrite <- (take_drop 1 (drop (length bs - S i) bs)).
              rewrite drop_drop.
              rewrite Hdrop.
              unfold take.
              replace (length bs - S i + 1) with (length bs - i) ; last lia.
              replace (length bs - (length bs - S i)) with (S i) ; last lia.
              simpl.
              replace (length bs - S i + 1) with (length bs - i) ; last lia.
              rewrite drop_length in Hdatf'.
              replace (length bs - (length bs - i)) with i in Hdatf' ; last lia.
              rewrite Hdatupd'.
              rewrite Hdatf'.
              by eexists _.
           ++ rewrite <- H0.
              by erewrite <- mem_update_length.
           ++ rewrite <- H1.
              by erewrite <- mem_update_length.
           ++ rewrite - Hdrop in H2.
              rewrite drop_length in H2.
              replace (length bs - (length bs - S i)) with (S i) in H2 ; last lia.
              rewrite drop_length.
              replace (length bs - (length bs - i)) with i ; last lia.
              rewrite Hdrop in H2.
              simpl in H2.
              rewrite Hdatupd in H2.
              unfold take in Hdrop.
              replace (length bs - i) with ((length bs - S i) + 1) ; last lia.
              rewrite - drop_drop.
              rewrite Hdrop.
              unfold drop => //=.
Qed.
 *)

Lemma list_insert_destruct {T: Type} k (l: list T) v:
  k < length l ->
  seq.take k l ++ v:: seq.drop (k+1) l = <[k := v]> l.
Proof.
  move: l v.
  induction k; move => l v Hlen; destruct l; simpl in Hlen => //=.
  - by inversion Hlen.
  - f_equal. by rewrite drop0.
  - by inversion Hlen.
  - f_equal.
    apply IHk.
    lia.
Qed.
    
Lemma mem_update_insert k b dat dat':
  mem_update k b dat = Some dat' ->
  dat' = Build_memory_list (ml_init dat) (<[(N.to_nat k) := b]> (ml_data dat)) /\
  (N.to_nat k) < length (ml_data dat).
Proof.
  unfold mem_update.
  destruct (k <? N.of_nat (length (ml_data dat)))%N eqn:Hk => //.
  move => Hupd.
  inversion Hupd; subst; clear Hupd.
  apply N.ltb_lt in Hk.
  split; last by lia.
  f_equal.
  rewrite - (list_insert_destruct (N.to_nat k) (ml_data dat) b) => //.
  lia.
Qed.
  
Lemma update_swap k b dat k' b' dat' dat'' :
  k <> k' ->
  mem_update k b dat = Some dat' ->
  mem_update k' b' dat' = Some dat'' ->
  exists dat0, mem_update k' b' dat = Some dat0 /\
            mem_update k b dat0 = Some dat''.
Proof.
  intros Hkk' Hupd Hupd'.
  apply mem_update_insert in Hupd as [Hupd Hk].
  apply mem_update_insert in Hupd' as [Hupd' Hk'].
  assert (length (ml_data dat) = length (ml_data dat')) as Hupdlen.
  { subst => /=.
    by rewrite insert_length.
  }
  exists (Build_memory_list (ml_init dat) (<[(N.to_nat k') := b']> (ml_data dat))).
  unfold mem_update.
  assert (k' <? N.of_nat (length (ml_data dat')))%N as Hk'0.
  { apply N.ltb_lt. lia. }
  assert (k <? N.of_nat (length (ml_data dat)))%N as Hk0.
  { apply N.ltb_lt. lia. }
  rewrite Hupdlen Hk'0 insert_length Hk0 => /=.
  subst.
  split; (do 2 f_equal); rewrite - list_insert_destruct; try by lias.
  rewrite list_insert_destruct; last by lias.
  simpl.
  rewrite list_insert_commute; last by lias.
  rewrite - (list_insert_destruct (N.to_nat k)) => //.
  by rewrite insert_length.
Qed.
  

  


Lemma swap_stores m m' m'' k off b bs :
  store m k off [b] 1 = Some m' ->
  store m' k (off + 1)%N bs (length bs) = Some m'' ->
  exists m0, store m k (off + 1)%N bs (length bs) = Some m0 /\
          store m0 k off [b] 1 = Some m''.
Proof.
  intros.
  assert (mem_length m = mem_length m') as Hmlen ;
    first (unfold mem_length, memory_list.mem_length ; erewrite store_length => //= ;
          by instantiate (1:=[b]) => //=).
  unfold store in H0.
  destruct (k + (off + 1) + N.of_nat (length (bs)) <=? mem_length m')%N eqn:Hlen ;
    try by inversion H0.
  apply N.leb_le in Hlen.
  rewrite <- Hmlen in Hlen.
  destruct (enough_space_to_store m k (off + 1)%N (bs)) as [m0 Hm0] => //=.
  exists m0 ; split => //=.
  unfold store, write_bytes, fold_lefti => //=.
  assert (mem_length m = mem_length m0) as Hmlen0 ;
    first by unfold mem_length, memory_list.mem_length ; erewrite store_length.
  rewrite Hmlen0 in Hlen.
  assert (k + off + 1 <= mem_length m0)%N ; first lia.
  apply N.leb_le in H1 ; rewrite H1.
  rewrite N.add_0_r.
  unfold mem_update.
  apply N.leb_le in H1.
  assert (k + off < N.of_nat (length (ml_data (mem_data m0))))%N ;
    first by unfold mem_length, memory_list.mem_length in H1 ; lia.
  apply N.ltb_lt in H2.
  rewrite H2.
  rewrite - H0.
  unfold write_bytes, fold_lefti.
  unfold store, write_bytes, fold_lefti in H.
  rewrite - Hmlen0 in H1.
  apply N.leb_le in H1 ; rewrite H1 in H.
  simpl in H.
  rewrite N.add_0_r in H.
  unfold mem_update in H.
  replace (length (ml_data (mem_data m0))) with (length (ml_data (mem_data m)))
    in H2 ; last by eapply store_length.
  rewrite H2 in H.
  inversion H.
  unfold store in Hm0.
  rewrite - Hmlen0 in Hlen.
  apply N.leb_le in Hlen ; rewrite Hlen in Hm0.
  unfold write_bytes, fold_lefti in Hm0.
  destruct (fold_left _ _ _) eqn:Hfl.
  destruct o ; inversion Hm0.
  simpl.
  assert (m1 = mem_data m0) ; first by rewrite - H5.
  (*    simpl in Hfl. *)
  cut (forall i dat datf n,
          i <= length bs ->
          length (ml_data dat) = N.to_nat (mem_length m) ->
          let j := length bs - i in
          fold_left (λ '(k0, acc) x,
                      (k0 + 1,
                        match acc with
                        | Some dat => mem_update (k + (off + 1) + N.of_nat k0)%N x dat
                        | None => None
                        end)) (bytes_takefill #00%byte (length (drop j bs))
                                              (drop j bs))
                    (j, Some dat) = (n, Some datf) ->
          exists m, fold_left (λ '(k0, acc) x,
                           (k0 + 1,
                             match acc with
                             | Some dat => mem_update (k + (off + 1) + N.of_nat k0)%N
                                                     x dat
                             | None => None
                             end)) (bytes_takefill #00%byte (length (drop j bs))
                                                   (drop j bs))
                         (j, mem_update (k + off)%N b dat) =
                 (m, mem_update (k + off)%N b datf)).
  - intros Hi.
    assert (length bs <= length bs) as Hlbs; first lia.
    apply (Hi _ (mem_data m) m1 n) in Hlbs as [nn Hia].
    + rewrite PeanoNat.Nat.sub_diag in Hia.
      unfold drop in Hia.
      unfold mem_update in Hia.
      rewrite H2 in Hia.
      rewrite Hia.
      rewrite H3.
      unfold mem_length, memory_list.mem_length in Hmlen0 ; rewrite Hmlen0 in H2 ;
        rewrite H2.
      done.
    + unfold mem_length, memory_list.mem_length.
      by rewrite Nat2N.id.
    + rewrite PeanoNat.Nat.sub_diag.
      unfold drop.
      done.
  - induction i ; intros ; subst j.
    + rewrite Nat.sub_0_r.
      rewrite drop_all.
      simpl.
      rewrite Nat.sub_0_r in H8.
      rewrite drop_all in H8.
      simpl in H8.
      inversion H8.
      by eexists _.
    + assert (i <= length bs) ; first lia.
      destruct (drop (length bs - S i) bs) eqn:Hdrop.
      * assert (length (drop (length bs - S i) bs) = 0) ; first by rewrite Hdrop.
        rewrite drop_length in H10. lia.
      * assert (exists dat', mem_update (k + off)%N b dat = Some dat') as [dat' Hdat'].
        { unfold mem_update. rewrite H7 Nat2N.id H2. by eexists _. }
        assert (exists dat'',
                   mem_update (k + (off + 1) + N.of_nat (length bs - S i))%N b0 dat'
                   = Some dat'') as [dat'' Hdat''].
        { unfold mem_update.
          erewrite <- mem_update_length => //=.
          rewrite H7 Nat2N.id.
          apply N.leb_le in Hlen.
          assert (k + (off + 1) + N.of_nat (length bs - S i) < N.of_nat (length (ml_data (mem_data m))))%N.
          { unfold mem_length, memory_list.mem_length in Hlen.
            assert (N.of_nat (length bs - S i) < N.of_nat (length bs))%N ; lia. }
          apply N.ltb_lt in H10.
          rewrite H10.
          by eexists _. }
        rewrite - Hdrop.
        assert (k + off <> k + (off + 1) + N.of_nat (length bs - S i))%N ; first lia.
        destruct (update_swap _ _ _ _ _ _ _ H10 Hdat' Hdat'')
          as (dat0 & Hdat0 & Hdat0'') => //=.
        eapply (IHi dat0) in H9 as [nn Hflf].
        ++ rewrite drop_length.
           rewrite <- (take_drop 1 (drop (length bs - S i) bs)).
           rewrite drop_drop.
           rewrite Hdrop.
           unfold take.
           replace (length bs - S i + 1) with (length bs - i) ; last lia.
           replace (length bs - (length bs - S i)) with (S i) ; last lia.
           simpl.
           replace (length bs - S i + 1) with (length bs - i) ; last lia.
           rewrite drop_length in Hflf.
           replace (length bs - (length bs - i)) with i in Hflf ; last lia.
           rewrite Hdat' Hdat''.
           rewrite - Hdat0''.
           rewrite Hflf.
           by eexists _.
        ++ erewrite <- mem_update_length => //=.
        ++ rewrite - Hdrop in H8.
           rewrite drop_length in H8.
           replace (length bs - (length bs - S i)) with (S i) in H8 ; last lia.
           rewrite drop_length.
           replace (length bs - (length bs - i)) with i ; last lia.
           rewrite Hdrop in H8.
           simpl in H8.
           rewrite Hdat0 in H8.
           replace (length bs - i) with (length bs - S i + 1) ; last lia.
           rewrite - drop_drop.
           rewrite Hdrop.
           unfold drop => //=.
Qed.

 
 
(*
Lemma store_trans m k off bs bs' m' m'' :
  length bs = length bs' ->
  store m k off bs (length bs) = Some m' ->
  store m' k off bs' (length bs') = Some m'' ->
  store m k off bs' (length bs') = Some m''.
Proof.
  generalize dependent off. generalize dependent bs'. generalize dependent m.
  generalize dependent m'. generalize dependent m''.
  induction bs ; intros m'' m' m bs' off Hlen Hs Hs'.
  - assert (mem_length m = mem_length m') as Hmlen ;
      first by unfold mem_length, memory_list.mem_length ; erewrite store_length. 
    apply Logic.eq_sym, nil_length_inv in Hlen ; subst.
    unfold store. unfold store in Hs.
    unfold store in Hs'.
    rewrite <- Hmlen in Hs'.
    destruct (k + off + N.of_nat (length []) <=? mem_length m)%N ; try by inversion Hs.
    unfold write_bytes => //=.
    unfold write_bytes in Hs ; simpl in Hs.
    unfold write_bytes in Hs' ; simpl in Hs'.
    rewrite Hs. rewrite <- Hs'.
    by destruct m'.
  - assert (mem_length m = mem_length m') as Hmlen ;
      first by unfold mem_length, memory_list.mem_length ; erewrite store_length.
    destruct bs' ; inversion Hlen.
    apply store_append1 in Hs as (m0 & Hm0 & Hm0').
    apply store_append1 in Hs' as (m1 & Hm1 & Hm1').
    specialize (IHbs _ _ _ _ _ H0 Hm0) as Hm2.
    eapply IHbs in Hm0 => //=.
    eapply store_append_inv.
    + unfold store. unfold store in Hm0'.
      destruct (k + off + N.of_nat 1 <=? mem_length m)%N ; try by inversion Hm0'.
      unfold write_bytes, fold_lefti => //=.
      unfold write_bytes, fold_lefti in Hm0' ; simpl in Hm0'.
      unfold mem_update. unfold mem_update in Hm0'.
      destruct (_ <? _)%N ; try by inversion Hm0'.
    + eapply IHbs => //=.
    

   

      
  
  intros Hlen Hs Hs'.
  assert (mem_length m = mem_length m') as Hmlen.
  { unfold mem_length, memory_list.mem_length ; by erewrite store_length. } 
  unfold store.
  unfold store in Hs.
  unfold store in Hs'.
  rewrite Hlen in Hs.
  rewrite <- Hmlen in Hs'.
  destruct (k + off + N.of_nat (length bs') <=? mem_length m)%N ; try by inversion Hs.
  unfold write_bytes.
  unfold write_bytes in Hs.
  unfold write_bytes in Hs'.
  unfold fold_lefti.
  unfold fold_lefti in Hs.
  unfold fold_lefti in Hs'.
  cut ((*forall k1,
          k1 <= length bs' ->
          let k0 := length bs' - k1 in *) forall k0,
          match
            (let
                '(_, acc_end) :=
                fold_left
                  (λ '(k0, acc) (x : byte),
                    (k0 + 1,
                      match acc with
                      | Some dat => mem_update (k + off + N.of_nat k0)%N x dat
                      | None => None
                      end)) (bytes_takefill #00%byte (length (drop k0 bs'))
                                            (drop k0 bs'))
                  (k0, fold_lefti
                               (λ off0 dat_o b,
                                 match dat_o with
                                 | Some dat => mem_update (k + off + N.of_nat off0)%N
                                                         b dat
                                 | None => None
                                 end) (bytes_takefill #00%byte k0 (take k0 bs'))
                               (Some (mem_data m')))
                       

                  (* Some (mem_data m')) *) in acc_end)
          with
          | Some dat => Some {| mem_data := dat; mem_max_opt := mem_max_opt m' |}
          | None => None
          end = Some m'' ->
          match
            (let
                '(_, acc_end) :=
                fold_left
                  (λ '(k0, acc) (x : byte),
                    (k0 + 1,
                      match acc with
                      | Some dat => mem_update (k + off + N.of_nat k0)%N x dat
                      | None => None
                      end)) (bytes_takefill #00%byte (length (drop k0 bs'))
                                            (drop k0 bs)) 
                  (k0, fold_lefti
                         (λ off0 dat_o b,
                           match dat_o with
                           | Some dat => mem_update (k + off + N.of_nat off0)%N
                                                   b dat
                           | None => None
                           end) (bytes_takefill #00%byte k0 (take k0 bs))
                         (Some (mem_data m)))


                    (*Some (mem_data m))*)

              in acc_end)
          with
          | Some dat => Some {| mem_data := dat; mem_max_opt := mem_max_opt m |}
          | None => None
          end = Some m' ->
          match
            (let
                '(_, acc_end) :=
                fold_left
                  (λ '(k0, acc) (x : byte),
                    (k0 + 1,
                      match acc with
                      | Some dat => mem_update (k + off + N.of_nat k0)%N x dat
                      | None => None
                      end)) (bytes_takefill #00%byte (length (drop k0 bs'))
                                            (drop k0 bs')) 
                  (k0, fold_lefti
                         (λ off0 dat_o b,
                           match dat_o with
                           | Some dat => mem_update (k + off + N.of_nat off0)%N
                                                   b dat
                           | None => None
                           end) (bytes_takefill #00%byte k0 (take k0 bs'))
                         (Some (mem_data m)))

                  (* Some (mem_data m) ) *) in acc_end)
          with
          | Some dat => Some {| mem_data := dat; mem_max_opt := mem_max_opt m |}
          | None => None
          end = Some m'').
  intros Hk. 
  specialize (Hk 0).
  simpl in Hk.
  apply Hk => //=.
  induction k0 ; intros Hs0 Hs0' => //=.
  unfold fold_lefti in Hs0 ;
    simpl in Hs0.
  ufold fold_lefti in Hs0' ; simpl in Hs0'.
  



  
(*  assert (length bs' <= length bs') ; first lia. *)
  apply Hk in H.
  rewrite PeanoNat.Nat.sub_diag in H.
  unfold drop in H. done.
  rewrite PeanoNat.Nat.sub_diag.
  unfold drop.
  done.
  rewrite PeanoNat.Nat.sub_diag.
  unfold drop.
  done.
  induction k1.
  intros.
  subst k0.
  rewrite <- minus_n_O.
  rewrite drop_all => //=.
  rewrite <- minus_n_O in H0.
  rewrite drop_all in H0.
  simpl in H0.
  rewrite <- minus_n_O in H1.
  rewrite drop_all in H1.
  simpl in H1. 
  rewrite firstn_all in H0.
  rewrite <- Hlen in H1.
  rewrite firstn_all in H1.
  rewrite firstn_all.
  by destruct m'' ; inversion H0 ; destruct m' ; inversion H1.
  intros. subst k0.
  assert (k1 <= length bs') ; first lia.
  apply IHk1 in H2.
  rewrite drop_length.
  rewrite <- (take_drop 1 (drop (length bs' - S k1) bs')).
  rewrite drop_drop.
  destruct (drop (length bs' - S k1) bs') eqn:Hdrop.
  assert (length (drop (length bs' - S k1) bs') = 0) ; first by rewrite Hdrop.
  rewrite drop_length in H3. lia.
  unfold take.
  replace (length bs' - S k1 + 1) with (length bs' - k1) ; last lia.
  replace (length bs' - (length bs' - S k1)) with (S k1) ; last lia.
  simpl.




  replace (length bs - S k1 + 1) with (length bs - k1) ; last lia.

  
  replace (mem_update (k + off + N.of_nat (length bs - S k1))%N b (mem_data m))
    with (Some (mem_data m)).
  done.
  rewrite trivial_update => //=.
  simpl in H1.
  rewrite list_extra.cons_app in H1. 
  apply those_app_inv in H1 as (tl1 & tl2 & Htl1 & Htl2 & Htl).
  unfold those in Htl1.
  simpl in Htl1. unfold read_bytes, those => //=.
  rewrite N.add_0_r.
  destruct (mem_lookup _ _) ; inversion Htl1.
  rewrite - H3 in Htl.
  by inversion Htl.
  rewrite drop_length in H1.
  replace (length bs - (length bs - S k1)) with (S k1) in H1 ; last lia.
  simpl in H1.
  rewrite list_extra.cons_app in H1. 
  apply those_app_inv in H1 as (tl1 & tl2 & Htl1 & Htl2 & Htl).
  replace (S (length bs - S k1)) with (length bs - k1) in Htl2 ; last lia.
  rewrite drop_length.
  replace (length bs - (length bs - k1)) with k1 ; last lia.  
  rewrite Htl2.
  unfold those in Htl1.
  simpl in Htl1.
  destruct (mem_lookup _ _) ; inversion Htl1 ; subst.
  inversion Htl.
  rewrite - (take_drop 1 (drop _ _)) in H3. 
  destruct (drop (length bs - S k1) bs) eqn:Hdrop.
  assert (length (drop (length bs - S k1) bs) = 0) ; first by rewrite Hdrop.
  rewrite drop_length in H1. lia.
  unfold take in H3.
  rewrite <- Hdrop in H3.
  rewrite drop_drop in H3.
  inversion H3.
  replace (length bs - S k1 +1) with (length bs - k1) ; last lia.
  done.


  
  generalize dependent bs'.
  induction bs ; intros.
  simpl in Hlen. 
  apply Logic.eq_sym, nil_length_inv in Hlen ; subst.
  simpl in Hs. simpl in Hs'. simpl.
  destruct m'' ; inversion Hs'.
  destruct m' ; inversion Hs.
  done.
  destruct bs' ; inversion Hlen.
  apply IHbs in H0.

  iainesa
Admitted. *)

Lemma store_trivial m k off bs :
  load m k off (length bs) = Some bs ->
  store m k off bs (length bs) = Some m. 
Proof.
  intros.
  unfold store.
  unfold load in H.
  rewrite N.add_assoc in H.
  destruct (k + off + N.of_nat (length bs) <=? mem_length m)%N ; try by inversion H.
  unfold write_bytes.
  unfold read_bytes in H.
  unfold fold_lefti.
  cut (forall k1,
          k1 <= length bs ->
          let k0 := length bs - k1 in
          those (map (λ off0, mem_lookup (k + off + N.of_nat off0)%N (mem_data m))
                       (iota k0 (length (drop k0 bs)))) = Some (drop k0 bs) ->
            match (let
                      '(_, acc_end) :=
                      fold_left
                        (λ '(k0, acc) x,
                          (k0 + 1,
                            match acc with
                            | Some dat => mem_update (k + off + N.of_nat k0)%N x dat
                            | None => None
                            end)) (bytes_takefill #00%byte (length (drop k0 bs))
                                                  (drop k0 bs))
                        (k0, Some (mem_data m)) in acc_end)
            with
            | Some dat => Some {| mem_data := dat ; mem_max_opt := mem_max_opt m |}
            | None => None
            end = Some m).
  intros Hk.
  assert (length bs <= length bs) ; first lia.
  apply Hk in H0.
  rewrite PeanoNat.Nat.sub_diag in H0.
  unfold drop in H0. done.
  rewrite PeanoNat.Nat.sub_diag.
  unfold drop. done.
  induction k1. intros.
  subst k0.
  rewrite <- minus_n_O.
  rewrite drop_all => //=.
  by destruct m.
  intros. subst k0.
  assert (k1 <= length bs) ; first lia.
  apply IHk1 in H2. 
  rewrite <- (take_drop 1 (drop (length bs - S k1) bs)).
  rewrite drop_drop.
  destruct (drop (length bs - S k1) bs) eqn:Hdrop.
  assert (length (drop (length bs - S k1) bs) = 0) ; first by rewrite Hdrop.
  rewrite drop_length in H3. lia.
  unfold take.
  replace (length bs - S k1 + 1) with (length bs - k1) ; last lia.
  simpl.
  replace (length bs - S k1 + 1) with (length bs - k1) ; last lia.
  replace (mem_update (k + off + N.of_nat (length bs - S k1))%N b (mem_data m))
    with (Some (mem_data m)).
  done.
  rewrite trivial_update => //=.
  simpl in H1.
  rewrite list_extra.cons_app in H1. 
  apply those_app_inv in H1 as (tl1 & tl2 & Htl1 & Htl2 & Htl).
  unfold those in Htl1.
  simpl in Htl1. unfold read_bytes, those => //=.
  rewrite N.add_0_r.
  destruct (mem_lookup _ _) ; inversion Htl1.
  rewrite - H3 in Htl.
  by inversion Htl.
  rewrite drop_length in H1.
  replace (length bs - (length bs - S k1)) with (S k1) in H1 ; last lia.
  simpl in H1.
  rewrite list_extra.cons_app in H1. 
  apply those_app_inv in H1 as (tl1 & tl2 & Htl1 & Htl2 & Htl).
  replace (S (length bs - S k1)) with (length bs - k1) in Htl2 ; last lia.
  rewrite drop_length.
  replace (length bs - (length bs - k1)) with k1 ; last lia.  
  rewrite Htl2.
  unfold those in Htl1.
  simpl in Htl1.
  destruct (mem_lookup _ _) ; inversion Htl1 ; subst.
  inversion Htl.
  rewrite - (take_drop 1 (drop _ _)) in H3. 
  destruct (drop (length bs - S k1) bs) eqn:Hdrop.
  assert (length (drop (length bs - S k1) bs) = 0) ; first by rewrite Hdrop.
  rewrite drop_length in H1. lia.
  unfold take in H3.
  rewrite <- Hdrop in H3.
  rewrite drop_drop in H3.
  inversion H3.
  replace (length bs - S k1 +1) with (length bs - k1) ; last lia.
  done.
Qed.  
(*

Lemma store_trivial_extension m k off bs m' bs' :
  store m k off bs (length bs) = Some m' ->
  load m k (off + N.of_nat (length bs))%N (length bs') = Some bs' ->
  store m k off (bs ++ bs') (length bs + length bs') = Some m'.
Proof.
Admitted.


Lemma if_store_then_load m k off bs m' :
  store m k off bs (length bs) = Some m' ->
  load m' k off (length bs) = Some bs.
Proof.
Admitted.
*)





Lemma store_append m k off b bs m':
  store m k off (b :: bs) (length (b :: bs)) = Some m' ->
  exists m'', store m k (off + 1)%N bs (length bs) = Some m'' /\
           store m'' k off [b] 1 = Some m'.
Proof.
  intros Hm.
  apply store_append1 in Hm as (m0 & Hm0 & Hm0').
  eapply swap_stores => //=.
Qed.


(* Earlier version of the proof, which relies on not-yet-proven lemmas : *)
(*
assert (mem_length m = mem_length m') as Hmm'.
  { unfold mem_length, memory_list.mem_length. erewrite store_length => //=. }
  assert (store m k off (b :: bs) (length (b :: bs)) = Some m') as Hm2 => //=.
  unfold store in Hm.
  destruct (k + off + N.of_nat (length (b :: bs)) <=? mem_length m)%N eqn:Hlen ;
    try by inversion Hm.
  replace (N.of_nat (length (b :: bs))) with (1 + N.of_nat (length bs))%N in Hlen ;
    last by simpl ; lia. rewrite N.add_assoc in Hlen.
  assert (exists b0, load m k off 1 = Some [b0]) as [b0 Hb0].
  { unfold load. apply N.leb_le in Hlen.
    assert (k + off + 1 <= k + off + 1 + N.of_nat (length bs))%N ; first lia.
    eapply N.le_trans in Hlen => //=.
    apply N.leb_le in Hlen. rewrite N.add_assoc. rewrite Hlen.
    unfold read_bytes => //=. unfold those => //=.
    unfold mem_lookup. 
    rewrite (nth_error_nth' _ b). simpl. by eexists _.
    rewrite N.add_0_r. apply N.leb_le in Hlen.
    unfold mem_length, memory_list.mem_length in Hlen. lia. }
  assert (exists m'', store m' k off [b0] 1 = Some m'') as [m'' Hm''].
  { unfold store. apply N.leb_le in Hlen. rewrite Hmm' in Hlen.
    assert (k + off + 1 <= k + off + 1 + N.of_nat (length bs))%N ; first lia.
    eapply N.le_trans in Hlen => //=.
    apply N.leb_le in Hlen. rewrite Hlen.
    unfold write_bytes. unfold fold_lefti => //=. rewrite N.add_0_r.
    unfold mem_update. unfold mem_length, memory_list.mem_length in Hlen.
    apply N.leb_le in Hlen.
    assert (k + off < N.of_nat (length (ml_data (mem_data m'))))%N ; first lia.
    apply N.ltb_lt in H0.
    rewrite H0. by eexists _. }
  exists m''. split.
  - assert (store m k off (b0 :: bs) (length (b0 :: bs)) = Some m'').
    eapply store_trans => //=. by simpl. 
    rewrite list_extra.cons_app.
    apply store_trivial_extension => //=.
    apply if_store_then_load in Hm2.
    apply load_append in Hm2. done.
    unfold store in H.
    unfold write_bytes in H.
    unfold fold_lefti in H.
    simpl in H.
    rewrite N.add_0_r in H. 
    rewrite trivial_update in H.
    unfold store.
    replace (k + off + N.pos (Pos.of_succ_nat (length bs)))%N with
      (k + (off + 1) + N.of_nat (length bs))%N in H ; last lia.
    destruct (k + (off + 1) + N.of_nat (length bs) <=? mem_length m)%N ;
      try by inversion H.
    unfold write_bytes.
    unfold fold_lefti.
    destruct (fold_left _ _ _) eqn:Hfl.
    replace 1 with (0+1) in Hfl ; last lia.
    rewrite (fold_left_lift _ (λ '(k0, acc) x,
                                (k0 + 1,
                                  match acc with
                                    Some dat => mem_update (k + (off + 1) + N.of_nat k0)%N x dat
                                      | None => None end ))) in Hfl.
    apply incr_fst_equals in Hfl.
    rewrite Hfl. done.
    intros => //=. unfold incr_fst => //=.
    replace (k + off + N.of_nat (i + 1))%N with (k + (off + 1) + N.of_nat i)%N ; last lia.
    done.
    unfold load in Hb0.
    destruct (k + (off + N.of_nat 1) <=? mem_length m)%N ; by inversion Hb0. 
  - assert (exists m''', store m'' k off [b] 1 = Some m''') as [m''' Hm'''].
    { unfold store.
      replace (mem_length m'') with (mem_length m') ;
        last by unfold mem_length, memory_list.mem_length ; erewrite store_length.
      apply N.leb_le in Hlen. rewrite Hmm' in Hlen.
      assert (k + off + 1 <= k + off + 1 + N.of_nat (length bs))%N ; first lia.
      eapply N.le_trans in Hlen => //=.
      apply N.leb_le in Hlen.
      rewrite Hlen.
      unfold write_bytes. unfold fold_lefti => //=. rewrite N.add_0_r.
      unfold mem_update. unfold mem_length, memory_list.mem_length in Hlen.
      apply N.leb_le in Hlen.
      assert (k + off < N.of_nat (length (ml_data (mem_data m'))))%N ; first lia.
      apply N.ltb_lt in H0.
      replace (length (ml_data (mem_data m''))) with
        (length (ml_data (mem_data m'))) ; last by erewrite store_length.
      rewrite H0. by eexists _. }
    replace 1 with (length [b0]) in Hm'' => //=.
    replace 1 with (length [b]) in Hm''' => //=.
    assert (length [b0] = length [b]) => //=.
    rewrite Hm'''.
    apply (store_trans _ _ _ _ _ _ _ H Hm'') in Hm''' => //=.
    rewrite store_trivial in Hm''' => //=.
    apply if_store_then_load in Hm2.
    unfold load ; unfold load in Hm2.
    destruct (k + (off + N.of_nat (length (b :: bs))) <=? mem_length m')%N eqn:Hlen' ;
      try by inversion Hm2.
    apply N.leb_le in Hlen'.
    simpl in Hlen'.
    assert (k + (off + N.of_nat 1) <=
              k + (off + N.pos (Pos.of_succ_nat (length bs))))%N ; first lia.
    apply (N.le_trans _ _ _ H0) in Hlen' => //=.
    apply N.leb_le in Hlen'. rewrite Hlen'.
    unfold read_bytes in Hm2.
    simpl in Hm2. rewrite list_extra.cons_app in Hm2.
    destruct (those_app_inv [mem_lookup (k + off + 0)%N (mem_data m')] _ _ Hm2)
      as (tl1 & tl2 & Htl1 & Htl2 & Htl).
    unfold those in Htl1. simpl in Htl1.
    unfold read_bytes. unfold those => //=.
    destruct (mem_lookup (k + off + 0)%N (mem_data m')) ; inversion Htl1.
    subst. inversion Htl ; subst => //=.
Qed.                             *)

    

Lemma gen_heap_update_big_wm bs bs' k off n (mems mems' : list memory) (m m' : memory) :
  length bs = length bs' -> 
  load m k off (length bs) = Some bs ->
  store m k off bs' (length bs') = Some m' ->
  update_list_at mems n m' = mems' ->
  mems !! n = Some m ->
  gen_heap_interp (gmap_of_memory mems) -∗
                  N.of_nat n ↦[wms][N.add k off] bs ==∗
                  gen_heap_interp (gmap_of_memory mems') ∗
                  N.of_nat n ↦[wms][N.add k off] bs'.
Proof.
  move : mems' m' off bs'.
  induction bs ; iIntros (mems' m' off bs' Hlen Hm Hm' Hmems Hmemsn) "Hσ Hwms".
  { simpl in Hlen. apply Logic.eq_sym, nil_length_inv in Hlen ; subst.
    iSplitR "Hwms" => //=.
    rewrite update_trivial => //=.
    simpl in Hm'. unfold store in Hm'.
    simpl in Hm. unfold load in Hm.
    rewrite <- N.add_assoc in Hm'.
    destruct (k + (off + N.of_nat 0) <=? mem_length m)%N ; try by inversion Hm.
    unfold write_bytes in Hm'. simpl in Hm'.
    destruct m ; simpl in Hm'.
    by rewrite Hm' in Hmemsn. }
  destruct bs' ; inversion Hlen.
  iDestruct (wms_append with "Hwms") as "[Hwm Hwms]".
  rewrite <- N.add_assoc.
  destruct (store_append _ _ _ _ _ _ Hm') as (m'' & Hm'' & Hb).
  iMod (IHbs with "Hσ Hwms") as "[Hσ Hwms]" => //; first by eapply load_append.
  iMod (gen_heap_update with "Hσ Hwm") as "[Hσ Hwm]". 
  iIntros "!>".
  iSplitR "Hwms Hwm" ; last by iApply wms_append ; rewrite N.add_assoc ; iFrame.

  unfold store in Hb.
  destruct (k + off + N.of_nat 1 <=? mem_length m'')%N eqn: Hlen0; try by inversion Hb.
  unfold write_bytes, fold_lefti in Hb ; simpl in Hb.
  rewrite N.add_0_r in Hb.
  destruct (mem_update (k + off)%N b (mem_data m'')) eqn:Hupd ; inversion Hb; clear Hb.

  rewrite update_list_at_insert ; last by apply lookup_lt_Some in Hmemsn.
  rewrite update_list_at_insert in Hmems ; last by apply lookup_lt_Some in Hmemsn.

  rewrite <- Hmems.
  rewrite <- H1.
  erewrite gmap_of_memory_insert => //.
  - rewrite Nat2N.id.
    by rewrite list_insert_insert.
  - rewrite Nat2N.id.
    rewrite list_lookup_insert => //; last by apply lookup_lt_Some in Hmemsn.
  - simpl in Hlen0.
    move/N.leb_spec0 in Hlen0.
    unfold mem_length, memory_list.mem_length in Hlen0.
    lia.
Qed.

(*
(* A version of gen_heap_update specifically for wasm memories. *)
Lemma gen_heap_update_big_wm σ n ml ml':
  gen_heap_interp σ -∗ 
  ([∗ list] i ↦ b ∈ ml, N.of_nat n ↦[wm][N.of_nat i] b) ==∗
  gen_heap_interp ((new_2d_gmap_at_n (N.of_nat n) ml') ∪ σ) ∗
  ([∗ list] i ↦ b ∈ ml', N.of_nat n ↦[wm][N.of_nat i] b).
Proof.
(*  revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
  { rewrite left_id_L. auto. }
  iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
  decompose_map_disjoint.
  rewrite !big_opM_insert // -insert_union_l //.
  by iMod (gen_heap_alloc with "Hσ'σ") as "($ & $ & $)";
    first by apply lookup_union_None.*)
Admitted.
*)

Lemma length_bits v t:
  types_agree t v -> length (bits v) = t_length t.
Proof.
  intros. unfold bits.
  destruct v ; destruct t ; by inversion H.
Qed.


Lemma memory_in_bounds m i b :
  (ml_data (mem_data m)) !! i = Some b -> i < N.to_nat (mem_length m) .
Proof.
  intros. 
  apply lookup_lt_Some in H. unfold mem_length, memory_list.mem_length.
  lia.
Qed.



Lemma map_app {A B} (l1 : list A) l2 (f : A -> B) : map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  induction l1 ; intros ; try done.
  simpl. by rewrite IHl1.
Qed. 

Lemma take_drop {A} n (l : list A) : n < length l -> l = seq.take n l ++ seq.drop n l.
Proof.
  intros. generalize dependent n. induction l ; intros.  by inversion H.
  destruct n. by unfold take, drop.
  simpl. rewrite <- (IHl n) => //=. simpl in H ; lia.
Qed.


Lemma those_map_Some (f : nat -> option byte) (l : list byte) :
  (forall x : nat, x < length l -> f x = l !! x) ->
  those (map f (iota 0 (length l))) = Some l.
Proof.
  remember (length l) as n. generalize dependent l.
  induction n ; intros.
  { apply Logic.eq_sym, nil_length_inv in Heqn ; subst ; by unfold those. }
  destruct l ; first by inversion Heqn. 
  cut (exists ys y, b :: l = ys ++ [y]) ;
  [ intro Htail ; destruct Htail as (ys & y & Htail) |
    exists (removelast (b :: l)) ;
    exists (List.last (b :: l) b) ;
    apply app_removelast_last ;
    apply not_eq_sym ; apply nil_cons ].
  rewrite Htail. rewrite Htail in Heqn. rewrite Htail in H.
  rewrite app_length in Heqn. simpl in Heqn.
  rewrite Nat.add_1_r in Heqn. inversion Heqn.
  assert (forall x, x < n -> f x = ys !! x).
  { intros. rewrite H ; last lia.
    rewrite lookup_app_l => //=. by rewrite <- H1. }
  destruct n. rewrite <- H1. apply Logic.eq_sym, nil_length_inv in H1. rewrite H1.
  unfold those => //=. rewrite H. rewrite H1 => //=. lia.
  rewrite (take_drop (length ys) (iota 0 (S (length ys)))).
  rewrite take_iota. 
  unfold ssrnat.minn. 
  replace (S (length ys - 1)) with (length ys) ; last by rewrite <- H1 ; lia.
  rewrite ssrnat.leqnn.
  rewrite drop_iota => //=.
  unfold ssrnat.addn , ssrnat.addn_rec. replace (0+length ys) with (length ys) ; last lia.
  unfold ssrnat.subn, ssrnat.subn_rec. replace (S (length ys) - length ys) with 1 ; last lia.
  simpl.
  rewrite map_app. apply those_app. rewrite <- H1. apply (IHn ys H1 H0).
  unfold those => //=. rewrite H. 
  rewrite list_lookup_middle => //=. rewrite <- H1 ; lia.
  replace (length (iota 0 (S (length ys)))) with (seq.size (iota 0 (S (length ys)))) ;
    last done.
  rewrite size_iota. lia.
Qed.


Lemma wms_is_load n k off v m t ws :
  types_agree t v -> s_mems (host_function := host_function) ws !! n = Some m ->
  (N.of_nat n ↦[wms][ k + off ] (bits v) -∗
            gen_heap_interp (gmap_of_memory (s_mems ws))
            -∗ ⌜ load m k off (t_length t) = Some (bits v) ⌝).
Proof.
  iIntros (Htv Hm) "Hwms Hm".
  iAssert ( (∀ i, ⌜ i < length (bits v) ⌝ -∗
                               ⌜ (ml_data (mem_data m)) !! (N.to_nat (k + off + N.of_nat i))
                  = (bits v) !! i ⌝)%I ) as "%Hmeq".
  { iIntros (i) "%Hi".
    iDestruct (big_sepL_lookup with "Hwms") as "H" => //.
    destruct (nth_lookup_or_length (bits v) i (encode 1)) => //=.
    lia.
    iDestruct (gen_heap_valid with "Hm H") as "%H".
    rewrite gmap_of_list_2d_lookup list_lookup_fmap Nat2N.id Hm in H.
    unfold memory_to_list in H. simpl in H. rewrite Nat2N.id in H.
    iPureIntro. replace (N.to_nat (k + off + N.of_nat i)) with
      (N.to_nat (k + off) + i). rewrite H.
    apply Logic.eq_sym.
    destruct (nth_lookup_or_length (bits v) i (encode 1)) => //=.
    lia. lia. } 
  iPureIntro.
  unfold load.
  assert (length (bits v) > 0). erewrite length_bits => //=. destruct t ; simpl ; lia.
  replace (k + (off + N.of_nat (t_length t)) <=? mem_length m)%N with true.
  unfold read_bytes, mem_lookup.
  remember (t_length t) as tl.
  induction tl. { simpl. unfold those => //=. erewrite <- length_bits in Heqtl => //=.
                  apply Logic.eq_sym, nil_length_inv in Heqtl. by rewrite Heqtl. }
  rewrite Heqtl. erewrite <- length_bits => //=.
  apply those_map_Some => //=.
  intros.
  rewrite nth_error_lookup. by apply Hmeq.
  apply Logic.eq_sym, N.leb_le.
  assert (ml_data (mem_data m) !! N.to_nat (k + off + N.of_nat (length (bits v) - 1)) =
            (bits v) !! (length (bits v) - 1)). apply Hmeq ; first lia.
  destruct (nth_lookup_or_length (bits v) (length (bits v) - 1) (encode 1)) => //=. 
  rewrite e in H0.
  apply memory_in_bounds in H0. unfold lt in H0.
  replace (S (N.to_nat (k + off + N.of_nat (length (bits v) - 1)))) with
    (N.to_nat (k + (off + N.of_nat (t_length t)))) in H0. lia.
  rewrite <- N2Nat.inj_succ. 
  rewrite <- N.add_succ_r. 
  rewrite <- Nat2N.inj_succ.
  replace (S (length (bits v) - 1)) with (length (bits v)) ; last lia.
  erewrite length_bits => //=. rewrite N.add_assoc. done.
  lia.
Qed.


Lemma if_load_then_store bs bs' m k off :
  length bs = length bs' ->
  load m k off (length bs) = Some bs ->
  exists m', store m k off bs' (length bs') = Some m'.
Proof.
  intros Hlen Hload.
  unfold store, write_bytes, fold_lefti.
  unfold load, read_bytes in Hload.
  rewrite N.add_assoc in Hload.
  rewrite - Hlen.
  destruct (_ <=? _)%N eqn:Hklen ; try by inversion Hload.
  cut (forall i dat,
          length (ml_data dat) = length (ml_data (mem_data m)) ->
          i <= length bs ->
          let j := length bs - i in
          those (map (λ off0, mem_lookup (k + off + N.of_nat off0)%N (mem_data m))
                     (iota j i)) = Some (drop j bs) ->
          exists dat', (let '(_, acc_end) :=
                     fold_left
                       (λ '(k0, acc) x,
                         (k0 + 1,
                           match acc with
                           | Some dat => mem_update (k + off + N.of_nat k0)%N x dat
                           | None => None
                           end)) (bytes_takefill #00%byte i (drop j bs'))
                       (j, Some dat) in acc_end) = Some dat').
  - intros Hi.
    assert (length bs <= length bs) ; first lia.
    eapply Hi in H as [dat' Hdat'].
    + rewrite PeanoNat.Nat.sub_diag in Hdat'.
      unfold drop in Hdat'.
      rewrite Hdat'.
      by eexists _.
    + done.
    + rewrite PeanoNat.Nat.sub_diag.
      unfold drop.
      exact Hload.
  - induction i ; intros ; subst j.
    + rewrite Nat.sub_0_r.
      rewrite Hlen.
      rewrite drop_all.
      simpl.
      by eexists _.
    + assert (i <= length bs) ; first lia.
      destruct (drop (length bs - S i) bs') eqn:Hdrop.
      * assert (length (drop (length bs - S i) bs') = 0) ; first by rewrite Hdrop.
        rewrite drop_length in H3. lia.
      * destruct (drop (length bs - S i) bs) eqn:Hdrop0.
        **  assert (length (drop (length bs - S i) bs) = 0) ; first by rewrite Hdrop0.
            rewrite drop_length in H3. lia.
        ** assert (exists dat0, mem_update (k + off + N.of_nat (length bs - S i))%N b dat =
                             Some dat0) as [dat0 Hdat0].
           { unfold mem_update.
             assert (k + off + N.of_nat (length bs - S i) <
                       N.of_nat (length (ml_data dat)))%N.
             rewrite H.
             unfold mem_length, memory_list.mem_length in Hklen.
             apply N.leb_le in Hklen.
             lia.
             apply N.ltb_lt in H3.
             rewrite H3.
             by eexists _. } 
           eapply (IHi dat0) in H2 as [dat' Hdat'].
        ++ simpl.
           replace (length bs - i) with (length bs - S i + 1) in Hdat' ; last lia.
           rewrite - drop_drop in Hdat'.
           rewrite Hdrop in Hdat'.
           unfold drop in Hdat'.
           rewrite Hdat0.
           rewrite Hdat'.
           by eexists _.
        ++ rewrite - H.
           erewrite <- mem_update_length ; last exact Hdat0.
           done.
        ++ simpl in H1.
           rewrite - those_those0 in H1.
           unfold those0 in H1.
           fold (those0 (A:=byte)) in H1.
           rewrite those_those0 in H1.
           destruct (mem_lookup _ _) ; try by inversion H1.
           unfold option_map in H1.
           destruct (those (map (λ off0, mem_lookup (k + off + N.of_nat off0)%N
                                (mem_data m))
                                (iota (S (length bs - S i)) i)) )
                    eqn:Hth ; try by inversion H1.
           replace (S (length bs - S i)) with (length bs - i) in Hth ; last lia.
           rewrite Hth.
           inversion H1.
           replace (length bs - i) with (length bs - S i + 1) ; last lia.
           rewrite - drop_drop.
           rewrite Hdrop0 => //=.
Qed.           
                                                                    
                                                                    

(*

Lemma if_load_then_store m addr off val1 val2 size :
  load m addr off size = Some val1 ->
  exists m', store m addr off val2 size = Some m'.
Proof.
  intro Hload.
  unfold store.
  unfold load in Hload.
  rewrite <- N.add_assoc.
  destruct (addr + (off + N.of_nat size) <=? mem_length m)%N ;
    try by inversion Hload.
  unfold write_bytes.
  unfold read_bytes in Hload.
  generalize dependent val1.
  induction size ; intros.
  - by eexists.
  - rewrite (take_drop size (iota 0 (S size))) in Hload.
    rewrite take_iota in Hload.
    unfold ssrnat.minn in Hload. 
    rewrite ssrnat.leqnn in Hload.
    rewrite drop_iota in Hload.
    unfold ssrnat.addn, ssrnat.addn_rec in Hload.
    replace (0+size) with size in Hload ; last lia.
    unfold ssrnat.subn, ssrnat.subn_rec in Hload.
    replace (S size - size) with 1 in Hload ; last lia.
    simpl in Hload.
    rewrite map_app in Hload.
    destruct (those_app_inv _ _ _ Hload) as (tl1 & tl2 & Hth1 & Hth2 & Htl).
    apply IHsize in Hth1.
    destruct Hth1 as [m' Hm].


    simpl. destruct val2 => //=. unfold fold_lefti => //=.
    (* Work in progress *)
    Admitted. *)



Lemma deserialise_bits v t :
  types_agree t v -> wasm_deserialise (bits v) t = v.
Proof.
  intros Htv.
  unfold wasm_deserialise.
  destruct t ;
    unfold bits ;
    destruct v ; (try by inversion Htv).
  rewrite Memdata.decode_encode_int.
  rewrite Z.mod_small.
  by rewrite Wasm_int.Int32.repr_unsigned.
  destruct s ; simpl ; replace (two_power_pos (_ * _))
    with Wasm_int.Int32.modulus ; [lia | done].
  rewrite Memdata.decode_encode_int.
  rewrite Z.mod_small.
  by rewrite Wasm_int.Int64.repr_unsigned.
  destruct s ; simpl ; replace (two_power_pos (_ * _))
    with Wasm_int.Int64.modulus ; [lia | done].
  rewrite Memdata.decode_encode_int_4.
  by rewrite Wasm_float.FloatSize32.of_to_bits.
  rewrite Memdata.decode_encode_int_8.
  by rewrite Wasm_float.FloatSize64.of_to_bits.
Qed.




Lemma bits_deserialise bs t :
  length bs = t_length t ->
  bits (wasm_deserialise bs t) = bs.
Proof.
  intros Hlen.
  unfold wasm_deserialise.
  destruct t ; simpl in Hlen ;
    repeat (destruct bs ; try by inversion Hlen) ;
    unfold bits.
  - unfold serialise_i32.
    rewrite Wasm_int.Int32.unsigned_repr ;
      unfold Memdata.decode_int, Memdata.int_of_bytes,  Memdata.rev_if_be.
    unfold Memdata.encode_int, Memdata.bytes_of_int, Memdata.rev_if_be.
    destruct Archi.big_endian ;
      unfold Memdata.int_of_bytes ;    
      simpl ; 
      rewrite Z.mul_0_l ; 
      rewrite Z.add_0_r ; 
      do 3 ( rewrite Z_div_plus ; last lia ;
             rewrite (Z.div_small (Integers.Byte.unsigned _) 256) ;
             last (by replace 256%Z with Integers.Byte.modulus ; last done ;
                     by apply Integers.Byte.unsigned_range) ; 
             rewrite Z.add_0_l) ; 
      rewrite Integers.Byte.repr_unsigned ;
      do 3 ( erewrite (Integers.Byte.eqm_repr_eq (Integers.Byte.unsigned _ + _) _) ;
             last (unfold Integers.Byte.eqm ;
                   replace Integers.Byte.modulus with 256%Z ; last done ;
                   unfold Zbits.eqmod ;
                   eexists _ ; by rewrite Z.add_comm)) ; 
      done.
    destruct Archi.big_endian ;
      simpl ;
      replace Wasm_int.Int32.max_unsigned with 4294967295%Z ; try done ;
      specialize (Integers.Byte.unsigned_range b) ; intros H ;
      replace Integers.Byte.modulus with 256%Z in H ; try done ;
      specialize (Integers.Byte.unsigned_range b0) ; intros H0 ;
      replace Integers.Byte.modulus with 256%Z in H0 ; try done ;
      specialize (Integers.Byte.unsigned_range b1) ; intros H1 ;
      replace Integers.Byte.modulus with 256%Z in H1 ; try done ;
      specialize (Integers.Byte.unsigned_range b2) ; intros H2 ;
      replace Integers.Byte.modulus with 256%Z in H2 ; try done ;
      lia.
  - unfold serialise_i64.
    rewrite Wasm_int.Int64.unsigned_repr ;
      unfold Memdata.decode_int, Memdata.int_of_bytes, Memdata.rev_if_be.
    unfold Memdata.encode_int, Memdata.bytes_of_int, Memdata.rev_if_be.
    destruct Archi.big_endian ;
      unfold Memdata.int_of_bytes ; 
      simpl ; 
      rewrite Z.mul_0_l ; 
      rewrite Z.add_0_r ; 
      do 7 ( rewrite Z_div_plus ; last lia ;
             rewrite (Z.div_small (Integers.Byte.unsigned _) 256) ;
             last (by replace 256%Z with Integers.Byte.modulus ; last done ;
                     by apply Integers.Byte.unsigned_range) ; 
             rewrite Z.add_0_l) ; 
      rewrite Integers.Byte.repr_unsigned ;
      do 7 ( erewrite (Integers.Byte.eqm_repr_eq (Integers.Byte.unsigned _ + _) _) ;
             last (unfold Integers.Byte.eqm ;
                   replace Integers.Byte.modulus with 256%Z ; last done ;
                   unfold Zbits.eqmod ;
                   eexists _ ; by rewrite Z.add_comm)) ;
      done.
    destruct Archi.big_endian ;
      simpl ;
      specialize (Integers.Byte.unsigned_range b) ; intros H ;
      replace Integers.Byte.modulus with 256%Z in H ; try done ;
      specialize (Integers.Byte.unsigned_range b0) ; intros H0 ;
      replace Integers.Byte.modulus with 256%Z in H0 ; try done ;
      specialize (Integers.Byte.unsigned_range b1) ; intros H1 ;
      replace Integers.Byte.modulus with 256%Z in H1 ; try done ;
      specialize (Integers.Byte.unsigned_range b2) ; intros H2 ;
      replace Integers.Byte.modulus with 256%Z in H2 ; try done ;
      specialize (Integers.Byte.unsigned_range b3) ; intros H3 ;
      replace Integers.Byte.modulus with 256%Z in H3 ; try done ;
      specialize (Integers.Byte.unsigned_range b4) ; intros H4 ;
      replace Integers.Byte.modulus with 256%Z in H4 ; try done ;
      specialize (Integers.Byte.unsigned_range b5) ; intros H5 ;
      replace Integers.Byte.modulus with 256%Z in H5 ; try done ;
      specialize (Integers.Byte.unsigned_range b6) ; intros H6 ;
      replace Integers.Byte.modulus with 256%Z in H6 ; try done ;
      replace Wasm_int.Int64.max_unsigned with 18446744073709551615%Z ; try done ;
      lia.
  - unfold serialise_f32.
    rewrite Wasm_float.FloatSize32.to_of_bits Integers.Int.unsigned_repr ;
      unfold Memdata.decode_int, Memdata.int_of_bytes , Memdata.rev_if_be.
    unfold Memdata.encode_int, Memdata.bytes_of_int, Memdata.rev_if_be.
    destruct Archi.big_endian ;
      unfold Memdata.int_of_bytes ;    
      simpl ; 
      rewrite Z.mul_0_l ; 
      rewrite Z.add_0_r ;
      do 3 ( rewrite Z_div_plus ; last lia ;
             rewrite (Z.div_small (Integers.Byte.unsigned _) 256) ;
             last (by replace 256%Z with Integers.Byte.modulus ; last done ;
                     by apply Integers.Byte.unsigned_range) ; 
             rewrite Z.add_0_l) ;
      rewrite Integers.Byte.repr_unsigned ;
      do 3 ( erewrite (Integers.Byte.eqm_repr_eq (Integers.Byte.unsigned _ + _) _) ;
             last (unfold Integers.Byte.eqm ;
                   replace Integers.Byte.modulus with 256%Z ; last done ;
                   unfold Zbits.eqmod ;
                   eexists _ ; by rewrite Z.add_comm)) ;
      done.
    destruct Archi.big_endian ;
      simpl ;
      replace Integers.Int.max_unsigned with 4294967295%Z ; try done ;
      specialize (Integers.Byte.unsigned_range b) ; intros H ;
      replace Integers.Byte.modulus with 256%Z in H ; try done ;
      specialize (Integers.Byte.unsigned_range b0) ; intros H0 ;
      replace Integers.Byte.modulus with 256%Z in H0 ; try done ;
      specialize (Integers.Byte.unsigned_range b1) ; intros H1 ;
      replace Integers.Byte.modulus with 256%Z in H1 ; try done ;
      specialize (Integers.Byte.unsigned_range b2) ; intros H2 ;
      replace Integers.Byte.modulus with 256%Z in H2 ; try done ;
      lia.
  - unfold serialise_f64.
    rewrite Wasm_float.FloatSize64.to_of_bits Integers.Int64.unsigned_repr ;
      unfold Memdata.decode_int, Memdata.int_of_bytes, Memdata.rev_if_be.
    unfold Memdata.encode_int, Memdata.bytes_of_int, Memdata.rev_if_be.
    destruct Archi.big_endian ;
      unfold Memdata.int_of_bytes ; 
      simpl ; 
      rewrite Z.mul_0_l ; 
      rewrite Z.add_0_r ; 
      do 7 ( rewrite Z_div_plus ; last lia ;
             rewrite (Z.div_small (Integers.Byte.unsigned _) 256) ;
             last (by replace 256%Z with Integers.Byte.modulus ; last done ;
                     by apply Integers.Byte.unsigned_range) ; 
             rewrite Z.add_0_l) ; 
      rewrite Integers.Byte.repr_unsigned ;
      do 7 ( erewrite (Integers.Byte.eqm_repr_eq (Integers.Byte.unsigned _ + _) _) ;
             last (unfold Integers.Byte.eqm ;
                   replace Integers.Byte.modulus with 256%Z ; last done ;
                   unfold Zbits.eqmod ;
                   eexists _ ; by rewrite Z.add_comm)) ;
      done.
    destruct Archi.big_endian ;
      simpl ;
      specialize (Integers.Byte.unsigned_range b) ; intros H ;
      replace Integers.Byte.modulus with 256%Z in H ; try done ;
      specialize (Integers.Byte.unsigned_range b0) ; intros H0 ;
      replace Integers.Byte.modulus with 256%Z in H0 ; try done ;
      specialize (Integers.Byte.unsigned_range b1) ; intros H1 ;
      replace Integers.Byte.modulus with 256%Z in H1 ; try done ;
      specialize (Integers.Byte.unsigned_range b2) ; intros H2 ;
      replace Integers.Byte.modulus with 256%Z in H2 ; try done ;
      specialize (Integers.Byte.unsigned_range b3) ; intros H3 ;
      replace Integers.Byte.modulus with 256%Z in H3 ; try done ;
      specialize (Integers.Byte.unsigned_range b4) ; intros H4 ;
      replace Integers.Byte.modulus with 256%Z in H4 ; try done ;
      specialize (Integers.Byte.unsigned_range b5) ; intros H5 ;
      replace Integers.Byte.modulus with 256%Z in H5 ; try done ;
      specialize (Integers.Byte.unsigned_range b6) ; intros H6 ;
      replace Integers.Byte.modulus with 256%Z in H6 ; try done ;
      replace Integers.Int64.max_unsigned with 18446744073709551615%Z ; try done ;
      lia.
Qed.    


Lemma deserialise_type bs t :
  types_agree t (wasm_deserialise bs t).
Proof.
  unfold wasm_deserialise.
  by destruct t.
Qed.



Lemma no_memory_no_memories ws n :
  s_mems (host_function := host_function) ws !! n = None ->
  forall k, gmap_of_memory (s_mems ws) !! (N.of_nat n, k) = None.
Proof.
  intros.
  unfold gmap_of_memory.
  rewrite gmap_of_list_2d_lookup => //=.
  rewrite Nat2N.id. 
  rewrite list_lookup_fmap H => //=.
Qed.



Lemma wms_implies_smems_is_Some ws n k b bs :
  gen_heap_interp (gmap_of_memory (s_mems ws)) -∗
                  ([∗ list] i ↦ b  ∈ (b :: bs), mapsto (L:=N*N) (V:=byte)
                                                     (N.of_nat n, N.of_nat (N.to_nat k+i))
                                                     (DfracOwn 1) b) -∗
                  (([∗ list] i ↦ b  ∈ (b :: bs), mapsto (L:=N*N) (V:=byte)
                                                     (N.of_nat n, N.of_nat (N.to_nat k+i))
                                                     (DfracOwn 1) b) ∗
                                                                     gen_heap_interp (gmap_of_memory (s_mems ws)) ∗
                            ⌜ exists m, s_mems (host_function := host_function) ws !! n = Some m ⌝).
Proof.
  iIntros "Hm Hwms".
  unfold big_opL.
  iDestruct "Hwms" as "[Hwm Hwms]".
  rewrite Nat.add_0_r. rewrite N2Nat.id.
  iDestruct (gen_heap_valid with "Hm Hwm") as "%Hm".
  iSplitR "Hm".
  - by iSplitL "Hwm".
  - iSplitL => //=. iPureIntro.
    destruct (s_mems ws !! n) as [m|] eqn:Hn ; first by eexists.
    rewrite no_memory_no_memories in Hm => //=.
Qed.



Lemma wp_load (Φ:iris.val -> iProp Σ) (s:stuckness) (E:coPset) (t:value_type) (v:value)
      (inst:instance) (off: static_offset) (a: alignment_exponent)
      (k: i32) (n:nat) (f0: frame):
  types_agree t v ->
  f0.(f_inst).(inst_memory) !! 0 = Some n ->
  (Φ (immV [v]) ∗
   ↪[frame] f0 ∗
     N.of_nat n ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ]
     (bits v) ⊢
     (WP [AI_basic (BI_const (VAL_int32 k)) ;
          AI_basic (BI_load t None a off)] @ s; E {{ w, (Φ w ∗ (N.of_nat n) ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ](bits v)) ∗ ↪[frame] f0 }})).
Proof.
  iIntros (Htv Hinstn) "[HΦ [Hf0 Hwms]]".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & Hm & ? & Hframe & Hγ)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0.
  inversion Hf0; subst; clear Hf0.
  destruct (bits v) eqn:Hb.
  destruct v ; inversion Hb.
  iDestruct (wms_implies_smems_is_Some with "Hm Hwms") as "(Hwms & Hm & %Hm)".
  destruct Hm as [m Hm].
  rewrite <- Hb.
  iDestruct (wms_is_load with "Hwms Hm") as "%Hload" => //=.
  rewrite - nth_error_lookup in Hm.
  rewrite - nth_error_lookup in Hinstn.
  simpl in Hinstn.
  destruct (inst_memory winst) eqn:Hinstmem => //.
  inversion Hinstn; subst; clear Hinstn.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], [AI_basic (BI_const _)], (hs, ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_load_success => //.
    unfold smem_ind.
    by rewrite Hinstmem.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H as [ H | [ [? Hfirst] | [ [a0 [cl [tf [h [Hfirst [Hnth Hcl]]]]]] | (?&?&?&Hfirst & Hfirst2 &
                                                                  Hfirst3 & Hσ)]]] ;
      last (eapply r_load_success => //= ; unfold smem_ind ; by rewrite Hinstmem) ;
      try by     unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    rewrite deserialise_bits in H => //=.
    inversion H ; subst. iFrame.
Qed.



Lemma wp_store (ϕ: iris.val -> iProp Σ) (s: stuckness) (E: coPset) (t: value_type) (v: value) (*(mem mem': memory)*) (bs : bytes) (off: static_offset) (a: alignment_exponent) (k: i32) (n: nat) (f0: frame) :
  types_agree t v ->
  length bs = t_length t ->
  f0.(f_inst).(inst_memory) !! 0 = Some n ->
  (*store mem (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) = Some mem' -> *)
  (ϕ (immV []) ∗
   ↪[frame] f0 ∗
  N.of_nat n ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ] bs) ⊢
  (WP ([AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t None a off)]) @ s; E {{ w, (ϕ w ∗ (N.of_nat n) ↦[wms][ Wasm_int.N_of_uint i32m k + off ] (bits v)) ∗ ↪[frame] f0 }}).
Proof.
  iIntros (Hvt Hbs Hinstn) "[HΦ [Hf0 Hwms]]".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & Hm & ? & Hframe & Hγ)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0.
  inversion Hf0; subst; clear Hf0.
  erewrite <- (bits_deserialise bs) => //=.
  remember (wasm_deserialise bs t) as vinit.
  assert (types_agree t vinit) as Hvinit.
  { rewrite Heqvinit. by apply deserialise_type. }
  destruct (bits vinit) eqn:Hb. destruct vinit ; inversion Hb.
  iDestruct (wms_implies_smems_is_Some with "Hm Hwms") as "(Hwms & Hm & %Hm)".
  destruct Hm as [m Hm].
  rewrite <- Hb.
  iDestruct (wms_is_load with "Hwms Hm") as "%Hload" => //=.
  rewrite - nth_error_lookup in Hm.
  rewrite - nth_error_lookup in Hinstn.
  simpl in Hinstn.
  destruct (inst_memory winst) eqn: Hinstmem => //.
  inversion Hinstn; subst m0; clear Hinstn.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    edestruct (if_load_then_store (bits vinit) (bits v)) as [mem Hsomemem] ;
      repeat erewrite length_bits => //=.
    erewrite length_bits in Hsomemem => //=.
    eexists [], [], (hs, _ (*upd_s_mem ws (update_list_at (s_mems ws) n m') *), locs, winst), [].
    repeat split => //.
    eapply r_store_success => //=.
    unfold smem_ind.
    by rewrite Hinstmem.    
  - iIntros "!>" (es σ2 efs HStep).
    destruct σ2 as [[[hs2 ws2] locs2] winst2].
    edestruct (if_load_then_store (bits vinit) (bits v)) as [mem Hsomemem] ;
      repeat erewrite length_bits => //=.
    erewrite length_bits in Hsomemem => //=.
    iMod (gen_heap_update_big_wm (bits vinit) (bits v) with "Hm Hwms") as "[Hm Hwms]".
    do 2 erewrite length_bits => //=.
    erewrite length_bits => //=.
    erewrite length_bits => //=.
    done.
    rewrite nth_error_lookup in Hm => //=.
    iModIntro.
    destruct HStep as [HStep [-> ->]].
    eapply reduce_det in HStep as [H | [[? Hfirst] | [ [ a0 [cl [tf [h [Hfirst [Hnth Hcl]]]]] ] | (?&?&?& Hfirst & Hfirst2 &
                                                                       Hfirst3 & Hσ) ]]] ;
      last (eapply r_store_success => //= ; unfold smem_ind ; by rewrite Hinstmem) ;
      try by     unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    inversion H ; subst; clear H => /=.
    iFrame.
    rewrite update_list_at_insert; last by rewrite nth_error_lookup in Hm; apply lookup_lt_Some in Hm.
    (* erewrite gmap_of_memory_insert_block => // ; [ idtac | by rewrite - nth_error_lookup |]. (* by apply store_length in Hstore'; lia ]. *) *)
    rewrite list_fmap_insert.    
    assert (mem_length mem = mem_length m) as Hmsize.
    { rewrite <- (length_bits v) in Hsomemem => //=.
      apply store_length in Hsomemem.
      by unfold mem_length, memory_list.mem_length; rewrite Hsomemem. }
    rewrite Hmsize.
(*    assert (mem_length mem' = mem_length mem) as Hmsize'.
    { apply mem_equiv_length in Hmem.
      apply mem_equiv_length in Hmdata'.
      lia.
    }
    rewrite Hmsize'. *)
    rewrite list_insert_id; last by rewrite list_lookup_fmap; rewrite - nth_error_lookup; rewrite Hm.
    auto.
Qed. 




Lemma wp_current_memory (s: stuckness) (E: coPset) (k: nat) (n: N) (f0:frame) (mem: memory) (Φ: iris.val -> iProp Σ) :
  f0.(f_inst).(inst_memory) !! 0 = Some k ->
  (Φ (immV [(VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (N.div n page_size))))]) ∗
   ↪[frame] f0 ∗
   (N.of_nat k) ↦[wmlength] n) ⊢
   WP ([AI_basic (BI_current_memory)]) @ s; E {{ w, (Φ w ∗ (N.of_nat k) ↦[wmlength] n) ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hf) "(HΦ & Hf0 & Hmemlength)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & Hm & ? & Hframe & Hγ)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hframe".
  iDestruct (gen_heap_valid with "Hγ Hmemlength") as "%Hmemlength".
  rewrite lookup_insert in Hframe.
  inversion Hframe; subst; clear Hframe.
  rewrite - nth_error_lookup in Hf.
  rewrite gmap_of_list_lookup list_lookup_fmap Nat2N.id in Hmemlength => /=.
  destruct (s_mems ws !! k) eqn:Hmemlookup => //.
  rewrite - nth_error_lookup in Hmemlookup.
  simpl in Hmemlength.
  inversion Hmemlength; clear Hmemlength.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    exists [], [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (N.div n page_size)))))], (hs, ws, locs, winst), [].

    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_current_memory => //.
    unfold mem_size.
    by f_equal.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
    iFrame.
Qed.


(*
Lemma reduce_grow_memory hs ws f c hs' ws' f' es' k mem mem':
  f.(f_inst).(inst_memory) !! 0 = Some k ->
  nth_error (s_mems ws) k = Some mem ->
  reduce hs ws f [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_grow_memory)] hs' ws' f' es' ->
  ((hs', ws', f', es') = (hs, ws, f, [AI_basic (BI_const (VAL_int32 int32_minus_one))] ) \/
   (hs', ws', f', es') = (hs, (upd_s_mem ws (update_list_at (s_mems ws) k mem')), f, [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))))]) /\
  mem_grow mem (Wasm_int.N_of_uint i32m c) = Some mem').
Proof.
  move => Hinst Hmem HReduce.
  destruct f as [locs inst].
  destruct f' as [locs' inst'].
  (*only_one_reduction HReduce [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))))] locs inst locs' inst'.*)
Admitted. *)

Lemma big_opL_app {A} (l1 : list A) l2 (f : nat -> A -> iProp Σ) :
  ⊢ ([∗ list] i↦b ∈ (l1 ++ l2), f i b) ∗-∗
                               (([∗ list] i↦b ∈ l1, f i b) ∗
                                                           [∗ list] i↦b ∈ l2, f (i + length l1) b).
Proof.
  generalize dependent f.
  induction l1 ; intros f => //=.
  iSplit.
  iIntros "H".
  iSplitR => //=.
  iApply (big_sepL_impl with "H") => //=.
  iIntros "!>" (k x) "%Hk Hfx".
  by rewrite - plus_n_O.
  iIntros "[_ H]".
  iApply (big_sepL_impl with "H") => //=.
  iIntros "!>" (k x) "%Hk Hfx".
  by rewrite - plus_n_O.
  iSplit.
  iIntros "[H0 Hplus]".
  iDestruct (IHl1 (λ i b, f (S i) b) with "Hplus") as "[H1 H2]".
  iSplitR "H2".
  iFrame.
  iApply (big_sepL_impl with "H2") => //=.
  iIntros "!>" (k x) "%Hk Hfx".
  replace (k + S (length l1)) with (S (k + length l1)) => //= ; last lia.
  iIntros "[[H0 H1] H2]".
  iSplitL "H0" => //=.
  iDestruct (big_sepL_impl with "H2") as "H2".
  iAssert (□ (∀ k x, ⌜ l2 !! k = Some x ⌝ → f (k + S (length l1)) x -∗
                                              (λ i b, f (S (i + length l1)) b) k x))%I
    as "H".
  iIntros "!>" (k x) "%Hk Hfx".
  replace (k + S (length l1)) with (S (k + length l1)) => //= ; last lia.
  iDestruct ("H2" with "H") as "H2".
  iDestruct (IHl1 (λ i b, f (S i) b)) as "[Hl Hr]".
  iApply "Hr". iFrame.
Qed.



Lemma gen_heap_alloc_grow (m m' : memory) (mems mems' : list memory) (k : nat) (n : N) : 
  mems !! k = Some m ->
  mem_grow m n = Some m' ->
  update_list_at mems k m' = mems' ->
  gen_heap_interp (gmap_of_memory mems) ==∗
                  gen_heap_interp (gmap_of_memory mems')
                  ∗ N.of_nat k↦[wms][ mem_length m ]
                  repeat (ml_init (mem_data m)) (N.to_nat (n * page_size)).
Proof.
  iIntros (Hmems Hgrow Hupd) "Hmems".
  assert (k < length mems) as Hk ; first by eapply lookup_lt_Some.
  assert (length (seq.take k mems) = k) as Hlentake.
  { rewrite length_is_size size_takel => //=.
    unfold ssrnat.leq, ssrnat.subn, ssrnat.subn_rec.
    rewrite - length_is_size.
    replace (k - length mems) with 0 => //= ; lia. }
  unfold mem_grow, memory_list.mem_grow in Hgrow.
  destruct (mem_max_opt m) eqn:Hmaxlim.
  destruct (mem_size m +n <=? n0)%N ; inversion Hgrow.
  - remember (N.to_nat (n * page_size)) as size.
    clear Heqsize n Hgrow.
    remember (Some n0) as sn.
    clear Heqsn.
    subst mems' m' sn.
    iInduction size as [|size] "IH".
    + simpl.
      rewrite cats0.
      rewrite update_trivial.
      unfold mem_block_at_pos => //=.
      by iSplitL.
      rewrite Hmems.
      destruct m. by destruct mem_data => //=.
    + iMod ("IH" with "Hmems") as "[Hmems Hm]".
      iMod (gen_heap_alloc with "Hmems") as "( Hmems & Hown & Htk )".
      * unfold gmap_of_memory.
        instantiate (1 := (N.of_nat k, (mem_length m + N.of_nat(size))%N)).
        rewrite gmap_of_list_2d_lookup => //=.
        rewrite Nat2N.id.
        rewrite list_lookup_fmap => //=.
        unfold update_list_at => //=.
        rewrite list_lookup_middle => //=.
        unfold memory_to_list => //=.
        rewrite lookup_app_r.
        rewrite lookup_ge_None => //=.
        rewrite repeat_length.
        unfold mem_length, memory_list.mem_length.
        lia.
        unfold mem_length, memory_list.mem_length.
        lia.
      * iModIntro. 
        iSplitL "Hmems".
        -- instantiate (1 := ml_init (mem_data m)).
           replace (<[ _ := _ ]> (gmap_of_memory _)) with
             (gmap_of_memory
                (update_list_at
                   mems k
                   {| mem_data :=
                     {| ml_init := ml_init (mem_data m);
                       ml_data := ml_data (mem_data m) ++
                                          repeat (ml_init (mem_data m)) (S size)
                     |} ;
                     mem_max_opt := mem_max_opt m
                   |})).
           done.
           apply map_eq.
           intros.
           destruct i.
           unfold gmap_of_memory.
           rewrite gmap_of_list_2d_lookup. 
           rewrite list_lookup_fmap.
           unfold memory_to_list.
           destruct (decide (N.to_nat n = k)) ; subst.
           ++ unfold update_list_at at 1 => //=.
              rewrite list_lookup_middle => //=.
              destruct (decide (n1 = (mem_length m + N.of_nat size)%N)) ; subst.
              ** rewrite N2Nat.id.
                 rewrite lookup_insert.
                 rewrite lookup_app_r.
                 unfold mem_length, memory_list.mem_length.
                 replace (N.to_nat (N.of_nat (length (ml_data (mem_data m))) +
                                      N.of_nat size) -
                         length (ml_data (mem_data m))) with size ; last lia.
                 rewrite repeat_cons.
                 rewrite lookup_app_r ; last by rewrite repeat_length.
                 rewrite repeat_length.
                 rewrite PeanoNat.Nat.sub_diag => //=.
                 unfold mem_length, memory_list.mem_length ; lia.
              ** rewrite lookup_insert_ne ; last by intro H ; inversion H ; apply n2.
                 rewrite gmap_of_list_2d_lookup.
                 rewrite list_lookup_fmap.
                 unfold update_list_at => //=.
                 rewrite (list_lookup_middle _ _ _ (N.to_nat n)) => //=.
                 rewrite repeat_cons.
                 rewrite catA.
                 destruct (decide (n1 < (mem_length m + N.of_nat size))%N).
                 rewrite lookup_app_l => //=.
                 rewrite app_length repeat_length.
                 unfold mem_length, memory_list.mem_length in l.
                 lia.
                 rewrite lookup_ge_None_2. 
                 rewrite lookup_ge_None_2 => //=.
                 rewrite app_length repeat_length.
                 unfold mem_length, memory_list.mem_length in n3.
                 lia.
                 repeat rewrite app_length => //=.
                 rewrite repeat_length.
                 unfold mem_length, memory_list.mem_length in n3.
                 unfold mem_length, memory_list.mem_length in n2.
                 lia.
           ++ rewrite lookup_insert_ne ; last by intros H ; inversion H ; lia.
              rewrite gmap_of_list_2d_lookup.
              rewrite list_lookup_fmap.
              rewrite update_ne => //=. 
              rewrite update_ne => //=.
        -- replace (S size) with (size + 1) ; last lia.
           rewrite repeat_app.
           unfold mem_block_at_pos.
           iApply big_opL_app.
           iSplitL "Hm" => //=.
           iSplitL => //=.
           rewrite repeat_length.
           rewrite Nat2N.inj_add.
           rewrite N2Nat.id.
           done.
  - remember (N.to_nat (n * page_size)) as size.
    inversion Hgrow.
    clear Heqsize n Hgrow.
    remember None as sn.
    clear Heqsn.
    subst mems' m' sn.
    iInduction size as [|size] "IH".
    + simpl.
      rewrite cats0.
      rewrite update_trivial.
      unfold mem_block_at_pos => //=.
      by iSplitL.
      rewrite Hmems.
      destruct m. by destruct mem_data => //=.
    + iMod ("IH" with "Hmems") as "[Hmems Hm]".
      iMod (gen_heap_alloc with "Hmems") as "( Hmems & Hown & Htk )".
      * unfold gmap_of_memory.
        instantiate (1 := (N.of_nat k, (mem_length m + N.of_nat(size))%N)).
        rewrite gmap_of_list_2d_lookup => //=.
        rewrite Nat2N.id.
        rewrite list_lookup_fmap => //=.
        unfold update_list_at => //=.
        rewrite list_lookup_middle => //=.
        unfold memory_to_list => //=.
        rewrite lookup_app_r.
        rewrite lookup_ge_None => //=.
        rewrite repeat_length.
        unfold mem_length, memory_list.mem_length.
        lia.
        unfold mem_length, memory_list.mem_length.
        lia.
      * iModIntro. 
        iSplitL "Hmems".
        -- instantiate (1 := ml_init (mem_data m)).
           replace (<[ _ := _ ]> (gmap_of_memory _)) with
             (gmap_of_memory
                (update_list_at
                   mems k
                   {| mem_data :=
                     {| ml_init := ml_init (mem_data m);
                       ml_data := ml_data (mem_data m) ++
                                          repeat (ml_init (mem_data m)) (S size)
                     |} ;
                     mem_max_opt := mem_max_opt m
                   |})).
           done.
           apply map_eq.
           intros.
           destruct i.
           unfold gmap_of_memory.
           rewrite gmap_of_list_2d_lookup. 
           rewrite list_lookup_fmap.
           unfold memory_to_list.
           destruct (decide (N.to_nat n = k)) ; subst.
           ++ unfold update_list_at at 1 => //=.
              rewrite list_lookup_middle => //=.
              destruct (decide (n0 = (mem_length m + N.of_nat size)%N)) ; subst.
              ** rewrite N2Nat.id.
                 rewrite lookup_insert.
                 rewrite lookup_app_r.
                 unfold mem_length, memory_list.mem_length.
                 replace (N.to_nat (N.of_nat (length (ml_data (mem_data m))) +
                                      N.of_nat size) -
                         length (ml_data (mem_data m))) with size ; last lia.
                 rewrite repeat_cons.
                 rewrite lookup_app_r ; last by rewrite repeat_length.
                 rewrite repeat_length.
                 rewrite PeanoNat.Nat.sub_diag => //=.
                 unfold mem_length, memory_list.mem_length ; lia.
              ** rewrite lookup_insert_ne ; last by intro H ; inversion H ; apply n1.
                 rewrite gmap_of_list_2d_lookup.
                 rewrite list_lookup_fmap.
                 unfold update_list_at => //=.
                 rewrite (list_lookup_middle _ _ _ (N.to_nat n)) => //=.
                 rewrite repeat_cons.
                 rewrite catA.
                 destruct (decide (n0 < (mem_length m + N.of_nat size))%N).
                 rewrite lookup_app_l => //=.
                 rewrite app_length repeat_length.
                 unfold mem_length, memory_list.mem_length in l.
                 lia.
                 rewrite lookup_ge_None_2. 
                 rewrite lookup_ge_None_2 => //=.
                 rewrite app_length repeat_length.
                 unfold mem_length, memory_list.mem_length in n2.
                 lia.
                 repeat rewrite app_length => //=.
                 rewrite repeat_length.
                 unfold mem_length, memory_list.mem_length in n2.
                 unfold mem_length, memory_list.mem_length in n1.
                 lia.
           ++ rewrite lookup_insert_ne ; last by intros H ; inversion H ; lia.
              rewrite gmap_of_list_2d_lookup.
              rewrite list_lookup_fmap.
              rewrite update_ne => //=. 
              rewrite update_ne => //=.
        -- replace (S size) with (size + 1) ; last lia.
           rewrite repeat_app.
           unfold mem_block_at_pos.
           iApply big_opL_app.
           iSplitL "Hm" => //=.
           iSplitL => //=.
           rewrite repeat_length.
           rewrite Nat2N.inj_add.
           rewrite N2Nat.id.
           done.
Qed.


  
 
Lemma wp_grow_memory (s: stuckness) (E: coPset) (k: nat) (f0 : frame)
      (n: N) (Φ Ψ : iris.val -> iProp Σ) (c: i32) :
  f0.(f_inst).(inst_memory) !! 0 = Some k ->
  ( ↪[frame] f0 ∗
     (N.of_nat k) ↦[wmlength] n ∗
     Φ (immV [VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (n `div` page_size)%N))]) ∗
     Ψ (immV [VAL_int32 int32_minus_one]))
    ⊢ WP [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_grow_memory)]
    @ s; E {{ w, ((Φ w ∗
                    (∃ b, (N.of_nat k) ↦[wms][ n ]
                    repeat b (N.to_nat (Wasm_int.N_of_uint i32m c * page_size))) ∗
                    (N.of_nat k) ↦[wmlength]
                    (n + Wasm_int.N_of_uint i32m c * page_size)%N)
                 ∨ (Ψ w ∗ (N.of_nat k) ↦[wmlength] n)) ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hfm) "(Hframe & Hmemlength & HΦ & HΨ)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[ hs ws ] locs ] winst].
  iDestruct "Hσ" as "(? & ? & Hm & ? & Hf & Hγ)".
  iDestruct (ghost_map_lookup with "Hf Hframe") as "%Hframe".
  iDestruct (gen_heap_valid with "Hγ Hmemlength") as "%Hmemlength".
  rewrite lookup_insert in Hframe.
  inversion Hframe ; subst ; clear Hframe.
  rewrite - nth_error_lookup in Hfm.
  rewrite gmap_of_list_lookup list_lookup_fmap Nat2N.id in Hmemlength => /=.
  destruct (s_mems ws !! k) eqn:Hmemlookup => //.
  simpl in Hmemlength.
  inversion Hmemlength as [Hmemlength']; clear Hmemlength.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    eexists _,_,(_,_,_,_),_.
    repeat split => //=.
    eapply r_grow_memory_failure => //=.
    by rewrite nth_error_lookup.
  - iIntros "!>" (es σ2 efs HStep). 
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    remember [AI_basic (BI_const (VAL_int32 c)) ; AI_basic BI_grow_memory] as es0.
    remember {| f_locs := locs ; f_inst := winst |} as f.
    remember {| f_locs := locs' ; f_inst := inst' |} as f'.
    replace [AI_basic (BI_const (VAL_int32 c)) ; AI_basic BI_grow_memory] with
      ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic BI_grow_memory]) in Heqes0 => //=.
    induction H ; try by inversion Heqes0 ;
      try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
    { destruct H ; try by inversion Heqes0 ;
        try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
      rewrite Heqes0 in H0.
      filled_trap H0 Hxl1. }
    { (* grow_memory succeeded *)
      (* iExists f. *)
      inversion Heqes0 ; subst c0 ; clear Heqes0.
      unfold smem_ind in H.
      destruct (inst_memory (f_inst f)) ; try by inversion Hfm.
      simpl in Hfm.
      inversion Hfm ; subst m1 ; clear Hfm.
      inversion H ; subst i ; clear H.
      rewrite nth_error_lookup in H0.
      rewrite Hmemlookup in H0.
      inversion H0 ; subst m0 ; clear H0.
      unfold mem_size in H1.
      rewrite Hmemlength' in H1.
      unfold upd_s_mem => //=.
      iMod (gen_heap_update with "Hγ Hmemlength") as "[Hγ Hmemlength]".
      iMod (gen_heap_alloc_grow with "Hm") as "[Hm Hown]" => //=.
      iIntros "!>".
      iFrame.
      iSplitL "Hγ".
      - rewrite - gmap_of_list_insert.
        rewrite Nat2N.id.
        instantiate (1:= mem_length mem').
        rewrite - list_fmap_insert.
        rewrite update_list_at_insert.
        done.
        by apply lookup_lt_Some in Hmemlookup.
        rewrite Nat2N.id.
        rewrite fmap_length.
        by apply lookup_lt_Some in Hmemlookup.
      - (* iSplitL => //=. *)
        (* iIntros "Hframe". *)
        iLeft.
        rewrite Hmemlength' H1.
        erewrite mem_grow_length => //=.
        rewrite Hmemlength'.
        replace (Wasm_int.N_of_uint i32m c) with (Z.to_N (Wasm_int.Int32.unsigned c)) ;
          last done.
        iFrame.
        by iExists _. }
    { (* grow_memory failed *)
      iSplitR "Hframe HΨ Hmemlength"  => //.
      iFrame.
      done.
      iFrame.
      iRight.
      iFrame. done. }
    rewrite Heqes0 in H0.
    simple_filled H0 k0 lh bef aft nn ll ll'.
    destruct bef.
    { destruct es ; first by exfalso ; eapply empty_no_reduce.
      inversion H0.
      apply Logic.eq_sym, app_eq_unit in H4 as [[ -> _ ] | [-> ->]].
      by subst ; exfalso ; eapply values_no_reduce.
      subst.
      unfold lfilled, lfill in H1.
      simpl in H1.
      rewrite app_nil_r in H1.
      move/eqP in H1 ; subst.
      apply IHreduce => //=. }
    exfalso.
    inversion H0.
    apply Logic.eq_sym, app_eq_unit in H4 as [[ _ Hes ] | [ _ Hes]].
    apply app_eq_unit in Hes as [[ -> _ ] | [Hes _ ]].
    by eapply empty_no_reduce.
    rewrite <- app_nil_l in Hes.
    clear IHreduce H1 Heqes0 H0.
    induction H ; try by inversion Hes ; try by apply app_inj_tail in Hes as [_ Habs] ;
      inversion Habs.
    { destruct H ; try by inversion Hes ; try by apply app_inj_tail in Hes as [_ Habs] ;
        inversion Habs.
      rewrite Hes in H0 ; filled_trap H0 Hxl1. }
    rewrite Hes in H0.
    simple_filled H0 k0 lh bef0 aft0 nnn lll lll'.
    apply Logic.eq_sym, app_eq_unit in H0 as [[ -> H0 ] | [_ H0]].
    apply app_eq_unit in H0 as [[ -> _ ] | [ -> -> ]].
    by eapply empty_no_reduce.
    apply IHreduce => //=.
    apply app_eq_nil in H0 as [ -> _].
    by eapply empty_no_reduce.
    apply app_eq_nil in Hes as [-> _].
    by eapply empty_no_reduce.
Qed.
      
End iris_rules_resources.
