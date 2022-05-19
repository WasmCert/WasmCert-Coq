From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris iris_locations iris_properties iris_atomicity iris_wp_def stdpp_aux.
Require Export datatypes host operations properties opsem.


Close Scope byte_scope.

(* basic instructions with simple(pure) reductions *)
Section iris_rules_pure.

Context `{!wasmG Σ}.

(* numerics *)
Lemma wp_unop (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v v' : value) (t: value_type) (op: unop) f0:
  app_unop op v = v' ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [v']) -∗
  WP [AI_basic (BI_const v); AI_basic (BI_unop t op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hunop) "Hf HΦ".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[[ hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. apply r_simple. rewrite <- Hunop. apply rs_unop.
  - destruct σ as [[[hs ws] locs] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'].
    destruct HStep as (H & -> & ->).
    only_one_reduction H. iFrame.
Qed.
 
Lemma wp_binop (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v1 v2 v : value) (t: value_type) (op: binop) f0:
  app_binop op v1 v2 = Some v ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [v]) -∗
  WP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hbinop) "Hf HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v)], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_binop_success.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H. iFrame.
Qed.
                                                                  

Lemma wp_binop_failure (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v1 v2 : value) (t: value_type) (op: binop) f0:
  app_binop op v1 v2 = None ->
  ▷ Φ trapV -∗
  ↪[frame] f0 -∗
  WP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hbinop) "Hf HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_trap], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_binop_failure.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H. iFrame.
Qed.
    
Lemma wp_relop (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v1 v2 : value) (b: bool) (t: value_type) (op: relop) f0:
  app_relop op v1 v2 = b ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [(VAL_int32 (wasm_bool b))]) -∗
  WP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hrelop) "Hf HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (wasm_bool b)))], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_relop.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H. iFrame.
Qed.

Lemma wp_testop_i32 (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v : i32) (b: bool) (op: testop) f0:
  app_testop_i (e:=i32t) op v = b ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [(VAL_int32 (wasm_bool b))]) -∗
    WP [AI_basic (BI_const (VAL_int32 v)); AI_basic (BI_testop T_i32 op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Htestop) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (wasm_bool b)))], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_testop_i32.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H. iFrame.
Qed.

Lemma wp_testop_i64 (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v : i64) (b: bool) (op: testop) f0:
  app_testop_i (e:=i64t) op v = b ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [(VAL_int32 (wasm_bool b))]) -∗
    WP [AI_basic (BI_const (VAL_int64 v)); AI_basic (BI_testop T_i64 op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Htestop) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (wasm_bool b)))], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_testop_i64.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H. iFrame.
Qed.

Lemma wp_cvtop_convert (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v v': value) (t1 t2: value_type) (sx: option sx) f0:
  cvt t2 sx v = Some v' ->
  types_agree t1 v ->
  ↪[frame] f0 -∗
  ▷Φ (immV [v']) -∗
    WP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hcvtop Htype) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_convert_success.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H. iFrame.
Qed.

Lemma wp_cvtop_convert_failure (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v : value) (t1 t2: value_type) (sx: option sx) f0:
  cvt t2 sx v = None ->
  types_agree t1 v ->
  ↪[frame] f0 -∗
  ▷Φ (trapV) -∗
    WP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hcvtop Htypes) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_trap], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_convert_failure.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H. iFrame.
Qed.

Lemma wp_cvtop_reinterpret (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v v': value) (t1 t2: value_type) f0:
  wasm_deserialise (bits v) t2 = v' ->
  types_agree t1 v ->
  ↪[frame] f0 -∗
  ▷Φ (immV [v']) -∗
    WP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hcvtop Htype) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_reinterpret.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H. iFrame.
Qed.

(* Non-numerics -- stack operations, control flows *)

Lemma wp_unreachable (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) f0 :
  ↪[frame] f0 -∗
  ▷Φ (trapV) -∗
  WP [AI_basic BI_unreachable] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_trap], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_unreachable.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H. iFrame.
Qed.

Lemma wp_nop (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) f0:
  ↪[frame] f0 -∗
  ▷Φ (immV []) -∗
    WP [AI_basic (BI_nop)] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_nop.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H. iFrame.
Qed.

Lemma wp_drop (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) v f0 :
  ↪[frame] f0 -∗
  ▷Φ (immV []) -∗
    WP [AI_basic (BI_const v) ; AI_basic BI_drop] @ s; E {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf0 HΦ".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [], σ, [].
    destruct σ as [[[ hs ws ] locs ] inst ].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple ; apply rs_drop.
  - destruct σ as [[[ hs ws ] locs ] inst ].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[ hs' ws' ] locs' ] inst'].
    destruct HStep as (H & -> & ->).
    only_one_reduction H. iFrame.
Qed.

Lemma wp_select_false (s: stuckness) (E :coPset) (Φ : iris.val -> iProp Σ) n v1 v2 f0 :
  n = Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷Φ (immV [v2]) -∗ WP [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                      AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_select) ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hn) "Hf0 HΦ".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v2)], σ, [].
    destruct σ as [[[ hs ws ] locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply r_simple ; by apply rs_select_false.
  - destruct σ as [[[ hs ws ] locs ] inst ].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[ hs' ws' ] locs' ] inst'].
    destruct HStep as (H & -> & ->).
    only_one_reduction H. iFrame.
Qed.

Lemma wp_select_true (s: stuckness) (E : coPset) (Φ: iris.val -> iProp Σ) n v1 v2 f0 :
  n <> Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷Φ (immV [v1]) -∗ WP [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                      AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_select) ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hn) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v1)], σ, [].
    destruct σ as [[[ hs ws ] locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply r_simple ; by apply rs_select_true.
  - destruct σ as [[[ hs ws ] locs ] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[ hs' ws' ] locs' ] inst'].
    destruct HStep as (H & -> & ->).
    only_one_reduction H. iFrame.
Qed.
    
End iris_rules_pure.
