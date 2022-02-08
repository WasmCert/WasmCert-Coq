
From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules_structural iris_rules_pure iris_rules_control iris_rules_resources iris_rules_calls.
Require Export datatypes host operations properties opsem.

Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

Close Scope byte_scope.

Lemma wp_ctx_frame_return (s: stuckness) (E: coPset) (Φ: val -> iProp Σ) vs vs0 n f0 f i lh :
  iris.to_val vs = Some (immV vs0) ->
  length vs = n ->
  ( WP vs @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}
  ⊢ WP vs ++ [AI_basic BI_return] @ s; E FRAME n ; f CTX i ; lh {{ v, Φ v ∗ ↪[frame] f0 }}).
Proof.
  iIntros (Hval Hlen) "HΦ".
  iIntros (LI HLI).
  iApply wp_return;eauto.
Qed.
