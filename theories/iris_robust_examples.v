From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_rules iris_fundamental iris_wp iris_interp_instance_alloc.
Require Export datatypes host operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }}) (at level 50).

Ltac take_drop_app_rewrite n :=
  match goal with
  | |- context [ WP ?e @ _; _ CTX _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ WP ?e @ _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ WP ?e @ _; _ FRAME _; _ CTX _; _  {{ _, _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ WP ?e @ _; _ FRAME _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  end.
  
Ltac take_drop_app_rewrite_twice n m :=
  take_drop_app_rewrite n;
  match goal with
  | |- context [ WP _ ++ ?e @ _; _ CTX _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop (length e - m) e);simpl take; simpl drop
  | |- context [ WP _ ++ ?e @ _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop (length e - m) e);simpl take; simpl drop
  end.

Import DummyHosts.

(* Example Programs *)
Section Examples.

  Import DummyHost.

  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ, !wtablimitG Σ, !wmemlimitG Σ,
        !logrel_na_invs Σ, HWP:host_program_logic}.

  Definition xx i := (VAL_int32 (Wasm_int.int_of_Z i32m i)).
  Definition xb b := (VAL_int32 (wasm_bool b)).

  Lemma wp_seq_can_trap_same_ctx (Φ Ψ : iris.val -> iProp Σ) (s : stuckness) (E : coPset) (es1 es2 : language.expr wasm_lang) f i lh :
    (¬ (Ψ trapV)) ∗ (Φ trapV) ∗ ↪[frame] f ∗
    (↪[frame] f -∗ WP es1 @ NotStuck; E {{ w, (⌜w = trapV⌝ ∨ Ψ w) ∗ ↪[frame] f }}) ∗
    (∀ w, Ψ w ∗ ↪[frame] f -∗ WP (iris.of_val w ++ es2) @ s; E CTX i; lh {{ v, Φ v ∗ ↪[frame] f }})%I
    ⊢ WP (es1 ++ es2) @ s; E CTX i; lh {{ v, Φ v ∗ ↪[frame] f }}.
  Proof.
    iIntros "(HPsi & Hphi & Hf & Hes1 & Hes2)".
    iApply (wp_wand_ctx _ _ _ (λ  v, Φ v ∗ ∃ f0, ↪[frame] f0 ∗ ⌜f0 = f⌝) with "[-]")%I;cycle 1.
    { iIntros (v) "[$ Hv]". iDestruct "Hv" as (f0) "[Hv ->]". iFrame. }
    iApply wp_seq_can_trap_ctx.
    iFrame. iSplitL "Hes1".
    { iIntros "Hf". iDestruct ("Hes1" with "Hf") as "Hes1".
      iApply (wp_wand with "Hes1").
      iIntros (v) "[$ Hv]". iExists _. iFrame. eauto. }
    { iIntros (w f') "[H [Hf ->]]".
      iDestruct ("Hes2" with "[$]") as "Hes2".
      iApply (wp_wand_ctx with "Hes2").
      iIntros (v) "[$ Hv]". iExists _. iFrame. eauto. }
  Qed.

  Lemma wp_seq_can_trap_same_empty_ctx (Φ Ψ : iris.val -> iProp Σ) (s : stuckness) (E : coPset) (es1 es2 : language.expr wasm_lang) f :
    (¬ (Ψ trapV)) ∗ (Φ trapV) ∗ ↪[frame] f ∗
    (↪[frame] f -∗ WP es1 @ NotStuck; E {{ w, (⌜w = trapV⌝ ∨ Ψ w) ∗ ↪[frame] f }}) ∗
    (∀ w, Ψ w ∗ ↪[frame] f -∗ WP (iris.of_val w ++ es2) @ s; E {{ v, Φ v ∗ ↪[frame] f }})%I
    ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v ∗ ↪[frame] f }}.
  Proof.
    iIntros "(HPsi & Hphi & Hf & Hes1 & Hes2)".
    iApply wp_wasm_empty_ctx.
    iApply wp_seq_can_trap_same_ctx.
    iFrame.
    iIntros (w) "?".
    iApply wp_wasm_empty_ctx.
    iApply "Hes2". done.
  Qed.

  Lemma wp_wand s E (e : iris.expr) (Φ Ψ : iris.val -> iProp Σ) :
    WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
  Proof. iApply (wp_wand). Qed.
  
  Definition lse a : iris.expr :=
    to_e_list
      [BI_const (xx 0);
       BI_const (xx 42);
       BI_store T_i32 None 0%N 0%N] ++
      [AI_invoke a] ++
    to_e_list
    [BI_const (xx 0);
     BI_load T_i32 None 0%N 0%N].


  Lemma lse_spec f n a C i es :
    (tc_label C) = [] ∧ (tc_return C) = None ->
    f.(f_inst).(inst_memory) !! 0 = Some n ->
    be_typing (upd_local_label_return C [] [[]] (Some [])) es (Tf [] []) ->
    
    {{{ ↪[frame] f
         ∗ na_own logrel_nais ⊤
         ∗ na_inv logrel_nais (wfN (N.of_nat a)) ((N.of_nat a) ↦[wf] (FC_func_native i (Tf [] []) [] es))
         ∗ interp_instance (HWP:=HWP) C i
         ∗ ∃ c, (N.of_nat n) ↦[wms][ 0%N ] (bits (VAL_int32 c)) }}}
      lse a
      {{{ w, (⌜w = trapV⌝ ∨ ⌜w = immV [xx 42]⌝
                                      ∗ (N.of_nat n) ↦[wms][ 0%N ] (bits (xx 42))
                                      ∗ na_own logrel_nais ⊤)
               ∗ ↪[frame] f }}}.
  Proof.
    iIntros (Hc Hn Hes Φ) "(Hf & Hown & #Ha & #Hi & Hn) HΦ".
    iDestruct "Hn" as (c) "Hn".
    iApply (wp_wand with "[-HΦ] HΦ").

    unfold lse. simpl.

    take_drop_app_rewrite 3.
    iApply (wp_seq _ _ _ (λ w, (⌜w = immV []⌝ ∗ N.of_nat n↦[wms][0] bits (xx 42)) ∗ ↪[frame] f)%I).
    iSplitR;[by iIntros "[[%Hcontr _] _]"|].
    iSplitR "Hown".
    { unfold serialise_i32. simpl. iApply (wp_store (λ w, ⌜w = immV ([])⌝)%I with "[$Hf Hn]");eauto.
      by rewrite Memdata.encode_int_length. }
    iIntros (w) "[[-> Hn] Hf]". iSimpl.

    take_drop_app_rewrite_twice 0 2.
    iApply wp_wasm_empty_ctx.
    iApply wp_base_push;auto.
    rewrite -(app_nil_r [_]).
    iApply (wp_seq_can_trap_same_ctx _ (λ v, interp_values [] v ∗ na_own logrel_nais ⊤)%I).
    iSplitR;[by iIntros "[H _]";iDestruct "H" as (v) "[%Hcontr _]"|].
    iSplitR;[auto|].
    iFrame.
    iSplitL "Hown".
    { iIntros "Hf". iApply fupd_wp.
      iMod (na_inv_acc with "Ha Hown") as "(>Haf & Hown & Hcls)";[solve_ndisj..|].
      rewrite -(app_nil_l [_]).
      iApply (wp_invoke_native with "Hf Haf");eauto.
      iModIntro. iNext. iIntros "[Hf Haf]".
      rewrite -wp_frame_rewrite.
      iApply wp_wasm_empty_ctx_frame.
      take_drop_app_rewrite 0.
      iApply (wp_block_local_ctx with "Hf");[eauto..|].
      iNext. iIntros "Hf".
      iApply wp_wasm_empty_ctx_frame.
      rewrite wp_frame_rewrite.
      
      iApply fupd_wp.
      iMod ("Hcls" with "[$]") as "Hown". iModIntro.
      simpl.

      iDestruct (be_fundamental_local _ _ [] _ [] with "Hi") as "Hl";eauto.
      iSpecialize ("Hl" $! _ [] with "Hf Hown []").
      { iRight. iExists _. iSplit;eauto. }
      unfold interp_expression_closure. simpl.
      iApply (wp_wand with "Hl").
      iIntros (v) "[[[H|H] Hown] HH]";iFrame. iRight;auto.
    }

    iIntros (w) "[[#Hval Hown] Hf]".
    iApply wp_base_pull. iApply wp_wasm_empty_ctx.
    iDestruct "Hval" as (ws) "[-> Heq]".
    iDestruct (big_sepL2_length with "Heq") as %Heq. destruct ws;[|done].
    iSimpl.

    iApply (wp_wand _ _ _ (λ vs, (⌜vs = immV _⌝ ∗ _) ∗ _)%I with "[Hn Hf]").
    { iApply wp_load;eauto;[|iFrame];eauto. }

    iIntros (v) "[[-> Hn] Hf]". iFrame.
    iRight. iFrame. auto.
  Qed.

End Examples.
