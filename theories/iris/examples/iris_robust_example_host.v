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
  (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).

Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).

Notation " n ↦[ha]{ q } f" := (ghost_map_elem (V := host_action) haGName n q f%V)
                                (at level 20, q at level 5, format " n ↦[ha]{ q } f") .
Notation " n ↦[ha] f" := (ghost_map_elem (V := host_action) haGName n (DfracOwn 1) f%V)
                           (at level 20, format " n ↦[ha] f") .

Notation " n ↪[vis]{ q } v" := (ghost_map_elem (V := module_export) visGName n q v%V)
                           (at level 20, q at level 5, format " n ↪[vis]{ q } v") .
Notation " n ↪[vis] v" := (ghost_map_elem (V := module_export) visGName n (DfracOwn 1) v%V)
                          (at level 20, format " n ↪[vis] v").

Notation " n ↪[mods]{ q } v" := (ghost_map_elem (V := module) msGName n q v%V)
                           (at level 20, q at level 5, format " n ↪[mods]{ q } v") .
Notation " n ↪[mods] v" := (ghost_map_elem (V := module) msGName n (DfracOwn 1) v%V)
                            (at level 20, format " n ↪[mods] v").


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



(* Example Programs *)
Section Host_instance.
  Context `{!wasmG Σ, !logrel_na_invs Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}.

  Global Program Instance host_wp : host_program_logic Σ :=
    { host_function := host_expr ;
      result := host_val;
      host_ctx := list inst_decl;
      fill_host := λ decls es, (decls,es);
      val_of_host_val := iris_host.val_of_host_val;
      wp_host := λ (s : stuckness), (λ (E : coPset) (he : host_expr) (Φ : host_val -d> iPropO Σ), (WP he @ s; E {{ Φ }})%I);
      wp_host_bind := _;
      wp_host_wand := _;
      fupd_wp_host := _;
      wp_fupd_host := _
    }.
  Next Obligation. simpl. iIntros (decls es Φ) "Hwp". iApply wp_lift_wasm. iFrame. Defined.
  Next Obligation. iIntros (es Φ Ψ) "Hwp Hwand". iApply (wp_wand with "Hwp Hwand"). Defined.
  Next Obligation. simpl. iIntros (e Φ) "Hwp". iApply weakestpre.fupd_wp. iFrame. Defined.
  Next Obligation. simpl. iIntros (e Φ) "Hwp". iApply weakestpre.wp_fupd. iFrame. Defined.
  
End Host_instance.

Section Host_robust_example.
  Context `{!wasmG Σ, !logrel_na_invs Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}.

  Definition lse_log_expr f log :=
    [BI_const (xx 42);
     BI_set_local 0;
     BI_call f;
     BI_get_local 0;
     BI_call log].

  Definition lse_log f log :=
    to_e_list (lse_log_expr f log).

  Definition log : string := "logN".
  Definition logN : namespace := nroot .@ log.

  Lemma lse_log_return_value f log log_func h w inst :
    (inst_funcs inst) !! log = Some log_func ->

    na_inv logrel_nais logN (N.of_nat h↦[ha]HA_print) -∗
    interp_values [] w -∗

    na_inv logrel_nais (wfN (N.of_nat log_func)) (N.of_nat log_func↦[wf]FC_func_host (Tf [T_i32] []) (Mk_hostfuncidx h)) -∗
    na_own logrel_nais ⊤ -∗
    ↪[frame] {| f_locs := [xx 42]; f_inst := inst |} -∗

    WP iris.of_val w
    CTX
    0; LH_base [] [AI_basic (BI_get_local 0); AI_basic (BI_call log)]
    {{ v, WP (iris.of_val v) CTX 1; LH_rec [] 0 [] (LH_base [] []) []
          {{ w0, ∃ f0,
                (↪[frame]f -∗
                  WP iris.of_val w0 @ NotStuck; ⊤ FRAME 0; f0
                  {{ w1, WP (([], iris.of_val w1) : host_expr)
                             {{ w2, (⌜w2 = trapHV⌝ ∨ ⌜w2 = immHV []⌝ ∗ na_own logrel_nais ⊤) ∗
                                                   ↪[frame]f }} }}) ∗  ↪[frame]f0 }} }}.
  Proof.
    iIntros (Hlog) "#Hh Hv #Hl Hown Hf".
    iDestruct "Hv" as (ws) "[-> #Hws]".
    iDestruct (big_sepL2_length with "Hws") as %Hlen. destruct ws;[|done].
    iApply wp_base_pull. iApply wp_wasm_empty_ctx.
    iSimpl.
    
    take_drop_app_rewrite 1.
    iApply (wp_seq _ _ _ (λ vs, ⌜vs = immV [xx 42]⌝ ∗ ↪[frame] _)%I).
    iSplitR;[by iIntros "[%Hcontr _]"|].
    iSplitL "Hf".
    { iApply (wp_get_local with "Hf");[|done]. simpl. auto. }
    iIntros (w) "[-> Hf]". iSimpl.

    take_drop_app_rewrite_twice 1 0.
    iApply wp_wasm_empty_ctx. iApply wp_base_push;auto.
    iApply (wp_call_ctx with "Hf");[simpl;eauto|].
    iNext. iIntros "Hf".
    iApply wp_base_pull. iApply wp_wasm_empty_ctx.
    iSimpl.

    take_drop_app_rewrite 1.
    iApply fupd_wp.
    iMod (na_inv_acc with "Hl Hown") as "(>Hlog & Hown & Hcls)";[solve_ndisj..|].
    iApply (wp_invoke_host with "Hlog Hf");[| |eauto|..].
    { instantiate (1:=[_]). cbn. constructor. }
    { simpl;auto. }
    iIntros "!>!> Hlog Hf".
    iApply fupd_wp. iMod ("Hcls" with "[$]") as "Hown". iModIntro.    
    assert ([AI_call_host (Tf [T_i32] []) (Mk_hostfuncidx h) [xx 42]]
            = iris.of_val (callHostV (Tf [T_i32] []) (Mk_hostfuncidx h) [xx 42] (LL_base [][]))) as ->.
    { simpl. auto. }
    iApply wp_value;[done|].
    (* iSimpl. *)

    eassert (LH_rec [] 0 [] (LH_base [] []) [] = push_base (LH_base [] []) _ _ _ _) as ->.
    { simpl. eauto. }
    iApply wp_label_push_nil_inv. iApply wp_wasm_empty_ctx.
    rewrite llfill_label.
    rewrite -/(iris.of_val (callHostV _ _ _ _)).
    iApply wp_value;[done|].
    iExists _. iFrame. iIntros "Hf".
    rewrite wp_frame_rewrite.
    rewrite llfill_local.
    rewrite -/(iris.of_val (callHostV _ _ _ _)).
    iApply wp_value;[done|].
    
    iApply weakestpre.fupd_wp. iMod (na_inv_acc with "Hh Hown") as "(>HL & Hown & Hcls)";[solve_ndisj..|].
    iApply (wp_call_host_action_no_state_change with "[$HL Hown Hcls Hf]");[eauto|..].
    { constructor. }
    { instantiate (2:=[]); simpl;auto. }
    { intros s' f'. constructor. }
    iNext. iIntros "HL".
    iApply weakestpre.fupd_wp. iMod ("Hcls" with "[$]") as "Hown". iModIntro.

    iApply wp_lift_wasm.
    rewrite -wp_frame_rewrite. iApply (wp_frame_bind with "Hf");auto.
    iIntros "Hf".
    iApply (wp_wand _ _ _ (λ v, ⌜v = immV []⌝ ∗ ↪[frame] _)%I with "[Hf]").
    { iApply (wp_label_value with "Hf");eauto. }
    iIntros (v) "[-> Hf]". iExists _. iFrame. iIntros "Hf".
    iApply (wp_wand _ _ _ (λ v, ⌜v = immV []⌝ ∗ ↪[frame] _)%I with "[Hf]").
    { iApply (wp_frame_value with "Hf");eauto. }
    iIntros (v) "[-> Hf]".
    
    iApply iris_host.wp_value;[done|]. iFrame. iRight;auto.
  Qed.

  Lemma llholed_basic_sh_append vh e :
    is_basic_expr e ->
    llholed_basic vh ->
    llholed_basic (llh_append vh e).
  Proof.
    induction vh;simpl;intros;auto.
    { apply iris_fundamental_composition.is_basic_app;auto. }
    { destruct H0 as [? ?]. split;auto.
      apply iris_fundamental_composition.is_basic_app;auto. }
    { destruct H0 as [? ?]. split;auto.
      apply iris_fundamental_composition.is_basic_app;auto. }
  Qed.

  Lemma lse_log_return_call_host f log log_func h w inst :
    (inst_funcs inst) !! log = Some log_func ->

    na_inv logrel_nais logN (N.of_nat h↦[ha]HA_print) -∗
    ▷ interp_call_host_cls [(Mk_hostfuncidx h, Tf [T_i32] [])] [] w -∗

    na_inv logrel_nais (wfN (N.of_nat log_func)) (N.of_nat log_func↦[wf]FC_func_host (Tf [T_i32] []) (Mk_hostfuncidx h)) -∗
    na_own logrel_nais ⊤ -∗
    ↪[frame] {| f_locs := [xx 42]; f_inst := inst |} -∗

    WP iris.of_val w
    CTX
    0; LH_base [] [AI_basic (BI_get_local 0); AI_basic (BI_call log)]
    {{ v, WP (iris.of_val v) CTX 1; LH_rec [] 0 [] (LH_base [] []) []
          {{ w0, ∃ f0,
                (↪[frame]f -∗
                  WP iris.of_val w0 @ NotStuck; ⊤ FRAME 0; f0
                  {{ w1, WP (([], iris.of_val w1) : host_expr)
                             {{ w2, (⌜w2 = trapHV⌝ ∨ ⌜w2 = immHV []⌝ ∗ na_own logrel_nais ⊤) ∗
                                                   ↪[frame]f }} }}) ∗  ↪[frame]f0 }} }}.
  Proof.
    iIntros (Hlog) "#Hh Hv #Hlog Hown Hf".
    iLöb as "IH"
  forall (w).
    
    rewrite fixpoint_interp_call_host_cls_eq.
    iDestruct "Hv" as (? ? ? ? ? ?) "(>%Heq & >%Htf & >%Hin & >%Hbasic & >#Hw & #Hcont)".
    apply elem_of_list_singleton in Hin. inversion Hin;subst.
    inversion H1;subst.

    iApply wp_base_pull. iApply wp_wasm_empty_ctx.
    iSimpl.
    assert (llfill vh [AI_call_host (Tf [T_i32] []) (Mk_hostfuncidx h) v] ++
                   [AI_basic (BI_get_local 0); AI_basic (BI_call log)]
            = llfill (LL_base [] [AI_basic (BI_get_local 0); AI_basic (BI_call log)])
                     (llfill vh [AI_call_host (Tf [T_i32] []) (Mk_hostfuncidx h) v]) ) as ->;[simpl;auto|].
    rewrite -iris_fundamental_composition.llfill_sh_append.
    rewrite -/(iris.of_val (callHostV _ _ _ _)).
    iApply wp_value;[done|].
    iSimpl.

    iDestruct "Hw" as "[%Hcontr|Hv]";[done|].
    iDestruct "Hv" as (ws) "[%Heq Hv]". inversion Heq.
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|w ws];[done|destruct ws;[|done]]. subst v.
    iSimpl in "Hv". iDestruct "Hv" as "[Hv _]".
    iDestruct "Hv" as (z) "->".

    eassert (LH_rec [] 0 [] (LH_base [] []) [] = push_base (LH_base [] []) _ _ _ _) as ->.
    { simpl. eauto. }
    iApply wp_label_push_nil_inv. iApply wp_wasm_empty_ctx.
    rewrite llfill_label.
    rewrite -/(iris.of_val (callHostV _ _ _ _)).
    iApply wp_value;[done|].
    iExists _. iFrame. iIntros "Hf".
    rewrite wp_frame_rewrite.
    rewrite llfill_local.
    rewrite -/(iris.of_val (callHostV _ _ _ _)).
    iApply wp_value;[done|].

    iApply weakestpre.fupd_wp. iMod (na_inv_acc with "Hh Hown") as "(>HL & Hown & Hcls)";[solve_ndisj..|].
    iApply (wp_call_host_action_no_state_change with "[- $HL]");[eauto|..].
    { constructor. }
    { instantiate (2:=[]). simpl;eauto. }
    { intros s' f'. constructor. }
    iNext. iIntros "HL".
    iApply weakestpre.fupd_wp. iMod ("Hcls" with "[$]") as "Hown". iModIntro.

    iApply wp_lift_wasm.
    simpl llfill.

    rewrite -wp_frame_rewrite. iApply (wp_frame_bind with "Hf").
    { eassert (llfill _ [] = llfill _ (iris.of_val (immV []))) as ->;auto.
      apply to_val_immV_AI_local_is_basic_None.
      apply llholed_basic_sh_append;auto. cbn. done. }
    iIntros "Hf".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_ctx_bind;[simpl;auto|].
    rewrite iris_fundamental_composition.llfill_sh_append. simpl llfill.

    rewrite -(app_nil_l (llfill vh [])) -app_assoc.
    iApply wp_wasm_empty_ctx. iApply wp_base_push;[auto|].
    iSimpl. rewrite -(app_nil_r (llfill vh [])).

    iApply (wp_seq_can_trap_ctx).
    instantiate (1:=λ f', (⌜f' = {| f_locs := [xx 42]; f_inst := inst |}⌝)%I).
    instantiate (2:=λ vs,((interp_values [] vs
                           ∨ ▷ interp_call_host_cls
                               [(Mk_hostfuncidx h, Tf [T_i32] [])] [] vs) ∗
                  (* ↪[frame] {| f_locs := [xx 42]; f_inst := f_inst f |} ∗ *) na_own logrel_nais ⊤)%I).
    iSplitR.
    { rewrite fixpoint_interp_call_host_cls_eq.
      iIntros "[[H|H] _]";[by iDestruct "H" as (? ?) "_"|].
      by iDestruct "H" as (? ? ? ? ? ?) "[>%Hcontr _]". }
    iSplitR.
    { iIntros (f') "[Hf' ->]".
      eassert (LH_rec [] 0 [] (LH_base [] []) [] = push_base (LH_base [] []) _ _ _ _) as ->.
      { simpl. eauto. }
      iApply wp_label_push_nil_inv. iApply wp_wasm_empty_ctx.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗ ↪[frame] _)%I with "[Hf']").
      { iApply (wp_label_trap with "Hf'");eauto. }
      iIntros (v) "[-> Hf]". iExists _. iFrame.
      iIntros "Hf".
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗ ↪[frame] _)%I with "[Hf]").
      { iApply (wp_frame_trap with "Hf");eauto. }
      iIntros (v) "[-> Hf]".
      iApply iris_host.wp_value;eauto.
      iFrame. by iLeft. }
    iFrame "Hf". iSplitL "Hown".
    { iIntros "Hf". assert (llfill vh [] = llfill vh (iris.of_val (immV []))) as ->;[auto|].
      iDestruct ("Hcont" $! (immV []) with "[] Hf Hown") as "Hc".
      { iRight. iExists _. iSplit;eauto. }
      iApply (wp_wand with "Hc").
      iIntros (v) "[H [Hf Hown]]".
      iSplitR "Hf";[|iExists _;iFrame;auto].
      iDestruct "H" as "[[H|H]|H]";auto.
    }

    iIntros (w f0) "[[[Hv|Hv] Hown] [Hf ->]]".
    { rewrite app_nil_r.
      iApply (lse_log_return_value with "Hh Hv Hlog Hown Hf");auto. }
    { rewrite app_nil_r.
      iApply ("IH" with "Hv Hown Hf"). }
  Qed.    

    
  Lemma lse_log_spec C i f g g_func es locs log log_func h idnstart inst :
    
    (tc_label C) = [] ∧ (tc_return C) = None ->
    be_typing (upd_local_label_return C locs [[]] (Some [])) es (Tf [] []) ->
    (* (f_locs f) = [xx 0] -> *)
    (inst_funcs inst) !! g = Some g_func ->
    (inst_funcs inst) !! log = Some log_func -> 
    
    ⊢ {{{ ↪[frame] f
         ∗ na_own logrel_nais ⊤
         ∗ N.of_nat idnstart ↦[wf] FC_func_native inst (Tf [] []) [T_i32] (lse_log_expr g log)
         ∗ na_inv logrel_nais (wfN (N.of_nat g_func)) ((N.of_nat g_func) ↦[wf] (FC_func_native i (Tf [] []) locs es))
         ∗ interp_instance C [(Mk_hostfuncidx h, Tf [T_i32] [])] i
         ∗ na_inv logrel_nais logN ((N.of_nat h) ↦[ha] HA_print)
         ∗ na_inv logrel_nais (wfN (N.of_nat log_func))
         (N.of_nat log_func↦[wf]FC_func_host (Tf [T_i32] []) (Mk_hostfuncidx h)) }}}
      ([], [AI_invoke idnstart])
      {{{ w, (⌜w = trapHV⌝ ∨ (⌜w = immHV []⌝ ∗ na_own logrel_nais ⊤))
               ∗ ↪[frame] f }}}.
  Proof.
    iIntros (HC Htyp Hg Hlog).
    iModIntro. iIntros (Φ) "(Hf & Hown & Hidnstart & #Hadv & #Hi & #Hh & #Hlog) HΦ".
    iApply (weakestpre.wp_wand with "[-HΦ] HΦ").
    iApply wp_lift_wasm.

    take_drop_app_rewrite 0.
    iApply (wp_invoke_native with "Hf Hidnstart");[eauto|eauto..|].
    iNext. iIntros "[Hf Hidnstart]".
    iApply (wp_frame_bind with "Hf").
    { by cbn. } 
    iIntros "Hf".
    take_drop_app_rewrite 0. iApply (wp_block with "Hf");[auto..|].
    iNext. iIntros "Hf".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_ctx_bind;[simpl;auto|]. repeat erewrite app_nil_l.
    
    iSimpl.

    take_drop_app_rewrite 2.
    iApply (wp_seq _ _ _ (λ vs, ⌜vs = immV []⌝ ∗ _)%I).
    iSplitR;[by iIntros "[%Hcontr _]"|].
    iSplitL "Hf".
    { iApply (wp_set_local with "Hf");[|done]. simpl. lia. }
    iIntros (w) "[-> Hf]". iSimpl. iSimpl in "Hf".

    iApply fupd_wp.
    iMod (na_inv_acc with "Hadv Hown") as "(>Hg & Hown & Hcls)";[solve_ndisj..|]. iModIntro.
    take_drop_app_rewrite_twice 0 2.
    iApply wp_wasm_empty_ctx. iApply wp_base_push;auto.
    iApply (wp_call_ctx with "Hf");[simpl;eauto|].
    iNext. iIntros "Hf".
    (* iApply wp_base_pull. iApply wp_wasm_empty_ctx. *)
    (* iSimpl. *)
  
    take_drop_app_rewrite 1.
    iApply (wp_seq_can_trap_ctx).
    instantiate (1:=λ f', (⌜f' = {|
                    f_locs := [xx 42];
                    f_inst := inst
                               |}⌝)%I).
    instantiate (2:=λ vs, ((interp_values [] vs ∨ interp_call_host_cls
                                                    [(Mk_hostfuncidx h, Tf [T_i32] [])] [] vs)
                             ∗ na_own logrel_nais ⊤)%I).
    iSplitR.
    { iIntros "[[Hcontr|Hcontr] _]".
      { iDestruct "Hcontr" as (?) "[%Hcontr H]";done. }
      { rewrite fixpoint_interp_call_host_cls_eq. iDestruct "Hcontr" as (? ? ? ? ? ? ?) "_";done. }
    }
    iSplitR.
    { iIntros (f') "[Hf' ->]".
      eassert (LH_rec [] 0 [] (LH_base [] []) [] = push_base (LH_base [] []) _ _ _ _) as ->.
      { simpl. eauto. }
      iApply wp_label_push_nil_inv. iApply wp_wasm_empty_ctx.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗ ↪[frame] _)%I with "[Hf']").
      { iApply (wp_label_trap with "Hf'");eauto. }
      iIntros (v) "[-> Hf]". iExists _. iFrame.
      iIntros "Hf".
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗ ↪[frame] _)%I with "[Hf]").
      { iApply (wp_frame_trap with "Hf");eauto. }
      iIntros (v) "[-> Hf]".
      iApply iris_host.wp_value;eauto.
      iFrame. by iLeft. }
    iFrame.
    iSplitR "Hlog".
    { iIntros "Hf". take_drop_app_rewrite 0.
      iApply (wp_invoke_native with "Hf Hg");[eauto..|].
      iNext. iIntros "[Hf Hg]".
      iApply fupd_wp. iMod ("Hcls" with "[$]") as "Hown".
      iModIntro.
      rewrite -wp_frame_rewrite.
      iApply wp_wasm_empty_ctx_frame.
      take_drop_app_rewrite 0.
      iApply (wp_block_local_ctx with "Hf");[eauto..|].
      iNext. iIntros "Hf".
      iApply wp_wasm_empty_ctx_frame.
      rewrite wp_frame_rewrite.
      
      iDestruct (be_fundamental_local_stuck_host _ _ [] with "Hi Hf Hown") as "HH";[eauto..|].
      instantiate (1:=n_zeros locs).
      unfold interp_expression_closure_stuck_host.

      iDestruct ("HH" with "[]") as "Hcont".
      { iSimpl. iRight. iExists _. iSplit;eauto. iApply n_zeros_interp_values. }
      erewrite app_nil_l.
      iApply (wp_wand with "Hcont").
      iIntros (v) "[[Hv Hown] Hf]".
      iSplitR "Hf";cycle 1.
      { iExists _. iFrame. auto. }
      iDestruct "Hv" as "[[Hv | Hv] | Hv]";auto. }

    iIntros (w f') "[[Hv Hown] [Hf ->]]".
    iSimpl. rewrite app_nil_r.
    iDestruct "Hv" as "[Hv | Hv]".
    { (* unknown call returned a value *)
      iApply (lse_log_return_value with "Hh Hv Hlog Hown Hf");auto. }
    
    { (* unknown call invoked the host log function *)
      iApply (lse_log_return_call_host with "Hh Hv Hlog Hown Hf");auto. }
  Qed.
  
  
  Definition lse_log_module :=
    {| mod_types := [Tf [] []; Tf [T_i32] []; Tf [] []];
       mod_funcs :=  [ {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [T_i32] ;
          modfunc_body := lse_log_expr 0 1
        |} ] ;
      mod_tables := [];
      mod_mems := [];
      mod_globals := [];
      mod_elem := [];
      mod_data := [];
      mod_start := Some {| modstart_func := Mk_funcidx 2 |};
      mod_imports := [ {| imp_module := list_byte_of_string "Adv";
                         imp_name := list_byte_of_string "adv_call";
                         imp_desc := ID_func 0 |};
                       {| imp_module := list_byte_of_string "Host";
                         imp_name := list_byte_of_string "log_call";
                         imp_desc := ID_func 1 |} ];
      mod_exports := []
    |}.

  Definition lse_func_impts : seq.seq extern_t := [ET_func (Tf [] []); ET_func (Tf [T_i32] [])].

  Ltac type_next :=
  match goal with
  | |- context [ be_typing _ ?e _  ] =>
      rewrite -(list.take_drop (length e - 1) e);simpl take; simpl drop;
      eapply bet_composition;[|econstructor;eauto];simpl
  end.
  
  Lemma lse_module_typing :
    module_typing lse_log_module (lse_func_impts) [].
  Proof.
    exists [Tf [] []],[]. simpl.
    repeat split;eauto.
    { apply Forall2_cons. split;auto. cbn.
      repeat split;auto.
      repeat type_next. constructor. }
    { apply Forall2_cons. split;auto. }
  Qed.

  Definition adv_lse_instantiate :=
    [ ID_instantiate [1%N] 0 [0%N] ;
      ID_instantiate [] 1 [1%N;0%N] ].

  
  Lemma instantiate_lse adv_module log_func h :
    module_typing adv_module [ET_func (Tf [T_i32] [])] [ET_func (Tf [] [])] ->
    (* we assume the adversary module has an export of the () → () *)
    mod_start adv_module = None -> (* that it does not have a start function *)
    module_restrictions adv_module ->
    (* that it adheres to the module restrictions (i.e. only constant initializers for globals) *)
    module_elem_bound_check_gmap ∅ [] adv_module ->
    (* if the adversary module declares a table, there cannot be more initializers that its size *)
    module_data_bound_check_gmap ∅ [] adv_module ->
    (* if the adversary module declares a memory, there cannot be more initializers that its size *)

    ⊢ {{{ N.of_nat log_func ↦[wf] (FC_func_host (Tf [T_i32] []) (Mk_hostfuncidx h)) ∗
          N.of_nat h ↦[ha] HA_print ∗
          0%N ↪[mods] adv_module ∗
          1%N ↪[mods] lse_log_module ∗
          na_own logrel_nais ⊤ ∗
          (∃ name, 0%N ↪[vis] {| modexp_name := name; modexp_desc := MED_func (Mk_funcidx log_func) |}) ∗
          (∃ vs, 1%N ↪[vis] vs) }}}
        ((adv_lse_instantiate,[]) : host_expr)
      {{{ v, (⌜v = trapHV⌝ ∨ (⌜v = immHV []⌝ ∗ na_own logrel_nais ⊤)) }}} .
  Proof.
    iIntros (Htyp Hnostart Hrestrict Hboundst Hboundsm).
    iModIntro. iIntros (Φ) "(Hlogfunc & Hh & Hmod_adv & Hmod_lse & Hown & Hvis1 & Hvis) HΦ".
    iDestruct "Hvis1" as (log) "Hvis1".
    iApply (wp_seq_host_nostart with "[$Hmod_adv] [Hvis Hvis1 Hlogfunc] ") => //.
    { iIntros "Hmod_adv".
      iApply weakestpre.wp_mono.
      2: iApply (instantiation_spec_operational_no_start _ _ _ [0%N] [_] _ _ _ _
                    {[ N.of_nat log_func := (FC_func_host (Tf [T_i32] []) (Mk_hostfuncidx h)) ]} ∅ ∅ ∅);eauto;iFrame.
      2: cbn; repeat iSplit =>//.
      iIntros (v) "[$ Hv]". iExact "Hv".
      { cbn. rewrite dom_singleton_L. iPureIntro. set_solver. }
      { iSimpl. iSplit =>//. iExists _. iFrame. rewrite lookup_singleton. auto. }
      (* unfold instantiation_resources_pre_wasm. cbn. *)
      (* unfold import_resources_wasm_typecheck. cbn. *)
      
      iPureIntro. destruct Htyp as [fts [gts Htyp]].
      destruct adv_module;simpl in *.
      destruct Htyp as (_&_&_&_&_&_&_&_&Htyp).
      apply Forall2_length in Htyp. rewrite /lse_func_impts /= // in Htyp.
    }

    iIntros (w) "[Himps Hinst_adv] Hmod_adv".
    iDestruct "Hinst_adv" as (inst_adv) "[Hinst_adv Hadv_exports]".
    iDestruct "Hinst_adv" as (g_adv_inits t_adv_inits m_adv_inits glob_adv_inits wts' wms')
                               "(Himpstyp & %HH & %Htyp_inits & %Hwts' & %Hbounds_elem & %Hmem_inits 
                               & %Hwms' & %Hbounds_data & %Hglob_inits_vals & %Hglob_inits & Hinst_adv_res)".
    destruct HH as (?&?&?&?&?&?).
    iDestruct (big_sepL2_length with "Hadv_exports") as %Hexp_len.
    destruct (mod_exports adv_module) eqn:Hexp;[done|].
    destruct l;[|done].
    iDestruct "Hadv_exports" as "[Hn _]".
    iDestruct "Himps" as "[Hm _]".
    revert Htyp. rewrite module_typing_body_eq =>Htyp.
    destruct Htyp as [fts [gts Htyp]].
    assert (Hmod:=Htyp).
    remember adv_module as advm.
    destruct adv_module. rewrite Heqadvm in Hexp.
    rewrite Heqadvm in Hmod.
    
    simpl in Hexp. subst mod_exports.
    destruct Hmod as (Hmod&_&_&_&_&_&_&Himpts&Hexpts).
    apply Forall2_length in Himpts as Hlenimpts.
    destruct mod_imports;[done|destruct mod_imports;[|done]].
    simpl in Himpts.
    apply Forall2_cons in Himpts as [Hm0 _].
    rewrite /module_import_typing /= in Hm0.
    destruct (imp_desc m0) eqn:Himpm0;try done.

      
    unfold lse_func_impts in Hexpts. simpl in Hexpts.
    apply Forall2_cons in Hexpts as [He _].
    unfold module_export_typing in He. simpl in He.
    destruct (modexp_desc m) eqn:Hm;[destruct f|by destruct t|by destruct m1|by destruct g].
    apply andb_true_iff in He as [Hle He].
    destruct (nth_error (Tf [T_i32] [] :: fts) n0) eqn:Hn;[|done].
    revert He. move/eqP=>He. subst f.
    iDestruct "Hn" as (name) "Hn".

    rewrite Heqadvm. simpl in Hmod.
    iDestruct "Hinst_adv_res" as "(Hresf & Hrest & Hresm & Hresg) /=".
    rewrite /get_import_func_count
            /get_import_mem_count
            /get_import_table_count
            /get_import_global_count /= Himpm0 /=.
    rewrite !drop_0 -Heqadvm.
    rewrite nth_error_lookup in Hn.
    destruct n0;[done|]. simpl in Hn.
    eapply Forall2_lookup_r in Hmod as [mf [Hmf Htypf]];[|eauto].
    destruct mf. simpl in Htypf.
    destruct modfunc_type. destruct Htypf as (Hlef & Hnthf & Htypf).
    revert Hlef. move/ssrnat.leP=>Hlef.
    assert (n1 < length mod_types) as Hlt;[lia|].
    rewrite Heqadvm /= in H.
    apply lookup_lt_is_Some in Hlt as [t Ht].
    rewrite - nth_error_lookup in Ht.
    erewrite nth_error_nth in Hnthf;eauto.
    revert Hnthf;move/eqP=>heq. subst t.
    iDestruct (big_sepL2_length with "Hresf") as %Hinstf_len.
    apply lookup_lt_Some in Hmf as Hlt'.
    rewrite Hinstf_len in Hlt'.
    apply lookup_lt_is_Some in Hlt' as [advf Hadv].
    iDestruct (big_sepL2_lookup_acc with "Hresf") as "[Hadvf Hcls]";[eauto..|].
    simpl.
    rewrite - nth_error_lookup in Hadv.
    rewrite H.
    erewrite !nth_error_nth;eauto;cycle 1.
    { destruct (inst_funcs inst_adv). by rewrite Coqlib.nth_error_nil in Hadv.
      simpl in *. rewrite drop_0 in Hadv. auto. }

    iDestruct "Himpstyp" as "[%Himpsdom [Himp _]]".
    iSimpl in "Himp". iDestruct "Himp" as (cl) "[Hlogfunc [%Hlookcl _]]".
    rewrite lookup_singleton in Hlookcl. inversion Hlookcl;subst cl;clear Hlookcl.
    iDestruct (mapsto_ne with "Hadvf Hlogfunc") as %Hne.
    
    iApply (weakestpre.wp_wand _ _ _ (λ v, _ ∗ ↪[frame]empty_frame)%I with "[-HΦ] [HΦ]");cycle 1.
    { iIntros (v) "[Hv ?]". iApply "HΦ". iExact "Hv". }
    { iApply (instantiation_spec_operational_start with "[$Hmod_lse Hadvf Hn Hm Hlogfunc]");[eauto|..].
      { apply lse_module_typing. }
      { unfold import_resources_host.
        instantiate (5:=[_;_]). iFrame "Hn Hm".
        unfold import_resources_wasm_typecheck,export_ownership_host.
        iSimpl. do 3 iSplit =>//.
        { instantiate (1:=∅).
          instantiate (1:=∅).
          instantiate (1:=∅).
          instantiate (1:= {[ N.of_nat log_func := (FC_func_host (Tf [T_i32] []) (Mk_hostfuncidx h));
                            N.of_nat advf := (FC_func_native inst_adv (Tf [] []) modfunc_locals modfunc_body)]}).
          unfold import_resources_wasm_typecheck => /=.
          iSplit.
          - iPureIntro. cbn. repeat split;auto.
            all: try by rewrite dom_insert_L dom_singleton_L;set_solver+.
          - iSplitL "Hadvf".
            { iExists _. iFrame. simpl. rewrite lookup_insert_ne //.
              rewrite lookup_insert. auto. }
            { iSplit =>//. iExists _. iFrame. simpl. rewrite lookup_insert. auto. }
        }
        { iSplit;auto.
          { rewrite /module_elem_bound_check_gmap /=.
            iPureIntro. by apply Forall_nil. }
          { rewrite /module_data_bound_check_gmap /=.
            iPureIntro. by apply Forall_nil. }
        }
      }
      { iIntros (idnstart) "Hf [Hmod_lse Hr]".
        iDestruct "Hr" as "([Himph Hexp] & Hr)".
        iDestruct "Hr" as (?) "[Hr _]".
        iDestruct "Hr" as (? ? ? ? ? ?) "([%Hdom [Himpr [Hlogfunc _]]] & %Htypr & %Htab_inits & %Hwts'0 & %Hbounds_elemr & 
        %Hmem_initsr & %Hwms0' & %Hbounds_datar & %Hglobsr & %Hglob_initsr & (Hr & _ & _ & _))".
        destruct Htypr as (Heq1&[? Heq2]&[? Heq3]&[? Heq4]&[? Heq6]&Heq5).
        rewrite Heq2.
        iSimpl in "Himpr Hlogfunc". cbn.
        iDestruct (big_sepL2_length with "Hr") as %Himprlen.
        destruct x;[done|destruct x;[|done]].
        iDestruct "Hr" as "[Hr _] /=". rewrite Heq1 /=.
        iDestruct "Himpr" as (cl) "[Hcl %Hcl]". destruct Hcl as [Hlookcl Hcltyp].
        rewrite lookup_insert_ne// lookup_singleton in Hlookcl. inversion Hcltyp;inversion Hlookcl.
        iDestruct ("Hcls" with "Hcl") as "Hresf". subst cl. clear Hlookcl H6 Hcltyp.
        iDestruct "Hlogfunc" as (cl) "[Hcl %Hcl]". destruct Hcl as [Hlookcl Hcltyp].
        rewrite lookup_insert in Hlookcl. inversion Hcltyp;inversion Hlookcl. subst cl. clear Hlookcl H6 Hcltyp.
        
        iApply weakestpre.fupd_wp.
        iMod (interp_instance_alloc [(Mk_hostfuncidx h, Tf [T_i32] [])]
               with "[] [] [] [Hcl] [Hrest Hresm Hresg Hresf]") as "[#Hi [[#Hires _] #Himpres]]";
          [apply Htyp|repeat split;eauto|eauto|..].
        4,5: by instantiate (1:=∅).
        { rewrite Heqadvm /=. auto. }
        { destruct Hglob_inits_vals as [? ?];eauto. }
        { instantiate (1:={[ N.of_nat log_func := FC_func_host (Tf [T_i32] []) (Mk_hostfuncidx h)]}).
          iApply big_sepM_singleton. simpl.
          iPureIntro. split;auto. constructor. }
        { instantiate (1:=∅). repeat iSplit;auto.
          rewrite dom_singleton_L /=. iPureIntro. set_solver+.
          rewrite module_import_init_tabs_dom. auto.
          rewrite module_import_init_mems_dom. auto.
          iSimpl. iSplit =>//. iExists _. iFrame. rewrite lookup_insert. auto.
        }
        { rewrite Htyp_inits Hmem_inits Hglob_inits
                  /module_inst_resources_wasm Heqadvm /=
                  /get_import_table_count
                  /get_import_mem_count
                  /get_import_global_count
                  /get_import_func_count /= -H Himpm0 /=. iFrame.
        }

        rewrite !app_nil_l.
        iDestruct (big_sepL2_lookup with "Hires") as "Ha".
        { rewrite Heqadvm /=. eauto. }
        { rewrite Heqadvm /= /get_import_func_count /= Himpm0 /= -nth_error_lookup. eauto. }
        iSimpl in "Ha". erewrite H, nth_error_nth;eauto.

        iDestruct "Himpres" as "[_ Himpres]".
        iSimpl in "Himpres". iDestruct "Himpres" as "[Himpres _]".
        iDestruct "Himpres" as (cl) "[Himpres %Hcl]".
        destruct Hcl as [Hcl _]. rewrite lookup_insert in Hcl. inversion Hcl;subst cl;clear Hcl.

        destruct (inst_funcs inst) eqn:Hinstfuncseq;[done|]. destruct l;[done|].
        simpl in Heq5. revert Heq5. move/eqP =>Hstart. rewrite Hinstfuncseq /= in Hstart.
        inversion Heq2;subst f f0 l. inversion Hstart.
        iMod (na_inv_alloc logrel_nais _ logN with "Hh") as "#Hh".
        iModIntro.
        iApply (lse_log_spec with "[$Hr $Hown $Hi $Ha $Hh $Hf $Himpres]");auto.
        { simplify_eq. simpl. auto. }
        { rewrite Hinstfuncseq;eauto. }
        { rewrite Hinstfuncseq;eauto. }
      }
    }
  Qed.

    

End Host_robust_example.
