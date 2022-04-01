From mathcomp Require Import ssreflect eqtype seq ssrbool ssrfun.
From iris.program_logic Require Import language weakestpre lifting.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
(* From iris.bi Require Export weakestpre. *)
Require Export iris_locations iris_properties stdpp_aux iris.
Require Export datatypes host operations properties opsem instantiation.

Section Iris_host.

Import DummyHosts.

Definition reduce := @reduce host_function host_instance.

Definition host_val := val.

(* Domain of the variable instantiation store *)
Definition vi := N.

(* variable instantiation store. *)
Definition vi_store := gmap vi module_export.

Definition module_decl := module.

(* an import is specified by giving the index of the instance to the module_export and a second index in the list*)
Definition vimp : Type := vi.

(* There is only one instance declaration instruction: instantiating a module.
   ID_instantiate vi vm vimps is supposed to instantiate the module vmth module
   in the program state, taking imports as specified by each of the vimps, 
   and store the list of exports in the vi_store for future use.
 *)
Inductive inst_decl: Type :=
  ID_instantiate: list vi -> N -> list vimp -> inst_decl.

Definition host_config : Type := store_record * vi_store * (list module) * (list inst_decl) * (list administrative_instruction).

Definition instantiate := instantiate host_function host_instance.

(* Does the start function always take 0 arguments? *)
Definition map_start (start: option nat) : list administrative_instruction :=
  match start with
  | Some n => [AI_invoke n]
  | None => []
  end.

Definition lookup_export_vi (vis: vi_store) (vimp: vimp) : option module_export:=
  vis !! vimp.
  (*
  let (vindex, vname) := vimp in
  match vis !! vindex with
  | Some vexts => vexts !! (N.to_nat vname)
  | None => None
  end.*)

(* some kind of folding on 2 lists *)
Fixpoint insert_exports (vis: vi_store) (iexps: list vi) (exps: list module_export) : option vi_store :=
  match iexps with
  | [::] => Some vis
  | i :: iexps' => match exps with
                 | [::] => None
                 | exp :: exps' => match (insert_exports vis iexps' exps') with
                                 | Some vis' => Some (<[ i := exp ]> vis')
                                 | None => None
                                 end
                 end
  end.


Definition empty_instance := Build_instance [::] [::] [::] [::] [::].
Definition empty_frame := Build_frame [::] empty_instance.

(* Dummy *)
Parameter hs: host_state host_instance.

(* Note that instantiation takes imports as module_export_desc but gives exports as module_export (i.e. with a name). *)
Print instantiation.instantiate.

Print module_export.

Print alloc_module.




Inductive host_reduce: host_config -> host_config -> Prop :=
| HR_host_step: forall s (vis: vi_store) m (viexps: list vi) vm vimps imps imp_descs s' vis' ms idecs' inst (exps: list module_export) start vs,
    ms !! (N.to_nat vm) = Some m ->
    those ((lookup_export_vi vis) <$> vimps) = Some imps ->
    map (fun imp => imp.(modexp_desc)) imps = imp_descs ->
    instantiate s m imp_descs ((s', inst, exps), start) ->
    length viexps = length exps ->
    const_list vs ->
    insert_exports vis viexps exps = Some vis' ->
    host_reduce (s, vis, ms, (ID_instantiate viexps vm vimps) :: idecs', vs) (s', vis', ms, idecs', map_start start)
| HR_wasm_step: forall s vis ms idecs s' es es' hs',
    (* No reentrancy and no host functions, so hs should just be dummy *)
    opsem.reduce hs s empty_frame es hs' s' empty_frame es' ->
    host_reduce (s, vis, ms, idecs, es) (s', vis, ms, idecs, es').

Definition host_expr : Type := (list inst_decl) * (list administrative_instruction).

(* val is the same as native Wasm, defined in Iris.v *)
(*
Definition val_eq_dec : forall v1 v2: val, {v1 = v2} + {v1 <> v2}.
Proof.
  decidable_equality.
Defined.
Definition val_eqb (v1 v2: val) : bool := val_eq_dec v1 v2.
Definition eqvalP : Equality.axiom val_eqb :=
  eq_dec_Equality_axiom val_eq_dec.

Canonical Structure val_eqMixin := EqMixin eqvalP.
Canonical Structure val_eqType := Eval hnf in EqType val val_eqMixin.
*)


Definition state : Type := store_record * vi_store * (list module) .

Definition observation := unit. 

Definition of_val (v: val) : host_expr := ([::], iris.of_val v).

Lemma of_val_imm (vs : list value) :
  ([::], ((λ v : value, AI_basic (BI_const v)) <$> vs)) = of_val (immV vs).
Proof. done. Qed.

Definition to_val (e: host_expr) : option val :=
  match e with
  | (e' :: es, _) => None
  | ([::], wes) => iris.to_val wes
  end.

Definition prim_step (e : host_expr) (s : state) (os : list observation) (e' : host_expr) (s' : state) (fork_es' : list host_expr) : Prop :=
  let '(ws, vis, ms) := s in
  let '(ws', vis', ms') := s' in
  let '(hes, wes) := e in
  let '(hes', wes') := e' in
    host_reduce (ws, vis, ms, hes, wes) (ws', vis', ms', hes', wes') /\ os = [] /\ fork_es' = [].


Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by apply iris.to_of_val.
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  destruct e as [hes wes] => /=.
  destruct hes => //.
  move => Htv; apply iris.of_to_val in Htv.
  unfold of_val.
  by f_equal.
Qed.

Lemma val_head_stuck : forall e1 s1 κ e2 s2 efs,
  prim_step e1 s1 κ e2 s2 efs →
  to_val e1 = None.
Proof.
  rewrite /prim_step.
  move => [hes wes] [[ws vis] hprog] κ [hes' wes'] [[ws' vis'] hprog'] efs [HRed _].
  inversion HRed => //=; subst.
  destruct hes' => //.
  eapply iris.val_head_stuck with (s1 := (hs, ws, [::], empty_instance)) (s2 := (hs', ws', [::], empty_instance)).
  unfold iris.prim_step.
  by repeat split => //.
Qed.

Lemma wasm_host_mixin : LanguageMixin of_val to_val prim_step.
Proof. split; eauto using to_of_val, of_to_val, val_head_stuck. Qed.

Canonical Structure wasm_host_lang := Language wasm_host_mixin.

Implicit Type σ : state.

Require Export iris_wp_def.

Definition function_closure := function_closure host_function.

(* The host expands the memory model of Wasm by vi_store and a list of module declarations. *)

Class hvisG Σ := HVisG {
  vis_genG :> ghost_mapG Σ N module_export
}.

Class hmsG Σ := HMsG {
  ms_genG :> ghost_mapG Σ N module
}.



Definition frameGName : positive := 10%positive.
Definition visGName : positive := 11%positive.
Definition msGName : positive := 12%positive.

Definition proph_id := positive. (* still have no idea about what this is *)

Instance eqdecision_vi: EqDecision vi.
Proof. move => n n'. unfold Decision. by decidable_equality. Qed.

Instance eqdecision_frame: EqDecision frame.
Proof. decidable_equality. Qed.

Instance eqdecision_module: EqDecision module.
Proof. move => m m'. unfold Decision. by decidable_equality. Qed.

Instance eqdecision_module_export: EqDecision (list module_export).
Proof. decidable_equality. Qed.

Notation " n ↪[vis]{ q } v" := (ghost_map_elem (V := module_export) visGName n q v%V)
                           (at level 20, q at level 5, format " n ↪[vis]{ q } v") .
Notation " n ↪[vis] v" := (ghost_map_elem (V := module_export) visGName n (DfracOwn 1) v%V)
                          (at level 20, format " n ↪[vis] v").

Notation " n ↪[mods]{ q } v" := (ghost_map_elem (V := module) msGName n q v%V)
                           (at level 20, q at level 5, format " n ↪[mods]{ q } v") .
Notation " n ↪[mods] v" := (ghost_map_elem (V := module) msGName n (DfracOwn 1) v%V)
                            (at level 20, format " n ↪[mods] v").

Global Instance host_heapG_irisG `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ} : weakestpre.irisGS wasm_host_lang Σ := {
  iris_invGS := func_invG; (* ??? *)
  state_interp σ _ κs _ :=
    let: (s, vis, ms) := σ in
     ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
      (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
      (gen_heap_interp (gmap_of_list s.(s_globals))) ∗
      (ghost_map_auth visGName 1 vis) ∗ 
      (ghost_map_auth msGName 1 (gmap_of_list ms)) ∗
      (* Should this really be here, though? *)
      (ghost_map_auth frameGName 1 (<[ tt := empty_frame ]> ∅)) ∗ 
      (gen_heap_interp (gmap_of_list (fmap mem_length s.(s_mems)))) ∗
      (gen_heap_interp (gmap_of_list (fmap tab_size s.(s_tables))))
    )%I;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
}.




Section host_lifting.
Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ}.


(* adding this would nullify all lemmas in weakestpre -- why? Is this not the 
   correct instance? *)
(*
Global Instance wp_host : Wp (iProp Σ) host_expr iris.val stuckness.
Proof using Σ wfuncG0 wtabG0 wmemG0 wmemsizeG0 wglobG0 wframeG0 hvisG0 hmsG0.
  by eapply weakestpre.wp'.
Qed.
*)

Lemma wp_host_test_const (s: stuckness) E vs:
  ⊢ wp s E (([::], (v_to_e_list vs)): host_expr) (λ v, ⌜ v = immV vs ⌝).
Proof.
  iApply weakestpre.wp_value => //.
  unfold IntoVal => /=. by f_equal. 
Qed.

(*
Let wp_wasm := @wp_wasm Σ wfuncG0.
*)


Definition reducible := @reducible wasm_host_lang.

Let reduce := @reduce host_function host_instance.

(* All the possible wasm expression that could appear in the host configuration, starting from empty *)
Inductive host_wasm_expr_valid : list administrative_instruction -> Prop :=
| HWEV_const: forall es,
    const_list es ->
    host_wasm_expr_valid es
(* Trap is also a possibility *)
| HWEV_trap:
    host_wasm_expr_valid [AI_trap]
| HWEV_invoke: forall n,
    host_wasm_expr_valid [AI_invoke n]
| HWEV_local: forall n f es,
    host_wasm_expr_valid [AI_local n f es].

Hint Constructors host_wasm_expr_valid.



(* Any possible wasm expression as defined above reduces independently from the frame. *)
Lemma hwev_reduce_ignore_frame es hs ws f1 f2 hs' ws' f' es':
  host_wasm_expr_valid es ->
  reduce hs ws f1 es hs' ws' f' es' ->
  reduce hs ws f2 es hs' ws' f2 es'.
Proof.
  move => Hhwev Hred.
  inversion Hhwev; subst; clear Hhwev.
  (* values *)
  - by apply values_no_reduce in Hred.
  (* trap *)
  - by apply test_no_reduce_trap in Hred.
  - remember [AI_invoke n] as es0. induction Hred; subst => //=.
    + inversion H; subst; clear H => //=; try by do 3 destruct vs => //.
      move/lfilledP in H1.
      inversion H1; subst; clear H1.
      by do 2 destruct vs => //=.
    + by eapply r_invoke_native => //=.
    + move/lfilledP in H.
      inversion H; subst; clear H => //; last by do 2 destruct vs => //.
      destruct vs => //=.
      2: { destruct vs, es, es'0 => //=. simpl in H1; inversion H1; subst; by simpl in H5. }
      destruct es => /=; first by exfalso; eapply empty_no_reduce.
      destruct es, es'0 => //=; simpl in H1.
      inversion H1; subst; clear H1.
      move/lfilledP in H0.
      inversion H0; subst; clear H0.
      simpl; rewrite cats0.
      by apply IHHred.
  (* local *)
  - remember [AI_local n f es0] as es1. induction Hred => //=.
    + inversion H; subst; clear H => //=; try by do 3 destruct vs => //.
      * inversion H2; subst; clear H2.
        by apply r_simple, rs_local_const.
      * inversion H0; subst; clear H0.
        by apply r_simple, rs_local_trap.
      * inversion H3; subst; clear H3.
        by apply r_simple; eapply rs_return.
      * move/lfilledP in H1.
        inversion H1; subst; clear H1.
        by do 2 destruct vs => //=.
    + by eapply r_invoke_native => //=.
    + move/lfilledP in H.
      inversion H; subst; clear H => //; last by do 2 destruct vs => //.
      destruct vs => //=.
      2: { destruct vs, es, es'0 => //=. simpl in H5; inversion H5; subst; by simpl in H1. }
      destruct es => /=; first by exfalso; eapply empty_no_reduce.
      destruct es, es'0 => //=; simpl in H5.
      inversion H5; subst; clear H5.
      move/lfilledP in H0.
      inversion H0; subst; clear H0.
      simpl; rewrite cats0.
      by apply IHHred.
    + by apply r_local.
Qed.



(* The set of possible wasm expressions is closed wrt reduce. *)
Lemma hwev_reduce_closed hs ws f es hs' ws' f' es':
  host_wasm_expr_valid es ->
  reduce hs ws f es hs' ws' f' es' ->
  host_wasm_expr_valid es'.
Proof.
  move => Hhwev Hred.
  inversion Hhwev; subst; clear Hhwev => /=.
  - by apply values_no_reduce in Hred. 
  - by apply test_no_reduce_trap in Hred.
  - remember [AI_invoke n] as es0. induction Hred => //=.
    + inversion H; subst; clear H => //=; try by do 3 destruct vs => //.
    + move/lfilledP in H.
      inversion H; subst; clear H => //; last by do 2 destruct vs => //.
      destruct vs => //=.
      2: { destruct vs, es, es'0 => //=. simpl in H5; inversion H5; subst; by simpl in H1. }
      destruct es => /=; first by exfalso; eapply empty_no_reduce.
      destruct es, es'0 => //=; simpl in H5.
      inversion H5; subst; clear H5.
      move/lfilledP in H0.
      inversion H0; subst; clear H0.
      simpl; rewrite cats0.
      by apply IHHred.
  - remember [AI_local n f0 es0] as es1.
    induction Hred; subst => //=; try by do 3 destruct vcs => //=.
    + inversion H; subst; clear H => //=; (try by do 3 destruct vs => //); by apply HWEV_const.
    + move/lfilledP in H.
      inversion H; subst; clear H => //; last by do 2 destruct vs => //.
      destruct vs => //=.
      2: { destruct vs, es, es'0 => //=. simpl in H1; inversion H1; subst; by simpl in H5. }
      destruct es => /=; first by exfalso; eapply empty_no_reduce.
      destruct es, es'0 => //=; simpl in H1.
      inversion H1; subst; clear H1.
      move/lfilledP in H0.
      inversion H0; subst; clear H0.
      simpl; rewrite cats0.
      by apply IHHred.
Qed.



(* Lifting reduction of valid wasm expressions to host configurations. *)
Lemma reducible_lift es ws vis ms:
  host_wasm_expr_valid es ->
  iris_wp_def.reducible es (hs, ws, [], empty_instance) ->
  reducible ([], es) (ws, vis, ms).
Proof.
  move => Hvalid.
  unfold reducible, iris_wp_def.reducible, language.reducible, prim_step.
  move => [κ [es' [σ' [efs HStep]]]].
  destruct σ' as [[[hs' ws'] vs'] inst'].
  exists [], ([], es'), (ws', vis, ms), [].
  simpl in *.
  destruct HStep as [HStep [-> ->]].
  split => //.
  eapply HR_wasm_step.
  by eapply hwev_reduce_ignore_frame in Hvalid => //.
Qed.

(* Lifting wasm wp to host wp *)
Lemma wp_host_wasm (s: stuckness) E (es: iris.expr) (Φ: iris.val -> iProp Σ):
  (* wp_wasm s E es Φ *)
  (* This abuse of notation is somehow possible. It is the weirdest thing I've 
     seen in a while *)
  host_wasm_expr_valid es ->
  WP es @ s; E {{ Φ }}
  ⊢ WP (([::], es): host_expr) @ s; E {{ Φ }}.
Proof.
  iLöb as "IH" forall (s E es Φ).
  iIntros (Hhwev).
  repeat rewrite weakestpre.wp_unfold /weakestpre.wp_pre /=.
  repeat rewrite wp_unfold /wp_pre /=.
  iIntros "Hwp".
  destruct (iris.to_val es) eqn: Hes => //=.
  iIntros ([[ws vis] ms] ns κ κs nt) "Hσ".
  iSpecialize ("Hwp" $! (hs, ws, [::], empty_instance) ns κ κs nt).
  iDestruct "Hσ" as "(Hwf & Hwt & Hwm & Hwg & Hvis & Hms & Hframe & Hmsize & Htsize)".
  iSpecialize ("Hwp" with "[$]").
  iMod "Hwp" as "(%Hred & Hwp)".
  iModIntro.
  iSplit.
  - destruct s => //.
    iPureIntro.
    by apply reducible_lift.
  - iIntros ([hes' wes'] [[ws' vis'] ms'] efs HStep).
    unfold Iris_host.prim_step in HStep.
    destruct HStep as [HStep [-> ->]].
    inversion HStep; subst; clear HStep.
    iSpecialize ("Hwp" $! wes' (hs', ws', [::], empty_instance) [::] with "[%]"); first by unfold iris.prim_step.
    iMod "Hwp".
    do 2 iModIntro.
    iMod "Hwp".
    iModIntro.
    iMod "Hwp".
    iModIntro.
    iDestruct "Hwp" as "((Hwf & Hwt & Hwm & Hwg & Hwframe & Hmsize & Htsize) & Hwp)".
    iDestruct "Hwp" as (f) "(Hf & Hwp & ?)".
    iFrame.
    iSplit => //.
    iApply "IH"; first by apply hwev_reduce_closed in H0.
    iApply "Hwp".
    by iApply "Hf".
Qed.

End host_lifting.

Section host_structural.
  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ}.

  (* Note that the host wp is based on the original wp, as in the one in iris.weakestpre, so we have many lemma 
     available *)


Lemma wp_seq_host_nostart (s : stuckness) (E : coPset) (Φ Ψ : host_val -> iProp Σ) v_exps modi v_imps m (es : list inst_decl) :
  m.(mod_start) = None ->
  modi ↪[mods] m -∗
  (modi ↪[mods] m -∗ WP (([::ID_instantiate v_exps modi v_imps], [::]): host_expr) @ s; E {{ w, Ψ w ∗ modi ↪[mods] m }}) -∗
  (∀ w, Ψ w -∗ modi↪[mods] m -∗ WP ((es, [::]): host_expr) @ s; E {{ v, Φ v }}) -∗
  WP (((ID_instantiate v_exps modi v_imps :: es), [::]): host_expr) @ s; E {{ v, Φ v }}.
Proof.
  (*
  move => Hnostart.  
  iLöb as "IH" forall (s E es Φ Ψ).
  iIntros "Hmod Hes1 Hes2".
                 
  iApply weakestpre.wp_unfold. repeat rewrite weakestpre.wp_unfold /weakestpre.wp_pre /=.

  iIntros (σ ns κ κs nt) "Hσ".
  iSpecialize ("Hes1" with "Hmod").
  iSpecialize ("Hes1" $! σ ns κ κs nt).
  destruct σ as [[ws vis] ms].
  iSpecialize ("Hes1" with "[$]").

  iMod "Hes1".
  iModIntro.
  iDestruct "Hes1" as "(%Hred & Hes1)".
  iFrame.

  iSplit.
  - iPureIntro.
    destruct s => //.
    unfold language.reducible in *.
    destruct Hred as [κ' [e' [σ' [efs HStep]]]].
    destruct e' as [we' he'].
    unfold prim_step in HStep.
    simpl in HStep.
    destruct σ' as [[ws' vis'] ms'].
    destruct HStep as [HStep [-> ->]].
    inversion HStep; subst; clear HStep => //=; last by apply empty_no_reduce in H0.
    
    exists [::], ((es, [::]): host_expr), (ws', vis', ms'), [::].
    repeat split => //.
    replace (ws', vis', ms', es, []) with (ws', vis', ms', es, map_start None).
    eapply HR_host_step => //.
  
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1".
    iSpecialize ("Hes2" with "Hes1").
    iDestruct (wp_unfold with "Hes2") as "Hes2"; rewrite /wp_pre /=.
    rewrite Hetov.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "[$]").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "[$]").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      by apply append_reducible.
    - iIntros (e2 σ2 efs HStep).
      assert (κ = [] /\ efs = []) as [-> ->]; first by apply prim_step_obs_efs_empty in HStep; inversion HStep.
      apply prim_step_split_reduce_r in HStep; last by [].
      destruct HStep as [[es'' [-> HStep]] | [n [m [lh [Hlf1 [Hlf2 ->]]]]]].
      + iSpecialize ("H2" $! es'' σ2 [] HStep).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iModIntro.
        destruct σ2 as [[[??] ?]?].
        iDestruct "H2" as "[Hσ H]".
        iDestruct "H" as (f1) "(Hf1 & Hes'' & Hefs)".
        iFrame. iExists _. iFrame.
        iIntros "?"; iSpecialize ("Hes''" with "[$]").
        iApply "IH".
        by iFrame. 
      + move/lfilledP in Hlf1.
        inversion Hlf1; subst; clear Hlf1.
        assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
        { unfold iris.prim_step.
          destruct σ as [[[??]?]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          move => HContra; subst.
          by destruct n.
        }
        iSpecialize ("H2" $! [AI_trap] σ [] HStep2).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        destruct σ as [[[??] ?]?].
        iDestruct "H2" as "[Hσ H]".
        iDestruct "H" as (f1) "(Hf1 & Hes'' & Hefs)".
        iFrame. iExists _. iFrame.
        iModIntro.
        iFrame.
        iIntros "?"; iSpecialize ("Hes''" with "[$]").
        replace [AI_trap] with (iris.of_val trapV) => //.
        repeat rewrite wp_unfold /wp_pre /=.
        destruct (iris.to_val (take n es1 ++ AI_trap :: drop m (es1 ++ es2))%SEQ) eqn:Hx.
  }
*)
Admitted.
  
End host_structural.



Section Instantiation_spec_operational.

Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ}.

Print module_export_desc.

(* The newly allocated resources due to instantiation. *)
Definition module_inst_resources_func (mfuncs: list module_func) (inst: instance) (inst_f: list funcaddr) : iProp Σ :=
  ([∗ list] f; addr ∈ mfuncs; inst_f,
   (* Allocated wasm resources *)
     N.of_nat addr ↦[wf] (FC_func_native
                             inst
                             (nth match f.(modfunc_type) with
                                 | Mk_typeidx k => k
                                 end (inst.(inst_types)) (Tf [] []))
                             f.(modfunc_locals)
                             f.(modfunc_body))
  )%I.

Definition module_inst_resources_tab (mtabs: list module_table) (inst_t: list tableaddr) : iProp Σ :=
  ([∗ list] tab; addr ∈ mtabs; inst_t,
    N.of_nat addr ↦[wtblock] (match tab.(modtab_type).(tt_limits) with
                            | {| lim_min := min; lim_max := omax |} =>
                                 (Build_tableinst
                                   (repeat None (ssrnat.nat_of_bin min)))
                                   (omax)
                       end)
  )%I.


Definition module_inst_resources_mem (mmems: list memory_type) (inst_m: list memaddr) : iProp Σ := 
  ([∗ list] mem; addr ∈ mmems; inst_m,
    N.of_nat addr ↦[wmblock] (match mem with
                                 | {| lim_min:= min; lim_max := omax |} =>
                                   Build_memory
                                     {| ml_init := #00%byte; ml_data := repeat #00%byte (N.to_nat min) |}
                                     (omax)
                                  end)
  ).

Definition module_inst_resources_glob (mglobs: list module_glob) (g_inits: list value) (inst_g: list globaladdr) : iProp Σ :=
  ([∗ list] g; addr ∈ mglobs; inst_g,
    N.of_nat addr ↦[wg] (Build_global
                           (g.(modglob_type).(tg_mut))
                           (nth addr g_inits (VAL_int32 int32_minus_one)) (* kinda unfortuante that this is O(n^2) *)
                        )
  ).


Print module_export_desc.

Print fold_left.

Print module.

Print instance.

(* Getting the count of each type of imports from a module. This is to calculate the correct shift for indices of the exports in the Wasm store later.*)
Definition get_import_func_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_func id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).

Definition get_import_table_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_table id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).
Definition get_import_mem_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_mem id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).
Definition get_import_global_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_global id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).
(* The collection of the four types of newly allocated resources *)
Definition module_inst_resources_wasm (m: module) (inst: instance) (g_inits: list value) : iProp Σ :=
  (module_inst_resources_func m.(mod_funcs) inst (drop (get_import_func_count m) inst.(inst_funcs)) ∗
  module_inst_resources_tab m.(mod_tables) (drop (get_import_table_count m) inst.(inst_tab)) ∗
  module_inst_resources_mem m.(mod_mems) (drop (get_import_mem_count m) inst.(inst_memory)) ∗                        
  module_inst_resources_glob m.(mod_globals) g_inits (drop (get_import_global_count m) inst.(inst_globs)))%I.

(* Resources in the host vis store for the imports *)
Definition import_resources_host (hs_imps: list vimp) (v_imps : list module_export): iProp Σ :=
  [∗ list] i ↦ hs_imp; v_imp ∈ hs_imps; v_imps,
  hs_imp ↪[vis] v_imp.


Definition export_ownership_host (hs_exps: list vi) : iProp Σ :=
  [∗ list] i ↦ hs_exp ∈ hs_exps,
  ∃ hv, hs_exp ↪[vis] hv.


Print instantiation.instantiate.

Print external_typing.

Print instantiate_globals.

Definition instantiate_globals := instantiate_globals host_function host_instance.

Search module_export.

Print module_export_typer.

Print alloc_module.

Print export_get_v_ext.

Print alloc_func.

Print module_export.

Print module_export_desc.

Print module_typing.

Print ext_t_funcs.

Print map.

Print extern_t.

(* Resources in the Wasm store, corresponding to those referred by the host vis store. This needs to also type-check
   with the module import. *)
Definition import_resources_wasm_typecheck (v_imps: list module_export) (t_imps: list extern_t) (wfs: gmap nat function_closure) (wts: gmap nat tableinst) (wms: gmap nat memory) (wgs: gmap nat global): iProp Σ :=
  (* Note that we do not actually need to know the exact content of the imports. However, these information are present
     in this predicate to make sure that they are kept incontact in the post. Note how these four gmaps are quantified
     in the instantiation spec. *)
  [∗ list] i ↦ v; t ∈ v_imps; t_imps,
  match v.(modexp_desc) with
  | MED_func (Mk_funcidx i) => ((∃ cl, N.of_nat i ↦[wf] cl ∗ ⌜ wfs !! i = Some cl /\ t = ET_func (cl_type cl) ⌝)%I)
  | MED_table (Mk_tableidx i) => (∃ tab, N.of_nat i ↦[wtblock] tab ∗ ⌜ wts !! i = Some tab /\ True ⌝) (* table type is currently not a part of the resources, so we cannot know this *)
  | MED_mem (Mk_memidx i) => (∃ mem, N.of_nat i ↦[wmblock] mem ∗ ⌜ wms !! i = Some mem /\ True⌝) (* same for memories *)
  | MED_global (Mk_globalidx i) => (∃ g gt, N.of_nat i ↦[wg] g ∗ ⌜ wgs !! i = Some g /\ t = ET_glob gt /\ global_agree g gt ⌝)
  end.

(*
Print module.

Print module_export.

Print module_export_desc.

Print module_import.

Print import_desc.


(* Getting the count of each type of imports from a module. This is to calculate the correct shift for indices of the exports in the Wasm store later.*)
Definition get_import_func_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_func id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).

Definition get_import_table_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_table id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).
Definition get_import_mem_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_mem id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).
Definition get_import_global_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_global id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).

(* The expected host resources that we should be getting from the module exports after instantiation. 

   Note that an export of index i is in fact the (i-n)th definition within the module itself (where n is the number of 
   imports of the same kind used by the module); so the correct index in the Wasm store should be the starting 
   offset + (i-n)).

   It is true that we can existentially quantify over the addresses to simplify this definition, and this might have 
   been an overkill. However, that loses the information that the newly allocated elements are guaranteed to be a 
   contiguous block (or maybe that is unimportant).
*)                                     
Definition export_resources_host (m: module) (hs_exps: list vi) (nf nt nm ng: nat) : iProp Σ :=
  [∗ list] i ↦ hs_exp; m_exp ∈ hs_exps; m.(mod_exports),
      N.of_nat i ↪[vis] match m_exp.(modexp_desc) with
               | MED_func (Mk_funcidx i) => {| modexp_name := m_exp.(modexp_name); modexp_desc := MED_func (Mk_funcidx (nf + i - get_import_func_count m)) |}
               | MED_table (Mk_tableidx i) => {| modexp_name := m_exp.(modexp_name); modexp_desc := MED_table (Mk_tableidx (nt + i - get_import_table_count m)) |}
               | MED_mem (Mk_memidx i) => {| modexp_name := m_exp.(modexp_name); modexp_desc := MED_mem (Mk_memidx (nm + i - get_import_mem_count m)) |}
               | MED_global (Mk_globalidx i) => {| modexp_name := m_exp.(modexp_name); modexp_desc := MED_global (Mk_globalidx (ng + i - get_import_global_count m)) |}
                        end.
*)

Definition exp_default := MED_func (Mk_funcidx 0).

(* The resources for module exports. This is a bit more complicated since it is allowed to export the imported elements,
   adding another case to be considered. *)
Definition module_export_resources_host (v_imps: list module_export) (hs_exps: list vi) (m_exps: list module_export) (inst: instance) : iProp Σ :=
  (* For each export, if it is actually imported by the module (i.e. not newly allocated), then we should have the
     host vis points to the old location; otherwise it should point to the address as specified in one of the four
     address lists. 

     We implement the above by first construct the list of exports corresponding to all the entities in the module
     (i.e. imports + new declarations), then lookup from this list to find the correct export.

     Upd: This is now obsolete, since the instance directly gives the above knowledge.
*)(*
  let wf_exps := ((pmap (fun x => match x.(modexp_desc) with
                              | MED_func _ => Some x.(modexp_desc)
                              | _ => None
                              end) v_imps) ++ (map (fun addr => MED_func (Mk_funcidx addr)) inst.(inst_funcs))) in 
  let wt_exps := ((pmap (fun x => match x.(modexp_desc) with
                              | MED_table _ => Some x.(modexp_desc)
                              | _ => None
                               end) v_imps) ++ (map (fun addr => MED_table (Mk_tableidx addr)) inst.(inst_tab))) in
  let wm_exps := ((pmap (fun x => match x.(modexp_desc) with
                              | MED_mem _ => Some x.(modexp_desc)
                              | _ => None
                               end) v_imps) ++ (map (fun addr => MED_mem (Mk_memidx addr)) inst.(inst_memory))) in
  let wg_exps := ((pmap (fun x => match x.(modexp_desc) with
                              | MED_global _ => Some x.(modexp_desc)
                              | _ => None
                               end) v_imps) ++ (map (fun addr => MED_global (Mk_globalidx addr)) inst.(inst_globs))) in
  [∗ list] hs_exp; m_exp ∈ hs_exps; m_exps,
                                    ∃ name, hs_exp ↪[vis] Build_module_export name
                                                   (match m_exp.(modexp_desc) with
                                                   | MED_func (Mk_funcidx n) => nth n wf_exps exp_default
                                                   | MED_table (Mk_tableidx n) => nth n wt_exps exp_default
                                                   | MED_mem (Mk_memidx n) => nth n wm_exps exp_default
                                                   | MED_global (Mk_globalidx n) => nth n wg_exps exp_default
                                                   end
                                                     ).
*)
  [∗ list] hs_exp; m_exp ∈ hs_exps; m_exps,
                                    ∃ name, hs_exp ↪[vis] Build_module_export name
                                                   (match m_exp.(modexp_desc) with
                                                   | MED_func (Mk_funcidx n) => MED_func (Mk_funcidx (nth n inst.(inst_funcs) 0))
                                                   | MED_table (Mk_tableidx n) => MED_table (Mk_tableidx (nth n inst.(inst_tab) 0))
                                                   | MED_mem (Mk_memidx n) => MED_mem (Mk_memidx (nth n inst.(inst_memory) 0))
                                                   | MED_global (Mk_globalidx n) => MED_global (Mk_globalidx (nth n inst.(inst_globs) 0))
                                                   end
                                                     ).
Print instantiation.instantiate.

Print alloc_module.

Print module_export_desc.

Print ext_funcs.

Definition ext_func_addrs := (map (fun x => match x with | Mk_funcidx i => i end)) ∘ ext_funcs.
Definition ext_tab_addrs := (map (fun x => match x with | Mk_tableidx i => i end)) ∘ ext_tabs.
Definition ext_mem_addrs := (map (fun x => match x with | Mk_memidx i => i end)) ∘ ext_mems.
Definition ext_glob_addrs := (map (fun x => match x with | Mk_globalidx i => i end)) ∘ ext_globs.

Lemma instantiation_spec_operational (s: stuckness) E (hs_mod: N) (hs_imps: list vimp) (v_imps: list module_export) (hs_exps: list vi) (m: module) t_imps t_exps:
  module_typing m t_imps t_exps ->
  ∀ wfs wts wms wgs,
  hs_mod ↪[mods] m -∗
  import_resources_host hs_imps v_imps -∗
  import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
  export_ownership_host hs_exps -∗
  WP (([:: ID_instantiate hs_exps hs_mod hs_imps], [::]): host_expr) @ s; E
  {{ v, hs_mod ↪[mods] m ∗
        import_resources_host hs_imps v_imps ∗ (* vis, for the imports stored in host *)
        import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs ∗ (* locations in the wasm store and type-checks *)
        ∃ inst g_inits,
          ⌜ inst.(inst_types) = m.(mod_types) /\
          (* We know what the imported part of the instance must be. *)
          let v_imp_descs := map (fun mexp => mexp.(modexp_desc)) v_imps in
          prefix (ext_func_addrs v_imp_descs) inst.(inst_funcs) /\
          prefix (ext_tab_addrs v_imp_descs) inst.(inst_tab) /\
          prefix (ext_mem_addrs v_imp_descs) inst.(inst_memory) /\
          prefix (ext_glob_addrs v_imp_descs) inst.(inst_globs)
          ⌝ ∗
          module_inst_resources_wasm m inst g_inits ∗ (* allocated wasm resources. This also specifies the information about the newly allocated part of the instance. *)
          module_export_resources_host v_imps hs_exps m.(mod_exports) inst (* export resources, in the host store *)
          (* missing the constraints for the initialised globals. A wp (in wasm) for each of them in the future. Omitted
             for now since we can just forbid the initialization of globals anyway *)                                                                                      
  }}.
Proof.
  (*
  move => Hmodtype.
  iIntros "Hmod Himphost Himpwasm Hexphost".
  
  repeat rewrite weakestpre.wp_unfold /weakestpre.wp_pre /=.
  
  iIntros ([[ws vis] ms] ns κ κs nt) "Hσ".
  iDestruct "Hσ" as "(Hwf & Hwt & Hwm & Hwg & Hvis & Hms & Hframe & Hmsize & Htsize)".

  (* Reflecting the assertions back *)
  iDestruct (ghost_map_lookup with "Hms Hmod") as "%Hmod".
  unfold import_resources_host, big_opL.
  Print big_sepL2.
  unfold big_sepL2.
  Search big_sepL2.
  Print ghost_map_lookup.
  iDestruct (ghost_map_lookup with "Hvis Himphost") as "%Himphost".
  Search ghost_map_elem big_opM.
  Search big_opL big_opM.

  Search gmap list.
  
  iDestruct (ghost_map_lookup_big with "Hvis Himphost") as "%Himphost".

  (* The key is to prove that the instantiate predicate holds with the premises given. *)
  assert (exists ws_res inst_res v_exps ostart, (instantiate ws m v_imps ((ws_res, inst_res, v_exps), ostart))) as Hinst.
  {
    admit.
  }

  destruct Hinst as [[[[ws_res inst_res] v_exps] ostart] Hinst].
  
  iApply fupd_mask_intro; first by set_solver.

  iIntros "Hmask".
  iSplit.
  
  - destruct s => //.
    iPureIntro.
    unfold language.reducible.
      
    exists [], (([::], [::]): host_expr), (ws2,
                                    <[ 0 := [:: Build_module_export (list_byte_of_string "add") (MED_func (Mk_funcidx 0))]]>
                                    (<[ 1 := [:: Build_module_export (list_byte_of_string "f") (MED_func (Mk_funcidx 1))]]> vis) ,
                                    ms), [].
    unfold prim_step.
    repeat split => //.
    admit.
    (*
    eapply HR_host_step => //.
    by rewrite gmap_of_list_lookup in Hmods.
*)
        
  - iIntros ([hes' wes'] [[ws3 vis3] ms3] efs HStep).
    destruct HStep as [HStep [-> ->]].
    inversion HStep; subst; clear HStep.
    iIntros "!>!>!>".
    iMod "Hmask".
    iModIntro.
*)
Admitted.
  
End Instantiation_spec_operational.


(* Examples *)

Section Example_Add.

Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ}.
  
Definition Add_module :=
  Build_module
    (* Function types *) [:: (Tf [::T_i32; T_i32] [::T_i32]) ]
    (* Functions *) [:: Build_module_func
                       (* Type signature, referencing from the function type components *) (Mk_typeidx 0)
                       (* List of local variable types to be used -- none for the addition here *) [::]
                       (* Function body *) [:: BI_get_local 0; BI_get_local 1; BI_binop T_i32 (Binop_i BOI_add)]
                       ]
    (* Tables *) [::]
    (* Memories *) [::]
    (* Globals *) [::]
    (* Table initializers *) [::]
    (* Memory initializers *) [::]
    (* Start function *) None
    (* Imports *) [::]
    (* Exports *) [:: Build_module_export
                     (* export name *) (list_byte_of_string "add")
                     (* export description *) (MED_func (Mk_funcidx 0))
                     ].

Definition xx i := (VAL_int32 (Wasm_int.int_of_Z i32m i)).

Definition M2 :=
  Build_module
    (* Function types *) [:: (Tf [::T_i32; T_i32] [::T_i32]); (Tf [::] [::T_i32]) ]
    (* Functions *) [:: Build_module_func
                       (* Type signature, referencing from the function type components *) (Mk_typeidx 1)
                       (* List of local variable types to be used -- none for the addition here *) [::]
                       (* Function body *) [:: BI_const (xx 13); BI_const (xx 2); BI_call 0]
                       (* Note that the imports take precedence, i.e. the imported function is the 0th function, and
                          this function is the 1st function instead. *)
                       ]
    (* Tables *) [::]
    (* Memories *) [::]
    (* Globals *) [::]
    (* Table initializers *) [::]
    (* Memory initializers *) [::]
    (* Start function *) (* This would actually not work -- the start function must have an empty function type *)
                  (* (Some (Build_module_start (Mk_funcidx 1))) *)
                  None
    (* Imports *) [:: Build_module_import
                     (* import module name (superfluous) *) (list_byte_of_string "Add_module")
                     (* import function name (superfluous) *) (list_byte_of_string "add")
                     (* import type description *) (ID_func 0)
                     ]
    (* Exports *) [:: Build_module_export
                     (* export name *) (list_byte_of_string "f")
                     (* export description *) (MED_func (Mk_funcidx 1))
                     ].

Definition module_decls := [:: Add_module; M2].

Definition add_program_instantiate :=
  [:: ID_instantiate [::0%N] 0 [::];
  (* The above exports the function 'add' to the 0th vi store of the host, which contains a list of exports consisting of
     only one function -- the add function. *)
  ID_instantiate [::1%N] 1 [:: 0%N]].
  





(* verify that both modules are well-typed *)
Lemma add_module_valid: module_typing Add_module [::] [:: ET_func (Tf [::T_i32; T_i32] [::T_i32])].
Proof.
  unfold module_typing.
  (* We have to provide the type of each function and each global in the instantiate module. *)
  exists [Tf [::T_i32; T_i32] [::T_i32]], [::].
  simpl.
  (* Most of the components of the module are empty and can be resolved trivially. *)
  repeat split; (try by apply Forall2_nil); (try by apply Forall_nil).
  - (* module_func_typing *)
    constructor; last by apply Forall2_nil.
    unfold module_func_typing.
    repeat split => //=.
    (* be_typing of the function body *)
    eapply bet_composition_front; first by apply bet_get_local => //.
    eapply bet_composition_front with (t2s := [T_i32; T_i32]).
    + replace [T_i32; T_i32] with ([T_i32] ++ [T_i32]) => //.
      apply bet_weakening_empty_1.
      by apply bet_get_local.
    + apply bet_binop.
      by constructor.
  - (* module_export_typing *)
    constructor; last by apply Forall2_nil.
    by unfold module_export_typing => /=.
Qed.


Lemma M2_valid: module_typing M2 [:: ET_func (Tf [::T_i32; T_i32] [::T_i32])] [:: ET_func (Tf [::] [::T_i32])].
Proof.
  unfold module_typing.
  exists [::Tf [::] [::T_i32]], [::].
  simpl.
  repeat split; (try by apply Forall2_nil); (try by apply Forall_nil).
  - (* module_func_typing *)
    constructor; last by apply Forall2_nil.
    unfold module_func_typing.
    repeat split => //=.
    (* be_typing of the function body *)
    eapply bet_composition_front; first by apply bet_const => //.
    eapply bet_composition_front with (t2s := [T_i32; T_i32]) => /=.
    + replace [T_i32; T_i32] with ([T_i32] ++ [T_i32]) => //.
      apply bet_weakening_empty_1.
      by apply bet_const.
    + by apply bet_call => //.
  - (* module_import_typing *)
    unfold module_import_typing => /=.
    by constructor => //. 
  - (* module_export_typing *)
    constructor; last by apply Forall2_nil.
    by unfold module_export_typing => /=.    
Qed.


Lemma add_instantiate_spec (s: stuckness) E hv:
  0%N ↪[mods] Add_module -∗
  0%N ↪[vis] hv -∗
  WP (([::ID_instantiate [::0%N] 0 [::]], [::]): host_expr) @ s; E
      {{ v, 0%N ↪[mods] Add_module ∗
             ∃ idf name,
               0%N ↪[vis] {| modexp_name := name; modexp_desc := (MED_func (Mk_funcidx idf)) |} ∗
                    N.of_nat idf ↦[wf] (FC_func_native
                                          (Build_instance [::Tf [::T_i32; T_i32] [::T_i32]] [::idf] [::] [::] [::])
                                          (Tf [::T_i32; T_i32] [::T_i32]) (* Function type *)
                                          [::] (* list of local variable types to be created -- none *)
                                          [BI_get_local 0; BI_get_local 1; BI_binop T_i32 (Binop_i BOI_add)])
      }}.
Proof.
  iIntros "Hmod Hhv".
  iApply weakestpre.wp_mono; last first.
  iApply (instantiation_spec_operational with "[$]") => //.
  - by apply add_module_valid.
  - by unfold import_resources_host => //.
  - do 4 instantiate (1 := ∅). by unfold import_resources_wasm_typecheck => //.
  - unfold export_ownership_host => /=.
    iSplit => //.
    by iExists hv.
  - iIntros (v) "H".
    iDestruct "H" as "(Hmod & Himphost & Himpwasm & Hinst)".
    iDestruct "Hinst" as (inst g_inits) "(%Hinst & Hexpwasm & Hexphost)".

    destruct Hinst as [Hinsttype [Hinstfunc [Hinsttab [Hinstmem Hinstglob]]]].
    
    (* Extract the resources from the post of the instantiation lemma *)
    unfold module_inst_resources_wasm, module_export_resources_host => /=.
    
    destruct inst => /=.
    
    (* Extracting the allocated wasm resources *)

    iDestruct "Hexpwasm" as "(Hexpwf & Hexpwt & Hexpwm & Hexpwg)".
    
    unfold module_inst_resources_func, module_inst_resources_tab, module_inst_resources_mem, module_inst_resources_glob => /=.
    unfold big_sepL2 => /=.

    (* functions *)
    destruct inst_funcs as [|n inst_funcs] => //=.
    iDestruct "Hexpwf" as "(Hwfcl & Hexpwf)".
    destruct inst_funcs => //=.

    (* tables *)
    destruct inst_tab => //=.

    (* memories *)
    destruct inst_memory => //=.

    (* globals *)
    destruct inst_globs => //=.

    

    (* Extracting the exported function indices in host. Note that we've lost the export name, but it's superfluous anyway *)
    iDestruct "Hexphost" as "(Hexphost & ?)".
    iDestruct "Hexphost" as (name) "Hexphost" => /=.

    simpl in *; subst.
    iFrame.
    iExists n, name.
    by iFrame.
Qed.

Lemma M2_instantiate_spec (s: stuckness) E hv expname0 n cl:
  (* Note that we don't require to know the exact body of the import -- the only important thing is that its type matches. *)
  cl_type cl = (Tf [::T_i32; T_i32] [::T_i32]) ->
  1%N ↪[mods] M2 -∗
  0%N ↪[vis] {| modexp_name := expname0; modexp_desc := MED_func (Mk_funcidx n) |} -∗
  N.of_nat n ↦[wf] cl -∗
  1%N ↪[vis] hv -∗
  WP (([::ID_instantiate [::1%N] 1 [::0%N]], [::]): host_expr) @ s; E
      {{ v,  1%N ↪[mods] M2 ∗
             0%N ↪[vis] {| modexp_name := expname0; modexp_desc := MED_func (Mk_funcidx n) |} ∗
             N.of_nat n ↦[wf] cl ∗
             ∃ idf name,
               1%N ↪[vis] {| modexp_name := name; modexp_desc := (MED_func (Mk_funcidx idf)) |} ∗
                    N.of_nat idf ↦[wf] (FC_func_native
                                          (Build_instance [::Tf [::T_i32; T_i32] [::T_i32]; Tf [::] [::T_i32]] [::n; idf] [::] [::] [::])
                                          (Tf [::] [::T_i32]) 
                                          [::] 
                                          [BI_const (xx 13); BI_const (xx 2); BI_call 0])
      }}.
Proof.
  move => Hcltype.
  iIntros "Hmod Hvimp Hwfcl Hhv".
  iApply weakestpre.wp_mono; last first.
  iApply (instantiation_spec_operational with "[$] [Hvimp] [Hwfcl] [Hhv] ") => //.
  - by apply M2_valid.
  - unfold import_resources_host.
    unfold big_sepL2.
    instantiate (1 := [::{| modexp_name := expname0; modexp_desc := MED_func (Mk_funcidx n) |}]) => /=.
    by iFrame.
  - do 3 instantiate (1 := ∅).
    instantiate (1 := <[ n := cl ]> ∅).
    unfold import_resources_wasm_typecheck => /=.
    iSplit => //.
    iExists cl.
    iFrame.
    iPureIntro.
    rewrite lookup_insert.
    split => //.
    by rewrite Hcltype.
  - unfold export_ownership_host => /=.
    iSplit => //.
    by iExists hv.
  - iIntros (v) "H".
    iDestruct "H" as "(Hmod & Himphost & Himpwasm & Hinst)".
    iDestruct "Hinst" as (inst g_inits) "(%Hinst & Hexpwasm & Hexphost)".
    
    destruct Hinst as [Hinsttype [Hinstfunc [Hinsttab [Hinstmem Hinstglob]]]].
    
    (* Extract the resources from the post of the instantiation lemma *)
    unfold module_inst_resources_wasm, module_export_resources_host => /=.
    
    destruct inst => /=.
    
    (* Extracting the allocated wasm resources *)

    iDestruct "Hexpwasm" as "(Hexpwf & Hexpwt & Hexpwm & Hexpwg)".
    
    unfold module_inst_resources_func, module_inst_resources_tab, module_inst_resources_mem, module_inst_resources_glob => /=.
    unfold big_sepL2 => /=.

    (* functions *)
    destruct inst_funcs as [|k inst_funcs] => //=.
    rewrite drop_0.
    destruct inst_funcs => //=.
    iDestruct "Hexpwf" as "(Hwfcl & Hexpwf)".
    destruct inst_funcs => //=.

    (* tables *)
    destruct inst_tab => //=.

    (* memories *)
    destruct inst_memory => //=.

    (* globals *)
    destruct inst_globs => //=.

    

    (* Extracting the exported function indices in host. Note that we've lost the export name, but it's superfluous anyway *)
    iDestruct "Hexphost" as "(Hexphost & ?)".
    iDestruct "Hexphost" as (name) "Hexphost" => /=.

    (* Extracting the imported resources in the host *)
    unfold import_resources_host => /=.
    iDestruct "Himphost" as "(Himphost & _)".

    (* Extracting the imported resources in Wasm *)
    unfold import_resources_wasm_typecheck => /=.
    iDestruct "Himpwasm" as "(Himpwasm & _)".
    iDestruct "Himpwasm" as (cl0) "(Hwfcl0 & %Hcltype0)" => /=.
    rewrite lookup_insert in Hcltype0.
    destruct Hcltype0 as [Hcl _].
    inversion Hcl; subst; clear Hcl.
    
    simpl in *; subst.
    unfold ext_func_addrs in Hinstfunc => /=.
    simpl in Hinstfunc.
    unfold prefix in Hinstfunc.
    destruct Hinstfunc as [l Hinstfunc].
    repeat destruct l => //=.
    inversion Hinstfunc; subst; clear Hinstfunc.
    
    iFrame.
    iExists n0, name.
    iFrame.

Qed.

(* Demonstrating that we have the correct resources after instantiating two modules in sequence. *)
Lemma add_program_instantiate_spec (s: stuckness) E hv0 hv1:
  0%N ↪[mods] Add_module -∗
  1%N ↪[mods] M2 -∗
  0%N ↪[vis] hv0 -∗
  1%N ↪[vis] hv1 -∗
  WP ((add_program_instantiate, [::]): host_expr) @ s; E {{ v,
             0%N ↪[mods] Add_module ∗
             1%N ↪[mods] M2 ∗
             ∃ idf0 idf1 name0 name1,
             0%N ↪[vis] {| modexp_name := name0; modexp_desc := (MED_func (Mk_funcidx idf0)) |} ∗
             1%N ↪[vis] {| modexp_name := name1; modexp_desc := (MED_func (Mk_funcidx idf1)) |} ∗
             N.of_nat idf0 ↦[wf] (FC_func_native
                                          (Build_instance [::Tf [::T_i32; T_i32] [::T_i32]] [::idf0] [::] [::] [::])
                                          (Tf [::T_i32; T_i32] [::T_i32]) (* Function type *)
                                          [::] (* list of local variable types to be created -- none *)
                                          [BI_get_local 0; BI_get_local 1; BI_binop T_i32 (Binop_i BOI_add)]) ∗
             N.of_nat idf1 ↦[wf] (FC_func_native
                                          (Build_instance [::Tf [::T_i32; T_i32] [::T_i32]; Tf [::] [::T_i32]] [::idf0; idf1] [::] [::] [::])
                                          (Tf [::] [::T_i32]) 
                                          [::] 
                                          [BI_const (xx 13); BI_const (xx 2); BI_call 0]) }}.
Proof.
  iIntros "Hmod0 Hmod1 Hvis0 Hvis1".
  iApply (wp_seq_host_nostart with "[$Hmod0] [Hvis0]") => //.
  - iIntros "Hmod0".
    iApply weakestpre.wp_mono; last by iApply (add_instantiate_spec with "[$]").
    iIntros (v) "(?&H)".
    iFrame.
    by iApply "H".
  - iIntros (w) "Hes1 Hmod0".
    iDestruct "Hes1" as (idf0 name0) "(Hvis0 & Hwf0)".
    iFrame "Hmod0".
    iApply weakestpre.wp_mono; last by iApply (M2_instantiate_spec with "[$] [$] [$]") => //=.
    
    iIntros (v) "Hes2".
    iDestruct "Hes2" as "(Hmod1 & Hvis0 & Hwf0 & Hes2)".
    iDestruct "Hes2" as (idf1 name1) "(Hvis1 & Hwf1)".
    iFrame.
    iExists idf0, idf1, name0, name1.
    iFrame.
Qed.


(* ***************** END OF EXAMPLES ********************* *)


Print instantiation.instantiate.
Print module_export.
Print module_export_desc.

Print Build_instance.
Print funcaddr.

Print function_closure.

Print instance.

Lemma Add_module_instantiate_spec ws n inst ws':
  length (ws.(s_funcs)) = n ->
  inst = Build_instance [::Tf [::T_i32; T_i32] [::T_i32]] [::(* wait... this is 1-indexed ???? *)n] [::] [::] [::] ->
  ws' = (Build_store_record
            (ws.(s_funcs) ++ [::FC_func_native
                                       inst 
                                       (Tf [::T_i32; T_i32] [::T_i32]) (* Function type *)
                                       [::] (* list of local variable types to be created -- none *)
                                       [BI_get_local 0; BI_get_local 1; BI_binop T_i32 (Binop_i BOI_add)]])
            ws.(s_tables)
            ws.(s_mems)
            ws.(s_globals)) ->
  instantiate ws Add_module [::]
              (
                ws',
                inst,
                [:: Build_module_export (list_byte_of_string "add") (MED_func (Mk_funcidx (n)))],
                (None: option nat)
              ).
Proof.
  move => Hfunclen Hinst Hstore.
  unfold instantiate, instantiation.instantiate.
  
  (* Types of imports and exports. This might be useful to craft a 'spec for a module' *)
  exists [::], [::ET_func (Tf [::T_i32; T_i32] [::T_i32])].
  exists hs. (* updated host state... but our host is built on dummyhost -- so this should really be just a dummy *)
  exists ws'.
  exists [::], [::], [::]. (* all of these should be empty *)
  
  repeat split; (try by apply Forall2_nil); (try by apply Forall_nil).
  - (* module_typing of the module, proved above *)
    by apply add_module_valid.
  - (* alloc_module *)
    unfold alloc_module => /=.
    repeat (apply/andP; split => //; try by rewrite Hinst).
    rewrite Hinst Hstore => /=.
    apply/eqP.
    f_equal.
    rewrite app_length.
    by rewrite Hfunclen.
  - (* This seems to be a recursive check that our store is containing the correct memories and tables -- but how
       are these working exactly when we actually have some non-empty memories/tables? *)
    simpl.
    (* potential bug in instantiation *)
    unfold init_mems => /=.
    unfold init_tabs => /=.
    by apply/eqP.    
Qed.



Lemma M2_instantiate_spec ws n inst ws' k:
  k < n ->
  length (ws.(s_funcs)) = n ->
  (* So the instance has to contain imported functions as well *)
  inst = Build_instance [::Tf [::T_i32; T_i32] [::T_i32]; Tf [::] [::T_i32]] [::k; n+1] [::] [::] [::] ->
  nth_error ws.(s_funcs) k = Some (FC_func_native
                                       inst (* redundant instance?? *)
                                       (Tf [::T_i32; T_i32] [::T_i32]) (* Function type *)
                                       [::] (* list of local variable types to be created -- none *)
                                       [BI_get_local 0; BI_get_local 1; BI_binop T_i32 (Binop_i BOI_add)]) ->
  ws' = (Build_store_record
            (ws.(s_funcs) ++ [::FC_func_native
                                       inst 
                                       (Tf [::] [::T_i32]) 
                                       [::] 
                                       [ BI_const (xx 13); BI_const (xx 2); BI_call 0]])
            ws.(s_tables)
            ws.(s_mems)
            ws.(s_globals)) ->
  instantiate ws M2 [::MED_func (Mk_funcidx k)]
              (
                ws',
                inst,
                [:: Build_module_export (list_byte_of_string "f") (MED_func (Mk_funcidx (n+1)))],
                (None: option nat)
              ).
Proof.
  move => Hindexsize Hfunclen Hinst Hfuncimport Hstore.
  unfold instantiate, instantiation.instantiate.
  
  exists [::ET_func (Tf [::T_i32; T_i32] [::T_i32])], [::ET_func (Tf [::] [::T_i32])], hs, ws', [::], [::], [::].
  
  repeat split; (try by apply Forall2_nil); (try by apply Forall_nil).
  - (* module_typing of the module, proved above *)
    by apply M2_valid.
  - (* external_typing *)
    constructor => //.
    econstructor => //.
    by lias.
  - (* alloc_module *)
    unfold alloc_module => /=.
    repeat (apply/andP; split => //; try by rewrite Hinst).
    rewrite Hinst Hstore => /=.
    apply/eqP.
    repeat f_equal.
    rewrite app_length.
    by rewrite Hfunclen.
  - simpl.
    unfold init_mems => /=.
    unfold init_tabs => /=.
    by apply/eqP.    
Qed.

(* Currently only states what are the exports we're getting instead of what the specs are.  *)
Lemma example_add_spec (s: stuckness) E:
  (* Module declaration resources *)
  0%N ↪[mods] Add_module -∗
  1%N ↪[mods] M2 -∗
  (* original vis resources -- this is required since the instantiation updates these two entries *)
  0 ↪[vis] ([::]: list module_export) -∗
  1 ↪[vis] ([::]: list module_export) -∗
  WP ((add_program_instantiate, [::]): host_expr) @ s; E
           {{ v, ⌜ v = immV [::] ⌝ ∗
                   0%N ↪[mods] Add_module ∗
                   1%N ↪[mods] M2 ∗
                   (* It now really seems that this exported funcid is a reference to the location in the store *)
                   0 ↪[vis] [:: Build_module_export (list_byte_of_string "add") (MED_func (Mk_funcidx 0))] ∗
                   1 ↪[vis] [:: Build_module_export (list_byte_of_string "f") (MED_func (Mk_funcidx 1))] ∗
                   (∃ k inst1 inst2, k ↪[wf] (FC_func_native
                                     inst1
                                     (Tf [::T_i32; T_i32] [::T_i32]) (* Function type *)
                                     [::] (* list of local variable types to be created -- none *)
                                     [BI_get_local 0; BI_get_local 1; BI_binop T_i32 (Binop_i BOI_add)]) ∗
                   k+1 ↪[wf] (FC_func_native
                                       inst2 
                                       (Tf [::] [::T_i32]) 
                                       [::] 
                                       [ BI_const (xx 13); BI_const (xx 2); BI_call 0]))
           }}.
Proof.
  iIntros "Hmod1 Hmod2 Hmodexp1 Hmodexp2".
  repeat rewrite weakestpre.wp_unfold /weakestpre.wp_pre /=.
  
  iIntros ([[ws vis] ms] ns κ κs nt) "Hσ".
  iDestruct "Hσ" as "(Hwf & Hwt & Hwm & Hwg & Hvis & Hms & Hframe & Hmsize)".
  iDestruct (ghost_map_lookup with "Hms Hmod1") as "%Hmod1".
  iDestruct (ghost_map_lookup with "Hms Hmod2") as "%Hmod2".
  iDestruct (ghost_map_lookup with "Hvis Hmodexp1") as "%Hmodexp1".
  iDestruct (ghost_map_lookup with "Hvis Hmodexp2") as "%Hmodexp2".

  remember (length ws.(s_funcs)) as wflen.
  remember (Build_instance [::Tf [::T_i32; T_i32] [::T_i32]] [::wflen + 1] [::] [::] [::]) as inst1.
  remember (Build_store_record
            (ws.(s_funcs) ++ [::FC_func_native
                                       inst1
                                       (Tf [::T_i32; T_i32] [::T_i32]) 
                                       [::] 
                                       [BI_get_local 0; BI_get_local 1; BI_binop T_i32 (Binop_i BOI_add)]])
            ws.(s_tables)
            ws.(s_mems)
            ws.(s_globals)) as ws1.
  
  specialize (Add_module_instantiate_spec ws wflen inst1 ws1) as Hinstantiate1.
  

  remember (Build_instance [::Tf [::T_i32; T_i32] [::T_i32]; Tf [::] [::T_i32]] [::wflen; wflen+1] [::] [::] [::]) as inst2.
  remember (Build_store_record
            (ws.(s_funcs) ++ [::FC_func_native
                                       inst2
                                       (Tf [::] [::T_i32]) 
                                       [::] 
                                       [ BI_const (xx 13); BI_const (xx 2); BI_call 0]])
            ws.(s_tables)
            ws.(s_mems)
            ws.(s_globals)) as ws2.
  
  specialize (M2_instantiate_spec ws1 (wflen+1) inst2 ws2 (wflen)) as Hinstantiate2.

  iApply fupd_mask_intro; first by set_solver.

  iIntros "Hmask".
  iSplit.
  
  - destruct s => //.
    iPureIntro.
    unfold language.reducible.
      
    exists [], (([::], [::]): host_expr), (ws2,
                                    <[ 0 := [:: Build_module_export (list_byte_of_string "add") (MED_func (Mk_funcidx 0))]]>
                                    (<[ 1 := [:: Build_module_export (list_byte_of_string "f") (MED_func (Mk_funcidx 1))]]> vis) ,
                                    ms), [].
    unfold prim_step.
    repeat split => //.
    admit.
    (*
    eapply HR_host_step => //.
    by rewrite gmap_of_list_lookup in Hmods.
*)
        
  - iIntros ([hes' wes'] [[ws3 vis3] ms3] efs HStep).
    destruct HStep as [HStep [-> ->]].
    inversion HStep; subst; clear HStep.
    iIntros "!>!>!>".
    iMod "Hmask".
    iModIntro.
    (* It's probably a bad idea to iFrame now... *)
    (*
    iFrame.
*)
      (*
      iSpecialize ("Hwp" $! wes' (hs', ws2, [::], empty_instance) [::] with "[%]"); first by unfold iris.prim_step.
      iMod "Hwp".
      do 2 iModIntro.
      iFrame.
      iSplit => //.
      iApply "IH"; first by apply hwev_reduce_closed in H0.
      iApply "Hwp".
      by iApply "Hf".
*)
Admitted.



End Example_Add.



Definition build_module_one_func (ft: function_type) (bes: expr) :=
  Build_module [:: ft] [:: (Build_module_func (Mk_typeidx 0) [::] bes)] [] [] [] [] [] (Some (Build_module_start (Mk_funcidx 0))) [] [].

Print module_typing.

Print module_func_typing.

Print module_func.

Print typeidx.

(*
Section Host_wp_import.
  (* Host wp must depend on the same memory model as for wasm *)
  Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

  Record host_program_logic := {
      wp_host (s : stuckness) : coPset -d> host_function -d> seq.seq value -d> (result -d> iPropO Σ) -d> iPropO Σ;
      wp_host_not_stuck : (forall σ ns κs nt Φ h E vcs t1s t2s a, (let '(hs,s,_,_) := σ in
                                              s_funcs s !! a = Some (FC_func_host (Tf t1s t2s) h)) ->
                                              state_interp σ ns κs nt -∗
                                              wp_host NotStuck E h vcs Φ ={E}=∗
                                              state_interp σ ns κs nt ∗ wp_host NotStuck E h vcs Φ ∗
                                              ⌜(let '(hs,s,_,_) := σ in (∃ hs' s' r, host_application hs s (Tf t1s t2s) h vcs hs' (Some (s',r))) ∨
                                               (∃ hs', host_application hs s (Tf t1s t2s) h vcs hs' None))⌝);
      wp_host_step_red : (∀ σ ns κ κs nt Φ h E vcs t1s t2s, (
                                                               
                                              state_interp σ ns (κ ++ κs) nt -∗
                                              wp_host NotStuck E h vcs Φ ={E,∅}=∗
                                              (∀ σ' r, ⌜(let '(hs,s,_,_) := σ in let '(hs',s',_,_) := σ' in host_application hs s (Tf t1s t2s) h vcs hs' (Some (s',r)))⌝
                                              ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
                                                 state_interp σ' (S ns) κs nt ∗ Φ r) ∗
                                              (∀ σ', ⌜(let '(hs,s,_,_) := σ in let '(hs',_,_,_) := σ' in host_application hs s (Tf t1s t2s) h vcs hs' None)⌝
                                              ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
                                                 state_interp σ' (S ns) κs nt ∗ wp_host NotStuck E h vcs Φ)));
    }.
  
End Host_wp_import.
 *)


(*
| HR_host_step: forall s vis m vi vm vimps imps s' vis' ms idecs' inst exps start vs,
    ms !! vm = Some m ->
    those ((lookup_export_vi vis) <$> vimps) = Some imps ->
    instantiate s m imps ((s', inst, exps), start) ->
    const_list vs ->
    vis' = <[ vi := exps ]> vis ->
    host_reduce (s, vis, ms, (ID_instantiate vi vm vimps) :: idecs', vs) (s', vis', ms, idecs', map_start start)
 *)
Lemma wp_host_inst_func_only (s: stuckness) E (bes: expr) (Φ: iris.val -> iProp Σ) (m: module) (ft: function_type) (es: expr) (impts expts : list extern_t) q:
  m = build_module_one_func ft es ->
  module_typing m impts expts ->
  WP ((to_e_list bes): iris.expr) @ s; E {{ Φ }} -∗
  (ghost_map_elem msGName 0%N q m)%I -∗
  (* Instantiating the 0th module and store exports (None) in the 0th resource should result in the expression containing
     the resulting value of the function body of the start function, with an empty resource generated at the 0th location *)
  WP (([::ID_instantiate 0 0 [::]], [::]): host_expr) @ s; E {{ v, Φ v ∗ (ghost_map_elem visGName 0 (DfracOwn 1) ([::]: list module_export)) }}.
Proof.
  move => Hmodule Hmoduletype.
  iIntros "Hwp Hmods".
  repeat rewrite weakestpre.wp_unfold /weakestpre.wp_pre /=.
  repeat rewrite wp_unfold /wp_pre /=.
  
  iIntros ([[ws vis] ms] ns κ κs nt) "Hσ".
  iDestruct "Hσ" as "(Hwf & Hwt & Hwm & Hwg & Hvis & Hms & Hframe & Hmsize)".
  iDestruct (ghost_map_lookup with "Hms Hmods") as "%Hmods".
  
  assert (exists s' inst, (instantiate ws m [::] ((s', inst, [::]), (Some 0)))) as [ws' Hinst].
  {
    (*
    destruct ws.
    exists Build_store_record (s.(s_funcs) ++ (Build_module_func (Mk_typeidx 0) [::] bes)) s.(s_tables) s.(s_mems) s.(s_globals).
    repeat split; unfold all2.*)
    admit.
  }
  destruct Hinst as [inst Hinstantiate].
  destruct (iris.to_val (to_e_list bes)) eqn: Hes => //.
  - (* Can a function body be consisted of only a list of consts? *)
    iMod "Hwp".
    iApply fupd_mask_intro; first by set_solver.
    iIntros "Hmask".
    iSplit.
    + iPureIntro.
      destruct s => //.
      econstructor.
      Search ID_instantiate.
      exists ([],map_start (Some 0)), (ws', <[0:=[]]> vis, ms), [].
      constructor => //.
      eapply HR_host_step => //; by rewrite gmap_of_list_lookup in Hmods.
    + iIntros (e2 σ2 efs HStep) "!>!>!>".
      iMod "Hmask".
      iModIntro.
      destruct σ2 as [[ws2 vis2] ms2].
      destruct e2 as [he2 we2].
      destruct HStep as [HStep [-> ->]].
      inversion HStep; subst; last by apply empty_no_reduce in H0.
      (* It appears that we need more resources in the precondition, so as to update the wasm store at this point. *)
      admit.
      
  - iSpecialize ("Hwp" $! (hs, ws, [::], empty_instance) ns κ κs nt).
    iSpecialize ("Hwp" with "[$]").
    iMod "Hwp" as "(%Hred & Hwp)".
    iModIntro.
    iSplit.
    
    + destruct s => //.
      iPureIntro.
      unfold language.reducible.
      
      exists [], (([::], [AI_invoke 0]): host_expr), (ws', <[ 0 := [::] ]> vis , ms), [].
      unfold prim_step => /=.
      repeat split => //.
      replace [AI_invoke 0] with (map_start (Some 0)); last trivial.
      eapply HR_host_step => //.
      by rewrite gmap_of_list_lookup in Hmods.
        
    + iIntros ([hes' wes'] [[ws2 vis2] ms2] efs HStep).
      destruct HStep as [HStep [-> ->]].
      inversion HStep; subst; clear HStep.
      (* Latter case is impossible *)
      (*
      iSpecialize ("Hwp" $! wes' (hs', ws2, [::], empty_instance) [::] with "[%]"); first by unfold iris.prim_step.
      iMod "Hwp".
      do 2 iModIntro.
      iMod "Hwp".
      iModIntro.
      iMod "Hwp".
      iModIntro.
      iDestruct "Hwp" as "((Hwf & Hwt & Hwm & Hwg & Hwframe & Hmsize) & Hwp)".
      iDestruct "Hwp" as (f) "(Hf & Hwp & ?)".
      iFrame.
      iSplit => //.
      iApply "IH"; first by apply hwev_reduce_closed in H0.
      iApply "Hwp".
      by iApply "Hf".
*)
Admitted.
      



                   

End Iris_host.
