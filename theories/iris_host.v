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
Definition vi := nat.

(* variable instantiation store *)
Definition vi_store := gmap vi (list module_export).

Definition module_decl := module.

(* an import is specified by giving the index of the instance to the module_export and a name given by the string *)
Definition vimp : Type := vi * (seq.seq Byte.byte).

(* There is only one instance declaration instruction: instantiating a module.
   ID_instantiate vi vm vimps is supposed to instantiate the module vmth module
   in the program state, taking imports as specified by each of the vimps, 
   and store the list of exports in the vi_store for future use.
 *)
Inductive inst_decl: Type :=
  ID_instantiate: vi -> nat -> list vimp -> inst_decl.

Definition host_config : Type := store_record * vi_store * (list module) * (list inst_decl) * (list administrative_instruction).

Definition instantiate := instantiate host_function host_instance.

(* Does the start function always take 0 arguments? *)
Definition map_start (start: option nat) : list administrative_instruction :=
  match start with
  | Some n => [AI_invoke n]
  | None => []
  end.

Fixpoint lookup_export vexts name : option module_export_desc :=
  match vexts with
  | [] => None
  | e :: vexts' => if e.(modexp_name) == name then Some e.(modexp_desc)
                                            else lookup_export vexts' name
  end.

Definition lookup_export_vi (vis: vi_store) (vimp: vimp) : option module_export_desc :=
  let (vi, vname) := vimp in
  match vis !! vi with
  | Some vexts => lookup_export vexts vname
  | None => None
  end.

Definition empty_instance := Build_instance [::] [::] [::] [::] [::].
Definition empty_frame := Build_frame [::] empty_instance.

(* Dummy *)
Parameter hs: host_state host_instance.

Inductive host_reduce: host_config -> host_config -> Prop :=
| HR_host_step: forall s vis m vi vm vimps imps s' vis' ms idecs' inst exps start vs,
    ms !! vm = Some m ->
    those ((lookup_export_vi vis) <$> vimps) = Some imps ->
    instantiate s m imps ((s', inst, exps), start) ->
    const_list vs ->
    vis' = <[ vi := exps ]> vis ->
    host_reduce (s, vis, ms, (ID_instantiate vi vm vimps) :: idecs', vs) (s', vis', ms, idecs', map_start start)
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
  destruct 0 => //; move:l; elim => //=; move => ? ? IH; by rewrite IH => //.
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

(*
Class wfuncG Σ := WFuncG {
  func_invG :> invGS Σ;
  func_gen_hsG :> gen_heapGS N function_closure Σ;
}.

Class wtabG Σ := WTabG {
  tab_gen_hsG :> gen_heapGS (N*N) funcelem Σ;
}.

Class wmemG Σ := WMemG {
  mem_gen_hsG :> gen_heapGS (N*N) byte Σ;
}.

Class wmemsizeG Σ := WMemsizeG {
  memsize_gen_hsG :> gen_heapGS N N Σ;
}.

Class wglobG Σ := WGlobG {
  glob_gen_hsG :> gen_heapGS N global Σ;
}.

Class wframeG Σ := WFrameG {
  locs_gen_hsG :> ghost_mapG Σ unit frame;
}.
*)
Require Export iris_wp_def.

(* The host expands the memory model of Wasm by vi_store and a list of module declarations. *)

Class hvisG Σ := HVisG {
  vis_genG :> ghost_mapG Σ nat (list module_export)
}.

Class hmsG Σ := HMsG {
  ms_genG :> ghost_mapG Σ N module
}.



Definition frameGName : positive := 10%positive.
Definition visGName : positive := 11%positive.
Definition msGName : positive := 12%positive.

Definition proph_id := positive. (* ??? *)

Instance eqdecision_frame: EqDecision frame.
Proof. decidable_equality. Qed.

Instance eqdecision_module: EqDecision module.
Proof. move => m m'. unfold Decision. by decidable_equality. Qed.

Global Instance host_heapG_irisG `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ} : weakestpre.irisGS wasm_host_lang Σ := {
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
      (gen_heap_interp (gmap_of_list (fmap mem_length s.(s_mems))))
    )%I;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
}.




Section host_lifting.
Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ}.


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
  - by apply values_no_reduce in Hred.
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
  iDestruct "Hσ" as "(Hwf & Hwt & Hwm & Hwg & Hvis & Hms & Hframe & Hmsize)".
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
    iDestruct "Hwp" as "((Hwf & Hwt & Hwm & Hwg & Hwframe & Hmsize) & Hwp)".
    iDestruct "Hwp" as (f) "(Hf & Hwp & ?)".
    iFrame.
    iSplit => //.
    iApply "IH"; first by apply hwev_reduce_closed in H0.
    iApply "Hwp".
    by iApply "Hf".
Qed.
  
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

  End host_lifting.


End Iris_host.
