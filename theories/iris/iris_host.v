From mathcomp Require Import ssreflect eqtype seq ssrbool ssrfun.
From iris.program_logic Require Import language weakestpre lifting.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
(* From iris.bi Require Export weakestpre. *)
Require Export iris_locations iris_properties iris_rules_resources iris_wp_def stdpp_aux iris.
Require Export datatypes host operations properties opsem instantiation.
(* We need a few helper lemmas from preservation. *)
Require Export type_preservation.

Close Scope byte.

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

Print check_bounds_elem.

Print module_elem_typing.

Print module_element.

Print module_typing.

Print s_tables.

Print tableinst.

Definition assert_const1 (es: expr) : option value :=
  match es with
  | [:: BI_const v] => Some v
  | _ => None
  end.

Definition assert_const1_i32 (es: expr) : option i32 :=
  match es with
  | [:: BI_const (VAL_int32 v)] => Some v
  | _ => None
  end.

Definition assert_const1_i32_to_nat (es:expr) : nat :=
  match assert_const1_i32 es with
  | Some v => nat_of_int v
  | _ => 0
  end.

Definition module_elem_bound_check_gmap (wts: gmap N tableinst) (imp_descs: list module_export_desc) (m: module) :=
  Forall (fun '{| modelem_table := (Mk_tableidx n);
                modelem_offset := eoff;
                modelem_init := fids |} =>
            match assert_const1_i32 eoff with
            | Some eoffi =>
              match (ext_tabs imp_descs) !! n with
              | Some (Mk_tableidx k) =>
                match wts !! (N.of_nat k) with
                | Some ti => nat_of_int eoffi + length fids <= length ti.(table_data)
                | None => False
                end
              | _ => 
                match (m.(mod_tables) !! (n - length (ext_tabs imp_descs))) with
                | Some modtab => (N.of_nat (nat_of_int eoffi + length fids) <= modtab.(modtab_type).(tt_limits).(lim_min))%N
                | None => False
                end
              end
            | None => False
              end
      ) m.(mod_elem).

Definition module_data_bound_check_gmap (wms: gmap N memory) (imp_descs: list module_export_desc) (m: module) :=
  Forall (fun '{| moddata_data := (Mk_memidx n);
                moddata_offset := doff;
                moddata_init := bs |} =>
            match assert_const1_i32 doff with
            | Some doffi =>
              match (ext_mems imp_descs) !! n with
              | Some (Mk_memidx k) =>
                match wms !! (N.of_nat k) with
                | Some mi => (N.of_nat (nat_of_int doffi + length bs) <= mem_length mi)%N
                | None => False
                end
              | _ => 
                match (m.(mod_mems) !! (n - length (ext_mems imp_descs))) with
                | Some modmem => (N.of_nat (nat_of_int doffi + length bs) <= page_size * (modmem.(lim_min)))%N
                | None => False
                end
              end
            | None => False
              end
         ) m.(mod_data).

Inductive host_reduce: host_config -> host_config -> Prop :=
| HR_host_step: forall s (vis: vi_store) m (viexps: list vi) vm vimps imps imp_descs s' vis' ms idecs' inst (exps: list module_export) start vs,
    ms !! (N.to_nat vm) = Some m ->
    those ((lookup_export_vi vis) <$> vimps) = Some imps ->
    fmap (fun imp => imp.(modexp_desc)) imps = imp_descs ->
    instantiate s m imp_descs ((s', inst, exps), start) ->
    length viexps = length exps ->
    const_list vs ->
    insert_exports vis viexps exps = Some vis' ->
    host_reduce (s, vis, ms, (ID_instantiate viexps vm vimps) :: idecs', vs) (s', vis', ms, idecs', map_start start)
| HR_host_step_init_oob: forall s (vis: vi_store) m (viexps: list vi) vm vimps imps imp_descs ms idecs' (exps: list module_export) vs,
    ms !! (N.to_nat vm) = Some m ->
    those ((lookup_export_vi vis) <$> vimps) = Some imps ->
    fmap (fun imp => imp.(modexp_desc)) imps = imp_descs ->
    const_list vs ->
    (not (module_elem_bound_check_gmap (gmap_of_list s.(s_tables)) imp_descs m /\ module_data_bound_check_gmap (gmap_of_list s.(s_mems)) imp_descs m)) ->
    host_reduce (s, vis, ms, (ID_instantiate viexps vm vimps) :: idecs', vs) (s, vis, ms, idecs', [AI_trap])
| HR_wasm_step: forall s vis ms idecs s' es es' hs',
    (* No reentrancy and no host functions, so hs should just be dummy *)
    opsem.reduce hs s empty_frame es hs' s' empty_frame es' ->
    host_reduce (s, vis, ms, idecs, es) (s', vis, ms, idecs, es').

Definition host_expr : Type := (list inst_decl) * (list administrative_instruction).

(* val is the same as native Wasm, defined in Iris.v *)


Definition state : Type := store_record * vi_store * (list module) .

Definition observation := unit. 

Definition of_val (v: host_val) : host_expr := ([::], iris.of_val v).

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
(*
Require Export iris_wp_def.

Definition function_closure := function_closure host_function.
*)
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

Global Instance host_heapG_irisG `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wtablimitG Σ, !wmemG Σ, !wmemsizeG Σ, !wmemlimitG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ} : weakestpre.irisGS wasm_host_lang Σ := {
  iris_invGS := func_invG; (* ??? *)
  state_interp σ _ κs _ :=
    let: (s, vis, ms) := σ in
     ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
      (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
      (gen_heap_interp (gmap_of_list s.(s_globals))) ∗
      (ghost_map_auth visGName 1 vis) ∗ 
      (ghost_map_auth msGName 1 (gmap_of_list ms)) ∗
      (ghost_map_auth frameGName 1 (<[ tt := empty_frame ]> ∅)) ∗ 
      (gen_heap_interp (gmap_of_list (fmap mem_length s.(s_mems)))) ∗
      (gen_heap_interp (gmap_of_list (fmap tab_size s.(s_tables)))) ∗
      (gen_heap_interp (gmap_of_list (fmap mem_max_opt s.(s_mems)))) ∗
      (gen_heap_interp (gmap_of_list (fmap table_max_opt s.(s_tables))))
    )%I;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
}.




Section host_lifting.
Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wtablimitG Σ, !wmemG Σ, !wmemsizeG Σ, !wmemlimitG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ}.


(* adding this would nullify all lemmas in weakestpre -- why? Is this not the 
   correct instance? *)
(*
Global Instance wp_host : Wp (iProp Σ) host_expr iris.val stuckness.
Proof using Σ wfuncG0 wtabG0 wmemG0 wmemsizeG0 wglobG0 wframeG0 hvisG0 hmsG0.
  by eapply weakestpre.wp'.
Qed.
*)
(*
Lemma wp_host_test_const (s: stuckness) E vs:
  ⊢ wp s E (([::], (v_to_e_list vs)): host_expr) (λ v, ⌜ v = immV vs ⌝).
Proof.
  iApply weakestpre.wp_value => //.
  unfold IntoVal => /=. by f_equal. 
Qed.
*)
(*
Let wp_wasm := @wp_wasm Σ wfuncG0.
*)


Definition reducible := @reducible wasm_host_lang.
(*
Let reduce := @reduce host_function host_instance.
*)
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
Lemma wp_host_wasm (s: stuckness) E (es: iris.expr) (Φ: host_val -> iProp Σ):
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
  iDestruct "Hσ" as "(Hwf & Hwt & Hwm & Hwg & Hvis & Hms & Hframe & ?)".
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
    iDestruct "Hwp" as "((?&?&?&?&?) & Hwp)".
    iDestruct "Hwp" as (f) "(Hf & Hwp & ?)".
    iFrame.
    iSplit => //.
    iApply "IH"; first by apply hwev_reduce_closed in H0.
    iApply "Hwp".
    by iApply "Hf".
Qed.

End host_lifting.

Section host_structural.
  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wtablimitG Σ, !wmemG Σ, !wmemsizeG Σ, !wmemlimitG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ}.

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

Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wtablimitG Σ, !wmemG Σ, !wmemsizeG Σ, !wmemlimitG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ}.

(* Resources in the host vis store for the imports *)
Definition import_resources_host (hs_imps: list vimp) (v_imps : list module_export): iProp Σ :=
  [∗ list] i ↦ hs_imp; v_imp ∈ hs_imps; v_imps,
  hs_imp ↪[vis] v_imp.


Definition export_ownership_host (hs_exps: list vi) : iProp Σ :=
  [∗ list] i ↦ hs_exp ∈ hs_exps,
  ∃ hv, hs_exp ↪[vis] hv.

Definition instantiate_globals := instantiate_globals host_function host_instance.

Definition ext_func_addrs := (map (fun x => match x with | Mk_funcidx i => i end)) ∘ ext_funcs.
Definition ext_tab_addrs := (map (fun x => match x with | Mk_tableidx i => i end)) ∘ ext_tabs.
Definition ext_mem_addrs := (map (fun x => match x with | Mk_memidx i => i end)) ∘ ext_mems.
Definition ext_glob_addrs := (map (fun x => match x with | Mk_globalidx i => i end)) ∘ ext_globs.

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

Definition import_resources_wasm_domcheck (v_imps: list module_export) (wfs: gmap N function_closure) (wts: gmap N tableinst) (wms: gmap N memory) (wgs: gmap N global) : iProp Σ :=
  ⌜ dom (gset N) wfs ≡ list_to_set (fmap N.of_nat (ext_func_addrs (fmap modexp_desc v_imps))) /\
    dom (gset N) wts ≡ list_to_set (fmap N.of_nat (ext_tab_addrs (fmap modexp_desc v_imps))) /\
    dom (gset N) wms ≡ list_to_set (fmap N.of_nat (ext_mem_addrs (fmap modexp_desc v_imps))) /\
    dom (gset N) wgs ≡ list_to_set (fmap N.of_nat (ext_glob_addrs (fmap modexp_desc v_imps))) ⌝.

(* Resources in the Wasm store, corresponding to those referred by the host vis store. This needs to also type-check
   with the module import. *)
Definition import_resources_wasm_typecheck (v_imps: list module_export) (t_imps: list extern_t) (wfs: gmap N function_closure) (wts: gmap N tableinst) (wms: gmap N memory) (wgs: gmap N global): iProp Σ :=
  (* Note that we do not actually need to know the exact content of the imports. However, these information are present
     in this predicate to make sure that they are kept incontact in the post. Note how these four gmaps are quantified
     in the instantiation spec. *)
  import_resources_wasm_domcheck v_imps wfs wts wms wgs ∗
  [∗ list] i ↦ v; t ∈ v_imps; t_imps,
  match v.(modexp_desc) with
  | MED_func (Mk_funcidx i) => ((∃ cl, N.of_nat i ↦[wf] cl ∗ ⌜ wfs !! (N.of_nat i) = Some cl /\ t = ET_func (cl_type cl) ⌝)%I)
  | MED_table (Mk_tableidx i) => (∃ tab tt, N.of_nat i ↦[wtblock] tab ∗ ⌜ wts !! (N.of_nat i) = Some tab /\ t = ET_tab tt /\ tab_typing tab tt ⌝)
  | MED_mem (Mk_memidx i) => (∃ mem mt, N.of_nat i ↦[wmblock] mem ∗ ⌜ wms !! (N.of_nat i) = Some mem /\ t = ET_mem mt /\ mem_typing mem mt ⌝) 
  | MED_global (Mk_globalidx i) => (∃ g gt, N.of_nat i ↦[wg] g ∗ ⌜ wgs !! (N.of_nat i) = Some g /\ t = ET_glob gt /\ global_agree g gt ⌝)
  end.


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


Lemma import_resources_host_lookup hs_imps v_imps vis:
  ⊢ ghost_map_auth visGName 1 vis -∗
    ([∗ list] hs_imp; v_imp ∈ hs_imps; v_imps, hs_imp ↪[vis] v_imp) -∗
    ⌜ length hs_imps = length v_imps /\ ∀ k hs_imp v_imp, hs_imps !! k = Some hs_imp -> v_imps !! k = Some v_imp -> vis !! hs_imp = Some v_imp ⌝.
Proof.
  iIntros "Hvis Himphost".
  iApply big_sepL2_pure.
  iInduction hs_imps as [|hs_imp hs_imps'] "IH" forall (v_imps); first by destruct v_imps.
  destruct v_imps => //=.
  iDestruct "Himphost" as "(Hvismap & Himpost)".
  iSplit.
  - by iDestruct (ghost_map_lookup with "Hvis Hvismap") as "%".
  - by iApply ("IH" with "[$]").   
Qed.



Lemma import_resources_wasm_lookup v_imps t_imps wfs wts wms wgs ws:
  ⊢ gen_heap_interp (gmap_of_list (s_funcs ws)) -∗
    gen_heap_interp (gmap_of_table (s_tables ws)) -∗
    gen_heap_interp (gmap_of_memory (s_mems ws)) -∗
    gen_heap_interp (gmap_of_list (s_globals ws)) -∗
    gen_heap_interp (gmap_of_list (fmap tab_size (s_tables ws))) -∗
    gen_heap_interp (gmap_of_list (fmap table_max_opt (s_tables ws))) -∗
    gen_heap_interp (gmap_of_list (fmap mem_length (s_mems ws))) -∗
    gen_heap_interp (gmap_of_list (fmap mem_max_opt (s_mems ws))) -∗
    import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs -∗
    ⌜ length v_imps = length t_imps /\ ∀ k v t, v_imps !! k = Some v -> t_imps !! k = Some t ->
      match modexp_desc v with
      | MED_func (Mk_funcidx i) => ∃ cl, ws.(s_funcs) !! i = Some cl /\ wfs !! N.of_nat i = Some cl /\ t = ET_func (cl_type cl) 
      | MED_table (Mk_tableidx i) => ∃ tab tt, ws.(s_tables) !! i = Some tab /\ wts !! N.of_nat i = Some tab /\ t = ET_tab tt /\ tab_typing tab tt
      | MED_mem (Mk_memidx i) => ∃ mem mt b_init, ws.(s_mems) !! i = Some {| mem_data := {| ml_init := b_init; ml_data := mem.(mem_data).(ml_data) |}; mem_max_opt := mem.(mem_max_opt) |} /\ wms !! N.of_nat i = Some mem /\ t = ET_mem mt /\ mem_typing mem mt
      | MED_global (Mk_globalidx i) => ∃ g gt, ws.(s_globals) !! i = Some g /\ wgs !! N.of_nat i = Some g /\ t = ET_glob gt /\ global_agree g gt
      end ⌝.
Proof. 
  iIntros "Hwf Hwt Hwm Hwg Hwtsize Hwtlimit Hwmlength Hwmlimit (Himpwasmdom & Himpwasm)".
  iSplit; first by iApply big_sepL2_length.
  iIntros (k v t Hv Ht).
  destruct v as [? modexp_desc].
  iDestruct (big_sepL2_lookup with "Himpwasm") as "Hvimp" => //.
  destruct modexp_desc as [e|e|e|e]; destruct e as [n] => /=.
  - (* functions *)
    iDestruct "Hvimp" as (cl) "(Hcl & %Hwfs)".
    destruct Hwfs as [Hwfs ->].
    iDestruct (gen_heap_valid with "Hwf Hcl") as "%Hwf".
    rewrite gmap_of_list_lookup in Hwf.
    rewrite Nat2N.id in Hwf.
    rewrite Hwf.
    iPureIntro.
    exists cl.
    by repeat split => //.
  - (* tables *)
    iDestruct "Hvimp" as (tab tt) "(Htab & %Hwts)".
    destruct Hwts as [Hwts [-> Htabletype]]. 
    iDestruct (tab_block_lookup with "Hwt Hwtsize Hwtlimit Htab") as "%Hwt".
    rewrite Nat2N.id in Hwt.
    iPureIntro.
    exists tab, tt.
    by repeat split => //.
  - (* memories *)
    iDestruct "Hvimp" as (mem mt) "(Hmem & %Hwms)".
    destruct Hwms as [Hwms [-> Hmemtype]]. 
    iDestruct (mem_block_lookup with "Hwm Hwmlength Hwmlimit Hmem") as "%Hwm".
    rewrite Nat2N.id in Hwm.
    destruct Hwm as [m [Hwmlookup [Hmdata Hmlimit]]].
    iPureIntro.
    eexists _, mt, m.(mem_data).(ml_init).
    repeat split => //.
    rewrite Hwmlookup.
    f_equal.
    destruct m.
    simpl in *.
    f_equal => //.
    destruct mem_data.
    simpl in *.
    by f_equal.
  - (* globals *)
    iDestruct "Hvimp" as (g gt) "(Hg & %Hwgs)".
    destruct Hwgs as [Hwgs [-> Hgt]].
    iDestruct (gen_heap_valid with "Hwg Hg") as "%Hwg".
    rewrite gmap_of_list_lookup in Hwg.
    rewrite Nat2N.id in Hwg.
    iPureIntro.
    exists g, gt.
    by repeat split => //.
Qed.
    
Definition gen_index offset len : list nat :=
  imap (fun i x => i+offset+x) (repeat 0 len).

Lemma gen_index_lookup offset len k:
  k < len ->
  (gen_index offset len) !! k = Some (offset + k).
Proof.
  move => Hlen.
  unfold gen_index.
  rewrite list_lookup_imap => /=.
  eapply repeat_lookup with (x := 0) in Hlen.
  rewrite Hlen.
  simpl.
  f_equal.
  by lias.
Qed.

Lemma gen_index_extend offset len:
  gen_index offset (len+1) = gen_index offset len ++ [::offset+len].
Proof.
  unfold gen_index.
  rewrite repeat_app => /=.
  induction len => //=.
  f_equal => //.
  do 2 rewrite - fmap_imap.
  rewrite IHlen.
  rewrite fmap_app => /=.
  repeat f_equal.
  by lias.
Qed.

Lemma combine_app {T1 T2: Type} (l1 l3: list T1) (l2 l4: list T2):
  length l1 = length l2 ->
  combine (l1 ++ l3) (l2 ++ l4) = combine l1 l2 ++ combine l3 l4.
Proof.
  generalize dependent l2.
  generalize dependent l3.
  generalize dependent l4.
  induction l1; move => l4 l3 l2 Hlen => /=; first by destruct l2 => //.
  - destruct l2 => //=.
    simpl in Hlen.
    inversion Hlen; subst; clear Hlen.
    f_equal.
    by apply IHl1.
Qed.
  
(* This is an actual interesting proof, technically *)
(* TODO: see if it's possible to refactor the 4 proofs into one *)
Lemma alloc_func_gen_index modfuncs ws inst ws' l:
  alloc_funcs host_function ws modfuncs inst = (ws', l) ->
  map (fun x => match x with | Mk_funcidx i => i end) l = gen_index (length (s_funcs ws)) (length modfuncs) /\
  length ws'.(s_funcs) = length ws.(s_funcs) + length modfuncs /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  unfold alloc_funcs, alloc_Xs.
  generalize dependent l.
  generalize dependent ws'.
  generalize dependent ws.
  induction modfuncs using List.rev_ind; move => ws ws' l Hallocfuncs.
  - inversion Hallocfuncs; subst; clear Hallocfuncs.
    split => //.
    by lias.
  - rewrite fold_left_app in Hallocfuncs.
    remember (fold_left _ modfuncs (ws,[])) as fold_res.
    simpl in Hallocfuncs.
    destruct fold_res as [ws0 l0].
    symmetry in Heqfold_res.
    unfold add_func in Hallocfuncs.
    inversion Hallocfuncs; subst; clear Hallocfuncs.
    rewrite map_app app_length /=.
    rewrite gen_index_extend.
    repeat split; try by eapply IHmodfuncs; rewrite Heqfold_res.
    + by repeat (f_equal; first by eapply IHmodfuncs; rewrite Heqfold_res).
    + rewrite app_length => /=.
      rewrite PeanoNat.Nat.add_assoc.
      f_equal.
      by eapply IHmodfuncs; rewrite Heqfold_res.
Qed.

Lemma alloc_tab_gen_index modtabtypes ws ws' l:
  alloc_tabs host_function ws modtabtypes = (ws', l) ->
  map (fun x => match x with | Mk_tableidx i => i end) l = gen_index (length (s_tables ws)) (length modtabtypes) /\
  ws'.(s_tables) = ws.(s_tables) ++ map (fun '{| tt_limits := {| lim_min := min; lim_max := maxo |} |} => {| table_data := repeat None (ssrnat.nat_of_bin min); table_max_opt := maxo |}) modtabtypes /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  unfold alloc_tabs, alloc_Xs.
  generalize dependent l.
  generalize dependent ws'.
  generalize dependent ws.
  induction modtabtypes using List.rev_ind; move => ws ws' l Halloc.
  - inversion Halloc; subst; clear Halloc.
    repeat split => //.
    simpl.
    by rewrite app_nil_r.
  - rewrite fold_left_app in Halloc.
    remember (fold_left _ modtabtypes (ws,[])) as fold_res.
    simpl in Halloc.
    destruct fold_res as [ws0 l0].
    symmetry in Heqfold_res.
    unfold alloc_tab, add_table in Halloc.
    destruct x => /=.
    destruct tt_limits => /=.
    specialize (IHmodtabtypes ws ws0 (rev l0)).
    rewrite Heqfold_res in IHmodtabtypes.
    inversion Halloc; subst; clear Halloc.
    simpl in *.
    rewrite map_app app_length /=.
    rewrite gen_index_extend.
    destruct IHmodtabtypes as [? [? [? [? ?]]]] => //.
    repeat split => //.
    + rewrite H.
      rewrite H0.
      by rewrite app_length map_length.
    + rewrite H0.
      rewrite - app_assoc.
      f_equal.
      by rewrite map_app => /=.
Qed.

Lemma alloc_mem_gen_index modmemtypes ws ws' l:
  alloc_mems host_function ws modmemtypes = (ws', l) ->
  map (fun x => match x with | Mk_memidx i => i end) l = gen_index (length (s_mems ws)) (length modmemtypes) /\
  ws'.(s_mems) = ws.(s_mems) ++ map (fun '{| lim_min := min; lim_max := maxo |} => {| mem_data := mem_make #00%byte (page_size * min)%N; mem_max_opt := maxo |}) modmemtypes /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  unfold alloc_mems, alloc_Xs.
  generalize dependent l.
  generalize dependent ws'.
  generalize dependent ws.
  induction modmemtypes using List.rev_ind; move => ws ws' l Halloc.
  - inversion Halloc; subst; clear Halloc.
    repeat split => //=.
    by rewrite app_nil_r.
  - rewrite fold_left_app in Halloc.
    remember (fold_left _ modmemtypes (ws,[])) as fold_res.
    simpl in Halloc.
    destruct fold_res as [ws0 l0].
    symmetry in Heqfold_res.
    unfold alloc_mem, add_mem in Halloc.
    destruct x => /=.
    specialize (IHmodmemtypes ws ws0 (rev l0)).
    rewrite Heqfold_res in IHmodmemtypes.
    inversion Halloc; subst; clear Halloc.
    simpl in *.
    rewrite map_app app_length /=.
    rewrite gen_index_extend.
    destruct IHmodmemtypes as [? [? [? [? ?]]]] => //.
    repeat split => //.
    + rewrite H.
      rewrite H0.
      by rewrite app_length map_length.
    + rewrite H0.
      rewrite - app_assoc.
      f_equal.
      by rewrite map_app => /=.
Qed.

Lemma alloc_glob_gen_index modglobs ws g_inits ws' l:
  length g_inits = length modglobs ->
  alloc_globs host_function ws modglobs g_inits = (ws', l) ->
  map (fun x => match x with | Mk_globalidx i => i end) l = gen_index (length (s_globals ws)) (length modglobs) /\
  length ws'.(s_globals) = length ws.(s_globals) + length modglobs /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems).
Proof.
  unfold alloc_globs, alloc_Xs.
  generalize dependent l.
  generalize dependent ws'.
  generalize dependent ws.
  generalize dependent g_inits.
  induction modglobs using List.rev_ind; move => g_inits ws ws' l Hlen Halloc.
  - inversion Halloc; subst; clear Halloc.
    split => //.
    by lias.
  - destruct g_inits using List.rev_ind; first by destruct modglobs => /=.
    repeat rewrite app_length in Hlen; simpl in Hlen.
    repeat rewrite - cat_app in Halloc.
    rewrite combine_app in Halloc; last by lias.
    simpl in Halloc.
    rewrite fold_left_app in Halloc.
    lazymatch goal with
    | _: context C [fold_left ?f (combine modglobs g_inits) (ws, [])] |- _ =>
      remember (fold_left f (combine modglobs g_inits) (ws, [])) as fold_res
    end.
    rewrite - Heqfold_res in Halloc.
    destruct fold_res as [ws0 l0].
    symmetry in Heqfold_res.
    unfold alloc_glob, add_glob in Halloc.
    simpl in Halloc.
    inversion Halloc; subst; clear Halloc.
    rewrite map_app app_length /=.
    rewrite gen_index_extend.
    repeat split; try by eapply IHmodglobs with (g_inits := g_inits) (ws' := ws0); [ lias | rewrite Heqfold_res ].
    + by repeat (f_equal; first eapply IHmodglobs with (g_inits := g_inits) (ws' := ws0); (try by lias); (try by rewrite Heqfold_res)).
    + rewrite app_length => /=.
      rewrite PeanoNat.Nat.add_assoc.
      f_equal.
      by eapply IHmodglobs with (g_inits := g_inits) (ws' := ws0); [ lias | rewrite Heqfold_res ].
Qed.


Definition module_glob_init_value (modglobs: list module_glob): option (list value) :=
  those (fmap (assert_const1 ∘ modglob_init) modglobs).

(* Table initialisers work as follows:
   - Each initialiser specifies a tableidx which is an index to the table list in the current module instance. 
   - Each initialiser specifies an offset eo (has to be const), which is the starting index that is going to be filled in.
   - For each f_j in the init array, replace s.tables[inst.tables(tableidx)][offset+j] with inst.funcs(f_j). Note how
     both the tableidx and the f_j (funcidx) here are referring to the index in the current module. 
   
   Memory initiliasers work similarly.
*)

Definition instantiation_resources_pre hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps : iProp Σ :=
  hs_mod ↪[mods] m ∗
  import_resources_host hs_imps v_imps ∗
  import_resources_wasm_typecheck v_imps t_imps wfs wts wms wgs ∗
  export_ownership_host hs_exps ∗
  ⌜ length hs_exps = length m.(mod_exports) ⌝ ∗
  ⌜ module_elem_bound_check_gmap wts (fmap modexp_desc v_imps) m ⌝ ∗
  ⌜ module_data_bound_check_gmap wms (fmap modexp_desc v_imps) m ⌝.

(* This builds a gmap from (tableid * index) to funcelem, representing the initial values dictated by the elem segment. However, note that the tableid here refers to the id in the instance instead of that in the store.

   Note that this tableid does not count the imported tables. 
 *)
Definition build_tab_initialiser (instfuncs: list funcaddr) (elem: module_element) (tabid: nat) (offset: nat) : gmap (nat * nat) funcelem :=
  fold_left (fun acc actor => actor acc) (imap (fun j e_init => match e_init with
                     | Mk_funcidx fid => map_insert (tabid, j + offset) (nth_error instfuncs fid) end) elem.(modelem_init) ) ∅.

Fixpoint module_tab_init_values (m: module) (inst: instance) (modelems: list module_element) : gmap (nat * nat) funcelem :=
  match modelems with
  | e_init :: e_inits' => match e_init.(modelem_table) with
                        | Mk_tableidx i => (module_tab_init_values m inst e_inits') ∪ (build_tab_initialiser inst.(inst_funcs) e_init i (assert_const1_i32_to_nat (e_init.(modelem_offset))))
                        end
                          
  | [] => ∅
  end.

(* Note that we use compcert byte for our internal memory representation, but module uses the pure Coq version of byte. *)
Definition build_mem_initialiser (datum: module_data) (memid: nat) (offset: nat) : gmap (nat * nat) byte :=
  fold_left (fun acc actor => actor acc)
            (imap (fun j b => map_insert (memid, j + offset) (compcert_byte_of_byte b)) datum.(moddata_init) ) ∅.


Fixpoint module_mem_init_values (m: module) (moddata: list module_data) : gmap (nat * nat) byte :=
  match moddata with
  | d_init :: d_inits' => match d_init.(moddata_data) with
                        | Mk_memidx i => (module_mem_init_values m d_inits') ∪ (build_mem_initialiser d_init i (assert_const1_i32_to_nat (d_init.(moddata_offset))))
                        end
                          
  | [] => ∅
  end.

(* g_inits have the correct types and values. Typing is redundant given the current restriction *)
Definition module_glob_init_values m g_inits :=
  (fmap typeof g_inits = fmap (tg_t ∘ modglob_type) m.(mod_globals)) /\
  module_glob_init_value m.(mod_globals) = Some g_inits.

(* The starting point for newly allocated tables. *)
Definition module_inst_table_base_create :=
  fun mt => match mt.(modtab_type).(tt_limits) with
         | {| lim_min := min; lim_max := omax |} =>
             (Build_tableinst
                (repeat (None: funcelem) (ssrnat.nat_of_bin min))
                (omax))
         end.
Definition module_inst_table_base (mtabs: list module_table) : list tableinst :=
  fmap module_inst_table_base_create mtabs.

(* Given a tableinst, an offset and a list of funcelems, replace the corresponding segment with the initialisers. *)
Definition table_init_replace_single (t: tableinst) (offset: nat) (fns: list funcelem) : tableinst :=
  Build_tableinst
    (take (length t.(table_data)) ((take offset t.(table_data)) ++ fns ++ (drop (offset + length fns) t.(table_data))))
    t.(table_max_opt).

Lemma table_init_replace_single_preserve_len t offset fns t':
  table_init_replace_single t offset fns = t' ->
  length t.(table_data) = length t'.(table_data).
Proof.
  move => Hreplace.
  unfold table_init_replace_single in Hreplace.
  subst => /=.
  rewrite take_length.
  repeat rewrite app_length.
  rewrite take_length drop_length.
  by lias.
Qed.

(*
Lemma fold_left_preserve {A B: Type} (P: A -> Prop) (f: A -> B -> A) (l: list B) (acc: A):
  P acc ->
  (forall (x:A) (act: B), P x -> P (f x act)) ->
  P (fold_left f l acc).
Proof.
Admitted.
*)

(* Each of these is guaranteed to be a some due to validation. *)
Definition lookup_funcaddr (inst: instance) (me_init: list funcidx) : list funcelem :=
  fmap (fun '(Mk_funcidx fidx) => nth_error inst.(inst_funcs) fidx) me_init.

(* For each table initialiser elem, if the target table is not imported, then
   we use its content to update the corresponding table build from the base. *)
Definition module_inst_build_tables (m : module) (inst: instance) : list tableinst :=
  fold_left (fun tabs '{| modelem_table := mt; modelem_offset := moff; modelem_init := me_init |} =>
               let itc := get_import_table_count m in 
               match mt with
               | Mk_tableidx k =>
                 if k <? itc then tabs else
                   (* These are guaranteed to succeed due to validation. *)
                   match nth_error tabs (k-itc) with
                   | Some t => <[ (k-itc) := table_init_replace_single t (assert_const1_i32_to_nat moff) (lookup_funcaddr inst me_init) ]> tabs
                   | None => tabs
                   end
               end
                 ) m.(mod_elem) (module_inst_table_base m.(mod_tables)).

Definition module_import_init_tabs (m: module) (inst: instance) (wts: gmap N tableinst) : gmap N tableinst :=
  fold_left (fun wts '{| modelem_table := mt; modelem_offset := moff; modelem_init := me_init |} =>
               let itc := get_import_table_count m in 
               match mt with
               | Mk_tableidx k =>
                 if k <? itc then
                   match nth_error inst.(inst_tab) k with
                   | Some t_addr =>
                     match wts !! (N.of_nat t_addr) with
                     | Some t => <[ (N.of_nat t_addr) := table_init_replace_single t (assert_const1_i32_to_nat moff) (lookup_funcaddr inst me_init) ]> wts
                     | None => wts
                     end
                   | None => wts
                   end
                 else wts
               end
            ) m.(mod_elem) wts.

(* A similar set of predicate but for memories instead. *)
Definition module_inst_mem_base_func := (fun '{| lim_min := min; lim_max := omax |} =>
          (Build_memory
             (Build_memory_list
               #00%byte
               (repeat #00%byte (ssrnat.nat_of_bin min))
               )
             (omax))).
Definition module_inst_mem_base (mmemtypes: list memory_type) : list memory :=
  fmap module_inst_mem_base_func mmemtypes.

Definition mem_init_replace_single (mem: memory) (offset: nat) (bs: list byte) : memory :=
  Build_memory
    (Build_memory_list
       mem.(mem_data).(ml_init)
       (take (length mem.(mem_data).(ml_data)) ((take offset mem.(mem_data).(ml_data)) ++ bs ++ (drop (offset + length bs) mem.(mem_data).(ml_data)))))
    mem.(mem_max_opt).



Definition module_inst_build_mems (m : module) (inst: instance) : list memory :=
  fold_left (fun mems '{| moddata_data := md; moddata_offset := moff; moddata_init := md_init |} =>
               let imc := get_import_mem_count m in 
               match md with
               | Mk_memidx k =>
                 if k <? imc then mems else
                   (* These are guaranteed to succeed due to validation. *)
                   match nth_error mems (k-imc) with
                   | Some mem => <[ (k-imc) := mem_init_replace_single mem (assert_const1_i32_to_nat moff) (fmap compcert_byte_of_byte md_init) ]> mems
                   | None => mems
                   end
               end
                 ) m.(mod_data) (module_inst_mem_base m.(mod_mems)).

Definition module_import_init_mems (m: module) (inst: instance) (wms: gmap N memory) : gmap N memory :=
  fold_left (fun wms '{| moddata_data := md; moddata_offset := moff; moddata_init := md_init |} =>
               let imc := get_import_mem_count m in 
               match md with
               | Mk_memidx k =>
                 if k <? imc then
                   match nth_error inst.(inst_memory) k with
                   | Some m_addr =>
                     match wms !! (N.of_nat m_addr) with
                     | Some mem => <[ (N.of_nat m_addr) := mem_init_replace_single mem (assert_const1_i32_to_nat moff) (fmap compcert_byte_of_byte md_init) ]> wms
                     | None => wms
                     end
                   | None => wms
                   end
                 else wms
               end
            ) m.(mod_data) wms.

Print module_glob.

Print global_type.

Print Build_global.


(* Again the allocated resources but for globals. Note that the initial value
   here is purely dummy. *)
Definition module_inst_global_base (mglobs: list module_glob) : list global :=
  fmap (fun '{| modglob_type := {| tg_mut := tgm; tg_t := tgvt |} ; modglob_init := mgi |} => (Build_global tgm (bitzero tgvt))) mglobs.

Definition global_init_replace_single (g: global) (v: value) : global :=
  Build_global g.(g_mut) v.

Fixpoint module_inst_global_init (gs: list global) (g_inits: list value) : list global :=
  match gs with
  | [::] => [::]
  | g :: gs' =>
    match g_inits with
    | [::] => g :: gs'
    | gi :: g_inits' => global_init_replace_single g gi :: module_inst_global_init gs' g_inits'
    end
  end.

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

Definition module_inst_resources_tab (tabs: list tableinst) (inst_t: list tableaddr) : iProp Σ :=
  ([∗ list] i ↦ tab; addr ∈ tabs; inst_t,
    N.of_nat addr ↦[wtblock] tab
  )%I.

Definition module_inst_resources_mem (mems: list memory) (inst_m: list memaddr) : iProp Σ := 
  ([∗ list] i ↦ mem; addr ∈ mems; inst_m,
    N.of_nat addr ↦[wmblock] mem
  ).

Definition module_inst_resources_glob (globs: list global) (inst_g: list globaladdr) : iProp Σ :=
  ([∗ list] i↦g; addr ∈ globs; inst_g,
    N.of_nat addr ↦[wg] g
  ).

(* The collection of the four types of newly allocated resources *)
Definition module_inst_resources_wasm (m: module) (inst: instance) (tab_inits: list tableinst) (mem_inits: list memory) (glob_inits: list global) : iProp Σ :=
  (module_inst_resources_func m.(mod_funcs) inst (drop (get_import_func_count m) inst.(inst_funcs)) ∗
  module_inst_resources_tab tab_inits (drop (get_import_table_count m) inst.(inst_tab)) ∗
  module_inst_resources_mem mem_inits (drop (get_import_mem_count m) inst.(inst_memory)) ∗                        
  module_inst_resources_glob glob_inits (drop (get_import_global_count m) inst.(inst_globs)))%I.

Definition instantiation_resources_post hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps (idfstart: option nat) : iProp Σ :=
  ∃ (inst: instance) (g_inits: list value) tab_inits mem_inits glob_inits wts' wms',
  hs_mod ↪[mods] m ∗
  import_resources_host hs_imps v_imps ∗ (* vis, for the imports stored in host *)
  import_resources_wasm_typecheck v_imps t_imps wfs wts' wms' wgs ∗ (* locations in the wasm store and type-checks *)
    ⌜ inst.(inst_types) = m.(mod_types) /\
   (* We know what the imported part of the instance must be. *)
  let v_imp_descs := map (fun mexp => mexp.(modexp_desc)) v_imps in
    prefix (ext_func_addrs v_imp_descs) inst.(inst_funcs) /\
    prefix (ext_tab_addrs v_imp_descs) inst.(inst_tab) /\
    prefix (ext_mem_addrs v_imp_descs) inst.(inst_memory) /\
    prefix (ext_glob_addrs v_imp_descs) inst.(inst_globs) /\
    check_start m inst idfstart ⌝ ∗
   (* The relevant initial values of allocated resources, as well as the newly
      initialised segments in the imported tables and memories *)
    ⌜ tab_inits = module_inst_build_tables m inst ⌝ ∗
    ⌜ wts' = module_import_init_tabs m inst wts ⌝ ∗
    ⌜ module_elem_bound_check_gmap wts (fmap modexp_desc v_imps) m ⌝ ∗
    ⌜ mem_inits = module_inst_build_mems m inst ⌝ ∗
    ⌜ wms' = module_import_init_mems m inst wms ⌝ ∗
    ⌜ module_data_bound_check_gmap wms (fmap modexp_desc v_imps) m ⌝ ∗
    ⌜ module_glob_init_values m g_inits ⌝ ∗
    ⌜ glob_inits = module_inst_global_init (module_inst_global_base m.(mod_globals)) g_inits ⌝ ∗
    module_inst_resources_wasm m inst tab_inits mem_inits glob_inits ∗ (* allocated wasm resources. This also specifies the information about the newly allocated part of the instance. *)
    module_export_resources_host v_imps hs_exps m.(mod_exports) inst. (* export resources, in the host store *)

Definition module_restrictions (m: module) : Prop :=
  (* Initializers for globals are only values. This is not that much a restriction as it seems, since they can
     only be either values or get_globals (from immutable globals) anyway. *)
  (exists (vs: list value), fmap modglob_init m.(mod_globals) = fmap (fun v => [BI_const v]) vs) /\
  (exists (vi32s: list i32), fmap modelem_offset m.(mod_elem) = fmap (fun v => [BI_const (VAL_int32 v)]) vi32s) /\
  (exists (vi32s: list i32), fmap moddata_offset m.(mod_data) = fmap (fun v => [BI_const (VAL_int32 v)]) vi32s).

Lemma fmap_fmap_lookup {T1 T2 T: Type} (f1: T1 -> T) (f2: T2 -> T) (l1: list T1) (l2: list T2):
  fmap f1 l1 = fmap f2 l2 ->
  forall i, fmap f1 (l1 !! i) = fmap f2 (l2 !! i).
Proof.
  move => Heq i.
  assert (length l1 = length l2) as Hlen.
  { erewrite <- fmap_length with (f := f1).
    rewrite Heq.
    by rewrite fmap_length.
  }
  destruct (l1 !! i) eqn:Hl1; destruct (l2 !! i) eqn:Hl2 => //=.
  - assert ((fmap f1 l1) !! i = (fmap f2 l2) !! i) as Heqi; first by rewrite Heq.
    repeat rewrite list_lookup_fmap in Heqi.
    rewrite Hl1 Hl2 in Heqi.
    by simpl in Heqi.
  - by apply lookup_lt_Some in Hl1; apply lookup_ge_None in Hl2; lias.
  - by apply lookup_lt_Some in Hl2; apply lookup_ge_None in Hl1; lias.
Qed.

Lemma BI_const_assert_const1_i32 (es: list expr) (vs: list i32):
  es = fmap (fun v => [BI_const (VAL_int32 v)]) vs ->
  those (fmap assert_const1_i32 es) = Some vs.
Proof.
  move: es.
  elim: vs => //=.
  - by move => es ->.
  - move => v vs IH es Hes.
    destruct es => //=.
    inversion Hes; subst; clear Hes.
    simpl.
    rewrite - cat1s.
    erewrite those_app => //=; last by apply IH.
    by [].
Qed.

Lemma all2_Forall2 {T1 T2: Type} r (l1: list T1) (l2: list T2):
  all2 r l1 l2 <-> Forall2 r l1 l2.
Proof.
  move: l2.
  elim: l1 => //=.
  - move => l2; destruct l2 => //=.
    split => //.
    move => Hcontra.
    by inversion Hcontra.
  - move => e l1 IH l2.
    destruct l2 => //=.
    + split => //.
      move => Hcontra.
      by inversion Hcontra.
    + split; move => H.
      * move/andP in H.
        destruct H.
        constructor => //.
        by apply IH.
      * apply/andP.
        inversion H; subst; clear H.
        split => //.
        by apply IH.
Qed.

Lemma map_fmap {T1 T2: Type} (f: T1 -> T2) (l: list T1):
  map f l = fmap f l.
Proof.
  trivial.
Qed.

(* Ok, this is not built-in, but fair enough since it is across 3 libraries *)
Lemma N_nat_bin n:
  n = N.of_nat (ssrnat.nat_of_bin n).
Proof.
  destruct n => //=.
  replace (ssrnat.nat_of_pos p) with (Pos.to_nat p); first by rewrite positive_nat_N.
  induction p => //=.
  - rewrite Pos2Nat.inj_xI.
    f_equal.
    rewrite IHp.
    rewrite ssrnat.NatTrec.doubleE.
    rewrite - ssrnat.mul2n.
    by lias.
  - rewrite Pos2Nat.inj_xO.
    rewrite IHp.
    rewrite ssrnat.NatTrec.doubleE.
    rewrite - ssrnat.mul2n.
    by lias.
Qed.

Lemma ext_tabs_lookup_exist (modexps: list module_export_desc) n tn:
  (ext_tabs modexps) !! n = Some tn ->
  exists k, modexps !! k = Some (MED_table tn).
Proof.
  move: n tn.
  induction modexps; move => n tn Hexttablookup => //=.
  simpl in Hexttablookup.
  destruct a => //. 
  2: { simpl in *.
       destruct n; simpl in *; first by inversion Hexttablookup; subst; exists 0.
       apply IHmodexps in Hexttablookup.
       destruct Hexttablookup as [k ?].
       by exists (S k).
  }
  all: simpl in *. 
  all: apply IHmodexps in Hexttablookup.
  all: destruct Hexttablookup as [k ?].
  all: by exists (S k).
Qed.

Lemma ext_mems_lookup_exist (modexps: list module_export_desc) n mn:
  (ext_mems modexps) !! n = Some mn ->
  exists k, modexps !! k = Some (MED_mem mn).
Proof.
  move: n mn.
  induction modexps; move => n mn Hextmemlookup => //=.
  simpl in Hextmemlookup.
  destruct a => //. 
  3: { simpl in *.
       destruct n; simpl in *; first try by inversion Hextmemlookup; subst; exists 0.
       apply IHmodexps in Hextmemlookup.
       destruct Hextmemlookup as [k ?].
       by exists (S k).
  }
  all: simpl in *. 
  all: apply IHmodexps in Hextmemlookup.
  all: destruct Hextmemlookup as [k ?].
  all: by exists (S k).
Qed.

Lemma fold_left_preserve {A B: Type} (P: A -> Prop) (f: A -> B -> A) (l: list B) (acc: A) :
  P acc ->
  (forall (x:A) (act: B), P x -> P (f x act)) ->
  P (fold_left f l acc).
Proof.
  rewrite -fold_left_rev_right.
  revert acc.
  induction l;simpl;auto.
  intros acc Ha Hnext.
  rewrite foldr_snoc /=. apply IHl =>//.
  apply Hnext=>//.
Qed.    
  
Lemma module_inst_build_tables_length m i :
  length (module_inst_build_tables m i) = length (mod_tables m).
Proof.
  unfold module_inst_build_tables.
  apply fold_left_preserve.
  { apply fmap_length. }
  { intros x me Heq.
    destruct me,modelem_table.
    destruct (n <? get_import_table_count m);auto.
    destruct (nth_error x (n - get_import_table_count m));auto.
    rewrite insert_length//. }
Qed.

Ltac forward H Hname :=
  lazymatch type of H with
  | ?Hx -> _ => let Hp := fresh "Hp" in
              assert Hx as Hp; last specialize (H Hp) as Hname end.

Lemma instantiation_spec_operational_no_start (s: stuckness) E (hs_mod: N) (hs_imps: list vimp) (v_imps: list module_export) (hs_exps: list vi) (m: module) t_imps t_exps wfs wts wms wgs :
  m.(mod_start) = None ->
  module_typing m t_imps t_exps ->
  module_restrictions m ->
  instantiation_resources_pre hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps -∗
  WP (([:: ID_instantiate hs_exps hs_mod hs_imps], [::]): host_expr) @ s; E
  {{ v, instantiation_resources_post hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps None }}.
Proof.
  
  move => Hmodstart Hmodtype Hmodrestr.
  iIntros "(Hmod & Himphost & Himpwasm & Hexphost & Hlenexp & %Hebound & %Hdbound)".
  
  repeat rewrite weakestpre.wp_unfold /weakestpre.wp_pre /=.
  
  iIntros ([[ws vis] ms] ns κ κs nt) "Hσ".
  iDestruct "Hσ" as "(Hwf & Hwt & Hwm & Hwg & Hvis & Hms & Hframe & Hmsize & Htsize & Hmlimit & Htlimit)".

  (* Reflecting the assertions back *)
  (* module declaration *)
  iDestruct (ghost_map_lookup with "Hms Hmod") as "%Hmod".
  rewrite gmap_of_list_lookup in Hmod.

  (* Import pointers in host (vis store) *)
  iDestruct (import_resources_host_lookup with "Hvis Himphost") as "%Himphost".
  destruct Himphost as [Himplen Himphost].

  (* Imported resources in Wasm and typing information *)
  iDestruct (import_resources_wasm_lookup with "Hwf Hwt Hwm Hwg Htsize Htlimit Hmsize Hmlimit Himpwasm") as "%Himpwasm".
  destruct Himpwasm as [Hvtlen Himpwasm].

  remember {| inst_types := m.(mod_types);
                  inst_funcs := ext_func_addrs (fmap modexp_desc v_imps) ++ (gen_index (length ws.(s_funcs)) (length m.(mod_funcs)));
                  inst_tab := ext_tab_addrs (fmap modexp_desc v_imps) ++ (gen_index (length ws.(s_tables)) (length m.(mod_tables)));
                  inst_memory := ext_mem_addrs (fmap modexp_desc v_imps) ++ (gen_index (length ws.(s_mems)) (length m.(mod_mems)));
                  inst_globs := ext_glob_addrs (fmap modexp_desc v_imps) ++ (gen_index (length ws.(s_globals)) (length m.(mod_globals)))
               |} as inst_res.
  
  unfold module_restrictions in Hmodrestr.
  destruct Hmodrestr as [[g_inits Hmodglob] [[e_inits Hmodelem] [d_inits Hmoddata]]].

  assert (length m.(mod_globals) = length g_inits) as Hginitslen.
  { erewrite <- fmap_length.
    instantiate (1 := modglob_init).
    rewrite Hmodglob.
    by rewrite fmap_length.
  }
  
  assert (length m.(mod_elem) = length e_inits) as Heinitslen.
  { erewrite <- fmap_length.
    instantiate (1 := modelem_offset).
    rewrite Hmodelem.
    by rewrite fmap_length.
  }
  
  assert (length m.(mod_data) = length d_inits) as Hdinitslen.
  { erewrite <- fmap_length.
    instantiate (1 := moddata_offset).
    rewrite Hmoddata.
    by rewrite fmap_length.
  }
  
  assert (fmap typeof g_inits = fmap (tg_t ∘ modglob_type) m.(mod_globals)) as Hginitstype.
  {
    unfold module_typing in Hmodtype.
    destruct m => /=.
    destruct Hmodtype as [fts [gts [? [? [? [Hglobtype ?]]]]]].
    apply list_eq.
    move => i.
    rewrite -> Forall2_lookup in Hglobtype.
    specialize Hglobtype with i.
    repeat rewrite list_lookup_fmap.
    simpl in *.
    destruct (mod_globals !! i) as [mg | ] eqn: Hmgi.
    - assert (i < length mod_globals) as Hlen; first by eapply lookup_lt_Some.
      simpl in Hmodglob.
      destruct (g_inits !! i) as [gi | ] eqn: Hgii; last by apply lookup_ge_None in Hgii; lias.
      inversion Hglobtype; subst; clear Hglobtype.
      simpl in *.
      unfold module_glob_typing in H5.
      assert ((modglob_init <$> mod_globals) !! i = ((fun v => [BI_const v]) <$> g_inits) !! i) as Hlookup; first by rewrite Hmodglob.
      repeat rewrite list_lookup_fmap in Hlookup.
      rewrite Hmgi Hgii in Hlookup.
      destruct mg.
      destruct H5 as [Hconstexpr [-> Hbet]].
      simpl in Hlookup.
      inversion Hlookup; subst; clear Hlookup.
      f_equal.
      simpl.
      apply BI_const_typing in Hbet.
      simpl in Hbet.
      by inversion Hbet.
    - assert (i >= length mod_globals) as Hlen; first by eapply lookup_ge_None.
      simpl in Hmodglob.
      destruct (g_inits !! i) as [gi | ] eqn: Hgii; [ by apply lookup_lt_Some in Hgii; lias | by auto ].
  }

  destruct (alloc_funcs host_function ws (mod_funcs m) inst_res) eqn:Hallocfunc.
  destruct (alloc_tabs host_function s0 (map modtab_type (mod_tables m))) eqn:Halloctab.
  destruct (alloc_mems host_function s1 (mod_mems m)) eqn:Hallocmem.
  destruct (alloc_globs host_function s2 (mod_globals m) g_inits) eqn:Hallocglob.

  remember (fmap (fun m_exp => {| modexp_name := modexp_name m_exp; modexp_desc := export_get_v_ext inst_res (modexp_desc m_exp) |}) m.(mod_exports)) as v_exps.

  (* Prove that the instantiation predicate holds *)
  assert (exists ws_res, (instantiate ws m (fmap modexp_desc v_imps) ((ws_res, inst_res, v_exps), None))) as Hinst.
  {
    unfold instantiate, instantiation.instantiate.
    unfold alloc_module => /=.
    eexists.
    exists t_imps, t_exps, hs, s3, g_inits.
    exists e_inits, d_inits.
    repeat split.
    - (* module_typing *)
      by apply Hmodtype.
    - (* import types *)
      apply Forall2_same_length_lookup.
      split => //; first by rewrite fmap_length.
      move => k vdesc t Hvdesc Ht.
      rewrite list_lookup_fmap in Hvdesc.
      remember (v_imps !! k) as v.
      destruct v as [v|]=> //.
      simpl in Hvdesc.
      inversion Hvdesc; subst; clear Hvdesc.
      symmetry in Heqv.
      specialize (Himpwasm k v t Heqv Ht).
      destruct v => /=.
      simpl in Himpwasm.
      destruct modexp_desc.
      + (* functions *)
        destruct f.
        destruct Himpwasm as [cl [Hws [? ->]]].
        eapply ETY_func => //; last by rewrite nth_error_lookup.
        apply lookup_lt_Some in Hws.
        by lias.
      + (* tables *)
        destruct t0.
        destruct Himpwasm as [tab [tt [Hwt [? [-> Htt]]]]].
        eapply ETY_tab => //; last by rewrite nth_error_lookup.
        apply lookup_lt_Some in Hwt.
        by lias.
      + (* memories *)
        destruct m0.
        destruct Himpwasm as [mem [mt [b_init [Hwm [? [-> Hmt]]]]]].
        eapply ETY_mem; [ | rewrite nth_error_lookup; by apply Hwm |].
        * apply lookup_lt_Some in Hwm; by lias.
        * unfold mem_typing.
          unfold mem_typing in Hmt.
          move/andP in Hmt.
          destruct Hmt as [Hmlimmin Hmlimmax].
          apply/andP.
          by split.
      + (* globals *)
        destruct g.
        destruct Himpwasm as [g [gt [Hwg [? [-> Hgt]]]]].
        eapply ETY_glob => //; last by rewrite nth_error_lookup.
        apply lookup_lt_Some in Hwg.
        by lias.
    - (* alloc module *)
      rewrite Hallocfunc Halloctab Hallocmem Hallocglob.
      repeat (apply/andP; split); try apply/eqP; subst => //=.
      + (* Functions *)
        unfold ext_func_addrs => /=.
        rewrite map_app => /=.
        (* The first part is the same. *)
        f_equal.
        (* We now have to prove that gen_index gives the correct indices of the newly allocated functions. This should
           be a general property that holds for alloc_Xs, tbh. *)
        by apply alloc_func_gen_index in Hallocfunc as [-> ?].
      + (* Tables *)
        unfold ext_tab_addrs => /=.
        rewrite map_app => /=.
        f_equal.
        apply alloc_tab_gen_index in Halloctab as [-> ?].
        rewrite map_length.
        by apply alloc_func_gen_index in Hallocfunc as [? [? [<- ?]]].
      + (* Memories *)
        unfold ext_mem_addrs => /=.
        rewrite map_app => /=.
        f_equal.
        apply alloc_mem_gen_index in Hallocmem as [-> ?].
        apply alloc_tab_gen_index in Halloctab as [? [? [? [<- ?]]]].
        by apply alloc_func_gen_index in Hallocfunc as [? [? [? [<- ?]]]].
      + (* Globals *)
        unfold ext_glob_addrs => /=.
        rewrite map_app => /=.
        f_equal.
        apply alloc_glob_gen_index in Hallocglob as [-> ?]; last by lias.
        apply alloc_mem_gen_index in Hallocmem as [? [? [? [? <-]]]].
        apply alloc_tab_gen_index in Halloctab as [? [? [? [? <-]]]].
        by apply alloc_func_gen_index in Hallocfunc as [? [? [? [? <-]]]].
    - (* global initializers *)
      unfold instantiation.instantiate_globals.
      rewrite Forall2_lookup.
      move => i.
      destruct (m.(mod_globals) !! i) eqn:Hmglob => /=.
      + destruct (g_inits !! i) eqn:Hginit => /=; last by apply lookup_lt_Some in Hmglob; apply lookup_ge_None in Hginit; lias.
        constructor.
        apply fmap_fmap_lookup with (i0 := i) in Hmodglob.
        repeat rewrite list_lookup_fmap in Hmodglob.
        rewrite Hmglob Hginit in Hmodglob.
        simpl in *.
        inversion Hmodglob; clear Hmodglob.
        rewrite H0.
        simpl.
        by repeat constructor.
      + apply lookup_ge_None in Hmglob.
        rewrite Hginitslen in Hmglob.
        apply lookup_ge_None in Hmglob.
        rewrite Hmglob.
        by constructor.
    - (* table initializers *)
      unfold instantiate_elem.
      rewrite Forall2_lookup.
      move => i.
      destruct (m.(mod_elem) !! i) eqn:Hmelem => /=.
      + destruct (e_inits !! i) eqn: Heinit => /=; last by apply lookup_lt_Some in Hmelem; apply lookup_ge_None in Heinit; lias.
        rewrite Heinit.
        constructor.
        apply fmap_fmap_lookup with (i0 := i) in Hmodelem.
        repeat rewrite list_lookup_fmap in Hmodelem.
        rewrite Hmelem Heinit in Hmodelem.
        simpl in *.
        inversion Hmodelem; subst; clear Hmodelem.
        rewrite H0.
        simpl.
        by repeat constructor.
      + apply lookup_ge_None in Hmelem.
        rewrite Heinitslen in Hmelem.
        apply lookup_ge_None in Hmelem.
        rewrite Hmelem.
        by constructor.
    - (* memory initializers *)
      unfold instantiate_data.
      rewrite Forall2_lookup.
      move => i.
      destruct (m.(mod_data) !! i) eqn:Hmdata => /=.
      + destruct (d_inits !! i) eqn: Hdinit => /=; last by apply lookup_lt_Some in Hmdata; apply lookup_ge_None in Hdinit; lias.
        rewrite Hdinit.
        constructor.
        apply fmap_fmap_lookup with (i0 := i) in Hmoddata.
        repeat rewrite list_lookup_fmap in Hmoddata.
        rewrite Hmdata Hdinit in Hmoddata.
        simpl in *.
        inversion Hmoddata; subst; clear Hmoddata.
        rewrite H0.
        simpl.
        by repeat constructor.
      + apply lookup_ge_None in Hmdata.
        rewrite Hdinitslen in Hmdata.
        apply lookup_ge_None in Hmdata.
        rewrite Hmdata.
        by constructor.
    - (* table initializers bound check *)

      (* This is a complicated/messy proof; there are a lot of playing around the indices. *)
      (* First we note that s_tables of s3 only differs from the original list of tables by the result of alloc_tab. *)
      apply alloc_glob_gen_index in Hallocglob as [? [? [? [? ?]]]]; last by lias.
      apply alloc_mem_gen_index in Hallocmem as [? [? [? [? ?]]]].
      apply alloc_tab_gen_index in Halloctab as [? [? [? [? ?]]]].
      apply alloc_func_gen_index in Hallocfunc as [? [? [? [? ?]]]].
      destruct ws, s0, s1, s2, s3.
      simpl in *; subst; simpl in *.

      unfold module_elem_bound_check_gmap in Hebound.

      (* Prove all2 by proving arbitrary lookups *)
      apply all2_Forall2.
      rewrite Forall2_lookup.
      move => i.
      destruct (m.(mod_elem) !! i) eqn:Hmelem => /=.
      + destruct (e_inits !! i) eqn: Heinit => /=; last by apply lookup_lt_Some in Hmelem; apply lookup_ge_None in Heinit; lias.
        constructor.
        apply fmap_fmap_lookup with (i0 := i) in Hmodelem.
        repeat rewrite list_lookup_fmap in Hmodelem.
        rewrite Hmelem Heinit in Hmodelem.
        simpl in Hmodelem.
        inversion Hmodelem; subst; clear Hmodelem.
        destruct m0.
        simpl in *.
        subst.
        destruct modelem_table => /=.
        destruct m.
        simpl in *.
        unfold module_typing in Hmodtype.
        destruct Hmodtype as [fts [gts [? [? [? [? [Helemtype _]]]]]]].
        rewrite -> Forall_lookup in Helemtype.
        specialize (Helemtype _ _ Hmelem).
        unfold module_elem_typing in Helemtype.
        destruct Helemtype as [_ [_ [Hlen1 Hlen2]]].
        rewrite app_length in Hlen1.
        rewrite map_length in Hlen1.
        simpl in *.

        rewrite -> Forall_lookup in Hebound.
        specialize (Hebound _ _ Hmelem).
        simpl in Hebound.

        unfold ext_tab_addrs.
        unfold compose.
        
        destruct (ext_tabs (modexp_desc <$> v_imps) !! n) as [tabid | ] eqn:Hexttablookup => //.
        {
          (* Initialiser is for an imported table *)
          destruct tabid as [tabn].

          destruct (wts !! N.of_nat tabn) as [ti | ] eqn:Hwtslookup => //.

          rewrite nth_error_app1; last first.
          { rewrite map_length.
            apply lookup_lt_Some in Hexttablookup.
            by lias.
          }
          rewrite Coqlib.list_map_nth.
          specialize (ext_tabs_lookup_exist _ _ _ Hexttablookup) as Hexplookup.
          destruct Hexplookup as [k Hexplookup].
          rewrite list_lookup_fmap in Hexplookup.
          destruct (v_imps !! k) as [mexp | ] eqn: Hvimpslookup => //.
          simpl in Hexplookup.
          inversion Hexplookup; subst; clear Hexplookup.
          destruct mexp => /=.
          simpl in *; subst.
          Search v_imps.
          destruct (t_imps !! k) as [tk | ] eqn: Htimpslookup; last by apply lookup_ge_None in Htimpslookup; apply lookup_lt_Some in Hvimpslookup; lias.
          specialize (Himpwasm _ _ _ Hvimpslookup Htimpslookup).
          simpl in *.
          destruct Himpwasm as [tab [tt [Htablookup [Hwtslookup2 [-> Htabtype]]]]].
          rewrite - nth_error_lookup in Hexttablookup.
          rewrite Hexttablookup.
          simpl.
          rewrite nth_error_app1; last by apply lookup_lt_Some in Htablookup.
          rewrite nth_error_lookup.
          rewrite Htablookup.
          rewrite Hwtslookup2 in Hwtslookup.
          inversion Hwtslookup; subst; clear Hwtslookup.
          replace (N_of_int t) with (N_of_nat (nat_of_int t)); first by apply/N.leb_spec0; lias.
          unfold nat_of_int, N_of_int.
          by rewrite Z_nat_N.
        }
        {
          (* Allocated memory *)
          rewrite nth_error_app2; last first.
          { rewrite map_length.
            apply lookup_ge_None in Hexttablookup.
            by lias.
          }
          apply lookup_ge_None in Hexttablookup.
          
          assert (n - length (ext_tabs (modexp_desc <$> v_imps)) < length mod_tables) as Hmtlen.
          {
            replace (length (ext_tabs _)) with (length (ext_t_tabs t_imps)) in *.
            - move/ssrnat.leP in Hlen1.
              rewrite -> Nat.le_succ_l in Hlen1.
              by lias.
            - clear - Hvtlen Himpwasm.
              move: Hvtlen Himpwasm.
              move: t_imps.
              elim: v_imps; destruct t_imps => //.
              move => Hvtlen Himpwasm.
              simpl in *.
              inversion Hvtlen; clear Hvtlen.
              specialize (H _ H1).
              forward H Hlen.
              {
                move => k v t Hlk Htk.
                specialize (Himpwasm (S k) v t).
                simpl in Himpwasm.
                by specialize (Himpwasm Hlk Htk).
              }
              unfold oapp.
              specialize (Himpwasm 0 a e).
              simpl in Himpwasm.
              do 2 forward Himpwasm Himpwasm => //.
              destruct a.
              simpl in *.
              destruct modexp_desc.
              * destruct f.
                destruct Himpwasm as [? [? [? ->]]].
                apply H.
                by apply Hp.
              * destruct t.
                destruct Himpwasm as [? [? [? [? [-> ?]]]]].
                simpl.
                by f_equal.
              * destruct m.
                destruct Himpwasm as [? [? [? [? [? [-> ?]]]]]].
                apply H.
                by apply Hp.
              * destruct g.
                destruct Himpwasm as [? [? [? [? [-> ?]]]]].
                apply H.
                by apply Hp.
          }
          rewrite nth_error_lookup gen_index_lookup map_length => //=.
          rewrite nth_error_app2; last by lias.
          rewrite nat_minus_plus.
          repeat rewrite Coqlib.list_map_nth.
          rewrite nth_error_lookup.
          destruct (mod_tables !! _) as [mt | ] eqn:Hmtlookup => //=.
          destruct mt, modtab_type, tt_limits => /=.
          clear - Hebound.
          simpl in Hebound.
          unfold N_of_int.
          unfold nat_of_int in Hebound.
          Search N.of_nat.
          rewrite Nat2N.inj_add in Hebound.
          rewrite Z_nat_N in Hebound.
          rewrite repeat_length.
          apply/N.leb_spec0.
          by rewrite - N_nat_bin.
        }
      + apply lookup_ge_None in Hmelem.
        rewrite Heinitslen in Hmelem.
        apply lookup_ge_None in Hmelem.
        rewrite Hmelem.
        by constructor.
      (* 20220419: I think there's a genuine case where this will not succeed.
         Check and add this to the pre, if necessary. *)
      (* 20220426: This is resolved: the bound check condition is added, and it's highly likely that it should work
         looking at the current proof progress. *)
    - (* memory initializers bound check *)

      
      (* Method is similar to table initialisers, but details are a bit simpler *)
      apply alloc_glob_gen_index in Hallocglob as [? [? [? [? ?]]]]; last by lias.
      apply alloc_mem_gen_index in Hallocmem as [? [? [? [? ?]]]].
      apply alloc_tab_gen_index in Halloctab as [? [? [? [? ?]]]].
      apply alloc_func_gen_index in Hallocfunc as [? [? [? [? ?]]]].
      destruct ws, s0, s1, s2, s3.
      simpl in *; subst; simpl in *.

      unfold module_data_bound_check_gmap in Hdbound.

      (* Prove all2 by proving arbitrary lookups *)
      apply all2_Forall2.
      rewrite Forall2_lookup.
      move => i.
      destruct (m.(mod_data) !! i) eqn:Hmdata => /=.
      + destruct (d_inits !! i) eqn: Hdinit => /=; last by apply lookup_lt_Some in Hmdata; apply lookup_ge_None in Hdinit; lias.
        constructor.
        apply fmap_fmap_lookup with (i0 := i) in Hmoddata.
        repeat rewrite list_lookup_fmap in Hmoddata.
        rewrite Hmdata Hdinit in Hmoddata.
        simpl in Hmoddata.
        inversion Hmoddata; subst; clear Hmoddata.
        destruct m0.
        simpl in *.
        subst.
        destruct moddata_data => /=.
        destruct m.
        simpl in *.
        (*
        unfold module_typing in Hmodtype.
        destruct Hmodtype as [fts [gts [? [? [? [? [Helemtype _]]]]]]].
        rewrite -> Forall_lookup in Helemtype.
        specialize (Helemtype _ _ Hmelem).
        unfold module_elem_typing in Helemtype.
        destruct Helemtype as [_ [_ [Hlen1 Hlen2]]].
        rewrite app_length in Hlen1.
        rewrite map_length in Hlen1.
        simpl in *.

        rewrite -> Forall_lookup in Hebound.
        specialize (Hebound _ _ Hmelem).
        simpl in Hebound.*)

        rewrite -> Forall_lookup in Hdbound.

        specialize (Hdbound _ _ Hmdata).
        simpl in Hdbound.

        unfold ext_mem_addrs.
        unfold compose.
        
        destruct (ext_mems (modexp_desc <$> v_imps) !! n) as [memid | ] eqn:Hextmemlookup => //.
        {
          (* Initialiser is for an imported memory *)
          destruct memid as [memn].

          destruct (wms !! N.of_nat memn) as [mi | ] eqn:Hwmslookup => //.

          rewrite nth_error_app1; last first.
          { rewrite map_length.
            apply lookup_lt_Some in Hextmemlookup.
            by lias.
          }
          rewrite Coqlib.list_map_nth.
          specialize (ext_mems_lookup_exist _ _ _ Hextmemlookup) as Hexplookup.
          destruct Hexplookup as [k Hexplookup].
          rewrite list_lookup_fmap in Hexplookup.
          destruct (v_imps !! k) as [mexp | ] eqn: Hvimpslookup => //.
          simpl in Hexplookup.
          inversion Hexplookup; subst; clear Hexplookup.
          destruct mexp => /=.
          simpl in *; subst.
          Search v_imps.
          destruct (t_imps !! k) as [tk | ] eqn: Htimpslookup; last by apply lookup_ge_None in Htimpslookup; apply lookup_lt_Some in Hvimpslookup; lias.
          specialize (Himpwasm _ _ _ Hvimpslookup Htimpslookup).
          simpl in *.
          destruct Himpwasm as [mem [mt [b_init [Hmemlookup [Hwmslookup2 [Hwmslookup3 Hmemtype]]]]]].
          rewrite - nth_error_lookup in Hextmemlookup.
          rewrite Hextmemlookup.
          simpl in *.
          rewrite nth_error_app1; last by apply lookup_lt_Some in Hmemlookup.
          rewrite nth_error_lookup.
          rewrite Hmemlookup.
          rewrite Hwmslookup2 in Hwmslookup.
          inversion Hwmslookup; subst; clear Hwmslookup.
          unfold instantiation.mem_length, memory_list.mem_length.
          simpl.
          replace (N_of_int t) with (N_of_nat (nat_of_int t)); last by unfold nat_of_int, N_of_int; rewrite Z_nat_N.
          apply/N.leb_spec0.
          unfold mem_length, memory_list.mem_length in Hdbound.
          by lias.
        }
        {
          (* Allocated memory *)
          rewrite nth_error_app2; last first.
          { rewrite map_length.
            apply lookup_ge_None in Hextmemlookup.
            by lias.
          }
          apply lookup_ge_None in Hextmemlookup.

          destruct (mod_mems !! (n-length (ext_mems (modexp_desc <$> v_imps)))) as [mm | ] eqn:Hmmlookup => //.
          specialize (lookup_lt_Some _ _ _ Hmmlookup) as Hmmlookuplen.
          
          assert (n - length (ext_mems (modexp_desc <$> v_imps)) < length mod_mems) as Hmmlen.
          {
            replace (length (ext_mems _)) with (length (ext_t_mems t_imps)) in *.
            - by lias.
            - clear - Hvtlen Himpwasm.
              move: Hvtlen Himpwasm.
              move: t_imps.
              elim: v_imps; destruct t_imps => //.
              move => Hvtlen Himpwasm.
              simpl in *.
              inversion Hvtlen; clear Hvtlen.
              specialize (H _ H1).
              forward H Hlen.
              {
                move => k v t Hlk Htk.
                specialize (Himpwasm (S k) v t).
                simpl in Himpwasm.
                by specialize (Himpwasm Hlk Htk).
              }
              unfold oapp.
              specialize (Himpwasm 0 a e).
              simpl in Himpwasm.
              do 2 forward Himpwasm Himpwasm => //.
              destruct a.
              simpl in *.
              destruct modexp_desc.
              * destruct f.
                destruct Himpwasm as [? [? [? ->]]].
                apply H.
                by apply Hp.
              * destruct t.
                destruct Himpwasm as [? [? [? [? [-> ?]]]]].
                by f_equal.
              * destruct m.
                destruct Himpwasm as [? [? [? [? [? [-> ?]]]]]].
                simpl.
                by f_equal.
              * destruct g.
                destruct Himpwasm as [? [? [? [? [-> ?]]]]].
                apply H.
                by apply Hp.
          }
          rewrite nth_error_lookup gen_index_lookup map_length => //=.
          rewrite nth_error_app2; last by lias.
          rewrite nat_minus_plus.
          repeat rewrite Coqlib.list_map_nth.
          rewrite nth_error_lookup.
          clear - Hdbound Hmmlookup.
          simpl in Hdbound.
          unfold N_of_int.
          unfold nat_of_int in Hdbound.
          rewrite Nat2N.inj_add in Hdbound.
          rewrite Z_nat_N in Hdbound.
          unfold Coqlib.option_map.
          destruct mm.
          rewrite Hmmlookup.
          unfold instantiation.mem_length, memory_list.mem_length.
          simpl in *.
          rewrite repeat_length.
          rewrite N2Nat.id.
          apply/N.leb_spec0.
          by lias.
        }
      + apply lookup_ge_None in Hmdata.
        rewrite Hdinitslen in Hmdata.
        apply lookup_ge_None in Hmdata.
        rewrite Hmdata.
        by constructor.
    - (* start function *)
      unfold check_start.
      by rewrite Hmodstart.
    - (* putting initlialized items into the store *)
      apply/eqP.
      by eauto.
  }

  destruct Hinst as [ws_res Hinst].

  assert (insert_exports vis hs_exps v_exps <> None) as Hinsertvis.
  {
    rewrite Heqv_exps.
    destruct m.
    simpl in *.
    (*
    elim => /=; destruct mod_exports => //=.
    move => hs_exp hs_exps IH Hlenexp.
    inversion Hlenexp; clear Hlenexp.
    destruct (insert_exports vis hs_exps (list_fmap _ _ _ mod_exports)) eqn:Hinsert => //.
    exfalso.*)
    admit.
  }
  
  iApply fupd_mask_intro; first by set_solver.
  
  iIntros "Hmask".
  iSplit.
  
  - destruct s => //.
    iPureIntro.
    unfold language.reducible.

(*
    
    exists [], (([::], [::]): host_expr), (ws_res, insert_exports vis hs_exps v_exps, ms), [].
    unfold language.prim_step => /=.
    repeat split => //.
    replace [] with (map_start None) => //.
    eapply HR_host_step => //.*)
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
Admitted.


Lemma instantiation_spec_operational_start (s: stuckness) E (hs_mod: N) (hs_imps: list vimp) (v_imps: list module_export) (hs_exps: list vi) (m: module) t_imps t_exps wfs wts wms wgs nstart (Φ: host_val -> iProp Σ):
  m.(mod_start) = Some (Build_module_start (Mk_funcidx nstart)) ->
  module_typing m t_imps t_exps ->
  instantiation_resources_pre hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps -∗
  (∀ idnstart, (↪[frame] empty_frame) -∗ (instantiation_resources_post hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps (Some idnstart)) -∗ WP (([::], [::AI_invoke idnstart]) : host_expr) {{ Φ }}) -∗
  WP (([:: ID_instantiate hs_exps hs_mod hs_imps], [::]): host_expr) @ s; E {{ Φ }}.
Proof.
Admitted.

End Instantiation_spec_operational.


(* Examples *)

Section Example_Add.
  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wtablimitG Σ, !wmemG Σ, !wmemsizeG Σ, !wmemlimitG Σ, !wglobG Σ, !wframeG Σ, !hvisG Σ, !hmsG Σ}.

  
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

(*
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
  iApply (instantiation_spec_operational_no_start with "[Hmod Hhv]"); unfold instantiation_resources_pre; [ | | iFrame] => //.
  - by apply add_module_valid.
  - unfold import_resources_host, import_resources_wasm_typecheck, export_ownership_host.
    instantiate (1 := [::]).
    do 4 (instantiate (1 := ∅)).
    repeat iSplit => //=.
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
  iApply (instantiation_spec_operational_no_start with "[Hmod Hvimp Hwfcl Hhv]"); [ | by apply M2_valid |] => //.
  - unfold instantiation_resources_pre.
    do 3 instantiate (1 := ∅).
    instantiate (1 := <[ n := cl ]> ∅).
    unfold import_resources_host.
    unfold big_sepL2.
    instantiate (1 := [::{| modexp_name := expname0; modexp_desc := MED_func (Mk_funcidx n) |}]) => /=.
    unfold import_resources_wasm_typecheck => /=.
    unfold export_ownership_host => /=.
    iFrame.
    iSplitL "Hwfcl".
    + iSplit => //.
      iExists cl.
      iFrame.
      iPureIntro.
      rewrite lookup_insert.
      split => //.
      by rewrite Hcltype.
    + iSplit => //.
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

*)
(* ***************** END OF EXAMPLES ********************* *)

(* No longer in use

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
      
*)
End Example_Add.

                   

End Iris_host.
