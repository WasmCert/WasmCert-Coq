From mathcomp Require Import ssreflect eqtype seq ssrbool ssrfun.
From iris.program_logic Require Import language weakestpre lifting.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris_locations iris_properties iris_rules_resources iris_wp_def stdpp_aux iris_instantiation iris.
Require Export datatypes host operations properties opsem instantiation.
Require Export type_preservation.

Close Scope byte.

Section Iris_host_def.

(* Domain of the variable instantiation store *)
Definition vi := N.

(* variable import/export store. *)
Definition vi_store := gmap vi module_export.

Definition module_decl := module.

(* an import is specified by giving the index of the instance to the module_export and a second index in the list*)
Definition vimp : Type := vi.


Inductive host_e: Type :=
| ID_instantiate: list vi -> N -> list vimp -> host_e
| H_get_global: globaladdr -> host_e.

(* What a host function can do : *)
Inductive host_action : Type :=
| HA_nothing : host_action
| HA_print : host_action
| HA_instantiate : host_e -> host_action
| HA_call_wasm : host_action
| HA_modify_table : host_action
.




Definition map_start (start: option nat) : list administrative_instruction :=
  match start with
  | Some n => [AI_invoke n]
  | None => []
  end.

Definition lookup_export_vi (vis: vi_store) (vimp: vimp) : option module_export:=
  vis !! vimp.

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

Definition stab_update s i idx newval :=
  match List.nth_error (s_tables s) i with 
  | None => None
  | Some stab_i =>
      if length (table_data stab_i) <? idx then None
      else
        Some {| s_funcs := s_funcs s ;
               s_mems := s_mems s ;
               s_globals := s_globals s ;
               s_tables := update_list_at (s_tables s) i
                                          {| table_data := update_list_at (table_data stab_i) idx (Some newval) ;
                                            table_max_opt := table_max_opt stab_i |}
             |} 
  end.


Definition update_table s f idx newval :=
   match f.(f_inst).(inst_tab) with
  | nil => None
  | ta :: q => stab_update s ta idx newval
  end.


Fixpoint no_more_locals llh :=
  match llh with
  | LL_base _ _ => true
  | LL_label _ _ _ llh _ => no_more_locals llh
  | LL_local _ _ _ _ _  => false end. 

Fixpoint innermost_frame llh defaultf :=
  match llh with
  | LL_base _ _ => defaultf 
  | LL_label _ _ _ llh _ => innermost_frame llh defaultf
  | LL_local _ _ f llh _ => if no_more_locals llh then f else innermost_frame llh defaultf
  end. 

Inductive host_reduce: store_record -> vi_store -> list module -> list host_e -> list host_action -> frame -> list administrative_instruction -> store_record -> vi_store -> list module -> list host_e -> list host_action -> frame -> list administrative_instruction -> Prop :=
| HR_host_step:
  forall s (vis: vi_store) m (viexps: list vi) vm vimps imps imp_descs s' vis' ms idecs' inst (exps: list module_export) start vs f fs,
    ms !! (N.to_nat vm) = Some m ->
    those ((lookup_export_vi vis) <$> vimps) = Some imps ->
    fmap (fun imp => imp.(modexp_desc)) imps = imp_descs ->
    instantiate s m imp_descs ((s', inst, exps), start) ->
    length viexps = length exps ->
    const_list vs ->
    insert_exports vis viexps exps = Some vis' ->
    host_reduce s vis ms ((ID_instantiate viexps vm vimps) :: idecs') fs f vs s' vis' ms idecs' fs f (map_start start)
| HR_host_step_init_oob: forall s (vis: vi_store) m (viexps: list vi) vm vimps imps imp_descs ms idecs' (exps: list module_export) f vs fs,
    ms !! (N.to_nat vm) = Some m ->
    those ((lookup_export_vi vis) <$> vimps) = Some imps ->
    fmap (fun imp => imp.(modexp_desc)) imps = imp_descs ->
    const_list vs ->
    (not (module_elem_bound_check_gmap (gmap_of_list s.(s_tables)) imp_descs m /\
            module_data_bound_check_gmap (gmap_of_list s.(s_mems)) imp_descs m)) ->
    host_reduce s vis ms ((ID_instantiate viexps vm vimps) :: idecs') fs f vs s vis ms idecs' fs f [AI_trap]
 | HR_call_host_action :
  forall (s:store_record) vis ms idecs (s':store_record) (tf:function_type)
    (h:hostfuncidx) (hi:nat) f
    (vcs:seq.seq value) fs
    (res : seq.seq administrative_instruction) (LI : seq.seq administrative_instruction) LI' lh f0,
    h = Mk_hostfuncidx hi ->
    fs !! hi = Some f ->
    (* if the action requires knowledge of the frame, it looks up the innermost frame 
       closest to the AI_call_host *)
    execute_action f s (innermost_frame lh f0) vcs s' res ->
    llfill lh [AI_call_host tf h vcs] = LI ->
    llfill lh res = LI' ->
    host_reduce s vis ms idecs fs f0 LI s' vis ms idecs fs f0 LI'
| HR_call_host_instantiate :
  forall s vis ms idecs h hi f fs LI LI' lh f0,
    h = Mk_hostfuncidx hi ->
    fs !! hi = Some (HA_instantiate f) ->
    llfill lh [AI_call_host (Tf [] []) h []] = LI ->
    llfill lh [] = LI' ->
    host_reduce s vis ms idecs fs f0 LI s vis ms (f :: idecs) fs f0 LI' 
| HR_wasm_step: forall s vis ms idecs s' es es' f1 f2 fs,
    opsem.reduce s f1 es s' f2 es' ->
    host_reduce s vis ms idecs fs f1 es s' vis ms idecs fs f2 es'
| HR_get_global: ∀ s f vis ms g v_glob fs vs,
    (s_globals s) !! g = Some v_glob ->
    const_list vs ->
    host_reduce s vis ms [H_get_global g] fs f vs s vis ms [] fs f (AI_basic (BI_const (g_val v_glob)) :: vs)
| HR_trap: ∀ s vis ms g fs f,
    host_reduce s vis ms [H_get_global g] fs f [::AI_trap] s vis ms [] fs f [::AI_trap]

                
with execute_action : host_action -> store_record -> frame -> list value -> store_record -> list administrative_instruction -> Prop :=
| execute_nothing : forall s f, execute_action HA_nothing s f [] s []
| execute_print : forall s f v, execute_action HA_print s f [v] s []
| execute_call_wasm : forall s f i, execute_action HA_call_wasm s f [VAL_int32 i] s [AI_basic (BI_call (Wasm_int.nat_of_uint i32m i))]
| execute_modify_table : forall s f tab_idx func_idx s' a,
    List.nth_error f.(f_inst).(inst_funcs) (Wasm_int.nat_of_uint i32m func_idx) = Some a ->
    update_table s f (Wasm_int.nat_of_uint i32m tab_idx) a = Some s' ->
    execute_action HA_modify_table s f [VAL_int32 tab_idx ; VAL_int32 func_idx]
                   s' []
.


Lemma llfill_const es lh LI :
  llfill lh es = LI -> const_list LI -> const_list es.
Proof.
  intros Hfill Hconst.
  destruct lh.
  - unfold llfill in Hfill. subst. unfold const_list in Hconst.
    repeat rewrite forallb_app in Hconst.
    apply andb_true_iff in Hconst as [_ Hconst].
    apply andb_true_iff in Hconst as [? _] => //.
  - unfold llfill in Hfill. subst.
    unfold const_list in Hconst ; rewrite forallb_app in Hconst ; simpl in Hconst.
    apply andb_true_iff in Hconst as [_ ?] => //.
  - unfold llfill in Hfill ; subst.
    unfold const_list in Hconst ; rewrite forallb_app in Hconst ; simpl in Hconst.
    apply andb_true_iff in Hconst as [_ ?] => //.
Qed. 


Lemma lh_of_sh_inj s0 s1 :
  lh_of_sh s0 = lh_of_sh s1 -> s0 = s1.
Proof.
  generalize dependent s1 ; induction s0 ; destruct s1 => //=.
  intro H ; inversion H ; subst ; clear H.
  generalize dependent l1 ; induction l ; intros l1 H ; destruct l1 => //=.
  simpl in H ; inversion H. specialize (IHl _ H2). by inversion IHl.
  intro H ; inversion H ; subst ; clear H. rewrite (IHs0 _ H4). 
 clear IHs0. generalize dependent l2 ; induction l ; intros l2 H ; destruct l2 => //=.
  simpl in H ; inversion H. specialize (IHl _ H2). by inversion IHl.
Qed.



Lemma llfill_unique e1 lh1 e2 lh2 :
  llfill lh1 [e1] = llfill lh2 [e2] ->
  e1 = e2 /\ lh1 = lh2 \/ (is_const e1) \/ is_const e2 \/
    (exists a b c, e1 = AI_label a b c \/ e2 = AI_label a b c)
  \/ (exists a b c, e1 = AI_local a b c \/ e2 = AI_local a b c).
Proof.
  intros Hfill.
  rewrite - (cat0s [_]) in Hfill.
  rewrite - (cat0s [e2]) in Hfill.
  destruct (is_const e1) eqn:He1, (is_const e2) eqn:He2 ;
    try by right ; (left + (right ; left)).
  destruct e1, e2 ;
    try by right ; right ; right ; (left + right ; eexists _,_,_ ; left + right).
  all: destruct (llfill_first_values Hfill Logic.eq_refl) as [??] => //.
  all: destruct H0 as [_ ->] => //.
  all: by left. 
Qed. 

Lemma sfill_const_list sh es :
  const_list (sfill sh es) -> const_list es.
Proof.
  destruct sh => //= ;
  intro H ; unfold const_list in H ; repeat rewrite forallb_app in H.
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [? _] => //.
  simpl in H. apply andb_true_iff in H as [??] => //.
Qed.
  

Lemma call_host_no_reduce tf h vcs s0 f s'0 f' es' llh LI:
  llfill llh [AI_call_host tf h vcs] = LI ->
  reduce s0 f LI s'0 f' es' -> False.
Proof.
  intros HLI Hred.
  apply val_head_stuck_reduce in Hred.
  fold (of_val (callHostV tf h vcs llh)) in HLI.
  subst. rewrite to_of_val in Hred => //.
Qed.

Lemma execute_action_det f s vcs s1 f0 res1 s2 res2 :
  execute_action f s f0 vcs s1 res1 -> execute_action f s f0 vcs s2 res2 ->
  s1 = s2 /\ res1 = res2.
Proof.
  intros Hea1 Hea2.
  inversion Hea1 ; inversion Hea2 ; subst => //.
  inversion H8 => //.
  inversion H12 ; subst. rewrite H in H7. inversion H7 ; subst.
  rewrite H0 in H8. by inversion H8. 
Qed.

Lemma llfill_trap_singleton es lh :
  llfill lh [es] = [AI_trap] -> lh = LL_base [] [] ∧ es = AI_trap.
Proof.
  intros Hfill.
  destruct lh.
  - inversion Hfill. destruct l,l0 =>//.
    simpl in H0. inversion H0;auto.
  - simpl in Hfill. destruct l =>//.
  - simpl in Hfill. destruct l =>//.
Qed.


Lemma call_host_reduce_det s vis ms idecs fs tf h vcs s1 vis1 ms1 idecs1 fs1 f1 es1 s2 vis2 ms2 idecs2 fs2 f2 es2 f0 llh LI :
  llfill llh [AI_call_host tf h vcs] = LI ->
  host_reduce s vis ms idecs fs f0 LI s1 vis1 ms1 idecs1 fs1 f1 es1 ->
  host_reduce s vis ms idecs fs f0 LI s2 vis2 ms2 idecs2 fs2 f2 es2 ->
  (s1, vis1, ms1, idecs1, fs1, f1, es1) = (s2, vis2, ms2, idecs2, fs2, f2, es2).
Proof.
  intros HLI Hred1 Hred2.
  induction Hred1.
  - apply (llfill_const _ _ _ HLI) in H4 => //.
  - apply (llfill_const _ _ _ HLI) in H2 => //. 
  - induction Hred2.
    + apply (llfill_const _ _ _ HLI) in H9 => //.
    + apply (llfill_const _ _ _ HLI) in H7 => //.
    + subst. rewrite - H7 in H2.
      apply llfill_unique in H2 as [[H ->] | [? | [? | [ (?&?&?&[?|?]) | (?&?&?&[?|?])]]]] => //=.
      inversion H ; subst.
      rewrite H0 in H5. inversion H5 ; subst.
      destruct (execute_action_det _ _ _ _ _ _ _ _ H1 H6) as (-> & ->) => //. 
    + simplify_eq. rewrite - H6 in H2. 
      apply llfill_unique in H2 as [[H ->] | [? | [? | [ (?&?&?&[?|?]) | (?&?&?&[?|?])]]]] => //=.
      inversion H ; subst.
      rewrite H0 in H5 ; inversion H5 ; subst ; inversion H1.
    + simplify_eq. exfalso ; by eapply call_host_no_reduce.
    + simplify_eq. by eapply llfill_const in H5;eauto.
    + simplify_eq. by apply llfill_trap_singleton in H2 as [? ?].
  - induction Hred2.
    + apply (llfill_const _ _ _ HLI) in H8 => //.
    + apply (llfill_const _ _ _ HLI) in H6 => //.
    + subst. rewrite - H6 in H1.
      apply llfill_unique in H1 as [[ H -> ] | [? | [? | [ (?&?&?&[?|?]) | (?&?&?&[?|?])]]]] => //=.
      inversion H ; subst. rewrite H0 in H4 ; inversion H4 ; subst.
      inversion H5.
    + subst. rewrite - H5 in H1.
      apply llfill_unique in H1 as [[ H -> ] | [? | [? | [ (?&?&?&[?|?]) | (?&?&?&[?|?])]]]] => //=.
      inversion H ; subst. rewrite H0 in H4 ; inversion H4 ; subst.
      done.
    + simplify_eq. exfalso ; by eapply call_host_no_reduce.
    + simplify_eq. by eapply llfill_const in H4;eauto.
    + simplify_eq. by apply llfill_trap_singleton in H1 as [? ?].
  - simplify_eq ; exfalso ; by eapply call_host_no_reduce.
  - simplify_eq. by eapply llfill_const in H0;eauto.
  - simplify_eq. by apply llfill_trap_singleton in HLI as [? ?].
Qed.

Lemma get_global_host_det he s vis ms fs f0 vs s1 vis1 ms1 idecs1 fs1 f1 vs1 vs2 s2 vis2 ms2 idecs2 fs2 f2 :
  const_list vs ->
  host_reduce s vis ms [H_get_global he] fs f0 vs s1 vis1 ms1 idecs1 fs1 f1 vs1 ->
  host_reduce s vis ms [H_get_global he] fs f0 vs s2 vis2 ms2 idecs2 fs2 f2 vs2 ->
  (s1, vis1, ms1, idecs1, fs1, f1, vs1) = (s2, vis2, ms2, idecs2, fs2, f2, vs2).
Proof.
  intros Hconst Hred1 Hred2.
  inversion Hred1;simplify_eq;try done;try by (eapply call_host_reduce_det in Hred2;eauto). 
  { eapply values_no_reduce in H;auto. done. }
  inversion Hred2;simplify_eq;try done;try by (eapply call_host_reduce_det in Hred2;eauto). 
  eapply values_no_reduce in H;auto. done.
Qed.  

Lemma trap_host_det g s vis ms fs f0 s1 vis1 ms1 idecs1 fs1 f1 vs1 vs2 s2 vis2 ms2 idecs2 fs2 f2 :
  host_reduce s vis ms [g] fs f0 [AI_trap] s1 vis1 ms1 idecs1 fs1 f1 vs1 ->
  host_reduce s vis ms [g] fs f0 [AI_trap] s2 vis2 ms2 idecs2 fs2 f2 vs2 ->
  (s1, vis1, ms1, idecs1, fs1, f1, vs1) = (s2, vis2, ms2, idecs2, fs2, f2, vs2).
Proof.
  intros Hred1 Hred2.
  remember [g]. remember [AI_trap].
  inversion Hred1;simplify_eq;try done.
  { by (eapply call_host_reduce_det in Hred1;eauto). }
  { by (eapply call_host_reduce_det in Hred1;eauto). }
  { apply test_no_reduce_trap in H. done. }
  { inversion Hred2;simplify_eq;try done;try by (eapply call_host_reduce_det in Hred1;eauto).
    apply test_no_reduce_trap in H. done. 
  }
Qed.  


Definition host_expr : Type := (list host_e) * (list administrative_instruction).

(* val is almost the same as native Wasm, defined in Iris.v, just without callHostV, brV and retV*)

Inductive host_val : Type :=
| immHV : (list value) -> host_val
| trapHV : host_val.

Definition val_of_host_val hv :=
  match hv with
  | immHV vs => immV vs
  | trapHV => trapV
  end.

Definition state : Type := store_record * vi_store * (list module) * (list host_action ) * frame.

Definition observation := unit. 

Definition of_val (v: host_val) : host_expr := ([::], iris.of_val (val_of_host_val v)).

Lemma of_val_imm (vs : list value) :
  ([::], ((λ v : value, AI_basic (BI_const v)) <$> vs)) = of_val (immHV vs).
Proof. done. Qed.

Definition to_val (e: host_expr) : option host_val :=
  match e with
  | (e' :: es, _) => None
  | ([::], wes) => match iris.to_val wes with
                 | Some (immV vs) => Some (immHV vs)
                 | Some (trapV) => Some trapHV
                 | Some (brV _ _) 
                 | Some (retV _) 
                 | Some (callHostV _ _ _ _)
                 | None => None
                 end
  end.


Definition prim_step (e : host_expr) (s : state) (os : list observation) (e' : host_expr) (s' : state) (fork_es' : list host_expr) : Prop :=
  let '(ws, vis, ms, fs, f) := s in
  let '(ws', vis', ms', fs', f') := s' in
  let '(hes, wes) := e in
  let '(hes', wes') := e' in
    host_reduce ws vis ms hes fs f wes ws' vis' ms' hes' fs' f' wes' /\ os = [] /\ fork_es' = [].


Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  unfold to_val, of_val.
  rewrite iris.to_of_val.
  destruct v => //=.
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  destruct e as [hes wes] => /=.
  destruct hes => //.
  move => Htv.
  destruct (iris.to_val wes) eqn:Hwes => //.
  apply iris.of_to_val in Hwes.
  destruct v0 => //= ; try by simplify_eq. 
Qed.

Lemma val_head_stuck : forall e1 s1 κ e2 s2 efs,
  prim_step e1 s1 κ e2 s2 efs →
  to_val e1 = None.
Proof.
  rewrite /prim_step.
  move => [hes wes] [[[[ws vis] hprog] fs] f] κ [hes' wes'] [[[[ws' vis'] hprog'] fs'] f'] efs [HRed _].
  induction HRed ; (try destruct idecs) => //=.
  - destruct (iris.to_val LI) eqn:Hwes => //.
    destruct v => //.
    apply to_val_const_list in Hwes.
    apply llfill_const in H2 => //.
    apply to_val_trap_is_singleton in Hwes as ->. 
    destruct lh ; simpl in H2 ;  destruct l => //.
  - destruct (iris.to_val LI) eqn:Hwes => //=.
    destruct v => //.
    apply to_val_const_list in Hwes.
    apply llfill_const in H1 => //.
    apply to_val_trap_is_singleton in Hwes as ->.
    destruct lh ; simpl in H1 ; destruct l => //. 
  - erewrite iris.val_head_stuck_reduce => //.
Qed.

Lemma wasm_host_mixin : LanguageMixin of_val to_val prim_step.
Proof. split; eauto using to_of_val, of_to_val, val_head_stuck. Qed.

Canonical Structure wasm_host_lang := Language wasm_host_mixin.

Implicit Type σ : state.

(* The host expands the memory model of Wasm by vi_store and a list of module declarations. *)

Class hvisG Σ := HVisG {
                    vis_genG :> ghost_mapG Σ N module_export;
                    visGName : gname
}.

Class hmsG Σ := HMsG {
                   ms_genG :> ghost_mapG Σ N module;
                   msGName : gname
                 }.

Class hasG Σ := HAsG {
                   ha_genG :> ghost_mapG Σ N host_action;
                   haGName : gname
                 }.

Definition proph_id := positive.

Instance eqdecision_vi: EqDecision vi.
Proof. move => n n'. unfold Decision. by decidable_equality. Qed.

Instance eqdecision_frame: EqDecision frame.
Proof. decidable_equality. Qed.

Instance eqdecision_module: EqDecision module.
Proof. move => m m'. unfold Decision. by decidable_equality. Qed.

Instance eqdecision_module_export: EqDecision (list module_export).
Proof. decidable_equality. Qed.

Instance eqdecision_inst_decl: EqDecision host_e.
Proof. move => i i'. unfold Decision. destruct i, i';try by right.
       { destruct (list_eq_dec l l1), (list_eq_dec l0 l2), (decide (n = n0)) ;
           try by right ; congruence. by left ; subst. }
       { destruct (decide (g = g0));subst;[by left|right].
         intros Hcontr. congruence. } Qed.

Instance eqdecision_host_action: EqDecision host_action.
Proof. move => m m'. unfold Decision. destruct m, m' ; try by (left + right).
       destruct (eqdecision_inst_decl h h0).
       by left ; subst.
       by right ; congruence. Qed.

End Iris_host_def.

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


Global Instance host_heapG_irisG `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ} : weakestpre.irisGS wasm_host_lang Σ := {
  iris_invGS := func_invG; (* ??? *)
  state_interp σ _ κs _  :=
    let: (s, vis, ms, fs, f) := σ in
     ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
      (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
      (gen_heap_interp (gmap_of_list s.(s_globals))) ∗
      (ghost_map_auth visGName 1 vis) ∗ 
      (ghost_map_auth msGName 1 (gmap_of_list ms)) ∗
      (ghost_map_auth haGName 1 (gmap_of_list fs)) ∗
      (ghost_map_auth frameGName 1 (<[ tt := f ]> ∅)) ∗ 
      (gen_heap_interp (gmap_of_list (fmap mem_length s.(s_mems)))) ∗
      (gen_heap_interp (gmap_of_list (fmap tab_size s.(s_tables)))) ∗
      (@gen_heap_interp _ _ _ _ _ memlimit_hsG (gmap_of_list (fmap mem_max_opt s.(s_mems)))) ∗
      (@gen_heap_interp _ _ _ _ _ tablimit_hsG (gmap_of_list (fmap table_max_opt s.(s_tables))))
    )%I;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
}.




Section Iris_host.
  

Section host_lifting.
Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}.


Lemma wp_call_host_action_no_state_change s E hes tf h hi f vcs (Φ : host_val -> iProp Σ) res llh LI LI' :
  h = Mk_hostfuncidx hi ->
  llfill llh [AI_call_host tf h vcs] = LI ->
  llfill llh res = LI' ->
  (forall s0 f0, execute_action f s0 f0 vcs s0 res) -> 
  N.of_nat hi ↦[ha] f ∗
  ▷ (N.of_nat hi ↦[ha] f -∗ WP ((hes, LI') : host_expr) @ s ; E {{ v, Φ v }})
  ⊢ WP ((hes, LI) : host_expr) @ s ; E {{ v, Φ v }}.
Proof.
  iIntros (Hh HLI HLI' Hexec) "(Hhi & Hwp)".
  iApply lifting.wp_lift_step => //=.
  - destruct hes => //.
    fold (iris.of_val (callHostV tf h vcs llh)) in HLI.
    subst. rewrite iris.to_of_val => //. 
  - iIntros (σ ns κ κs nt) "Hσ".
    iApply fupd_mask_intro ; first by solve_ndisj.
    iIntros "Hfupd".
    destruct σ as [[[[ws vi] ms] has] f0].
    iDestruct "Hσ" as "(? & ? & ? & ? & ? & ? & Hha & ? & ? & ? & ? & ?)".
    iDestruct (ghost_map_lookup with "Hha Hhi") as "%Hf0".
    rewrite gmap_of_list_lookup Nat2N.id in Hf0.
    iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], (_,_), (_,_,_,_,_), [].
    repeat split => //=.
    eapply HR_call_host_action => //.
  - iIntros "!>" (es σ2 efs HStep).
    destruct σ2 as [[[[s2 vi2] ms2] has2] f2].
    destruct es as [hes2 es2].
    iMod "Hfupd". iDestruct ("Hwp" with "Hhi") as "Hwp".
    iModIntro.
    destruct HStep as [HStep [-> ->]].
    eapply call_host_reduce_det in HStep ; last first.
    eapply HR_call_host_action => //=.
    exact HLI. inversion HStep ; subst.
    iFrame. done.  
Qed.

Lemma wp_get_global_host s E g v vs (Φ : host_val -> iProp Σ) :
  N.of_nat g ↦[wg] v -∗
  ▷ (N.of_nat g ↦[wg] v -∗ Φ (immHV ((g_val v) :: vs))) -∗
  WP (([H_get_global g], v_to_e_list vs) : host_expr) @ s; E {{ Φ }}.
Proof.
  iIntros "Hglob HΦ".
  iApply lifting.wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[[s0 vis] ms] fs] f].
  iDestruct "Hσ" as "(? & ? & ? & Hg & ?)".
  iDestruct (gen_heap_valid with "Hg Hglob") as "%Hglob".
  rewrite gmap_of_list_lookup Nat2N.id in Hglob.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    eexists [], (_,_), (_, _, _, _, _), [].
    repeat split => //.
    apply HR_get_global;eauto. apply v_to_e_is_const_list.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[[s1 vis1] ms1] fs1] f1] => // /=.
    destruct es as [? ?].
    simpl in HStep. destruct HStep as [H [-> ->]].
    eapply get_global_host_det in H;[..|apply HR_get_global;eauto];[|apply v_to_e_is_const_list..].
    inversion H;subst. iFrame. iSimpl.
    assert (iris.to_val (AI_basic (BI_const (g_val v)) :: v_to_e_list vs)%SEQ =
              Some (immV (g_val v :: vs))).
    { rewrite separate1.
      assert ([AI_basic (BI_const (g_val v))] = v_to_e_list [(g_val v)]) as ->;auto.
      erewrite v_to_e_cat. rewrite to_val_cons_immV. auto. }
    rewrite H0. iSimpl. iSplit =>//.  iApply "HΦ". iFrame.
Qed.

Lemma wp_get_global_trap_host s E g (Φ : host_val -> iProp Σ) :
  ▷ (Φ trapHV) -∗
  WP (([H_get_global g], [AI_trap]) : host_expr) @ s; E {{ Φ }}.
Proof.
  iIntros " HΦ".
  iApply lifting.wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[[s0 vis] ms] fs] f].
  iDestruct "Hσ" as "(? & ? & ? & Hg & ?)".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    eexists [], (_,_), (_, _, _, _, _), [].
    repeat split => //.
    apply HR_trap;eauto.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[[s1 vis1] ms1] fs1] f1] => // /=.
    destruct es as [? ?].
    simpl in HStep. destruct HStep as [H [-> ->]].
    eapply trap_host_det in H;[..|apply HR_trap].
    inversion H;subst. iFrame. iSimpl. done.
Qed.

Lemma wp_call_host_instantiate s E hes h hi f (Φ : host_val -> iProp Σ) llh LI LI' :
  h = Mk_hostfuncidx hi ->
  llfill llh [AI_call_host (Tf [] []) h []] = LI ->
  llfill llh [] = LI' ->
  N.of_nat hi ↦[ha] (HA_instantiate f) ∗
  ▷ (N.of_nat hi ↦[ha] (HA_instantiate f) -∗ WP ((f :: hes, LI') : host_expr) @ s ; E {{ v, Φ v }})
  ⊢ WP ((hes, LI) : host_expr) @ s ; E {{ v, Φ v }}.
Proof.
  iIntros (Hh HLI HLI') "(Hhi & Hwp)".
  iApply lifting.wp_lift_step => //=.
  - destruct hes => //. subst.
    fold (iris.of_val (callHostV (Tf [] []) (Mk_hostfuncidx hi) [] llh)).
    rewrite iris.to_of_val => //. 
  - iIntros (σ ns κ κs nt) "Hσ".
    iApply fupd_mask_intro ; first by solve_ndisj.
    iIntros "Hfupd".
    destruct σ as [[[[ws vi] ms] has] f0].
    iDestruct "Hσ" as "(? & ? & ? & ? & ? & ? & Hha & ? & ? & ? & ? & ?)".
    iDestruct (ghost_map_lookup with "Hha Hhi") as "%Hf0".
    rewrite gmap_of_list_lookup Nat2N.id in Hf0.
    iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], (_,_), (_,_,_,_,_), [].
    repeat split => //=.
    eapply HR_call_host_instantiate => //.
  - iIntros "!>" (es σ2 efs HStep).
    destruct σ2 as [[[[s2 vi2] ms2] has2] f2].
    destruct es as [hes2 es2].
    iMod "Hfupd".
    iModIntro.
    iDestruct ("Hwp" with "[$]") as "Hwp".
    destruct HStep as [HStep [-> ->]].
    eapply call_host_reduce_det in HStep ; last first.
    eapply HR_call_host_instantiate => //=.
    exact HLI. inversion HStep ; subst.
    iFrame. done.  
Qed.

Lemma wp_call_host_modify_table s E h hi tab_idx func_idx LI LI' llh f0 n func_idx0 hes a Φ :
  h = Mk_hostfuncidx hi ->
  llfill llh [AI_call_host (Tf [T_i32 ; T_i32] []) h [VAL_int32 tab_idx ; VAL_int32 func_idx]] = LI ->
  llfill llh [] = LI' ->
  (innermost_frame llh f0).(f_inst).(inst_funcs) !! (Wasm_int.nat_of_uint i32m func_idx) = Some a -> 
  (innermost_frame llh f0).(f_inst).(inst_tab) !! 0 = Some n ->
  ↪[frame] f0 ∗
   N.of_nat hi ↦[ha] HA_modify_table ∗
   N.of_nat n ↦[wt][ Wasm_int.N_of_uint i32m tab_idx ] func_idx0 ∗
   ▷ (↪[frame] f0 ∗
       N.of_nat hi ↦[ha] HA_modify_table ∗
       N.of_nat n ↦[wt][ Wasm_int.N_of_uint i32m tab_idx ] Some a -∗
       WP ((hes, LI') : host_expr) @ s ; E {{ Φ }})
   ⊢ WP ((hes, LI) : host_expr) @ s ; E {{ Φ }}.
Proof.
  iIntros (Hh HLI HLI' Ha Hn) "(Hf & Hhi & Hwt & Hwp)".
  iApply lifting.wp_lift_step => //=.
  - destruct hes => //. subst.
    fold (iris.of_val (callHostV (Tf [T_i32 ; T_i32] []) (Mk_hostfuncidx hi) [VAL_int32 tab_idx ; VAL_int32 func_idx ] llh)).
    rewrite iris.to_of_val => //. 
  - iIntros (σ ns κ κs nt) "Hσ".
    destruct σ as [[[[ws vi] ms] has] f1].
    iDestruct "Hσ" as "(Hfunc & Htab & ? & ? & ? & ? & Hha & Hf1 & ? & Htabsize & ? & ?)".
    iDestruct (ghost_map_lookup with "Hha Hhi") as "%Hha".
    rewrite gmap_of_list_lookup Nat2N.id in Hha.
    rewrite - nth_error_lookup in Ha.
    iDestruct (ghost_map_lookup with "Hf1 Hf") as "%Hf0".
    rewrite lookup_insert in Hf0. inversion Hf0 ; subst ; clear Hf0.
    destruct (inst_tab (f_inst (innermost_frame llh f0))) eqn:Hf => //. 
    simpl in Hn ; inversion Hn ; subst ; clear Hn.
    iDestruct (gen_heap_valid with "Htab Hwt") as "%H".
    simplify_lookup.
    rewrite - nth_error_lookup in Heq.
    destruct (nth_error (s_tables ws) n) eqn:Htables.
    2:{ apply (nth_error_none_fmap _ _ table_to_list) in Htables.
        rewrite Htables in Heq. done. }
    rewrite (map_nth_error table_to_list _ _ Htables) in Heq.
    inversion Heq ; subst ; clear Heq.
    unfold table_to_list in H.
    specialize (lookup_lt_Some _ _ _ H) as Hlt.
    replace (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned tab_idx))) with
      (Wasm_int.nat_of_uint i32m tab_idx) in Hlt ; last by rewrite Z_N_nat.
    iApply fupd_mask_intro ; first by solve_ndisj.
    iIntros "Hfupd".
    iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], (_,_), (_,_,_,_,_), [].
    repeat split => //=.
    eapply HR_call_host_action => //.
    eapply execute_modify_table => //.
    unfold update_table. 
    rewrite Hf. unfold stab_update.
    rewrite Htables. 
    destruct (length (table_data t) <? _) eqn:Habs'.
    apply ltb_lt in Habs'. lia.
    done.
  - iIntros "!>" (es σ2 efs HStep).
    destruct σ2 as [[[[s2 vi2] ms2] has2] f2].
    destruct es as [hes2 es2].
    destruct HStep as [HStep [-> ->]].
    eapply call_host_reduce_det in HStep ; last first.
    eapply HR_call_host_action => //=.
    eapply execute_modify_table => //.
    2: done.
    unfold update_table. rewrite Hf. unfold stab_update. rewrite Htables.
    unfold table_to_list in H. destruct (_ <? _) eqn:Habs.
    apply ltb_lt in Habs. lia. done. 
    inversion HStep ; subst. simpl.
    iMod (gen_heap_update with "Htab Hwt") as "[Htab Hwt]".
    iMod "Hfupd".
    iDestruct ("Hwp" with "[$]") as "Hwp".
    (* instantiate (1:= Some a).  *)
    iFrame. repeat rewrite fmap_update_list_at => /=.
    rewrite (update_trivial (table_max_opt <$> _)).
    rewrite (update_trivial (tab_size <$> _)). iFrame.
    erewrite gmap_of_table_insert.
    rewrite Nat2N.id. 
    repeat rewrite update_list_at_insert.
    instantiate (1 := t).
    rewrite Z_N_nat. done.
    simpl in Hlt. done.
    rewrite nth_error_lookup in Htables ; apply lookup_lt_Some in Htables. done.
    rewrite Nat2N.id. by rewrite - nth_error_lookup.
    rewrite Z_N_nat. done.
    apply (map_nth_error tab_size) in Htables.
    rewrite nth_error_lookup in Htables.
    rewrite Htables. unfold tab_size => /=.
    rewrite update_length => //.
    apply (map_nth_error table_max_opt) in Htables.
    rewrite nth_error_lookup in Htables. done. 
Qed.

Definition reducible := @reducible wasm_host_lang.




Lemma wp_value s E (e : host_expr) v Φ :
  to_val e = Some v ->
  Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof.
  intro.
  iIntros "HΦ".
  iApply weakestpre.wp_value.
  unfold IntoVal.
  apply of_to_val.
  done.
  done.
Qed.

Lemma wp_lift_wasm s E δ es Φ:
  WP es @ NotStuck; E {{ v, WP ((δ, iris.of_val v) : host_expr) @ s; E {{ Φ }} }}
     ⊢ WP ((δ, es) : host_expr) @ s; E {{ Φ }}.
Proof.
  iLöb as "IH"
forall (s E es Φ).
  iIntros "Hwp".
  destruct (to_val ((δ,es))) eqn:Htv.
  { iApply weakestpre.wp_unfold.
    rewrite /weakestpre.wp_pre /=.
    iDestruct (wp_unfold with "Hwp") as "Hwp".
    rewrite /wp_pre /=.
    destruct δ => //.
    simpl in Htv.
    destruct (iris.to_val es) => //.
    rewrite weakestpre.wp_unfold /weakestpre.wp_pre /= iris.to_of_val.
    destruct v ; by iMod "Hwp". }
  rewrite weakestpre.wp_unfold.
  iDestruct (wp_unfold with "Hwp") as "Hwp".
  rewrite /wp_pre /=.
  rewrite /weakestpre.wp_pre /=.
  unfold to_val in Htv ; rewrite Htv.
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es) eqn:Hes.
  { apply iris.of_to_val in Hes as <-.
    iMod "Hwp".
    iDestruct (weakestpre.wp_unfold with "Hwp") as "Hwp".
    rewrite /weakestpre.wp_pre /=.
    rewrite iris.to_of_val Htv.
    iSpecialize ("Hwp" $! σ ns κ κs nt with "[$]").
    by iApply "Hwp". }
  destruct σ as [[[[s0 vis] ms] has] f].
  iDestruct "Hσ" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)".
  destruct f as [loc ins].
  iSpecialize ("Hwp" $! (s0, loc, ins) ns κ κs nt with "[$]").
  iMod "Hwp" as "[%Hs He2]".
  iModIntro.
  iSplit.
  { destruct s => //.
    iPureIntro.
    destruct Hs as (obs & es' & [[??]?] & efs & ? & -> & ->).
    eexists [], (_,_), (_,_,_,_,_), [].
    repeat split => //.
    eapply HR_wasm_step.
    exact H. }
  iIntros ([δ2 es2] [[[[s2 vis2] ms2] has2] f2] efs (Hred & -> & ->)).
  destruct Hs as (obs & es' & [[??]?] & efs & Hredes & -> & ->).
  inversion Hred ; simplify_eq ; 
    (try by exfalso ; eapply values_no_reduce) ;
    try by subst ; exfalso ; eapply call_host_no_reduce.
  destruct f2 as [l2 i2].
  assert (iris.prim_step es (s0, loc, ins) [] es2 (s2, l2, i2) []) as Hstep.
  repeat split => //.
  iSpecialize ("He2" $! es2 (s2, l2, i2) [] Hstep).
  iMod "He2".
  repeat iModIntro.
  repeat iMod "He2".
  iDestruct "He2" as "[Hσ Hf]".
  iDestruct "Hσ" as "(?&?&?&?&?&?&?&?&?)".
  iFrame.
  iDestruct "Hf" as (f) "(Hf & Hwp & ?)".
  iDestruct ("Hwp" with "Hf") as "Hwp".
  iModIntro ; iSplit ; last done.
  iApply ("IH" with "Hwp").
Qed.


End host_lifting.

Section host_structural.
  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ }.

Lemma prim_step_inst_cons_reduce_nostart v_exps modi m v_imps ws1 vis1 ms1 ha1 f1 κ (es es': list host_e) wes σ2 efs vs:
  ms1 !! N.to_nat modi = Some m ->
  mod_start m = None ->
  const_list vs ->
  prim_step ((ID_instantiate v_exps modi v_imps :: es), vs) (ws1, vis1, ms1, ha1, f1) κ (es', wes) σ2 efs ->
  prim_step ([ID_instantiate v_exps modi v_imps], []) (ws1, vis1, ms1, ha1, f1) [] ([], wes) σ2 [] /\ κ = [] /\ efs = [] /\ es' = es /\ (wes = [] \/ wes = [AI_trap]).
Proof.
  move => Hmodi Hnostart Hconst HStep.
  destruct σ2 as [[[[ws2 vis2] ms2] ha2] f2].
  simpl in *.
  destruct HStep as [HStep [-> ->]].
  inversion HStep; subst; clear HStep.
  { repeat split => //; last first.
    { rewrite H3 in Hmodi.
      inversion Hmodi; subst m0.
      unfold instantiate in H9.
      destruct H9 as [? [? [? [? [? [? [_ [_ [_ [_ [_ [_ [_ [_ [Hstart _]]]]]]]]]]]]]]].
      unfold check_start in Hstart.
      rewrite Hnostart in Hstart.
      move/eqP in Hstart.
      simpl in Hstart.
      by subst start; simpl; left.
    }
    by eapply HR_host_step => //.
  }
  { repeat split => //.
    { by eapply HR_host_step_init_oob. }
    { by right. }
  }
  { by eapply llfill_const in Hconst => //. }
  { by eapply llfill_const in Hconst => //. }
  { by eapply values_no_reduce in Hconst => //. }
Qed.
  
Lemma wp_seq_host_nostart (s : stuckness) (E : coPset) (Φ Ψ : host_val -> iProp Σ) v_exps modi v_imps m (es : list host_e) vs:
  m.(mod_start) = None ->
  const_list vs ->
  ¬ Ψ (trapHV) -∗
  modi ↪[mods] m -∗
  (modi ↪[mods] m -∗ WP (([::ID_instantiate v_exps modi v_imps], [::]): host_expr) @ E {{ w, Ψ w ∗ modi ↪[mods] m }}) -∗
  (∀ w, Ψ w -∗ modi↪[mods] m -∗ WP ((es, [::]): host_expr) @ E {{ v, Φ v }}) -∗
  WP (((ID_instantiate v_exps modi v_imps :: es), vs): host_expr) @ E {{ v, Φ v }}.
Proof.
  move => Hnostart Hconst.
  iIntros "Hntrap Hmod Hes1 Hes2".
                 
  iApply weakestpre.wp_unfold. repeat rewrite weakestpre.wp_unfold /weakestpre.wp_pre /=.

  iIntros (σ ns κ κs nt) "Hσ".
  destruct σ as [[[[ws vis] ms] ha] f].
  iDestruct "Hσ" as "(Hf & Ht & Hm & Hg & Hvis & Hms & Hha & Hframe & Hmemlen & Htabsize & Hmemlim & Htablim)".
  iDestruct (ghost_map_lookup with "Hms Hmod") as "%Hmodlookup".
  iSpecialize ("Hes1" with "Hmod").
  iSpecialize ("Hes1" $! (ws, vis, ms, ha, f) ns κ κs nt).
  iSpecialize ("Hes1" with "[$]").

  iMod "Hes1".
  iModIntro.
  iDestruct "Hes1" as "(%Hred & Hes1)".
  iFrame.

  rewrite gmap_of_list_lookup in Hmodlookup.
  
  iSplit.
  - unfold language.reducible in *.
    destruct Hred as [κ' [e' [σ' [efs HStep]]]].
    destruct e' as [we' he'].
    unfold language.prim_step.
    simpl in HStep.
    destruct σ' as [[[[ws' vis'] ms'] fs'] f'].
    destruct HStep as [HStep [-> ->]].
    inversion HStep; subst; clear HStep.
    { iPureIntro.
      exists [::], ((es, map_start None): host_expr), (ws', vis', ms', fs', f'), [::].
      repeat split => //.
      eapply HR_host_step => //.
      instantiate (1 := inst).
      rewrite H3 in Hmodlookup; inversion Hmodlookup; subst m0; clear Hmodlookup.
      replace start with (None: option nat) in H9 => //.
      unfold instantiate in H9.
      destruct H9 as [? [? [? [? [? [? [_ [_ [_ [_ [_ [_ [_ [_ [Hstart _]]]]]]]]]]]]]]].
      unfold check_start in Hstart.
      rewrite Hnostart in Hstart.
      move/eqP in Hstart.
      by simpl in Hstart.
    }
    { iPureIntro.
      exists [::], ((es, [AI_trap]): host_expr), (ws', vis', ms', fs', f'), [::].
      repeat split => //.
      by eapply HR_host_step_init_oob => //.
    }
    { by apply llfill_is_nil in H2; destruct H2 as [??]. }
    { by apply llfill_is_nil in H1; destruct H1 as [??]. }
    { by apply empty_no_reduce in H. }

  - iIntros (e2 σ2 efs HStep).
    destruct σ2 as [[[[ws2 vis2] ms2] fs2] f2].
    destruct e2 as [he2 we2].
    eapply prim_step_inst_cons_reduce_nostart in HStep as [HStep [-> [-> [-> Hwsor]]]] => //.
    destruct Hwsor.
    { subst we2.
      iSpecialize ("Hes1" $! ([], []) (ws2, vis2, ms2, fs2, f2) [] HStep).
      iMod "Hes1"; iModIntro.
      iModIntro.
      repeat (iMod "Hes1"; iModIntro).
      iFrame.
      iDestruct "Hes1" as "(Hσ & Hwp)".
      iFrame.
      iSplit => //.
      iDestruct "Hwp" as "(Hwp & _)".
      replace (([], []): host_expr) with (language.of_val (immHV [::])) => //.
      rewrite weakestpre.wp_value_fupd'.
      iMod "Hwp".
      iDestruct "Hwp" as "(HΨ & Hmodi)".
      by iApply ("Hes2" with "[$HΨ] [$Hmodi]").
    }
    { subst we2.
      iSpecialize ("Hes1" $! ([], [AI_trap]) (ws2, vis2, ms2, fs2, f2) [] HStep).
      iMod "Hes1"; iModIntro.
      iModIntro.
      repeat (iMod "Hes1"; iModIntro).
      iFrame.
      iDestruct "Hes1" as "(Hσ & Hwp)".
      iFrame.
      iSplit => //.
      iDestruct "Hwp" as "(Hwp & _)".
      replace (([], [AI_trap]): host_expr) with (language.of_val (trapHV)) => //.
      rewrite weakestpre.wp_value_fupd'.
      iMod "Hwp".
      iDestruct "Hwp" as "(HΨ & Hmodi)".
      by iDestruct ("Hntrap" with "HΨ") as "%".
    } 
Qed.

End host_structural.



Section Instantiation_spec_operational.

Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}.

(* Resources in the host vis store for the imports *)
Definition import_resources_host (hs_imps: list vimp) (v_imps : list module_export): iProp Σ :=
  [∗ list] i ↦ hs_imp; v_imp ∈ hs_imps; v_imps,
  hs_imp ↪[vis] v_imp.


Definition export_ownership_host (hs_exps: list vi) : iProp Σ :=
  [∗ list] i ↦ hs_exp ∈ hs_exps,
  ∃ hv, hs_exp ↪[vis] hv.

(* The resources for module exports. This is a bit more complicated since it is allowed to export the imported elements,
   adding another case to be considered. *)
Definition module_export_resources_host (hs_exps: list vi) (m_exps: list module_export) (inst: instance) : iProp Σ :=
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

Definition instantiation_resources_pre hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps : iProp Σ :=
  hs_mod ↪[mods] m ∗
  import_resources_host hs_imps v_imps ∗
  instantiation_resources_pre_wasm m v_imps t_imps wfs wts wms wgs ∗       
  export_ownership_host hs_exps ∗
  ⌜ length hs_exps = length m.(mod_exports) ⌝.

Definition instantiation_resources_post hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps (idfstart: option nat) : iProp Σ :=
  hs_mod ↪[mods] m ∗
  import_resources_host hs_imps v_imps ∗ (* vis, for the imports stored in host *)
  ∃ (inst: instance), 
  instantiation_resources_post_wasm m v_imps t_imps wfs wts wms wgs idfstart inst ∗       
  module_export_resources_host hs_exps m.(mod_exports) inst. (* export resources, in the host store *)

Lemma insert_exports_none_len vis iexps exps:
  insert_exports vis iexps exps = None ->
  length iexps <> length exps.
Proof.
  move: iexps exps vis.
  induction iexps; intros => //.
  destruct exps => //=.
  move => Hlen.
  inversion Hlen; clear Hlen.
  simpl in H.
  destruct (insert_exports vis iexps exps) eqn:H0 => //.
  by eapply IHiexps in H1 => //.
Qed.

Ltac forward H Hname :=
  lazymatch type of H with
  | ?Hx -> _ => let Hp := fresh "Hp" in
              assert Hx as Hp; last specialize (H Hp) as Hname end.


Lemma host_export_state_update vis vis' inst hs_exps mexp:
  ⌜ length hs_exps = length mexp ⌝ -∗
  ⌜ insert_exports vis hs_exps ((fun m_exp => {| modexp_name := modexp_name m_exp; modexp_desc := export_get_v_ext inst (modexp_desc m_exp) |}) <$> mexp) = Some vis' ⌝ -∗
  ghost_map_auth visGName 1 vis -∗
  export_ownership_host hs_exps -∗ |==>
  (ghost_map_auth visGName 1 vis' ∗
   module_export_resources_host hs_exps mexp inst).
Proof.
  move : vis vis' inst mexp.
  iInduction hs_exps as [|a] "IH"; iIntros (vis vis' inst mexp) "%Hlen %Hie".
  - simpl in Hie.
    inversion Hie; subst; clear Hie.
    iIntros "Hvis _".
    iModIntro.
    iFrame.
    unfold module_export_resources_host.
    simpl in Hlen.
    by destruct mexp.
  - destruct mexp => //=.
    simpl in Hlen.
    simpl in Hie.
    destruct (insert_exports _ _ _) eqn:Hie2 => //.
    inversion Hlen; clear Hlen.
    inversion Hie; subst; clear Hie.
    iSpecialize ("IH" $! _ _ _ _ (H0) (Hie2)).
    iIntros "Hσ Hexport".
    unfold export_ownership_host.
    iSimpl in "Hexport".
    iDestruct "Hexport" as "(Hv & Hexport)".
    iSpecialize ("IH" with "[$] [$]").
    iMod "IH" as "(Hσ & Hexport)".
    iDestruct "Hv" as (hv) "Hv" => /=.
    iDestruct (ghost_map_update with "Hσ Hv") as "Hupd".
    iMod "Hupd" as "(Hσ & Hv)".
    iModIntro.
    iFrame.
    by iExists (modexp_name m).
Qed.

Lemma instantiation_spec_operational_no_start (s: stuckness) E (hs_mod: N) (hs_imps: list vimp) (v_imps: list module_export) (hs_exps: list vi) (m: module) t_imps t_exps wfs wts wms wgs :
  m.(mod_start) = None ->
  module_typing m t_imps t_exps ->
  module_restrictions m ->
  instantiation_resources_pre hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps -∗
  WP (([:: ID_instantiate hs_exps hs_mod hs_imps], [::]): host_expr) @ s; E
   {{ v, ⌜ v = immHV [] ⌝ ∗
        instantiation_resources_post hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps None }}.
Proof.
  
  move => Hmodstart Hmodtype Hmodrestr.
  assert (module_restrictions m) as Hmodrestr2 => //.
  
  iIntros "(Hmod & Himphost & Himpwasmpre & Hexphost & %Hlenexp)".
  iDestruct "Himpwasmpre" as "(Himpwasm & %Hebound & %Hdbound)".
  
  repeat rewrite weakestpre.wp_unfold /weakestpre.wp_pre /=.
  
  iIntros ([[[[ws vis] ms] has] f] ns κ κs nt) "Hσ".
  iDestruct "Hσ" as "(Hwf & Hwt & Hwm & Hwg & Hvis & Hms & Hhas & Hframe & Hmsize & Htsize & Hmlimit & Htlimit)".

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

  destruct (alloc_funcs ws (mod_funcs m) inst_res) eqn:Hallocfunc.
  destruct (alloc_tabs s0 (map modtab_type (mod_tables m))) eqn:Halloctab.
  destruct (alloc_mems s1 (mod_mems m)) eqn:Hallocmem.
  destruct (alloc_globs s2 (mod_globals m) g_inits) eqn:Hallocglob.

  remember (fmap (fun m_exp => {| modexp_name := modexp_name m_exp; modexp_desc := export_get_v_ext inst_res (modexp_desc m_exp) |}) m.(mod_exports)) as v_exps.

  remember (init_mems 
    (init_tabs s3 inst_res
       [seq Z.to_nat (Wasm_int.Int32.intval o) | o <- e_inits] 
       (mod_elem m)) inst_res
    [seq Z.to_N (Wasm_int.Int32.intval o) | o <- d_inits] 
    (mod_data m)) as ws_res.
  
  (* Prove that the instantiation predicate holds *)
  assert ((instantiate ws m (fmap modexp_desc v_imps) ((ws_res, inst_res, v_exps), None))) as Hinst.
  {
    unfold instantiate, instantiation.instantiate.
    unfold alloc_module => /=.


    exists t_imps, t_exps, s3, g_inits.

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
        destruct f0.
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
        destruct Himpwasm as [mem [mt [Hwm [? [-> Hmt]]]]].
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
        f_equal.
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

      apply alloc_glob_gen_index in Hallocglob as [? [? [? [? ?]]]]; last by lias.
      apply alloc_mem_gen_index in Hallocmem as [? [? [? [? ?]]]].
      apply alloc_tab_gen_index in Halloctab as [? [? [? [? ?]]]].
      apply alloc_func_gen_index in Hallocfunc as [? [? [? [? ?]]]].
      destruct ws, s0, s1, s2, s3.
      simpl in *; subst; simpl in *.

      unfold module_elem_bound_check_gmap in Hebound.

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
                destruct Himpwasm as [? [? [? [? [-> ?]]]]].
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
    - (* memory initializers bound check *)

      
      apply alloc_glob_gen_index in Hallocglob as [? [? [? [? ?]]]]; last by lias.
      apply alloc_mem_gen_index in Hallocmem as [? [? [? [? ?]]]].
      apply alloc_tab_gen_index in Halloctab as [? [? [? [? ?]]]].
      apply alloc_func_gen_index in Hallocfunc as [? [? [? [? ?]]]].
      destruct ws, s0, s1, s2, s3.
      simpl in *; subst; simpl in *.

      unfold module_data_bound_check_gmap in Hdbound.

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
          destruct (t_imps !! k) as [tk | ] eqn: Htimpslookup; last by apply lookup_ge_None in Htimpslookup; apply lookup_lt_Some in Hvimpslookup; lias.
          specialize (Himpwasm _ _ _ Hvimpslookup Htimpslookup).
          simpl in *.
          destruct Himpwasm as [mem [mt [Hmemlookup [Hwmslookup2 [Hwmslookup3 Hmemtype]]]]].
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
                destruct Himpwasm as [? [? [? [? [-> ?]]]]].
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

  assert (length hs_exps = length v_exps) as Hlenexp2.
  {
    rewrite Hlenexp.
    rewrite Heqv_exps.
    by rewrite map_length.
  }

  (* Assert that the new vis store exists and is what we want *)
  assert (exists vis', insert_exports vis hs_exps v_exps = Some vis') as Hinsertexp.
  {
    destruct (insert_exports vis hs_exps v_exps) as [ovis | ] eqn:Hovis; first by eexists.
    exfalso.
    apply insert_exports_none_len in Hovis.
    by apply Hovis; clear Hovis.
  }

  assert (length (lookup_export_vi vis <$> hs_imps) = length v_imps) as Hvilen.
  {
    by rewrite fmap_length.
  }
    
  assert (those (lookup_export_vi vis <$> hs_imps) = Some v_imps) as Hvilookup.
  {
    apply those_projection_backward => //.
    move => k.
    rewrite list_lookup_fmap.
    rewrite fmap_length in Hvilen.
    destruct (hs_imps !! k) eqn:Hhsimpsk => /=.
    - destruct (v_imps !! k) eqn:Hvimpsk.
      + by eapply Himphost in Hhsimpsk => //.
      + apply lookup_lt_Some in Hhsimpsk.
        apply lookup_ge_None in Hvimpsk.
        rewrite Hvilen in Hhsimpsk.
        by lias.
    - destruct (v_imps !! k) eqn:Hvimpsk => //.
      + apply lookup_lt_Some in Hvimpsk.
        apply lookup_ge_None in Hhsimpsk.
        rewrite Hvilen in Hhsimpsk.
        by lias.
  }

  destruct Hinsertexp as [vis' Hinsertexp].
  
  iApply fupd_mask_intro; first by solve_ndisj.
  
  iIntros "Hmask".
  iSplit.
  
  - destruct s => //.
    iPureIntro.
    unfold language.reducible, language.prim_step.
    exists [::], ([::], map_start None), (ws_res, vis', ms, has, f), [::].
    repeat split => //.
    by eapply HR_host_step.
  - iIntros ([hes' wes'] [[[[ws3 vis3] ms3] has3] f3] efs HStep).
    destruct HStep as [HStep [-> ->]].
    revert Heqinst_res.
    inversion HStep; subst; clear HStep; move => Heqinst_res.
    

    5: {
      (* Wasm reduction is impossible. *)
      by apply empty_no_reduce in H.
    }

    (* The two branches about host actions *)
    4: by apply llfill_is_nil in H1 as [??] => //.
    
    3:  by apply llfill_is_nil in H2 as [??] => //. 

    2: { 

      iDestruct (import_resources_wts_subset with "Hwt Htsize Htlimit [Himpwasm]") as "%Hwt" => //.
      { by iDestruct "Himpwasm" as "(?&?&?&?)". } 
      specialize (Hwt Hvtlen).
      
      iDestruct (import_resources_wms_subset with "Hwm Hmsize Hmlimit [Himpwasm]") as "%Hwm" => //.
      { by iDestruct "Himpwasm" as "(?&?&?&?)". } 
      specialize (Hwm Hvtlen).
      
      exfalso.
      apply H20. clear H20.
      rewrite Hmod in H3. 
      inversion H3; symmetry in H0; subst; clear H3. 
    
      rewrite Hvilookup in H7.
      inversion H7; subst; clear H7.

      split.
      - by eapply module_elem_bound_check_gmap_extend.
      - by eapply module_data_bound_check_gmap_extend.
    } 

    (* On to the main branch, the only possible reduction (successful case) *)

    rewrite Hmod in H3.
    
    revert Heqinst_res.
    inversion H3; symmetry in H0; subst; clear H3.
    
    rewrite Hvilookup in H4.
    inversion H4; subst; clear H4.

    move => Heqinst_res.
    
    iIntros "!>!>!>".

    specialize (instantiate_det _ _ _ _ _ Hinst H9) as Hinsteq.

    destruct ws3.
    simpl in *.
    inversion Hinsteq.
    simpl.

    (* Wasm state update, using the instantiation characterisation lemma *)
    iDestruct (instantiation_wasm_spec with "") as "H" => //.
    iDestruct ("H" with "[Himpwasm] [Hwf Hwt Hwm Hwg Hmsize Htsize Hmlimit Htlimit]") as "Hq".
    { unfold instantiation_resources_pre_wasm.
      by iFrame.
    }
    { unfold gen_heap_wasm_store.
      by iFrame.
    }

    iClear "H".

    iMod "Hq" as "(Hwasmpost & Hσ)".
    unfold gen_heap_wasm_store => /=.
    iDestruct "Hσ" as "(?&?&?&?&?&?&?&?)".
    iFrame.

    rewrite <- H3.
    rewrite <- H2 in H22.

    rewrite -> H1 in *.

    (* host state update *)
    rewrite Hinsertexp in H22.
    revert Heqinst_res.
    inversion H22; subst; clear H22.
    move => Heqinst_res.
    
    rewrite fmap_length in H20.
    iDestruct (host_export_state_update $! H20 Hinsertexp with "[$] [$]") as "H".
    
    iMod "H" as "(Hvis & Hexphost)".
    
    iFrame.

    iMod "Hmask".


    iModIntro.

    iApply weakestpre.wp_value; first by instantiate (1 := immHV []) => //.

    iSplit => //.

    iExists inst.
    
    by iFrame.

Qed.

(* Instantiating modules with a start function. We combine the handling of sequence here all in one. *)
Lemma instantiation_spec_operational_start_seq s E (hs_mod: N) (hs_imps: list vimp) (v_imps: list module_export) (hs_exps: list vi) (m: module) t_imps t_exps wfs wts wms wgs nstart (Φ: host_val -> iProp Σ) idecls:
  m.(mod_start) = Some (Build_module_start (Mk_funcidx nstart)) ->
  module_typing m t_imps t_exps ->
  module_restrictions m ->
  ↪[frame] empty_frame -∗                            
  instantiation_resources_pre hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps -∗
  (∀ idnstart, (↪[frame] empty_frame) -∗ (instantiation_resources_post hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps (Some idnstart)) -∗ WP ((idecls, [::AI_invoke idnstart]) : host_expr) @ s; E {{ Φ }}) -∗
  WP (((ID_instantiate hs_exps hs_mod hs_imps) :: idecls, [::]): host_expr) @ s; E {{ Φ }}.
Proof.
  move => Hmodstart Hmodtype Hmodrestr.
  assert (module_restrictions m) as Hmodrestr2 => //.
  
  iIntros "Hframeown (Hmod & Himphost & Himpwasmpre & Hexphost & %Hlenexp) Hwpstart".
  iDestruct "Himpwasmpre" as "(Himpwasm & %Hebound & %Hdbound)".
  
  repeat rewrite weakestpre.wp_unfold /weakestpre.wp_pre /=.
  
  iIntros ([[[[ws vis] ms] has] f] ns κ κs nt) "Hσ".
  iDestruct "Hσ" as "(Hwf & Hwt & Hwm & Hwg & Hvis & Hms & Hhas & Hframe & Hmsize & Htsize & Hmlimit & Htlimit)".

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

  destruct (alloc_funcs ws (mod_funcs m) inst_res) eqn:Hallocfunc.
  destruct (alloc_tabs s0 (map modtab_type (mod_tables m))) eqn:Halloctab.
  destruct (alloc_mems s1 (mod_mems m)) eqn:Hallocmem.
  destruct (alloc_globs s2 (mod_globals m) g_inits) eqn:Hallocglob.

  remember (fmap (fun m_exp => {| modexp_name := modexp_name m_exp; modexp_desc := export_get_v_ext inst_res (modexp_desc m_exp) |}) m.(mod_exports)) as v_exps.

  remember (init_mems 
    (init_tabs s3 inst_res
       [seq Z.to_nat (Wasm_int.Int32.intval o) | o <- e_inits] 
       (mod_elem m)) inst_res
    [seq Z.to_N (Wasm_int.Int32.intval o) | o <- d_inits] 
    (mod_data m)) as ws_res.
  
  remember (nth_error (inst_funcs inst_res) nstart) as ostart.
  
  (* Prove that the instantiation predicate holds *)
  assert ((instantiate ws m (fmap modexp_desc v_imps) ((ws_res, inst_res, v_exps), ostart ))) as Hinst.
  {
    unfold instantiate, instantiation.instantiate.
    unfold alloc_module => /=.


    exists t_imps, t_exps, s3, g_inits.

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
        destruct f0.
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
        destruct Himpwasm as [mem [mt [Hwm [? [-> Hmt]]]]].
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
        f_equal.
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

      apply alloc_glob_gen_index in Hallocglob as [? [? [? [? ?]]]]; last by lias.
      apply alloc_mem_gen_index in Hallocmem as [? [? [? [? ?]]]].
      apply alloc_tab_gen_index in Halloctab as [? [? [? [? ?]]]].
      apply alloc_func_gen_index in Hallocfunc as [? [? [? [? ?]]]].
      destruct ws, s0, s1, s2, s3.
      simpl in *; subst; simpl in *.

      unfold module_elem_bound_check_gmap in Hebound.

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
                destruct Himpwasm as [? [? [? [? [-> ?]]]]].
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
          destruct (t_imps !! k) as [tk | ] eqn: Htimpslookup; last by apply lookup_ge_None in Htimpslookup; apply lookup_lt_Some in Hvimpslookup; lias.
          specialize (Himpwasm _ _ _ Hvimpslookup Htimpslookup).
          simpl in *.
          destruct Himpwasm as [mem [mt [Hmemlookup [Hwmslookup2 [Hwmslookup3 Hmemtype]]]]].
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
                destruct Himpwasm as [? [? [? [? [-> ?]]]]].
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
      rewrite Heqostart.
      by rewrite Hmodstart.
    - (* putting initlialized items into the store *)
      apply/eqP.
      by eauto.
  }

  assert (length hs_exps = length v_exps) as Hlenexp2.
  {
    rewrite Hlenexp.
    rewrite Heqv_exps.
    by rewrite map_length.
  }

  (* Assert that the new vis store exists and is what we want *)
  assert (exists vis', insert_exports vis hs_exps v_exps = Some vis') as Hinsertexp.
  {
    destruct (insert_exports vis hs_exps v_exps) as [ovis | ] eqn:Hovis; first by eexists.
    exfalso.
    apply insert_exports_none_len in Hovis.
    by apply Hovis; clear Hovis.
  }

  assert (length (lookup_export_vi vis <$> hs_imps) = length v_imps) as Hvilen.
  {
    by rewrite fmap_length.
  }
    
  assert (those (lookup_export_vi vis <$> hs_imps) = Some v_imps) as Hvilookup.
  {
    apply those_projection_backward => //.
    move => k.
    rewrite list_lookup_fmap.
    rewrite fmap_length in Hvilen.
    destruct (hs_imps !! k) eqn:Hhsimpsk => /=.
    - destruct (v_imps !! k) eqn:Hvimpsk.
      + by eapply Himphost in Hhsimpsk => //.
      + apply lookup_lt_Some in Hhsimpsk.
        apply lookup_ge_None in Hvimpsk.
        rewrite Hvilen in Hhsimpsk.
        by lias.
    - destruct (v_imps !! k) eqn:Hvimpsk => //.
      + apply lookup_lt_Some in Hvimpsk.
        apply lookup_ge_None in Hhsimpsk.
        rewrite Hvilen in Hhsimpsk.
        by lias.
  }

  assert (
    length (ext_func_addrs (modexp_desc <$> v_imps)) = length (ext_t_funcs t_imps) /\
    length (ext_tab_addrs (modexp_desc <$> v_imps)) = length (ext_t_tabs t_imps) /\
    length (ext_mem_addrs (modexp_desc <$> v_imps)) = length (ext_t_mems t_imps) /\
    length (ext_glob_addrs (modexp_desc <$> v_imps)) = length (ext_t_globs t_imps)) as Hvtcomplen.
    {
      clear - Himpwasm Hvtlen.
      move: Hvtlen Himpwasm.
      move: t_imps.
      induction v_imps => /=; move => t_imps Hvtlen Himpwasm; destruct t_imps => //.
      simpl in *.
      specialize (IHv_imps t_imps).
      forward IHv_imps IHv_imps; first by lias.
      forward IHv_imps IHv_imps.
      { intros.
        specialize (Himpwasm (S k) v t).
        simpl in *.
        by specialize (Himpwasm H H0).
      }
      destruct IHv_imps as [Hflen [Htlen [Hmlen Hglen]]].
      specialize (Himpwasm 0 a e).
      do 2 forward Himpwasm Himpwasm => //.
      
      destruct a, modexp_desc; simpl in Himpwasm => /=.
      - destruct f.
        destruct Himpwasm as [? [? [? ->]]] => /=.
        repeat split => //.
        by f_equal.
      - destruct t.
        destruct Himpwasm as [? [? [? [? [-> ?]]]]] => /=.
        repeat split => //.
        by f_equal.
      - destruct m.
        destruct Himpwasm as [? [? [? [? [-> ?]]]]] => /=.
        repeat split => //.
        by f_equal.
      - destruct g.
        destruct Himpwasm as [? [? [? [? [-> ?]]]]] => /=.
        repeat split => //.
        by f_equal.
    }

  destruct Hvtcomplen as [Hvtflen [Hvttlen [Hvtmlen Hvtglen]]].
  destruct ostart as [idfstart | ]; last first.
  {
    destruct m; simpl in *.
    unfold module_typing in Hmodtype.
    destruct Hmodtype as [fts [gts [Hmodfunc [_ [_ [_ [_ [_ [Hstart _]]]]]]]]].
    unfold module_start_typing in Hstart.
    rewrite Hmodstart in Hstart.
    simpl in Hstart.
    move/andP in Hstart.
    destruct Hstart as [Hextlen Hnth].
    exfalso.
    rewrite nth_error_lookup in Heqostart.
    symmetry in Heqostart.
    apply lookup_ge_None in Heqostart.
    move/ssrnat.ltP in Hextlen.
    rewrite Heqinst_res in Heqostart.
    simpl in Heqostart.
    rewrite app_length gen_index_length in Heqostart.
    rewrite app_length in Hextlen.
    rewrite Hvtflen in Heqostart.
    replace (length fts) with (length mod_funcs) in Hextlen; last by apply Forall2_length in Hmodfunc.
    by lias.
  }    

  destruct Hinsertexp as [vis' Hinsertexp].
  
  iApply fupd_mask_intro; first by solve_ndisj.
  
  iIntros "Hmask".
  iSplit.
  
  - destruct s => //.
    iPureIntro.
    unfold language.reducible, language.prim_step.
    exists [::], (idecls, map_start (Some idfstart)), (ws_res, vis', ms, has, f), [::].
    repeat split => //.
    by eapply HR_host_step.
  - iIntros ([hes' wes'] [[[[ws3 vis3] ms3] has3] f3] efs HStep).
    destruct HStep as [HStep [-> ->]].
    revert Heqinst_res.
    inversion HStep; subst; clear HStep; move => Heqinst_res.
    

    5: {
      by apply empty_no_reduce in H.
    }

    (* The two branches about host actions *)
    4: by apply llfill_is_nil in H1 as [??] => //.
    
    3:  by apply llfill_is_nil in H2 as [??] => //. 
    
    2: {
      (* oob case is impossible, because we've proven the bound check conditions. *)

      iDestruct (import_resources_wts_subset with "Hwt Htsize Htlimit [Himpwasm]") as "%Hwt".
      { by iDestruct "Himpwasm" as "(?&?&?&?)". } 
      specialize (Hwt Hvtlen).
      
      iDestruct (import_resources_wms_subset with "Hwm Hmsize Hmlimit [Himpwasm]") as "%Hwm".
      { by iDestruct "Himpwasm" as "(?&?&?&?)". } 
      specialize (Hwm Hvtlen).
      
      exfalso.
      apply H20. clear H20.
      rewrite Hmod in H3. 
      inversion H3; symmetry in H0; subst; clear H3. 
    
      rewrite Hvilookup in H7.
      inversion H7; subst; clear H7.

      split.
      - by eapply module_elem_bound_check_gmap_extend.
      - by eapply module_data_bound_check_gmap_extend.
    }

    (* On to the main branch, the only possible reduction (successful case) *)

    rewrite Hmod in H3.
    
    revert Heqinst_res.
    inversion H3; symmetry in H0; subst; clear H3.
    
    rewrite Hvilookup in H4.
    inversion H4; subst; clear H4.

    move => Heqinst_res.
    
    iIntros "!>!>!>".

    specialize (instantiate_det _ _ _ _ _ Hinst H9) as Hinsteq.

    destruct ws3.
    simpl in *.
    inversion Hinsteq.
    simpl.

    (* Wasm state update, using the instantiation characterisation lemma *)
    iDestruct (instantiation_wasm_spec with "") as "H" => //.
    iDestruct ("H" with "[Himpwasm] [Hwf Hwt Hwm Hwg Hmsize Htsize Hmlimit Htlimit]") as "Hq".
    { unfold instantiation_resources_pre_wasm.
      by iFrame.
    }
    { unfold gen_heap_wasm_store.
      by iFrame.
    }

    iClear "H".

    iMod "Hq" as "(Hwasmpost & Hσ)".
    unfold gen_heap_wasm_store => /=.
    iDestruct "Hσ" as "(?&?&?&?&?&?&?&?)".
    iFrame.

    rewrite <- H3.
    rewrite <- H2 in H22.

    rewrite -> H1 in *.

    (* host state update *)
    rewrite Hinsertexp in H22.
    revert Heqinst_res.
    inversion H22; subst; clear H22.
    move => Heqinst_res.
    
    rewrite fmap_length in H20.
    iDestruct (host_export_state_update $! H20 Hinsertexp with "[$] [$]") as "H".
    
    iMod "H" as "(Hvis & Hexphost)".
    
    iFrame.

    iMod "Hmask".


    iModIntro.
    iSplit => //.

    (* Apply the wp spec premise for start function *)
    iSpecialize ("Hwpstart" $! idfstart).
    iApply ("Hwpstart" with "[$Hframeown]") => //.

    unfold instantiation_resources_post.
    iFrame.
    iExists inst.
    by iFrame.
Qed.
    
Lemma instantiation_spec_operational_start s E (hs_mod: N) (hs_imps: list vimp) (v_imps: list module_export) (hs_exps: list vi) (m: module) t_imps t_exps wfs wts wms wgs nstart (Φ: host_val -> iProp Σ):
  m.(mod_start) = Some (Build_module_start (Mk_funcidx nstart)) ->
  module_typing m t_imps t_exps ->
  module_restrictions m ->
  ↪[frame] empty_frame -∗                            
  instantiation_resources_pre hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps -∗
  (∀ idnstart, (↪[frame] empty_frame) -∗ (instantiation_resources_post hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps (Some idnstart)) -∗ WP (([::], [::AI_invoke idnstart]) : host_expr) @ s; E {{ Φ }}) -∗
  WP (([:: ID_instantiate hs_exps hs_mod hs_imps], [::]): host_expr) @ s; E {{ Φ }}.
Proof.
  iIntros.
  by iApply (instantiation_spec_operational_start_seq with "[$] [$] [$]").
Qed.
  
End Instantiation_spec_operational.

End Iris_host.
