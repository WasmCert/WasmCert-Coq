From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
(* From iris.bi Require Export weakestpre. *)
Require Export iris iris_locations iris_properties iris_atomicity iris_wp stdpp_aux.
Require Export datatypes host operations properties opsem.

Import uPred.

Set Default Proof Using "Type". (* what is this? *)

Close Scope byte_scope.

Let expr := iris.expr.
Let val := iris.val.
Let to_val := iris.to_val.

(* Defining a Wasm-specific WP with frame existence *)

Import DummyHosts.
  (*
Let reduce := @reduce host_function host_instance.
*)

Canonical Structure wasm_lang := Language wasm_mixin.
 
Let reducible := @reducible wasm_lang.
Let state := state wasm_lang.

Implicit Type σ : state.

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

Definition frameGName : positive := 10%positive.

Definition proph_id := positive. (* ??? *)


Instance eqdecision_frame: EqDecision frame.
Proof. decidable_equality. Qed.

(* TODO: Global Instance doesn't seem to actually make this global... *)
Global Instance heapG_irisG `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, wmemsizeG Σ, !wglobG Σ, !wframeG Σ} : irisGS wasm_lang Σ := {
  iris_invGS := func_invG; (* ??? *)
  state_interp σ _ κs _ :=
    let: (_, s, locs, inst) := σ in
     ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
      (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
      (gen_heap_interp (gmap_of_list s.(s_globals))) ∗
      (ghost_map_auth frameGName 1 (<[ tt := Build_frame locs inst ]> ∅)) ∗ 
      (gen_heap_interp (gmap_of_list (fmap mem_length s.(s_mems))))
      
    )%I;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
  }.

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

(* Resource ownerships *)
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



Section Wasm_wp.
  Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

  Global Instance wp_wasm : Wp (iProp Σ) (expr) (val) stuckness.
  Proof using Σ wfuncG0 wtabG0 wmemG0 wmemsizeG0 wglobG0 wframeG0.
    eapply wp'. Unshelve. exact frame. exact (λ f,  ↪[frame] f)%I. Defined.

End Wasm_wp.

(* A Definition of a context dependent WP for WASM expressions *)

Definition wp_wasm_ctx `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}
          (s : stuckness) (E : coPset) (e : language.expr wasm_lang)
           (Φ : val -> iProp Σ) (i : nat) (lh : lholed) : iProp Σ := 
  ∀ LI, ⌜lfilled i lh e LI⌝ -∗ WP LI @ s; E {{ Φ }}.


Definition wp_wasm_frame `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}
          (s : stuckness) (E : coPset) (es : language.expr wasm_lang)
          (Φ : val -> iProp Σ) (n: nat) (f: frame) : iProp Σ :=
  
  WP [AI_local n f es] @ s; E {{ Φ }}.

Definition wp_wasm_ctx_frame `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}
          (s : stuckness) (E : coPset) (es : language.expr wasm_lang)
          (Φ : val -> iProp Σ) (n: nat) (f: frame) (i : nat) (lh : lholed) : iProp Σ :=
  
  ∀ LI, ⌜lfilled i lh es LI⌝ -∗ WP [AI_local n f LI] @ s; E {{ Φ }}.


(* Notations *)

(* Context wps for blocks *)
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

(* Frame wps for Local *)

Notation "'WP' e @ s ; E 'FRAME' n ; f {{ Φ } }" := (wp_wasm_frame s E e%E Φ n f)
  (at level 20, only parsing) : bi_scope.

Notation "'WP' e @ s ; E 'FRAME' n ; f {{ v , Q } }" := (wp_wasm_frame s E e%E (λ v, Q) n f)
  (at level 20, e, Q, n, f at level 200,
    format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Notation "'WP' e @ s ; E 'FRAME' n ; f 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx_frame s E e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ s ; E 'FRAME' n ; f 'CTX_EMPTY' {{ v , Q } }" := (wp_wasm_ctx_frame s E e%E (λ v, Q) n f 0 (LH_base [] []))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'FRAME' n ; f 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx_frame NotStuck E e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @ '[' E  '/' ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'FRAME' n ; f 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx_frame MaybeStuck E e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' E  '/' ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'FRAME' n ; f 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx_frame NotStuck ⊤ e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'FRAME' n ; f 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx_frame MaybeStuck ⊤ e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e '/' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* Tactics *)
Ltac only_one_reduction H :=
  let Hstart := fresh "Hstart" in
  let a := fresh "a" in
  let Hstart1 := fresh "Hstart" in
  let Hstart2 := fresh "Hstart" in
  let Hσ := fresh "Hσ" in 
  eapply reduce_det in H
      as [H | [ [i0 Hstart] | [ [a [cl [tf [h [i0 [Hstart [Hnth Hcl]]]]]]] | (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ)]]] ;
  last (by repeat econstructor) ;
  first (try inversion H ; subst ; clear H => /=; match goal with [f: frame |- _] => iExists f; iFrame; by iIntros | _ => idtac end) ;
  try by repeat (unfold first_instr in Hstart ; simpl in Hstart) ; inversion Hstart.

Lemma find_first_const es n f :
  const_list es ->
  first_instr [AI_local n f es] = Some (AI_local n f es,0)
  (* ∨ first_instr [AI_local n f es] = None *).
Proof.
  intros Hconst.
  destruct es.
  all: rewrite /first_instr /= //.
  assert (first_instr_instr a = None) as ->.
  { apply andb_true_iff in Hconst as [Hconst _].
    destruct a;try done. destruct b;try done. }
  assert (find_first_some (map first_instr_instr es) = None) as ->.
  { simpl in Hconst.
    apply andb_true_iff in Hconst as [_ Hconst]. clear -Hconst.
    induction es;[done|].
    simpl. apply andb_true_iff in Hconst as [Ha Hconst].
    destruct a;try done. destruct b;try done. simpl.
    apply IHes. auto. }
  auto. 
Qed.

Lemma to_val_immV_inj es es' vs :
  iris.to_val es = Some (immV vs) ->
  iris.to_val es' = Some (immV vs) ->
  es = es'.
Proof.
  revert es' vs.
  induction es;intros es' vs Hsome Heq.
  { simpl in *. simplify_eq.
    apply to_val_nil in Heq. auto. }
  { destruct vs.
    apply to_val_nil in Hsome. done.
    destruct es'.
    symmetry in Heq. simpl in *. simplify_eq.
    simpl in *.
    destruct a,a0 =>//.
    destruct b,b0 =>//.
    destruct (iris.to_val es) eqn:Hv,(iris.to_val es') eqn:Hv'=>//.
    destruct v2,v3 =>//.
    simplify_eq. f_equiv.
    apply IHes with vs;auto.
    destruct es' =>//.
    1,2: destruct es =>//. }
Qed.


Lemma last_inj {A : Type} (l1 l2 : list A) (a b : A) :
    l1 = l2 -> last l1 = Some a -> last l2 = Some b -> a = b.
Proof.
  intros Heq Hla1 Hla2.
  subst. rewrite Hla1 in Hla2. inversion Hla2. done.
Qed.
Lemma const_list_snoc_eq vs :
  forall ves es es' e,
    const_list ves ->
    const_list vs ->
    es ≠ [] ->
    to_val es = None ->
    (vs ++ es ++ es')%SEQ = ves ++ [e] ->
    es' = [] ∧ ∃ vs2, ves = vs ++ vs2 ∧ es = vs2 ++ [e] ∧ const_list vs2.
Proof.
  induction vs;
    intros ves es es' e Hconst1 Hconst2 Hneq Hnval Heq.
  { erewrite app_nil_l in Heq.
    apply app_eq_inv in Heq as [[k [Hk1 Hk2]] | [k [Hk1 Hk2]]].
    { destruct k.
      { rewrite app_nil_r in Hk1.
        rewrite app_nil_l in Hk2.
        simplify_eq.
        assert (is_Some (to_val (ves))) as [c Hc];[|congruence].
        unfold to_val in Hnval. unfold to_val.
        apply const_list_is_val in Hconst1 as [v ->]. eauto. }
      { destruct k,es' =>//.
        rewrite app_nil_r in Hk2. simplify_eq.
        eauto. }  }
    { rewrite Hk1 in Hconst1.
      apply to_val_cat_None1 with (es2:=k) in Hnval.
      apply const_list_is_val in Hconst1 as [v Hv].
      congruence. } }
  { destruct ves.
    { destruct vs,es,es' =>//. }
    inversion Heq;subst.
    simpl in Hconst1,Hconst2.
    apply andb_true_iff in Hconst1,Hconst2.
    destruct Hconst1 as [Ha0 Hconst1].
    destruct Hconst2 as [_ Hconst2].
    apply IHvs in H1;auto.
    destruct H1 as [Heqes' [vs2 [Heq1 Heq2]]].
    subst. eauto.
  }
Qed.
Lemma length_to_val_immV v1 :
  forall vs1, to_val v1 = Some (immV vs1)
         -> length v1 = length vs1.
Proof.
  induction v1;intros vs1 Hval.
  destruct vs1 =>//.
  destruct vs1.
  apply to_val_nil in Hval. done.
  simpl in *.
  destruct a;try done.
  destruct b;try done.
  destruct (to_val v1) eqn:Hv1;try done.
  destruct v2;try done.
  simplify_eq. auto.
  destruct v1;try done.
Qed.
Lemma const_list_app v1 v2 :
  const_list (v1 ++ v2) <-> const_list v1 ∧ const_list v2.
Proof.
  split.
  - intros Hconst.
    apply const_list_is_val in Hconst as [v Hv].
    apply to_val_cat in Hv as [Hv1%to_val_const_list Hv2%to_val_const_list];auto.
  - intros [Hconst1 Hconst2].
    apply const_list_is_val in Hconst1 as [v1' Hv1].
    apply const_list_is_val in Hconst2 as [v2' Hv2].
    eapply to_val_const_list.
    apply to_val_cat_inv;eauto.
Qed.



Section iris_properties.
  Import DummyHosts.

(*
Variable host_function : eqType.

Let host := host.host host_function.
Let function_closure := function_closure host_function.
Let store_record := store_record host_function.

Variable host_instance : host.
*)
  Let reduce := @reduce host_function host_instance.

  Ltac false_assumption := exfalso ; apply ssrbool.not_false_is_true ; assumption.

  (* given a nonempty list x :: xs, gives user a hypothesis "Htail : x :: xs = ys ++ [y]" *)
  Ltac get_tail x xs ys y Htail :=
    cut (exists ys y, x :: xs = ys ++ [y]) ;
    [ intro Htail ; destruct Htail as (ys & y & Htail) |
      exists (removelast (x :: xs)) ;
      exists (List.last (x :: xs) AI_trap) ;
      apply app_removelast_last ;
      apply not_eq_sym ; apply nil_cons ].
  
  Lemma found_intruse l1 l2 (x : administrative_instruction) :
    l1 = l2 -> (In x l1 -> False) -> In x l2 -> False.
  Proof.
    intros. rewrite H in H0. apply H0 ; exact H1.
  Qed.
  
  Ltac found_intruse x H Hxl1 :=
    exfalso ; 
    apply (found_intruse _ _ x H) ;
    [intro Hxl1 ; repeat ((destruct Hxl1 as [Hxl1 | Hxl1] ; [ inversion Hxl1 |]) +
                          assumption  ) |
      try by (apply in_or_app ; right ; left ; trivial) ].

  
  Inductive first_instr_Ind : list administrative_instruction -> administrative_instruction -> nat -> Prop :=
  | first_instr_const vs es a i : const_list vs -> first_instr_Ind es a i -> first_instr_Ind (vs ++ es) a i
  | first_instr_trap es : first_instr_Ind (AI_trap :: es) AI_trap 0
  | first_instr_invoke es a : first_instr_Ind (AI_invoke a :: es) (AI_invoke a) 0
  | first_instr_local n f es es' a i : first_instr_Ind es a i -> first_instr_Ind (AI_local n f es :: es') a (S i)
  | first_instr_label n es1 es es' a i : first_instr_Ind es a i -> first_instr_Ind (AI_label n es1 es :: es') a (S i)
  | first_instr_local_base n f es es' : const_list es -> first_instr_Ind (AI_local n f es :: es') (AI_local n f es) 0
  | first_instr_label_base n es1 es es' : const_list es -> first_instr_Ind (AI_label n es1 es :: es') (AI_label n es1 es) 0
  | first_instr_basic bi es': (∀ b, bi ≠ BI_const b) -> first_instr_Ind (AI_basic bi :: es' ) (AI_basic bi) 0.

  Lemma first_instr_Ind_not_empty es a i :
    first_instr_Ind es a i -> es ≠ [].
  Proof.
    intros Hf. induction Hf;auto.
    intros Hcontr. destruct vs,es =>//.
  Qed.
  Lemma first_instr_app e :
    ∀ a es', first_instr e = Some a -> first_instr (e ++ es') = Some a.
  Proof.
    induction e; intros a0 es';try done.
    cbn. destruct (first_instr_instr a) eqn:Ha;auto.
    intros Hf. eapply IHe with (es':=es') in Hf. auto.
  Qed.
  Lemma first_instr_app_skip e :
    ∀ es', first_instr e = None -> first_instr (e ++ es') = first_instr es'.
  Proof.
    induction e; intros a0;try done.
    cbn. destruct (first_instr_instr a) eqn:Ha;auto. done.
    intros Hf. eapply IHe in Hf. eauto.
  Qed.

  Lemma first_instr_None_const es :
    first_instr es = None -> const_list es.
  Proof.
    induction es;auto.
    cbn.
    destruct (first_instr_instr a) eqn:Ha;[done|].
    intros H. apply IHes in H.
    unfold first_instr_instr in Ha.
    destruct a =>//.
    destruct b =>//.
    destruct (first_instr l0) eqn:Hl0.
    { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha. destruct p;done. }
    { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha. done. }
    destruct (first_instr l) eqn:Hl0.
    { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha. destruct p;done. }
    { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha. done. }
  Qed.

  Lemma find_first_const_label es es1 n :
  const_list es ->
  first_instr [AI_label n es1 es] = Some (AI_label n es1 es,0)
  (* ∨ first_instr [AI_local n f es] = None *).
Proof.
  intros Hconst.
  destruct es.
  all: rewrite /first_instr /= //.
  assert (first_instr_instr a = None) as ->.
  { apply andb_true_iff in Hconst as [Hconst _].
    destruct a;try done. destruct b;try done. }
  assert (find_first_some (map first_instr_instr es) = None) as ->.
  { simpl in Hconst.
    apply andb_true_iff in Hconst as [_ Hconst]. clear -Hconst.
    induction es;[done|].
    simpl. apply andb_true_iff in Hconst as [Ha Hconst].
    destruct a;try done. destruct b;try done. simpl.
    apply IHes. auto. }
  auto. 
Qed.

  Lemma first_instr_Ind_Equivalent es a i :
    first_instr es = Some (a,i) <-> first_instr_Ind es a i.
  Proof.
    revert es a.
    induction i;intros es a.
    { split.
      { intros Hf.
        destruct es;try done.
        destruct a0;try done.
        { all: cbn in Hf. rewrite separate1. destruct b; try done; simplify_eq; try by constructor.
          constructor;auto.
          induction es;try done.
          simpl in Hf.
          destruct (first_instr_instr a0) eqn:Ha0; simplify_eq.
          { unfold first_instr_instr in Ha0.
            destruct a0; try done; simplify_eq; try by constructor.
            destruct b; try done; simplify_eq; try by constructor.
            destruct (first_instr l0) eqn:Hl0.
            { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0.
              destruct p;done. }
            { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0. simplify_eq.
              constructor. apply first_instr_None_const. auto. }
            destruct (first_instr l) eqn:Hl0.
            { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0.
              destruct p;done. }
            { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0. simplify_eq.
              constructor. apply first_instr_None_const. auto. }
          }
          
          unfold first_instr_instr in Ha0. destruct a0 =>//.
          destruct b  =>//.
          rewrite separate1. apply first_instr_const;auto.
          destruct (first_instr l0) eqn:Hl0.
          { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0. destruct p;done. }
          { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0. done. }
          destruct (first_instr l) eqn:Hl0.
          { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0. destruct p;done. }
          { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0. done. }
        }
        { cbn in Hf. simplify_eq. constructor. }
        { cbn in Hf. simplify_eq. constructor. }
        { cbn in Hf.
          destruct (find_first_some (map first_instr_instr l0)) eqn:Hl0.
          destruct p;try done. 
          simplify_eq. constructor. apply first_instr_None_const. auto. }
        { cbn in Hf.
          destruct (find_first_some (map first_instr_instr l)) eqn:Hl0.
          destruct p;try done. 
          simplify_eq. constructor. apply first_instr_None_const. auto. }
      }
      { intros Hi. induction Hi;subst;auto.
        { rewrite Wasm.iris_properties.first_instr_const;auto. }
        { cbn. unfold first_instr in IHHi. by rewrite IHHi. }
        { cbn. unfold first_instr in IHHi. by rewrite IHHi. }
        { eapply find_first_const in H.
          rewrite separate1. erewrite first_instr_app;eauto. }
        { eapply find_first_const_label in H.
          rewrite separate1. erewrite first_instr_app;eauto. }
        { cbn. destruct bi;try done. specialize (H v). done. }
      }
    }
    { split.
      { intros Hf.
        induction es;try done.
        destruct a0;try done.
        { destruct b; try done. cbn in Hf. apply IHes in Hf.
          rewrite separate1. constructor;auto. }
        { constructor. apply IHi.
          cbn in Hf.
          destruct (find_first_some (map first_instr_instr l0)) eqn:Hl0;try done.
          destruct p;try done. simplify_eq. auto. }
        { constructor. apply IHi.
          cbn in Hf.
          destruct (find_first_some (map first_instr_instr l)) eqn:Hl0;try done.
          destruct p;try done. simplify_eq. auto. }
      }
      { intros Hf.
        induction Hf;subst;try (by cbn).
        { rewrite Wasm.iris_properties.first_instr_const;auto. }
        { cbn. unfold first_instr in IHHf. by rewrite IHHf. }
        { cbn. unfold first_instr in IHHf. by rewrite IHHf. }
        { eapply find_first_const in H.
          rewrite separate1. erewrite first_instr_app;eauto. }
        { eapply find_first_const_label in H.
          rewrite separate1. erewrite first_instr_app;eauto. }
        { cbn. destruct bi;try done. specialize (H v). done. }
      }
    }
  Qed.

  Lemma destruct_list_rev {A : Type} (l : list A) :
    l = [] ∨ ∃ a l', l = l' ++ [a].
  Proof.
    induction l;eauto.
    right. destruct l;eauto.
    exists a,[]. auto.
    destruct IHl as [Hcontr | [a' [l' Heq]]].
    done. rewrite Heq.
    eexists. eexists.
    rewrite separate1 app_assoc. eauto.
  Qed.

  Lemma to_val_None_first_singleton es :
    ((∃ v, to_val es = Some (immV v)) -> False) ->
    (to_val es = Some trapV -> False) ->
    ∃ vs e es', es = vs ++ [e] ++ es' ∧ const_list vs ∧ ((to_val ([e]) = None)
                                                         ∨ (e = AI_trap ∧ (vs ≠ [] ∨ es' ≠ []))
                                                         ∨ (∃ n, e = (AI_basic (BI_br n)))
                                                         ∨ (e = (AI_basic BI_return))).
  Proof.
    induction es;intros Hes1 Hes2.
    { exfalso. apply Hes1. eauto. }
    { destruct (to_val [a]) eqn:Ha.
      { destruct v.
        { destruct (to_val es) eqn:Hes.
          { unfold to_val in Hes.
            unfold to_val in Ha.
            destruct v. 
            { eapply to_val_cat_inv in Hes;[|apply Ha].
              rewrite -separate1 in Hes. unfold to_val in Hes1.
              exfalso. apply Hes1. eauto. }
            { apply to_val_trap_is_singleton in Hes as ->.
              apply to_val_const_list in Ha.
              exists [a],AI_trap,[]. cbn. repeat split;auto. }
            { apply to_val_br in Hes as ->.
              rewrite to_e_list_fmap.
              rewrite list_extra.cons_app app_assoc.
              apply to_val_const_list in Ha as [? ->]%const_es_exists.
              erewrite v_to_e_cat. eexists _,_,_. split;eauto.
              split;[apply v_to_e_is_const_list|]. right. right. left. eauto. }
            { apply to_val_ret in Hes as ->.
              rewrite to_e_list_fmap.
              rewrite list_extra.cons_app app_assoc.
              apply to_val_const_list in Ha as [? ->]%const_es_exists.
              erewrite v_to_e_cat.
              eexists _,_,_. split;eauto.
              split;[apply v_to_e_is_const_list|]. right. right. right. eauto. }
          }
          { destruct IHes as [vs [e [es' [Heq [Hconst HH]]]]];auto.  by intros [? ?]. done.
            apply to_val_const_list in Ha.
            destruct HH as [Hnone | [[-> Hne] | [[? Hne] | Hne]]].
            { exists (a::vs),e,es'. subst. split;auto. split;[|left;auto].
              rewrite separate1. apply const_list_app. auto. }
            { exists (a::vs),AI_trap,es'. subst. split;auto.
              split;[|right;auto]. rewrite separate1. apply const_list_app. auto. }
            { subst. rewrite separate1 app_assoc.
              eexists _,_,_. split;eauto. split;[apply const_list_app;auto|].
              right;right;left. eauto. }
            { subst. rewrite separate1 app_assoc.
              eexists _,_,_. split;eauto. split;[apply const_list_app;auto|].
              right;right;right. eauto. }
          }
        }
        { unfold to_val in Ha.
          apply to_val_trap_is_singleton in Ha as Heq.
          simplify_eq.
          unfold to_val in Hes1.
          unfold to_val in Hes2.
          destruct es =>//.
          exists [],AI_trap,(a :: es).
          repeat split;auto. }
        { destruct a;try done. destruct b;try done.
          apply to_val_br in Ha. destruct l =>//.
          destruct e =>//. rewrite app_nil_l app_nil_r in Ha.
          simplify_eq. eexists [],_,es. split;eauto.
          repeat split;eauto. }
        { destruct a;try done. destruct b;try done.
          apply to_val_ret in Ha. destruct l =>//.
          destruct e =>//. rewrite app_nil_l app_nil_r in Ha.
          simplify_eq. eexists [],_,es. split;eauto.
        }
      }
      { exists [],a,es. auto. }
    }
  Qed.
    
  Lemma const_list_snoc_eq3 es'' :
  forall vs es ves e es',
    const_list ves ->
    const_list vs ->
    es ≠ [] ->
    ((∃ v, to_val es = Some (immV v)) -> False) ->
    (to_val es = Some trapV -> False) ->
    to_val [e] = None ∨ e = AI_trap ->
    (vs ++ es ++ es')%SEQ = ves ++ [e] ++ es'' ->
    ∃ vs2 es2, ves = vs ++ vs2 ∧ es = vs2 ++ [e] ++ es2 ∧ es'' = es2 ++ es' ∧ const_list vs2.
  Proof.
    intros vs es ves e es' Hconst1 Hconst2 Hneq Hnval1 Hnval2 He Heq.
    apply to_val_None_first_singleton in Hnval2 as HH;auto.
    destruct HH as [vs' [e' [es2 [Heq' [Hconst HH]]]]].
    assert (Heqcopy:=Heq).
    rewrite Heq' in Heqcopy.
    assert (vs ++ (vs' ++ [e'] ++ es2)%list ++ es' = (vs ++ vs') ++ [e'] ++ (es2 ++ es'))%SEQ as Heq2.
    { rewrite !app_assoc. repeat erewrite app_assoc. auto. }
    rewrite Heq2 in Heqcopy. clear Heq2. unfold to_val in He. unfold to_val in HH.
    apply first_values in Heqcopy as [Heq1 [Heq2 Heq3]];auto.
    2: (destruct HH as [-> | [[-> _] | [[? ->] | ->]]]; by intros [? ?]).
    2: by (destruct He as [-> | ->]; intros [? ?]).
    2: destruct HH as [?|[? |[?|?]]];auto.
    all: try apply const_list_app;auto.
    subst e'.
    rewrite -Heq1 in Heq.
    rewrite -Heq3 in Heq.
    assert ((vs ++ vs')%SEQ ++ [e] ++ (es2 ++ es')%SEQ =
              (vs ++ (vs' ++ [e] ++ es2) ++ es')%SEQ) as Hassoc.
    { rewrite !app_assoc. repeat erewrite app_assoc. auto. }
    rewrite Hassoc in Heq;clear Hassoc.
    apply app_inv_head in Heq.
    apply app_inv_tail in Heq.
    eexists _,_. eauto.
  Qed.     

  Lemma lfilled_one_depth_trap k lh es vs n es' es'' :
    const_list vs ->
    lfilled k lh es (vs ++ [AI_label n es' [AI_trap]] ++ es'') ->
    k = 0 ∨ k = 1.
  Proof.
    revert lh es vs n es' es''.
    induction k;intros lh es vs n es' es'';auto.
    destruct k;auto.
    intros Hconst Hfill%lfilled_Ind_Equivalent.
    exfalso.
    inversion Hfill;subst.
    apply first_values in H0 as [? [? ?]];auto.
    simplify_eq.
    inversion H4;subst.
    do 2 destruct vs0 =>//. all: by intros [? ?].
  Qed.    

  Lemma reduce_return_trap_label es hs' s' f' vs n es'0 es'' es' :
    reduce hs' s' f' es hs' s' f' es' ->
    const_list vs ->
    es = (vs ++ [AI_label n es'0 [AI_trap]] ++ es'') ->
    ∃ lh', lfilled 0 lh' [AI_trap] es'.
  Proof.
    intros Hred.
    revert vs es''. induction Hred;[|intros vs es'' Hconst Heq..].
    { induction H; intros vs' es'' Hconst Heq;subst.
      all: try (do 2 destruct vs' =>//).
      all: try (do 3 destruct vs' =>//).
      all: try (apply const_list_concat_inv in Heq as [? [? ?]];auto; done).
      destruct vs',es'' =>//.
      rewrite app_nil_r app_nil_l in Heq. simplify_eq.
      exists (LH_base [] []). by cbn.
      1,2: destruct vs' =>//.
      destruct vs',es'' =>//.
      exists (LH_base [] []). by cbn.
      1,2: destruct vs' =>//.
      destruct vs'=>//;[|destruct vs'=>//].
      destruct es''=>//.
      { apply lfilled_Ind_Equivalent in H1. inversion H1;subst.
        inversion Heq;subst.
        do 3 (destruct vs0 || destruct vs || destruct es'0 || destruct es') =>//.
        inversion Heq;subst.
        do 2 destruct vs0 =>//. }
      { destruct vs',es'' =>//. destruct es'' =>//.
        rewrite app_nil_l in Heq. inversion Heq;subst. done.
        1,2: do 2 destruct vs' =>//. }
      { apply lfilled_Ind_Equivalent in H0. inversion H0;subst.
        apply const_list_concat_inv in H1 as [? [? ?]];auto; done. }
    }
    all: try (subst; do 2 destruct vs =>//).
    all: try (subst; do 3 destruct vs =>//).
    subst. apply const_list_concat_inv in Heq as [? [? ?]];auto. done. apply v_to_e_is_const_list.
    subst.
    apply lfilled_one_depth_trap in H as Hk;auto.
    destruct Hk as [-> | ->].
    { apply lfilled_Ind_Equivalent in H. inversion H;subst.
      apply const_list_snoc_eq3 in H1;auto.
      2: eapply reduce_not_nil;eauto.
      2,3: unfold to_val; eapply val_head_stuck_reduce in Hred;eauto.
      2,3: by rewrite Hred; try intros [? ?]; try intros ?. 
      destruct H1 as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst2]]]]].
      subst.
      edestruct IHHred as [lh' Hlh'];eauto.
      apply lfilled_Ind_Equivalent in Hlh'.
      inversion Hlh';subst.
      apply lfilled_Ind_Equivalent in H0.
      inversion H0;subst.
      exists (LH_base (vs0 ++ vs) (es'2 ++ es'1)).
      assert (vs0 ++ (vs ++ [AI_trap] ++ es'2) ++ es'1 = (vs0 ++ vs) ++ [AI_trap] ++ (es'2 ++ es'1))%SEQ as Heq.
      { repeat erewrite app_assoc. auto. }
      erewrite Heq. apply lfilled_Ind_Equivalent. constructor.
      apply const_list_app. auto.
    }
    { apply lfilled_Ind_Equivalent in H.
      inversion H;subst.
      apply first_values in H2 as [Heq1 [Heq2 Heq3]];auto.
      simplify_eq. apply lfilled_Ind_Equivalent in H6.
      apply filled_singleton in H6 as [? [? ?]].
      3: eapply reduce_not_nil;eauto.
      2: intros;done.
      subst.
      apply val_head_stuck_reduce in Hred.
      done. all: by intros [? ?].
    }
  Qed.

  Lemma reduce_focus_one es1 hs s f hs' s' f' vs n es'0 LI es'' es' :
    reduce hs s f es1 hs' s' f' es' ->
    es1 = (vs ++ [AI_label n es'0 LI] ++ es'') ->
    const_list vs ->
    iris.to_val LI = None ->
    (∀ i j lh vs0, const_list vs0 -> lfilled i lh (vs0 ++ [AI_basic (BI_br j)]) LI -> False) ->
    ∃ LI', reduce hs s f LI hs' s' f' LI'.
  Proof.
    intros Hred.
    revert vs n es'0 LI es''.
    induction Hred;intros vs n' es'0 LI es'' Heq Hconst HLI Hnbr.
    all: try (subst; do 2 destruct vs =>//).
    all: try (subst; do 3 destruct vs =>//).
    { induction H;subst.
      all: try (do 2 destruct vs =>//).
      all: try (do 3 destruct vs =>//).
      all: try (apply const_list_concat_inv in Heq as [? [? ?]];auto; done).
      { destruct vs,es'' =>//.
        2: destruct vs =>//.
        2: destruct vs,es'' =>//.
        rewrite app_nil_l app_nil_r in Heq.
        simplify_eq.
        exfalso. apply const_list_is_val in H as [? ?].
        congruence. }
      { destruct vs,es'' =>//.
        2: destruct vs =>//.
        2: destruct vs,es'' =>//.
        rewrite app_nil_l app_nil_r in Heq.
        simplify_eq. }
      { destruct vs,es'' =>//.
        2: destruct vs =>//.
        2: destruct vs,es'' =>//.
        rewrite app_nil_l app_nil_r in Heq.
        simplify_eq. 
        apply Hnbr in H1. done. auto.
      }
      { destruct vs =>//.
        { inversion Heq;subst. done. }
        destruct vs =>//.
        { inversion Heq;subst. simpl in Hconst.
          apply andb_true_iff in Hconst as [? ?]. done. }
      }
      { apply lfilled_Ind_Equivalent in H0; inversion H0;subst.
        apply first_values in H1 as [? [? ?]];auto. done. all: by intros [? ?].
      }      
    }
    { subst. symmetry in Heq.
      apply const_list_snoc_eq in Heq as [-> [vs2 [? [? ?]]]];auto;subst.
      do 2 destruct vs2 =>//.
      apply v_to_e_is_const_list.
    }
    { subst.
      apply reduce_not_nil in Hred as Hnil.
      apply val_head_stuck_reduce in Hred as Hnval.
      apply lfilled_Ind_Equivalent in H.
      inversion H;subst.
      { apply const_list_snoc_eq3 in H1 as [? [? [? [? [? ?]]]]];auto;subst.
        eapply IHHred;eauto. all: rewrite /to_val Hnval. by intros [? ?]. by intros ?. }
      { apply first_values in H1 as [? [? ?]];auto. simplify_eq.
        apply lfilled_Ind_Equivalent in H6.
        apply lfilled_swap with (es':=es') in H6 as Hfill'.
        destruct Hfill' as [LI' Hfill'].
        exists LI'. eapply r_label;eauto. all: by intros [? ?].
      }
    }
  Qed.

  Lemma lfilled_trap_not_br i lh LI :
    lfilled i lh [AI_trap] LI ->
    (∀ i j lh vs0, const_list vs0 -> lfilled i lh (vs0 ++ [AI_basic (BI_br j)]) LI -> False).
  Proof.
    revert lh LI.
    induction i; intros lh LI Hfill%lfilled_Ind_Equivalent.
    { inversion Hfill;subst.
      intros i j lh vs' Hconst Hfill'.
      apply lfilled_Ind_Equivalent in Hfill'.
      inversion Hfill'.
      { simplify_eq.
        assert (vs0 ++ (vs' ++ [AI_basic (BI_br j)]) ++ es'0 =
                (vs0 ++ vs') ++ (AI_basic (BI_br j)) :: es'0)%SEQ as Heq.
        { repeat erewrite app_assoc. rewrite (separate1 _ es'0).
          repeat erewrite app_assoc. auto. }
        rewrite Heq in H0;clear Heq.
        apply first_values in H0 as [? [? ?]];auto.
        all: try by intros [? ?].
        2: apply const_list_app;auto. done.
      }
      { subst.
        apply first_values in H0 as [? [? ?]];auto. done.
        all: by intros [? ?].
      }      
    }
    { inversion Hfill;subst.
      intros i' j lh vs' Hconst Hfill'.
      apply lfilled_Ind_Equivalent in Hfill'.
      inversion Hfill'.
      { simplify_eq.
        assert (vs0 ++ (vs' ++ [AI_basic (BI_br j)]) ++ es'0 =
                (vs0 ++ vs') ++ (AI_basic (BI_br j)) :: es'0)%SEQ as Heq.
        { repeat erewrite app_assoc. rewrite (separate1 _ es'0).
          repeat erewrite app_assoc. auto. }
        rewrite Heq in H;clear Heq.
        apply first_values in H as [? [? ?]];auto.
        all: try by intros [? ?].
        2: apply const_list_app;auto. done.
      }
      { simplify_eq.
        eapply first_values in H as [? [? ?]];auto.
        simplify_eq.
        apply lfilled_Ind_Equivalent in H6.
        apply lfilled_Ind_Equivalent in H1.
        eapply IHi in H1;eauto. all: try by intros [? ?]. Unshelve. apply 0. apply 0. apply lh'.
      }
    }
  Qed.

  Lemma lfilled_singleton (a : administrative_instruction) k lh es (les : list administrative_instruction) i lh'  :
    es ≠ [] ->
    ((∃ v, to_val es = Some (immV v)) -> False) ->
    (to_val es = Some trapV -> False) ->
    to_val [a] = None ∨ a = AI_trap ->
    (∀ n e1 e2, a ≠ AI_label n e1 e2) ->
    lfilled k lh es les -> 
    lfilled i lh' [a] les ->
    ∃ j lh, lfilled j lh [a] es ∧ j + k = i.
  Proof.
    revert a k lh es les lh'.
    induction i;intros a k lh es les lh' Hne Hnone1 Hnone2 Ha Hnlabel
                       Hfill1%lfilled_Ind_Equivalent Hfill2%lfilled_Ind_Equivalent.
    { inversion Hfill2;subst.
      inversion Hfill1;subst.
      { apply const_list_snoc_eq3 in H0 as [? [? [? [? [? ?]]]]];auto.
        subst. exists 0, (LH_base x x0). split;[|lia]. apply lfilled_Ind_Equivalent. by constructor. }
      { apply first_values in H0 as [? [? ?]];auto. subst.
        specialize (Hnlabel n es'0 LI). done. 2: unfold to_val in Ha;destruct Ha as [-> | ->]. all: try by intros [? ?]. }
    }
    { inversion Hfill2;subst.
      inversion Hfill1;subst.
      { apply const_list_snoc_eq3 in H as [? [? [? [? [? ?]]]]];auto.
        subst.
        exists (S i),(LH_rec x n es' lh'0 x0).
        split;[|lia].
        apply lfilled_Ind_Equivalent. constructor;auto. }
      { apply first_values in H as [? [? ?]];auto. simplify_eq.
        apply lfilled_Ind_Equivalent in H1.
        apply lfilled_Ind_Equivalent in H6.
        eapply IHi in H1;[|eauto..].
        destruct H1 as [? [? ?]].
        eexists _,_. split;[apply H|lia]. all:try by intros [? ?]. }
    }
  Qed.
  
  Lemma trap_reduce_state_eq i lh es hs s f hs' s' f' es' :
    reduce hs s f es hs' s' f' es' ->
    lfilled i lh [AI_trap] es -> 
    (hs,s,f) = (hs',s',f').
  Proof.
    intros Hred. 
    revert i lh.
    induction Hred;auto.
    { subst. intros i lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill.
      all: subst.
      all: apply first_values in H0 as [? [? ?]];auto.
      all: done. }
    { subst. intros i lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill.
      all: subst.
      all: apply first_values in H0 as [? [? ?]];auto.
      all: done. }
    { subst. intros i' lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill.
      all: do 3 destruct vs =>//. }
    { subst. intros i' lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill.
      all: do 3 destruct vs =>//. }
    { subst. intros i' lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill.
      all: do 4 destruct vs =>//. }
    { subst. intros i' lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill.
      all: do 4 destruct vs =>//. }
    { subst. intros i' lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill.
      all: do 3 destruct vs =>//. }
    { intros i lh' Hlh'.
      eapply lfilled_singleton in Hlh' as [? [? ?]];[..|apply H];auto.
      eapply IHHred. apply H1.
      eapply reduce_not_nil;eauto.
      1,2: unfold to_val; eapply val_head_stuck_reduce in Hred as ->. by intros [? ?]. by intros ?. }
    { intros i lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill;subst.
      all: do 2 destruct vs =>//. }
  Qed.

  Lemma trap_reduce_lfilled i lh es hs s f hs' s' f' es' :
    reduce hs s f es hs' s' f' es' ->
    lfilled i lh [AI_trap] es -> 
    exists lh' j, lfilled j lh' [AI_trap] es' ∧ j <= i.
  Proof.
    intros Hred.
    revert i lh.
    induction Hred;[|intros i' lh' Hfill%lfilled_Ind_Equivalent..].
    2-25: inversion Hfill;
    try done;
    try by destruct vs =>//;
    try by do 2 destruct vs =>//;
    try by do 3 destruct vs =>//;
    try by do 4 destruct vs =>//.
    { induction H;intros i' lh' Hfill%lfilled_Ind_Equivalent.
      all: inversion Hfill;
        try by destruct vs =>//;
        try by do 2 destruct vs =>//;
        try by do 3 destruct vs =>//.
      all: try apply first_values in H3 as [? [? ?]];auto;try done.
      all: try by do 2 destruct vs0 =>//.
      all: try by intros [? ?].
      { simplify_eq.
        destruct vs0,es'' =>//.
        erewrite app_nil_l in H0. simplify_eq.
        inversion H5;subst.
        apply const_list_app in H as [_ [H _]%const_list_app];done.
        2,3: destruct vs0 =>//.
        exists (LH_rec vs0 n0 es' lh' es''),(S k0). split;[|lia].
        apply lfilled_Ind_Equivalent;constructor;auto. }
      { simplify_eq.
        destruct vs,es'' =>//.
        erewrite app_nil_l in H. simplify_eq.
        inversion H4;subst.
        destruct vs,es' =>//.
        all: try by destruct vs =>//.
        exists (LH_base [] []),0. split;[|lia]. by cbn.
        do 2 destruct vs =>//. }
      { exfalso. simplify_eq.
        destruct vs0,es'' =>//.
        2,3: try by destruct vs0 =>//.
        erewrite app_nil_l in H2. simplify_eq.
        apply lfilled_Ind_Equivalent in H7.
        eapply lfilled_singleton in H7 ;[..|apply H1];auto.
        2: destruct vs =>//.
        destruct H7 as [? [? [Hcontr ?]]].
        apply lfilled_Ind_Equivalent in Hcontr.
        inversion Hcontr.
        1,2: apply first_values in H2 as [? [? ?]];auto;try by intros [? ?]. done. done.
        intros [? [? ?]%to_val_cat]. done.
        intros ?%to_val_trap_is_singleton. do 2 destruct vs =>//. }
      { destruct vs =>//;[|do 2 destruct vs =>//].
        inversion H0;subst. done. }
      { destruct vs =>//;[|do 2 destruct vs =>//].
        inversion H0;subst. done. }
      { exists (LH_base [] []),0. by cbn. }
      { exists (LH_base [] []),0. split;[|lia]. by cbn. }
      
    }
    { apply first_values in H9 as [? [? ?]];auto. done.
      1,2: by intros [? ?].
      subst. apply v_to_e_is_const_list. }
    { apply first_values in H9 as [? [? ?]];auto. done.
      subst. 1,2: by intros [? ?]. simplify_eq. apply v_to_e_is_const_list. }
    { subst.
      apply lfilled_Ind_Equivalent in H.
      inversion H.
      { subst.
        apply lfilled_Ind_Equivalent in H0.
        inversion H0;subst.
        apply const_list_snoc_eq3 in H2 as [? [? [? [? [? ?]]]]];auto.
        2: eapply reduce_not_nil;eauto.
        2,3: rewrite /to_val; eapply val_head_stuck_reduce in Hred as ->. 2: by intros [? ?]. 2: done.
        subst.
        assert (lfilled 0 (LH_base x x0) [AI_trap] (x ++ [AI_trap] ++ x0)) as Hf%IHHred.
        { apply lfilled_Ind_Equivalent. constructor. auto. }
        destruct Hf as [lh' [j [Hfill'%lfilled_Ind_Equivalent Hle]]].
        inversion Hfill';subst.
        { exists (LH_base (vs0++vs) (es'0 ++ es'1)),0.
          assert (vs0 ++ (vs ++ [AI_trap] ++ es'0) ++ es'1 =
                    (vs0 ++ vs) ++ [AI_trap] ++ (es'0 ++ es'1))%SEQ as Heq.
          { repeat erewrite app_assoc. auto. }
          rewrite Heq. split;[|lia]. apply lfilled_Ind_Equivalent. constructor.
          apply const_list_app. auto. }
        { exists (LH_rec (vs0 ++ vs) n es'0 lh'0 (es'' ++ es'1)),(S k).
          assert (vs0 ++ (vs ++ [AI_label n es'0 LI] ++ es'') ++ es'1 =
                 (vs0 ++ vs) ++ [AI_label n es'0 LI] ++ (es'' ++ es'1))%SEQ as ->.
          { repeat erewrite app_assoc. auto. } inversion Hle.
          (* apply lfilled_Ind_Equivalent. constructor;auto. *)
          (* apply const_list_app;auto. *)
        }
      }
      { apply first_values in H2 as [? [? ?]];auto. done. by intros [? ?]. by intros [? ?]. }
    }
    { subst.
      apply lfilled_Ind_Equivalent in H.
      apply lfilled_Ind_Equivalent in H0.
      inversion H;subst.
      { apply const_list_snoc_eq3 in H3 as [? [? [? [? [? ?]]]]];auto.
        2: eapply reduce_not_nil;eauto.
        2,3: rewrite /to_val; eapply val_head_stuck_reduce in Hred as ->. 2: by intros [? ?]. 2: done.
        subst.
        inversion H0;subst.
        destruct IHHred with (i := S k0) (lh:=LH_rec x n es'0 lh'0 x0) as [lh' [j [Hfill'%lfilled_Ind_Equivalent Hle]]].
        { apply lfilled_Ind_Equivalent. constructor;auto. }
        inversion Hfill';subst.
        { exists (LH_base (vs0 ++ vs) (es'2 ++ es'1)),0.
          assert (vs0 ++ (vs ++ [AI_trap] ++ es'2) ++ es'1 =
                    (vs0 ++ vs) ++ [AI_trap] ++ (es'2 ++ es'1))%SEQ as Heq.
          { repeat erewrite app_assoc. auto. }
          rewrite Heq. split;[|lia]. apply lfilled_Ind_Equivalent. constructor.
          apply const_list_app. auto. }
        { exists (LH_rec (vs0 ++ vs) n0 es'2 lh'1 (es'' ++ es'1)),(S k).
          assert (vs0 ++ (vs ++ [AI_label n0 es'2 LI0] ++ es'') ++ es'1 =
                 (vs0 ++ vs) ++ [AI_label n0 es'2 LI0] ++ (es'' ++ es'1))%SEQ as ->.
          { repeat erewrite app_assoc. auto. }
          split;[|lia].
          apply lfilled_Ind_Equivalent. constructor;auto.
          apply const_list_app;auto.
        }
      }
      { apply first_values in H3 as [? [? ?]];simplify_eq;auto.
        apply lfilled_Ind_Equivalent in H2.
        apply lfilled_Ind_Equivalent in H8.
        eapply lfilled_singleton in H2 as [? [? [HH%IHHred Heq]]];[..|apply H8];auto.
        2: eapply reduce_not_nil;eauto.
        2,3: rewrite /to_val; eapply val_head_stuck_reduce in Hred as ->. 2: by intros [? ?]. 2: done.
        inversion H0;subst.
        destruct HH as [lh2 [j2 [Hlh2 Hle2]]].
        apply lfilled_Ind_Equivalent in H13.
        eapply lfilled_trans in H13 as [? ?];[|apply Hlh2].
        exists (LH_rec vs n es'0 x1 es''),(S (j2 + k1)). split;[|lia].
        apply lfilled_Ind_Equivalent;constructor;auto.
        apply lfilled_Ind_Equivalent;auto.
        1,2: by intros [? ?].
      }
    }
  Qed.
    
  Lemma trap_reduce_nested hs s f es hs' s' f' es' lh i :
    lfilled i lh [AI_trap] es -> reduce hs s f es hs' s' f' es' ->
    (exists lh' j, lfilled j lh' [AI_trap] es' ∧ j <= i) ∧ (hs,s,f) = (hs',s',f').
  Proof.
    intros Hfill Hred.
    eapply trap_reduce_state_eq in Hred as Heq;eauto.
    eapply trap_reduce_lfilled in Hred as Hf;eauto.
  Qed.

  Lemma first_values_elem_of vs1 e1 es1 vs2 e2 es2 :
  ((∃ v, to_val [e1] = Some (immV v)) -> False) ->
  ((∃ v, to_val [e2] = Some (immV v)) -> False) ->
  e2 ∉ vs1 ->
  e1 ∉ vs2 ->
  vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 ->
  vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
Proof.
  intros He1 He2 Hvs1 Hvs2 Heq.
  generalize dependent vs2; induction vs1 ; intros.
  { destruct vs2 ; inversion Heq => //=. rewrite <- H0 in Hvs2.
    simpl in Hvs2. apply not_elem_of_cons in Hvs2 as [Hcontr _]. done. }
  destruct vs2 ; inversion Heq.
  { rewrite H0 in Hvs1.
    simpl in Hvs1. apply not_elem_of_cons in Hvs1 as [Hcontr _]. done. }
  assert (vs1 = vs2 /\ e1 = e2 /\ es1 = es2) as H ; last by destruct H ; subst.
  apply not_elem_of_cons in Hvs1 as [Hne Hvs1].
  apply not_elem_of_cons in Hvs2 as [Hne' Hvs2].
  apply IHvs1 => //=.
Qed.
Lemma const_list_elem_of e es :
  const_list es ->
  ((∃ v, to_val [e] = Some (immV v)) -> False) ->
  e ∉ es.
Proof.
  intros Hes Hv.
  induction es.
  { apply not_elem_of_nil. }
  { destruct (e == a) eqn:Heq.
    { revert Heq. move/eqP =>Heq.
      destruct a;try done. destruct b;try done.
      simplify_eq. exfalso. apply Hv. eauto. }
    simpl in Hes. apply andb_true_iff in Hes as [He Hes].
    revert Heq. move/eqP =>Heq.
    apply IHes in Hes.
    apply not_elem_of_cons. auto. }
Qed.
Lemma const_list_l_snoc_eq3 es'' :
  forall vs es ves e es',
    const_list ves ->
    e ∉ vs ->
    es ≠ [] ->
    ((∃ v, to_val es = Some (immV v)) -> False) ->
    (to_val es = Some trapV -> False) ->
    ((∃ v, to_val [e] = Some (immV v)) -> False) ->
    (vs ++ es ++ es')%SEQ = ves ++ [e] ++ es'' ->
    ∃ vs2 es2, ves = vs ++ vs2 ∧ es = vs2 ++ [e] ++ es2 ∧ es'' = es2 ++ es' ∧ const_list vs2.
  Proof.
    intros vs es ves e es' Hconst1 Hnin Hneq Hnval1 Hnval2 He Heq.
    apply to_val_None_first_singleton in Hnval2 as HH;auto.
    destruct HH as [vs' [e' [es2 [Heq' [Hconst HH]]]]].
    assert (Heqcopy:=Heq).
    rewrite Heq' in Heqcopy.
    assert (vs ++ (vs' ++ [e'] ++ es2)%list ++ es' = (vs ++ vs') ++ [e'] ++ (es2 ++ es'))%SEQ as Heq2.
    { rewrite !app_assoc. repeat erewrite app_assoc. auto. }
    rewrite Heq2 in Heqcopy. clear Heq2. unfold to_val in He. (* unfold to_val in HH. *)
    apply first_values_elem_of in Heqcopy as [Heq1 [Heq2 Heq3]];auto.
    (* all: unfold iris.to_val in HH. *)
    2: (destruct HH as [-> | [[-> _] | [[? ->] | ->]]]; by intros [? ?]).
    2: { apply not_elem_of_app. split;[|apply const_list_elem_of;auto]. auto. }
    2: apply const_list_elem_of;auto.
    2: (destruct HH as [-> | [[-> _] | [[? ->] | ->]]]; by intros [? ?]).
    subst e'.
    rewrite -Heq1 in Heq.
    rewrite -Heq3 in Heq.
    assert ((vs ++ vs')%SEQ ++ [e] ++ (es2 ++ es')%SEQ =
              (vs ++ (vs' ++ [e] ++ es2) ++ es')%SEQ) as Hassoc.
    { rewrite !app_assoc. repeat erewrite app_assoc. auto. }
    rewrite Hassoc in Heq;clear Hassoc.
    apply app_inv_head in Heq.
    apply app_inv_tail in Heq.
    eexists _,_. eauto.    
  Qed.  

Lemma elem_of_app_l :
  ∀ (A : Type) (l1 l2 : seq.seq A) (x : A) (eqA : EqDecision A), x ∈ l1 ++ l2 ↔ x ∈ l1 ∨ (x ∈ l2 ∧ x ∉ l1).
Proof.
  intros A l1 l2 x eqA.
  induction l1.
  { rewrite app_nil_l.
    split;intros.
    right.
    split;auto.
    apply not_elem_of_nil.
    destruct H as [? | [? ?]];try done.
    inversion H.
  }
  { simpl. destruct (decide (x = a)).
    { simplify_eq. split.
      intros Ha. left. constructor.
      intros _. constructor. }
    { split.
      { intros [Hcontr|[Ha | [Ha Hnin]]%IHl1]%elem_of_cons;[done|..].
        left. by constructor.
        right. split;auto. apply not_elem_of_cons;auto. }
      { intros [[Hcontr|Ha]%elem_of_cons|[Hin Hnin]];[done|..].
        constructor. apply elem_of_app. by left.
        constructor. apply elem_of_app. by right. }
    }
  }
Qed.

Lemma filled_is_val_br_app_cases : ∀ i lh es1 es2 LI j v1 e1 ,
    iris.to_val LI = Some (brV j v1 e1) ->
    (es1 ++ es2) ≠ [] ->
    lfilled i lh (es1 ++ es2) LI ->
    i = 0 ∧ ∃ vs es, lh = LH_base vs es ∧ ((∃ es11 es12, es1 = es11 ++ (AI_basic (BI_br j)) :: es12 ∧ const_list es11) ∨
                                           (∃ es21 es22, es2 = es21 ++ (AI_basic (BI_br j)) :: es22 ∧ const_list es21 ∧ const_list es1) ∨
                                           (∃ es1' es2', es = es1' ++ (AI_basic (BI_br j)) :: es2' ∧ const_list es1 ∧ const_list es2 ∧ const_list es1')).
Proof.
  assert (EqDecision administrative_instruction) as Heqa.
  { unfold EqDecision. apply administrative_instruction_eq_dec. }
  
  intros i lh es1 es2 LI j v1 e1 HLI Hnil Hfill.
  eapply filled_is_val_br in Hfill as Heq;eauto. subst.
  apply lfilled_Ind_Equivalent in Hfill.
  inversion Hfill.
  simplify_eq. split;auto.
  exists vs,es'. split;auto.
  clear Hfill.
  apply to_val_br in HLI as Heq.
  repeat erewrite app_assoc in Heq.
  rewrite -!app_assoc in Heq.
  assert ((AI_basic (BI_br j)) ∈ (vs ++ es1 ++ es2 ++ es')) as Hin.
  { rewrite Heq. apply elem_of_app. right. constructor. }
  
  apply elem_of_app in Hin as [Hcontr | Hin].
  { apply elem_of_list_split in Hcontr as [l1 [l2 Hl]]. subst.
    apply const_list_app in H as [_ H]. done. }

  apply elem_of_app_l in Hin as [Hin | [Hin Hnin]].
  { left.
    eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin]]].
    rewrite (app_assoc _ es2) in Heq.
    apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
    2: apply v_to_e_is_const_list.
    2: apply const_list_elem_of;auto;by intros [? ?].
    2: by intros [? [[_ ?]%to_val_cat _]%to_val_cat].
    2: intros ?%to_val_trap_is_singleton;by do 2 destruct l1 =>//.
    destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]]. Unshelve.
    rewrite separate1 in Heq2. rewrite -!app_assoc in Heq2.
    apply const_list_l_snoc_eq3 in Heq2;auto;try by intros [? ?].
    2: intros ?;done.
    destruct Heq2 as [vs3 [es4 [Heq21 [Heq22 [Heq23 Hconst']]]]].
    destruct vs3 =>//;[|destruct vs3 =>//].
    destruct es4 =>//. rewrite app_nil_l in Heq23.
    rewrite app_nil_l app_nil_r in Heq22.
    rewrite app_nil_r in Heq21. simplify_eq.
    exists l1,l2. split;auto. }
  apply elem_of_app_l in Hin as [Hin | [Hin Hnin2]].
  { right;left.
    eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
    rewrite separate1 in Heq. rewrite -!app_assoc in Heq.
    do 2 rewrite app_assoc in Heq. exists l1,l2. split;auto.
    apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
    4: intros ?;done.
    2: apply v_to_e_is_const_list.
    2: { apply not_elem_of_app;split;auto.
         apply not_elem_of_app;split;auto.
         apply const_list_elem_of;auto. by intros [? ?]. }
    destruct Heq as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
    simplify_eq.
    destruct vs2 =>//;[|destruct vs2 =>//].
    destruct es2 =>//. rewrite app_nil_r in Heq1.
    pose proof (v_to_e_is_const_list v1) as Hc.
    rewrite -to_e_list_fmap Heq1 in Hc.
    apply const_list_app in Hc as [[? ?]%const_list_app ?]. auto. }
  { right;right.
    eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
    rewrite separate1 in Heq.
    do 3 rewrite app_assoc in Heq.
    exists l1,l2. split;auto.
    apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
    4: intros ?;done.
    2: apply v_to_e_is_const_list.
    2: { repeat (apply not_elem_of_app;split;auto).
         apply const_list_elem_of;auto. by intros [? ?]. }
    destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]].
    simplify_eq.
    destruct vs2 =>//;[|destruct vs2 =>//].
    destruct es3 =>//.
    rewrite app_nil_r in Heq1.
    pose proof (v_to_e_is_const_list v1) as Hc.
    rewrite -to_e_list_fmap Heq1 in Hc.
    apply const_list_app in Hc as [[[? ?]%const_list_app ?]%const_list_app ?]. auto.
  }
  all: auto.
Qed.

Lemma filled_is_val_ret_app_cases : ∀ i lh es1 es2 LI v1 e1 ,
    iris.to_val LI = Some (retV v1 e1) ->
    (es1 ++ es2) ≠ [] ->
    lfilled i lh (es1 ++ es2) LI ->
    i = 0 ∧ ∃ vs es, lh = LH_base vs es ∧ ((∃ es11 es12, es1 = es11 ++ (AI_basic (BI_return)) :: es12 ∧ const_list es11) ∨
                                           (∃ es21 es22, es2 = es21 ++ (AI_basic (BI_return)) :: es22 ∧ const_list es21 ∧ const_list es1) ∨
                                           (∃ es1' es2', es = es1' ++ (AI_basic (BI_return)) :: es2' ∧ const_list es1 ∧ const_list es2 ∧ const_list es1')).
Proof.
  assert (EqDecision administrative_instruction) as Heqa.
  { unfold EqDecision. apply administrative_instruction_eq_dec. }
  
  intros i lh es1 es2 LI v1 e1 HLI Hnil Hfill.
  eapply filled_is_val_ret in Hfill as Heq;eauto. subst.
  apply lfilled_Ind_Equivalent in Hfill.
  inversion Hfill.
  simplify_eq. split;auto.
  exists vs,es'. split;auto.
  clear Hfill.
  apply to_val_ret in HLI as Heq.
  repeat erewrite app_assoc in Heq.
  rewrite -!app_assoc in Heq.
  assert ((AI_basic (BI_return)) ∈ (vs ++ es1 ++ es2 ++ es')) as Hin.
  { rewrite Heq. apply elem_of_app. right. constructor. }
  
  apply elem_of_app in Hin as [Hcontr | Hin].
  { apply elem_of_list_split in Hcontr as [l1 [l2 Hl]]. subst.
    apply const_list_app in H as [_ H]. done. }

  apply elem_of_app_l in Hin as [Hin | [Hin Hnin]].
  { left.
    eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin]]].
    rewrite (app_assoc _ es2) in Heq.
    apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
    2: apply v_to_e_is_const_list.
    2: apply const_list_elem_of;auto;by intros [? ?].
    2: by intros [? [[_ ?]%to_val_cat _]%to_val_cat].
    2: intros ?%to_val_trap_is_singleton;by do 2 destruct l1 =>//.
    destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]]. Unshelve.
    rewrite separate1 in Heq2. rewrite -!app_assoc in Heq2.
    apply const_list_l_snoc_eq3 in Heq2;auto;try by intros [? ?].
    2: intros ?;done.
    destruct Heq2 as [vs3 [es4 [Heq21 [Heq22 [Heq23 Hconst']]]]].
    destruct vs3 =>//;[|destruct vs3 =>//].
    destruct es4 =>//. rewrite app_nil_l in Heq23.
    rewrite app_nil_l app_nil_r in Heq22.
    rewrite app_nil_r in Heq21. simplify_eq.
    exists l1,l2. split;auto. }
  apply elem_of_app_l in Hin as [Hin | [Hin Hnin2]].
  { right;left.
    eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
    rewrite separate1 in Heq. rewrite -!app_assoc in Heq.
    do 2 rewrite app_assoc in Heq. exists l1,l2. split;auto.
    apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
    4: intros ?;done.
    2: apply v_to_e_is_const_list.
    2: { apply not_elem_of_app;split;auto.
         apply not_elem_of_app;split;auto.
         apply const_list_elem_of;auto. by intros [? ?]. }
    destruct Heq as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
    simplify_eq.
    destruct vs2 =>//;[|destruct vs2 =>//].
    destruct es2 =>//. rewrite app_nil_r in Heq1.
    pose proof (v_to_e_is_const_list v1) as Hc.
    rewrite -to_e_list_fmap Heq1 in Hc.
    apply const_list_app in Hc as [[? ?]%const_list_app ?]. auto. }
  { right;right.
    eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
    rewrite separate1 in Heq.
    do 3 rewrite app_assoc in Heq.
    exists l1,l2. split;auto.
    apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
    4: intros ?;done.
    2: apply v_to_e_is_const_list.
    2: { repeat (apply not_elem_of_app;split;auto).
         apply const_list_elem_of;auto. by intros [? ?]. }
    destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]].
    simplify_eq.
    destruct vs2 =>//;[|destruct vs2 =>//].
    destruct es3 =>//.
    rewrite app_nil_r in Heq1.
    pose proof (v_to_e_is_const_list v1) as Hc.
    rewrite -to_e_list_fmap Heq1 in Hc.
    apply const_list_app in Hc as [[[? ?]%const_list_app ?]%const_list_app ?]. auto.
  }
  all: auto.
Qed.

Lemma of_val_br_app_r n v es1 es2 :
  of_val (brV n v es1) ++ es2 = of_val (brV n v (es1 ++ es2)).
Proof.
  simpl. destruct es2.
  { repeat erewrite app_nil_r. auto. }
  { rewrite separate1. rewrite (separate1 a).
    repeat erewrite app_assoc. rewrite -!app_assoc. f_equiv.
    simpl.  auto. }
Qed.

Lemma of_val_ret_app_r v es1 es2 :
  of_val (retV v es1) ++ es2 = of_val (retV v (es1 ++ es2)).
Proof.
  simpl. destruct es2.
  { repeat erewrite app_nil_r. auto. }
  { rewrite separate1. rewrite (separate1 a).
    repeat erewrite app_assoc. rewrite -!app_assoc. f_equiv.
    simpl.  auto. }
Qed.

Lemma lfilled_to_val_app i lh es1 es2 LI vs :
  lfilled i lh (es1 ++ es2)%list LI ->
  to_val LI = Some vs ->
  (∃ vs', to_val es1 = Some vs' ∧ lfilled i lh ((iris.of_val vs') ++ es2) LI).
Proof.
  intros Hfilled Hetov.
  destruct vs.
  { pose proof (filled_is_val_imm _ _ _ _ _ Hetov Hfilled) as
    [vs [es' [-> [-> [Hconst1 Hconst2]]]]].
    apply const_list_is_val in Hconst1 as [v1 Hv1].
    apply const_list_is_val in Hconst2 as [v2 Hv2].
    edestruct fill_val as [vs12 [Hvs12 Heql]];eauto.
    assert (Hvs12':=Hvs12). unfold to_val.
    apply to_val_cat in Hvs12' as [-> Hev2].
    apply iris.of_to_val in Hev2 as <-. eexists. split; eauto.
    rewrite -!of_val_imm.
    erewrite <- fmap_app. rewrite take_drop.
    rewrite of_val_imm.
    apply lfilled_Ind_Equivalent in Hfilled.
    inversion Hfilled;simplify_eq.
    erewrite of_to_val;eauto.
    apply lfilled_Ind_Equivalent. constructor. auto. }
  { apply to_val_trap_is_singleton in Hetov as Heq. subst.
    apply lfilled_Ind_Equivalent in Hfilled.
    inversion Hfilled.
    2: { exfalso. do 2 destruct vs =>//=. }
    simplify_eq.
    apply app_eq_singleton in H as [[HH HH']|[HH HH']];subst.
    { exfalso. destruct es1,es2,es' =>//=. }
    apply app_eq_singleton in HH' as [[HH HH']|[HH HH']];subst.
    { apply app_eq_singleton in HH as [[-> ->]|[-> ->]].
      simpl. eauto. eauto. }
    { apply app_nil in HH as [-> ->]. eauto. }
  }
  { destruct (decide (es1 ++ es2 = [])).
    { apply app_nil in e0 as [-> ->]. eauto. }
    eapply filled_is_val_br_app_cases in Hfilled as HH;[|eauto..].
    destruct HH as [-> [vs [es [-> HH]]]].
    destruct HH as [[es11 [es12 [Heq Hconst]]]
                   |[[es11 [es12 [Heq (Hconst & Hconst')]]]
                    |[es11 [es12 [Heq (Hconst&Hconst'&Hconst'')]]]]].
    { apply const_es_exists in Hconst as Hv.
      destruct Hv as [v Hv].
      exists (brV n v es12). rewrite -to_val_br_eq Heq -Hv.
      split;auto. rewrite Hv in Heq. erewrite of_to_val. 2: apply to_val_br_eq.
      rewrite -Heq. auto. }
    { apply const_list_is_val in Hconst' as Hv.
      destruct Hv as [v Hv].
      exists (immV v). split;auto. erewrite of_to_val;eauto. }
    { apply const_list_is_val in Hconst as Hv.
      destruct Hv as [v Hv].
      exists (immV v). split;auto. erewrite of_to_val;eauto. }  
  }
  { destruct (decide (es1 ++ es2 = [])).
    { apply app_nil in e0 as [-> ->]. eauto. }
    eapply filled_is_val_ret_app_cases in Hfilled as HH;[|eauto..].
    destruct HH as [-> [vs [es [-> HH]]]].
    destruct HH as [[es11 [es12 [Heq Hconst]]]
                   |[[es11 [es12 [Heq (Hconst & Hconst')]]]
                    |[es11 [es12 [Heq (Hconst&Hconst'&Hconst'')]]]]].
    { apply const_es_exists in Hconst as Hv.
      destruct Hv as [v Hv].
      exists (retV v es12). rewrite -to_val_ret_eq Heq -Hv.
      split;auto. rewrite Hv in Heq. erewrite of_to_val. 2: apply to_val_ret_eq.
      rewrite -Heq. auto. }
    { apply const_list_is_val in Hconst' as Hv.
      destruct Hv as [v Hv].
      exists (immV v). split;auto. erewrite of_to_val;eauto. }
    { apply const_list_is_val in Hconst as Hv.
      destruct Hv as [v Hv].
      exists (immV v). split;auto. erewrite of_to_val;eauto. }  
  }
Qed.

Lemma lfilled_to_val_0 i lh e es v :
  lfilled i lh e es ->
  iris.to_val es = Some v ->
  i = 0.
Proof.
  intros Hfill Hes.
  apply lfilled_Ind_Equivalent in Hfill.
  inversion Hfill;auto.
  simplify_eq.
  exfalso.
  destruct v.
  { apply to_val_const_list in Hes as [? ?]%const_list_app. done. }
  { apply to_val_trap_is_singleton in Hes. do 2 destruct vs =>//. }
  { apply to_val_br in Hes. apply first_values in Hes as [? [? ?]];auto;try by intros [? ?].
    done. apply v_to_e_is_const_list. }
  { apply to_val_ret in Hes. apply first_values in Hes as [? [? ?]];auto;try by intros [? ?].
    done. apply v_to_e_is_const_list. }
Qed.  
  
End iris_properties.
