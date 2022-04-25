From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
(* From iris.bi Require Export weakestpre. *)
Require Export datatypes host operations properties opsem.
Require Export iris_locations iris_properties iris_atomicity iris_wp stdpp_aux.

Import uPred.

Set Default Proof Using "Type".

Close Scope byte_scope.

Definition expr := iris.expr.
Definition val := iris.val.
Definition to_val := iris.to_val.

(* Defining a Wasm-specific WP with frame existence *)

Import DummyHosts.

Canonical Structure wasm_lang := Language wasm_mixin.
 
Local Definition reducible := @reducible wasm_lang.
Local Definition state := state wasm_lang.

Implicit Type σ : state.

Class wfuncG Σ := WFuncG {
  func_invG :> invGS Σ;
  func_gen_hsG :> gen_heapGS N function_closure Σ;
}.

Class wtabG Σ := WTabG {
  tab_gen_hsG :> gen_heapGS (N*N) funcelem Σ;
}.

Class wtabsizeG Σ := WTabSizeG {
  tabsize_hsG :> gen_heapGS N nat Σ;
}.

Class wtablimitG Σ := WTabLimitG {
  tablimit_hsG :> gen_heapGS N (option N) Σ;                          
}.

Class wmemG Σ := WMemG {
  mem_gen_hsG :> gen_heapGS (N*N) byte Σ;
}.

Class wmemsizeG Σ := WMemSizeG {
  memsize_gen_hsG :> gen_heapGS N N Σ;
}.

Class wmemlimitG Σ := WMemLimitG {
  memlimit_hsG :> gen_heapGS N (option N) Σ;
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
Global Instance heapG_irisG `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wtablimitG Σ, !wmemG Σ, !wmemsizeG Σ, !wmemlimitG Σ, !wglobG Σ, !wframeG Σ} : irisGS wasm_lang Σ := {
  iris_invGS := func_invG; (* ??? *)
  state_interp σ _ κs _ :=
    let: (_, s, locs, inst) := σ in
     ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
      (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
      (gen_heap_interp (gmap_of_list s.(s_globals))) ∗
      (ghost_map_auth frameGName 1 (<[ tt := Build_frame locs inst ]> ∅)) ∗ 
      (gen_heap_interp (gmap_of_list (fmap mem_length s.(s_mems)))) ∗
      (gen_heap_interp (gmap_of_list (fmap tab_size s.(s_tables)))) ∗
      (gen_heap_interp (gmap_of_list (fmap mem_max_opt s.(s_mems)))) ∗
      (gen_heap_interp (gmap_of_list (fmap table_max_opt s.(s_tables))))
      
    )%I;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
  }.

Section Host_wp_import.
  (* Host wp must depend on the same memory model as for wasm *)
  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wtablimitG Σ, !wmemG Σ, !wmemsizeG Σ, !wmemlimitG Σ, !wglobG Σ, !wframeG Σ}.

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
Notation "n ↪[wtsize] m" := (mapsto (L:=N) (V:=nat) n (DfracDiscarded) m%V)
                              (at level 20, format "n ↪[wtsize] m") : bi_scope.
Notation "n ↪[wtlimit] m" := (mapsto (L:=N) (V:=option N) n (DfracDiscarded) m%V)
                              (at level 20, format "n ↪[wtlimit] m") : bi_scope.
Notation "n ↦[wm]{ q } [ i ] v" := (mapsto (L:=N*N) (V:=byte) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wm]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wm][ i ] v" := (mapsto (L:=N*N) (V:=byte) (n, i) (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wm][ i ] v") : bi_scope.
Notation "n ↦[wmlength] v" := (mapsto (L:=N) (V:=N) n (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wmlength] v") : bi_scope.
Notation "n ↪[wmlimit] v" := (mapsto (L:=N) (V:=option N) n (DfracDiscarded) v% V)
                           (at level 20, format "n ↪[wmlimit] v") : bi_scope.
Notation "n ↦[wg]{ q } v" := (mapsto (L:=N) (V:=global) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wg]{ q } v").
Notation "n ↦[wg] v" := (mapsto (L:=N) (V:=global) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wg] v") .
Notation " ↪[frame]{ q } v" := (ghost_map_elem frameGName tt q v%V)
                           (at level 20, q at level 5, format " ↪[frame]{ q } v") .
Notation " ↪[frame] v" := (ghost_map_elem frameGName tt (DfracOwn 1) v%V)
                           (at level 20, format " ↪[frame] v").

(* Predicates for memory blocks and whole tables *)  
Definition mem_block `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wtablimitG Σ, !wmemG Σ, !wmemsizeG Σ, !wmemlimitG Σ, !wglobG Σ, !wframeG Σ} (n: N) (m: memory) :=
  (([∗ list] i ↦ b ∈ (m.(mem_data).(ml_data)), n ↦[wm][ (N.of_nat i) ] b ) ∗
     n ↦[wmlength] mem_length m ∗ n ↪[wmlimit] (mem_max_opt m))%I.

Definition mem_block_at_pos `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wtablimitG Σ, !wmemG Σ, !wmemsizeG Σ, !wmemlimitG Σ, !wglobG Σ, !wframeG Σ} (n: N) (l:bytes) k :=
  ([∗ list] i ↦ b ∈ l, n ↦[wm][ (N.of_nat (N.to_nat k+i)) ] b)%I.

Definition tab_block `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wtablimitG Σ, !wmemG Σ, !wmemsizeG Σ, !wmemlimitG Σ, !wglobG Σ, !wframeG Σ} (n: N) (tab: tableinst) :=
  (([∗ list] i ↦ tabelem ∈ (tab.(table_data)), n ↦[wt][ (N.of_nat i) ] tabelem ) ∗
     (n ↪[wtsize] (tab_size tab)) ∗ (n ↪[wtlimit] (table_max_opt tab)))%I.


Notation "n ↦[wmblock] m" := (mem_block n m)
                           (at level 20, format "n ↦[wmblock] m"): bi_scope.
Notation "n ↦[wms][ i ] l" := (mem_block_at_pos n l i)
                                (at level 20, format "n ↦[wms][ i ] l"): bi_scope.
Notation "n ↦[wtblock] t" := (tab_block n t)
                           (at level 20, format "n ↦[wtblock] t"): bi_scope.

Section Wasm_wp.
  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wtablimitG Σ, !wmemG Σ, !wmemsizeG Σ, !wmemlimitG Σ, !wglobG Σ, !wframeG Σ}.

  Global Instance wp_wasm : Wp (iProp Σ) (expr) (val) stuckness.
  Proof using Σ wfuncG0 wtabG0 wtabsizeG0 wtablimitG0 wmemG0 wmemsizeG0 wmemlimitG0 wglobG0 wframeG0.
    eapply wp'. Unshelve. exact frame. exact (λ f,  ↪[frame] f)%I. Defined.

End Wasm_wp.

(* A Definition of a context dependent WP for WASM expressions *)

Definition wp_wasm_ctx `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wtablimitG Σ, !wmemG Σ, !wmemsizeG Σ, !wmemlimitG Σ, !wglobG Σ, !wframeG Σ}
          (s : stuckness) (E : coPset) (e : language.expr wasm_lang)
           (Φ : val -> iProp Σ) (i : nat) (lh : lholed) : iProp Σ := 
  ∀ LI, ⌜lfilled i lh e LI⌝ -∗ WP LI @ s; E {{ Φ }}.


Definition wp_wasm_frame `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wtablimitG Σ, !wmemG Σ, !wmemsizeG Σ, !wmemlimitG Σ, !wglobG Σ, !wframeG Σ}
          (s : stuckness) (E : coPset) (es : language.expr wasm_lang)
          (Φ : val -> iProp Σ) (n: nat) (f: frame) : iProp Σ :=
  
  WP [AI_local n f es] @ s; E {{ Φ }}.

Definition wp_wasm_ctx_frame `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wtablimitG Σ, !wmemG Σ, !wmemsizeG Σ, !wmemlimitG Σ, !wglobG Σ, !wframeG Σ}
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
  { unfold iris.to_val in Hsome. simpl in Hsome. simplify_eq.
    apply to_val_nil in Heq. auto. }
  { destruct vs.
    apply to_val_nil in Hsome. done.
    destruct es'.
    symmetry in Heq. unfold iris.to_val in Heq. simpl in *. simplify_eq.
    unfold iris.to_val in *.
    simpl in *.
    destruct a,a0 ; simpl in * ; (try done) ;
      (try destruct b ; simpl in * ; try done) ;
      (try destruct b0 ; simpl in * ; try done) ;
      (try destruct (merge_values_list (map _ l0)) as [vv|]; try done) ;
      try destruct vv ;
      try destruct i ;
      try destruct (vh_decrease _) ;
      try rewrite merge_br flatten_simplify in Hsome ;
      try rewrite merge_br flatten_simplify in Heq ;
      try rewrite merge_return flatten_simplify in Hsome ;
      try rewrite merge_return flatten_simplify in Heq ;
      try rewrite merge_trap flatten_simplify in Hsome ;
      try rewrite merge_trap flatten_simplify in Heq ;
      simpl in * ; simplify_eq.
    - rewrite merge_prepend in Hsome.
      rewrite merge_prepend in Heq.
      destruct (merge_values_list _) => //.
      destruct (merge_values_list _) eqn:Hmerge => //.
      simpl in *.
      destruct v2 => //.
      destruct v3 => //.
      simplify_eq.
      erewrite IHes => //.
      by rewrite Hmerge.
    - destruct es' => //.
    - destruct es => //.
    - destruct es, es' => //. }
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
        apply const_list_to_val in Hconst1 as [v ->]. eauto. }
      { destruct k,es' =>//.
        rewrite app_nil_r in Hk2. simplify_eq.
        eauto. }  }
    { rewrite Hk1 in Hconst1.
      apply to_val_cat_None1 with (es2:=k) in Hnval.
      apply const_list_to_val in Hconst1 as [v Hv].
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
  destruct vs1 => //.
  destruct vs1.
  apply to_val_nil in Hval. done.
  unfold to_val, iris.to_val in Hval.
  simpl in *.
  destruct a;try done ; simpl in *.
  destruct b;try done ; simpl in *.
  - rewrite merge_br flatten_simplify in Hval ; inversion Hval.
  - rewrite merge_return flatten_simplify in Hval ; inversion Hval.
  - rewrite merge_prepend in Hval. unfold to_val, iris.to_val in IHv1.
    destruct (merge_values_list _) => //. destruct v2 => //.
    inversion Hval ; subst. by erewrite IHv1.
  - rewrite merge_trap flatten_simplify in Hval.
    destruct v1 => //.
  - destruct (merge_values_list _) => //.
    destruct v0 => //.
    destruct i => //.
    destruct (vh_decrease _) => //.
    rewrite merge_br flatten_simplify in Hval ; inversion Hval.
    rewrite merge_return flatten_simplify in Hval ; inversion Hval. 
Qed.
Lemma const_list_app v1 v2 :
  const_list (v1 ++ v2) <-> const_list v1 ∧ const_list v2.
Proof.
  split.
  - intros Hconst.
    apply const_list_to_val in Hconst as [v Hv].
    apply to_val_cat in Hv as [Hv1%to_val_const_list Hv2%to_val_const_list];auto.
  - intros [Hconst1 Hconst2].
    apply const_list_to_val in Hconst1 as [v1' Hv1].
    apply const_list_to_val in Hconst2 as [v2' Hv2].
    eapply to_val_const_list.
    apply to_val_cat_inv;eauto.
Qed.

Section iris_properties.
  Import DummyHosts.

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
        { rewrite iris.iris_properties.first_instr_const;auto. }
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
        { rewrite iris.iris_properties.first_instr_const;auto. }
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
    (const_list es -> False) ->
    (es <> [AI_trap]) ->
    ∃ vs e es', es = vs ++ [e] ++ es' ∧ const_list vs ∧
                  ((to_val ([e]) = None)
                   ∨ (e = AI_trap ∧ (vs ≠ [] ∨ es' ≠ []))
                   ∨ (∃ n, e = (AI_basic (BI_br n)))
                   ∨ (e = (AI_basic BI_return))
                   \/ (exists n es LI, e = AI_label n es LI
                                 /\ ((exists i (vh: valid_holed i), to_val LI = Some (brV vh))
                                    \/ exists sh, to_val LI = Some (retV sh)))).
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
              exfalso. apply Hes1. by eapply to_val_const_list. }
            { apply to_val_trap_is_singleton in Hes as ->.
              apply to_val_const_list in Ha.
              exists [a],AI_trap,[]. cbn. repeat split;auto. }
            { destruct lh.
              - apply to_val_br_base in Hes as ->.
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat. eexists _,_,_. split;eauto.
                split;[apply v_to_e_is_const_list|]. right. right. left. eauto.
              - apply to_val_br_rec in Hes as (LI & -> & Htv).
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat. eexists _,_,_. split ; eauto.
                split ; [apply v_to_e_is_const_list |].
                repeat right. eexists _,_,_ ; split => //=.
                left. eauto.
            }
            { destruct s.
              - apply to_val_ret_base in Hes as ->.
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat.
                eexists _,_,_. split;eauto.
                split;[apply v_to_e_is_const_list|]. right. right. right. eauto.
              - apply to_val_ret_rec in Hes as (LI & -> & Htv).
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat.
                eexists _,_,_. split ; eauto.
                split;[apply v_to_e_is_const_list|]. repeat right.
                eexists _,_,_. split => //=.
                right. eauto.
            }
          }
          { destruct IHes as [vs [e [es' [Heq [Hconst HH]]]]];auto.  intros Hconst. apply const_list_to_val in Hconst as [??]. unfold to_val in Hes ; congruence. intro. rewrite H in Hes. unfold to_val, iris.to_val in Hes ; done.
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
          destruct es => //.
          exists [],AI_trap,(a :: es).
          repeat split;auto. }
        { destruct a;try done. destruct b;try done.
          unfold to_val, iris.to_val in Ha ; simpl in Ha.
          inversion Ha.
          apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
          exists [], (AI_basic (BI_br i)), es.
          repeat split => //=.
          right ; right ; left. eauto.
          unfold to_val, iris.to_val in Ha. simpl in Ha.
          destruct (merge_values_list _) eqn:Hmerge => //.
          destruct v => //.
          destruct i0 => //.
          destruct (vh_decrease _) => //.
          inversion Ha.
          destruct H0.
          apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
          exists [], (AI_label n l l0), es.
          repeat split => //.
          repeat right.
          eexists _,_,_ ; split => //.
          left.
          unfold to_val, iris.to_val.
          rewrite Hmerge. eauto. }
        { destruct a;try done. destruct b;try done.
          unfold to_val, iris.to_val in Ha ; simpl in Ha.
          inversion Ha ; subst.
          exists [], (AI_basic BI_return), es.
          repeat split => //=.
          right; right; right ; left ; eauto.
          unfold to_val, iris.to_val in Ha ; simpl in Ha.
          destruct (merge_values_list _) eqn:Hmerge => //.
          destruct v => //.
          destruct i => //.
          destruct (vh_decrease _) => //.
          inversion Ha ; subst.
          exists [], (AI_label n l l0), es.
          repeat split => //.
          repeat right.
          eexists _,_,_ ; split => //.
          right.
          unfold to_val, iris.to_val.
          rewrite Hmerge ; eauto.
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
    (const_list es -> False) ->
    (es = [AI_trap] -> False) ->
    (is_const e -> False) ->
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
    2:{ (destruct HH as [He' | [[-> _] | [[?  ->] | [-> | (? & ? & ? & -> & [ (? & ? & HLI) | [? HLI] ])]]]]) => //. destruct e' => //. destruct b => //. }
    2: by apply const_list_app. 
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
      2: eapply values_no_reduce => //.
      2: intros -> ; eapply AI_trap_irreducible => //.
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
        exfalso. apply const_list_to_val in H as [? ?].
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
      unfold to_val, iris.to_val => /=.
      unfold iris.to_val in HLI.
      destruct (merge_values_list _) => //.
    }
    { subst.
      apply reduce_not_nil in Hred as Hnil.
      apply val_head_stuck_reduce in Hred as Hnval.
      apply lfilled_Ind_Equivalent in H.
      inversion H;subst.
      { apply const_list_snoc_eq3 in H1 as [? [? [? [? [? ?]]]]];auto;subst.
        eapply IHHred;eauto. by eapply values_no_reduce.
        by intros -> ; eapply AI_trap_irreducible. }
      { apply first_values in H1 as [? [? ?]];auto. simplify_eq.
        apply lfilled_Ind_Equivalent in H6.
        apply lfilled_swap with (es':=es') in H6 as Hfill'.
        destruct Hfill' as [LI' Hfill'].
        exists LI'. eapply r_label;eauto.
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
    (const_list es -> False) ->
    (es <> [AI_trap]) ->
    (is_const a -> False) ->
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
        specialize (Hnlabel n es'0 LI). done. }
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
        eexists _,_. split;[apply H|lia]. }
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
      eapply values_no_reduce => //.
      intros -> ; eapply AI_trap_irreducible => //.
    }
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
        unfold const_list. rewrite forallb_app.
        intros [??]%andb_true_iff. done.
        do 2 destruct vs => //. }
      { destruct vs =>//;[|do 2 destruct vs =>//].
        inversion H0;subst. done. }
      { destruct vs =>//;[|do 2 destruct vs =>//].
        inversion H0;subst. done. }
      { exists (LH_base [] []),0. by cbn. }
      { exists (LH_base [] []),0. split;[|lia]. by cbn. }
      
    }
    { apply first_values in H9 as [? [? ?]];auto. done.
      subst. apply v_to_e_is_const_list. }
    { apply first_values in H9 as [? [? ?]];auto. done.
      subst. simplify_eq. apply v_to_e_is_const_list. }
    { subst.
      apply lfilled_Ind_Equivalent in H.
      inversion H.
      { subst.
        apply lfilled_Ind_Equivalent in H0.
        inversion H0;subst.
        apply const_list_snoc_eq3 in H2 as [? [? [? [? [? ?]]]]];auto.
        2: eapply reduce_not_nil;eauto.
        2: eapply values_no_reduce => //.
        2: intros -> ; eapply AI_trap_irreducible => //.
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
      { apply first_values in H2 as [? [? ?]];auto. done. }
    }
    { subst.
      apply lfilled_Ind_Equivalent in H.
      apply lfilled_Ind_Equivalent in H0.
      inversion H;subst.
      { apply const_list_snoc_eq3 in H3 as [? [? [? [? [? ?]]]]];auto.
        2: eapply reduce_not_nil;eauto.
        2: eapply values_no_reduce => //.
        2: intros -> ; eapply AI_trap_irreducible => //.
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
        2: eapply values_no_reduce => //.
        2: intros -> ; eapply AI_trap_irreducible => //.
        inversion H0;subst.
        destruct HH as [lh2 [j2 [Hlh2 Hle2]]].
        apply lfilled_Ind_Equivalent in H13.
        eapply lfilled_trans in H13 as [? ?];[|apply Hlh2].
        exists (LH_rec vs n es'0 x1 es''),(S (j2 + k1)). split;[|lia].
        apply lfilled_Ind_Equivalent;constructor;auto.
        apply lfilled_Ind_Equivalent;auto.
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
  (is_const e1 -> False) ->
  (is_const e2 -> False) ->
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
  (is_const e -> False) ->
  e ∉ es.
Proof.
  intros Hes Hv.
  intro Hin.
  unfold const_list in Hes.
  edestruct forallb_forall.
  apply Hv.
  eapply H in Hes.
  exact Hes.
  by apply elem_of_list_In.
Qed.

Lemma const_list_l_snoc_eq3 es'' :
  forall vs es ves e es',
    const_list ves ->
    e ∉ vs ->
    es ≠ [] ->
    (const_list es -> False) ->
    (es <> [AI_trap]) ->
    (is_const e -> False) ->
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
    2: (destruct HH as [He' | [[-> _] | [[? ->] | [-> | (? & ? & ? & -> & ?)]]]] => //).
    2: destruct e' => //; destruct b => //.
    2: { apply not_elem_of_app. split;[|apply const_list_elem_of;auto]. auto. }
    2: apply const_list_elem_of;auto.
    2: (destruct HH as [He' | [[-> _] | [[? ->] | [-> | (? & ? & ? & -> & ?)]]]] => //).
    2: destruct e' => // ; destruct b => //.
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

Lemma filled_is_val_br_base_app_cases : ∀ i lh es1 es2 LI j v1 e1 ,
    iris.to_val LI = Some (brV (VH_base j v1 e1)) ->
    (es1 ++ es2) ≠ [] ->
    lfilled i lh (es1 ++ es2) LI ->
    i = 0 ∧ ∃ vs es, lh = LH_base vs es ∧ ((∃ es11 es12, es1 = es11 ++ (AI_basic (BI_br j)) :: es12 ∧ const_list es11) ∨
                                           (∃ es21 es22, es2 = es21 ++ (AI_basic (BI_br j)) :: es22 ∧ const_list es21 ∧ const_list es1) ∨
                                           (∃ es1' es2', es = es1' ++ (AI_basic (BI_br j)) :: es2' ∧ const_list es1 ∧ const_list es2 ∧ const_list es1')).
Proof.
  assert (EqDecision administrative_instruction) as Heqa.
  { unfold EqDecision. apply administrative_instruction_eq_dec. }
  
  intros i lh es1 es2 LI j v1 e1 HLI Hnil Hfill.
  eapply filled_is_val_br_base in Hfill as Heq;eauto. subst.
  apply lfilled_Ind_Equivalent in Hfill.
  inversion Hfill.
  simplify_eq. split;auto.
  exists vs,es'. split;auto.
  clear Hfill.
  apply to_val_br_base in HLI as Heq.
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
    2: unfold const_list ; repeat rewrite forallb_app ; intros Habs ;
    repeat apply andb_true_iff in Habs as [Habs ?] => //.
    2: do 2 destruct l1 => //.
    destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]]. Unshelve.
    rewrite separate1 in Heq2. rewrite -!app_assoc in Heq2.
    apply const_list_l_snoc_eq3 in Heq2;auto;try by intros [? ?].
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
    2: apply v_to_e_is_const_list.
    2: { apply not_elem_of_app;split;auto.
         apply not_elem_of_app;split;auto.
         apply const_list_elem_of;auto. }
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
    2: apply v_to_e_is_const_list.
    2: { repeat (apply not_elem_of_app;split;auto).
         apply const_list_elem_of;auto. }
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

Lemma filled_is_val_ret_base_app_cases : ∀ i lh es1 es2 LI v1 e1 ,
    iris.to_val LI = Some (retV (SH_base v1 e1)) ->
    (es1 ++ es2) ≠ [] ->
    lfilled i lh (es1 ++ es2) LI ->
    i = 0 ∧ ∃ vs es, lh = LH_base vs es ∧ ((∃ es11 es12, es1 = es11 ++ (AI_basic (BI_return)) :: es12 ∧ const_list es11) ∨
                                           (∃ es21 es22, es2 = es21 ++ (AI_basic (BI_return)) :: es22 ∧ const_list es21 ∧ const_list es1) ∨
                                           (∃ es1' es2', es = es1' ++ (AI_basic (BI_return)) :: es2' ∧ const_list es1 ∧ const_list es2 ∧ const_list es1')).
Proof.
  assert (EqDecision administrative_instruction) as Heqa.
  { unfold EqDecision. apply administrative_instruction_eq_dec. }
  
  intros i lh es1 es2 LI v1 e1 HLI Hnil Hfill.
  eapply filled_is_val_ret_base in Hfill as Heq;eauto. subst.
  apply lfilled_Ind_Equivalent in Hfill.
  inversion Hfill.
  simplify_eq. split;auto.
  exists vs,es'. split;auto.
  clear Hfill.
  apply to_val_ret_base in HLI as Heq.
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
    2: unfold const_list ; repeat rewrite forallb_app ; intros Habs ;
    repeat apply andb_true_iff in Habs as [Habs ?] => //.
    2: do 2 destruct l1 => //.
    destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]]. Unshelve.
    rewrite separate1 in Heq2. rewrite -!app_assoc in Heq2.
    apply const_list_l_snoc_eq3 in Heq2;auto;try by intros [? ?].
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
    2: apply v_to_e_is_const_list.
    2: { apply not_elem_of_app;split;auto.
         apply not_elem_of_app;split;auto.
         apply const_list_elem_of;auto. }
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
    2: apply v_to_e_is_const_list.
    2: { repeat (apply not_elem_of_app;split;auto).
         apply const_list_elem_of;auto. }
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

Lemma of_val_br_app_r n (vh : valid_holed n) es2 :
  of_val (brV vh) ++ es2 = of_val (brV (vh_append vh es2)).
Proof.
  simpl. destruct vh => //= ; by rewrite app_comm_cons app_assoc. 
Qed.

Lemma of_val_ret_app_r sh es2 :
  of_val (retV sh) ++ es2 = of_val (retV (sh_append sh es2)).
Proof.
  simpl. destruct sh => //= ; by rewrite app_comm_cons app_assoc.
Qed.

Definition lh_prepend lh v :=
  match lh with
  | LH_base bef aft => LH_base (AI_basic (BI_const v) :: bef) aft
  | LH_rec bef n es lh aft => LH_rec (AI_basic (BI_const v) :: bef) n es lh aft end.

Lemma lfilled_prepend i lh es v LI :
  lfilled i lh es LI -> lfilled i (lh_prepend lh v) es (AI_basic (BI_const v) :: LI).
Proof.
  destruct i, lh ; unfold lfilled, lfill ; destruct (const_list l) eqn:Hl => //=.
  - intros H ; apply b2p in H ; subst ; rewrite Hl => //=.
  - fold lfill. destruct (lfill _ _ _) eqn:Hfill => //=.
    intros H ; apply b2p in H ; subst ; rewrite Hl => //=.
Qed.
    
Lemma lfilled_vLI i lh e es v LI :
  lfilled i lh (e :: es) (AI_basic (BI_const v) :: LI) ->
  (exists lh', lh_prepend lh' v = lh /\ lfilled i lh' (e :: es) LI) \/
    i = 0 /\ e = AI_basic (BI_const v) /\ exists aft, lh = LH_base [] aft /\ es ++ aft = LI.
Proof.
  intros Hfilled.
  unfold lfilled, lfill in Hfilled ; destruct i, lh ; destruct (const_list l) eqn:Hl => //.
  - apply b2p in Hfilled.
    destruct l.
    + inversion Hfilled ; subst.
      right. repeat split => //=.
      exists l0 => //.
    + inversion Hfilled ; subst.
      left. exists (LH_base l l0).
      split => //=.
      unfold lfilled, lfill => //=.
      unfold const_list in Hl. simpl in Hl. 
      unfold const_list ; rewrite Hl. done.
  - fold lfill in Hfilled.
    destruct (lfill i lh (e :: es)) eqn:Hfill => //.
    apply b2p in Hfilled.
    destruct l ; inversion Hfilled.
    subst.
    left. exists (LH_rec l n l0 lh l1).
    split => //.
    unfold lfilled, lfill ; fold lfill.
    unfold const_list in Hl ; simpl in Hl ; unfold const_list ; rewrite Hl.
    rewrite Hfill.
    done.
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
    apply const_list_to_val in Hconst1 as [v1 Hv1].
    apply const_list_to_val in Hconst2 as [v2 Hv2].
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
  { (* destruct es1 (*(decide (es1 ++ es2 = [])).*) ; first eauto. *)
    (*    { apply app_nil in e as [-> ->]. eauto. } *)
    remember (length_rec LI) as n.
    assert (length_rec LI < S n) ; first lia.
    remember (S n) as m.
    clear Heqn Heqm n.
    generalize dependent i0. generalize dependent es1. generalize dependent lh.
    generalize dependent i.
    generalize dependent LI.
    induction m ; intros LI Hsize ; intros ; first lia.
(*     { destruct i ; destruct lh ; unfold lfilled, lfill in Hfilled => //. } *)
    destruct es1 ; first eauto.
    unfold to_val, iris.to_val in Hetov ; simpl in Hetov.
    destruct LI ; first by inversion Hetov.
    destruct a0 ; try destruct b ; simpl in Hetov  => //.
    - rewrite merge_br flatten_simplify in Hetov.
      inversion Hetov.
      apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
      eapply filled_is_val_br_base_app_cases in Hfilled as HH;[|eauto..].
      destruct HH as [-> [vs [es [-> HH]]]].
      destruct HH as [[es11 [es12 [Heq Hconst]]]
                     |[[es11 [es12 [Heq (Hconst & Hconst')]]]
                      |[es11 [es12 [Heq (Hconst&Hconst'&Hconst'')]]]]].
      { apply const_es_exists in Hconst as Hv.
        destruct Hv as [v Hv].
        exists (brV (VH_base i0 v es12)). rewrite -to_val_br_eq Heq -Hv.
        split;auto. rewrite Hv in Heq. erewrite of_to_val. 2: apply to_val_br_eq.
        rewrite -Heq. auto. }
      { apply const_list_to_val in Hconst' as Hv.
        destruct Hv as [v Hv].
        exists (immV v). split;auto. erewrite of_to_val;eauto. }
      { apply const_list_to_val in Hconst as Hv.
        destruct Hv as [v Hv].
        exists (immV v). split;auto. erewrite of_to_val;eauto. }
      unfold iris.to_val => /=.
      rewrite merge_br flatten_simplify => //=.
    - rewrite merge_return flatten_simplify in Hetov => //.
    - rewrite merge_prepend in Hetov.
      destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v0 => //.
      simpl in Hetov.
      rewrite - app_comm_cons in Hfilled.
      apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
      + rewrite app_comm_cons in Hfilled.
        assert (length_rec LI < m) ;
          first by specialize (cons_length_rec (AI_basic (BI_const v)) LI) ; lia.
        specialize (IHm _ H _ _ _ Hfilled i1 lh1).
        unfold to_val in IHm at 1.
        unfold iris.to_val in IHm.
        rewrite Hmerge in IHm.
        destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
        exists vs' ; split => //.
        subst ; by apply lfilled_prepend.
      + assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
        unfold lfilled, lfill => //=.
        assert (length_rec ((es1 ++ es2) ++ aft) < m).
        { specialize (cons_length_rec (AI_basic (BI_const v))
                                      ((es1 ++ es2) ++ aft)) as H1.
          rewrite app_comm_cons in Hsize.
          repeat rewrite - cat_app in Hsize.
          rewrite app_comm_cons in H1.
          repeat rewrite - cat_app in H1.
          lia. }
        specialize (IHm _ H0 _ _ _ H i1 lh1).
        unfold to_val in IHm at 1.
        unfold iris.to_val in IHm.
        rewrite Hmerge in IHm.
        destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).        
        exists (val_combine (immV [v]) vs') ; split => //=.
        * unfold to_val, iris.to_val => /=.
          rewrite merge_prepend.
          unfold to_val, iris.to_val in Htv.
          destruct (merge_values_list (map _ es1)) eqn:Hmerge1 => //=.
          inversion Htv.
          destruct vs' => //.
          assert (to_val es1 = Some trapV) ;
            first by unfold to_val, iris.to_val ; rewrite Hmerge1 H2.
          apply to_val_trap_is_singleton in H1 as ->.
          simpl in Hmerge.
          rewrite merge_trap flatten_simplify in Hmerge.
          by destruct (es2 ++ aft).
        * unfold lfilled, lfill => //=.
          unfold lfilled, lfill in Hfill ; simpl in Hfill.
          apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
          destruct vs' => //.
          apply to_val_trap_is_singleton in Htv as ->.
          simpl in Hmerge.
          rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
          unfold iris.of_val. destruct lh => //.
          unfold iris.of_val. destruct s => //.
    - rewrite merge_trap flatten_simplify in Hetov.
      by destruct LI.
    - destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v => // ; last by rewrite merge_return flatten_simplify in Hetov.
      destruct i1 => //.
      destruct (vh_decrease _) eqn:Hdecr => //.
      rewrite merge_br flatten_simplify in Hetov.
      inversion Hetov.
      destruct H0.
      apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
      assert (length_rec l0 < m).
      { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
      unfold lfilled, lfill in Hfilled ; 
        destruct i,lh ; fold lfill in Hfilled => //.
      + destruct (const_list l1) eqn:Hl1 => //.
        apply b2p in Hfilled.
        destruct l1 ; inversion Hfilled ; subst ; 
          last by unfold const_list in Hl1; inversion Hl1.
        eexists. split.
        * unfold to_val, iris.to_val => /=.
          rewrite Hmerge Hdecr merge_br flatten_simplify => //.
        * unfold lfilled, lfill => //=.
          replace l0 with (vfill v [AI_basic (BI_br (S i1))]) ; first done.
          assert (iris.to_val l0 = Some (brV lh1)) ;
            first by unfold iris.to_val ; rewrite Hmerge.          
          apply iris.of_to_val in H0 as <-.
          unfold iris.of_val. by rewrite (vfill_decrease _ Hdecr).
      + destruct (const_list l1) eqn:Hl1 => //.
        destruct (lfill _ _ _) eqn:Hfill => //.
        apply b2p in Hfilled.
        destruct l1 ; inversion Hfilled ; subst ;
          last by unfold const_list in Hl1.
        assert (lfilled i lh ((a :: es1) ++ es2) l4); 
          first by unfold lfilled ; rewrite Hfill.
        specialize (IHm l4 H i lh (a :: es1) H0 (S i1) lh1).
        unfold to_val in IHm at 1.
        unfold iris.to_val in IHm.
        rewrite Hmerge in IHm.
        destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill').
        eexists ; split => //.
        unfold lfilled, lfill ; fold lfill => //=.
        unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
        apply b2p in Hfill' ; by subst. }
  { remember (length_rec LI) as n.
    assert (length_rec LI < S n) ; first lia.
    remember (S n) as m.
    clear Heqn Heqm n.
    generalize dependent s. generalize dependent es1. generalize dependent lh.
    generalize dependent i. 
    generalize dependent LI.
    induction m ; intros LI Hsize ; intros ; first lia.
(*     { destruct i ; destruct lh ; unfold lfilled, lfill in Hfilled => //. } *)
    destruct es1 ; first eauto.
    unfold to_val, iris.to_val in Hetov ; simpl in Hetov.
    destruct LI ; first by inversion Hetov.
    destruct a0 ; try destruct b ; simpl in Hetov  => //.
    - rewrite merge_br flatten_simplify in Hetov => //.
    - rewrite merge_return flatten_simplify in Hetov.
      inversion Hetov ; subst.
      eapply filled_is_val_ret_base_app_cases in Hfilled as HH;[|eauto..].
      destruct HH as [-> [vs [es [-> HH]]]].
      destruct HH as [[es11 [es12 [Heq Hconst]]]
                     |[[es11 [es12 [Heq (Hconst & Hconst')]]]
                      |[es11 [es12 [Heq (Hconst&Hconst'&Hconst'')]]]]].
      { apply const_es_exists in Hconst as Hv.
        destruct Hv as [v Hv].
        exists (retV (SH_base v es12)). rewrite -to_val_ret_eq Heq -Hv.
        split;auto. rewrite Hv in Heq. erewrite of_to_val. 2: apply to_val_ret_eq.
        rewrite -Heq. auto. }
      { apply const_list_to_val in Hconst' as Hv.
        destruct Hv as [v Hv].
        exists (immV v). split;auto. erewrite of_to_val;eauto. }
      { apply const_list_to_val in Hconst as Hv.
        destruct Hv as [v Hv].
        exists (immV v). split;auto. erewrite of_to_val;eauto. }
      unfold iris.to_val => /=.
      rewrite merge_return flatten_simplify => //=.
    - rewrite merge_prepend in Hetov.
      destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v0 => //.
      simpl in Hetov.
      rewrite - app_comm_cons in Hfilled.
      apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
      + rewrite app_comm_cons in Hfilled.
        assert (length_rec LI < m) ;
          first by specialize (cons_length_rec (AI_basic (BI_const v)) LI) ; lia.
        specialize (IHm _ H _ _ _ Hfilled s0).
        unfold to_val in IHm at 1.
        unfold iris.to_val in IHm.
        rewrite Hmerge in IHm.
        destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
        exists vs' ; split => //.
        subst ; by apply lfilled_prepend.
      + assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
        unfold lfilled, lfill => //=.
        assert (length_rec ((es1 ++ es2) ++ aft) < m).
        { specialize (cons_length_rec (AI_basic (BI_const v))
                                      ((es1 ++ es2) ++ aft)) as H1.
          rewrite app_comm_cons in Hsize.
          repeat rewrite - cat_app in Hsize.
          rewrite app_comm_cons in H1.
          repeat rewrite - cat_app in H1.
          lia. }
        specialize (IHm _ H0 _ _ _ H s0).
        unfold to_val in IHm at 1.
        unfold iris.to_val in IHm.
        rewrite Hmerge in IHm.
        destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).        
        exists (val_combine (immV [v]) vs') ; split => //=.
        * unfold to_val, iris.to_val => /=.
          rewrite merge_prepend.
          unfold to_val, iris.to_val in Htv.
          destruct (merge_values_list (map _ es1)) eqn:Hmerge1 => //=.
          inversion Htv.
          destruct vs' => //.
          assert (to_val es1 = Some trapV) ;
            first by unfold to_val, iris.to_val ; rewrite Hmerge1 H2.
          apply to_val_trap_is_singleton in H1 as ->.
          simpl in Hmerge.
          rewrite merge_trap flatten_simplify in Hmerge.
          by destruct (es2 ++ aft).
        * unfold lfilled, lfill => //=.
          unfold lfilled, lfill in Hfill ; simpl in Hfill.
          apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
          destruct vs' => //.
          apply to_val_trap_is_singleton in Htv as ->.
          simpl in Hmerge.
          rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
          unfold iris.of_val. destruct lh => //.
          unfold iris.of_val. destruct s1 => //.
    - rewrite merge_trap flatten_simplify in Hetov.
      by destruct LI.
    - destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v => //.
      destruct i0 => //.
      destruct (vh_decrease _) eqn:Hdecr => //.
      rewrite merge_br flatten_simplify in Hetov => //.
      rewrite merge_return flatten_simplify in Hetov.
      inversion Hetov ; subst.
      assert (length_rec l0 < m).
      { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
      unfold lfilled, lfill in Hfilled ; 
        destruct i,lh ; fold lfill in Hfilled => //.
      + destruct (const_list l1) eqn:Hl1 => //.
        apply b2p in Hfilled.
        destruct l1 ; inversion Hfilled ; subst ; 
          last by unfold const_list in Hl1; inversion Hl1.
        eexists. split.
        * unfold to_val, iris.to_val => /=.
          rewrite Hmerge merge_return flatten_simplify => //.
        * unfold lfilled, lfill => //=.
          replace l0 with (sfill s0 [AI_basic BI_return]) ; first done.
          assert (iris.to_val l0 = Some (retV s0)) ;
            first by unfold iris.to_val ; rewrite Hmerge.          
          apply iris.of_to_val in H0 as <-.
          unfold iris.of_val. done.
      + destruct (const_list l1) eqn:Hl1 => //.
        destruct (lfill _ _ _) eqn:Hfill => //.
        apply b2p in Hfilled.
        destruct l1 ; inversion Hfilled ; subst ;
          last by unfold const_list in Hl1.
        assert (lfilled i lh ((a :: es1) ++ es2) l4); 
          first by unfold lfilled ; rewrite Hfill.
        specialize (IHm l4 H i lh (a :: es1) H0 s0).
        unfold to_val in IHm at 1.
        unfold iris.to_val in IHm.
        rewrite Hmerge in IHm.
        destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill').
        eexists ; split => //.
        unfold lfilled, lfill ; fold lfill => //=.
        unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
        apply b2p in Hfill' ; by subst. }
Qed.

Lemma to_val_brV_None vs n i lh es LI :
  const_list vs ->
  length vs = n ->
  lfilled i lh (vs ++ [AI_basic (BI_br i)]) LI ->
  iris.to_val [AI_label n es LI] = None.
Proof.
  intros Hconst Hlen Hlfill.
  eapply val_head_stuck_reduce.
  apply r_simple. eapply rs_br;eauto.
  Unshelve. done. apply (Build_store_record [] [] [] []).
  apply (Build_frame [] (Build_instance [] [] [] [] [])).
Qed.

Lemma to_val_immV_label_None es v m ctx :
  iris.to_val es = Some (immV v) ->
  iris.to_val [AI_label m ctx es] = None.
Proof.
  intros Hes.
  eapply val_head_stuck_reduce.
  eapply r_simple, rs_label_const. eapply to_val_const_list;eauto.
  Unshelve. done. apply (Build_store_record [] [] [] []).
  apply (Build_frame [] (Build_instance [] [] [] [] [])).
Qed.  
  
Lemma to_val_trapV_label_None es m ctx :
  iris.to_val es = Some trapV ->
  iris.to_val [AI_label m ctx es] = None.
Proof.
  intros Hes.
  apply to_val_trap_is_singleton in Hes as ->.
  eapply val_head_stuck_reduce.
  eapply r_simple, rs_label_trap.
  Unshelve. done. apply (Build_store_record [] [] [] []).
  apply (Build_frame [] (Build_instance [] [] [] [] [])).
Qed.

Lemma to_val_cons_immV v l :
  iris.to_val (AI_basic (BI_const v) :: iris.of_val (immV l)) = Some (immV (v :: l)).
Proof.
  rewrite separate1.
  erewrite to_val_cat_inv;eauto.
  2: apply to_of_val.
  auto.
Qed.
Lemma to_val_cons_brV i (lh : valid_holed i) v es :
  iris.to_val es = Some (brV lh) ->
  iris.to_val (AI_basic (BI_const v) :: es) = Some (brV (vh_push_const lh [v])).
Proof.
  intros Hes.
  unfold to_val,iris.to_val. cbn.
  unfold to_val,iris.to_val in Hes.
  destruct (merge_values_list (map to_val_instr es)) eqn:Hsome;[|done].
  simplify_eq.
  unfold merge_values_list in Hsome.
  destruct (map to_val_instr es) eqn:Hmap;try done.
  destruct v0;try done.
  rewrite merge_prepend. by rewrite /= Hsome.
Qed.
Lemma to_val_cons_retV s v es :
  iris.to_val es = Some (retV s) ->
  iris.to_val (AI_basic (BI_const v) :: es) = Some (retV (sh_push_const s [v])).
Proof.
  intros Hes.
  unfold to_val,iris.to_val. cbn.
  unfold to_val,iris.to_val in Hes.
  destruct (merge_values_list (map to_val_instr es)) eqn:Hsome;[|done].
  simplify_eq.
  unfold merge_values_list in Hsome.
  destruct (map to_val_instr es) eqn:Hmap;try done.
  destruct v0;try done.
  rewrite merge_prepend. by rewrite /= Hsome.
Qed.
Lemma to_val_cons_None es v :
  iris.to_val es = None ->
  iris.to_val (AI_basic (BI_const v) :: es) = None.
Proof.
  intros Hes.
  rewrite separate1.
  apply to_val_cat_None2;auto.
Qed.
  
Lemma to_val_AI_trap_Some_nil es vs :
    iris.to_val ([AI_trap] ++ es) = Some vs -> es = [].
  Proof.
    destruct es =>//.
    intros Hes;exfalso.
    assert (iris.to_val ([AI_trap] ++ (a :: es)) = None).
    { rewrite -(app_nil_l [AI_trap]).
      rewrite -app_assoc.
      apply to_val_not_trap_interweave;auto. }
    congruence.
  Qed.

  Lemma to_val_None_label n es' LI :
    iris.to_val LI = None ->
    iris.to_val [AI_label n es' LI] = None.
  Proof.
    intros HLI.
    unfold iris.to_val. cbn. 
    unfold iris.to_val in HLI.
    destruct (merge_values_list (map to_val_instr LI)) eqn:Hmerge;done.
  Qed.    

Lemma trap_context_reduce hs locs s LI lh k :
  lfilled (S k) lh [AI_trap] LI ->
  ∃ e', reduce hs locs s LI hs locs s e'.
Proof.
  revert LI lh.
  induction k;intros LI lh Hfill%lfilled_Ind_Equivalent.
  { inversion Hfill;simplify_eq. inversion H1;simplify_eq.
    destruct (decide (vs0 ++ [AI_trap] ++ es'0 = [AI_trap])).
    { destruct vs0,es'0 =>//.
      2: destruct vs0 =>//.
      2: destruct vs0,es'0 =>//.
      erewrite app_nil_l, app_nil_r.
      exists (vs ++ [AI_trap] ++ es'').
      eapply r_label.
      2: instantiate (3:=0).
      2,3: apply lfilled_Ind_Equivalent;constructor;auto.
      apply r_simple. apply rs_label_trap. }
    { exists (vs ++ [AI_label n es' ([AI_trap])] ++ es'').
      eapply r_label.
      2: instantiate (3:=1).
      2,3: apply lfilled_Ind_Equivalent;constructor;auto.
      2: instantiate (2:=LH_base [] []).
      2,3: apply lfilled_Ind_Equivalent.
      2,3: cbn;rewrite app_nil_r; by apply/eqseqP.
      apply r_simple. eapply rs_trap. auto.
      apply lfilled_Ind_Equivalent. eauto.
    }
  }
  { inversion Hfill;simplify_eq.
    apply lfilled_Ind_Equivalent in H1.
    eapply IHk in H1 as Hred.
    destruct Hred as [e' Hred].
    eexists.
    eapply r_label;[eauto|..].
    instantiate (2:=1).
    all: apply lfilled_Ind_Equivalent;constructor;auto.
    all: apply lfilled_Ind_Equivalent.
    instantiate (1:=LH_base [] []).
    all: cbn;rewrite app_nil_r;by apply/eqseqP.
  }
Qed.

Lemma to_val_trapV_lfilled_None es k lh LI :
  iris.to_val es = Some trapV ->
  lfilled (S k) lh es LI ->
  iris.to_val LI = None.
Proof.
  intros Hes Hfill.
  apply to_val_trap_is_singleton in Hes as ->.
  eapply trap_context_reduce in Hfill as [e' Hred].
  eapply val_head_stuck_reduce;eauto.
  Unshelve.
  done.
  apply (Build_store_record [] [] [] []).
  apply (Build_frame [] (Build_instance [] [] [] [] [])).
Qed.

Lemma lfilled_to_val_0 i lh e es v :
  iris.to_val e = Some trapV ->
  lfilled i lh e es ->
  iris.to_val es = Some v ->
  i = 0.
Proof.
  intros He Hfill Hes.
  destruct i;auto.
  exfalso.
  apply to_val_trapV_lfilled_None in Hfill;auto.
  unfold to_val in Hfill.
  congruence.
Qed.

Lemma to_val_None_lfilled LI k lh es :
  iris.to_val es = None → lfilled k lh es LI -> iris.to_val LI = None.
Proof.
  revert LI lh es;induction k;intros LI lh es Hnone Hfill%lfilled_Ind_Equivalent.
  { inversion Hfill;simplify_eq.
    apply to_val_cat_None2;auto.
    apply to_val_cat_None1;auto. }
  { inversion Hfill;simplify_eq.
    apply lfilled_Ind_Equivalent in H1.
    apply IHk in H1;auto.
    apply to_val_cat_None2;auto.
    apply to_val_cat_None1;auto.
    apply to_val_None_label. auto.
  }
Qed.
    
  
End iris_properties.