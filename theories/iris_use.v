(** Example of Iris usage **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity iris_wp_def stdpp_aux.
Require Export iris_rules.
Require Export datatypes host operations properties opsem.
Require Import Coq.Program.Equality.

Import uPred.

Set Default Proof Using "Type". (* what is this? *)

Close Scope byte_scope.

Let expr := iris.expr.
Let val := iris.val.
Let to_val := iris.to_val.


Section Host.

Import DummyHosts.
  
Let reduce := @reduce host_function host_instance.


Canonical Structure wasm_lang := Language wasm_mixin.
 
Let reducible := @reducible wasm_lang.

(* wp for instructions *)

Section lifting.


(*
(* This requires inverting wp again........ It would be really amazing
   if we can actually prove this, since I can't find anywhere in Iris where
   this has been done. *)
Lemma wp_trap_lfilled (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (es : language.expr wasm_lang) (lh: lholed):
  lfilled 0 lh [AI_trap] es ->
  WP es @ s; E {{ v, Φ v }} ⊢
  |={E}=> Φ trapV.
Proof.
  move => Hlf.
  iIntros "H".
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  move/lfilledP in Hlf.
  inversion Hlf; subst; clear Hlf.
  (* if both vs and es' are empty then we're good: wp_value is directly applicable. *)
  destruct (iris.to_val (vs ++ [AI_trap] ++ es')) as [v|] eqn:Hetov.
  {
    destruct v.
    (* actual value, which is impossible *)
    {
      apply to_val_cat in Hetov as [Hvs He].
      apply to_val_cat in He as [Het He'].
      simpl in Het.
      by inversion He'.
    }
    (* trapV *)
    {
      apply iris.of_to_val in Hetov.
      simpl in Hetov.
      destruct vs; by [destruct es' | destruct vs].
    }
  }
  rewrite Hetov.
  (* We now need to feed an explicit configuration and state to the premise. *)
Admitted.

Lemma wp_seq_trap (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
  (WP es1 @ s; E {{ w, ⌜ w = trapV ⌝ }} ∗
  WP ([AI_trap] ++ es2) @ s; E {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v }}.
Proof.
  iIntros "(Hes1 & Hes2)".
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val (es1 ++ es2)) as [vs|] eqn:Hetov.
  {
    destruct vs.
    {
      apply to_val_cat in Hetov as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      by iMod "Hes1" as "%Hes1".
    }
    {
      apply to_val_trap_is_singleton in Hetov.
      apply app_eq_singleton in Hetov as [[-> ->]|[-> ->]] => //.
      iMod "Hes1" => //.
      by iDestruct "Hes1" as "%Hes1".
    }
  }
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1" as "->".
    destruct es2 => //.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "Hσ").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "Hσ").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      by apply append_reducible.
    - iIntros (e2 σ2 efs HStep).
      apply prim_step_split_reduce_r_correct in HStep; last by [].
      destruct HStep as [[es'' [-> HStep]] | [n [m [Hlf [-> HStep]]]]].
      + iSpecialize ("H2" $! es'' σ2 efs HStep).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iModIntro.
        destruct σ2 as [[??] ?].
        iDestruct "H2" as "(Hσ & Hes'' & Hefs)".
        iFrame.
Admitted.
*)

(* Knowing hypothesis "Hred : objs -> _" (with frames (locs, inst) and (locs', inst')),
   attempts to exfalso away most of the possible ways Hred could hold, leaving the user
   with only the one possible desired case. Tactic will also attempt to trivially solve
   this one case, but may give it to user if attempt fails. *)

(*
Ltac only_one_reduction Hred objs locs inst locs' inst' :=
  let a := fresh "a" in
  let aft := fresh "aft" in
  let bef := fresh "bef" in
  let e := fresh "e" in
  let e' := fresh "e'" in
  let es := fresh "es" in
  let es0 := fresh "es" in
  let es1 := fresh "es" in
  let es2 := fresh "es" in
  let f := fresh "f" in
  let f' := fresh "f" in
  let g := fresh "g" in
  let hs := fresh "hs" in
  let hs' := fresh "hs" in
  let H := fresh "H" in
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  let Hconst := fresh "Hconst" in
  let Heqes0 := fresh "Heqes" in
  let Heqes2 := fresh "Heqes" in
  let Heqg := fresh "Heqg" in
  let Ht1s := fresh "Ht1s" in
  let Ht2s := fresh "Ht2s" in
  let Hvs := fresh "Hvs" in
  let Hxl1 := fresh "Hxl1" in
  let IHreduce := fresh "IHreduce" in
  let k := fresh "k" in
  let l := fresh "l" in
  let l' := fresh "l" in
  let les := fresh "les" in
  let les' := fresh "les" in
  let lh := fresh "lh" in
  let m := fresh "m" in
  let n0 := fresh "n" in
  let n' := fresh "n" in
  let s := fresh "s" in
  let t1s := fresh "t1s" in
  let t2s := fresh "t2s" in
  let vs := fresh "vs" in
  remember objs as es0 eqn:Heqes0 ;
  remember {| f_locs := locs ; f_inst := inst |} as f eqn:Heqf ;
  remember {| f_locs := locs' ; f_inst := inst' |} as f' eqn:Heqf' ;
  apply Logic.eq_sym in Heqes0 ;
  induction Hred as [e e' s ? hs H | | | | | a | a | a | | | | | | | | | | | | | | | |
                      s ? es les s' f' es' les' k lh hs hs' Hred IHreduce H0 H1 | ];
  (* induction on the reduction. Most cases will be trivially solved by the following
     two attemps : *)
  (try by inversion Heqes0) ;
  (try by found_intruse (AI_invoke a) Heqes0 Hxl1) ;
  (* reduce_simple case : *)
  first (destruct H as [ | | | | | | | | | | | | | | 
                    vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                    vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                  | | | | | | | | | | | | | 
                         es' lh Htrap' H0 ]  ;
         (* by case_analysis on the reduce_simple. most cases solved by just the 
            following inversion ; some cases need a little extra help *)
         inversion Heqes0 as [[ Hhd ]] ; subst ;
         (try by found_intruse (AI_basic (BI_block (Tf t1s t2s) es)) Hhd Hxl1) ;
         (try by found_intruse (AI_basic (BI_loop (Tf t1s t2s) es)) Hhd Hxl1) ;
         (try by filled_trap H0 Hxl1) ) ;
  (* lfilled case *)
  last (rewrite <- Heqes0 in H0 ;
        (* the simple_filled tactic unfolds lfilled, solves the case where k>0,
           and in the case k=0 leaves user with hypothesis H0 modified to now be
           les = bef ++ es ++ aft *)
        simple_filled2 H0 k lh bef aft n0 l l' ;
        first
          ( apply Logic.eq_sym in H0 ;
            remember ([] : seq.seq administrative_instruction) as g eqn:Heqg in s;
            let rec auxb H0 :=
              (* We maintain as an invariant that when auxb H0 is called,
                 H0 is the hypothesis "H0 : bef ++ es ++ aft = [some explicit sequence]" *)
              ( let b0 := fresh "b" in
                let Hb0 := fresh "Hb" in
                let H2 := fresh "H" in
                destruct bef as [| b0 bef ] ;
                [ (* case bef = []. Our invariant gives us that
                     "H0 : es ++ aft = [some explicit sequence]".
                     Recall g was defined as [] with "Heqg : g = []". *)
                  let rec auxe H0 g Heqg :=
                    (* We maintain as an invariant than when auxe H0 g Heqg is called,
                       H0 is the hypothesis "H0 : es ++ aft = [some explicit sequence]",
                       Hred is the hypothesis "Hred : (g ++ es) -> es'",
                       and Heqg is "Heqg : g = [some (other) explicit sequence]" *)
                    ( let e0 := fresh "e" in
                      let g' := fresh "g" in
                      let He0 := fresh "He" in
                      let Heqg' := fresh "Heqg" in
                      let H2 := fresh "H" in
                      destruct es as [| e0 es] ;
                      [ (* case es = []. Our invariants give us that
                           "Hred : g -> es' " with g described explicitly in Heqg.
                           Thus to conclude, we can … *)
                        rewrite <- Heqg in Hred ;
                        remember g as es2 eqn:Heqes2 in Hred ;
                        apply Logic.eq_sym in Heqes2 ;
                        rewrite Heqg in Heqes2 ;
                        (* use our induction hypothesis 
                           (case where bef = aft = []), or …  *)
                        (( by simpl in H0 ; rewrite H0 in H1 ;
                           unfold lfilled, lfill in H1 ;
                           destruct (const_list []) ; [| false_assumption] ;
                           apply b2p in H1 ; rewrite H1 ; rewrite app_nil_r ;
                           apply IHreduce ; subst ; trivial) +
                           (* use no_reduce (case where bef or aft is nonempty, and thus
                              g is shorter than the original objs). Strict subsequences
                              of valid reduction sequences tend to not reduce, so this
                              will work most of the time *)
                           (exfalso ; no_reduce Heqes2 Hred) )
                      | (* case es = e0 :: es. Our invariant gives us that
                           "H0 : e0 :: es ++ aft = [some explicit sequence]". We can
                           try to conclude by inverting H0, in case the explicit sentence is
                           empty *)
                        (by inversion H0) +
                          (* else, we know the explicit sentence is nonempty. 
                             Now by inverting H0 we get 
                             "H2 : es ++ aft = [some shorter explicit sequence]"
                             The invariant also gives us
                             "Hred : (g ++ e0 :: es) -> es'", so to maintain the invariant  
                             we define g' to be g ++ [e0] and create an equation Heqg' that
                             describes g' explicitly *)
                          ( inversion H0 as [[ He0 H2 ]] ;
                            rewrite He0 in Hred ;
                            remember (g ++ [e0]) as g' eqn:Heqg' ;
                            rewrite Heqg in Heqg' ;
                            rewrite He0 in Heqg' ;
                            simpl in Heqg' ;
                            (* we can now make a recursive call to auxe. The length of the
                               explicit list in H2 has strictly decreased *)
                            auxe H2 g' Heqg'
                          )
                      ]
                    ) in auxe H0 g Heqg
                | (* case bef = b0 :: bef. Our invariant gives us that
                     "H0 : b0 :: bef ++ es ++ aft = [some explicit sequence]".
                     We can attempt to conclude by inverting H0, which will work if
                     the explicit sequence is empty *)
                  (by inversion H0 ) +
                    (* else, we know the explicit sequence is nonempty, so by inverting
                       H0, we get "H2 : bef ++ es ++ aft = [some explicit sequence]" *)
                    ( inversion H0 as [[ Hb0 H2 ]] ;
                      auxb H2 )
                ]
              ) in auxb H0
          )
       ) ;        
  (* at this point, only one case should be remaining.
     we attempt to solve this case too trivially, as the following line is often
     what user would be going to do next anyway *)
  try by inversion Heqes0 ; subst ; inversion Heqf' ; subst ; iFrame.
*)

(* An attempt at making reduce_det a proved lemma. Work in progress

Lemma reduce_det: forall hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2,
  reduce hs f ws es hs1 f1 ws1 es1 ->
  reduce hs f ws es hs2 f2 ws2 es2 ->
  ( In (AI_basic BI_grow_memory) es -> False ) ->
  ( forall a, In (AI_invoke a) es -> False) -> 
  (hs1, f1, ws1, es1) = (hs2, f2, ws2, es2).
Proof.
  intros hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2 Hred1 Hred2 Hgrow_memory Hinvoke.
  destruct es as [ | e0 es ].
  { empty_list_no_reduce Hred1. }
  destruct es as [ | e1 es ].
  { remember [e0] as es.
    apply Logic.eq_sym in Heqes.
    destruct e0.
    destruct b ; try by exfalso ; no_reduce Heqes Hred1. *)

(* Control flows *)

            
 (*| rs_return :
      forall n i vs es lh f,
        const_list vs ->
        length vs = n ->
        lfilled i lh (vs ++ [::AI_basic BI_return]) es ->
        reduce_simple [::AI_local n f es] vs*)
(* return is a contextual rule, but it is also a function rule. Before we tackle with wp, 
   we must have set up the way in which to handle AI_local. 
   intuitively, AI_local functions as a fresh bind, in a fresh ctx, very similar to wp_seq_ctx 
   solution idea: another WP now that can abstract away the AI_local "wrapper", using AI_local 
   instead of AI_label. Note that AI_label and contexts can still occur within an AI_local....
   Main difference is that AI_local is not nested in the same way as label, in which label 
   knows about the nesting structure for br, whereas local "stops" br from exiting.

   Why is there a need for a new WP? because there can be a nested label structure inside a 
   label, and we need to have knowledge of that for the return instruction. The label wrapper
   is always the outermost layer! so current ctxWP does not work for that reason.
*)
(* Frame rules attempt *)


(*
Lemma AI_local_reduce_frame_indep hs ws f0 n f es hs' ws' f0' es0' f1:
  reduce hs ws f0 [AI_local n f es] hs' ws' f0' es0' ->
  reduce hs ws f1 [AI_local n f es] hs' ws' f1 es0'.
Proof.
Admitted.

Lemma AI_local_reduce_frame_const hs ws f0 n f es hs' ws' f0' es0':
  reduce hs ws f0 [AI_local n f es] hs' ws' f0' es0' ->
  f0 = f0'.
Proof.
Admitted.
*)

(* This is not true (corner cases), but assumed for convenience temporarily. It
   is almost the same as the prim_step_split lemma.
   TODO: change to use the prim_step_split lemma instead.
 *)


(* This is provable, of course. But how can we deal with recursive functions
   by this and the above? *)
Lemma wp_invoke_native E vcs ves finst ts1 ts2 ts es a Φ m f0:
  iris.to_val ves = Some (immV vcs) ->
  length vcs = length ts1 ->
  length ts2 = m ->
  ↪[frame] f0 -∗
  (↪[frame] f0 -∗ WP ([AI_basic (BI_block (Tf [] ts2) es)]) @ NotStuck; E FRAME m; (Build_frame (vcs ++ n_zeros ts) finst) {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
  (N.of_nat a) ↦[wf] (FC_func_native finst (Tf ts1 ts2) ts es) -∗
  WP (ves ++ [AI_invoke a]) @ NotStuck; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  move => Htoval Harglen Hretlen.
  iIntros "Hf0 Hwp Hfunc".
  iApply wp_lift_step; first by apply to_val_cat_None2.
  
  iIntros (σ n κ κs nt) "Hσ".
  destruct σ as [[[hs ws] locs] inst].
  iDestruct "Hσ" as "(Hf & Ht & Hm & Hg & Hframe & Hmemlen)".
  iDestruct (gen_heap_valid with "Hf Hfunc") as "%Hfunc".
  rewrite gmap_of_list_lookup Nat2N.id in Hfunc.
  rewrite - nth_error_lookup in Hfunc.
          
  assert (reduce hs ws {|f_locs := locs; f_inst := inst|} (ves ++ [AI_invoke a]) hs ws {|f_locs := locs; f_inst := inst|} ([AI_local m (Build_frame (vcs ++ n_zeros ts) finst) [AI_basic (BI_block (Tf [] ts2) es)]])) as Hred.
  {
    eapply r_invoke_native; first by apply Hfunc.
    all: try by eauto.
    apply iris.of_to_val in Htoval.
    subst.
    by elim vcs.
  }
  
  iApply fupd_mask_intro; first by solve_ndisj.
  iIntros "Hmask".
  iSplit.
  (* reducibility *)
  - iPureIntro.
    exists [].
    eexists.
    exists (hs, ws, locs, inst), [].
    simpl.
    by repeat split => //.
    
  - iIntros (es' σ' efs HStep).
    destruct σ' as [[[hs' ws'] locs'] inst'].

    iModIntro.
    iMod "Hmask".
    iModIntro.
    iSimpl.

    inversion HStep as [Hred' [-> ->]].
    (* Wait, we do not have reduce_det for invoke; but it ought to be true... *)
    admit.
    (*eapply reduce_det in Hred => //.
    inversion Hred; subst; clear Hred.

    iExists f0.
    
    by iFrame.*)
Admitted.
(*
(*
  The sequence rule for AI_local, like wp_seq_ctx for AI_label.
  However, this is much more complicated:
  - we're not remembering the entire call stack in the WP assertion, so there's
    some deduction required;
  - resources for the frame need to be create in-place for the instructions
    inside the frame. This needs to be done in a similar fashion as
    gen_heap_alloc.
*)
Lemma wp_frame_seq (s: stuckness) (E: coPset) (Φ Ψ: val -> iProp Σ) (es1 es2: language.expr wasm_lang) (wf wf': frame) (n: nat) (P: iProp Σ) (cs: list frame):
  length wf.(f_locs) = length wf'.(f_locs) ->
  ((¬ Ψ trapV) ∗
    ((P ∗ stack_interp (rcons cs wf)) -∗
     WP es1 @ NotStuck; E {{ w, Ψ w ∗ stack_interp (rcons cs wf') }}) ∗
  (∀ w, (Ψ w ∗ stack_interp cs) -∗ WP (iris.of_val w ++ es2) @ s; E FRAME n; wf' {{ v, Φ v ∗ stack_interp cs }})
  ⊢ (P ∗ stack_interp cs) -∗ WP es1 ++ es2 @ s; E FRAME n; wf {{ v, Φ v ∗ stack_interp cs }})%I.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ wf wf' n P cs).
  iIntros (Hflen) "(Hntrap & Hes1 & Hes2)".
  iIntros "(HP & Hcs)".
  unfold wp_return_frame.
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  iIntros (σ ns κ κs nt) "hσ".
  iApply fupd_mask_intro; first by solve_ndisj.
  iIntros "hmask".
  iSplit.
  { (* reducibility *)admit. }
  iIntros (es' σ' efs HStep).
  destruct σ as [[[hs ws] locs] inst].
  destruct σ' as [[[hs' ws'] locs'] inst'].
  iDestruct "Hσ" as "(Hf & Ht & Hm & Hg & Hcsi & Hγ)".
  iDestruct "Hcsi" as (cs0) "(Hcs0 & %Hstack)".
  iMod (gen_heap_update with "Hcs0 Hli") as "(Hl & Hli)".
Admitted.

Definition xx i := (VAL_int32 (Wasm_int.int_of_Z i32m i)).
Definition xb b := (VAL_int32 (wasm_bool b)).

Definition my_add : expr :=
  [AI_basic (BI_const (xx 3));
     AI_basic (BI_const (xx 2));
  AI_basic (BI_binop T_i32 (Binop_i BOI_add))].

Lemma frame_ex1 f f0 s E:
  frame_interp f ⊢ WP [AI_local 1 f0 (my_add ++ [AI_basic BI_return])] @ s; E {{ v, ⌜ v = immV [xx 5] ⌝ ∗ frame_interp f }}.
Proof.
  iIntros "Hf".
  iApply wp_frame_rewrite.
  iApply wp_frame_seq => //.
  instantiate (1 := fun x => (⌜ x = immV [xx 5] ⌝)%I).
  instantiate (1 := (emp)%I).
  2: { by iFrame. }
  iSplit; first trivial.
  iSplitL.
  - iIntros "[_ H]".
    iApply wp_wand.
    instantiate (1 := fun x => (⌜ x = immV [xx 5] ⌝)%I); first by iApply wp_binop.
    iSimpl.
    iIntros (v Hv).
    subst.
    by iFrame.
  - iIntros (w) "[%Hw Hf]".
    subst.
    iApply wp_frame_return; last by iFrame; eauto.
    + by instantiate (1 := [AI_basic (BI_const (xx 5))]).
    + trivial.
    + instantiate (1 := LH_base [::] [::]).
      instantiate (1 := 0).
      by unfold lfilled, lfill => /=.
Qed.
*)
                      
(*
Definition frame_push_local (ls: lstack) n f := rcons ls (n, f, 0, LH_base [::] [::]).
 *)
(*
Fixpoint inner_frame (ls: lstack) : option frame :=
  match ls with
  | [::] => None
  | [::(n, f, k, lh)] => Some f
  | cf :: cs => inner_frame cs
  end.

Fixpoint update_inner_frame (ls: lstack) (f: frame) : option lstack :=
  match ls with
  | [::] => None
  | [::(n, f', k, lh)] => Some [::(n, f, k, lh)]
  | cf :: cs => match update_inner_frame cs f with
              | Some ls' => Some (cf :: ls')
              | None => None
              end
  end.
*)


(* 
  The main difference here is that, changes in frames (AI_local) have impact on the local variables from the aspect of the internal expression, which are part of the state -- while pushing a label has no such impact. 

  We need to somehow account for this whenever we enter or leave a call frame. In particular, in both the 2nd and the 3rd premises, we need to give them resources of the locals and current instance -- whatever they produce, the corresponding modification needs to be made to the frame stored in the lstack construct. In some sense we're providing a wrapper for the internal instructions to execute.
 *)

(* Firstly, we could enter a local frame by temporarily forget about the current frame and construct the new frame 
   resources in place. 

   We ensure that no frame resources from inside is leaked to the outer frame by forcing the inner frame information 
   to be separated by (frame_interp f'); the requirement that f' has the same number of locals guarantee that no local
   variable inside the frame could escape from the frame.
   

 *)
(*
Lemma wp_frame_push_local (s: stuckness) (E: coPset) (Φ: val -> iProp Σ) n f n0 f0 es:
  (*  length f.(f_locs) = length f'.(f_locs) -> *)
  WP es @ NotStuck; E FRAME n ; f {{ v, Φ v }} ⊢
  WP [AI_local n f es] @ s; E FRAME n0 ; f0 {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es Φ n f n0 f0).
  iIntros "Hwp".
  unfold wp_return_frame.
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  iIntros (σ ????) "Hσ".
  destruct σ as [[[hs ws] locs] inst].
  iApply fupd_mask_intro; first by solve_ndisj.
  iIntros "Hmask".
  iSplit.
  { destruct s => //=.
    iSpecialize ("Hwp" $! (hs, ws, locs, inst) ns κ κs nt with "Hσ").
    iPureIntro.
    econstructor.
    eexists.
    (* This will not work, instead it's just for observation. *)
    exists (hs, ws, locs, inst), [].
    unfold language.prim_step => /=.
    repeat split => //.
    apply r_local.
    admit.
  }
Admitted.
*)

(* basic instructions with non-simple(non-pure) reductions *)

(* Function related *)

Lemma wp_call: False.
Proof.
Admitted.

Lemma wp_call_indirect: False.
Proof.
Admitted.



(* former version of wp_grow_memory, asserts knowledge of whole memory *)
(*
Lemma wp_grow_memory (s: stuckness) (E: coPset) (k: nat) (f0: frame) (mem: memory) (Φ Ψ: val -> iProp Σ) (c: i32) :
  f0.(f_inst).(inst_memory) !! 0 = Some k ->
  match mem_max_opt mem with
  | Some maxlim => (mem_size mem + (Wasm_int.N_of_uint i32m c) <=? maxlim)%N
  | None => true
  end ->
  ( ↪[frame] f0 ∗
  Φ (immV [VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))]) ∗
  (Ψ (immV [VAL_int32 int32_minus_one])) ∗
     (N.of_nat k) ↦[wmblock] mem ) ⊢ WP ([AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_grow_memory)]) @ s; E {{ w, ((Φ w ∗ (N.of_nat k) ↦[wmblock] {| mem_data:= {| ml_init := ml_init mem.(mem_data); ml_data := ml_data mem.(mem_data) ++ repeat (#00)%byte (N.to_nat ((Wasm_int.N_of_uint i32m c) * page_size)) |}; mem_max_opt:= mem_max_opt mem |}) ∨ (Ψ w ∗ (N.of_nat k) ↦[wmblock] mem)) ∗ ↪[frame] f0  }}.
Proof.
  iIntros (Hfm Hmsizelim) "(Hframe & HΦ & HΨ & Hmemblock)".
  iDestruct "Hmemblock" as "(Hmemdata & Hmemlength)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & Hm & ? & Hf & Hγ)".
  iDestruct (ghost_map_lookup with "Hf Hframe") as "%Hframe".
  iDestruct (gen_heap_valid with "Hγ Hmemlength") as "%Hmemlength".
  rewrite lookup_insert in Hframe.
  inversion Hframe; subst; clear Hframe.
  rewrite - nth_error_lookup in Hfm.
  rewrite gmap_of_list_lookup list_lookup_fmap Nat2N.id in Hmemlength => /=.
  destruct (s_mems ws !! k) eqn:Hmemlookup => //.
  simpl in Hmemlength.
  inversion Hmemlength as [Hmemlength']; clear Hmemlength.
  iAssert ( (∀ i, ⌜(ml_data (mem_data mem)) !! i = (ml_data (mem_data m)) !! i ⌝)%I) as "%Hmeq".
  {
    iIntros (i).
    destruct (ml_data (mem_data mem) !! i) eqn:Hmd.
    - iDestruct (big_sepL_lookup with "Hmemdata") as "H" => //.
      iDestruct (gen_heap_valid with "Hm H") as "%H".
      rewrite gmap_of_list_2d_lookup list_lookup_fmap Nat2N.id Hmemlookup in H.
      unfold memory_to_list in H.
      simpl in H.
      by rewrite Nat2N.id in H.
    - apply lookup_ge_None in Hmd.
      iPureIntro.
      symmetry.
      apply lookup_ge_None.
      unfold mem_length, memory_list.mem_length in Hmemlength'.
      lia.
  }
  iAssert (⌜mem ≡ₘm⌝%I) as "%Hmem".
  {
    unfold mem_block_equiv.
    by rewrite (list_eq (ml_data (mem_data mem)) (ml_data (mem_data m))).
  }
  iSplit.
  assert (exists mem', mem_grow mem (Wasm_int.N_of_uint i32m c) = Some mem') as [mem' Hmem'].
  { unfold mem_grow.
    destruct (mem_max_opt mem) eqn:Hmaxsize; eexists => //.
    by rewrite Hmsizelim.
  }
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    admit.
    (*
    exists [], [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))))], (hs, (upd_s_mem ws (update_list_at (s_mems ws) k mem')), locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_grow_memory_success => //.
    rewrite - nth_error_lookup in Hmemlookup.
    rewrite Hmemlookup.
    f_equal.
  (* There's a small bug in memory_list: mem_grow should not be using ml_init but #00 instead. Finish this when that is fixed *)
    admit.*)
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    (* DO NOT USE reduce_det here -- grow_memory is NOT determinstic. *)
    iExists {| f_locs := locs; f_inst := winst |}.
    eapply reduce_grow_memory in H; [ idtac | by rewrite - nth_error_lookup | by rewrite nth_error_lookup ].
    (*
    destruct H as [HReduce | [HReduce Hmem']]; inversion HReduce; subst; clear HReduce; iFrame.
    (* failure *)
    + iSplit => //.
      iRight.
      iFrame.
      by rewrite Hmemlength'.
    (* success *)
    + admit.
*)
Admitted. *)




End lifting.

(* What should a function spec look like?
  A (Wasm) function closure is of the form

    FC_func_native inst ft vts bes

  but this is not an expression nor a value, so we need to define our custom version of wp for it, like

    ▷ WP (FC_func_native inst ft vts bes) {{ v, Φ v }}.

    ( Would WP bes {{ ... }} be enough? )

  to express our function specs.

  What should such a wp require (to be established), and how to use it? 

  Given a spec in the above form, we expect to be able to use it to
    figure out a spec for Invoke i, when s.funcs[i] is a Wasm function...
 
  s.funcs[a] = FC_func_native i (Tf t1s t2s) ts bes ->
  f' = {| inst := i; locs := vcs ++ zs |} ->
  ... ->
  (hs, s, f, ves ++ [AI_invoke a]) ↪ 
  (hs, s, f, [AI_local m f' [AI_basic (BI_block (Tf [] t2s) bes)]])

Lemma invoke_native_spec `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ, !wlocsG Σ} (s : stuckness) (E : coPset) (Φs: list (val -> iProp Σ)) inst ft vts bes :
  [∗ list] i ↦ Φ ∈ Φs, (i ↦[wf] FC_func_native inst ft vts bes ∗ □ (WP (FC_func_native inst ft vts bes)
*)

End Host.

Local Hint Resolve language.val_irreducible : core.
Local Hint Resolve to_of_val : core.
Local Hint Unfold language.irreducible : core.

