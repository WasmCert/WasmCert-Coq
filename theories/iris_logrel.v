From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules.
Require Export datatypes host operations properties opsem typing.
Import uPred.

(* functor needed for NA invariants *)
Class logrel_na_invs Σ :=
  {
    logrel_na_invG :> na_invG Σ;
    logrel_nais : na_inv_pool_name;
  }.

Definition wf : string := "wfN".
Definition wt : string := "wtN".
Definition wm : string := "wmN".
Definition wg : string := "wgN".
Definition wfN (a : N) : namespace := nroot .@ wf .@ a.
Definition wtN (a b: N) : namespace := nroot .@ wt .@ a .@ b.
Definition wmN (a: N) : namespace := nroot .@ wm .@ a.
Definition wgN (a: N) : namespace := nroot .@ wg .@ a.


Close Scope byte_scope.

(* Example Programs *)
Section logrel.
  
  Import DummyHosts. (* placeholder *)

  Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.

  
  Definition xb b := (VAL_int32 (wasm_bool b)).

  Let expr := iris.expr.
  Let val := iris.val.



  Notation VR := ((leibnizO val) -n> iPropO Σ).
  Notation WR := ((leibnizO value) -n> iPropO Σ).
  Notation FR := ((leibnizO frame) -n> iPropO Σ).
  Notation FfR := ((leibnizO N) -n> iPropO Σ).
  Notation ClR := ((leibnizO function_closure) -n> iPropO Σ).
  Notation CtxR := ((leibnizO lholed) -n> iPropO Σ).
  Notation TR := ((leibnizO N) -n> iPropO Σ).
  Notation TeR := ((leibnizO N) -n> (leibnizO N) -n> iPropO Σ).
  Notation MR := ((leibnizO N) -n> iPropO Σ).
  Notation GR := ((leibnizO N) -n> iPropO Σ).
  Notation IR := ((leibnizO instance) -n> iPropO Σ).

  Implicit Types w : (leibnizO value).
  Implicit Types ws : (list (leibnizO value)).
  Implicit Types v : (leibnizO val).
  Implicit Types f : (leibnizO frame).
  Implicit Types cl : (leibnizO function_closure).
  Implicit Types lh : (leibnizO lholed).
  Implicit Types n m : (leibnizO N).
  Implicit Types g : (leibnizO global).
  Implicit Types i : (leibnizO instance).

  Implicit Types τ : value_type.
  Implicit Types τs : result_type.
  Implicit Types ηs : result_type.
  Implicit Types τf : function_type.
  Implicit Types τc : list (list value_type).
  Implicit Types τt : table_type.
  Implicit Types τm : memory_type.
  Implicit Types τg : global_type.
  Implicit Types τctx : t_context.

  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- VALUE RELATION ------------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)


  Definition interp_value_i32 : WR := λne w, ⌜∃ z, w = VAL_int32 z⌝%I.
  Definition interp_value_i64 : WR := λne w, ⌜∃ z, w = VAL_int64 z⌝%I.
  Definition interp_value_f32 : WR := λne w, ⌜∃ z, w = VAL_float32 z⌝%I.
  Definition interp_value_f64 : WR := λne w, ⌜∃ z, w = VAL_float64 z⌝%I.

   Definition interp_value (τ : value_type) : WR :=
    match τ return _ with
    | T_i32 => interp_value_i32
    | T_i64 => interp_value_i64
    | T_f32 => interp_value_f32
    | T_f64 => interp_value_f64
    end.

  Definition interp_values (τs : result_type) : VR :=
    λne v, (∃ ws, ⌜v = immV ws⌝ ∗ [∗ list] w;τ ∈ ws;τs, interp_value τ w)%I.
  Definition interp_val (τs : result_type) : VR :=
    λne v, ((⌜v = trapV⌝) ∨ interp_values τs v)%I.

  
  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------------- CLOSURE RELATION ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* Note: here we assume that the function table does not mutate *)
  (* this is fine for a simple host with no reentrancy, but is not *)
  (* powerful enough to prove examples such as Landin's Knot *)

  Definition interp_closure_native i tf1s tf2s tlocs e : iProp Σ :=
    □ ∀ vcs, interp_val tf1s (immV vcs) -∗
             na_own logrel_nais ⊤ -∗
             ∀ f1, ∃ f2, ↪[frame] f1 -∗ WP e FRAME (length tf2s); (Build_frame (vcs ++ (n_zeros tlocs)) i)
                        CTX 1; LH_rec [] (length tf2s) [] (LH_base [] []) []
                        {{ v, (interp_val tf2s v ∗ na_own logrel_nais ⊤) ∗ ↪[frame] f2 }}.
  
  Definition interp_closure_host tf1s tf2s h : iProp Σ :=
    □ ∀ vcs, interp_val tf1s (immV vcs) -∗
             wp_host HWP NotStuck ⊤ h vcs
                        (λ r, from_option (interp_val tf2s) False (iris.to_val (result_to_stack r))).
  
  Definition interp_closure (τf : function_type) : ClR :=
      λne cl, (match cl with
              | FC_func_native i (Tf tf1s tf2s) tlocs e => ⌜τf = Tf tf1s tf2s⌝ ∗ interp_closure_native i tf1s tf2s tlocs (to_e_list e)
              | FC_func_host (Tf tf1s tf2s) h => ⌜τf = Tf tf1s tf2s⌝ ∗ interp_closure_host tf2s tf2s h
              end)%I.
  
  Definition interp_function (τf : function_type) : FfR :=
    λne n, (∃ (cl : function_closure), na_inv logrel_nais (wfN n) (n ↦[wf] cl)
                                     ∗ interp_closure τf cl)%I.

  
  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- TABLE RELATION ------------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_table_entry (τf : function_type) : TeR :=
    λne n m, (∃ (fe : funcelem), na_inv logrel_nais (wtN n m) (n ↦[wt][m] fe)
                                        ∗ from_option ((interp_function τf) ∘ N.of_nat) True fe)%I.
  (* ⊤ means failure is allowed in case the table is not populated *)

  Definition interp_table (table_size : nat) (τt : table_type) : TR :=
    λne n, ([∗ list] i ∈ mapi (λ j _, j) (repeat 0 table_size), ∃ (τf : function_type), interp_table_entry τf n (N.of_nat i))%I.


  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- MEMORY RELATION ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)
    
  Definition interp_mem (τm : memory_type) : MR :=
    λne n, (na_inv logrel_nais (wmN n) (∃ (mem : memory), n ↦[wmblock] mem ∗ ⌜mem_typing mem τm⌝))%I.
  (* wmblock is shorthand for entire block + size, mem_typing has size restrictions *)

  
  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------------- GLOBALS RELATION ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_global (τg : global_type) : GR :=
    λne n,
      (match (tg_mut τg) with
      | MUT_immut => ∃ (P : value_type -> WR),
         (□ ∀ w, P (tg_t τg) w -∗ interp_value (tg_t τg) w) ∗ 
         na_inv logrel_nais (wgN n) (∃ g, n ↦[wg] g ∗ P (tg_t τg) (g_val g))
      | MUT_mut => na_inv logrel_nais (wgN n) (∃ g, n ↦[wg] g ∗ interp_value (tg_t τg) (g_val g))
      end)%I.


  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- FRAME RELATION ------------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_frame (τs : result_type) (i : instance) : FR :=
    λne f, (∃ vs, ⌜f = Build_frame vs i⌝ ∗ interp_val τs (immV vs))%I.

  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------------- INSTANCE RELATION ----------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_instance (τctx : t_context) : IR :=
    λne i, let '{| inst_types := ts; inst_funcs := fs; inst_tab := tbs; inst_memory := ms; inst_globs := gs; |} := i in
           let '{| tc_types_t := ts'; tc_func_t := tfs; tc_global := tgs; tc_table := tabs_t; tc_memory := mems_t;
                   tc_local := tl; tc_label := tlabel; tc_return := treturn |} := τctx in 
           ((* Type declarations *)
             ⌜ts = ts'⌝ ∗
            (* Function declarations *)
           ([∗ list] f;tf ∈ fs;tfs, interp_function tf (N.of_nat f)) ∗
            (* Function tables *)           
           (match nth_error tabs_t 0 with
            | Some τt => ∃ table_size, ⌜table_size >= N.to_nat τt.(tt_limits).(lim_min)⌝ ∗
                                      from_option ((interp_table table_size τt) ∘ N.of_nat) False (nth_error tbs 0)
            | None => False
            end) ∗
            (* Linear Memory *)
           (match nth_error mems_t 0 with
            | Some τm => from_option ((interp_mem τm) ∘ N.of_nat) False (nth_error ms 0)
            | None => False
            end) ∗
            (* Global declarations *)
           ([∗ list] g;gt ∈ gs;tgs, interp_global gt (N.of_nat g)))%I.


  Global Instance interp_function_persistent τf n : Persistent (interp_function τf n).
  Proof.
    unfold interp_function, interp_closure, interp_closure_host, interp_closure_native.
    apply exist_persistent =>cl/=.
    apply sep_persistent;[apply _|].
    destruct cl,f; apply sep_persistent; apply _.
  Qed.
  Global Instance interp_global_persistent τg n : Persistent (interp_global τg n).
  Proof.
    unfold interp_global.
    destruct (tg_mut τg);apply _.
  Qed.
  Global Instance interp_instance_persistent τctx i : Persistent (interp_instance τctx i).
  Proof.
    destruct i, τctx;simpl.
    repeat apply sep_persistent;apply _.
  Qed.
  Global Instance interp_val_persistent τr vs : Persistent (interp_val τr vs).
  Proof.
    unfold interp_val, interp_value. apply or_persistent; [apply _|].
    apply exist_persistent =>v/=.
    apply sep_persistent;[apply _|].
    apply big_sepL2_persistent =>n ? xx.
    destruct xx;apply _.
  Qed.

  
  (* --------------------------------------------------------------------------------------- *)
  (* ------------------------------- EXPRESSION RELATION ----------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  (* Definition interp_expression_ctx (τs : result_type) (lh : lholed) (es : expr) (τl : result_type) (i : instance) : iProp Σ := *)
  (*   (WP es CTX lh_depth lh; lh {{ vs, interp_val τs vs ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f }})%I. *)

  (*Definition interp_ctx_return (τs2 : result_type) (τl : result_type) (i : instance) (v : val) : CtxR :=
    λne lh, (□ ∀ f, ↪[frame] f ∗ interp_frame τl i f -∗ interp_expression_ctx τs2 lh (of_val v) (interp_frame τl i))%I.*)
  
  (* Definition interp_br (τs : result_type) (lh : lholed) (τl : result_type) (i : instance) : VR := *)
  (*   λne (w : leibnizO val), (∃ j (v : list value), ⌜w = brV j v []⌝ ∗ *)
  (*                                           (∀ f, ↪[frame] f ∗ interp_frame τl i f -∗ interp_expression_ctx τs lh ((of_val (immV v)) ++ [AI_basic (BI_br j)]) τl i))%I. *)

  Notation BR := ((leibnizO val) -n> (leibnizO lholed) -n> (leibnizO (list (list value_type))) -n> iPropO Σ).
  
  Definition interp_br_def (τl : result_type) (i : instance)
                       (interp_br' : BR) : BR :=
    λne (w : leibnizO val) (lh : leibnizO lholed) (τc : leibnizO (list (list value_type))),
      ((∃ j (v : list value) es, ⌜w = brV j v es⌝ ∗
                              ∃ τs' vs k es lh' es' lh'' τs'',
                                ⌜τc !! j = Some τs'⌝ ∗ ⌜get_layer lh ((lh_depth lh) - S j) = Some (vs,k,es,lh',es')⌝ ∗
                                ⌜lh_depth lh'' = (lh_depth lh) - S j⌝ ∧ ⌜is_Some (lh_minus lh lh'')⌝ ∗
                                     interp_val (τs'' ++ τs') (immV v) ∗
                                     ∀ f, ↪[frame] f ∗ interp_frame τl i f -∗
                                     WP of_val (immV (drop (length τs'') v)) ++ [::AI_basic (BI_br j)] CTX S (lh_depth lh'); LH_rec vs k es lh' es'
                                     {{ vs, ((∃ τs, interp_val τs vs) ∨ ▷ interp_br' vs lh'' (drop (S j) τc)) ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f }}))%I.

  Global Instance interp_br_def_contractive τl i : Contractive (interp_br_def τl i).
  Proof.
    solve_proper_prepare.
    repeat (apply exist_ne +
            apply sep_ne +
            apply and_ne +
            auto +
            (rewrite /pointwise_relation; intros) +
            apply forall_ne + apply wand_ne).
    solve_contractive.
  Defined.
  
  Definition interp_br (τl : result_type) (i : instance) : BR :=
    fixpoint (interp_br_def τl i).
  
  Lemma fixpoint_interp_br_eq (τc : list (list (value_type))) (lh : lholed) (τl : result_type) (i : instance) v :
    interp_br τl i v lh τc ≡ interp_br_def τl i (interp_br τl i) v lh τc.
  Proof. exact: (fixpoint_unfold (interp_br_def τl i) v lh τc). Qed.
  
  Definition interp_expression (τc : list (list (value_type))) (τs : result_type) (lh : lholed) (τl : result_type) (i : instance) (es : expr) : iProp Σ :=
    (WP es {{ vs, (interp_val τs vs ∨ interp_br τl i vs lh τc) ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f }})%I.
  
  
  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------------- CONTEXT RELATION ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Fixpoint lholed_valid lh : Prop :=
    match lh with
    | LH_base vs es => const_list vs
    | LH_rec vs n es' lh' es'' => const_list vs ∧ lholed_valid lh'
    end.
  Lemma lholed_valid_fill (lh : lholed) :
    ∀ es, lholed_valid lh -> ∃ LI, lfilled (lh_depth lh) lh es LI.
  Proof.
    induction lh;intros es Hval.
    { exists (l ++ es ++ l0). apply lfilled_Ind_Equivalent. constructor. auto. }
    { destruct Hval as [Hconst [LI Hval%lfilled_Ind_Equivalent]%(IHlh es)].
      eexists. apply lfilled_Ind_Equivalent. constructor;eauto. }
  Qed.

  Fixpoint lholed_lengths (τc : list (list value_type)) lh : Prop :=
    match τc, lh with
    | [], LH_base vs es => True
    | τs :: τc, LH_rec _ n _ lh' _ => length τs = n ∧ lholed_lengths τc lh'
    | _,_ => False
    end.

  (*Definition interp_ctx_continuations (τc : list (list (value_type))) (τs2 : result_type) (τl : result_type) (i : instance) : CtxR :=
    λne lh, ([∗ list] k↦τs ∈ τc, ∃ vs j es lh' es', ⌜get_layer lh ((lh_depth lh) - S k) = Some (vs,j,es,lh',es')⌝ ∧
                                   (□ ∀ v f lh'', ⌜lh_depth lh'' = (lh_depth lh) - S k⌝ ∧ ⌜is_Some (lh_minus lh lh'')⌝ →
                                                  interp_val τs v -∗ ↪[frame] f ∗ interp_frame τl i f -∗
                                                  interp_expression τs2 lh'' (vs ++ ((of_val v) ++ es) ++ es') (interp_frame τl i)))%I.*)

  Definition interp_ctx_continuation (τc : list (list (value_type))) (lh : lholed) (k : nat) (τs τl : result_type) (i : instance) : iProp Σ :=
    (∃ vs j es lh' es' lh'', ⌜get_layer lh ((lh_depth lh) - S k) = Some (vs,j,es,lh',es')⌝ ∧ ⌜lh_depth lh'' = (lh_depth lh) - S k⌝ ∧ ⌜is_Some (lh_minus lh lh'')⌝ ∧
                          (□ ∀ v f, interp_val τs v -∗ ↪[frame] f ∗ interp_frame τl i f -∗
                                    ∃ τs2, interp_expression (drop (S k) τc) τs2 lh'' τl i (vs ++ ((of_val v) ++ es) ++ es')))%I.
  
  Definition interp_ctx_continuations (τc : list (list (value_type))) (τl : result_type) (i : instance) : CtxR :=
    λne lh, ([∗ list] k↦τs ∈ τc, interp_ctx_continuation τc lh k τs τl i)%I.

  (* Definition interp_ctx_return (τc : list (list (value_type))) (τs2 : result_type) (τl : result_type) (i : instance) : CtxR := *)
  (*   λne lh, (□ ∀ v f, interp_val τs2 v -∗ ↪[frame] f ∗ interp_frame τl i f -∗ interp_expression_ctx τs2 lh (of_val v) τl i)%I. *)
  
  Definition interp_ctx (τc : list (list value_type)) (τl : result_type) (i : instance) : CtxR :=
    λne lh, (⌜base_is_empty lh⌝ ∗
             ⌜lholed_lengths (rev τc) lh⌝ ∗
             ⌜lholed_valid lh⌝ ∗
             interp_ctx_continuations τc τl i lh
             (* interp_ctx_return τc τs2 τl i lh *)
            )%I.

  Global Instance interp_ctx_continuations_persistent τc τl i lh : Persistent (interp_ctx_continuations τc τl i lh).
  Proof. apply _. Qed.
  Global Instance interp_ctx_persistent τc τl i lh : Persistent (interp_ctx τc τl i lh).
  Proof. apply _. Qed.

  Notation IctxR := ((leibnizO instance) -n> (leibnizO lholed) -n> (leibnizO frame) -n> iPropO Σ).

  (* Definition interp_instance_ctx (τctx : t_context) : IctxR := *)
  (*   λne i lh f, let '{| tc_types_t := ts'; tc_func_t := tfs; tc_global := tgs; tc_table := tabs_t; tc_memory := mems_t; *)
  (*                       tc_local := tl; tc_label := tlabel; tc_return := treturn |} := τctx in *)
  (*               (interp_instance τctx i ∗ *)
  (*                interp_frame tl i f ∗ *)
  (*                interp_ctx tlabel lh)%I. *)


  Definition semantic_typing (τctx : t_context) (es : expr) (tf : function_type) : iProp Σ :=
    match tf with
    | Tf τ1 τ2 => ∀ i lh, (* interp_instance_ctx τctx i lh f -∗ *)
                              interp_instance τctx i -∗
                              interp_ctx (tc_label τctx) (tc_local τctx) i lh -∗
                              ∀ f vs, ↪[frame] f ∗ interp_frame (tc_local τctx) i f -∗
                                      interp_val τ1 vs -∗
                                      interp_expression (tc_label τctx) τ2 lh (tc_local τctx) i ((of_val vs) ++ es)
    end.

End logrel.
