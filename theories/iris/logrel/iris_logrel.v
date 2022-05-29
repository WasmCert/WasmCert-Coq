From mathcomp Require Import ssreflect ssrbool eqtype seq.
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
  


  Context `{!wasmG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.

  
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
  Notation BR := ((leibnizO val) -n> (leibnizO lholed) -n> (leibnizO (list (list value_type))) -n> iPropO Σ).
  Notation RR := ((leibnizO val) -n> iPropO Σ).

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
  Implicit Types τr : result_type.
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
    ∀ vcs, interp_val tf1s (immV vcs) -∗
             na_own logrel_nais ⊤ -∗
             ∀ f1, ↪[frame] f1 -∗ WP e FRAME (length tf2s); (Build_frame (vcs ++ (n_zeros tlocs)) i)
                                       CTX 1; LH_rec [] (length tf2s) [] (LH_base [] []) []
                        {{ v, (interp_val tf2s v ∗ na_own logrel_nais ⊤) ∗ ↪[frame] f1 }}.
  
  Definition interp_closure_host tf1s tf2s (h : hostfuncidx) : iProp Σ :=
    ∀ vcs, interp_val tf1s (immV vcs) -∗
                      ∃ r, (interp_val tf2s) r.
(*    ∀ vcs, interp_val tf1s (immV vcs) -∗
             wp_host HWP NotStuck ⊤ h vcs
                        (λ r, from_option (interp_val tf2s) False (iris.to_val (result_to_stack r))).  *)
  
  Definition interp_closure (τf : function_type) : ClR :=
      λne cl, (match cl with
               | FC_func_native i (Tf tf1s tf2s) tlocs e => ⌜τf = Tf tf1s tf2s⌝ ∗
                       □ ▷ interp_closure_native i tf1s tf2s tlocs (to_e_list e)
               | FC_func_host (Tf tf1s tf2s) h => ⌜τf = Tf tf1s tf2s⌝ ∗ □ interp_closure_host tf1s tf2s h
               end)%I. 
  
  Definition interp_function (τf : function_type) (interp_closure' : N -> function_type -> ClR) : FfR :=
    λne n, (∃ (cl : function_closure), na_inv logrel_nais (wfN n) (n ↦[wf] cl)
                                     ∗ interp_closure' n τf cl)%I.
  
  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- TABLE RELATION ------------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_table_entry (τf : function_type) (interp_closure' : N -> function_type -> ClR) : TeR :=
    λne n m, (∃ (fe : funcelem), na_inv logrel_nais (wtN n m) (n ↦[wt][m] fe)
                                ∗ from_option ((interp_function τf interp_closure') ∘ N.of_nat) True fe)%I.
  (* ⊤ means failure is allowed in case the table is not populated *)


  (* the table interpretation is a bit tricky: the table size needs to represent the full table, 
     with the capability to increase its size with None entries. A None entry is to describe the 
     out of bounds behaviour of a call indirect (with a trap rather than getting stuck) *)
  Definition interp_table (table_size : nat) (interp_closure' : N -> function_type -> ClR) : TR :=
    λne n, ([∗ list] i↦_ ∈ (repeat 0 table_size), ∃ (τf : function_type), interp_table_entry τf interp_closure' n (N.of_nat i))%I.


  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- MEMORY RELATION ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)
    
  Definition interp_mem : MR :=
    λne n, (na_inv logrel_nais (wmN n) (∃ (mem : memory),
                                           ([∗ list] i ↦ b ∈ (mem.(mem_data).(ml_data)), n ↦[wm][ (N.of_nat i) ] b) ∗
                                           n ↦[wmlength] mem_length mem))%I.
  
  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------------- GLOBALS RELATION ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_global (τg : global_type) : GR :=
    λne n,
      (match (tg_mut τg) with
      | MUT_immut => ∃ (P : value_type -> WR),
         (□ ∀ w, P (tg_t τg) w -∗ interp_value (tg_t τg) w) ∗ 
         na_inv logrel_nais (wgN n) (∃ w, n ↦[wg] Build_global MUT_immut w ∗ P (tg_t τg) w)
      | MUT_mut => na_inv logrel_nais (wgN n) (∃ w, n ↦[wg] Build_global MUT_mut w ∗ interp_value (tg_t τg) w)
      end)%I.


  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- FRAME RELATION ------------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  (* the frame interpretation includes all resources needed by the currently running frame *)
  Definition interp_frame (τs : result_type) (i : instance) : FR :=
    λne f, (∃ vs, ⌜f = Build_frame vs i⌝ ∗ interp_val τs (immV vs) ∗ na_own logrel_nais ⊤)%I.

  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------------- INSTANCE RELATION ----------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_instance' (τctx : t_context) (interp_closure' : N -> function_type -> ClR) (interp_closure'' : N -> function_type -> ClR) : IR :=
    λne i, let '{| inst_types := ts; inst_funcs := fs; inst_tab := tbs; inst_memory := ms; inst_globs := gs; |} := i in
           let '{| tc_types_t := ts'; tc_func_t := tfs; tc_global := tgs; tc_table := tabs_t; tc_memory := mems_t;
                   tc_local := tl; tc_label := tlabel; tc_return := treturn |} := τctx in 
           ((* Type declarations *)
             ⌜ts = ts'⌝ ∗
            (* Function declarations *)
           ([∗ list] f;tf ∈ fs;tfs, interp_function tf interp_closure' (N.of_nat f)) ∗
            (* Function tables *)           
           (match nth_error tabs_t 0 with
            | Some τt => match nth_error tbs 0 with
                        | Some a => (∃ table_size (table_lim : option N),
                                       ⌜ssrnat.leq (ssrnat.nat_of_bool table_lim)
                                        (ssrnat.nat_of_bool (lim_max (tt_limits τt)))⌝
                                       ∗ (N.of_nat a) ↪[wtlimit] table_lim
                                       ∗ (N.of_nat a) ↪[wtsize] table_size
                                       ∗ (interp_table table_size interp_closure'') (N.of_nat a))
                        | None => False
                        end
            | None => True
            end) ∗
            (* Linear Memory *)
           (match nth_error mems_t 0 with
            | Some τm => match nth_error ms 0 with
                        | Some a => (N.of_nat a) ↪[wmlimit] (lim_max τm) ∗ interp_mem (N.of_nat a)
                        | None => False
                        end
            | None => True
            end) ∗
            (* Global declarations *)
           ([∗ list] g;gt ∈ gs;tgs, interp_global gt (N.of_nat g)))%I.

   Definition interp_instance (τctx : t_context) : IR := interp_instance' τctx (λ n, interp_closure) (λ n, interp_closure). 
  
  
  Global Instance interp_function_persistent τf n (icl : N -> function_type -> ClR) :
    (∀ n τf cl, Persistent (icl n τf cl)) -> Persistent (interp_function τf icl n).
  Proof.
    intros Hpers.
    unfold interp_function. (* , interp_closure, interp_closure_host, interp_closure_native. *)
    apply exist_persistent =>cl/=.
    apply sep_persistent;[apply _|]. auto.
  Qed.
  Global Instance interp_global_persistent τg n : Persistent (interp_global τg n).
  Proof.
    unfold interp_global.
    destruct (tg_mut τg);apply _.
  Qed.
  Global Instance interp_instance_persistent' τctx i (icl icl' : N -> function_type -> ClR) :
    (∀ n τf cl, Persistent (icl n τf cl)) -> (∀ n τf cl, Persistent (icl' n τf cl)) -> Persistent (interp_instance' τctx icl icl' i).
  Proof.
    destruct i, τctx;simpl.
    repeat apply sep_persistent;apply _.
  Qed.
  Global Instance interp_value_persistent τ vs : Persistent (interp_value τ vs).
  Proof.
    unfold interp_value. destruct τ;apply _.
  Qed.
  Global Instance interp_val_persistent τr vs : Persistent (interp_val τr vs).
  Proof.
    unfold interp_val, interp_value. apply or_persistent; [apply _|].
    apply exist_persistent =>v/=.
    apply sep_persistent;[apply _|].
    apply big_sepL2_persistent =>n ? xx.
    destruct xx;apply _.
  Qed.

  Global Instance interp_instance_persistent τctx i : Persistent (interp_instance τctx i).
  Proof.
    apply interp_instance_persistent'.
    all: intros. all: unfold interp_closure. all: simpl.
    all: destruct cl,f; apply sep_persistent;apply _.
  Qed.
  
  (* --------------------------------------------------------------------------------------- *)
  (* ------------------------------- EXPRESSION RELATION ----------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  Fixpoint get_base_l {i : nat} (lh : valid_holed i) :=
    match lh with
    | VH_base _ vs _ => vs
    | VH_rec _ _ _ _ lh' _ => get_base_l lh'
    end.
  Fixpoint simple_get_base_l (lh : simple_valid_holed) :=
    match lh with
    | SH_base vs _ => vs
    | SH_rec _ _ _ lh' _ => simple_get_base_l lh'
    end.

  Definition interp_return_option (τr : option result_type) (τl : result_type) (i : instance) : RR :=
    λne (w : leibnizO val), (∃ (vh : simple_valid_holed) (v : seq.seq value), ⌜w = retV vh⌝ ∗ ⌜simple_get_base_l vh = v⌝ ∗
                             match τr with 
                             | Some τr => (∃ τs'', interp_val (τs'' ++ τr) (immV v) ∗
                                           ∀ f f', ↪[frame] f' -∗
                                               WP [AI_local (length τr) f (of_val w)] {{ vs, interp_val τr vs ∗ ↪[frame] f' }})
                             | None => False
                             end)%I.

  Definition interp_br_def (τl : result_type) (i : instance) (τro : option result_type)
                       (interp_br' : BR) : BR :=
    λne (w : leibnizO val) (lh : leibnizO lholed) (τc : leibnizO (list (list value_type))),
      ((∃ j, ∃ (vh : valid_holed j) (v : seq.seq value) p, ⌜w = brV vh⌝ ∗ ⌜get_base_l vh = v⌝ ∗ ⌜lh_depth (lh_of_vh vh) = p⌝ ∗
                              ∃ τs' vs k es lh' es' lh'' τs'',
                                ⌜τc !! (j - p) = Some τs'⌝ ∗ ⌜get_layer lh ((lh_depth lh) - S (j - p)) = Some (vs,k,es,lh',es')⌝ ∗
                                ⌜lh_depth lh'' = (lh_depth lh) - S (j - p)⌝ ∧ ⌜is_Some (lh_minus lh lh'')⌝ ∗
                                     interp_val (τs'' ++ τs') (immV v) ∗
                                     ∀ f, ↪[frame] f ∗ interp_frame τl i f -∗
                                     WP of_val (immV (drop (length τs'') v)) ++ [::AI_basic (BI_br (j - p))] CTX S (lh_depth lh'); LH_rec vs k es lh' es'
                                        {{ vs, ((∃ τs, interp_val τs vs) ∨ ▷ interp_br' vs lh'' (drop (S (j - p)) τc) ∨ interp_return_option τro τl i vs)
                                                 ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f }}))%I.

  Global Instance interp_br_def_contractive τl i τto : Contractive (interp_br_def τl i τto).
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
  
  Definition interp_br (τl : result_type) (i : instance) (τto : option result_type) : BR :=
    fixpoint (interp_br_def τl i τto).

  Definition interp_br_body τc lh j p (w : seq.seq value) τl i τto : iProp Σ :=
    ∃ τs' vs k es lh' es' lh'' τs'',
      ⌜τc !! (j - p) = Some τs'⌝ ∗ ⌜get_layer lh ((lh_depth lh) - S (j - p)) = Some (vs,k,es,lh',es')⌝ ∗
      ⌜lh_depth lh'' = (lh_depth lh) - S (j - p)⌝ ∧ ⌜is_Some (lh_minus lh lh'')⌝ ∗
      interp_val (τs'' ++ τs') (immV w) ∗
      ∀ f, ↪[frame] f ∗ interp_frame τl i f -∗
            WP of_val (immV (drop (length τs'') w)) ++ [::AI_basic (BI_br (j - p))] CTX S (lh_depth lh'); LH_rec vs k es lh' es'
            {{ vs, ((∃ τs, interp_val τs vs) ∨ ▷ interp_br τl i τto vs lh'' (drop (S (j - p)) τc) ∨ interp_return_option τto τl i vs) ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f }}.
  
  Lemma fixpoint_interp_br_eq (τc : list (list (value_type))) (lh : lholed) (τl : result_type) (i : instance) (τto : option result_type) v :
    interp_br τl i τto v lh τc ≡ interp_br_def τl i τto (interp_br τl i τto) v lh τc.
  Proof. exact: (fixpoint_unfold (interp_br_def τl i τto) v lh τc). Qed.
  
  Definition interp_expression (τc : list (list (value_type))) (τto : option result_type)
             (τs : result_type) (lh : lholed) (τl : result_type) (i : instance) (es : expr) : iProp Σ :=
    (WP es {{ vs, (interp_val τs vs ∨ interp_br τl i τto vs lh τc ∨ interp_return_option τto τl i vs) ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f }})%I.
  
  
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

  Definition interp_ctx_continuation (τc : list (list (value_type))) (τto : option result_type) (lh : lholed) (k : nat) (τs τl : result_type) (i : instance) : iProp Σ :=
    (∃ vs j es lh' es' lh'', ⌜get_layer lh ((lh_depth lh) - S k) = Some (vs,j,es,lh',es')⌝ ∧ ⌜lh_depth lh'' = (lh_depth lh) - S k⌝ ∧ ⌜is_Some (lh_minus lh lh'')⌝ ∧
                          (□ ∀ v f, interp_val τs v -∗ ↪[frame] f ∗ interp_frame τl i f -∗
                                    ∃ τs2, interp_expression (drop (S k) τc) τto τs2 lh'' τl i (vs ++ ((of_val v) ++ es) ++ es')))%I.
  
  Definition interp_ctx_continuations (τc : list (list (value_type))) (τto : option result_type) (τl : result_type) (i : instance) : CtxR :=
    λne lh, ([∗ list] k↦τs ∈ τc, interp_ctx_continuation τc τto lh k τs τl i)%I.
  
  Definition interp_ctx (τc : list (list value_type)) (τto : option result_type) (τl : result_type) (i : instance) : CtxR :=
    λne lh, (⌜base_is_empty lh⌝ ∗
             ⌜lholed_lengths (rev τc) lh⌝ ∗
             ⌜lholed_valid lh⌝ ∗
             interp_ctx_continuations τc τto τl i lh
            )%I.

  Global Instance interp_ctx_continuations_persistent τc τl τto i lh : Persistent (interp_ctx_continuations τc τl τto i lh).
  Proof. apply _. Qed.
  Global Instance interp_ctx_persistent τc τto τl i lh : Persistent (interp_ctx τc τto τl i lh).
  Proof. apply _. Qed.

  Notation IctxR := ((leibnizO instance) -n> (leibnizO lholed) -n> (leibnizO frame) -n> iPropO Σ).

  Definition semantic_typing (τctx : t_context) (es : expr) (tf : function_type) : iProp Σ :=
    match tf with
    | Tf τ1 τ2 => ∀ i lh, interp_instance τctx i -∗
                         interp_ctx (tc_label τctx) (tc_return τctx) (tc_local τctx) i lh -∗
                         ∀ f vs, ↪[frame] f ∗ interp_frame (tc_local τctx) i f -∗
                                  interp_val τ1 vs -∗
                                  interp_expression (tc_label τctx) (tc_return τctx) τ2 lh (tc_local τctx) i ((of_val vs) ++ es)
    end.

  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------- RELATIONS FOR CLOSED CONTEXTS ----------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_expression_closed (τs : result_type) (τl : result_type) (i : instance) (es : expr) : iProp Σ :=
    (WP es {{ vs, interp_val τs vs ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f }})%I.

  Definition semantic_typing_closed (τctx : t_context) (es : expr) (tf : function_type) : iProp Σ :=
    ⌜(tc_label τctx) = [] ∧ (tc_return τctx) = None⌝ ∧
    match tf with
    | Tf τ1 τ2 => ∀ i, interp_instance τctx i -∗
                      ∀ f vs, ↪[frame] f ∗ interp_frame (tc_local τctx) i f -∗
                               interp_val τ1 vs -∗
                               interp_expression_closed τ2 (tc_local τctx) i ((of_val vs) ++ es)
    end.


  Definition interp_expression_closure (τs : result_type) (f : frame) (es : expr) : iProp Σ :=
    (WP es {{ vs, (interp_val τs vs ∗ na_own logrel_nais ⊤) ∗ ↪[frame] f }})%I.

  Definition semantic_typing_local (τctx : t_context) (es : seq.seq basic_instruction) (ts : result_type) (tf : function_type) : iProp Σ :=
    ⌜(tc_label τctx) = [] ∧ (tc_return τctx) = None⌝ ∧
    match tf with
    | Tf τ1 τ2 => ∀ i, interp_instance τctx i -∗
                      ∀ f vs, ↪[frame] f -∗ na_own logrel_nais ⊤ -∗
                               interp_val (τ1 ++ ts) (immV vs) -∗
                               interp_expression_closure τ2 f [::AI_local (length τ2)
                                                                (Build_frame vs i)
                                                                [::AI_label (length τ2) [] (to_e_list es)]]
    end.
  

End logrel.
