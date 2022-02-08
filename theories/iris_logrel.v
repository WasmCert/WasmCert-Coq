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
Definition wfN (a : N) : namespace := nroot .@ wf .@ a.

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

  Implicit Types w : (leibnizO value).
  Implicit Types ws : (list (leibnizO value)).
  Implicit Types v : (leibnizO val).
  Implicit Types f : (leibnizO frame).
  Implicit Types cl : (leibnizO function_closure).
  Implicit Types lh : (leibnizO lholed).

  Implicit Types τ : value_type.
  Implicit Types τs : result_type.
  Implicit Types ηs : result_type.
  Implicit Types τf : function_type.
  Implicit Types τc : list (list value_type).

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

  Definition interp_val (τs : result_type) : VR :=
    λne v, (∃ ws, ⌜v = immV ws⌝ ∗ [∗ list] w;τ ∈ ws;τs, interp_value τ w)%I.


  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- FRAME RELATION ------------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  (* Note: the frame relation is not persistent *)
    
  Definition interp_frame (τs : result_type) (i : instance) : FR :=
    λne f, (∃ vs, ⌜f = Build_frame vs i⌝ ∗ interp_val τs (immV vs) ∗ ↪[frame] f)%I.

  
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

  Fixpoint lholed_return_lengths (τc : list (list value_type)) lh : Prop :=
    match τc, lh with
    | [], LH_base vs es => True
    | τs :: τc, LH_rec _ n _ lh' _ => length τs = n ∧ lholed_return_lengths τc lh'
    | _,_ => False
    end.
  
  Definition interp_ctx (τc : list (list value_type)) : CtxR :=
    λne lh, (⌜base_is_empty lh⌝ ∗ ⌜lholed_return_lengths τc lh⌝)%I.
  
  
  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------------- CLOSURE RELATION ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* Note: here we assume that the function table does not mutate *)
  (* this is fine for a simple host with no reentrancy, but is not *)
  (* powerful enough to prove examples such as Landin's Knot *)

  Definition interp_closure_native i tf1s tf2s tlocs e : iProp Σ :=
    □ ∀ vcs, interp_val tf1s (immV vcs) -∗
             na_own logrel_nais ⊤ -∗
             ∃ f', WP e FRAME (length tf2s); (Build_frame (vcs ++ (n_zeros tlocs)) i)
                        CTX 1; LH_rec [] (length tf2s) [] (LH_base [] []) []
                        {{ v, (interp_val tf2s v ∗ na_own logrel_nais ⊤) ∗ ↪[frame] f' }}.
  
  Definition interp_closure_host tf1s tf2s h : iProp Σ :=
    □ ∀ vcs, interp_val tf1s (immV vcs) -∗
             wp_host HWP NotStuck ⊤ h vcs
                        (λ r, from_option (interp_val tf2s) False (to_val (result_to_stack r))).
  
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

  
  






(*   Definition tab_typing (t : tableinst) (tt : table_type) : bool := *)
(*   (tt.(tt_limits).(lim_min) <= tab_size t) && *)
(*   (t.(table_max_opt) < tt.(tt_limits).(lim_max)). *)

(* Definition tabi_agree ts (n : nat) (tab_t : table_type) : bool := *)
(*   (n < List.length ts) && *)
(*   match List.nth_error ts n with *)
(*   | None => false *)
(*   | Some x => tab_typing x tab_t *)
(*   end. *)

End logrel.

  
