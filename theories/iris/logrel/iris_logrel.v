From mathcomp Require Import ssreflect ssrbool eqtype seq.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Require Export iris_properties iris_atomicity.
Require Export iris_rules.
Import uPred.

Definition wf : string := "wfN".
Definition wt : string := "wtN".
Definition wm : string := "wmN".
Definition wg : string := "wgN".
Definition wfN (a : N) : namespace := nroot .@ wf .@ a.
Definition wtN (a b: N) : namespace := nroot .@ wt .@ a .@ b.
Definition wmN (a: N) : namespace := nroot .@ wm .@ a.
Definition wgN (a: N) : namespace := nroot .@ wg .@ a.

Section logrel.
  
  Context `{!wasmG Σ, !logrel_na_invs Σ}.

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
  Notation HR := ((leibnizO val) -n> (leibnizO lholed) -n> (leibnizO (list (list value_type))) -n> (leibnizO result_type) -n> iPropO Σ).
  Notation HRcls := ((leibnizO val) -n> iPropO Σ).

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
    match τ with
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
  (* ---------------------------------- FRAME RELATION ------------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)
  
  (* the frame interpretation includes all resources needed by the currently running frame *)
  Definition interp_frame (τs : result_type) (i : instance) : FR :=
    λne f, (∃ vs, ⌜f = Build_frame vs i⌝ ∗ interp_val τs (immV vs) ∗ na_own logrel_nais ⊤)%I.

  
  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- RETURN RELATION ------------------------------------ *)
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
  
  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------------- CLOSURE RELATION ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Definition is_basic (a : administrative_instruction) : Prop :=
    match a with
    | AI_basic _ => True
    | _ => False
    end.
  
  Fixpoint is_basic_expr (ai : seq.seq administrative_instruction) : Prop :=
    match ai with
    | [] => True
    | a :: ai => is_basic a ∧ is_basic_expr ai
    end.
  
  Fixpoint llholed_basic (vh : llholed) : Prop :=
    match vh with
    | LL_base _ ai => is_basic_expr ai
    | LL_label _ _ _ vh ai => is_basic_expr ai ∧ llholed_basic vh
    | LL_local _ _ _ vh ai => is_basic_expr ai ∧ llholed_basic vh
    end.
  
  (* The following definition is a fixed point for the call host host, in an empty context *)
  Definition interp_call_host_cls_def (host_list : list (hostfuncidx * function_type)) (τ2 : result_type)
             (interp_call_host' : HRcls) : HRcls :=
    (λne (w : leibnizO val),
      (∃ (vh : llholed) (v : seq.seq value) (tf : function_type)
                              (h : hostfuncidx) (τs1 τs2 : result_type),
                               ⌜w = callHostV tf h v vh⌝ ∗
                               ⌜tf = Tf τs1 τs2⌝ ∗
                               ⌜(h,tf) ∈ host_list⌝ ∗
                               ⌜llholed_basic vh⌝ ∗
                               interp_val τs1 (immV v) ∗
                               (* continuation for when the host function reenters *)
                               □ (∀ v2 f, interp_val τs2 v2 -∗
                                        ↪[frame] f -∗ na_own logrel_nais ⊤ -∗
                                        WP llfill vh (iris.of_val v2)
                                        {{ vs, (interp_val τ2 vs
                                                ∨ ▷ interp_call_host' vs) ∗ ↪[frame] f ∗ na_own logrel_nais ⊤ }}
                               ))
    )%I.

  Global Instance interp_call_host_cls_def_contractive hl t2 : Contractive (interp_call_host_cls_def hl t2).
  Proof.
    solve_proper_prepare.
    repeat (apply exist_ne +
                apply intuitionistically_ne +
                apply or_ne +
                apply sep_ne +
                apply and_ne +
                apply wp_ne +
                auto +
                (rewrite /pointwise_relation; intros) +
                apply forall_ne + apply wand_ne).
    f_contractive. apply H.
  Defined.

  Definition interp_call_host_cls (host_list : list (hostfuncidx * function_type)) (t2 : result_type)
    := fixpoint (interp_call_host_cls_def host_list t2).

  Lemma fixpoint_interp_call_host_cls_eq (host_list : list (hostfuncidx * function_type)) (t2 : result_type) v :
    interp_call_host_cls host_list t2 v ≡ (interp_call_host_cls_def host_list t2 (interp_call_host_cls host_list t2)) v.
  Proof. exact : (fixpoint_unfold (interp_call_host_cls_def host_list t2)). Qed.

  Definition interp_closure_native i tf1s tf2s tlocs e hl : iProp Σ :=
    ∀ vcs f, interp_val tf1s (immV vcs) -∗
             na_own logrel_nais ⊤ -∗
             ↪[frame] f -∗
             WP e FRAME (length tf2s); (Build_frame (vcs ++ (n_zeros tlocs)) i)
                  CTX 1; LH_rec [] (length tf2s) [] (LH_base [] []) []
                                {{ v, (interp_val tf2s v
                                       ∨ interp_call_host_cls hl tf2s v)
                                        ∗ na_own logrel_nais ⊤ ∗ ↪[frame] f }}.

  Definition interp_closure (host_list : list (hostfuncidx * function_type)) (τf : function_type) : ClR :=
      λne cl, (match cl with
               | FC_func_native i (Tf tf1s tf2s) tlocs e => ⌜τf = Tf tf1s tf2s⌝ ∗
                       □ ▷ interp_closure_native i tf1s tf2s tlocs (to_e_list e) host_list
               | FC_func_host (Tf tf1s tf2s) h => ⌜τf = Tf tf1s tf2s⌝ ∗ ⌜(h,τf) ∈ host_list⌝ (* ∗ □ interp_closure_host tf1s tf2s h *)
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

   Definition interp_instance (τctx : t_context) (host_list : list (hostfuncidx * function_type)) : IR := interp_instance' τctx (λ n, interp_closure host_list) (λ n, interp_closure host_list). 
  
  
  Global Instance interp_function_persistent τf n (icl : N -> function_type -> ClR) :
    (∀ n τf cl, Persistent (icl n τf cl)) -> Persistent (interp_function τf icl n).
  Proof.
    intros Hpers.
    unfold interp_function. 
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
  Global Instance interp_call_host_cls_persistent hl t v : Persistent (interp_call_host_cls hl t v).
  Proof. rewrite fixpoint_interp_call_host_cls_eq. cbn.
         repeat ((apply exist_persistent =>?) +
                   apply sep_persistent + apply or_persistent).
         all: try apply _.
  Qed.
         

  Global Instance interp_instance_persistent τctx hl i : Persistent (interp_instance τctx hl i).
  Proof.
    apply interp_instance_persistent'.
    all: intros. all: unfold interp_closure. all: simpl.
    all: destruct cl,f; try apply sep_persistent;apply _.
  Qed.
  
  (* --------------------------------------------------------------------------------------- *)
  (* ------------------------------- EXPRESSION RELATION ----------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_call_host_br_def (τl : result_type) (i : instance) (τro : option result_type) (host_list : list (hostfuncidx * function_type))
             (interp_call_host_br' : HR * BR) : HR * BR :=
    (λne (w : leibnizO val) (lh : leibnizO lholed) (τc : leibnizO (list (list value_type))) (τ2 : leibnizO result_type),
      (∃ (vh : llholed) (v : seq.seq value) (tf : function_type)
                              (h : hostfuncidx) (τs1 τs2 : result_type),
                               ⌜w = callHostV tf h v vh⌝ ∗
                               ⌜tf = Tf τs1 τs2⌝ ∗
                               ⌜(h,tf) ∈ host_list⌝ ∗
                               ⌜llholed_basic vh⌝ ∗
                               interp_val τs1 (immV v) ∗
                               (* continuation for when the host function reenters *)
                               □ (∀ v2 f, interp_val τs2 v2 -∗
                                        ↪[frame] f ∗ interp_frame τl i f -∗
                                        WP llfill vh (iris.of_val v2)
                                        {{ vs, (interp_val τ2 vs
                                                ∨ ▷ interp_call_host_br'.2 vs lh τc
                                                ∨ interp_return_option τro τl i vs
                                                ∨ ▷ interp_call_host_br'.1 vs lh τc τ2)
                                                 ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f }}
                               )
                           )%I
                              
      ,
      
      λne (w : leibnizO val) (lh : leibnizO lholed) (τc : leibnizO (list (list value_type))
                                                    ),
      ((∃ j, ∃ (vh : valid_holed j) (v : seq.seq value) p, ⌜w = brV vh⌝ ∗ ⌜get_base_l vh = v⌝ ∗ ⌜lh_depth (lh_of_vh vh) = p⌝ ∗
                              ∃ τs' vs k es lh' es' lh'' τs'',
                                ⌜τc !! (j - p) = Some τs'⌝ ∗ ⌜get_layer lh ((lh_depth lh) - S (j - p)) = Some (vs,k,es,lh',es')⌝ ∗
                                ⌜lh_depth lh'' = (lh_depth lh) - S (j - p)⌝ ∧ ⌜is_Some (lh_minus lh lh'')⌝ ∗
                                     interp_val (τs'' ++ τs') (immV v) ∗
                                     ∀ f, ↪[frame] f ∗ interp_frame τl i f -∗
                                           WP of_val (immV (drop (length τs'') v)) ++ [::AI_basic (BI_br (j - p))]
                                           CTX S (lh_depth lh'); LH_rec vs k es lh' es'
                                           {{ vs, ((∃ τs, interp_val τs vs)
                                                   ∨ ▷ interp_call_host_br'.2 vs lh'' (drop (S (j - p)) τc)
                                                   ∨ interp_return_option τro τl i vs
                                                   ∨ ▷ (∃ τs, interp_call_host_br'.1 vs lh'' (drop (S (j - p)) τc) τs))
                              ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f }}))%I
      
    ).

  Lemma dist_later_prod (o o1 : HR) (o0 o2 : BR) (n : nat) :
    dist_later n (o, o0) (o1, o2) ->
    dist_later n o o1 ∧ dist_later n o0 o2.
  Proof.
    intros Hdist.
    auto.
    destruct n;auto.
  Qed.
  
  Global Instance interp_call_host_br_def_contractive τl i τto hl : Contractive (interp_call_host_br_def τl i τto hl).
  Proof.
    solve_proper_prepare.
    destruct x,y.
    apply dist_later_prod in H as [? ?].
    apply pair_ne.
    { solve_proper_prepare.
      repeat (apply exist_ne +
                apply intuitionistically_ne +
                apply or_ne +
                apply sep_ne +
                apply and_ne +
                apply wp_ne +
                auto +
                (rewrite /pointwise_relation; intros) +
                apply forall_ne + apply wand_ne).
      { f_contractive. apply H0. }
      { f_contractive. apply H. }
    }
    { solve_proper_prepare.
      repeat (apply exist_ne +
                apply or_ne +
                apply sep_ne +
                apply and_ne +
                apply wp_ne +
                auto +
                (rewrite /pointwise_relation; intros) +
                apply forall_ne + apply wand_ne).
      { f_contractive. apply H0. }
      { f_contractive. apply exist_ne. apply H. }
    }
  Defined.

  Definition interp_call_host_br (τl : result_type) (i : instance) (τto : option result_type) (host_list : list (hostfuncidx * function_type)) : HR * BR :=
    fixpoint (interp_call_host_br_def τl i τto host_list).

  Definition interp_call_host (τl : result_type) (i : instance) (τto : option result_type) (host_list : list (hostfuncidx * function_type))
    := (interp_call_host_br τl i τto host_list).1.
  Definition interp_br (τl : result_type) (i : instance) (τto : option result_type) (host_list : list (hostfuncidx * function_type))
    := (interp_call_host_br τl i τto host_list).2.

  Lemma fixpoint_interp_br_eq (τc : list (list (value_type))) (τl : result_type) (i : instance) (τto : option result_type)
        (host_list : list (hostfuncidx * function_type)) v lh :
    interp_br τl i τto host_list v lh τc ≡ (interp_call_host_br_def τl i τto host_list (interp_call_host_br τl i τto host_list)).2 v lh τc.
  Proof. pose proof (fixpoint_unfold (interp_call_host_br_def τl i τto host_list)). destruct H as [? ?].
         specialize (H0 v lh τc). auto. Qed.

  Lemma fixpoint_interp_call_host_eq lh (τc : list (list (value_type))) (τl : result_type) (i : instance) (τto : option result_type)
        (host_list : list (hostfuncidx * function_type)) v t2 :
    interp_call_host τl i τto host_list v lh τc t2 ≡ (interp_call_host_br_def τl i τto host_list (interp_call_host_br τl i τto host_list)).1 v lh τc t2.
  Proof. pose proof (fixpoint_unfold (interp_call_host_br_def τl i τto host_list)). destruct H as [? ?].
         specialize (H v lh τc t2). auto. Qed.
  
  Definition interp_br_body τc lh j p (w : seq.seq value) τl i τto hl : iProp Σ :=
    ∃ τs' vs k es lh' es' lh'' τs'',
      ⌜τc !! (j - p) = Some τs'⌝ ∗ ⌜get_layer lh ((lh_depth lh) - S (j - p)) = Some (vs,k,es,lh',es')⌝ ∗
      ⌜lh_depth lh'' = (lh_depth lh) - S (j - p)⌝ ∧ ⌜is_Some (lh_minus lh lh'')⌝ ∗
      interp_val (τs'' ++ τs') (immV w) ∗
      ∀ f, ↪[frame] f ∗ interp_frame τl i f -∗
            WP of_val (immV (drop (length τs'') w)) ++ [::AI_basic (BI_br (j - p))] CTX S (lh_depth lh'); LH_rec vs k es lh' es'
                {{ vs, ((∃ τs, interp_val τs vs) ∨
                          ▷ interp_br τl i τto hl vs lh'' (drop (S (j - p)) τc) ∨
                          interp_return_option τto τl i vs ∨
                          ▷ (∃ τs, interp_call_host τl i τto hl vs lh'' (drop (S (j - p)) τc) τs)) 
                         ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f }}.
  
  Definition interp_expression (τc : list (list (value_type))) (τto : option result_type) (host_list : list (hostfuncidx * function_type))
             (τs : result_type) (lh : lholed) (τl : result_type) (i : instance) (es : expr) : iProp Σ :=
    (WP es {{ vs, (interp_val τs vs
                   ∨ interp_br τl i τto host_list vs lh τc
                   ∨ interp_return_option τto τl i vs
                   ∨ interp_call_host τl i τto host_list vs lh τc τs) ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f }})%I.
  
  
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

  Definition interp_ctx_continuation (τc : list (list (value_type))) (τto : option result_type) (hl : list (hostfuncidx * function_type)) (lh : lholed) (k : nat) (τs τl : result_type) (i : instance) : iProp Σ :=
    (∃ vs j es lh' es' lh'', ⌜get_layer lh ((lh_depth lh) - S k) = Some (vs,j,es,lh',es')⌝ ∧ ⌜lh_depth lh'' = (lh_depth lh) - S k⌝ ∧ ⌜is_Some (lh_minus lh lh'')⌝ ∧
                          (□ ∀ v f, interp_val τs v -∗ ↪[frame] f ∗ interp_frame τl i f -∗
                                    ∃ τs2, interp_expression (drop (S k) τc) τto hl τs2 lh'' τl i (vs ++ ((of_val v) ++ es) ++ es')))%I.
  
  Definition interp_ctx_continuations (τc : list (list (value_type))) (τto : option result_type) (hl : list (hostfuncidx * function_type)) (τl : result_type) (i : instance) : CtxR :=
    λne lh, ([∗ list] k↦τs ∈ τc, interp_ctx_continuation τc τto hl lh k τs τl i)%I.
  
  Definition interp_ctx (τc : list (list value_type)) (τto : option result_type) (hl : list (hostfuncidx * function_type)) (τl : result_type) (i : instance) : CtxR :=
    λne lh, (⌜base_is_empty lh⌝ ∗
             ⌜lholed_lengths (rev τc) lh⌝ ∗
             ⌜lholed_valid lh⌝ ∗
             interp_ctx_continuations τc τto hl τl i lh
            )%I.

  Global Instance interp_ctx_continuations_persistent τc τl τto hl i lh : Persistent (interp_ctx_continuations τc τl τto hl i lh).
  Proof. apply _. Qed.
  Global Instance interp_ctx_persistent τc τto hl τl i lh : Persistent (interp_ctx τc τto τl hl i lh).
  Proof. apply _. Qed.

  Notation IctxR := ((leibnizO instance) -n> (leibnizO lholed) -n> (leibnizO frame) -n> iPropO Σ).

  Definition semantic_typing (τctx : t_context) (es : expr) (tf : function_type) : iProp Σ :=
    match tf with
    | Tf τ1 τ2 => ∀ i lh hl, interp_instance τctx hl i -∗
                         interp_ctx (tc_label τctx) (tc_return τctx) hl (tc_local τctx) i lh -∗
                         ∀ f vs, ↪[frame] f ∗ interp_frame (tc_local τctx) i f -∗
                                  interp_val τ1 vs -∗
                                  interp_expression (tc_label τctx) (tc_return τctx) hl τ2 lh (tc_local τctx) i ((of_val vs) ++ es)
    end.

  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------- RELATIONS FOR CLOSED CONTEXTS ----------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_expression_closure_stuck_host (hl : list (hostfuncidx * function_type)) (τs : result_type) (f : frame) (es : expr) : iProp Σ :=
    (WP es {{ vs, ((interp_val τs vs ∨ interp_call_host_cls hl τs vs) ∗ na_own logrel_nais ⊤) ∗ ↪[frame] f }})%I.

  Definition semantic_typing_local_stuck_host (hl : list (hostfuncidx * function_type)) (τctx : t_context) (es : seq.seq basic_instruction) (ts : result_type) (tf : function_type) : iProp Σ :=
    ⌜(tc_label τctx) = [] ∧ (tc_return τctx) = None⌝ ∧
    match tf with
    | Tf τ1 τ2 => ∀ i, interp_instance τctx hl i -∗
                      ∀ f vs, ↪[frame] f -∗ na_own logrel_nais ⊤ -∗
                               interp_val (τ1 ++ ts) (immV vs) -∗
                               interp_expression_closure_stuck_host hl τ2 f [::AI_local (length τ2)
                                                                (Build_frame vs i)
                                                                [::AI_label (length τ2) [] (to_e_list es)]]
    end.
  
  Definition interp_expression_closure_no_host (τs : result_type) (f : frame) (es : expr) : iProp Σ :=
    (WP es {{ vs, (interp_val τs vs ∗ na_own logrel_nais ⊤) ∗ ↪[frame] f }})%I.

  Definition semantic_typing_local_no_host (τctx : t_context) (es : seq.seq basic_instruction) (ts : result_type) (tf : function_type) : iProp Σ :=
    ⌜(tc_label τctx) = [] ∧ (tc_return τctx) = None⌝ ∧
    match tf with
    | Tf τ1 τ2 => ∀ i, interp_instance τctx [] i -∗
                      ∀ f vs, ↪[frame] f -∗ na_own logrel_nais ⊤ -∗
                               interp_val (τ1 ++ ts) (immV vs) -∗
                               interp_expression_closure_no_host τ2 f [::AI_local (length τ2)
                                                                (Build_frame vs i)
                                                                [::AI_label (length τ2) [] (to_e_list es)]]
    end.
  
End logrel.

(* --------------------------------------------------------------------------------------- *)
(* --------------------------------- HOST INTEGRATION ------------------------------------ *)
(* --------------------------------------------------------------------------------------- *)

Reserved Notation "'WPh' h {{ Φ } }" (at level 20, h, Φ at level 200).

Class host_program_logic Σ `{wasmG Σ} := {
    host_function : Type ;
    result : Type ;

    (* host context *)
    host_ctx : Type ;
    fill_host : host_ctx -> iris.expr -> host_function ;

    (* we need functions that translates result to a logical wasm value *)
    val_of_host_val : result -> iris.val ;

    (* the host WP *)
    wp_host (s : stuckness) : coPset -d> host_function -d> (result -d> iPropO Σ) -d> iPropO Σ
    where "'WPh' h {{ Φ } }" := (wp_host NotStuck ⊤ h Φ);

    (* host bind lemma *)
    wp_host_bind :
    (∀ hctx es Φ, 
        WP es {{ v, WPh fill_host hctx (iris.of_val v) {{ Φ }} }} -∗
           WPh fill_host hctx es {{ Φ }});

    (* host wand *)
    wp_host_wand :
    (∀ es Φ Ψ, WP es {{ Φ }} -∗ (∀ r, Φ r -∗ Ψ r) -∗ WP es {{ Ψ }});

    (* host fupd intro *)
    fupd_wp_host :
    (∀ e Φ, (|={⊤}=> WPh e {{ Φ }}) -∗ WPh e {{ Φ }});
    wp_fupd_host :
    (∀ e Φ, (WPh e {{ λ v, |={⊤}=> Φ v }}) -∗ WPh e {{ Φ }});
  }.

Notation "'WPh' h {{ Φ } }" := (wp_host NotStuck ⊤ h Φ).

Section logrel_host.
  Context `{!wasmG Σ, !logrel_na_invs Σ, !host_program_logic Σ}.

  Definition interp_expression_closure (hctx : host_ctx) (τs : result_type)  (f : frame) (es : expr) : iProp Σ :=
    (WPh fill_host hctx es {{ λ vs, (interp_val τs (val_of_host_val vs) ∗ na_own logrel_nais ⊤) ∗ ↪[frame] f }})%I.

  Definition interp_closure_host (t2 : result_type) (hctx : host_ctx) tf1s tf2s (h : hostfuncidx) : iProp Σ :=
    □ ∀ vcs f llh, interp_val tf1s (immV vcs) -∗
           na_own logrel_nais ⊤ -∗
           ↪[frame] f -∗
           ▷ (∀ v2, interp_val tf2s v2 -∗ na_own logrel_nais ⊤ -∗ ↪[frame] f -∗
                               WPh fill_host hctx (llfill llh (iris.of_val v2)) {{ λ r, (interp_val t2 (val_of_host_val r) ∗ na_own logrel_nais ⊤) ∗ ↪[frame] f }}) -∗
           WPh fill_host hctx (llfill llh [AI_call_host (Tf tf1s tf2s) h vcs])
           {{ λ r, (interp_val t2 (val_of_host_val r) ∗ na_own logrel_nais ⊤) ∗ ↪[frame] f }}.

  Definition interp_host_calls (t2 : result_type) (hctx : host_ctx) (hl : list (hostfuncidx * function_type)) : iProp Σ :=
    [∗ list] ht ∈ hl, let '(h, t) := ht in
                      let 'Tf tf1s tf2s := t in
                      interp_closure_host t2 hctx tf1s tf2s h.

  Global Instance interp_host_calls_persistent t2 hctx hl : Persistent (interp_host_calls t2 hctx hl).
  Proof. apply big_sepL_persistent =>n x. destruct x,f; apply _. Qed.
         
  Definition interp_host_return (hctx : host_ctx) (τ2 : result_type) : iProp Σ :=
    □ ∀ v f, interp_val τ2 v -∗
             na_own logrel_nais ⊤ -∗          
             ↪[frame] f -∗
             WPh fill_host hctx (iris.of_val v) {{ λ r, (interp_val τ2 (val_of_host_val r) ∗ na_own logrel_nais ⊤) ∗ ↪[frame]f }}.
  
  Definition semantic_typing_local (τctx : t_context) (hl : list (hostfuncidx * function_type))
             (es : seq.seq basic_instruction) (ts : result_type) (tf : function_type) (hctx : host_ctx) : iProp Σ :=
    ⌜(tc_label τctx) = [] ∧ (tc_return τctx) = None⌝ ∧
    match tf with
    | Tf τ1 τ2 => ∀ i, interp_instance τctx hl i -∗
                      interp_host_calls τ2 hctx hl -∗
                      interp_host_return hctx τ2 -∗        
                      ∀ f vs, ↪[frame] f -∗ na_own logrel_nais ⊤ -∗
                               interp_val (τ1 ++ ts) (immV vs) -∗
                               interp_expression_closure hctx τ2 f [::AI_local (length τ2)
                                                                (Build_frame vs i)
                                                                [::AI_label (length τ2) [] (to_e_list es)]]
    end.

End logrel_host.
