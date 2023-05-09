(** Wasm interpreter **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Wasm Require Import common.
From Coq Require Import ZArith.BinInt NArith.BinNat.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From ExtLib Require Import Structures.Monad.
From ITree Require Import ITree ITreeFacts.
From Wasm Require Export memory_list operations host.

Import Monads.
Import MonadNotation.

Open Scope monad_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

Section Host.

Variable host_function : eqType.

Let config_tuple := config_tuple host_function.
Let store_record := store_record host_function.

Let executable_host := executable_host host_function.
Variable executable_host_instance : executable_host.
Let host_event := host_event executable_host_instance.

Let host_monad : Monad host_event := host_monad executable_host_instance.
Let host_apply : store_record -> function_type -> host_function -> seq value ->
                 host_event (option (store_record * result)) :=
  @host_apply _ executable_host_instance.

Let sdata_drop := @sdata_drop host_function.
Let selem_drop := @selem_drop host_function.

Section ITreeExtract.
(** Some helper functions to extract an interactive tree to a simple-to-interact-with function,
  in order to reduce the shim. **)

Definition option_of_itree_void {A} (t : itree void1 A) : option A :=
  match observe t with
  | RetF r => Some r (** We got a return. **)
  | TauF i => None (** Exhaustion. **)
  | VisF _ a _ => match a with end (** Void, by definition. **)
  end.

Context {R : Type}.
(** We assume an interpreter, as defined by the end of this file. **)
Variable run : forall (eff : Type -> Type),
  host_event -< eff -> depth -> instance -> config_tuple -> itree eff R.

Variable M : Type -> Type.
Hypothesis FM : Functor.Functor M.
Hypothesis MM : Monad M.
Hypothesis IM : MonadIter M.
Variable convert : host_event ~> M.

Definition from_event_monad : itree host_event ~> M :=
  interp convert.

(** This function instantiates the interpreter [run] to a function that does not
  manipulate interaction trees, making it easier to link it to the OCaml shim. **)
Definition run_extraction d i cfg : M R :=
  from_event_monad (run _ d i cfg).

End ITreeExtract.


(** * Types used by the interpreter **)

Inductive res : Type :=
  | R_crash : res_crash -> res
  | R_trap : res
  | R_value : seq value -> res
  .

Definition res_eq_dec : forall r1 r2 : res, {r1 = r2} + {r1 <> r2}.
Proof. decidable_equality. Defined.

Definition res_eqb (r1 r2 : res) : bool := res_eq_dec r1 r2.
Definition eqresP : Equality.axiom res_eqb :=
  eq_dec_Equality_axiom res_eq_dec.

Canonical Structure res_eqMixin := EqMixin eqresP.
Canonical Structure res_eqType := Eval hnf in EqType res res_eqMixin.

Let res_tuple := res_tuple host_function.
Let config_one_tuple_without_e := config_one_tuple_without_e host_function.

Definition crash_error : res_step := RS_crash C_error.


(** * The interpreter itself. **)

(** An inductive for the [mrec] fixed-point combinator, expressing the signature of the
   functions [run_step_base] and [run_one_step]. **)
Inductive run_stepE : Type -> Type :=
  | call_run_step_base :
    depth -> config_tuple ->
    run_stepE res_tuple
  | call_run_one_step :
    depth -> config_one_tuple_without_e -> administrative_instruction ->
    run_stepE res_tuple
  .

Section RunStep.

(** See ITree/tutorial/Imp.v: these commands are used to enable other events to be mangled in. **)
Context {eff : Type -> Type}.
Context {eff_has_host_event : host_event -< eff}.

Definition run_step_base (call : run_stepE ~> itree (run_stepE +' eff))
    (d : depth) (cfg : config_tuple)
  : itree (run_stepE +' eff) res_tuple :=
  let: (s, (f, es)) := cfg in
  let: (ves, es') := split_vals_e es in (** Framing out constants. **)
  match es' with
  | [::] => ret (s, (f, crash_error))
  | e :: es'' =>
    if e_is_trap e
    then
      if (es'' != [::]) || (ves != [::])
      then ret (s, (f, RS_normal [::AI_trap]))
      else ret (s, (f, crash_error))
    else
      '(s', (f', r)) <- call _ (call_run_one_step d (s, (f, (rev ves))) e) ;;
      if r is RS_normal res
      then ret (s', (f', RS_normal (res ++ es'')))
      else ret (s', (f', r))
  end.

(* Auxiliary definitions for complicated commands *)

Definition BI_ref_is_null_aux s f ves: itree (run_stepE +' eff) res_tuple :=
  if ves is v :: ves' then
    if v is VAL_ref (VAL_ref_null t)
    then ret (s, (f, RS_normal [:: $VAN (VAL_int32 (Wasm_int.int_of_Z i32m (Zpos xH)))]))
    else ret (s, (f, RS_normal [:: $VAN (VAL_int32 (Wasm_int.int_of_Z i32m Z0))]))
  else ret (s, (f, crash_error)).

Definition BI_cvtop_aux s f t2 cvtop t1 sx ves: itree (run_stepE +' eff) res_tuple :=
  match cvtop with
  | CVO_convert =>
    if ves is (VAL_num v) :: ves' then
      if types_agree (T_num t1) (VAL_num v)
      then
        expect (cvt t2 sx v) (fun v' =>
             ret (s, (f, RS_normal (vs_to_es (VAL_num v' :: ves')))))
          (ret (s, (f, RS_normal ((vs_to_es ves') ++ [::AI_trap]))))
      else ret (s, (f, crash_error))
    else ret (s, (f, crash_error))
  | CVO_Reinterpret =>
    if ves is (VAL_num v) :: ves' then
      if types_agree (T_num t1) (VAL_num v) && (sx == None)
      then ret (s, (f, RS_normal (vs_to_es (VAL_num (wasm_deserialise (bits v) t2) :: ves'))))
      else ret (s, (f, crash_error))
    else ret (s, (f, crash_error))
  end.

Definition BI_call_indirect_aux s f x y ves: itree (run_stepE +' eff) res_tuple :=
  if ves is VAL_num (VAL_int32 i) :: ves' then
    match stab_elem s f.(f_inst) x (Wasm_int.nat_of_uint i32m i) with
    | Some r =>
        if r is (VAL_ref_null t) then
          ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
        else
          if r is (VAL_ref_func a) then
            match List.nth_error s.(s_funcs) a with
            | Some cl =>
                if stypes s f.(f_inst) y == Some (cl_type cl)
                then ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_invoke a])))
                else ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
            (* Not Trap because this is not supposed to happen after validation *)
            | None => ret (s, (f, crash_error))
            end
          else
            (* Not Trap because this is not supposed to happen after validation *)
            ret (s, (f, crash_error))
    | None => ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
    end
  else ret (s, (f, crash_error)).

(* Memories *)
Definition BI_memory_grow_aux s f ves: itree (run_stepE +' eff) res_tuple :=
  if ves is VAL_num (VAL_int32 c) :: ves' then
    expect
      (smem_ind s f.(f_inst))
      (fun j =>
         if List.nth_error s.(s_mems) j is Some s_mem_s_j then
           let: l := mem_size s_mem_s_j in
           let: mem' := mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m c) in
           if mem' is Some mem'' then
             ret (upd_s_mem s (set_nth mem'' s.(s_mems) j mem''), (f,
                 RS_normal (vs_to_es (VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat l))) :: ves'))))
           else ret (s, (f, crash_error))
         else ret (s, (f, crash_error)))
      (ret (s, (f, crash_error)))
  else ret (s, (f, crash_error)).

Definition BI_memory_fill_aux s f ves: itree (run_stepE +' eff) res_tuple :=
  if ves is VAL_num (VAL_int32 n) :: val :: VAL_num (VAL_int32 d) :: ves' then
    if smem s f.(f_inst) is Some mem then
      if val is VAL_ref ref then
        let val_d := Wasm_int.N_of_uint i32m d in
        let val_n := Wasm_int.N_of_uint i32m n in
        if (val_d + val_n) > length mem.(meminst_data).(ml_data) then
          ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
        else
          if n == Wasm_int.int_zero i32m then
            ret (s, (f, RS_normal (vs_to_es ves')))
          else
            ret (s, (f, RS_normal (vs_to_es ves' ++ v_to_e_list [::VAL_num (VAL_int32 d); val] ++ AI_basic (BI_store T_i32 (Some Tp_i8) N0 N0) :: v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_d + 1)))); val; VAL_num (VAL_int32 n)] ++ [::AI_basic BI_memory_fill])))
      else ret (s, (f, crash_error))
    else ret (s, (f, crash_error))
  else ret (s, (f, crash_error)).

Definition BI_memory_copy_aux s f ves : itree (run_stepE +' eff) res_tuple :=
  if ves is VAL_num (VAL_int32 n) :: VAL_num (VAL_int32 ss) :: VAL_num (VAL_int32 dd) :: ves' then
    (* Note that there can only be one memory allowed currently, therefore the difference
           in the syntax *)
    if smem s f.(f_inst) is Some mem then
      let val_s := Wasm_int.N_of_uint i32m ss in
      let val_d := Wasm_int.N_of_uint i32m dd in
      let val_n := Wasm_int.N_of_uint i32m n in
      if ((val_s + val_n) > length mem.(meminst_data).(ml_data)) ||
           ((val_d + val_n) > length mem.(meminst_data).(ml_data))
      then
        ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
      else
        if n == Wasm_int.int_zero i32m then
          ret (s, (f, RS_normal (vs_to_es ves')))
        else
          if val_d <= val_s then
            ret (s, (f, RS_normal (vs_to_es ves' ++
                                    v_to_e_list [::VAL_num (VAL_int32 dd); VAL_num (VAL_int32 ss)] ++ [::AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) N0 N0); AI_basic (BI_store T_i32 (Some Tp_i8) N0 N0)] ++
                                    v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_d + 1)))); VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_s + 1)))); VAL_num (VAL_int32 n)] ++ [::AI_basic (BI_memory_copy)])))
          else
            ret (s, (f, RS_normal (vs_to_es ves' ++
                                    v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_d + val_n - 1)))); VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_s + val_n - 1))))] ++ [::AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) N0 N0); AI_basic (BI_store T_i32 (Some Tp_i8) N0 N0)] ++
                                    v_to_e_list [::VAL_num (VAL_int32 dd); VAL_num (VAL_int32 ss); VAL_num (VAL_int32 n)] ++ [::AI_basic (BI_memory_copy)])))
                
    else ret (s, (f, crash_error))
  else ret (s, (f, crash_error)).

Definition BI_memory_init_aux s f x ves : itree (run_stepE +' eff) res_tuple :=
  if ves is VAL_num (VAL_int32 n) :: VAL_num (VAL_int32 ss) :: VAL_num (VAL_int32 dd) :: ves' then
    if smem s f.(f_inst) is Some mem then
      if sdata s f.(f_inst) x is Some data then
        let val_s := Wasm_int.N_of_uint i32m ss in
        let val_d := Wasm_int.N_of_uint i32m dd in
        let val_n := Wasm_int.N_of_uint i32m n in
        if ((val_s + val_n) > length data.(datainst_data)) ||
             ((val_d + val_n) > length mem.(meminst_data).(ml_data))
        then
          ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
        else
          if n == Wasm_int.int_zero i32m then
            ret (s, (f, RS_normal (vs_to_es ves')))
          else
            if lookup_N data.(datainst_data) val_s is Some b then
              ret (s, (f, RS_normal (vs_to_es ves' ++
                                      v_to_e_list [::VAL_num (VAL_int32 dd); VAL_num (wasm_deserialise [::b] T_i32)] ++ [::AI_basic (BI_store T_i32 (Some Tp_i8) N0 N0)] ++
                                      v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_d + 1)))); VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_s + 1)))); VAL_num (VAL_int32 n)] ++ [::AI_basic (BI_memory_init x)])))
            else ret (s, (f, crash_error))
      else ret (s, (f, crash_error))
    else ret (s, (f, crash_error))
  else ret (s, (f, crash_error)).

(* Tables *)
Definition BI_table_grow_aux s f x ves: itree (run_stepE +' eff) res_tuple :=
  if ves is VAL_num (VAL_int32 n) :: val :: ves' then
    if stab s f.(f_inst) x is Some tab then
      if val is VAL_ref ref then
        if stab_grow s f.(f_inst) x (Wasm_int.N_of_uint i32m n) ref is Some s' then
          let sz := Z.of_nat (length tab.(tableinst_elem)) in
          ret (s', (f, RS_normal (vs_to_es (VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m sz)) :: ves))))
        else ret (s, (f, RS_normal (vs_to_es (VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (-1)%Z)) :: ves))))
      else ret (s, (f, crash_error))
    else ret (s, (f, crash_error))
  else ret (s, (f, crash_error)).

Definition BI_table_fill_aux s f x ves: itree (run_stepE +' eff) res_tuple :=
  if ves is VAL_num (VAL_int32 n) :: val :: VAL_num (VAL_int32 i) :: ves' then
    if stab s f.(f_inst) x is Some tab then
      if val is VAL_ref ref then
        let val_i := Wasm_int.N_of_uint i32m i in
        let val_n := Wasm_int.N_of_uint i32m n in
        if (val_i + val_n) > length tab.(tableinst_elem) then
          ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
        else
          if n == Wasm_int.int_zero i32m then
            ret (s, (f, RS_normal (vs_to_es ves')))
          else
            ret (s, (f, RS_normal (vs_to_es ves' ++ v_to_e_list [::VAL_num (VAL_int32 i); val] ++ AI_basic (BI_table_set x) :: v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_i + 1)))); val; VAL_num (VAL_int32 n)] ++ [::AI_basic (BI_table_fill x)])))
      else ret (s, (f, crash_error))
    else ret (s, (f, crash_error))
  else ret (s, (f, crash_error)).

Definition BI_table_copy_aux s f x y ves: itree (run_stepE +' eff) res_tuple :=
  if ves is VAL_num (VAL_int32 n) :: VAL_num (VAL_int32 ss) :: VAL_num (VAL_int32 dd) :: ves' then
    if stab s f.(f_inst) x is Some tabx then
      if stab s f.(f_inst) y is Some taby then
        let val_s := Wasm_int.N_of_uint i32m ss in
        let val_d := Wasm_int.N_of_uint i32m dd in
        let val_n := Wasm_int.N_of_uint i32m n in
        if ((val_s + val_n) > length taby.(tableinst_elem)) ||
             ((val_d + val_n) > length tabx.(tableinst_elem))
        then
          ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
        else
          if n == Wasm_int.int_zero i32m then
            ret (s, (f, RS_normal (vs_to_es ves')))
          else
            if val_d <= val_s then
              ret (s, (f, RS_normal (vs_to_es ves' ++
                                      v_to_e_list [::VAL_num (VAL_int32 dd); VAL_num (VAL_int32 ss)] ++ [::AI_basic (BI_table_get y); AI_basic (BI_table_set x)] ++
                                      v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_d + 1)))); VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_s + 1)))); VAL_num (VAL_int32 n)] ++ [::AI_basic (BI_table_copy x y)])))
            else
              ret (s, (f, RS_normal (vs_to_es ves' ++
                                      v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_d + val_n - 1)))); VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_s + val_n - 1))))] ++ [::AI_basic (BI_table_get y); AI_basic (BI_table_set x)] ++
                                      v_to_e_list [::VAL_num (VAL_int32 dd); VAL_num (VAL_int32 ss); VAL_num (VAL_int32 n)] ++ [::AI_basic (BI_table_copy x y)])))
                  
      else ret (s, (f, crash_error))
    else ret (s, (f, crash_error))
  else ret (s, (f, crash_error)).

Definition BI_table_init_aux s f x y ves: itree (run_stepE +' eff) res_tuple :=
  if ves is VAL_num (VAL_int32 n) :: VAL_num (VAL_int32 ss) :: VAL_num (VAL_int32 dd) :: ves' then
    if stab s f.(f_inst) x is Some tab then
      if selem s f.(f_inst) y is Some elem then
        let val_s := Wasm_int.N_of_uint i32m ss in
        let val_d := Wasm_int.N_of_uint i32m dd in
        let val_n := Wasm_int.N_of_uint i32m n in
        if ((val_s + val_n) > length elem.(eleminst_elem)) ||
             ((val_d + val_n) > length tab.(tableinst_elem))
        then
          ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
        else
          if n == Wasm_int.int_zero i32m then
            ret (s, (f, RS_normal (vs_to_es ves')))
          else
            if lookup_N elem.(eleminst_elem) val_s is Some ref then
              ret (s, (f, RS_normal (vs_to_es ves' ++
                                      v_to_e_list [::VAL_num (VAL_int32 dd); VAL_ref ref] ++ [::AI_basic (BI_table_set x)] ++
                                      v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_d + 1)))); VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_s + 1)))); VAL_num (VAL_int32 n)] ++ [::AI_basic (BI_table_init x y)])))
            else ret (s, (f, crash_error))
      else ret (s, (f, crash_error))
    else ret (s, (f, crash_error))
  else ret (s, (f, crash_error)).

Definition AI_invoke_aux s f i ves: itree (run_stepE +' eff) res_tuple :=
  match List.nth_error s.(s_funcs) i with
  | Some cl =>
      match cl with
      | FC_func_native i (Tf t1s t2s) ts es =>
          let: n := length t1s in
          let: m := length t2s in
          if length ves >= n
          then
            let: (ves', ves'') := split_n ves n in
            let: zs := n_zeros ts in
            ret (s, (f, RS_normal (vs_to_es ves''
                                    ++ [::AI_local m (Build_frame (rev ves' ++ zs) i) (to_e_list es)])))
else ret (s, (f, crash_error))
  | FC_func_host (Tf t1s t2s) h =>
    let: n := length t1s in
    let: m := length t2s in
    if length ves >= n
    then
      let: (ves', ves'') := split_n ves n in
      r <- trigger (host_apply s (Tf t1s t2s) h (rev ves')) ;;
      match r with
      | Some (s', r) =>
          if result_types_agree t2s r
          then
            let: rves := result_to_stack r in
            ret (s', (f, RS_normal (vs_to_es ves'' ++ rves)))
          else ret (s (* FIXME: Why not [s']? *), (f, crash_error))
      | None => ret (s, (f, RS_normal (vs_to_es ves'' ++ [::AI_trap])))
      end
    else ret (s, (f, crash_error))
  end
  | None => ret (s, (f, crash_error))
  end.

Definition run_one_step (call : run_stepE ~> itree (run_stepE +' eff))
      (d : depth) (cfg : config_one_tuple_without_e) (e : administrative_instruction)
    : itree (run_stepE +' eff) res_tuple :=
  let: (s, (f, ves)) := cfg in
  match e with

  (** unop **)
  | AI_basic (BI_unop t op) =>
    if ves is (VAL_num v) :: ves' then
      ret (s, (f, RS_normal (vs_to_es (VAL_num (app_unop_num op v) :: ves'))))
    else ret (s, (f, crash_error))
             
  (** binop **)
  | AI_basic (BI_binop t op) =>
    if ves is (VAL_num v2) :: (VAL_num v1) :: ves' then
      expect (app_binop_num op v1 v2)
             (fun v => ret (s, (f, RS_normal (vs_to_es (VAL_num v :: ves')))))
             (ret (s, (f, RS_normal ((vs_to_es ves') ++ [::AI_trap]))))
    else ret (s, (f, crash_error))
          
  (** testops **)
  | AI_basic (BI_testop T_i32 testop) =>
    if ves is VAL_num (VAL_int32 c) :: ves' then
      ret (s, (f, RS_normal (vs_to_es (VAL_num (VAL_int32 (wasm_bool (@app_testop_i i32t testop c))) :: ves'))))
    else ret (s, (f, crash_error))
  | AI_basic (BI_testop T_i64 testop) =>
    if ves is VAL_num (VAL_int64 c) :: ves' then
      ret (s, (f, RS_normal (vs_to_es (VAL_num (VAL_int32 (wasm_bool (@app_testop_i i64t testop c))) :: ves'))))
    else ret (s, (f, crash_error))
             
  | AI_basic (BI_testop _ _) => ret (s, (f, crash_error))

  (** relops **)
  | AI_basic (BI_relop t op) =>
    if ves is (VAL_num v2) :: (VAL_num v1) :: ves' then
      ret (s, (f, RS_normal (vs_to_es (VAL_num (VAL_int32 (wasm_bool (app_relop_num op v1 v2))) :: ves'))))
    else ret (s, (f, crash_error))
             
  (** convert and reinterpret **)
  | AI_basic (BI_cvtop t2 cvtop t1 sx) =>
      BI_cvtop_aux s f t2 cvtop t1 sx ves

  (** reference instructions **)
  | AI_basic BI_ref_is_null =>
      BI_ref_is_null_aux s f ves

  | AI_basic (BI_ref_func x) =>
      if List.nth_error f.(f_inst).(inst_funcs) x is Some a 
      then ret (s, (f, RS_normal [:: AI_ref a]))
      else ret (s, (f, crash_error))
               
  (** control-flow instructions **)
  | AI_basic BI_unreachable => ret (s, (f, RS_normal ((vs_to_es ves) ++ [::AI_trap])))
  | AI_basic BI_nop => ret (s, (f, RS_normal (vs_to_es ves)))
  | AI_basic BI_drop =>
    if ves is v :: ves' then
      ret (s, (f, RS_normal (vs_to_es ves')))
    else ret (s, (f, crash_error))

  | AI_basic (BI_select ot) =>
    if ves is (VAL_num (VAL_int32 c)) :: v2 :: v1 :: ves' then
      if c == Wasm_int.int_zero i32m
      then ret (s, (f, RS_normal (vs_to_es (v2 :: ves'))))
      else ret (s, (f, RS_normal (vs_to_es (v1 :: ves'))))
    else ret (s, (f, crash_error))

  | AI_basic (BI_block tb es) =>
    if expand f.(f_inst) tb is Some (Tf t1s t2s) then
      if length ves >= length t1s
      then
        let: (ves', ves'')  := split_n ves (length t1s) in
        ret (s, (f, RS_normal (vs_to_es ves''
                              ++ [::AI_label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)])))
      else ret (s, (f, crash_error))
    else ret (s, (f, crash_error))

  | AI_basic (BI_loop tb es) =>
    if expand f.(f_inst) tb is Some (Tf t1s t2s) then
      if length ves >= length t1s
      then
        let: (ves', ves'') := split_n ves (length t1s) in
        ret (s, (f, RS_normal (vs_to_es ves''
                              ++ [::AI_label (length t1s) [::AI_basic (BI_loop tb es)]
                                      (vs_to_es ves' ++ to_e_list es)])))
      else ret (s, (f, crash_error))
    else ret (s, (f, crash_error))

  | AI_basic (BI_if tf es1 es2) =>
    if ves is VAL_num (VAL_int32 c) :: ves' then
      if c == Wasm_int.int_zero i32m
      then ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_block tf es2)])))
      else ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_block tf es1)])))
    else ret (s, (f, crash_error))

  | AI_basic (BI_br j) => ret (s, (f, RS_break j ves))
  | AI_basic (BI_br_if j) =>
    if ves is VAL_num (VAL_int32 c) :: ves' then
      if c == Wasm_int.int_zero i32m
      then ret (s, (f, RS_normal (vs_to_es ves')))
      else ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br j)])))
    else ret (s, (f, crash_error))
  | AI_basic (BI_br_table js j) =>
    if ves is VAL_num (VAL_int32 c) :: ves' then
      let: k := Wasm_int.nat_of_uint i32m c in
      if k < length js
      then
        expect (List.nth_error js k) (fun js_at_k =>
            ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br js_at_k)]))))
          (ret (s, (f, crash_error)))
      else ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br j)])))
    else ret (s, (f, crash_error))

  | AI_basic (BI_call j) =>
    if List.nth_error f.(f_inst).(inst_funcs) j is Some a then
      ret (s, (f, RS_normal (vs_to_es ves ++ [::AI_invoke a])))
    else ret (s, (f, crash_error))

  | AI_basic (BI_call_indirect x y) =>
      BI_call_indirect_aux s f x y ves

  | AI_basic BI_return => ret (s, (f, RS_return ves))

  | AI_basic (BI_local_get j) =>
    if j < length f.(f_locs)
    then
      expect (List.nth_error f.(f_locs) j) (fun vs_at_j =>
          ret (s, (f, RS_normal (vs_to_es (vs_at_j :: ves)))))
        (ret (s, (f, crash_error)))
    else ret (s, (f, crash_error))

  | AI_basic (BI_local_set j) =>
    if ves is v :: ves' then
      if j < length f.(f_locs)
      then ret (s, (Build_frame (set_nth v f.(f_locs) j v) f.(f_inst), RS_normal (vs_to_es ves')))
      else ret (s, (f, crash_error))
    else ret (s, (f, crash_error))

  | AI_basic (BI_local_tee j) =>
    if ves is v :: ves' then
      ret (s, (f, RS_normal (vs_to_es (v :: ves) ++ [::AI_basic (BI_local_set j)])))
    else ret (s, (f, crash_error))

  | AI_basic (BI_global_get j) =>
    if sglob_val s f.(f_inst) j is Some xx
    then ret (s, (f, RS_normal (vs_to_es (xx :: ves))))
    else ret (s, (f, crash_error))

  | AI_basic (BI_global_set j) =>
    if ves is v :: ves' then
      if supdate_glob s f.(f_inst) j v is Some xx
      then ret (xx, (f, RS_normal (vs_to_es ves')))
      else ret (s, (f, crash_error))
    else ret (s, (f, crash_error))
             
    | AI_basic (BI_load t None a off) =>
      if ves is VAL_num (VAL_int32 k) :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load (mem_s_j) (Wasm_int.N_of_uint i32m k) off (tnum_length t))
                 (fun bs => ret (s, (f, RS_normal (vs_to_es (VAL_num (wasm_deserialise bs t) :: ves')))))
                 (ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap]))))
             else ret (s, (f, crash_error)))
          (ret (s, (f, crash_error)))
      else ret (s, (f, crash_error))

    | AI_basic (BI_load t (Some (tp, sx)) a off) =>
      if ves is VAL_num (VAL_int32 k) :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load_packed sx (mem_s_j) (Wasm_int.N_of_uint i32m k) off (tp_length tp) (tnum_length t))
                 (fun bs => ret (s, (f, RS_normal (vs_to_es (VAL_num (wasm_deserialise bs t) :: ves')))))
                 (ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap]))))
             else ret (s, (f, crash_error)))
          (ret (s, (f, crash_error)))
      else ret (s, (f, crash_error))

    | AI_basic (BI_store t None a off) =>
      if ves is (VAL_num v) :: VAL_num (VAL_int32 k) :: ves' then
        if types_agree (T_num t) (VAL_num v)
        then
          expect
            (smem_ind s f.(f_inst))
            (fun j =>
               if List.nth_error s.(s_mems) j is Some mem_s_j then
                 expect
                   (store mem_s_j (Wasm_int.N_of_uint i32m k) off (bits v) (tnum_length t))
                   (fun mem' =>
                      (ret (upd_s_mem s (set_nth mem' s.(s_mems) j mem'), (f, RS_normal (vs_to_es ves')))))
                   (ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap]))))
               else ret (s, (f, crash_error)))
            (ret (s, (f, crash_error)))
        else ret (s, (f, crash_error))
      else ret (s, (f, crash_error))

    | AI_basic (BI_store t (Some tp) a off) =>
      if ves is (VAL_num v) :: VAL_num (VAL_int32 k) :: ves' then
        if types_agree (T_num t) (VAL_num v)
        then
          expect
            (smem_ind s f.(f_inst))
            (fun j =>
               if List.nth_error s.(s_mems) j is Some mem_s_j then
                 expect
                   (store_packed mem_s_j (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp))
                   (fun mem' =>
                      (ret (upd_s_mem s (set_nth mem' s.(s_mems) j mem'), (f, RS_normal (vs_to_es ves')))))
                   (ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap]))))
               else ret (s, (f, crash_error)))
            (ret (s, (f, crash_error)))
        else ret (s, (f, crash_error))
      else ret (s, (f, crash_error))

    | AI_basic BI_memory_size =>
      expect
        (smem_ind s f.(f_inst))
        (fun j =>
           if List.nth_error s.(s_mems) j is Some s_mem_s_j then
             (ret (s, (f, RS_normal (vs_to_es (VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j)))) :: ves)))))
           else ret (s, (f, crash_error)))
        (ret (s, (f, crash_error)))
        
  | AI_basic BI_memory_grow =>
      BI_memory_grow_aux s f ves
               
  | AI_basic BI_memory_fill =>
      BI_memory_fill_aux s f ves
               
  | AI_basic (BI_memory_copy) =>
      BI_memory_copy_aux s f ves
               
  | AI_basic (BI_memory_init x) =>
      BI_memory_init_aux s f x ves
                         
  | AI_basic (BI_data_drop x) =>
      if sdata_drop s f.(f_inst) x is Some s' then
        ret (s', (f, RS_normal (vs_to_es ves)))
      else ret (s, (f, crash_error))
               

    (* Table instructions *)
    | AI_basic (BI_table_get x) =>
      if ves is VAL_num (VAL_int32 i) :: ves' then
        if stab s f.(f_inst) x is Some tab then
          if (Wasm_int.nat_of_uint i32m i) >= length tab.(tableinst_elem) then
            ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
            else
            if List.nth_error tab.(tableinst_elem) (Wasm_int.nat_of_uint i32m i) is Some val then
              ret (s, (f, RS_normal (vs_to_es (VAL_ref val :: ves'))))
              else ret (s, (f, crash_error))
          else ret (s, (f, crash_error))
      else ret (s, (f, crash_error))
    
    | AI_basic (BI_table_set x) =>
      if ves is val :: VAL_num (VAL_int32 i) :: ves' then
        if stab s f.(f_inst) x is Some tab then
          if val is VAL_ref ref then
            if (Wasm_int.nat_of_uint i32m i) >= length tab.(tableinst_elem) then
              ret (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
            else
              if stab_update s f.(f_inst) x (Wasm_int.nat_of_uint i32m i) ref is Some s' then
                ret (s', (f, RS_normal (vs_to_es ves)))
            else ret (s, (f, crash_error))
          else ret (s, (f, crash_error))
        else ret (s, (f, crash_error))
      else ret (s, (f, crash_error))

               
    | AI_basic (BI_table_size x) =>
        if stab s f.(f_inst) x is Some tab then
          let sz := Z.of_nat (length tab.(tableinst_elem)) in
            ret (s, (f, RS_normal (vs_to_es (VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m sz)) :: ves))))
        else ret (s, (f, crash_error))
                 
  | AI_basic (BI_table_grow x) =>
      BI_table_fill_aux s f x ves
               
  | AI_basic (BI_table_fill x) =>
      BI_table_fill_aux s f x ves
               
  | AI_basic (BI_table_copy x y) =>
      BI_table_copy_aux s f x y ves

  | AI_basic (BI_table_init x y) =>
      BI_table_init_aux s f x y ves

    | AI_basic (BI_elem_drop x) =>
      if selem_drop s f.(f_inst) x is Some s' then
        ret (s', (f, RS_normal (vs_to_es ves)))
      else ret (s, (f, crash_error))
            
    
               
    (* These values are not supposed to get into here *)
    | AI_basic (BI_const_num _) => ret (s, (f, crash_error))
    | AI_basic (BI_const_vec _) => ret (s, (f, crash_error))
    | AI_basic (BI_ref_null _) => ret (s, (f, crash_error))                    
    | AI_ref _ => ret (s, (f, crash_error))                    
    | AI_ref_extern _ => ret (s, (f, crash_error))                    

  | AI_invoke i =>
      AI_invoke_aux s f i ves

  | AI_label ln les es =>
    if es_is_trap es
    then ret (s, (f, RS_normal (vs_to_es ves ++ [::AI_trap])))
    else
      if const_list es
      then ret (s, (f, RS_normal (vs_to_es ves ++ es)))
      else
      '(s', (f', res)) <- call res_tuple (call_run_step_base d (s, (f, es))) ;;
      match res with
      | RS_break 0 bvs =>
        if length bvs >= ln
        then ret (s', (f', RS_normal ((vs_to_es ((take ln bvs) ++ ves)) ++ les)))
        else ret (s', (f', crash_error))
      | RS_break (n.+1) bvs => ret (s', (f', RS_break n bvs))
      | RS_return rvs => ret (s', (f', RS_return rvs))
      | RS_normal es' =>
        ret (s', (f', RS_normal (vs_to_es ves ++ [::AI_label ln les es'])))
      | RS_crash error => ret (s', (f', RS_crash error))
      end

  | AI_local ln f0 es =>
    if es_is_trap es
    then ret (s, (f, RS_normal (vs_to_es ves ++ [::AI_trap])))
    else
      if const_list es
      then
        if length es == ln
        then ret (s, (f, RS_normal (vs_to_es ves ++ es)))
        else ret (s, (f, crash_error))
      else
        '(s', (f', res)) <- call res_tuple (call_run_step_base d (s, (f0, es))) ;;
        match res return itree (run_stepE +' eff) res_tuple with
        | RS_return rvs =>
          if length rvs >= ln
          then ret (s', (f, RS_normal (vs_to_es (take ln rvs ++ ves))))
          else ret (s', (f, crash_error))
        | RS_normal es' =>
          ret (s', (f, RS_normal (vs_to_es ves ++ [::AI_local ln f' es'])))
        | RS_crash error => ret (s', (f, RS_crash error))
        | RS_break _ _ => ret (s', (f, crash_error))
        end

  | AI_trap => ret (s, (f, crash_error))
  end.

Definition run_step_call : run_stepE ~> itree eff :=
  mrec (fun T (f : run_stepE T) =>
    let call _ f := trigger f in
    match f with
    | call_run_step_base d cgf =>
      run_step_base call d cgf
    | call_run_one_step d cgf e =>
      run_one_step call d cgf e
    end).

(** Enough fuel so that [run_one_step] does not run out of exhaustion. **)
Definition run_one_step_fuel : administrative_instruction -> nat.
Proof.
  move=> es. induction es using administrative_instruction_rect';
    let rec aux v :=
      lazymatch goal with
      | F : TProp.Forall _ _ |- _ =>
        apply TProp.max in F;
        move: F;
        let n := fresh "n" in
        move=> n;
        aux (n + v)
      | |- _ => exact (v.+1)
      end in
    aux (1 : nat).
Defined.

(** Enough fuel so that [run_step] does not run out of exhaustion. **)
Definition run_step_fuel (cfg : config_tuple) : nat :=
  let: (s, (vs, es)) := cfg in
  1 + List.fold_left max (List.map run_one_step_fuel es) 0.

(** [run_step] is defined by calling [run_step_base], whilst burning enough fuel
   for it to be fully computed. **)
Definition run_step (d : depth) (inst : instance) (cfg : config_tuple) : itree eff res_tuple :=
  burn (run_step_fuel cfg) (run_step_call (call_run_step_base d cfg)).

End RunStep.

Section Run.

Context {eff : Type -> Type}.
Context {eff_has_host_event : host_event -< eff}.

Definition run_v : depth -> instance -> config_tuple -> itree eff (store_record * res) :=
  let run_v :=
    rec-fix run_v (d, i, (s, (vs, es))) :=
      if es_is_trap es
      then ret (s, R_trap)
      else
      if const_list es
      then ret (s, R_value (fst (split_vals_e es)))
        else
          '(s', (vs', r)) <- run_step d i (s, (vs, es)) ;;
          match r with
          | RS_normal es' => run_v (d, i, (s', (vs', es')))
          | RS_crash error => ret (s, R_crash error)
          | _ => ret (s, R_crash C_error)
          end in
  fun d i cfg => run_v (d, i, cfg).

End Run.

Definition run_step_extraction_eqType := run_extraction (@run_step).
Definition run_v_extraction_eqType := run_extraction (@run_v).

End Host.

(* Our current assumptions consist of the classical axiom [Classical_Prop.classic],
  as well as Flocq's axioms.
  The classical axiom comes from our definitions of [f32] and [f64] in numerics.v,
  that use functions (like [Binary.binary_normalize]) based on this axiom.
[[
Print Assumptions run_step.
]]
*)


(** The following module is designed to fit OCaml’s types, and thus to better extract. **)

(** First, due to universe inconsistencies, we are not allowed to extract directly to
  the same monad [host_event].
  We thus assume another monad with the right assumption.
  Again, this module type is designed to extract nicely to OCaml. **)
Module Type TargetMonad (EH : Executable_Host).

Parameter monad : Type -> Type.
Parameter monad_ret : forall t : Type, t -> monad t.
Parameter monad_bind : forall t u : Type, monad t -> (t -> monad u) -> monad u.
Parameter monad_iter : forall R I : Type, (I -> monad (I + R)%type) -> I -> monad R.

Parameter convert : EH.host_event ~> monad.

End TargetMonad.

(** The following module converts the module type above into a proper Coq monad. **)
Module convert_target_monad (EH : Executable_Host) (M : TargetMonad EH).

Export M.

Definition monad_monad : Monad monad := {|
    ret := monad_ret ;
    bind := monad_bind
  |}.

Definition monad_Iter : MonadIter monad := monad_iter.

Definition monad_functor := Functor_Monad (M := monad_monad).

End convert_target_monad.

Module Interpreter (EH : Executable_Host) (TM : TargetMonad EH).

Module Exec := convert_to_executable_host EH.
Import Exec.

Module Target := convert_target_monad EH TM.
Import Target.

Definition run_step
  : depth -> instance -> config_tuple -> monad res_tuple :=
  @run_step_extraction_eqType host_function executable_host_instance
    monad monad_functor monad_monad monad_Iter convert.
Definition run_v
  : depth -> instance -> config_tuple -> monad (store_record * res) :=
  @run_v_extraction_eqType host_function executable_host_instance
    monad monad_functor monad_monad monad_Iter convert.

(** State whether a list of administrative instruction is a final value. **)
Definition is_const_list : list administrative_instruction -> option (list value) :=
  @those_const_list.

(** A useful definition for converting [itree] to [option] without executing anything,
  assuming a way to remove events.
  Warning: this breaks the semantics of [itree]s by mapping any event to [None].
  The function [tr] has an unusual type [forall T A, E T -> A] instead of [E ~> void1],
  otherwise it is simply and brutally removed in the extraction process. **)
Definition itree_to_option (E : Type -> Type) (tr : forall T A, E T -> A) :
    forall R, itree E R -> option R :=
  fun _ tree => option_of_itree_void (translate (fun T => tr T _) tree).

End Interpreter.

