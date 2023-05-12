(** Wasm interpreter **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Wasm Require Import common.
From Coq Require Import ZArith.BinInt.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export memory_list operations host.
Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

Inductive res : Type :=
| R_crash : res_crash -> res
| R_trap : res
| R_value : list value -> res.

Definition res_eq_dec : forall r1 r2 : res, {r1 = r2} + {r1 <> r2}.
Proof. decidable_equality. Defined.

Definition res_eqb (r1 r2 : res) : bool := res_eq_dec r1 r2.
Definition eqresP : Equality.axiom res_eqb :=
  eq_dec_Equality_axiom res_eq_dec.

Canonical Structure res_eqMixin := EqMixin eqresP.
Canonical Structure res_eqType := Eval hnf in EqType res res_eqMixin.

Section Host_func.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record := store_record host_function.
Let host_state := host_state host_instance.
Let res_tuple := res_tuple host_function.
Let config_tuple := config_tuple host_function.
Let config_one_tuple_without_e := config_one_tuple_without_e host_function.


Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                       (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).

Definition crash_error := RS_crash C_error.

Definition depth := nat.

Definition fuel := nat.

(* Auxiliary definitions for complicated commands *)

Definition BI_ref_is_null_aux s f ves: res_tuple :=
  if ves is v :: ves' then
    if v is VAL_ref (VAL_ref_null t)
    then (s, (f, RS_normal [:: $VAN (VAL_int32 (Wasm_int.int_of_Z i32m (Zpos xH)))]))
    else (s, (f, RS_normal [:: $VAN (VAL_int32 (Wasm_int.int_of_Z i32m Z0))]))
  else (s, (f, crash_error)).

Definition BI_cvtop_aux s f t2 cvtop t1 sx ves: res_tuple :=
  match cvtop with
  | CVO_convert =>
    if ves is (VAL_num v) :: ves' then
      if types_agree (T_num t1) (VAL_num v)
      then
        expect (cvt t2 sx v) (fun v' =>
             (s, (f, RS_normal (vs_to_es (VAL_num v' :: ves')))))
          ((s, (f, RS_normal ((vs_to_es ves') ++ [::AI_trap]))))
      else (s, (f, crash_error))
    else (s, (f, crash_error))
  | CVO_Reinterpret =>
    if ves is (VAL_num v) :: ves' then
      if types_agree (T_num t1) (VAL_num v) && (sx == None)
      then (s, (f, RS_normal (vs_to_es (VAL_num (wasm_deserialise (bits v) t2) :: ves'))))
      else (s, (f, crash_error))
    else (s, (f, crash_error))
  end.

Definition BI_call_indirect_aux s f x y ves: res_tuple :=
  if ves is VAL_num (VAL_int32 i) :: ves' then
    match stab_elem s f.(f_inst) x (Wasm_int.nat_of_uint i32m i) with
    | Some r =>
        if r is (VAL_ref_null t) then
          (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
        else
          if r is (VAL_ref_func a) then
            match List.nth_error s.(s_funcs) a with
            | Some cl =>
                if stypes s f.(f_inst) y == Some (cl_type cl)
                then (s, (f, RS_normal (vs_to_es ves' ++ [::AI_invoke a])))
                else (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
            (* Not Trap because this is not supposed to happen after validation *)
            | None => (s, (f, crash_error))
            end
          else
            (* Not Trap because this is not supposed to happen after validation *)
            (s, (f, crash_error))
    | None => (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
    end
  else (s, (f, crash_error)).

(* Memories *)
Definition BI_memory_grow_aux s f ves: res_tuple :=
  if ves is VAL_num (VAL_int32 c) :: ves' then
    expect
      (smem_ind s f.(f_inst))
      (fun j =>
         if List.nth_error s.(s_mems) j is Some s_mem_s_j then
           let: l := mem_size s_mem_s_j in
           let: mem' := mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m c) in
           if mem' is Some mem'' then
             (upd_s_mem s (set_nth mem'' s.(s_mems) j mem''), (f,
                 RS_normal (vs_to_es (VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat l))) :: ves'))))
           else (s, (f, crash_error))
         else (s, (f, crash_error)))
      ((s, (f, crash_error)))
  else (s, (f, crash_error)).

Definition BI_memory_fill_aux s f ves: res_tuple :=
  if ves is VAL_num (VAL_int32 n) :: val :: VAL_num (VAL_int32 d) :: ves' then
    if smem s f.(f_inst) is Some mem then
      if val is VAL_ref ref then
        let val_d := Wasm_int.N_of_uint i32m d in
        let val_n := Wasm_int.N_of_uint i32m n in
        if (val_d + val_n) > length mem.(meminst_data).(ml_data) then
          (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
        else
          if n == Wasm_int.int_zero i32m then
            (s, (f, RS_normal (vs_to_es ves')))
          else
            (s, (f, RS_normal (vs_to_es ves' ++ v_to_e_list [::VAL_num (VAL_int32 d); val] ++ AI_basic (BI_store T_i32 (Some Tp_i8) N0 N0) :: v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_d + 1)))); val; VAL_num (VAL_int32 n)] ++ [::AI_basic BI_memory_fill])))
      else (s, (f, crash_error))
    else (s, (f, crash_error))
  else (s, (f, crash_error)).

Definition BI_memory_copy_aux s f ves : res_tuple :=
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
        (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
      else
        if n == Wasm_int.int_zero i32m then
          (s, (f, RS_normal (vs_to_es ves')))
        else
          if val_d <= val_s then
            (s, (f, RS_normal (vs_to_es ves' ++
                                    v_to_e_list [::VAL_num (VAL_int32 dd); VAL_num (VAL_int32 ss)] ++ [::AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) N0 N0); AI_basic (BI_store T_i32 (Some Tp_i8) N0 N0)] ++
                                    v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_d + 1)))); VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_s + 1)))); VAL_num (VAL_int32 n)] ++ [::AI_basic (BI_memory_copy)])))
          else
            (s, (f, RS_normal (vs_to_es ves' ++
                                    v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_d + val_n - 1)))); VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_s + val_n - 1))))] ++ [::AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) N0 N0); AI_basic (BI_store T_i32 (Some Tp_i8) N0 N0)] ++
                                    v_to_e_list [::VAL_num (VAL_int32 dd); VAL_num (VAL_int32 ss); VAL_num (VAL_int32 n)] ++ [::AI_basic (BI_memory_copy)])))
                
    else (s, (f, crash_error))
  else (s, (f, crash_error)).

Definition BI_memory_init_aux s f x ves : res_tuple :=
  if ves is VAL_num (VAL_int32 n) :: VAL_num (VAL_int32 ss) :: VAL_num (VAL_int32 dd) :: ves' then
    if smem s f.(f_inst) is Some mem then
      if sdata s f.(f_inst) x is Some data then
        let val_s := Wasm_int.N_of_uint i32m ss in
        let val_d := Wasm_int.N_of_uint i32m dd in
        let val_n := Wasm_int.N_of_uint i32m n in
        if ((val_s + val_n) > length data.(datainst_data)) ||
             ((val_d + val_n) > length mem.(meminst_data).(ml_data))
        then
          (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
        else
          if n == Wasm_int.int_zero i32m then
            (s, (f, RS_normal (vs_to_es ves')))
          else
            if lookup_N data.(datainst_data) val_s is Some b then
              (s, (f, RS_normal (vs_to_es ves' ++
                                      v_to_e_list [::VAL_num (VAL_int32 dd); VAL_num (wasm_deserialise [::b] T_i32)] ++ [::AI_basic (BI_store T_i32 (Some Tp_i8) N0 N0)] ++
                                      v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_d + 1)))); VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_s + 1)))); VAL_num (VAL_int32 n)] ++ [::AI_basic (BI_memory_init x)])))
            else (s, (f, crash_error))
      else (s, (f, crash_error))
    else (s, (f, crash_error))
  else (s, (f, crash_error)).

(* Tables *)
Definition BI_table_grow_aux s f x ves: res_tuple :=
  if ves is VAL_num (VAL_int32 n) :: val :: ves' then
    if stab s f.(f_inst) x is Some tab then
      if val is VAL_ref ref then
        if stab_grow s f.(f_inst) x (Wasm_int.N_of_uint i32m n) ref is Some s' then
          let sz := Z.of_nat (length tab.(tableinst_elem)) in
          (s', (f, RS_normal (vs_to_es (VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m sz)) :: ves))))
        else (s, (f, RS_normal (vs_to_es (VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (-1)%Z)) :: ves))))
      else (s, (f, crash_error))
    else (s, (f, crash_error))
  else (s, (f, crash_error)).

Definition BI_table_fill_aux s f x ves: res_tuple :=
  if ves is VAL_num (VAL_int32 n) :: val :: VAL_num (VAL_int32 i) :: ves' then
    if stab s f.(f_inst) x is Some tab then
      if val is VAL_ref ref then
        let val_i := Wasm_int.N_of_uint i32m i in
        let val_n := Wasm_int.N_of_uint i32m n in
        if (val_i + val_n) > length tab.(tableinst_elem) then
          (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
        else
          if n == Wasm_int.int_zero i32m then
            (s, (f, RS_normal (vs_to_es ves')))
          else
            (s, (f, RS_normal (vs_to_es ves' ++ v_to_e_list [::VAL_num (VAL_int32 i); val] ++ AI_basic (BI_table_set x) :: v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_i + 1)))); val; VAL_num (VAL_int32 n)] ++ [::AI_basic (BI_table_fill x)])))
      else (s, (f, crash_error))
    else (s, (f, crash_error))
  else (s, (f, crash_error)).

Definition BI_table_copy_aux s f x y ves: res_tuple :=
  if ves is VAL_num (VAL_int32 n) :: VAL_num (VAL_int32 ss) :: VAL_num (VAL_int32 dd) :: ves' then
    if stab s f.(f_inst) x is Some tabx then
      if stab s f.(f_inst) y is Some taby then
        let val_s := Wasm_int.N_of_uint i32m ss in
        let val_d := Wasm_int.N_of_uint i32m dd in
        let val_n := Wasm_int.N_of_uint i32m n in
        if ((val_s + val_n) > length taby.(tableinst_elem)) ||
             ((val_d + val_n) > length tabx.(tableinst_elem))
        then
          (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
        else
          if n == Wasm_int.int_zero i32m then
            (s, (f, RS_normal (vs_to_es ves')))
          else
            if val_d <= val_s then
              (s, (f, RS_normal (vs_to_es ves' ++
                                      v_to_e_list [::VAL_num (VAL_int32 dd); VAL_num (VAL_int32 ss)] ++ [::AI_basic (BI_table_get y); AI_basic (BI_table_set x)] ++
                                      v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_d + 1)))); VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_s + 1)))); VAL_num (VAL_int32 n)] ++ [::AI_basic (BI_table_copy x y)])))
            else
              (s, (f, RS_normal (vs_to_es ves' ++
                                      v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_d + val_n - 1)))); VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_s + val_n - 1))))] ++ [::AI_basic (BI_table_get y); AI_basic (BI_table_set x)] ++
                                      v_to_e_list [::VAL_num (VAL_int32 dd); VAL_num (VAL_int32 ss); VAL_num (VAL_int32 n)] ++ [::AI_basic (BI_table_copy x y)])))
                  
      else (s, (f, crash_error))
    else (s, (f, crash_error))
  else (s, (f, crash_error)).

Definition BI_table_init_aux s f x y ves: res_tuple :=
  if ves is VAL_num (VAL_int32 n) :: VAL_num (VAL_int32 ss) :: VAL_num (VAL_int32 dd) :: ves' then
    if stab s f.(f_inst) x is Some tab then
      if selem s f.(f_inst) y is Some elem then
        let val_s := Wasm_int.N_of_uint i32m ss in
        let val_d := Wasm_int.N_of_uint i32m dd in
        let val_n := Wasm_int.N_of_uint i32m n in
        if ((val_s + val_n) > length elem.(eleminst_elem)) ||
             ((val_d + val_n) > length tab.(tableinst_elem))
        then
          (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))
        else
          if n == Wasm_int.int_zero i32m then
            (s, (f, RS_normal (vs_to_es ves')))
          else
            if lookup_N elem.(eleminst_elem) val_s is Some ref then
              (s, (f, RS_normal (vs_to_es ves' ++
                                      v_to_e_list [::VAL_num (VAL_int32 dd); VAL_ref ref] ++ [::AI_basic (BI_table_set x)] ++
                                      v_to_e_list [::VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_d + 1)))); VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (val_s + 1)))); VAL_num (VAL_int32 n)] ++ [::AI_basic (BI_table_init x y)])))
            else (s, (f, crash_error))
      else (s, (f, crash_error))
    else (s, (f, crash_error))
  else (s, (f, crash_error)).

Definition AI_invoke_aux hs s f i ves: host_state * res_tuple :=
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
            (hs, (s, (f, RS_normal (vs_to_es ves''
                                    ++ [::AI_local m (Build_frame (rev ves' ++ zs) i) (to_e_list es)]))))
else (hs, (s, (f, crash_error)))
  | FC_func_host (Tf t1s t2s) h =>
    let: n := length t1s in
    let: m := length t2s in
    if length ves >= n
    then
      let: (ves', ves'') := split_n ves n in
      match host_application_impl hs s (Tf t1s t2s) h (rev ves') with
      | (hs', Some (s', r)) =>
          if result_types_agree t2s r
          then
            let: rves := result_to_stack r in
            (hs', (s', (f, RS_normal (vs_to_es ves'' ++ rves))))
          else (hs', (s (* FIXME: Why not [s']? *), (f, crash_error)))
      | (hs', None) => (hs', (s, (f, RS_normal (vs_to_es ves'' ++ [::AI_trap]))))
      end
    else (hs, (s, (f, crash_error)))
  end
  | None => (hs, (s, (f, crash_error)))
  end.

Fixpoint run_step_with_fuel (fuel : fuel) (d : depth) (cfg : host_state * config_tuple) : host_state * res_tuple :=
  let: (hs, (s, (f, es))) := cfg in
  match fuel with
  | 0 => (hs, (s, (f, RS_crash C_exhaustion)))
  | fuel.+1 =>
    let: (ves, es') := split_vals_e es in (** Framing out constants. **)
    match es' with
    | [::] => (hs, (s, (f, crash_error)))
    | e :: es'' =>
      if e_is_trap e
      then
        if (es'' != [::]) || (ves != [::])
        then (hs, (s, (f, RS_normal [::AI_trap])))
        else (hs, (s, (f, crash_error)))
      else
        let: (hs', (s', (f', r))) := run_one_step fuel d (hs, (s, (f, (rev ves)))) e in
        if r is RS_normal res
        then (hs', (s', (f', RS_normal (res ++ es''))))
        else (hs', (s', (f', r)))
    end
  end
    
with run_one_step (fuel : fuel) (d : depth) (cfg : host_state * config_one_tuple_without_e) (e : administrative_instruction) : host_state * res_tuple :=
  let: (hs, (s, (f, ves))) := cfg in
  match fuel with
  | 0 => (hs, (s, (f, RS_crash C_exhaustion)))
  | fuel.+1 =>
  match e with

  (** unop **)
  | AI_basic (BI_unop t op) =>
    if ves is (VAL_num v) :: ves' then
      (hs, (s, (f, RS_normal (vs_to_es (VAL_num (app_unop_num op v) :: ves')))))
    else (hs, (s, (f, crash_error)))
             
  (** binop **)
  | AI_basic (BI_binop t op) =>
    if ves is (VAL_num v2) :: (VAL_num v1) :: ves' then
      expect (app_binop_num op v1 v2)
             (fun v => (hs, (s, (f, RS_normal (vs_to_es (VAL_num v :: ves'))))))
             (hs, ((s, (f, RS_normal ((vs_to_es ves') ++ [::AI_trap])))))
    else (hs, (s, (f, crash_error)))
          
  (** testops **)
  | AI_basic (BI_testop T_i32 testop) =>
    if ves is VAL_num (VAL_int32 c) :: ves' then
      (hs, (s, (f, RS_normal (vs_to_es (VAL_num (VAL_int32 (wasm_bool (@app_testop_i i32t testop c))) :: ves')))))
    else (hs, (s, (f, crash_error)))
  | AI_basic (BI_testop T_i64 testop) =>
    if ves is VAL_num (VAL_int64 c) :: ves' then
      (hs, (s, (f, RS_normal (vs_to_es (VAL_num (VAL_int32 (wasm_bool (@app_testop_i i64t testop c))) :: ves')))))
    else (hs, (s, (f, crash_error)))
             
  | AI_basic (BI_testop _ _) => (hs, (s, (f, crash_error)))

  (** relops **)
  | AI_basic (BI_relop t op) =>
    if ves is (VAL_num v2) :: (VAL_num v1) :: ves' then
      (hs, (s, (f, RS_normal (vs_to_es (VAL_num (VAL_int32 (wasm_bool (app_relop_num op v1 v2))) :: ves')))))
    else (hs, (s, (f, crash_error)))
             
  (** convert and reinterpret **)
  | AI_basic (BI_cvtop t2 cvtop t1 sx) =>
      (hs, BI_cvtop_aux s f t2 cvtop t1 sx ves)

  (** reference instructions **)
  | AI_basic BI_ref_is_null =>
      (hs, BI_ref_is_null_aux s f ves)

  | AI_basic (BI_ref_func x) =>
      if List.nth_error f.(f_inst).(inst_funcs) x is Some a 
      then (hs, (s, (f, RS_normal [:: AI_ref a])))
      else (hs, (s, (f, crash_error)))
               
  (** control-flow instructions **)
  | AI_basic BI_unreachable => (hs, (s, (f, RS_normal ((vs_to_es ves) ++ [::AI_trap]))))
  | AI_basic BI_nop => (hs, (s, (f, RS_normal (vs_to_es ves))))
  | AI_basic BI_drop =>
    if ves is v :: ves' then
      (hs, (s, (f, RS_normal (vs_to_es ves'))))
    else (hs, (s, (f, crash_error)))

  | AI_basic (BI_select ot) =>
    if ves is (VAL_num (VAL_int32 c)) :: v2 :: v1 :: ves' then
      if c == Wasm_int.int_zero i32m
      then (hs, (s, (f, RS_normal (vs_to_es (v2 :: ves')))))
      else (hs, (s, (f, RS_normal (vs_to_es (v1 :: ves')))))
    else (hs, (s, (f, crash_error)))

  | AI_basic (BI_block tb es) =>
    if expand f.(f_inst) tb is Some (Tf t1s t2s) then
      if length ves >= length t1s
      then
        let: (ves', ves'')  := split_n ves (length t1s) in
        (hs, (s, (f, RS_normal (vs_to_es ves''
                              ++ [::AI_label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)]))))
      else (hs, (s, (f, crash_error)))
    else (hs, (s, (f, crash_error)))

  | AI_basic (BI_loop tb es) =>
    if expand f.(f_inst) tb is Some (Tf t1s t2s) then
      if length ves >= length t1s
      then
        let: (ves', ves'') := split_n ves (length t1s) in
        (hs, (s, (f, RS_normal (vs_to_es ves''
                              ++ [::AI_label (length t1s) [::AI_basic (BI_loop tb es)]
                                      (vs_to_es ves' ++ to_e_list es)]))))
      else (hs, (s, (f, crash_error)))
    else (hs, (s, (f, crash_error)))

  | AI_basic (BI_if tf es1 es2) =>
    if ves is VAL_num (VAL_int32 c) :: ves' then
      if c == Wasm_int.int_zero i32m
      then (hs, (s, (f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_block tf es2)]))))
      else (hs, (s, (f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_block tf es1)]))))
    else (hs, (s, (f, crash_error)))

  | AI_basic (BI_br j) => (hs, (s, (f, RS_break j ves)))
  | AI_basic (BI_br_if j) =>
    if ves is VAL_num (VAL_int32 c) :: ves' then
      if c == Wasm_int.int_zero i32m
      then (hs, (s, (f, RS_normal (vs_to_es ves'))))
      else (hs, (s, (f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br j)]))))
    else (hs, (s, (f, crash_error)))
  | AI_basic (BI_br_table js j) =>
    if ves is VAL_num (VAL_int32 c) :: ves' then
      let: k := Wasm_int.nat_of_uint i32m c in
      if k < length js
      then
        expect (List.nth_error js k) (fun js_at_k =>
            (hs, (s, (f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br js_at_k)])))))
          (hs, ((s, (f, crash_error))))
      else (hs, (s, (f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br j)]))))
    else (hs, (s, (f, crash_error)))

  | AI_basic (BI_call j) =>
    if List.nth_error f.(f_inst).(inst_funcs) j is Some a then
      (hs, (s, (f, RS_normal (vs_to_es ves ++ [::AI_invoke a]))))
    else (hs, (s, (f, crash_error)))

  | AI_basic (BI_call_indirect x y) =>
      (hs, BI_call_indirect_aux s f x y ves)

  | AI_basic BI_return => (hs, (s, (f, RS_return ves)))

  | AI_basic (BI_local_get j) =>
    if j < length f.(f_locs)
    then
      expect (List.nth_error f.(f_locs) j) (fun vs_at_j =>
          (hs, (s, (f, RS_normal (vs_to_es (vs_at_j :: ves))))))
        (hs, ((s, (f, crash_error))))
    else (hs, (s, (f, crash_error)))

  | AI_basic (BI_local_set j) =>
    if ves is v :: ves' then
      if j < length f.(f_locs)
      then (hs, (s, (Build_frame (set_nth v f.(f_locs) j v) f.(f_inst), RS_normal (vs_to_es ves'))))
      else (hs, (s, (f, crash_error)))
    else (hs, (s, (f, crash_error)))

  | AI_basic (BI_local_tee j) =>
    if ves is v :: ves' then
      (hs, (s, (f, RS_normal (vs_to_es (v :: ves) ++ [::AI_basic (BI_local_set j)]))))
    else (hs, (s, (f, crash_error)))

  | AI_basic (BI_global_get j) =>
    if sglob_val s f.(f_inst) j is Some xx
    then (hs, (s, (f, RS_normal (vs_to_es (xx :: ves)))))
    else (hs, (s, (f, crash_error)))

  | AI_basic (BI_global_set j) =>
    if ves is v :: ves' then
      if supdate_glob s f.(f_inst) j v is Some xx
      then (hs, (xx, (f, RS_normal (vs_to_es ves'))))
      else (hs, (s, (f, crash_error)))
    else (hs, (s, (f, crash_error)))
             
    | AI_basic (BI_load t None a off) =>
      if ves is VAL_num (VAL_int32 k) :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load (mem_s_j) (Wasm_int.N_of_uint i32m k) off (tnum_length t))
                 (fun bs => (hs, (s, (f, RS_normal (vs_to_es (VAL_num (wasm_deserialise bs t) :: ves'))))))
                 (hs, ((s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))))
             else (hs, (s, (f, crash_error))))
          (hs, ((s, (f, crash_error))))
      else (hs, (s, (f, crash_error)))

    | AI_basic (BI_load t (Some (tp, sx)) a off) =>
      if ves is VAL_num (VAL_int32 k) :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load_packed sx (mem_s_j) (Wasm_int.N_of_uint i32m k) off (tp_length tp) (tnum_length t))
                 (fun bs => (hs, (s, (f, RS_normal (vs_to_es (VAL_num (wasm_deserialise bs t) :: ves'))))))
                 (hs, ((s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))))
             else (hs, (s, (f, crash_error))))
          (hs, ((s, (f, crash_error))))
      else (hs, (s, (f, crash_error)))

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
                      ((hs, (upd_s_mem s (set_nth mem' s.(s_mems) j mem'), (f, RS_normal (vs_to_es ves'))))))
                   (hs, ((s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))))
               else (hs, (s, (f, crash_error))))
            (hs, ((s, (f, crash_error))))
        else (hs, (s, (f, crash_error)))
      else (hs, (s, (f, crash_error)))

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
                      (hs, ((upd_s_mem s (set_nth mem' s.(s_mems) j mem'), (f, RS_normal (vs_to_es ves'))))))
                   (hs, ((s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap])))))
               else (hs, (s, (f, crash_error))))
            (hs, ((s, (f, crash_error))))
        else (hs, (s, (f, crash_error)))
      else (hs, (s, (f, crash_error)))

    | AI_basic BI_memory_size =>
      expect
        (smem_ind s f.(f_inst))
        (fun j =>
           if List.nth_error s.(s_mems) j is Some s_mem_s_j then
             (hs, ((s, (f, RS_normal (vs_to_es (VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j)))) :: ves))))))
           else (hs, (s, (f, crash_error))))
        (hs, ((s, (f, crash_error))))
        
  | AI_basic BI_memory_grow =>
      (hs, BI_memory_grow_aux s f ves)
               
  | AI_basic BI_memory_fill =>
      (hs, BI_memory_fill_aux s f ves)
               
  | AI_basic (BI_memory_copy) =>
      (hs, BI_memory_copy_aux s f ves)
               
  | AI_basic (BI_memory_init x) =>
      (hs, BI_memory_init_aux s f x ves)
                         
  | AI_basic (BI_data_drop x) =>
      if sdata_drop s f.(f_inst) x is Some s' then
        (hs, (s', (f, RS_normal (vs_to_es ves))))
      else (hs, (s, (f, crash_error)))
               

    (* Table instructions *)
    | AI_basic (BI_table_get x) =>
      if ves is VAL_num (VAL_int32 i) :: ves' then
        if stab s f.(f_inst) x is Some tab then
          if (Wasm_int.nat_of_uint i32m i) >= length tab.(tableinst_elem) then
            (hs, (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap]))))
            else
            if List.nth_error tab.(tableinst_elem) (Wasm_int.nat_of_uint i32m i) is Some val then
              (hs, (s, (f, RS_normal (vs_to_es (VAL_ref val :: ves')))))
              else (hs, (s, (f, crash_error)))
          else (hs, (s, (f, crash_error)))
      else (hs, (s, (f, crash_error)))
    
    | AI_basic (BI_table_set x) =>
      if ves is val :: VAL_num (VAL_int32 i) :: ves' then
        if stab s f.(f_inst) x is Some tab then
          if val is VAL_ref ref then
            if (Wasm_int.nat_of_uint i32m i) >= length tab.(tableinst_elem) then
              (hs, (s, (f, RS_normal (vs_to_es ves' ++ [::AI_trap]))))
            else
              if stab_update s f.(f_inst) x (Wasm_int.nat_of_uint i32m i) ref is Some s' then
                (hs, (s', (f, RS_normal (vs_to_es ves))))
            else (hs, (s, (f, crash_error)))
          else (hs, (s, (f, crash_error)))
        else (hs, (s, (f, crash_error)))
      else (hs, (s, (f, crash_error)))

               
    | AI_basic (BI_table_size x) =>
        if stab s f.(f_inst) x is Some tab then
          let sz := Z.of_nat (length tab.(tableinst_elem)) in
            (hs, (s, (f, RS_normal (vs_to_es (VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m sz)) :: ves)))))
        else (hs, (s, (f, crash_error)))
                 
  | AI_basic (BI_table_grow x) =>
      (hs, BI_table_fill_aux s f x ves)
               
  | AI_basic (BI_table_fill x) =>
      (hs, BI_table_fill_aux s f x ves)
               
  | AI_basic (BI_table_copy x y) =>
      (hs, BI_table_copy_aux s f x y ves)

  | AI_basic (BI_table_init x y) =>
      (hs, BI_table_init_aux s f x y ves)

    | AI_basic (BI_elem_drop x) =>
      if selem_drop s f.(f_inst) x is Some s' then
        (hs, (s', (f, RS_normal (vs_to_es ves))))
      else (hs, (s, (f, crash_error)))
            
    
               
    (* These values are not supposed to get into here *)
    | AI_basic (BI_const_num _) => (hs, (s, (f, crash_error)))
    | AI_basic (BI_const_vec _) => (hs, (s, (f, crash_error)))
    | AI_basic (BI_ref_null _) => (hs, (s, (f, crash_error)))                  
    | AI_ref _ => (hs, (s, (f, crash_error)))      
    | AI_ref_extern _ => (hs, (s, (f, crash_error)))                    

  | AI_invoke i =>
      AI_invoke_aux hs s f i ves

  | AI_label ln les es =>
    if es_is_trap es
    then (hs, (s, (f, RS_normal (vs_to_es ves ++ [::AI_trap]))))
    else
      if const_list es
      then (hs, (s, (f, RS_normal (vs_to_es ves ++ es))))
      else
      let: (hs', (s', (f', res))) := run_step_with_fuel fuel d (hs, (s, (f, es))) in
      match res with
      | RS_break 0 bvs =>
        if length bvs >= ln
        then (hs', (s', (f', RS_normal ((vs_to_es ((take ln bvs) ++ ves)) ++ les))))
        else (hs', (s', (f', crash_error)))
      | RS_break (n.+1) bvs => (hs', (s', (f', RS_break n bvs)))
      | RS_return rvs => (hs', (s', (f', RS_return rvs)))
      | RS_normal es' =>
        (hs', (s', (f', RS_normal (vs_to_es ves ++ [::AI_label ln les es']))))
      | RS_crash error => (hs', (s', (f', RS_crash error)))
      end

  | AI_local ln f0 es =>
    if es_is_trap es
    then (hs, (s, (f, RS_normal (vs_to_es ves ++ [::AI_trap]))))
    else
      if const_list es
      then
        if length es == ln
        then (hs, (s, (f, RS_normal (vs_to_es ves ++ es))))
        else (hs, (s, (f, crash_error)))
      else
        let: (hs', (s', (f', res))) := run_step_with_fuel fuel d (hs, (s, (f0, es))) in
        match res return host_state * res_tuple with
        | RS_return rvs =>
          if length rvs >= ln
          then (hs', (s', (f, RS_normal (vs_to_es (take ln rvs ++ ves)))))
          else (hs', (s', (f, crash_error)))
        | RS_normal es' =>
          (hs', (s', (f, RS_normal (vs_to_es ves ++ [::AI_local ln f' es']))))
        | RS_crash error => (hs', (s', (f, RS_crash error)))
        | RS_break _ _ => (hs', (s', (f, crash_error)))
        end

  | AI_trap => (hs, (s, (f, crash_error)))
  end
  end.

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
Definition run_step_fuel (cfg : host_state * config_tuple) : nat :=
  let: (hs, (s, (f, es))) := cfg in
  1 + List.fold_left max (List.map run_one_step_fuel es) 0.

Definition run_step (d : depth) (cfg : host_state * config_tuple) : host_state * res_tuple :=
  run_step_with_fuel (run_step_fuel cfg) d cfg.

Fixpoint run_v (fuel : fuel) (d : depth) (cfg : host_state * config_tuple) : ((host_state * store_record * res)%type) :=
  let: (hs, (s, (f, es))) := cfg in
  match fuel with
  | 0 => (hs, s, R_crash C_exhaustion)
  | fuel.+1 =>
    if es_is_trap es
    then (hs, s, R_trap)
    else
      if const_list es
      then (hs, s, R_value (fst (split_vals_e es)))
      else
        let: (hs', (s', (f', res))) := run_step d (hs, (s, (f, es))) in
        match res with
        | RS_normal es' => run_v fuel d (hs', (s', (f', es')))
        | RS_crash error => (hs', s', R_crash error)
        | _ => (hs', s', R_crash C_error)
        end
  end.

End Host_func.
