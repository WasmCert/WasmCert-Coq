(** Wasm type checker **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)
Require Import common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import operations typing.


Section Host.

Variable host_function : eqType.

Let store_record := store_record host_function.
Let function_closure := function_closure host_function.
Let administrative_instruction := administrative_instruction host_function.


Inductive checker_type_aux : Type :=
| CTA_any : checker_type_aux
| CTA_some : value_type -> checker_type_aux.

Scheme Equality for checker_type_aux.
Definition checker_type_aux_eqb v1 v2 := is_left (checker_type_aux_eq_dec v1 v2).
Definition eqchecker_type_auxP  : Equality.axiom checker_type_aux_eqb :=
  eq_dec_Equality_axiom checker_type_aux_eq_dec.

Canonical Structure checker_type_aux_eqMixin := EqMixin eqchecker_type_auxP.
Canonical Structure checker_type_aux_eqType :=
  Eval hnf in EqType checker_type_aux checker_type_aux_eqMixin.

Inductive checker_type : Type :=
| CT_top_type : seq checker_type_aux -> checker_type
| CT_type : seq value_type -> checker_type
| CT_bot : checker_type.

Definition checker_type_eq_dec : forall v1 v2 : checker_type, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition checker_type_eqb v1 v2 : bool := checker_type_eq_dec v1 v2.
Definition eqchecker_typeP : Equality.axiom checker_type_eqb :=
  eq_dec_Equality_axiom checker_type_eq_dec.

Canonical Structure checker_type_eqMixin := EqMixin eqchecker_typeP.
Canonical Structure checker_type_eqType := Eval hnf in EqType checker_type checker_type_eqMixin.


Definition to_ct_list (ts : seq value_type) : seq checker_type_aux :=
  map CTA_some ts.

Fixpoint ct_suffix (ts ts' : seq checker_type_aux) : bool :=
  (ts == ts')
  ||
  match ts' with
  | [::] => false
  | _ :: ts'' => ct_suffix ts ts''
  end.

Definition consume (t : checker_type) (cons : seq checker_type_aux) : checker_type :=
  match t with
  | CT_type ts =>
    if ct_suffix cons (to_ct_list ts)
    then CT_type (take (length ts - length cons) ts)
    else CT_bot
  | CT_top_type cts =>
    if ct_suffix cons cts
    then CT_top_type (take (length cts - length cons) cts)
    else
      (if ct_suffix cts cons
       then CT_top_type [::]
       else CT_bot)
  | _ => CT_bot
  end.

Definition produce (t1 t2 : checker_type) : checker_type :=
  match (t1, t2) with
  | (CT_top_type ts, CT_type ts') => CT_top_type (ts ++ (to_ct_list ts'))
  | (CT_type ts, CT_type ts') => CT_type (ts ++ ts')
  | (CT_type ts', CT_top_type ts) => CT_top_type ts
  | (CT_top_type ts', CT_top_type ts) => CT_top_type ts
  | _ => CT_bot
  end.

Definition type_update (curr_type : checker_type) (cons : seq checker_type_aux) (prods : checker_type) : checker_type :=
  produce (consume curr_type cons) prods.

Definition select_return_top (ts : seq checker_type_aux) (cta1 cta2 : checker_type_aux) : checker_type :=
  match (cta1, cta2) with
  | (_, CTA_any) => CT_top_type (take (length ts - 3) ts ++ [::cta1])
  | (CTA_any, _) => CT_top_type (take (length ts - 3) ts ++ [::cta2])
  | (CTA_some t1, CTA_some t2) =>
    if t1 == t2
    then CT_top_type (take (length ts - 3) ts ++ [::CTA_some t1])
    else CT_bot
  end.

Definition type_update_select (t : checker_type) : checker_type :=
  match t with
  | CT_type ts =>
    if (length ts >= 3) && (List.nth_error ts (length ts - 2) == List.nth_error ts (length ts - 3))
    then (consume (CT_type ts) [::CTA_any; CTA_some T_i32])
    else CT_bot
  | CT_top_type ts =>
    match length ts with
    | 0 => CT_top_type [::CTA_any]
    | 1 => type_update (CT_top_type ts) [::CTA_some T_i32] (CT_top_type [::CTA_any])
    | 2 => consume (CT_top_type ts) [::CTA_some T_i32]
    | _ =>
      match List.nth_error ts (length ts - 2), List.nth_error ts (length ts - 3) with
      | Some ts_at_2, Some ts_at_3 =>
        type_update (CT_top_type ts) [::CTA_any; CTA_any; CTA_some T_i32]
                    (select_return_top ts ts_at_2 ts_at_3)
      | _, _ => CT_bot (* TODO: is that OK? *)
      end
    end
  | CT_bot => CT_bot
  end.

Fixpoint same_lab_h (iss : seq nat) (lab_c : seq (seq value_type)) (ts : seq value_type) : option (seq value_type) :=
  match iss with
  | [::] => Some ts
  | i :: iss' =>
    if i >= length lab_c
    then None
    else
      match List.nth_error lab_c i with
      | None => None (* TODO *)
      | Some xx =>
        if xx == ts then same_lab_h iss' lab_c xx
        else None
      end
  end.

Definition same_lab (iss : seq nat) (lab_c : seq (seq value_type)) : option (seq value_type) :=
  match iss with
  | [::] => None
  | i :: iss' =>
    if i >= length lab_c
    then None
    else
      match List.nth_error lab_c i with
      | Some xx => same_lab_h iss' lab_c xx
      | None => None (* TODO: ??? *)
      end
  end.


Definition c_types_agree (ct : checker_type) (ts' : seq value_type) : bool :=
  match ct with
  | CT_type ts => ts == ts'
  | CT_top_type ts => ct_suffix ts (to_ct_list ts')
  | CT_bot => false
  end.

Fixpoint check_single (C : t_context) (be : basic_instruction) (ts : checker_type) {struct be} : checker_type :=
  let check := fix check (C : t_context) (es : seq basic_instruction) (ts : checker_type) {struct es} : checker_type :=
      match es with
      | [::] => ts
      | e :: es' =>
        match ts with
        | CT_bot => CT_bot
        | _ => check C es' (check_single C e ts)
        end
      end in
  let b_e_type_checker C (es : seq basic_instruction) tf :=
       match tf with
       | Tf tn tm =>
         c_types_agree (check C es (CT_type tn)) tm
       end in 
  match be with
  | EConst v => type_update ts [::] (CT_type [::typeof v])
  | Unop_i t _ =>
    if is_int_t t
    then type_update ts [::CTA_some t] (CT_type [::t])
    else CT_bot
  | Unop_f t _ =>
    if is_float_t t
    then  type_update ts [::CTA_some t] (CT_type [::t])
    else CT_bot
  | Binop_i t _ =>
    if is_int_t t
    then type_update ts [::CTA_some t; CTA_some t] (CT_type [::t])
    else CT_bot
  | Binop_f t _ =>
    if is_int_t t
    then type_update ts [::CTA_some t; CTA_some t] (CT_type [::t])
    else CT_bot
  | Testop t _ =>
    if is_int_t t
    then type_update ts [::CTA_some t] (CT_type [::T_i32])
    else CT_bot
  | Relop_i t _ =>
    if is_int_t t
    then type_update ts [::CTA_some t; CTA_some t] (CT_type [::T_i32])
    else CT_bot
  | Relop_f t _ =>
    if is_int_t t
    then type_update ts [::CTA_some t; CTA_some t] (CT_type [::T_i32])
    else CT_bot
  | Cvtop t1 Convert t2 sx =>
    if typing.convert_cond t1 t2 sx
    then type_update ts [::CTA_some t2] (CT_type [::t1])
    else CT_bot
  | Cvtop t1 Reinterpret t2 sxo =>
    if (t1 != t2) && (t_length t1 == t_length t2) && (sxo == None)
    then type_update ts [::CTA_some t2] (CT_type [::t1])
    else CT_bot
  | Unreachable => type_update ts [::] (CT_top_type [::])
  | Nop => ts
  | Drop => type_update ts [::CTA_any] (CT_type [::])
  | Select => type_update_select ts
  | Block tf es =>
    match tf with
    | Tf tn tm =>
      if b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es (Tf tn tm)
      then type_update ts (to_ct_list tn) (CT_type tm)
      else CT_bot
    end
  | Loop tf es =>
    match tf with
    | Tf tn tm =>
      if b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es (Tf tn tm)
      then type_update ts (to_ct_list tn) (CT_type tm)
      else CT_bot
    end
  | If tf es1 es2 =>
    match tf with
    | Tf tn tm =>
      if b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es1 (Tf tn tm)
                          && b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es2 (Tf tn tm)
      then type_update ts (to_ct_list (tn ++ [::T_i32])) (CT_type tm)
      else CT_bot
    end
  | Br i =>
    if i < length (tc_label C)
    then
      match List.nth_error (tc_label C) i with
      | Some xx => type_update ts (to_ct_list xx) (CT_top_type [::])
      | None => CT_bot (* Isa mismatch *)
      end
    else CT_bot
  | Br_if i =>
    if i < length (tc_label C)
    then
      match List.nth_error (tc_label C) i with
      | Some xx => type_update ts (to_ct_list (xx ++ [::T_i32])) (CT_type xx)
      | None => CT_bot (* Isa mismatch *)
      end
    else CT_bot
  | Br_table iss i =>
    match same_lab (iss ++ [::i]) (tc_label C) with
    | None => CT_bot
    | Some tls => type_update ts (to_ct_list (tls ++ [::T_i32])) (CT_top_type [::])
    end
  | Return =>
    match tc_return C with
    | None => CT_bot
    | Some tls => type_update ts (to_ct_list tls) (CT_top_type [::])
    end
  | Call i =>
    if i < length (tc_func_t C)
    then
      match List.nth_error (tc_func_t C) i with
      | None => CT_bot (* Isa mismatch *)
      | Some (Tf tn tm) =>
        type_update ts (to_ct_list tn) (CT_type tm)
      end
    else CT_bot
  | Call_indirect i =>
    if (tc_table C != None) && (i < length (tc_types_t C))
    then
      match List.nth_error (tc_func_t C) i with
      | None => CT_bot (* Isa mismatch *)
      | Some (Tf tn tm) =>
        type_update ts (to_ct_list (tn ++ [::T_i32])) (CT_type tm)
      end
    else CT_bot
  | Get_local i =>
    if i < length (tc_func_t C)
    then
      match List.nth_error (tc_local C) i with
      | None => CT_bot (* Isa mismatch *)
      | Some xx => type_update ts [::] (CT_type [::xx])
      end
    else CT_bot
  | Set_local i =>
    if i < length (tc_local C)
    then
      match List.nth_error (tc_local C) i with
      | None => CT_bot (* Isa mismatch *)
      | Some xx => type_update ts [::CTA_some xx] (CT_type [::])
      end
    else CT_bot
  | Tee_local i =>
    if i < length (tc_local C)
    then
      match List.nth_error (tc_local C) i with
      | None => CT_bot (* Isa mismatch *)
      | Some xx => type_update ts [::CTA_some xx] (CT_type [::xx])
      end
    else CT_bot
  | Get_global i =>
    if i < length (tc_global C)
    then
      match List.nth_error (tc_global C) i with
      | None => CT_bot (* Isa mismatch *)
      | Some xx => type_update ts [::] (CT_type [::tg_t xx])
      end
    else CT_bot
  | Set_global i =>
    if i < length (tc_global C)
    then
      match List.nth_error (tc_global C) i with
      | None => CT_bot (* Isa mismatch *)
      | Some xx =>
        if is_mut xx
        then type_update ts [::CTA_some (tg_t xx)] (CT_type [::])
        else CT_bot
      end
    else CT_bot
  | Load t tp_sx a off =>
    if (tc_memory C != None) && load_store_t_bounds a (option_projl tp_sx) t
    then type_update ts [::CTA_some T_i32] (CT_type [::t])
    else CT_bot
  | Store t tp a off =>
    if (tc_memory C != None) && load_store_t_bounds a tp t
    then type_update ts [::CTA_some T_i32; CTA_some t] (CT_type [::])
    else CT_bot
  | Current_memory =>
    if tc_memory C != None
    then type_update ts [::] (CT_type [::T_i32])
    else CT_bot
  | Grow_memory =>
    if tc_memory C != None
    then type_update ts [::CTA_some T_i32] (CT_type [::T_i32])
    else CT_bot
  end.


(* TODO: try to avoid repetition *)
Fixpoint check (C : t_context) (es : seq basic_instruction) (ts : checker_type) {struct es} : checker_type :=
  match es with
  | [::] => ts
  | e :: es' =>
    match ts with
    | CT_bot => CT_bot
    | _ => check C es' (check_single C e ts)
    end
  end.

(* TODO: try to avoid repetition *)
Definition b_e_type_checker (C : t_context) (es : seq basic_instruction) (tf : function_type) : bool :=
  match tf with
  | Tf tn tm => c_types_agree (check C es (CT_type tn)) tm
  end.

Fixpoint collect_at_inds A (l : seq A) (ns : seq nat) : seq A :=
  match ns with
  | n :: ns' =>
    match (List.nth_error l n) with
    | Some x => x :: collect_at_inds l ns'
    | None => collect_at_inds l ns'
    end
  | [::] => [::]
  end.

(* TODO: This definition is kind of a duplication of inst_typing, to avoid more dependent definitions becoming Prop downstream *)
Definition inst_type_check (s : store_record) (i : instance) : t_context :=
  Build_t_context
    (i_types i)
    (collect_at_inds (map cl_type (s_funcs s)) (i_funcs i))
    (collect_at_inds (map (fun glob => Build_global_type (g_mut glob) (typeof (g_val glob))) (s_globs s)) (i_globs i))
    (option_map (@length (option function_closure)) (match (i_tab i) with | Some n => List.nth_error (s_tab s) n | None => None end))
    (option_map (@length (byte)) (option_bind (List.nth_error (s_memory s)) (i_memory i)))
    [::]
    [::]
    None.

Definition cl_type_check (s : store_record) (cl : function_closure) : bool :=
  match cl with
  | Func_native i tf ts es =>
    match tf with
    | Tf t1s t2s =>
      let C := inst_type_check s i in
      let C' := upd_local_label_return C (app (tc_local C) (app t1s ts)) (app [::t2s] (tc_label  C)) (Some t2s) in
      b_e_type_checker C' es (Tf [::] t2s)
    end
(*| cl_typing_native : forall i S C ts t1s t2s es tf,*)
  | Func_host tf h => true
  end.

(* FIXME: Isn’t this supposed to be in [typing.v] instead? *)
Inductive e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
| ety_a : forall s C bes tf,
  be_typing C bes tf -> e_typing s C (to_e_list bes) tf
| ety_composition : forall s C es e t1s t2s t3s,
  e_typing s C es (Tf t1s t2s) ->
  e_typing s C [::e] (Tf t2s t3s) ->
  e_typing s C (es ++ [::e]) (Tf t1s t3s)
| ety_weakening : forall s C es ts t1s t2s,
  e_typing s C es (Tf t1s t2s) ->
  e_typing s C es (Tf (ts ++ t1s) (ts ++ t2s))
| ety_trap : forall s C tf,
  e_typing s C [::Trap] tf
| ety_local : forall s C n i vs es ts,
  s_typing s (Some ts) i vs es ts ->
  Nat.eqb (length ts) n ->
  e_typing s C [::Local n i vs es] (Tf [::] ts)
| ety_callcl : forall s C cl tf,
  cl_typing s cl tf ->
  e_typing s C [::Callcl cl] tf
| ety_lanel : forall s C e0s es ts t2s n,
  e_typing s C e0s (Tf ts t2s) ->
  e_typing s (upd_label C ([::ts] ++ tc_label C)) es (Tf [::] t2s) ->
  Nat.eqb (length ts) n ->
  e_typing s C [::Label n e0s es] (Tf [::] t2s)

with s_typing : store_record -> option (seq value_type) -> instance -> seq value -> seq administrative_instruction -> seq value_type -> Prop :=
| mk_s_typing : forall s i vs es rs ts C C0 tvs0,
  let tvs := map typeof vs in
  inst_typing s i C0 ->
  C = upd_local_return C0 ((tc_local tvs0) ++ tvs) rs ->
  e_typing s C es (Tf [::] ts) ->
  (rs = Some ts \/ rs = None) ->
  s_typing s rs i vs es ts
.

Definition tab_agree (s : store_record) (tcl : option function_closure) : bool :=
  match tcl with
  | None => true
  | Some cl => cl_type_check s cl
  end.

Definition mem_agree bs m : bool :=
  m <= mem_size bs.

Definition store_typing (s : store_record) : bool :=
  match s with
  | Build_store_record fs tclss bss gs =>
    all (fun f => cl_type_check s f) fs &&
    all (tab_agree s) (flatten tclss)
  end.

Inductive config_typing : instance -> store_record -> seq value -> seq administrative_instruction -> seq value_type -> Prop :=
| mk_config_typing :
  forall i s vs es ts,
  store_typing s ->
  s_typing s None i vs es ts ->
  config_typing i s vs es ts.

End Host.

