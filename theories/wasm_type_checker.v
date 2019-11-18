(* Wasm type checker *)
(* (C) J. Pichon - see LICENSE.txt *)
From mathcomp
Require Import ssreflect.all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import wasm wasm_typing.

Inductive checker_type_aux : Type :=
| CTA_any : checker_type_aux
| CTA_some : value_type -> checker_type_aux.

Definition checker_type_aux_eqb (cta1 cta2 : checker_type_aux) : bool :=
  match (cta1, cta2) with
  | (CTA_any, CTA_any) => true
  | (CTA_some t1, CTA_some t2) => t1 == t2
  | _ => false
  end.

Axiom eqchecker_type_auxP : Equality.axiom checker_type_aux_eqb.
(* TODO *)
Canonical checker_type_aux_eqMixin := EqMixin eqchecker_type_auxP.
Canonical checker_type_aux_eqType := Eval hnf in EqType checker_type_aux checker_type_aux_eqMixin.

Inductive checker_type : Type :=
| CT_top_type : list checker_type_aux -> checker_type
| CT_type : list value_type -> checker_type
| CT_bot : checker_type.

Definition checker_type_eqb (ct1 ct2 : checker_type) : bool :=
  match (ct1, ct2) with
  | (CT_top_type ctas1, CT_top_type ctas2) => ctas1 == ctas2
  | (CT_type ts1, CT_type ts2) => ts1 == ts2
  | (CT_bot, CT_bot) => true
  | _ => false
  end.

Axiom eqchecker_typeP : Equality.axiom checker_type_eqb.
(* TODO *)
Canonical checker_type_eqMixin := EqMixin eqchecker_typeP.
Canonical checker_type_eqType := Eval hnf in EqType checker_type checker_type_eqMixin.


Definition to_ct_list (ts : list value_type) : list checker_type_aux :=
  map CTA_some ts.

Fixpoint ct_suffix (ts ts' : list checker_type_aux) : bool :=
  (ts == ts')
  ||
  match ts' with
  | [::] => false
  | _ :: ts'' => ct_suffix ts ts''
  end.

Definition consume (t : checker_type) (cons : list checker_type_aux) : checker_type :=
  match t with
  | CT_type ts =>
    if ct_suffix cons (to_ct_list ts)
    then CT_type (List.firstn (length ts - length cons) ts)
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

Definition type_update (curr_type : checker_type) (cons : list checker_type_aux) (prods : checker_type) : checker_type :=
  produce (consume curr_type cons) prods.

Definition select_return_top (ts : list checker_type_aux) (cta1 cta2 : checker_type_aux) : checker_type :=
  match (cta1, cta2) with
  | (_, CTA_any) => CT_top_type (List.firstn (length ts - 3) ts ++ [::cta1])
  | (CTA_any, _) => CT_top_type (List.firstn (length ts - 3) ts ++ [::cta2])
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
      match (List.nth_error ts (length ts - 2), List.nth_error ts (length ts - 3)) with
      | (Some ts_at_2, Some ts_at_3) =>
        type_update (CT_top_type ts) [::CTA_any; CTA_any; CTA_some T_i32]
                    (select_return_top ts ts_at_2 ts_at_3)
      | _ => CT_bot (* TODO: is that OK? *)
      end
    end
  | CT_bot => CT_bot
  end.

Fixpoint same_lab_h (iss : list nat) (lab_c : list (list value_type)) (ts : list value_type) : option (list value_type) :=
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

Definition same_lab (iss : list nat) (lab_c : list (list value_type)) : option (list value_type) :=
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


Definition c_types_agree (ct : checker_type) (ts' : list value_type) : bool :=
  match ct with
  | CT_type ts => ts == ts'
  | CT_top_type ts => ct_suffix ts (to_ct_list ts')
  | CT_bot => false
  end.

Fixpoint check_single (C : t_context) (be : basic_instruction) (ts : checker_type) {struct be} : checker_type :=
  let check := fix check (C : t_context) (es : list basic_instruction) (ts : checker_type) {struct es} : checker_type :=
      match es with
      | [::] => ts
      | e :: es' =>
        match ts with
        | CT_bot => CT_bot
        | _ => check C es' (check_single C e ts)
        end
      end in
  let b_e_type_checker C (es : list basic_instruction) tf :=
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
    if wasm_typing.convert_cond t1 t2 sx
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
Fixpoint check (C : t_context) (es : list basic_instruction) (ts : checker_type) {struct es} : checker_type :=
  match es with
  | [::] => ts
  | e :: es' =>
    match ts with
    | CT_bot => CT_bot
    | _ => check C es' (check_single C e ts)
    end
  end.

(* TODO: try to avoid repetition *)
Definition b_e_type_checker (C : t_context) (es : list basic_instruction) (tf : function_type) : bool :=
  match tf with
  | Tf tn tm => c_types_agree (check C es (CT_type tn)) tm
  end.

Definition cl_type_check (S : s_context) (cl : function_closure) : bool :=
  match cl with
  | Func_native i tf ts es =>
    match tf with
    | Tf t1s t2s =>
      (i < length (sc_inst S))
        && match List.nth_error (sc_inst S) i with
           | Some C =>
             let C' := upd_local_label_return C (app (tc_local C) (app t1s ts)) (app [::t2s] (tc_label  C)) (Some t2s) in
             b_e_type_checker C' es (Tf [::] t2s)
           | None => false
        end
(*| cl_typing_native : forall i S C ts t1s t2s es tf,*)
    end
  | Func_host tf h => true
  end.

Inductive e_typing : s_context -> t_context -> list administrative_instruction -> function_type -> Prop :=
| ety_a : forall S C bes tf,
  be_typing C bes tf -> e_typing S C (to_e_list bes) tf
| ety_composition : forall S C es e t1s t2s t3s,
  e_typing S C es (Tf t1s t2s) ->
  e_typing S C [::e] (Tf t2s t3s) ->
  e_typing S C (es ++ [::e]) (Tf t1s t3s)
| ety_weakening : forall S C es ts t1s t2s,
  e_typing S C es (Tf t1s t2s) ->
  e_typing S C es (Tf (ts ++ t1s) (ts ++ t2s))
| ety_trap : forall S C tf,
  e_typing S C [::Trap] tf
| ety_local : forall S C n i vs es ts,
  s_typing S (Some ts) i vs es ts ->
  Nat.eqb (length ts) n ->
  e_typing S C [::Local n i vs es] (Tf [::] ts)
| ety_callcl : forall S C cl tf,
  cl_typing S cl tf ->
  e_typing S C [::Callcl cl] tf
| ety_lanel : forall S C e0s es ts t2s n,
  e_typing S C e0s (Tf ts t2s) ->
  e_typing S (upd_label C ([::ts] ++ tc_label C)) es (Tf [::] t2s) ->
  Nat.eqb (length ts) n ->
  e_typing S C [::Label n e0s es] (Tf [::] t2s)
with s_typing : s_context -> option (list value_type) -> nat -> list value -> list administrative_instruction -> list value_type -> Prop :=
| mk_s_typing : forall S i vs es rs ts C C0 tvs0,
  i < length (sc_inst S) ->
  let tvs := map typeof vs in
  Some C0 = List.nth_error (sc_inst S) i ->
  Some tvs0 = List.nth_error (sc_inst S) i ->
  C = upd_local_return C0 ((tc_local tvs0) ++ tvs) rs ->
  e_typing S C es (Tf [::] ts) ->
  (rs == Some ts) || (rs == None) ->
  s_typing S rs i vs es ts.

Definition globi_agree (gs : list global_type) (n : nat) (g : global_type) : bool :=
  (n < length gs) && (List.nth_error gs n == Some g).

Definition memi_agree (sm : list nat) (j : option nat) (m : option nat) : bool :=
  (match (j, m) with
   | (None, _) => false
   | (_, None) => false
   | (Some j', Some m') =>
     (j' < length sm) && (List.nth_error sm j' == Some m')
   end)
  ||
  ((j == None) && (m == None)).

Definition funci_agree (fs : list function_type) (n : nat) (f : function_type) : bool :=
  (n < length fs) && (List.nth_error fs n == Some f).

Definition inst_typing (S : s_context) (inst : instance) (C : t_context) :=
  match (inst, C) with
  | (Build_instance ts fs i j gs, Build_t_context ts' tfs tgs n m [::] [::] None) =>
      (ts == ts') && 
         (all2 (funci_agree (sc_funcs S)) fs tfs) &&
         (all2 (globi_agree (sc_globs S)) gs tgs) &&
            (match (i, n) with
               | (None, None) => true
               | (None, Some _) => false | (Some _, None) => false
               | (Some i', Some n') => (i' < length (sc_tab S)) && (List.nth_error (sc_tab S) i' == Some n')
               end) &&
            (memi_agree (sc_mem S) j m)
  | _ => false
  end.

Definition glob_agree (g : global) (tg : global_type) : bool :=
  (tg_mut tg == g_mut g) && (tg_t tg == typeof (g_val g)).

Definition tab_agree (S : s_context) (tcl : option function_closure) : bool :=
  match tcl with
  | None => true
  | Some cl => cl_type_check S cl
  end.

Definition mem_agree bs m : bool :=
  m <= mem_size bs.

Definition store_typing (s : store_record) (S : s_context) : bool :=
  match (s, S) with
  | (Build_store_record insts fs tclss bss gs, Build_s_context Cs tfs ns ms tgs) =>
    all2 (inst_typing S) insts Cs &&
    all2 (fun f tf => cl_type_check S f && (cl_type f == tf)) fs tfs &&
    all (tab_agree S) (flatten tclss) &&
    all2 (fun tcls n => n <= length tcls) tclss ns &&
    all2 mem_agree bss ms &&
    all2 glob_agree gs tgs
  end.

Inductive config_typing : nat -> store_record -> list value -> list administrative_instruction -> list value_type -> Prop :=
| mk_config_typing :
  forall S i s vs es ts,
  store_typing s S ->
  s_typing S None i vs es ts ->
  config_typing i s vs es ts.
