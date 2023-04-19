(** Wasm type checker **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)
Require Import common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import operations typing datatypes_properties.

Section Host.

Variable host_function : eqType.

Let store_record := store_record host_function.
Let function_closure := function_closure host_function.

Inductive poly_type : Type :=
| PT_num_vec
| PT_ref
.

Scheme Equality for poly_type.
Definition poly_type_eqb v1 v2 := is_left (poly_type_eq_dec v1 v2).
Definition eqpoly_typeP: Equality.axiom poly_type_eqb :=
  eq_dec_Equality_axiom poly_type_eq_dec.

Canonical Structure poly_type_eqMixin := EqMixin eqpoly_typeP.
Canonical Structure poly_type_eqType :=
  Eval hnf in EqType poly_type poly_type_eqMixin.

Definition poly_type_compat (pt: poly_type) (t: value_type) : bool :=
  match pt with
  | PT_num_vec =>
      match t with
      | T_num _ | T_vec _ => true
      | _ => false
      end
  | PT_ref =>
      match t with
      | T_ref _ => true
      | _ => false
      end
  end.

Definition poly_poly_compat (pt1 pt2: poly_type) : bool :=
  pt1 == pt2.

Inductive checker_type_aux : Type :=
| CTA_any : checker_type_aux
| CTA_poly : poly_type -> checker_type_aux
| CTA_some : value_type -> checker_type_aux.

Definition checker_type_aux_eq_dec : forall v1 v2 : checker_type_aux,
  {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality.
Defined.
Definition checker_type_aux_eqb v1 v2 := is_left (checker_type_aux_eq_dec v1 v2).
Definition eqchecker_type_auxP: Equality.axiom checker_type_aux_eqb :=
  eq_dec_Equality_axiom checker_type_aux_eq_dec.

Canonical Structure checker_type_aux_eqMixin := EqMixin eqchecker_type_auxP.
Canonical Structure checker_type_aux_eqType :=
  Eval hnf in EqType checker_type_aux checker_type_aux_eqMixin.

Definition poly_cta_compat (pt: poly_type) (cta: checker_type_aux) : bool :=
  match cta with
  | CTA_any => true
  | CTA_poly pt' => poly_poly_compat pt pt'
  | CTA_some vt => poly_type_compat pt vt
  end.

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

Definition ct_compat (t1 t2: checker_type_aux) : bool :=
  match t1 with
  | CTA_any => true
  | CTA_poly pt1 =>
      match t2 with
      | CTA_any => true
      | CTA_poly pt2 => poly_poly_compat pt1 pt2
      | CTA_some vt => poly_type_compat pt1 vt
      end
  | CTA_some vt1 =>
    match t2 with
    | CTA_any => true
    | CTA_poly pt2 => poly_type_compat pt2 vt1
    | CTA_some vt2 => (vt1 == vt2)
    end
  end.

Definition ct_list_compat (l1 l2: list checker_type_aux) : bool :=
  all2 ct_compat l1 l2.

Definition ct_suffix (ts ts' : list checker_type_aux) : bool :=
  (size ts <= size ts') && (ct_list_compat (drop (size ts' - size ts) ts') ts).

Definition consume (t : checker_type) (cons : seq checker_type_aux) : checker_type :=
  match t with
  | CT_type ts =>
    if ct_suffix cons (to_ct_list ts)
    then CT_type (take (size ts - size cons) ts)
    else CT_bot
  | CT_top_type cts =>
    if ct_suffix cons cts
    then CT_top_type (take (size cts - size cons) cts)
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

Definition is_num_vec (vt: value_type) :=
  match vt with
  | T_num _ | T_vec _ => true
  | _ => false
  end.

(* Poly types are currently exclusive, therefore the trivial implementation *)
Definition merge_poly (pt1 pt2: poly_type) : option poly_type :=
  if (pt1 == pt2) then Some pt1 else None.

Definition merge_cta (cta1 cta2: checker_type_aux) : option checker_type_aux:=
  match cta1 with
  | CTA_any => Some cta2
  | CTA_poly pt1 =>
      match cta2 with
      | CTA_any => Some cta1
      | CTA_poly pt2 =>
          match merge_poly pt1 pt2 with
          | Some pt => Some (CTA_poly pt)
          | None => None
          end
      | CTA_some vt2 =>
          if poly_type_compat pt1 vt2 then Some (CTA_some vt2)
          else None
      end
  | CTA_some vt1 =>
      match cta2 with
      | CTA_any => Some cta1
      | CTA_poly pt2 =>
          if poly_type_compat pt2 vt1 then Some (CTA_some vt1)
          else None
      | CTA_some vt2 =>
          if vt1 == vt2 then Some (CTA_some vt1)
          else None
      end
  end.

Definition select_return_top (ts : seq checker_type_aux) (cta1 cta2 : checker_type_aux) : checker_type :=
  if (poly_cta_compat PT_num_vec cta1) && (poly_cta_compat PT_num_vec cta2) then
    match merge_cta cta1 cta2 with
    | Some cta => CT_top_type (take (length ts - 3) ts ++ [::cta])
    | None => CT_bot
    end
  else CT_bot.
         
Definition type_update_select (ot: option (list value_type)) (ct : checker_type) : checker_type :=
  match ot with
  | Some [::t] =>
      type_update ct [::CTA_some t; CTA_some t; CTA_some (T_num T_i32)] (CT_type [::t])
  | None =>
      match ct with
      | CT_type ts =>
          if (length ts >= 3) && (List.nth_error ts (length ts - 2) == List.nth_error ts (length ts - 3))
          then
            consume (CT_type ts) [::CTA_poly PT_num_vec; CTA_some (T_num T_i32)]
          else CT_bot
      | CT_top_type ts =>
          match length ts with
          | 0 => CT_top_type [::CTA_poly PT_num_vec]
          | 1 => type_update (CT_top_type ts) [::CTA_some (T_num T_i32)] (CT_top_type [::CTA_poly PT_num_vec])
          | 2 =>
              match ts with
              | vt :: ts' =>
                  if poly_cta_compat PT_num_vec vt then
                    consume (CT_top_type ts) [::CTA_some (T_num T_i32)]
                  else CT_bot
              | _ => CT_bot (* Impossible branch *)
              end
          | _ =>
              match List.nth_error ts (length ts - 2), List.nth_error ts (length ts - 3) with
              | Some ts_at_2, Some ts_at_3 =>
                  type_update (CT_top_type ts) [::CTA_any; CTA_any; CTA_some (T_num T_i32)]
                    (select_return_top ts ts_at_2 ts_at_3)
              | _, _ => CT_bot
              end
          end
      | CT_bot => CT_bot
      end
  | _ => CT_bot
  end.

Definition is_ref (t: value_type) : bool :=
  match t with
  | T_ref _ => true
  | _ => false
  end.

Definition is_ref_cta (cta: checker_type_aux) : bool :=
  match cta with
  | CTA_any => true
  | CTA_some (T_ref _) => true
  | _ => false
  end.

Fixpoint same_lab_h (iss : seq labelidx) (lab_c : seq (seq value_type)) (ts : seq value_type) : option (seq value_type) :=
  match iss with
  | [::] => Some ts
  | i :: iss' =>
    if i >= length lab_c
    then None
    else
      match List.nth_error lab_c i with
      | None => None (* TODO *)
                  (* See comment to the same_lab predicate below in the same place. *)
      | Some xx =>
        if xx == ts then same_lab_h iss' lab_c xx
        else None
      end
  end.

Definition same_lab (iss : seq labelidx) (lab_c : seq (seq value_type)) : option (seq value_type) :=
  match iss with
  | [::] => None
  | i :: iss' =>
    if i >= length lab_c
    then None
    else
      match List.nth_error lab_c i with
      | Some xx => same_lab_h iss' lab_c xx
      | None => None (* TODO: ??? *)
                  (* I think this case will never happen, since we've already
                       checked the length. Or we can remove the previous if. *)
                  (* We have to stick with line-by-line correspondance,
                    even if it means checking things twice. *)
      end
  end.


Definition c_types_agree (ct : checker_type) (ts' : seq value_type) : bool :=
  match ct with
  | CT_type ts => ts == ts'
  | CT_top_type ts => ct_suffix ts (to_ct_list ts')
  | CT_bot => false
  end.

Definition is_int (t: number_type) :=
  match t with
  | T_i32 => true
  | T_i64 => true
  | T_f32 => false
  | T_f64 => false
  end.

Definition is_float (t: number_type) :=
  match t with
  | T_i32 => false
  | T_i64 => false
  | T_f32 => true
  | T_f64 => true
  end.


Fixpoint check_single (C : t_context) (ts : checker_type) (be : basic_instruction) : checker_type :=
  let b_e_type_checker (C : t_context) (es : list basic_instruction) (tf : function_type) : bool :=
    let: (Tf tn tm) := tf in
      c_types_agree (List.fold_left (check_single C) es (CT_type tn)) tm 
in
  if ts == CT_bot then CT_bot
  else
  match be with
  | BI_const v => type_update ts [::] (CT_type [::typeof v])
  | BI_ref_null t => type_update ts [::] (CT_type [::T_ref t])
  | BI_ref_is_null => type_update ts [::CTA_poly PT_ref] (CT_type [::T_num T_i32])
  | BI_ref_func x =>
      match List.nth_error (tc_func C) x with
      | Some tf =>
          if x \in (tc_ref C) then
            type_update ts [::] (CT_type [::T_ref T_funcref])
          else CT_bot
      | None => CT_bot
      end
  | BI_unop t op =>
    match op with
    | Unop_i _ => if is_int t
                  then type_update ts [::CTA_some (T_num t)] (CT_type [::(T_num t)])
                  else CT_bot
    | Unop_f _ => if is_float t
                  then type_update ts [::CTA_some (T_num t)] (CT_type [::(T_num t)])
                  else CT_bot
    end
  | BI_binop t op =>
    match op with
    | Binop_i _ => if is_int t
                  then type_update ts [::CTA_some (T_num t); CTA_some (T_num t)] (CT_type [::(T_num t)])
                  else CT_bot
    | Binop_f _ => if is_float t
                  then type_update ts [::CTA_some (T_num t); CTA_some (T_num t)] (CT_type [::(T_num t)])
                  else CT_bot
    end
  | BI_testop t _ =>
    if is_int_t t
    then type_update ts [::CTA_some (T_num t)] (CT_type [::(T_num T_i32)])
    else CT_bot
  | BI_relop t op =>
    match op with
    | Relop_i _ => if is_int t
                  then type_update ts [::CTA_some (T_num t); CTA_some (T_num t)] (CT_type [::(T_num T_i32)])
                  else CT_bot
    | Relop_f _ => if is_float t
                  then type_update ts [::CTA_some (T_num t); CTA_some (T_num t)] (CT_type [::(T_num T_i32)])
                  else CT_bot
    end
  | BI_cvtop t1 CVO_convert t2 sx =>
    if typing.convert_cond t1 t2 sx
    then type_update ts [::CTA_some (T_num t2)] (CT_type [::T_num t1])
    else CT_bot
  | BI_cvtop t1 CVO_reinterpret t2 sxo =>
    if (t1 != t2) && (tnum_length t1 == tnum_length t2) && (sxo == None)
    then type_update ts [::CTA_some (T_num t2)] (CT_type [::T_num t1])
    else CT_bot
  | BI_unreachable => type_update ts [::] (CT_top_type [::])
  | BI_nop => ts
  | BI_drop => type_update ts [::CTA_any] (CT_type [::])
  | BI_select ot => type_update_select ot ts
  | BI_block bt es =>
      match expand_t C bt with
      | Some (Tf tn tm) =>
          if b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es (Tf tn tm)
          then type_update ts (to_ct_list tn) (CT_type tm)
          else CT_bot
      | None => CT_bot
      end
  | BI_loop bt es =>
      match expand_t C bt with
      | Some (Tf tn tm) =>
          if b_e_type_checker (upd_label C ([::tn] ++ tc_label C)) es (Tf tn tm)
          then type_update ts (to_ct_list tn) (CT_type tm)
          else CT_bot
      | None => CT_bot
      end
  | BI_if bt es1 es2 =>
      match expand_t C bt with
      | Some (Tf tn tm) =>
          if b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es1 (Tf tn tm)
             && b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es2 (Tf tn tm)
          then type_update ts (to_ct_list (tn ++ [::(T_num T_i32)])) (CT_type tm)
          else CT_bot
      | None => CT_bot
      end
  | BI_br i =>
    if i < length (tc_label C)
    then
      match List.nth_error (tc_label C) i with
      | Some xx => type_update ts (to_ct_list xx) (CT_top_type [::])
      | None => CT_bot 
      end
    else CT_bot
  | BI_br_if i =>
    if i < length (tc_label C)
    then
      match List.nth_error (tc_label C) i with
      | Some xx => type_update ts (to_ct_list (xx ++ [::(T_num T_i32)])) (CT_type xx)
      | None => CT_bot
      end
    else CT_bot
  | BI_br_table iss i =>
    match same_lab (iss ++ [:: i]) (tc_label C) with
    | None => CT_bot
    | Some tls => type_update ts (to_ct_list (tls ++ [::(T_num T_i32)])) (CT_top_type [::])
    end
  | BI_return =>
    match tc_return C with
    | None => CT_bot
    | Some tls => type_update ts (to_ct_list tls) (CT_top_type [::])
    end
  | BI_call i =>
    if i < length (tc_func C)
    then
      match List.nth_error (tc_func C) i with
      | None => CT_bot
      | Some (Tf tn tm) =>
        type_update ts (to_ct_list tn) (CT_type tm)
      end
    else CT_bot
  | BI_call_indirect i j =>
    match List.nth_error (tc_table C) i with
    | None => CT_bot 
    | Some tabtype =>
        if tabtype.(tt_elem_type) == T_funcref then
          match List.nth_error (tc_type C) j with
          | Some (Tf tn tm) =>
              type_update ts (to_ct_list (tn ++ [::(T_num T_i32)])) (CT_type tm)
          | None => CT_bot
          end
        else CT_bot  
    end
  | BI_local_get i =>
      match List.nth_error (tc_local C) i with
      | None => CT_bot
      | Some xx => type_update ts [::] (CT_type [::xx])
      end
  | BI_local_set i =>
      match List.nth_error (tc_local C) i with
      | None => CT_bot
      | Some xx => type_update ts [::CTA_some xx] (CT_type [::])
      end
  | BI_local_tee i =>
      match List.nth_error (tc_local C) i with
      | None => CT_bot
      | Some xx => type_update ts [::CTA_some xx] (CT_type [::xx])
      end
  | BI_global_get i =>
      match List.nth_error (tc_global C) i with
      | None => CT_bot
      | Some xx => type_update ts [::] (CT_type [::tg_t xx])
      end
  | BI_global_set i =>
      match List.nth_error (tc_global C) i with
      | None => CT_bot
      | Some xx =>
          if is_mut xx
          then type_update ts [::CTA_some (tg_t xx)] (CT_type [::])
          else CT_bot
      end
  | BI_load t tp_sx a off =>
    if (C.(tc_memory) != nil) && load_store_t_bounds a (option_projl tp_sx) t
    then type_update ts [::CTA_some (T_num T_i32)] (CT_type [::T_num t])
    else CT_bot
  | BI_store t tp a off =>
    if (C.(tc_memory) != nil) && load_store_t_bounds a tp t
    then type_update ts [::CTA_some (T_num T_i32); CTA_some (T_num t)] (CT_type [::])
    else CT_bot
  | BI_memory_size =>
    if C.(tc_memory) != nil
    then type_update ts [::] (CT_type [::(T_num T_i32)])
    else CT_bot
  | BI_memory_grow =>
    if C.(tc_memory) != nil
    then type_update ts [::CTA_some (T_num T_i32)] (CT_type [::(T_num T_i32)])
    else CT_bot
  | BI_memory_fill =>
    if C.(tc_memory) != nil
    then type_update ts [::CTA_some (T_num T_i32); CTA_some (T_num T_i32); CTA_some (T_num T_i32)] (CT_type [::])
    else CT_bot
  | BI_memory_copy =>
      match List.nth_error (tc_memory C) 0 with
      | None => CT_bot
      | Some _ =>
         type_update ts [::CTA_some (T_num T_i32); CTA_some (T_num T_i32); CTA_some (T_num T_i32)] (CT_type [::])
      end
  | BI_memory_init x =>
      match List.nth_error (tc_memory C) 0 with
      | None => CT_bot
      | Some tabtype =>
          match List.nth_error (tc_data C) x with
          | None => CT_bot
          | Some t =>
             type_update ts [::CTA_some (T_num T_i32); CTA_some (T_num T_i32); CTA_some (T_num T_i32)] (CT_type [::])
          end
      end
  | BI_data_drop x =>
      match List.nth_error (tc_data C) x with
      | None => CT_bot
      | Some _ => ts
      end
  | BI_table_get x =>
      match List.nth_error (tc_table C) x with
      | None => CT_bot
      | Some tabtype => type_update ts [::CTA_some (T_num T_i32)] (CT_type [::T_ref (tabtype.(tt_elem_type))])
      end
  | BI_table_set x =>
      match List.nth_error (tc_table C) x with
      | None => CT_bot
      | Some tabtype => type_update ts [::CTA_some (T_num T_i32); CTA_some (T_ref tabtype.(tt_elem_type))] (CT_type [::])
      end
  | BI_table_size x =>
      match List.nth_error (tc_table C) x with
      | None => CT_bot
      | Some _ => type_update ts [::] (CT_type [::T_num T_i32])
      end
  | BI_table_grow x =>
      match List.nth_error (tc_table C) x with
      | None => CT_bot
      | Some tabtype => type_update ts [::CTA_some (T_ref tabtype.(tt_elem_type)); CTA_some (T_num T_i32)] (CT_type [::T_num T_i32])
      end
  | BI_table_fill x =>
      match List.nth_error (tc_table C) x with
      | None => CT_bot
      | Some tabtype => type_update ts [::CTA_some (T_num T_i32); CTA_some (T_ref tabtype.(tt_elem_type)); CTA_some (T_num T_i32)] (CT_type [::])
      end
  | BI_table_copy x y =>
      match List.nth_error (tc_table C) x with
      | None => CT_bot
      | Some tabtype1 =>
          match List.nth_error (tc_table C) y with
          | None => CT_bot
          | Some tabtype2 =>
              if tabtype1.(tt_elem_type) == tabtype2.(tt_elem_type) then
                type_update ts [::CTA_some (T_num T_i32); CTA_some (T_num T_i32); CTA_some (T_num T_i32)] (CT_type [::])
              else CT_bot
          end
      end
  | BI_table_init x y =>
      match List.nth_error (tc_table C) x with
      | None => CT_bot
      | Some tabtype =>
          match List.nth_error (tc_elem C) y with
          | None => CT_bot
          | Some t =>
              if tabtype.(tt_elem_type) == t then
                type_update ts [::CTA_some (T_num T_i32); CTA_some (T_num T_i32); CTA_some (T_num T_i32)] (CT_type [::])
              else CT_bot
          end
      end
  | BI_elem_drop x =>
      match List.nth_error (tc_elem C) x with
      | None => CT_bot
      | Some _ => ts
      end
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

Definition check (C : t_context) (es : list basic_instruction) (ts : checker_type): checker_type :=
  List.fold_left (check_single C) es ts.

Definition b_e_type_checker (C : t_context) (es : list basic_instruction) (tf : function_type) : bool :=
  let: (Tf tn tm) := tf in
  c_types_agree (List.fold_left (check_single C) es (CT_type tn)) tm  .

(* TODO: This definition is kind of a duplication of inst_typing, to avoid more dependent definitions becoming Prop downstream *)

(* UPD: This in fact makes the soundness proof extremely tedious and dependent on the type_checker reflecting typing.
  I have edited the later functions to avoid using these. *)
(*
Definition inst_type_check (s : store_record) (i : instance) : t_context := {|
  (* TODO: ported this from option to list, but not too sure it's right *)
  tc_types_t := i_types i;
  tc_func_t := collect_at_inds (map cl_type (s_funcs s)) (i_funcs i);
  tc_global :=
    collect_at_inds
      (map (fun glob => {| tg_mut := glob.(g_mut); tg_t := typeof glob.(g_val) |}) s.(s_globals))
      i.(i_globs);
  tc_table :=
    collect_at_inds
      (map
        (fun t =>
          (* TODO: this is probably wrong? *)
          {| tt_limits := {| lim_min := 0; lim_max := Some (List.length t.(table_data)) |}; tt_elem_type := ELT_funcref |})
          s.(s_tables))
      i.(i_tab);
  tc_memory :=
    collect_at_inds
      (map
        (fun m =>
          (* TODO: this is probably wrong? *)
          {| lim_min := 0; lim_max := Some (List.length m.(mem_data)) |})
        s.(s_mems))
      i.(i_memory);
  tc_local := nil;
  tc_label := nil;
  tc_return := None;
|}.

Definition cl_type_check (s : store_record) (cl : function_closure) : bool :=
  match cl with
  | Func_native i tf ts es =>
    let '(Tf t1s t2s) := tf in
    let C := inst_type_check s i in
    let C' := upd_local_label_return C (app (tc_local C) (app t1s ts)) (app [::t2s] (tc_label  C)) (Some t2s) in
    b_e_type_checker C' es (Tf [::] t2s)
  | Func_host tf h => true
  end.
*)
End Host.

