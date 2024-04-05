(** Wasm type checker **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import BinNat.
Require Import common operations typing datatypes_properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* flag for unreachable. Operand stack is represented in reverse direction (stack) *)
Record checker_type: Type :=
  { CT_type: list value_type;
    CT_unr: bool;
  }.

Notation "<< ts , unr >>" := (Build_checker_type ts unr) (at level 5).

Definition checker_type_eq_dec : forall v1 v2 : checker_type, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition checker_type_eqb v1 v2 : bool := checker_type_eq_dec v1 v2.
Definition eqchecker_typeP : Equality.axiom checker_type_eqb :=
  eq_dec_Equality_axiom checker_type_eq_dec.

Canonical Structure checker_type_eqMixin := EqMixin eqchecker_typeP.
Canonical Structure checker_type_eqType := Eval hnf in EqType checker_type checker_type_eqMixin.

Fixpoint consume (ct: checker_type) (cons : list value_type) : option checker_type :=
  match cons with
  | nil => Some ct
  | t_cons :: cons' =>
      match ct.(CT_type) with
      | nil =>
          match ct.(CT_unr) with
          | true => Some <<nil, true>>
          | false => None
          end
      | t :: ts' =>
          if t <t: t_cons then
            consume <<ts', ct.(CT_unr)>> cons'
          else None
      end
  end.

Definition produce (t1 : checker_type) (t2: list value_type) : checker_type :=
  <<t2 ++ t1.(CT_type), t1.(CT_unr)>>.

Definition type_update (ct : checker_type) (cons : list value_type) (prods : list value_type) : option checker_type :=
  match consume ct cons with
  | Some ct' => Some (produce ct' prods)
  | None => None
  end.

Definition type_update_top (ct : checker_type) (cons : list value_type) (prods : list value_type) : option checker_type :=
  match consume ct cons with
  | Some _ => Some <<prods, true>>
  | None => None
  end.

(* Needs an update in GC *)
Definition value_type_select (t1 t2: value_type) : option value_type :=
  if is_numeric_type t1 && is_numeric_type t2 then
    if t1 == T_bot then Some t2
    else if t2 == T_bot then Some t1
         else if (t1 == t2) then Some t1
              else None
  else None.

Definition type_update_select (ct : checker_type) (ots: option (list value_type)) : option checker_type :=
  match ots with
  | Some [::vt] => type_update ct ([:: T_num T_i32; vt; vt]) [::vt]
  | Some _ => None
  | None =>
      match ct.(CT_type) with
      | [:: t1; t2] =>
          if (is_numeric_type t2) && ct.(CT_unr) then type_update ct [::T_num T_i32; t2] [::t2]
          else None
      | t1 :: t2 :: t3 :: _ =>
          match value_type_select t2 t3 with
          | Some tsup =>
             type_update ct [::T_num T_i32; t2; t3] [::tsup]
          | None => None
          end
      | _ =>
          if ct.(CT_unr) then type_update ct [::T_num T_i32] [::T_bot]
          else None
      end
  end.

Definition type_update_ref_is_null (ct : checker_type) : option checker_type :=
  match ct.(CT_type) with
  | nil =>
      if ct.(CT_unr) then
        Some <<[::T_num T_i32], true>>
      else None
  | t :: ts' =>
      if is_ref_t t then
        Some <<(T_num T_i32 :: ts'), ct.(CT_unr)>>
      else None
  end.

Definition type_update_drop (ct : checker_type) : option checker_type :=
  match ct.(CT_type) with
  | nil =>
      if ct.(CT_unr) then
        Some <<nil, true>>
      else None
  | t :: ts' =>
      Some <<ts', ct.(CT_unr)>>
  end.

Fixpoint same_lab_h (iss : seq tableidx) (lab_c : seq (seq value_type)) (ts : seq value_type) : option (seq value_type) :=
  match iss with
  | [::] => Some ts
  | i :: iss' =>
      match lookup_N lab_c i with
      | None => None
      | Some xx =>
          if xx == ts then same_lab_h iss' lab_c xx
          else None
      end
  end.

(**
   Br_table iss i needs to make sure that Br (each element in iss) and Br i would 
     consume the same type. See section 3.3.5.8 in the official spec.
**)
Definition same_lab (iss : seq tableidx) (lab_c : seq (seq value_type)) : option (seq value_type) :=
  match iss with
  | [::] => None
  | i :: iss' =>
      match lookup_N lab_c i with
      | Some xx => same_lab_h iss' lab_c xx
      | None => None
      end
  end.

Definition c_types_agree (ct : checker_type) (ts' : seq value_type) : bool :=
  match ct.(CT_unr) with
  | false => ct.(CT_type) <ts: ts'
  | true => ct.(CT_type) <ts: (take (size ct.(CT_type)) ts')
  end.

(* Using an auxiliary context with all locals/labels/returns reversed for optimisation, avoiding excessive reversing during execution *)
Fixpoint check_single (C : t_context) (ct : option checker_type) (be : basic_instruction) : option checker_type :=
  let b_e_type_checker (C : t_context) (es : list basic_instruction) (tf : function_type) : bool :=
    let: (Tf tn tm) := tf in
    match List.fold_left (check_single C) es (Some <<tn, false>>) with
    | Some ts => c_types_agree ts tm
    | None => false
    end
  in
  match ct with
  | None => None
  | Some ts =>
      match be with
      | BI_const_num v => type_update ts [::] [::T_num (typeof_num v)]
      | BI_const_vec v => type_update ts [::] [::T_vec (typeof_vec v)]
      | BI_ref_null t => type_update ts [::]  [::T_ref t]
      | BI_ref_is_null => type_update_ref_is_null ts
      | BI_ref_func x =>
          match lookup_N C.(tc_funcs) x with
          | Some _ =>
              if x \in C.(tc_refs)
              then type_update ts [::] [::T_ref T_funcref]
              else None
          | _ => None
          end
      | BI_unop t op =>
          match op with
          | Unop_i _ => if is_int_t t
                       then type_update ts [::(T_num t)] [::T_num t]
                       else None
          | Unop_f _ => if is_float_t t
                       then type_update ts [::(T_num t)] [::T_num t]
                       else None
          | Unop_extend _ =>
              (* Technically, this needs to check validity of the extend arg; but such instruction can never arise from parsing *)
              if is_int_t t
              then type_update ts [::(T_num t)] [::T_num t]
              else None
          end
      | BI_binop t op =>
          match op with
          | Binop_i _ => if is_int_t t
                        then type_update ts [::(T_num t); (T_num t)] [::(T_num t)]
                        else None
          | Binop_f _ => if is_float_t t
                        then type_update ts [::(T_num t); (T_num t)] [::(T_num t)]
                        else None
          end
      | BI_testop t _ =>
          if is_int_t t
          then type_update ts [::(T_num t)] [::(T_num T_i32)]
          else None
      | BI_relop t op =>
          match op with
          | Relop_i _ => if is_int_t t
                        then type_update ts [::(T_num t); (T_num t)] [::(T_num T_i32)]
                        else None
          | Relop_f _ => if is_float_t t
                        then type_update ts [::(T_num t); (T_num t)] [::(T_num T_i32)]
                        else None
          end
      | BI_cvtop t2 op t1 sx =>
          if cvtop_valid t2 op t1 sx
          then type_update ts [::(T_num t1)] [::(T_num t2)]
          else None
      | BI_unreachable => Some <<nil, true>>
      | BI_nop => Some ts
      | BI_drop => type_update_drop ts
      | BI_select ot => type_update_select ts ot
      | BI_block bt es =>
          match expand_t C bt with
          | Some (Tf tn tm) =>
              if b_e_type_checker (upd_label C ([::tm] ++ tc_labels C)) es (Tf tn tm)
              then type_update ts (tn) tm
              else None
          | None => None
          end
      | BI_loop bt es =>
          match expand_t C bt with
          | Some (Tf tn tm) =>
              if b_e_type_checker (upd_label C ([::tn] ++ tc_labels C)) es (Tf tn tm)
              then type_update ts (tn) tm
              else None
          | None => None
          end
      | BI_if bt es1 es2 =>
          match expand_t C bt with
          | Some (Tf tn tm) =>
              if b_e_type_checker (upd_label C ([::tm] ++ tc_labels C)) es1 (Tf tn tm)
                 && b_e_type_checker (upd_label C ([::tm] ++ tc_labels C)) es2 (Tf tn tm)
              then type_update ts ((T_num T_i32 :: tn)) tm
              else None
          | None => None
          end
      | BI_br i =>
          match lookup_N (tc_labels C) i with
          | Some xx => type_update_top ts (xx) nil
          | None => None 
          end
      | BI_br_if i =>
          match lookup_N (tc_labels C) i with
          | Some xx => type_update ts ((T_num T_i32 :: xx)) xx
          | None => None 
          end
      | BI_br_table iss i =>
          match same_lab (iss ++ [::i]) (tc_labels C) with
          | None => None
          | Some tls => type_update_top ts ((T_num T_i32 :: tls)) nil
          end
      | BI_return =>
          match tc_return C with
          | None => None
          | Some tls => type_update_top ts (tls) nil
          end
      | BI_call x =>
          match lookup_N (tc_funcs C) x with
          | None => None 
          | Some (Tf tn tm) =>
              type_update ts (tn) tm
          end
      | BI_call_indirect x y =>
          match lookup_N C.(tc_tables) x with
          | Some tabt =>
              if tabt.(tt_elem_type) == T_funcref then
                match lookup_N (tc_types C) y with
                | Some (Tf tn tm) =>
                    type_update ts ((T_num T_i32 :: tn)) tm
                | None => None 
                end
              else None
          | None => None
          end
      | BI_local_get i =>
          match lookup_N (tc_locals C) i with
          | None => None 
          | Some xx => type_update ts [::] [::xx]
          end
      | BI_local_set i =>
          match lookup_N (tc_locals C) i with
          | None => None 
          | Some xx => type_update ts [::xx] [::]
          end
      | BI_local_tee i =>
          match lookup_N (tc_locals C) i with
          | None => None 
          | Some xx => type_update ts [::xx] [::xx]
          end
      | BI_global_get i =>
          match lookup_N (tc_globals C) i with
          | None => None 
          | Some xx => type_update ts [::] [::tg_t xx]
          end
      | BI_global_set i =>
          match lookup_N (tc_globals C) i with
          | None => None 
          | Some xx =>
              if is_mut xx
              then type_update ts [::(tg_t xx)] [::]
              else None
          end
      | BI_table_get x =>
          match lookup_N (tc_tables C) x with
          | None => None 
          | Some tabt =>
              type_update ts [::(T_num T_i32)] [::T_ref tabt.(tt_elem_type)]
          end
      | BI_table_set x =>
          match lookup_N (tc_tables C) x with
          | None => None 
          | Some tabt =>
              type_update ts [::(T_ref tabt.(tt_elem_type)); (T_num T_i32)] nil
          end
      | BI_table_size x =>
          match lookup_N (tc_tables C) x with
          | None => None 
          | Some tabt =>
              type_update ts nil [::T_num T_i32]
          end
      | BI_table_grow x =>
          match lookup_N (tc_tables C) x with
          | None => None 
          | Some tabt =>
              type_update ts [::T_num T_i32; (T_ref tabt.(tt_elem_type))] [::T_num T_i32]
          end
      | BI_table_fill x =>
          match lookup_N (tc_tables C) x with
          | None => None 
          | Some tabt =>
              type_update ts [::(T_num T_i32); (T_ref tabt.(tt_elem_type)); (T_num T_i32)] nil
          end
      | BI_table_copy x y =>
          match lookup_N (tc_tables C) x with
          | None => None 
          | Some tabt1 =>
              match lookup_N (tc_tables C) y with
              | Some tabt2 =>
                  if tabt1.(tt_elem_type) == tabt2.(tt_elem_type)
                  then type_update ts [::(T_num T_i32); (T_num T_i32); (T_num T_i32)] nil
                  else None
              | None => None
              end
          end
      | BI_table_init x y =>
          match lookup_N (tc_tables C) x with
          | None => None 
          | Some tabt =>
              match lookup_N (tc_elems C) y with
              | Some t =>
                  if tabt.(tt_elem_type) == t
                  then type_update ts [::(T_num T_i32); (T_num T_i32); (T_num T_i32)] nil
                  else None
              | None => None
              end
          end
      | BI_elem_drop x =>
          match lookup_N (tc_elems C) x with
          | None => None 
          | Some tabt => Some ts
          end
      | BI_load t tp_sx a off =>
          match lookup_N C.(tc_mems) 0%N with
          | Some _ =>
              if load_store_t_bounds a (option_projl tp_sx) t
              then type_update ts [::(T_num T_i32)] [::T_num t]
              else None
          | None => None
          end
      | BI_store t tp a off =>
          match lookup_N C.(tc_mems) 0%N with
          | Some _ =>
              if load_store_t_bounds a tp t
              then type_update ts [::T_num t; T_num T_i32] [::]
              else None
          | None => None
          end
      | BI_memory_size =>
          match lookup_N C.(tc_mems) 0%N with
          | Some _ =>
              type_update ts [::] [::(T_num T_i32)]
          | None => None
          end
      | BI_memory_grow =>
          match lookup_N C.(tc_mems) 0%N with
          | Some _ =>
              type_update ts [::(T_num T_i32)] [::(T_num T_i32)]
          | None => None
          end
      | BI_memory_fill =>
          match lookup_N C.(tc_mems) 0%N with
          | Some _ =>
              type_update ts [::(T_num T_i32); (T_num T_i32); (T_num T_i32)] nil
          | None => None
          end
      | BI_memory_copy =>
          match lookup_N C.(tc_mems) 0%N with
          | Some _ =>
              type_update ts [::(T_num T_i32); (T_num T_i32); (T_num T_i32)] nil
          | None => None
          end
      | BI_memory_init x =>
          match lookup_N C.(tc_mems) 0%N with
          | Some _ =>
              match lookup_N C.(tc_datas) x with
              | Some _ =>
                  type_update ts [::(T_num T_i32); (T_num T_i32); (T_num T_i32)] nil
              | None => None
              end
          | None => None
          end
      | BI_data_drop x =>
          match lookup_N C.(tc_datas) x with
          | Some _ => Some ts
          | None => None
          end
      end
  end.


Definition check (C : t_context) (es : list basic_instruction) (ct : option checker_type): option checker_type :=
  List.fold_left (check_single C) es ct.

Definition b_e_type_checker_aux (C : t_context) (es : list basic_instruction) (tf : function_type) : bool :=
  let: (Tf tn tm) := tf in
  match (List.fold_left (check_single C) es (Some <<tn, false>>)) with
  | Some ts =>
      c_types_agree ts tm
  | None => false
  end.

(*
  A context with local/label/return reversed for optimised validation.
*)

Definition rev_tf (tf: function_type) :=
  match tf with
  | Tf tn tm => Tf (rev tn) (rev tm)
  end.

Definition context_reverse (C: t_context): t_context :=
  {|
    tc_types := map rev_tf C.(tc_types);
    tc_funcs := map rev_tf C.(tc_funcs);
    tc_tables := C.(tc_tables);
    tc_mems := C.(tc_mems);
    tc_globals := C.(tc_globals);
    tc_elems := C.(tc_elems);
    tc_datas := C.(tc_datas);
    tc_locals := C.(tc_locals);
    tc_labels := map rev C.(tc_labels);
    tc_return := option_map rev C.(tc_return);
    tc_refs := C.(tc_refs);
  |}.

Definition b_e_type_checker (C : t_context) (es : list basic_instruction) (tf : function_type) : bool :=
  let: (Tf tn tm) := tf in
  b_e_type_checker_aux (context_reverse C) es (Tf (rev tn) (rev tm)).
