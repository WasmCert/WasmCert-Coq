(** Wasm type checker **)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From HB Require Import structures.
From Wasm Require Export typing datatypes_properties operations subtyping_properties.
From Coq Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Flag for unreachable.
   The operand stack is represented in reverse direction (stack) *)
Record checker_type: Type :=
  { CT_type: list value_type;
    CT_unr: bool;
  }.

Notation "<< ts , unr >>" := (Build_checker_type ts unr) (at level 0).

Definition checker_type_eq_dec : forall v1 v2 : checker_type, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition checker_type_eqb v1 v2 : bool := checker_type_eq_dec v1 v2.
Definition eqchecker_typeP : Equality.axiom checker_type_eqb :=
  eq_dec_Equality_axiom checker_type_eq_dec.

HB.instance Definition checker_type_eqMixin := hasDecEq.Build checker_type eqchecker_typeP.

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

(** With subtyping in Wasm 2.0, br_table now needs to find the common subtype to be consumed. **)

Fixpoint common_lab_h (iss : seq tableidx) (lab_c : seq (seq value_type)) (ts : seq value_type) : option (seq value_type) :=
  match iss with
  | [::] => Some ts
  | i :: iss' =>
      match lookup_N lab_c i with
      | None => None
      | Some xx =>
          match ts_inf xx ts with
          | Some ts' => common_lab_h iss' lab_c ts'
          | None => None
          end
      end
  end.

Definition common_lab (iss : seq tableidx) (lab_c : seq (seq value_type)) : option (seq value_type) :=
  match iss with
  | [::] => None
  | i :: iss' =>
      match lookup_N lab_c i with
      | Some xx => common_lab_h iss' lab_c xx
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
          match unop_type_agree t op with
          | true => type_update ts [::T_num t] [::T_num t]
          | false => None
          end
      | BI_binop t op =>
          match binop_type_agree t op with
          | true => type_update ts [::T_num t; T_num t] [::T_num t]
          | false => None
          end
      | BI_testop t _ =>
          if is_int_t t
          then type_update ts [::(T_num t)] [::(T_num T_i32)]
          else None
      | BI_relop t op =>
          match relop_type_agree t op with
          | true => type_update ts [::T_num t; T_num t] [::T_num T_i32]
          | false => None
          end
      | BI_cvtop t2 op t1 sx =>
          if cvtop_valid t2 op t1 sx
          then type_update ts [::(T_num t1)] [::(T_num t2)]
          else None
      | BI_vunop sh op =>
          type_update ts [::T_vec T_v128] [::T_vec T_v128]
      | BI_vbinop sh op =>
          type_update ts [::T_vec T_v128; T_vec T_v128] [::T_vec T_v128]
      | BI_vternop sh op =>
          type_update ts [::T_vec T_v128; T_vec T_v128; T_vec T_v128] [::T_vec T_v128]
      | BI_vtestop sh tv =>
          type_update ts [::T_vec T_v128] [::T_num T_i32]
      | BI_vshiftop sh sv =>
          type_update ts [::T_num T_i32; T_vec T_v128] [::T_vec T_v128]
      | BI_splat_vec shape =>
          type_update ts [::T_num (typeof_shape_unpacked shape)] [::T_vec T_v128]
      | BI_extract_vec shape sx x =>
          if N.ltb x (shape_dim shape) then
            type_update ts [::T_vec T_v128] [::T_num (typeof_shape_unpacked shape)]
          else None
      | BI_replace_vec shape x =>
          if N.ltb x (shape_dim shape) then
            type_update ts [::T_num (typeof_shape_unpacked shape); T_vec T_v128] [::T_vec T_v128]
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
          match common_lab (iss ++ [::i]) (tc_labels C) with
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
      | BI_return_call x =>
          match C.(tc_return) with
          | Some t2s =>
              match lookup_N (tc_funcs C) x with
              | None => None 
              | Some (Tf tn tm) =>
                  if (t2s == tm) then
                    type_update_top ts (tn) nil
                  else None
              end
          | None => None
          end
      | BI_return_call_indirect x y =>
          match C.(tc_return) with
          | Some t2s =>
              match lookup_N C.(tc_tables) x with
              | Some tabt =>
                  if tabt.(tt_elem_type) == T_funcref then
                    match lookup_N (tc_types C) y with
                    | Some (Tf tn tm) =>
                        if (t2s == tm) then
                          type_update_top ts ((T_num T_i32 :: tn)) nil
                        else None
                    | None => None 
                    end
                  else None
              | None => None
              end
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
      | BI_load t tp_sx marg =>
          match lookup_N C.(tc_mems) 0%N with
          | Some _ =>
              if load_store_t_bounds marg.(memarg_align) (option_projl tp_sx) t
              then type_update ts [::(T_num T_i32)] [::T_num t]
              else None
          | None => None
          end
      | BI_load_vec lvarg marg =>
          match lookup_N C.(tc_mems) 0%N with
          | Some _ =>
              if load_vec_bounds lvarg marg
              then type_update ts [::(T_num T_i32)] [::T_vec T_v128]
              else None
          | None => None
          end
      | BI_load_vec_lane width marg x =>
          match lookup_N C.(tc_mems) 0%N with
          | Some _ =>
              if load_vec_lane_bounds width marg x
              then type_update ts [:: T_vec T_v128; T_num T_i32] [::T_vec T_v128]
              else None
          | None => None
          end
      | BI_store t tp marg =>
          match lookup_N C.(tc_mems) 0%N with
          | Some _ =>
              if load_store_t_bounds marg.(memarg_align) tp t
              then type_update ts [::T_num t; T_num T_i32] [::]
              else None
          | None => None
          end
      | BI_store_vec_lane width marg x =>
          match lookup_N C.(tc_mems) 0%N with
          | Some _ =>
              if load_vec_lane_bounds width marg x
              then type_update ts [::T_vec T_v128; T_num T_i32] [::]
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
