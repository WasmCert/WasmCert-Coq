(* soundness of the Wasm interpreter *)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp
Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import wasm opsem interpreter wasm_properties_aux.


Section Host.

(* TODO: The host should be defined as a mixin. *)
Variable mem_grow_impl : mem -> nat -> option mem.
Hypothesis mem_grow_impl_correct :
  forall m n m',
    mem_grow_impl m n = Some m' ->
    mem_grow m n = m'.

Variable host_apply_impl : store_record -> function_type -> wasm.host -> list value -> option (store_record * list value).
Hypothesis host_apply_impl_correct :
  forall s tf h vs m',
    host_apply_impl s tf h vs = Some m' ->
    exists hs, wasm.host_apply s tf h vs hs = Some m'.

Let run_step := run_step mem_grow_impl host_apply_impl.

Hint Constructors reduce_simple : core.
Hint Constructors reduce : core.

Lemma r_eliml: forall s vs es s' vs' es' lconst i,
    const_list lconst ->
    reduce s vs es i s' vs' es' ->
    reduce s vs (lconst ++ es) i s' vs' (lconst ++ es').
Proof.
  move => s vs es s' vs' es' lconst i HConst H.
  eapply r_label; try apply lfilled_Ind_Equivalent.
  - apply H.
  - replace (lconst++es) with (lconst++es++[::]); first by apply LfilledBase.
    f_equal. by apply cats0.
  - replace (lconst++es') with (lconst++es'++[::]); first by apply LfilledBase.
    f_equal. by apply cats0.
Qed.
    
Lemma r_elimr: forall s vs es s' vs' es' i les,
    reduce s vs es i s' vs' es' ->
    reduce s vs (es ++ les) i s' vs' (es' ++ les).
Proof.
  move => s vs es s' vs' es' i les H.
  eapply r_label; try apply lfilled_Ind_Equivalent.
  - apply H.
  - replace (es++les) with ([::]++es++les) => //. by apply LfilledBase.
  - replace (es'++les) with ([::]++es'++les) => //. by apply LfilledBase.
Qed.

Lemma r_eliml_empty: forall s vs es s' vs' lconst i,
    const_list lconst ->
    reduce s vs es i s' vs' [::] ->
    reduce s vs (lconst ++ es) i s' vs' lconst.
Proof.
  move => s vs es s' vs' lconst i HConst H.
  assert (reduce s vs (lconst++es) i s' vs' (lconst++[::])); first by apply r_eliml.
  by rewrite cats0 in H0.
Qed.

Lemma r_elimr_empty: forall s vs es s' vs' i les,
    reduce s vs es i s' vs' [::] ->
    reduce s vs (es ++ les) i s' vs' les.
Proof.
  move => s vs es s' vs' i les H.
  assert (reduce s vs (es++les) i s' vs' ([::] ++les)); first by apply r_elimr.
  by rewrite cat0s in H0.
Qed.

Lemma split3: forall {X:Type} (l:seq X) n v,
    n < size l ->
    List.nth_error l n = Some v ->
    l = (take n l) ++ [::v] ++ (drop (n+1) l).
Proof.
  move => X l. elim: l => //=.
  move => a l IH n v HLen HNth.
  destruct n => //=.
  - simpl in HNth. inversion HNth. f_equal. by rewrite drop0.
  - f_equal. apply IH => //=.
Qed.
  
  
Lemma rev_move: forall {X:Type} (l1 l2:seq X),
  rev l1 = l2 -> l1 = rev l2.
Proof.
  move => X l1 l2 HRev. rewrite -HRev. symmetry. by apply revK.
Qed.

Lemma const_list_cons : forall a l,
  const_list (a :: l) = is_const a && const_list l.
Proof.
  by [].
Qed.

Lemma v_to_e_take_drop_split: forall l n,
  v_to_e_list l = v_to_e_list (take n l) ++ v_to_e_list (drop n l).
Proof.
  move => l n. rewrite v_to_e_cat. by rewrite cat_take_drop.
Qed.

Lemma v_to_e_rev: forall l,
  v_to_e_list (rev l) = rev (v_to_e_list l).
Proof.
  elim => //=.
  move => a l IH. rewrite rev_cons. rewrite -cats1. rewrite -v_to_e_cat.
  rewrite rev_cons. rewrite -cats1. by rewrite -IH.
Qed.

Ltac simplify_hypothesis Hb :=
  repeat rewrite length_is_size in Hb;
  repeat lazymatch type of Hb with
  | ?b = true => fold (is_true b) in Hb
  | is_true (es_is_trap _) => move/es_is_trapP: Hb => Hb
  | is_true (const_list (_ :: _)) => rewrite const_list_cons in Hb
  | _ = _ => rewrite Hb
  | context C' [size (rev _)] => rewrite size_rev in Hb
  end.

Ltac simplify_goal :=
  repeat match goal with H: _ |- _ => simplify_hypothesis H end.

Ltac explode_and_simplify :=
  repeat lazymatch goal with
  | |- ?T = _ -> _ =>
    lazymatch T with
    | context C [split_n ?l ?n] => rewrite (split_n_is_take_drop l n)
    | context C [vs_to_es ?l] => rewrite/vs_to_es
    | context C [match ?b with true => ?v1 | false => ?v2 end] =>
      let Hb := fresh "if_expr" in
      destruct b eqn:Hb;
      simplify_hypothesis Hb;
      try by []
    | context C [match (rev ?lconst) with
                 | _ :: _ => _ 
                 | _ => _
                 end] =>
      let HRevConst := fresh "HRevConst" in 
      destruct (rev lconst) eqn:HRevConst;
      simplify_hypothesis HRevConst;
      try by []
    | context C [match ?v with
                 | ConstInt32 _ => _
                 | _ => _
                 end] =>
      destruct v;
      try by []
    | context C [match ?v with
                 | Some _ => _
                 | _ => _
                 end] =>
      let Hv := fresh "option_expr" in
      destruct v eqn:Hv;
      simplify_hypothesis Hv;
      try by []
    | context C [expect (?X) ?f ?err] =>
       let HExpect := fresh "HExpect" in
       destruct X eqn:HExpect;
       simplify_hypothesis HExpect;
       simpl;
       try by []
    | context C [match ?l with
                 | _ :: _ => _
                 | _ => _
                 end] =>
      destruct l;
      try by []
    end
  end;
  repeat first [
      rewrite drop_rev
    | rewrite take_rev
    | rewrite revK ].

Ltac subst_rev_const_list :=
 lazymatch goal with
 | HRevConst: rev ?lconst = ?h :: ?t |- _ =>
   apply rev_move in HRevConst; rewrite HRevConst; rewrite -cat1s; rewrite rev_cat;
   rewrite -v_to_e_cat; rewrite -catA
 end.

Ltac pattern_match :=
  lazymatch goal with
  | |- (_, _, _) = (_, _, _) -> _ =>
    let H := fresh in
    move=> H; inversion H; subst; clear H
  end.

Ltac stack_frame :=
  repeat lazymatch goal with
  | |- reduce _ _ (_ :: ?l) _ _ _ _ =>
    rewrite - cat1s
  | |- reduce _ _ (?l1 ++ ?l2 :: ?l3) _ _ _ ((?l5 ++ ?l4) ++ ?l3) =>
    rewrite -cat1s; rewrite catA;
    apply r_elimr; try apply r_eliml; try apply v_to_e_is_const_list
  | |- reduce _ _ (?l1 ++ ?l2 :: ?l3) _ _ _ (?l5 ++ ?l3) =>
    rewrite -cat1s; rewrite catA;
    apply r_elimr; try apply r_eliml_empty; try apply v_to_e_is_const_list
  | |- reduce _ _ (v_to_e_list ?l1 ++ _) _ _ _ (v_to_e_list (take ?n ?l1) ++ _) =>
    rewrite (v_to_e_take_drop_split l1 n); rewrite -catA;
    apply r_eliml; try apply v_to_e_is_const_list
  end.

Lemma run_step_soundness : forall d i s vs es s' vs' es',
    run_step d i (s, vs, es) = (s', vs', RS_normal es') ->
    reduce s vs es i s' vs' es'.
Proof with eauto.
  move => d i s vs es s' vs' es'. simpl.
  (* split_vals_e es: takes the maximum initial segment of es whose elements
     are all of the form Basic EConst v; returns a pair of list (ves, es') where
     ves are those v's in that initial segment and es is the remainder of the original
     es. *)
  (* v_to_e_list: some kind of the opposite of above: takes a list of v and gives back
     a list where each v is mapped to Basic (EConst v). *)
  
  (* I think this is what's happening here: find the first non-EConst thing in es (which
     is an operation); if it's trap then end(???) if there are more operations in es
     and vs is not empty; or crash otherwise. Else if e is not trap then try to execute
     e and see what happens, according to run_one_step. *)
  destruct (split_vals_e es) as [lconst les] eqn:HSplitVals.
  apply split_vals_e_v_to_e_duality in HSplitVals. rewrite HSplitVals. clear HSplitVals.
  destruct les as [|a les'] eqn:Hles => //.
  - unfold run_one_step. elim: d.
    + (* Base case *)
      case a => //. move => b.
      { (* Basic b *)
        destruct b => //.
        - (* Basic Unreachable *)
          explode_and_simplify; pattern_match; stack_frame. by eauto.
            
        - (* Basic Nop *)
          explode_and_simplify; pattern_match; stack_frame. by eauto.
            
        - (* Basic Drop *)
          explode_and_simplify; pattern_match; stack_frame; subst_rev_const_list.
          apply r_eliml_empty; first by apply v_to_e_is_const_list.
          simpl. by eauto.
          
        - (* Basic Select *)
          explode_and_simplify; pattern_match; stack_frame; subst_rev_const_list.
          + (* Select_true *)
            do 3 (rewrite -cat1s; rewrite rev_cat).
            do 2 rewrite -catA.
            replace (rev (v::l)) with (rev l ++ [::v]).
            repeat rewrite -v_to_e_cat.
            rewrite -catA.
            apply r_eliml; first by apply v_to_e_is_const_list.
            simpl. by eauto.
            (* replace *) rewrite rev_cons. by rewrite -cats1.
          + (* Select_false *)    
            do 3 (rewrite -cat1s; rewrite rev_cat).
            do 2 rewrite -catA.
            repeat rewrite -v_to_e_cat.
            rewrite -catA.
            apply r_eliml; first by apply v_to_e_is_const_list.
            simpl. apply r_simple. apply rs_select_false.
            move/eqP in if_expr0. by apply/eqP.

        - (* Basic Block *) destruct f.
          explode_and_simplify; pattern_match; stack_frame.
          apply r_simple. eapply rs_block; first by apply v_to_e_is_const_list.
          eauto. repeat rewrite length_is_size.
          rewrite v_to_e_drop_exchange. rewrite size_drop. rewrite v_to_e_size.
          by rewrite subKn. by [].
                        
        - (* Basic loop *)
          destruct f.
          explode_and_simplify; pattern_match; stack_frame.
          apply r_simple. eapply rs_loop => //=. 
          +(*1*) by apply v_to_e_is_const_list.
          +(*2*) repeat rewrite length_is_size.
            rewrite v_to_e_drop_exchange. rewrite size_drop. rewrite v_to_e_size.
              by rewrite subKn.

        - (* Basic If *)
          explode_and_simplify; pattern_match; stack_frame; subst_rev_const_list; try (apply r_eliml; first by apply v_to_e_is_const_list) => //=.
          + apply r_simple. by apply rs_if_false.
          + apply r_simple. apply rs_if_true. apply/eqP.
            by move/eqP in if_expr0.

        - (* Basic Br_if *)
          explode_and_simplify; pattern_match; stack_frame; subst_rev_const_list.
          + apply r_eliml_empty; first by apply v_to_e_is_const_list.
            apply r_simple. by apply rs_br_if_false.
          + apply r_eliml; first by apply v_to_e_is_const_list.
            simpl. apply r_simple. apply rs_br_if_true. apply/eqP.
              by move/eqP in if_expr0.

        - (* Basic Br_table *)
          explode_and_simplify; pattern_match; stack_frame; subst_rev_const_list;
          (apply r_eliml => //=; first by apply v_to_e_is_const_list).
          + apply r_simple. apply rs_br_table.
            * by rewrite length_is_size.
            * simpl. by apply/eqP.
          + apply r_simple. eapply rs_br_table_length.
            rewrite length_is_size. move/ltP in if_expr0. apply/leP. omega.

        - (* Basic (Call i0) *)
          explode_and_simplify; pattern_match; stack_frame.
          rewrite cats0. apply r_call. by apply/eqP.
          
        - (* Basic (Call_indirect i0) *)
          explode_and_simplify; pattern_match; stack_frame; subst_rev_const_list;
            (apply r_eliml; first by apply v_to_e_is_const_list) => //=.
          + eapply r_call_indirect_success. simpl. by apply/eqP.
              by eauto. by auto.
          + eapply r_call_indirect_failure1. simpl. apply/eqP. by eauto.
            move/eqP in if_expr0. by apply/eqP.
          + eapply r_call_indirect_failure2. simpl. by apply/eqP.
            
        - (* Basic (Get_local i0) *)
          explode_and_simplify; pattern_match; stack_frame.
          rewrite rev_cons. rewrite revK. rewrite -cats1. rewrite -v_to_e_cat.
          apply r_eliml; first by apply v_to_e_is_const_list.
          rewrite (split3 if_expr0 HExpect).
          apply r_get_local. rewrite length_is_size. rewrite size_take.
          by rewrite if_expr0.
            
        - (* Basic (Set_local i0) *)
          explode_and_simplify; pattern_match.
          rewrite - update_list_at_is_set_nth => //=.         
          stack_frame; subst_rev_const_list => //=.
          apply r_eliml_empty; first by apply v_to_e_is_const_list.
          apply r_set_local. by rewrite length_is_size.
          
        - (* Basic (Tee_local i0) *)
          explode_and_simplify; pattern_match; stack_frame; subst_rev_const_list.
          simpl. repeat rewrite rev_cons. repeat rewrite -cats1.
          repeat rewrite -v_to_e_cat. repeat rewrite -catA.
          apply r_eliml; first by apply v_to_e_is_const_list.
          apply r_simple. by apply rs_tee_local.
    
        - (* Basic (Get_global i0) *)
          explode_and_simplify; pattern_match; stack_frame.
          rewrite rev_cons. rewrite -cats1. rewrite revK. rewrite -v_to_e_cat.
          apply r_eliml; first by apply v_to_e_is_const_list.
          apply r_get_global. by apply/eqP.

        - (* Basic (Set_global i0) *)
          explode_and_simplify; pattern_match; stack_frame; subst_rev_const_list.
          simpl. apply r_eliml_empty; first by apply v_to_e_is_const_list.
            by apply r_set_global.

        - (* Basic (Load v o a0 s0) *)
          explode_and_simplify; try (pattern_match; stack_frame; subst_rev_const_list).
          destruct p => //=.
          destruct p => //=; explode_and_simplify; pattern_match; stack_frame; subst_rev_const_list; simpl; try (rewrite rev_cons; rewrite -cats1; rewrite -v_to_e_cat; simpl); try (apply r_eliml; first by apply v_to_e_is_const_list).
          + eapply r_load_packed_success. by eauto. apply/eqP. by eauto. by [].
          + eapply r_load_packed_failure. apply/eqP. by eauto. by eauto. by [].
          + simpl. rewrite rev_cons; rewrite -cats1; rewrite -v_to_e_cat; simpl.
            apply r_eliml; first by apply v_to_e_is_const_list.
            eapply r_load_success. by eauto. apply/eqP. by eauto. by apply/eqP.
          + apply r_eliml; first by apply v_to_e_is_const_list.
            simpl. eapply r_load_failure. by eauto. by eauto. by apply/eqP.
          + by destruct p => //=.
          + by destruct p => //=.
          + by destruct p => //=.
            
        - (* Basic (Store v o a0 s0) *)
          explode_and_simplify; pattern_match; stack_frame; subst_rev_const_list => //=; rewrite rev_cons; rewrite -cats1; rewrite -v_to_e_cat; rewrite -catA; simpl; try (apply r_eliml; first by apply v_to_e_is_const_list); try (apply r_eliml_empty; first by apply v_to_e_is_const_list).
          + eapply r_store_packed_success => //=. apply/eqP. by eauto. by apply/eqP.
          + eapply r_store_packed_failure => //=. by eauto. by eauto. by [].
          + eapply r_store_success => //=. by eauto. by [].
          + eapply r_store_failure => //=. by eauto. apply/eqP. by eauto. by [].

        - (* Basic Current_memory *)
          explode_and_simplify; pattern_match; stack_frame.
          rewrite rev_cons; rewrite -cats1; rewrite -v_to_e_cat; rewrite revK.
          apply r_eliml; first by apply v_to_e_is_const_list.
          eapply r_current_memory => //=. by eauto. by [].

        - (* Basic Grow_memory *)
          explode_and_simplify; pattern_match; stack_frame; subst_rev_const_list => //=.
          rewrite rev_cons; rewrite -cats1; rewrite -v_to_e_cat.
          apply r_eliml; first by apply v_to_e_is_const_list.
          simpl. eapply r_grow_memory_success => //=. by [].
            by apply mem_grow_impl_correct in HExpect0.

        (* TODO: ask about usage of type markups e.g. Binop_i/f, T_i32/i64/f32/f64 *)
            
        - (* Basic Unop_i v u *)
          explode_and_simplify; destruct v => //=; pattern_match; stack_frame; subst_rev_const_list => //=; try (rewrite rev_cons; rewrite -cats1; rewrite -v_to_e_cat); try apply r_eliml; try apply v_to_e_is_const_list; try apply r_simple.
          (* Somehow the constructor hints no longer work *)
          + by apply rs_unop_i32.
          + by apply rs_unop_i64.

        - (* Basic Unop_f v u *)
          explode_and_simplify; destruct v => //; pattern_match; stack_frame; subst_rev_const_list => //; try (rewrite rev_cons; rewrite -cats1; rewrite -v_to_e_cat); try apply r_eliml; try apply v_to_e_is_const_list; try (rewrite rev_cons; rewrite -cats1; rewrite -v_to_e_cat); try apply r_eliml; try apply v_to_e_is_const_list; try apply r_simple.
          + by apply rs_unop_f32.
          + by apply rs_unop_f64.

        - (* Basic Binop_i v b *)
          explode_and_simplify; destruct v => //; pattern_match; stack_frame; subst_rev_const_list => //; repeat (rewrite rev_cons; rewrite -cats1; rewrite -v_to_e_cat); repeat rewrite -catA; try apply r_eliml; try apply v_to_e_is_const_list; apply r_simple; simpl; by eauto.

        - (* Basic Binop_f v b *)         
          explode_and_simplify; destruct v => //; pattern_match; stack_frame; subst_rev_const_list => //; repeat (rewrite rev_cons; rewrite -cats1; rewrite -v_to_e_cat); repeat rewrite -catA; try apply r_eliml; try apply v_to_e_is_const_list; apply r_simple; simpl; by eauto.

        - (* Basic (Testop v t) *)
          explode_and_simplify; destruct v => //; pattern_match; stack_frame; subst_rev_const_list => //; repeat (rewrite rev_cons; rewrite -cats1; rewrite -v_to_e_cat); try apply r_eliml; try apply v_to_e_is_const_list; apply r_simple; simpl.
          + by apply rs_testop_i32.
          + by apply rs_testop_i64.

        - (* Basic (Relop_i v r) *)
          explode_and_simplify; destruct v => //; pattern_match; stack_frame; subst_rev_const_list => //; repeat (rewrite rev_cons; rewrite -cats1; rewrite -v_to_e_cat); repeat rewrite -catA; try apply r_eliml; try apply v_to_e_is_const_list; apply r_simple; simpl.
          + by apply rs_relop_i32.
          + by apply rs_relop_i64.

        - (* Basic (relop_f v r) *)
          explode_and_simplify; destruct v => //; pattern_match; stack_frame; subst_rev_const_list => //; repeat (rewrite rev_cons; rewrite -cats1; rewrite -v_to_e_cat); repeat rewrite -catA; try apply r_eliml; try apply v_to_e_is_const_list; apply r_simple; simpl.
          + by apply rs_relop_f32.
          + by apply rs_relop_f64.

        - (* Basic (Cvtop v c v0 o) *)
          explode_and_simplify; destruct c => //; pattern_match; stack_frame; subst_rev_const_list => //; repeat (rewrite rev_cons; rewrite -cats1; rewrite -v_to_e_cat); try apply r_eliml; try apply v_to_e_is_const_list; apply r_simple; simpl; try by apply rs_convert_success.
          + simpl in if_expr1. move/eqP in if_expr1. subst. by apply rs_reinterpret.
          + simpl in if_expr1. move/eqP in if_expr1. subst. apply rs_convert_failure. by []. by apply/eqP.
          + simpl in if_expr1. move/eqP in if_expr1. subst. by apply rs_reinterpret.
          + apply rs_convert_failure. by []. by apply/eqP.
      }
      {  (* Trap *)
        explode_and_simplify.
        pattern_match.
        apply r_simple. eapply rs_trap => //=.
          + destruct lconst => //=. simpl in if_expr0. destruct les' => //=.
          + apply lfilled_Ind_Equivalent.
            replace (Trap :: les') with ([::Trap] ++ les').
            apply LfilledBase; first by apply v_to_e_is_const_list.
            (* replace *) by [].
      }
      { (* Callcl *)
        simpl.
        destruct f.
        (* This is a bit inconvenient as another 'f' is generated *)
        - (* Func_native *)
          destruct f.
          (* check with Martin for how to work with this kind of ifs *)
          destruct ((if length l1 <= length (rev lconst)
     then
      let (ves', ves'') := split_n (rev lconst) (length l1) in
      (s, vs,
      RS_normal
        (vs_to_es ves'' ++
         [:: Local (length l2) i0 (rev ves' ++ n_zeros l)
               [:: Basic (Block (Tf [::] l2) l0)]]))
                     else (s, vs, crash_error))) eqn:H => //.
          destruct p => //.
          destruct r => //.
          destruct (length l1 <= length (rev lconst)) eqn:HLen => //.
          rewrite split_n_is_take_drop in H. inversion H. subst. clear H.
          move => H. inversion H. subst. clear H.
          replace ((Callcl (Func_native i0 (Tf l1 l2) l l0)) :: les') with (([:: Callcl (Func_native i0 (Tf l1 l2) l l0)] ++ les')).
          rewrite catA. apply r_elimr. unfold vs_to_es.
          (* Check with Martin: how to replace only one occurrence *)
          replace (v_to_e_list lconst) with (take (size lconst - length l1) (v_to_e_list lconst) ++ drop (size lconst - length l1) (v_to_e_list lconst)).
          rewrite drop_rev. rewrite revK. rewrite take_rev. rewrite revK.
          rewrite v_to_e_take_exchange.
          rewrite - catA.
          apply r_eliml.
          { apply const_list_take. by apply v_to_e_is_const_list. }
          (* The eapply below generates 7 subgoals, but most are trivial. *)
          eapply r_callcl_native => //=.
          (*2*) symmetry. by apply v_to_e_drop_exchange.
          (*5*) repeat rewrite length_is_size. rewrite size_drop.
          repeat rewrite length_is_size in HLen. rewrite size_rev in HLen.
            by rewrite subKn.
              by apply cat_take_drop.
                by [].
        - (* Func_host *)
          (* This should be very similar with the case above. *)
          admit.
      }
      { (* Label *)
        (* This should be an interesting case because it relates to our previous work
           on lfilled *)
        simpl.
        (* es_is_trap: the name is a bit misleading -- it actually means if the first
           element of es is a trap (rather than the entire list es). *)
        (* edit: after careful research (because a case in the proof later doesn't go
           through, I realized that this is wrong. es_is_trap should only be true
           if es is just [::Trap] ! See Conrad's outline page 63-64 *)
        move => n l l0.
        explode_and_simplify.

        (*destruct (es_is_trap l0) eqn:HTrap.*)
        - pattern_match.
          rewrite - cat1s. rewrite catA. apply r_elimr. apply r_eliml; first by apply v_to_e_is_const_list.
          apply r_simple. by eapply rs_label_trap.
        - destruct l0 => //=.
          + pattern_match.
            rewrite - cat1s. rewrite catA. apply r_elimr. apply r_eliml; first by apply v_to_e_is_const_list.
            apply r_simple. by apply rs_label_const.
          + simplify_goal. move/andP: if_expr0 => [HConsta HConstList].
            pattern_match.
            rewrite - cat1s. rewrite catA. apply r_elimr. apply r_eliml; first by apply v_to_e_is_const_list.
            apply r_simple. apply rs_label_const.
            simpl. rewrite HConsta. by apply HConstList.

        (* The following is useless work (before I identified the error in es_is_trap) *)

        (* destruct l0 => //=.
        - move => H. inversion H. subst.
          apply split_vals_e_v_to_e_duality in HSplitVals. rewrite HSplitVals.
          clear H. clear HSplitVals.
          unfold vs_to_es. rewrite revK.
          rewrite - cat1s. rewrite catA. apply r_elimr. apply r_eliml.
          apply r_simple. by apply rs_label_const.
        - destruct a => //=.
          + destruct (const_list l0) eqn:HConst => //.
            (* These two lines have become a pattern everywhere. Maybe we can
               put it before the large destruct *)
            move => H. inversion H. subst. clear H.
            apply split_vals_e_v_to_e_duality in HSplitVals. rewrite HSplitVals.
            clear HSplitVals.
            unfold vs_to_es. rewrite revK.
            rewrite - cat1s. rewrite catA. apply r_elimr. apply r_eliml.
            apply r_simple. by apply rs_label_const.
          + move => H. inversion H. subst. clear H.
            apply split_vals_e_v_to_e_duality in HSplitVals. rewrite HSplitVals.
            clear HSplitVals.
            unfold vs_to_es. rewrite revK.
            rewrite - cat1s. rewrite catA. apply r_elimr. apply r_eliml.
            assert (lfilledInd 0 (LBase [::] l0) [::Trap] ([::]++[::Trap]++l0)) as LF0; first by apply LfilledBase.
            assert (lfilledInd 1 (LRec [::] n l (LBase [::] l0) [::]) [::Trap] ([::]++[::(Label n l ([::]++[::Trap]++l0))] ++ [::])) as LF1.
            apply LfilledRec; first by []. by [].
            simpl in LF0. simpl in LF1.
            apply r_label. *)
            

      }

      { (* Local *)
        move => n i0 l l0.
        explode_and_simplify.
        (*destruct (es_is_trap l0) eqn:HTrap.*)
        - pattern_match.
          rewrite - cat1s. rewrite - catA. apply r_eliml; first by apply v_to_e_is_const_list. apply r_elimr.
          apply r_simple. apply rs_local_trap.
        - pattern_match.
          rewrite - cat1s. rewrite - catA. apply r_eliml; first by apply v_to_e_is_const_list. apply r_elimr.
          apply r_simple. by apply rs_local_const.
      }
    + (* This has grown to an extent that I'm no longer sure where I am *)
      move => n IH. destruct a as [b | | | |].
      * (* Basic *) admit.
      * (* Trap: the exact proof flows through -- I've checked.*) admit.
      * (* Callcl: same *) admit.
      * (* Label *)
        (* Some of the same proof can be reused, but now there are more cases *)

            admit.
        
      * (* Local *) admit.
        
         
Admitted. (* TODO *)

End Host.

(* TODO: Here are all what we need to implement.
Print Assumptions run_step.
[[
wasm_deserialise : bytes -> value_type -> value
serialise_i64 : i64 -> bytes
serialise_i32 : i32 -> bytes
serialise_f64 : f64 -> bytes
serialise_f32 : f32 -> bytes
wasm.host : eqType
(* Some [Equality.axiom] in the wasm module. *)
Classical_Prop.classic : forall P : Prop, P \/ ~ P
(* A whole bunch of axioms.  It seems that they come from Flocq, mainly as an axiomatisation of [R].
  Just that we can see things like classical logic and so on. *)
]]
*)
