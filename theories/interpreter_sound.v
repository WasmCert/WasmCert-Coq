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

Hint Constructors reduce_simple.

(* Check with Martin for these two: I think they should be in opsem for reduce,
   but they are currently not. Missing this it's impossible to prove quite a number
   of cases (edit: in fact all cases) -- unless I've overlooked something *)
Axiom r_unchangedl: forall s vs es es' i l,
    reduce s vs es i s vs es' ->
    reduce s vs (l++es) i s vs (l++es').

Axiom r_unchangedr: forall s vs es es' i l,
    reduce s vs es i s vs es' ->
    reduce s vs (es++l) i s vs (es'++l).

(* After some thoughts, I think we need these two sensible things instead *)
Lemma r_eliml: forall s vs es s' vs' es' lconst i,
    const_list lconst ->
    reduce s vs es i s' vs' es' ->
    reduce s vs (lconst ++ es) i s' vs' (lconst ++ es').
Proof.
  move => s vs es s' vs' es' lconst i HConst H.
  eapply r_label; try (apply lfilled_Ind_Equivalent).
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
  eapply r_label; try (apply lfilled_Ind_Equivalent).
  - apply H.
  - replace (es++les) with ([::]++es++les) => //. by apply LfilledBase.
  - replace (es'++les) with ([::]++es'++les) => //. by apply LfilledBase.
Qed.

Lemma run_step_soundness : forall d i s vs es s' vs' es',
    run_step d i (s, vs, es) = (s', vs', RS_normal es') ->
    exists j,
      reduce s vs es j s' vs' es'.
Proof.
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
      case a => //=. move => b.
      { (* Basic b *)
        destruct b => //=.
        - (* Basic Unreachable *) move => H. inversion H; subst.
          clear H. exists i. unfold vs_to_es.
          rewrite revK.
          (* The rule rs_unreachable in reduce_simple gives that Basic Unreachable
             reduces to Trap; v_to_e_list lconst obviously refers to the initial 
             segment of Basic EConst, so if we have a rule saying something like
               reduce s vs es ?j s vs es' ->
               reduce s vs (ves++es) ?j s vs (ves++es')
             Then we're done for this case. But there doesn't seem to be such a rule? *)
          (* I've added two axioms for the above to make this work. I believe they should
             be part of the opsem. *)
          rewrite - cat1s. rewrite catA.
          apply r_elimr. apply r_eliml; first by apply v_to_e_is_const_list.
            by apply r_simple.
            
        - (* Basic Nop *) move => H. inversion H; subst.
          clear H. exists i. unfold vs_to_es.
          rewrite revK.
          (* The same situation as above. *)
          rewrite - cat1s. apply r_eliml; first by apply v_to_e_is_const_list. replace les' with ([::] ++ les').
          apply r_elimr. by apply r_simple.
            by apply cat0s.
            
        - (* Basic Drop *) move => H. inversion H; subst.
          destruct (rev lconst) eqn:HRLConst => //.
          inversion H1. subst. clear H H1. unfold vs_to_es.
          exists i. 
          (* Similar, although this case is a bit more tedious *)
          rewrite - cat1s. rewrite catA. apply r_elimr.
          replace lconst with (rev l ++ [::v]).
          rewrite - v_to_e_cat.
          replace (v_to_e_list (rev l)) with (v_to_e_list (rev l) ++ [::]).
          repeat rewrite - catA. apply r_eliml; first by apply v_to_e_is_const_list. apply r_simple.
          rewrite cat0s. by rewrite cat1s.
            by apply cats0.
            rewrite - catrevE. rewrite - (revK lconst). by rewrite HRLConst.

          (* Let's move on to something less trivial*)
          - Focus 3. (* Basic loop *)
          destruct f.
          (* so it seems that lconst is a stack of numbers; then f is a function
             which takes l0 as the list of arguments, therefore the length 
             requirement. *)
          (* Ask Martin how to do this nicely *)
          case HLen: (length l0 <= length (rev lconst)) => //.
          rewrite split_n_is_take_drop. unfold vs_to_es.
          rewrite drop_rev. rewrite take_rev. repeat rewrite revK.
          move => H. inversion H. subst. clear H.
          exists i.
          rewrite - cat1s. repeat rewrite catA. apply r_elimr.
          replace (v_to_e_list lconst) with (v_to_e_list (take (size lconst - length l0) lconst) ++ v_to_e_list (drop (size lconst - length l0) lconst)).
          rewrite - catA. apply r_eliml; first by apply v_to_e_is_const_list.
          apply r_simple.
          eapply rs_loop => //=. (* generates 4 subgoals but most are trivial *)
          +(*1*) by apply v_to_e_is_const_list.
          +(*2*) repeat rewrite length_is_size. repeat rewrite length_is_size in HLen.
          rewrite size_rev in HLen.
          rewrite v_to_e_drop_exchange. rewrite size_drop. rewrite v_to_e_size.
            by rewrite subKn.
          + rewrite v_to_e_take_exchange. rewrite v_to_e_drop_exchange.
            by apply cat_take_drop.

          - Focus 9. (* Basic Set_local i0 *)
            destruct (rev lconst) eqn:HConst => //=.
            destruct (i0 < length vs) eqn:HLen => //=.
            move => H. inversion H. subst. clear H.
            rewrite - update_list_at_is_set_nth => //=.
            
            unfold vs_to_es. rewrite - cat1s.
            exists i. rewrite catA. apply r_elimr.
            replace lconst with (rev l ++ [::v]).
            replace (v_to_e_list (rev l)) with (v_to_e_list (rev l) ++ [::]).
            rewrite - v_to_e_cat. rewrite - catA.
            apply r_eliml => //=; first by apply v_to_e_is_const_list.
            (* Ask martin if we can change opsem here *)
            assert (forall x, (reduce s' ((take i0 vs) ++ [::x] ++ (drop (size vs - i0 - 1) vs)) [::Basic (EConst v); Basic (Set_local i0)] i s' ((take i0 vs) ++ [::v] ++ (drop (size vs - i0 - 1) vs)) [::])) as HGoal.
            move => x. apply r_set_local.
            + rewrite length_is_size. rewrite length_is_size in HLen. rewrite size_take.
              by rewrite HLen.
              (* too much hassle, probably just change opsem *)
            + admit.
            + by apply cats0.
            + admit.
            
    
            
            
            
          
        (* It feels like most cases in this branch (Basic b) can be done via an
           application of r_simple followed by some rs_xxx rule and rewriting 
           associativity randomly and applying some of the above lemmas.*)
          
          (* There's probably a better method, but idc for now... *)
          (* Put these in a nice rectangle so we can easily know how many subgoals
             are left! *)  
          admit. admit. admit. admit.
          admit. admit. admit. admit.
          admit. admit. admit. admit.
          admit. admit. admit. admit.
          admit. admit. admit. admit.
          admit. admit. admit. 
      }
      {  (* Trap *)
        simpl.
        (* Check with Martin for how to do this nicely *)
        move => H. destruct les' => //=.
        - destruct lconst => //=.
          simpl in H. inversion H. subst. clear H.
          exists i. apply r_simple. eapply rs_trap.
          + by destruct es => //.
          + apply lfilled_Ind_Equivalent.
            assert (lfilledInd 0 (LBase ((Basic (EConst v)) :: (v_to_e_list lconst)) [::]) [::Trap] (Basic (EConst v)::v_to_e_list lconst ++ [::Trap] ++ [::])) as LF0.
            { apply LfilledBase. simpl. by apply v_to_e_is_const_list. }
            by apply LF0.
        - simpl in H. inversion H. subst. clear H.
          exists i. apply r_simple. eapply rs_trap => //=.
          + destruct lconst => //=.
          + apply lfilled_Ind_Equivalent.
            assert (lfilledInd 0 (LBase (v_to_e_list lconst) ([::a0]++les')) [::Trap] (v_to_e_list lconst ++ [::Trap] ++ [::a0]++les')) as LF0.
            { apply LfilledBase. simpl. by apply v_to_e_is_const_list. }
            by apply LF0.
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
          exists i. replace ((Callcl (Func_native i0 (Tf l1 l2) l l0)) :: les') with (([:: Callcl (Func_native i0 (Tf l1 l2) l l0)] ++ les')).
          rewrite catA. apply (r_unchangedr les'). unfold vs_to_es.
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
        destruct (es_is_trap l0) eqn:HTrap.
        - unfold es_is_trap in HTrap. destruct l0 => //. destruct l0 => //.
          destruct a0 => //=.
          move => H. inversion H. subst.
          exists i. unfold vs_to_es. rewrite revK.
          rewrite - cat1s. rewrite catA. apply r_elimr. apply r_eliml; first by apply v_to_e_is_const_list.
          apply r_simple. by eapply rs_label_trap.
        - destruct l0 => //=.
          + move => H. inversion H. subst.
          exists i. unfold vs_to_es. rewrite revK.
          rewrite - cat1s. rewrite catA. apply r_elimr. apply r_eliml; first by apply v_to_e_is_const_list.
          apply r_simple. by apply rs_label_const.
          + destruct (is_const a0) eqn:HConsta => //=.
            destruct (const_list l0) eqn:HConstList => //=.
            move => H. inversion H. subst.
            exists i. unfold vs_to_es. rewrite revK.
            rewrite - cat1s. rewrite catA. apply r_elimr. apply r_eliml; first by apply v_to_e_is_const_list.
            apply r_simple. apply rs_label_const.
            simpl. rewrite HConsta. by apply HConstList.

        (* The following is useless work (before I identified the error in es_is_trap) *)

        (* destruct l0 => //=.
        - move => H. inversion H. subst.
          apply split_vals_e_v_to_e_duality in HSplitVals. rewrite HSplitVals.
          clear H. clear HSplitVals.
          exists i. unfold vs_to_es. rewrite revK.
          rewrite - cat1s. rewrite catA. apply r_elimr. apply r_eliml.
          apply r_simple. by apply rs_label_const.
        - destruct a => //=.
          + destruct (const_list l0) eqn:HConst => //.
            (* These two lines have become a pattern everywhere. Maybe we can
               put it before the large destruct *)
            move => H. inversion H. subst. clear H.
            apply split_vals_e_v_to_e_duality in HSplitVals. rewrite HSplitVals.
            clear HSplitVals.
            exists i. unfold vs_to_es. rewrite revK.
            rewrite - cat1s. rewrite catA. apply r_elimr. apply r_eliml.
            apply r_simple. by apply rs_label_const.
          + move => H. inversion H. subst. clear H.
            apply split_vals_e_v_to_e_duality in HSplitVals. rewrite HSplitVals.
            clear HSplitVals.
            exists i. unfold vs_to_es. rewrite revK.
            rewrite - cat1s. rewrite catA. apply r_elimr. apply r_eliml.
            assert (lfilledInd 0 (LBase [::] l0) [::Trap] ([::]++[::Trap]++l0)) as LF0; first by apply LfilledBase.
            assert (lfilledInd 1 (LRec [::] n l (LBase [::] l0) [::]) [::Trap] ([::]++[::(Label n l ([::]++[::Trap]++l0))] ++ [::])) as LF1.
            apply LfilledRec; first by []. by [].
            simpl in LF0. simpl in LF1.
            apply r_label. *)
            

      }

      { (* Local *)
        simpl.
        move => n i0 l l0.
        destruct (es_is_trap l0) eqn:HTrap.
        - move => H. inversion H. subst.
          exists i. unfold vs_to_es. rewrite revK.
          rewrite - cat1s. rewrite - catA. apply r_eliml; first by apply v_to_e_is_const_list. apply r_elimr.
          unfold es_is_trap in HTrap. destruct l0 => //=. destruct l0 => //=.
          destruct a0 => //=.
          apply r_simple. apply rs_local_trap.
        - destruct (const_list l0) eqn:HConstList => //=.
          destruct (length l0 == n) eqn:HLen => //=.
          move => H. inversion H. subst.
          exists i. unfold vs_to_es. rewrite revK.
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
