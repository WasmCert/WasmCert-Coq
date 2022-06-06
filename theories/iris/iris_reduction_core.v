From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap proph_map.
Require Export iris iris_locations stdpp_aux.
Require Export datatypes host operations properties opsem.
Require Import iris_reduce_properties iris_wasm_lang_properties.



Section reduction_core.

  Let reducible := @reducible wasm_lang.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.



  Lemma reduction_core bef0 es0 aft0 bef1 es1 aft1 es0' es1' s f s' f' s0 f0 :
    reduce s f es0 s0 f0 es0' ->
    reduce s f es1 s' f' es1' ->
    const_list bef0 ->
    const_list bef1 ->
    bef0 ++ es0 ++ aft0 = bef1 ++ es1 ++ aft1 ->
    (exists core bc0 ac0 bc1 ac1 core',
        const_list bc0 /\
          const_list bc1 /\
          es0 = bc0 ++ core ++ ac0 /\
          es1 = bc1 ++ core ++ ac1 /\
          bef0 ++ bc0 = bef1 ++ bc1 /\
          ac0 ++ aft0 = ac1 ++ aft1 /\
          reduce s f core s' f' core' /\
          bc1 ++ core' ++ ac1 = es1') \/
      exists lh0 lh1, lfilled 0 lh0 [AI_trap] es0 /\ lfilled 0 lh1 [AI_trap] es1 /\
                   (s,f) = (s', f').
  Proof.
    intros Hred0 Hred1 Hbef0 Hbef1 Heq.
    cut (forall nnnn, length es1 < nnnn ->
                 (∃ core bc0 ac0 bc1 ac1 core' : seq.seq administrative_instruction,
                     const_list bc0
                     ∧ const_list bc1
                     ∧ es0 = bc0 ++ core ++ ac0
                     ∧ es1 = bc1 ++ core ++ ac1
                     ∧ bef0 ++ bc0 = bef1 ++ bc1
                     ∧ ac0 ++ aft0 = ac1 ++ aft1
                     ∧ reduce s f core s' f' core' ∧ bc1 ++ core' ++ ac1 = es1')
                 ∨ (∃ lh0 lh1 : lholed, lfilled 0 lh0 [AI_trap] es0 ∧ lfilled 0 lh1 [AI_trap] es1 /\ (s,f) = (s',f'))).
    { intro Hn ; eapply (Hn (S (length es1))) ; lia. }
    intro nnnn.
    generalize dependent es1.
    generalize dependent es1'.
    generalize dependent es0.
    generalize dependent es0'.
    generalize dependent bef1.
    generalize dependent aft1.
    induction nnnn.
    intros ; lia.
    intros aft1 bef1 Hbef1 es0' es0 Hred0 es1' es1 Hred1 Heq Hlen.
    edestruct first_non_value_reduce as (vs0 & e0 & afte0 & Hvs0 & He0 & Heq0) ;
      try exact Hred0.
    rewrite Heq0 in Heq.
    induction Hred1 as [ | ? ? ? aaa Hr | ? ? ? aaa ? ? Hr1 Hr2 Hr3 |
                         ? ? ? aaa ? ? Hr1 Hr2 Hr3 | ? ? ? ? Hr |
                         aaa ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 Hr5 Hr6
                             Hr7 Hr8 Hr9 Hr10 |
                         aaa ? ? ? ? ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 |

                         ? ? ? ? Hr | ? ? ? ? ? ? Hr1 Hr2 Hr3 |
                         ? ? ? ? Hr | ? ? ? ? ? Hr | ? ? ? ? ? kkk aaa ? ? Hr1 Hr2 Hr3 |
                         ? ? ? ? kkk aaa ? ? Hr1 Hr2 Hr3 |
                         ? ? ? ? ? kkk aaa ? ? ? ? Hr1 Hr2 Hr3 |
                         ? ? ? ? ? kkk aaa ? ? ? Hr1 Hr2 Hr3 |
                         ? ? ? ? ? ? kkk aaa ? ? Hr1 Hr2 Hr3 Hr4 |
                         ? ? ? ? ? ? kkk ? aaa Hr1 Hr2 Hr3 Hr4 |
                         ? ? ? ? ? ? kkk ? aaa ? ? Hr1 Hr2 Hr3 Hr4 |
                         ? ? ? ? ? ? kkk ? aaa ? Hr1 Hr2 Hr3 Hr4 | ? ? ? ? ? Hr1 Hr2 Hr3 |
                         ? ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 | ? ? ? ? ? ? Hr1 Hr2 Hr3 |
                         ? ? ? ? ? ? ? ? ? ? Hr1 IHHred Hr2 Hr3 |
                         ? ? ? ? ? ? ? ? Hr IHHred ] ;
      try (by left ; do 2 rewrite app_assoc in Heq ;
           rewrite - (app_assoc ( _ ++ _)) in Heq ;
           rewrite - app_comm_cons in Heq ;
           apply first_values in Heq as (<- & -> & <-) ;try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
           try (destruct He0 as [-> | ->]; by intros [? ?]) ;
           try (by const_list_app) ;
           rewrite separate1 in Heq0 ;
           eexists _, vs0, afte0, [], [], _ ;
           repeat split ; try done ; try (by rewrite app_nil_r) ;
             by econstructor) ;
      try (by left ; rewrite (separate1 (AI_basic (BI_const _))) in Heq ;
           repeat rewrite app_assoc in Heq ;
           repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
           rewrite - app_comm_cons in Heq ;
           apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
           try (destruct He0 as [-> | ->]; by intros [? ?]);
           try (by const_list_app) ;
           destruct vs0 ;
           [ simpl in Heq0 ;
             exfalso ;
             apply Logic.eq_sym in Heq0 ;
             clear Hafts ;
             generalize dependent afte0 ;
             induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
             try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                  assert (const_list (a0 :: ves)) as Hconst ;
                  first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                  first_not_const Hconst) ;
             [ destruct H ; try (by inversion Heq0) ;
               try (by destruct vs ; inversion Heq0 ;
                    first_not_const H) ; 
               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
               unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef
             | rewrite - Heq0 in H ;
               simple_filled2 H k lh bef aft nn ll ll' ;
               [ destruct bef ;
                 [ destruct es ; first empty_list_no_reduce ;
                   inversion H ; subst ;
                     by eapply IHHred0
                 | inversion H ;
                   first_not_const Hvs ]
               | destruct bef ; inversion H ;
                 first_not_const Hvs ]]
           | get_tail a vs0 ys y Htail ;
             rewrite Htail in Hbefs ;
             repeat rewrite catA in Hbefs ;
             apply app_inj_tail in Hbefs as [Hbefs ->] ;
             rewrite Htail in Heq0 ;
             rewrite - app_assoc in Heq0 ;
             rewrite - separate1 in Heq0 ;
             rewrite separate2 in Heq0 ;
             eexists _, ys, afte0, [], [], _ ;
             repeat split ; try done ; try (by rewrite app_nil_r) ;
             [ rewrite Htail in Hvs0 ;
               unfold const_list in Hvs0 ;
               rewrite forallb_app in Hvs0 ;
               apply andb_true_iff in Hvs0 as [Hys _] ;
                 by unfold const_list 
             | by econstructor ]]) ;
      try by (left ; rewrite separate2 in Heq ;
              repeat rewrite app_assoc in Heq ;
              repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
              rewrite - app_comm_cons in Heq ;
              apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
              try (destruct He0 as [-> | ->]; by intros [? ?]);
              try (by const_list_app) ;
              destruct vs0 ;
              [ simpl in Heq0 ;
                exfalso ;
                apply Logic.eq_sym in Heq0 ;
                clear Hafts ;
                generalize dependent afte0 ;
                induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                     assert (const_list (a0 :: ves)) as Hconst ;
                     first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                     first_not_const Hconst) ;
                [ destruct H ; try (by inversion Heq0) ;
                  try (by destruct vs ; inversion Heq0 ;
                       first_not_const H) ; 
                  try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                  unfold lfilled, lfill in H0 ;
                  destruct lh as [bef aft |] ; last (by false_assumption) ;
                  destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                  move/eqP in H0 ;
                  rewrite H0 in Heq0 ; 
                  destruct bef ; inversion Heq0 ;
                  first_not_const Hbef
                | rewrite - Heq0 in H ;
                  simple_filled2 H k lh bef aft nn ll ll' ;
                  [ destruct bef ;
                    [ destruct es ; first empty_list_no_reduce ;
                      inversion H ; subst ;
                        by eapply IHHred0
                    | inversion H ;
                      first_not_const Hvs ]
                  | destruct bef ; inversion H ;
                    first_not_const Hvs ]]
              |] ;
              destruct vs0 ;
              [ exfalso ;
                clear Hafts ;
                generalize dependent afte0 ;
                induction Hred0 ; intros afte0 Heq0 ; 
                try (by inversion Heq0) ;
                try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                     destruct ves as [| b1 ves] ; inversion Heq0 ;
                     assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                     first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                     first_not_const Hconst) ;
                [ destruct H ;
                  try (by inversion Heq0) ;
                  try (by destruct vs ; first (by inversion Heq0) ;
                       destruct vs ; inversion Heq0 ;
                       first_not_const H) ;
                  unfold lfilled, lfill in H0 ;
                  destruct lh as [bef aft |] ; last (by false_assumption) ;
                  destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                  move/eqP in H0 ; 
                  rewrite H0 in Heq0 ;
                  destruct bef ; 
                  inversion Heq0 ; subst ;
                  inversion Hvs0 ; 
                  destruct bef ; inversion Heq0 ;
                  first_not_const Hbef 
                | rewrite Heq0 in H ;
                  simple_filled2 H k lh bef aft nn ll ll' ;
                  [ destruct bef ;
                    [ destruct es ; first empty_list_no_reduce ;
                      destruct es ; inversion H ; subst ;
                      [ values_no_reduce 
                      | by eapply IHHred0 ]
                    | destruct bef ;
                      [ destruct es ; first empty_list_no_reduce ;
                        inversion H ;
                        remember (a1 :: es) as es0 ;
                        subst a1 ;
                        clear Heq0 afte0 H H4 aft H0 IHHred0 ;
                        generalize dependent es ;
                        induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                        try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                             assert (const_list (b0 :: ves)) as Hconst ;
                             first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                             first_not_const Hconst) ;
                        [ destruct H ; try (by inversion Heq0) ;
                          try (by destruct vs ; inversion Heq0 ;
                               first_not_const H) ; 
                          try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                          unfold lfilled, lfill in H0 ;
                          destruct lh as [bef aft |] ; last (by false_assumption) ;
                          destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                          move/eqP in H0 ;
                          rewrite H0 in Heq0 ; 
                          destruct bef ; inversion Heq0 ;
                          first_not_const Hbef
                        | rewrite Heq0 in H ;
                          simple_filled2 H k lh bef aft nn ll ll' ;
                          [ destruct bef ;
                            [ destruct es ; first empty_list_no_reduce ;
                              inversion H ; subst ;
                                by eapply IHHred0
                            | inversion H ;
                              first_not_const Hvs ]
                          | destruct bef ; inversion H ;
                            first_not_const Hvs ]]
                      | inversion H ;
                        first_not_const Hvs ]]
                  | destruct bef ; inversion H ;
                    subst ; inversion Hvs0 ;
                    destruct bef ; inversion H ;
                    first_not_const Hvs ]] 
              | get_tail a0 vs0 ys y Htail ;
                rewrite Htail in Hbefs ;
                rewrite app_comm_cons in Hbefs ;
                get_tail a ys ys' y' Htail' ;
                rewrite Htail' in Hbefs ;
                rewrite (separate1 (AI_basic (BI_const _))) in Hbefs ;
                repeat rewrite catA in Hbefs ;
                rewrite assoc_list_seq in Hbefs ;
                apply app_inj_tail in Hbefs as [Hys' ->] ;
                apply app_inj_tail in Hys' as [Hys ->] ;
                rewrite Htail app_comm_cons Htail' - app_assoc - separate1 - app_assoc
                - separate1 separate3 in Heq0 ;
                eexists _, ys', afte0, [], [], _ ;
                repeat split ; try done ; try (by rewrite app_nil_r) ;
                [ rewrite Htail app_comm_cons Htail' in Hvs0 ;
                  unfold const_list in Hvs0 ;
                  repeat rewrite forallb_app in Hvs0 ;
                  repeat apply andb_true_iff in Hvs0 as [Hvs0 _] ;
                  done
                | by econstructor]]) .
    { destruct H as [ | ? ? ? ? ? Hr | ? ? ? ? Hr | | | | ? ? ? ? ? Hr1 Hr2 |
                      ? ? ? ? Hr1 Hr2 | ? ? ? Hr | | | | ? ? ? Hr | ? ? ? Hr |
                      ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 | ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 |
                      ? ? ? ? Hr | ? ? ? ? Hr | ? ? ? Hr | | ? ? ? ? ? ? Hr1 Hr2 Hr3 |
                      ? ? Hr | ? ? Hr | ? ? ? ? Hr1 Hr2 | ? ? ? Hr | ? ? ? Hr1 Hr2 |
                    | ? ? ? ? ? ? Hr1 Hr2 Hr3 | ? ? Hr | ? ? Hr1 Hr2 ].
      all: try (by left ; do 2 rewrite app_assoc in Heq ;
                rewrite - (app_assoc ( _ ++ _)) in Heq ;
                rewrite - app_comm_cons in Heq;
                apply first_values in Heq as (<- & -> & <-); try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                try (destruct He0 as [-> | ->]; by intros [? ?]);
                try (by const_list_app);
                rewrite separate1 in Heq0;
                eexists _, vs0, afte0, [], [], _ ;
                repeat split ; try done ; try (by rewrite app_nil_r) ;
                  by repeat econstructor).
      
      all: try (destruct v ; (try destruct b) ; try by inversion Hr). 
      all: try (by  left ; rewrite (separate1 (AI_basic (BI_const _))) in Heq ; 
                repeat rewrite app_assoc in Heq  ;
                repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
                rewrite - app_comm_cons in Heq ;
                apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                try (destruct He0 as [-> | ->]; by intros [? ?]);
                try (by const_list_app) ; 
                destruct vs0 ;
                [ simpl in Heq0 ;
                  exfalso ;
                  apply Logic.eq_sym in Heq0 ;
                  clear Hafts ;
                  generalize dependent afte0 ;
                  induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                  try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                       assert (const_list (a0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                  [ destruct H ; try (by inversion Heq0) ;
                    try (by destruct vs ; inversion Heq0 ;
                         first_not_const H) ; 
                    try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                    unfold lfilled, lfill in H0 ;
                    destruct lh as [bef aft |] ; last (by false_assumption) ;
                    destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                    move/eqP in H0 ;
                    rewrite H0 in Heq0 ; 
                    destruct bef ; inversion Heq0 ;
                    first_not_const Hbef
                  | rewrite - Heq0 in H ;
                    simple_filled2 H k lh bef aft nn ll ll' ;
                    [ destruct bef ;
                      [ destruct es ; first empty_list_no_reduce ;
                        inversion H ; subst ;
                          by eapply IHHred0
                      | inversion H ;
                        first_not_const Hvs ]
                    | destruct bef ; inversion H ;
                      first_not_const Hvs ]]
                | get_tail a vs0 ys y Htail ;
                  rewrite Htail in Hbefs ;
                  repeat rewrite catA in Hbefs ;
                  apply app_inj_tail in Hbefs as [Hbefs ->] ;
                  rewrite Htail in Heq0 ;
                  rewrite - app_assoc in Heq0 ;
                  rewrite - separate1 in Heq0 ;
                  rewrite separate2 in Heq0 ;
                  eexists _, ys, afte0, [], [], _ ;
                  repeat split ; try done ; try (by rewrite app_nil_r) ;
                  [ rewrite Htail in Hvs0 ;
                    unfold const_list in Hvs0 ;
                    rewrite forallb_app in Hvs0 ;
                    apply andb_true_iff in Hvs0 as [Hys _] ;
                      by unfold const_list 
                  | by repeat econstructor ]]).
      all: try by (left ; rewrite separate2 in Heq ;
                   repeat rewrite app_assoc in Heq ;
                   repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
                   rewrite - app_comm_cons in Heq ;
                   apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                   try (destruct He0 as [-> | ->]; by intros [? ?]);
                   try (by const_list_app) ;
                   destruct vs0 ;
                   [ simpl in Heq0 ;
                     exfalso ;
                     apply Logic.eq_sym in Heq0 ;
                     clear Hafts ;
                     generalize dependent afte0 ;
                     induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                     try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                          assert (const_list (a0 :: ves)) as Hconst ;
                          first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                          first_not_const Hconst) ;
                     [ destruct H ; try (by inversion Heq0) ;
                       try (by destruct vs ; inversion Heq0 ;
                            first_not_const H) ; 
                       try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                       unfold lfilled, lfill in H0 ;
                       destruct lh as [bef aft |] ; last (by false_assumption) ;
                       destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                       move/eqP in H0 ;
                       rewrite H0 in Heq0 ; 
                       destruct bef ; inversion Heq0 ;
                       first_not_const Hbef
                     | rewrite - Heq0 in H ;
                       simple_filled2 H k lh bef aft nn ll ll' ;
                       [ destruct bef ;
                         [ destruct es ; first empty_list_no_reduce ;
                           inversion H ; subst ;
                             by eapply IHHred0
                         | inversion H ;
                           first_not_const Hvs ]
                       | destruct bef ; inversion H ;
                         first_not_const Hvs ]]
                   |] ;
                   destruct vs0 ;
                   [ exfalso ;
                     clear Hafts ;
                     generalize dependent afte0 ;
                     induction Hred0 ; intros afte0 Heq0 ; 
                     try (by inversion Heq0) ;
                     try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                          destruct ves as [| b1 ves] ; inversion Heq0 ;
                          assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                          first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                          first_not_const Hconst) ;
                     [ destruct H ;
                       try (by inversion Heq0) ;
                       try (by destruct vs ; first (by inversion Heq0) ;
                            destruct vs ; inversion Heq0 ;
                            first_not_const H) ;
                       unfold lfilled, lfill in H0 ;
                       destruct lh as [bef aft |] ; last (by false_assumption) ;
                       destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                       move/eqP in H0 ; 
                       rewrite H0 in Heq0 ;
                       destruct bef ; 
                       inversion Heq0 ; subst ;
                       inversion Hvs0 ; 
                       destruct bef ; inversion Heq0 ;
                       first_not_const Hbef 
                     | rewrite Heq0 in H ;
                       simple_filled2 H k lh bef aft nn ll ll' ;
                       [ destruct bef ;
                         [ destruct es ; first empty_list_no_reduce ;
                           destruct es ; inversion H ; subst ;
                           [ values_no_reduce 
                           | by eapply IHHred0 ]
                         | destruct bef ;
                           [ destruct es ; first empty_list_no_reduce ;
                             inversion H ;
                             remember (a1 :: es) as es0 ;
                             subst a1 ;
                             clear Heq0 afte0 H H4 aft H0 IHHred0 ;
                             generalize dependent es ;
                             induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                             try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                                  assert (const_list (b0 :: ves)) as Hconst ;
                                  first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                                  first_not_const Hconst) ;
                             [ destruct H ; try (by inversion Heq0) ;
                               try (by destruct vs ; inversion Heq0 ;
                                    first_not_const H) ; 
                               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                               unfold lfilled, lfill in H0 ;
                               destruct lh as [bef aft |] ; last (by false_assumption) ;
                               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                               move/eqP in H0 ;
                               rewrite H0 in Heq0 ; 
                               destruct bef ; inversion Heq0 ;
                               first_not_const Hbef
                             | rewrite Heq0 in H ;
                               simple_filled2 H k lh bef aft nn ll ll' ;
                               [ destruct bef ;
                                 [ destruct es ; first empty_list_no_reduce ;
                                   inversion H ; subst ;
                                     by eapply IHHred0
                                 | inversion H ;
                                   first_not_const Hvs ]
                               | destruct bef ; inversion H ;
                                 first_not_const Hvs ]]
                           | inversion H ;
                             first_not_const Hvs ]]
                       | destruct bef ; inversion H ;
                         subst ; inversion Hvs0 ;
                         destruct bef ; inversion H ;
                         first_not_const Hvs ]] 
                   | get_tail a0 vs0 ys y Htail ;
                     rewrite Htail in Hbefs ;
                     rewrite app_comm_cons in Hbefs ;
                     get_tail a ys ys' y' Htail' ;
                     rewrite Htail' in Hbefs ;
                     rewrite (separate1 (AI_basic (BI_const _))) in Hbefs ;
                     repeat rewrite catA in Hbefs ;
                     rewrite assoc_list_seq in Hbefs ;
                     apply app_inj_tail in Hbefs as [Hys' ->] ;
                     apply app_inj_tail in Hys' as [Hys ->] ;
                     rewrite Htail app_comm_cons Htail' - app_assoc - separate1 - app_assoc
                     - separate1 separate3 in Heq0 ;
                     eexists _, ys', afte0, [], [], _ ;
                     repeat split ; try done ; try (by rewrite app_nil_r) ;
                     [ rewrite Htail app_comm_cons Htail' in Hvs0 ;
                       unfold const_list in Hvs0 ;
                       repeat rewrite forallb_app in Hvs0 ;
                       repeat apply andb_true_iff in Hvs0 as [Hvs0 _] ;
                       done
                     | by repeat econstructor]]).
      - left ; rewrite separate3 in Heq ;
          repeat rewrite app_assoc in Heq ;
          repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
          rewrite - app_comm_cons in Heq ;
          apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try (by const_list_app) ;
          destruct vs0.
        exfalso ;
          apply Logic.eq_sym in Heq0 ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|a0 ves]; inversion Heq0 ;
               assert (const_list (a0 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [ destruct H ; try (by inversion Heq0) ;
            try (by destruct vs ; inversion Heq0 ;
                 first_not_const H) ; 
            try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ;
            rewrite H0 in Heq0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef
          | rewrite - Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                inversion H ; subst ;
                  by eapply IHHred0
              | inversion H ;
                first_not_const Hvs ]
            | destruct bef ; inversion H ;
              first_not_const Hvs ]].
        destruct vs0.
        exfalso ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; 
          try (by inversion Heq0) ;
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [ destruct H ;
            try (by inversion Heq0) ;
            try (by destruct vs ; first (by inversion Heq0) ;
                 destruct vs ; inversion Heq0 ;
                 first_not_const H) ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ; 
            rewrite H0 in Heq0 ;
            destruct bef ; 
            inversion Heq0 ; subst ;
            inversion Hvs0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef 
          | rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                destruct es ; inversion H ; subst ;
                [ values_no_reduce 
                | by eapply IHHred0 ]
              | destruct bef ;
                [ destruct es ; first empty_list_no_reduce ;
                  inversion H ;
                  remember (a1 :: es) as es0 ;
                  subst a1 ;
                  clear Heq0 afte0 H H4 aft H0 IHHred0 ;
                  generalize dependent es ;
                  induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                  try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                       assert (const_list (b0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                  [ destruct H ; try (by inversion Heq0) ;
                    try (by destruct vs ; inversion Heq0 ;
                         first_not_const H) ; 
                    try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                    unfold lfilled, lfill in H0 ;
                    destruct lh as [bef aft |] ; last (by false_assumption) ;
                    destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                    move/eqP in H0 ;
                    rewrite H0 in Heq0 ; 
                    destruct bef ; inversion Heq0 ;
                    first_not_const Hbef
                  | rewrite Heq0 in H ;
                    simple_filled2 H k lh bef aft nn ll ll' ;
                    [ destruct bef ;
                      [ destruct es ; first empty_list_no_reduce ;
                        inversion H ; subst ;
                          by eapply IHHred0
                      | inversion H ;
                        first_not_const Hvs ]
                    | destruct bef ; inversion H ;
                      first_not_const Hvs ]]
                | inversion H ;
                  first_not_const Hvs ]]
            | destruct bef ; inversion H ;
              subst ; inversion Hvs0 ;
              destruct bef ; inversion H ;
              first_not_const Hvs ]] .
        destruct vs0.
        exfalso ;
          apply Logic.eq_sym in Heq0 ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|b0 ves]; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b2 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: b2 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst). 
        destruct H ; try (by inversion Heq0) ;
          try (by repeat (destruct vs ; first by inversion Heq0) ;
               inversion Heq0 ;
               first_not_const H) ; 
          try (by inversion Heq0 ; subst ; simpl in H ; false_assumption).
        unfold lfilled, lfill in H0 ;
          destruct lh as [bef aft |] ; last (by false_assumption) ;
          destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
          move/eqP in H0 ;
          rewrite H0 in Heq0.
        repeat (destruct bef ; first by inversion Heq0 ; subst ; first_not_const Hvs0).
        inversion Heq0 ; subst. first_not_const Hbef.
        rewrite - Heq0 in H ;
          simple_filled2 H k lh bef aft nn ll ll'.
        destruct bef.
        destruct es ; first empty_list_no_reduce.
        destruct es ; first (inversion H ; subst ; values_no_reduce).
        unfold const_list, forallb in Hvs0.
        repeat apply andb_true_iff in Hvs0 as [Hvs0 _].
        by rewrite Hvs0.
        destruct es ; first (inversion H ; subst ; values_no_reduce).
        inversion H. subst.
        by eapply IHHred0.
        destruct bef. 
        destruct es ; first empty_list_no_reduce. 
        destruct es ; first (inversion H ; subst ; values_no_reduce).
        unfold const_list, forallb in Hvs0.
        repeat apply andb_true_iff in Hvs0 as [? Hvs0].
        by rewrite H2.
        inversion H.
        remember (a2 :: a3 :: es) as es0 ;
          subst a2 a3.
        clear Heq0 afte0 H H5 aft H0 IHHred0 ;
          generalize dependent es.
        unfold const_list, forallb in Hvs0.
        apply andb_true_iff in Hvs0 as [_ Hvs0].
        induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [ destruct H ;
            try (by inversion Heq0) ;
            try (by destruct vs ; first (by inversion Heq0) ;
                 destruct vs ; inversion Heq0 ;
                 first_not_const H) ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ; 
            rewrite H0 in Heq0 ;
            destruct bef ; 
            inversion Heq0 ; subst ;
            inversion Hvs0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef 
          | rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                destruct es ; inversion H ; subst ;
                [ values_no_reduce 
                | by eapply IHHred0 ]
              | destruct bef ;
                [ destruct es ; first empty_list_no_reduce ;
                  inversion H ;
                  remember (a3 :: es) as es0 ;
                  subst a3 ;
                  clear Heq0 afte0 H H5 aft H0 IHHred0 ;
                  generalize dependent es ;
                  induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                  try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                       assert (const_list (b0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                  [ destruct H ; try (by inversion Heq0) ;
                    try (by destruct vs ; inversion Heq0 ;
                         first_not_const H) ; 
                    try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                    unfold lfilled, lfill in H0 ;
                    destruct lh as [bef aft |] ; last (by false_assumption) ;
                    destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                    move/eqP in H0 ;
                    rewrite H0 in Heq0 ; 
                    destruct bef ; inversion Heq0 ;
                    first_not_const Hbef
                  | rewrite Heq0 in H ;
                    simple_filled2 H k lh bef aft nn ll ll' ;
                    [ destruct bef ;
                      [ destruct es ; first empty_list_no_reduce ;
                        inversion H ; subst ;
                          by eapply IHHred0
                      | inversion H ;
                        first_not_const Hvs ]
                    | destruct bef ; inversion H ;
                      first_not_const Hvs ]]
                | inversion H ;
                  first_not_const Hvs1 ]]
            | destruct bef ; inversion H ;
              subst ; inversion Hvs0 ;
              destruct bef ; inversion H ;
              first_not_const Hvs1 ]] .
        destruct bef ; last by inversion H ; first_not_const Hvs.
        destruct es ; first empty_list_no_reduce.
        inversion H.
        remember (a3 :: es) as es0.
        subst a3.
        clear afte0 H5 Heq0 H aft H0 IHHred0.
        generalize dependent es. 
        induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|b0 ves]; inversion Heq0 ;
               assert (const_list (b0 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [ destruct H ; try (by inversion Heq0) ;
            try (by destruct vs ; inversion Heq0 ;
                 first_not_const H) ; 
            try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ;
            rewrite H0 in Heq0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef 
          | rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                inversion H ; subst ;
                  by eapply IHHred0
              | inversion H ;
                first_not_const Hvs ]
            | destruct bef ; inversion H ;
              first_not_const Hvs ]].
        apply first_values in H as (_ & Habs & _) => //= ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
        get_tail a1 vs0 vs1 b1 Htail1.
        rewrite Htail1 app_comm_cons in Hbefs.
        get_tail a0 vs1 vs2 b2 Htail2.
        rewrite Htail2 app_comm_cons app_comm_cons in Hbefs.
        get_tail a vs2 vs3 b3 Htail3.
        rewrite Htail3 in Hbefs.
        rewrite (separate1 (AI_basic _)) in Hbefs.
        rewrite (separate1 _ [_]) in Hbefs.
        repeat rewrite assoc_list_seq in Hbefs.
        repeat rewrite app_assoc in Hbefs.
        repeat apply app_inj_tail in Hbefs as [Hbefs ->].
        rewrite Htail1 app_comm_cons Htail2 app_comm_cons app_comm_cons Htail3 in Heq0.
        repeat rewrite - app_assoc in Heq0.
        simpl in Heq0.
        rewrite separate4 in Heq0.
        eexists _, vs3, afte0, [], [], _.
        repeat split => //= ; try by rewrite app_nil_r.
        rewrite - Hbefs in Hbef1.
        unfold const_list in Hbef1.
        rewrite forallb_app in Hbef1.
        apply andb_true_iff in Hbef1 as [_ Hbef1].
        done.
        by repeat econstructor.
      - left ; rewrite separate3 in Heq ;
          repeat rewrite app_assoc in Heq ;
          repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
          rewrite - app_comm_cons in Heq ;
          apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]) ;
          try (by const_list_app) ;
          destruct vs0.
        exfalso ;
          apply Logic.eq_sym in Heq0 ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|a0 ves]; inversion Heq0 ;
               assert (const_list (a0 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [ destruct H ; try (by inversion Heq0) ;
            try (by destruct vs ; inversion Heq0 ;
                 first_not_const H) ; 
            try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ;
            rewrite H0 in Heq0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef
          | rewrite - Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                inversion H ; subst ;
                  by eapply IHHred0
              | inversion H ;
                first_not_const Hvs ]
            | destruct bef ; inversion H ;
              first_not_const Hvs ]].
        destruct vs0.
        exfalso ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; 
          try (by inversion Heq0) ;
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [ destruct H ;
            try (by inversion Heq0) ;
            try (by destruct vs ; first (by inversion Heq0) ;
                 destruct vs ; inversion Heq0 ;
                 first_not_const H) ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ; 
            rewrite H0 in Heq0 ;
            destruct bef ; 
            inversion Heq0 ; subst ;
            inversion Hvs0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef 
          | rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                destruct es ; inversion H ; subst ;
                [ values_no_reduce 
                | by eapply IHHred0 ]
              | destruct bef ;
                [ destruct es ; first empty_list_no_reduce ;
                  inversion H ;
                  remember (a1 :: es) as es0 ;
                  subst a1 ;
                  clear Heq0 afte0 H H4 aft H0 IHHred0 ;
                  generalize dependent es ;
                  induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                  try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                       assert (const_list (b0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                  [ destruct H ; try (by inversion Heq0) ;
                    try (by destruct vs ; inversion Heq0 ;
                         first_not_const H) ; 
                    try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                    unfold lfilled, lfill in H0 ;
                    destruct lh as [bef aft |] ; last (by false_assumption) ;
                    destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                    move/eqP in H0 ;
                    rewrite H0 in Heq0 ; 
                    destruct bef ; inversion Heq0 ;
                    first_not_const Hbef
                  | rewrite Heq0 in H ;
                    simple_filled2 H k lh bef aft nn ll ll' ;
                    [ destruct bef ;
                      [ destruct es ; first empty_list_no_reduce ;
                        inversion H ; subst ;
                          by eapply IHHred0
                      | inversion H ;
                        first_not_const Hvs ]
                    | destruct bef ; inversion H ;
                      first_not_const Hvs ]]
                | inversion H ;
                  first_not_const Hvs ]]
            | destruct bef ; inversion H ;
              subst ; inversion Hvs0 ;
              destruct bef ; inversion H ;
              first_not_const Hvs ]] .
        destruct vs0.
        exfalso ;
          apply Logic.eq_sym in Heq0 ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|b0 ves]; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b2 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: b2 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst). 
        destruct H ; try (by inversion Heq0) ;
          try (by repeat (destruct vs ; first by inversion Heq0) ;
               inversion Heq0 ;
               first_not_const H) ; 
          try (by inversion Heq0 ; subst ; simpl in H ; false_assumption).
        unfold lfilled, lfill in H0 ;
          destruct lh as [bef aft |] ; last (by false_assumption) ;
          destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
          move/eqP in H0 ;
          rewrite H0 in Heq0.
        repeat (destruct bef ; first by inversion Heq0 ; subst ; first_not_const Hvs0).
        inversion Heq0 ; subst. first_not_const Hbef.
        rewrite - Heq0 in H ;
          simple_filled2 H k lh bef aft nn ll ll'.
        destruct bef.
        destruct es ; first empty_list_no_reduce.
        destruct es ; first (inversion H ; subst ; values_no_reduce).
        unfold const_list, forallb in Hvs0.
        repeat apply andb_true_iff in Hvs0 as [Hvs0 _].
        by rewrite Hvs0.
        destruct es ; first (inversion H ; subst ; values_no_reduce).
        inversion H. subst.
        by eapply IHHred0.
        destruct bef.
        destruct es ; first empty_list_no_reduce.
        destruct es ; first (inversion H ; subst ; values_no_reduce).
        unfold const_list, forallb in Hvs0.
        repeat apply andb_true_iff in Hvs0 as [? Hvs0].
        by rewrite H2.
        inversion H.
        remember (a2 :: a3 :: es) as es0 ;
          subst a2 a3.
        clear Heq0 afte0 H H5 aft H0 IHHred0 ;
          generalize dependent es.
        unfold const_list, forallb in Hvs0.
        apply andb_true_iff in Hvs0 as [_ Hvs0].
        induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [ destruct H ;
            try (by inversion Heq0) ;
            try (by destruct vs ; first (by inversion Heq0) ;
                 destruct vs ; inversion Heq0 ;
                 first_not_const H) ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ; 
            rewrite H0 in Heq0 ;
            destruct bef ; 
            inversion Heq0 ; subst ;
            inversion Hvs0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef 
          | rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                destruct es ; inversion H ; subst ;
                [ values_no_reduce 
                | by eapply IHHred0 ]
              | destruct bef ;
                [ destruct es ; first empty_list_no_reduce ;
                  inversion H ;
                  remember (a3 :: es) as es0 ;
                  subst a3 ;
                  clear Heq0 afte0 H H5 aft H0 IHHred0 ;
                  generalize dependent es ;
                  induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                  try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                       assert (const_list (b0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                  [ destruct H ; try (by inversion Heq0) ;
                    try (by destruct vs ; inversion Heq0 ;
                         first_not_const H) ; 
                    try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                    unfold lfilled, lfill in H0 ;
                    destruct lh as [bef aft |] ; last (by false_assumption) ;
                    destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                    move/eqP in H0 ;
                    rewrite H0 in Heq0 ; 
                    destruct bef ; inversion Heq0 ;
                    first_not_const Hbef
                  | rewrite Heq0 in H ;
                    simple_filled2 H k lh bef aft nn ll ll' ;
                    [ destruct bef ;
                      [ destruct es ; first empty_list_no_reduce ;
                        inversion H ; subst ;
                          by eapply IHHred0
                      | inversion H ;
                        first_not_const Hvs ]
                    | destruct bef ; inversion H ;
                      first_not_const Hvs ]]
                | inversion H ;
                  first_not_const Hvs1 ]]
            | destruct bef ; inversion H ;
              subst ; inversion Hvs0 ;
              destruct bef ; inversion H ;
              first_not_const Hvs1 ]] .
        destruct bef ; last by inversion H ; first_not_const Hvs.
        destruct es ; first empty_list_no_reduce.
        inversion H.
        remember (a3 :: es) as es0.
        subst a3.
        clear afte0 H5 Heq0 H aft H0 IHHred0.
        generalize dependent es. 
        induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|b0 ves]; inversion Heq0 ;
               assert (const_list (b0 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [ destruct H ; try (by inversion Heq0) ;
            try (by destruct vs ; inversion Heq0 ;
                 first_not_const H) ; 
            try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ;
            rewrite H0 in Heq0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef 
          | rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                inversion H ; subst ;
                  by eapply IHHred0
              | inversion H ;
                first_not_const Hvs ]
            | destruct bef ; inversion H ;
              first_not_const Hvs ]].
        apply first_values in H as (_ & Habs & _) => //= ; (try done) ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                                                    try (destruct He0 as [-> | ->]; by intros [? ?]).
        get_tail a1 vs0 vs1 b1 Htail1.
        rewrite Htail1 app_comm_cons in Hbefs.
        get_tail a0 vs1 vs2 b2 Htail2.
        rewrite Htail2 app_comm_cons app_comm_cons in Hbefs.
        get_tail a vs2 vs3 b3 Htail3.
        rewrite Htail3 in Hbefs.
        rewrite (separate1 (AI_basic _)) in Hbefs.
        rewrite (separate1 _ [_]) in Hbefs.
        repeat rewrite assoc_list_seq in Hbefs.
        repeat rewrite app_assoc in Hbefs.
        repeat apply app_inj_tail in Hbefs as [Hbefs ->].
        rewrite Htail1 app_comm_cons Htail2 app_comm_cons app_comm_cons Htail3 in Heq0.
        repeat rewrite - app_assoc in Heq0.
        simpl in Heq0.
        rewrite separate4 in Heq0.
        eexists _, vs3, afte0, [], [], _.
        repeat split => //= ; try by rewrite app_nil_r.
        rewrite - Hbefs in Hbef1.
        unfold const_list in Hbef1.
        rewrite forallb_app in Hbef1.
        apply andb_true_iff in Hbef1 as [_ Hbef1].
        done.
        by repeat econstructor. 
      - left ; repeat rewrite app_assoc in Heq.
        repeat rewrite - (app_assoc (_ ++ _)) in Heq.
        rewrite - app_comm_cons in Heq.
        apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try (by const_list_app).
        cut (forall nnn, length vs0 < nnn -> length vs0 < n  -> False).
        { intros Hnnn. destruct (decide (length vs0 < n)).
          exfalso ; by eapply Hnnn.
          assert (length vs0 >= n) ; first lia.
          rewrite - (take_drop (length vs0 - n) vs0) in Hbefs.
          assert (length (drop (length vs0 - n) vs0) = length vs). 
          { rewrite drop_length. rewrite Hr2. lia. }
          rewrite assoc_list_seq in Hbefs.
          destruct (app_inj_2 _ _ _ _ H0 Hbefs) as [Hbefs' Hvss].
          rewrite - (take_drop (length vs0 - n) vs0) Hvss in Heq0.
          rewrite - app_assoc in Heq0.
          rewrite separate1 in Heq0.
          rewrite (app_assoc vs) in Heq0.
          eexists _,(take (length vs0 - n) vs0),afte0,[],[],_ ;
            repeat split ; try done ; try by rewrite app_nil_r.
          rewrite - (take_drop (length vs0 - n) vs0) in Hvs0.
          unfold const_list in Hvs0.
          rewrite forallb_app in Hvs0.
          by apply andb_true_iff in Hvs0 as [? _].
          apply r_simple. by eapply rs_block. }
        intros nnn.
        clear Hbefs Hafts.
        generalize dependent afte0.
        generalize dependent vs0.
        generalize dependent es0'.
        generalize dependent es0.
        induction nnn.
        intros ; lia.
        intros es0 es0' Hred.
        induction Hred ; intros vs0 Hvs0 afte0 Heq Hnnn Hlen'  ;
          try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by  rewrite - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]) ;
               rewrite H1 ; apply v_to_e_is_const_list).
        { destruct H ;
            try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
            try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
            try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
            try (by rewrite - (app_nil_r [_;_;_;_]) separate3 - app_assoc in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])).
          - rewrite - (app_nil_r [_]) in Heq.
            apply first_values in Heq as (-> & Hblock & <-) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
            apply (block_not_enough_arguments_no_reduce s f vs0 t1s0 t2s0 es0
                                                        s f [AI_label m0 [] (vs0 ++ to_e_list es0)]) => //=.
            apply r_simple ; eapply rs_block => //=.
            inversion Hblock ; subst.
            by rewrite - Hr3 in Hlen'.
          - rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq.
            apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
            unfold const_list, forallb ; by rewrite H.
          - unfold lfilled, lfill in H0.
            destruct lh as [bef aft|] ; last by false_assumption.
            destruct (const_list bef) eqn:Hbef ; last by false_assumption.
            move/eqP in H0.
            rewrite H0 in Heq.
            apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]). }
        simple_filled2 H k lh bef aft nn ll ll'.
        rewrite H in Heq.
        edestruct first_non_value_reduce as (vse & e & afte & Hvse & He & Heqe) ;
          try exact Hred.
        rewrite Heqe in Heq.
        repeat rewrite app_assoc in Heq.
        repeat rewrite - (app_assoc (_ ++ _)) in Heq.
        rewrite - app_comm_cons in Heq.
        apply first_values in Heq as (<- & -> & <-) ; try done ; try (by destruct He ; destruct e => // ; destruct b => //) ;
          try (destruct He as [-> | ->]; by intros [? ?]) ;
          try by const_list_app.
        destruct bef.
        eapply IHHred => //=.
        simpl in Hlen', Hnnn.
        rewrite app_length in Hlen', Hnnn.
        eapply IHnnn => //= ; lia.
        rewrite H in Heq.
        apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
      - left ; repeat rewrite app_assoc in Heq.
        repeat rewrite - (app_assoc (_ ++ _)) in Heq.
        rewrite - app_comm_cons in Heq.
        apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try (by const_list_app).
        cut (forall nnn, length vs0 < nnn -> length vs0 < n  -> False).
        { intros Hnnn. destruct (decide (length vs0 < n)).
          exfalso ; by eapply Hnnn.
          assert (length vs0 >= n) ; first lia.
          rewrite - (take_drop (length vs0 - n) vs0) in Hbefs.
          assert (length (drop (length vs0 - n) vs0) = length vs). 
          { rewrite drop_length. rewrite Hr2. lia. }
          rewrite assoc_list_seq in Hbefs.
          destruct (app_inj_2 _ _ _ _ H0 Hbefs) as [Hbefs' Hvss].
          rewrite - (take_drop (length vs0 - n) vs0) Hvss in Heq0.
          rewrite - app_assoc in Heq0.
          rewrite separate1 in Heq0.
          rewrite (app_assoc vs) in Heq0.
          eexists _,(take (length vs0 - n) vs0),afte0,[],[],_ ;
            repeat split ; try done ; try by rewrite app_nil_r.
          rewrite - (take_drop (length vs0 - n) vs0) in Hvs0.
          unfold const_list in Hvs0.
          rewrite forallb_app in Hvs0.
          by apply andb_true_iff in Hvs0 as [? _].
          apply r_simple. by eapply rs_loop. }
        intros nnn.
        clear Hbefs Hafts.
        generalize dependent afte0.
        generalize dependent vs0.
        generalize dependent es0'.
        generalize dependent es0.
        induction nnn.
        intros ; lia.
        intros es0 es0' Hred.
        induction Hred ; intros vs0 Hvs0 afte0 Heq Hnnn Hlen' ;
          try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
               try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (destruct v ; try (destruct b) ; try done) ;
          try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
               try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
               try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by  rewrite - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
               try (destruct He0 as [-> | ->]; by intros [? ?]) ;
               rewrite H1 ; apply v_to_e_is_const_list).
        { destruct H ;
            try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                 try (destruct He0 as [-> | ->]; by intros [? ?])) ;
            try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                 try (destruct He0 as [-> | ->]; by intros [? ?])) ;
            try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                 try (destruct He0 as [-> | ->]; by intros [? ?])) ;
            try (by rewrite - (app_nil_r [_;_;_;_]) separate3 - app_assoc in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                 try (destruct He0 as [-> | ->]; by intros [? ?])).
          - rewrite - (app_nil_r [_]) in Heq.
            apply first_values in Heq as (-> & Hblock & <-) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
              try (destruct He0 as [-> | ->]; by intros [? ?]);
              apply (block_not_enough_arguments_no_reduce s f vs0 t1s0 t2s0 es0
                                                          s f [AI_label m0 [] (vs0 ++ to_e_list es0)]) => //=.
            apply r_simple ; eapply rs_block => //=.
            inversion Hblock ; subst.
            by rewrite - Hr3 in Hlen'.
          - rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq.
            apply first_values in Heq as (_ & Habs & _) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
              try (destruct He0 as [-> | ->]; by intros [? ?]).
            unfold const_list, forallb ; by rewrite H.
          - unfold lfilled, lfill in H0.
            destruct lh as [bef aft|] ; last by false_assumption.
            destruct (const_list bef) eqn:Hbef ; last by false_assumption.
            move/eqP in H0.
            rewrite H0 in Heq.
            apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]). }
        simple_filled2 H k lh bef aft nn ll ll'.
        rewrite H in Heq.
        edestruct first_non_value_reduce as (vse & e & afte & Hvse & He & Heqe) ;
          try exact Hred.
        rewrite Heqe in Heq.
        repeat rewrite app_assoc in Heq.
        repeat rewrite - (app_assoc (_ ++ _)) in Heq.
        rewrite - app_comm_cons in Heq.
        apply first_values in Heq as (<- & -> & <-) ; try done ; try (by destruct He ; destruct e => // ; destruct b => //) ;
          try (destruct He as [-> | ->]; by intros [? ?]) ;
          try by const_list_app.
        destruct bef.
        eapply IHHred => //=.
        simpl in Hlen', Hnnn.
        rewrite app_length in Hlen', Hnnn.
        eapply IHnnn => //= ; lia.
        rewrite H in Heq.
        apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
      
      - right.
        unfold lfilled, lfill in Hr2.
        destruct lh as [bef aft|] ; last by false_assumption.
        destruct (const_list bef) eqn:Hbef ; last by false_assumption.
        move/eqP in Hr2 ; subst es.
        repeat rewrite app_assoc in Heq.
        repeat rewrite - (app_assoc (_ ++ _)) in Heq.
        rewrite - app_comm_cons in Heq.
        apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try by const_list_app.
        exists (LH_base vs0 afte0), (LH_base bef aft).
        split ; unfold lfilled, lfill.
        by rewrite Hvs0 Heq0.
        by rewrite Hbef. }
         
    - left ; repeat rewrite app_assoc in Heq.
      repeat rewrite - (app_assoc (_ ++ _)) in Heq.
      rewrite - app_comm_cons in Heq. 

      apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
        try (by const_list_app ; rewrite Hr3 ; apply v_to_e_is_const_list ).
      cut (forall nnn, length vs0 < nnn -> length vs0 < n  -> False).
      { intros Hnnn. destruct (decide (length vs0 < n)).
        exfalso ; by eapply Hnnn.
        assert (length vs0 >= n) ; first lia.
        rewrite - (take_drop (length vs0 - n) vs0) in Hbefs.
        assert (length (drop (length vs0 - n) vs0) = length ves). 
        { rewrite drop_length. rewrite Hr3 v_to_e_length Hr4. lia. }
        rewrite assoc_list_seq in Hbefs.
        destruct (app_inj_2 _ _ _ _ H0 Hbefs) as [Hbefs' Hvss].
        rewrite - (take_drop (length vs0 - n) vs0) Hvss in Heq0.
        rewrite - app_assoc in Heq0.
        rewrite separate1 in Heq0.
        rewrite (app_assoc ves) in Heq0.
        eexists _,(take (length vs0 - n) vs0),afte0,[],[],_ ;
          repeat split ; try done ; try by rewrite app_nil_r.
        rewrite - (take_drop (length vs0 - n) vs0) in Hvs0.
        unfold const_list in Hvs0.
        rewrite forallb_app in Hvs0.
        by apply andb_true_iff in Hvs0 as [? _].
        by econstructor. }
      intros nnn.
      clear Hbefs Hafts.
      generalize dependent afte0.
      generalize dependent vs0.
      generalize dependent es0'.
      generalize dependent es0.
      induction nnn.
      intros ; lia.
      intros es0 es0' Hred.
      induction Hred ; intros afte0 vs0 Hvs0 Heq Hnnn Hlen' ;
        try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by  rewrite - (app_nil_r [_]) in Heq ;
             apply first_values in Heq as (_ & Habs & _) ;try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]) ;
             rewrite H1 ; apply v_to_e_is_const_list).
      { destruct H ;
          try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_;_;_;_]) separate3 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])).
        - rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq.
          apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
          unfold const_list, forallb ; by rewrite H.
        - unfold lfilled, lfill in H0.
          destruct lh as [bef aft|] ; last by false_assumption.
          destruct (const_list bef) eqn:Hbef ; last by false_assumption.
          move/eqP in H0.
          rewrite H0 in Heq.
          apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]). }
      + rewrite - (app_nil_r [_]) in Heq.
        apply first_values in Heq as (-> & Hblock & <-) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]).
        eapply (invoke_not_enough_arguments_no_reduce_native s f _ _ s f) => //=.
        rewrite Hr2 in Hr1.
        inversion Hblock ; subst a.
        exact Hr1.
        by econstructor.
        by rewrite Hr6.
        rewrite H1.
        by apply v_to_e_is_const_list.
      + rewrite - (app_nil_r [_]) in Heq.
        apply first_values in Heq as (-> & Hblock & <-) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]).
        eapply (invoke_not_enough_arguments_no_reduce_native s f _ _ s f) => //=.
        rewrite Hr2 in Hr1.
        inversion Hblock ; subst a.
        exact Hr1.
        by econstructor.
        by rewrite Hr6.
        rewrite H1.
        by apply v_to_e_is_const_list.
      + simple_filled2 H k0 lh bef aft nn ll ll'.
        rewrite H in Heq.
        edestruct first_non_value_reduce as (vse & e & afte & Hvse & He & Heqe) ;
          try exact Hred.
        rewrite Heqe in Heq.
        repeat rewrite app_assoc in Heq.
        repeat rewrite - (app_assoc (_ ++ _)) in Heq.
        rewrite - app_comm_cons in Heq.
        apply first_values in Heq as (<- & -> & <-) ; try done ; try (by destruct He ; destruct e => // ; destruct b => //) ;
          try (destruct He as [-> | ->]; by intros [? ?]);
          try by const_list_app.
        destruct bef.
        eapply IHHred => //=.
        simpl in Hlen', Hnnn.
        rewrite app_length in Hlen', Hnnn.
        eapply IHnnn => //= ; lia.
        rewrite H in Heq.
        apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
    - left ; repeat rewrite app_assoc in Heq.
      repeat rewrite - (app_assoc (_ ++ _)) in Heq.
      rewrite - app_comm_cons in Heq. 

      apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
        try (by const_list_app ; rewrite Hr3 ; apply v_to_e_is_const_list ).
      cut (forall nnn, length vs0 < nnn -> length vs0 < n  -> False).
      { intros Hnnn. destruct (decide (length vs0 < n)).
        exfalso ; by eapply Hnnn.
        assert (length vs0 >= n) ; first lia.
        rewrite - (take_drop (length vs0 - n) vs0) in Hbefs.
        assert (length (drop (length vs0 - n) vs0) = length ves). 
        { rewrite drop_length. rewrite Hr3 v_to_e_length Hr4. lia. }
        rewrite assoc_list_seq in Hbefs.
        destruct (app_inj_2 _ _ _ _ H0 Hbefs) as [Hbefs' Hvss].
        rewrite - (take_drop (length vs0 - n) vs0) Hvss in Heq0.
        rewrite - app_assoc in Heq0.
        rewrite separate1 in Heq0.
        rewrite (app_assoc ves) in Heq0.
        eexists _,(take (length vs0 - n) vs0),afte0,[],[],_ ;
          repeat split ; try done ; try by rewrite app_nil_r.
        rewrite - (take_drop (length vs0 - n) vs0) in Hvs0.
        unfold const_list in Hvs0.
        rewrite forallb_app in Hvs0.
        by apply andb_true_iff in Hvs0 as [? _].
        by econstructor. }
      intros nnn.
      clear Hbefs Hafts.
      generalize dependent afte0.
      generalize dependent vs0.
      generalize dependent es0'.
      generalize dependent es0.
      induction nnn.
      intros ; lia.
      intros es0 es0' Hred.
      induction Hred ; intros afte0 vs0 Hvs0 Heq Hnnn Hlen' ;
        try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by  rewrite - (app_nil_r [_]) in Heq ;
             apply first_values in Heq as (_ & Habs & _) ;try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]) ;
             rewrite H1 ; apply v_to_e_is_const_list).
      { destruct H ;
          try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_;_;_;_]) separate3 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])).
        - rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq.
          apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
          unfold const_list, forallb ; by rewrite H.
        - unfold lfilled, lfill in H0.
          destruct lh as [bef aft|] ; last by false_assumption.
          destruct (const_list bef) eqn:Hbef ; last by false_assumption.
          move/eqP in H0.
          rewrite H0 in Heq.
          apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]). }
      + rewrite - (app_nil_r [_]) in Heq.
        apply first_values in Heq as (-> & Hblock & <-) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ; 
          try (destruct He0 as [-> | ->]; by intros [? ?]).
        eapply (invoke_not_enough_arguments_no_reduce_host s f _ _ s f) => //=.
        rewrite Hr2 in Hr1.
        inversion Hblock ; subst a.
        exact Hr1.
        by econstructor.
        by rewrite Hr5.
        rewrite H1.
        by apply v_to_e_is_const_list.
      + rewrite - (app_nil_r [_]) in Heq.
        apply first_values in Heq as (-> & Hblock & <-) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]).
        eapply (invoke_not_enough_arguments_no_reduce_host s f _ _ s f) => //=.
        rewrite Hr2 in Hr1.
        inversion Hblock ; subst a.
        exact Hr1.
        by econstructor.
        by rewrite Hr5.
        rewrite H1.
        by apply v_to_e_is_const_list.
      + simple_filled2 H k lh bef aft nn ll ll'.
        rewrite H in Heq.
        edestruct first_non_value_reduce as (vse & e & afte & Hvse & He & Heqe) ;
          try exact Hred.
        rewrite Heqe in Heq.
        repeat rewrite app_assoc in Heq.
        repeat rewrite - (app_assoc (_ ++ _)) in Heq.
        rewrite - app_comm_cons in Heq.
        apply first_values in Heq as (<- & -> & <-) ; try done ; try (by destruct He ; destruct e => // ; destruct b => //) ; try (destruct He as [-> | ->]; by intros [? ?]);
          try by const_list_app.
        destruct bef.
        eapply IHHred => //=.
        simpl in Hlen', Hnnn.
        rewrite app_length in Hlen', Hnnn.
        eapply IHnnn => //= ; lia.
        rewrite H in Heq.
        apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
    - unfold lfilled, lfill in Hr2.
      destruct k.
      { destruct lh as [bef aft|] ; last by false_assumption.
        destruct (const_list bef) eqn:Hbef ; last by false_assumption.
        move/eqP in Hr2.
        destruct bef.
        destruct aft.
        unfold lfilled, lfill in Hr3 ; simpl in Hr3, Hr2.
        repeat rewrite app_nil_r in Hr3, Hr2.
        move/eqP in Hr3.
        subst.
        by eapply IHHred.
        edestruct IHnnnn as [(core & bc0 & ac0 & bc1 & ac1 & core' & Hbc0 & Hbc1 &
                                Hes0 & Hes & Hbefs & Hafts & Hredcore & Hcore') |
                              (lh0 & lh1 & Hfill0 & Hfill1 & Hσ)].
        exact Hbef1.
        exact Hred0.
        exact Hr1.
        subst.
        rewrite Heq.
        simpl.
        repeat rewrite app_assoc.
        rewrite - (app_assoc (_ ++ _)).
        done.
        rewrite Hr2 in Hlen.
        simpl in Hlen.
        rewrite app_length in Hlen.
        simpl in Hlen.
        lia.
        left.
        eexists core,bc0,ac0,bc1,(ac1 ++ (a :: aft)),core'.
        repeat split => //=.
        rewrite Hr2 Hes.
        simpl.
        repeat rewrite app_assoc.
        done.
        by rewrite - app_assoc.
        repeat rewrite app_assoc.
        rewrite - (app_assoc bc1).
        rewrite Hcore'.
        unfold lfilled, lfill in Hr3 ; simpl in Hr3.
        move/eqP in Hr3.
        by rewrite Hr3.
        right.
        assert (lfilled 0 (LH_base [] (a :: aft)) es les).
        unfold lfilled, lfill => //= ; by rewrite Hr2.
        destruct (lfilled_trans Hfill1 H) as [lh' Hfilltrap].
        eexists _,_ ; split => //=.
        edestruct IHnnnn as [(core & bc0 & ac0 & bc1 & ac1 & core' & Hbc0 & Hbc1 &
                                Hes0 & Hes & Hbefs & Hafts & Hredcore & Hcore') |
                              (lh0 & lh1 & Hfill0 & Hfill1 & Hσ)].
        instantiate (1 := (bef1 ++ a :: bef)).
        by const_list_app.
        exact Hred0.
        exact Hr1.
        instantiate (1 := (aft ++ aft1)).
        subst.
        rewrite Heq.
        simpl.
        repeat rewrite - app_assoc.
        done.
        rewrite Hr2 in Hlen.
        simpl in Hlen.
        repeat rewrite app_length in Hlen.
        simpl in Hlen.
        lia.
        left.
        eexists core,bc0,ac0,(a :: bef ++ bc1),(ac1 ++ aft),core'.
        repeat split => //.
        rewrite app_comm_cons.
        by const_list_app.
        rewrite Hr2 Hes.
        simpl.
        repeat rewrite app_assoc.
        done.
        rewrite Hbefs.
        repeat rewrite - app_assoc.
        done.
        rewrite Hafts.
        by rewrite - app_assoc.
        rewrite app_comm_cons.
        repeat rewrite - app_assoc.
        rewrite (app_assoc bc1).
        rewrite (app_assoc (bc1 ++ core')).
        rewrite - (app_assoc bc1).
        rewrite Hcore'.
        unfold lfilled, lfill in Hr3.
        rewrite Hbef in Hr3.
        move/eqP in Hr3.
        by rewrite Hr3.
        right.
        assert (lfilled 0 (LH_base (a :: bef) aft) es les).
        unfold lfilled, lfill ; by rewrite Hbef Hr2.
        destruct (lfilled_trans Hfill1 H) as [lh' Hfilltrap].
        eexists _,_ ; split => //=. }
      fold lfill in Hr2.
      destruct lh ; first by false_assumption.
      destruct (const_list l) eqn:Hl ; last by false_assumption.
      destruct (lfill k lh es) eqn:Hfill ; last by false_assumption.
      move/eqP in Hr2.
      rewrite Hr2 in Heq.
      repeat rewrite app_assoc in Heq.
      repeat rewrite - (app_assoc (_ ++ _)) in Heq.
      repeat rewrite - app_comm_cons in Heq.
      apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ; try (destruct He0 as [-> | ->]; by intros [? ?]);
        try by const_list_app.
      unfold lfilled, lfill in Hr3 ; fold lfill in Hr3.
      rewrite Hl in Hr3.
      destruct (lfill k lh es') eqn : Hfill' ; last by false_assumption.
      left ; eexists [AI_label n l0 l2], vs0, afte0, l, l1, _.
      repeat split => //=.
      eapply r_label.
      exact Hr1.
      instantiate (1 := LH_rec [] n l0 lh []).
      instantiate (1 := S k).
      unfold lfilled, lfill ; fold lfill => //=.
      rewrite Hfill.
      done.
      unfold lfilled, lfill ; fold lfill => //=.
      rewrite Hfill'.
      done.
      by move/eqP in Hr3.
  Qed.

End reduction_core.
