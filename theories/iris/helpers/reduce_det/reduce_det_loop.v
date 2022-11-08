From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_det_prelude.

Lemma loop_det vs n m t1s t2s s f es s' f' es' :
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  reduce s f (vs ++ [AI_basic (BI_loop (Tf t1s t2s) es)]) s' f' es' ->
  reduce_det_goal s f [AI_label n [AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)] s' f' es' (vs ++ [AI_basic (BI_loop (Tf t1s t2s) es)]).
Proof.
  move => H H0 H1 H2 Hred.
  remember (vs ++ [AI_basic (BI_loop (Tf t1s t2s) es)])%SEQ as es0.
  apply Logic.eq_sym in Heqes0.
  induction Hred ; (try by repeat ((by inversion Heqes0) +
                                    (destruct vs ; first by inversion Heqes0))) ;
  try by right ; right ; left ;
    exists a ; rewrite first_instr_const => //= ; subst ; apply v_to_e_is_const_list.
  { left ; destruct H3 ;
      try by repeat ((by inversion Heqes0) +
                     (destruct vs ; first by inversion Heqes0)).
    apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
    apply app_inj_tail in Heqes0 as [Hvs Hbl].
      by inversion Hbl ; subst.
      rewrite <- Heqes0 in H4.
      unfold lfilled, lfill in H4. destruct lh ; last by false_assumption.
      remember (const_list l) as b eqn:Hl ;
        destruct b ; last by false_assumption.
      move/eqP in H4.
      replace [AI_basic (BI_block (Tf t1s t2s) es)] with
          (AI_basic (BI_block (Tf t1s t2s) es) :: []) in H4 => //=.
      apply first_values in H4 as (_ & Habs & _) => //= ; try by (intros [? ?]). }
  {
    apply app_inj_tail in Heqes0 as [? Hcontra].
      by inversion Hcontra.
  }
  {
    apply app_inj_tail in Heqes0 as [? Hcontra].
      by inversion Hcontra.
  }
  simple_filled H3 k lh bef aft nn ll ll'.
  destruct aft. { destruct bef. { rewrite app_nil_l app_nil_r in H3.
                                  unfold lfilled, lfill in H4 ; simpl in H4.
                                  move/eqP in H4 ; rewrite app_nil_r in H4 ; subst.
                                  apply IHHred => //=. }
                                destruct es0 ; first by empty_list_no_reduce.
                  get_tail a0 es0 ys y Htail.
                  rewrite Htail app_nil_r in H3. rewrite <- Heqes0 in H3.
                  rewrite app_assoc in H3. apply app_inj_tail in H3 as [Hvs' Hy].
                  rewrite Htail in Hred. rewrite <- Hy in Hred. exfalso.
                  apply (loop_not_enough_arguments_no_reduce
                           _ _ _ _ _ _ _ _ _ Hred).
                  - rewrite Hvs' in H.
                    unfold const_list in H. rewrite forallb_app in H.
                      by apply andb_true_iff in H as [_ Hys].
                  - rewrite Hvs' in H0. simpl in H0. subst. rewrite app_length in H0.
                    lia. }
                get_tail a aft aft' a' Htail. rewrite Htail in H3.
  rewrite <- Heqes0 in H3. do 2 rewrite app_assoc in H3.
  apply app_inj_tail in H3 as [Hvs' _].
  exfalso ; values_no_reduce. rewrite Hvs' in H.
  unfold const_list in H. do 2 rewrite forallb_app in H.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ H].
  done. rewrite <- Heqes0 in Hxl1. apply in_app_or in Hxl1 as [Habs | Habs].
  intruse_among_values vs Habs H. inversion Habs ; inversion H5.
Qed.
