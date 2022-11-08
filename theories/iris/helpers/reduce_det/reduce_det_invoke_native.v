From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_properties iris_reduce_det_prelude.

Lemma invoke_native_det ws2 f2 es2 s a f f' t1s t2s ts es vcs:
  nth_error (s_funcs s) a = Some (FC_func_native (f_inst f') (Tf t1s t2s) ts es) ->
  length t1s = length vcs ->
  f_locs f' = (vcs ++ n_zeros ts) ->
  reduce s f (v_to_e_list vcs ++ [AI_invoke a]) ws2 f2 es2 ->
  (s, f, [AI_local (length t2s) f' [AI_basic (BI_block (Tf [] t2s) es)]]) = (ws2, f2, es2).
Proof.
  remember (v_to_e_list vcs ++ [AI_invoke a])%SEQ as es0.
  move => Hnth Hlen Hflocs Hred.
  induction Hred ; try by do 4 destruct vcs => //; try by inversion Heqes0 ;
                                                try by (apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs).
  (* 3 remaining cases *)
  (* reduce_simple *)
  { destruct H ; (try by inversion Heqes0) ;
    (try by do 5 destruct vcs => //=);
    (try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs).
    rewrite Heqes0 in H0 ; filled_trap H0 Hxl1.
    apply in_app_or in Hxl1.
    destruct Hxl1; try by simpl in H1; destruct H1.
    apply const_list_In in H1 => //.
      by apply v_to_e_is_const_list. }
  (* Invoke native, the desired case *)
  { apply app_inj_tail in Heqes0 as [-> Habs]; inversion Habs; subst.
    apply v_to_e_inj in H1; subst.
    rewrite Hnth in H.
    inversion H; subst; clear H.
    do 3 f_equal. 
    destruct f', f'0. simpl in H1, H4, H8; by subst; f_equal.
  }
  { apply app_inj_tail in Heqes0 as [-> Ha].
    inversion Ha ; subst.
    rewrite Hnth in H ; done. } 
  (* r_label *)
  {
    rewrite Heqes0 in H. simple_filled H k lh bef aft nn ll ll'.
    (* es0 is either a const which can be handled by Hred, or AI_invoke
         which we can then apply the IH. *)
    - unfold lfilled, lfill in H0.
      rewrite Hvs in H0.
      move/eqP in H0.
      (* If both aft and bef are empty (trivial r_label), we can just apply the IH; this is also the only place where IH is ever needed. Otherwise, if bef is shorter, we do not have enough arguments; on the other hand, aft cannot be non-empty since AI_invoke is the last non-const instruction. *)
      destruct aft as [| ea aft]. { destruct bef as [| eb bef]. { rewrite app_nil_l app_nil_r in H0.
                                                                  subst.
                                                                  rewrite app_nil_l app_nil_r in H.
                                                                    by apply IHHred.
                                                                }
                                                                destruct es0 ; first by empty_list_no_reduce.
                                    exfalso.
                                    get_tail a0 es0 ys y Htail.
                                    rewrite Htail app_nil_r in H. 
                                    rewrite app_assoc in H. apply app_inj_tail in H as [Hvs' Hy].
                                    rewrite Htail in Hred. rewrite <- Hy in Hred.
                                    eapply invoke_not_enough_arguments_no_reduce_native => //=.
                                    - assert (const_list (v_to_e_list vcs)) as Hconst; first by apply v_to_e_is_const_list.           
                                      rewrite Hvs' in Hconst.
                                      unfold const_list in Hconst. rewrite forallb_app in Hconst.
                                        by apply andb_true_iff in Hconst as [_ Hys].
                                    - rewrite Hlen.
                                      replace (length vcs) with (length (v_to_e_list vcs)); last by apply v_to_e_length.
                                      rewrite Hvs' => /=.
                                      rewrite app_length.
                                      lia. }
                                  exfalso.
      get_tail ea aft aft' a' Htail. rewrite Htail in H.
      do 2 rewrite app_assoc in H.
      apply app_inj_tail in H as [Hvs' <-].
      values_no_reduce.
      assert (const_list (v_to_e_list vcs)) as Hconst; first by apply v_to_e_is_const_list.
      rewrite Hvs' in Hconst.
      unfold const_list in Hconst. do 2 rewrite forallb_app in Hconst.
      apply andb_true_iff in Hconst as [Hconst _].
        by apply andb_true_iff in Hconst as [_ Hconst].
    - apply in_app_or in Hxl1 as [Hxl1 | Hxl1] => /=; last by destruct Hxl1.
      apply const_list_In in Hxl1 => //.
        by apply v_to_e_is_const_list.
  }
Qed.
  
