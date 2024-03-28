(** Several soundness properties of the relational instantiation. **)
(** Most notably, the post-instantiation store is a well-typed extension
    of the old store, and the generated module instance is well-typed in 
    that store. **)

From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat.
From Wasm Require Import instantiation_spec instantiation_properties type_preservation.
From Coq Require Import BinNat NArith ZArith.
Require Import Coq.Program.Equality.

Section Host.

Context `{ho: host}.

(*
Lemma functions_agree_aux s_funcs funcs f tf: 
  functions_agree s_funcs f tf ->
  functions_agree (List.app s_funcs funcs) f tf.
Proof.
  rewrite /functions_agree /typing.functions_agree.
  move/andP => [H1 H2]. move/eqP in H2.
  apply/andP. split.
  + (* f < length (s_funcs [::func])  *)
    rewrite app_length.
    by rewrite ssrnat.ltn_addr.
  + (* option_map cl_type (List.nth_error (s_funcs [::func]) f) == Some tf *)
    apply/eqP.
    rewrite <-H2.
    apply f_equal.
    apply nth_error_app1.
    by apply/ssrnat.ltP.
Qed.

Lemma globals_agree_aux s_globs globs n tg: 
  globals_agree s_globs n tg ->
  globals_agree (s_globs ++ globs) n tg.
Proof.
  rewrite /globals_agree.
  move/andP => [H1 H2]. move/eqP in H2.
  apply/andP. split.
  + rewrite app_length.
    by rewrite ssrnat.ltn_addr.
  + apply/eqP.
    rewrite <- H2.
    apply f_equal.
    apply nth_error_app1.
    by apply/ssrnat.ltP.
Qed.

Lemma tabi_agree_aux s_tabs tabs n tt:
  tabi_agree s_tabs n tt -> 
  tabi_agree (s_tabs ++ tabs) n tt.
Proof.
  rewrite /tabi_agree.
  move/andP => [H1 H2].
  apply/andP. split.
  + rewrite app_length.
    by rewrite ssrnat.ltn_addr.
  + assert (H: nth_error (s_tabs ++ tabs) n = nth_error s_tabs n).
    { apply nth_error_app1. by apply/ssrnat.ltP. }
    by rewrite -> H.
Qed.

Lemma memi_agree_aux s_mems mems n tm:
  memi_agree s_mems n tm -> 
  memi_agree (s_mems ++ mems) n tm.
Proof.
  rewrite /memi_agree.
  move/andP => [H1 H2].
  apply/andP. split.
  + rewrite app_length.
    by rewrite ssrnat.ltn_addr.
  + assert (H: nth_error (s_mems ++ mems) n = nth_error s_mems n).
    { apply nth_error_app1. by apply/ssrnat.ltP. }
    by rewrite -> H.
Qed.

Lemma cl_type_check_single_aux s_funcs s_tables s_mems s_globals func funcs tabs mems globs:
  cl_type_check_single {| s_funcs := s_funcs; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} func ->
  cl_type_check_single {| s_funcs := s_funcs ++ funcs; 
                          s_tables := s_tables ++ tabs;
                          s_mems := s_mems ++ mems;
                          s_globals := s_globals ++ globs|} func.
Proof.
  move => Hcl.
  destruct Hcl as [tf' Hcl_typing].
  exists tf'.
  destruct func as [i tf ts es | tf h].
  + (* cl_typing_native *)
    inversion Hcl_typing; subst.
    rename H4 into Hinst_typing. rename H8 into Hbe_typing.
    apply cl_typing_native
      with (C := C)
           (C' := upd_local_label_return C (t1s ++ ts) ([::t2s]) (Some t2s))
          => //=.
    destruct C.
    rewrite /inst_typing. simpl.
    rewrite /inst_typing in Hinst_typing. simpl in Hinst_typing.
    destruct tc_local => //=.
    destruct tc_label => //=.
    destruct tc_return => //=.
    destruct i.
    move/andP in Hinst_typing. destruct Hinst_typing as [Hinst_typing Hmem].
    move/andP in Hinst_typing. destruct Hinst_typing as [Hinst_typing Htab].
    move/andP in Hinst_typing. destruct Hinst_typing as [Hinst_typing Hglb].
    move/andP in Hinst_typing. destruct Hinst_typing as [Hty Hfunc].
    move/eqP in Hty; subst.
    apply/andP. split => //=.
    apply/andP. split => //=.
    apply/andP. split => //=.
    apply/andP. split => //=.
    - (* functions_agree *)
      eapply all2_weaken.
      apply functions_agree_aux.
      by exact Hfunc.
    - (* globals_agree *)
      eapply all2_weaken.
      apply globals_agree_aux.
      by exact Hglb.
    - (* tabi_agree *)
      eapply all2_weaken.
      apply tabi_agree_aux.
      by exact Htab.
    - (* memi_agree *)
      eapply all2_weaken.
      apply memi_agree_aux.
      by exact Hmem.
  + (* cl_typing_host *)
    inversion Hcl_typing; subst.
    by apply cl_typing_host.
Qed.

Let tab_agree := @tab_agree host_function.

Lemma tab_agree_aux s_funcs s_tables s_mems s_globals tab funcs tabs mems globs:
  tab_agree {| s_funcs := s_funcs; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} tab ->
  tab_agree {| s_funcs := s_funcs ++ funcs;
               s_tables := s_tables ++ tabs;
               s_mems := s_mems ++ mems;
               s_globals := s_globals ++ globs |} tab .
Proof.
  rewrite /tab_agree /typing.tab_agree.
  move => Htb.
  destruct Htb as [Htable Hs_tables]; subst.
  constructor.
  - (* forall tabcl_agree (table_data tab) *)
    induction (table_data tab) as [| hd tl IH]; first by constructor.
    (* forall tabcl_agree hd :: tl *)
    inversion Htable as [| x y Hhd Htl]; subst.
    constructor.
    (* tabcl_agree hd *)
    destruct hd => //=. 
    rewrite /tabcl_agree in Hhd. simpl in Hhd.
    rewrite size_cat. by rewrite ssrnat.ltn_addr.
    (* forall tabcl_agree tl *)
    apply IH. exact Htl.
  - (* tabsize_agree table *)
    assumption.
Qed.


Lemma external_typing_aux s v_imps t_imps:
  Forall2 (instantiation_spec.external_typing host_function s) v_imps t_imps -> 
  length (ext_funcs v_imps) = length (ext_t_funcs t_imps) /\
  length (ext_globs v_imps) = length (ext_t_globs t_imps) /\
  length (ext_tabs v_imps) = length (ext_t_tabs t_imps) /\
  length (ext_mems v_imps) = length (ext_t_mems t_imps).
Proof.
  generalize t_imps.
  induction v_imps as [| v_imp v_imps' IH ].
  - move => t_imps' H.
    apply Forall2_length in H.
    by destruct t_imps' => //=.
  - clear t_imps. move => t_imps H.
    inversion H; subst.
    rewrite /ext_funcs /ext_t_funcs.
    repeat split; inversion H2; subst; simpl; f_equal; by apply IH.
Qed.

Lemma tab_agree_from_typing mod_tables s_tabs s :
  all module_tab_typing mod_tables -> 
  s_tabs = map (fun '{| tt_limits := {| lim_min := min; lim_max := maxo |} |} =>
              {| table_data := repeat None (ssrnat.nat_of_bin min); table_max_opt := maxo |})
                 (map modtab_type mod_tables) ->
  Forall (typing.tab_agree (host_function:=host_function) s) s_tabs.
Proof.
  move => HTabType Heqs_tabs_new.
  rewrite List.Forall_forall => ti Hin.
      
  rewrite -> Heqs_tabs_new in Hin.
  eapply List.In_nth_error in Hin.
  destruct Hin as [n Hnth].
  rewrite Coqlib.list_map_nth in Hnth.
  rewrite /Coqlib.option_map in Hnth.
  destruct (nth_error (map modtab_type mod_tables) n) eqn: Heqt => //=.
  inversion Hnth. clear Hnth.
  rename H0 into Heq_ti.

  assert (Hex_tab: exists tab, nth_error mod_tables n = Some tab).
  {
    eapply nth_error_same_length_list with (l1 := (map modtab_type mod_tables)) => //; eauto.
    by rewrite map_length.
  }
  destruct Hex_tab as [tab Htab].

  rewrite /module_tab_typing in HTabType.
  eapply list_all_forall in HTabType; last by apply Coqlib.nth_error_in in Htab; eauto.

  apply map_nth_error with (f := modtab_type) in Htab.
  rewrite Heqt in Htab.
  inversion Htab. 
  rewrite <- H0 in HTabType. rewrite <- H0.
  clear Htab H0.

  rewrite /limit_typing in HTabType.

  destruct t. simpl in HTabType.
  destruct tt_limits.

  move/andP in HTabType. destruct HTabType as [Hmax Hmin].

  rewrite /typing.tab_agree. simpl.
  split.
  * (* tabcl_agree *)
    apply Forall_forall => lim Hin.
    apply repeat_spec in Hin.
    rewrite /tabcl_agree.
    by rewrite Hin.
  * (* tabsize_agree *)
    rewrite /tabsize_agree. simpl.
    destruct lim_max as [max | ] => //.
    rewrite /tab_size. simpl.
    rewrite repeat_length.
    destruct lim_min as [ | min].
    -- simpl.
       by apply ssrnat.leq0n.
    -- apply/ssrnat.leP.
       move/N.leb_spec0 in Hmin.
       repeat rewrite nat_bin.
       by lias.
Qed.


Lemma mem_agree_from_typing mod_mems s_mems:
  all module_mem_typing mod_mems ->
  s_mems = map (fun '{| lim_min := min; lim_max := maxo |} =>
               {| mem_data := memory_list.mem_make #00 match min with
                                      | 0%N => 0%N
                                      | N.pos q => N.pos (64 * 1024 * q)
                                      end;
                  mem_max_opt := maxo |}) mod_mems ->
  Forall mem_agree s_mems.
Proof.
  move => HMemType Heqs_mems.

  rewrite List.Forall_forall => mi Hin.

  rewrite -> Heqs_mems in Hin.
  eapply List.In_nth_error in Hin.
  destruct Hin as [n Hnth].
  rewrite Coqlib.list_map_nth in Hnth.
  rewrite /Coqlib.option_map in Hnth.
  destruct (nth_error mod_mems n) eqn: Heqm; last by rewrite Heqm in Hnth; inversion Hnth.
    
  rewrite /module_mem_typing in HMemType.
  eapply list_all_forall in HMemType; last by apply Coqlib.nth_error_in in Heqm; eauto.
  rewrite Heqm in Hnth.
  injection Hnth as <-.

  rewrite /limit_typing in HMemType.
  destruct m. simpl in HMemType.

  rewrite /mem_agree. simpl.
  destruct lim_max as [max | ] => //.
  rewrite /mem_size /operations.mem_length /memory_list.mem_length.
  rewrite repeat_length.
  rewrite N2Nat.id.
  rewrite /page_size.
  destruct lim_min as [ | min].
  + rewrite N.div_0_l => //.
    by apply N.le_0_l.
  + remove_bools_options.
    clear - H0.
    replace (N.pos _ / (64 * 1024))%N with (N.pos min); first by apply/N.leb_spec0.
    replace (N.pos _ / (64 * 1024))%N with (N.pos ((64 * 1024) * min) / (64*1024))%N => //.
    rewrite Pos.mul_comm => /=.
    replace (N.pos (min * 65536)) with (N.pos min * 65536)%N => //.
    by rewrite N.div_mul.
Qed.

Definition module_export_entity_relate (R : module_export_desc -> extern_t -> Prop) : Prop :=
  forall vi ti, R vi ti ->
           match vi with
           | MED_func _ => match ti with
                          | ET_func _ => True
                          | _ => False
                          end
           | MED_table _ => match ti with
                           | ET_tab _ => True
                           | _ => False
                           end                             
           | MED_mem _ => match ti with
                         | ET_mem _ => True
                         | _ => False
                         end
           | MED_global _ => match ti with
                            | ET_glob _ => True
                            | _ => False
                            end                            
           end.

Lemma external_typing_relate s :
  module_export_entity_relate (instantiation_spec.external_typing host_function s).
Proof.
  rewrite /module_export_entity_relate => vi ti HR.
  inversion HR => //.
Qed.
  
Lemma vt_imps_funcs_lookup R v_imps t_imps fn ft (k: nat):
  module_export_entity_relate R ->
  Forall2 R v_imps t_imps ->
  (ext_funcs v_imps) !! k = Some fn ->
  (ext_t_funcs t_imps) !! k = Some ft ->
  exists n, v_imps !! n = Some (MED_func fn) /\ t_imps !! n = Some (ET_func ft).
Proof.
  move: t_imps k.
  induction v_imps; move => t_imps k HR HForall2 Hext_vl Hext_tl => //=; first by destruct k.
  inversion HForall2; subst.
  specialize (HR a y H1) as H2.
  destruct a; destruct y; simpl in * => //.
  { destruct k => //.
    + exists 0. simpl in *.      
      inversion Hext_vl; subst.
      by inversion Hext_tl.
    + simpl in *.
      specialize (IHv_imps l' k HR H3 Hext_vl Hext_tl).
      destruct IHv_imps as [n Hvimp].
      by exists (S n).
  }
  all: specialize (IHv_imps l' k HR H3 Hext_vl Hext_tl).
  all: destruct IHv_imps as [n Hvimp].
  all: by exists (S n).
Qed.

Lemma vt_imps_funcs_relate v_imps t_imps fn ft (k: nat) R:
  module_export_entity_relate R ->
  Forall2 R v_imps t_imps ->
  (ext_funcs v_imps) !! k = Some fn ->
  (ext_t_funcs t_imps) !! k = Some ft ->
  R (MED_func fn) (ET_func ft).
Proof.
  move => HR HForall2 Hvl Htl.
  eapply vt_imps_funcs_lookup in Hvl; eauto => //.
  destruct Hvl as [n [Hvl' Htl']].
  eapply Forall2_lookup in HForall2; eauto.
  destruct HForall2 as [y [Htl'' HR']].
  rewrite Htl'' in Htl'; by injection Htl' as ->.
Qed.

Lemma external_typing_funcs_aux s n v_imps v_imp t_imps t_imp:
  Forall2 (instantiation_spec.external_typing host_function s) v_imps t_imps ->
  nth_error (map (fun '(Mk_funcidx i) => i) (ext_funcs v_imps)) n = Some v_imp ->
  nth_error (ext_t_funcs t_imps) n = Some t_imp -> 
  option_map cl_type (nth_error (s_funcs s) v_imp) = Some t_imp. 
Proof.
  move => Htyping Hmvimps_nth Htimps_nth.
  rewrite Coqlib.list_map_nth in Hmvimps_nth.
  rewrite /Coqlib.option_map in Hmvimps_nth.
  destruct (nth_error (ext_funcs v_imps) n) eqn: Hvimps_nth => //.
  destruct f as [fidx]. inversion Hmvimps_nth.
  rewrite <- H0 in *. clear Hmvimps_nth H0.
  specialize (external_typing_relate s) as HR.
  specialize (vt_imps_funcs_relate _ _ _ _ _ _ HR Htyping Hvimps_nth Htimps_nth) as Htyping_n.
  inversion Htyping_n; subst.
  rewrite /option_map.
  by rewrite H3.
Qed.
 *)

(*
Lemma external_typing_globs_aux s n v_imps v_imp t_imps t_imp:
  Forall2 (instantiation_spec.external_typing host_function s) v_imps t_imps ->
  nth_error (map (fun '(Mk_globalidx i) => i) (ext_globs v_imps)) n = Some v_imp ->
  nth_error (ext_t_globs t_imps) n = Some t_imp ->
  option_map (fun g => global_agree g t_imp) (nth_error (s_globals s) v_imp) = Some true. 
Proof.
  move => Htyping Hmvimps_nth Htimps_nth.
  rewrite Coqlib.list_map_nth in Hmvimps_nth.
  rewrite /Coqlib.option_map in Hmvimps_nth.
  destruct (nth_error (ext_globs v_imps) n) eqn: Hvimps_nth => //.
  destruct g as [gidx]. inversion Hmvimps_nth.
  rewrite <- H0 in *. clear Hmvimps_nth H0.
  specialize (external_typing_relate s) as HR.
  specialize (vt_imps_globs_relate _ _ _ _ _ _ HR Htyping Hvimps_nth Htimps_nth) as Htyping_n.
  inversion Htyping_n; subst.
  rewrite /option_map.
  rewrite H3. by rewrite H4.
Qed.

Lemma vt_imps_tabs_lookup v_imps t_imps tn tt (k: nat) R:
  module_export_entity_relate R ->
  Forall2 R v_imps t_imps ->
  (ext_tabs v_imps) !! k = Some tn ->
  (ext_t_tabs t_imps) !! k = Some tt ->
  exists n, v_imps !! n = Some (MED_table tn) /\ t_imps !! n = Some (ET_tab tt).
Proof.
  move: t_imps k.
  induction v_imps; move => t_imps k HR HForall2 Hext_vl Hext_tl => //; first by destruct k.
  inversion HForall2; subst.
  specialize (HR a y H1) as H2.
  destruct a; destruct y; simpl in * => //.
  2 : { destruct k => //.
        + exists 0. simpl in *.      
          inversion Hext_vl; subst.
          by inversion Hext_tl; subst.
        + simpl in *.
          specialize (IHv_imps l' k HR H3 Hext_vl Hext_tl).
          destruct IHv_imps as [n Hvimp].
          by exists (S n).
  }
  all: specialize (IHv_imps l' k HR H3 Hext_vl Hext_tl).
  all: destruct IHv_imps as [n Hvimp].
  all: by exists (S n).
Qed.

Lemma vt_imps_tabs_relate v_imps t_imps tn tt (k: nat) R:
  module_export_entity_relate R ->
  Forall2 R v_imps t_imps ->
  (ext_tabs v_imps) !! k = Some tn ->
  (ext_t_tabs t_imps) !! k = Some tt ->
  R (MED_table tn) (ET_tab tt).
Proof.
  move => HR HForall2 Hvl Htl.
  eapply vt_imps_tabs_lookup in Hvl => //; eauto.
  destruct Hvl as [n [Hvl' Htl']].
  eapply Forall2_lookup in HForall2; eauto.
  destruct HForall2 as [y [Htl'' HR']].
  rewrite Htl'' in Htl'; by injection Htl' as ->.
Qed.

Lemma external_typing_tabs_aux s n v_imps v_imp t_imps t_imp:
  Forall2 (instantiation_spec.external_typing host_function s) v_imps t_imps ->
  nth_error (map (fun '(Mk_tableidx i) => i) (ext_tabs v_imps)) n = Some v_imp ->
  nth_error (ext_t_tabs t_imps) n = Some t_imp ->
  tabi_agree (s_tables s) v_imp t_imp.
Proof.
  move => Htyping Hmvimps_nth Htimps_nth.
  rewrite Coqlib.list_map_nth in Hmvimps_nth.
  rewrite /Coqlib.option_map in Hmvimps_nth.
  destruct (nth_error (ext_tabs v_imps) n) eqn: Hvimps_nth => //.
  destruct t as [tidx]. inversion Hmvimps_nth.
  rewrite <- H0 in *. clear Hmvimps_nth H0.
  specialize (external_typing_relate s) as HR.
  specialize (vt_imps_tabs_relate _ _ _ _ _ _ HR Htyping Hvimps_nth Htimps_nth) as Htyping_n.
  inversion Htyping_n; subst.
  rewrite /option_map.
  rewrite /tabi_agree.
  apply/andP. split => //.
  by rewrite H3.
Qed.

Lemma vt_imps_mems_lookup v_imps t_imps tn tt (k: nat) R:
  module_export_entity_relate R ->
  Forall2 R v_imps t_imps ->
  (ext_mems v_imps) !! k = Some tn ->
  (ext_t_mems t_imps) !! k = Some tt ->
  exists n, v_imps !! n = Some (MED_mem tn) /\ t_imps !! n = Some (ET_mem tt).
Proof.
  move: t_imps k.
  induction v_imps; move => t_imps k HR HForall2 Hext_vl Hext_tl => //=; first by destruct k.
  inversion HForall2; subst.
  specialize (HR a y H1) as H2.
  destruct a; destruct y; simpl in * => //.
  3 : { destruct k => //.
        + exists 0. simpl in *.      
          inversion Hext_vl; subst.
          by inversion Hext_tl; subst.
        + simpl in *.
          specialize (IHv_imps l' k HR H3 Hext_vl Hext_tl).
          destruct IHv_imps as [n Hvimp].
          by exists (S n).
  }
  all: specialize (IHv_imps l' k HR H3 Hext_vl Hext_tl).
  all: destruct IHv_imps as [n Hvimp].
  all: by exists (S n).
Qed.

Lemma vt_imps_mems_relate v_imps t_imps mn mt (k: nat) R:
  module_export_entity_relate R ->
  Forall2 R v_imps t_imps ->
  (ext_mems v_imps) !! k = Some mn ->
  (ext_t_mems t_imps) !! k = Some mt ->
  R (MED_mem mn) (ET_mem mt).
Proof.
  move => HR HForall2 Hvl Htl.
  eapply vt_imps_mems_lookup in Hvl => //; eauto.
  destruct Hvl as [n [Hvl' Htl']].
  eapply Forall2_lookup in HForall2; eauto.
  destruct HForall2 as [y [Htl'' HR']].
  rewrite Htl'' in Htl'; by injection Htl' as ->.
Qed.

Lemma external_typing_mems_aux s n v_imps v_imp t_imps t_imp:
  Forall2 (instantiation_spec.external_typing host_function s) v_imps t_imps ->
  nth_error (map (fun '(Mk_memidx i) => i) (ext_mems v_imps)) n = Some v_imp ->
  nth_error (ext_t_mems t_imps) n = Some t_imp ->
  memi_agree (s_mems s) v_imp t_imp.
Proof.
  move => Htyping Hmvimps_nth Htimps_nth.
  rewrite Coqlib.list_map_nth in Hmvimps_nth.
  rewrite /Coqlib.option_map in Hmvimps_nth.
  destruct (nth_error (ext_mems v_imps) n) eqn: Hvimps_nth => //.
  destruct m as [midx]. inversion Hmvimps_nth.
  rewrite <- H0 in *. clear Hmvimps_nth H0.
  specialize (external_typing_relate s) as HR.
  specialize (vt_imps_mems_relate _ _ _ _ _ _ HR Htyping Hvimps_nth Htimps_nth) as Htyping_n.
  inversion Htyping_n; subst.
  rewrite /memi_agree.
  apply/andP. split => //.
  by rewrite H3.
Qed. 

Lemma Forall_Forall2_l {T1 T2: Type} (l1: list T1) (l2: list T2) (R: T1 -> T2 -> Prop) :
  length l1 = length l2 -> Forall (fun x => forall (y: T2), R x y) l1 -> Forall2 R l1 l2.
Proof.
  move : l2.
  induction l1; destruct l2 => //; move => Hlen Hall; simpl in *.
  constructor.
  - inversion Hall; subst; by apply H1.
  - eapply IHl1; first by lias.
    inversion Hall; subst; assumption.
Qed.
  
Lemma ext_typing_exists_func addr s:
  addr < length s.(s_funcs) ->
  exists t, external_typing s (MED_func (Mk_funcidx addr)) t.
Proof.
  move => Hlen.
  assert (exists f, s.(s_funcs) !! addr = Some f) as Hnth.
  { destruct (s.(s_funcs) !! addr) eqn:Hnth'; try by eexists => //.
    exfalso.
    apply nth_error_Some in Hnth'; by lias. }
  destruct Hnth as [f Hnth].
  eexists.
  econstructor; eauto.
Qed.

Lemma ext_typing_exists_tab addr s:
  addr < length s.(s_tables) ->
  exists t, external_typing s (MED_table (Mk_tableidx addr)) t.
Proof.
  move => Hlen.
  assert (exists tab, s.(s_tables) !! addr = Some tab) as Hnth.
  { destruct (s.(s_tables) !! addr) eqn:Hnth'; try by eexists => //.
    exfalso.
    apply nth_error_Some in Hnth'; by lias. }
  destruct Hnth as [tab Hnth].
  
  (* Note that all tables can be tab_typed. This lemma needs more information if
     this is no longer true in the future. *)
  exists (ET_tab {| tt_limits := {| lim_min := N.of_nat (tab_size tab); lim_max := table_max_opt tab |} ; tt_elem_type := ELT_funcref |}).
  econstructor; eauto.
  unfold tab_typing, limit_match => /=.
  apply/andP; split => //=; first by apply/N.leb_spec0; lias.
  destruct (table_max_opt tab) eqn:Hopt => //.
  by apply/N.leb_spec0; lias.
Qed.

Lemma ext_typing_exists_mem addr s:
  addr < length s.(s_mems) ->
  exists t, external_typing s (MED_mem (Mk_memidx addr)) t.
Proof.
  move => Hlen.
  assert (exists mem, s.(s_mems) !! addr = Some mem) as Hnth.
  { destruct (s.(s_mems) !! addr) eqn:Hnth'; try by eexists => //.
    exfalso.
    apply nth_error_Some in Hnth'; by lias. }
  destruct Hnth as [mem Hnth].
  
  (* Similar to tab_typing *)
  exists (ET_mem {| lim_min := mem_size mem; lim_max := mem_max_opt mem |}).
  econstructor; eauto.
  unfold mem_typing, limit_match => /=.
  apply/andP; split => //=; first by apply/N.leb_spec0; lias.
  destruct (mem_max_opt mem) eqn:Hopt => //.
  by apply/N.leb_spec0; lias.
Qed.

Lemma ext_typing_exists_glob addr s:
  addr < length s.(s_globals) ->
  exists t, external_typing s (MED_global (Mk_globalidx addr)) t.
Proof.
  move => Hlen.
  assert (exists glob, s.(s_globals) !! addr = Some glob) as Hnth.
  { destruct (s.(s_globals) !! addr) eqn:Hnth'; try by eexists => //.
    exfalso.
    apply nth_error_Some in Hnth'; by lias. }
  destruct Hnth as [glob Hnth].
  
  exists (ET_glob {| tg_mut := g_mut glob; tg_t := typeof (g_val glob) |}).
  econstructor; eauto.
  unfold global_agree => /=.
  by apply/andP.
Qed.

Lemma alloc_module_sound s s' m v_imps t_imps v_exps t_exps inst gvs hs: 
  alloc_module host_function s m v_imps gvs (s', inst, v_exps) ->
  module_typing m t_imps t_exps ->
  Forall2 (instantiation_spec.external_typing host_function s) v_imps t_imps -> 
  instantiate_globals host_function host_instance inst hs s' m gvs -> 
  store_typing s ->
  ((store_typing s' /\
   (exists C, inst_typing s' inst C)) /\
   store_extension s s' /\
   List.Forall (fun x => exists t, external_typing s' (modexp_desc x) t) v_exps
  ).  
Proof.
  move => Halloc Hmod_typing Himp_typing Hinit_globs Hstore_typing.
  rewrite /module_typing in Hmod_typing.
  destruct m.
  destruct Hmod_typing as [fts [gts [HFuncType [HTabType [HMemType [HGlobType [HElemType [HDataType [HStartValid [HImpValid HExpValid]]]]]]]]]].

  rewrite /alloc_module in Halloc. simpl in *.
  remember (alloc_funcs host_function s mod_funcs inst) as s_ifs.
  destruct s_ifs as [s1 ifs].
  remember (alloc_tabs host_function s1 (map modtab_type mod_tables)) as s_its.
  destruct s_its as [s2 its].
  remember (alloc_mems host_function s2 mod_mems) as s_ims.
  destruct s_ims as [s3 ims].
  remember (alloc_globs host_function s3 mod_globals gvs) as s_igs.
  destruct s_igs as [s_end igs].

  destruct inst. simpl in *.
  
  repeat (move/andP in Halloc; destruct Halloc as [Halloc ?]).
  move/eqP in H; subst.
  move/eqP in H0; subst.
  move/eqP in H1; subst.
  move/eqP in H2; subst.
  move/eqP in H3; subst.
  move/eqP in H4; subst.
  move/eqP in Halloc; subst.
  
  destruct s_end. destruct s. simpl in *. destruct Hstore_typing as [Hcl [Htab_agree Hmem_agree]].
  specialize (alloc_func_gen_index _ _ _ _ _ _ (Logic.eq_sym Heqs_ifs)) as Hfuncidx.
  destruct Hfuncidx as [Hfunidx [Hfunc1 [Htab1 [Hmem1 Hglob1]]]]; simpl in *.
  specialize (alloc_tab_gen_index _ _ _ _ _ (Logic.eq_sym Heqs_its)) as Htabidx.
  destruct Htabidx as [Htabidx [Htab2 [Hfunc2 [Hmem2 Hglob2]]]]; simpl in *.
  specialize (alloc_mem_gen_index _ _ _ _ _ (Logic.eq_sym Heqs_ims)) as Hmemidx.
  destruct Hmemidx as [Hmemidx [Hmem3 [Hfunc3 [Htab3 Hglob3]]]]; simpl in *.

  assert (Hgvs_len : length gvs = length mod_globals).
  {
    rewrite /instantiate_globals in Hinit_globs.
    simpl in Hinit_globs.
    apply Forall2_length in Hinit_globs.
    by symmetry in Hinit_globs.
  }
  specialize (alloc_glob_gen_index _ _ _ _ _ _ Hgvs_len (Logic.eq_sym Heqs_igs)) as Hglobidx.
  destruct Hglobidx as [Hglobidx [Hglob4 [Hfunc4 [Htab4 Hmem4]]]]; simpl in *.
  
  rewrite <- Hfunc4 in *. rewrite <- Hfunc3 in *. rewrite <- Hfunc2 in *. rewrite -> Hfunc1 in *.
  rewrite <- Htab4 in *. rewrite <- Htab3 in *. rewrite -> Htab2 in *. rewrite <- Htab1 in *.
  rewrite <- Hmem4 in *. rewrite -> Hmem3 in *. rewrite <- Hmem2 in *. rewrite <- Hmem1 in *.
  rewrite -> Hglob4 in *. rewrite <- Hglob3 in *. rewrite <- Hglob2 in *. rewrite <- Hglob1 in *.

  clear Hfunc1 Hfunc2 Hfunc3 Hfunc4.
  clear Htab1 Htab2 Htab3 Htab4.
  clear Hmem1 Hmem2 Hmem3 Hmem4.
  clear Hglob1 Hglob2 Hglob3 Hglob4.
  clear Heqs_ifs Heqs_its Heqs_ims Heqs_igs.

  remember (map (fun mf => gen_func_instance _ mf _) mod_funcs) as s_funcs_new.
  remember (map _ (map _ mod_tables)) as s_tabs_new.
  remember (map (fun '{| lim_min := min; lim_max := maxo |} => _) mod_mems) as s_mems_new.
  remember (map _ (combine mod_globals gvs)) as s_globs_new.
  
  (* We now know the exact new store and instance *)

  remember (Build_t_context mod_types _ _ _ _ nil nil None) as C.
  remember (Build_store_record (s_funcs0 ++ s_funcs_new)%list (s_tables0 ++ s_tabs_new)%list (s_mems0 ++ s_mems_new)%list (s_globals0 ++ s_globs_new)%list) as s_new.
  remember (Build_instance mod_types _ _ _ _) as inst_new.
  assert (inst_typing s_new inst_new C) as HIT.
  {
    destruct C.
    destruct tc_local => //=.
    destruct tc_label => //=.
    destruct tc_return => //=.

    inversion HeqC; subst.

    specialize (external_typing_aux _ _ _ Himp_typing) as Hvimps_len.
    destruct Hvimps_len as [Himps_func_len [Himps_glob_len [Himps_tab_len Himps_mem_len]]].
    
    apply/andP. split.
    apply/andP. split.
    apply/andP. split.
    apply/andP. split => //=.

    -- (* functions_agree *) 
      rewrite /gen_func_instance /typing.functions_agree. simpl.
      eapply all2_and with (g := (fun n0 f => ssrnat.leq (S n0) _)) => //.
      assert (Hifs_len: length (map (fun '(Mk_funcidx i) => i) ifs) = length mod_funcs).
      {
        rewrite <- gen_index_len with (offset := (length s_funcs0)).
        by rewrite Hfunidx.
      }
      specialize (external_typing_aux _ _ _ Himp_typing) as Hvimps_len.
      split.
      ++ (* n < length fs *)
        rewrite - Forall2_all2 List.app_length map_length => /=.
        apply Forall_Forall2_l.
        ** (* v_imps & t_imps *)
          rewrite map_length.
          repeat rewrite -> app_length.
          rewrite Himps_func_len. f_equal.
          replace (length ifs) with (length (map (fun '(Mk_funcidx i) => i) ifs)); last by rewrite map_length.
          rewrite Hifs_len.
          by apply Forall2_length in HFuncType.
        ** rewrite map_app.
           rewrite Forall_app.
           split.
           *** apply Forall_spec.
               move => i n0 Hnth _.             
               rewrite Coqlib.list_map_nth in Hnth.
               destruct (ext_funcs v_imps !! i) eqn: Hvimp => //.
               destruct f.
               simpl in Hnth.
               injection Hnth as <-.
               apply ext_funcs_lookup_exist in Hvimp.
               destruct Hvimp as [k Hvimp].
               eapply Forall2_lookup in Himp_typing; eauto.
               destruct Himp_typing as [y [Htnh Himp_typing]].
               inversion Himp_typing; subst; simpl in *.
               clear - H0.
               apply/ssrnat.ltP. move/ssrnat.ltP in H0.
               by lias.
           *** rewrite Hfunidx.
               apply Forall_spec.
               move => n i H _.
               apply gen_index_in in H.
               by apply/ssrnat.ltP.
      ++ (* cl_type *)
        rewrite <- Forall2_all2.
        rewrite map_app.
        apply Forall2_app.
        ** apply Forall2_spec; first by rewrite map_length.
           move => i j ft Hvimps_nth Htimps_nth.
           apply/eqP. 
           specialize (external_typing_funcs_aux _ _ _ _ _ _ Himp_typing Hvimps_nth Htimps_nth) as Hext_typing. simpl in Hext_typing.
           rewrite <- Hext_typing.
           f_equal.
           apply nth_error_app1.
           rewrite /option_map in Hext_typing.
           destruct (nth_error s_funcs0 j) eqn: Hfuncs_nth => //.
           by eapply nth_error_Some; rewrite Hfuncs_nth.
        ** rewrite /module_func_typing in HFuncType. simpl in HFuncType.
           apply Forall2_spec.
           *** (* length (map (λ '(Mk_funcidx i), i) ifs) = length fts *)
             rewrite Hifs_len.
             by apply Forall2_length in HFuncType.
           *** move => i fidx ft Hidxs_nth Hfts_nth.
               
               specialize (nth_error_same_length_list _ _ _ _ _ _ Hifs_len Hidxs_nth) as Hfuncs_nth.
               destruct Hfuncs_nth as [func Hfuncs_nth].
               specialize (Forall2_nth_error _ _ _ _ _ _ _ _ HFuncType Hfuncs_nth Hfts_nth) as HFuncType_n.
               simpl in HFuncType_n.
               destruct func. destruct modfunc_type. destruct ft as [t1s t2s].
               destruct HFuncType_n as [_ [Hft _]].
               
               rewrite Hfunidx in Hidxs_nth.
               rewrite gen_index_lookup in Hidxs_nth; last by eapply nth_error_Some_length in Hfuncs_nth.
               inversion Hidxs_nth; subst. clear Hidxs_nth.

               rewrite nth_error_app2; last by lias.
               rewrite Nat.add_comm Nat.add_sub.
               rewrite Coqlib.list_map_nth.
               by rewrite Hfuncs_nth.
    -- (* globals_agree *)
      rewrite /globals_agree.
      eapply all2_and with (g := (fun n tg => ssrnat.leq (S n) _)) => //.
      assert (Higs_len: length (map (fun '(Mk_globalidx i) => i) igs) = length mod_globals).
      {
        rewrite <- gen_index_len with (offset := length s_globals0).
        by rewrite Hglobidx.
      }
      assert (Hcombine_len: length (combine mod_globals gvs) = length mod_globals).
      {
        rewrite combine_length.
        rewrite Hgvs_len.
        by lias.
      }
      split.
      ++ (* n < length gs *)
        rewrite <- Forall2_all2.
        rewrite List.app_length map_length.
        apply Forall_Forall2_l.
        ** rewrite map_length.
           repeat rewrite -> app_length.
           rewrite Himps_glob_len. f_equal.
           replace (length igs) with (length (map (fun '(Mk_globalidx i) => i) igs)); last by rewrite map_length.
           rewrite Higs_len.
           by apply Forall2_length in HGlobType.
        ** rewrite map_app.
           rewrite Forall_app.
           split.
           *** apply Forall_spec.
               move => i n0 Hnth _.
               
               rewrite Coqlib.list_map_nth in Hnth.
               destruct (ext_globs v_imps !! i) eqn: Hvimp => //.
               simpl in Hnth.
               apply ext_globs_lookup_exist in Hvimp.
               destruct Hvimp as [k Hvimp].

               eapply Forall2_lookup in Himp_typing; last by apply Hvimp.
               destruct Himp_typing as [y [Hkth Himp_typing]].
               inversion Himp_typing; subst.
               injection Hnth as ->.
               clear - H0; simpl in H0.
               apply/ssrnat.ltP. move/ssrnat.ltP in H0.
               by lias.
           *** rewrite Hglobidx.
               apply Forall_spec.
               move => i x H _.
               apply gen_index_in in H.
               rewrite Hcombine_len.
               by apply/ssrnat.ltP.
      ++ (* global_agree *) 
        rewrite <- Forall2_all2 => /=.
        rewrite map_app.
        apply Forall2_app.
        ** apply Forall2_spec; first by rewrite map_length.
           move => i j ? Hvimps_nth Htimps_nth.
           apply/eqP.
           specialize (external_typing_globs_aux _ _ _ _ _ _ Himp_typing Hvimps_nth Htimps_nth) as Hext_typing. simpl in Hext_typing.
           rewrite <- Hext_typing.
           f_equal.
           apply nth_error_app1.
           rewrite /option_map in Hext_typing.
           destruct (nth_error s_globals0 j) eqn: Hglobs_nth => //.
           by eapply nth_error_Some_length in Hglobs_nth.
        ** rewrite /module_glob_typing in HGlobType. simpl in HGlobType.
           apply Forall2_spec.
           *** (* length (map (λ '(Mk_globalidx i), i) igs) = length gts *)
             rewrite Higs_len.
             by apply Forall2_length in HGlobType.
           *** move => i gidx gt Hidxs_nth Hgts_nth.

               specialize (nth_error_same_length_list _ _ _ _ _ _ Higs_len Hidxs_nth) as Hglobs_nth.
               destruct Hglobs_nth as [glob Hglobs_nth].
               specialize (Forall2_nth_error _ _ _ _ _ _ _ _ HGlobType Hglobs_nth Hgts_nth) as HGlobType_n.
               simpl in HGlobType_n.
               destruct glob.
               destruct HGlobType_n as [_ [Hgt _]]. subst.

               rewrite Hglobidx in Hidxs_nth.
               rewrite gen_index_lookup in Hidxs_nth; last by eapply nth_error_Some_length in Hglobs_nth.
               inversion Hidxs_nth; subst. clear Hidxs_nth.

               rewrite nth_error_app2; last by lias.
               rewrite Nat.add_comm Nat.add_sub.
               rewrite Coqlib.list_map_nth.

               specialize (nth_error_same_length_list _ _ _ _ _ _ (Logic.eq_sym Hgvs_len) Hglobs_nth) as Hgvs_nth.
               destruct Hgvs_nth as [gv Hgvs_nth].
               assert (Hcombine : (combine mod_globals gvs) !! i = Some ({| modglob_type := modglob_type; modglob_init := modglob_init |}, gv)).
               {
                 rewrite -> nth_error_nth' with (d := ({| modglob_type := modglob_type; modglob_init := modglob_init |}, gv)); last by rewrite Hcombine_len; eapply nth_error_Some_length in Hglobs_nth.
                 rewrite combine_nth => //.
                 by repeat erewrite nth_error_nth => //. 
               }
               rewrite Hcombine. simpl.
               rewrite /global_agree. simpl.
               apply/eqP. f_equal.
               apply/andP. split => //.
               apply/eqP.
               
               rewrite /instantiate_globals in Hinit_globs. simpl in Hinit_globs.
               eapply Forall2_lookup in Hinit_globs; last by apply Hglobs_nth.
               destruct Hinit_globs as [y [Hith Hred]].
               rewrite Hith in Hgvs_nth; injection Hgvs_nth as ->.
               
               eapply Forall2_lookup in HGlobType; last by apply Hglobs_nth.
               destruct HGlobType as [y [Hnth [Hconst [-> Hbet]]]].

               specialize (const_exprs_impl _ _ _ Hconst Hbet) as Hexprs.
               clear Hconst.
               destruct Hexprs as [expr [-> Hconst]]; remove_bools_options.
               rewrite /const_expr in Hconst. simpl in Hconst.
               destruct expr; simpl in * => //.
               { (* modglob_init = [BI_get_global i0] *)

                 (* [BI_get_global i0] ->* gv *)
                 apply reduce_trans_get_global in Hred.
                 rewrite /sglob_val /sglob /sglob_ind in Hred.
                 simpl in Hred.
                 rewrite /option_map in Hred.
                 destruct (option_bind _ _) eqn: Heq1 => //.
                 injection Hred as <-.
                 rewrite /option_bind in Heq1.
                 destruct (nth_error (map _ _) i0) eqn: Heq2 => //.

                 (* [BI_get_global i0] has type modglob_type *)
                 eapply Get_global_typing in Hbet => //; eauto.
                 simpl in Hbet.
                 destruct Hbet as [ty [Hextlookup [H1 _]]].
                 injection H1 as <-.
                 rewrite /option_map in Hextlookup.
                 destruct (nth_error (ext_t_globs t_imps) i0) eqn: Htl => //.

                 rewrite Coqlib.list_map_nth in Heq2.
                 assert (Heq3: (ext_globs v_imps ++ igs) !! i0 = ext_globs v_imps !! i0).
                 { apply nth_error_Some_length in Htl.
                   rewrite <- Himps_glob_len in Htl.
                   eapply nth_error_app1 with (l' := igs) in Htl.
                   by repeat rewrite nth_error_lookup in Htl.
                 }
                 rewrite Heq3 in Heq2.
                 rewrite <- Coqlib.list_map_nth in Heq2.
                 eapply external_typing_globs_aux in Himp_typing; simpl in Himp_typing; eauto.
                 rewrite/option_map in Himp_typing.
                 remove_bools_options; subst.
                 rewrite nth_error_app1 in Heq1; last by apply nth_error_Some_length in Hoption.
                 rewrite Hoption in Heq1. injection Heq1 as ->.
                 unfold global_agree in H3.
                 remove_bools_options.
                 assumption.
               }
               { (* modglob_init = [BI_const v] *)
                 apply reduce_trans_const in Hred. subst.
                 apply BI_const_typing in Hbet.
                 simpl in Hbet. by inversion Hbet.
               }
    -- (* tabi_agree *) 
      rewrite <- Forall2_all2 => /=.
      rewrite map_app.
      apply Forall2_app.
      ** apply Forall2_spec; first by rewrite map_length.
         move => i j ? Hvimps_nth Htimps_nth.
         specialize (external_typing_tabs_aux _ _ _ _ _ _ Himp_typing Hvimps_nth Htimps_nth) as Hext_typing. simpl in Hext_typing.
         by eapply tabi_agree_aux.
      ** assert (Hits_len: length (map (fun '(Mk_tableidx i) => i) its) = length mod_tables).
         {
           rewrite <- gen_index_len with (offset := length s_tables0).
           rewrite Htabidx.
           by rewrite map_length.
         }
         apply Forall2_spec.
         *** rewrite Hits_len.
             by rewrite map_length.
         *** move => i tidx tt Hidxs_nth Htts_nth.

             rewrite Htabidx in Hidxs_nth.
             rewrite gen_index_lookup in Hidxs_nth; last by eapply nth_error_Some_length in Htts_nth.
             inversion Hidxs_nth; subst. clear Hidxs_nth.
             
             rewrite /tabi_agree.
             apply/andP. split.

             {
               apply /ssrnat.ltP.
               rewrite app_length map_length map_length.
               apply nth_error_Some_length in Htts_nth.
               rewrite map_length in Htts_nth.
               by lias.
             }
             {
               rewrite nth_error_app2; last by lias.
               rewrite Nat.add_comm Nat.add_sub.
               rewrite Coqlib.list_map_nth.
               rewrite Htts_nth.
               
               destruct tt. destruct tt_limits. simpl.
               rewrite /tab_typing. simpl.
               apply/andP. split => /=.
               - rewrite /tab_size. simpl. 
                 rewrite repeat_length.
                 apply/N.leb_spec0.
                 by rewrite nat_bin N2Nat.id; lias.
               - destruct lim_max => //.
                 by apply/N.leb_spec0; lias.
             }
    -- (* memi_agree *)
      rewrite <- Forall2_all2 => /=.
      rewrite map_app.
      assert (Hims_len: length (map (fun '(Mk_memidx i) => i) ims) = length mod_mems).
      {
        rewrite <- gen_index_len with (offset := length s_mems0).
        by rewrite Hmemidx.
      }
      apply Forall2_app.
      ** apply Forall2_spec; first by rewrite map_length.
         move => i j ? Hvimps_nth Htimps_nth.
         specialize (external_typing_mems_aux _ _ _ _ _ _ Himp_typing Hvimps_nth Htimps_nth) as Hext_typing. simpl in Hext_typing.
         by eapply memi_agree_aux.            
      ** rewrite /module_mem_typing in HMemType.
         apply Forall2_spec; first by rewrite Hims_len.
         move => i midx mt Hidxs_nth Hmts_nth.

         rewrite Hmemidx in Hidxs_nth.
         rewrite gen_index_lookup in Hidxs_nth; last by eapply nth_error_Some_length in Hmts_nth.
         inversion Hidxs_nth; subst. clear Hidxs_nth.

         rewrite /memi_agree.
         apply/andP. split.

         {
           apply /ssrnat.ltP.
           rewrite app_length map_length.
           apply nth_error_Some_length in Hmts_nth.
           (* unification doesn't go through trivially *)
           remember (length mod_mems) as n.
           rewrite - Heqn.
           by lias.
         }
         {
           rewrite nth_error_app2; last by lias.
           rewrite Nat.add_comm Nat.add_sub.
           rewrite Coqlib.list_map_nth.
           rewrite Hmts_nth.

           destruct mt. 
           rewrite /mem_typing. simpl.
           apply/andP. split => //=; last by destruct lim_max => //; apply/N.leb_spec0; lias.
           rewrite /mem_size /operations.mem_length /memory_list.mem_length. simpl.
           destruct lim_min => //.
           rewrite /page_size. simpl.
           rewrite repeat_length.
           rewrite Znat.positive_nat_N.
           
           assert (Hdiv: N.div (N.pos ((64 * 1024) * p)) (N.pos (64 * 1024)) = N.pos p).
           {
             replace (N.pos (64 * 1024 * p)) with (N.mul (N.pos (64 * 1024)) (N.pos p)); last by simpl.
             rewrite N.mul_comm.
             by apply N.div_mul => //.
           }
           rewrite Hdiv.
           by rewrite N.leb_refl.
         }
  }
  repeat split.
  4: {
    exists C; destruct C; inversion HeqC; subst.
    by apply HIT.
  }

  (* store_typing and inst_typing *)
  - (* cl_type *)
    rewrite -> List.Forall_app.
    split.
    + (* forall cl_type_check s' s_funcs0 *)
      apply List.Forall_forall => fc Hin.
      subst.
      apply cl_type_check_single_aux.
      rewrite -> List.Forall_forall in Hcl.
      by apply Hcl.
    + (* forall cl_type_check s' s_funcs_new *)
      rewrite List.Forall_forall => fc Hin.

      rewrite -> Heqs_funcs_new in Hin.
      rewrite /gen_func_instance in Hin.
      simpl in Hin.
      eapply List.In_nth_error in Hin.
      destruct Hin as [n Hnth].
      rewrite Coqlib.list_map_nth in Hnth.
      rewrite /Coqlib.option_map in Hnth.
      destruct (nth_error mod_funcs n) eqn: Heqm => //=.
      inversion Hnth. clear Hnth.
      rename H0 into Heq_fc. 

      assert (Hex_ty: exists ty, List.nth_error fts n = Some ty).
      {
        apply Forall2_length in HFuncType.
        apply nth_error_Some_length in Heqm.
        rewrite HFuncType in Heqm.
        apply nth_error_Some in Heqm.
        by destruct (fts !! n) => //; eexists.
      }
      
      specialize (external_typing_aux _ _ _ Himp_typing) as Hvimps_len.
      destruct Hvimps_len as [Himps_func_len [Himps_glob_len [Himps_tab_len Himps_mem_len]]].

      destruct Hex_ty as [ty Hty].
      specialize (Forall2_nth_error _ _ _ _ _ n m ty HFuncType Heqm Hty) as HFuncType_n.

      rewrite /typing.cl_type_check_single.
      destruct ty as [t1s t2s].
      exists (Tf t1s t2s).

      eapply cl_typing_native with (C := C) => //=.
      * (* the type index of function m references type (Tf t1s t2s) in mod_types *)
        rewrite /module_func_typing in HFuncType_n.
        destruct m. simpl.
        destruct modfunc_type as [i].
        destruct HFuncType_n as [_ [Hnth _]].
        move/eqP in Hnth.
        rewrite <- Hnth.
        by subst => /=.
      * (* be_typing *)
        rewrite /module_func_typing in HFuncType_n.
        rewrite /upd_local_label_return.
        destruct m. simpl.
        destruct modfunc_type.
        destruct HFuncType_n as [_ [_ Hbe_typing]].
        by apply Hbe_typing. 
  - (* tab_agree *)
    rewrite Forall_app.
    split.
    + (* forall tab_agree s' s_tables0 *)
      apply Forall_forall => ti Hin.
      subst s_new.
      rewrite -> Forall_forall in Htab_agree.
      apply tab_agree_aux.
      by apply Htab_agree.
    + (* forall tab_agree s' s_tabs_new *)
      by eapply tab_agree_from_typing; eauto.
  - (* mem_agree *)
    rewrite Forall_app.
    split.
    + (* forall mem_agree s_mems0 *)
      by exact Hmem_agree.
    + (* forall mem_agree s_mems_new *)
      by eapply mem_agree_from_typing; eauto.
  - (* store_extension *)
    subst s_new.
    unfold store_extension => /=.
    apply/andP; split; last by clear; eapply comp_extension_extend; eauto; apply all2_glob_extension_same.
    apply/andP; split; last by clear; eapply comp_extension_extend; eauto; apply all2_mem_extension_same.
    apply/andP; split; last by clear; eapply comp_extension_extend; eauto; apply all2_tab_extension_same.
    clear; eapply comp_extension_extend; eauto; apply all2_func_extension_same.
  - (* export typing *) 
    apply Forall_forall.
    move => vexp Hin.
    apply In_nth_error in Hin as [n Hnth].
    rewrite nth_error_map in Hnth.
    destruct (mod_exports !! n) as [mexp | ] eqn:Hnthexp => //.
    simpl in Hnth; injection Hnth as <- => /=.
    
    eapply Forall2_lookup with (i := n) in HExpValid; eauto.
    destruct HExpValid as [extt [Hnthtexp Hexptype]].
    destruct mexp as [mname mdesc].
    unfold module_export_typing in Hexptype.
    
    unfold export_get_v_ext => /=.
    destruct mdesc as [o | o | o | o]; destruct o as [i]; destruct extt => //; simpl in *.
  - apply ext_typing_exists_func.
    assert (i < length (inst_funcs inst_new)) as Hlen.
    {
      unfold inst_typing in HIT; destruct inst_new, C.
      remove_bools_options; simpl in *.
      repeat rewrite length_is_size.
      destruct tc_local, tc_label, tc_return => //.
      remove_bools_options.
      replace (size inst_funcs) with (size tc_func_t) => //.
      symmetry. by eapply all2_size; eauto.
    }
    assert (exists a, (inst_funcs inst_new) !! i = Some a) as [a Hnth].
    {
      destruct ((inst_funcs inst_new) !! i) eqn:Hnth; try by eexists.
      exfalso.
      by apply nth_error_Some in Hnth; lias.
    }
    erewrite nth_error_nth; last by apply Hnth.
    eapply inst_typing_func in Hnth as [cl Hnthcl]; eauto.
    by apply nth_error_Some_length in Hnthcl; lias.
  - apply ext_typing_exists_tab.
    assert (i < length (inst_tab inst_new)) as Hlen.
    {
      unfold inst_typing in HIT; destruct inst_new, C.
      remove_bools_options; simpl in *.
      repeat rewrite length_is_size.
      destruct tc_local, tc_label, tc_return => //.
      remove_bools_options.
      replace (size inst_tab) with (size tc_table) => //.
      symmetry. by eapply all2_size; eauto.
    }
    assert (exists a, (inst_tab inst_new) !! i = Some a) as [a Hnth].
    {
      destruct ((inst_tab inst_new) !! i) eqn:Hnth; try by eexists.
      exfalso.
      by apply nth_error_Some in Hnth; lias.
    }
    erewrite nth_error_nth; last by apply Hnth.
    by eapply inst_typing_tab; eauto.
  - apply ext_typing_exists_mem.
    assert (i < length (inst_memory inst_new)) as Hlen.
    {
      unfold inst_typing in HIT; destruct inst_new, C.
      remove_bools_options; simpl in *.
      repeat rewrite length_is_size.
      destruct tc_local, tc_label, tc_return => //.
      remove_bools_options.
      replace (size inst_memory) with (size tc_memory) => //.
      symmetry. by eapply all2_size; eauto.
    }
    assert (exists a, (inst_memory inst_new) !! i = Some a) as [a Hnth].
    {
      destruct ((inst_memory inst_new) !! i) eqn:Hnth; try by eexists.
      exfalso.
      by apply nth_error_Some in Hnth; lias.
    }
    erewrite nth_error_nth; last by apply Hnth.
    by eapply inst_typing_mem; eauto.
  - apply ext_typing_exists_glob.
    assert (i < length (inst_globs inst_new)) as Hlen.
    {
      unfold inst_typing in HIT; destruct inst_new, C.
      remove_bools_options; simpl in *.
      repeat rewrite length_is_size.
      destruct tc_local, tc_label, tc_return => //.
      remove_bools_options.
      replace (size inst_globs) with (size tc_global) => //.
      symmetry. by eapply all2_size; eauto.
    }
    assert (exists a, (inst_globs inst_new) !! i = Some a) as [a Hnth].
    {
      destruct ((inst_globs inst_new) !! i) eqn:Hnth; try by eexists.
      exfalso.
      by apply nth_error_Some in Hnth; lias.
    }
    erewrite nth_error_nth; last by apply Hnth.
    by eapply inst_typing_glob; eauto.
Qed.

Lemma init_tab_preserve ws inst e_inits melem ws':
  init_tab host_function ws inst e_inits melem = ws' ->
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  move => Hinit.
  rewrite /init_tab in Hinit.
  destruct ws'.
  destruct (nth _ _) eqn: Hl => /=.
  inversion Hinit; repeat split => //.
Qed.

Lemma init_tabs_preserve ws inst e_inits melem ws':
  init_tabs host_function ws inst e_inits melem = ws' ->
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  move => Hinit.
  unfold init_tabs in Hinit.
  rewrite - Hinit.
  apply fold_left_preserve => //.
  move => x [n me] Heq.
  destruct ws, x.
  simpl in *.
  destruct Heq as [-> [-> ->]].
  unfold init_tab => /=.
  by destruct (nth _ _) eqn:Hl => /=.
Qed.

Lemma comp_extension_same_length {T: Type} (l1 l2: list T) f:
  all2 f l1 l2 ->
  comp_extension l1 l2 f.
Proof.
  move => Hall2.
  assert (length l1 = length l2) as Hlen; first by apply all2_size in Hall2; repeat rewrite length_is_size.
  unfold comp_extension; apply/andP; split => //.
  - by lias.
  - by rewrite Hlen length_is_size take_size.
Qed.

Lemma Forall2_set_2 {T1 T2: Type} (l1: list T1) (l2: list T2) f x y n:
  Forall2 f l1 l2 ->
  nth_error l1 n = Some x ->
  f x y ->
  Forall2 f l1 (set_nth y l2 n y).
Proof.
  move: l2 x y n.
  induction l1; move => l2 x y n Hall2 Hnth Hf; destruct l2, n => //=; (try by apply Forall2_length in Hall2); simpl in *.
  - injection Hnth as ->.
    constructor => //.
    by inversion Hall2.
  - inversion Hall2; subst; clear Hall2.
    constructor => //.
    by eapply IHl1; eauto.
Qed.

Lemma Forall_set {T: Type} (l: list T) n x P:
  n < length l ->
  Forall P l -> P x -> Forall P (set_nth x l n x).
Proof.
  move : n x.
  induction l; move => n x Hlen Hall HP; destruct n => //=; try constructor; inversion Hall => //.
  subst.
  by apply IHl => //.
Qed.

Lemma Forall_firstn {T: Type} (l: list T) n P:
  Forall P l ->
  Forall P (firstn n l).
Proof.
  move : n. induction l; destruct n; move => Hall => //=.
  constructor; first by inversion Hall.
  by apply IHl; inversion Hall.
Qed.

Lemma Forall_skipn {T: Type} (l: list T) n P:
  Forall P l ->
  Forall P (skipn n l).
Proof.
  move : n. induction l; destruct n; move => Hall => //=.
  by apply IHl; inversion Hall.
Qed.

Lemma init_tab_extension s inst mod_elem e_off s':
  store_typing s ->
  Forall (fun n => n < length (s_funcs s)) (inst_funcs inst) ->
  (fun s => all (fun '(Mk_funcidx i) => ssrnat.leq (S i) (length (inst_funcs inst))) s) (modelem_init mod_elem) -> 
  match nth_error (inst_tab inst) match modelem_table mod_elem with
                                  | Mk_tableidx i => i
                                  end with
  | Some i =>
      match nth_error (s_tables s) i with
      | Some ti => (N_of_int e_off + N.of_nat (length (modelem_init mod_elem)) <=? N.of_nat (length (table_data ti)))%N
      | None => false
      end
  | None => false
  end ->
  s' = (init_tab host_function s inst (Z.to_nat (Wasm_int.Int32.intval e_off)) mod_elem) ->
  all2 tab_extension s.(s_tables) s'.(s_tables).
Proof.
  move => Htyping Hinst_typing Hinit_typing Hbound ->.
  
  rewrite /init_tab.
  destruct mod_elem. simpl in *.
  destruct modelem_table.
  destruct (nth_error (inst_tab inst) n) as [taddr | ] eqn: Htaddr => //.
  destruct (nth_error (s_tables s) taddr) as [tinst | ] eqn: Htinst => //.

  rewrite -> nth_error_nth with (x := taddr) => //.
  erewrite -> nth_error_nth => //; eauto.

  destruct tinst. simpl in Hbound.

  rewrite /store_typing /typing.store_typing in Htyping.
  destruct s. simpl in *.
  destruct Htyping as [Hcl_type [Htab_agree Hmem_agree]].
  assert (Hle: taddr < length s_tables). { apply nth_error_Some_length in Htinst; lias. }
  apply Forall2_all2.
  eapply Forall2_set_2; [ by apply Forall2_all2, all2_tab_extension_same | eauto | ].
  unfold tab_extension, tab_size => /=.
  apply/andP; split => //.
  
  repeat rewrite app_length.
  rewrite firstn_length map_length skipn_length.

  by lias.
Qed.

Lemma init_tab_typing s inst mod_elem e_off s':
  store_typing s ->
  Forall (fun n => n < length (s_funcs s)) (inst_funcs inst) ->
  (fun s => all (fun '(Mk_funcidx i) => ssrnat.leq (S i) (length (inst_funcs inst))) s) (modelem_init mod_elem) -> 
  match nth_error (inst_tab inst) match modelem_table mod_elem with
                                  | Mk_tableidx i => i
                                  end with
  | Some i =>
      match nth_error (s_tables s) i with
      | Some ti => (N_of_int e_off + N.of_nat (length (modelem_init mod_elem)) <=? N.of_nat (length (table_data ti)))%N
      | None => false
      end
  | None => false
  end ->
  s' = (init_tab host_function s inst (Z.to_nat (Wasm_int.Int32.intval e_off)) mod_elem) ->
  store_typing s'.
Proof.
  move => Htyping Hinst_typing Hinit_typing Hbound Heqs'.
  
  specialize (init_tab_preserve _ _ _ _ _ (Logic.eq_sym Heqs')) as [Heqf [Heqm Heqg]].
  specialize (init_tab_extension _ _ _ _ _ Htyping Hinst_typing Hinit_typing Hbound Heqs') as Htext.
  assert (store_extension s s') as Hext.
  { unfold store_extension.
    apply/andP; split; last by rewrite Heqg; apply comp_extension_same_refl; unfold ssrbool.reflexive; apply glob_extension_refl.
    apply/andP; split; last by rewrite Heqm; apply comp_extension_same_refl; unfold ssrbool.reflexive; apply mem_extension_refl.
    apply/andP; split; first by rewrite Heqf; apply comp_extension_same_refl; unfold ssrbool.reflexive; apply func_extension_refl.
    apply comp_extension_same_length.
    by eapply init_tab_extension; eauto.
  }
  
  unfold store_typing, typing.store_typing in *.
  destruct s, s'. simpl in *.
  destruct Htyping as [Hcl_type [Htab_agree Hmem_agree]].
  repeat split; last by subst s_mems0.
  - unfold typing.cl_type_check_single in *.
    apply Forall_forall.
    rewrite -> Forall_forall in Hcl_type.
    move => x Hin.
    subst s_funcs0.
    apply Hcl_type in Hin as [tf Htype].
    exists tf.
    unfold init_tab in Hext; simpl in Hext.
    by eapply store_extension_cl_typing; eauto.
  - (* tab_agree *)
    clear Hcl_type Hmem_agree.
    unfold init_tab in Heqs'; simpl in Heqs'.
    destruct mod_elem, modelem_table; simpl in *.
    destruct (nth_error (inst_tab inst) _) as [taddr | ] eqn:Hinstlookup => //.
    destruct (nth_error s_tables taddr) as [tab | ] eqn:Hstablookup => //.
    rewrite -> nth_error_nth with (x := taddr) in Heqs' => //.
    rewrite -> nth_error_nth with (x := tab) in Heqs' => //.

    destruct tab => /=.
    subst s_funcs0 s_mems0 s_globals0.
    assert (Hlt: taddr < length s_tables). { by apply nth_error_Some_length in Hstablookup; lias. }

    inversion Heqs'; subst s_tables0; clear Heqs'.
    apply Forall_set => //.
    eapply Forall_lookup in Htab_agree; last by apply Hstablookup.
    destruct Htab_agree as [Htabcl_agree Htabsize_agree].
    
    split => /=.
    + apply Forall_app; split; first by apply Forall_firstn.
      apply Forall_app; split; last by apply Forall_skipn.
      
      (* Forall tabcl_agree (the new table) *)
      rewrite /tabcl_agree. simpl.
      apply Forall_spec => i addr Haddr.
      rewrite Coqlib.list_map_nth in Haddr.
      destruct (modelem_init !! i) eqn: Hinit_nth => //.
      destruct f as [fidx]. simpl in Haddr.
      inversion Haddr; subst. clear Haddr.
      destruct (nth_error (inst_funcs inst) fidx) eqn: Hinst_nth => //.
      eapply Forall_lookup in Hinst_typing; by eauto => //.
    + (* tabsize_agree *)
      rewrite /tabsize_agree /tab_size.
      simpl in *.

      rewrite /tabsize_agree /tab_size in Htabsize_agree.
      simpl in Htabsize_agree.
      destruct table_max_opt => //.
      
      repeat rewrite app_length.
      rewrite firstn_length map_length skipn_length.

      rewrite /N_of_int in Hbound.
      move/N.leb_spec0 in Hbound.
      by lias.
Qed.
  
Lemma init_tabs_sound s s' inst m x:
  store_typing s ->
  Forall (fun n => n < length (s_funcs s)) (inst_funcs inst) ->
  Forall
    (fun s => all (fun '(Mk_funcidx i) => ssrnat.leq (S i) (length (inst_funcs inst))) s)
    (map modelem_init (mod_elem m)) ->
  check_bounds_elem host_function inst s m x ->
  s' = (init_tabs host_function s inst [seq Z.to_nat (Wasm_int.Int32.intval o) | o <- x] (mod_elem m)) ->
  (comp_extension s.(s_tables) s'.(s_tables) tab_extension /\
  store_typing s').
Proof.
  rewrite /check_bounds_elem. destruct m. simpl.
  clear mod_types mod_funcs mod_tables mod_mems mod_globals mod_data mod_start mod_imports mod_exports.
  move: s s' x.
  induction mod_elem as [ | mod_elem mod_elems];
  move => s s' e_offs Htyping Hinsts_typing Hinits_typing Hbounds Heqs;
  rewrite <- Forall2_all2 in Hbounds.
  - inversion Hbounds; subst.
    unfold init_tabs => /=.
    split => //.
    apply comp_extension_same_refl.
    unfold ssrbool.reflexive.
    by apply tab_extension_refl.
  - inversion Hbounds; subst.
    rename x into e_off. rename l into e_offs.

    simpl in Hinits_typing. inversion Hinits_typing; subst.
    rename H1 into Hinit_typing. rename H4 into Hinits_typing'.
    
    rewrite /init_tabs. simpl.
    remember (init_tab host_function s inst (Z.to_nat (Wasm_int.Int32.intval e_off)) mod_elem) as s1 eqn:Heqs1.
    
    (* tab extension *)
    assert (comp_extension (s_tables s) (s_tables s1) tab_extension) as Hext.
    { apply comp_extension_same_length. by eapply init_tab_extension; eauto. }

    assert (store_typing s1) as Hstoretype.
    { by eapply init_tab_typing; eauto. }
    
    eapply IHmod_elems with (s := s1) (x := e_offs) in Hstoretype as [Hext' Hstype']; eauto.

    + split => //; last by eapply comp_extension_trans; [ by eauto | | by apply tab_extension_trans].
    
    (* recover invariant *)
    + (* Forall (λ n : nat, n < length (s_funcs s1)) (inst_funcs inst) *)
      symmetry in Heqs1.
      apply init_tab_preserve in Heqs1.
      destruct Heqs1 as [Heqfuncs _].
      by rewrite <- Heqfuncs.
    + (* check_bounds *)
      rewrite <- Forall2_all2.
      apply Forall2_spec; first by eapply Forall2_length in H3.
      
      move => i e_off1 mod_elem1 Hoffs_nth Helems_nth.
    
      eapply Forall2_lookup with (i := i) in H3 as [? [Hnth Hlookup]]; eauto.
      rewrite Helems_nth in Hnth.
      injection Hnth as <-.
      
      destruct mod_elem1, modelem_table. simpl in *.

      destruct (nth_error (inst_tab inst) n) as [taddr0 | ] eqn: Haddr0 => //.
      destruct (nth_error (s_tables s) taddr0) as [tinst0 | ] eqn: Hinst0 => //.

      subst s1.
    
      rewrite /init_tab.
      destruct mod_elem. simpl in *.
      destruct modelem_table.
      
      destruct (nth_error (inst_tab inst) n0) as [taddr1 | ] eqn: Haddr1 => //.
      destruct (nth_error (s_tables s) taddr1) as [tinst1 | ] eqn: Hinst1 => //.

      erewrite -> nth_error_nth; last (erewrite nth_error_nth; last eauto); last eauto.
      erewrite -> nth_error_nth; last eauto.

      destruct tinst1. simpl in *.
      assert (Hlen: taddr1 < length (s_tables s)).
      { by eapply nth_error_Some_length in Hinst1; lias. }
      destruct (taddr0 == taddr1) eqn:Haddreq; move/eqP in Haddreq.
      * (* taddr0 = taddr1 *)
        subst taddr0.
        rewrite nth_error_set_eq => //.
        rewrite Hinst0 in Hinst1.
        injection Hinst1 as ->.

        repeat rewrite app_length.
        rewrite firstn_length map_length skipn_length.

        move/N.leb_spec0 in H2.
        rewrite /N_of_int in H2.

        move/N.leb_spec0 in Hlookup.
        rewrite /N_of_int in Hlookup.
        simpl in *.

        replace (Init.Nat.min (Z.to_nat (Wasm_int.Int32.intval e_off)) (length table_data)) with (Z.to_nat (Wasm_int.Int32.intval e_off)); last by lias.

        apply/N.leb_spec0.

        rewrite Nat.add_assoc.
        replace (Nat.add (Z.to_nat (Wasm_int.Int32.intval e_off)) (length modelem_init0)) with (Z.to_nat (Wasm_int.Int32.intval e_off) + length modelem_init0); last by lias.
        
        rewrite Nat.add_comm Nat.sub_add => //.
        by lias.
      * (* taddr0 /= taddr1 *)
        rewrite nth_error_set_neq => //; last lias.
        by rewrite Hinst0.
Qed.

Lemma init_mem_preserve ws inst d_inits mdata ws':
  init_mem host_function ws inst d_inits mdata = ws' ->
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  move => Hinit.
  rewrite /init_mem in Hinit.
  destruct ws'.
  destruct (nth _ _) eqn: Hl => /=.
  inversion Hinit; repeat split => //.
Qed.

Lemma init_mems_preserve ws inst d_inits mdata ws':
  init_mems host_function ws inst d_inits mdata = ws' ->
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  move => Hinit.
  unfold init_mems in Hinit.
  rewrite - Hinit.
  apply fold_left_preserve => //.
  move => x [n md] Heq.
  destruct ws, x.
  simpl in *.
  destruct Heq as [-> [-> ->]].
  by unfold init_mem => /=.
Qed.

Lemma init_mem_extension s inst mod_data d_off s':
  store_typing s ->
  match nth_error (inst_memory inst) match moddata_data mod_data with
                                  | Mk_memidx i => i
                                  end with
  | Some i =>
      match nth_error (s_mems s) i with
      | Some mem => (N_of_int d_off + N.of_nat (length (moddata_init mod_data)) <=? mem_length mem)%N
      | None => false
      end
  | None => false
  end ->
  s' = init_mem host_function s inst (Z.to_N (Wasm_int.Int32.intval d_off)) mod_data ->
  all2 mem_extension s.(s_mems) s'.(s_mems).
Proof.
  move => Htyping Hbound ->.
  
  rewrite /init_mem.
  destruct mod_data. simpl in *.
  destruct moddata_data.
  destruct (nth_error (inst_memory inst)) as [maddr | ] eqn: Hmaddr => //.
  destruct (nth_error (s_mems s) maddr) as [minst | ] eqn: Hinst => //.

  rewrite -> nth_error_nth with (x := maddr) => //.
  erewrite -> nth_error_nth; eauto => //.

  destruct minst. simpl.

  rewrite /store_typing /typing.store_typing in Htyping.
  destruct s. simpl in *.
  destruct Htyping as [Hcl_type [Htab_agree Hmem_agree]].

  assert (Hle: maddr < length s_mems).
  { by eapply nth_error_Some_length in Hinst; lias. }
  
  apply Forall2_all2.
  eapply Forall2_set_2; [ by apply Forall2_all2, all2_mem_extension_same | eauto | ].
  
  rewrite /mem_extension /mem_size /operations.mem_length /memory_list.mem_length.
  apply/andP; split => //.
  simpl.

  repeat rewrite app_length.
  rewrite firstn_length map_length skipn_length.

  (* using Hbound *)
  rewrite /mem_length /memory_list.mem_length in Hbound.
  simpl in Hbound.

  move/N.leb_spec0 in Hbound.
  replace (Init.Nat.min (ssrnat.nat_of_bin (Z.to_N (Wasm_int.Int32.intval d_off))) (length (memory_list.ml_data mem_data))) with (ssrnat.nat_of_bin (Z.to_N (Wasm_int.Int32.intval d_off))).
  2 : { rewrite /N_of_int in Hbound.
        repeat rewrite nat_bin.
        by lias. }
  apply/N.leb_spec0.
  apply N.eq_le_incl. repeat f_equal.
  rewrite /N_of_int in Hbound. 
  rewrite nat_bin.
  by lias.
Qed.

Lemma init_mem_typing s inst mod_data d_off s':
  store_typing s ->
  match nth_error (inst_memory inst) match moddata_data mod_data with
                                  | Mk_memidx i => i
                                  end with
  | Some i =>
      match nth_error (s_mems s) i with
      | Some mem => (N_of_int d_off + N.of_nat (length (moddata_init mod_data)) <=? mem_length mem)%N
      | None => false
      end
  | None => false
  end ->
  s' = init_mem host_function s inst (Z.to_N (Wasm_int.Int32.intval d_off)) mod_data ->
  store_typing s'.
Proof.
  move => Htyping Hbound Heqs'.
  
  specialize (init_mem_preserve _ _ _ _ _ (Logic.eq_sym Heqs')) as [Heqf [Heqt Heqg]].
  specialize (init_mem_extension _ _ _ _ _ Htyping Hbound Heqs') as Htext.
  assert (store_extension s s') as Hext.
  { unfold store_extension.
    apply/andP; split; last by rewrite Heqg; apply comp_extension_same_refl; unfold ssrbool.reflexive; apply glob_extension_refl.
    apply/andP; split; last by apply comp_extension_same_length; eapply init_mem_extension; eauto.
    apply/andP; split; last by rewrite Heqt; apply comp_extension_same_refl; unfold ssrbool.reflexive; apply tab_extension_refl.
    by rewrite Heqf; apply comp_extension_same_refl; unfold ssrbool.reflexive; apply func_extension_refl.
  }
  
  unfold store_typing, typing.store_typing in *.
  destruct s, s'. simpl in *.
  destruct Htyping as [Hcl_type [Htab_agree Hmem_agree]].
  repeat split.
  - unfold typing.cl_type_check_single in *.
    apply Forall_forall.
    rewrite -> Forall_forall in Hcl_type.
    move => x Hin.
    subst s_funcs0.
    apply Hcl_type in Hin as [tf Htype].
    exists tf.
    unfold init_mem in Hext; simpl in Hext.
    by eapply store_extension_cl_typing; eauto.
  - by subst.
  - (* mem_agree *)
    clear Hcl_type Htab_agree.
    destruct mod_data, moddata_data; simpl in *.
    destruct (nth_error (inst_memory inst) n) as [maddr | ] eqn:Hmaddr => //=.
    destruct (nth_error s_mems maddr) as [mem | ] eqn:Hsmlookup => //=.

    unfold init_mem in Heqs'; simpl in Heqs'.
    subst s_funcs0 s_tables0 s_globals0.
    inversion Heqs'; subst s_mems0; clear Heqs'.

    rewrite -> nth_error_nth with (x := maddr) => //.
    apply Forall_set => //; first by apply nth_error_Some_length in Hsmlookup; lias.

    rewrite /mem_agree in Hmem_agree.
    rewrite -> Forall_nth in Hmem_agree.
    rewrite /mem_agree => /=.
    rewrite -> nth_error_nth with (x := mem) => //=.
    clear - Hbound Hmem_agree Hsmlookup.

    specialize (Hmem_agree maddr mem).

    erewrite nth_error_nth in Hmem_agree; last eauto.

    assert (maddr < length s_mems)%coq_nat as Hlen; first by apply nth_error_Some_length in Hsmlookup.

    specialize (Hmem_agree Hlen).

    destruct mem, mem_max_opt => //=.
    simpl in *.
    
    rewrite /mem_size /operations.mem_length /memory_list.mem_length. simpl.
    rewrite /mem_size /operations.mem_length /memory_list.mem_length in Hsmlookup.
    simpl in Hsmlookup.

    repeat rewrite app_length.
    rewrite firstn_length map_length skipn_length.

    rewrite /mem_length /memory_list.mem_length in Hbound.
    simpl in Hbound.

    move/N.leb_spec0 in Hbound.
    rewrite /N_of_int in Hbound.

    rewrite nat_bin.

    replace (Init.Nat.min (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off))) (length (memory_list.ml_data mem_data))) with (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off))); last by lias.
    
    rewrite Nat.add_assoc.
    replace (ssrnat.addn (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off))) (length moddata_init)) with (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off)) + length moddata_init); last by lias.
    
    rewrite Nat.add_comm Nat.sub_add => //; last by lias.
Qed.

Lemma init_mems_sound s s' inst m x:
  store_typing s ->
  check_bounds_data host_function inst s m x ->
  s' = (init_mems host_function s inst [seq Z.to_N (Wasm_int.Int32.intval o) | o <- x] (mod_data m)) ->
  (comp_extension s.(s_mems) s'.(s_mems) mem_extension /\
  store_typing s').
Proof.
  rewrite /check_bounds_data. destruct m. simpl.
  clear mod_types mod_funcs mod_tables mod_mems mod_globals mod_elem mod_start mod_imports mod_exports. 
  move: s s' x.
  induction mod_data as [ | mod_data mod_datas]; move => s s' d_offs Htyping Hbounds Heqs;
  rewrite <- Forall2_all2 in Hbounds.
  - inversion Hbounds; subst.
    simpl.
    rewrite /init_mems.
    split => //=.
    apply comp_extension_same_refl; unfold ssrbool.reflexive; by apply mem_extension_refl.
  - inversion Hbounds; subst.
    rename x into d_off. rename l into d_offs.
    rewrite /init_mems. simpl.
    (* d_off & mod_data represent the altered mem segment during s -> s1 *)
    remember (init_mem host_function s inst (Z.to_N (Wasm_int.Int32.intval d_off)) mod_data) as s1 eqn: Heqs1.

    (* mem extension *)
    assert (comp_extension (s_mems s) (s_mems s1) mem_extension) as Hext.
    { apply comp_extension_same_length. by eapply init_mem_extension; eauto. }

    assert (store_typing s1) as Hstoretype.
    { by eapply init_mem_typing; eauto. }
    
    eapply IHmod_datas with (s := s1) (x := d_offs) in Hstoretype as [Hext' Hstype']; eauto.

    + split => //; last by eapply comp_extension_trans; [ by eauto | | by apply mem_extension_trans].
    
    (* recover invariant - check_bound *)
    clear Htyping Hbounds.
    rewrite <- Forall2_all2.
    apply Forall2_spec; first by eapply Forall2_length; eauto.
    move => i d_off1 mod_data1 Hoffs_nth Helems_nth.

    eapply Forall2_lookup in H3; last eauto.
    destruct H3 as [data [Hnth Hinstmem]].
    rewrite Helems_nth in Hnth.
    injection Hnth as <-.

    destruct mod_data1. simpl in *.
    destruct moddata_data.

    destruct (nth_error (inst_memory inst) n) as [maddr1 | ] eqn: Haddr1 => //.
    destruct (nth_error (s_mems s) maddr1) as [minst1 | ] eqn: Hinst1 => //.

    destruct mod_data. simpl in *.
    destruct moddata_data.

    destruct (nth_error (inst_memory inst) n0) as [maddr | ] eqn: Haddr => //.
    destruct (nth_error (s_mems s) maddr) as [minst | ] eqn: Hminst => //.

    subst s1.

    rewrite/init_mem /=.
    
    rewrite -> nth_error_nth with (x := maddr) => //.
    erewrite nth_error_nth; eauto => //.

    destruct minst. simpl.

    assert (Hlen : maddr < length (s_mems s)).
    { by eapply nth_error_Some_length in Hminst; lias. }
    destruct (maddr == maddr1) eqn:Heqaddr; move/eqP in Heqaddr.
    * (* maddr = maddr1 *)
      subst maddr1.
      rewrite nth_error_set_eq => //.
      rewrite /instantiation_spec.mem_length /memory_list.mem_length /=.

      (* from addr = addr1, we could know that minst1 = minst0 (has been destructed) *)
      rewrite Hinst1 in Hminst.
      inversion Hminst; subst. clear Hminst.
      rewrite /instantiation_spec.mem_length /memory_list.mem_length in Hinstmem.
      simpl in Hinstmem.

      rewrite /instantiation_spec.mem_length /memory_list.mem_length in H2.
      simpl in H2.
        
      repeat rewrite app_length.
      rewrite firstn_length map_length skipn_length.

      move/N.leb_spec0 in Hinstmem.
      rewrite /N_of_int in Hinstmem.
        
      move/N.leb_spec0 in H2.
      rewrite /N_of_int in H2.
        
      apply/N.leb_spec0.
        
      rewrite nat_bin.

      replace (Init.Nat.min (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off))) (length (memory_list.ml_data mem_data))) with (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off))); last by lias.

      rewrite Nat.add_assoc.
      replace (ssrnat.addn (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off))) (length moddata_init0)) with (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off)) + length moddata_init0); last by lias.
      rewrite Nat.add_comm Nat.sub_add => //. 
      by lias.
    * (* maddr /= maddr1 *)
      rewrite nth_error_set_neq; eauto.
      by rewrite Hinst1.
Qed.

Lemma elem_typing_proj_is m t_imps t_exps:
  module_typing m t_imps t_exps ->
  Forall
    (all (fun '(Mk_funcidx i) => ssrnat.leq (S i) (length (ext_t_funcs t_imps) + length (mod_funcs m))))
    (map modelem_init (mod_elem m)). 
Proof.
  move => [fts [gts H]].
  destruct m. simpl in *.
  destruct H as [HFuncTyping [_ [_ [_ [HElemTyping _]]]]].
  apply Forall2_length in HFuncTyping.
  rewrite HFuncTyping.
  
  rewrite /module_elem_typing in HElemTyping.
  simpl in HElemTyping.
  apply Forall_spec => i fidx Hinit_nth.
  
  rewrite Coqlib.list_map_nth in Hinit_nth.
  destruct (mod_elem !! i) eqn: Helem_nth => //.
  
  eapply Forall_lookup in HElemTyping; eauto => //.
  destruct m, modelem_table.
  simpl in Hinit_nth.
  inversion Hinit_nth; subst. clear Hinit_nth.
  destruct HElemTyping as [_ [_ [_ H]]].
  by rewrite app_length in H.
Qed.


Lemma init_tabs_preserve_typing_aux s s' m v_imps t_imps v_exps t_exps inst gvs hs: 
  alloc_module host_function s m v_imps gvs (s', inst, v_exps) ->
  module_typing m t_imps t_exps ->
  Forall2 (instantiation_spec.external_typing host_function s) v_imps t_imps -> 
  instantiate_globals host_function host_instance inst hs s' m gvs ->
  store_typing s -> 
  length (inst_funcs inst) = length (ext_t_funcs t_imps) + length (mod_funcs m) /\
    Forall (fun n => n < length (s_funcs s')) (inst_funcs inst).
Proof.
  move => Halloc Hmod_typing Himp_typing Hinit_globs Hstore_typing.
  rewrite /module_typing in Hmod_typing.
  destruct m.
  destruct Hmod_typing as [fts [gts [HFuncType [HTabType [HMemType [HGlobType [HElemType [HDataType [HStartValid [HImpValid HExpValid]]]]]]]]]].

  rewrite /alloc_module in Halloc. simpl in *.
  remember (alloc_funcs host_function s mod_funcs inst) as s_ifs.
  destruct s_ifs as [s1 ifs].
  remember (alloc_tabs host_function s1 (map modtab_type mod_tables)) as s_its.
  destruct s_its as [s2 its].
  remember (alloc_mems host_function s2 mod_mems) as s_ims.
  destruct s_ims as [s3 ims].
  remember (alloc_globs host_function s3 mod_globals gvs) as s_igs.
  destruct s_igs as [s_end igs].

  destruct inst. simpl in *.
  
  repeat (move/andP in Halloc; destruct Halloc as [Halloc ?]).
  move/eqP in H; subst.
  move/eqP in H0; subst.
  move/eqP in H1; subst.
  move/eqP in H2; subst.
  move/eqP in H3; subst.
  move/eqP in H4; subst.
  move/eqP in Halloc; subst.
  
  destruct s_end. destruct s. simpl in *. destruct Hstore_typing as [Hcl [Htab_agree Hmem_agree]].
  specialize (alloc_func_gen_index _ _ _ _ _ _ (Logic.eq_sym Heqs_ifs)) as Hfuncidx.
  destruct Hfuncidx as [Hfunidx [Hfunc1 [Htab1 [Hmem1 Hglob1]]]]; simpl in *.
  specialize (alloc_tab_gen_index _ _ _ _ _ (Logic.eq_sym Heqs_its)) as Htabidx.
  destruct Htabidx as [Htabidx [Htab2 [Hfunc2 [Hmem2 Hglob2]]]]; simpl in *.
  specialize (alloc_mem_gen_index _ _ _ _ _ (Logic.eq_sym Heqs_ims)) as Hmemidx.
  destruct Hmemidx as [Hmemidx [Hmem3 [Hfunc3 [Htab3 Hglob3]]]]; simpl in *.

  assert (Hgvs_len : length gvs = length mod_globals).
  {
    rewrite /instantiate_globals in Hinit_globs.
    simpl in Hinit_globs.
    apply Forall2_length in Hinit_globs.
    by symmetry in Hinit_globs.
  }
  specialize (alloc_glob_gen_index _ _ _ _ _ _ Hgvs_len (Logic.eq_sym Heqs_igs)) as Hglobidx.
  destruct Hglobidx as [Hglobidx [Hglob4 [Hfunc4 [Htab4 Hmem4]]]]; simpl in *.
  
  rewrite <- Hfunc4 in *. rewrite <- Hfunc3 in *. rewrite <- Hfunc2 in *. rewrite -> Hfunc1 in *.
  rewrite <- Htab4 in *. rewrite <- Htab3 in *. rewrite -> Htab2 in *. rewrite <- Htab1 in *.
  rewrite <- Hmem4 in *. rewrite -> Hmem3 in *. rewrite <- Hmem2 in *. rewrite <- Hmem1 in *.
  rewrite -> Hglob4 in *. rewrite <- Hglob3 in *. rewrite <- Hglob2 in *. rewrite <- Hglob1 in *.

  clear Hfunc1 Hfunc2 Hfunc3 Hfunc4.
  clear Htab1 Htab2 Htab3 Htab4.
  clear Hmem1 Hmem2 Hmem3 Hmem4.
  clear Hglob1 Hglob2 Hglob3 Hglob4.
  clear Heqs_ifs Heqs_its Heqs_ims Heqs_igs.

  remember (map (fun mf => gen_func_instance _ mf _) mod_funcs) as s_funcs_new.
  remember (map _ (map _ mod_tables)) as s_tabs_new.
  remember (map (fun '{| lim_min := min; lim_max := maxo |} => _) mod_mems) as s_mems_new.
  remember (map _ (combine mod_globals gvs)) as s_globs_new.
  
  split.
  - rewrite map_length app_length.
    eapply external_typing_aux in Himp_typing.
    destruct Himp_typing as [Hext_funcs_len _].
    rewrite <- gen_index_len with (offset := (length s_funcs0)) (len := length mod_funcs).
    rewrite <- Hfunidx.
    rewrite map_length.
    by lias.
  - rewrite map_app Forall_app.
    split.
    + apply Forall_spec => i n0 Hnth => //.
      rewrite Coqlib.list_map_nth in Hnth.
      destruct (ext_funcs v_imps !! i) eqn: Hvimp => //.
      simpl in Hnth.
      apply ext_funcs_lookup_exist in Hvimp.
      destruct Hvimp as [k Hvimp].
      eapply Forall2_lookup in Himp_typing; last eassumption.
      destruct Himp_typing as [extt [Hntht Hexttype]].
      destruct f. injection Hnth as <-.
      inversion Hexttype; subst; clear Hexttype.
      simpl in *.
      apply nth_error_Some_length in H1.
      rewrite app_length.
      by lias.
    + rewrite Hfunidx.
      rewrite Heqs_funcs_new.
      rewrite app_length map_length.
      apply Forall_spec => i x H.
      apply gen_index_in in H.
      by lias.
Qed.

Lemma alloc_module_extract_export s m v_imps g_inits s' inst v_exps:
  alloc_module s m v_imps g_inits (s', inst, v_exps) ->
  v_exps = map (fun m_exp => {| modexp_name := modexp_name m_exp; modexp_desc := export_get_v_ext inst (modexp_desc m_exp) |}) (mod_exports m).
Proof.
  move => Halloc.
  simpl in *.
  destruct (alloc_funcs _ _ _ _) as [s1 i_fs].
  destruct (alloc_tabs _ _ _) as [s2 i_ts].
  destruct (alloc_mems _ _ _) as [s3 i_ms].
  destruct (alloc_globs _ _ _) as [s4 i_gs].
  by remove_bools_options.
Qed.

Lemma store_extension_export_typing s s' v_exp t_exp:
  store_extension s s' ->
  external_typing s v_exp t_exp ->
  external_typing s' v_exp t_exp.
Proof.
  move => Hext Hexttype.
  unfold external_typing in Hexttype.
  destruct v_exp, t_exp; inversion Hexttype; simpl in *; subst.
  - eapply store_extension_lookup_func in Hext; eauto.
    econstructor; (try eassumption) => //.
    apply nth_error_Some_length in Hext.
    by lias.
  - eapply store_extension_lookup_tab in Hext; eauto.
    destruct Hext as [y [Hnth Hext]].
    econstructor; (try eassumption); first by apply nth_error_Some_length in Hnth; lias.
    by eapply tab_typing_extension; eauto.
  - eapply store_extension_lookup_mem in Hext; eauto.
    destruct Hext as [y [Hnth Hext]].
    econstructor; (try eassumption); first by apply nth_error_Some_length in Hnth; lias.
    by eapply mem_typing_extension; eauto.
  - eapply store_extension_lookup_glob in Hext; eauto.
    destruct Hext as [y [Hnth Hext]].
    econstructor; (try eassumption); last by eapply global_agree_extension; eauto.
    apply nth_error_Some_length in Hnth.
    by lias.
Qed.
 *)

Lemma nth_error_map' {T1 T2: Type}: forall (f: T1 -> T2) (l: list T1) n,
    List.nth_error (map f l) n = option_map f (List.nth_error l n).
Proof.
  by induction l; destruct n => //=.
Qed.

Lemma vt_imps_globs_lookup s v_imps t_imps gn gt (k: nat):
  List.Forall2 (external_typing s) v_imps t_imps ->
  List.nth_error (ext_globs v_imps) k = Some gn ->
  List.nth_error (ext_t_globs t_imps) k = Some gt ->
  exists n, v_imps !! n = Some (EV_global gn) /\ t_imps !! n = Some (ET_global gt).
Proof.
  move: t_imps k gn gt.
  induction v_imps; destruct t_imps; move => k; try by destruct k eqn:Hk => //=.
  move => gn gt Hall2 Hv Ht.
  unfold ssrfun.Option.apply in *.
  inversion Hall2; subst; clear Hall2.
  unfold external_typing, ext_typing in H2.
  destruct a, e => //; (try by simpl in H2); remove_bools_options; simpl ext_globs in Hv; simpl ext_t_globs in Ht.
  4 : {
    destruct k; first by exists 0; inversion Hv; inversion Ht; subst.
    simpl in *.
    eapply IHv_imps in H4 as [n [Hnthv Hntht]]; eauto.
    by exists (S n).
  }
  all: eapply IHv_imps in H4 as [n [Hnthv Hntht]]; eauto; by exists (S n).
Qed.

Lemma import_subtyping_globs_impl': forall t_imps_mod t_imps i gt,
    List.Forall2 import_subtyping t_imps t_imps_mod ->
    List.nth_error (ext_t_globs t_imps_mod) i = Some gt ->
    exists gt', List.nth_error (ext_t_globs t_imps) i = Some gt' /\ global_subtyping gt' gt.
Proof.
  induction t_imps_mod; destruct t_imps => //; (try by destruct i); first by move => ?? Hcontra; inversion Hcontra.
  move => i gt Hall2 Hnth.
  inversion Hall2; subst; clear Hall2.
  unfold import_subtyping in H2.
  destruct a, e => //; (try by simpl in H2); remove_bools_options; subst; simpl in *.
  4: { destruct i; simpl in * => //.
       - exists g0; by inversion Hnth; subst.
       - by eapply IHt_imps_mod => //.
  }
  all: by eapply IHt_imps_mod; eauto.
Qed.            

Lemma vt_imps_globs_typing s v_imps t_imps gn gt (k: nat):
  List.Forall2 (external_typing s) v_imps t_imps ->
  (ext_globs v_imps) !! k = Some gn ->
  (ext_t_globs t_imps) !! k = Some gt ->
  external_typing s (EV_global gn) (ET_global gt).
Proof.
  move => HForall2 Hvl Htl.
  eapply vt_imps_globs_lookup in Hvl => //; eauto.
  destruct Hvl as [n [Hvl' Htl']].
  eapply Forall2_lookup in HForall2; eauto.
  destruct HForall2 as [y [Htl'' HR']].
  by simplify_multieq.
Qed.

Lemma instantiation_sound: forall (s: store_record) m v_imps s' f exps,
  store_typing s ->
  instantiate s m v_imps (s', f, exps) ->
  (store_typing s') /\
  (store_extension s s') /\
  (exists C, frame_typing s' f C).
Proof.
  move => s m v_imps s' f exps HST Hinst.
  unfold instantiate in Hinst.
  destruct Hinst as [t_imps_mod [t_imps [t_exps [hs' [inst [g_inits [r_inits [Hmodtype [Himptype [Hsubtype [Hallocmodule [Hinstglob [Hinstelem [Heqf Heqexps]]]]]]]]]]]]]].

  unfold alloc_module in Hallocmodule.
  destruct (alloc_funcs _ _ _) as [s1 ifs] eqn:Hallocfuncs.
  destruct (alloc_tabs _ _) as [s2 its] eqn:Halloctabs.
  destruct (alloc_mems _ _) as [s3 ims] eqn:Hallocmems.
  destruct (alloc_globs _ _) as [s4 igs] eqn:Hallocglobs.
  destruct (alloc_elems _ _) as [s5 ies] eqn:Hallocelems.
  destruct (alloc_datas _ _) as [s6 ids] eqn:Hallocdatas.

  remove_bools_options.

  apply alloc_func_gen_addrs in Hallocfuncs.
  apply alloc_table_gen_addrs in Halloctabs.
  apply alloc_mem_gen_addrs in Hallocmems.
  apply alloc_global_gen_addrs in Hallocglobs; last by apply List.Forall2_length in Hinstglob.
  apply alloc_elem_gen_addrs in Hallocelems; last by apply List.Forall2_length in Hinstelem.
  apply alloc_data_gen_addrs in Hallocdatas.

  (* Important to prove the goals first separately as there is some sort of dependency *)
  assert (store_extension s s') as Hstoreext.
  { 
    extract_premise.
    destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
    unfold store_extension => /=.
    erewrite component_extension_extend; eauto; last by apply all2_func_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_table_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_mem_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_global_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_elem_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_data_extension_same.
  }

  destruct m; unfold module_typing in Hmodtype; simpl in *.
  destruct Hmodtype as [fts [tts [mts [gts [rts [dts [Hmtypes [Hmfunctype [Hmtabletype [Hmmemtype [Hmglobaltype [Hmelemtype [Hmdatatype [Hstarttype [Hmimptype [Hmexptype Hexpunique]]]]]]]]]]]]]]]].

  remember (Build_t_context mod_types (ext_t_funcs t_imps_mod ++ fts) (ext_t_tabs t_imps_mod ++ tts) (ext_t_mems t_imps_mod ++ mts) (ext_t_globs t_imps_mod ++ gts) rts dts nil nil None nil) as C.

  assert (inst_typing s' f.(f_inst) = Some C) as HIT.
  {
    extract_premise.
    destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
    destruct inst; subst; simpl in *.
    replace (all functype_valid inst_types) with true; last by symmetry; apply Forall_all.
    resolve_if_true_eq.
    (* Functions *)
    {
      apply those_exists.
      move => n oft Hnth.
      rewrite List.nth_error_map in Hnth.
      remove_bools_options.
      apply cat_lookup in Hoption.
      destruct Hoption as [Hnth | Hnth].
      - (* Imports *)
        apply ext_funcs_lookup_exist in Hnth as [k Hnth].
        eapply Forall2_lookup in Himptype as [t [Hntht Hexttype]]; eauto.
        unfold external_typing, ext_typing in Hexttype.
        remove_bools_options.
        by eapply ext_func_typing_extension in Hoption; eauto.
      - (* New *)
        unfold ext_func_typing => /=.
        resolve_if_true_eq; last by eexists.
        apply nth_error_exists.
        rewrite gen_addrs_gen_index in Hnth.
        apply nth_error_map in Hnth as [k [Hnth Hmap]].
        apply gen_index_lookup_Some in Hnth as [??]; subst.
        rewrite Nat2N.id List.app_length List.map_length.
        by lias.
    }
    resolve_if_true_eq.
    (* Tables *)
    {
      apply those_exists.
      move => n oft Hnth.
      rewrite List.nth_error_map in Hnth.
      remove_bools_options.
      apply cat_lookup in Hoption.
      destruct Hoption as [Hnth | Hnth].
      - (* Imports *)
        apply ext_tabs_lookup_exist in Hnth as [k Hnth].
        eapply Forall2_lookup in Himptype as [t' [Hntht Hexttype]]; eauto.
        unfold external_typing, ext_typing in Hexttype.
        remove_bools_options.
        by eapply ext_table_typing_extension in Hoption as [? [??]]; eauto.
      - (* New *)
        unfold ext_table_typing => /=.
        resolve_if_true_eq; last by eexists.
        apply nth_error_exists.
        rewrite gen_addrs_gen_index in Hnth.
        apply nth_error_map in Hnth as [k [Hnth Hmap]].
        apply gen_index_lookup_Some in Hnth as [??]; subst.
        rewrite Nat2N.id List.app_length List.map_length.
        by lias.
    }
    resolve_if_true_eq.
    (* Memories *)
    {
      apply those_exists.
      move => n oft Hnth.
      rewrite List.nth_error_map in Hnth.
      remove_bools_options.
      apply cat_lookup in Hoption.
      destruct Hoption as [Hnth | Hnth].
      - (* Imports *)
        apply ext_mems_lookup_exist in Hnth as [k Hnth].
        eapply Forall2_lookup in Himptype as [t' [Hntht Hexttype]]; eauto.
        unfold external_typing, ext_typing in Hexttype.
        remove_bools_options.
        by eapply ext_mem_typing_extension in Hoption as [? [??]]; eauto.
      - (* New *)
        unfold ext_mem_typing => /=.
        rewrite List.map_length in Hnth.
        resolve_if_true_eq; last by eexists.
        apply nth_error_exists.
        rewrite gen_addrs_gen_index in Hnth.
        apply nth_error_map in Hnth as [k [Hnth Hmap]].
        apply gen_index_lookup_Some in Hnth as [??]; subst.
        rewrite Nat2N.id List.app_length; repeat rewrite List.map_length.
        by lias.
    }
    resolve_if_true_eq.
    (* Globals *)
    {
      apply those_exists.
      move => n oft Hnth.
      rewrite List.nth_error_map in Hnth.
      remove_bools_options.
      apply cat_lookup in Hoption.
      destruct Hoption as [Hnth | Hnth].
      - (* Imports *)
        apply ext_globs_lookup_exist in Hnth as [k Hnth].
        eapply Forall2_lookup in Himptype as [t' [Hntht Hexttype]]; eauto.
        unfold external_typing, ext_typing in Hexttype.
        remove_bools_options.
        by eapply ext_global_typing_extension in Hoption; eauto.
      - (* New *)
        unfold ext_global_typing => /=.
        resolve_if_true_eq; last by eexists.
        apply nth_error_exists.
        rewrite gen_addrs_gen_index in Hnth.
        apply nth_error_map in Hnth as [k [Hnth Hmap]].
        apply gen_index_lookup_Some in Hnth as [??]; subst.
        rewrite Nat2N.id List.app_length List.map_length List.combine_length.
        apply List.Forall2_length in Hinstglob; simpl in Hinstglob; rewrite Hinstglob.
        by lias.
    }
    resolve_if_true_eq.
    (* Elements *)
    {
      apply those_exists.
      move => n oft Hnth.
      rewrite List.nth_error_map in Hnth.
      remove_bools_options.
      rewrite gen_addrs_gen_index in Hoption.
      apply nth_error_map in Hoption as [k [Hnth Hmap]].
      apply gen_index_lookup_Some in Hnth as [??]; subst.
      (* New *)
      resolve_if_true_eq.
      - apply nth_error_exists.
        rewrite Nat2N.id List.app_length List.map_length List.combine_length.
        apply List.Forall2_length in Hinstelem; simpl in Hinstelem; rewrite Hinstelem.
        by lias.
      - destruct y0; unfold eleminst_typing => /=.
        resolve_if_true_eq; last by eexists.
        apply Forall_all, Forall_spec.
        move => m vref Hnth.
        apply cat_lookup2 in Hsome3; last by lias.
        apply nth_error_map in Hsome3 as [[elem vrefs] [Hnthcombine Heq]].
        injection Heq as <- ->.
        rewrite Nat2N.id in Hnthcombine.
        replace ((_ + _)%coq_nat - _) with n in Hnthcombine; last by lias.
        apply combine_lookup in Hnthcombine as [Hnthelem Hnthinit].
        eapply Forall2_lookup in Hinstelem as [vref' [Hnthinit' Hmap]] => /=; last by apply Hnthelem.
        simplify_multieq.
        eapply Forall2_nth_impl' in Hmap as [bes [Hnth' Hreduce]]; eauto.
        eapply Forall2_nth_impl in Hmelemtype as [et [Hnthet Helemtype]]; last by apply Hnthelem.
        destruct elem; unfold module_elem_typing in Helemtype.
        destruct Helemtype as [-> [Hall Hvalidmode]].
        eapply Forall_lookup in Hall as [Hconst Hbet]; last by apply Hnth'.
        eapply const_exprs_impl in Hconst as [be [-> Hconst]]; last by apply Hbet.
        destruct be => //=.
        (* VAL_num *)
        { replace (to_e_list [::BI_const_num v]) with ([::$V (VAL_num v)]) in Hreduce; last done.
          by apply reduce_trans_value in Hreduce.
        }
        (* VAL_vec *)
        { replace (to_e_list [::BI_const_vec v]) with ([::$V (VAL_vec v)]) in Hreduce; last done.
          by apply reduce_trans_value in Hreduce.
        }
        (* ref_null *)
        { replace (to_e_list [::BI_ref_null r]) with ([::$V (VAL_ref (VAL_ref_null r))]) in Hreduce; last done.
          apply reduce_trans_value in Hreduce.
          injection Hreduce as <-.
          unfold value_typing => /=.
          invert_be_typing.
          apply instr_subtyping_empty1_impl' in Htisub; simpl in *.
          by resolve_subtyping.
        }
        (* ref_func *)
        { apply reduce_trans_ref_func in Hreduce as [addr [Hnthaddr ->]].
          unfold value_typing; simpl in *.
          unfold ext_func_typing => /=.
          invert_be_typing.
          apply instr_subtyping_empty1_impl' in Htisub; simpl in *; remove_bools_options.
          apply cat_lookup in Hnthaddr.
          destruct Hnthaddr as [Hnthaddr | Hnthaddr].
          - apply ext_funcs_lookup_exist in Hnthaddr as [k Hnthaddr].
            eapply Forall2_nth_impl in Himptype as [et [Hnthext Hext]]; last by apply Hnthaddr.
            unfold external_typing, ext_typing, ext_func_typing in Hext; simpl in Hext.
            remove_bools_options.
            unfold lookup_N in *.
            by erewrite nth_error_app_Some; eauto.
          - rewrite gen_addrs_gen_index in Hnthaddr.
            apply nth_error_map in Hnthaddr as [k [Hnthindex <-]].
            apply gen_index_lookup_Some in Hnthindex as [-> Hlength].
            unfold lookup_N.
            rewrite List.nth_error_app2; last by lias.
            rewrite Nat2N.id nth_error_map'.
            replace (_ + _ - _) with (N.to_nat f - length (ext_funcs v_imps)); last by lias.
            move/ltP in Hlength.
            apply nth_error_exists in Hlength as [mf Hnthmf].
            by rewrite Hnthmf.
        }
        (* global_get *)
        { apply reduce_trans_global_get in Hreduce.
          unfold sglob_val, sglob, sglob_ind in Hreduce.
          simpl in *; remove_bools_options.
          invert_be_typing.
          apply instr_subtyping_empty1_impl' in Htisub; simpl in *; remove_bools_options.
          simplify_multieq.
          eapply import_subtyping_globs_impl' in Hsubtype as [gt' [Hnthsub Hsub]]; eauto.
          unfold global_subtyping in Hsub; remove_bools_options; subst.
          eapply vt_imps_globs_typing in Hoption0; eauto.
          simpl in Hoption0.
          unfold external_typing, ext_typing, ext_global_typing in Hoption0.
          simpl in Hoption0; remove_bools_options.
          unfold lookup_N in *.
          rewrite List.nth_error_app1 in Hoption; last by apply nth_error_Some_length in Hoption0.
          simplify_multieq.
          eapply Forall_lookup in Hconjl4 as [gt Hgtype]; eauto.
          destruct g0; unfold globalinst_typing in Hgtype.
          remove_bools_options; simpl in *.
          eapply value_typing_extension; eauto.
          by eapply value_typing_trans; eauto.
        }
    }
    resolve_if_true_eq.
    (* data *)
    {
      apply those_exists.
      move => n xok Hnth.
      apply nth_error_map in Hnth as [v [Hnth Hmap]].
      rewrite - Hmap.
      resolve_if_true_eq.
      { apply nth_error_exists.
        rewrite List.app_length List.map_length.
        subst.
        rewrite gen_addrs_gen_index in Hnth.
        apply nth_error_map in Hnth as [k [Hnthindex <-]].
        apply gen_index_lookup_Some in Hnthindex as [-> Hlength].
        by lias.
      }
      { unfold datainst_typing.
        by exists tt.
      }
    }
    subst.
    admit.
  }

  assert (store_typing s') as HST'.
  {
    extract_premise.
    destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
    destruct HST as [Hsfunctype [Hstabletype [Hsmemtype [Hsglobaltype [Hselemtype Hsdatatype]]]]].
    repeat split => //.
    (* Functions *)
    {
      rewrite List.Forall_app; split.
      (* Originals *)
      {
        eapply List.Forall_impl; eauto => /=.
        move => fi [ft Hft].
        exists ft.
        by eapply store_extension_funcinst_typing; eauto.
      }
      (* New *)
      {
        apply Forall_spec.
        move => n fi Hnth.
        apply nth_error_map in Hnth as [mf [Hnth Hmap]].
        subst.
        unfold funcinst_typing.
        eexists; split; first by eauto.
        eapply Forall2_lookup in Hmfunctype as [tf [Hnthtf Hmftype]]; eauto.
        unfold module_func_typing in Hmftype; destruct mf, tf; simpl in *.
        destruct Hmftype as [Hnthmf [Hbet Hdefaultable]].
        unfold gen_func_instance => /=.
        rewrite Hnthmf; split => //.
        rewrite HIT => /=.
        rewrite Hnthmf; split => //.
        unfold expr_typing.
        split => //.
        admit.
      }
    }
    (* Tables *)
    {
      rewrite List.Forall_app; split.
      (* Originals *)
      {
        eapply List.Forall_impl; eauto => /=.
        move => ti [tabt Htabt].
        exists tabt.
        by eapply store_extension_tableinst_typing; eauto.
      }
      (* New *)
      {
        apply Forall_spec.
        move => n fi Hnth.
        apply nth_error_map in Hnth as [mt [Hnth <-]].
        apply nth_error_map in Hnth as [mtab [Hnth <-]].
        eapply all_projection in Hmtabletype; eauto.
        unfold module_table_typing in Hmtabletype.
        destruct mtab, modtab_type, tt_limits.
        unfold tableinst_typing, gen_table_instance; simpl in *.
        rewrite Hmtabletype List.repeat_length N2Nat.id eq_refl.
        rewrite all_repeat; first by eexists.
        unfold value_typing => /=.
        by rewrite value_subtyping_eq.
      }
    }
    (* Memories *)
    {
      rewrite List.Forall_app; split.
      (* Originals *)
      {
        eapply List.Forall_impl; eauto => /=.
        move => ? [t ?].
        exists t.
        by eapply store_extension_meminst_typing; eauto.
      }
      (* New *)
      {
        apply Forall_spec.
        move => n fi Hnth.
        apply nth_error_map in Hnth as [mt [Hnth <-]].
        apply nth_error_map in Hnth as [mm [Hnth <-]].
        eapply all_projection in Hmmemtype; eauto.
        unfold module_mem_typing in Hmmemtype.
        unfold meminst_typing, gen_mem_instance, memory_list.mem_make, memory_list.mem_length.
        rewrite Hmmemtype List.repeat_length N2Nat.id N.mul_comm eq_refl.
        by eexists.
      }
    }
    (* Globals *)
    {
      rewrite List.Forall_app; split.
      (* Originals *)
      {
        eapply List.Forall_impl; eauto => /=.
        move => ? [t ?].
        exists t.
        by eapply store_extension_globalinst_typing; eauto.
      }
      (* New *)
      {
        apply Forall_spec.
        move => n fi Hnth.
        apply nth_error_map in Hnth as [[mg gv] [Hnth <-]].
        apply combine_lookup in Hnth as [Hnthmg Hnthgv].
        eapply Forall2_lookup in Hmglobaltype as [gt [Hnth Hmap]]; eauto.
        unfold module_glob_typing in Hmap.
        destruct mg; destruct Hmap as [Hconst [<- Hbet]].
        unfold globalinst_typing.
        exists gt.
        destruct gt => /=.
        resolve_if_true_eq.
        simpl in *.
        eapply Forall2_lookup in Hinstglob as [v [Hnthv Hreduce]]; eauto.
        simplify_multieq.
        simpl in *.
        admit.
      }
    }
    admit.
    admit.
  }
  repeat split => //.
  exists C.
  unfold frame_typing; rewrite HIT.
  exists nil; subst => /=.
  by destruct C.
Qed.

End Host.
