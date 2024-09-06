(** Properties of instantiation spec **)

From mathcomp Require Import ssreflect eqtype seq ssrbool ssrfun ssrnat.
Require Import Coq.Program.Equality NArith.
Require Export instantiation_spec.
Require Export type_preservation properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Some of the proofs were adapted from the Iris branch -- therefore the stdpp notations for now *)
Notation "l !! n" := (List.nth_error l n) (at level 10).

Definition exp_default := MED_func 0%N.

(* Getting the count of each type of imports from a module. This is to calculate the correct shift for indices of the exports in the Wasm store later. *)
Definition get_import_func_count (m: module) :=
  length (pmap (fun x => match x.(imp_desc) with
                      | MID_func id => Some id
                      | _ => None
                      end) m.(mod_imports)).

Definition get_import_table_count (m: module) :=
  length (pmap (fun x => match x.(imp_desc) with
                      | MID_table id => Some id
                      | _ => None
                      end) m.(mod_imports)).
Definition get_import_mem_count (m: module) :=
  length (pmap (fun x => match x.(imp_desc) with
                      | MID_mem id => Some id
                      | _ => None
                      end) m.(mod_imports)).

Definition get_import_global_count (m: module) :=
  length (pmap (fun x => match x.(imp_desc) with
                      | MID_global id => Some id
                      | _ => None
                      end) m.(mod_imports)).

Lemma ext_funcs_lookup_exist (modexps: list extern_value) n fn:
  (ext_funcs modexps) !! n = Some fn ->
  exists k, modexps !! k = Some (EV_func fn).
Proof.
  move: n fn.
  induction modexps; move => n tn Hextfunclookup; try by destruct n => //=.
  simpl in Hextfunclookup.
  destruct a => //. 
  { simpl in *.
    destruct n; simpl in *; first by inversion Hextfunclookup; subst; exists 0.
    apply IHmodexps in Hextfunclookup.
    destruct Hextfunclookup as [k ?].
    by exists (S k).
  }
  all: simpl in *. 
  all: apply IHmodexps in Hextfunclookup.
  all: destruct Hextfunclookup as [k ?].
  all: by exists (S k).
Qed.

Lemma ext_tables_lookup_exist (modexps: list extern_value) n tn:
  (ext_tables modexps) !! n = Some tn ->
  exists k, modexps !! k = Some (EV_table tn).
Proof.
  move: n tn.
  induction modexps; move => n tn Hexttablookup; try by destruct n => //=.
  simpl in Hexttablookup.
  destruct a => //. 
  2: { simpl in *.
       destruct n; simpl in *; first by inversion Hexttablookup; subst; exists 0.
       apply IHmodexps in Hexttablookup.
       destruct Hexttablookup as [k ?].
       by exists (S k).
  }
  all: simpl in *. 
  all: apply IHmodexps in Hexttablookup.
  all: destruct Hexttablookup as [k ?].
  all: by exists (S k).
Qed.

Lemma ext_mems_lookup_exist (modexps: list extern_value) n mn:
  (ext_mems modexps) !! n = Some mn ->
  exists k, modexps !! k = Some (EV_mem mn).
Proof.
  move: n mn.
  induction modexps; move => n mn Hextmemlookup; try by destruct n => //=.
  simpl in Hextmemlookup.
  destruct a => //. 
  3: { simpl in *.
       destruct n; simpl in *; first try by inversion Hextmemlookup; subst; exists 0.
       apply IHmodexps in Hextmemlookup.
       destruct Hextmemlookup as [k ?].
       by exists (S k).
  }
  all: simpl in *. 
  all: apply IHmodexps in Hextmemlookup.
  all: destruct Hextmemlookup as [k ?].
  all: by exists (S k).
Qed.

Lemma ext_globals_lookup_exist (modexps: list extern_value) n fn:
  (ext_globals modexps) !! n = Some fn ->
  exists k, modexps !! k = Some (EV_global fn).
Proof.
  move: n fn.
  induction modexps; move => n tn Hextgloblookup; try by destruct n => //=.
  simpl in Hextgloblookup.
  destruct a => //. 
  4: { simpl in *.
       destruct n; simpl in *; first by inversion Hextgloblookup; subst; exists 0.
       apply IHmodexps in Hextgloblookup.
       destruct Hextgloblookup as [k ?].
       by exists (S k).
  }
  all: simpl in *. 
  all: apply IHmodexps in Hextgloblookup.
  all: destruct Hextgloblookup as [k ?].
  all: by exists (S k).
Qed.

Lemma ext_funcs_lookup_exist_inv (modexps: list extern_value) n idx:
  modexps !! n = Some (EV_func idx) ->
  exists k, ((ext_funcs modexps) !! k = Some idx).
Proof.
  move : n idx.
  induction modexps; move => n idx H; try by destruct n => //=.
  destruct n; simpl in *.
  { inversion H; subst; by exists 0 => /=. }
  apply IHmodexps in H.
  destruct H as [k Hl].
  destruct a; try by exists k.
  by exists (S k).
Qed.

Lemma ext_tables_lookup_exist_inv (modexps: list extern_value) n idx:
  modexps !! n = Some (EV_table idx) ->
  exists k, ((ext_tables modexps) !! k = Some idx).
Proof.
  move : n idx.
  induction modexps; move => n idx H; try by destruct n => //=.
  destruct n; simpl in *.
  { inversion H; subst; by exists 0 => /=. }
  apply IHmodexps in H.
  destruct H as [k Hl].
  destruct a; try by exists k.
  by exists (S k).
Qed.

Lemma ext_mems_lookup_exist_inv (modexps: list extern_value) n idx:
  modexps !! n = Some (EV_mem idx) ->
  exists k, ((ext_mems modexps) !! k = Some idx).
Proof.
  move : n idx.
  induction modexps; move => n idx H; try by destruct n => //=.
  destruct n; simpl in *.
  { inversion H; subst; by exists 0 => /=. }
  apply IHmodexps in H.
  destruct H as [k Hl].
  destruct a; try by exists k.
  by exists (S k).
Qed.

Lemma ext_globals_lookup_exist_inv (modexps: list extern_value) n idx:
  modexps !! n = Some (EV_global idx) ->
  exists k, ((ext_globals modexps) !! k = Some idx).
Proof.
  move : n idx.
  induction modexps; move => n idx H; try by destruct n => //=.
  destruct n; simpl in *.
  { inversion H; subst; by exists 0 => /=. }
  apply IHmodexps in H.
  destruct H as [k Hl].
  destruct a; try by exists k.
  by exists (S k).
Qed.

Section Host.

Context `{ho: host}.

(* Proving relations between stores obtained by alloc_Xs *)
Lemma alloc_Xs_IP {A B: Type} (f: store_record -> A -> store_record * B) s_init xs s_end ys (R: store_record -> store_record -> list A -> list B -> Prop) :
  alloc_Xs f s_init xs = (s_end, ys) ->
  (R s_init s_init [::] [::]) ->
  (forall s s0 x xs' ys' s' y,
    (s, y) = f s' x ->
    R s0 s' xs' ys' ->
    R s0 s (xs' ++ [::x]) (ys' ++ [::y])) ->
  R s_init s_end xs ys.
Proof.
  move: s_init s_end ys.
  induction xs using List.rev_ind => //=; move => s_init s_end ys Hallocxs Hinit IH; simpl in *.
  - unfold alloc_Xs in Hallocxs.
    simpl in Hallocxs.
    by injection Hallocxs as ->; subst.
  - unfold alloc_Xs in Hallocxs.
    rewrite List.fold_left_app in Hallocxs.
    simpl in Hallocxs.
    
    remember (List.fold_left _ xs _) as fold_res.
    destruct fold_res as [s0 ys0].
    remember (f s0 x) as sf.
    destruct sf as [s' y'].
    injection Hallocxs as ->; subst.
    eapply IH; eauto.
    apply IHxs; eauto.
    unfold alloc_Xs.
    by rewrite <- Heqfold_res.
Qed.

Lemma alloc_func_iota_N modfuncs ws inst ws' l:
  alloc_funcs ws modfuncs inst = (ws', l) ->
  l = iota_N (length (s_funcs ws)) (length modfuncs) /\
  ws'.(s_funcs) = ws.(s_funcs) ++ map (fun mf => gen_func_instance mf inst) modfuncs /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals) /\
  ws.(s_elems) = ws'.(s_elems) /\
  ws.(s_datas) = ws'.(s_datas).
Proof.
  unfold alloc_funcs.
  move => Halloc.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => ys = iota_N _ (length xs) /\ _))
    in Halloc; eauto => //=.
  - unfold iota_N => /=.
    repeat split.
    by rewrite cats0.
  - move => s s0 x xs' ys' s' y Hallocx [Hys [Hcomp [? [? [?[??]]]]]].
    repeat rewrite -> iota_N_iota_N in *.
    unfold alloc_func, add_func in Hallocx; injection Hallocx as ->; subst => /=.
    rewrite List.length_app map_cat iota_N_extend Hcomp => /=.
    repeat split => //=.
    + by rewrite List.length_app List.length_map.
    + by rewrite catA => /=.
Qed.

Lemma alloc_table_iota_N modtables ws ws' l:
  alloc_tabs ws modtables = (ws', l) ->
  l = iota_N (length (s_tables ws)) (length modtables) /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws'.(s_tables) = ws.(s_tables) ++ map (fun mf => gen_table_instance mf (VAL_ref_null (mf.(tt_elem_type)))) modtables /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals) /\
  ws.(s_elems) = ws'.(s_elems) /\
  ws.(s_datas) = ws'.(s_datas).
Proof.
  unfold alloc_tabs.
  move => Halloc.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => ys = iota_N _ (length xs) /\ _))
    in Halloc; eauto => //=.
  - unfold iota_N => /=.
    repeat split.
    by rewrite cats0.
  - move => s s0 x xs' ys' s' y Hallocx [Hys [? [Hcomp [? [?[??]]]]]].
    repeat rewrite -> iota_N_iota_N in *.
    unfold alloc_tab, alloc_tab_ref, add_table in Hallocx.
    destruct x, tt_limits.
    injection Hallocx as ->; subst => /=.
    rewrite List.length_app map_cat iota_N_extend Hcomp => /=.
    repeat split => //=.
    + by rewrite List.length_app List.length_map => /=.
    + by rewrite catA => /=.
Qed.

Lemma alloc_mem_iota_N modmems ws ws' l:
  alloc_mems ws modmems = (ws', l) ->
  l = iota_N (length (s_mems ws)) (length modmems) /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws'.(s_mems) = ws.(s_mems) ++ map (fun mf => gen_mem_instance mf) modmems /\
  ws.(s_globals) = ws'.(s_globals) /\
  ws.(s_elems) = ws'.(s_elems) /\
  ws.(s_datas) = ws'.(s_datas).
Proof.
  unfold alloc_mems.
  move => Halloc.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => ys = iota_N _ (length xs) /\ _))
    in Halloc; eauto => //=.
  - unfold iota_N => /=.
    repeat split.
    by rewrite cats0.
  - move => s s0 x xs' ys' s' y Hallocx [Hys [? [? [Hcomp [?[??]]]]]].
    repeat rewrite -> iota_N_iota_N in *.
    unfold alloc_mem, add_mem in Hallocx.
    destruct x.
    injection Hallocx as ->; subst => /=.
    rewrite List.length_app map_cat iota_N_extend Hcomp => /=.
    repeat split => //=.
    + by rewrite List.length_app List.length_map => /=.
    + by rewrite catA => /=.
Qed.

Lemma combine_snoc {T1 T2: Type}: forall (l1: list T1) (l2: list T2) lc x,
  lc ++ [::x] = List.combine l1 l2 ->
  length l1 = length l2 ->
  exists l1' l2' a b,
    (l1 = l1' ++ [::a] /\ l2 = l2' ++ [::b] /\ lc = List.combine l1' l2' /\ x = (a, b)).
Proof.
  induction l1 as [| a l1']; move => l2 lc x Hcomb Hlen; first by destruct lc.
  destruct l2 as [|b l2'], lc as [|p lc'] => //; simpl in *; try by rewrite combine_nil in Hcomb.
  - destruct l1', l2' => //; simpl in *.
    injection Hcomb as ->.
    by exists nil, nil, a, b.
  - simpl in *.
    injection Hlen as Hlen.
    injection Hcomb as ->.
    apply IHl1' in H => //.
    destruct H as [l1'' [l2'' [a' [b' [-> [-> [-> ->]]]]]]].
    by exists (a :: l1''), (b :: l2''), a', b'.
Qed.

Lemma alloc_global_iota_N modglobals g_inits ws ws' l:
  alloc_globs ws modglobals g_inits = (ws', l) ->
  length g_inits = length modglobals ->
  l = iota_N (length (s_globals ws)) (length modglobals) /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws'.(s_globals) = ws.(s_globals) ++ map (fun '({| modglob_type := gt; modglob_init := ge |}, v) => {| g_type := gt; g_val := v |} ) (List.combine modglobals g_inits) /\
  ws.(s_elems) = ws'.(s_elems) /\
  ws.(s_datas) = ws'.(s_datas).
Proof.
  unfold alloc_globs.
  move => Halloc.
  remember (List.combine modglobals g_inits) as comb.
  move : modglobals g_inits Heqcomb.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => forall globs g_inits, xs = List.combine globs g_inits -> length g_inits = length globs -> ys = iota_N _ _ /\ _))
    in Halloc; eauto => //=.
  - unfold iota_N => /=.
    repeat split; last by rewrite cats0.
    by destruct globs, g_inits => //.
  - repeat setoid_rewrite iota_N_iota_N.
    move => s s0 x xs' ys' s' y Hallocx Hind modglobs g_inits Hcomb Hgloblen.
    apply combine_snoc in Hcomb; last by lias.
    destruct Hcomb as [modglobs' [g_inits' [g [v [-> [-> [-> ->]]]]]]].
    destruct (Hind modglobs' g_inits') as [Hys [? [? [? [Hcomp [??]]]]]] => //; clear Hind.
    { repeat rewrite List.length_app in Hgloblen; simpl in Hgloblen. by lias. }
    unfold alloc_glob, add_glob in Hallocx. injection Hallocx as ->; subst => /=.
    rewrite map_cat List.length_app iota_N_extend Hcomp => /=.
    rewrite List.length_app.
    repeat split => //=.
    + do 3 f_equal.
      repeat rewrite List.length_app in Hgloblen; simpl in Hgloblen.
      rewrite List.length_map List.length_combine.
      by lias.
    + rewrite -catA.
      by destruct g.
Qed.

Lemma alloc_elem_iota_N modelems r_inits ws ws' l:
  alloc_elems ws modelems r_inits = (ws', l) ->
  length r_inits = length modelems ->
  l = iota_N (length (s_elems ws)) (length modelems) /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals) /\
  ws'.(s_elems) = ws.(s_elems) ++ map (fun '(elem, refs) => {| eleminst_type := elem.(modelem_type); eleminst_elem := refs |} ) (List.combine modelems r_inits) /\
  ws.(s_datas) = ws'.(s_datas).
Proof.
  unfold alloc_elems.
  move => Halloc.
  remember (List.combine modelems r_inits) as comb.
  move : modelems r_inits Heqcomb.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => forall elems r_inits, xs = List.combine elems r_inits -> length r_inits = length elems -> ys = iota_N _ _ /\ _))
    in Halloc; eauto => //=.
  - unfold iota_N => /=.
    repeat split; last by rewrite cats0.
    by destruct elems, r_inits => //.
  - repeat setoid_rewrite iota_N_iota_N.
    move => s s0 x xs' ys' s' y Hallocx Hind modelems r_inits Hcomb Helemlen.
    apply combine_snoc in Hcomb; last by lias.
    destruct Hcomb as [modelems' [r_inits' [r [v [-> [-> [-> ->]]]]]]].
    destruct (Hind modelems' r_inits') as [Hys [? [? [? [? [Hcomp ?]]]]]] => //; clear Hind.
    { repeat rewrite List.length_app in Helemlen; simpl in Helemlen. by lias. }
    unfold alloc_elem, add_elem in Hallocx. injection Hallocx as ->; subst => /=.
    rewrite map_cat List.length_app iota_N_extend Hcomp => /=.
    rewrite List.length_app.
    repeat split => //=.
    + do 3 f_equal.
      repeat rewrite List.length_app in Helemlen; simpl in Helemlen.
      rewrite List.length_map List.length_combine.
      by lias.
    + rewrite -catA.
      by destruct r.
Qed.

Lemma alloc_data_iota_N moddatas ws ws' l:
  alloc_datas ws moddatas = (ws', l) ->
  l = iota_N (length (s_datas ws)) (length moddatas) /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals) /\
  ws.(s_elems) = ws'.(s_elems) /\
  ws'.(s_datas) = ws.(s_datas) ++ map (fun md => {| datainst_data := md.(moddata_init) |} ) moddatas.
Proof.
  unfold alloc_datas.
  move => Halloc.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => ys = iota_N _ (length xs) /\ _))
    in Halloc; eauto => //=.
  - unfold iota_N => /=.
    repeat split.
    by rewrite cats0.
  - move => s s0 x xs' ys' s' y Hallocx [Hys [? [? [? [? [? Hcomp]]]]]].
    repeat rewrite -> iota_N_iota_N in *.
    unfold alloc_data, add_data in Hallocx.
    destruct x.
    injection Hallocx as ->; subst => /=.
    rewrite List.length_app map_cat iota_N_extend Hcomp => /=.
    repeat split => //=.
    + by rewrite List.length_app List.length_map => /=.
    + by rewrite catA => /=.
Qed.

Lemma bet_const_exprs_len tc es t1 t2:
  const_exprs tc es ->
  be_typing tc es (Tf t1 t2) ->
  length t2 = length es + length t1.
Proof.
  move: t1 t2.
  induction es; move => t1 t2 Hconst Hbet.
  { invert_be_typing; subst.
    apply values_subtyping_size in Hbet.
    by repeat rewrite length_is_size.
  }
  { rewrite <- cat1s in Hbet.
    invert_be_typing.
    simpl in Hconst; remove_bools_options.
    destruct tf_principal.
    eapply IHes in H2_comp => //.
    unfold const_expr in H.
    rewrite H2_comp => /=.
    destruct a => //; invert_be_typing; simpl in Hinvgoal.
    all: try by
      (injection Hinvgoal as -> ->;
      apply instr_subtyping_size_exact in Htisub; simpl in *;
      repeat rewrite length_is_size;
         by lias).
    all: by
      (extract_premise;
       injection Hconjl as -> ->;
      apply instr_subtyping_size_exact in Htisub; simpl in *;
      repeat rewrite length_is_size;
         by lias).
  }
Qed.
  
Lemma const_exprs_impl tc es t:
  const_exprs tc es ->
  be_typing tc es (Tf [::] [::t]) ->
  exists e, es = [:: e] /\ const_expr tc e.
Proof.
  move => Hconst Hbet.
  eapply bet_const_exprs_len in Hbet => //.
  do 2 destruct es => //=.
  exists b; split => //.
  unfold const_exprs in Hconst.
  simpl in Hconst.
  move/andP in Hconst.
  by destruct Hconst.
Qed.

Lemma value_no_reduce (hs hs': host_state) s f v s' f' e':
  reduce hs s f [::$V v] hs' s' f' e' ->
  False.
Proof.
  move => Hred.
  dependent induction Hred; subst; (try by repeat destruct vs => //; destruct v as [v | v | v]; destruct v => //); (try by repeat destruct vcs => //; destruct v as [v | v | v]; destruct v => //).
  { inversion H; subst; clear H; try by destruct v as [v | v | v]; destruct v => //.
    by destruct lh as [vs ? | ? vs]; simpl in H1; destruct v as [v | v | v]; destruct v; do 2 destruct vs => //.
  }
  { destruct lh as [vs ? | ? vs] => //=; simpl in H; last by destruct v as [v | v | v]; destruct v => //; do 2 destruct vs => //=.
    destruct vs => //=; last first.
    { destruct vs, es, l => //=.
      by apply reduce_not_nil in Hred.
    }
    destruct es => //=; first by apply reduce_not_nil in Hred.
    by destruct es, l => //=.
  }
Qed.

Lemma reduce_trans_value hs1 s1 f1 v1 hs2 s2 f2 v2:
  reduce_trans (hs1, s1, f1, [::$V v1]) (hs2, s2, f2, [::$V v2]) ->
  v1 = v2.
Proof.
  move => Hred.
  unfold reduce_trans in Hred.
  apply Operators_Properties.clos_rt_rt1n_iff in Hred.
  inversion Hred => //; first by apply ve_inj.
  unfold reduce_tuple in H.
  destruct y as [[[??]?]?].
  by apply value_no_reduce in H.
Qed.

Lemma reduce_ref_func hs s f hs' s' f' i e:
  reduce hs s f [::AI_basic (BI_ref_func i)] hs' s' f' e ->
  exists addr, lookup_N f.(f_inst).(inst_funcs) i = Some addr /\ e = [::$V (VAL_ref (VAL_ref_func addr))].
Proof.
  move => Hred.
  dependent induction Hred; subst; (try by repeat destruct vcs => //); (try by repeat destruct vs => //).
  { inversion H; subst; clear H; try by repeat destruct vs => //.
    destruct lh as [vs ? | ? vs]; simpl in H1; by do 2 destruct vs => //=.
  }
  { by exists addr. }
  { destruct lh as [vs ? | ? vs] => //=; simpl in H; last by do 2 destruct vs => //.
    destruct vs as [ | v ?]; last by destruct v as [v | v | v]; destruct v => //=.
    destruct es => //=; first by apply reduce_not_nil in Hred.
    destruct es, l => //=.
    simpl in *.
    inversion H; subst; clear H.
    rewrite cats0.
    by eapply IHHred.
  }
Qed.

Lemma reduce_trans_ref_func hs1 s1 f1 x hs2 s2 f2 v:
  reduce_trans (hs1, s1, f1, [:: AI_basic (BI_ref_func x)]) (hs2, s2, f2, [::$V v]) ->
  exists addr, lookup_N f1.(f_inst).(inst_funcs) x = Some addr /\ v = VAL_ref (VAL_ref_func addr).
Proof.
  move => Hred.
  unfold reduce_trans in Hred.
  apply Operators_Properties.clos_rt_rt1n_iff in Hred.
  inversion Hred; subst; clear Hred; first by (apply (f_equal e_to_v_opt) in H3; simpl in *; rewrite v2e2v in H3).
  destruct y as [[[??]?]?].
  unfold reduce_tuple, opsem.reduce_tuple in H.
  apply reduce_ref_func in H.
  destruct H as [addr [Hnth ->]].
  inversion H0; subst; clear H0 => //.
  - apply (f_equal e_to_v_opt) in H4; rewrite v2e2v in H4; simpl in H4.
    injection H4 as <-.
    by exists addr.
  - unfold reduce_tuple, opsem.reduce_tuple in H.
    destruct y as [[[??]?]?].
    by apply value_no_reduce in H.
Qed.

Lemma reduce_global_get hs s f hs' s' f' i e:
  reduce hs s f [::AI_basic (BI_global_get i)] hs' s' f' e ->
  exists v, sglob_val s (f_inst f) i = Some v /\ e = [::$V v].
Proof.
  move => Hred.
  dependent induction Hred; subst; (try by repeat destruct vcs => //); (try by repeat destruct vs => //).
  { inversion H; subst; clear H; try by repeat destruct vs => //.
    destruct lh as [vs ? | ? vs]; simpl in H1; by do 2 destruct vs => //=.
  }
  { by exists v. }
  { destruct lh as [vs ? | ? vs] => //=; simpl in H; last by do 2 destruct vs => //.
    destruct vs as [ | v ?]; last by destruct v as [v | v | v]; destruct v => //=.
    destruct es => //=; first by apply reduce_not_nil in Hred.
    destruct es, l => //=.
    simpl in *.
    inversion H; subst; clear H.
    rewrite cats0.
    by eapply IHHred.
  }
Qed.
    
Lemma reduce_trans_global_get hs s f hs' s' f' i v:
  reduce_trans (hs, s, f, [::AI_basic (BI_global_get i)]) (hs', s', f', [::$V v]) ->
  sglob_val s (f_inst f) i = Some v.
Proof.
  move => Hred.
  unfold reduce_trans, opsem.reduce_trans in *.
  apply Operators_Properties.clos_rt_rt1n_iff in Hred.
  inversion Hred; subst; clear Hred; first by repeat destruct v.
  destruct y as [[[??]?]?].
  unfold reduce_tuple, opsem.reduce_tuple in H.
  apply reduce_global_get in H.
  destruct H as [v' [Hsgv ->]].
  inversion H0; subst; clear H0 => //.
  - uapply Hsgv; f_equal.
    by apply ve_inj.
  - unfold reduce_tuple, opsem.reduce_tuple in H.
    destruct y as [[[??]?]?].
    by apply value_no_reduce in H.
Qed.

Lemma vt_imps_comp_len s (v_imps: list extern_value) t_imps:
  List.Forall2 (external_typing s) v_imps t_imps ->
  (length (ext_funcs v_imps) = length (ext_t_funcs t_imps) /\
    length (ext_tables v_imps) = length (ext_t_tables t_imps) /\
    length (ext_mems v_imps) = length (ext_t_mems t_imps) /\
    length (ext_globals v_imps) = length (ext_t_globals t_imps)).
Proof.
  move: t_imps.
  induction v_imps; move => t_imps Hexttype; destruct t_imps; try by apply List.Forall2_length in Hexttype.
  inversion Hexttype; subst; clear Hexttype.
  apply IHv_imps in H4.
  destruct H4 as [Hft [Htt [Hmt Hgt]]].
  unfold external_typing, ext_typing in H2.
  destruct a, e; simpl in H2; remove_bools_options => //=; repeat split; try by f_equal.
Qed.

Lemma import_subtyping_comp_len t_imps1 t_imps2:
  List.Forall2 import_subtyping t_imps1 t_imps2->
  (length (ext_t_funcs t_imps1) = length (ext_t_funcs t_imps2) /\
    length (ext_t_tables t_imps1) = length (ext_t_tables t_imps2) /\
    length (ext_t_mems t_imps1) = length (ext_t_mems t_imps2) /\
    length (ext_t_globals t_imps1) = length (ext_t_globals t_imps2)).
Proof.
  move: t_imps2.
  induction t_imps1; move => t_imps2 Hexttype; destruct t_imps2; try by apply List.Forall2_length in Hexttype.
  inversion Hexttype; subst; clear Hexttype.
  apply IHt_imps1 in H4.
  destruct H4 as [Hft [Htt [Hmt Hgt]]].
  unfold import_subtyping in H2.
  destruct a, e; simpl in H2; remove_bools_options => //=; repeat split; try by lias.
Qed.

Lemma import_subtyping_components: forall t_imps1 t_imps2,
    List.Forall2 import_subtyping t_imps1 t_imps2 ->
    List.Forall2 import_func_subtyping (ext_t_funcs t_imps1) (ext_t_funcs t_imps2) /\
    List.Forall2 import_table_subtyping (ext_t_tables t_imps1) (ext_t_tables t_imps2) /\
    List.Forall2 import_mem_subtyping (ext_t_mems t_imps1) (ext_t_mems t_imps2) /\
    List.Forall2 import_global_subtyping (ext_t_globals t_imps1) (ext_t_globals t_imps2).
Proof.
  induction t_imps1; destruct t_imps2 => //=; move => Hall2; inversion Hall2; subst; clear Hall2 => /=.
  destruct a, e => //=; repeat split; (try constructor) => //; by apply IHt_imps1.
Qed.

Lemma vt_imps_funcs_lookup s v_imps t_imps gt (k: nat):
  List.Forall2 (external_typing s) v_imps t_imps ->
  List.nth_error (ext_t_funcs t_imps) k = Some gt ->
  exists n gn,
    List.nth_error (ext_funcs v_imps) k = Some gn /\
    v_imps !! n = Some (EV_func gn) /\
    t_imps !! n = Some (ET_func gt).
Proof.
  move: t_imps k gt.
  induction v_imps; destruct t_imps; move => k gt Hall2; (try by inversion Hall2); (try by destruct k).
  move => Ht.
  inversion Hall2; subst; clear Hall2.
  unfold external_typing, ext_typing in H2.
  destruct a, e => //; (try by simpl in H2); remove_bools_options; simpl ext_t_funcs in Ht.
  1 : {
    destruct k; first by exists 0, f => /=; simpl in Ht; inversion Ht; subst.
    simpl in *.
    eapply IHv_imps in H4 as [n [v [Hnthv Hntht]]]; eauto.
    by exists (S n), v.
  }
  all: eapply IHv_imps in H4 as [n [v [Hnthv Hntht]]]; eauto; by exists (S n), v.
Qed.

Lemma vt_imps_tables_lookup s v_imps t_imps gt (k: nat):
  List.Forall2 (external_typing s) v_imps t_imps ->
  List.nth_error (ext_t_tables t_imps) k = Some gt ->
  exists n gn,
    List.nth_error (ext_tables v_imps) k = Some gn /\
    v_imps !! n = Some (EV_table gn) /\
    t_imps !! n = Some (ET_table gt).
Proof.
  move: t_imps k gt.
  induction v_imps; destruct t_imps; move => k gt Hall2; (try by inversion Hall2); (try by destruct k).
  move => Ht.
  inversion Hall2; subst; clear Hall2.
  unfold external_typing, ext_typing in H2.
  destruct a, e => //; (try by simpl in H2); remove_bools_options; simpl ext_t_tables in Ht.
  2 : {
    destruct k; first by exists 0, t => /=; simpl in Ht; inversion Ht; subst.
    simpl in *.
    eapply IHv_imps in H4 as [n [v [Hnthv Hntht]]]; eauto.
    by exists (S n), v.
  }
  all: eapply IHv_imps in H4 as [n [v [Hnthv Hntht]]]; eauto; by exists (S n), v.
Qed.

Lemma vt_imps_mems_lookup s v_imps t_imps gt (k: nat):
  List.Forall2 (external_typing s) v_imps t_imps ->
  List.nth_error (ext_t_mems t_imps) k = Some gt ->
  exists n gn,
    List.nth_error (ext_mems v_imps) k = Some gn /\
    v_imps !! n = Some (EV_mem gn) /\
    t_imps !! n = Some (ET_mem gt).
Proof.
  move: t_imps k gt.
  induction v_imps; destruct t_imps; move => k gt Hall2; (try by inversion Hall2); (try by destruct k).
  move => Ht.
  inversion Hall2; subst; clear Hall2.
  unfold external_typing, ext_typing in H2.
  destruct a, e => //; (try by simpl in H2); remove_bools_options; simpl ext_t_mems in Ht.
  3 : {
    destruct k; first by exists 0, m => /=; simpl in Ht; inversion Ht; subst.
    simpl in *.
    eapply IHv_imps in H4 as [n [v [Hnthv Hntht]]]; eauto.
    by exists (S n), v.
  }
  all: eapply IHv_imps in H4 as [n [v [Hnthv Hntht]]]; eauto; by exists (S n), v.
Qed.

Lemma vt_imps_globals_lookup s v_imps t_imps gt (k: nat):
  List.Forall2 (external_typing s) v_imps t_imps ->
  List.nth_error (ext_t_globals t_imps) k = Some gt ->
  exists n gn,
    List.nth_error (ext_globals v_imps) k = Some gn /\
    v_imps !! n = Some (EV_global gn) /\
    t_imps !! n = Some (ET_global gt).
Proof.
  move: t_imps k gt.
  induction v_imps; destruct t_imps; move => k gt Hall2; (try by inversion Hall2); (try by destruct k).
  move => Ht.
  inversion Hall2; subst; clear Hall2.
  unfold external_typing, ext_typing in H2.
  destruct a, e => //; (try by simpl in H2); remove_bools_options; simpl ext_t_globals in Ht.
  4 : {
    destruct k; first by exists 0, g => /=; simpl in Ht; inversion Ht; subst.
    simpl in *.
    eapply IHv_imps in H4 as [n [v [Hnthv Hntht]]]; eauto.
    by exists (S n), v.
  }
  all: eapply IHv_imps in H4 as [n [v [Hnthv Hntht]]]; eauto; by exists (S n), v.
Qed.

Lemma combine_lookup_spec {T1 T2: Type}: forall (l1: list T1) (l2: list T2) n v1 v2,
    List.nth_error l1 n = Some v1 ->
    List.nth_error l2 n = Some v2 ->
    List.nth_error (List.combine l1 l2) n = Some (v1, v2).
Proof.
  induction l1; destruct l2; destruct n => /=; move => v1 v2 Hnth1 Hnth2 => //=; first by inversion Hnth1; inversion Hnth2.
  by apply IHl1.
Qed.

Lemma import_subtyping_globs_impl': forall t_imps_mod t_imps i gt,
    List.Forall2 import_subtyping t_imps t_imps_mod ->
    List.nth_error (ext_t_globals t_imps_mod) i = Some gt ->
    exists gt', List.nth_error (ext_t_globals t_imps) i = Some gt' /\ import_global_subtyping gt' gt.
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

Lemma vt_imps_globals_typing s v_imps t_imps gt (k: nat):
  List.Forall2 (external_typing s) v_imps t_imps ->
  (ext_t_globals t_imps) !! k = Some gt ->
  exists gn, (ext_globals v_imps) !! k = Some gn /\
          external_typing s (EV_global gn) (ET_global gt).
Proof.
  move => HForall2 Htl.
  eapply vt_imps_globals_lookup in Htl as [n [gn [Hvl [Hnth Ht]]]] => //; eauto.
  eapply Forall2_lookup in HForall2; eauto.
  destruct HForall2 as [y [Htl'' HR']].
  exists gn.
  by simplify_multieq.
Qed.

Lemma init_value_typing: forall C hs s f bes v t,
  reduce_trans (hs, s, f, (to_e_list bes)) (hs, s, f, [::$V v]) ->
  const_exprs C bes ->
  be_typing C bes (Tf nil [::t]) ->
  (forall n addr, List.nth_error f.(f_inst).(inst_funcs) n = Some addr ->
             (addr < N.of_nat (length s.(s_funcs)))%N) ->
  (forall gidx v t, sglob_val s f.(f_inst) gidx = Some v ->
               lookup_N C.(tc_globals) gidx = Some t ->
               value_typing s v t.(tg_t)) ->
  value_typing s v t.
Proof.
  move => C hs s f bes v t Hreduce Hconst Hbet Hsfunc Hsglobtype.
  eapply const_exprs_impl in Hconst as [be [-> Hconst]]; eauto.
  destruct be => //; invert_be_typing.
  (* VAL_num *)
  { replace (to_e_list [::BI_const_num v0]) with ([::$V (VAL_num v0)]) in Hreduce; last done.
    apply reduce_trans_value in Hreduce; subst.
    unfold value_typing => /=.
    by simplify_subtyping.
  }
  (* VAL_vec *)
  { replace (to_e_list [::BI_const_vec v0]) with ([::$V (VAL_vec v0)]) in Hreduce; last done.
    apply reduce_trans_value in Hreduce; subst.
    unfold value_typing => /=.
    by simplify_subtyping.
  }
  (* ref_null *)
  { replace (to_e_list [::BI_ref_null r]) with ([::$V (VAL_ref (VAL_ref_null r))]) in Hreduce; last done.
    apply reduce_trans_value in Hreduce; subst.
    unfold value_typing => /=.
    by simplify_subtyping.
  }
  (* ref_func *)
  { apply reduce_trans_ref_func in Hreduce as [addr [Hnthaddr ->]].
    unfold value_typing => /=; unfold ext_func_typing => /=.
    invert_be_typing.
    apply instr_subtyping_empty1_impl' in Htisub; simpl in *; remove_bools_options.
    assert (exists x, lookup_N (s_funcs s) addr = Some x) as [? Hnth].
    { apply Hsfunc in Hnthaddr.
      destruct (lookup_N (s_funcs s) addr) eqn:Hnth; first by eexists.
      exfalso.
      apply List.nth_error_None in Hnth.
      by lias.
    }
    rewrite Hnth => /=.
    by resolve_subtyping.
  }
  (* global_get *)
  { apply reduce_trans_global_get in Hreduce.
    unfold value_typing => /=.
    assert (tg_t extr <t: t) as Hsub; first by simplify_subtyping.
    eapply Hsglobtype in Hreduce; eauto.
    unfold value_typing in Hreduce; remove_bools_options.
    by resolve_subtyping.
  }
Qed.

End Host.
