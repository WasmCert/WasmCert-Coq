(** Properties of instantiation spec **)

From mathcomp Require Import ssreflect eqtype seq ssrbool ssrfun.
Require Import Coq.Program.Equality List NArith.
Require Export instantiation_spec.
Require Export type_preservation type_progress properties.

Notation "l !! n" := (List.nth_error l n) (at level 10).

Section module_typing_det.

Lemma list_eq {T: Type} (l1 l2: list T):
  (forall i, List.nth_error l1 i = List.nth_error l2 i) -> l1 = l2.
Proof.
  move: l1 l2.
  induction l1; destruct l2 => //=; move => H; try by specialize (H 0).
  f_equal.
  - specialize (H 0); by injection H.
  - apply IHl1; move => i.
    by specialize (H (S i)).
Qed.

Lemma Forall2_length {T1 T2: Type} (f: T1 -> T2 -> Prop) l1 l2:
  List.Forall2 f l1 l2 ->
  length l1 = length l2.
Proof.
  move: l1 l2.
  induction l1; destruct l2 => //=; move => H; inversion H; subst; clear H.
  f_equal; by apply IHl1.
Qed.

Lemma Forall_lookup {T: Type} (P: T -> Prop) l i x:
  List.Forall P l ->
  List.nth_error l i = Some x ->
  P x.
Proof.
  move: l i x.
  induction l; destruct i => //=; move => x Hall Hnth.
  - injection Hnth as ->.
    by inversion Hall.
  - eapply IHl; eauto => //.
    by inversion Hall.
Qed.

Lemma Forall_spec {T: Type} (P: T -> Prop) (l: list T):
  (forall n x, List.nth_error l n = Some x -> P x) ->
  Forall P l.
Proof.
  induction l; move => Hspec => //.
  constructor.
  - by eapply (Hspec 0 a).
  - apply IHl.
    move => n x Hnth.
    by apply (Hspec (S n) x).
Qed.

Lemma Forall2_lookup {T1 T2: Type} (f: T1 -> T2 -> Prop) l1 l2 i x:
  List.Forall2 f l1 l2 ->
  List.nth_error l1 i = Some x ->
  exists y, List.nth_error l2 i = Some y /\ f x y.
Proof.
  move: l1 l2 i x.
  induction l1; destruct l2, i => //=; move => x Hall2 Hnth; try by inversion Hall2.
  - injection Hnth as ->. eexists; split => //.
    by inversion Hall2.
  - apply IHl1 => //.
    by inversion Hall2.
Qed.

Lemma Forall2_function_eq_cond {T1 T2: Type} (P: T1 -> Prop) (f g: T1 -> T2 -> Prop) l1 l2 l3:
  List.Forall P l1 ->
  List.Forall2 f l1 l2 ->
  List.Forall2 g l1 l3 ->
  (forall x y z, P x -> f x y -> g x z -> y = z) ->
  l2 = l3.
Proof.
  move => Hall Hall2f Hall2g Heq.
  apply list_eq.
  move => i.
  destruct (List.nth_error l1 i) eqn:Hnth.
  { eapply Forall_lookup in Hall; eauto => //.
    eapply Forall2_lookup in Hall2f as [y [Hnth1 Hf]]; eauto => //.
    eapply Forall2_lookup in Hall2g as [z [Hnth2 Hg]]; eauto => //.
    rewrite Hnth1 Hnth2; f_equal.
    by eapply Heq; eauto.
  }
  { apply Forall2_length in Hall2f.
    apply Forall2_length in Hall2g.
    apply List.nth_error_None in Hnth.
    specialize (List.nth_error_None l2 i) as [_ Hnone1].
    rewrite Hnone1; last by lias.
    symmetry. rewrite -> List.nth_error_None. by lias.
  }
Qed.

Lemma Forall2_function_eq {T1 T2: Type} (f g: T1 -> T2 -> Prop) l1 l2 l3:
  List.Forall2 f l1 l2 ->
  List.Forall2 g l1 l3 ->
  (forall x y z, f x y -> g x z -> y = z) ->
  l2 = l3.
Proof.
  move => Hall2f Hall2g Heq.
  eapply Forall2_function_eq_cond with (P := fun _ => True) in Hall2g; eauto.
  clear. by induction l1; constructor.
Qed.

Lemma Forall2_all2: forall {A B: Type} (R : A -> B -> bool) (l1 : seq.seq A) (l2 : seq.seq B),
    List.Forall2 R l1 l2 <-> all2 R l1 l2.
Proof.
  move => A B R l1.
  split.
  - move: l2.
    induction l1; move => l2 HForall2.
    * by inversion HForall2.
    * inversion HForall2; subst.
      specialize (IHl1 l' H3).
      apply/andP. split => //.
  - move: l2.
    induction l1; move => l2 Hall2.
    * inversion Hall2. by destruct l2 => //.
    * inversion Hall2. destruct l2 => //.
      move/andP in H0. destruct H0.
      specialize (IHl1 l2 H0).
      apply Forall2_cons => //.
Qed.

Lemma all2_and: forall A B (f g h : A -> B -> bool) l1 l2,
  (forall a b, f a b = (g a b) && (h a b)) -> 
  all2 g l1 l2 /\ all2 h l1 l2 -> 
  all2 f l1 l2.
Proof.
  move => A B f g h l1 l2 Hand [Hg Hh].
  apply all2_spec; first by apply all2_size in Hg.
  move => n x y Hnth1 Hnth2.
  eapply all2_projection in Hg; eauto.
  eapply all2_projection in Hh; eauto.
  rewrite Hand; by lias.
Qed.

Lemma Forall2_nth_error: forall A B R (l1 : seq.seq A) (l2 : seq.seq B) n m k,
    List.Forall2 R l1 l2 ->
    List.nth_error l1 n = Some m ->
    List.nth_error l2 n = Some k ->
    R m k.
Proof.
  move => A B R l1 l2 n m k HForall2 Hnth1 Hnth2.
  eapply Forall2_lookup in Hnth1; eauto.
  destruct Hnth1 as [y [Hnth2' HR]].
  rewrite Hnth2' in Hnth2; by injection Hnth2 as ->.
Qed.

Lemma Forall2_spec: forall A B (R : A -> B -> Prop) (l1 : seq.seq A) (l2 : seq.seq B),
    List.length l1 = List.length l2 -> 
    (forall n m k,
    List.nth_error l1 n = Some m -> 
    List.nth_error l2 n = Some k ->
    R m k) ->
    List.Forall2 R l1 l2.
Proof.
  move => A B R l1.
  induction l1; move => l2 Hlen Hlookup; destruct l2 => //; simpl in *.
  constructor.
  - by apply (Hlookup 0 a b).
  - apply IHl1; first by lias.
    move => i x y Hl1 Hl2.
    by eapply (Hlookup (S i)) => //.
Qed.

Lemma nth_error_same_length_list:
  forall (A B : Type) (l1 : seq.seq A) (l2 : seq.seq B) (i : nat) (m : A),
     length l1 = length l2 ->
     nth_error l1 i = Some m -> 
     exists n, nth_error l2 i = Some n.
Proof.
  move => A B l1 l2 i m Hlen Hl1.
  apply nth_error_Some_length in Hl1.
  rewrite Hlen in Hl1.
  apply nth_error_Some in Hl1.
  by destruct (l2 !! i) => //; eexists.
Qed.

Fixpoint imap_aux {T1 T2: Type} (f: nat -> T1 -> T2) (l: list T1) (i: nat) : list T2 :=
  match l with
  | [::] => [::]
  | e :: l' => (f i e) :: imap_aux f l' (S i)
  end.

Definition imap {T1 T2: Type} (f: nat -> T1 -> T2) l := imap_aux f l 0.

Lemma imap_extend_aux {T1 T2: Type} (f: nat -> T1 -> T2) l e j:
  imap_aux f (app l [:: e]) j = app (imap_aux f l j) [:: f (length l + j) e].
Proof.
  move: j.
  induction l => //=; move => j.
  f_equal. rewrite (IHl (S j)).
  repeat f_equal.
  by lias.
Qed.

Lemma imap_extend {T1 T2: Type} (f: nat -> T1 -> T2) l e:
  imap f (app l [:: e]) = app (imap f l) [:: f (length l) e].
Proof.
  unfold imap.
  rewrite (imap_extend_aux f l e 0).
  repeat f_equal.
  by lias.
Qed.

Lemma imap_length_aux {T1 T2: Type} (f: nat -> T1 -> T2) l j:
  length (imap_aux f l j) = length l.
Proof.
  move: j.
  induction l => //=; move => j.
  f_equal; by apply IHl.
Qed.

Lemma imap_length {T1 T2: Type} (f: nat -> T1 -> T2) l:
  length (imap f l) = length l.
Proof.
  by apply (imap_length_aux f l 0).
Qed.

Lemma list_lookup_imap_aux {T1 T2: Type} (f: nat -> T1 -> T2) l i j:
  List.nth_error (imap_aux f l j) i = option_map (f (i + j)) (List.nth_error l i).
Proof.
  move: l i j.
  induction l; destruct i; move => j => //=.
  specialize (IHl i (S j)).
  rewrite IHl; repeat f_equal. by lias.
Qed.

Lemma list_lookup_imap {T1 T2: Type} (f: nat -> T1 -> T2) l i:
  List.nth_error (imap f l) i = option_map (f i) (List.nth_error l i).
Proof.
  unfold imap.
  rewrite -> (list_lookup_imap_aux f l i 0).
  by rewrite PeanoNat.Nat.add_0_r.
Qed.

Lemma repeat_lookup_Some {T: Type} (x y: T) n i:
  List.nth_error (List.repeat x n) i = Some y ->
  x = y /\ i < n.
Proof.
  move: i.
  induction n; destruct i => //=; move => H; try by inversion H; lias.
  apply IHn in H as [-> Hlt].
  split; by lias.
Qed.

Lemma NoDup_alt {T: Type} (l: list T):
  (forall i j x, l !! i = Some x -> l !! j = Some x -> i = j) -> List.NoDup l.
Proof.
  induction l; move => H => //; try by constructor.
  constructor.
  - move => Hin.
    apply List.In_nth_error in Hin as [n Hnth].
    specialize (H 0 (S n) a); simpl in H.
    by apply H in Hnth => //.
  - apply IHl.
    move => i j x Hnth1 Hnth2.
    specialize (H (S i) (S j) x); simpl in H.
    by apply H in Hnth1; lias.
Qed.
    
Definition gen_index offset len : list nat :=
  imap (fun i x => i+offset+x) (List.repeat 0 len).

Lemma gen_index_lookup offset len k:
  k < len ->
  (gen_index offset len) !! k = Some (offset + k).
Proof.
  move => Hlen.
  unfold gen_index.
  rewrite list_lookup_imap => /=.
  eapply List.nth_error_repeat with (a := 0) in Hlen.
  rewrite Hlen.
  simpl.
  f_equal.
  by lias.
Qed.

Lemma gen_index_lookup_Some n l i x:
  (gen_index n l) !! i = Some x ->
  x = n + i /\ i < l.
Proof.
  unfold gen_index.
  move => Hl.
  rewrite list_lookup_imap in Hl.
  destruct (List.repeat _ _ !! i) eqn: Hrl => //.
  simpl in Hl.
  inversion Hl; subst; clear Hl.
  apply repeat_lookup_Some in Hrl as [<- ?].
  by lias.
Qed.
 
Lemma gen_index_NoDup n l:
  List.NoDup (gen_index n l).
Proof.
  apply NoDup_alt.
  move => i j x Hli Hlj.
  apply gen_index_lookup_Some in Hli as [-> ?].
  apply gen_index_lookup_Some in Hlj as [? ?].
  by lias.
Qed.

Lemma gen_index_length n len:
  length (gen_index n len) = len.
Proof.
  unfold gen_index.
  rewrite imap_length.
  by rewrite List.repeat_length.
Qed.

Lemma gen_index_extend offset len:
  gen_index offset (len+1) = gen_index offset len ++ [::offset+len].
Proof.
  unfold gen_index.
  rewrite List.repeat_app imap_extend List.repeat_length => /=.
  do 2 f_equal.
  by lias.
Qed.

Lemma gen_index_len offset len:
  length (gen_index offset len) = len.
Proof.
  unfold gen_index.
  rewrite imap_length.
  by rewrite repeat_length.
Qed.

Lemma gen_index_in n i offset len:
  (gen_index offset len) !! n = Some i  ->
  i < offset + len.
Proof.
  move => H.
  apply gen_index_lookup_Some in H as [-> Hlt].
  by lias.
Qed.

Lemma gen_index_lookup_None: forall n m i,
  i >= m ->
  List.nth_error (gen_index n m) i = None.
Proof.
  move => n m i Hge.
  rewrite list_lookup_imap.
  destruct (_ !! i) eqn:Hnth => //.
  by apply repeat_lookup_Some in Hnth as [_ ?]; lias.
Qed.

Lemma gen_index_iota: forall n m,
  gen_index n m = iota n m.
Proof.
  move => n m.
  apply list_eq.
  move => i.
  destruct (Nat.ltb i m) eqn:Hlt; move/PeanoNat.Nat.ltb_spec0 in Hlt.
  - rewrite gen_index_lookup; last by lias.
    rewrite -> nth_error_nth with (x := 0), nth_iota; try by lias.
    by rewrite length_is_size size_iota; lias.
  - rewrite gen_index_lookup_None; last by lias.
    symmetry.
    apply List.nth_error_None.
    by rewrite length_is_size size_iota; lias.
Qed.

Lemma module_typing_det_import_aux m it1 et1 it2 et2:
  module_typing m it1 et1 ->
  module_typing m it2 et2 ->
  it1 = it2.
Proof.
  move => Hmt1 Hmt2.
  unfold module_typing in Hmt1, Hmt2.
  destruct m.
  destruct Hmt1 as [fts1 [gts1 [Hmft1 [Hmtt1 [Hmmt1 [Hmgt1 [Hmet1 [Hmdt1 [Hmst1 [Hmimt1 Hmext1]]]]]]]]]].
  destruct Hmt2 as [fts2 [gts2 [Hmft2 [Hmtt2 [Hmmt2 [Hmgt2 [Hmet2 [Hmdt2 [Hmst2 [Hmimt2 Hmext2]]]]]]]]]].
  
  clear - Hmimt1 Hmimt2.
  eapply Forall2_function_eq; eauto.
  move => x y z Heq1 Heq2; simpl in *.
  unfold module_import_typing in *.
  destruct x => /=; simpl in *.
  destruct imp_desc; simpl in *; destruct y, z => //; remove_bools_options; by subst.
Qed.

Lemma module_typing_det m it1 et1 it2 et2:
  module_typing m it1 et1 ->
  module_typing m it2 et2 ->
  (it1, et1) = (it2, et2).
Proof.
  move => Hmt1 Hmt2.
  specialize (module_typing_det_import_aux _ _ _ _ _ Hmt1 Hmt2) as ->.
  unfold module_typing in Hmt1, Hmt2.
  destruct m.
  destruct Hmt1 as [fts1 [gts1 [Hmft1 [Hmtt1 [Hmmt1 [Hmgt1 [Hmet1 [Hmdt1 [Hmst1 [Hmimt1 Hmext1]]]]]]]]]].
  destruct Hmt2 as [fts2 [gts2 [Hmft2 [Hmtt2 [Hmmt2 [Hmgt2 [Hmet2 [Hmdt2 [Hmst2 [Hmimt2 Hmext2]]]]]]]]]].

  (* Function types *)
  assert (fts1 = fts2) as Heqfts.
  { clear - Hmft1 Hmft2.
    eapply Forall2_function_eq; eauto.
    move => x y z Heq1 Heq2; simpl in *.
    unfold module_func_typing in *.
    simpl in *.
    destruct x, modfunc_type, y, z => /=; simpl in *.
    destruct Heq1 as [_ [Heq1 _]].
    destruct Heq2 as [_ [Heq2 _]].
    remove_bools_options.
    by rewrite - Heq1 Heq2.
  }
  subst.

  (* Global types *)
  assert (gts1 = gts2) as Heqgts.
  { clear - Hmgt1 Hmgt2.
    eapply Forall2_function_eq; eauto.
    move => x y z Heq1 Heq2; simpl in *.
    unfold module_func_typing in *.
    simpl in *.
    destruct x, modglob_type, y, z => /=; simpl in *.
    destruct Heq1 as [_ [Heq1 _]].
    destruct Heq2 as [_ [Heq2 _]].
    inversion Heq1; inversion Heq2; by subst. 
  }
  subst.
  
  f_equal.

  clear - Hmext1 Hmext2.
  eapply Forall2_function_eq; eauto.
  move => x y z Heq1 Heq2; simpl in *.
  unfold module_export_typing in *.
  simpl in *.
  destruct x, modexp_desc; [destruct f | destruct t | destruct m | destruct g]; destruct y, z; simpl in *; remove_bools_options; by subst => //.
Qed.    
  
End module_typing_det.

Definition exp_default := MED_func (Mk_funcidx 0).

Definition ext_func_addrs := (map (fun x => match x with | Mk_funcidx i => i end)) \o ext_funcs.
Definition ext_tab_addrs := (map (fun x => match x with | Mk_tableidx i => i end)) \o ext_tabs.
Definition ext_mem_addrs := (map (fun x => match x with | Mk_memidx i => i end)) \o ext_mems.
Definition ext_glob_addrs := (map (fun x => match x with | Mk_globalidx i => i end)) \o ext_globs.

Lemma ext_func_addrs_aux l:
  ext_func_addrs l = map (fun '(Mk_funcidx i) => i) (ext_funcs l).
Proof.
  by [].
Qed.

Lemma ext_tab_addrs_aux l:
  ext_tab_addrs l = map (fun '(Mk_tableidx i) => i) (ext_tabs l).
Proof.
  by [].
Qed.

Lemma ext_mem_addrs_aux l:
  ext_mem_addrs l = map (fun '(Mk_memidx i) => i) (ext_mems l).
Proof.
  by [].
Qed.

Lemma ext_glob_addrs_aux l:
  ext_glob_addrs l = map (fun '(Mk_globalidx i) => i) (ext_globs l).
Proof.
  by [].
Qed.

(* Getting the count of each type of imports from a module. This is to calculate the correct shift for indices of the exports in the Wasm store later. *)
Definition get_import_func_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_func id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).

Definition get_import_table_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_table id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).
Definition get_import_mem_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_mem id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).
Definition get_import_global_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_global id => Some id
                                                                   | _ => None
                                                                      end) m.(mod_imports)).


Lemma ext_funcs_lookup_exist (modexps: list module_export_desc) n fn:
  (ext_funcs modexps) !! n = Some fn ->
  exists k, modexps !! k = Some (MED_func fn).
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

Lemma ext_tabs_lookup_exist (modexps: list module_export_desc) n tn:
  (ext_tabs modexps) !! n = Some tn ->
  exists k, modexps !! k = Some (MED_table tn).
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

Lemma ext_mems_lookup_exist (modexps: list module_export_desc) n mn:
  (ext_mems modexps) !! n = Some mn ->
  exists k, modexps !! k = Some (MED_mem mn).
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

Lemma ext_globs_lookup_exist (modexps: list module_export_desc) n fn:
  (ext_globs modexps) !! n = Some fn ->
  exists k, modexps !! k = Some (MED_global fn).
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

Lemma ext_funcs_lookup_exist_inv (modexps: list module_export_desc) n idx:
  modexps !! n = Some (MED_func idx) ->
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

Lemma ext_tabs_lookup_exist_inv (modexps: list module_export_desc) n idx:
  modexps !! n = Some (MED_table idx) ->
  exists k, ((ext_tabs modexps) !! k = Some idx).
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

Lemma ext_mems_lookup_exist_inv (modexps: list module_export_desc) n idx:
  modexps !! n = Some (MED_mem idx) ->
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

Lemma ext_globs_lookup_exist_inv (modexps: list module_export_desc) n idx:
  modexps !! n = Some (MED_global idx) ->
  exists k, ((ext_globs modexps) !! k = Some idx).
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
  
Variable host_function: eqType.

Local Definition function_closure := function_closure host_function.
Local Definition store_record := store_record host_function.

Local Definition alloc_Xs := @alloc_Xs host_function.
Local Definition alloc_funcs := alloc_funcs host_function.
Local Definition alloc_tabs := alloc_tabs host_function.
Local Definition alloc_mems := alloc_mems host_function.
Local Definition alloc_globs := alloc_globs host_function.
Local Definition alloc_module := alloc_module host_function.

Local Definition init_tab := init_tab host_function.
Local Definition init_tabs := init_tabs host_function.
Local Definition init_mem := init_mem host_function.
Local Definition init_mems := init_mems host_function.

Variable host_instance: host host_function.

Local Definition reduce := @reduce host_function host_instance.

Definition gen_func_instance mf inst : function_closure :=
  let ft := List.nth match modfunc_type mf with
                | Mk_typeidx n => n
                end (inst_types inst) (Tf [::] [::]) in
  FC_func_native inst ft (modfunc_locals mf) (modfunc_body mf).
                
(* Proving relations between stores obtained by alloc_Xs *)
Lemma alloc_Xs_IP {A B: Type} (f: store_record -> A -> store_record * B) s_init xs s_end ys (R: store_record -> store_record -> list A -> list B -> Prop) :
  alloc_Xs _ _ f s_init xs = (s_end, ys) ->
  (R s_init s_init [::] [::]) ->
  (forall s s0 x xs' ys' s' y,
    (s, y) = f s' x ->
    R s0 s' xs' ys' ->
    R s0 s (xs' ++ [::x]) (ys' ++ [::y])) ->
  R s_init s_end xs ys.
Proof.
  move: s_init s_end ys.
  induction xs using rev_ind => //=; move => s_init s_end ys Hallocxs Hinit IH; simpl in *.
  - unfold alloc_Xs, instantiation_spec.alloc_Xs in Hallocxs.
    simpl in Hallocxs.
    by injection Hallocxs as ->; subst.
  - unfold alloc_Xs, instantiation_spec.alloc_Xs in Hallocxs.
    rewrite fold_left_app in Hallocxs.
    simpl in Hallocxs.
    
    remember (fold_left _ xs _) as fold_res.
    destruct fold_res as [s0 ys0].
    remember (f s0 x) as sf.
    destruct sf as [s' y'].
    injection Hallocxs as ->; subst.
    eapply IH; eauto.
    apply IHxs; eauto.
    unfold alloc_Xs, instantiation_spec.alloc_Xs.
    by rewrite <- Heqfold_res.
Qed.

Lemma alloc_func_gen_index modfuncs ws inst ws' l:
  alloc_funcs ws modfuncs inst = (ws', l) ->
  map (fun x => match x with | Mk_funcidx i => i end) l = gen_index (length (s_funcs ws)) (length modfuncs) /\
  ws'.(s_funcs) = ws.(s_funcs) ++ map (fun mf => gen_func_instance mf inst) modfuncs /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  unfold alloc_funcs, instantiation_spec.alloc_funcs.
  move => Halloc.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => map _ ys = gen_index _ _ /\ _))
    in Halloc; eauto => //=.
  - unfold gen_index, imap => /=.
    repeat split.
    by rewrite app_nil_r.
  - move => s s0 x xs' ys' s' y Hallocx [Hys [Hcomp [? [? ?]]]].
    unfold alloc_func, add_func in Hallocx; injection Hallocx as ->; subst => /=.
    rewrite app_length map_app gen_index_extend Hys Hcomp => /=.
    repeat split => //=.
    + by rewrite app_length map_length.
    + rewrite map_app.
      unfold gen_func_instance => /=.
      by rewrite app_assoc.
Qed.

Lemma alloc_tab_gen_index modtabtypes ws ws' l:
  alloc_tabs ws modtabtypes = (ws', l) ->
  map (fun x => match x with | Mk_tableidx i => i end) l = gen_index (length (s_tables ws)) (length modtabtypes) /\
  ws'.(s_tables) = ws.(s_tables) ++ map (fun '{| tt_limits := {| lim_min := min; lim_max := maxo |} |} => {| table_data := repeat None (ssrnat.nat_of_bin min); table_max_opt := maxo |}) modtabtypes /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  unfold alloc_tabs, instantiation_spec.alloc_tabs.
  move => Halloc.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => map _ ys = gen_index _ _ /\ _))
    in Halloc; eauto => //=.
  - unfold gen_index, imap => /=.
    repeat split.
    by rewrite app_nil_r.
  - move => s s0 x xs' ys' s' y Hallocx [Hys [Hcomp [? [? ?]]]].
    unfold alloc_tab, add_table in Hallocx. destruct x as [[lim_min lim_max]]. injection Hallocx as ->; subst => /=.
    rewrite app_length map_app gen_index_extend Hys Hcomp => /=.
    repeat split => //=.
    + by rewrite app_length map_length.
    + rewrite map_app.
      by rewrite app_assoc.
Qed.

Lemma alloc_mem_gen_index modmemtypes ws ws' l:
  alloc_mems ws modmemtypes = (ws', l) ->
  map (fun x => match x with | Mk_memidx i => i end) l = gen_index (length (s_mems ws)) (length modmemtypes) /\
  ws'.(s_mems) = ws.(s_mems) ++ map (fun '{| lim_min := min; lim_max := maxo |} => {| mem_data := memory_list.mem_make #00%byte (page_size * min)%N; mem_max_opt := maxo |}) modmemtypes /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  unfold alloc_mems, instantiation_spec.alloc_mems.
  move => Halloc.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => map _ ys = gen_index _ _ /\ _))
    in Halloc; eauto => //=.
  - unfold gen_index, imap => /=.
    repeat split.
    by rewrite app_nil_r.
  - move => s s0 x xs' ys' s' y Hallocx [Hys [Hcomp [? [? ?]]]].
    unfold alloc_mem, add_mem in Hallocx. destruct x as [memid]. injection Hallocx as ->; subst => /=.
    rewrite app_length map_app gen_index_extend Hys Hcomp => /=.
    repeat split => //=.
    + by rewrite app_length map_length.
    + rewrite map_app.
      by rewrite app_assoc.
Qed.

Lemma combine_snoc {T1 T2: Type}: forall (l1: list T1) (l2: list T2) lc x,
  lc ++ [::x] = combine l1 l2 ->
  length l1 = length l2 ->
  exists l1' l2' a b,
    (l1 = l1' ++ [::a] /\ l2 = l2' ++ [::b] /\ lc = combine l1' l2' /\ x = (a, b)).
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

Lemma alloc_glob_gen_index modglobs ws g_inits ws' l:
  length g_inits = length modglobs ->
  alloc_globs ws modglobs g_inits = (ws', l) ->
  map (fun x => match x with | Mk_globalidx i => i end) l = gen_index (length (s_globals ws)) (length modglobs) /\
  ws'.(s_globals) = ws.(s_globals) ++ map (fun '({| modglob_type := gt; modglob_init := ge |}, v) => {| g_mut := gt.(tg_mut); g_val := v |} ) (combine modglobs g_inits) /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems).
Proof.
  unfold alloc_globs, instantiation_spec.alloc_globs.
  move => Hgloblen Halloc.
  move : Hgloblen.
  remember (combine modglobs g_inits) as comb.
  move : Heqcomb.
  move : modglobs g_inits.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => forall globs g_inits, xs = combine globs g_inits -> length g_inits = length globs -> map _ ys = gen_index _ _ /\ _))
    in Halloc; eauto => //.
  - unfold gen_index, imap => /=.
    move => modglobs g_inits Hcomb Hgloblen.
    destruct g_inits, modglobs => //=.
    repeat split.
    by rewrite app_nil_r.
  - move => s s0 x xs' ys' s' y Hallocx Hind modglobs g_inits Hcomb Hgloblen.
    apply combine_snoc in Hcomb; last by lias.
    destruct Hcomb as [modglobs' [g_inits' [g [v [-> [-> [-> ->]]]]]]].
    destruct (Hind modglobs' g_inits') as [Hys [Hcomp [? [? ?]]]] => //; clear Hind.
    { repeat rewrite app_length in Hgloblen; simpl in Hgloblen. by lias. }
    unfold alloc_glob, add_glob in Hallocx. injection Hallocx as ->; subst => /=.
    rewrite app_length map_app gen_index_extend Hys Hcomp => /=.
    repeat split => //=.
    + rewrite app_length map_length combine_length.
      do 3 f_equal.
      repeat rewrite app_length in Hgloblen; simpl in Hgloblen.
      by lias.
    + rewrite map_app.
      rewrite app_assoc => /=.
      by destruct g.
Qed.

Lemma init_tabs_preserve ws inst e_inits melem ws':
  init_tabs ws inst e_inits melem = ws' ->
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  move => Hinit.
  unfold init_tabs, instantiation_spec.init_tabs in Hinit.
  rewrite - Hinit.
  apply fold_left_preserve => //.
  move => x [n me] Heq.
  destruct ws, x.
  simpl in *.
  destruct Heq as [-> [-> ->]].
  unfold init_tab, instantiation_spec.init_tab => /=.
  by destruct (nth _ _) eqn:Hl => /=.
Qed.

Lemma init_mems_preserve ws inst d_inits mdata ws':
  init_mems ws inst d_inits mdata = ws' ->
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  move => Hinit.
  unfold init_mems, instantiation_spec.init_mems in Hinit.
  rewrite - Hinit.
  apply fold_left_preserve => //.
  move => x [n md] Heq.
  destruct ws, x.
  simpl in *.
  destruct Heq as [-> [-> ->]].
  by unfold init_mem, instantiation_spec.init_mem => /=.
Qed.

Lemma mod_imps_len_t m t_imps t_exps:
  module_typing m t_imps t_exps ->
  get_import_func_count m = length (ext_t_funcs t_imps) /\
  get_import_table_count m = length (ext_t_tabs t_imps) /\
  get_import_mem_count m = length (ext_t_mems t_imps) /\
  get_import_global_count m = length (ext_t_globs t_imps).
Proof.
  unfold get_import_func_count, get_import_table_count, get_import_mem_count, get_import_global_count.
  unfold module_typing.
  move => Hmt.
  destruct m.
  destruct Hmt as [fts [gts [? [? [? [? [? [? [? [Himptype ?]]]]]]]]]].
  simpl in *.
  clear - mod_imports Himptype.
  move : Himptype.
  move : t_imps fts gts.
  induction mod_imports; move => t_imps fts gts Himptype => //=.
  - apply Forall2_length in Himptype.
    by destruct t_imps => //=.
  - destruct t_imps; first by apply Forall2_length in Himptype.
    simpl in *.
    inversion Himptype; subst; clear Himptype.
    unfold module_import_typing in H2.
    destruct a, imp_desc => /=; simpl in H2; destruct e => //.
    all:
      try by (move/andP in H2;
      destruct H2 as [Hlen Hnth];
      move/eqP in Hnth; subst;
      simpl;
      apply IHmod_imports in H4 as [? [? [? ?]]] => //;
      repeat split => //;
      f_equal).
    move/eqP in H2; subst.
    simpl.
    apply IHmod_imports in H4 as [? [? [? ?]]] => //.
    repeat split => //.
    by f_equal.
Qed.

Section Instantiation_det.

Lemma bet_const_exprs_len tc es t1 t2:
  const_exprs tc es ->
  be_typing tc es (Tf t1 t2) ->
  length t2 = length es + length t1.
Proof.
  move: t1 t2.
  induction es; move => t1 t2 Hconst Hbet; destruct t2 => //=.
  { apply empty_typing in Hbet. by subst. }
  { apply empty_typing in Hbet. by subst. }
  { rewrite <- cat1s in Hbet.
    invert_be_typing; subst.
    destruct ts1_comp, ts3_comp => //; clear H2_comp.
    simpl in Hconst.
    move/andP in Hconst.
    destruct Hconst as [Hconst Hconsts].
    apply IHes in H4_comp => //.
    destruct es, ts4_comp => //=.
    unfold const_expr in Hconst.
    destruct a => //; invert_be_typing; by destruct ts2_comp.
  }
  { rewrite <- cat1s in Hbet.
    apply composition_typing in Hbet.
    destruct Hbet as [ts [t1s [t2s [t3s [-> [Heqt2 [Hbet1 Hbet2]]]]]]].
    simpl in Hconst.
    move/andP in Hconst.
    destruct Hconst as [Hconst Hconsts].
    eapply IHes in Hbet2 => //.
    assert (length t2 + 1 = length ts + length t2s) as Hlent2.
    { rewrite - app_length - cat_app - Heqt2.
      by lias.
    }
    unfold const_expr in Hconst.
    destruct a => //; invert_be_typing; rewrite -> app_length in *; simpl in *; by lias.
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

Local Definition host_state := host_state host_instance.

Lemma const_no_reduce (hs hs': host_state) s f v s' f' e':
  reduce hs s f [::AI_basic (BI_const v)] hs' s' f' e' ->
  False.
Proof.
  move => Hred.
  dependent induction Hred; subst; try by repeat destruct vcs => //.
  { inversion H; subst; clear H; try by repeat destruct vs => //.
    destruct lh as [vs ? | ? vs]; simpl in H1; by do 2 destruct vs => //=.
  }
  { destruct lh as [vs ? | ? vs] => //=; simpl in H; last by do 2 destruct vs => //=.
    destruct vs => //=; last first.
    { destruct vs, es, l => //=.
      by apply reduce_not_nil in Hred.
    }
    destruct es => //=; first by apply reduce_not_nil in Hred.
    destruct es, l => //=.
    simpl in *.
    inversion H; subst; clear H.
    by eapply IHHred.
  }
Qed.

Local Definition reduce_trans := @reduce_trans host_function host_instance.

Lemma reduce_trans_const hs1 s1 f1 v1 hs2 s2 f2 v2:
  reduce_trans (hs1, s1, f1, [::AI_basic (BI_const v1)]) (hs2, s2, f2, [::AI_basic (BI_const v2)]) ->
  v1 = v2.
Proof.
  move => Hred.
  unfold reduce_trans in Hred.
  apply Operators_Properties.clos_rt_rt1n_iff in Hred.
  inversion Hred => //.
  unfold reduce_tuple in H.
  destruct y as [[[??]?]?].
  by apply const_no_reduce in H.
Qed.

Lemma reduce_get_global hs s f hs' s' f' i e:
  reduce hs s f [::AI_basic (BI_get_global i)] hs' s' f' e ->
  exists v, sglob_val s (f_inst f) i = Some v /\ e = [::AI_basic (BI_const v)].
Proof.
  move => Hred.
  dependent induction Hred; subst; try by repeat destruct vcs => //.
  { inversion H; subst; clear H; try by repeat destruct vs => //.
    destruct lh as [vs ? | ? vs]; simpl in H1; by do 2 destruct vs => //=.
  }
  { by exists v. }
  { destruct lh as [vs ? | ? vs] => //=; simpl in H; last by do 2 destruct vs => //=.
    destruct vs => //=.
    destruct es => //=; first by apply reduce_not_nil in Hred.
    destruct es, l => //=.
    simpl in *.
    inversion H; subst; clear H.
    rewrite cats0.
    by eapply IHHred.
  }
Qed.
    
Lemma reduce_trans_get_global hs s f hs' s' f' i v:
  reduce_trans (hs, s, f, [::AI_basic (BI_get_global i)]) (hs', s', f', [::AI_basic (BI_const v)]) ->
  sglob_val s (f_inst f) i = Some v.
Proof.
  move => Hred.
  unfold reduce_trans, opsem.reduce_trans in *.
  apply Operators_Properties.clos_rt_rt1n_iff in Hred.
  inversion Hred; subst; clear Hred.
  destruct y as [[[??]?]?].
  unfold reduce_tuple, opsem.reduce_tuple in H.
  apply reduce_get_global in H.
  destruct H as [v' [Hsgv ->]].
  inversion H0; subst; clear H0 => //.
  unfold reduce_tuple, opsem.reduce_tuple in H.
  destruct y as [[[??]?]?].
  by apply const_no_reduce in H.
Qed.

Lemma modglobs_const: forall tc modglobs gt,
  Forall2 (module_glob_typing tc) modglobs gt ->
  Forall (fun g => exists e, g.(modglob_init) = [::e] /\ const_expr tc e) modglobs.
Proof.
  move => tc modglobs. move: tc.
  induction modglobs; move => tc gt Hall2; destruct gt => //=.
  - by apply Forall2_length in Hall2.
  - inversion Hall2 as [ | ???? Ha Hall2']; subst.
    constructor.
    + unfold module_glob_typing in Ha.
      destruct a => /=; destruct Ha as [Hconst [-> Hbet]].
      by apply const_exprs_impl in Hbet; eauto.
    + by eapply IHmodglobs; eauto.
Qed.

Local Definition instantiate_globals := instantiate_globals host_function host_instance.
Local Definition instantiate_elem := instantiate_elem host_function host_instance.
Local Definition instantiate_data := instantiate_data host_function host_instance.

Lemma module_glob_init_det m v_imps t_imps inst hs1 s1 hs2 s2 gi1 gi2:
  module_typing m v_imps t_imps ->
  instantiate_globals inst hs1 s1 m gi1 ->
  instantiate_globals inst hs2 s2 m gi2 ->
  (forall i, i < length (ext_t_globs v_imps) -> sglob_val s1 inst i = sglob_val s2 inst i) ->
  gi1 = gi2.
Proof.
  move => Hmt Hgi1 Hgi2 Hsgveq.
  unfold module_typing in Hmt.
  unfold instantiate_globals, instantiation_spec.instantiate_globals in *.
  destruct m; simpl in *.
  destruct Hmt as [fts [gts [_ [_ [_ [Hmgt _]]]]]].
  assert (length gi1 = length gi2) as Hlen; first by (apply Forall2_length in Hgi1; apply Forall2_length in Hgi2; rewrite Hgi1 in Hgi2).

  remember (Build_t_context _ _ _ _ _ _ _ _) as tc.
  apply modglobs_const in Hmgt.

  eapply Forall2_function_eq_cond; eauto => //.
  move => x y z Hconst Heq1 Heq2.
  simpl in *.

  destruct x as [gt gi]; simpl in *.
  destruct Hconst as [e [-> Hconst]]; simpl in *.
  unfold const_expr in Hconst.
  rewrite Heqtc in Hconst; simpl in Hconst.
  destruct e; simpl in * => //; remove_bools_options.
  { apply reduce_trans_get_global in Heq1.
    apply reduce_trans_get_global in Heq2.
    specialize (Hsgveq i).
    rewrite Hsgveq in Heq1; last by move/ssrnat.ltP in H; lias.
    rewrite Heq1 in Heq2.
    by injection Heq2.
  }
  { apply reduce_trans_const in Heq1.
    apply reduce_trans_const in Heq2.
    by subst.
  }
Qed.

Lemma module_elem_init_det m v_imps t_imps inst hs1 hs2 s eo1 eo2:
  module_typing m v_imps t_imps ->
  instantiate_elem inst hs1 s m eo1 ->
  instantiate_elem inst hs2 s m eo2 ->
  eo1 = eo2.
Proof.
  move => Hmt Heo1 Heo2.
  unfold module_typing in Hmt.
  unfold instantiate_elem, instantiation_spec.instantiate_elem in *.
  destruct m; simpl in *.
  destruct Hmt as [fts [gts [_ [_ [_ [_ [Hmet _]]]]]]].
  assert (length eo1 = length eo2) as Hlen; first by (apply Forall2_length in Heo1; apply Forall2_length in Heo2; rewrite Heo1 in Heo2).

  eapply Forall2_function_eq_cond; eauto => //.
  move => x y z Hconst Heq1 Heq2.
  simpl in *.

  destruct x as [[et] eo ei]; simpl in *.
  destruct Hconst as [Hconst [Hbet [Hilen Halllen]]].
  apply const_exprs_impl in Hbet => //; clear Hconst.
  destruct Hbet as [e [-> Hconst]].
  unfold const_expr in Hconst; simpl in Hconst.
  destruct e; simpl in * => //; remove_bools_options.
  { apply reduce_trans_get_global in Heq1.
    apply reduce_trans_get_global in Heq2.
    rewrite Heq1 in Heq2.
    by injection Heq2.
  }
  { apply reduce_trans_const in Heq1.
    apply reduce_trans_const in Heq2.
    rewrite Heq1 in Heq2.
    by injection Heq2.
  }
Qed.

Lemma module_data_init_det m v_imps t_imps inst hs1 hs2 s do1 do2:
  module_typing m v_imps t_imps ->
  instantiate_data inst hs1 s m do1 ->
  instantiate_data inst hs2 s m do2 ->
  do1 = do2.
Proof.
  move => Hmt Hdo1 Hdo2.
  unfold module_typing in Hmt.
  unfold instantiate_data, instantiation_spec.instantiate_data in *.
  destruct m; simpl in *.
  destruct Hmt as [fts [gts [_ [_ [_ [_ [_ [Hmdt _]]]]]]]].
  assert (length do1 = length do2) as Hlen; first by (apply Forall2_length in Hdo1; apply Forall2_length in Hdo2; rewrite Hdo1 in Hdo2).

  eapply Forall2_function_eq_cond; eauto => //.
  move => x y z Hconst Heq1 Heq2.
  simpl in *.

  destruct x as [[dm] d_o di]; simpl in *.
  destruct Hconst as [Hconst [Hbet Hilen]].
  apply const_exprs_impl in Hbet => //; clear Hconst.
  destruct Hbet as [e [-> Hconst]].
  unfold const_expr in Hconst; simpl in Hconst.
  destruct e; simpl in * => //; remove_bools_options.
  { apply reduce_trans_get_global in Heq1.
    apply reduce_trans_get_global in Heq2.
    rewrite Heq1 in Heq2.
    by injection Heq2.
  }
  { apply reduce_trans_const in Heq1.
    apply reduce_trans_const in Heq2.
    rewrite Heq1 in Heq2.
    by injection Heq2.
  }
Qed.

Lemma vt_imps_comp_len hs s (v_imps: list v_ext) t_imps:
  Forall2 (external_typing hs s) v_imps t_imps ->
  (length (ext_funcs v_imps) = length (ext_t_funcs t_imps) /\
    length (ext_tabs v_imps) = length (ext_t_tabs t_imps) /\
    length (ext_mems v_imps) = length (ext_t_mems t_imps) /\
    length (ext_globs v_imps) = length (ext_t_globs t_imps)).
Proof.
  move: t_imps.
  induction v_imps; move => t_imps Hexttype; destruct t_imps; try by apply Forall2_length in Hexttype.
  inversion Hexttype; subst; clear Hexttype.
  apply IHv_imps in H4.
  destruct H4 as [Hft [Htt [Hmt Hgt]]].
  destruct a; inversion H2; subst; clear H2 => //=; by repeat split; lias.
Qed.

Local Definition external_typing := external_typing host_function.

Lemma alloc_module_det hs1 hs2 s m v_imps t_imps t_exps g_inits g_inits' s_res1 s_res2 inst inst' exps exps':
  module_typing m t_imps t_exps ->
  Forall2 (external_typing s) v_imps t_imps ->
  length g_inits = length (mod_globals m) -> 
  length g_inits' = length (mod_globals m) -> 
  alloc_module s m v_imps g_inits (s_res1, inst, exps) ->
  alloc_module s m v_imps g_inits' (s_res2, inst', exps') ->
  instantiate_globals inst hs1 s_res1 m g_inits ->
  instantiate_globals inst' hs2 s_res2 m g_inits' ->
  (inst, exps) = (inst', exps') /\
  g_inits = g_inits' /\
  (s_res1 = s_res2).
Proof.
  move => Hmt Hexttype Hglen1 Hglen2 Ham1 Ham2 Hinitg1 Hinitg2.
  unfold alloc_module, instantiation_spec.alloc_module in *.
  remember (instantiation_spec.alloc_funcs host_function s (mod_funcs m) inst) as res_f.
  destruct res_f as [s0 idf].
  remember (instantiation_spec.alloc_tabs host_function s0 (map modtab_type (mod_tables m))) as res_t.
  destruct res_t as [s1 idt].
  remember (instantiation_spec.alloc_mems host_function s1 (mod_mems m)) as res_m.
  destruct res_m as [s2 idm].
  remember (instantiation_spec.alloc_globs host_function s2 (mod_globals m) g_inits) as res_g.
  destruct res_g as [s3 idg].
  symmetry in Heqres_f.
  symmetry in Heqres_t.
  symmetry in Heqres_m.
  symmetry in Heqres_g.
  apply alloc_func_gen_index in Heqres_f.
  apply alloc_tab_gen_index in Heqres_t.
  apply alloc_mem_gen_index in Heqres_m.
  apply alloc_glob_gen_index in Heqres_g => //.
  destruct s0, s1, s2, s3; simpl in *.
  destruct Heqres_f as [Hidf [-> [<- [<- <-]]]].
  destruct Heqres_t as [Hidt [-> [<- [<- <-]]]].
  destruct Heqres_m as [Hidm [-> [<- [<- <-]]]].
  destruct Heqres_g as [Hidg [-> [<- [<- <-]]]].
  
  remember (instantiation_spec.alloc_funcs host_function s (mod_funcs m) inst') as res_f'.
  destruct res_f' as [s0' idf'].
  remember (instantiation_spec.alloc_tabs host_function s0' (map modtab_type (mod_tables m))) as res_t'.
  destruct res_t' as [s1' idt'].
  remember (instantiation_spec.alloc_mems host_function s1' (mod_mems m)) as res_m'.
  destruct res_m' as [s2' idm'].
  remember (instantiation_spec.alloc_globs host_function s2' (mod_globals m) g_inits') as res_g'.
  destruct res_g' as [s3' idg'].
  symmetry in Heqres_f'.
  symmetry in Heqres_t'.
  symmetry in Heqres_m'.
  symmetry in Heqres_g'.
  apply alloc_func_gen_index in Heqres_f'.
  apply alloc_tab_gen_index in Heqres_t'.
  apply alloc_mem_gen_index in Heqres_m'.
  apply alloc_glob_gen_index in Heqres_g' => //.
  destruct s0', s1', s2', s3'; simpl in *.
  destruct Heqres_f' as [Hidf' [-> [<- [<- <-]]]].
  destruct Heqres_t' as [Hidt' [-> [<- [<- <-]]]].
  destruct Heqres_m' as [Hidm' [-> [<- [<- <-]]]].
  destruct Heqres_g' as [Hidg' [-> [<- [<- <-]]]].
  
  rewrite <- Hidf' in Hidf.

  assert (idf = idf').
  { clear - Hidf.
    move: Hidf.
    move: idf'.
    induction idf as [|fi ?]; move => idf'; destruct idf' => //=.
    move => H.
    destruct fi, f.
    inversion H; subst; clear H.
    f_equal.
    by apply IHidf.
  }
  subst.

  
  rewrite <- Hidt' in Hidt.

  assert (idt = idt').
  { clear - Hidt.
    move: Hidt.
    move: idt'.
    induction idt as [|ti ?]; move => idt'; destruct idt' => //=.
    move => H.
    destruct ti, t.
    inversion H; subst; clear H.
    f_equal.
    by apply IHidt.
  }
  subst.

  
  rewrite <- Hidm' in Hidm.

  assert (idm = idm').
  { clear - Hidm.
    move: Hidm.
    move: idm'.
    induction idm as [|mi ?]; move => idm'; destruct idm' => //=.
    move => H.
    destruct mi, m.
    inversion H; subst; clear H.
    f_equal.
    by apply IHidm.
  }
  subst.

  
  rewrite <- Hidg' in Hidg.

  assert (idg = idg').
  { clear - Hidg.
    move: Hidg.
    move: idg'.
    induction idg as [|gi ?]; move => idg'; destruct idg' => //=.
    move => H.
    destruct gi, g.
    inversion H; subst; clear H.
    f_equal.
    by apply IHidg.
  }
  subst.

  move/andP in Ham1; move/andP in Ham2.
  destruct Ham1 as [Ham1 Hsres1].
  destruct Ham2 as [Ham2 Hsres2].
  move/eqP in Hsres1; move/eqP in Hsres2; subst.
  move/andP in Ham1; move/andP in Ham2.
  destruct Ham1 as [Ham1 Hig1].
  destruct Ham2 as [Ham2 Hig2].
  move/eqP in Hig1.
  move/eqP in Hig2.
  move/andP in Ham1; move/andP in Ham2.
  destruct Ham1 as [Ham1 Him1].
  destruct Ham2 as [Ham2 Him2].
  move/eqP in Him1.
  move/eqP in Him2.
  move/andP in Ham1; move/andP in Ham2.
  destruct Ham1 as [Ham1 Hit1].
  destruct Ham2 as [Ham2 Hit2].
  move/eqP in Hit1.
  move/eqP in Hit2.
  move/andP in Ham1; move/andP in Ham2.
  destruct Ham1 as [Ham1 Hif1].
  destruct Ham2 as [Ham2 Hif2].
  move/eqP in Hif1.
  move/eqP in Hif2.
  move/andP in Ham1; move/andP in Ham2.
  destruct Ham1 as [Ham1 Hitype1].
  destruct Ham2 as [Ham2 Hitype2].
  move/eqP in Hitype1.
  move/eqP in Hitype2.
  rewrite <- Hif2 in Hif1.
  rewrite <- Hit2 in Hit1.
  rewrite <- Him2 in Him1.
  rewrite <- Hig2 in Hig1.
  rewrite <- Hitype2 in Hitype1.
  destruct inst, inst'.
  simpl in *.
  subst.
  split => //.

  move/eqP in Ham1; move/eqP in Ham2.
  assert (g_inits = g_inits') as Heqgi.
  {
    eapply module_glob_init_det; eauto => //.
    move => i Hilen.
    unfold sglob_val, sglob, sglob_ind => /=.
    repeat rewrite nth_error_lookup.
    repeat rewrite map_map.
    repeat rewrite list_lookup_map.
    remember ((ext_globs v_imps ++ idg') !! i) as gi.
    specialize (vt_imps_comp_len _ _ _ _ Hexttype) as Hcomplen.
    destruct Hcomplen as [_ [_ [_ Hglen]]].
    rewrite <- Hglen in Hilen.
    rewrite nth_error_app1 in Heqgi => //.
    destruct gi as [g |]; symmetry in Heqgi; last by rewrite -> nth_error_None in Heqgi; lias.
    destruct g.
    assert (n < length (s_globals s)) as Hnlen.
    { unfold module_typing in Hmt.
      destruct m; simpl in *.
      destruct Hmt as [fts [gts [_ [_ [_ [_ [_ [_ [_ [Hit _]]]]]]]]]].
      apply ext_globs_lookup_exist in Heqgi as [k Hvi].
      eapply Forall2_lookup in Hexttype; eauto.
      destruct Hexttype as [y [Hnth Hexttype]].
      inversion Hexttype; subst; clear Hexttype.
      by move/ssrnat.ltP in H0.
    }
    subst s_res1 s_res2 => /=.
    rewrite Coqlib.list_map_nth => /=.
    rewrite nth_error_app1 => //.
    rewrite Heqgi => /=.
    by repeat rewrite nth_error_app1 => //.
  }
  split => //; last by subst.
Qed.

Local Definition instantiate := instantiate host_function host_instance.

Lemma instantiate_det s m vimps res res':
  instantiate s m vimps res ->
  instantiate s m vimps res' ->
  res = res'.
Proof.
  move => Hinst1 Hinst2.
  destruct res as [[[s1 inst1] exp1] start1].
  destruct res' as [[[s2 inst2] exp2] start2].
  unfold instantiate, instantiation_spec.instantiate in *.
  destruct Hinst1 as (t_imps1 & t_exps1 & hs1 & ws1 & g_inits1 & e_offs1 & d_offs1 & Hmodtype1 & Hexttype1 & Hallocmodule1 & Hinstglob1 & Hinstelem1 & Hinstdata1 & Hcbelem1 & Hcbdata1 & Hcstart1 & Hws1).
  destruct Hinst2 as [t_imps2 [t_exps2 [hs2 [ws2 [g_inits2 [e_offs2 [d_offs2 [Hmodtype2 [Hexttype2 [Hallocmodule2 [Hinstglob2 [Hinstelem2 [Hinstdata2 [Hcbelem2 [Hcbdata2 [Hcstart2 Hws2]]]]]]]]]]]]]]]].

  specialize (module_typing_det _ _ _ _ _ Hmodtype1 Hmodtype2) as Hvteq.
  inversion Hvteq; subst; clear Hvteq.

  (* Instance, alloc_module store, and exports *)
  eapply alloc_module_det in Hallocmodule1; eauto => //.
  3: { by apply Forall2_length in Hinstglob1. }
  2: { by apply Forall2_length in Hinstglob2. }

  destruct Hallocmodule1 as [Hieeq [Hgieq Hwseq]].
  inversion Hieeq; subst; clear Hieeq.

  (* Start *)
  unfold check_start in *.
  move/eqP in Hcstart1; move/eqP in Hcstart2.
  rewrite Hcstart2 in Hcstart1; subst.
  repeat f_equal.

  (* Final store *)
  assert (e_offs1 = e_offs2) as Heoffeq.
  { by eapply module_elem_init_det; eauto. }
  
  assert (d_offs1 = d_offs2) as Hdoffeq.
  { by eapply module_data_init_det; eauto. }

  subst.
  move/eqP in Hws1.
  move/eqP in Hws2.
  by subst.
Qed.
  
End Instantiation_det.

End Host.
