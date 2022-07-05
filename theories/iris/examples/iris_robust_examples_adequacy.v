From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
Require Import Eqdep_dec.
Require Import iris_robust_examples.

Class adv_module_record :=
  { adv_module : module;
    no_start : mod_start adv_module = None;
    restrictions : module_restrictions adv_module;
    elem_bounds : module_elem_bound_check_gmap ∅ [] adv_module;
    data_bounds : module_data_bound_check_gmap ∅ [] adv_module
  }.  

Section adequacy.
  Context (Σ: gFunctors).
  Context {inv_preg: invGpreS Σ}.
  Context {na_invg: na_invG Σ}.
  Context {func_preg: gen_heapGpreS N function_closure Σ}.
  Context {tab_preg: gen_heapGpreS (N*N) funcelem Σ}.
  Context {tabsize_preg: gen_heapGpreS N nat Σ}.
  Context {tablimits_preg: gen_heapGpreS N (option N) Σ}.
  Context {mem_preg: gen_heapGpreS (N*N) byte Σ}.
  Context {memsize_preg: gen_heapGpreS N N Σ}.
  Context {memlimit_preg: gen_heapGpreS N (option N) Σ}.
  Context {glob_preg: gen_heapGpreS N global Σ}.
  Context {locs_preg: gen_heapGpreS unit frame Σ}.
  Context {vis_preg: gen_heapGpreS N module_export Σ}.
  Context {ms_preg: gen_heapGpreS N module Σ}.
  Context {has_preg: gen_heapGpreS N host_action Σ}.


  Definition S := Build_store_record [] [] [] [ {| g_mut := MUT_mut; g_val := xx 0 |} ].
  Definition V (vs : module_export) : vi_store :=
    <[0%N:=vs]> (<[1%N:={| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |} ]> ∅).
  Definition M adv_module := [adv_module; lse_module].

  
  
  Lemma ex_adequacy `{Hadv:adv_module_record} he' S' V' M' HA' F vs :
    module_typing adv_module [] lse_func_impts ->
    rtc erased_step (([(adv_lse_instantiate 0,[])],
                      (S,(V vs),(M adv_module),[],empty_frame)) : cfg wasm_host_lang)
        ([he'], (S',V', M', HA', F)) →
    (∀ v, to_val he' = Some v ->
          v = trapHV ∨ v = immHV [xx 42] ).
  Proof.
    intros Hmodtyping Hstep.
    pose proof (wp_adequacy Σ wasm_host_lang NotStuck (adv_lse_instantiate 0,[])
                            (S,(V vs),(M adv_module),[],empty_frame)
    (λ v, v = trapHV ∨ v = immHV [xx 42])).
    simpl in H.
    
    eassert _.
    { apply H.
      iIntros (Hinv κs).
      iMod (gen_heap_init (∅:gmap N function_closure)) as (func_heapg) "[Hfunc_ctx _]".
      iMod (gen_heap_init (∅:gmap (N*N) funcelem)) as (tab_heapg) "[Htab_ctx _]".
      iMod (gen_heap_init (∅:gmap N nat)) as (tabsize_heapg) "[Htabsize_ctx _]".
      iMod (@gen_heap_init _ _ _ _ _ tablimits_preg (∅:gmap N (option N))) as (tablimit_heapg) "[Htablimit_ctx _]".
      iMod (gen_heap_init (∅:gmap (N*N) byte)) as (mem_heapg) "[Hmem_ctx _]".
      iMod (gen_heap_init (∅:gmap N N)) as (memsize_heapg) "[Hmemsize_ctx _]".
      iMod (@gen_heap_init _ _ _ _ _ memlimit_preg (∅:gmap N (option N))) as (memlimit_heapg) "[Hmemlimit_ctx _]".
      iMod (gen_heap_init (∅:gmap N global)) as (global_heapg) "[Hglobal_ctx _]".
      
      apply (@gen_heapGpreS_heap) in locs_preg as frame_heapg.
      iMod (ghost_map_alloc (∅:gmap unit frame)) as (γframe) "[Hframe_ctx _]".
      apply (@gen_heapGpreS_heap) in vis_preg as vis_heapg.
      iMod (ghost_map_alloc (∅:gmap N module_export)) as (γvis) "[Hvis_ctx _]".
      apply (@gen_heapGpreS_heap) in ms_preg as ms_heapg.
      iMod (ghost_map_alloc (∅:gmap N module)) as (γms) "[Hms_ctx _]".
      apply (@gen_heapGpreS_heap) in has_preg as has_heapg.
      iMod (ghost_map_alloc (∅:gmap N host_action)) as (γhas) "[Hhas_ctx _]".

      iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".
      pose wasmg := WasmG Σ Hinv func_heapg tab_heapg tabsize_heapg
                          tablimit_heapg mem_heapg memsize_heapg memlimit_heapg
                          global_heapg frame_heapg γframe.
      pose visgg := HVisG Σ vis_heapg γvis.
      pose msgg := HMsG Σ ms_heapg γms.
      pose hasgg := HAsG Σ has_heapg γhas.
      pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
      assert (typeof (xx 0) = T_i32) as Hwret;[auto|].
      pose proof (instantiate_lse 0 Hmodtyping no_start restrictions elem_bounds data_bounds Hwret).

      iMod (ghost_map_insert tt empty_frame with "Hframe_ctx") as "[Hframe_ctx Hf]";[auto|].
      iMod (ghost_map_insert 1%N {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv1]";[auto|].
      iMod (ghost_map_insert 0%N vs with "Hvis_ctx") as "[Hvis_ctx Hv0]";[auto|].
      iMod (ghost_map_insert 1%N lse_module with "Hms_ctx") as "[Hms_ctx Hm1]";[auto|].
      iMod (ghost_map_insert 0%N adv_module with "Hms_ctx") as "[Hms_ctx Hm0]";[auto|].
      iMod (gen_heap_alloc _ (N.of_nat 0) {| g_mut := MUT_mut; g_val := xx 0 |} with "Hglobal_ctx") as "[Hglobal_ctx [Hg _]]";[auto|].

      iDestruct (instantiate_lse $! (λ v, ⌜v = trapHV ∨ v = immHV [xx 42]⌝%I)
                  with "[$Hg $Hm1 $Hm0 $Hna $Hf Hv0 Hv1]") as "HH";
        [eauto|apply no_start|apply restrictions|apply elem_bounds|apply data_bounds|eauto..].
      { iSplitL "Hv1";[iExists _;iFrame|]. iExists _;iFrame. }
      iDestruct ("HH" with "[]") as "HH";[auto|].
      iModIntro.
      iExists _,_. iFrame "HH". iFrame.
    }
    intros v Hval.
    destruct X. eapply adequate_result with (t2 := []).
    apply of_to_val in Hval as <-. eauto.
  Qed.
          
End adequacy.

Theorem lse_adequacy `{adv_module_record}
        he' S' V' M' HA' F vs :
  module_typing adv_module [] lse_func_impts ->
  rtc erased_step (([(adv_lse_instantiate 0,[])],
                     (S,(V vs),(M adv_module),[],empty_frame)) : cfg wasm_host_lang)
      ([he'], (S',V', M', HA', F)) →
  (∀ v, to_val he' = Some v -> v = trapHV ∨ v = immHV [xx 42] ).
Proof.
  set (Σ := #[invΣ;
              na_invΣ;
              gen_heapΣ N function_closure;
              gen_heapΣ (N*N) funcelem;
              gen_heapΣ N nat;
              gen_heapΣ N (option N);
              gen_heapΣ (N*N) byte;
              gen_heapΣ N N;
              gen_heapΣ N (option N);
              gen_heapΣ N global;
              gen_heapΣ unit frame;
              gen_heapΣ N module_export;
              gen_heapΣ N module;
              gen_heapΣ N host_action
      ]).
  eapply (@ex_adequacy Σ); typeclasses eauto.
Qed.



