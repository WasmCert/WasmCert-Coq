(** Example of Iris usage **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
Require Export iris.
Set Default Proof Using "Type". (* what is this? *)

Record loc := { loc_car : Z }.
Instance loc_eq_decision : EqDecision loc.
Proof. solve_decision. Defined.

Instance loc_inhabited : Inhabited loc := populate {|loc_car := 0 |}.

Instance loc_countable : Countable loc.
Proof. by apply (inj_countable' loc_car (λ i, {| loc_car := i |})); intros []. Qed.

Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ p, {| loc_car := p |}) (λ l, Some (loc_car l)) _.

Definition proph_id := positive.

From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export proph_map.
Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG loc val Σ;
  heapG_proph_mapG :> proph_mapG proph_id (val * val) Σ
}.

Instance heapG_irisG `{!heapG Σ} : irisG wasm_lang Σ := {
  iris_invG := heapG_invG;
  state_interp σ κs _ := True%I
(*    (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id))%I*);
  fork_post _ := True%I;
                                                       }.

Definition xx i := (ConstInt32 (Wasm_int.int_of_nat i32m i)).

Definition my_add : expr :=
  [Basic (EConst (xx 3));
     Basic (EConst (xx 2));
     Basic (Binop_i T_i32 Add)].

Lemma wp_nil `{!heapG Σ} (s : stuckness) (E : coPset) (Φ : iProp Σ) :
  Φ -∗ WP ([] : expr) @ s ; E {{ fun v => Φ }}%I.
Proof.
  iIntros "H".
  
Admitted. (* TODO *)

Lemma wp_seq `{!heapG Σ} (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (es1 es2 : expr) :
  WP (es2 : expr) @ s ; E {{ fun v => WP (es1 : expr) @ s ; E {{ fun v' => Φ (v ++ v') }}%I }}%I -∗ WP ((es1 ++ es2) : expr) @ s ; E {{ Φ }}%I.
Proof.
  elim: es1.
  { iIntros "H".
    iSimpl.
    admit. }
  { move => e es H.
    iIntros "H".
    iSimpl.
    (* FIXME: iSimpl "H". *)
Admitted. (* TODO *)

Lemma wp_val `{!heapG Σ} (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v0 : wasm.value) (es : expr) (v : val) :
  WP es @ s ; E {{ v, (Φ (v0 :: v)) }}%I -∗ WP (((Basic (EConst v0)) :: es) : expr) @ s ; E {{ v, Φ v }}%I.
Proof.
Admitted. (* TODO *)

Lemma myadd_spec `{!heapG Σ} (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v : val) :
  (Φ (xx 5 :: v)) -∗ WP my_add @ s;E {{ Φ }}%I.
Proof.
  iIntros "HΦ".
  unfold my_add.

  iApply wp_value.
  simpl.
  (* FIXME: iApply. *)
Admitted.

