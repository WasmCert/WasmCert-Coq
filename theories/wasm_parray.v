(** A repackaged version of the persistent array interface in Rocq
 *)

From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat.
From Stdlib Require Import ZArith Lia.
From Wasm Require Export memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N_scope.

Global Parameter wasm_parrayof: Type -> Type.

(* Persistent array, but removing some functions and relaxing the max_length
   to 2^32-1. Also adding a different method of creating an array for
   growing vectors.
 *)
Class Array := {
    arr_make: forall A, N -> A -> wasm_parrayof A;
    (* The same as make but initialises its prefix with values from
   the prefix of another array.
   Does not overflow if the length exceeds the make length.
   This is used in the vector_grow function. *)
    arr_make_copy: forall A, N -> A -> wasm_parrayof A -> N -> wasm_parrayof A;
    arr_get : forall A, wasm_parrayof A -> N -> A;
    arr_default : forall A, wasm_parrayof A -> A;
    arr_set : forall A, wasm_parrayof A -> N -> A -> wasm_parrayof A;
    (* Takes the length and the generator for the block *)
    arr_set_gen : forall A, wasm_parrayof A -> N -> N -> (N -> A) -> wasm_parrayof A;
    arr_length : forall A, wasm_parrayof A -> N;
    arr_copy : forall A, wasm_parrayof A -> wasm_parrayof A;
  }.

Notation " t .[ i ] " := (arr_get t i) (at level 5).
Notation " t .[ i <- a ] " := (arr_set t i a) (at level 5).

(* Can't seem to assemble the type in OCaml since the type signature is not available *)

Section Array_instance.

  Parameter ocaml_arr_make: forall A, N -> A -> wasm_parrayof A.
  (* The same as make but initialises its prefix with values from
   the prefix of another Parameter ocaml_array.
   Does not overflow if the length exceeds the make length.
   This is used in the vector_grow function. *)
  Parameter ocaml_arr_make_copy: forall A, N -> A -> wasm_parrayof A -> N -> wasm_parrayof A.
  Parameter ocaml_arr_get : forall A, wasm_parrayof A -> N -> A.
  Parameter ocaml_arr_default : forall A, wasm_parrayof A -> A.
  Parameter ocaml_arr_set : forall A, wasm_parrayof A -> N -> A -> wasm_parrayof A.
  (* Takes the length and the generator for the block *)
  Parameter ocaml_arr_set_gen : forall A, wasm_parrayof A -> N -> N -> (N -> A) -> wasm_parrayof A.
  Parameter ocaml_arr_length : forall A, wasm_parrayof A -> N.
  Parameter ocaml_arr_copy : forall A, wasm_parrayof A -> wasm_parrayof A.

  (* Putting the instance opaque so we don't unfold to the extraction primitives *)
  Global Instance wasm_array_inst : Array.
  Proof.
    by refine {|
      arr_make := ocaml_arr_make;
      arr_make_copy := ocaml_arr_make_copy;
      arr_get := ocaml_arr_get;
      arr_default := ocaml_arr_default;
      arr_set := ocaml_arr_set;
      arr_set_gen := ocaml_arr_set_gen;
      arr_length := ocaml_arr_length;
      arr_copy := ocaml_arr_copy;
      |}.
  Qed.
  
End Array_instance.

Definition max_arr_length : N := byte_limit.

Section Array_axioms.

Context {A: Type}.

Local Definition array := wasm_parrayof A.

Parameter get_out_of_bounds :
  forall (t : array) (i : N),
    N.ltb i (arr_length t) = false -> t.[i] = arr_default t.
Parameter get_set_same :
  forall (t : array) (i : N) (a : A),
    N.ltb i (arr_length t) = true -> t.[i<-a].[i] = a.
Parameter get_set_other :
  forall (t : array) (i j : N) (a : A),
    i <> j -> t.[i<-a].[j] = t.[j].
Parameter default_set :
  forall (t : array) (i : N) (a : A),
    arr_default t.[i<-a] = arr_default t.
Parameter get_make :
  forall (a : A) (size i : N),
    (arr_make size a).[i] = a.
Parameter get_make_copy:
  forall (a: A) (size i: N) (t: array) (initlen: N),
    N.ltb i size ->
    N.leb initlen (arr_length t) ->
    N.ltb i (arr_length t) ->
    (arr_make_copy size a t initlen).[i] = t.[i].
Parameter get_make_copy_default:
  forall (a: A) (size i: N) (t: array) (initlen: N),
    N.ltb i size ->
    N.leb initlen (arr_length t) ->
    N.leb initlen i ->
    (arr_make_copy size a t initlen).[i] = a.
Parameter leb_length :
  forall (t : array),
    N.leb (arr_length t) max_arr_length = true.
Parameter length_make :
  forall (size : N) (a : A),
    arr_length (arr_make size a) =
      N.min size max_arr_length.
Parameter length_make_copy :
  forall (size : N) (a : A) (t: array) (initlen: N),
    arr_length (arr_make_copy size a t initlen) =
      N.min size max_arr_length.
Parameter length_set :
  forall (t : array) (i : N) (a : A),
    arr_length t.[i<-a] = arr_length t.

(* Some added axioms for set_gen *)
Parameter length_set_gen :
  forall (t : array) (i : N) (len: N) (gen: N -> A),
    arr_length (arr_set_gen t i len gen) = arr_length t.

Parameter arr_set_gen_lookup:
  forall n len gen (t: array) i,
    N.ltb i len ->
    arr_get (arr_set_gen t n len gen) (N.add n i) = (gen i).

Parameter arr_set_gen_lt:
  forall n len gen (t: array) i,
    N.ltb i n ->
    arr_get (arr_set_gen t n len gen) i = arr_get t i.

Parameter arr_set_gen_ge:
  forall n len gen (t: array) i,
    N.leb (N.add n len) i ->
    arr_get (arr_set_gen t n len gen) i = arr_get t i.
                                         
Parameter get_copy :
  forall (t : array) (i : N),
    (arr_copy t).[i] = t.[i].
Parameter length_copy :
  forall (t : array), arr_length (arr_copy t) = arr_length t.
Parameter array_ext :
  forall (t1 t2 : array),
    arr_length t1 = arr_length t2 ->
    (forall i : N,
        N.ltb i (arr_length t1) = true -> t1.[i] = t2.[i]) ->
    arr_default t1 = arr_default t2 -> t1 = t2.
Parameter default_copy :
  forall (t : array), arr_default (arr_copy t) = arr_default t.
Parameter default_make :
  forall (a : A) (size : N),
    arr_default (arr_make size a) = a.
Parameter get_set_same_default :
  forall (t : array) (i : N),
    t.[i<-arr_default t].[i] = arr_default t.
Parameter get_not_default_lt :
  forall (t : array) (x : N),
    t.[x] <> arr_default t -> N.ltb x (arr_length t) = true.

End Array_axioms.