(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*  Modified by Xiaojia Rao                                                                            *)
(*  Summary of changes:                                                                                *)
(*  - Added a separate node type for block updates *)
(*  - Maximum array length changed to 2^32 to comply with Wasm's limit (may not work on 32-bit OCaml)  *)
(*  - Added a different make function `make_copy` that uses an initialiser array and deep copy         *)
(*******************************************************************************************************)

(** Uniform Arrays: non-flat arrays (even floats are boxed, i.e., doesn't use
    {!Obj.double_array_tag}) *)
module UArray :
sig
  type 'a t
  val empty : 'a t
  val unsafe_get : 'a t -> int -> 'a
  val unsafe_set : 'a t -> int -> 'a -> unit
  val length : 'a t -> int
  val make : int -> 'a -> 'a t
  val copy : 'a t -> 'a t
  val of_array : 'a array -> 'a t
  val to_array : 'a t -> 'a array
  (* 'a should not be float (no Obj.double_tag) *)
  val unsafe_of_obj : Obj.t -> 'a t
end =
struct
  type 'a t = Obj.t array
  (** Guaranteed to be a non-flat array and no funny business with write
      barriers because of the opacity of Obj.t. *)

  let empty = [||]

  let length (v : 'a t) = Array.length v

  let of_array v =
    if (Obj.tag (Obj.repr v) == Obj.double_array_tag) then begin
      let n = Array.length v in
      (* Ensure that we initialize it with a non-float *)
      let ans = Array.make n (Obj.repr ()) in
      for i = 0 to n - 1 do
        Array.unsafe_set ans i (Obj.repr (Array.unsafe_get v i))
    done;
      ans
    end else
      (Obj.magic (Array.copy v))

  let obj_is_float x = Obj.tag x == Obj.double_tag

  let to_array (type a) (v : a t) : a array =
    let () = assert (not (Array.exists obj_is_float v)) in
    Obj.magic (Array.copy v)

  let unsafe_of_obj (type a) (v : Obj.t) =
    let () = assert (Obj.tag v == 0) in
    (Obj.obj v : a t)

  let unsafe_get = Obj.magic Array.unsafe_get
  let unsafe_set = Obj.magic Array.unsafe_set
 
 let make (type a) n (x : a) : a t =
    (* Ensure that we initialize it with a non-float *)
    let ans = Array.make n (Obj.repr ()) in
    let () = Array.fill ans 0 n (Obj.repr x) in
    ans

  let copy = Array.copy

end

(* Changed to 2^32 bit to match Wasm's memory limit. This needs 64-bit OCaml to work *)
let max_array_length = max_int

let max_length = max_array_length

let to_int i = i

let trunc_size n =
  if 0<=n && n < max_array_length then
    to_int n
  else max_array_length

let uarray_get_range a i len =
  let res = Array.make len (UArray.unsafe_get a i) in
  for j = 1 to len - 1 do
    Array.unsafe_set res j (UArray.unsafe_get a (i + j))
  done;
  res

let uarray_set_range a i block =
  let len = Array.length block in
  for j = 0 to len - 1 do
    UArray.unsafe_set a (i + j) (Array.unsafe_get block j)
  done

(* -------------------------------------------------- *)

type 'a t = ('a kind) ref
and 'a kind =
  | Array of 'a UArray.t * 'a
  | Updated of int * 'a * 'a t
  | BlockUpdated of int * 'a array * 'a t

let unsafe_of_obj t def = ref (Array (UArray.unsafe_of_obj t, def))
let of_array t def = ref (Array (UArray.of_array t, def))

let rec rerootk t k =
  match !t with
  | Array (a, _) -> k a
  | Updated (i, v, p) ->
      let k' a =
        let v' = UArray.unsafe_get a i in
        UArray.unsafe_set a i v;
        t := !p; (* i.e., Array (a, def) *)
        p := Updated (i, v', t);
        k a in
      rerootk p k'
  | BlockUpdated (i, old_vals, p) ->
      let k' a =
        let len = Array.length old_vals in
        let v' = uarray_get_range a i len in
        uarray_set_range a i old_vals;
        t := !p; 
        p := BlockUpdated (i, v', t);
        k a in
      rerootk p k'

let reroot t = rerootk t (fun a -> a)

let length_int p =
  UArray.length (reroot p)

let length p = length_int p

let get p n =
  let t = reroot p in
  let l = UArray.length t in
  if 0 <= n && n < l then
    UArray.unsafe_get t (to_int n)
  else
    match !p with
    | Array (_, def) -> def
    | Updated _ -> assert false
    | BlockUpdated _ -> assert false

let set p n e =
  let a = reroot p in
  let l = (UArray.length a) in
  if 0 <= n && n < l then
    let i = to_int n in
    let v' = UArray.unsafe_get a i in
    UArray.unsafe_set a i e;
    let t = ref !p in (* i.e., Array (a, def) *)
      p := Updated (i, v', t);
      t
  else p

(* --- NEW BLOCK SET FUNCTION --- *)

let set_gen p start_pos block_len generator =
  let a = reroot p in
  let i = to_int start_pos in
  let len = to_int block_len in
  let total_len = UArray.length a in
  (* Check bounds and block size *)
  if 0 <= start_pos && (start_pos + block_len) <= (total_len) then
  let old_vals = uarray_get_range a i len in
  for j = 0 to len - 1 do
    let new_val = generator (j) in
    UArray.unsafe_set a (i + j) new_val
  done;
  let t = ref !p in 
  p := BlockUpdated (i, old_vals, t); 
  t
  else p
(* ------------------------------ *)

let default p =
  let _ = reroot p in
  match !p with
  | Array (_,def) -> def
  | Updated _ -> assert false
  | BlockUpdated _ -> assert false (* ADDED: BlockUpdated case, should not be reached *)

let make_int n def =
  ref (Array (UArray.make n def, def))

let make n def = make_int (trunc_size n) def

(* An addition to the kernel Parray extraction that initialises with another array acting as an initialiser *)
    let make_copy n init arr initlen =
      if initlen <= (length arr) then
        let trunc_n = trunc_size n in
        if (length arr) <= (trunc_n) then
          let marr = UArray.make trunc_n init in
          let initlen_int = to_int initlen in
          for i = 0 to initlen_int - 1 do
            UArray.unsafe_set marr i (get arr (i))
          done;
          ref (Array (marr, init))
        else assert false
      else assert false

let uinit n f =
  if Int.equal n 0 then UArray.empty
  else begin
    let t = UArray.make n (f 0) in
    for i = 1 to n - 1 do
      UArray.unsafe_set t i (f i)
    done;
t
  end

let init n f def =
  let n = trunc_size n in
  let t = uinit n f in
  ref (Array (t, def))

let to_array p =
  let _ = reroot p in
  match !p with
  | Array (t,def) -> UArray.to_array t, def
  | Updated _ -> assert false
  | BlockUpdated _ -> assert false (* ADDED: BlockUpdated case, should not be reached *)

let copy p =
  let _ = reroot p in
  match !p with
  | Array (t, def) -> ref (Array (UArray.copy t, def))
  | Updated _ -> assert false
  | BlockUpdated _ -> assert false (* ADDED: BlockUpdated case, should not be reached *)

(* Higher order combinators: the callback may update the underlying
   array requiring a reroot between each call. To avoid doing n
   reroots (-> O(n^2)), we copy if we have to reroot again. *)

let is_rooted p = match !p with
  | Array _ -> true
  | Updated _ -> false
  | BlockUpdated _ -> false (* ADDED: BlockUpdated is not rooted *)

type 'a cache = {
  orig : 'a t;
mutable self : 'a UArray.t;
  mutable rerooted_again : bool;
}

let make_cache p = {
  orig = p;
self = reroot p;
  rerooted_again = false;
}

let uget_cache cache i =
  let () = if not cache.rerooted_again && not (is_rooted cache.orig)
    then begin
      cache.self <- UArray.copy (reroot cache.orig);
cache.rerooted_again <- true
    end
  in
  UArray.unsafe_get cache.self i

let map f p =
  let t = make_cache p in
  let len = UArray.length t.self in
  let res = uinit len (fun i -> f (uget_cache t i)) in
  let def = f (default p) in
  ref (Array (res, def))

let fold_left f x p =
  let r = ref x in
  let t = make_cache p in
  let len = UArray.length t.self in
  for i = 0 to len - 1 do
    r := f !r (uget_cache t i)
  done;
  f !r (default p)

let fold_left2 f a p1 p2 =
  let r = ref a in
  let t1 = make_cache p1 in
  let len = UArray.length t1.self in
  let t2 = make_cache p2 in
  if UArray.length t2.self <> len then invalid_arg "Parray.fold_left2";
for i = 0 to len - 1 do
    let v1 = uget_cache t1 i in
    let v2 = uget_cache t2 i in
    r := f !r v1 v2
  done;
f !r (default p1) (default p2)
    
