
(** Convert a function [t -> t -> bool] to a Coq function [forall x y : t, {x = y} + {x <> y}]. *)
let comparison comp x y =
  if comp x y then Extract.Left else Extract.Right

(** Convert a function [('a -> 'b) -> 'monad -> 'monad] to a [Extract.functor0]. *)
let build_functor (f : ('a -> 'b) -> 'monad -> 'monad) _ _ map =
  f (Obj.magic map)

(** Convert a function [('i -> ('i, 'r) Extract.sum 'monad) -> 'i -> 'r 'monad] to a [Extract.monadIter]. *)
let monadIter monad _ _ f =
  let rec loop i =
    Extract.bind2 monad (f i) (fun x ->
      let x = Obj.magic x in
      match x with
      | Extract.Inl i -> loop i
      | Extract.Inr r -> Extract.ret monad r) in
  loop

let run_v comp exec monad funct project d i cfg =
  let comp = comparison comp in
  let funct = build_functor funct in
  let project _ = project in
  let monadIter = monadIter monad in
  Extract.run_v_extraction comp exec monad funct monadIter project (Convert.to_nat d) i cfg

let run_step comp exec monad funct project d i cfg =
  let comp = comparison comp in
  let funct = build_functor funct in
  let project _ = project in
  let monadIter = monadIter monad in
  Extract.run_step_extraction comp exec monad funct monadIter project (Convert.to_nat d) i cfg

