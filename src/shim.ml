
(** Convert a function [t -> t -> bool] to a Coq function [forall x y : t, {x = y} + {x <> y}]. *)
let comparison comp x y = comp x y

(** Convert a function [('a -> 'b) -> 'monad -> 'monad] to a [Extract.functor0]. *)
let build_functor (f : ('a -> 'b) -> 'monad -> 'monad) _ _ map =
  f (Obj.magic map)

(** We set the target monad to be exactly the host events.
   This is not possible in Coq due to universe inconsistencies as it might in some very specific
   cases yield an infinite computation.
   It is not an issue in OCaml to have infinite computations. *)
module TargetMonad =
  functor (EH : Extract.Executable_Host) -> struct

    type 'v monad = EH.host_event

    let monad_ret = EH.host_ret
    let monad_bind = EH.host_bind

    let convert x = x

    let rec monad_iter f x =
      monad_bind (f x) (function
        | Extract.Inl y -> monad_iter f y
        | Extract.Inr r -> Extract.ret monad r)

  end

module Interpreter =
  functor (EH : Extract.Executable_Host) -> struct

    module Interpreter = Extract.Interpreter (EH) (TargetMonad (EH))

    type store_record = EH.host_function Extract.store_record

    let run_v d i cfg = Interpreter.run_v (Convert.to_nat d) i cfg

    let run_step d i cfg = Interpreter.run_step (Convert.to_nat d) i cfg

  end

