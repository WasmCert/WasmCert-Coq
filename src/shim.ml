
module type InterpreterType = sig

  module Host : Extract.Executable_Host
  include module type of Host

  type store_record = host_function Extract.store_record
  type config_tuple = host_function Extract.config_tuple

  val run_v :
    int -> Extract.instance -> config_tuple ->
    (store_record * Extract.res) host_event

  val run_step :
    int -> Extract.instance -> config_tuple ->
    host_function Extract.res_tuple host_event

  val lookup_exported_function :
    string -> ((store_record * Extract.instance) * Extract.module_export list) ->
    config_tuple option

  val interp_instantiate_wrapper :
    Extract.module0 ->
    (((store_record * Extract.instance) * Extract.module_export list) * int option) option

  end


(** We set the target monad to be exactly the host events.
   This is not possible in Coq due to universe inconsistencies as it might in some very specific
   cases yield an infinite computation.
   It is not an issue in OCaml to have infinite computations. *)
module TargetMonad =
  functor (EH : Extract.Executable_Host) -> struct

    type 'v monad = 'v EH.host_event

    let monad_ret = EH.host_ret
    let monad_bind = EH.host_bind

    let convert x = x

    let rec monad_iter f x =
      monad_bind (f x) (function
        | Extract.Inl y -> monad_iter f y
        | Extract.Inr r -> monad_ret r)

  end

module Interpreter =
  functor (EH : Extract.Executable_Host) -> struct

    module Host = EH
    include Host

    module Interpreter = Extract.Interpreter (EH) (TargetMonad (EH))
    module Instantiation = Extract.Instantiation (EH)

    type store_record = EH.host_function Extract.store_record
    type config_tuple = EH.host_function Extract.config_tuple

    let run_v d i cfg = Interpreter.run_v (Convert.to_nat d) i cfg

    let run_step d i cfg = Interpreter.run_step (Convert.to_nat d) i cfg

    let lookup_exported_function name =
      Instantiation.lookup_exported_function (Utils.explode name)

    let interp_instantiate_wrapper m =
      Option.map (fun (store_inst_exps, start) ->
          (store_inst_exps, Option.map Convert.from_nat start))
        (Interpreter.itree_to_option (fun _ _ _ ->
          (* Normally, this interaction tree should already have been evaluated at this point. *)
            assert false)
          (Instantiation.interp_instantiate_wrapper m))

  end

