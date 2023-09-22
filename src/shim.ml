
module type Host = sig
    include Extract.Executable_Host
    val show_host_function : host_function -> string
  end

module DummyHost = struct
    include Extract.DummyHost
    let show_host_function _ = assert false
  end

module type InterpreterType = sig

    module Host : Host
    include module type of Host

    val ( >>= ) : 'a host_event -> ('a -> 'b host_event) -> 'b host_event
    val ( let* ) : 'a host_event -> ('a -> 'b host_event) -> 'b host_event
    val ( let+ ) : 'a host_event -> ('a -> 'b) -> 'b host_event
    val ( and+ ) : 'a host_event -> 'b host_event -> ('a * 'b) host_event
    val pure : 'a -> 'a host_event

    type store_record = Extract.EmptyHost.store_record
    type config_tuple = Extract.config_tuple
    type res_tuple = Extract.res_tuple
    type administrative_instruction = Extract.administrative_instruction

    val run_v :
      Extract.nat ->
      Obj.t * Obj.t Extract.store_record * Extract.frame * administrative_instruction list ->
      (Obj.t * Obj.t Extract.store_record) * Extract.res

    val run_step_compat :
      config_tuple -> Extract.res_tuple

    val is_const_list : administrative_instruction list -> Extract.value0 list option

    val lookup_exported_function :
      (* string -> ((store_record * Extract.instance) * Extract.module_export list) -> *)
      (* config_tuple option *)
      (* XXX where does "Dune__exe__Extract" come from? should it be exposed? *)
      string ->
      (((Extract.Equality.sort * Extract.EmptyHost.store_record) * Extract.instance) * Extract.module_export list) ->
      (((Extract.Equality.sort * Extract.EmptyHost.store_record) * Extract.frame) * Extract.administrative_instruction list) option

    val interp_instantiate_wrapper :
      (* Extract.module0 -> *)
      (* (((store_record * Extract.instance) * Extract.module_export list) * int option) option *)
      Extract.module0 ->
      ((((Extract.Equality.sort * Extract.EmptyHost.store_record) * Extract.instance) * Extract.module_export list) * Extract.nat option) option

    val run_parse_module : string -> Extract.module0 option

    val pp_values : Extract.value0 list -> string
    val pp_store : int -> Dune__exe__Extract.EmptyHost.store_record -> string
    val pp_res_tuple_except_store :
      ((Extract.EmptyHost.store_record * Extract.frame) * Extract.res_step) -> string
    val pp_config_tuple_except_store :
      ((Extract.EmptyHost.store_record * Extract.frame) * Extract.administrative_instruction list) ->
      string

  end

module Interpreter =
  functor (EH : Host) -> struct

    module Host = EH
    include Host

    let ( >>= ) = host_bind

    let ( let* ) = host_bind

    let pure = host_ret

    let ( let+ ) a f =
      let* a = a in
      pure (f a)

    let ( and+ ) a b =
      let* a = a in
      let* b = b in
      pure (a, b)

    (* We are based on the functional version of the interpreter for now *)
    module Interpreter = Extract.Interpreter_func_extract
    module Instantiation = Extract.Instantiation_func_extract
    module PP = Extract.PP

    type store_record = Extract.EmptyHost.store_record
    type config_tuple = Extract.config_tuple
    type res_tuple = Extract.res_tuple
    type administrative_instruction = Extract.administrative_instruction

    let run_v i cfg =
      let (hs, s, f, es) = cfg in
      Interpreter.run_v hs s f es i

    let run_step_compat cfg =
      Interpreter.run_step_compat cfg

    let is_const_list = Interpreter.is_const_list

    let lookup_exported_function name =
      Instantiation.lookup_exported_function (Utils.explode name)

    let interp_instantiate_wrapper m =
      Instantiation.interp_instantiate_wrapper m
(*
    let show_host_function_char_list h = Utils.explode (show_host_function h)
*)
    let run_parse_module m = Extract.run_parse_module (Utils.explode m)

    let pp_values l =
      Utils.implode (PP.pp_values l)

    let pp_store i st =
      Utils.implode (PP.pp_store (Convert.to_nat i) st)

    let pp_res_tuple_except_store r =
      Utils.implode (PP.pp_res_tuple_except_store r)

    let pp_config_tuple_except_store cfg =
      Utils.implode (PP.pp_config_tuple_except_store cfg)

  end

