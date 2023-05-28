
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

    type store_record = Dune__exe__Extract.EmptyHost.store_record
    type config_tuple = host_function Extract.config_tuple
    type res_tuple = host_function Extract.res_tuple
    type administrative_instruction = Extract.administrative_instruction

    val run_v :
      (* int -> Extract.instance -> config_tuple -> *)
      (* (store_record * Extract.res) host_event *)
      int -> Extract.typeidx ->
      Obj.t * Obj.t Extract.store_record * Extract.frame * administrative_instruction list ->
      (Obj.t * Obj.t Extract.store_record) * Extract.res

    val run_step :
      (* int -> Extract.instance -> config_tuple -> *)
      (* host_function Extract.res_tuple host_event *)
      int -> 'a ->
      Obj.t * Obj.t Extract.store_record * Extract.frame * administrative_instruction list -> Extract.res_step'


    val is_const_list : administrative_instruction list -> Extract.value0 list option

    val lookup_exported_function :
      (* string -> ((store_record * Extract.instance) * Extract.module_export list) -> *)
      (* config_tuple option *)
      (* XXX where does "Dune__exe__Extract" come from? should it be exposed? *)
      string -> (Dune__exe__Extract.EmptyHost.store_record * Extract.instance) *
      Extract.module_export list ->
      ((Dune__exe__Extract.EmptyHost.store_record * Extract.frame) * administrative_instruction list) option

    val interp_instantiate_wrapper :
      (* Extract.module0 -> *)
      (* (((store_record * Extract.instance) * Extract.module_export list) * int option) option *)
      Extract.module0 ->
      (((Dune__exe__Extract.EmptyHost.store_record * Extract.instance) * Extract.module_export list) * Extract.typeidx option) option

    val run_parse_module : string -> Extract.module0 option

    val pp_values : Extract.value0 list -> string
    val pp_store : int -> Dune__exe__Extract.EmptyHost.store_record -> string
    val pp_res_tuple_except_store : res_tuple -> string
    val pp_config_tuple_except_store :
      (store_record * Extract.frame) * administrative_instruction list ->
      (* XXX should update config_tuple to this? *)
      (* config_tuple -> *)
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

    module Interpreter = Extract.Interpreter_func
    module Instantiation = Extract.Instantiation
    module PP = Extract.PP (EH)

    type store_record = Dune__exe__Extract.EmptyHost.store_record
    type config_tuple = host_function Extract.config_tuple
    type res_tuple = host_function Extract.res_tuple
    type administrative_instruction = Extract.administrative_instruction

    let run_v d i cfg =
      let (hs, s, f, es) = cfg in
      Interpreter.run_v hs s f es (Convert.to_nat d) i

    let run_step d i cfg =
      let (hs, s, f, es) = cfg in
      Interpreter.run_step hs s f es (Convert.to_nat d)

    let is_const_list = Interpreter.is_const_list

    let lookup_exported_function name =
      Instantiation.lookup_exported_function (Utils.explode name)

    let interp_instantiate_wrapper m =
      Instantiation.interp_instantiate_wrapper m

    let show_host_function_char_list h = Utils.explode (show_host_function h)

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

