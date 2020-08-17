(** Interface between [Extract] and the main files. *)

module type InterpreterType = sig

  module Host : Extract.Executable_Host
  include module type of Host

  type store_record = host_function Extract.store_record
  type config_tuple = host_function Extract.config_tuple

  (** Run the interpreter until reaching a result. *)
  val run_v :
    int (** The depth *) -> Extract.instance -> config_tuple ->
    (store_record * Extract.res) host_event

  (** Run one step of the interpreter. *)
  val run_step :
    int (** The depth *) -> Extract.instance -> config_tuple ->
    host_function Extract.res_tuple host_event

  (** Look-up a specific extracted function of the instantiation. *)
  val lookup_exported_function :
    string -> ((store_record * Extract.instance) * Extract.module_export list) ->
    config_tuple option

  (** Perform the instantiation of a module. *)
  val interp_instantiate_wrapper :
    Extract.module0 ->
    (((store_record * Extract.instance) * Extract.module_export list) * int option) option

  end

module Interpreter : functor (EH : Extract.Executable_Host) -> InterpreterType with module Host = EH

