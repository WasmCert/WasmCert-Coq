(** Interface between [Extract] and the main files. *)

module Interpreter : functor (EH : Extract.Executable_Host) -> sig

  type store_record = EH.host_function Extract.store_record

  (** Run the interpreter until reaching a result. *)
  val run_v :
    int (** The depth *) -> Extract.instance -> EH.host_function Extract.config_tuple ->
    (store_record * Extract.res) EH.host_event

  (** Run one step of the interpreter. *)
  val run_step :
    int (** The depth *) -> Extract.instance -> EH.host_function Extract.config_tuple ->
    EH.host_function Extract.res_tuple EH.host_event

  end

