(** Interface between [Extract] and the main files. *)

(** Run the interpreter until reaching a result. *)
val run_v :
  ('host_function -> 'host_function -> bool) (** Comparison of host functions. *) ->
  'host_function Extract.executable_host (** An interface for the host. *) ->
  'monad Extract.monad (** A monad to project into. *) ->
  (('a -> 'b) -> (*'a*) 'monad -> (*'b*) 'monad) (** A [fmap] operation on the monad. *) ->
  ('host_event -> 'monad) (** The projection function. *) ->
  int (** The depth *) ->
  Extract.instance (** The instance *) ->
  'host_function Extract.config_tuple (** The configuration tuple *) ->
  'monad

(** Run one step of the interpreter. *)
val run_step :
  ('host_function -> 'host_function -> bool) (** Comparison of host functions. *) ->
  'host_function Extract.executable_host (** An interface for the host. *) ->
  'monad Extract.monad (** A monad to project into. *) ->
  (('a -> 'b) -> (*'a*) 'monad -> (*'b*) 'monad) (** A [fmap] operation on the monad. *) ->
  ('host_event -> 'monad) (** The projection function. *) ->
  int (** The depth *) ->
  Extract.instance (** The instance *) ->
  'host_function Extract.config_tuple (** The configuration tuple *) ->
  'monad

