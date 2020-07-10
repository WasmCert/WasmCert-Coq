(** Interface between [Extract] and the main files. *)

(** Run the interpreter until reaching a result. *)
val run_v :
  ('host_function -> 'host_function -> bool) (** Comparison of host functions. *) ->
  ('host_function, 'host_event) Extract.executable_host (** An interface for the host. *) ->
  'monad Extract.monad -> 'monad Extract.functor0 -> (** A monad to project into. *)
  'monad Extract.monadIter (** This monad should be iterable. *) ->
  ('host_event -> 'monad) (** The projection function. *) ->
  int (** The depth *) ->
  Extract.instance (** The instance *) ->
  'host_function Extract.config_tuple (** The configuration tuple *) ->
  'monad

(** Run one step of the interpreter. *)
val run_step :
  ('host_function -> 'host_function -> bool) (** Comparison of host functions. *) ->
  ('host_function, 'host_event) Extract.executable_host (** An interface for the host. *) ->
  'monad Extract.monad -> 'monad Extract.functor0 -> (** A monad to project into. *)
  'monad Extract.monadIter (** This monad should be iterable. *) ->
  ('host_event -> 'monad) (** The projection function. *) ->
  int (** The depth *) ->
  Extract.instance (** The instance *) ->
  'host_function Extract.config_tuple (** The configuration tuple *) ->
  'monad

