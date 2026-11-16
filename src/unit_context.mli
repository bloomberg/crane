(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What every stage of one unit's extraction reads about the unit: a value
    built where the unit starts, once its plan decides its configuration,
    and handed to the stages that generate, finish and render it.  Lowering
    finds it in its input ({!Translation_state.unit_context}), naming and
    printing in the position they write at ({!Cpp_state.render_ctx}), the
    finishing passes in their argument ({!Cpp_pipeline.finish}).  Nothing
    installs it anywhere for a reader to find. *)

type t = {
  config : Table.unit_config;
      (** The unit's configuration ({!Target_plan.t.config}): whether it
          runs on several threads, which withholds a [Crane NonAtomicRc] or
          [Crane SingleThreaded] request. *)
  callables : Callable_abi.decided;
      (** The callable plans decided so far: none until the unit's are
          ({!Callable_abi.decide}), then its own, its foreign and its
          projection plans as they are planned. *)
  scopes : Scope_plan.bound;
      (** How a definition written outside its struct's body names the
          struct, and the other facts of the unit's scope plan: none until
          the plan is decided ({!Cpp.plan_scopes}). *)
}

(** [make ~config] is the context of a unit configured as [config], with
    no plan decided. *)
val make : config:Table.unit_config -> t

(** The context of a declaration extracted outside every unit: one that
    runs on one thread. *)
val detached : t

(** {!Table.non_atomic_rc_for} the unit's configuration. *)
val non_atomic_rc : t -> bool

(** {!Table.count_rc_for} the unit's configuration. *)
val count_rc : t -> bool
