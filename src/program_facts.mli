(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What analysing a unit's structure observed about the program: facts, and
    no backend decisions -- those are {!Target_plan}'s.

    Computed by {!analyze} as a value, from the structure alone, before
    anything is rendered. *)

type t = {
  used_customs : Core.Ref.User.Set.t;
      (** The custom-extracted references the structure names -- a
          constructor's inductive with it -- whose imports its header
          includes, with those of any further custom emitting them names. *)
  higher_order_projections : Core.Ref.User.Set.t;
      (** The projections used as function values rather than as field
          accessors, which need a standalone definition. *)
  effects : Core_plan.Effects.t;
      (** Which applications are a monad's [bind] or [ret], and the mode
          each is generated in. *)
}

(** [analyze struc] observes one unit's structure; it writes nothing. *)
val analyze : Core.Program.t -> t

(** What analysing the whole normalized program observed, before it is split into
    units: interprocedural summaries, fixed points over every function. *)
type program = {
  throwing_values : Names.GlobRef.t list;
      (** The definitions whose body only throws. *)
  parameter_ownership : (Names.GlobRef.t * bool list) list;
      (** Which parameters of each function it owns rather than borrows,
          innermost first ({!Core_plan.Ownership.summarize}). *)
  recursive_groups : Core_plan.Recursive_groups.t;
      (** Which functions recurse through which. *)
  partner_closure_params : (Names.GlobRef.t * int list) list;
      (** Which parameters of each function a call from its recursive group
          passes a closure for ({!Translation_callable_params.partner_closure_params}). *)
  recursion : Core_plan.Recursion.t;
      (** How each function recurses through itself. *)
  control : Lower_control.t;
      (** The control the recursion plan lowers to ({!Control_ir}). *)
}

(** [analyze_program p] analyses the normalized program [p].  Its one write
    is the enum inductives {!Core_plan.Method_registry.create} registers
    ({!Base.Table.add_enum_inductive}), a property of their declarations. *)
val analyze_program : Translation_state.t -> Core_passes.Phase.normalized Core_passes.Phase.program -> program

(** What lowering reads of [program] ({!Translation_state.program_facts}). *)
val lowering : program -> Translation_state.program_facts

(** Whether two analyses of a unit observed the same facts: under
    [CRANE_CHECK_IR] a unit is analysed twice and the two must agree. *)
val equal : t -> t -> bool
