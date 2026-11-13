(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The C++ calling convention of a generated callable: its template head
    in final declaration order, each parameter with the origin it has and
    the way a call may supply it.

    The head is the third numbering a call moves between ({!Scheme}).  A parameter that
    stands for a scheme variable keeps that variable's identity wherever the
    declaration put it -- after a phantom parameter was dropped, or a
    defaulted one moved last -- so a call maps an instantiation onto the head
    by identity and never by position.  A parameter C++ introduces -- a class
    dictionary, a deduced callable, one the declaration computes -- has an
    origin that is no scheme variable, and so cannot take a type argument
    meant for one.

    A callee has one plan, wherever it is generated: a function rendered
    inside a struct and the same function at namespace scope take one head.
    Every plan is decided before anything is rendered, by planning the
    unit's callables ({!Cpp.plan_callables}), and installed then
    ({!install}); generating a declaration only checks it ({!check}).
    Generating a declaration must reproduce its plan exactly, and a
    declaration generated with no plan is one the planning missed.  Both are
    reported under [CRANE_CHECK_IR]. *)

(** A C++ type, as a plan records it. *)
type ty = Cpp_ir.Lowered.Type.t

(** How a template parameter is declared, as a plan records it. *)
type kind = Cpp_ir.Lowered.phase Cpp_ir.Template.Parameter_kind.t

(** A parameter of one head. *)
module Template_param : sig
  type t

  (** The parameter's place in the head, from [0]. *)
  val position : t -> int

  (** The name the declaration gives the parameter. *)
  val name : t -> Names.Id.t

  (** Same position and same name. *)
  val equal : t -> t -> bool
end

(** What a template parameter stands for, which decides whether a call's
    type argument may be written at it. *)
type origin =
  | From_scheme of Scheme.Var.t
      (** The callee's scheme variable this parameter declares. *)
  | From_instance of int
      (** The [k]th class dictionary the callable takes. *)
  | From_callable of int
      (** The type of the value parameter at this index, a callable the
          declaration deduces rather than spells. *)
  | Derived of Names.Id.t
      (** A parameter the declaration introduces for its own reasons, named
          so: none of a call's type arguments is its. *)

(** What the builder of a head knows of a parameter as it names it, and
    records rather than leaving the name to say: the callee's type variable
    [Tvar i] it declares, the [k]th class dictionary it stands for, or the
    value parameter at index [i] whose callable type it deduces.  A
    parameter its builder records nothing for is [Derived]. *)
type minted =
  | Scheme_param of int
  | Instance_param of int
  | Callable_param of int

(** How a call may supply a template parameter. *)
type write_policy =
  | Writable  (** A call may write it, and must where nothing deduces it. *)
  | Deduce_only  (** No call writes it: C++ deduces it from an argument. *)
  | Defaulted of Cpp_ir.Lowered.Type.t
      (** A call may leave it to the default the declaration gives it. *)
  | Phantom of Cpp_ir.Lowered.Type.t
      (** A leading parameter no signature mentions, declared without a
          default: nothing deduces it, so a call writing anything after it
          writes it too, as this filler. *)

(** One parameter of a head. *)
type template_parameter = {
  id : Template_param.t;  (** its place and name *)
  origin : origin;  (** what it stands for *)
  kind : Cpp_ir.Lowered.phase Cpp_ir.Template.Parameter_kind.t;  (** how it is declared *)
  write : write_policy;  (** how a call may supply it *)
}

(** What the plan of a method adds: it is generated as a member of an
    inductive and called on its receiver, which carries the inductive's own
    variables. *)
type receiver = {
  dropped : Scheme.Var.t list;
      (** The function's variables the method declares no parameter for: no
          signature or annotation of it mentions them. *)
  dropped_names : Names.Id.t list;
      (** The names those variables had in the method, its own variables
          included, which the function's scheme has no variable for. *)
  params : Cpp_ir.Lowered.Type.t list;
      (** The C++ types the method's parameters other than its receiver are
          declared at, in declaration order. *)
  ret : Cpp_ir.Lowered.Type.t;  (** The return type the method is declared at. *)
  return_only : Names.Id.t list;
      (** The method's own variables the return type alone mentions, which it
          spells erased there. *)
}

(** Why a callee's convention declares no template parameter for one of its
    scheme variables, so that no call writes a type argument for it. *)
type omission =
  | Class_carrier
      (** A higher-kinded class parameter: the instance's associated type,
          which the dictionary for it carries. *)
  | Unmentioned
      (** A variable the callee's type does not mention, where it mentions
          a higher-kinded one ([mbind]'s [B] only ever appears under the
          carrier [M B]). *)

(** How a value parameter is passed: [Owned], by value, the caller moving
    or copying its argument in; [Borrowed], by const reference;
    [Forwarded], a callable the head deduces, by forwarding reference. *)
type passing =
  | Owned
  | Borrowed
  | Forwarded

(** The C++ types a function's value parameters are declared at, in
    declaration order, and the return type it is declared at: its signature
    after the relaxations of its head ({!relaxations}), ownership wrappers
    included. *)
type signature = {
  params : Cpp_ir.Lowered.Type.t list;  (** value parameters' types *)
  ret : Cpp_ir.Lowered.Type.t;  (** the return type *)
}

(** The plan of one callable. *)
type t

(** The global the plan is of; for an instance's method, the instance
    ({!of_instance_method}). *)
val callee : t -> Names.GlobRef.t

(** How each of the callee's value parameters is passed, in declaration
    order, where the plan is of a declaration generated here; a foreign plan
    does not say. *)
val passing : t -> passing list option

(** The signature of the callee, where the plan is of a function generated
    here; a method's is in {!receiver}, a foreign plan does not say. *)
val signature : t -> signature option

(** Where the callee is a method, what its plan says of it as one. *)
val receiver : t -> receiver option

(** The head, in declaration order. *)
val template_head : t -> template_parameter list

(** The head as the declaration spells it: each parameter's kind and name,
    in order. *)
val declared_head : t -> Cpp_ir.Lowered.phase Cpp_ir.Template.parameters

(** What the relaxations that made the head out of the declaration's own
    decided ({!Head_relaxation}), in the order they were made: a
    declaration generated under the head is rewritten by each.  None for a
    foreign plan. *)
val relaxations : t -> Head_relaxation.t list

(** Whether the callee's convention keeps its scheme variable [v] -- does
    not omit it ({!omission}) -- as the plan was made. *)
val keeps : t -> Scheme.Var.t -> bool

(** {!keeps} for the variable the callee's type spells [Tvar (_, i)]: the
    crossing from the body's numbering.  One the plan does not know is
    kept. *)
val keeps_tvar : t -> int -> bool

(** The variables a call's dictionaries stand at, in order: those the
    convention omits, up to the last one its type mentions. *)
val dictionary_carriers : t -> Scheme.Var.t list

(** The plan of a declaration of [callee] whose head is [temps], as
    {!Gen_functions} finalises it; [deduced_callables] are the declared
    positions of the value parameters the head deduces as an [F &&].
    [minted] is what the builders of [temps] recorded of each parameter, by
    the name they gave it; a parameter a relaxation added has no record,
    and is [Derived].  [scheme] is the callee's scheme, whose [i]th variable
    a parameter recorded as [Scheme_param i] declares; the first
    [phantom_prefix] of those are its leading phantoms.  A variable
    [relaxed] says the declaration relaxed out of its head declares nothing
    any more: the parameter left at it is [Derived].  [receiver] is what
    the plan of a method adds; [passing] how its value parameters are
    passed, in declaration order; [signature] what a function is declared
    at; [omitted] says why the convention omits a variable of [scheme], if
    it does. *)
val of_head :
  ?omitted:(Scheme.Var.t -> omission option) ->
  ?phantom_prefix:int ->
  ?relaxed:(int -> bool) ->
  ?deduced_callables:Param_pos.orig Param_pos.pos list ->
  ?receiver:receiver ->
  ?passing:passing list ->
  ?signature:signature ->
  ?relaxations:Head_relaxation.t list ->
  ?minted:(Names.Id.t * minted) list ->
  callee:Names.GlobRef.t ->
  scheme:Scheme.Id.t option ->
  Cpp_ir.Lowered.phase Cpp_ir.Template.parameters ->
  t

(** The plan of the method [mf] of the struct of [instance]: its head, its
    parameters' types and its return type, [minted] what the struct's
    builder recorded of its parameters.  The method has no global of its
    own, so the plan's callee is the instance, and no scheme. *)
val of_instance_method :
  ?minted:(Names.Id.t * minted) list ->
  instance:Names.GlobRef.t ->
  Cpp_ir.Lowered.phase Cpp_ir.Field.Method.t ->
  t

(** Whether the value parameter at the declared position [pos] is a callable
    the head deduces as an [F &&]: the callee then calls it at its own
    instantiation.  None is, in a foreign plan. *)
val deduces_callable_at : t -> Param_pos.orig Param_pos.pos -> bool

(** The parameter declaring scheme variable [v], if the head has one. *)
val parameter_of_var : t -> Scheme.Var.t -> template_parameter option

(** The same callee, with the same head; where a plan was recorded is not
    part of it. *)
val equal : t -> t -> bool

(** The plan's own invariants, as violations: positions and names unique
    and in order, every scheme origin the callee's scheme's, no origin
    declared twice. *)
val validate : t -> string list

(** {2 The frozen map} *)

(** [install callables assumed] makes [callables] the unit's plans, and
    [assumed] the callables a function of the unit with none is assumed to
    deduce ({!deduces_callable}).  Done once, before anything is rendered:
    from here the plans are an immutable program fact.  Under
    [CRANE_CHECK_IR] a callee planned twice with two heads is an error. *)
val install :
  t list -> (Names.GlobRef.t * Param_pos.orig Param_pos.pos list) list -> unit

(** Checks the head a declaration is generated with against its plan, adding
    nothing: under [CRANE_CHECK_IR] a different head, or a declaration
    generated with no plan, is an error. *)
val check : t -> unit

(** The installed plan of a declaration. *)
val lookup : Names.GlobRef.t -> t option

(** {!lookup} for a declaration that is generated: an anomaly where planning
    made it no plan. *)
val planned : Names.GlobRef.t -> t

(** [install_instance_methods planned] makes [planned] the plans of the unit's
    instance structs' methods: for each instance, each method's by name. *)
val install_instance_methods : (Names.GlobRef.t * (Names.Id.t * t) list) list -> unit

(** The installed plan of the method [name] of [instance]'s struct. *)
val instance_method : instance:Names.GlobRef.t -> Names.Id.t -> t option

(** {!instance_method} for a method that is generated: an anomaly where
    planning made it no plan. *)
val planned_instance_method : instance:Names.GlobRef.t -> Names.Id.t -> t

(** {!check} for the method [name] of [instance]'s struct. *)
val check_instance_method : instance:Names.GlobRef.t -> Names.Id.t -> t -> unit

(** Whether a call to [r] passes the callable it declares at [pos] to a
    deduced [F &&]: as [r]'s plan says ({!deduces_callable_at}), or where it
    has none as its call sites assume ({!install}). *)
val deduces_callable : Names.GlobRef.t -> Param_pos.orig Param_pos.pos -> bool

(** The plan of a callable Crane does not generate here -- a custom mapping,
    a declaration of another file or library -- as the conventions its call
    sites assume state it: [instances] dictionaries first, then one parameter per variable [kept] keeps, in
    order and no more than [reachable] of them, a template-template one
    where [higher_kinded] says so, a [relaxed] one a [Derived] parameter
    defaulted to [void], the first [phantom_prefix] of them phantoms, each
    variable omitted as [omitted] says. *)
val foreign :
  ?omitted:(Scheme.Var.t -> omission option) ->
  ?instances:int ->
  ?higher_kinded:(Scheme.Var.t -> bool) ->
  ?kept:(Scheme.Var.t -> bool) ->
  ?reachable:int ->
  ?relaxed:(int -> bool) ->
  ?phantom_prefix:int ->
  callee:Names.GlobRef.t ->
  scheme:Scheme.Id.t option ->
  unit ->
  t

(** [install_foreign derive callees] makes the {!foreign} plan [derive r]
    gives each of [callees] with no installed plan of its own, or only a
    method's, the unit's plan of [r]: planned with no dictionary, before
    anything is rendered.  Replaces the unit's previous foreign plans. *)
val install_foreign : (Names.GlobRef.t -> t) -> Names.GlobRef.t list -> unit

(** The installed plan of [callee], or else its foreign one, with
    [instances] dictionaries: the one {!install_foreign} planned, or where it
    planned none, {!foreign}'s.  Under [CRANE_CHECK_IR] a planned one is
    checked against {!foreign}'s, and emission finding none planned is a
    violation: every callee a body names is planned before bodies are
    generated.  A method's call is still planned against its foreign one: it is written as its function's call would be, then
    printed on the receiver without the variables the receiver carries or
    {!dropped_positions}. *)
val plan :
  ?omitted:(Scheme.Var.t -> omission option) ->
  ?instances:int ->
  ?higher_kinded:(Scheme.Var.t -> bool) ->
  ?kept:(Scheme.Var.t -> bool) ->
  ?reachable:int ->
  ?relaxed:(int -> bool) ->
  ?phantom_prefix:int ->
  Names.GlobRef.t ->
  scheme:Scheme.Id.t option ->
  t

(** [install_projections derive fields] makes [derive x] the unit's plan of
    a call of each class field [x] of [fields] through a concrete instance,
    planned before anything is rendered.  Replaces the unit's previous
    projection plans. *)
val install_projections : (Names.GlobRef.t -> t) -> Names.GlobRef.t list -> unit

(** The plan {!install_projections} made of a call of the class field [x]
    through a concrete instance.  Under [CRANE_CHECK_IR] it is checked
    against [derive x]; emission finding none planned is a violation. *)
val projection : (Names.GlobRef.t -> t) -> Names.GlobRef.t -> t

(** How many foreign plans the unit planned, and how many emission found
    planned or derived itself. *)
val report_foreign : unit -> string

(** The places, among the variables of the function [r] was made from, of
    those the method [r] dropped ({!receiver}); none where [r] is not a
    planned method. *)
val dropped_positions : Names.GlobRef.t -> int list

(** The C++ types the planned method [r]'s parameters other than its
    receiver are declared at ({!receiver}); [None] where [r] is not a
    planned method. *)
val method_params : Names.GlobRef.t -> Cpp_ir.Lowered.Type.t list option

(** The callee's ML type the plan was made against: the ML-shaped signature
    beside the declared one ({!signature}), before the head's relaxations,
    in the callee's own variables, which a call's C++ head is rebuilt from
    at the call's instantiation.  [None] for a global with no recorded
    type. *)
val ml_type : t -> Miniml.ml_type option

(** [planned_ml_type r] -- {!ml_type} of the unit's plan of [r], installed,
    foreign or a projection's, without planning one; [None] where none is
    planned. *)
val planned_ml_type : Names.GlobRef.t -> Miniml.ml_type option option
