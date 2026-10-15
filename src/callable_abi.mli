(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The C++ calling convention of a generated callable: its template head
    in final declaration order, each parameter with the origin it has and
    the way a call may supply it (docs/Type-Argument-Numbering-Refactor-Plan.md,
    section 3.3).

    The head is the third numbering a call moves between.  A parameter that
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

(** A parameter of one head. *)
module Template_param : sig
  type t

  (** The parameter's place in the head, from [0]. *)
  val position : t -> int

  val name : t -> Names.Id.t
  val equal : t -> t -> bool
end

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

type write_policy =
  | Writable  (** A call may write it, and must where nothing deduces it. *)
  | Deduce_only  (** No call writes it: C++ deduces it from an argument. *)
  | Defaulted of Minicpp.cpp_type
      (** A call may leave it to the default the declaration gives it. *)
  | Phantom of Minicpp.cpp_type
      (** A leading parameter no signature mentions, declared without a
          default: nothing deduces it, so a call writing anything after it
          writes it too, as this filler. *)

type template_parameter = {
  id : Template_param.t;
  origin : origin;
  kind : Minicpp.template_type;
  write : write_policy;
}

(** What the plan of a method adds: it is generated as a member of an
    inductive and called on its receiver, which carries the inductive's own
    variables. *)
type receiver = {
  dropped : Scheme.Var.t list;
      (** The function's variables the method declares no parameter for: no
          signature or annotation of it mentions them. *)
  params : Minicpp.cpp_type list;
      (** The C++ types the method's parameters other than its receiver are
          declared at, in declaration order. *)
}

(** How a value parameter is passed: [Owned], by value, the caller moving
    or copying its argument in; [Borrowed], by const reference;
    [Forwarded], a callable the head deduces, by forwarding reference. *)
type passing =
  | Owned
  | Borrowed
  | Forwarded

type t

val callee : t -> Names.GlobRef.t

(** How each of the callee's value parameters is passed, in declaration
    order, where the plan is of a declaration generated here; a foreign plan
    does not say. *)
val passing : t -> passing list option

(** Where the callee is a method, what its plan says of it as one. *)
val receiver : t -> receiver option

(** The head, in declaration order. *)
val template_head : t -> template_parameter list

(** The plan of a declaration of [callee] whose head is [temps], as
    {!Gen_functions} finalises it; [deduced_callables] are the declared
    positions of the value parameters the head deduces as an [F &&].  [scheme] is the callee's scheme, which
    the parameters named for its variables ([T1], [T2], ...) declare; the
    first [phantom_prefix] of those are its leading phantoms.  A variable
    [relaxed] says the declaration relaxed out of its head declares nothing
    any more: the parameter left at it is [Derived].  A parameter named for
    the [k]th variable declares the scheme's [renumber k]th, where a method
    numbers its own variables after the receiver's, and [receiver] is what
    the plan of a method adds; [passing] how its value parameters are
    passed, in declaration order. *)
val of_head :
  ?phantom_prefix:int ->
  ?relaxed:(int -> bool) ->
  ?renumber:(int -> int) ->
  ?deduced_callables:Param_pos.orig Param_pos.pos list ->
  ?receiver:receiver ->
  ?passing:passing list ->
  callee:Names.GlobRef.t ->
  scheme:Scheme.Id.t option ->
  (Minicpp.template_type * Names.Id.t) list ->
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

(** The plan invariants of section 8.1, as violations: positions and names
    unique and in order, every scheme origin the callee's scheme's, no
    origin declared twice. *)
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

(** Whether a call to [r] passes the callable it declares at [pos] to a
    deduced [F &&]: as [r]'s plan says ({!deduces_callable_at}), or where it
    has none as its call sites assume ({!install}). *)
val deduces_callable : Names.GlobRef.t -> Param_pos.orig Param_pos.pos -> bool

(** The plan of a callable Crane does not generate here -- a custom mapping,
    a declaration of another file or library -- as the conventions its call
    sites assume state it: [instances]
    dictionaries first, then one parameter per variable [kept] keeps, in
    order and no more than [reachable] of them, a template-template one
    where [higher_kinded] says so, a [relaxed] one a [Derived] parameter
    defaulted to [void], the first [phantom_prefix] of them phantoms. *)
val foreign :
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

(** The installed plan of [callee], or else its {!foreign} one.  A method's
    call is still planned against its foreign one: it is written as its
    function's call would be, then printed on the receiver without the
    variables the receiver carries or {!dropped_positions}. *)
val plan :
  ?instances:int ->
  ?higher_kinded:(Scheme.Var.t -> bool) ->
  ?kept:(Scheme.Var.t -> bool) ->
  ?reachable:int ->
  ?relaxed:(int -> bool) ->
  ?phantom_prefix:int ->
  Names.GlobRef.t ->
  scheme:Scheme.Id.t option ->
  t

(** The places, among the variables of the function [r] was made from, of
    those the method [r] dropped ({!receiver}); none where [r] is not a
    planned method. *)
val dropped_positions : Names.GlobRef.t -> int list

(** The C++ types the planned method [r]'s parameters other than its
    receiver are declared at ({!receiver}); [None] where [r] is not a
    planned method. *)
val method_params : Names.GlobRef.t -> Minicpp.cpp_type list option
