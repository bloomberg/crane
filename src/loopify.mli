(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Loopify pass: transforms recursive MiniCpp functions into iterative ones.

    Operates on {!Minicpp.cpp_decl} nodes after translation produces them but
    before pretty-printing. Detects self-recursive function/method bodies and
    rewrites them using while loops and explicit stacks to prevent stack
    overflow on deep inputs. *)

open Names
open Minicpp

(** Transform a single top-level declaration. Recursion through [Dtemplate]
    wrappers to find inner [Dfun] nodes. Also transforms recursive methods
    inside [Dstruct] fields ([Fmethod]). *)
val transform_decl :
  ?tparams:(template_type * Id.t) list -> cpp_decl -> cpp_decl

(** Turn only the tail-recursive local fixpoints in a declaration's bodies
    into loops: the part of loopification that needs no frame and changes no
    evaluation order, applied whatever the loopification policy says. *)
val transform_local_tail_loops :
  ?tparams:(template_type * Id.t) list -> cpp_decl -> cpp_decl

(** [try_inline_mutual_into ~partner r body] is the body [body] of the
    function [r] with the partners the recursion plan inlines into it
    inlined ({!Recursion_plan.inlinings}), each read as [partner] has it --
    registered with {!register_decl}, unless given -- at the calls the plan
    lists by occurrence: a tail call continuing in the partner's body, any
    other running it in a lambda invoked in place. *)
val try_inline_mutual_into :
  ?partner:(GlobRef.t -> Loopify_analysis.registered_fn option) -> GlobRef.t -> cpp_stmt list -> cpp_stmt list

(** The tail loop Loopify's own transform makes of the body [body] of the
    function [f], whose parameters are [params], under the template
    parameters [tparams], its partners read as [partner] has them: its
    jumps found by a checker of the C++ calls and its varying parameters
    read off them.  {!Control_to_legacy_minicpp}, which lowers the loop from
    the function's ControlIR instead, is compared with it under
    [CRANE_CHECK_IR]. *)
val checker_tail_loop :
  partner:(GlobRef.t -> Loopify_analysis.registered_fn option) ->
  tparams:(template_type * Id.t) list ->
  dfun ->
  (Id.t * cpp_type) list ->
  cpp_stmt list ->
  cpp_stmt list

(** [after_tail_loop ~tparams f params loop] is the body of the function
    [f] once Loopify's transform has made [loop] of it: the local fixpoints
    in [loop] lowered, and the outcome recorded.  It raises
    [Loopify_analysis.Not_linearisable] where that transform declines the
    function whole. *)
val after_tail_loop :
  tparams:(template_type * Id.t) list -> dfun -> (Id.t * cpp_type) list -> cpp_stmt list -> cpp_stmt list

(** Under [CRANE_CHECK_IR], the function [decl] is, if its loop was lowered
    as it was generated, must not tie the knot of an Equations functional:
    Loopify inlines one before its transform, reading the unit's functions,
    which are known only once every one is generated. *)
val check_lowered : cpp_decl -> unit

val worthwhile_move_type : cpp_type -> bool
(** Whether a value of this type is expensive enough to copy that writing
    [std::move] around it earns its keep: a reference count to bump, an
    inductive to clone, or a type parameter that may be either.  Exported for
    {!Last_use}, which asks the same question of a local as loopify asks of a
    frame field. *)

(** [register_decl d] makes [d], if it is a function definition, known to
    mutual-recursion inlining before any function is transformed: called on
    every function of a unit, and every helper loopification transforms,
    before any is finished ({!Cpp.finish_ahead}), so that a mutual partner
    is seen whichever is finished first. *)
val register_decl : cpp_decl -> unit

(** {2 Diagnostics}

    Every bail-out in this pass used to return the original recursive body
    silently, making the pass's coverage unmeasurable. The pass now records an
    outcome per recursive function, validated against the postcondition that no
    self-call survives the transform. [Set Crane Loopify Diagnostics] prints
    them as they are produced; [Set Crane Loopify Strict] turns a decline into
    an error. *)

(** What the pass did with one recursive function. *)
type loopify_outcome =
  | Lp_tail  (** Rewritten to a flat [while] loop. *)
  | Lp_tmc  (** Rewritten by the tail-modulo-cons transform. *)
  | Lp_frame  (** Rewritten to an explicit frame stack. *)
  | Lp_deferred of string
      (** Intentionally not rewritten because the shape already runs in O(1)
          stack (e.g. a [lazy_]-wrapped cofixpoint). Not a failure. *)
  | Lp_declined of string  (** Left as C++ recursion, for the given reason. *)

(** Render an outcome for the diagnostic report. *)
val string_of_outcome : loopify_outcome -> string

(** Outcomes recorded so far, in the order the functions were first processed.

    A function may be transformed more than once per unit — the
    header/implementation passes each invoke {!transform_decl} — so each name is
    collapsed to its best outcome, which is the one describing the emitted C++.
*)
val get_outcomes : unit -> (string * loopify_outcome) list

(** Print the collapsed outcomes ([Crane Loopify Diagnostics]) and raise on any
    decline ([Crane Loopify Strict]). Call once per unit, after transforming.

    The [unit_name] prefixes each line so a decline can be traced to the
    compilation unit that produced it. *)
val report_outcomes : ?unit_name:string -> unit -> unit
