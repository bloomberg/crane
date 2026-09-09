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
    wrappers to find inner [Dfundef] nodes. Also transforms recursive methods
    inside [Dstruct] fields ([Fmethod]). *)
val transform_decl :
  ?tparams:(template_type * Id.t) list -> cpp_decl -> cpp_decl

(** Pre-register a function definition for mutual recursion detection.
    Call this for all functions in a mutual fixpoint group before any of
    them are individually transformed, so that [transform_decl] can
    detect and inline mutual calls.

    @param refs   List of [(GlobRef.t, type_args)] pairs identifying the
                  function — a single definition may be known under several
                  global references in a mutual fixpoint group.
    @param ret_ty Function return type, used as the return type of the lambda
                  a non-tail inlined call is wrapped in.
    @param params Function parameters [(id, type)] used to reconstruct the
                  callee's signature when inlining it into a caller.
    @param body   Function body statements, stored verbatim for inlining. *)
val register_fundef :
  (GlobRef.t * cpp_type list) list ->
  cpp_type ->
  (Id.t * cpp_type) list ->
  cpp_stmt list ->
  unit

(** Clear the mutual-recursion registry populated by {!register_fundef}. The
    registry is scoped to one compilation unit, so callers reset it at each
    unit boundary before repopulating it. *)
val clear_mutual_table : unit -> unit

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

    A function may be transformed more than once per unit — the dry run and the
    header/implementation passes each invoke {!transform_decl} — so each name is
    collapsed to its best outcome, which is the one describing the emitted C++.
*)
val get_outcomes : unit -> (string * loopify_outcome) list

(** Print the collapsed outcomes ([Crane Loopify Diagnostics]) and raise on any
    decline ([Crane Loopify Strict]). Call once per unit, after transforming.

    The [unit_name] prefixes each line so a decline can be traced to the
    compilation unit that produced it. *)
val report_outcomes : ?unit_name:string -> unit -> unit

(** Discard all recorded outcomes; called at each compilation-unit boundary. *)
val clear_outcomes : unit -> unit
