(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Loopify pass: transforms recursive MiniCpp functions into iterative ones.

    Operates on {!Minicpp.cpp_decl} nodes after translation produces them but
    before pretty-printing. Detects self-recursive function/method bodies and
    rewrites them using while loops and explicit stacks to prevent stack
    overflow on deep inputs. *)

open Names
open Minicpp

(** [try_inline_mutual_into ~partner r body] is the body [body] of the
    function [r] with the partners the recursion plan inlines into it
    inlined ({!Recursion_plan.inlinings}), each read as [partner] has it, at
    the calls the plan lists by occurrence: a tail call continuing in the
    partner's body, any other running it in a lambda invoked in place. *)
val try_inline_mutual_into :
  partner:(GlobRef.t -> Loopify_analysis.registered_fn option) -> GlobRef.t -> cpp_stmt list -> cpp_stmt list

(** The tail loop Loopify's own transform makes of the body [body] of the
    function [f], whose parameters are [params], under the template
    parameters [tparams], its partners read as [partner] has them: its
    jumps found by a checker of the C++ calls and its varying parameters
    read off them.  {!Control_to_legacy_minicpp}, which lowers the loop from
    the function's ControlIR instead, is compared with it under
    [CRANE_CHECK_IR].  Where given, [parts] says which parameters every
    call passes a value stored in what the caller passed for it, which its
    shadows may point at ({!Loopify_tail.pointer_safe_flags}); so for
    {!checker_modulo_cons}, {!checker_frame_machine}, {!frame_machine},
    {!modulo_cons_loop}, {!local_frame_machine}, and for the fixpoint of
    the member it names, {!lower_local_tail_loops} and
    {!lower_local_loops}. *)
val checker_tail_loop :
  partner:(GlobRef.t -> Loopify_analysis.registered_fn option) ->
  ?parts:bool list ->
  tparams:(template_type * Id.t) list ->
  dfun ->
  (Id.t * cpp_type) list ->
  cpp_stmt list ->
  cpp_stmt list

(** [after_tail_loop ~tparams f params loop] is the body of the function
    [f] once Loopify's transform has made [loop] of it: the local fixpoints
    in [loop] lowered, and the outcome recorded, [strategy] -- a tail loop
    unless given -- or, where a call survived, a decline for [survived].
    It raises [Loopify_analysis.Not_linearisable] where that transform
    declines the function whole. *)
val after_tail_loop :
  ?strategy:Loopify_analysis.loopify_outcome ->
  ?survived:string ->
  tparams:(template_type * Id.t) list ->
  dfun ->
  (Id.t * cpp_type) list ->
  cpp_stmt list ->
  cpp_stmt list

(** The loop Loopify's own transform makes of the body [body] of the
    function [f], planned tail modulo cons, as {!checker_tail_loop} makes a
    tail loop: its branches read off the plan's chains, its calls and
    varying parameters off the C++ calls.  [body] itself where it is not so
    planned. *)
val checker_modulo_cons :
  partner:(GlobRef.t -> Loopify_analysis.registered_fn option) ->
  ?parts:bool list ->
  tparams:(template_type * Id.t) list ->
  dfun ->
  (Id.t * cpp_type) list ->
  cpp_stmt list ->
  cpp_stmt list

(** The machine with a stack Loopify's own transform makes of the body
    [body] of the function [f], as {!checker_tail_loop} makes a tail loop:
    its calls recognised by a checker of the C++ calls. *)
val checker_frame_machine :
  partner:(GlobRef.t -> Loopify_analysis.registered_fn option) ->
  ?parts:bool list ->
  tparams:(template_type * Id.t) list ->
  dfun ->
  (Id.t * cpp_type) list ->
  cpp_stmt list ->
  cpp_stmt list

(** Why no loop of a function Loopify loopifies was made: the transform
    declined it, [Declined why] recording [why] whatever the body holds; or
    it made none, [Left survived], and a call of the function left in the
    body is a decline for [survived], where something sharper is known than
    {!Loopify_analysis.survived_generically}. *)
type unlowered =
  | Declined of string
  | Left of string option

(** [frame_machine ~loop ?entry ~tparams check f params body] is the
    machine with a stack of frames of the function [f], the loop [loop] of
    its ControlIR, whose body [body] has its partners inlined and its tail
    calls exposed: [check] recognises the calls that enter it at [f], and
    the body Loopify adopts, where its ControlIR has the entry [entry], is
    a second entry of it ({!Loopify_frame.find_adopted}).  With it comes
    the reason a call it leaves behind survived, where it adopted a body.
    [Error why] where Loopify would do anything else with [f]: adopt
    another body than the entry or one where there is none, decline a
    branch depending on a recursive call, or make a machine
    disagreeing with its ControlIR; [why] is what Loopify records of the
    function it makes no machine of.  A machine may leave a call behind that
    its ControlIR holds as an ordinary recursive call: the calls entering it
    are then those its loop's [Continue]s, its entry's included, are made
    of, and its frames are laid out for those alone.  Under [CRANE_CHECK_IR] the calls entering a machine leaving none
    must be those.  It raises [Loopify_analysis.Not_linearisable] where the
    transform declines. *)
val frame_machine :
  loop:Control_ir.Loop.t ->
  ?entry:Control_ir.Loop.t ->
  ?parts:bool list ->
  tparams:(template_type * Id.t) list ->
  Loopify_analysis.call_checker ->
  dfun ->
  (Id.t * cpp_type) list ->
  cpp_stmt list ->
  (cpp_stmt list * string option, unlowered) result

(** Whether the body [body] of the function [f] still calls it, as Loopify
    reads its calls: a machine made of it leaves a call behind. *)
val leaves_calls : dfun -> cpp_stmt list -> bool

(** [record_unlowered ?unlowered f body] records the outcome of the
    function [f], whose body is [body], of which no loop of its own is made
    for the reason [unlowered] -- none made, unless given -- as Loopify
    records it of such a function it loopifies: nothing where the plan
    lowers it to none, a deferral for a suspended cofixpoint, and otherwise
    the decline, or the planned strategy read off [body]: a decline where a
    call of [f] is left in it ({!Loopify_analysis.report_outcome}). *)
val record_unlowered : ?unlowered:unlowered -> dfun -> cpp_stmt list -> unit

(** [record_unlowered_method m] is {!record_unlowered} for the method [m],
    of which no loop is attempted: its calls those of the method. *)
val record_unlowered_method : method_field -> unit

(** [modulo_cons_loop ~jumped ~varying ~shapes ~tparams check f params
    body] is the tail-modulo-cons loop of the function [f], whose body
    [body] has its partners inlined and its tail calls exposed: [check]
    recognises the calls the loop takes, [shapes] the branches it builds
    cells in ({!Loopify_tmc.branch_along}), [varying] the parameters it
    changes, and [jumped] is told each call it takes.  [None] where
    Loopify would do anything else with [f]: adopt a fixpoint, decline a
    branch depending on a recursive call, or fall back
    to a frame stack for a call the loop leaves.  It raises
    [Loopify_analysis.Not_linearisable] where the transform declines. *)
val modulo_cons_loop :
  jumped:(cpp_expr -> unit) ->
  varying:bool list ->
  ?parts:bool list ->
  shapes:Loopify_tmc.shape list ->
  tparams:(template_type * Id.t) list ->
  Loopify_analysis.call_checker ->
  dfun ->
  (Id.t * cpp_type) list ->
  cpp_stmt list ->
  cpp_stmt list option

(** [transform_method_own ~varying ~tparams ~self_ty m] is Loopify's
    transform of the method [m] of a struct whose receiver pointer type is
    [self_ty], under the struct's template parameters [tparams], before the
    local fixpoints in it are lowered: [m] itself where it declines.  A tail
    loop varies the receiver and parameters [varying], where given, and
    points at those [parts] says every call passes a value stored in what
    the caller passed for it, where given ({!Loopify_tail.pointer_safe_flags}).
    With [controlled], a loop tail modulo cons or a machine takes the calls
    the method's ControlIR continues by, and builds its cells along its
    turns ({!Loopify_tmc.control_shapes}). *)
val transform_method_own :
  ?varying:bool list ->
  ?parts:bool list ->
  ?controlled:bool ->
  tparams:(template_type * Id.t) list ->
  self_ty:cpp_type ->
  method_field ->
  cpp_field

(** [lower_local_tail_loops ~tparams stmts] is [stmts] with the
    tail-recursive local fixpoints in them turned into loops, under the
    template parameters [tparams]. *)
val lower_local_tail_loops :
  ?parts:(Miniml.Occurrence.t * int) * bool list -> tparams:(template_type * Id.t) list -> cpp_stmt list -> cpp_stmt list

(** [lower_local_loops ~tparams stmts] is [stmts] with every local fixpoint
    in them that Loopify lowers turned into its loop or its machine. *)
val lower_local_loops :
  ?parts:(Miniml.Occurrence.t * int) * bool list -> tparams:(template_type * Id.t) list -> cpp_stmt list -> cpp_stmt list

(** [lower_function_locals ~tparams params body] is the body [body] of a
    function taking [params], of which Loopify makes no loop of its own,
    with every local fixpoint in it Loopify lowers turned into its loop or
    its machine. *)
val lower_function_locals :
  tparams:(template_type * Id.t) list -> (Id.t * cpp_type) list -> cpp_stmt list -> cpp_stmt list

(** [local_frame_machine ~member ~name ~binders ~tparams check params ret_ty
    body] is the body of the machine with a stack of frames of the local
    fixpoint [name], the function [member] of a Core fixpoint, its body
    [body] over its parameters [params], standing for the Core binders
    [binders], with its tail calls exposed: [check] recognises the calls
    entering it.  The local fixpoints in it are lowered after it, as Loopify
    lowers them.  [None] where the machine leaves a call behind.  Under
    [CRANE_CHECK_IR] the calls entering it must be its loop's [Continue]s.
    It raises [Loopify_analysis.Not_linearisable] where the transform
    declines. *)
val local_frame_machine :
  member:Miniml.Occurrence.t * int ->
  name:Id.t ->
  binders:(Id.t * Core_binder.t) list ->
  ?parts:bool list ->
  tparams:(template_type * Id.t) list ->
  Loopify_analysis.call_checker ->
  (Id.t * cpp_type) list ->
  cpp_type ->
  cpp_stmt list ->
  cpp_stmt list option

val worthwhile_move_type : cpp_type -> bool
(** Whether a value of this type is expensive enough to copy that writing
    [std::move] around it earns its keep: a reference count to bump, an
    inductive to clone, or a type parameter that may be either.  Exported for
    {!Last_use}, which asks the same question of a local as loopify asks of a
    frame field. *)

(** [check_pointer_fields ds] checks, under [CRANE_CHECK_IR], the fields
    each constructor struct of the struct [ds] stores behind the pointer
    against those planned before rendering, which the recursion plan's
    tail-modulo-cons chains were read with. *)
val check_pointer_fields : dstruct -> unit

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

(** Outcomes recorded so far, in the order the functions were first
    processed, each name collapsed to the last outcome recorded of it, the
    one describing the emitted C++: a member of a recursive group lowered
    and then left with its partners is recorded as left last. *)
val get_outcomes : unit -> (string * loopify_outcome) list

(** Print the collapsed outcomes ([Crane Loopify Diagnostics]) and raise on any
    decline ([Crane Loopify Strict]). Call once per unit, after transforming.

    The [unit_name] prefixes each line so a decline can be traced to the
    compilation unit that produced it. *)
val report_outcomes : ?unit_name:string -> unit -> unit
