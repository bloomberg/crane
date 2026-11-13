(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Loopify pass: transforms recursive C++ functions into iterative ones.

    Operates on {!Cpp_ir.Lowered} declarations after translation produces them
    and before the finish pipeline ({!Cpp_pipeline}); ControlIR lowering
    ({!Control_to_cpp_ir}) is its main caller.  Each function, method and local fixpoint is
    lowered as the recursion plan decided from its Core body
    ({!Recursion_plan.strategy}): a [while] loop, a loop tail modulo cons,
    or a machine with an explicit stack of frames, which keeps deep inputs
    from overflowing the C++ stack.  Each loop must agree with its ControlIR
    ({!Lower_control.loop}); under [CRANE_CHECK_IR] a disagreement is a
    violation. *)

open Names
open Loopify_analysis

(** [after_tail_loop ~tparams f params loop] is the body of the function
    [f] once Loopify's transform has made [loop] of it: the local fixpoints
    in [loop] lowered, and the outcome recorded, [strategy] -- a tail loop
    unless given -- or, where a call survived, a decline for [survived].
    A local fixpoint whose transform declines is left as it was, its
    decline recorded; the caller catches
    [Loopify_analysis.Not_linearisable] around the transform that built
    [loop], not around this. *)
val after_tail_loop :
  ?strategy:Loopify_analysis.loopify_outcome ->
  ?survived:string ->
  tparams:(param_kind * Id.t) list ->
  func ->
  (Id.t * ty) list ->
  stmt list ->
  stmt list

(** Why no loop of a function Loopify loopifies was made: the transform
    declined it, [Declined why] recording [why] whatever the body holds; or
    it made none, [Left survived], and a call of the function left in the
    body is a decline for [survived], where something sharper is known than
    {!Loopify_analysis.survived_generically}. *)
type unlowered =
  | Declined of string  (** The transform declined, for this reason. *)
  | Left of string option
      (** No loop was made; the reason to record if a call survives. *)

(** [frame_machine ~loop ?entry ?entered_pointers ~varying ~parts ~tparams
    check f params body] is the machine with a stack of frames of the
    function [f], the loop [loop] of its ControlIR, whose body [body] has
    its tail calls exposed: [check] recognises the calls that enter it at
    [f], and the body Loopify adopts, where its ControlIR has the entry
    [entry], is a second entry of it ({!Loopify_frame.find_adopted}), whose
    frames hold by pointer the parameters standing for the Core binders
    [entered_pointers] accepts; its frames save the parameters [varying] of
    [f]'s, and hold by pointer those [parts] marks.  With it comes
    the reason a call it leaves behind survived, where it adopted a body.
    [Error why] where Loopify would do anything else with [f]: adopt
    another body than the entry or none where there is one, or make a
    machine disagreeing with its ControlIR, each a violation under
    [CRANE_CHECK_IR]; [why] is what Loopify records of the function it
    makes no machine of.  A machine may leave a call behind that its
    ControlIR holds as an ordinary recursive call: the calls entering it are
    those its loop's [Continue]s, its entry's included, are made of, whether
    or not it leaves one, and its frames are laid out for those alone.  It
    raises [Loopify_analysis.Not_linearisable] where the transform
    declines. *)
val frame_machine :
  loop:Control_ir.Loop.t ->
  ?entry:Control_ir.Loop.t ->
  ?entered_pointers:(Core_binder.t -> bool) ->
  varying:bool list ->
  parts:bool list ->
  tparams:(param_kind * Id.t) list ->
  Loopify_analysis.call_checker ->
  func ->
  (Id.t * ty) list ->
  stmt list ->
  (stmt list * string option, unlowered) result

(** The recursive calls of the definition [r], each by the occurrence the
    C++ call made of it records: a function's own, in its recursive group's
    bodies ({!Recursion_plan.calls}), or those of the member of the local
    fixpoint a helper lifted for it lowers. *)
val definition_calls : GlobRef.t -> Miniml.Occurrence.t list

(** [record_unlowered ?unlowered f body] records the outcome of the
    function [f], whose body is [body], of which no loop of its own is made
    for the reason [unlowered] -- none made, unless given -- as Loopify
    records it of such a function it loopifies: nothing where the plan
    lowers it to none, a deferral for a suspended cofixpoint, and otherwise
    the decline, or the planned strategy read off [body]: a decline where a
    call of [f] is left in it ({!Loopify_analysis.report_outcome}). *)
val record_unlowered : ?unlowered:unlowered -> func -> stmt list -> unit

(** [record_unlowered_method m] is {!record_unlowered} for the method [m],
    of which no loop is attempted: its calls those of the method. *)
val record_unlowered_method : meth -> unit

(** [modulo_cons_loop ~jumped ?cursor ~varying ~parts ~shapes ~tparams check
    f params body] is the tail-modulo-cons loop of the function [f], whose
    body [body] has its tail calls exposed: [check] recognises the calls the
    loop takes, [shapes] the branches it builds cells in
    ({!Loopify_tmc.branch_along}), [varying] the parameters it changes,
    [parts] those every call passes a value stored in what the caller passed
    for it, [cursor] the input it recycles the cells of, and [jumped] is
    told each call it takes.  [None] where
    Loopify would do anything else with [f]: adopt a body, a violation under
    [CRANE_CHECK_IR], or leave a call behind.  It raises
    [Loopify_analysis.Not_linearisable] where the transform declines. *)
val modulo_cons_loop :
  jumped:(expr -> unit) ->
  ?cursor:Reuse_cursor.t ->
  varying:bool list ->
  parts:bool list ->
  shapes:Loopify_tmc.shape list ->
  tparams:(param_kind * Id.t) list ->
  Loopify_analysis.call_checker ->
  func ->
  (Id.t * ty) list ->
  stmt list ->
  stmt list option

(** [transform_method_own ?cursor ?moves ~varying ~parts ~park ~tparams
    ~self_ty m] is Loopify's
    transform of the method [m] of a struct whose receiver pointer type is
    [self_ty], under the struct's template parameters [tparams], before the
    local fixpoints in it are lowered: [m] itself where it declines.  A tail
    loop or a machine varies the receiver and parameters [varying], and
    points at those [parts] says every call passes a value stored in what
    the caller passed for it, where given ({!Loopify_tail.pointer_safe_flags}).
    A loop tail modulo cons or a machine takes the calls the method's
    ControlIR continues by, and builds its cells along its turns
    ({!Loopify_tmc.control_shapes}), recycling the cells of the input
    [cursor] walks, where given.  A tail loop parks the receiver of the
    calls made of [park], those of the turns that make the receiver they
    pass ({!Control_ir.Term.rebuilt}), and passes the others theirs, which the
    turns derive from the loop's parameters; a loop of another kind parks
    none.  Under [CRANE_CHECK_IR] it parks every call of [park].  A tail
    loop moves a parameter into its own next value at the calls [moves]
    gives ({!Ownership_ir.continue_moves}). *)
val transform_method_own :
  ?cursor:Reuse_cursor.t ->
  ?moves:(Miniml.Occurrence.t * Ownership_ir.Continue_move.t list) list ->
  varying:bool list ->
  parts:bool list ->
  park:Miniml.Occurrence.t list ->
  tparams:(param_kind * Id.t) list ->
  self_ty:ty ->
  meth ->
  field

(** Why a method is not lowered to a machine or a loop tail modulo cons
    whose recursive call passes a receiver made in a turn: a frame or a cell
    keeps a pointer to the receiver, which that value does not outlive. *)
val value_receiver : string

(** Why a method is not lowered to a tail loop one of whose recursive calls
    makes the receiver it passes and reads the receiver in another
    argument: the receiver is parked before that argument is evaluated. *)
val rebuilt_receiver_read : string

(** [lower_local_tail_loops ~tparams stmts] is [stmts] with the
    tail-recursive local fixpoints in them turned into loops, under the
    template parameters [tparams]. *)
val lower_local_tail_loops :
  tparams:(param_kind * Id.t) list -> stmt list -> stmt list

(** [lower_function_locals ~tparams params body] is the body [body] of a
    function taking [params], of which Loopify makes no loop of its own,
    with every local fixpoint in it Loopify lowers turned into its loop or
    its machine. *)
val lower_function_locals :
  tparams:(param_kind * Id.t) list -> (Id.t * ty) list -> stmt list -> stmt list

(** [local_frame_machine ~member ~name ~binders ~varying ~parts ~tparams
    check params ret_ty body] is the body of the machine with a stack of
    frames of the local fixpoint [name], the function [member] of a Core
    fixpoint, its body [body] over its parameters [params], standing for the
    Core binders [binders], with its tail calls exposed: [check] recognises
    the calls entering it, its frames save the parameters [varying], and
    hold by pointer those [parts] marks.
    The local fixpoints in it are lowered after it, as Loopify
    lowers them.  [None] where the machine leaves a call behind.  Under
    [CRANE_CHECK_IR] the calls entering it must be its loop's [Continue]s.
    It raises [Loopify_analysis.Not_linearisable] where the transform
    declines. *)
val local_frame_machine :
  member:Miniml.Occurrence.t * int ->
  name:Id.t ->
  binders:(Id.t * Core_binder.t) list ->
  varying:bool list ->
  parts:bool list ->
  tparams:(param_kind * Id.t) list ->
  Loopify_analysis.call_checker ->
  (Id.t * ty) list ->
  ty ->
  stmt list ->
  stmt list option

(** What the ControlIR loop of a local fixpoint's function says of each
    parameter its lambda takes -- the loop's parameters that are not void
    ({!Ml_type_util.void_binder}), the last first, the reverse of the
    source order the lambda keeps them in: whether some Continue changes it
    ({!Control_ir.Term.invariant_parameters}), and whether every Continue passes
    it a value stored in what the caller passed for it
    ({!Control_ir.Term.parts_passed}) or, of a machine with a stack of frames,
    whether its frames hold it by pointer ({!Frame_storage}). *)
type member_plan = {
  member_varying : bool list;  (** Whether some Continue changes it. *)
  member_parts : bool list;
      (** Whether it is passed parts of the caller's, or held by pointer in
          a frame. *)
  member_moves : (Miniml.Occurrence.t * Ownership_ir.Continue_move.t list) list;
      (** The parameters each Continue of a tail loop moves into their next
          value ({!Ownership_ir.continue_moves}); empty for a machine. *)
}

(** [member_plan ~frames member params] is the plan of the local fixpoint
    function [member] whose lambda takes [params], the last first, lowered as a machine with
    a stack of frames where [frames]; [None] where it has no ControlIR loop,
    or the lambda takes other parameters than the loop. *)
val member_plan :
  frames:bool -> Miniml.Occurrence.t * int -> (Names.Id.t * ty) list -> member_plan option

val worthwhile_move_type : ty -> bool
(** Whether a value of this type is expensive enough to copy that writing
    [std::move] around it earns its keep: a reference count to bump, an
    inductive to clone, or a type parameter that may be either.  Exported for
    {!Cpp_simplify}, which asks the same question of a local as loopify asks
    of a frame field. *)

(** {2 Diagnostics}

    The pass records an outcome per recursive function, so that a bail-out,
    which leaves the original recursive body, is never silent and coverage
    is measurable.  Each outcome is validated against the postcondition that
    no self-call survives the transform.  [Set Crane Loopify Diagnostics]
    prints them as they are produced; [Set Crane Loopify Strict] turns a
    decline into an error.  What it did with each is a
    {!Loopify_analysis.loopify_outcome}. *)

(** Print the collapsed outcomes ([Crane Loopify Diagnostics]) and raise on any
    decline ([Crane Loopify Strict]). Call once per unit, after transforming.

    The [unit_name] prefixes each line so a decline can be traced to the
    compilation unit that produced it. *)
val report_outcomes : ?unit_name:string -> unit -> unit
