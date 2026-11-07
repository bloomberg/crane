(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Which reads of a local are its last use, decided over Core
    (docs/Pipeline-Disentangling-Plan.md, Milestone 7).

    A region is a term translation generates as one C++ body: a function's,
    a method's or a local fixpoint's, a lambda's, or that of a let standing
    where an expression is expected.  A variable bound in a region is read
    only inside it, so what is decided of its reads there is decided of all
    of them.  A read is a last use when, on every path through the region,
    nothing can read the variable after it, nor at the same time: the
    arguments of a call and the fields of a constructor are evaluated in an
    order C++ leaves open, so a variable read by two of them is read last by
    neither.  A pattern variable of a match on a variable is a part of it,
    which C++ binds by reference: moving the whole is not a last use while a
    part is still to be read, nor moving a part while the whole is, though
    two parts are independent; so is a component of a pair read through its
    projection, unless the read takes the whole pair ({!use}).  A let-bound local fixpoint, or a lambda
    with a type variable of its own, which may be lifted to a function
    template or inlined, may read what it closes over wherever it is used,
    so nothing it closes over is read last in the let's scope; a lambda
    bound to a local copies it where it is made.  An argument an inline custom's template
    splices twice is read twice, and one it never splices is not read.

    Each read gets a mode ({!Use}): a move where it is a last use of what
    the region owns, a borrow where it is read in place, else a copy, named
    by what a copy of the variable's Core type is. *)

type t

(** Nothing planned: no read is a last use. *)
val empty : t

(** Whether a body owning a value of ML type [ty] moves it at its last use:
    one a copy of which costs more than a move.  This is the reading
    {!worth_moving_cpp} makes, made of the ML type: an inductive that is not
    an enum or coinductive, a closure, a type variable or one applied to
    arguments, a type nothing determined (held in the box), and a mapped type unless it is a scalar or declared trivially
    copyable with arguments that are too. *)
val worth_moving : Miniml.ml_type -> bool

(** The same question asked of the C++ type a value is declared at: a
    reference count to bump, an inductive to clone, an erased box, or a type
    parameter that may be either.  What the backend asks of the locals and
    frame fields it declares itself. *)
val worth_moving_cpp : Minicpp.cpp_type -> bool

(** What both ask of the global type [r] applied to [args], [worth] judging
    an argument: an inductive unless an enum or coinductive, a mapped type
    unless a scalar or trivially copyable one with no argument worth moving.
    The question a type node instantiating a mapping asks of its mapping. *)
val worth_moving_ref : ('a -> bool) -> Names.GlobRef.t -> 'a list -> bool

(** A let a machine with a stack of frames resumes at: [calls], the
    occurrences of the recursive calls its right-hand side ends in, and
    [kept], the binders the frame saved for them keeps across them, which
    what follows the let reads in the frame rather than where they were
    bound; [held], those of [kept] the frame holds itself, rather than
    binding them again from what it holds -- the handler resuming there
    owns each, having moved its frame off the stack; [passed], those of
    [held] what follows passes on, as they are, to a parameter of a call
    entering the machine ({!Recursion_plan.passing}): a frame may keep one
    as a pointer to it, for an entry taking that parameter by pointer, so
    what follows does not own it. *)
type resume = {
  calls : Miniml.Occurrence.t list;
  kept : Core_binder.t list;
  held : Core_binder.t list;
  passed : Core_binder.t list;
}

(** The points the definition [origin], whose body is lowered as a machine
    with a stack of frames, resumes at, as [resume_at] finds them by the
    Core binder each binds: the region is that body, standing under
    [depth] of the definition's binders.  [entry_captures]: where the region
    is the body of a local fixpoint of one member that a machine adopts as an
    entry, [k], the region-relative level of the fixpoint's member (its
    parameters lie between it and the root): the machine enters it with its
    parameters and the variables it reads from below [k], its captures, a
    call of the member passing the captures as well, and the entry's frame
    holds each, the handler owning it as a frame's handler owns what the
    frame holds ({!resume.held}).  [parameter_type l]: the Core type of the
    parameter of the loop the machine runs that the definition's binder at
    level [l] is, where it is one. *)
type resumes = {
  origin : Names.GlobRef.t;
  depth : int;
  resume_at : Core_binder.t -> resume option;
  entry_captures : int option;
  parameter_type : int -> Miniml.ml_type option;
}

(** [region ~owned ~copied ~resumes ~n_outer t] is the plan of [t]'s reads,
    [t] standing under binders it reads but does not bind, of which it owns
    those at the de Bruijn indices [owned], and generated under a head of
    [n_outer] type variables.  The closures it makes capture a copy of each
    variable at [copied] -- a method's receiver, which they capture as a
    copy of the object -- and own that copy: it is theirs to move, and a
    read outside them reads the original.  Where [t] is lowered as a
    machine resuming at [resumes], a let whose right-hand side is one of
    the calls a point resumes after saves its frame before evaluating the
    call's arguments: the binders the frame keeps are not read after them,
    so an argument may be their last use -- where the region is [certain]ly
    lowered as that machine (the default).  Where it may be generated as it
    is, the saves are planned ({!save_moves}) but no read relies on one
    having been made.  [outer i]: the Core type of the variable bound
    outside [t] at the index [i] there, which says what a copy of it is
    ({!Use}). *)
val region :
  ?owned:int list ->
  ?copied:int list ->
  ?outer:(int -> Miniml.ml_type option) ->
  ?resumes:resumes ->
  ?certain:bool ->
  n_outer:int ->
  Miniml.ml_ast ->
  t

(** Whether, as [p] plans it, [let x : ty := a] binds the closure [a] to a
    C++ local, which the region owns: [a] is a local fixpoint or a lambda
    with no type variable of its own past the head's
    ({!Ml_type_util.own_type_variables}).  [None] where nothing is planned. *)
val closure_local : t -> Miniml.ml_type -> Miniml.ml_ast -> bool option

(** [reuse_arm p ~scrutinee ~branch ~constructor] is [p] for the branch
    numbered [branch] of the match on the variable [scrutinee], generated to
    rebuild a [constructor] in the scrutinee's storage: the fields it binds
    are moved out into locals of its own, and the scrutinee, which keeps the
    storage, is not read by value. *)
val reuse_arm : t -> scrutinee:Miniml.ml_ast -> branch:int -> constructor:Names.GlobRef.t -> t

module Allocation : sig
  type t =
    | Fresh  (** allocates the storage it is built in *)
    | Reuse
        (** is built in the storage the innermost rebuilding branch frees
            ({!reuse_arm}): one of the constructions of the rebuilt
            constructor that branch returns, never one it passes to a call
            or builds inside a closure *)
end

(** [allocation p e] -- where, as [p] plans it, the construction [e] is
    built. *)
val allocation : t -> Miniml.ml_ast -> Allocation.t

(** [fields_by_value p ~case ~by_value] is [p] for the body of [case], a
    match taking a record apart, whose fields translation binds as locals of
    their own where [by_value] says so, in the order the pattern binds them:
    those are the body's own. *)
val fields_by_value : t -> case:Miniml.ml_ast -> by_value:bool list -> t

(** [bound_at_instance p ~let_] is [p] for the let at the occurrence [let_],
    binding a lambda with a type variable of its own that translation binds
    to a local all the same, at the one instance its uses agree on
    ({!Translation_support.let_lambda}): the local is the region's own, and
    copies what it closes over where it is made. *)
val bound_at_instance : t -> let_:Miniml.Occurrence.t -> t


(** What [p] says of a read. *)
type fate =
  | Last_use
  | Read_again  (** a later or concurrent read, or a closure, may read it *)
  | Inspected
      (** a last use where translation reads the value in place: the
          scrutinee of a variant match, which binds its alternatives by
          reference, or of a custom match spelling it twice; the function an
          application calls.  Only the read standing in that position:
          the arguments of a call it makes are taken by value. *)
  | Unplanned  (** not a read of the region [p] was made of *)

(** What a read does with its variable's value.  A read that leaves the
    value, being read again or not owned where it stands, copies it, and
    says what the copy is, as the variable's Core type does -- a field stored
    behind a pointer is bound as the value it points at, an abbreviation is
    what it abbreviates. *)
module Use : sig
  type t =
    | Move
        (** takes it: the variable is owned where it is read, and the read is
            its last use where its value may be taken *)
    | Share
        (** copies a handle on a counted block, a retain: a closure, a
            coinductive's or shared variant's value *)
    | Clone
        (** copies the value itself, a copy worth a move
            ({!worth_moving}): an inductive's value, a mapped type's that is
            neither a scalar nor trivially copyable, one a type variable
            stands for, a box *)
    | Copy  (** copies bits moving would not spare: a scalar, an enum *)
    | Borrow  (** reads it in place ({!Inspected}) *)
end

(** [use ~whole p o]: with [~whole], of a read that takes its variable's
    whole value even where Core reads one component of it, or reads it in
    place ({!Inspected}): a closure captures the whole of what it reads, and
    a variable held boxed is unboxed whole by a cast.  With [~boxed], of a
    variable held boxed: read whole, and a copy of it copies the box, a
    [Clone].  [declared]: the C++ type the variable is declared at, which
    says what a copy is only where its Core type is one inference gave up
    on -- the slot it is bound in typed it, or else it is held in a box.
    [None] of a read the plan was not made of: translation lowering it
    reached a term the region it planned does not contain. *)
val use :
  ?whole:bool -> ?boxed:bool -> ?declared:Minicpp.cpp_type -> t -> Miniml.Occurrence.t -> Use.t option

(** What a copy of a variable declared at the C++ type [ty] is, as {!Use}
    names it: what the C++ a read is lowered to does, which the plan's
    reading of the Core type must agree with. *)
val copy_of_declared : Minicpp.cpp_type -> Use.t

(** [evaluated_first p at]: the positions among its arguments of those the
    local fixpoint applied where it is written, at the occurrence [at],
    reads before the call, in order.  The plan binds such a fixpoint's
    parameters to its arguments in order, so that an argument may be the
    last use of a variable an earlier one reads; a call leaves its
    arguments unordered, and the earlier one is evaluated first: each
    reading a variable, or a part of one, that a later argument moves. *)
val evaluated_first : t -> Miniml.Occurrence.t -> int list

(** Whether a match taking the record [t] apart takes its value, as [p]
    plans it, rather than reading it in place: [t] is not a variable read by
    copy or in place, a global naming which reads it, or a field of one.
    What else it is, a value computed, a variable moved, or a global named by
    calling it -- a cofixpoint, or one that only throws -- is evaluated once
    into a local of its own, which the fields are moved out of. *)
val takes_record : t -> Miniml.ml_ast -> bool

(** Whether a variant match takes apart a scrutinee the region owns, binding
    its fields by mutable reference: the scrutinee is a variable owned there.
    One named through an application is read in place. *)
val owns_scrutinee : t -> Miniml.ml_ast -> bool

(** Whether a custom match on a pair binds its components by value, being
    the pair's last reader: the pair its scrutinee has just built, or a
    variable owned there that its one branch does not read whole. *)
val pair_by_value : t -> Miniml.ml_ast -> Miniml.ml_branch array -> bool

(** Whether a let of type [ty] bound to [a] binds by reference the field [a]
    projects out of a record that is not moved there. *)
val projects_in_place : t -> Miniml.ml_type -> Miniml.ml_ast -> bool

(** How a closure holds a variable it reads from the scope it is made in. *)
module Capture : sig
  type t =
    | By_reference
        (** reads it where it stands: a local fixpoint generated in place
            ({!Analyze_closures.In_place}), which runs while the scope does *)
    | By_move
        (** takes its value where it is made: the variable is owned there,
            and the capture is its last use -- nothing after the closure,
            beside it, or captured with it reads it *)
    | Shared
        (** holds a copy of its own, made where it is made, the variable
            left to the scope: what the copy is, the variable's {!Use}
            says *)
end

(** Where a value a machine's frame holds across a call is stored
    ({!Frame_storage}). *)
module Storage : sig
  type t =
    | Local
        (** where the machine's caller keeps it -- a parameter, or a field
            bound into one, which outlives the machine and which nothing
            changes while it runs: the frame holds a pointer to it *)
    | Frame  (** in the frame itself, a value of its own *)
end

(** Each variable the lambda or local fixpoint [closure] reads from the
    scope it is made in, by its de Bruijn index at [closure], in order,
    with how it holds it: generated as closures that copy what they
    capture, [By_move] or [Shared]; with [~in_place], generated in place,
    [By_reference]. *)
val captures : ?in_place:bool -> t -> Miniml.ml_ast -> (int * Capture.t) list

(** Of the local fixpoint [fix], generated as closures, one per function,
    for each function in order, each variable its closure reads from the
    scope, by its de Bruijn index at [fix], with how it holds it: the last
    function reading a variable {!captures} takes [By_move] takes it so,
    those made before it share it.  [[]] where [fix] is no fixpoint. *)
val captures_by_member : t -> Miniml.ml_ast -> (int * Capture.t) list list

(** Each variable the terms [ts] read, by its de Bruijn index where they
    stand, with how a closure made around them holds it -- the
    eta-expansion of a partial application of which they are the arguments:
    [By_move] what they read by move ({!use}) directly, not inside a let or
    a match they contain, and what a closure among them takes by move
    ({!captures}); the rest [Shared]. *)
val eta_captures : t -> Miniml.ml_ast list -> (int * Capture.t) list

(** A term copied to two places -- an eta argument pushed into both branches
    of a conditional -- holds one read twice; it is a last use where every
    copy is one. *)
val fate : ?whole:bool -> t -> Miniml.Occurrence.t -> fate

(** What a [Continue] moves into the next value of one of its loop's
    parameters: nothing ([Keep]); the parameter itself, read once by the
    argument passed it ([Move_parameter]); or the argument whole, a local of
    the turn, at the last read of it the lowering makes ([Move_argument]). *)
module Continue_move : sig
  type t = Keep | Move_parameter | Move_argument
end

(** For each [Continue] of the loop [l] itself, by the occurrence of the
    call it is made of, and for each of [l]'s parameters, outermost first,
    what the turn moves into the parameter's next value.  [Move_parameter]:
    the argument passed it reads it once, as the turn's last read of it --
    no other argument, nor a closure reading at its uses, reads it or a part
    of it -- and is not that read alone, and the parameter's type is worth
    moving.  A loop keeps each parameter it varies in a local of its own,
    which the next turn's value replaces: the read is the local's last.
    [Move_argument]: the argument is a variable the turn binds and owns,
    read there whole, at a type worth moving, and after it by nothing but
    the Continue's other arguments naming it -- not a part of it, which may
    be bound into it: the lowering, which orders the arguments' evaluation,
    moves it at the last of those reads it makes.  Whether a
    parameter is kept in a local, rather than by pointer, is the lowering's
    to say.  A machine's loop moves nothing so. *)
val continue_moves : Control_ir.Term.loop -> (Miniml.Occurrence.t * Continue_move.t list) list

(** [save_moves p let_]: of the let at the occurrence [let_], a point a
    machine with a stack of frames resumes at ({!resumes}), the binders the
    frame saved for its call keeps that the save may move into the frame:
    each owned there, and the save its last read in the turn -- the call's
    arguments, evaluated after it, read neither it nor a part of it, nothing
    reads it at a closure's uses or after the let, and the frame keeps no
    part of it, nor anything it is a part of, beside it.  What follows the
    let reads it in the frame.  [None] of a let no point resumes at. *)
val save_moves : t -> Miniml.Occurrence.t -> Core_binder.t list option

(** Which binders each frame saved at a resume point moves into it, by the
    Core binder of the let the machine resumes at: what translation, which
    holds the plan, says ({!save_moves}) where it generates that let, read by
    the frame machine ({!Loopify_frame}) where it saves the frame. *)
module Frame_save : sig
  type t = Core_binder.t list

  (** [record binder t]: the frame saved at the let binding [binder] moves
      the binders [t].  A let generated twice is generated alike: under
      [CRANE_CHECK_IR], recording another set is a violation, and only what
      both move is moved. *)
  val record : Core_binder.t -> t -> unit

  val lookup : Core_binder.t -> t option
end

(** How each function of a local fixpoint passes its parameters -- the
    callable plan of a function with no global, which the frames of its
    machine read ({!Storage}): for each of its Core
    parameters, outermost first, how the lambda it is generated as takes
    it, [None] for one of no runtime value, which the lambda does not take.
    Translation decides it once per group, before generating the group's
    lambdas from it and before any loop is lowered from them
    ({!Translation.local_passing}). *)
module Local_passing : sig
  type t = Callable_abi.passing option list

  (** [record member t]: the function [member] -- the fixpoint's
      occurrence, and the function's position in it -- passes its
      parameters as [t].  A member generated twice is generated alike:
      under [CRANE_CHECK_IR], recording another plan is a violation. *)
  val record : Miniml.Occurrence.t * int -> t -> unit

  (** What was recorded of [member]: [None] where it is generated as no
      lambda (a lifted helper's plan is its global's). *)
  val lookup : Miniml.Occurrence.t * int -> t option
end

(** [entry_moves p]: of each call [p]'s region makes that may enter a
    frame of the machine it is certainly lowered as -- of the definition
    itself, of a local function (the member of the fixpoint whose body the
    region is, perhaps an adopted entry: {!resumes.entry_captures}), or a
    local fixpoint applied where it is written -- the binders the frame
    entering there may take: the arguments that are variables read last,
    and the captures an adopted entry takes besides them read by nothing
    after the call nor beside it, each owned there, or held by the entry's
    frame.  The frame holds each by value, where the callee may have lent
    it. *)
val entry_moves : t -> (Miniml.Occurrence.t * Core_binder.t list) list

(** A region's plan, as {!Entry_moves} names it. *)
type region_plan = t

(** Which binders the frame entering a machine's entry at each call takes,
    by the call's occurrence: what translation, which holds the plan, says
    ({!entry_moves}) where it plans the region, read by the frame machine
    ({!Loopify_frame}) where it pushes the frame. *)
module Entry_moves : sig
  type t = Core_binder.t list

  (** [record call t]: the frame entering an entry at [call] moves [t].
      Recording another set is a violation under [CRANE_CHECK_IR], and only
      what both move is moved. *)
  val record : Miniml.Occurrence.t -> t -> unit

  (** [record_plan p]: {!record} of every call {!entry_moves} plans. *)
  val record_plan : region_plan -> unit

  val lookup : Miniml.Occurrence.t -> t option
end
