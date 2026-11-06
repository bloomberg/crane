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

    This is not yet the plan's OwnershipIR: it decides no use's mode, only
    which reads a move may be made at. *)

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
    owns each, having moved its frame off the stack. *)
type resume = {calls : Miniml.Occurrence.t list; kept : Core_binder.t list; held : Core_binder.t list}

(** The points the definition [origin], whose body is lowered as a machine
    with a stack of frames, resumes at, as [resume_at] finds them by the
    Core binder each binds: the region is that body, standing under
    [depth] of the definition's binders. *)
type resumes = {origin : Names.GlobRef.t; depth : int; resume_at : Core_binder.t -> resume option}

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
    so an argument may be their last use. *)
val region : ?owned:int list -> ?copied:int list -> ?resumes:resumes -> n_outer:int -> Miniml.ml_ast -> t

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

(** What a read does with its variable's value. *)
module Use : sig
  type t =
    | Move
        (** takes it: the variable is owned where it is read, and the read is
            its last use where its value may be taken *)
    | Copy
        (** reads it by value and leaves it: the variable is read again, or
            is not owned there *)
    | Borrow  (** reads it in place ({!Inspected}) *)
end

(** [use ~whole p o]: with [~whole], of a read that takes its variable's
    whole value even where Core reads one component of it, or reads it in
    place ({!Inspected}): a closure captures the whole of what it reads, and
    a variable held boxed is unboxed whole by a cast.  [None] of a read the
    plan was not made of: translation lowering it reached a term the region
    it planned does not contain. *)
val use : ?whole:bool -> t -> Miniml.Occurrence.t -> Use.t option

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

(** The de Bruijn indices, at [closure], of the variables the lambda or
    local fixpoint [closure] takes by move when it is made, as closures that
    copy what they capture: each is owned there, and the capture is its last
    use -- nothing after the closure, beside it, or captured with it reads
    it. *)
val moved_captures : t -> Miniml.ml_ast -> int list

(** Of the local fixpoint [fix], generated as closures, one per function,
    for each function in order, the de Bruijn indices at [fix] of the
    variables its closure takes by move ({!moved_captures}): each the last
    function reading it takes, those made before it copying it.  [[]] where
    [fix] is no fixpoint. *)
val moved_captures_by_member : t -> Miniml.ml_ast -> int list list

(** The de Bruijn indices, at [ts], of the variables [ts] read by move
    ({!use}) directly -- not inside a closure, a let or a match they
    contain -- and those a closure among them takes by move
    ({!moved_captures}): what a closure made around them, the eta-expansion
    of a partial application of which they are the arguments, takes by move
    when it is made. *)
val moved_reads : t -> Miniml.ml_ast list -> int list

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
    machine read ([Storage.Frame], plan 4.10): for each of its Core
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
