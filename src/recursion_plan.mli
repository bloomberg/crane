(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How each function of a normalized program recurses, read off its Core
    body before any function is lowered, so that the decision to make a loop
    of a function is a fact about the program
    ({!Program_facts.analyze_program}) rather than something the C++ printer
    rediscovers; Loopify transforms a function by it.

    A call is a tail call where the function's result is the call's.  The
    effect operations are read as {!Core_effects} elaborates them: in a
    sequential computation the continuation of a [bind] and the value of a
    [ret] stand where the operation does.  A custom whose replacement text is
    just its one argument stands for that argument.  The plan is per
    recursive group ({!Recursive_groups}), exactly one each, and a member
    recurses by the calls of itself it makes once its partners are spliced
    into it ({!splice_partners}).  A function on no cycle does not
    recurse.

    For a function that does not recurse only by tail calls, the plan also
    reads the constructors its result is built of around its calls, which
    decide whether it is lowered tail modulo cons ({!strategy}). *)

(** How a function, or a recursive group, recurses. *)
type kind =
  | No_recursion  (** it makes no recursive call *)
  | Tail  (** every recursive call is a tail call *)
  | Nontail  (** some recursive call is not *)

(** A recursive group's plan: its members, in definition order, and how
    the group recurses: as the member that recurses most. *)
type group = private {
  members : Names.GlobRef.t list;  (** in definition order *)
  kind : kind;  (** that of the member that recurses most *)
}

(** The plan of a whole program: a {!group} per recursive group, and the
    strategy, calls, resume points and adoptable fixpoints of each function
    and local fixpoint. *)
type t

(** The plan of a program that defines nothing. *)
val empty : t

(** [analyze groups p] plans every function the normalized program [p]
    defines, in the recursive groups [groups]. *)
val analyze : Recursive_groups.t -> Core_phase.normalized Core_phase.program -> t

(** Whether two plans decide every function and fixpoint alike. *)
val equal : t -> t -> bool

(** The effect operation the use [use] is, where [effects] says it is
    generated sequentially: a bind's continuation and a ret's value then
    stand where the operation does. *)
val sequential : Core_effects.t -> Miniml.global_use -> Core_effects.operation option

(** Whether the custom [r]'s replacement text is its one argument, which is
    then where the custom is. *)
val identity : Names.GlobRef.t -> bool

(** Whether translation generates a match at [ty] over [branches] standing
    as a let's right-hand side as statements, each branch assigning the
    binder -- a custom match, or a record's one branch -- rather than in a
    lambda invoked in place, as it does any other.  A recursive call only
    the latter's branches end in is not a point the let resumes at. *)
val match_bound_in_place : Miniml.ml_type -> Miniml.ml_branch array -> bool

(** What [t] lowers to loops of tail calls alone: the functions planned
    {!Tail_loop}, and the local fixpoints of one member planned so, by
    occurrence. *)
val tail_loops : t -> Names.GlobRef.t list * Miniml.Occurrence.t list

(** The functions [t] reads constructor chains around the calls of, for
    them to be lowered tail modulo cons ({!Modulo_cons}), in a group none of
    whose members suspends, and the local fixpoints of one member it reads
    so, by occurrence.  Whether one is so lowered also depends on how its
    constructors store their fields ({!strategy}). *)
val modulo_cons_loops : t -> Names.GlobRef.t list * Miniml.Occurrence.t list

(** The functions [t] finds recursing by a call that is not a tail call, in
    a group none of whose members suspends, that it reads no constructor
    chains for: those lowered with a stack of frames ({!Frame_stack}); and
    the local fixpoints of one member it finds so, by occurrence. *)
val frame_loops : t -> Names.GlobRef.t list * Miniml.Occurrence.t list

(** [e] with each temporary {!Normalize} bound a call, where it is read
    once, put back where it is read: the body the constructor chains are
    read off. *)
val restore_temporaries : Miniml.ml_ast -> Miniml.ml_ast

(** Make [t] the extraction's plan, the one {!strategy} reads. *)
val install : t -> unit

(** The plan of the group of the function [r], if [r] is on a cycle. *)
val group_of : Names.GlobRef.t -> group option

(** A constructor applied around a recursive call: its argument [hole], in
    the constructor's declared order, holds the call. *)
type cell = private {
  constructor : Names.GlobRef.t;
  hole : int;  (** the argument holding the call, in declared order *)
}

(** The constructors around one recursive call, outermost first, the
    innermost holding the call itself. *)
type chain = private {
  around : cell list;  (** outermost first, the innermost excluded *)
  innermost : cell;  (** the cell holding the call itself *)
}

(** How a function's recursion is lowered, one per function. *)
type strategy =
  | No_loop  (** it does not recurse *)
  | Tail_loop  (** every recursive call is a tail call, and becomes a jump *)
  | Modulo_cons of chain list
      (** tail modulo cons: each call that is not a tail call is the one
          call of one of these chains, all ending in the same cell, which is
          left empty and filled by the next turn of the loop; there is at
          least one *)
  | Frame_stack  (** some call is not a tail call: an explicit stack *)
  | Suspended of kind
      (** it recurses so, but its body, or a partner's, suspends a
          computation: a coinductive result built at a constructor whose
          arguments may run the corecursion, or suspended whole.  Its calls
          run when the suspension is forced, after it has returned, and
          there is no stack for a loop to save. *)

(** The kind of recursion a strategy lowers. *)
val kind_of_strategy : strategy -> kind

(** The strategy of the function [r], if the program defines it: the kind
    of its own calls, the copies of its partners spliced into it
    ({!splice_partners}) included, whether the group suspends
    ({!Suspended}), and for a member that does not recurse only by tail
    calls whether it is lowered tail modulo cons.  It is, where each call
    that is not a tail call is the one call of a chain of constructor
    applications in tail position, the innermost holding it directly, read
    off [r]'s Core body with {!Normalize}'s temporaries put back.
    Every chain ends in the same constructor, holding the call at the same
    argument, which its constructor stores behind the pointer, and every
    constructor in a chain stores some field there: [pointer_fields c] are
    the arguments of [c] so stored, [None] where it stores none
    ({!Loopify_analysis.constructor_pointer_fields}). *)
val strategy :
  pointer_fields:(Names.GlobRef.t -> int list option) -> Names.GlobRef.t -> strategy option

(** The strategy of the function [member] of the local fixpoint
    [occurrence], if the program has that fixpoint: planned from its body as
    a definition's is, every call between the members of its group
    counting.  A helper lifted for that function is planned by it
    ({!Lifted.fixpoint}). *)
val strategy_at :
  pointer_fields:(Names.GlobRef.t -> int list option) ->
  Miniml.Occurrence.t * int ->
  strategy option

(** The strategy of a helper lifted for the lambda the let [occurrence]
    binds, if the program has that let: no loop, for a lambda bound by a
    let does not call itself. *)
val strategy_of_let : Miniml.Occurrence.t -> strategy option

(** The local fixpoints the machine of the function [r], lowered by an
    explicit stack, may adopt as a second entry: those in its flow -- run
    where its body runs, not under a lambda nor in another local fixpoint --
    some member of which names a function of its recursive group, read in
    its body as translation generates it.  Two machines cannot unwind each
    other's stack, so such a fixpoint is lowered inside [r]'s; the first of
    them in the flow that lowering can take is adopted
    ({!Loopify_frame.find_adopted}). *)
val adoptable : Names.GlobRef.t -> Miniml.Occurrence.t list

(** {!adoptable} in the plan [t]. *)
val adoptable_in : t -> Names.GlobRef.t -> Miniml.Occurrence.t list

(** [splice_partners ~loopified ~inlines p]: [p], a program being
    normalized, with the partners of each function [loopified] says it
    loopifies, in its recursive group, spliced into its Core body, a copy
    that is new terms.  A partner is spliced at the calls of it that run in
    the function's statements, read off the body as translation generates
    it: the first partner whose call runs there at every such call at once,
    then the next, each once, until no partner's call runs there.  A call
    runs in the statements unless it stands in a lambda -- a closure's body,
    a local fixpoint's, a suspended constructor argument, or a match, let,
    fixpoint or bind standing as an operand, or a match bound by a let,
    which translation runs in a lambda invoked in place -- or in an enum's
    match.  Each tail call is replaced by the partner's body, its
    parameters bound to the call's arguments ({!Core_copy.call}), where the
    next partners' calls are read too.  A call that runs in place of one,
    where [inlines] says the function takes its partners' bodies at such
    calls -- a method does not -- is entered where the partner yields what
    the function does, its body, run there, calls the function back, each
    of its uses of itself is a call made there -- the copy entered is no
    value a closure could call -- and no other partner is entered: a copy of it is bound in front of the body, a
    local fixpoint whose calls of the partner are its own, and each such
    call is a call of the copy ({!Splices.entered_copy}).  Any other is
    replaced by a copy of the partner's body as a tail call is, run where
    the call was, where no partner's call is read.  Once no partner is left
    to splice, a partner whose copies brought calls of it that are not tail
    calls is entered at them so, where none is entered yet: they would
    otherwise be calls of another function, made on the C++ stack at every
    turn that passes through them.  A function that does not call itself
    once spliced into, which makes no loop, is left as it is.  A function
    some partner of which is spliced in neither way, or whose partner's body
    would need instantiating -- a call solving one of its variables, a
    partner of more or fewer variables or another monad, or one suspended
    whole -- is left as it is, calling its partners, and so is every
    function of its recursive group.  A custom is not generated, and splices
    nothing.  The functions decided, and the copy each enters, are
    recorded in [p]'s splices: splicing again leaves a function decided as
    it is, so normalizing the result again rewrites nothing. *)
val splice_partners :
  loopified:(Names.GlobRef.t -> bool) -> inlines:(Names.GlobRef.t -> bool) -> Core_phase.normalizing -> Core_phase.normalizing

(** Whether functions of types [a] and [b] yield one type, once every
    abbreviation is unfolded and a variable of the definition's scheme is
    read alike whether it is written as the scheme's or as rigid. *)
val yields_alike : Miniml.ml_type -> Miniml.ml_type -> bool

(** {!adoptable} for the function [member] of the local fixpoint
    [occurrence], lowered as a helper of its own ({!Lifted.fixpoint}): the
    fixpoints in its flow naming a member of its group. *)
val adoptable_at : Miniml.Occurrence.t * int -> Miniml.Occurrence.t list

(** Whether some machine may adopt the local fixpoint [occurrence]: a
    function's ({!adoptable}) or that of a helper lifted for a fixpoint of
    [lifted] ({!adoptable_by_fixpoint}). *)
val adoptable_somewhere : lifted:Miniml.Occurrence.t list -> Miniml.Occurrence.t -> bool

(** Whether the machine of a helper lifted for the function of one of the
    local fixpoints [lifted] may adopt the local fixpoint [occurrence]
    ({!adoptable_at}).  A fixpoint generated as a lambda adopts nothing: its
    machine has one entry. *)
val adoptable_by_fixpoint : lifted:Miniml.Occurrence.t list -> Miniml.Occurrence.t -> bool

(** The calls of the function [member] of the local fixpoint [occurrence]
    made in its group's bodies, each by the occurrence of the read at its
    head, which the C++ call made of it records
    ({!Minicpp.call_sig.cs_occurrence}): the recursive calls a loop of that
    function takes. *)
val member_calls : Miniml.Occurrence.t * int -> Miniml.Occurrence.t list

(** The calls of the function [r] made in its recursive group's bodies,
    each by the occurrence of the use heading it, which the C++ call made
    of it records ({!Minicpp.call_sig.cs_occurrence}): the recursive calls
    of [r], the copies of its partners spliced into its body included.
    Empty for a function on no cycle. *)
val calls : Names.GlobRef.t -> Miniml.Occurrence.t list

(** Whether the bodies of the group of the local fixpoint [occurrence] read
    its function [member] other than at the head of a call: the function
    named as a value, which a loop made of it, no longer a function, cannot
    stand for. *)
val named_as_value : Miniml.Occurrence.t * int -> bool

(** The calls entering the local fixpoint of one member at [occurrence],
    each by the occurrence its C++ call records: its own ({!member_calls}),
    and those made where it is bound -- the fixpoint applied there, by its
    occurrence, or the reads of the let binding it.  What a machine
    adopting the fixpoint reroutes to its entry. *)
val entering : Miniml.Occurrence.t -> Miniml.Occurrence.t list

(** A recursive call a function resumes after: a call of the function of
    the group [Function g], with no fewer arguments than its parameters --
    one with fewer is a closure, and calls where it runs; a call of the
    member [m] of the local fixpoint at [Member (occurrence, m)]; or that
    fixpoint applied where it is written, reaching a recursive call, at
    [Entering occurrence].  Which of them a machine is entered by is the
    machine's: a function's own calls, the members of a fixpoint it
    adopts. *)
type target =
  | Function of Names.GlobRef.t
  | Member of Miniml.Occurrence.t * int
  | Entering of Miniml.Occurrence.t

(** A call a function resumes after: what it calls, and the occurrence the
    C++ call made of it records ({!Minicpp.call_sig.cs_occurrence}) -- the
    global's use, the read of the member at its head, or the fixpoint's
    own where it is applied as written.  Two calls ending two branches of
    one right-hand side are told apart by it. *)
type call = private {
  target : target;
  occurrence : Miniml.Occurrence.t;
}

(** Where a function goes on once a recursive call returns: [binder], the
    binder the call's result is bound to, [live], the binders bound before
    it that what follows reads as values -- what a frame keeps across the
    call: not a dictionary the declaration takes, nor a member of a local
    fixpoint the point is in that what follows only calls -- [after], the
    calls its right-hand side ends in, [passes], the binders of [live] what
    follows hands on unchanged to one of those calls ({!passing}), and
    [read_by_call], those of [live]
    those calls read: their arguments, directly or through a closure a let
    binds, and what a local fixpoint called captures -- a closure reads what
    it captures when it is called, and a machine adopting the fixpoint takes
    its captures as arguments.  They are still read where the frame for the
    call is saved, the call being made after.  [recomputable] are the
    binders in scope, outermost first, whose value makes no call: a frame
    may bind one again from what it reads rather than keep it. *)
type resume = private {
  binder : Core_binder.t;
  live : Core_binder.t list;
  after : call list;
  passes : passing list;
  read_by_call : Core_binder.t list;
  recomputable : recomputable list;
}

(** A binder of [live] that what follows passes on, as it is, to the
    recursive call [call], one entering the machine there -- its value what
    a let or a bind binds, or what follows returns: [passed], the argument,
    for [into], the parameter of the function called, the argument read
    through the coercions keeping its representation ({!in_place}).  What
    follows an enclosing point keeping the binder too passes it on here as
    well, the frames of the two keeping it alike.  A call whose value goes
    into some other term, or under a lambda, or in a local fixpoint's bodies,
    passes nothing here. *)
and passing = private {
  passed : Core_binder.t;
  into : Core_binder.t;
  call : call;
}

(** A binder whose value makes no call: a closure a let binds, which reads
    the binders it captures, or a pattern variable of the one branch of a
    record's match on a variable, a field of that variable, which
    translation binds as a statement.  [from] are the binders it reads,
    dictionaries left out: a declaration takes those as template arguments,
    in scope everywhere. *)
and recomputable = private {
  recomputed : Core_binder.t;
  from : Core_binder.t list;
}

(** Whether a coercion from [from] into [into] keeps the value's
    representation: two instances of one inductive agreeing on the
    arguments its C++ type takes, those of its parameters
    ({!Table.get_ind_num_param_vars_opt}); its indices it does not take. *)
val in_place : Miniml.ml_type -> Miniml.ml_type -> bool

(** The points binding [b] at which its definition, a member of a group that
    does not recurse only by tail calls, resumes after a recursive call: a
    let whose right-hand side is the call, or ends in one in some branch,
    and a sequential bind's continuation, in the definition's body or a
    local fixpoint's.  A call under a lambda is not one.  A point's binder
    records its let or bind ({!Core_binder.site}): two lets of one
    definition at one level, in two branches, both bind [b] only where [b]
    records neither. *)
val resumes_binding : Core_binder.t -> resume list
