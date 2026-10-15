(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The types a local definition leaves open are its own variables.

    Extraction leaves a metavariable wherever nothing outside a local
    fixpoint fixes one of its types -- [let fix len {B} (xs : list B)] says
    nothing of [B] -- and the fixpoint is lifted to a C++ template over
    exactly those variables.  {!structure} mints them before the program is
    frozen, so that no fixpoint's generation solves a metavariable of the
    frozen program; a let-bound lambda's are still minted where it is
    generated, numbered past the template head it is generated under, as
    {!Miniml.Meta.Let_lambda_variable} says. *)

(** [mint ?late ~rigidity ~next ty] solves every unsolved metavariable of
    [ty], in order, to a variable of [rigidity] numbered [!next], [!next + 1],
    and so on, advancing [next]; [late] says why, after freezing. *)
val mint :
  ?late:Miniml.Meta.late_solution ->
  rigidity:Miniml.tvar_rigidity ->
  next:int ref ->
  Miniml.ml_type ->
  unit

(** [mint_in_ast mint e] applies [mint] to every type [e] annotates, in
    order.  A global use is not walked: its instantiation was frozen by
    extraction and holds no metavariable, and a hole in it is not to be
    renumbered into one of the caller's variables. *)
val mint_in_ast : (Miniml.ml_type -> unit) -> Miniml.ml_ast -> unit

(** [recover_fix_codomains ids funs] -- a recursive group's signatures and
    bodies, with each function's codomain recovered from its body where
    erasure lost it: a variable no parameter mentions, where a tail position
    builds a constructor, is that constructor's inductive.  Returned in new
    arrays: a group's own are shared by every declaration its definition
    was inlined into, [Fix_F] into each function defined by well-founded
    recursion. *)
val recover_fix_codomains :
  (Names.Id.t * Miniml.ml_type) array ->
  Miniml.ml_ast array ->
  (Names.Id.t * Miniml.ml_type) array * Miniml.ml_ast array

(** Under [CRANE_CHECK_IR], a group about to be lowered whose signatures
    still hold an unsolved metavariable is a violation: {!structure} missed
    the shape it is lowered in, and lowering would decide the variable. *)
val check_minted : (Names.Id.t * Miniml.ml_type) array -> unit

(** Mints the open variables of every local fixpoint of the structure's
    declarations, at each of the shapes translation lowers one in: a
    let-bound group's signatures, an applied group's signatures, bodies and
    arguments, a bare group's signatures.  Each group numbers its own from
    [1], as its lifting expects, and they are rigid: they are the group's,
    and a substitution for the variables of the declaration around it -- an
    instance method's body takes its class's -- must not capture them.  A
    group inside a let-bound lambda is left to the lambda, which mints
    everything it contains. *)
val structure : Miniml.ml_structure -> unit
