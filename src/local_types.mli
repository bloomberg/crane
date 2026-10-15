(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The types a local definition leaves open are its own variables.

    Extraction leaves a metavariable wherever nothing outside a local
    definition fixes one of its types -- [let fix len {B} (xs : list B)] says
    nothing of [B], nor [let id := fun x => x] of [x]'s -- and the definition
    is lifted to a C++ template over exactly those variables.  {!structure}
    mints them before the program is frozen, so that lowering a body solves
    no metavariable of the frozen program; lowering checks what it finds
    instead ({!check_minted}, {!check_let_lambda}). *)

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
    the shape it is lowered in. *)
val check_minted : (Names.Id.t * Miniml.ml_type) array -> unit

(** [check_let_lambda ~outer t a] -- under [CRANE_CHECK_IR], the lambda [a]
    bound at [t], about to be lowered under a head of [outer] variables, is
    a violation if a type of it is still open, or if its variables were
    minted past some other number than [outer], so that they would collide
    with the head's or leave a gap.  The second is checked where the minted
    cells are still found in [t] or [a]'s annotations. *)
val check_let_lambda : outer:int -> Miniml.ml_type -> Miniml.ml_ast -> unit

(** Mints the open variables of every local definition of the structure's
    declarations, rigid: they are the definition's, and a substitution for
    the variables around it -- an instance method's body takes its class's
    -- must not capture them.

    A recursive group's are minted at each of the shapes translation lowers
    one in -- a let-bound group's signatures; an applied group's signatures,
    bodies and arguments; a bare group's signatures -- each numbered from
    [1], as its lifting expects, after the codomains its bodies determine
    are filled.  A let-bound lambda's, everything it contains included, are
    numbered past the variables of the declaration it is in, which name its
    head's. *)
val structure : Miniml.ml_structure -> unit
