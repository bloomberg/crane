(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** ControlIR (docs/Pipeline-Disentangling-Plan.md, sections 4.9 and 6.4):
    a function's control as it is implemented, before any C++ is chosen for
    it.  The terms it does not change stay Core ({!Miniml.ml_ast}); what it
    makes explicit is where control goes.

    This first version holds the loops of direct tail recursion: a function
    that recurses only by tail calls is a [Loop] over its parameters, each
    of its recursive calls a [Continue] of it, and every other way out a
    [Return].  {!Lower_control} produces them. *)

(** What a loop is the loop of: a function of the program, or the member
    [m] of the local fixpoint [occurrence]. *)
module Loop : sig
  type t =
    | Function of Names.GlobRef.t
    | Member of Miniml.Occurrence.t * int

  val equal : t -> t -> bool
end

module Term : sig
  type t =
    | Loop of loop
    | Let of let_
    | Match of match_
    | Return of Miniml.ml_ast
    | Continue of continue_

  (** The loop [loop] over [parameters], outermost first, running [body]. *)
  and loop = {
    loop : Loop.t;
    parameters : (Miniml.ml_ident * Miniml.ml_type) list;
    body : t;
  }

  (** [value] bound to [binder] while [body] runs: a let, or a sequential
      bind's action and its continuation's parameter. *)
  and let_ = {
    binder : Miniml.ml_ident;
    binder_type : Miniml.ml_type;
    value : Miniml.ml_ast;
    body : t;
  }

  and match_ = {
    scrutinee_type : Miniml.ml_type;
    scrutinee : Miniml.ml_ast;
    branches : branch list;
  }

  and branch = {
    binders : (Miniml.ml_ident * Miniml.ml_type) list;
    result_type : Miniml.ml_type;
    pattern : Miniml.ml_pattern;
    body : t;
  }

  (** The next turn of [target], its parameters taking [arguments]: the
      recursive call made of [occurrence], the use of the global or the read
      of the member heading it. *)
  and continue_ = {
    target : Loop.t;
    occurrence : Miniml.Occurrence.t;
    arguments : Miniml.ml_ast list;
  }
end

(** The occurrences of the calls [t] continues a loop by, in order. *)
val continues : Term.t -> Miniml.Occurrence.t list

(** [t] with [f] applied to the value of every [Return] in it. *)
val map_returns : (Miniml.ml_ast -> Miniml.ml_ast) -> Term.t -> Term.t
