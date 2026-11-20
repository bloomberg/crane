(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Which parameters of each function are owned and which borrowed, settled
    across calls.

    {!Escape.infer_owned_params} decides one function at a time, and reads a
    parameter handed to a callee as merely read.  But when the callee owns
    that parameter -- stores it, captures it, returns it -- a borrowed
    argument is copied at the call, where an owned one would have been
    moved: a retain, and a release when the callee is done with its copy.
    So a parameter passed directly to an owned parameter is owned too, and
    since owning one parameter can make a caller own its own, the flags are
    the least fixed point over every function of the structure, starting
    from every parameter borrowed. *)

(** [read_off ~settled params body]: of each parameter of [params],
    innermost first, whether [body], standing under them, owns it, as
    [settled] says of its callees' parameters: it lets the parameter escape
    ({!Escape.infer_owned_params}, told [matches_reuse]), or the parameter
    is a pair whose components it lets escape, which a pair taken by value
    moves out. *)
val read_off :
  ?matches_reuse:bool ->
  settled:(Names.GlobRef.t -> bool list option) -> ('name * Core.Type.t) list -> Core.Expr.t -> bool list

(** The flags of [struc]'s functions, settled across calls: each
    function's, innermost first, for the parameters its head declares,
    eta-expansion's included ({!Base.Type_util.declared_parameters}).  A
    custom constant has none: its mapping, not its body, is what a call to
    it runs.  [receiver r] is the position, outermost first, of the
    parameter the function [r] generated as a method takes as its receiver,
    which is borrowed. *)
val summarize :
  ?receiver:(Names.GlobRef.t -> int option) -> Core.Program.t -> (Names.GlobRef.t * bool list) list

(** The functions of [struc] whose matches may reuse the cell they take
    apart ({!Core_to_cpp.Match}): those Loopify leaves alone, not being
    loopified, and constants with no local fixpoint
    ({!Escape.loop_free}), which have no recursion for it to rewrite.  The
    others' scrutinees are owned for reuse only where a loop's cursor may
    recycle them. *)
val reusing_matches : Core.Program.t -> Core.Ref.User.Set.t

(** Every function [struc] defines, in a functor or not: a constant with a
    parameter, and each member of a recursive group, with its body, its
    type, and whether it is a constant.  A custom constant is not one. *)
val functions : Core.Program.t -> (Names.GlobRef.t * Core.Expr.t * Core.Type.t * bool) list
