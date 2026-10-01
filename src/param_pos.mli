(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Positions in a callee's value-parameter list, one type per numbering.

    A call site reaches the callee's parameters through three numberings, and
    an index of one used as an index of another reads a neighbouring
    parameter's type without any error:

    - an argument's place among the call's regular arguments, the class
      dictionaries partitioned out of it ([int]);
    - a position of the {e declared} parameter list ({!orig}): the callee's ML
      domains with the [Tdummy] ones dropped, dictionary parameters included,
      erased ones too;
    - a position of the {e instantiated} list ({!subst}): the same after the
      call's type arguments are substituted, which can turn a parameter into
      [Tdummy] and so drop it -- the [m A] of a [bind] whose instance erases
      [m].

    The two lists are kept as distinct types, and so are their positions, so
    reading one list at the other's position does not compile. *)

type orig
type subst

(** A position in a parameter list of kind ['k]. *)
type 'k pos

(** A parameter list of kind ['k]. *)
type 'k params

(** The value parameters of an ML function type: its domains up the arrow
    spine, definitional-class aliases expanded, the [Tdummy] ones dropped.
    [~expand] expands an alias that stands for a function type. *)
val orig_params :
  expand:(Miniml.ml_type -> Miniml.ml_type) -> Miniml.ml_type -> orig params

val subst_params :
  expand:(Miniml.ml_type -> Miniml.ml_type) -> Miniml.ml_type -> subst params

val to_list : 'k params -> Miniml.ml_type list
val length : 'k params -> int
val nth : 'k params -> 'k pos -> Miniml.ml_type option

(** Every parameter with its position. *)
val positioned : 'k params -> ('k pos * Miniml.ml_type) list

(** The declared position of the call's [i]th regular argument, the
    [leading] parameters the dictionaries occupy -- erased instances among
    them -- coming first. *)
val of_regular : leading:int -> int -> orig pos

(** [regular_of pos ~leading] inverts {!of_regular}; [None] for a position
    a dictionary occupies. *)
val regular_of : leading:int -> orig pos -> int option

(** The instantiated position of a declared one, [None] where the
    instantiation erased the parameter outright -- so that no neighbour is
    returned in its place.  [~erased] says whether a declared parameter type
    is [Tdummy] once instantiated.

    The count is taken over the declared list's own elements rather than by
    walking the two arrow spines side by side: substitution can uncover an
    alias whose expansion has a different arity, and paired spines then drift
    against each other. *)
val subst_of_orig :
  erased:(Miniml.ml_type -> bool) -> orig params -> orig pos -> subst pos option

(** Positions at which a custom mapping's parameters are read: its text
    takes the arguments in declared order, so its instantiated list is read
    at the declared positions.  The one sanctioned crossing. *)
val subst_at_declared : orig pos -> subst pos

(** The declared position of a methodified callee's receiver, as the method
    registry records it. *)
val of_receiver : int -> orig pos

val equal : 'k pos -> 'k pos -> bool
