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
    two parts are independent.  A let-bound lambda or local fixpoint may
    read what it closes over wherever it is used, so nothing it closes over
    is read last in the let's scope.  An argument an inline custom's template
    splices twice is read twice, and one it never splices is not read.

    This is not yet the plan's OwnershipIR: it decides no use's mode, only
    which reads a move may be made at. *)

type t

(** Nothing planned: no read is a last use. *)
val empty : t

(** Whether a body owning a value of ML type [ty] moves it at its last use:
    one a copy of which costs more than a move.  This is the C++ reading
    {!Loopify_analysis.worthwhile_move_type} makes, read off the ML type: an
    inductive that is not an enum or coinductive, a closure, a type
    variable, and a mapped type unless it is a scalar or declared trivially
    copyable with arguments that are too. *)
val worth_moving : Miniml.ml_type -> bool

(** [region ~owned t] is the plan of [t]'s reads, [t] standing under binders
    it reads but does not bind, of which it owns those at the de Bruijn
    indices [owned]. *)
val region : ?owned:int list -> Miniml.ml_ast -> t

(** [reuse_arm p ~scrutinee ~branch] is [p] for the branch numbered [branch]
    of the match on the variable [scrutinee], generated to rebuild
    in the scrutinee's storage: the fields it binds are moved out into locals
    of its own, and the scrutinee, which keeps the storage, is not read by
    value. *)
val reuse_arm : t -> scrutinee:Miniml.ml_ast -> branch:int -> t


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

(** Whether a read takes its variable's value: the variable is owned where
    it is read, and the read is its last use where it may be taken. *)
val moves : t -> Miniml.Occurrence.t -> bool

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

(** The de Bruijn indices, at [closure], of the variables the lambda
    [closure] takes by move when it is made: each is owned there, and the
    capture is its last use -- nothing after the lambda, beside it, or
    captured with it reads it. *)
val moved_captures : t -> Miniml.ml_ast -> int list

(** A term copied to two places -- an eta argument pushed into both branches
    of a conditional -- holds one read twice; it is a last use where every
    copy is one. *)
val fate : t -> Miniml.Occurrence.t -> fate
