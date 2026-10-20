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

(** [region t] is the plan of [t]'s reads, [t] standing under binders it
    reads but does not bind. *)
val region : Miniml.ml_ast -> t

(** What [p] says of a read. *)
type fate =
  | Last_use
  | Read_again  (** a later or concurrent read, or a closure, may read it *)
  | Inspected
      (** a last use where translation reads the value in place: the
          scrutinee of a variant match, which binds its alternatives by
          reference, or of a custom match spelling it twice; a field of a
          record being constructed *)
  | Unplanned  (** not a read of the region [p] was made of *)

(** A term copied to two places -- an eta argument pushed into both branches
    of a conditional -- holds one read twice; it is a last use where every
    copy is one. *)
val fate : t -> Miniml.Occurrence.t -> fate
