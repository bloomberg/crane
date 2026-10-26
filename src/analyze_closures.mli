(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How a local fixpoint group is generated, decided over Core
    (docs/Pipeline-Disentangling-Plan.md, section 3.8 and Milestone 7):
    whether it may outlive the scope it is bound in, and so must be closures
    holding copies rather than lambdas referring into that scope. *)

type group =
  | Lifted
      (** lifted to a function template, being polymorphic in a type variable
          of its own past the head's ({!Ml_type_util.own_type_variables}): it
          is passed what it closes over, so a call of it names each such
          variable as a value *)
  | In_place
      (** by reference: no member escapes, so it runs where it is called *)
  | Closures
      (** holding copies: a member may outlive the scope -- named other than
          as the function an application applies, or named at all inside a
          closure, a lambda or a local fixpoint not generated in place --
          in the scope the group is let-bound in, or in a member's own body,
          where a self-call in a closure a member returns runs after the
          scope has gone.  A cofixpoint's body is suspended, so any mention
          of a member there escapes.  A let, a match, a bind generated as
          sequencing and a group generated in place, applied or let-bound,
          run where they stand. *)

(** [group ~n_outer ?continuation ~cofix ids bodies], of the group of
    binders [ids] and bodies [bodies], a cofixpoint where [cofix] says so,
    generated under a head of [n_outer] type variables: let-bound in
    [continuation], where it is given, or else applied in place. *)
val group :
  n_outer:int ->
  ?continuation:Miniml.ml_ast ->
  cofix:bool ->
  (Names.Id.t * Miniml.ml_type) array ->
  Miniml.ml_ast array ->
  group
