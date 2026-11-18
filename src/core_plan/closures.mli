(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How a local fixpoint group is generated, decided over Core before
    translation lowers it: whether it may outlive the scope it is bound in,
    and so must be closures holding copies rather than lambdas referring
    into that scope.  Translation asks {!group} at each local fixpoint it
    generates. *)

(** The way a local fixpoint group is generated. *)
type group =
  | Lifted
      (** lifted to a function template, being polymorphic in a type variable
          of its own past the head's ({!Base.Type_util.own_type_variables}): it
          is passed what it closes over, so a call of it names each such
          variable as a value *)
  | In_place
      (** by reference: no member escapes, so it runs where it is called *)
  | Closures
      (** holding copies: a member may outlive the scope -- named other than
          as the function an application applies to every parameter it
          takes, or named at all inside a
          closure, a lambda or a local fixpoint not generated in place, or
          the thunk suspending a coinductive constructor's arguments -- in
          the scope the group is let-bound in, or in a member's own body,
          where a self-call in a closure a member returns runs after the
          scope has gone.  A cofixpoint's body is suspended, so any mention
          of a member there escapes; so does any in the value a body
          suspended whole returns, and a group applied there is one.  A
          let, a match, a bind generated as sequencing and a group
          generated in place, applied or let-bound, run where they stand. *)

(** Whether a coinductive constructor is suspended, given the type of each
    binder where it stands, by de Bruijn index: the inductive it heads and
    its arguments ({!Core_to_cpp.Suspension.suspends_constructor}). *)
type suspends_constructor =
  binder_type:(int -> Core.Type.t option) -> Names.GlobRef.t -> Core.Expr.t list -> bool

(** [suspended_tail ~effects body]: the occurrences of the local fixpoint
    groups standing in the tail of [body], let-bound or applied, where the
    value they hand on is the one a body suspended whole returns -- the body
    of a let, the branches of a match, the continuation of a bind generated
    as sequencing.  Their declarations run where the body does, and what
    the value names runs in the thunk. *)
val suspended_tail : effects:Effects.t -> Core.Expr.t -> Core.Occurrence.t list

(** [group ~effects ~n_outer ~suspends ~lex ~suspended ?continuation ~cofix
    ids bodies], of the group of binders [ids] and bodies [bodies], a
    cofixpoint where [cofix] says so, standing in [lex] under a head of
    [n_outer] type variables, in a unit whose effect operations are
    [effects] and whose coinductive constructors [suspends] says are
    suspended: let-bound in [continuation] -- the member the let binds, by
    its position in the group, the let's binder and its body -- where it is
    given, or else applied in place; [suspended] where it stands in
    the tail of a body suspended whole ({!suspended_tail}). *)
val group :
  effects:Effects.t ->
  n_outer:int ->
  suspends:suspends_constructor ->
  lex:Core.Lexenv.t ->
  suspended:bool ->
  ?continuation:int * (Core.Binder_name.t * Core.Type.t) * Core.Expr.t ->
  cofix:bool ->
  (Names.Id.t * Core.Type.t) array ->
  Core.Expr.t array ->
  group
