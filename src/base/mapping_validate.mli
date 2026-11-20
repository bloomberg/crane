(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The checks of design section 19 that need only a decoded descriptor and
    the Rocq environment.  Each failure is a user error naming the instance,
    the mapped type or operation, and the one rule broken.  [UnsafeVerbatim]
    and [ExactParameter] are accepted with the warning
    [crane-mapping-unsafe].

    Template holes are found outside C++ comments and string and character
    literals (raw string literals are not recognised); each template context
    admits the holes of design section 18.2. *)

open Mapping_descriptor

(** Check a type mapping of [source], resolved from [instance]: component
    names unique and every named component declared; canonical and view
    types not top-level references; [ReadWriteViews] only with a mutable
    access model; a raw-pointer canonical type not [NativeRAII]; constructor
    references constructors of the inductive [source] reduces to, each at
    most once, with field positions (from 0, after the parameters) in range;
    template holes available in their context. *)
val type_mapping :
  Environ.env ->
  Evd.evar_map ->
  instance:Names.GlobRef.t ->
  source:EConstr.types ->
  type_mapping ->
  unit

(** What is known about an operation's argument and result types: the type
    mapping of the type of the argument of that name, and of the result type,
    when the type is closed and mapped. *)
type operation_context = {
  argument_mapping : string -> type_mapping option;
  result_mapping : type_mapping option;
}

val no_context : operation_context

(** Check an operation mapping of [source], resolved from [instance]:
    argument names unique; [%arg(x)] names a declared argument that is not
    [Ignore]; holes available in an operation template; every argument a
    fact, result or initialiser names declared; a borrowed result has an
    owner; a [PureOperation] has no [Write], [WriteCanonical], [Replace],
    [ReturnFreshIdentity], [WritesComponent], [RetainsArgument],
    [ReleasesIdentity] or [ExternalEffect].  Where [context] knows a type
    mapping: path components declared by the argument's type; [Write] and
    [Replace] allowed by its access model; [ReadViewBorrow] and
    [WritableViewBorrow] backed by the result type's views; a fresh identity
    not [ExternallyOwned] and its initialised components declared. *)
val operation_mapping :
  Environ.env ->
  instance:Names.GlobRef.t ->
  source:declaration ->
  operation_context ->
  operation_mapping ->
  unit
