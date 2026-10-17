(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The headers what a unit writes needs (docs/Pipeline-Disentangling-Plan.md,
    Milestone 9): read off what is generated ahead of its files -- its
    finished declarations, the concepts of its module types, the types of
    its eponymous records' fields -- where the printer writes it, rather
    than raised by the pass that built each construct or by the printer as
    it spells it.  The driver demands them all before either file is
    rendered ({!Cpp.finish_ahead}); the printer demands nothing, and under
    [CRANE_CHECK_IR] what it writes is checked against them
    ({!Table.written_needs_header}).

    Only what is written counts.  The annotations a node carries for later
    passes -- a call's signature, a projection's field type, a structured
    binding's field types -- are not written; a custom mapping writes only
    what its placeholders name; and a printing rule may drop a node's part,
    as a returned abort is written as a [throw] without its type. *)

(** The text of the acquire fence a destructor's drain issues before it
    takes a node it owns alone, which needs [<atomic>]. *)
val acquire_fence : string

(** The headers the finished declaration [d] needs for what it writes. *)
val of_decl : Minicpp.cpp_decl -> Table.header list

(** The headers the type [t] needs where it is written. *)
val of_type : Minicpp.cpp_type -> Table.header list

(** The headers the concept of a module type needs for what it writes. *)
val of_modtype_concept : Modtype_concept.t -> Table.header list

(** The globals the finished declaration [d] writes the names of, where the
    printer resolves them: a type's, a constant's or a constructor's, an
    enum's, the concept constraining a template parameter. *)
val globals_of_decl : Minicpp.cpp_decl -> Names.GlobRef.t list

(** The globals the type [t] writes the names of where it is written. *)
val globals_of_type : Minicpp.cpp_type -> Names.GlobRef.t list

(** [tyctors_of_decl f d] calls [f ~vl ~owner t] at each type constructor
    [Ttyctor t] the finished declaration [d] writes, in the order written,
    with the names of the template parameters its type variables are read
    as there ([vl]), and the struct whose members are written around it, if
    any ([owner]). *)
val tyctors_of_decl :
  (vl:Names.Id.t list -> owner:Names.GlobRef.t option -> Minicpp.cpp_type -> unit) ->
  Minicpp.cpp_decl ->
  unit

(** [tyctors_of_type f ~vl t] is {!tyctors_of_decl} of the type [t], written
    where its type variables are read as [vl]. *)
val tyctors_of_type :
  (vl:Names.Id.t list -> owner:Names.GlobRef.t option -> Minicpp.cpp_type -> unit) ->
  vl:Names.Id.t list ->
  Minicpp.cpp_type ->
  unit

(** The promoted type variables -- a class's [Type]-valued fields -- the
    finished declaration [d] writes, in the order it writes them. *)
val promoted_of_decl : Minicpp.cpp_decl -> Names.Id.t list

(** The promoted type variables the type [t] writes, in order. *)
val promoted_of_type : Minicpp.cpp_type -> Names.Id.t list
