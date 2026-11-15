(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The target-language descriptor the extraction driver renders a
    {!Core.Program.t} through. *)

open Names

(** Which "unsafe" backend features an extracted program requires, so the
    preamble can emit the corresponding helpers: [erased_values] for
    {!Core.Expr.Erased_value} values, [erased_types] for {!Core.Type.Erased}
    types, [unknown_types] for {!Core.Type.Unknown} types, and [magic] for
    {!Core.Expr.Coerce} coercions. *)
type unsafe_needs = {
  erased_values : bool;
  erased_types : bool;
  unknown_types : bool;
  magic : bool;
}

(** A backend descriptor: the set of hooks the generic extraction driver
    uses to render a {!Core.Program.t} for one concrete output language.  It
    bundles the reserved [keywords], source-file conventions
    ([file_suffix], [file_naming], [preamble]) and printers ([pp_struct],
    [pp_hstruct]), the optional interface-file conventions ([sig_suffix],
    [sig_preamble]), and [pp_decl] for printing one declaration in
    isolation. *)
type t = {
  keywords : Id.Set.t;
  global_scope_keywords : Id.Set.t;
      (** Names refused only to a declaration the backend emits at global
          scope, where the target's own libraries have already spent them. *)
  (* Concerning the source file *)
  file_suffix : string;
  file_naming : ModPath.t -> string;
  (* the second argument is a comment to add to the preamble *)
  preamble : Id.t -> string option -> ModPath.t list -> unsafe_needs -> Pp.t;
  pp_struct : Core.Program.t -> Pp.t;
  pp_hstruct : Core.Program.t -> Pp.t;
  (* Concerning a possible interface file *)
  sig_suffix : string option;
  (* the second argument is a comment to add to the preamble *)
  sig_preamble : Id.t -> string option -> ModPath.t list -> unsafe_needs -> Pp.t;
  (* for an isolated declaration print, an element of the module given *)
  pp_decl : module_:ModPath.t -> Core.Decl.t -> Pp.t;
}
