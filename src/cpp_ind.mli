(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Pretty-printing of inductive-type and top-level declarations to C++.

   This module renders MiniML inductives ([ml_ind]) and declarations
   ([ml_decl]/[ml_spec]) into their C++ surface syntax. It has two families of
   entry points:

   - the source-file family ([pp_cpp_ind], [pp_decl], [pp_tydef]) emits the full
     definitions that go into the generated [.cpp]; and
   - the header family ([pp_cpp_ind_header], [pp_hdecl], [pp_hdecl_spec_only],
     [pp_spec]) emits the declarations/specs that go into the generated [.h].

   Everything else in the implementation is an internal helper and is
   deliberately hidden by this interface. *)

(** Render a mutual inductive block to its full C++ definition. *)
val pp_cpp_ind : Names.MutInd.t -> Miniml.ml_ind -> Pp.t

(** [pp_tydef ids name def] renders a C++ type alias/definition [name = def]
    parameterised over the type variables [ids]. *)
val pp_tydef : Names.variable list -> Pp.t -> Pp.t -> Pp.t

(** Render a top-level declaration (function, type, term) to its C++ definition. *)
val pp_decl : Miniml.ml_decl -> Pp.t

(** Header counterpart of {!pp_cpp_ind}: render a mutual inductive block's
    declarations for the generated [.h]. *)
val pp_cpp_ind_header : Names.MutInd.t -> Miniml.ml_ind -> Pp.t

(** Header counterpart of {!pp_decl}: render a declaration for the generated
    [.h]. *)
val pp_hdecl : Miniml.ml_decl -> Pp.t

(** Like {!pp_hdecl} but emits only the specification (no inline definition). *)
val pp_hdecl_spec_only : Miniml.ml_decl -> Pp.t

(** Render an [ml_spec] (module-signature element) to its C++ header form. *)
val pp_spec : Miniml.ml_spec -> Pp.t
