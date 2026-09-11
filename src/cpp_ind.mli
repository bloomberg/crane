(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Which C++ declarations a MiniML declaration becomes.

   This module turns MiniML inductives ([ml_ind]) and declarations
   ([ml_decl]/[ml_spec]) into {!Minicpp.cpp_decl} values.  It has two families
   of entry points:

   - the source-file family ([ind_cpp_decls], [impl_decls]) gives the full
     definitions that go into the generated [.cpp]; and
   - the header family ([ind_header_decls], [header_decls])
     gives the declarations that go into the generated [.h].

   Each answer pairs a declaration with the name environment its
   sub-expressions are printed in; {!pp_decls} prints them.

   Everything else in the implementation is an internal helper and is
   deliberately hidden by this interface. *)

(** A declaration together with the name environment it is printed in. *)
type rendered = (Common.env * Minicpp.cpp_decl) list

(** Print the declarations an entry point answered with. *)
val pp_decls : rendered -> Pp.t

(** The full C++ definition of a mutual inductive block. *)
val ind_cpp_decls : Names.MutInd.t -> Miniml.ml_ind -> rendered

(** Header counterpart of {!ind_cpp_decls}. *)
val ind_header_decls : Names.MutInd.t -> Miniml.ml_ind -> rendered

(** The implementation-file declarations for one MiniML declaration. *)
val impl_decls : Miniml.ml_decl -> rendered

(** The header declarations for one MiniML declaration. *)
val header_decls : Miniml.ml_decl -> rendered

