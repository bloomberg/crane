(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Minimal reproduction of a codegen bug in the default [list] representation.

   A record with a [Type]-valued field ([carrier]) and a field whose type
   depends on it ([contents : list carrier]) erases [carrier] to a promoted
   type parameter.  When such a value is built at a concrete instance in a
   MONOMORPHIC (non-template) context (the global [d] below), the [list carrier]
   field is emitted with the promoted type variable left unsubstituted, e.g.

     static inline const dyn d = dyn{List<T1>::cons(1, ...)};
                                           ^^ 'T1' is not declared here

   which fails to compile with "use of undeclared identifier 'T1'".  The
   element type should either be substituted with the concrete instance
   ([uint64_t]) or erased to [std::any], matching how the surrounding record
   field is erased.

   This is the same defect that blocks extracting a list-heavy program (e.g. a
   parser whose grammar entries are dependent pairs carrying list-typed semantic
   values) to the default [Datatypes::List<T>] representation. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

Module ListDepTypeErasure.

  Record dyn := { carrier : Type ; contents : list carrier }.

  (* Built at a concrete carrier ([nat]) in a global (monomorphic) context. *)
  Definition d : dyn := {| carrier := nat ; contents := [1; 2; 3]%nat |}.

  (* An accessor over the (erased) list field, so the test can observe a value. *)
  Definition dlen (x : dyn) : nat := List.length (contents x).

End ListDepTypeErasure.

Crane Extraction "list_dep_type_erasure" ListDepTypeErasure.
