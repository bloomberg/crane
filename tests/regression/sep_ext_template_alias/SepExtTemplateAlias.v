(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: separate extraction of an eta-reduced functor alias
   (Module WFacts := WFacts_fun.) must emit a template using alias
   (template <OT X> using WFacts = WFacts_fun<X>;) rather than a
   bare non-template alias (using WFacts = WFacts_fun;). *)

Module Type OT.
  Parameter t : Type.
End OT.

Module WFacts_fun (X : OT).
  Definition foo : Type := X.t.
End WFacts_fun.

(** Module abbreviation without explicit parameters — Rocq's extraction
    eta-reduces this to MEident(WFacts_fun).  The generated C++ alias
    must carry the template parameter from the module type. *)
Module WFacts := WFacts_fun.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Separate Extraction WFacts_fun WFacts.
