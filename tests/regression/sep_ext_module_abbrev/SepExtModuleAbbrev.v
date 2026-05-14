(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: separate extraction of module abbreviations and
   dependent type arguments (Bugs 2 and 3):
   - Bug 2: Module M (P : WS) := F P.E P  should extract to
       struct M : F<typename P::E, P> {};   (not a bare type expression in body)
   - Bug 3: M::E used as template argument must include typename keyword *)

Module Type OrderedType.
  Parameter t : Type.
End OrderedType.

Module Type WS.
  Declare Module E : OrderedType.
  Parameter key : Type.
End WS.

(** Base functor: takes two module args and does something *)
Module OrdFacts (X : OrderedType) (M : WS).
  Definition key_eq (a b : M.key) : bool := true.
  Definition ord_eq (a b : X.t) : bool := true.
End OrdFacts.

(** KeyFacts: takes a WS module, uses M.E as the OrderedType arg *)
(** Bug 3: inside the struct, using ME := M.E needs typename M::E *)
Module KeyFacts (M : WS).
  Module ME := M.E.
End KeyFacts.

(** Module abbreviation: M (P : WS) := OrdFacts P.E P
    Bug 2: should extract to struct WFacts : OrdFacts<typename P::E, P> {}
    Bug 3: the P.E arg needs typename *)
Module WFacts (P : WS) := OrdFacts P.E P.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Separate Extraction OrdFacts WFacts KeyFacts.
