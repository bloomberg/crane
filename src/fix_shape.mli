(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Every fixpoint takes the shape its type says, before anything counts its
    parameters: {!Normalize}, {!Ownership.settle}, and translation.

    - The [let]s between a fixpoint's binder and its first lambda go under
      the lambdas: [fix F (h := H F) (l : L) := b] as
      [fix F (l : L) := let h := H F in b].  A call unfolds the body, so the
      [let]s run at every call either way; floated, the fixpoint's
      parameters are its lambdas', and a reference to [F] in [H F] is a
      function, not a fixpoint of no parameters returning one.
    - A local cofixpoint whose functions take no parameter --
      [cofix o := Cons 1 o] -- is the call
      [(cofix o (_ : unit) := Cons 1 (o tt)) tt].  A value cannot name
      itself before it is built, a function can: each occurrence of [o]
      becomes a corecursive call, which the constructor guarding it
      suspends, as it does a top-level [CoFixpoint]'s.  A top-level
      parameterless [CoFixpoint] is already emitted as such a function. *)

(** [fix F (h := H F) (l : L) := b] as [fix F (l : L) := let h := H F in b]. *)
val float_lets_under_lams : Miniml.ml_ast -> Miniml.ml_ast

val structure : Miniml.ml_structure -> Miniml.ml_structure
