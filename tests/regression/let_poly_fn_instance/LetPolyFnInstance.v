(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.

(** A let-bound polymorphic function is lifted to a template, and the lifted
    template's arity is taken from the lambda.  Instantiating it at a function
    type and applying the result absorbs the extra argument into the same call,
    so [g 4] is emitted as a second argument to the one-parameter [_anon_f]. *)

Module LetPolyFnInstance.

  Definition test : nat :=
    let f := fun (A : Type) (x : A) => x in
    f nat 3 + (let g := f (nat -> nat) (fun y => y + 1) in g 4).

End LetPolyFnInstance.

Crane Extraction "let_poly_fn_instance" LetPolyFnInstance.
