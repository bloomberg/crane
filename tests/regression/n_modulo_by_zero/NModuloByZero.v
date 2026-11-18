From Crane Require Import Mapping.NatIntStd Mapping.NInt.
From Crane Require Extraction.
From Stdlib Require Import List NArith.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Wrong value, no diagnostic.  Rocq defines [N.modulo x 0 = x], but
    Mapping.NInt prints [N.modulo] as [(%a1 == 0u ? 0u : %a0 % %a1)], so
    [N.modulo 4 0] is [0] in C++.  NIntBDE and NGMP have the same zero branch;
    [N.div x 0 = 0] is right.  Not a fixed-width effect. *)
Module NModuloByZero.

Definition a (x y : N) : N := N.modulo x y.
Definition t : N := N.modulo 4 0.

End NModuloByZero.

Crane Extraction "n_modulo_by_zero" NModuloByZero.
