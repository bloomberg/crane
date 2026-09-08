(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.

(** An expression nested past the depth limit is rewritten into a sequence of
    bindings inside an immediately-invoked lambda.  The lambda is given the
    expression's own type as its trailing return type, and for a [const]-
    qualified scalar that is [-> const uint64_t], which [-Wignored-qualifiers]
    rejects under [-Werror]. *)

Module DeepExprConstReturn.

  Definition f (n : nat) : nat := n + 1.

  Definition test : nat := f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

End DeepExprConstReturn.

Crane Extraction "deep_expr_const_return" DeepExprConstReturn.
