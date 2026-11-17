(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

From Crane Require Import Mapping.Std.

(** Declared in a file other than [AstLike], so that [AstLike]'s child
    module [Ident] collides with it and [AstLike] is written as a struct. *)
Inductive ident : Set := Global (n : nat) | Local (n : nat).
