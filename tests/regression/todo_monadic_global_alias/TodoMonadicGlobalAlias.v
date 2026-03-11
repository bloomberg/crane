(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: bare references to global monadic values should call the thunk. *)

From Crane Require Import Mapping.Std Monads.ITree Monads.IO.

Import MonadNotations.

Module TodoMonadicGlobalAlias.

Definition base : IO nat :=
  Ret 7.

Definition alias : IO nat :=
  base.

Definition rebound : IO nat :=
  x <- base ;;
  Ret (S x).

End TodoMonadicGlobalAlias.

Require Crane.Extraction.

Crane Extraction "todo_monadic_global_alias" TodoMonadicGlobalAlias.
