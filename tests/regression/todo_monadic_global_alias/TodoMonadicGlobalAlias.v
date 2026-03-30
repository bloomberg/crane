(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: bare references to global monadic values should call the thunk. *)

From Crane Require Import Mapping.Std Monads.ITree Monads.IO.

Module TodoMonadicGlobalAlias.

Definition base : itree iIO nat :=
  Ret 7.

Definition alias : itree iIO nat :=
  base.

Definition rebound : itree iIO nat :=
  x <- base ;;
  Ret (S x).

End TodoMonadicGlobalAlias.

Require Crane.Extraction.

Crane Extraction "todo_monadic_global_alias" TodoMonadicGlobalAlias.
