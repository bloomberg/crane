(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Erased ITree extraction mode.

   In this mode (the default), [itree E R] extracts to just [R] — the
   monadic wrapper is completely erased. [bind] becomes sequential
   statements and [Ret] disappears. Effect events are dispatched via
   inline customs on the smart constructors.

   Re-exports [ITreeBase.v] (shared library erasure directives) and adds
   the erased-mode-specific directives.
*)
From Crane Require Extraction.
From Crane Require Export Monads.ITreeBase.

Crane Extract Skip itreeF.
Crane Extract Inlined Constant observe => "".

(** The ITree library defines [Ret] as a [Notation]. We shadow it with
    a [Definition] so Crane's monad registration can reference it as a
    global. Users still write [Ret x] — the Definition has the same
    behavior as the Notation it shadows. *)
Definition Ret {E : Type -> Type} {R : Type} (x : R) : itree E R := Ret x.

Crane Extract Monad itree [ bind := ITree.bind , ret := Ret ] => "%t1".
