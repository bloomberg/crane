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

Crane Extract Inductive itree => "%t1" [ "%a0" ].
Crane Extract Inductive itreeF => "" [ "%a0" "%a0" "" ].
Crane Extract Inlined Constant observe => "".

(** An event is performed where it is written, so the trigger around it has
    nothing left to say.  Reified mode keeps the [Vis] node and so gives
    [trigger] a spelling of its own; that is why this lives here rather than
    in [ITreeBase.v]. *)
Crane Extract Skip ITree.trigger.
(** An erased tree is its result, its events already performed where they
    were written, so relabelling them is the identity. *)
Crane Extract Inlined Constant translate => "%a1".

(** The ITree library defines [Ret] as a [Notation]. We shadow it with
    a [Definition] so Crane's monad registration can reference it as a
    global. Users still write [Ret x] — the Definition has the same
    behavior as the Notation it shadows. *)
Definition Ret {E : Type -> Type} {R : Type} (x : R) : itree E R := Ret x.

Crane Extract Monad itree [ bind := ITree.bind , ret := Ret ] => "%t1".

(** ITree's general recursion, [rec body a]: each [call x] of the body is a
    recursive call, answered by running the body on [x].  An erased tree
    performs its events where it is written, so the body is run with its
    handler on a stack ([crane_rec.h]) and a call invokes the innermost
    handler of its types.  The recursion is C++ recursion: as deep as the
    nesting of calls. *)
Crane Extract Inlined Constant ITree.Interp.Recursion.rec =>
  "crane::rec<%t1, %t2>(%a0, %a1)" From "crane_rec.h".
Crane Extract Inlined Constant ITree.Interp.Recursion.call =>
  "crane::rec_call<%t1, %t2>(%a0)" From "crane_rec.h".
Crane Extract Skip ITree.Interp.Recursion.callE.
