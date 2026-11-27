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
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[export] Instance itree_mapping (E : Type -> Type) (R : Type) : TypeMapping (itree E R) :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.SourceType R;
     type_components := [];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (itree E R);
     type_interface := AlgebraicInterface [event (Ref (@go E R)) "%a0"];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
#[export] Instance itreeF_mapping (E : Type -> Type) (R T : Type) : TypeMapping (itreeF E R T) :=
  event_family []
    [event (Ref (@RetF E R T)) "%a0"; event (Ref (@TauF E R T)) "%a0"; event (Ref (@VisF E R T)) ""].
Crane Extract Skip observe.

(** An event is performed where it is written, so the trigger around it has
    nothing left to say.  Reified mode keeps the [Vis] node and so gives
    [trigger] a spelling of its own; that is why this lives here rather than
    in [ITreeBase.v]. *)
Crane Extract Skip ITree.trigger.
(** An erased tree is its result, its events already performed where they
    were written, so relabelling them is the identity. *)
#[export] Instance translate_mapping : OperationMapping (Ref (@translate)) :=
  pass_through ["h"] "t" [].

(** The ITree library defines [Ret] as a [Notation]. We shadow it with
    a [Definition] so Crane's monad registration can reference it as a
    global. Users still write [Ret x] — the Definition has the same
    behavior as the Notation it shadows. *)
Definition Ret {E : Type -> Type} {R : Type} (x : R) : itree E R := Ret x.

Crane Extract Monad itree [ bind := ITree.bind , ret := Ret ] => "%t1".

(** ITree's general recursion, [rec body a]: each [call x] of the body is a
    recursive call, answered by running the body on [x].  An erased tree
    performs its events where it is written, so the body is run with its
    handler on a stack ([crane_fn.h]) and a call invokes the innermost
    handler of its types.  The recursion is C++ recursion: as deep as the
    nesting of calls. *)
#[export] Instance rec_mapping : OperationMapping (Ref (@ITree.Interp.Recursion.rec)) :=
  effect_cpp ["crane_fn.h"] ["body"; "a"]
    (Structured (Call "crane::rec" [TypeParameter "A"; TypeParameter "B"] [Arg "body"; Arg "a"])).
#[export] Instance call_mapping : OperationMapping (Ref (@ITree.Interp.Recursion.call)) :=
  effect_cpp ["crane_fn.h"] ["a"]
    (Structured (Call "crane::rec_call" [TypeParameter "A"; TypeParameter "B"] [Arg "a"])).
Crane Extract Skip ITree.Interp.Recursion.callE.
