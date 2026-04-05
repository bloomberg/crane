(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Regression test: embed-based custom itree smart constructors must
   extract to valid C++ when the effect inductive has a custom extraction
   mapping, without needing separate Crane Extract Inlined Constant
   directives for each smart constructor.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree.

Local Open Scope pstring_scope.
Local Open Scope itree_scope.
Import ITreeNotations.

Inductive bugE : Type -> Type :=
| BugCreate : PrimString.string -> bugE unit
| BugRead : bugE int.

Crane Extract Skip bugE.

Definition bug_create {E} `{bugE -< E} (title : PrimString.string) : itree E unit :=
  embed (BugCreate title).

Definition bug_read {E} `{bugE -< E} : itree E int :=
  embed BugRead.

Definition bug_main : itree bugE int :=
  bug_create "hello" ;;
  bug_read.

Crane Extract Inductive bugE => ""
  [ "bug_create_impl(%a0)"
    "bug_read_impl()" ]
  From "embed_effect_helper.h".

Crane Extraction "embed_effect" bug_main.
