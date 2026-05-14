(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: separate extraction must insert the 'template' keyword
   for dependent template member access in qualified names.
   E.g. typename Raw::Tree<t_elt> -> typename Raw::template Tree<t_elt> *)

Require Import List.
Import ListNotations.

Module Type RawSig.
  Parameter elt : Type.
  Parameter tree : Type.
  Parameter empty : tree.
  Parameter elements : tree -> list elt.
End RawSig.

Module MakeOps (Raw : RawSig).
  Definition to_list (t : Raw.tree) : list Raw.elt :=
    Raw.elements t.

  Definition is_empty (t : Raw.tree) : bool :=
    match Raw.elements t with
    | [] => true
    | _ => false
    end.
End MakeOps.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Separate Extraction MakeOps.
