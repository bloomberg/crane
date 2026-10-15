(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** A module whose only inductive is its eponymous type is promoted: the
    module's struct is the type itself.  Its implementation file is then
    skipped, on the assumption that the header defined every member inline;
    but a definition that is not a method of the type ([sizes], whose first
    argument is a list) is only declared there, as a static member, so it is
    defined nowhere and [example], which calls it, does not link. *)

From Stdlib Require Import List.
Import ListNotations.

Module PromotedModuleStaticFnUndefined.
  Inductive promotedModuleStaticFnUndefined : Type :=
  | Leaf : promotedModuleStaticFnUndefined
  | Node : promotedModuleStaticFnUndefined -> nat ->
           promotedModuleStaticFnUndefined -> promotedModuleStaticFnUndefined.

  Fixpoint size (t : promotedModuleStaticFnUndefined) : nat :=
    match t with
    | Leaf => 0
    | Node l _ r => S (size l + size r)
    end.

  Definition sizes (ts : list promotedModuleStaticFnUndefined) : list nat :=
    map (fun t => S (size t)) ts.

  Definition total (ts : list promotedModuleStaticFnUndefined) : nat :=
    fold_left Nat.add (sizes ts) 0.

  Definition example (n : nat) : nat := total [Leaf; Node Leaf n Leaf].
End PromotedModuleStaticFnUndefined.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Extraction "promoted_module_static_fn_undefined" PromotedModuleStaticFnUndefined.
