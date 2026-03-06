(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: update_region patching ROM segment. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module RegionPatchWrite.

Fixpoint update_region (rom : list nat) (base : nat) (bytes : list nat) {struct rom}
  : list nat :=
  match rom with
  | [] => []
  | r :: rom' =>
      match base with
      | 0 =>
          match bytes with
          | [] => r :: rom'
          | b :: bytes' => b :: update_region rom' 0 bytes'
          end
      | S n => r :: update_region rom' n bytes
      end
  end.

Definition t : nat := nth 2 (update_region [0; 0; 0; 0] 1 [7; 8]) 0.

End RegionPatchWrite.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "region_patch_write" RegionPatchWrite.
