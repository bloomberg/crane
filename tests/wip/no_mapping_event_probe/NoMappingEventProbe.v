From Stdlib Require Import Lists.List.
From Crane Require Import Mapping.NatIntStd Monads.ITree.
From Crane Require Extraction.
Import ListNotations.

Local Open Scope itree_scope.

Module NoMappingEventProbe.

Inductive reproE : Type -> Type :=
| Hidden : nat -> nat -> reproE unit
| Revealed : nat -> nat -> reproE unit.

Definition cell_size : nat := 42.

Definition draw_hidden_tile (x y : nat) : itree reproE unit :=
  embed (Hidden x y).

Definition draw_revealed_tile (x y : nat) : itree reproE unit :=
  embed (Revealed x y).

Fixpoint loop (x y : nat) (cells : list bool) : itree reproE unit :=
  match cells with
  | [] => Ret tt
  | revealed :: rest =>
      (if revealed
       then draw_revealed_tile x y
       else draw_hidden_tile x y) ;;
      loop (x + cell_size) y rest
  end.

End NoMappingEventProbe.

Crane Extraction "no_mapping_event_probe" NoMappingEventProbe.
