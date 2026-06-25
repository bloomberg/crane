From Stdlib Require Import Lists.List.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree.
From Crane Require Extraction.
Import ListNotations.

Set Crane Loopify.
Local Open Scope itree_scope.

Module LoopifyUnitVoidRepro.

Axiom c_int : Type.
Axiom c_zero : c_int.

Axiom reproE : Type -> Type.
Crane Extract Skip reproE.

Definition cell_size : nat := 42.

Axiom draw_hidden_tile : nat -> nat -> itree reproE unit.
Axiom draw_revealed_tile : nat -> nat -> itree reproE unit.

Fixpoint loop (x y : nat) (cells : list bool) : itree reproE unit :=
  match cells with
  | [] => Ret tt
  | revealed :: rest =>
      (if revealed
        then draw_revealed_tile x y
        else draw_hidden_tile x y) ;;
      loop (x + cell_size) y rest
  end.

Definition run : itree reproE c_int :=
  loop 0 0 [true; false] ;;
  Ret c_zero.

End LoopifyUnitVoidRepro.

Crane Extract Inlined Constant LoopifyUnitVoidRepro.c_int => "int".
Crane Extract Inlined Constant LoopifyUnitVoidRepro.c_zero => "0".
Crane Extract Inlined Constant LoopifyUnitVoidRepro.draw_hidden_tile =>
  "((void)%a0, (void)%a1)".
Crane Extract Inlined Constant LoopifyUnitVoidRepro.draw_revealed_tile =>
  "((void)%a0, (void)%a1)".

Crane Extraction "loopify_unit_void_repro" LoopifyUnitVoidRepro.
