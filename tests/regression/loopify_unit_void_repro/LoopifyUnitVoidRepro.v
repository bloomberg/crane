From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Stdlib Require Import Lists.List.
From Crane Require Import Mapping.Std Mapping.NatInt Monads.ITree.
From Crane Require Extraction.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.
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

#[global] Instance c_int_mapping : TypeMapping LoopifyUnitVoidRepro.c_int :=
  value_type [] (Int I32) BitCopy.
#[global] Instance c_zero_mapping : OperationMapping (Ref (@LoopifyUnitVoidRepro.c_zero)) :=
  pure_cpp [] []
    (Structured (Verbatim "0")).
#[global] Instance draw_hidden_tile_mapping : OperationMapping (Ref (@LoopifyUnitVoidRepro.draw_hidden_tile)) :=
  effect_cpp [] ["x0"; "x1"]
    (Expr "((void)%arg(x0), (void)%arg(x1))").
#[global] Instance draw_revealed_tile_mapping : OperationMapping (Ref (@LoopifyUnitVoidRepro.draw_revealed_tile)) :=
  effect_cpp [] ["x0"; "x1"]
    (Expr "((void)%arg(x0), (void)%arg(x1))").

Crane Extraction "loopify_unit_void_repro" LoopifyUnitVoidRepro.
