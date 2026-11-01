From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

(** A constructor field whose type is a custom applied to a functor's
    parameter type: [lhs : option nt], [option] a custom, its inductive
    declared in the parameter's signature.  Extraction carried the type
    argument [nt] among the custom's term arguments too, and the field's
    conversion read it as a value -- a callee no callable plan exists for.
    From ParseALot's [SllOptimizationSound]. *)

Module FunctorParamCtorField.
  Module Type T.
    Parameter nt : Type.
    Inductive frame := Fr (lhs : option nt) (n : nat).
  End T.

  Module Impl (D : T).
    Definition mk (x : D.nt) : D.frame := D.Fr (Some x) 0.
    Definition depth (f : D.frame) : nat := match f with D.Fr _ n => n end.
  End Impl.

  Module Names <: T.
    Definition nt := bool.
    Inductive frame := Fr (lhs : option nt) (n : nat).
  End Names.

  Module NamesImpl := Impl Names.

  Definition made_depth (b : bool) : nat := NamesImpl.depth (NamesImpl.mk b).
End FunctorParamCtorField.

Crane Extraction "functor_param_ctor_field" FunctorParamCtorField.
