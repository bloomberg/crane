(** A holder whose body names another holder.

    [stateT nat (stateT bool (itree E))] with [E] a parameter is written
    through two holders, the carrier of [itree E] and the carrier of
    [stateT bool (itree E)], whose body names the first applied to [E].  The
    outer holder is declared over [E] under its own parameter's name, and
    its body applies the inner holder to that parameter:
      template <typename CraneP0> struct crane_carrier_tch1 {
        template <typename CraneTcArg>
        using c = stateT<bool, crane_carrier_tch<CraneP0>::template c, CraneTcArg>;
      };
    The renaming used to stop at the inner carrier, a type constructor, so
    the body still wrote the use site's [T1] and the holder was declared
    over no parameter at all ([template <> struct ...]). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module HolderInsideHolderBody.
  Definition stateT (S : Type) (M : Type -> Type) (A : Type) : Type := S -> M (prod S A).

  Variant noE : Type -> Type := .

  Definition stacked_id {E : Type -> Type} (m : stateT nat (stateT bool (itree E)) nat)
    : stateT nat (stateT bool (itree E)) nat := m.

  Definition five : nat := 5.
End HolderInsideHolderBody.

Crane Extraction "holder_inside_holder_body" HolderInsideHolderBody.
