(** Crane bug: a holder whose body names another holder is declared over
    none of the parameters its body names.

    [stateT nat (stateT bool (itree E))] with [E] a parameter is written
    through two holders, the carrier of [itree E] and the carrier of
    [stateT bool (itree E)], whose body names the first applied to [E].
    Observed (e3703bf80, and after the synthesised templates are planned):
      template <typename CraneP0> struct crane_carrier_tch {
        template <typename CraneTcArg> using c = Itree<CraneP0, CraneTcArg>;
      };
      ...
      template <> struct crane_carrier_tch1 {
        template <typename CraneTcArg>
        using c = stateT<bool, crane_carrier_tch<T1>::template c, CraneTcArg>;
      };
      template <typename T1>
      static stateT<Nat, crane_carrier_tch1<T1>::template c, Nat> stacked_id(...)
    Diagnostics:
      error: extraneous 'template<>' in declaration of struct 'crane_carrier_tch1'
      error: use of undeclared identifier 'T1'
    The use captures [T1], read off the outer body's rendering, which writes
    it inside the inner holder's arguments.  But the outer body is renamed
    over the captured parameters structurally, and the inner carrier is a
    type constructor the renaming does not enter, so the renamed body still
    writes [T1], and the declaration, which takes its parameters from the
    holder names the body writes, finds none.  Expected: [template
    <typename CraneP0> struct crane_carrier_tch1] with
    [crane_carrier_tch<CraneP0>] in its body. *)

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
