(* A definition whose event family is only ever *applied*, never passed bare,
   used to get that family declared as a plain `typename` while the signature
   kept writing it applied -- `T1<std::any>` against `template <typename> T1`,
   which does not parse.  That is fixed: the kind is now read off the ML type,
   and where nothing demands a higher kind the application is taken back off.
   The handler method's undeducible return parameter is fixed too.

   What is left is the last line of the .cpp:

     return h<AE, AE>(sum1_inl(AE::a0(std::move(n))));

     error: no viable conversion from returned value of type
            'shared_ptr<ITree<std::any>>' to function return type
            'shared_ptr<ITree<Nat>>'

   `h`'s result index is undeducible, so its declaration erases it and `h`
   returns `shared_ptr<ITree<std::any>>`; `use` promises the tree at a real
   index.  `crane_cast_to` in crane_itree.h is exactly that conversion and
   nothing emits it, because the call site cannot tell that the callee erased
   the index: the decision is made by the signature relaxations in gen_decls,
   from the converted C++ type, and is not reconstructible from the ML type
   the call site has.  Reading it back out of a table is the dead end recorded
   in `decl-tparam-table-unsound` -- declaration emission interleaves with body
   generation.  `result_is_index_only_tvar` is the nearest existing predicate
   and does not cover this: in `sum1 E F X` the index `X` is a *parameter* of
   `sum1`, not an index, so the "carried only as an index" test says no.

   Reduced from Vellvm's Semantics/Handlers/Intrinsics.v:94
   (interp_intrinsics_h); ITree's own Recursion.interp_mrec has the same shape. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
Import ITreeNotations.
Open Scope itree_scope.

Variant AE : Type -> Type := | A0 : nat -> AE nat.

Definition handle {E} : AE ~> itree E :=
  fun _ e => match e with A0 n => Ret n end.

Section P.
  Variable E F : Type -> Type.
  Notation Eff := (E +' AE +' F).

  (* annotated: E and F are rendered, and come out template-template *)
  Definition E_trigger : Handler E Eff := fun _ e => trigger e.
  Definition F_trigger : Handler F Eff := fun _ e => trigger e.

  (* unannotated: type comes from case_, E and F only ever applied *)
  Definition h := case_ E_trigger (case_ (@handle Eff) F_trigger).
End P.

Module AppliedTypenameNotHk.
  Definition use (n : nat) : itree (AE +' AE +' AE) nat :=
    h AE AE nat (inl1 (A0 n)).
End AppliedTypenameNotHk.

Crane Extraction "applied_typename_not_hk" AppliedTypenameNotHk.
