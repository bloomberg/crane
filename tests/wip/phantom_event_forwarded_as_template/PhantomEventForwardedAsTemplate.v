(** Two aliases over one section variable disagree about its {e kind}.

    [semantic_function] applies [E] -- [itree E _] -- which the reified
    backend erases, so [E] is spelled nowhere in the rendered type and comes
    out phantom, [typename e = void].  [intrinsic_definitions] never applies
    [E]; it only forwards it into [semantic_function].  With no application of
    its own, its kind is read from [E]'s Rocq type [Type -> Type] and emitted
    faithfully as [template <typename> class e] -- which is then passed to the
    [typename] slot the first alias declared:

      error: use of template template parameter 'e' requires template
      arguments

    Erasure is what makes them disagree: it removes the evidence of arity from
    the applier and leaves it in the forwarder.  Neither alias is wrong read
    alone.

    [phantom_alias_targ_unbound] is the same pair of definitions and does
    {e not} reproduce this -- there both aliases come out phantom.  The
    difference is the promoted class field: with a [ptr] in the parameter list
    the forwarder's rendered type spells something, and the phantom judgement
    that covered the whole list no longer covers [e] with it.

    Seen in Vellvm at [vellvm_bench.h:15261], from
    [rocq/Semantics/IntrinsicsDefinitions.v:380], with four more locations
    downstream of it: [defined_intrinsics]'s declaration and definition
    ([:17285], [:55521]) and its one call site ([:63054], [:63055]). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.

Variant FailE : Type -> Type := Throw : unit -> FailE void.

Class Params := { ptr : Type; zero_ptr : ptr; width : nat }.

Section S.
  Context {Pa : Params}.
  Context {E : Type -> Type}.

  Definition semantic_function := list ptr -> option ptr -> itree E nat.
  Definition intrinsic_definitions := list (nat * semantic_function).

  Definition one : semantic_function := fun _ _ => Ret width.

  Definition defined_intrinsics : intrinsic_definitions :=
    cons (0, one) nil.
End S.

Module PhantomEventForwardedAsTemplate.
  Definition use `{Pa : Params} : @intrinsic_definitions Pa FailE :=
    defined_intrinsics.
End PhantomEventForwardedAsTemplate.
Crane Extraction "phantom_event_forwarded_as_template" PhantomEventForwardedAsTemplate.
