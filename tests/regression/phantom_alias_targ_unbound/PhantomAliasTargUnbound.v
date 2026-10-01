(** An erased event family reached only through a *phantom alias template*
    is dropped from the enclosing definition's head while the signature still
    spells it, and the alias itself is emitted higher-kinded.

    Three distinct defects, all from the same definition:

    1. [defined_intrinsics] is emitted as

         template <Params _tcI0> intrinsic_definitions<T1> defined_intrinsics()

       -- the return type names [T1] but the head never declares it:

         error: use of undeclared identifier 'T1'

       The call site does pass it, [defined_intrinsics<_tcI0, FailE>()], so
       the head is one parameter short of the call.

    2. The alias [intrinsic_definitions] is declared higher-kinded,

         template <template <typename> class e>
         using intrinsic_definitions = List<std::pair<Nat, semantic_function<e>>>;

       yet every use passes a plain type ([intrinsic_definitions<FailE>]).
       [semantic_function] right above it gets the correct
       [template <typename e = void>], so the two aliases disagree about the
       kind of the same Rocq parameter.

    3. [one] declares [template <Params _tcI0, typename T1>] but is called as
       [one<_tcI0>()], dropping the event argument.

    Both aliases are phantom in [E]: it occurs only under [itree], which the
    reified backend erases, so neither expansion mentions it.

    Seen in Vellvm at [vellvm_bench.h:11452] (declaration) and [:15662]
    (definition), from [src/rocq/Semantics/IntrinsicsDefinitions.v:380]:

      Definition semantic_function :=
        list dvalue -> option ptr -> itree E (dvalue + dvalue).

    Related to [monad_itree_targ_unbound], which loses the event from the head
    the same way but reaches it through a higher-kinded monad slot rather than
    through an alias. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.

Variant FailE : Type -> Type := Throw : unit -> FailE void.

Class Params := { width : nat }.

Section S.
  Context {Pa : Params}.
  Context {E : Type -> Type}.

  (* [E] occurs only under [itree], so the alias is phantom in [E]. *)
  Definition semantic_function := list nat -> itree E nat.
  Definition intrinsic_definitions := list (nat * semantic_function).

  Definition one : semantic_function := fun _ => Ret width.

  Definition defined_intrinsics : intrinsic_definitions :=
    cons (0, one) nil.
End S.

Module Qs.
  Definition use `{Pa : Params} : @intrinsic_definitions FailE := defined_intrinsics.
End Qs.
Crane Extraction "phantom_alias_targ_unbound" Qs.
