(** Crane bug: ExtLib's [ret] at the itree monad, inside the step lambda
    given to [ITree.iter], names the family-parametric instance bare.

    Observed (edb2edd97):
      template <typename T1> static top<T1, Nat> count(const Nat &n) {
        return ITree::template iter<AllE<T1, std::any>, Nat, Nat>(
            [=](Nat k) mutable { ...
                return Monad0::template ret<Monad_itree, Sum<Nat, Nat>>(Sum<Nat, Nat>::inr(k)); ...
    It should be [Monad_itree<AllE<T1, std::any>>].  Diagnostic:
      error: no matching function for call to 'ret'
      note: candidate template ignored: invalid explicitly-specified
            argument for template parameter '_tcI0'
    edb2edd97 fixed this when the call's expected result is the enclosing
    definition's type (instance_use_drops_family_arg); here the expected
    type comes from [ITree.iter]'s argument, [I -> itree E (I + R)], inside
    a lambda.  Compile-only (the runtime check would also hit
    match_observe_alias_family).

    Reduced from Vellvm, [Semantics/Libraries.v] [puts_denotation] /
    [i8_str_index]'s [ITree.iter] body: [Monad0::template ret<Monad_itree,
    ...>] (35 errors in Vellvm on edb2edd97). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.
From ExtLib Require Import Structures.Monad.
Import ITreeNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Module RetInIterLambda.
  Section WithParam.
    Context {P : Type}.
    Variant aE : Type -> Type := A : P -> aE nat.
    Variant bE : Type -> Type := B : bE nat.
    Definition AllE := aE +' bE.
    Definition top := itree AllE.

    (* Vellvm's Libraries.puts_denotation: [ret] (ExtLib, at the itree
       monad) inside the step lambda given to [ITree.iter]. *)
    Definition count (n : nat) : top nat :=
      ITree.iter (fun k => if Nat.eqb k n then ret (inr k) else ret (inl (S k))) 0.
  End WithParam.

  Definition c : itree (@AllE nat) nat := @count nat 3.
End RetInIterLambda.

Crane Extraction "ret_in_iter_lambda" RetInIterLambda.
