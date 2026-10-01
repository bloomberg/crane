(* [Monad_stateT] is generated as [template <Monad _tcI0, typename T1>], with
   the monad dictionary first and the state type second.  Every use site passes
   only one argument -- the *state* type -- which lands in the dictionary slot,
   and the dictionary itself is dropped.

   Expected: [Monad_stateT<Monad_itree, env>::template bind<Nat, Nat>(...)]
   Actual:   [Monad_stateT<env>::template bind<Nat, Nat>(...)]
     error: too few template arguments for class template 'Monad_stateT'
     note: template is declared here:
           template <Monad _tcI0, typename T1> struct Monad_stateT {

   The underlying monad here is [itree E], which the reified backend erases --
   so this looks like the erased-event family again, but in a *class* template
   argument list rather than a function one.

   In Vellvm: 6 errors, vellvm_bench.h:14694 onwards, from the global-state
   handler -- [Monads::template Monad_stateT<global_env>::template bind<T2, T2>]
   against [template <Monad _tcI0, typename T1> struct Monad_stateT] at
   vellvm_bench.h:2395.  Two more of the same shape for [definition]. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ExtLib Require Import Structures.Monads Data.Monads.StateMonad.
From ITree Require Import ITree.
Import MonadNotation.
Open Scope monad_scope.

Variant FailE : Type -> Type := Throw : unit -> FailE void.

Definition env := nat.

Section S.
  Context {E} `{FailE -< E}.

  Definition step (n : nat) : stateT env (itree E) nat :=
    mkStateT (fun s => Ret (n, s)).

  Definition twice (n : nat) : stateT env (itree E) nat :=
    bind (Monad := Monad_stateT env _) (step n) (fun a =>
    bind (Monad := Monad_stateT env _) (step a) (fun b => ret (Monad := Monad_stateT env _) b)).
End S.

Module StateTDictArgDropped.
  Definition use (n : nat) : itree FailE (nat * env) := runStateT (twice n) 0.
End StateTDictArgDropped.
Crane Extraction "stateT_dict_arg_dropped" StateTDictArgDropped.
