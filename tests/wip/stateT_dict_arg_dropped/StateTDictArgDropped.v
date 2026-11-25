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
   vellvm_bench.h:2395.  Two more of the same shape for [definition].

   Diagnosis (2026-11-24): the dictionary is no longer dropped; the use
   sites now read [Monad_stateT<Monad_itree<crane::obj>, env>].  What fails
   is how [stateT]'s higher-kinded parameter [m] is spelled.  The record is
   [template <typename S, typename m, typename t> struct stateT] and its
   field [S -> m (t * S)] is printed [crane::fn<m(S)>]: [Records.gen_record]
   ([field_cpp_ty]) reads an applied record parameter as the parameter
   itself, "the carrier already applied at the erased element".  Two things
   disagree with that reading:

   - [step] builds [stateT<Nat, std::shared_ptr<ITree<crane::obj>>, Nat>]
     from a lambda returning [itree_ret(std::make_pair(n, s))], an
     [ITree<std::pair<Nat, Nat>>], which does not convert to the
     [ITree<crane::obj>] the field holds: no erasing coercion is emitted
     at the record's construction.
   - [Monad_stateT]'s carrier alias writes [stateT<T1, typename
     _tcI0::template m<CraneA0>, CraneA0>], the dictionary's carrier at
     [A] rather than at the erased element, and its [ret]/[bind] build the
     field from [_tcI0::ret<std::pair<A, T1>>], an [m<std::pair<A, T1>>].

   An inductive's constructor field applying a family parameter is spelled
   [crane::rebind_t<E, X>] instead (Sum1's [crane::rebind_t<E1, X>]), which
   with the carrier passed at [crane::obj] would type both [step] and
   [Monad_stateT] as written.  Whether records follow inductives there
   (field [crane::fn<crane::rebind_t<m, std::pair<t, S>>(S)>], and the
   instance's carrier written at [crane::obj]), or keep the erased reading
   and coerce at construction, is a decision for the plain-carrier design
   (crane::rebind_t), not a local fix; left in wip. *)
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
