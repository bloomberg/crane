(** Crane bug: a dependent member alias used as a template template argument
    is emitted without the [template] keyword, so it is parsed as a type.

    [stateT S M A] is [S -> M (A * S)], i.e. a type constructor built out of
    another one, and Crane correctly spells it as an alias template taking a
    template template parameter:

      template <typename S, template <typename> class M, typename A>
      using stateT = std::function<M<std::pair<A, S>>(S)>;

    [run] takes a [Monad M] instance, whose carrier reaches the body as the
    member alias [_tcI0::m].  Passing that member into [stateT] needs the
    [template] disambiguator, and Crane omits it:

      run(stateT<T2, _tcI0::m, Nat> step, const T2 &s)
                     ^^ needs [_tcI0::template m]

    Expected: [stateT<T2, typename _tcI0::template m, Nat>].
    Actual:   error: template argument for template template parameter must be
                     a class template or type alias template
              error: no matching function for call to 'run'

    Seen in Vellvm five times, all on [Monads::template stateT<T2, _tcI0::m,
    std::any, Sum<std::any, std::any>>] in the state-monad interpretation
    layer. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monads Data.Monads.OptionMonad.

(* A type constructor built out of another one -- Crane spells it as a
   template template argument. *)
Definition stateT (S : Type) (M : Type -> Type) (A : Type) : Type :=
  S -> M (A * S)%type.

Class Iter (M : Type -> Type) : Type :=
  { iter : forall {A}, (A -> M A) -> A -> M A ; label : nat }.

(* [run]'s argument type mentions [M] -- the carrier of the [Monad] instance --
   in template-template position. *)
Definition run {M : Type -> Type} `{Monad M} (S : Type)
               (step : stateT S M nat) (s : S) : M (nat * S)%type :=
  step s.

Module MemberAliasAsTtArg.
  Definition use (o : nat) : option (nat * nat)%type :=
    @run option Monad_option nat (fun s => Some (S s, s)) o.
End MemberAliasAsTtArg.

Crane Extraction "member_alias_as_tt_arg" MemberAliasAsTtArg.
