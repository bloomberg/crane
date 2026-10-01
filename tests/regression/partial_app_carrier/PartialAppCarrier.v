(** Crane bug: a monad transformer applied to a partially-applied
    two-parameter type ([stateT nat (box E)], Vellvm's [stateT S (itree E)])
    does not compile.

    Observed:
      template <typename _CraneTcArg>
      using _crane_carrier_tc_35ed2f4e6492a577 = box<_CraneTcArg, std::any>;
      struct PartialAppCarrier {
        template <typename s, template <typename> class m, typename a>
        using stateT = std::function<m<std::pair<s, a>>(s)>;
        template <typename E, typename A> struct box { ... };
        ...
        static inline const stateT<Nat, _crane_carrier_tc_35ed2f4e6492a577, Nat>
            get_st = [](Nat s) {
              return box<std::any<std::pair<Nat, Nat>>, std::any>::box0(...); };
    - the carrier alias is emitted before, and outside, the struct that
      declares [box]:  error: no template named 'box'
    - it fills the wrong slot: [box E] partially applied should be
      [box<E, _CraneTcArg>], not [box<_CraneTcArg, std::any>];
    - [get_st] (polymorphic in [E]) becomes a non-template constant, and its
      body writes [box<std::any<std::pair<Nat, Nat>>, std::any>]:
        error: expected '>' / expected expression

    Reduced from Vellvm's vanilla-ITree extraction: [Semantics/] handlers
    over [stateT global_env (itree E)] come out as
      Monads::template stateT<global_env<...>, Itree, T2>
    and fail with [too few template arguments for class template 'Itree']
    (66x). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module PartialAppCarrier.
  (* ExtLib's stateT, as Vellvm uses it over [itree E]. *)
  Definition stateT (S : Type) (M : Type -> Type) (A : Type) : Type := S -> M (prod S A).

  Inductive box (E : Type -> Type) (A : Type) : Type := Box (a : A).
  Arguments Box {E A}.

  Variant noE : Type -> Type := .

  (* the carrier [box E] is a partial application of a two-parameter type *)
  Definition get_st {E : Type -> Type} : stateT nat (box E) nat := fun s => Box (s, s).

  Definition r : box noE (nat * nat) := get_st 3.
  Definition is_three : bool := match r with Box (a, _) => Nat.eqb a 3 end.
End PartialAppCarrier.

Crane Extraction "partial_app_carrier" PartialAppCarrier.
