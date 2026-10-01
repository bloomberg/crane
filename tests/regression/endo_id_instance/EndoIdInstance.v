(** Crane bug (runtime): a definitional-class instance defined as a
    polymorphic function ([Instance Endo_lit : Endo lit := @id lit]) is
    emitted as [std::any_cast] of a lambda, which throws during static
    initialisation.

    Observed (a5d6c442b):
      static inline const Endo<lit> Endo_lit = std::any_cast<Endo<lit>>(
          [](const lit &eta0_) { return Datatypes::id(eta0_); });
    [std::any_cast<Endo<lit>>] applied to a lambda builds a [std::any]
    holding the lambda's closure type and asks for a [std::function], so
    at startup:
      libc++abi: terminating due to uncaught exception of type
      std::bad_any_cast: bad any cast
    The lambda should initialise the [Endo<lit>] (a [std::function]) directly.

    Reduced from Vellvm, [Syntax/Traversal.v:203]
    ([Instance Endo_tint_literal : Endo tint_literal | 50 := id.]): the
    first thing the compiled Vellvm interpreter does is throw this, from a
    global initialiser ([std::any_cast<std::function<Tint_literal(Tint_literal)>>]). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module EndoIdInstance.
  (* Vellvm's Syntax/Traversal.v: a definitional class of endomorphisms. *)
  Class Endo (T : Type) := endo : T -> T.

  Record lit : Type := mkLit { sz : nat ; x : nat }.

  (* [Instance Endo_tint_literal : Endo tint_literal := id.] *)
  #[global] Instance Endo_lit : Endo lit := @id lit.

  Definition bump {T} `{Endo T} (t : T) : T := endo t.
  Definition l1 : lit := bump (mkLit 3 4).
  Definition is_seven : bool := Nat.eqb (sz l1 + x l1) 7.
End EndoIdInstance.

Crane Extraction "endo_id_instance" EndoIdInstance.
