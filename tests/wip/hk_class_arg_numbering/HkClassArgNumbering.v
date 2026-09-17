(** Crane bug: a class over a *type constructor* is not promoted to a template
    parameter when taken as an explicit argument, and the parameter it should
    have become is left undeclared.

    [run] takes [iM : Iter M], where [M : Type -> Type].  Crane leaves it as a
    value parameter spelled with a template parameter that is never declared:

      template <Functor _tcI0, Monad _tcI1, typename T2, typename F1>
      ...
      typename _tcI0::template F<T2> run(Iter<T1> x0_, F1 &&x1_, const T2 &x2_)
                                              ^^ never declared

    A class over a plain [Type] is promoted correctly -- that is
    [class_arg_in_method], which passes as of 697c44518.  Only the
    higher-kinded case is left.

    Expected: [run] takes [Iter] as a template parameter, as it would for a
              class over a [Type].
    Actual:   error: use of undeclared identifier 'T1'
              error: too many template arguments for template template
                     parameter 'T1'

    The [too many template arguments] comes from the same confusion one level
    down, in [iter]: [crane_erase_fn<T1<std::any, std::any>>] gives two
    arguments to a [template <typename> class].

    Seen in Vellvm on ITree's [interp] --

      static typename _tcI0::template m<T3> interp(MonadIter<T2> iM, ...)

    with [T2] undeclared in a list that declares [_tcI0, _tcI1, T1, T3, F1]:
    14 "use of undeclared identifier 'T1'/'T2'" plus 3 "too many template
    arguments for template template parameter".

    This test also shows [fwd_decl_before_concept]; it is not isolated from
    it, because the instances here are concept-constrained by construction. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monads Structures.Functor Data.Monads.OptionMonad.

(* A class over a type constructor, taken as an explicit argument. *)
Class Iter (M : Type -> Type) : Type :=
  iter : forall {A}, (A -> M A) -> A -> M A.

Definition run {M : Type -> Type} `{Monad M} `{Functor M}
               (iM : Iter M) {R : Type} (step : R -> M R) (x : R) : M R :=
  iter step x.

#[global] Instance Iter_option : Iter option := fun A f x => f x.

Module HkClassArgNumbering.
  Definition use (n : nat) : option nat :=
    @run option Monad_option (@Functor_Monad option Monad_option)
         Iter_option nat (fun m => Some (S m)) n.
End HkClassArgNumbering.

Crane Extraction "hk_class_arg_numbering" HkClassArgNumbering.
