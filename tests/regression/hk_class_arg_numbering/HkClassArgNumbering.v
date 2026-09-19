(** Crane bug: a class over a *type constructor* reaches its uses with the
    wrong number of template arguments.

    [run] takes [iM : Iter M], where [M : Type -> Type].  Its own signature is
    right -- the carrier resolves to the class parameter's alias template:

      typename _tcI0::template F<T2> run(Iter<_tcI0::F> x0_, F1 &&x1_,
                                         const T2 &x2_)

    What is left is the arity of that carrier everywhere else.  In [iter] the
    erasure helper applies it to two arguments:

      T1<T2> iter(Iter<T1> iter0, F1 &&x, const T2 &x0) {
        return iter0(crane_erase_fn<T1<std::any, std::any>>(x), x0);
                                       ^^ [T1] takes one

    and [run]'s call passes the carrier as a type rather than as the template
    it is:

      iter<typename _tcI0::F, T2>(...)
           ^^ deduction is not allowed for an alias template member

    Expected: [crane_erase_fn<std::function<T1<std::any>(std::any)>>] and a
              template template argument [_tcI0::F].
    Actual:   error: too many template arguments for template template
                     parameter 'T1'
              error: template argument for template template parameter must be
                     a class template or type alias template

    Seen in Vellvm on ITree's [interp].

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
