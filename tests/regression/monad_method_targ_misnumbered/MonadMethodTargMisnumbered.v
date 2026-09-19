(* A monad-polymorphic Fixpoint in a Section, extracted with the reified ITree
   backend, numbers the type arguments of its dictionary method calls against a
   different variable space than its own template head.

   Expected: the body uses the head's own parameters, e.g.

     template <Monad _tcI0, typename T2, typename T3, typename F0>
     typename _tcI0::template m<T3> monad_fold_right(...) {
       ... return _tcI0::template ret<T3>(b);
       ... return _tcI0::template bind<T3, T3>(...);

   Actual: the head is right but the method calls name T10, which is not a
   template parameter of anything:

       ... return _tcI0::template ret<T10>(b);
       ... return _tcI0::template bind<T10, T10>(...);

     error: use of undeclared identifier 'T10'

   Requires Monads.ITreeReified to be imported. Without it Crane routes the
   calls through the helper struct instead (Monad0::template ret<_tcI0>(b)),
   which is correct and compiles -- so the mis-numbering only shows up in the
   direct concept-member call form.

   Reduced from Vellvm's Utils/ListUtil.v:831 (monad_fold_right), which emits
   character-for-character the same body. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ExtLib Require Import Structures.Monads Data.Monads.OptionMonad.
Import MonadNotation.
Open Scope monad_scope.

Section monad.
  Variable m : Type -> Type.
  Variable M : Monad m.

  Fixpoint monad_fold_right {A B} (f : B -> A -> m B) (l : list A) (b : B) : m B :=
    match l with
    | nil => ret b
    | cons x xs =>
        r <- monad_fold_right f xs b ;;
        f r x
    end.
End monad.

Module MonadMethodTargMisnumbered.
  Definition use (l : list nat) : option nat :=
    monad_fold_right option _ (fun b a => Some (b + a)) l 0.
End MonadMethodTargMisnumbered.

Crane Extraction "monad_method_targ_misnumbered" MonadMethodTargMisnumbered.
