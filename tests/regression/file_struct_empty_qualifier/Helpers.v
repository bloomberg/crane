From Crane Require Extraction.
From ExtLib Require Import Structures.Monads.
From Stdlib Require Import List NArith.
Import ListNotations MonadNotation.
Open Scope monad_scope.

(* A nested module named [N], in a file that also uses the *type* [N].  The
   module cannot become a struct called [N] -- the type already owns that
   name -- so Crane folds it into a struct named after the file, [Helpers]. *)
Module N.
  Fixpoint length {A} (l : list A) : N :=
    match l with [] => 0%N | _ :: t => N.succ (length t) end.
End N.

Section monad.
  Variable m : Type -> Type.
  Context {M : Monad m}.

  Definition map_monad {A B} (f : A -> m B) : list A -> m (list B) :=
    fix loop l :=
      match l with
      | [] => ret []
      | a :: l' => b <- f a ;; bs <- loop l' ;; ret (b :: bs)
      end.
End monad.
