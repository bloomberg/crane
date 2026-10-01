From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
From ExtLib Require Import Structures.Monad.
From ITree Require Import ITree.
Import ListNotations MonadNotation.
Open Scope monad_scope.

(** [mfr] recurses in the first argument of [bind], so [Set Crane Loopify]
    turns it into an explicit frame stack.  The generated loop declares its
    result as [typename _tcI0::template m<T3> _result{};] -- a
    default-constructed monadic value -- and at [m = itree E] that type has no
    default constructor (an [Itree] is a lazy cell, built only from a node or a
    thunk), so the C++ does not compile: "no matching constructor for
    initialization of 'typename Monad_itree<...>::m<...>'".

    Found in Vellvm with the global [Set Crane Loopify]: 35 of the 59 errors
    are this one, in [ListUtil.monad_fold_right] and [ListUtil.map_monad]. *)

Module LoopifyResultNoDefault.

  Section M.
    Context {m : Type -> Type} `{Monad m}.

    Fixpoint mfr {A B} (f : B -> A -> m B) (l : list A) (b : B) : m B :=
      match l with
      | [] => ret b
      | x :: xs => r <- mfr f xs b ;; f r x
      end.
  End M.

  (** A real event type: at [void1] the instance is emitted as a bare
      [Monad_itree], a separate problem. *)
  Variant ev : Type -> Type := Ask : ev nat.

  Definition sum_tree (_ : unit) : itree ev nat :=
    mfr (fun r x => ret (r + x)) [1; 2; 3; 4] 0.

End LoopifyResultNoDefault.

Set Crane Loopify.
Crane Extraction "loopify_result_no_default" LoopifyResultNoDefault.
