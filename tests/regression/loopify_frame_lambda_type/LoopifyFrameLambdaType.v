From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
From ExtLib Require Import Structures.Monad.
Import ListNotations MonadNotation.
Open Scope monad_scope.

(** [comb] recurses in the first argument of [bind], so [Set Crane Loopify]
    gives it a frame stack whose resume frame saves the continuation.  The
    frame declares that field's type as
    [std::decay_t<decltype([](std::pair<...> x0) { ... })>] -- the type of a
    lambda *expression* written inside the struct -- and a lambda expression
    has a type of its own: the continuation built at the push site is a
    different closure type, so the push does not compile ("no viable
    conversion from '(lambda at ...)'").  The body copied into the
    [decltype] also stands the captured pattern variables in with
    [std::declval<T1 &>()], which trips libc++'s "std::declval can only be
    used in an unevaluated context" static assertion, since a lambda body is
    evaluated.

    Found in Vellvm with the global [Set Crane Loopify]:
    [Denotation.combine_lists_varargs], 3 of its 59 errors. *)

Module LoopifyFrameLambdaType.

  Variant res (X : Type) : Type := Err | Ok (x : X).
  Arguments Err {X}.
  Arguments Ok {X}.

  #[export] Instance Monad_res : Monad res :=
    {| ret _ x := Ok x;
       bind _ _ c k := match c with Err => Err | Ok x => k x end |}.

  Fixpoint comb {A B : Type} (l1 : list A) (l2 : list B)
      : res (list (A * B) * list B) :=
    match l1, l2 with
    | [], [] => ret ([], [])
    | x :: xs, y :: ys =>
        '(l, rest) <- comb xs ys ;;
        ret ((x, y) :: l, rest)
    | _, [] => Err
    | [], rest => ret ([], rest)
    end.

  Definition check (_ : unit) : bool :=
    match comb [1; 2] [10; 20; 30; 40] with
    | Ok (pairs, rest) =>
        Nat.eqb (List.length pairs) 2 && Nat.eqb (List.fold_left Nat.add rest 0) 70
    | Err => false
    end.

End LoopifyFrameLambdaType.

Set Crane Loopify.
Crane Extraction "loopify_frame_lambda_type" LoopifyFrameLambdaType.
