(** Crane bug (runtime): a [let]-bound monadic computation over the
    *source* family, inside a function whose result is over the *target*
    family, gets its Monad instance at the target family.

    Observed (post-interp_state_after_interp HEAD):
      Itree<BotE<std::any>, Nat> LetBoundMonadFamily::gen(Itree<TopE<std::any>, Nat> arg) {
        ... Monad0::template bind<Monad_itree<BotE<std::any>>, ...>(arg, ...)   // should be TopE
    [arg] (a TopE tree) is then converted structurally to a BotE tree by the
    Itree/ItreeF/Sum1 converting constructors, and at run time:
      libc++abi: terminating due to uncaught exception of type
      std::logic_error: unreachable: inactive constructor field at this instantiation
    ([t]'s type is fixed by [x <- arg], and it is passed to [interp h t]
    whose parameter is [itree TopE _]; the enclosing function's result type
    [itree BotE nat] should not reach it.)

    Reduced from Vellvm, [Semantics/TopLevel.v] [interpreter_gen]:
      let t := args <- arg_gen;; denote_vellvm ... in interp_mcfg t (...)
    emitted as [t0 = Monad0::template bind<Monad_itree<MCFGEbot<...>>, ...>]
    (arg_gen and denote_vellvm are MCFGtop).  This is the runtime throw of
    the zero-error Vellvm binary (Sum1 MCFGbot<-MCFGtop converting ctor,
    under interp_intrinsics's interp). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.
From ExtLib Require Import Structures.Monad.
Import ITreeNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Module LetBoundMonadFamily.
    Variant getE : Type -> Type := Get : nat -> getE nat.
    Variant outE : Type -> Type := Out : nat -> outE unit.
    Variant noE : Type -> Type := .
    Definition TopE := getE +' outE.
    Definition BotE := outE +' noE.

    Definition h_get : getE ~> itree BotE := fun _ e => match e with Get _ => Ret 2 end.
    Definition h_out : outE ~> itree BotE := fun _ e => trigger e.
    Definition h : TopE ~> itree BotE := case_ h_get h_out.

    (* Vellvm's TopLevel.interpreter_gen:
         let t := args <- arg_gen;; denote_vellvm ... args ... in interp_mcfg t ...
       The let-bound [t] is a tree over the *source* family (MCFGEtop), the
       function's result is over the target family (MCFGEbot). *)
    Definition gen (arg : itree TopE nat) : itree BotE nat :=
      let t := x <- arg ;; ret (S x) in
      interp h t.

  Definition result : itree BotE nat := gen (trigger (Get 0)).
  Fixpoint run (fuel : nat) (t : itree BotE nat) : option nat :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF r => Some r
             | TauF t' => run f t'
             | VisF _ _ => None
             end
    end.
  (* Get answered with 2, then S 2 = 3 *)
  Definition is_three : bool := match run 100 result with Some n => Nat.eqb n 3 | None => false end.
End LetBoundMonadFamily.

Crane Extraction "let_bound_monad_family" LetBoundMonadFamily.
