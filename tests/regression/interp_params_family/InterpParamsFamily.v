(** Crane bug: [interp h prog] at event families built inside a
    [Context {Pa : Params}] section passes ITree's [MonadIter_itree]
    dictionary without its family argument.

    Observed (86aac86af):
      [](auto &&_ec0, std::any _ec1) { return ::MonadIter_itree(_ec0, _ec1); }
    [MonadIter_itree] is [template <typename T1, typename F0>
    Itree<T1, std::any> MonadIter_itree(F0 &&, std::any)]; [T1] (the
    family, here [OutE<typename _tcI0::ptr>]) is not deducible and not
    written.  Diagnostics:
      error: no matching function for call to 'MonadIter_itree'
      note: candidate template ignored: couldn't infer template argument 'T1'
      error: no matching function for call to 'interp'
    With closed families (itree_interp, now in regression) the argument is
    written ([MonadIter_itree<noE>]).

    Found behind Vellvm's interp_mcfg error on 86aac86af, after hand-fixing
    it: [InterpretationStack.interp_mcfg]'s [interp_state] and
    [interp_intrinsics]'s [interp] both get
    [::MonadIter_itree(_ec0, _ec1)] (plus a [ReSum_id] dictionary lambda
    of the wrong arity, reported separately). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.
Import ITreeNotations.
Local Open Scope itree_scope.

Module InterpParamsFamily.
  Class Params : Type := { ptr : Type ; zero : ptr }.

  Section WithParams.
    Context {Pa : Params}.
    Variant getE : Type -> Type := Get : getE nat.
    Variant putE : Type -> Type := Put : ptr -> putE unit.
    Variant noE : Type -> Type := .
    Definition InE := getE +' putE.
    Definition OutE := putE +' noE.

    Definition prog : itree InE nat := x <- trigger Get ;; y <- trigger Get ;; Ret (x + y).

    (* Vellvm's interpretation stack: handlers into another family built
       from promoted-parameter events, combined with case_ / id_ and run
       with interp. *)
    Definition h_get : getE ~> itree OutE := fun _ e => match e with Get => Ret 2 end.
    Definition h_put : putE ~> itree OutE := fun _ e => trigger e.
    Definition h : InE ~> itree OutE := case_ h_get h_put.
    Definition out : itree OutE nat := interp h prog.
  End WithParams.

  #[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.

  Fixpoint run (fuel : nat) (t : itree OutE nat) : option nat :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF r => Some r
             | TauF t' => run f t'
             | VisF _ _ => None
             end
    end.
  Definition is_four : bool := match run 100 out with Some n => Nat.eqb n 4 | None => false end.
End InterpParamsFamily.

Crane Extraction "interp_params_family" InterpParamsFamily.
