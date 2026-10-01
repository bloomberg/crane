(** Crane bug (runtime): [interp_state h (interp intr prog)] -- a tree
    produced by one [interp] (into the source family [TopE]) then
    interpreted statefully into [BotE] -- converts the source tree to the
    target family *structurally* instead of interpreting its events.

    It compiles; at run time a [Sum1] converting constructor reaches an
    alternative the target sum does not have:
      libc++abi: terminating due to uncaught exception of type
      std::logic_error: unreachable: inactive constructor field at this instantiation
    [interp_state h prog] on the same [prog] without the inner [interp]
    runs correctly (the first visible event is the re-raised [Out 1]).

    Reduced from Vellvm, [Semantics/InterpretationStack.v]
    ([interp_mcfg t s := interp_state interp_vellvm_h (interp_intrinsics t) s],
    [interp_intrinsics] an [interp] into [MCFGEtop]): with its last compile
    error hand-fixed, the compiled interpreter dies with this exception,
    thrown from [Sum1<ExternalCallE, Sum1<OOME, ...>>::Sum1<ExternalCallE,
    Sum1<IntrinsicE, ...>>] (MCFGEtop -> MCFGEbot) under ITree::bind, from
    [Itree<std::any, Dvalue>] made from the [interp_intrinsics] tree
    ([interp_state<..., std::any, FusedS, T1>] writes the source family as
    [std::any]). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree Events.State.
Import ITreeNotations.
Local Open Scope itree_scope.

Module InterpStateAfterInterp.
  Variant getE : Type -> Type := Get : getE nat.
  Variant outE : Type -> Type := Out : nat -> outE unit.
  Variant noE : Type -> Type := .
  Definition TopE := getE +' outE.
  Definition BotE := outE +' noE.

  Definition prog : itree TopE nat :=
    x <- trigger Get ;; trigger (Out x) ;; y <- trigger Get ;; Ret (x + y).

  Definition h_get : getE ~> Monads.stateT nat (itree BotE) :=
    fun _ e s => match e with Get => Ret (S s, s) end.
  (* Vellvm's fused_trigger: events not interpreted here are re-raised in
     the target family. *)
  Definition pass {F} `{F -< BotE} : F ~> Monads.stateT nat (itree BotE) :=
    fun _ e s => r <- trigger e ;; Ret (s, r).
  Definition h : TopE ~> Monads.stateT nat (itree BotE) := case_ h_get (pass (F := outE)).

  (* Vellvm: interp_state interp_vellvm_h (interp_intrinsics t) s, where
     interp_intrinsics is itself an interp into the same family. *)
  Definition intr : TopE ~> itree TopE := fun _ e => trigger e.
  Definition out : itree BotE (nat * nat) := interp_state h (interp intr prog) 1.

  (* The first visible event is the re-raised [Out 1] (Get answered 1). *)
  Fixpoint first_out (fuel : nat) (t : itree BotE (nat * nat)) : option nat :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF _ => None
             | TauF t' => first_out f t'
             | VisF e _ => match e with inl1 (Out n) => Some n | inr1 e' => match e' with end end
             end
    end.
  Definition is_one : bool := match first_out 200 out with Some n => Nat.eqb n 1 | None => false end.
End InterpStateAfterInterp.

Crane Extraction "interp_state_after_interp" InterpStateAfterInterp.
