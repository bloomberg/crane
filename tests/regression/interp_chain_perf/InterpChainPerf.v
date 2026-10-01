(** Crane bug (performance): [interp_state h (interp intr (prog n))] runs in
    time growing much faster than [n] -- roughly n^2.8 -- where it should
    be linear.

    Measured (77f357713, -O2), [prog n] a loop of n iterations with one
    event each:
      n=10  0.049s    n=20  0.087s    n=40  0.352s    n=80  2.394s
    Results are correct.  In Vellvm, the compiled interpreter (which now
    compiles and runs without throwing) did not finish loop-phi-arith at
    n=100 in minutes (OCaml: 3.2 s at n=100000), RSS growing ~2 MB/s.

    A SIGALRM backtrace of the Vellvm binary shows the cost: hundreds of
    alternating nested frames
      std::function<...Itree<MCFGEtop-tree>::Go ()>::__clone()
      std::function<...Itree<std::any, std::any>::Itree<MCFGEtop-tree const&)::'lambda'()...>::__clone()
    i.e. the lazy converting constructors of Itree wrap a tree converted
    between [Itree<E, R>] and [Itree<std::any, std::any>] again at every
    step, and each copy of the thunk deep-clones the whole chain.

    Reduced from Vellvm, [Semantics/InterpretationStack.v]
    [interp_mcfg t s := interp_state interp_vellvm_h (interp_intrinsics t) s].
    The t.cpp asserts n=200 completes within 2 seconds (a linear
    implementation takes milliseconds). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree Events.State.
Import ITreeNotations.
Local Open Scope itree_scope.

Module InterpChainPerf.
  Variant getE : Type -> Type := Get : getE nat.
  Variant outE : Type -> Type := Out : nat -> outE unit.
  Variant noE : Type -> Type := .
  Definition TopE := getE +' outE.
  Definition BotE := outE +' noE.

  (* A loop of [n] iterations, one event per iteration, like the
     interpreter's per-instruction local reads. *)
  Definition prog (n : nat) : itree TopE nat :=
    ITree.iter (fun '(i, acc) =>
      if Nat.eqb i n then Ret (inr acc)
      else x <- trigger Get ;; Ret (inl (S i, acc + x))) (0, 0).

  Definition intr : TopE ~> itree TopE := fun _ e => trigger e.
  Definition h_get : getE ~> Monads.stateT nat (itree BotE) :=
    fun _ e s => match e with Get => Ret (s, 1) end.
  Definition pass {F} `{F -< BotE} : F ~> Monads.stateT nat (itree BotE) :=
    fun _ e s => r <- trigger e ;; Ret (s, r).
  Definition h : TopE ~> Monads.stateT nat (itree BotE) := case_ h_get (pass (F := outE)).

  (* Vellvm's interp_mcfg shape: interp_state h (interp intr t). *)
  Definition run_n (n : nat) : itree BotE (nat * nat) := interp_state h (interp intr (prog n)) 0.

  Fixpoint drive (fuel : nat) (t : itree BotE (nat * nat)) : option nat :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF (_, r) => Some r
             | TauF t' => drive f t'
             | VisF _ _ => None
             end
    end.
End InterpChainPerf.

Crane Extraction "interp_chain_perf" InterpChainPerf.
