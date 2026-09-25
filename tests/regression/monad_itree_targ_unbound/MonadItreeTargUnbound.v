(** A definition of the [~>] (natural-transformation) form whose target is
    ITree's [Basics.Monads.stateT] loses the event-family template parameter
    from its *head* but keeps referring to it in its *body*, so the emitted
    [Monad_itree<T1>] dictionary argument is unbound.

    Expected: the head declares every template parameter the body mentions,
    e.g. [template <Params _tcI0, typename T1, typename T2>], and the call
    site's three arguments [<_tcI0, FailE, Nat>] line up with it.

    Actual: the head is [template <Params _tcI0, typename T2>] -- the event
    slot is erased -- while the body still emits
    [Monad_stateT<Monad_itree<T1>, env>], giving

      error: use of undeclared identifier 'T1'

    Note the numbering: the surviving index parameter is still named [T2], so
    the erased event kept its [T1] slot in the body's numbering.

    Using ExtLib's record [stateT] instead of ITree's function-shaped
    [Basics.Monads.stateT] does *not* reproduce -- there the head correctly
    declares [T1].

    Seen in Vellvm at [vellvm_bench.h:14705], from
    [src/rocq/Semantics/Handlers/Global.v:62]:

      Definition handle_global_debug {E} `{FailureE -< E}
        : GlobalE ~> stateT map (itree E) :=
        fun _ e => (res <- handle_global e;; update_globals_ref e;; ret res)%monad.

    11 of the 47 [use of undeclared identifier] errors in that build are this
    shape.

    Once the head declared [T1], two further defects in [handle] were
    reachable, both on the [vis] with an absurd continuation:

    - The continuation [fun x : void => match x with end] is a lambda whose
      body only throws, so its deduced return type is [void], and
      [itree_vis] cannot read a tree type off it.  The lambda is annotated
      with its slot's codomain in that case, but the slot it was handed was
      the tree's {e result} type: [gen_expr_custom_cons] gave the i-th value
      argument the i-th type argument, which is right for [pair] and wrong
      for [VisF], whose second field is [X -> itree E R].

    - The event reaching [itree_vis] is plain data -- the [subevent]
      injection into an abstract [E] leaves the bare [FailE] -- and
      [itree_vis] took only an event already spelled as a thunk, where
      [itree_trigger] reified plain data. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ExtLib Require Import Structures.Monads Data.Monads.StateMonad.
From ITree Require Import ITree Basics.Basics Events.State Basics.MonadState.
Import ITree.Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

Variant FailE : Type -> Type := Throw : unit -> FailE void.
Variant Ev : Type -> Type := Ev0 : Ev nat.

Class Params := { width : nat }.

Definition env := nat.

Section S.
  Context {Pa : Params}.
  Context {E} `{FailE -< E}.

  Definition step (n : nat) : stateT env (itree E) nat :=
    fun s => Ret (s, n + width).

  Definition handle : Ev ~> stateT env (itree E) :=
    fun _ e => match e with
               | Ev0 => fun s =>
                   if Nat.eqb s 0
                   then vis (@subevent FailE E _ _ (Throw tt)) (fun x : void => match x with end)
                   else Ret (s, s)
               end.

  (* The [~>] form, exactly as Vellvm's [handle_global_debug]. *)
  Definition twice : Ev ~> stateT env (itree E) :=
    fun _ e =>
      (res <- handle _ e;;
       step 1;;
       ret res)%monad.

End S.

Module Qf.
  Definition use `{Pa : Params} (n : nat) : itree FailE (nat * env) :=
    twice nat Ev0 n.
End Qf.
Crane Extraction "monad_itree_targ_unbound" Qf.
