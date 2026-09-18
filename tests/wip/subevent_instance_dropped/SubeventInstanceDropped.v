(** Crane bug: a function that takes an ITree subevent instance ([E -< X])
    loses the instance -- and every other parameter's name -- from its
    signature, while the body and the call sites still pass it.

    [cast] takes the [E -< X] instance and the event.  Crane emits it with no
    parameter names at all, and with the instance gone:

      template <template <typename> class T1, typename T2 = void, typename T3>
      std::shared_ptr<ITree<T3>> cast(T1<T3>) {
        return <T2, T3>(h);
                     ^^ [h] is the instance, which is not a parameter
      }

    The callee in that body has lost its name too.  At the call site the
    instance is passed anyway, as an extra leading argument the declaration
    does not have:

      cast<FailE, T1, Empty_set>(h, FailE::fail(std::move(n)));
                                 ^^ one argument too many, and undeclared

    Expected: the instance to be a parameter (or to be erased consistently at
              the call sites), and the event parameter to keep its name.
    Actual:   error: use of undeclared identifier 'h'
              error: expected expression
              error: 'T2' does not refer to a value

    Seen in Vellvm 128 times -- [h] 50, [h0] 31, [h1] 28, [h3] 13, [h2] 6 --
    the largest cluster in the extracted interpreter.  Every [LLVMEvents]
    raiser goes through it: [raise], [raiseUB], [raiseOOM], [raiseLLVM],
    [intrinsic], all of which are [trigger_cast] over a [-<] instance. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.

Variant FailE : Type -> Type := Fail : nat -> FailE void.

(* [cast] takes the subevent instance and passes it on. *)
Definition cast {E X Y} `{E -< X} (e : E Y) : itree X Y := trigger e.

Definition boom {E} {A} `{FailE -< E} (n : nat) : itree E A :=
  ITree.bind (cast (Fail n)) (fun v : void => match v with end).

Module SubeventInstanceDropped.
  Definition use (n : nat) : itree FailE nat := boom n.
End SubeventInstanceDropped.

Crane Extraction "subevent_instance_dropped" SubeventInstanceDropped.
