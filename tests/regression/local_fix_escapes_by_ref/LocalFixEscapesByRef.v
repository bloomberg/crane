From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
From ExtLib Require Import Structures.Monad.
Import ListNotations MonadNotation.
Open Scope monad_scope.

(** [map_monad_acc] (Vellvm's [ListUtil.map_monad_acc]) is a local [fix]
    whose recursive call sits in a [bind] continuation.  Crane emitted the
    fix as [auto loop_impl = [&](auto &_self_loop, ...) { ... f(a0) ... }]
    and the continuation as [[=](T3 b) { return _self_loop(_self_loop, ...);
    }], which copied [loop_impl] -- still holding [f] and the enclosing frame
    {e by reference} -- into a closure that escapes.  In a state monad the
    bind does not run the continuation; it returns a function of the state,
    which is called after [map_monad_acc] has returned, by when [f] is a
    dangling reference.  The fixpoint's escape analysis looked only at the
    code after the fixpoint, never inside its own bodies, and not at all
    when the fixpoint is applied where it is defined.  A self-call inside a
    closure the fixpoint's body builds now makes the fixpoint capture by
    value.

    [check] alone can pass, because the dead frame is often still intact;
    the test driver also builds the state function, overwrites the stack,
    and only then runs it.

    Found in Vellvm's mem-scan and alloca-churn ([Memory1]'s state monad
    [memS]). *)

Module LocalFixEscapesByRef.

  (** A record, like Vellvm's [MemS]: [bind] builds a new state function and
      returns it without running [k]. *)
  Inductive res (A : Type) : Type := Res (s : nat) (a : A).
  Arguments Res {A}.

  Record st (A : Type) : Type := mkst { runst : nat -> res A }.
  Arguments mkst {A}.
  Arguments runst {A}.

  #[export] Instance Monad_st : Monad st :=
    {| ret _ x := mkst (fun s => Res s x);
       bind _ _ m k := mkst (fun s => match runst m s with Res s' a => runst (k a) s' end) |}.

  Definition map_monad_acc {A B} (f : A -> st B) (l : list A) : st (list B) :=
    (fix loop acc l :=
       match l with
       | [] => ret (rev_append acc [])
       | a :: l' => b <- f a ;; loop (b :: acc) l'
       end) [] l.

  (** Each step doubles the element and counts one state tick. *)
  Definition run (l : list nat) : res (list nat) :=
    runst (map_monad_acc (fun x => mkst (fun s => Res (S s) (2 * x))) l) 0.

  Definition check (_ : unit) : bool :=
    match run [1; 2; 3; 4] with
    | Res n r => Nat.eqb n 4 && Nat.eqb (fold_left Nat.add r 0) 20
    end.

End LocalFixEscapesByRef.

Crane Extraction "local_fix_escapes_by_ref" LocalFixEscapesByRef.
