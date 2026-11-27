(** Found by Ephyra round 28 (ST programs on main: [FZ_ST_MAIN]). A
    tail-recursive local helper in the ST monad whose accumulator [acc] is
    read only by a [newSTRef] whose reference is never used. Seen with
    pair-valued references (with a [nat] reference the read survived as an
    unused [_x] and compiled). Kin of the st-code-rank2 round 26
    [st_dead_stores] and round 5's [unused_let_local_fix_werror].

    Expected: compiles with the suite's flags; [result = 53].

    Fixed: the dead allocation was dropped, but the loop that replaces the
    tail recursion still copied the parameter into [_loop_acc] and
    reassigned it each iteration, which clang rejects under [-Werror] as set
    but not used.  A finishing pass ([dead_stores], ported from
    st-code-rank2) drops a by-value variable only ever assigned. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From ITree Require Import ITree Events.Exception.
From Crane Require Import Monads.ITree Monads.Error Monads.STMonad.
Import Monads.
Local Open Scope monad_scope.

Section S.
  Context {R : STRefs}.
  Notation E0 := (STEvent R (fun _ : nat => (nat * nat)%type) +' exceptE Err).

  Definition st_1 : itree E0 nat :=
    r0 <- newSTRef (2, 1);;
    let fix h (k : nat) (acc : nat) (p : STRef (nat * nat)) : itree E0 nat :=
      match k with
      | O => Ret 5
      | Datatypes.S k' => r <- newSTRef (k', acc);; h k' 7 p
      end in
    y <- h 4 1 r0;;
    '(a, b) <- readSTRef r0;;
    Ret (y * 10 + a + b).
End S.

Module StDeadRefLoopParam.
  Definition result : nat := run_st (@st_1 cpp_refs).
End StDeadRefLoopParam.

Crane Extraction "st_dead_ref_loop_param" StDeadRefLoopParam.
