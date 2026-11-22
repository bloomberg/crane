(** Found by Ephyra (round 23, under SharedVariant; reduced without it).
    A closure reads both a pair [pp] and [sb := snd pp].

    Expected: [result = 2] (both elements pass the filter).

    Fixed: a segfault (wrong value 0 under SharedVariant).  [sb] was bound
    as a reference into the pair, [const Sum<...> &sb = pp.second;], while
    the closure's init-captures were [pp = std::move(pp), sb = std::move(sb)]:
    [pp] was moved first, so [sb] copied the moved-from [pp.second].  The
    pass binding a member copy by reference (Simplify.bind_by_reference)
    checked that nothing later moves from [pp], but did not count a lambda
    taking [pp] into its capture by move; it does now, so [sb] stays a
    copy. *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Extraction.
From Stdlib Require Import List.
Import ListNotations.

Module CaptureMoveThenAlias.

Definition result : nat :=
  let pp := (0, (@inl (list nat) nat [1; 2; 3])) in
  let sb := snd pp in
  List.length (filter (fun _ : option bool =>
    match sb with
    | inl l => Nat.eqb (List.length l) 3
    | inr _ => let (p, q) := pp in false
    end) [None; Some true]).

End CaptureMoveThenAlias.

Crane Extraction "capture_move_then_alias" CaptureMoveThenAlias.
