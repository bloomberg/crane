(** Found by Ephyra round 23 (under SharedVariant; reduced without it).
    A closure reads both a pair [pp] and [sb := snd pp]. [sb] is lowered
    to a reference into the pair, [const Sum<...> &sb = pp.second;], and
    the closure's init-captures are [pp = std::move(pp), sb = std::move(sb)]:
    [pp] is moved first, so [sb] then copies the moved-from [pp.second].
    Expected: [result = 2] (both elements pass the filter).
    Actual: segfault (the moved-from list inside the [inl] is read); under
    SharedVariant, with a [bool] payload, the moved-from [shared_variant]
    holds no alternative and the filter keeps nothing (wrong value 0
    instead of 2). Also on main. *)
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
