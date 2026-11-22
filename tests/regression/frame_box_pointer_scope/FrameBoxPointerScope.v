(** Found by Ephyra (round 22, ASan). Memory safety: a recursion over two
    lists whose last case runs a local fixpoint that calls the function
    again, under [Set Crane Loopify] and [Set Crane SharedVariant].
    Expected [result = 6], with no memory error (the test is built with
    ASan, as the dune rule says).

    Fixed: Loopify's [_call] frame held [l] and [m] by pointer, and the
    adopted [go] entry pushed [_call{crane_raw(a10), crane_raw(a1)}] from
    the [crane::shared_box] copies its own frame kept, which died with the
    handler. The plan took every pointer field for a cell a copy of the
    field shares, but a shared variant holds the value in the slot itself,
    so a frame's copy of it is a value of its own. Now only fields whose
    value lies in a cell count as such (in the frame storage plan and in
    the parts a turn passes), and the frame holds [l] and [m] by value. *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Set Crane Loopify.
Set Crane SharedVariant.
Module FrameBoxPointerScope.
Fixpoint z4 (l : list (sum bool nat)) (m : list (nat * bool)) {struct l} : nat :=
  match l, m with
  | [], _ => 5
  | _ :: _, [] => 6
  | _ :: r, _ :: s =>
    let fix go (k : list nat) (acc : nat) {struct k} : nat :=
      match k with [] => z4 r s | _ :: rest => go rest 0 end in
    go [] 0
  end.
Definition result : nat := z4 [inr 0; inr 0; inl true] [(0, true)].
End FrameBoxPointerScope.
Crane Extraction "frame_box_pointer_scope" FrameBoxPointerScope.
