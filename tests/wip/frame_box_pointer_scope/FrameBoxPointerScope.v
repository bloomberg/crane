(** Found by Ephyra (round 22, ASan). Memory safety: a recursion over two
    lists whose last case runs a local fixpoint that calls the function
    again, under [Set Crane Loopify] and [Set Crane SharedVariant].

    Expected: [result = 6], with no memory error (the test is built with
    ASan, as the dune rule says).

    Actual: ASan "stack-use-after-scope". Loopify replaces the recursion by
    an explicit stack of frames. The [_call_go] branch moves the frame's
    [crane::shared_box] fields into locals [a1]/[a10] and pushes
    [_call{crane_raw(a10), crane_raw(a1)}]: raw pointers into those locals'
    storage (under SharedVariant a nullary constructor lives inside the box),
    which are destroyed when the branch ends, before the [_call] frame is
    popped and read. Without ASan it happens to print 6. Also on main. *)
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
