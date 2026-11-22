(** Found by the BDE probe after Ephyra round 20. A non-tail recursion
    over a list under [Mapping.BDE]: Loopify lowers it to a frame machine
    whose stack is a [crane::small_vector].

    Expected: compiles with the BDE flavour; [total = 6], [all_small = true].

    Fixed: the BDE [crane::small_vector] (theories/cpp_bde/small_vector.h)
    had [push_back] only, and the frame machine pushes with
    [_stack.emplace_back(...)]; it now has [emplace_back].  The frame then
    walked the list with [crane_raw] of a [bsl::shared_ptr], which had no
    overload; crane_fn.h now takes any smart pointer with [get()]. *)
From Crane Require Import Mapping.NatIntBDE Mapping.BDE.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

Module FrameStackBde.

Fixpoint sum (l : list nat) : nat :=
  match l with [] => 0 | x :: r => x + sum r end.

Definition total : nat := sum [1; 2; 3].

Definition all_small : bool := forallb (fun x => Nat.ltb x 4) [1; 2; 3].

End FrameStackBde.

Crane Extraction "frame_stack_bde" FrameStackBde.
