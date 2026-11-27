(* [Set Crane Loopify] must reach a recursive function that was methodified.
   A module with more than one inductive makes [wraps] eligible, and the
   method it becomes calls itself on a moved-from receiver -- [std::move] of
   the object [this] points at.  That is a cast, not a temporary, so the
   loopifier can park the receiver's address in a frame like any other; it
   used to read the move as a value receiver and decline, leaving an unbounded
   C++ recursion that overflows the stack at depth 100000. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.
Set Crane Loopify.

Module MethodifiedTmcNoLoopify.

  (* A second inductive in the module is what makes [wraps] methodifiable. *)
  Inductive lst : Set := Nil | Cons : nat -> lst -> lst.

  Inductive wrap : Set := W : lst -> wrap | WW : wrap -> wrap.

  Fixpoint wraps (n : nat) (w : wrap) : wrap :=
    match n with O => w | S k => WW (wraps k w) end.

  Fixpoint wdepth (w : wrap) : nat :=
    match w with W _ => 0 | WW x => S (wdepth x) end.

  Definition deep : nat := wdepth (wraps 100000 (W Nil)).

End MethodifiedTmcNoLoopify.

Crane Extraction "methodified_tmc_no_loopify" MethodifiedTmcNoLoopify.
