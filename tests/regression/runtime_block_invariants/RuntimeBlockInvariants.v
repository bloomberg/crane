(* The runtime's shared blocks, exercised directly by the driver: a
   coinductive's cell and a closure block.

   Expected:
   - forcing a [crane::lazy] that holds nothing throws, instead of
     dereferencing a null node;
   - forcing a cell from inside its own thunk throws, as OCaml's [Lazy.force]
     does, instead of running the thunk twice and destroying the first
     result under its caller;
   - a thunk that throws leaves the cell forceable again;
   - a closure capturing an over-aligned value is allocated at that
     alignment: the per-type free list's [operator new] ignored alignment.
   Before: a null dereference, a second run, and a misaligned capture. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Module RuntimeBlockInvariants.
  CoInductive stream : Type := SCons : nat -> stream -> stream.

  CoFixpoint from (n : nat) : stream := SCons n (from (S n)).

  Definition hd (s : stream) : nat := match s with SCons x _ => x end.
End RuntimeBlockInvariants.

Crane Extraction "runtime_block_invariants" RuntimeBlockInvariants.
