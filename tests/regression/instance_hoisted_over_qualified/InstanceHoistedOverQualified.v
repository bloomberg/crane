(* A typeclass instance declared in a file that becomes a file struct is
   emitted at *file scope*, but references to it are qualified with the
   struct's name, which does not declare it.

   Expected: map_monad<EOUP_Monad, Nat, Nat>(...)
   Actual:   map_monad<MemoryBytes::EOUP_Monad, Nat, Nat>(...)
     error: no member named 'EOUP_Monad' in 'MemoryBytes'

   [struct EOUP_Monad] is forward-declared and defined at file scope, outside
   [struct MemoryBytes], so the qualifier is wrong by where the struct was
   emitted while being right by where it was declared in Rocq.

   Two things are needed and neither is obvious:

   - The instance must live in a *file*, not a Rocq [Module].  An instance
     inside a [Module] stays nested in that module's struct, so the qualifier
     is correct and the same program compiles.
   - That file's definitions must be wrapped in a file struct, which only
     happens when a name collides across files -- hence [Eou.helper].

   Signature positions were already correct: the enclosing hoisted
   definition's own return and parameter types name file-scope structs
   unqualified.  It was specifically a type argument written inside an
   *expression*.

   Fixed by recording the instance where the layout already records the
   wrapper module's [using] aliases -- both are names the wrapper's module
   contributes to global scope rather than to the struct, and
   [Cpp_names.struct_qualifier_for] reads the one table for both.  The
   printer cannot answer this: the reference is in the [.cpp], which is
   written before the [.h] that declares the struct, so "where was this
   emitted" has to be settled by [Structure_analysis] before rendering. *)
From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import List.
From CraneTestsRegression Require Import instance_hoisted_over_qualified.Eou.
From CraneTestsRegression Require Import instance_hoisted_over_qualified.MemoryBytes.

Module InstanceHoistedOverQualified.
  Definition use (bs : list nat) := (Eou.helper 0, MemoryBytes.bump_all bs).
End InstanceHoistedOverQualified.

Crane Extraction "instance_hoisted_over_qualified" InstanceHoistedOverQualified.
