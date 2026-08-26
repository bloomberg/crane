From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane NonAtomicRc.
Set Crane Loopify.
Set Crane Reuse.

(** Codegen bug: the generated C++ does not compile.

    With Loopify + Reuse + NonAtomicRc all on, the TMC loop emits a
    reuse-uniqueness latch

      LoopifyReuseBoolQualified::bool _uniq = true;   <-- qualified [bool]

    inside the extracted module's namespace, so clang rejects it with
    "expected unqualified-id" and every later use of [_uniq] is an
    undeclared identifier.

    Root cause: [src/loopify.ml:3406] declares the latch with
    [Tid (Id.of_string "bool", [])]. [Tid] is the *user-defined* type
    constructor, so the printer prefixes it with the current module
    namespace; a builtin needs a raw type instead.

    Any TMC-shaped fixpoint triggers it. All three options are required:
    dropping [Set Crane Reuse.] removes the latch and the file compiles. *)

Module LoopifyReuseBoolQualified.

Inductive lst : Type :=
| nil : lst
| cons : nat -> lst -> lst.

Fixpoint build (n : nat) (acc : lst) : lst :=
  match n with O => acc | S m => build m (cons n acc) end.

Fixpoint sum (l : lst) : nat :=
  match l with nil => 0 | cons x t => x + sum t end.

Fixpoint incr (l : lst) : lst :=
  match l with nil => nil | cons x t => cons (x + 1) (incr t) end.

Definition go (n : nat) : nat := sum (incr (build n nil)).

End LoopifyReuseBoolQualified.

Crane Extraction "loopify_reuse_bool_qualified" LoopifyReuseBoolQualified.
