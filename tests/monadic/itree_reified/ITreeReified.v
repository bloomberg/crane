(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Test: Reified ITree extraction.

   Exercises:
   - Functions that take [itree] as a parameter (value position),
     extracted as [std::shared_ptr<ITree<R>>].
   - CoFixpoint tree traversal with [observe] / pattern matching on
     [itreeF] constructors (RetF, TauF, VisF).
   - A [main] function with automatic wrapper generation.
*)
From Corelib Require Import PrimString.
Require Import Crane.Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.

(** IO axioms defined inline to avoid importing Monads.IO which
    pulls in sequential-mode Monads.ITree. *)
Module IO_axioms.
  Axiom ioE : Type -> Type.
  Axiom iprint_endline : string -> ioE unit.
End IO_axioms.

Crane Extract Skip Module IO_axioms.
Export IO_axioms.

(* In reified mode, iprint_endline is used as an effect value inside Vis nodes.
   It must produce a std::function<std::any()> thunk. *)
Crane Extract Inlined Constant iprint_endline =>
  "[&]() -> std::any { std::cout << %a0 << '\n'; return std::any{}; }".

Definition print_endline (s : string) : itree ioE unit :=
  ITree.trigger (iprint_endline s).

Crane Extract Inlined Constant print_endline =>
  "std::cout << %a0 << '\n'".

Module ITreeReified.

(** ---- Basic reified-parameter tests ---- *)

(** Pass-through: takes a reified itree and returns it unchanged. *)
Definition run_tree (t : itree ioE unit) : itree ioE unit := t.

(** Sequence two reified itrees. *)
Definition sequence_trees (t1 t2 : itree ioE unit) : itree ioE unit :=
  t1 ;; t2.

(** Direct mode (no itree params) should be unchanged. *)
Definition test_direct : itree ioE unit :=
  print_endline "direct1" ;; print_endline "direct2" ;; Ret tt.

(** ---- Observable tree traversal ---- *)

(** Traverse an [itree E T], logging at every Tau and Vis node.
    The result lives in [itree (ioE +' E) T]: original effects on
    the right, logging effects (IO) on the left. *)
Definition with_logging_body {E T}
  (rec : itree E T -> itree (ioE +' E) T)
  (ot  : itreeF E T (itree E T)) : itree (ioE +' E) T :=
  match ot with
  | RetF r   => Ret r
  | TauF t'  =>
      Vis (inl1 (iprint_endline "[tau]")) (fun _ => Tau (rec t'))
  | VisF e k =>
      Vis (inl1 (iprint_endline "[vis]")) (fun _ =>
        Vis (inr1 e) (fun x => rec (k x)))
  end.

Definition with_logging {E T} : itree E T -> itree (ioE +' E) T :=
  cofix with_logging_ t := with_logging_body with_logging_ (observe t).

(** A simple tree to instrument. *)
Definition greet : itree ioE unit :=
  print_endline "Hello!" ;; Ret tt.

(** Apply with_logging to greet, producing itree (ioE +' ioE) unit. *)
Definition test_logging : itree (ioE +' ioE) unit :=
  with_logging greet.

(** ---- Main (auto-wrapper) ---- *)

Definition main : itree ioE unit :=
  print_endline "=== Starting ===" ;;
  run_tree (print_endline "Hello from reified mode!") ;;
  sequence_trees
    (print_endline "First")
    (print_endline "Second") ;;
  print_endline "=== Done ===" ;;
  Ret tt.

End ITreeReified.

Crane Extraction "itree_reified" ITreeReified.
