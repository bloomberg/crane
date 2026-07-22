From Crane Require Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** Attempt to reproduce the residual Newick.h/PPM.h bug: a LIST is built by
    generically dispatching to another production's result (mirroring how
    the real grammar builds e.g. [TREES ::= TREE TREES] via a generic
    `find_predicate_and_action`-style call whose return type is
    production-dependent, hence erased to [std::any]), and consing that
    generic result onto an accumulating list, then forwarding the whole list
    to a concretely-typed top-level function. Earlier attempts using a
    directly concretely-typed [list nat] (not built via generic dispatch)
    did NOT reproduce the bug -- this tries forcing genuine erasure of the
    list itself via a single generic [run] function whose return type
    [domty (projT1 e)] depends on the runtime witness [e], just like
    Newick's grammar-entry dispatch. *)
Definition wrap_list (xs : list nat) : bool := Nat.eqb (List.length xs) (List.length xs).

Definition domty (n : nat) : Type :=
  match n with
  | 0 => list nat   (* TREES-like: produces a list *)
  | _ => nat         (* TREE-like: produces a single leaf *)
  end.

Definition entry : Type := { p : nat & unit -> domty p }.

Definition mk (p : nat) (f : unit -> domty p) : entry := existT _ p f.

(* Generic dispatch, mirroring find_predicate_and_action: return type
   depends on the runtime witness `e`, forcing erasure. *)
Definition run (e : entry) : domty (projT1 e) := (projT2 e) tt.

Definition entry_tree : entry := mk 1 (fun _ => 42).

Definition entry_trees : entry :=
  mk 0 (fun _ => (run entry_tree) :: nil).

Definition check (u : unit) : bool := wrap_list (run entry_trees).

Crane Extraction "sigt_leaf_list_dispatch" check entry_trees entry_tree.
