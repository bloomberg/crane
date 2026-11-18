From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A local fixpoint called once with a literal list of pairs, inside a
    polymorphic definition, is inlined; its list parameter is declared
    [List<T1>] although the literal is [List<std::pair<uint64_t, T1>>].  The
    converting constructor compiles, and at run time throws
    [std::logic_error: unreachable: inactive constructor field at this
    instantiation] (wrong type, caught only by that guard). *)
Module InlinedLocalFixParamType.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.

Definition f {A : Type} (a : A) : list (option tree) :=
  let fix go (l : list tree) (acc : list (option tree)) {struct l} : list (option tree) :=
    match l with [] => [] | _ :: r => go r [] end in
  go (let fix go2 (l : list (nat * A)) (acc : list tree) {struct l} : list tree :=
        match l with [] => acc | _ :: _ => flat_map (fun _ : bool => @nil tree) [true] end
      in go2 [(0, a)] []) [].

Definition t : nat := length (f 0).

(** The same defect with the list literal's elements themselves lists: [go]'s
    parameter was declared [List<T1>] for a [List<List<T1>>]. *)
Definition g {A : Type} (a : A) : nat :=
  let fix go (l : list (list A)) : nat :=
    match l with [] => 0 | _ :: r => S (go r) end in
  go [@nil A; @nil A].

Definition u : nat := g true.

(** The same defect with a record accumulator, the list's elements pairs
    with the record, under a projection. *)
Record pt : Type := mkpt { px : nat; py : bool }.

Definition h {A : Type} (a : A) : bool :=
  py (let fix go (l : list (A * pt)) (acc : pt) {struct l} : pt :=
        match l with [] => acc | _ :: r => go r (mkpt 0 true) end
      in go [(a, mkpt 0 true)] (mkpt 0 false)).

Definition v : bool := h 9.

End InlinedLocalFixParamType.

Crane Extraction "inlined_local_fix_param_type" InlinedLocalFixParamType.
