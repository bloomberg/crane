(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Closures stored in data structures — functions in lists/records. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module ClosuresInData.

(** A list of functions: successor, doubling, and squaring. *)
Definition fn_list : list (nat -> nat) :=
  [S; fun x => x + x; fun x => x * x].

(** [apply_all fns x] applies every function in [fns] to [x],
    returning the list of results. *)
Definition apply_all (fns : list (nat -> nat)) (x : nat) : list nat :=
  map (fun f => f x) fns.

(** A pair of invertible transformations: [forward] and [backward]. *)
Record transform := mk_transform {
  forward : nat -> nat;
  backward : nat -> nat
}.

(** A transform that doubles via addition and halves via division. *)
Definition double_transform : transform :=
  mk_transform (fun x => x + x) (fun x => x / 2).

Definition apply_forward (t : transform) (x : nat) : nat := forward t x.
Definition apply_backward (t : transform) (x : nat) : nat := backward t x.

(** [compose_all fns x] folds [fns] left, threading [x] through each
    function in sequence. *)
Definition compose_all (fns : list (nat -> nat)) (x : nat) : nat :=
  List.fold_left (fun acc f => f acc) fns x.

(** A pipeline of transformations: increment, double, then add 10. *)
Definition pipeline : list (nat -> nat) :=
  [fun x => x + 1; fun x => x * 2; fun x => x + 10].

(** [maybe_apply mf x] applies function [mf] to [x] if present,
    otherwise returns [x] unchanged. *)
Definition maybe_apply (mf : option (nat -> nat)) (x : nat) : nat :=
  match mf with
  | None => x
  | Some f => f x
  end.

(* === Test values === *)

Definition test_apply_all : list nat := apply_all fn_list 5.
Definition test_forward : nat := apply_forward double_transform 7.
Definition test_backward : nat := apply_backward double_transform 14.
Definition test_compose : nat := compose_all pipeline 3.
Definition test_maybe_some : nat := maybe_apply (Some S) 41.
Definition test_maybe_none : nat := maybe_apply None 42.

End ClosuresInData.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "closures_in_data" ClosuresInData.
