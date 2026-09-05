From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module UnitReturningCallbackMap.

(** A [unit]-returning function becomes [void] in a higher-order position,
    which does not match the [std::monostate] element type the surrounding
    [map] was instantiated with. *)
Definition noop (n : nat) : unit := tt.

Definition units : list unit := map noop [1;2;3].

Definition callbacks : list (nat -> unit) := [noop; fun _ => tt].

Definition run : nat :=
  List.length units + List.length (map (fun f => f 0) callbacks).

Record sink := mkSink { emit : nat -> unit ; drained : unit }.

Definition s : sink := mkSink noop tt.

Definition total : nat :=
  run + (match emit s 5 with tt => 1 end) + (match drained s with tt => 1 end).

End UnitReturningCallbackMap.
Crane Extraction "unit_returning_callback_map" UnitReturningCallbackMap.
