(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Records with default field values. *)

From Stdlib Require Import Nat Bool List String.
Import ListNotations.

Module RecordDefaults.

(* Record with default values via notation/wrapper *)
Record Config := mkConfig {
  cfg_width  : nat;
  cfg_height : nat;
  cfg_depth  : nat;
  cfg_debug  : bool;
}.

Definition default_config : Config := {|
  cfg_width  := 80;
  cfg_height := 24;
  cfg_depth  := 1;
  cfg_debug  := false;
|}.

(* Update individual fields *)
Definition set_width (w : nat) (c : Config) : Config :=
  {| cfg_width := w;
     cfg_height := cfg_height c;
     cfg_depth := cfg_depth c;
     cfg_debug := cfg_debug c |}.

Definition set_debug (d : bool) (c : Config) : Config :=
  {| cfg_width := cfg_width c;
     cfg_height := cfg_height c;
     cfg_depth := cfg_depth c;
     cfg_debug := d |}.

(* Nested record *)
Record Point := mkPoint { px : nat; py : nat }.
Record Rect := mkRect { origin : Point; extent : Point }.

Definition rect_area (r : Rect) : nat :=
  px (extent r) * py (extent r).

Definition make_rect (x y w h : nat) : Rect :=
  {| origin := {| px := x; py := y |};
     extent := {| px := w; py := h |} |}.

(* Config computations *)
Definition total_cells (c : Config) : nat :=
  cfg_width c * cfg_height c * cfg_depth c.

(* Test values *)
Definition test_default_width : nat := cfg_width default_config.
Definition test_default_debug : bool := cfg_debug default_config.
Definition test_cells : nat := total_cells default_config.
Definition test_modified : nat :=
  total_cells (set_width 120 (set_debug true default_config)).
Definition test_rect_area : nat := rect_area (make_rect 0 0 10 5).

End RecordDefaults.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "record_defaults" RecordDefaults.
