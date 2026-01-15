(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Test: Nested modules with inductives at different levels *)

From Stdlib Require Import NArith.
Open Scope nat_scope.

(* Outer module *)
Module Outer.
  (* Inductive at outer level *)
  Inductive color : Type :=
  | Red : color
  | Green : color
  | Blue : color.

  (* Inner module with its own inductive *)
  Module Inner.
    (* Inductive at inner level *)
    Inductive shape : Type :=
    | Circle : nat -> shape
    | Square : nat -> shape
    | Triangle : nat -> nat -> nat -> shape.

    (* Function using inner inductive *)
    Definition area (s : shape) : nat :=
      match s with
      | Circle r => r * r * 3  (* approximation *)
      | Square side => side * side
      | Triangle a b c => Nat.div (a * b) 2  (* approximation *)
      end.
  End Inner.

  (* Function in outer module using inner inductive *)
  Definition shape_with_color (s : Inner.shape) (c : color) : nat :=
    match c with
    | Red => Inner.area s + 100
    | Green => Inner.area s + 200
    | Blue => Inner.area s + 300
    end.

  (* Function using outer inductive *)
  Definition color_code (c : color) : nat :=
    match c with
    | Red => 1
    | Green => 2
    | Blue => 3
    end.
End Outer.

(* Test values *)
Definition my_circle := Outer.Inner.Circle 5.
Definition my_color := Outer.Red.
Definition test_area := Outer.Inner.area my_circle.
Definition test_combined := Outer.shape_with_color my_circle my_color.
Definition test_color := Outer.color_code my_color.

Require Crane.Extraction.
Require Crane.Mapping.Std.
Require Crane.Mapping.NatIntStd.

Crane Extraction TestCompile "nested_mod" test_area test_combined test_color.
