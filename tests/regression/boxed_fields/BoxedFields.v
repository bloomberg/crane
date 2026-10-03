(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Set Crane BoxedFields]: a constructor field whose type is an inductive is
    stored behind the recursive-field smart pointer, and one typed by a
    parameter as [crane::field<T>], boxed where copying [T] is not cheap.
    Covers an inductive held by another, a list of them (built by tail modulo
    cons), custom-mapped option and pair fields, a recursive type holding a
    non-recursive one, loopified traversals that read the boxed fields, and a
    parameter field instantiated both ways. *)

From Stdlib Require Import List.
Import ListNotations.

Module BoxedFields.

Inductive point : Type := Pt : nat -> nat -> point.

Definition px (p : point) : nat := match p with Pt x _ => x end.
Definition py (p : point) : nat := match p with Pt _ y => y end.

Inductive shape : Type :=
| Circle : point -> nat -> shape
| Poly : list point -> shape
| Tagged : option point -> (nat * point) -> shape.

Definition weight (s : shape) : nat :=
  match s with
  | Circle c r => px c + py c + r
  | Poly ps => fold_left (fun acc p => acc + px p + py p) ps 0
  | Tagged o (n, p) =>
    n + px p + match o with Some q => py q | None => 0 end
  end.

Fixpoint shift (d : nat) (ps : list point) : list point :=
  match ps with
  | [] => []
  | Pt x y :: rest => Pt (x + d) y :: shift d rest
  end.

Inductive scene : Type :=
| Empty : scene
| Layer : shape -> scene -> scene.

Fixpoint total (s : scene) : nat :=
  match s with
  | Empty => 0
  | Layer sh rest => weight sh + total rest
  end.

Fixpoint move_all (d : nat) (s : scene) : scene :=
  match s with
  | Empty => Empty
  | Layer (Circle (Pt x y) r) rest => Layer (Circle (Pt (x + d) y) r) (move_all d rest)
  | Layer (Poly ps) rest => Layer (Poly (shift d ps)) (move_all d rest)
  | Layer t rest => Layer t (move_all d rest)
  end.

Definition sample : scene :=
  Layer (Circle (Pt 1 2) 3)
    (Layer (Poly [Pt 1 1; Pt 2 2; Pt 3 3])
       (Layer (Tagged (Some (Pt 4 5)) (6, Pt 7 8)) Empty)).

Definition sample_total : nat := total sample.
Definition moved_total : nat := total (move_all 10 sample).

(** Fields typed by a parameter: boxed or not per instantiation. *)
Inductive tagged (A : Type) : Type := Tag : nat -> A -> tagged A.
Arguments Tag {A}.

Definition untag {A} (t : tagged A) : A := match t with Tag _ a => a end.
Definition tag_of {A} (t : tagged A) : nat := match t with Tag n _ => n end.

Definition heavy : tagged scene := Tag 1 sample.
Definition light : tagged nat := Tag 2 40.
Definition heavy_total : nat := tag_of heavy + total (untag heavy).
Definition light_total : nat := tag_of light + untag light.

End BoxedFields.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Set Crane BoxedFields.
Set Crane Loopify.
Crane Extraction "boxed_fields" BoxedFields.
