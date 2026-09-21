From Crane Require Import Mapping.Std.
From CraneTestsWIP Require Import method_body_names_later_struct.A.

(** Named after the inductive, so the collision puts this file's contents in a
    struct of their own and flattens [Zed]'s members into it. *)
Module Zed.
  (** No [zed] argument, so it stays behind in that struct. *)
  Definition norm (c : comparison) : comparison := c.
End Zed.

(** The back edge: a by-value [zed] field, so this struct needs [zed] complete
    and cannot be moved in front of it. *)
Record boxed : Set := Mk {unbox : zed}.

Definition roundtrip (x : zed) : zed := unbox (Mk x).
